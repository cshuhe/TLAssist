import requests
import re
import json
import sys
from pathlib import Path

API_KEY = "YOUR_API_KEY_HERE"
url = "YOUR_API_BASE_URL_HERE"


def read_file_content(filename):
    p = Path(filename)
    if not p.exists():
        print(f"ERROR: file not found: {filename}")
        sys.exit(1)
    return p.read_text(encoding="utf-8")


def extract_json_from_text(text):
    m = re.search(r"```json\s*(\{.*?\})\s*```", text, re.S)
    if m:
        return m.group(1).strip()
    m = re.search(r"```(?:.|\n)*?(\{.*?\})(?:.|\n)*?```", text, re.S)
    if m:
        return m.group(1).strip()
    m = re.search(r"(\{(?:[^{}]|(?R))*\})", text, re.S)
    if m:
        return m.group(1).strip()
    m = re.search(r"\{.*\}", text, re.S)
    if m:
        return m.group(0).strip()
    return None


def ask_model(messages):
    headers = {
        "Content-Type": "application/json",
        "Authorization": f"Bearer {API_KEY}"
    }
    payload = {
        "model": "claude-sonnet-4-5-20250929",
        "messages": messages,
        "max_tokens": 8192,
        "temperature": 0.1
    }
    resp = requests.post(url, headers=headers, json=payload)
    try:
        content = resp.json()
    except Exception as e:
        print("Error parsing response JSON:", e)
        print("Raw response text:", resp.text)
        return None

    try:
        return content["choices"][0]["message"]["content"]
    except Exception as e:
        print("Unexpected response format:", e)
        print(json.dumps(content, indent=2, ensure_ascii=False))
        return None


def construct_prompts(reference, pseudocode):
    system_prompt = (
        "You are a TLA+ master. The immediate goal is to convert pseudocode into a JSON description "
        "following the conventions shown in the provided draft.md. You may adjust variables "
        "to match the pseudocode; action structures should follow the draft style. Produce clear JSON."
    )

    user_prompt = (
        f"the contents of draft.md are as follows:\n'''\n{reference}\n'''\n\n"
        f"the pseudocode is as follows:\n'''\n{pseudocode}\n'''\n"
        "Please study the mapping between pseudocode and JSON files in draft.md, and convert the pseudocode into a "
        "sensible JSON format that meets the following requirements: "
        "\n- Do NOT model an explicit PROPOSE/SEND action. Instead, receivedS is a mapping from processes to V"
        "\n- For SendEcho (or equivalent) actions, use only the guard `receivedS[self] \in V`. Do NOT add conditions like Cardinality(Sends(...)) or checks against SEND messages."
        "\n- If the model emits any Sends-related helpers/actions, remove them."

        "\n- Constants and variables can be partially removed or added according to the requirements of the pseudocode. "
        "\n- action structures should follow the draft.md style; you may add or omit subitems based on the pseudocode (Do not omit Next and Spec) "
        "\n- Do NOT add N or F into CONSTANTS. Use derived expressions N == Cardinality(Correct \cup Faulty) and F == Cardinality(Faulty) in TLA+, so omit them from CONSTANTS."
        "\n- Do NOT invent helpers/fields not in the pseudocode (e.g. \"EchoAuthors\")."
        "\n- Byzantine action: model faulty processes as able to inject only the message types appearing in pseudocode.(but do not model SEND/PROPOSE messages)"

        "\n- Do not model message-sending state with Boolean variables (e.g., sentReady).Use set-based conditions instead, inferring sends from self ∉ receivedR[self][v][self][v] or similar predicates."
        "\n- If SymbolOf is used, it must be interpreted exactly as follows: it abstracts encoded message fragments and is instantiated as a total function from processes to fragments with a fixed one-to-one correspondence; moreover, both the description and the instance of SymbolOf must be copied verbatim from the JSON file, with no rewriting or abbreviation allowed."
        "\n- When reasoning about the condition of each action in Actions, the pseudocode must be interpreted faithfully, and variables must not be introduced or assigned arbitrarily."
        "\n- Copy the `Invariants` and `Properties` sections from the input JSON verbatim into the output JSON. Do not modify names, descriptions, or `spec_instance` fields—preserve them exactly."

        "\n- CRITICAL BYZANTINE EQUIVOCATION LOGIC: Read the PROPOSE/ECHO behavior in the pseudocode carefully."
        "\n  * MODE A (Default): IF the pseudocode explicitly checks `and an (Echo) message has not been sent` (or similar guards preventing multiple echos), use single-value mapping: "
        "\n      - `receivedS` type is `Correct -> V \\cup {\"\"}`."
        "\n      - `SendEcho` condition uses `receivedS[self] \\in V`."
        "\n  * MODE B (Set-based): IF the pseudocode does NOT have a 'ECHO message has not been sent' guard (e.g., just `upon receiving <PROPOSE, M> ... do send <ECHO, M>`), you MUST model the Byzantine sender sending multiple different values to the same process. Apply these updates:"
        "\n      1 `receivedS` type: `Correct -> SUBSET V`."
        "\n      2 `receivedS` init: `If sender \\in Correct, receivedS maps all correct processes to a singleton set {CHOOSE v \\in V : TRUE}; otherwise unconstrained mapped to SUBSET V`."
        "\n      3 `SendEcho` condition: Must extract the value using `\\E val \\in receivedS[self]` and MUST not add the guard `\\A v \\in V : self \\notin receivedE[self][v]`."
        "\n      4 `SendEcho` effect: Use the extracted `val` instead of `receivedS[self]`."
        "\n      5 `Validity` property: Must safely extract the single value if the sender is correct: `LET Val == IF sender \\in Correct THEN CHOOSE v \\in V : v \\in receivedS[sender] ELSE \"\"`."
        "\n  Do not add self = sender as a condition for SendDisperse in SigBRB; the DISPERSE round can be performed by any correct node. And Do not forget ByzantineFinal action."
        "\n  The Authenticated Echo Broadcast pseudocode should not include the Totality property in `Properties`, since AEB is not required to satisfy totality. The Authenticated Double-Echo Broadcast pseudocode should include the Totality property. The overall structure of both pseudocode specifications should remain consistent with `draft.md`. DO NOT use `echos` and `readys`."
        "\n\n Please produce an initial JSON draft that follows the above. Return ONLY the JSON (inside a json block is preferred). "
    )
    return system_prompt, user_prompt


def main():
    reference = read_file_content("draft.md")
    pseudocode_filename = "BrachaRBC.txt"      # change here
    json_file = "BrachaRBC.json"          # change here

    pseudocode = read_file_content(pseudocode_filename)
    system_prompt, user_prompt = construct_prompts(reference, pseudocode)

    messages_step1 = [{"role": "system", "content": system_prompt}]
    messages_step1.append({"role": "user", "content": user_prompt})

    print("Requesting the new JSON from model...")
    reply1 = ask_model(messages_step1)
    if not reply1:
        print("No response for the draft. Exiting.")
        return

    draft_json_text = extract_json_from_text(reply1)
    if draft_json_text:
        print("\n--- JSON saved！ ---\n")
        try:
            parsed = json.loads(draft_json_text)
            pretty = json.dumps(parsed, indent=2, ensure_ascii=False)
            print(pretty)
            with open(json_file, "w", encoding="utf-8") as f:
                json.dump(parsed, f, ensure_ascii=False, indent=2)
        except Exception:
            print(draft_json_text)
    else:
        print("Could not extract JSON from the model's initial reply. Here's the raw reply for debugging:\n")
        print(reply1)
        draft_json_text = reply1


if __name__ == "__main__":
    main()
