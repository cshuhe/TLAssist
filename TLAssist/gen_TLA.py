import requests
import json
import os
import subprocess
import re
import time

API_KEY = "YOUR_API_KEY_HERE"
url = "YOUR_API_BASE_URL_HERE"


headers = {
    "Content-Type": "application/json",
    "Authorization": f"Bearer {API_KEY}"
}

system_prompt = """
You are a TLA+ expert responsible for converting pseudocode and JSON configurations into a precise TLA+ specification. Please follow these steps:
1. Carefully analyze the algorithm logic in the pseudocode.
2. Parse the parameters, initial state, and constraints from the JSON configuration.
3. Generate a complete TLA+ specification that conforms to TLA+ syntax and includes:
   - constant and variable declarations
   - the definition of the initial state (Init)
   - state transition rules (Next)
   - safety invariants and liveness properties
4. Remain capable of multi-turn dialogue to handle subsequent modification requests.
"""

messages = [
    {"role": "system", "content": system_prompt}
]

# ----------- save TLA+ code --------------------
history_counter = 0


def save_tla_history(code: str, step: str = ""):
    """Every time LLM outputs TLA code, it is sequentially saved as history_1. tla, history_2. tla """
    global history_counter
    history_counter += 1
    fn = f"history_{history_counter}"
    if step:
        fn += f"_{step}"
    tla_filename, cfg_filename, txt_filename = save_tla_code(code, base_filename=fn)
    print(f"=== The historical TLA+ code has been saved as {tla_filename}（step={step}）===")
    return tla_filename, cfg_filename, txt_filename


def process_files(pseudo_path, json_path):
    try:
        with open(pseudo_path, 'r', encoding='utf-8') as f:
            pseudo_code = f.read().strip()
        with open(json_path, 'r', encoding='utf-8') as f:
            json_config = json.load(f)
        return pseudo_code, json.dumps(json_config, indent=2)
    except Exception as e:
        print(f"File processing error: {str(e)}")
        return None, None


def add_to_history(role, content):
    messages.append({"role": role, "content": content})


def trim_history(messages, max_rounds=2):
    system_msgs = [msg for msg in messages if msg["role"] == "system"]
    user_assistant_pairs = []
    buffer = []
    for msg in messages:
        if msg["role"] != "system":
            buffer.append(msg)
            if msg["role"] == "assistant":
                user_assistant_pairs.append(buffer)
                buffer = []
    if buffer:
        user_assistant_pairs.append(buffer)
    selected_pairs = user_assistant_pairs[-max_rounds:]
    trimmed_messages = system_msgs + [item for pair in selected_pairs for item in pair]
    return trimmed_messages


def query_model():
    global messages
    messages = trim_history(messages, max_rounds=2)
    try:
        data = {
            "model": "claude-sonnet-4-5-20250929",
            "messages": messages,
            "stream": False,
            "max_tokens": 8192,  
            "temperature": 0.1
        }

        print("\nWaiting for LLM response...")
        start_time = time.time()

        response = requests.post(url, headers=headers, json=data, timeout=1000)

        end_time = time.time()
        latency = end_time - start_time

        if response.status_code == 200:
            result = response.json()
            assistant_reply = result['choices'][0]['message']['content']
            add_to_history("assistant", assistant_reply)

            print(f"LLM generation completed! Latency: {latency:.2f} seconds")

            csv_file = "llm_latency_metrics.csv"
            file_exists = os.path.isfile(csv_file)
            with open(csv_file, "a", encoding="utf-8") as f:

                if not file_exists:
                    f.write("Timestamp,Model,Latency_Seconds\n")


                current_time_str = time.strftime("%Y-%m-%d %H:%M:%S", time.localtime())
                model_name = data["model"]
                f.write(f"{current_time_str},{model_name},{latency:.2f}\n")

            return assistant_reply
        else:
            print(f"Request failed, error code:{response.status_code}")
            print(f"Error details：{response.text}")
            return None

    except Exception as e:
        print(f"Exception occurred:{str(e)}")
        return None


def generate_tla_plus(pseudo_code, json_config):
    instruction = f"""
Please generate a complete TLA+ specification, including the configuration section, based on the following inputs:

=== PSEUDOCODE ===
{pseudo_code}

=== JSON CONFIG ===
{json_config}

Generation requirements:
1. Replace the following symbols as indicated: change `∈` to `\in`, `∧` to `/\`, `∃` to `\E`, `U` to `\cup`, `\setminus` to `\`, `/` to `\div`, `\Diamond` to `<>`, etc.
2. If the specification uses Cardinality and natural number operations, make sure to EXTENDS FiniteSets, Naturals, Sequences, TLC first.
3. Generate TLA+, do not generate PlusCal. The MODULE name must be `generated_spec`.
4. **CONSTANTS and VARIABLES must strictly follow the json settings**. Do not add or delete VARIABLES and CONSTANTS.
5. If the property in Properties has spec_instance, then it should be written strictly according to spec_instance. And don't use Placeholder.
6. Each part of the generated TLA+ code should be strictly generated according to JSON, especially the receivedS variable's init logic. Ensure the ELSE branch is truly unconstrained (a set of functions), not just hardcoded to empty strings. NEVER use `CHOOSE` in the ELSE branch. Because the ELSE branch represents an unconstrained set of functions, it requires the membership operator (`\in`) instead of equality (`=`).
7. The module body must include: `vars == <<sender, receivedS, delivered, receivedE, receivedR>>` (The variable names in `vars` must match the VARIABLES declared at the top of the module.)
8. Append a single configuration block at the end of the file and **use exactly the format below — do not duplicate it, do not add extra separators or comments**.

---------------------- MODULE generated_spec ----------------------
(Place your main TLA+ module content here)
=============================================================================
==== CONFIG ====
CONSTANTS
    Correct = {{p1, p2, p3}}
    Faulty = {{p4}}
    V = {{v1, v2}}
    (List all constant definitions here according to the json, one per line)
SPECIFICATION Spec
INVARIANT TypeInv
INVARIANT Consistency
PROPERTY Validity
PROPERTY Totality
    (INVARIANT and PROPERTY are set according to the json file; list each property on its own line)
=======================================================================
**Notes:**
- The configuration block must be unique and complete; it must include Spec, INVARIANT, and PROPERTY, and must appear strictly after the main module.
- The configuration block must start with `==== CONFIG ====`, `CONSTANTS ...`, etc., and must end with at least ten equals signs.
- Each parameter in the configuration must appear one per line, named as in the example.
- When generating the TLA+ .cfg file, output all constant values using native TLA+ syntax.

"""
    return instruction.strip()


def save_tla_code(code: str, base_filename: str = "generated_spec"):
    # Patterns for splitting
    config_marker = r"^==== CONFIG ====\s*$"
    sep_marker = r"^={2,}\s*$"  # any line of two or more '=' signs

    lines = code.splitlines(keepends=True)
    tla_lines, cfg_lines, txt_lines = [], [], []

    section = 'tla'
    for line in lines:
        if section == 'tla' and re.match(config_marker, line):
            section = 'cfg'
            continue
        if section == 'cfg' and re.match(sep_marker, line):
            section = 'txt'
            continue

        if section == 'tla':
            tla_lines.append(line)
        elif section == 'cfg':
            cfg_lines.append(line)
        else:
            txt_lines.append(line)

    # Determine if it starts with history-N_ (strictly distinguish between history and regular files)
    if base_filename.startswith("history_"):
        history_dir = "history"
        os.makedirs(history_dir, exist_ok=True)
        tla_filename = os.path.join(history_dir, f"{base_filename}.tla")
        cfg_filename = os.path.join(history_dir, f"{base_filename}.cfg") if cfg_lines else None
        txt_filename = os.path.join(history_dir, f"{base_filename}.txt") if txt_lines else None
    else:
        tla_filename = f"{base_filename}.tla"
        cfg_filename = f"{base_filename}.cfg" if cfg_lines else None
        txt_filename = f"{base_filename}.txt" if txt_lines else None

    try:
        with open(tla_filename, 'w', encoding='utf-8') as f:
            f.writelines(tla_lines)
        print(f"TLA+ code saved to {os.path.abspath(tla_filename)}")

        if cfg_filename:
            with open(cfg_filename, 'w', encoding='utf-8') as f:
                f.writelines(cfg_lines)
            print(f"Config saved to {os.path.abspath(cfg_filename)}")

        if txt_filename:
            with open(txt_filename, 'w', encoding='utf-8') as f:
                f.writelines(txt_lines)
            print(f"Post-separator notes saved to {os.path.abspath(txt_filename)}")

        return tla_filename, cfg_filename, txt_filename

    except Exception as e:
        print(f"Error saving files: {e}")
        return None, None, None


def run_tlc(tla_file, cfg_file=None, timeout=30000):
    try:
        tla_jar_path = "./tla2tools.jar"
        module_name = os.path.splitext(os.path.basename(tla_file))[0]

        command = [
            "java",
            "-XX:+UseParallelGC",
            "-Xmx8G",
            "-cp",
            tla_jar_path,
            "tlc2.TLC",
            "-deadlock",
            "-workers",
            "8",
            module_name
        ]

        work_dir = os.path.dirname(os.path.abspath(tla_file))

        print(f"start TLC: {' '.join(command)}", flush=True)
        print(f"work directory: {work_dir}", flush=True)

        process = subprocess.Popen(
            command,
            cwd=work_dir,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            bufsize=1
        )

        output_lines = []
        start_time = time.time()

        while True:
            line = process.stdout.readline()

            if line:
                print(line, end="", flush=True)
                output_lines.append(line)

            if process.poll() is not None:

                remaining = process.stdout.read()
                if remaining:
                    print(remaining, end="", flush=True)
                    output_lines.append(remaining)
                break

            if time.time() - start_time > timeout:
                process.kill()
                timeout_msg = f"\nTLC execution timeout after {timeout} seconds\n"
                print(timeout_msg, flush=True)
                output_lines.append(timeout_msg)
                return "".join(output_lines), timeout_msg

        output = "".join(output_lines)
        error = ""

        if process.returncode != 0:
            error = f"TLC exited with return code {process.returncode}"

        return output, error

    except Exception as e:
        print(f"Error running TLC: {str(e)}", flush=True)
        return "", str(e)


def analyze_tlc_output(output):
    if not output:
        return "unknown", None, None, "No output from TLC"
    # 1) Prioritize matching the '* * Errors:' segment - retrieve all from this tag to the end of the file
    m_errs = re.search(r'(\*\*\*\s*Errors:.*\r?\n[\s\S]*)', output, re.IGNORECASE)
    if m_errs:
        block = m_errs.group(1).strip()
        line_nums = re.findall(r'line\s+(\d+)', block, re.IGNORECASE)
        if line_nums:
            nums = list(map(int, line_nums))
            start_line = min(nums)
            end_line = max(nums)
        else:
            start_line = end_line = None
        return "tlc_errors", start_line, end_line, block

    # 2) Match Parse Error style
    parse_error_match = re.search(
        r'(\*\*\*Parse Error\*\*\*[\s\S]+?Residual stack trace follows:)', output, re.IGNORECASE
    )
    if parse_error_match:
        parse_error_block = parse_error_match.group(1).strip()
        m = re.search(r'at line (\d+), col(?:umn)? (\d+)', parse_error_block, re.IGNORECASE)
        if m:
            start_line = int(m.group(1))
            end_line = start_line
        else:
            start_line = end_line = None
        return "parse", start_line, end_line, parse_error_block

    # 3) Model/semantic style error block
    inv_match = re.search(
        r'(Error: .+?\n[\s\S]+?The error trace is:[\s\S]+?)(?:(?:\n\n)|(?:\*\*\*)|$)', output, re.MULTILINE
    )
    if inv_match:
        block = inv_match.group(1).strip()
        m = re.search(r'line\s+(\d+)', block, re.IGNORECASE)
        start_line = int(m.group(1)) if m else None
        return "model", start_line, start_line, block

    # 4) Find common prompts for grammar errors directly
    m2 = re.search(r'Syntax error at line (\d+), column (\d+)', output, re.IGNORECASE)
    if m2:
        line = int(m2.group(1))
        return "syntax", line, line, f"Syntax error at line {line}, column {m2.group(2)}"

    # 5) Successfully detected
    if re.search(r'No error has been found', output, re.IGNORECASE):
        return "success", None, None, "TLC检查通过"

    # 6) Other unknown situations: Return original output
    return "unknown", None, None, output


def extract_tla_snippet(tla_path, start, end, context=3):
    try:
        with open(tla_path, encoding='utf-8') as f:
            lines = f.readlines()
    except IOError:
        return f"can't open {tla_path}"
    lo = max(1, start - context) if start is not None else 1
    hi = min(len(lines), end + context) if end is not None else len(lines)
    snippet = []
    for lineno in range(lo, hi + 1):
        prefix = ">> " if start is not None and end is not None and start <= lineno <= end else "   "
        snippet.append(f"{prefix}{lineno:4d}: {lines[lineno - 1].rstrip()}")
    return "\n".join(snippet)


def tlc_feedback_loop(initial_tla_code, max_attempts=4):
    print("\n===== Start TLC feedback loop =====")

    tla_file, cfg_file, txt_file = save_tla_code(initial_tla_code)
    current_tla_code = initial_tla_code
    attempts = 0

    save_tla_history(current_tla_code, f"tlc_attempt_{attempts}_start")

    while attempts < max_attempts:
        attempts += 1
        print(f"\n=== Try #{attempts} ===")

        start = None
        end = None
        error_type = "unknown"
        error_msg = ""

        tlc_output, tlc_error = run_tlc(tla_file, cfg_file)

        if tlc_error:
            print(f"TLC error: {tlc_error}")

            error_type = "error"
            error_msg = tlc_error

            if tlc_output:
                error_msg += "\n\nTLC output:\n" + tlc_output

            if tlc_output:
                analyzed_type, analyzed_start, analyzed_end, analyzed_msg = analyze_tlc_output(tlc_output)
                if analyzed_start is not None:
                    start = analyzed_start
                    end = analyzed_end
                    error_type = analyzed_type
                    error_msg = analyzed_msg

        else:
            error_type, start, end, error_msg = analyze_tlc_output(tlc_output)

        code_snippet = ""

        if start is not None and end is not None:
            code_snippet = extract_tla_snippet(tla_file, start, end)
        else:
            code_snippet = "No specific source line could be located."

        if error_type == "success":
            print("\n===== TLC success! =====")
            return current_tla_code, "TLC verification successful!"

        feedback_prompt = f"""
TLC inspection found the following {error_type} error:
{error_msg}
The error is approximately located on lines {start} to {end}.
The corresponding code snippet is shown below, where arrows indicate the error line:
{code_snippet}
Please fix this part of the code based on the above information and return the complete `.tla` file content, retaining the original `==== CONFIG ====` configuration section.
Please provide the complete repaired TLA+ code:
"""

        print(f"\nSend error feedback to LLM:\n{feedback_prompt}")

        add_to_history("user", feedback_prompt)
        new_tla_code = query_model()

        if not new_tla_code:
            print("LLM failed to generate repair code")
            continue

        tla_file, cfg_file, txt_file = save_tla_code(new_tla_code)
        save_tla_history(new_tla_code, f"tlc_attempt_{attempts}")

        if not tla_file:
            print("Unable to save repaired TLA+ code")
            continue

        current_tla_code = new_tla_code
        print("The repaired TLA+ code has been saved and is ready to run TLC again...")
        time.sleep(2)

    return current_tla_code, f"After {max_attempts} attempts, TLC validation still failed"


def main():
    print("Start API connection...")

    pseudo_file = "BrachaRBC.txt"
    json_file = "BrachaRBC.json"

    pseudo_code, json_config = process_files(pseudo_file, json_file)
    if not pseudo_code or not json_config:
        print("File processing failed, program terminated")
        return

    gen_prompt = generate_tla_plus(pseudo_code, json_config)
    add_to_history("user", gen_prompt)

    print("Generating initial TLA+ specifications...")
    initial_output = query_model()

    if initial_output:
        print("\n===== TLA+ code =====")
        print(f"output type: {type(initial_output)}")
        print(f"Initial_output: {initial_output}")
        save_tla_history(initial_output, "initial")

        if initial_output:

            tla_file, cfg_file, txt_file = save_tla_code(initial_output)
            if tla_file:
                final_code, status = tlc_feedback_loop(initial_output)
                save_tla_history(final_code, "final_validated")
                final_file, final_cfg, final_txt = save_tla_code(final_code, "final_validated_spec")
                print(f"\nfinal state: {status}")
            else:
                print("Unable to save TLA+ file, skip TLC verification")

    print("\nEnter multi round dialogue mode (enter 'exit' to end)")
    while True:
        user_input = input("\nUser：").strip()
        if user_input.lower() in ["exit", "exit"]:
            print("End of conversation.")
            break
        add_to_history("user", user_input)
        response = query_model()

        if response:
            if "MODULE" in response and "==== CONFIG ====" in response:
                save_tla_history(response, f"interactive_{history_counter}")
                print(f"\nAssistant (TLA+)：{response}")
            else:
                print(f"\nnAssistant：{response}")


if __name__ == "__main__":
    main()
