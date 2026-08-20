#!/usr/bin/env python3
"""Run generated TLA+ specifications with TLC.

Examples:
    python3 run_tla.py SigBRB
    python3 run_tla.py SigBRB.tla
    python3 run_tla.py --list
"""

from __future__ import annotations

import argparse
import os
from pathlib import Path
import shlex
import subprocess
import sys
import time
import queue
import threading

PROJECT_DIR = Path(__file__).resolve().parent
SPEC_DIR = PROJECT_DIR / "Target_TLA_Specification"
TLA_JAR = PROJECT_DIR / "TLAssist" / "tla2tools.jar"


def available_specs() -> dict[str, Path]:
    """Return a case-insensitive mapping from module name to .tla path."""
    if not SPEC_DIR.is_dir():
        return {}
    return {p.stem.lower(): p for p in sorted(SPEC_DIR.glob("*.tla"))}


def resolve_spec(name: str) -> Path:
    """Resolve a module name such as SigBRB or SigBRB.tla safely."""
    raw = Path(name).name
    stem = raw[:-4] if raw.lower().endswith(".tla") else raw
    specs = available_specs()
    spec = specs.get(stem.lower())
    if spec is None:
        known = ", ".join(p.stem for p in specs.values()) or "(none)"
        raise FileNotFoundError(
            f"Unknown TLA+ specification: {name}\nAvailable specifications: {known}"
        )
    return spec


def resolve_config(spec: Path, config_arg: str | None) -> Path:
    """Use an explicitly supplied cfg, otherwise pair <name>.tla with <name>.cfg."""
    if config_arg:
        cfg = Path(config_arg).expanduser()
        if not cfg.is_absolute():
            cfg = (Path.cwd() / cfg).resolve()
    else:
        cfg = spec.with_suffix(".cfg")

    if not cfg.is_file():
        raise FileNotFoundError(
            f"Configuration file not found: {cfg}\n"
            f"TLC needs concrete CONSTANT assignments for this specification. "
            f"Create/edit {spec.stem}.cfg or pass --config <file>."
        )
    return cfg


def java_command(
    spec: Path,
    cfg: Path,
    *,
    workers: int,
    memory: str,
    check_deadlock: bool,
) -> list[str]:
    command = [
        "java",
        "-XX:+UseParallelGC",
        f"-Xmx{memory}",
        "-cp",
        str(TLA_JAR),
        "tlc2.TLC",
    ]
    if not check_deadlock:
        # TLC's -deadlock flag disables deadlock checking. This mirrors gen_TLA.py.
        command.append("-deadlock")
    command.extend([
        "-workers",
        str(workers),
        "-config",
        cfg.name,
        spec.stem,
    ])
    return command


def run_one(
    spec: Path,
    cfg: Path,
    *,
    workers: int,
    memory: str,
    timeout: int | None,
    check_deadlock: bool,
) -> int:
    if not TLA_JAR.is_file():
        print(f"Error: tla2tools.jar not found: {TLA_JAR}", file=sys.stderr)
        return 2

    command = java_command(
        spec,
        cfg,
        workers=workers,
        memory=memory,
        check_deadlock=check_deadlock,
    )

    print(f"\n=== TLC: {spec.stem} ===")
    print(f"TLA : {spec}")
    print(f"CFG : {cfg}")
    print("CMD : " + shlex.join(command))


    try:
        process = subprocess.Popen(
            command,
            cwd=spec.parent,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            bufsize=1,
        )
    except FileNotFoundError:
        print("Error: Java was not found. Please install a Java runtime first.", file=sys.stderr)
        return 127
    except OSError as exc:
        print(f"Error starting TLC: {exc}", file=sys.stderr)
        return 2

    assert process.stdout is not None
    started = time.monotonic()
    output_queue: queue.Queue[str | None] = queue.Queue()

    def _pump_output() -> None:
        try:
            for line in process.stdout:
                output_queue.put(line)
        finally:
            output_queue.put(None)

    reader = threading.Thread(target=_pump_output, daemon=True)
    reader.start()
    stream_finished = False

    try:
        while True:
            if timeout is not None and time.monotonic() - started > timeout:
                process.kill()
                process.wait()
                print(f"\nTLC timed out after {timeout} seconds.", file=sys.stderr)
                return 124

            try:
                item = output_queue.get(timeout=0.1)
            except queue.Empty:
                item = ""

            if item is None:
                stream_finished = True
            elif item:
                print(item, end="", flush=True)

            if process.poll() is not None and stream_finished:
                break
    except KeyboardInterrupt:
        process.kill()
        process.wait()
        print("\nTLC interrupted by user.", file=sys.stderr)
        return 130

    if process.returncode == 0:
        print(f"\n=== {spec.stem}: TLC finished successfully ===")
    else:
        print(f"\n=== {spec.stem}: TLC exited with code {process.returncode} ===", file=sys.stderr)
    return int(process.returncode or 0)


def print_list() -> None:
    specs = available_specs()
    if not specs:
        print(f"No .tla files found in {SPEC_DIR}")
        return
    print(f"Specifications in {SPEC_DIR}:")
    for spec in specs.values():
        cfg = spec.with_suffix(".cfg")
        cfg_status = "cfg: yes" if cfg.is_file() else "cfg: MISSING"
        print(f"  {spec.stem:<28} {cfg_status}")


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description=(
            "Run a generated TLA+ module by name. By default, <name>.cfg is "
            "automatically loaded from Target_TLA_Specification."
        )
    )
    parser.add_argument("name", nargs="?", help="module name, e.g. SigBRB or SigBRB.tla")
    parser.add_argument("--list", action="store_true", help="list available .tla modules and cfg status")
    parser.add_argument("--config", help="override the default same-name .cfg file")
    parser.add_argument("--workers", type=int, default=8, help="TLC worker count (default: 8)")
    parser.add_argument("--memory", default="8G", help="Java max heap, e.g. 4G or 2048m (default: 8G)")
    parser.add_argument("--timeout", type=int, default=None, help="optional timeout in seconds")
    parser.add_argument(
        "--check-deadlock",
        action="store_true",
        help="enable TLC deadlock checking (the original gen_TLA.py disables it)",
    )
    return parser


def main() -> int:
    args = build_parser().parse_args()

    if args.workers < 1:
        print("Error: --workers must be at least 1", file=sys.stderr)
        return 2
    if args.timeout is not None and args.timeout < 1:
        print("Error: --timeout must be at least 1 second", file=sys.stderr)
        return 2

    if args.list:
        print_list()
        return 0

    if not args.name:
        build_parser().print_help()
        print("\nTip: python3 run_tla.py SigBRB")
        return 0

    try:
        spec = resolve_spec(args.name)
        cfg = resolve_config(spec, args.config)
    except FileNotFoundError as exc:
        print(f"Error: {exc}", file=sys.stderr)
        return 2

    return run_one(
        spec,
        cfg,
        workers=args.workers,
        memory=args.memory,
        timeout=args.timeout,
        check_deadlock=args.check_deadlock,
    )


if __name__ == "__main__":
    raise SystemExit(main())
