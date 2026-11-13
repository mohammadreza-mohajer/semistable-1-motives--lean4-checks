#!/usr/bin/env python3
"""Run the nine Lean checks and record fresh output outside the archived results."""

import argparse
import hashlib
import json
import re
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path


ROOT = Path(__file__).resolve().parent
DECLARATIONS = [
    "reduced_differential_square_zero",
    "scalar_block_trace",
    "concrete_dual_matrices_are_trace_zero",
    "concrete_projective_dual_pairing",
    "concrete_self_gram_matrix",
    "concrete_self_trace_determinant",
    "elliptic_affine_point_count",
    "elliptic_projective_point_count",
    "elliptic_frobenius_trace",
]


def timestamp():
    return datetime.now(timezone.utc).isoformat()


def run_command(arguments):
    return subprocess.run(
        arguments, cwd=ROOT, capture_output=True, text=True,
        encoding="utf-8", errors="replace", check=False,
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", default="lean", help="Lean executable (default: lean)")
    args = parser.parse_args()
    output = ROOT / ".build" / "latest"
    output.mkdir(parents=True, exist_ok=True)
    source_path = ROOT / "AppendixChecks.lean"
    source_bytes = source_path.read_bytes()
    source_text = source_bytes.decode("utf-8")
    started = timestamp()
    try:
        version = run_command([args.lean, "--version"])
    except OSError as error:
        print("Unable to run Lean: " + str(error), file=sys.stderr)
        return 2
    version_text = version.stdout + version.stderr
    print(version_text, end="")
    (output / "lean_version.txt").write_text(version_text, encoding="utf-8")
    if version.returncode != 0 or not re.search(r"\bversion 4\.19\.0(?:,|\s|\))", version_text):
        print("Lean 4.19.0 is required. See lean-toolchain and README.md.", file=sys.stderr)
        return 2

    command = [args.lean, "-o", str(output / "AppendixChecks.olean"), "AppendixChecks.lean"]
    completed = run_command(command)
    compiler_output = completed.stdout + completed.stderr
    print(compiler_output, end="")
    (output / "lean_output.txt").write_text(compiler_output, encoding="utf-8")
    reports = [
        line for line in compiler_output.splitlines()
        if "does not depend on any axioms" in line or "depends on axioms:" in line
    ]
    names = []
    errors = []
    for line in reports:
        match = re.fullmatch(
            r"'SemistableAppendix\.(\w+)' (?:does not depend on any axioms|depends on axioms: \[propext\])",
            line,
        )
        if match:
            names.append(match.group(1))
        else:
            errors.append("Unexpected dependency report: " + line)
    declarations = re.findall(r"^theorem\s+(\w+)", source_text, re.MULTILINE)
    if completed.returncode != 0:
        errors.append("Lean returned a nonzero exit code.")
    if declarations != DECLARATIONS or names != DECLARATIONS:
        errors.append("Expected all nine theorem declarations and their dependency reports in order.")
    placeholders = bool(re.search(r"\b(?:sorry|admit)\b", source_text))
    custom_axioms = bool(re.search(r"^\s*axiom\s", source_text, re.MULTILINE))
    if placeholders or custom_axioms:
        errors.append("The source contains proof placeholders or additional axiom declarations.")
    record = {
        "status": "verified" if not errors else "failed",
        "started_utc": started,
        "finished_utc": timestamp(),
        "lean_version": version_text.strip(),
        "command": ["lean", "-o", ".build/latest/AppendixChecks.olean", "AppendixChecks.lean"],
        "source": "AppendixChecks.lean",
        "source_sha256": hashlib.sha256(source_bytes).hexdigest(),
        "exit_code": completed.returncode,
        "declarations": declarations,
        "declaration_count": len(declarations),
        "axiom_reports": reports,
        "source_contains_proof_placeholders": placeholders,
        "source_declares_axioms": custom_axioms,
        "validation_errors": errors,
    }
    (output / "lean_run_status.json").write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8")
    if errors:
        print("\n".join(errors), file=sys.stderr)
        return 1
    print("All nine Lean declarations checked successfully. Fresh records: .build/latest/")
    return 0


if __name__ == "__main__":
    sys.exit(main())
