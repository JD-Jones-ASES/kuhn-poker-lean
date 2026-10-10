#!/usr/bin/env python3
"""Exercise the source guard's Lake-option and control-byte checks through its actual CLI.

Each control runs the committed guard in a temporary, otherwise clean project.
The denied lines test each advertised option independently, so a malformed regex
cannot make the guard pass while silently dropping one of its alternatives.
No files in the development are modified.
"""

from pathlib import Path
import shutil
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parents[1]
CLEAN_LAKEFILE = 'name = "sourceGuardFixture"\nversion = "0.1.0"\n'
DENIED = [
    ("moreLeanArgs", 'moreLeanArgs = ["--threads=1"]'),
    ("weakLeanArgs", 'weakLeanArgs = ["--threads=1"]'),
    ("leanOptions", 'leanOptions = { pp.universes = true }'),
    ("leanOptions table", '[leanOptions]\npp.universes = true'),
    ("debug option", 'debug.skipKernelTC = true'),
    ("-D argument", 'arguments = ["-Dpp.universes=true"]'),
]


def main():
    failures = []
    with tempfile.TemporaryDirectory(prefix="kuhn-source-guard-") as directory:
        fixture = Path(directory)
        (fixture / "scripts").mkdir()
        (fixture / "KuhnPoker").mkdir()
        shutil.copyfile(ROOT / "scripts" / "check-source.py", fixture / "scripts" / "check-source.py")
        for name in ("KuhnPoker/Defs.lean", "KuhnPoker.lean", "Solution.lean", "Test.lean"):
            (fixture / name).write_text("namespace KuhnPoker\nend KuhnPoker\n", encoding="utf-8")
        (fixture / "Challenge.lean").write_text("theorem placeholder : True := sorry\n", encoding="utf-8")

        def run(extra=""):
            (fixture / "lakefile.toml").write_text(CLEAN_LAKEFILE + extra + "\n", encoding="utf-8")
            return subprocess.run(
                [sys.executable, "-I", str(fixture / "scripts" / "check-source.py")],
                cwd=fixture, text=True, encoding="utf-8", errors="replace", capture_output=True,
            )

        clean = run()
        if clean.returncode != 0 or "Source guard passed" not in clean.stdout:
            failures.append("clean fixture did not pass: " + (clean.stdout + clean.stderr).strip())
        for label, denied_line in DENIED:
            result = run(denied_line)
            if result.returncode == 0 or "lakefile.toml:" not in result.stderr or \
                    "prohibited option or argument" not in result.stderr:
                failures.append(label + " was not rejected by the Lake-option guard")
        control = fixture / "scripts" / "control_byte.py"
        control.write_bytes(b"PATTERN = 1\x08\n")
        result = run()
        control.unlink()
        if result.returncode == 0 or "control characters" not in result.stderr:
            failures.append("a control byte in a script was not rejected")

    for failure in failures:
        print("FAIL: " + failure)
    print(f"Source guard controls: {'FAIL' if failures else 'PASS'} "
          f"(one clean fixture, {len(DENIED)} prohibited-option fixtures, one control-byte fixture)")
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
