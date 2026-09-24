#!/usr/bin/env python3
"""Check the paired draft on the verified toolchain; not Palomar Comparator.

Run after scripts/syncfailcomp.sh --sync-only to keep builds in the persistent
Linux mirror. Existing pinned dependencies are validated before and after use.
No toolchain upgrade, package download, submission, or full kernel replay is
performed. Challenge's nine deliberate theorem holes are expected.
"""

from pathlib import Path
import subprocess
import sys

LIBRARY = Path(__file__).resolve().parent.parent
PROJECT = LIBRARY.parent
sys.path.insert(0, str(LIBRARY))
import prepare_packages  # noqa: E402


def main():
    prepare_packages.check_runtime(PROJECT)
    output = PROJECT / ".lake" / "build" / "lib" / "lean" / "FailureOfComposition" / "Palomar"
    output.mkdir(parents=True, exist_ok=True)
    override = PROJECT / ".lake" / "palomar-draft-packages.json"
    prepare_packages.prepare_packages(PROJECT, override)
    environment = prepare_packages.clean_environment()

    def run(*arguments):
        command = ["lake", f"--packages={override}", *arguments]
        print("RUN " + " ".join(command), flush=True)
        subprocess.run(command, cwd=PROJECT, env=environment, check=True)

    try:
        # Lake refreshes the existing production dependency graph incrementally.
        run("build", "FailureOfComposition")
        for module in ("Challenge", "Solution"):
            flags = ["-Dlinter.mathlibStandardSet=true", "-DwarningAsError=true"] \
                if module == "Solution" else []
            run("env", "lean", *flags, "-o", str(output / f"{module}.olean"),
                f"FailureOfComposition/Palomar/{module}.lean")
        run("env", "lean", "--run", "FailureOfComposition/Palomar/CheckInterface.lean")
    finally:
        prepare_packages.check_packages(PROJECT, override)
    print("PASS local paired draft check; Palomar eligibility and Comparator remain outstanding")


if __name__ == "__main__":
    try:
        main()
    except subprocess.CalledProcessError as error:
        raise SystemExit(error.returncode) from error
    except (OSError, ValueError) as error:
        raise SystemExit(str(error)) from error
