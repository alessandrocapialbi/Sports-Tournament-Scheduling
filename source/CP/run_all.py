import subprocess
import sys

# Configuration
SCRIPT_NAME = "source/CP/run.py"
SOURCE_DIR = "source/CP"
OUTPUT_DIR = "res/CP"
TIMEOUT = 300


def main():
    """
    Run this script from parent dir.
    """
    for N in range(6, 23, 2):
        print("\n==============================")
        print(f"Launching run for N = {N}")
        print("==============================")

        cmd = [
            sys.executable,      # uses same python interpreter
            SCRIPT_NAME,
            "--dir", SOURCE_DIR,
            "--N", str(N),
            "--outdir", OUTPUT_DIR,
            "--timeout", str(TIMEOUT)
        ]

        result = subprocess.run(cmd)

        if result.returncode != 0:
            print(f"Run failed for N = {N}")
        else:
            print(f"Completed N = {N}")


if __name__ == "__main__":
    main()
