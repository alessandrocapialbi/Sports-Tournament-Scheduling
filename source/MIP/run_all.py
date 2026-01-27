#!/usr/bin/env python3

import subprocess
import sys

def main():

    timeout = 300
    outdir = "res/MIP"

    print("\nRunning all instances (n = 6 to 16)...\n")

    for n in range(6, 17, 2):  # 6,8,10,12,14,16

        print("=" * 60)
        print(f"Running instance with n = {n}")
        print("=" * 60)

        try:
            subprocess.run(
                [
                    sys.executable,
                    "source/MIP/run.py",
                    "-n", str(n),
                    "-o", outdir,
                    "-t", str(timeout)
                ],
                check=True
            )

        except subprocess.CalledProcessError:
            print(f"Instance n={n} finished with non-optimal result or error.\n")

        except Exception as e:
            print(f"Unexpected error for n={n}: {e}\n")

    print("\nAll runs completed.\n")


if __name__ == "__main__":
    main()
