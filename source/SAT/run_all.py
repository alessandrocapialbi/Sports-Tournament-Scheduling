import subprocess
import sys
import os
import time
import math


TIMEOUT = 300


def main():
    save_dir = "./res/SAT"
    os.makedirs(save_dir, exist_ok=True)

    solvers = ["z3", "ortools"]
    mode = "both"

    for n in range(6, 23, 2):

        print("=" * 60)
        print(f"Running N={n}")
        print("=" * 60)

        for solver in solvers:
            cmd = [
                sys.executable,
                "source/SAT/run.py",
                "--N", str(n),
                "--mode", mode,
                "--solver", solver,
                "--outdir", save_dir,
                "--timeout", str(TIMEOUT)
            ]

            start_time = time.time()

            try:
                result = subprocess.run(
                    cmd,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE,
                    text=True
                )

                runtime = math.floor(time.time() - start_time)

                print(f"\n{solver}-{mode} runtime: {runtime}s")

                if result.stdout:
                    print(result.stdout)

                if result.stderr:
                    print("Errors:")
                    print(result.stderr)

            except subprocess.TimeoutExpired:
                print(f"Timeout at N={n} ({solver}-{mode})")

    print("\nBatch execution completed.")


if __name__ == "__main__":
    main()
