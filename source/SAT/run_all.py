import subprocess
import sys
import os
import time
import math


TIMEOUT = 300  # seconds


def main():
    # Run from parent folder
    script_name = "./source/SAT/solve.py"
    save_dir = "./res/SAT"

    os.makedirs(save_dir, exist_ok=True)

    for n in range(6, 21, 2):

        mode = "both" if n <= 10 else "satisfy"

        print("=" * 60)
        print(f"Running solver for N={n} (mode={mode})")
        print("=" * 60)

        cmd = [
            sys.executable,
            "source/SAT/run.py",
            "--N", str(n),
            "--mode", mode,
            "--outdir", save_dir,
            "--timeout", str(TIMEOUT)
        ]

        start_time = time.time()

        try:
            result = subprocess.run(
                cmd,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                timeout=TIMEOUT
            )

            end_time = time.time()
            runtime = math.floor(end_time - start_time)

            print(f"Runtime: {runtime} seconds\n")
            print(result.stdout)

            if result.stderr:
                print("Warnings/Errors:")
                print(result.stderr)

        except subprocess.TimeoutExpired as te:
            end_time = time.time()
            runtime = TIMEOUT

            print(f"\n⏳ Timeout: Solver exceeded {TIMEOUT} seconds for N={n}")
            print("Process terminated.")
            print(f"Recorded runtime: {runtime} seconds\n")

            # Ensure process is killed
            if te.process:
                te.process.kill()

        except Exception as e:
            print(f"\nError while running N={n}")
            print(str(e))

    print("\nBatch execution completed.")


if __name__ == "__main__":
    main()
