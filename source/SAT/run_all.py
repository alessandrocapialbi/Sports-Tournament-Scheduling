import subprocess
import sys
import os


def main():
    script_name = "./source/SAT/run.py"
    save_dir = "./res/SAT"

    # Ensure results directory exists
    os.makedirs(save_dir, exist_ok=True)

    # Loop through even N from 6 to 20
    for n in range(6, 21, 2):
        # Mode logic
        if n <= 12:
            mode = "both"
        else:
            mode = "optimize"

        print("=" * 60)
        print(f"Running solver for N={n} (mode={mode})")
        print("=" * 60)

        cmd = [
            sys.executable,
            script_name,
            "-n", str(n),
            "--mode", mode,
            "--savedir", save_dir
        ]

        try:
            result = subprocess.run(
                cmd,
                check=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True
            )

            print(result.stdout)

            if result.stderr:
                print("Warnings/Errors:")
                print(result.stderr)

        except subprocess.CalledProcessError as e:
            print(f"Error while running N={n}")
            print("Return code:", e.returncode)
            print("Output:")
            print(e.stdout)
            print("Errors:")
            print(e.stderr)

    print("\nBatch execution completed.")


if __name__ == "__main__":
    main()
