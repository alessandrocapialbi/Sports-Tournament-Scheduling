import subprocess
import sys
import os

def main():
    script_name = "./source/SAT/run.py"
    save_dir = "./res/SAT"

    os.makedirs(save_dir, exist_ok=True)

    for n in range(6, 21, 2):
        mode = "both" if n <= 10 else "satisfy"

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
                text=True,
                timeout=300  # Timeout in seconds
            )

            print(result.stdout)
            if result.stderr:
                print("Warnings/Errors:")
                print(result.stderr)

        except subprocess.TimeoutExpired as te:
            print(f"TimeoutExpired: Solver took longer than 300s for N={n}")
            print("Killing solver process.")
            # You can record this in JSON or elsewhere too
            print(te)

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
