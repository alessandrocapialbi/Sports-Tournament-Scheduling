import subprocess
import sys

def main():

    timeout = 300
    outdir = "res/MIP"
    solvers = ["cbc", "highs"]

    print("\nRunning all instances (n = 6 to 22)...\n")

    for n in range(6, 23, 2):
        for solver in solvers:
            print("=" * 60)
            print(f"Running instance with n = {n}")
            print("=" * 60)

            try:
                subprocess.run(
                    [
                        sys.executable,
                        "source/MIP/run.py",
                        "--N", str(n),
                        "--outdir", outdir,
                        "-t", str(timeout),
                        "--solver", solver
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
