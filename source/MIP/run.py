import argparse
import subprocess
import re
import os
import sys
import json
import time as tm
from pathlib import Path

def previous_unsolved(outdir, N, solver):
    prev_n = N - 2
    prev_file = os.path.join(outdir, f"{prev_n}.json")

    if not os.path.exists(prev_file):
        return False

    with open(prev_file, "r") as f:
        data = json.load(f)

    key = f"MIP-{solver}"

    if key not in data:
        return False

    return data[key]["sol"] == []

def parse_solution_matrix(stdout):
    week_blocks = re.findall(
        r"Week\s+\d+:(.*?)(?=Week\s+\d+:|Total Imbalance:|----------|$)",
        stdout,
        re.DOTALL
    )

    if not week_blocks:
        return None

    weeks = []

    for block in week_blocks:
        # Extract matches in format: "Period X: A vs B"
        period_matches = re.findall(
            r"Period\s+\d+:\s*(\d+)\s+vs\s+(\d+)",
            block
        )

        week_matches = [[int(a), int(b)] for a, b in period_matches]

        if week_matches:
            weeks.append(week_matches)

    if not weeks:
        return None

    num_weeks = len(weeks)
    num_periods = len(weeks[0])

    # Ensure all weeks have same number of periods
    for w in weeks:
        if len(w) != num_periods:
            return None

    # Convert week-major → period-major (same structure as before)
    matrix = []

    for p in range(num_periods):
        row = []
        for w in range(num_weeks):
            row.append(weeks[w][p])
        matrix.append(row)

    # Convert team numbering from 0-based to 1-based
    for p in range(num_periods):
        for w in range(num_weeks):
            for t in range(2):
                matrix[p][w][t] += 1

    return matrix

def run_scheduler(n, solver, timeout=300):

    result = {
        "time": timeout,
        "optimal": False,
        "obj": None,
        "sol": []
    }

    start_time = tm.time()

    try:
        process = subprocess.run(
            [
                sys.executable,
                "source/MIP/model.py",
                "--N", str(n),                     # positional arg: teams
                "--solver", solver,
            ],
            capture_output=True,
            text=True,
            timeout=timeout
        )

        elapsed_time = int(tm.time() - start_time)

        if process.returncode != 0:
            print(f"Warning: Solver failed with return code {process.returncode}")
            if process.stderr:
                print("STDERR:", process.stderr[:500])
            return result

        print(process.stdout)

        imbalance = None
        imbalance_match = re.search(r"TOTAL IMBALANCE:\s*(\d+)", process.stdout)
        if imbalance_match:
            imbalance = int(imbalance_match.group(1))

        schedule_matrix = parse_solution_matrix(process.stdout)

        if imbalance is None or not schedule_matrix:
            print("Failed to extract solution.")
            return result

        # Competition optimality rule: imbalance <= N
        is_optimal = imbalance is not None and imbalance <= n

        if is_optimal:
            result["time"] = elapsed_time
        else:
            result["time"] = timeout

        result["optimal"] = is_optimal
        result["obj"] = imbalance
        result["sol"] = schedule_matrix

        if not is_optimal:
            print(f"Warning: Objective {imbalance} > N={n}, setting optimal=False")

    except subprocess.TimeoutExpired:
        print(f"Timeout: Solver exceeded {timeout} seconds")
        result["time"] = timeout
        result["optimal"] = False

    except Exception as e:
        print(f"Unexpected error: {e}")
        import traceback
        traceback.print_exc()
        result["time"] = timeout
        result["optimal"] = False

    return result



def main():
    parser = argparse.ArgumentParser(
        description="Run the MIP round-robin scheduler and output results as JSON.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s --N 12 --solver cbc  --outdir results/MIP --timeout 300
  %(prog)s --N 8  --solver highs --outdir results/MIP --timeout 60
  %(prog)s --N 14 --solver highs --outdir results/MIP --no-skip-non-solvable
        """
    )

    parser.add_argument(
        "--N", type=int, required=True, metavar="N",
        help="Number of teams (must be even, >= 6)"
    )
    parser.add_argument(
        "--solver", type=str, required=True,
        choices=["cbc", "highs"],
        help="MIP solver backend"
    )
    parser.add_argument(
        "--outdir", type=str, default="res", metavar="DIR",
        help="Output directory for JSON results (default: res)"
    )
    parser.add_argument(
        "--timeout", type=int, default=300, metavar="SECONDS",
        help="Timeout in seconds (default: 300)"
    )
    parser.add_argument(
        "--no-skip-non-solvable",
        dest="skip_non_solvable",
        action="store_false",
        help="Disable skipping when N-2 had an empty solution"
    )
    parser.set_defaults(skip_non_solvable=True)

    args = parser.parse_args()

    # validation
    if args.N < 6:
        print(f"Error: Number of teams must be at least 6 (got {args.N})")
        sys.exit(1)
    if args.N % 2 != 0:
        print(f"Error: Number of teams must be even (got {args.N})")
        sys.exit(1)
    if args.timeout <= 0:
        print(f"Error: Timeout must be positive (got {args.timeout})")
        sys.exit(1)

    script_path = Path("source/MIP/model.py")
    if not script_path.exists():
        print(f"Error: model.py not found at {script_path}")
        sys.exit(1)

    # output setup
    os.makedirs(args.outdir, exist_ok=True)
    output_file = os.path.join(args.outdir, f"{args.N}.json")
    key = f"MIP-{args.solver}"

    # skip check
    if args.skip_non_solvable and args.N > 6:
        if previous_unsolved(args.outdir, args.N, args.solver):
            print(f"Skipping {key} at N={args.N} (unsolved at N={args.N - 2})")
            result = {
                "time": args.timeout,
                "optimal": False,
                "obj": None,
                "sol": []
            }
            # Merge into existing file if present, otherwise create it
            existing = {}
            if os.path.exists(output_file):
                with open(output_file, "r") as f:
                    existing = json.load(f)
            existing[key] = result

            with open(output_file, "w") as f:
                json.dump(existing, f, indent=2)

            print(f"Skipped result saved to: {output_file}")
            sys.exit(0)

    # run
    print(f"\nRunning {key} for N={args.N}...")
    print(f"Timeout: {args.timeout} seconds")
    print(f"Output will be saved to: {output_file}\n")

    result = run_scheduler(args.N, args.solver, args.timeout)

    # Merge into existing file (preserves other solver keys in the same JSON)
    existing = {}
    if os.path.exists(output_file):
        with open(output_file, "r") as f:
            existing = json.load(f)
    existing[key] = result

    with open(output_file, "w") as f:
        json.dump(existing, f, indent=2)

    # summary
    print("\n" + "=" * 80)
    print("RESULTS SUMMARY")
    print("=" * 80)
    print(f"Teams:                        {args.N}")
    print(f"Solver:                       {args.solver}")
    print(f"Time:                         {result['time']} seconds")
    print(f"Optimal:                      {result['optimal']}")
    print(f"Objective (Total Imbalance):  {result['obj']}")
    print(f"Solution:                     {'Found' if result['sol'] else 'Not found'}")
    print(f"\nResults saved to: {output_file}")
    print("=" * 80 + "\n")

    sys.exit(0 if result['optimal'] else 1)


if __name__ == "__main__":
    main()
