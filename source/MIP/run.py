import argparse
import subprocess
import re
import sys
import json
import time as tm
from pathlib import Path


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


def run_scheduler(n, timeout=300):

    result = {
        "time": timeout,
        "optimal": False,
        "obj": None,
        "sol": []
    }

    start_time = tm.time()

    try:
        process = subprocess.run(
            [sys.executable, "source/MIP/model.py", str(n)],
            capture_output=True,
            text=True,
            timeout=timeout
        )

        elapsed_time = int(tm.time() - start_time)

        if process.returncode != 0:
            print(f"Warning: Solver failed with return code {process.returncode}")
            if process.stderr:
                print("STDERR:", process.stderr[:500])
            return result  # time already = timeout, optimal=False

        # Print solver output so schedule is visible
        print(process.stdout)

        imbalance = None
        imbalance_match = re.search(r"TOTAL IMBALANCE:\s*(\d+)", process.stdout)
        if imbalance_match:
            imbalance = int(imbalance_match.group(1))

        schedule_matrix = parse_solution_matrix(process.stdout)

        if imbalance is None or not schedule_matrix:
            print("Failed to extract solution.")
            return result

        # Competition optimality rule
        is_optimal = imbalance and imbalance <= n

        if is_optimal:
            result["time"] = elapsed_time
        else:
            result["time"] = timeout  # required rule

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
        description='Run the round-robin scheduler and output results in JSON format.',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s -n 12 -o results/MIP -t 300
  %(prog)s -n 8 -o results/MIP -t 60
  %(prog)s --teams 10 --outdir results/CP --timeout 300

The output JSON file will be created at: <outdir>/<n>.json
        """
    )

    parser.add_argument(
        '-n', '--teams',
        type=int,
        required=True,
        metavar='N',
        help='Number of teams (must be even, minimum 4)'
    )

    parser.add_argument(
        '-o', '--outdir',
        type=str,
        required=True,
        metavar='DIR',
        help='Output directory for results (e.g., results/MIP)'
    )

    parser.add_argument(
        '-t', '--timeout',
        type=int,
        default=300,
        metavar='SECONDS',
        help='Timeout in seconds (default: 300)'
    )

    args = parser.parse_args()

    # Validate input
    if args.teams < 6:
        print(f"Error: Number of teams must be at least 6 (got {args.teams})")
        sys.exit(1)
    if args.teams % 2 != 0:
        print(f"Error: Number of teams must be even (got {args.teams})")
        sys.exit(1)
    if args.timeout <= 0:
        print(f"Error: Timeout must be positive (got {args.timeout})")
        sys.exit(1)

    # Create output directory if it doesn't exist
    outdir = Path(args.outdir)
    outdir.mkdir(parents=True, exist_ok=True)

    # Output file path
    output_file = outdir / f"{args.teams}.json"

    print(f"\nRunning scheduler for {args.teams} teams...")
    print(f"Timeout: {args.timeout} seconds")
    print(f"Output will be saved to: {output_file}\n")

    # Run the scheduler
    result = run_scheduler(args.teams, args.timeout)

    # Create the final JSON structure
    approach_name = "MIP-CBC_MILP"

    json_output = {
        approach_name: result
    }

    # Write to JSON file
    with open(output_file, 'w') as f:
        json.dump(json_output, f, indent=2)

    # Print summary
    print("\n" + "=" * 80)
    print("RESULTS SUMMARY")
    print("=" * 80)
    print(f"Teams: {args.teams}")
    print(f"Time: {result['time']} seconds")
    print(f"Optimal: {result['optimal']}")
    print(f"Objective (Total Imbalance): {result['obj']}")
    print(f"Solution: {'Found' if len(result['sol']) > 0 else 'Not found'}")
    print(f"\nResults saved to: {output_file}")
    print("=" * 80 + "\n")

    # Return appropriate exit code
    sys.exit(0 if result['optimal'] else 1)


if __name__ == "__main__":
    main()
