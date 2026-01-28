import subprocess
import json
import os
import time
import math
import argparse
import re
from pathlib import Path


def run_z3_model(script_path, mode, N, timeout_sec=300):
    cmd = [
        "python",
        str(script_path),
        "-n", str(N),
        "--mode", mode
    ]

    start_time = time.time()

    try:
        result = subprocess.run(
            cmd,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            timeout=timeout_sec
        )

        timed_out = False

    except subprocess.TimeoutExpired as e:
        end_time = time.time()
        runtime_floor = timeout_sec

        return runtime_floor, False, None, []

    end_time = time.time()

    actual_runtime = end_time - start_time
    runtime_floor = math.floor(actual_runtime)

    stdout = result.stdout
    print(stdout)

    # --------------------------------------------------
    # Objective extraction (only for optimization)
    # --------------------------------------------------
    obj = None
    obj_match = re.search(r"Total Imbalance:\s*(\d+)", stdout)
    if obj_match:
        obj = int(obj_match.group(1))

    # --------------------------------------------------
    # Solution extraction
    # --------------------------------------------------
    sol = parse_solution_matrix(stdout)

    # --------------------------------------------------
    # Optimality detection
    # --------------------------------------------------
    optimal = True
    if not sol or (obj and obj > N):
        optimal = False
        runtime_floor = timeout_sec

    return runtime_floor, optimal, obj, sol


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
        matches = re.findall(r"(\d+)\s+vs\s+(\d+)", block)
        week_matches = [[int(a), int(b)] for a, b in matches]

        if week_matches:
            weeks.append(week_matches)

    if not weeks:
        return None

    num_weeks = len(weeks)
    num_periods = len(weeks[0])

    matrix = []

    for p in range(num_periods):
        row = []
        for w in range(num_weeks):
            if p < len(weeks[w]):
                row.append(weeks[w][p])
            else:
                return None
        matrix.append(row)

    # Convert team numbering from 0-based to 1-based
    for p in range(num_periods):
        for w in range(num_weeks):
            for t in range(2):
                matrix[p][w][t] += 1

    return matrix


def main():
    parser = argparse.ArgumentParser(
        description="Run Z3 scheduling script and produce grouped JSON (subprocess style)."
    )

    parser.add_argument(
        "--N",
        type=int,
        required=True,
        help="Number of teams"
    )

    parser.add_argument(
        "--timeout",
        type=int,
        default=300,
        help="Timeout in seconds (default 300)"
    )

    parser.add_argument(
        "--outdir",
        type=str,
        default="res",
        help="Directory where JSON file will be saved"
    )

    parser.add_argument(
        "-m", "--mode",
        type=str,
        choices=["satisfy", "optimize", "both"],
        required=True,
        help="Execution mode: 'sat' for satisfaction, 'opt' for optimization."
    )

    args = parser.parse_args()

    script_path = Path("source/SAT/solve.py")

    if not script_path.exists():
        print("Invalid script path")
        return

    if args.N % 2 != 0:
        print("N must be even")
        return

    results = {}

    # --------------------------------------------------
    # Run based on mode
    # --------------------------------------------------
    modes_to_run = []

    if args.mode == "both":
        modes_to_run = ["satisfy", "optimize"]
    else:
        modes_to_run = [args.mode]

    for mode in modes_to_run:
        approach_name = f"Z3-{mode}"
        print(f"Running {approach_name}...")

        runtime, optimal, obj, sol = run_z3_model(
            script_path=script_path,
            mode=mode,
            N=args.N,
            timeout_sec=args.timeout
        )

        results[approach_name] = {
            "time": runtime,
            "optimal": optimal,
            "obj": obj,
            "sol": sol if sol else []
        }

    # --------------------------------------------------
    # Save JSON
    # --------------------------------------------------
    os.makedirs(args.outdir, exist_ok=True)
    output_path = os.path.join(args.outdir, f"{args.N}.json")

    with open(output_path, "w") as f:
        json.dump(results, f, indent=4)

    print(f"\nSaved grouped results to {output_path}")


if __name__ == "__main__":
    main()
