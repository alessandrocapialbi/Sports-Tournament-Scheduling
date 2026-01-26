#!/usr/bin/env python3
"""
Sports Scheduling Problem Solver

This script solves the sports scheduling problem using SAT encoding.
It supports both decision (satisfy) and optimization modes.
"""

import argparse
import time
import sys
import os
from solve import satisfy, solve_with_optimization
from utils import format_json, save_json, calculate_params


def main():
    parser = argparse.ArgumentParser(
        description='Solve the sports scheduling problem for N teams',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python run.py -n 6 --mode satisfy
  python run.py -n 8 --mode optimize
  python run.py -n 10 --mode both --savedir results
        """
    )

    parser.add_argument(
        '-n', '--teams',
        type=int,
        required=True,
        help='Number of teams (must be even)'
    )

    parser.add_argument(
        '--mode',
        type=str,
        choices=['satisfy', 'optimize', 'both'],
        default='both',
        help='Solving mode: satisfy (decision), optimize (with balance), or both (default: both)'
    )

    parser.add_argument(
        '--savedir',
        type=str,
        default='.',
        help='Directory to save output JSON file (default: current directory)'
    )

    args = parser.parse_args()

    # Validate input
    if args.teams % 2 != 0:
        print(f"Error: Number of teams must be even, got {args.teams}")
        sys.exit(1)

    if args.teams < 4:
        print(f"Error: Number of teams must be at least 4, got {args.teams}")
        sys.exit(1)

    N = args.teams

    # Create save directory if it doesn't exist
    if args.savedir != '.':
        os.makedirs(args.savedir, exist_ok=True)

    # Build output file path
    output_file = os.path.join(args.savedir, f"{N}.json")

    # Store all results
    all_results = {}

    print(f"\n{'=' * 60}")
    print(f"Sports Scheduling Problem - N={N} teams")
    print(f"{'=' * 60}\n")

    # Calculate parameters
    T, S, W, P, M = calculate_params(N)

    # Run SAT Decision Version
    if args.mode in ['satisfy', 'both']:
        print(f"\n{'=' * 60}")
        print("Running SAT Decision Version (Satisfy)")
        print(f"{'=' * 60}\n")

        start_time = time.time()
        try:
            solution = satisfy(N)
            runtime = time.time() - start_time

            if solution is not None:
                # Get match pairs for formatting
                from utils import generate_rb_and_flattened
                _, match_pairs = generate_rb_and_flattened(N, W, P, S)

                json_result = format_json(
                    N=N,
                    P=P,
                    W=W,
                    match_pairs=match_pairs,
                    extracted_solution=solution,
                    runtime=runtime,
                    approach_name="Z3_Decision",
                    is_optimal=True,
                    objective_value=None
                )
                all_results.update(json_result)
                print(f"\nRuntime: {runtime:.2f} seconds")
            else:
                runtime = time.time() - start_time
                # UNSAT case
                json_result = {
                    "Z3_Decision": {
                        "time": 300,
                        "optimal": False,
                        "obj": None,
                        "sol": None
                    }
                }
                all_results.update(json_result)
                print(f"\nNo solution found (UNSAT)")

        except Exception as e:
            print(f"Error during SAT decision solving: {e}")
            json_result = {
                "Z3_Decision": {
                    "time": 300,
                    "optimal": False,
                    "obj": None,
                    "sol": None
                }
            }
            all_results.update(json_result)

    # Run SAT Optimization Version
    if args.mode in ['optimize', 'both']:
        print(f"\n{'=' * 60}")
        print("Running SAT Optimization Version (Home/Away Balance)")
        print(f"{'=' * 60}\n")

        start_time = time.time()
        try:
            solution = solve_with_optimization(N)
            runtime = time.time() - start_time

            if solution is not None:
                # Get match pairs for formatting
                from utils import generate_rb_and_flattened
                _, match_pairs = generate_rb_and_flattened(N, W, P, S)

                objective_value = solution.get('imbalance')

                json_result = format_json(
                    N=N,
                    P=P,
                    W=W,
                    match_pairs=match_pairs,
                    extracted_solution=solution,
                    runtime=runtime,
                    approach_name="Z3_Optimization",
                    is_optimal=True,
                    objective_value=objective_value
                )
                all_results.update(json_result)
                print(f"\nRuntime: {runtime:.2f} seconds")
                print(f"Objective (Total Imbalance): {objective_value}")
            else:
                runtime = time.time() - start_time
                # UNSAT case
                json_result = {
                    "Z3_Optimization": {
                        "time": 300,
                        "optimal": False,
                        "obj": None,
                        "sol": None
                    }
                }
                all_results.update(json_result)
                print(f"\nNo solution found (UNSAT)")

        except Exception as e:
            print(f"Error during SAT optimization solving: {e}")
            json_result = {
                "Z3_Optimization": {
                    "time": 300,
                    "optimal": False,
                    "obj": None,
                    "sol": None
                }
            }
            all_results.update(json_result)

    # Save results to JSON
    if all_results:
        save_json(all_results, output_file)
        print(f"\n{'=' * 60}")
        print(f"All results saved to {output_file}")
        print(f"{'=' * 60}\n")
    else:
        print("\nNo results to save.")


if __name__ == "__main__":
    main()