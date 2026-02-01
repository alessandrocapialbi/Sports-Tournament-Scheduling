# Round Robin Tournament Scheduling

This project solves single round robin sport tournament scheduling using three different approaches: Constraint Programming (CP), Boolean Satisfiability (SAT), and Mixed Integer Programming (MIP).

## Prerequisites

- Docker installed on your system

## Building the Docker Image

From the project root directory (where the Dockerfile is located), build the Docker image:

```bash
docker build -t cdmo-project .
```

## Running the Docker Container

Start an interactive shell in the container:

```bash
docker run -it cdmo-project
```

You will be placed in the `/cdmo` directory, which is the working directory for all operations.

## Project Structure

```
/cdmo
├── source/
│   ├── CP/          # Constraint Programming models (.mzn files)
│   │   ├── run.py
│   │   └── run_all.py
│   ├── SAT/         # SAT/SMT models (Z3)
│   │   ├── solve.py
│   │   ├── run.py
│   │   └── run_all.py
│   └── MIP/         # Mixed Integer Programming models
│       ├── model.py
│       ├── run.py
│       └── run_all.py
└── res/             # Results directory
    ├── CP/
    ├── SAT/
    └── MIP/
```

## Running Individual Models

All commands below should be executed from the `/cdmo` directory inside the Docker container.

### Constraint Programming (CP)

#### Run a single CP model with a specific solver:

```bash
python source/CP/run.py --model source/CP/<model_file>.mzn --solver <solver> --N <num_teams> [--timeout <seconds>]
```

**Parameters:**
- `--model`: Path to the MiniZinc model file (`.mzn`)
- `--solver`: Solver to use (`gecode`, `chuffed`, or `cp-sat`)
- `--N`: Number of teams (must be even, minimum 6)
- `--timeout`: Time limit in seconds (default: 300)
- `--outdir`: Output directory (default: `res`)

**Example:**
```bash
python source/CP/run.py --model source/CP/opt_baseline.mzn --solver gecode --N 8 --timeout 300
```

#### Run all CP models in a directory:

```bash
python source/CP/run.py --dir source/CP --N <num_teams> [--timeout <seconds>] [--outdir <output_dir>]
```

**Parameters:**
- `--dir`: Directory containing `.mzn` files
- `--N`: Number of teams (must be even, minimum 6)
- `--timeout`: Time limit in seconds (default: 300)
- `--outdir`: Output directory (default: `res`)
- `--no-skip-non-solvable`: Disable optimization that skips model-solver pairs that failed at N-2

**Example:**
```bash
python source/CP/run.py --dir source/CP --N 10 --timeout 300 --outdir res/CP
```

### SAT (Z3 & OR-Tools)

#### Run the SAT solver:

```bash
python source/SAT/run.py --N <num_teams> --mode <mode> --solver <solver> [--timeout <seconds>] [--outdir <output_dir>]
```

**Parameters:**
- `--N`: Number of teams (must be even, minimum 6)
- `--solver`: Solver to use:
    - `z3`: Z3 SMT solver
    - `ortools`: OR-Tools CP-SAT solver
- `--mode`: Execution mode:
  - `satisfy`: Find a feasible solution
  - `optimize`: Find an optimal solution
  - `both`: Run both satisfaction and optimization
- `--timeout`: Time limit in seconds (default: 300)
- `--outdir`: Output directory (default: `res`)

**Examples:**
```bash
# Run satisfaction with Z3
python source/SAT/run.py --N 8 --mode satisfy --solver z3

# Run optimization with OR-Tools
python source/SAT/run.py --N 10 --mode optimize --solver ortools --timeout 600
```

### Mixed Integer Programming (MIP)
#### Run the MIP solver:
```bash
python source/MIP/run.py --N <num_teams> --solver <solver> [--timeout <seconds>] [--outdir <output_dir>] [--no-skip-non-solvable]
```
**Parameters:**
- `--N`: Number of teams (must be even, minimum 6)
- `--solver`: Solver to use:
  - `cbc`: COIN-OR CBC solver
  - `highs`: HiGHS solver
- `--timeout`: Time limit in seconds (default: 300)
- `--outdir`: Output directory for results (default: `res`)
- `--no-skip-non-solvable`: Don't skip instances known to be non-solvable (optional)

**Example:**
```bash
python source/MIP/run.py --N 12 --solver cbc --timeout 300
python source/MIP/run.py --N 12 --solver highs --timeout 300 --outdir res/MIP
```

## Running All Models Automatically

To run all instances for all models with a single command, use the respective `run_all.py` scripts.

### Run All CP Models

Runs all CP models with all solvers for N = 6, 8, 10, ..., 22:

```bash
python source/CP/run_all.py
```

This executes:
- All `.mzn` files in `source/CP/`
- With all three solvers: `gecode`, `chuffed`, `cp-sat`
- For even values of N from 6 to 22
- Results saved to `res/CP/`
- Timeout: 300 seconds per instance

### Run All SAT Models

Runs both solvers (z3 and ortools) for N = 6, 8, 10, ..., 22:

```bash
python source/SAT/run_all.py
```

This executes:
- Both `satisfy` and `optimize` modes for every N in the range
- Both `z3` and `ortools` solvers
- For even values of N from 6 to 22
- Results saved to `res/SAT/`
- Timeout: 300 seconds per instance

### Run All MIP Models

Runs MIP solver for N = 6, 8, 10, ..., 16:

```bash
python source/MIP/run_all.py
```

This executes:
- The CBC MILP solver
- For even values of N from 6 to 16
- Results saved to `res/MIP/`
- Timeout: 300 seconds per instance

### Run Everything

To execute all models across all approaches sequentially:

```bash
python source/CP/run_all.py && python source/SAT/run_all.py && python source/MIP/run_all.py
```

## Output Format

All results are saved as JSON files in the respective output directories:

- CP results: `res/CP/<N>.json`
- SAT results: `res/SAT/<N>.json`
- MIP results: `res/MIP/<N>.json`

### JSON Structure

Each JSON file contains results grouped by approach:

```json
{
    "file_name-solver": {
        "time": <runtime_in_seconds>,
        "optimal": <true_or_false>,
        "obj": <total_imbalance>,
        "sol": [
            [[team1, team2], [team3, team4], ...],  // Period 1
            [[team1, team2], [team3, team4], ...],  // Period 2
            ...
        ]
    }
}
```

**Fields:**
- `time`: Runtime in seconds (floored). Set to timeout if non-optimal.
- `optimal`: `true` if solution found with objective ≤ N, `false` otherwise
- `obj`: Total imbalance value (or `null` if no solution found)
- `sol`: Schedule matrix in period-major format with 1-based team indexing (or `[]` if no solution)

### Example Output

For `opt_baseline.mzn` CP with `gecode` and `chuffed` solver (N=8):

```json
{
    "opt_baseline-gecode": {
        "time": 45,
        "optimal": true,
        "obj": 6,
        "sol": [
            [[1, 2], [3, 4], [5, 6], [7, 8]],
            [[1, 3], [2, 5], [4, 7], [6, 8]],
            ...
        ]
    },
    "opt_baseline-chuffed": {
        "time": 52,
        "optimal": true,
        "obj": 8,
        "sol": [...]
    }
}
```

## Solvers Used

- **CP**: MiniZinc with Gecode, Chuffed, and OR-Tools CP-SAT
- **SAT**: Z3 solver and OR-Tools CP-SAT
- **MIP**: CBC (COIN-OR Branch and Cut) MILP solver and HiGHS 

All solvers are free and open-source, ensuring full reproducibility.

## Notes

- The project automatically creates output directories if they don't exist
- Team numbering in solutions is 1-based (teams 1 to N)
- The CP solver includes an optimization to skip model-solver pairs that had no solution at N-2 (can be disabled with `--no-skip-non-solvable`)
- Runtime is measured as the floor of actual execution time
- If a solution is non-optimal (objective > N or no solution found), runtime is set to the timeout value
- For SAT, optimization mode is only run for smaller instances (N ≤ 10) due to computational complexity
