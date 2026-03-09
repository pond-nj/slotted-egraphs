import subprocess
from pathlib import Path


def count_sat_in_dir(dir_path: str, z3_path: str = "z3") -> int:
    """
    Run z3 -smt2 on all .smt2 files in dir_path (non-recursive)
    and return how many are SAT.
    """
    directory = Path(dir_path)
    sat_count = 0
    files = list(directory.glob("*.smt2"))
    print("total files:", len(files))
    for i, smt_file in enumerate(files):
        # Run: z3 -smt2 <file>
        result = subprocess.run(
            [z3_path, "-smt2", str(smt_file)],
            capture_output=True,
            text=True,
        )
        out = (result.stdout + result.stderr).lower()
        out = out.split()
        if ["sat"] == out:
            sat_count += 1
            print(i, "sat", smt_file)
        elif ["unsat"] == out:
            print(i, "unsat", smt_file)
        else:
            raise ValueError(f"Unexpected output: {out}")

    return sat_count


if __name__ == "__main__":
    import sys

    if len(sys.argv) != 2:
        print(f"Usage: {sys.argv[0]} DIR_WITH_SMT2_FILES")
        raise SystemExit(1)

    dir_path = sys.argv[1]
    n_sat = count_sat_in_dir(dir_path)
    print(f"SAT files: {n_sat}")
