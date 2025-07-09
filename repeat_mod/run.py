#!/usr/bin/env python3
import sys
import os
import time
import subprocess
import json

RESULTS_FILE_PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)), "results.json")

def generate_coq_file_rewrite_bng(n, filename, method):
    
    method_to_text = {
        "repeatrewrite": "repeat rewrite",
        "repeatsetoidrewrite": "repeat setoid_rewrite",
        "rewritebottomup": "rewrite_strat bottomup",
        "rewritetopdown": "rewrite_strat topdown"
    }

    with open(filename, 'w') as f:
        f.write("Require Import Morphisms Setoid.\n")
        f.write("Section Test.\n\n")
        f.write("Variable nat : Set.\n")
        f.write("Variable b : nat.\n")
        f.write("Variable p : nat.\n")
        f.write("Variable mod : nat -> nat -> nat.\n")
        f.write("Variable mod_mod : forall (a : nat) (n : nat), (mod (mod a n) n) = (mod a n).\n\n")

        # Build the left-hand side (((b mod p) mod p) mod p) ...
        lhs = "b"
        for _ in range(n):
            lhs = f"(mod {lhs} p)"
        rhs = "mod b p"

        f.write(f"Theorem mod_mod_chain : {lhs} = {rhs}.\n")
        f.write("Proof.\n")
        f.write("  ")
        f.write(f"{method_to_text[method]} mod_mod. ")
        f.write("reflexivity.\n")
        f.write("Qed.\n")
        f.write("End Test.\n")


def generate_lean_file(n, filename, strategy):
    strategy_to_text = {
        'simp': 'simp only [mod_mod]',
        'repeat': 'repeat rw [mod_mod]',
    }

    with open(filename, 'w') as f:
        f.write("set_option maxHeartbeats 0\n")
        f.write("set_option maxRecDepth 100000\n\n")
        f.write("theorem mod_mod (a n : Nat) : Nat.mod (Nat.mod a n) n = Nat.mod a n := sorry\n\n")

        f.write("variable (b p : Nat)\n\n")

        lhs = "b"
        for _ in range(n):
            lhs = f"Nat.mod ({lhs}) p"
        rhs = "Nat.mod b p"

        f.write(f"theorem mod_mod_chain : {lhs} = {rhs} := by\n")
        f.write(f"  {strategy_to_text[strategy]}\n")


def load_results():
    if not os.path.exists(RESULTS_FILE_PATH):
        return {}

    with open(RESULTS_FILE_PATH, "r") as f:
        return json.load(f)

def save_results(results):
    with open(RESULTS_FILE_PATH, "w") as f:
        json.dump(results, f, indent=4)

def main():
    if len(sys.argv) < 6:
        print("Usage: run.py {mengine|coqc|lean} config_fp n executable_path timeout")
        sys.exit(1)

    engine = sys.argv[1]
    config_fp = sys.argv[2]
    n = int(sys.argv[3])
    exe_path = os.path.expanduser(sys.argv[4])
    timeout = int(sys.argv[5])


    if engine == "mengine":
        key = f"{engine}_n{n}"
        results = load_results()
        if key in results:
            print(f"Skipping {key}, already exists in results.")
            return

        args = [exe_path, "--proof=0", "mod", str(n)]
        start = time.perf_counter()
        subprocess.run(args, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        end = time.perf_counter()
        success = True

        results[key] = {"time_taken": end - start, "success": success}
        save_results(results)
    elif engine == "coqc":
        for method in ["repeatrewrite", "repeatsetoidrewrite", "rewritebottomup", "rewritetopdown"]:

            key = f"{engine}_{method}_n{n}"
            results = load_results()
            if key in results:
                print(f"Skipping {key}, already exists in results.")
                continue

            filename = f"test_{method}_n{n}.v"
            generate_coq_file_rewrite_bng(n, filename, method)

            start = time.perf_counter()
            try:
                proc = subprocess.run([exe_path, filename], capture_output=True, text=True, timeout=timeout)
                success = proc.returncode == 0
            except subprocess.TimeoutExpired:
                success = False
            end = time.perf_counter()
            os.remove(filename)

            results = load_results()
            results[key] = {"time_taken": end - start, "success": success}
            save_results(results)
    elif engine == "lean":
        for strategy in ["repeat", "simp"]:
            if strategy == "repeat" and n > 500:
                print(f"Skipping {strategy} for n={n} as it causes stack overflow.")
                continue

            key = f"{engine}_n{n}_{strategy}"
            results = load_results()
            if key in results:
                print(f"Skipping {key}, already exists in results.")
                return

            filename = f"test_n{n}.lean"
            generate_lean_file(n, filename, strategy)

            start = time.perf_counter()
            try:
                proc = subprocess.run([exe_path, filename], capture_output=True, text=True, timeout=timeout)
                success = proc.returncode == 0
            except subprocess.TimeoutExpired:
                success = False
            end = time.perf_counter()
            os.remove(filename)

            results[key] = {"time_taken": end - start, "success": success}
            save_results(results)
    else:
        print(f"Unknown engine '{engine}'")
        sys.exit(1)

if __name__ == "__main__":
    main()