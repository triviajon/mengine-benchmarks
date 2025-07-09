#!/usr/bin/env python3
import sys
import os
import time
import subprocess
import json

RESULTS_FILE_PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)), "results.json")
strat_to_coq_string = {
    "rewritebng": "rewrite!",
    "repeatrewrite": "repeat rewrite",
    "repeatsetoidrewrite": "repeat setoid_rewrite",
    "rewritebottomup": "rewrite_strat bottomup",
    "rewritetopdown": "rewrite_strat topdown",
}

def generate_coq_file(n, m, filename, strategy):
    nat_args = " -> ".join(["nat"] * (n + 1))

    let_bindings = []
    for i in range(1, m + 1):
        if i == 1:
            args = " ".join(["x0"] * n)
            let_bindings.append(f"        let x{i} := f {args} in")
        else:
            args = " ".join([f"x{i-1}"] * n)
            let_bindings.append(f"        let x{i} := f {args} in")

    content = f"""Require Import Setoid Morphisms.
Section Test.
    Variable nat : Set.
    Variable x0 : nat.
    Variable f : {nat_args}.

    Lemma f_n_x0 : f {" ".join(["x0"] * n)} = x0. Admitted.

    Goal 
{"\n".join(let_bindings)}
        x{m} = x0.
    Proof.
        simpl.
        {strat_to_coq_string[strategy]} f_n_x0.
        apply eq_refl.
    Qed.
End Test.
"""

    with open(filename, "w") as f:
        f.write(content)

def generate_lean_file(n, m, filename):
    nat_args = " -> ".join(["Nat"] * (n + 1))

    let_bindings = []
    for i in range(1, m + 1):
        if i == 1:
            args = " ".join(["x0"] * n)
            let_bindings.append(f"        let x{i} := f {args}")
        else:
            args = " ".join([f"x{i-1}"] * n)
            let_bindings.append(f"        let x{i} := f {args}")

    content = f"""set_option maxHeartbeats 0
set_option maxRecDepth 10000
variable (x0 : Nat)
variable (f : {nat_args})

theorem f_n_x0 : f {" ".join(["x0"] * n)} = x0 := sorry

theorem simp :
  {"\n".join(let_bindings)}
  x{m} = x0 := by
  simp only [f_n_x0]
  done
"""
    with open(filename, "w") as f:
        f.write(content)


def load_results():
    if not os.path.exists(RESULTS_FILE_PATH):
        return {}

    with open(RESULTS_FILE_PATH, "r") as f:
        return json.load(f)

def save_results(results):
    with open(RESULTS_FILE_PATH, "w") as f:
        json.dump(results, f, indent=4)

def main():
    if len(sys.argv) < 7:
        print("Usage: run.py {mengine|coqc|lean} config_fp n m executable_path timeout")
        sys.exit(1)

    engine = sys.argv[1]
    config_fp = sys.argv[2]
    n = int(sys.argv[3])
    m = int(sys.argv[4])
    exe_path = os.path.expanduser(sys.argv[5])
    timeout = int(sys.argv[6])



    if engine == "mengine":
        key = f"{engine}_n{n}_m{m}"
        results = load_results()
        if key in results:
            print(f"Results for {key} already exist. Skipping.")
            sys.exit(0)
        args = [exe_path, "--proof=0", "nm", str(n), str(m)]
        start = time.perf_counter()
        subprocess.run(args, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        end = time.perf_counter()
        success = True

        results = load_results()
        results[key] = {"time_taken": end - start, "success": success}
        save_results(results)
    elif engine == "coqc":
        for strategy in ["rewritebng", "repeatrewrite", "repeatsetoidrewrite", "rewritebottomup", "rewritetopdown"]:
            if strategy in ["repeatsetoidrewrite", "rewritebottomup", 'rewritetopdown'] and m > 11:
                print(f"Skipping {strategy} for n={n} as it may take too long.")
                continue
            
            key = f"{engine}_n{n}_m{m}_{strategy}"
            # results = load_results()
            # if key in results:
            #     print(f"Results for {key} already exist. Skipping.")
            #     continue
            filename = f"test_n{n}_m{m}_{strategy}.v"
            generate_coq_file(n, m, filename, strategy)
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
        key = f"{engine}_n{n}_m{m}"
        results = load_results()
        if key in results:
            print(f"Results for {key} already exist. Skipping.")
            sys.exit(0)
        filename = f"test_n{n}_m{m}.lean"
        generate_lean_file(n, m, filename)
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
    else:
        print(f"Unknown engine '{engine}'")
        sys.exit(1)

if __name__ == "__main__":
    main()
