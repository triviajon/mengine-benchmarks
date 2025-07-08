#!/usr/bin/env python3
import sys
import os
import time
import subprocess
import json

RESULTS_FILE_PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)), "results.json")

def generate_coq_file(n, filename):
    def generate_goal(n):
        preds = [f"P{i}" for i in range(1, n+1)]
        forall_line = f"  Goal forall ({' '.join(preds)} : map -> Prop),\n"

        # Construct sep-chains
        def make_sep(lst):
            if len(lst) == 1:
                return lst[0]
            return f"sep {lst[0]} ({make_sep(lst[1:])})"

        lhs = make_sep(preds)
        rhs = make_sep(preds[::-1])
        goal_line = f"    iff1 ({lhs})\n         ({rhs}).\n"

        return forall_line + goal_line

    content = """Require Import coqutil.Lift1Prop.
Require Import coqutil.Map.Interface coqutil.Map.Properties coqutil.Map.Separation coqutil.Map.SeparationLogic.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List.
Require Import coqutil.sanity coqutil.Decidable coqutil.Tactics.destr coqutil.Tactics.ltac_list_ops.

Import Map.Interface.map Map.Properties.map.

Section Test.
  Context {key value} {map : map key value} {ok : ok map}.
  Context {key_eqb: key -> key -> bool} {key_eq_dec: EqDecider key_eqb}.
  Local Open Scope sep_scope.
  Import List.ListNotations.

  __GOAL__

  Proof.
    intros.
    cancel.
  Qed.
End Test.
"""
    content = content.replace("__GOAL__", str(generate_goal(n)))

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
    if len(sys.argv) < 6:
        print("Usage: run.py {mengine|coqc|lean} config_fp n executable_path timeout")
        sys.exit(1)

    engine = sys.argv[1]
    config_fp = sys.argv[2]
    n = int(sys.argv[3])
    exe_path = os.path.expanduser(sys.argv[4])
    timeout = int(sys.argv[5])

    config = json.load(open(config_fp, "r"))
    coqutil_binding = os.path.expanduser(os.path.join(config.get("coqutil_root_path", None), "src", "coqutil"))
    if not coqutil_binding:
        print("No coqutil root path provided in config.")
        sys.exit(1)

    results = load_results()
    if engine == "mengine":
        key = f"{engine}_n{n}"

        if results.get(key, None):
            print(f"Skipping {key} as it has already been run.")
            return

        args = [exe_path, "--proof=0", "sep1", str(n)]
        start = time.perf_counter()
        subprocess.run(args, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        end = time.perf_counter()
        success = True

        results[key] = {"time_taken": end - start, "success": success}
        save_results(results)
    elif engine == "coqc":
        key = f"{engine}_n{n}"
        if results.get(key, None):
            print(f"Skipping {key} as it has already been run.")
            return

        filename = f"test_n{n}.v"
        generate_coq_file(n, filename)

        start = time.perf_counter()
        try:
            proc = subprocess.run([exe_path, "-Q", coqutil_binding, "coqutil", filename], capture_output=True, text=True, timeout=timeout)
            success = proc.returncode == 0
            print(proc.stdout)
            print(proc.stderr)
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
