#!/usr/bin/env python3
import sys
import os
import time
import subprocess
import json

RESULTS_FILE_PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)), "results.json")

def generate_coq_file_repeat_rewrite(n, filename):
    content = """Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.

Section Test.
    Variable eq : (forall (A: Type), (forall (_: A), (forall (_: A), Prop))).
    Variable eq_refl : (forall (B: Type), (forall (x: B), (((eq B) x) x))).
    Variable eq_sym : forall (A : Type) (x y : A), eq A x y -> eq A y x.
    Variable eq_subst : (forall (P: Prop), (forall (Q: Prop), (forall (_: (((eq Prop) P) Q)), (forall (_: Q), P)))).
    Variable app_cong : (forall (A: Type), (forall (B: Type), (forall (f: (forall (_: A), B)), (forall (g: (forall (_: A), B)), (forall (x: A), (forall (y: A), (forall (_: (((eq (forall (_: A), B)) f) g)), (forall (_: (((eq A) x) y)), (((eq B) (f x)) (g y)))))))))).
    Variable eq_trans : (forall (A: Type), (forall (x: A), (forall (y: A), (forall (z: A), (forall (_: (((eq A) x) y)), (forall (_: (((eq A) y) z)), (((eq A) x) z))))))).
    
    Variable nat : Type.
    Variable f : (forall (_: nat), nat).
    Variable g : (forall (_: nat), nat).
    Variable a : nat.
    Variable eq_fa_a : (((eq nat) (f a)) a).

    Instance eq_Equivalence (A : Type) : Equivalence (@eq A) := {
      Equivalence_Reflexive := @eq_refl A;
      Equivalence_Symmetric := @eq_sym A;
      Equivalence_Transitive := @eq_trans A
    }.
    Instance fn_Proper (A : Type) (fn : A -> A) : Proper (eq A ==> eq A) fn.
    Proof.
      intro x. intro y. intro Hxy. 
      exact (app_cong A A fn fn x y (eq_refl (A -> A) fn) Hxy).
    Qed.

    (* Generate the example *)
    Fixpoint repeat_f (n : Datatypes.nat) : nat :=
      match n with
      | 0 => a
      | S n' => f (repeat_f n')
      end.
    Definition gfa (n : Datatypes.nat) : nat := g (repeat_f n).

    Goal eq nat (repeat_f __N__) (a).
    Proof.
      cbn [repeat_f].
      Time (repeat rewrite eq_fa_a).
      apply eq_refl.
    Qed.
End Test.
"""
    content = content.replace("__N__", str(n))

    with open(filename, "w") as f:
        f.write(content)

def generate_coq_file_repeat_setoid_rewrite(n, filename):
    content = """Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.

Section Test.
    Variable eq : (forall (A: Type), (forall (_: A), (forall (_: A), Prop))).
    Variable eq_refl : (forall (B: Type), (forall (x: B), (((eq B) x) x))).
    Variable eq_sym : forall (A : Type) (x y : A), eq A x y -> eq A y x.
    Variable eq_subst : (forall (P: Prop), (forall (Q: Prop), (forall (_: (((eq Prop) P) Q)), (forall (_: Q), P)))).
    Variable app_cong : (forall (A: Type), (forall (B: Type), (forall (f: (forall (_: A), B)), (forall (g: (forall (_: A), B)), (forall (x: A), (forall (y: A), (forall (_: (((eq (forall (_: A), B)) f) g)), (forall (_: (((eq A) x) y)), (((eq B) (f x)) (g y)))))))))).
    Variable eq_trans : (forall (A: Type), (forall (x: A), (forall (y: A), (forall (z: A), (forall (_: (((eq A) x) y)), (forall (_: (((eq A) y) z)), (((eq A) x) z))))))).
    
    Variable nat : Type.
    Variable f : (forall (_: nat), nat).
    Variable g : (forall (_: nat), nat).
    Variable a : nat.
    Variable eq_fa_a : (((eq nat) (f a)) a).

    Instance eq_Equivalence (A : Type) : Equivalence (@eq A) := {
      Equivalence_Reflexive := @eq_refl A;
      Equivalence_Symmetric := @eq_sym A;
      Equivalence_Transitive := @eq_trans A
    }.
    Instance fn_Proper (A : Type) (fn : A -> A) : Proper (eq A ==> eq A) fn.
    Proof.
      intro x. intro y. intro Hxy. 
      exact (app_cong A A fn fn x y (eq_refl (A -> A) fn) Hxy).
    Qed.

    (* Generate the example *)
    Fixpoint repeat_f (n : Datatypes.nat) : nat :=
      match n with
      | 0 => a
      | S n' => f (repeat_f n')
      end.

    Goal eq nat (repeat_f __N__) (a).
    Proof.
      cbn [repeat_f].
      Time (repeat setoid_rewrite eq_fa_a).
      apply eq_refl.
    Qed.
End Test.
"""
    content = content.replace("__N__", str(n))

    with open(filename, "w") as f:
        f.write(content)


def generate_coq_file_rewrite_topdown(n, filename):
    content = """Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.

Section Test.
    Variable eq : (forall (A: Type), (forall (_: A), (forall (_: A), Prop))).
    Variable eq_refl : (forall (B: Type), (forall (x: B), (((eq B) x) x))).
    Variable eq_sym : forall (A : Type) (x y : A), eq A x y -> eq A y x.
    Variable eq_subst : (forall (P: Prop), (forall (Q: Prop), (forall (_: (((eq Prop) P) Q)), (forall (_: Q), P)))).
    Variable app_cong : (forall (A: Type), (forall (B: Type), (forall (f: (forall (_: A), B)), (forall (g: (forall (_: A), B)), (forall (x: A), (forall (y: A), (forall (_: (((eq (forall (_: A), B)) f) g)), (forall (_: (((eq A) x) y)), (((eq B) (f x)) (g y)))))))))).
    Variable eq_trans : (forall (A: Type), (forall (x: A), (forall (y: A), (forall (z: A), (forall (_: (((eq A) x) y)), (forall (_: (((eq A) y) z)), (((eq A) x) z))))))).
    
    Variable nat : Type.
    Variable f : (forall (_: nat), nat).
    Variable g : (forall (_: nat), nat).
    Variable a : nat.
    Variable eq_fa_a : (((eq nat) (f a)) a).

    Instance eq_Equivalence (A : Type) : Equivalence (@eq A) := {
      Equivalence_Reflexive := @eq_refl A;
      Equivalence_Symmetric := @eq_sym A;
      Equivalence_Transitive := @eq_trans A
    }.
    Instance fn_Proper (A : Type) (fn : A -> A) : Proper (eq A ==> eq A) fn.
    Proof.
      intro x. intro y. intro Hxy. 
      exact (app_cong A A fn fn x y (eq_refl (A -> A) fn) Hxy).
    Qed.

    (* Generate the example *)
    Fixpoint repeat_f (n : Datatypes.nat) : nat :=
      match n with
      | 0 => a
      | S n' => f (repeat_f n')
      end.

    Goal eq nat (repeat_f __N__) (a).
    Proof.
      cbn [repeat_f].
      Time (rewrite_strat topdown eq_fa_a).
      apply eq_refl.
    Qed.
End Test.
  
  """
    content = content.replace("__N__", str(n))

    with open(filename, "w") as f:
        f.write(content)

def generate_coq_file_rewrite_bottomup(n, filename):
    content = """Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.

Section Test.
    Variable eq : (forall (A: Type), (forall (_: A), (forall (_: A), Prop))).
    Variable eq_refl : (forall (B: Type), (forall (x: B), (((eq B) x) x))).
    Variable eq_sym : forall (A : Type) (x y : A), eq A x y -> eq A y x.
    Variable eq_subst : (forall (P: Prop), (forall (Q: Prop), (forall (_: (((eq Prop) P) Q)), (forall (_: Q), P)))).
    Variable app_cong : (forall (A: Type), (forall (B: Type), (forall (f: (forall (_: A), B)), (forall (g: (forall (_: A), B)), (forall (x: A), (forall (y: A), (forall (_: (((eq (forall (_: A), B)) f) g)), (forall (_: (((eq A) x) y)), (((eq B) (f x)) (g y)))))))))).
    Variable eq_trans : (forall (A: Type), (forall (x: A), (forall (y: A), (forall (z: A), (forall (_: (((eq A) x) y)), (forall (_: (((eq A) y) z)), (((eq A) x) z))))))).
    
    Variable nat : Type.
    Variable f : (forall (_: nat), nat).
    Variable g : (forall (_: nat), nat).
    Variable a : nat.
    Variable eq_fa_a : (((eq nat) (f a)) a).

    Instance eq_Equivalence (A : Type) : Equivalence (@eq A) := {
      Equivalence_Reflexive := @eq_refl A;
      Equivalence_Symmetric := @eq_sym A;
      Equivalence_Transitive := @eq_trans A
    }.
    Instance fn_Proper (A : Type) (fn : A -> A) : Proper (eq A ==> eq A) fn.
    Proof.
      intro x. intro y. intro Hxy. 
      exact (app_cong A A fn fn x y (eq_refl (A -> A) fn) Hxy).
    Qed.

    (* Generate the example *)
    Fixpoint repeat_f (n : Datatypes.nat) : nat :=
      match n with
      | 0 => a
      | S n' => f (repeat_f n')
      end.

    Goal eq nat (repeat_f __N__) (a).
    Proof.
      cbn [repeat_f].
      Time (rewrite_strat bottomup eq_fa_a).
      apply eq_refl.
    Qed.
End Test.
  
  """
    content = content.replace("__N__", str(n))

    with open(filename, "w") as f:
        f.write(content)

def generate_coq_file_rewrite_bng(n, filename):
    content = """Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.

Section Test.
    Variable eq : (forall (A: Type), (forall (_: A), (forall (_: A), Prop))).
    Variable eq_refl : (forall (B: Type), (forall (x: B), (((eq B) x) x))).
    Variable eq_sym : forall (A : Type) (x y : A), eq A x y -> eq A y x.
    Variable eq_subst : (forall (P: Prop), (forall (Q: Prop), (forall (_: (((eq Prop) P) Q)), (forall (_: Q), P)))).
    Variable app_cong : (forall (A: Type), (forall (B: Type), (forall (f: (forall (_: A), B)), (forall (g: (forall (_: A), B)), (forall (x: A), (forall (y: A), (forall (_: (((eq (forall (_: A), B)) f) g)), (forall (_: (((eq A) x) y)), (((eq B) (f x)) (g y)))))))))).
    Variable eq_trans : (forall (A: Type), (forall (x: A), (forall (y: A), (forall (z: A), (forall (_: (((eq A) x) y)), (forall (_: (((eq A) y) z)), (((eq A) x) z))))))).
    
    Variable nat : Type.
    Variable f : (forall (_: nat), nat).
    Variable g : (forall (_: nat), nat).
    Variable a : nat.
    Variable eq_fa_a : (((eq nat) (f a)) a).

    Instance eq_Equivalence (A : Type) : Equivalence (@eq A) := {
      Equivalence_Reflexive := @eq_refl A;
      Equivalence_Symmetric := @eq_sym A;
      Equivalence_Transitive := @eq_trans A
    }.
    Instance fn_Proper (A : Type) (fn : A -> A) : Proper (eq A ==> eq A) fn.
    Proof.
      intro x. intro y. intro Hxy. 
      exact (app_cong A A fn fn x y (eq_refl (A -> A) fn) Hxy).
    Qed.

    (* Generate the example *)
    Fixpoint repeat_f (n : Datatypes.nat) : nat :=
      match n with
      | 0 => a
      | S n' => f (repeat_f n')
      end.
    Definition gfa (n : Datatypes.nat) : nat := g (repeat_f n).

    Goal eq nat (repeat_f __N__) (a).
    Proof.
      cbn [repeat_f].
      Time (rewrite! eq_fa_a).
      apply eq_refl.
    Qed.
End Test.
"""
    content = content.replace("__N__", str(n))

    with open(filename, "w") as f:
        f.write(content)


def generate_lean_file_rewrite(n, filename):
    """
    Generate a Lean file that applies f to a n times using rewrite.

    Args:
        n (int): Number of nested f applications, i.e., f (f (f ... a)).
        filename (str): Output .lean file path.
    """
    expr = "a"
    for _ in range(n):
        expr = f"f ({expr})"

    content = f"""import Std.Tactic
set_option maxRecDepth 4096

section Test

variable {{A : Type}}
variable (f : A → A) (eq_fa_a : ∀ x : A, f x = x)
variable (a : A)

example : ({expr}) = a := by
  repeat' rw [eq_fa_a]

end Test
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

        args = [exe_path, "--proof=0", "gfa", str(n), "0"]
        start = time.perf_counter()
        subprocess.run(args, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        end = time.perf_counter()
        success = True

        results[key] = {"time_taken": end - start, "success": success}
        save_results(results)
    elif engine == "coqc":
        for method in ["repeatrewrite", "repeatsetoidrewrite", "rewritebottomup", "rewritetopdown", "rewritebng"]:
            if method in ["repeatsetoidrewrite", "repeatrewrite", "rewritebng"] and n > 200:
                print(f"Skipping {method} for n={n}, as it is not supported for large n.")
                continue

            key = f"{engine}_{method}_n{n}"
            results = load_results()
            if key in results:
                print(f"Skipping {key}, already exists in results.")
                continue

            filename = f"test_{method}_n{n}.v"
            if method == "repeatrewrite":
                generate_coq_file_repeat_rewrite(n, filename)
            elif method == "repeatsetoidrewrite":
                generate_coq_file_repeat_setoid_rewrite(n, filename)
            elif method == "rewritebottomup":
                generate_coq_file_rewrite_bottomup(n, filename)
            elif method == "rewritetopdown":
                generate_coq_file_rewrite_topdown(n, filename)
            elif method == "rewritebng":
                generate_coq_file_rewrite_bng(n, filename)

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
    elif engine == "lean":
      key = f"{engine}_n{n}"
      results = load_results()
      if key in results:
          print(f"Skipping {key}, already exists in results.")
          return

      filename = f"test_n{n}.lean"
      generate_lean_file_rewrite(n, filename)
      
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
