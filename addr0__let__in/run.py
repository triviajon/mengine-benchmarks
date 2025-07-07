#!/usr/bin/env python3
import sys
import os
import time
import subprocess
import json

RESULTS_FILE_PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)), "results.json")

def generate_coq_file_let__in(n, filename):
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
  Variable v0 : nat.
  Variable O : nat.
  Variable add : nat -> nat -> nat.
  Variable add_r_O : (forall (n: nat), (((eq nat) ((add n) O)) n)).

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
  Instance fn2_Proper (A : Type) (fn : A -> A -> A) : Proper (eq A ==> eq A ==> eq A) fn.
  Proof.
    intro x1. intro x2. intro Hx.
    intro y1. intro y2. intro Hy.
    apply app_cong; auto.
  Qed.

  Goal exists v', eq nat (
    __LETS__
    ) v'.
  Proof.
    eexists.
    Time repeat rewrite add_r_O.
    apply eq_refl.
  Qed.
  
End Test.
"""
    lines = []
    for i in range(1, n + 1):
        vprev = "v0" if i == 1 else f"v{i-1}"
        lines.append(f"  let v{i} := add (add {vprev} {vprev}) O in")
    lines.append(f"  add (add v{n} v{n}) O")
    generated = "\n".join(lines)
    content = content.replace("__LETS__", generated)

    with open(filename, "w") as f:
        f.write(content)

def generate_coq_file_LetIn(n, filename):
    content = """Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.

Local Parameter eq : (forall (A: Type), (forall (_: A), (forall (_: A), Prop))).
Local Parameter eq_refl : (forall (B: Type), (forall (x: B), (((eq B) x) x))).
Local Parameter eq_sym : forall (A : Type) (x y : A), eq A x y -> eq A y x.
Local Parameter eq_subst : (forall (P: Prop), (forall (Q: Prop), (forall (_: (((eq Prop) P) Q)), (forall (_: Q), P)))).
Local Parameter app_cong : (forall (A: Type), (forall (B: Type), (forall (f: (forall (_: A), B)), (forall (g: (forall (_: A), B)), (forall (x: A), (forall (y: A), (forall (_: (((eq (forall (_: A), B)) f) g)), (forall (_: (((eq A) x) y)), (((eq B) (f x)) (g y)))))))))).
Local Parameter eq_trans : (forall (A: Type), (forall (x: A), (forall (y: A), (forall (z: A), (forall (_: (((eq A) x) y)), (forall (_: (((eq A) y) z)), (((eq A) x) z))))))).
Local Parameter lambda_extensionality : (forall (A: Type), (forall (B: Type), (forall (f: (forall (_: A), B)), (forall (g: (forall (_: A), B)), (forall (_: (forall (x: A), (((eq B) (f x)) (g x)))), (((eq (forall (_: A), B)) f) g)))))).

Module Type LetInT.
  Parameter Let_In : forall {A P} (x : A) (f : forall a : A, P a), P x.
  Axiom Let_In_def : @Let_In = fun A P x f => let y := x in f y.
  (*
  Global Strategy 100 [Let_In].
  Hint Opaque Let_In : rewrite.
  *)
  Reserved Notation "'dlet_nd' x .. y := v 'in' f"
          (at level 200, x binder, y binder, f at level 200, format "'dlet_nd'  x .. y  :=  v  'in' '//' f").
  Reserved Notation "'dlet' x .. y := v 'in' f"
          (at level 200, x binder, y binder, f at level 200, format "'dlet'  x .. y  :=  v  'in' '//' f").
  Notation "'dlet_nd' x .. y := v 'in' f" := (Let_In (P:=fun _ => _) v (fun x => .. (fun y => f) .. )) (only parsing).
  Notation "'dlet' x .. y := v 'in' f" := (Let_In v (fun x => .. (fun y => f) .. )).
  Axiom Let_In_nd_Proper : forall {A P},
      Proper ((@eq A) ==> pointwise_relation _ (@eq P) ==> (@eq P)) (@Let_In A (fun _ => P)).
  Hint Extern 0 (Proper _ (@Let_In _ _)) => simple apply @Let_In_nd_Proper : typeclass_instances.
End LetInT.

Module Export LetIn : LetInT.
  Definition Let_In {A P} (x : A) (f : forall a : A, P a) : P x
    := let y := x in f y.
  Lemma Let_In_def : @Let_In = fun A P x f => let y := x in f y.
  Proof. reflexivity. Qed.
  Global Strategy 100 [Let_In].
  Hint Opaque Let_In : rewrite.
  Global Instance Let_In_nd_Proper {A P}
    : Proper ((@eq A) ==> pointwise_relation _ (@eq P) ==> (@eq P)) (@Let_In A (fun _ => P)).
  Proof. cbv; intros; subst. apply app_cong. apply lambda_extensionality. exact H0. exact H. Qed.
End LetIn.


Section Test.
  Local Parameter nat : Type.
  Local Parameter v0 : nat.
  Local Parameter O : nat.
  Local Parameter add : nat -> nat -> nat.
  Local Parameter add_r_O : (forall (n: nat), (((eq nat) ((add n) O)) n)).

  (* The following represents a let ... in binder expressed as a definition instead of 
    using the built-in Coq let ... in notation, to block the default Coq behavior. *)    
  Instance eq_Equivalence (A : Type) : Equivalence (@eq A) := {
    Equivalence_Reflexive := @eq_refl A;
    Equivalence_Symmetric := @eq_sym A;
    Equivalence_Transitive := @eq_trans A
  }.

  Goal exists v', eq nat (
    __LETS__
    ) v'.
  Proof.
    eexists.
    Time setoid_rewrite add_r_O.
    apply eq_refl.
  Qed.
  
End Test."""
    lines = []
    for i in range(1, n + 1):
        vprev = "v0" if i == 1 else f"v{i-1}"
        lines.append(f"  let v{i} := add (add {vprev} {vprev}) O in")
    lines.append(f"  add (add v{n} v{n}) O")
    generated = "\n".join(lines)
    content = content.replace("__LETS__", generated)

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

        args = [exe_path, "--proof=0", "addr0", "native", str(n)]
        start = time.perf_counter()
        subprocess.run(args, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        end = time.perf_counter()
        success = True

        results[key] = {"time_taken": end - start, "success": success}
        save_results(results)
    elif engine == "coqc":
        for method in ["letin", "LetInConst"]:
            key = f"{engine}_{method}_n{n}"
            results = load_results()
            if key in results:
                print(f"Skipping {key}, already exists in results.")
                continue


            filename = f"test_{method}_n{n}.v"
            if method == "letin":
                generate_coq_file_let__in(n, filename)
            else:
                generate_coq_file_LetIn(n, filename)
                
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
