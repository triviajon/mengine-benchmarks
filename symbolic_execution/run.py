#!/usr/bin/env python3
import sys
import os
import time
import subprocess
import json

RESULTS_FILE_PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)), "results.json")

def generate_coq_file(n, filename):
    content = """Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.

Section A.
    Variable not : Prop -> Prop.
    Variable and : (forall (_: Prop), (forall (_: Prop), Prop)).
    Variable and_conj : (forall (A: Prop), (forall (B: Prop), (forall (_: A), (forall (_: B), ((and A) B))))).
    Variable lambda_extensionality : (forall (A: Type), (forall (B: Type), (forall (f: (forall (_: A), B)), (forall (g: (forall (_: A), B)), (forall (_: (forall (x: A), (((@eq B) (f x)) (g x)))), (((@eq (forall (_: A), B)) f) g)))))).
    Variable nat : Type.
    Variable add : (forall (_: nat), (forall (_: nat), nat)).
    Variable O : nat.
    Variable add_r_O : (forall (n: nat), (((@eq nat) ((add n) O)) n)).
    Variable f : (forall (_: nat), nat).
    Variable g : (forall (_: nat), nat).
    Variable h : (forall (_: nat), (forall (_: nat), nat)).
    Variable positive : Type.
    Variable xI : (forall (_: positive), positive).
    Variable xO : (forall (_: positive), positive).
    Variable xH : positive.
    Variable N : Type.
    Variable N0 : N.
    Variable Z : Type.
    Variable Z0 : Z.
    Variable Zpos : (forall (_: positive), Z).
    Variable Zneg : (forall (_: positive), Z).
    Variable string : Type.
    Variable a : string.
    Variable b : string.
    Variable c : string.
    Variable list : (forall (_: Type), Type).
    Variable list_nil : (forall (A: Type), (list A)).
    Variable list_cons : (forall (A: Type), (forall (_: A), (forall (_: (list A)), (list A)))).
    Variable option : (forall (_: Type), Type).
    Variable option_some : (forall (A: Type), (forall (_: A), (option A))).
    Variable option_none : (forall (A: Type), (option A)).
    Variable word : Type.
    Variable word_of_Z : (forall (_: Z), word).
    Variable word_add : (forall (_: (option word)), (forall (_: (option word)), word)).
    Variable word_sub : (forall (_: (option word)), (forall (_: (option word)), word)).
    Variable byte : Type.
    Variable partial_map : (forall (_: Type), (forall (_: Type), Type)).
    Variable partial_map_empty : (forall (A: Type), (forall (B: Type), ((partial_map A) B))).
    Variable partial_map_get : (forall (A: Type), (forall (B: Type), (forall (_: ((partial_map A) B)), (forall (_: A), (option B))))).
    Variable partial_map_put : (forall (A: Type), (forall (B: Type), (forall (_: ((partial_map A) B)), (forall (_: A), (forall (_: B), ((partial_map A) B)))))).
    Variable partial_map_remove : (forall (A: Type), (forall (B: Type), (forall (_: ((partial_map A) B)), (forall (_: A), (option B))))).
    Variable partial_map_get_put_same : (forall (A: Type), (forall (B: Type), (forall (map: ((partial_map A) B)), (forall (k: A), (forall (v: B), (((@eq (option B)) ((((partial_map_get A) B) (((((partial_map_put A) B) map) k) v)) k)) ((option_some B) v))))))).
    Variable partial_map_get_put_diff : (forall (A: Type), (forall (B: Type), (forall (map: ((partial_map A) B)), (forall (k: A), (forall (v: B), forall (k': A), not (@eq A k k') -> (((@eq (option B)) ((((partial_map_get A) B) (((((partial_map_put A) B) map) k') v)) k)) (((partial_map_get A) B) map k))))))).
    Variable partial_map_put_put_same :
        forall (A B : Type) (map : partial_map A B) (k : A) (v1 v2 : B),
        @eq (partial_map A B) (partial_map_put A B (partial_map_put A B map k v1) k v2)
        (partial_map_put A B map k v2).

    Variable word_add_sub_cancel : forall (v: word), @eq (option word)
        (option_some word (word_sub (option_some word (word_add (option_some word v) (option_some word v))) (option_some word v))) 
        (option_some word v).
    Variable bopname : Type.
    Variable bopname_add : bopname.
    Variable bopname_sub : bopname.
    Variable interp_binop : (forall (_: bopname), (forall (_: (option word)), (forall (_: (option word)), word))).
    Variable binop_add_to_word_add : (forall (w1: (option word)), (forall (w2: (option word)), (((@eq word) (((interp_binop bopname_add) w1) w2)) ((word_add w1) w2)))).
    Variable binop_add_to_word_sub : (forall (w1: (option word)), (forall (w2: (option word)), (((@eq word) (((interp_binop bopname_sub) w1) w2)) ((word_sub w1) w2)))).
    Inductive expr : Type :=
        | expr_literal : Z -> expr
        | expr_var : string -> expr
        | expr_op : bopname -> expr -> expr -> expr.
    Fixpoint eval_expr (me : partial_map word byte) (le : partial_map string word) (e : expr) : option word :=
        match e with
        | expr_literal v => option_some word (word_of_Z v)
        | expr_var x => partial_map_get string word le x
        | expr_op op e1 e2 => option_some word (interp_binop op (eval_expr me le e1) (eval_expr me le e2))
        end.
    Variable cmd : Type.
    Variable cmd_skip : cmd.
    Variable cmd_set : (forall (lhs: string), (forall (rhs: expr), cmd)).
    Variable cmd_unset : (forall (lhs: string), cmd).
    Variable cmd_cond : (forall (condition: expr), (forall (nonzero_branch: cmd), (forall (zero_branch: cmd), cmd))).
    Variable cmd_seq : (forall (s1: cmd), (forall (s2: cmd), cmd)).
    Variable cmd_input : forall (lhs: string), cmd.
    Variable cmd_output : forall (arg: string), cmd.
    Variable IOEvent : Type.
    Variable IOEvent_IN : word -> IOEvent.
    Variable IOEvent_OUT : word -> IOEvent.      
    Variable exec : cmd ->
        list IOEvent ->
        partial_map word byte ->
        partial_map string word ->
        (list IOEvent -> partial_map word byte -> partial_map string word -> Prop) -> Prop.
    Variable exec_skip : forall (t : list IOEvent) (m : partial_map word byte) (l : partial_map string word)
        (post : list IOEvent -> partial_map word byte -> partial_map string word -> Prop),
        post t m l -> exec cmd_skip t m l post.
    Variable exec_set : forall (t : list IOEvent) (x : string) (e : expr) (m : partial_map word byte)
        (l : partial_map string word)
        (post : list IOEvent -> partial_map word byte -> partial_map string word -> Prop) (v : word),
        @eq (option word) (eval_expr m l e) (option_some word v) ->
        post t m (partial_map_put string word l x v) ->
        exec (cmd_set x e) t m l post.
    Variable exec_seq : forall (t : list IOEvent) (c1 c2 : cmd) (m : partial_map word byte)
        (l : partial_map string word)
        (post : list IOEvent -> partial_map word byte -> partial_map string word ->Prop),
        exec c1 t m l (fun (t' : list IOEvent) (m' : partial_map word byte) (l' : partial_map string word) => exec c2 t' m' l' post) ->
        exec (cmd_seq c1 c2) t m l post.
     Variable exec_input : forall (t : list IOEvent) (lhs : string) (m : partial_map word byte)
        (l : partial_map string word)
        (post : list IOEvent -> partial_map word byte -> partial_map string word -> Prop),
        (forall v : word, post (list_cons IOEvent (IOEvent_IN v) t) m (partial_map_put string word l lhs v)) ->
        exec (cmd_input lhs) t m l post.
    Variable word_add_0_r : forall x : word,
        @eq word (word_add (option_some word x) (option_some word (word_of_Z Z0))) x.
    Variable ex : forall (A: Type), forall (P: A -> Prop), Prop.
    Variable ex_intro : forall (A: Type), forall (P: A -> Prop), 
        forall (x: A), P x -> ex A P.
    Variable not_eq_string_b_a : (not (((@eq string) b) a)).

    Fixpoint repeated_cmds (n : Datatypes.nat) (t x : string) : cmd :=
        match n with
        | 0 => cmd_skip
        | S n' =>
            cmd_seq
            (cmd_set t (expr_op bopname_add (expr_var t) (expr_var t)))
            (cmd_seq
                (cmd_set t (expr_op bopname_sub (expr_var t) (expr_var x)))
                (repeated_cmds n' t x))
        end.
  
    Definition generated_cmd (n : Datatypes.nat) (t x : string) : cmd :=
        cmd_seq (cmd_input x) (cmd_seq (cmd_set t (expr_var x)) (repeated_cmds n t x)).

    Ltac solve_eq_by_rewriting :=
    let step :=
        first [
        rewrite partial_map_get_put_same
        | rewrite partial_map_get_put_diff; apply not_eq_string_b_a
        | rewrite binop_add_to_word_sub
        | rewrite binop_add_to_word_add
        ]
    in
    simpl;
    repeat step;
    apply eq_refl.

    Ltac repeat_exec :=
        repeat match goal with
        | [ |- exec (cmd_seq _ _) _ _ _ _ ] =>
            apply exec_seq
        | [ |- exec (cmd_set _ _) _ _ _ _ ] =>
            try (rewrite partial_map_put_put_same); eapply exec_set; try solve_eq_by_rewriting
        | [ |- exec cmd_skip _ _ _ _ ] =>
            apply exec_skip
        end.

    Goal let n := __N__ in let t := (list_nil IOEvent) in
        forall (m : partial_map word byte) (l : partial_map string word),
            exec (generated_cmd n a b) t m l 
            (fun (t' : list IOEvent) (m' : partial_map word byte) (l' : partial_map string word) =>
                and (@eq (partial_map word byte) m' m)
                    (ex word (fun v : word =>
                        and (@eq (list IOEvent) t' (list_cons IOEvent (IOEvent_IN v) (list_nil IOEvent)))
                            (@eq (option word) (partial_map_get string word l' a) 
                                              (option_some word v))))).
    Proof.
        unfold generated_cmd;
        cbn [repeated_cmds];
        intros;
        apply exec_seq;
        apply exec_input;
        intros.
        Time repeat_exec.
    Admitted.
End A.
"""
    content = content.replace("__N__", str(n))

    with open(filename, "w") as f:
        f.write(content)

def generate_lean_file(n, filename):
    content = """import Lean.Elab.Tactic

namespace Eval

-- variable (String : Type)
-- variable (a b c : String)

section

inductive byte where

inductive word where

def word_of_Int : Int → word := sorry
def word_add : Option word → Option word → word := sorry
def word_sub : Option word → Option word → word := sorry

structure partial_map (A B : Type) where
  (fn : A -> Option B)

def partial_map_empty (A B : Type) : partial_map A B :=
  { fn := fun _ => none }

def partial_map_get {A B : Type} (m : partial_map A B) (k : A) : Option B :=
  m.fn k

def partial_map_put {A B : Type} [DecidableEq A] (m : partial_map A B) (k : A) (v : B) : partial_map A B :=
  { fn := fun x => if x = k then some v else m.fn x }

def partial_map_remove {A B : Type} [DecidableEq A] (m : partial_map A B) (k : A) : partial_map A B :=
  { fn := fun x => if x = k then none else m.fn x }

theorem partial_map_get_put_same {A B : Type} [DecidableEq A] (m : partial_map A B) (k : A) (v : B) :
  partial_map_get (partial_map_put m k v) k = some v := by
  simp [partial_map_get, partial_map_put]
end

theorem partial_map_get_put_diff {A B : Type} [DecidableEq A] (m : partial_map A B) (k k' : A) (v : B)
  (h : k ≠ k') :
  partial_map_get (partial_map_put m k' v) k = partial_map_get m k :=
  if_neg h

theorem partial_map_put_put_same {A B : Type} [DecidableEq A] (m : partial_map A B) (k : A) (v1 v2 : B) :
  partial_map_put (partial_map_put m k v1) k v2 = partial_map_put m k v2 := by
  sorry

variable (word_add_sub_cancel :
  forall v : word,
    @some word (word_sub (@some word (word_add (@some word v) (@some word v))) (@some word v))
      = @some word v)

inductive Bopname : Type where
  | add
  | sub

def interp_binop : Bopname → Option word → Option word → word := sorry

theorem binop_add_to_word_add :
  forall w1 w2, interp_binop Bopname.add w1 w2 = word_add w1 w2 := sorry
theorem binop_add_to_word_sub :
  forall w1 w2, interp_binop Bopname.sub w1 w2 = word_sub w1 w2 := sorry

inductive Expr : Type where
  | literal (v: Int)
  | var (x: String)
  | op (bop : Bopname) (e1 e2 : Expr)

def eval_expr (me : partial_map word byte) (le : partial_map String word) (e : Expr) : Option word :=
  match e with
  | Expr.literal v => @some word (word_of_Int v)
  | Expr.var x => @partial_map_get String word le x
  | Expr.op bop e1 e2 => some (interp_binop bop (eval_expr me le e1) (eval_expr me le e2))
  inductive cmd : Type where
    | skip : cmd
    | set : String -> Expr -> cmd
    | unset : String -> cmd
    | cond : Expr -> cmd -> cmd -> cmd
    | seq : cmd -> cmd -> cmd
    | input : String -> cmd
    | output : String -> cmd

inductive IOEvent : Type
| IN : word → IOEvent
| OUT : word → IOEvent

inductive exec : cmd -> List IOEvent -> partial_map word byte -> partial_map String word ->
  (List IOEvent -> partial_map word byte -> partial_map String word -> Prop) -> Prop
| skip :
    forall t m l post,
      post t m l ->
      exec cmd.skip t m l post

| set :
    forall t x e m l post v,
      eval_expr m l e = some v ->
      post t m (partial_map_put l x v) ->
      exec (cmd.set x e) t m l post

| input :
    forall t lhs m l post [DecidableEq String],
      (forall v, post (IOEvent.IN v :: t) m (partial_map_put l lhs v)) ->
      exec (cmd.input lhs) t m l post

| seq : forall c1 c2 t m l post mid,
    exec c1 t m l mid ->
    (forall t' m' l', mid t' m' l' -> exec c2 t' m' l' post) ->
    exec (cmd.seq c1 c2) t m l post

theorem exec_seq_cps :
  ∀ (t : List IOEvent) (c1 c2 : cmd) (m : partial_map word byte) (l : partial_map String word)
    (post : List IOEvent → partial_map word byte → partial_map String word → Prop),
    exec c1 t m l
      (λ (t' : List IOEvent) (m' : partial_map word byte) (l' : partial_map String word) =>
        exec c2 t' m' l' post) →
    exec (cmd.seq c1 c2) t m l post := sorry

variable (word_add_0_r : forall x : word, word_add (some x) (some (word_of_Int 0)) = x)
variable (ex : forall A : Type, (A -> Prop) -> Prop)
variable (ex_intro : forall A (P : A -> Prop) (x : A), P x -> ex A P)

def repeated_cmds : Nat -> String -> String -> cmd
  | 0, _, _ => cmd.skip
  | (n + 1), t, x =>
    cmd.seq
      (cmd.set t (Expr.op Bopname.add (Expr.var t) (Expr.var t)))
      (cmd.seq
        (cmd.set t (Expr.op Bopname.sub (Expr.var t) (Expr.var x)))
        (repeated_cmds n t x)
      )

def generated_cmd (n : Nat) (t x : String) : cmd :=
  cmd.seq (cmd.input x) (cmd.seq (cmd.set t (Expr.var x))
  (@repeated_cmds n t x))

macro "solve_eq_by_rewriting" : tactic =>
  `(tactic|
    repeat first
      | rw [partial_map_get_put_same]
      | rw [partial_map_get_put_diff]; apply not_eq_string_b_a
      | rw [binop_add_to_word_sub]
      | rw [binop_add_to_word_add]
  )


open Lean Elab Tactic

-- n >= 7 causes us to hit maxHeartbeats unless we disable the limit
set_option maxHeartbeats 0

elab "solve_repeated" : tactic => do
  evalTactic (← `(tactic| apply exec_seq_cps))
  evalTactic (← `(tactic| apply exec.set))
  evalTactic (← `(tactic| simp [eval_expr]))
  evalTactic (← `(tactic| solve_eq_by_rewriting))

theorem generated_cmd_correct :
  let n := __N__;
  let t := @List.nil IOEvent;
  forall m l,
    exec (generated_cmd n "a" "b") t m l
      (fun t' m' l' =>
        And (m' = m)
          (ex word (fun v =>
            And (t' = List.cons (IOEvent.IN v) (@List.nil IOEvent))
                (partial_map_get l' "a" = some v)))) := by
  simp
  intros m l
  dsimp [generated_cmd, repeated_cmds]
  apply exec_seq_cps
  apply exec.input
  intros v
  repeat solve_repeated
  apply exec.skip
  -- don't care about solving post-condition for now
  sorry

"""
    content = content.replace("__N__", str(n))
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
            print(f"Skipping {key} as it has already been run.")
            return
        args = [exe_path, "--proof=0", "sym", str(n)]
        start = time.perf_counter()
        subprocess.run(args, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        end = time.perf_counter()
        success = True

        results = load_results()
        results[key] = {"time_taken": end - start, "success": success}
        save_results(results)
    elif engine == "coqc":
          key = f"{engine}_n{n}"
          results = load_results() 
          if key in results:
              print(f"Skipping {key} as it has already been run.")
              return
          filename = f"test_n{n}.v"
          generate_coq_file(n, filename)

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
      key = f"{engine}_n{n}"
      results = load_results()
      if key in results:
          print(f"Skipping {key} as it has already been run.")
          return
      filename = f"test_n{n}.lean"
      generate_lean_file(n, filename)
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
