import Lean.Elab.Tactic

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
