Require Import Coq.Setoids.Setoid.
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