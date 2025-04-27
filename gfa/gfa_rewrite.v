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

    Goal eq nat (gfa __N__) (g a).
    Proof.
      unfold gfa. cbn [repeat_f].
      Time (repeat rewrite eq_fa_a).
      apply eq_refl.
    Qed.
End Test.