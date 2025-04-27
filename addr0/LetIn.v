Require Import Coq.Setoids.Setoid.
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
  
End Test.