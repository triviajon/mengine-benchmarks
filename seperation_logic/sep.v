Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List.

Context { partial_map : (forall (_: Type), (forall (_: Type), Type)) }.
Context { partial_map_empty : (forall (A: Type), (forall (B: Type), ((partial_map A) B))) }.
Context { partial_map_get : (forall (A: Type), (forall (B: Type), (forall (_: ((partial_map A) B)), (forall (_: A), (option B))))) }.
Context { partial_map_put : (forall (A: Type), (forall (B: Type), (forall (_: ((partial_map A) B)), (forall (_: A), (forall (_: B), ((partial_map A) B)))))) }.
Context { partial_map_remove : (forall (A: Type), (forall (B: Type), (forall (_: ((partial_map A) B)), (forall (_: A), (option B))))) }.

Context { partial_map_fold : forall (A B : Type), 
    forall (R: Type), (R -> A -> B -> R) -> R -> (partial_map A B) -> R
}.

Context { partial_map_get_put_same : (forall (A: Type), (forall (B: Type), (forall (map: ((partial_map A) B)), (forall (k: A), (forall (v: B), (((@eq (option B)) ((((partial_map_get A) B) (((((partial_map_put A) B) map) k) v)) k)) ((@Some B) v))))))) }.
Context { partial_map_get_put_diff : (forall (A: Type), (forall (B: Type), (forall (map: ((partial_map A) B)), (forall (k: A), (forall (v: B), forall (k': A), not (@eq A k k') -> (((@eq (option B)) ((((partial_map_get A) B) (((((partial_map_put A) B) map) k') v)) k)) (((partial_map_get A) B) map k))))))) }.
Context { partial_map_put_put_same :
    forall (A B : Type) (map : partial_map A B) (k : A) (v1 v2 : B),
    @eq (partial_map A B) (partial_map_put A B (partial_map_put A B map k v1) k v2)
    (partial_map_put A B map k v2) }.

Definition putmany { A B : Type }: (partial_map A B) -> (partial_map A B) -> (partial_map A B) := 
    partial_map_fold A B (partial_map A B) (partial_map_put A B).
Definition disjoint { A B : Type } (a b : partial_map A B) :=
    forall k v1 v2, partial_map_get A B a k = Some v1 -> partial_map_get A B b k = Some v2 -> False.
Definition split {A B : Type} (m m1 m2 : partial_map A B) := m = (putmany m1 m2) /\ disjoint m1 m2.

Lemma putmany_comm {A B}
: forall x y : partial_map A B,
disjoint x y -> putmany x y = putmany y
x. Admitted.

Definition impl1 {T: Type} (P Q: T -> Prop) := forall x, P x -> Q x.
Definition iff1 {T: Type} (P Q: T -> Prop) := forall x, P x <-> Q x.
Definition and1 {T: Type} (P Q: T -> Prop) := fun x => P x /\ Q x.
Definition or1 {T: Type} (P Q: T -> Prop) := fun x => P x \/ Q x.
Definition ex1 {A B} (P : A -> B -> Prop) := fun (b:B) => exists a:A, P a b.

Global Instance Transitive_impl1 T : Transitive (@impl1 T). firstorder idtac. Qed.
Global Instance Reflexive_impl1 T : Reflexive (@impl1 T). firstorder idtac. Qed.
Global Instance Proper_impl1_impl1 T : Proper (Basics.flip impl1 ==> impl1 ==> Basics.impl) (@impl1 T). firstorder idtac. Qed.
Global Instance subrelation_iff1_impl1 T : subrelation (@iff1 T) (@impl1 T). firstorder idtac. Qed.
Global Instance Equivalence_iff1 T : Equivalence (@iff1 T). firstorder idtac. Qed.
Global Instance Proper_iff1_iff1 T : Proper (iff1 ==> iff1 ==> iff) (@iff1 T). firstorder idtac. Qed.
Global Instance Proper_iff1_impl1 T : Proper (Basics.flip impl1 ==> impl1 ==> Basics.impl) (@impl1 T). firstorder idtac. Qed.
Global Instance Proper_impl1_iff1 T : Proper (iff1 ==> iff1 ==> iff) (@impl1 T). firstorder idtac. Qed.
Global Instance Proper_ex1_iff1 A B : Proper (pointwise_relation _ iff1 ==> iff1) (@ex1 A B). firstorder idtac. Qed.
Global Instance Proper_ex1_impl1 A B : Proper (pointwise_relation _ impl1 ==> impl1) (@ex1 A B). firstorder idtac. Qed.
Global Instance iff1_rewrite_relation T : RewriteRelation (@iff1 T) := {}.

Definition emp {A B : Type} (P : Prop) := fun m : (partial_map A B) => m = (partial_map_empty A B) /\ P.
Definition sep {A B : Type} (p q : (partial_map A B) -> Prop) m :=
    exists mp mq, split m mp mq /\ p mp /\ q mq.
Definition ptsto {A B : Type} k v := fun m : (partial_map A B) => m = (partial_map_put A B) (partial_map_empty A B) k v.
Definition read {A B : Type} k (P : B -> (partial_map A B) -> Prop) := (ex1 (fun v => sep (ptsto k v) (P v))).

Lemma sep_cancel_l {A B} (P Q R: partial_map A B -> Prop)
: iff1 P Q -> iff1 (sep P R) (sep Q R). Admitted.

Lemma sep_cancel_r {A B} (P Q R: partial_map A B -> Prop)
: iff1 Q R -> iff1 (sep P Q) (sep P R). Admitted.

Infix "*" := sep (at level 40, left associativity).

Ltac t :=
repeat match goal with
| _ => progress subst
| H:_ /\ _ |- _ => destruct H
| H:exists _, _ |- _ => destruct H
(* | H:disjoint (putmany _ _) _ |- _ => eapply disjoint_putmany_l in H; destruct H
| H:disjoint _ (putmany _ _) |- _ => eapply disjoint_putmany_r in H; destruct H *)
| _ => progress intuition idtac
end.

Lemma disjoint_comm {A B}
: forall m1 m2 : partial_map A B,
disjoint m1 m2 <-> disjoint m2 m1. Admitted.

Lemma sep_comm {A B: Type} (p q: partial_map A B -> Prop) : iff1 (p*q) (q*p).
Proof. cbv [iff1 sep split]. t; exists x1, x0;
eauto 10 using putmany_comm, (fun m1 m2 => proj2 (disjoint_comm m1 m2)). Qed.
Lemma sep_assoc {A B: Type} (p q r: partial_map A B -> Prop) : iff1 ((p*q)*r) (p*(q*r)).
Proof. Admitted.
    
(* 
Ltac cancel_step := once (
      let RHS := lazymatch goal with |- iff1 _ (seps ?RHS) => RHS end in
      let jy := index_and_element_of RHS in (* <-- multi-success! *)
      let j := lazymatch jy with (?i, _) => i end in
      let y := lazymatch jy with (_, ?y) => y end in
      assert_fails (has_evar y); (* <-- different from ecancel_step *)
      let LHS := lazymatch goal with |- Lift1Prop.iff1 (seps ?LHS) _ => LHS end in
      let i := find_constr_eq LHS y in (* <-- different from ecancel_step *)
      cancel_seps_at_indices i j; [exact eq_refl|]). (* already unified using constr_eq *)
 *)

 Ltac pick_leaf t :=
 match t with
 | @sep _ _ ?a ?b => pick_leaf a
 | _ => t
 end.

 Ltac find_subexpr_eq lhs y :=
 lazymatch lhs with
 | @sep _ _ ?a ?b =>
     idtac "searching left in" a;
     first
       [ find_subexpr_eq a y
       | idtac "searching right in" b; find_subexpr_eq b y ]
 | ?z =>
     idtac "trying to match" z "with" y;
     constr_eq z y;
     idtac "match succeeded!";
     constr:(z)
 end.



Ltac cancel_subexprs z y :=
  repeat (
    lazymatch goal with
    | |- iff1 (sep ?a ?b) _ =>
        first [constr_eq a z | constr_eq b z; symmetry; apply sep_comm];
        change (sep z ?rest) with (z * rest)
    | |- iff1 _ (sep ?a ?b) =>
        first [constr_eq a y | constr_eq b y; symmetry; apply sep_comm];
        change (sep y ?rest) with (y * rest)
    end
  );
  apply sep_cancel_l; exact eq_refl.

Ltac cancel_step_tree :=
  once (
    let RHS := lazymatch goal with |- iff1 _ ?rhs => rhs end in
    let y := (pick_leaf RHS) in
    assert_fails (has_evar y);
    let LHS := lazymatch goal with |- iff1 ?lhs _ => lhs end in
    idtac "LHS:" LHS;
    let y := pick_leaf RHS in
    idtac "picked:" y;
    let z := find_subexpr_eq LHS y in
    idtac "found z:" z;
    cancel_subexprs z y;
    exact eq_refl
  ).

 Goal forall (A B: Type) (p q r: partial_map A B -> Prop), iff1 (p*q*r) (r*q*p).
intros.
Abort.


