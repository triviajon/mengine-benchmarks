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

Fixpoint seps {A B : Type} (xs : list ((partial_map A B) -> Prop)) : (partial_map A B) -> Prop :=
    match xs with
    | cons x nil => x
    | cons x xs => sep x (seps xs)
    | nil => emp True
end.

Ltac index_and_element_of xs :=
multimatch xs with
| cons ?x _ => constr:((0%nat, x))
| cons _ ?xs =>
    let r := index_and_element_of xs in
    multimatch r with
    | (?i, ?y) => constr:((S i, y))
    end
end.  

Ltac find_constr_eq xs y :=
match xs with
| cons ?x _ => constr:(ltac:(constr_eq x y; exact 0%nat))
| cons _ ?xs => let i := find_constr_eq xs y in constr:(S i)
end.

Fixpoint nth {A B : Type} (n : nat) (xs : list ((partial_map A B) -> Prop)) : (partial_map A B) -> Prop :=
match n, xs with
| O, cons x _ => x
| S n', cons _ xs' => nth n' xs'
| _, _ => emp True
end.

Fixpoint remove_nth {A B : Type} (n : nat) (xs : list ((partial_map A B) -> Prop)) : list ((partial_map A B) -> Prop) :=
match n, xs with
| O, cons _ xs' => xs'
| S n', cons x xs' => cons x (remove_nth n' xs')
| _, _ => xs
end.

Fixpoint firstn {A B : Type} (n : nat) (xs : list ((partial_map A B) -> Prop)) : list ((partial_map A B) -> Prop) :=
match n, xs with
| O, _ => nil
| S n', cons x xs' => cons x (firstn n' xs')
| _, _ => nil
end.

Fixpoint skipn {A B : Type} (n : nat) (xs : list ((partial_map A B) -> Prop)) : list ((partial_map A B) -> Prop) :=
match n, xs with
| O, _ => xs
| S n', cons _ xs' => skipn n' xs'
| _, nil => nil
end.

Definition hd {A B : Type} (default : (partial_map A B) -> Prop) (xs : list ((partial_map A B) -> Prop)) : (partial_map A B) -> Prop :=
match xs with
| cons x _ => x
| nil => default
end.

Definition tl {A B : Type} (xs : list ((partial_map A B) -> Prop)) : list ((partial_map A B) -> Prop) :=
match xs with
| cons _ xs' => xs'
| nil => nil
end.


Lemma cancel_seps_at_indices {A B : Type} i j xs ys
    (Hij : nth i xs = nth j ys)
    (Hrest : iff1 (seps (remove_nth i xs)) (seps (remove_nth j ys)))
: iff1 (@seps A B xs) (@seps A B ys).
Proof. Admitted.

Ltac cancel_seps_at_indices i j :=
lazymatch goal with
| |- iff1 (seps ?LHS) (seps ?RHS) =>
    simple refine (cancel_seps_at_indices i j LHS RHS _ _);
    cbv [firstn skipn app hd tl]
end.

Module Tree.
    Inductive Tree(A: Type): Type :=
    | Leaf(a: A)
    | Node(left right: Tree A).
    Arguments Leaf {A} _.
    Arguments Node {A} _ _.
    Section Interp.
      Context {A B: Type}.
      Context (interp_Leaf: A -> B).
      Context (interp_Node: B -> B -> B).
      Fixpoint interp(t: Tree A): B :=
        match t with
        | Leaf a => interp_Leaf a
        | Node t1 t2 => interp_Node (interp t1) (interp t2)
        end.
    End Interp.
  
    Definition flatten{A: Type}: Tree A -> list A := interp (fun a => cons a nil) (@app A).
  
    Section WithMap.
      Context {key value : Type}.
      Context {key_eqb: key -> key -> bool}.
  
      Definition to_sep: Tree ((partial_map key value) -> Prop) -> (partial_map key value) -> Prop := interp (fun x => x) sep.
  
      Lemma flatten_iff1_to_sep(t : Tree.Tree ((partial_map key value) -> Prop)):
        iff1 (seps (flatten t)) (to_sep t).
      Admitted.

      Lemma iff1_to_sep_of_iff1_flatten(LHS RHS : Tree ((partial_map key value) -> Prop)):
        iff1 (seps (flatten LHS)) (seps (flatten RHS)) ->
        iff1 (to_sep LHS) (to_sep RHS).
      Proof. rewrite! flatten_iff1_to_sep. exact id. Qed.
  
      Lemma impl1_to_sep_of_impl1_flatten(LHS RHS : Tree ((partial_map key value) -> Prop)):
        impl1 (seps (flatten LHS)) (seps (flatten RHS)) ->
        impl1 (to_sep LHS) (to_sep RHS).
      Proof. rewrite! flatten_iff1_to_sep. exact id. Qed.
  
      Lemma flatten_to_sep_with_and(t : Tree.Tree ((partial_map key value) -> Prop))(m: (partial_map key value))(C: Prop):
        seps (flatten t) m /\ C -> to_sep t m /\ C.
      Proof.
        intros (H & HC). refine (conj _ HC). eapply flatten_iff1_to_sep. exact H.
      Qed.
    End WithMap.
  End Tree.

Ltac reify e :=
  lazymatch e with
  | @sep ?key ?value ?map ?a ?b =>
    let a := reify a in
    let b := reify b in
    uconstr:(@Tree.Node (map -> Prop) a b)
  | ?a => uconstr:(Tree.Leaf a)
  end.

Ltac reify_goal :=
  lazymatch goal with
  | |- iff1 ?LHS ?RHS =>
    let LHS := reify LHS in
    let RHS := reify RHS in
    change (iff1 (Tree.to_sep LHS) (Tree.to_sep RHS));
    eapply Tree.iff1_to_sep_of_iff1_flatten
  | |- impl1 ?LHS ?RHS =>
    let LHS := reify LHS in
    let RHS := reify RHS in
    change (impl1 (Tree.to_sep LHS) (Tree.to_sep RHS));
    eapply Tree.impl1_to_sep_of_impl1_flatten
  end;
  cbv [Tree.flatten Tree.interp app].

Ltac cancel_step := once (
    let RHS := lazymatch goal with |- iff1 _ (seps ?RHS) => RHS end in
    let jy := index_and_element_of RHS in (* <-- multi-success! *)
    let j := lazymatch jy with (?i, _) => i end in
    let y := lazymatch jy with (_, ?y) => y end in
    assert_fails (has_evar y); (* <-- different from ecancel_step *)
    let LHS := lazymatch goal with |- iff1 (seps ?LHS) _ => LHS end in
    let i := find_constr_eq LHS y in (* <-- different from ecancel_step *)
    cancel_seps_at_indices i j; [exact eq_refl|]). (* already unified using constr_eq *)

Ltac cancel_done :=
lazymatch goal with
| |- iff1 (seps (cons _ nil)) _ => idtac
| |- iff1 _ (seps (cons _ nil )) => idtac
| |- ?g => assert_fails (has_evar g)
end;
cbv [seps].

Ltac cancel_seps :=
repeat cancel_step;
(* repeat cancel_emp_l;
repeat cancel_emp_r;
repeat cancel_emp_impl; *)
try solve [ cancel_done ].
  

(* Ltac cancel := reify_goal; repeat (cancel_step; cbv [nth remove_nth]). *)
Ltac cancel := reify_goal; cancel_seps.

(* Model memory as a map from nat -> nat. *)
Definition gen_ptsto_goal {A B : Type} (ps : list ((partial_map A B) -> Prop)) (R : list ((partial_map A B) -> Prop)) :=
  iff1 (seps (ps ++ R)) (seps (rev ps ++ R)).

Fixpoint gen_ptsto_list (n : nat) : list ((partial_map nat nat) -> Prop) :=
match n with
| O => nil
| S n' => ptsto n n :: gen_ptsto_list n'
end.

Goal gen_ptsto_goal (gen_ptsto_list 2) nil.
Proof. cbv [gen_ptsto_goal gen_ptsto_list rev].
  reify_goal. 
  cancel_step.
  
  
  cancel. reflexivity. simpl.
    cancel.
Time (cancel; reflexivity). Qed.


Goal 
    forall (a_addr a b_addr b c_addr c: nat) R, 
    let a_mem_frag_pred := ptsto a_addr a in
    let b_mem_frag_pred := ptsto b_addr b in
    let c_mem_frag_pred := ptsto c_addr c in
    iff1
        (seps (a_mem_frag_pred :: b_mem_frag_pred :: c_mem_frag_pred :: R))
        (seps (c_mem_frag_pred :: b_mem_frag_pred :: a_mem_frag_pred :: R)).
Proof.
    intros.
    cancel.
    reflexivity.