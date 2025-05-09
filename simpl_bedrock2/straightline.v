Require Import Coq.Setoids.Setoid.
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
    (* Variable \0 : string. *)
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


 
