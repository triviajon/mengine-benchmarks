Require Import Coq.Init.Tactics.

Section Test.

Variable T : Type.

Variable f g : T -> T.
Variable h : T -> T -> T.
Variable a b c : T.
Variable eq_haa_a : forall x y : T, h x y = c.

Goal @eq T (__HAA__) c. 
Time rewrite eq_haa_a.
reflexivity.
Qed.

End Test.

