Lemma ex2 : forall A B : Prop,
A \/ B -> ~(~A /\ ~B).
Proof.
intros A B.
intro H1.
intro H2.
destruct H1 as [H3|H4].
destruct H2 as [H5 H6].
contradict H5.
assumption.
destruct H2 as [H5 H6].
contradict H6.
assumption.
Qed.