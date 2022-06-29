Lemma ex1: forall A : Prop,
~~~A -> ~A.
Proof.
intro A.
intro H1.
contradict H1.
intro H2.
contradict H2.
assumption.
Qed.