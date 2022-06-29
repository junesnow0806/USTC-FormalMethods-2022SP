Lemma ex3: forall T (P:T -> Prop),
(~exists x, P x) -> forall x, ~ P x.
Proof.
intro T.
intro P.
intro H1.
intro x.
intro H2.
elim H1.
exists x.
exact H2.
Qed.