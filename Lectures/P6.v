From LECTURES Require Export W5.


Lemma even_double_conv : forall n, exists k,
  n = if even n then double k else S (double k).
Proof.