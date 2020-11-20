Theorem ld_one : forall m n : nat,
    m <> n -> S m <> S n.
Proof.
  auto.
Qed.

Theorem ld_two : forall n : nat,
    S n <> n.
Proof.
  intros n.
  induction n as [| n' Hn'].
  - unfold not. discriminate.
  - assert (H: S n' <> n' -> S (S n') <> S n').
    { exact (ld_one (S n') n'). } 
  apply H.
  assumption.
Qed.
    
