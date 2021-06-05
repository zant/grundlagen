Theorem l_one : forall m n : nat,
    m <> n -> S m <> S n.
Proof.
  auto.
Qed.

Theorem l_two : forall n : nat,
    S n <> n.
Proof.
  intros n.
  induction n as [| n' Hn'].
  - unfold not. discriminate.
  - apply (l_one (S n') n'). assumption.
Qed.

Theorem l_three : forall x : nat,
    x <> 1 -> exists u : nat, x <> S u.
Proof.
  intros x H.
  induction x as [| x' Hx'].
  - exists 0. unfold not. discriminate.
  - exists 0. apply H.
Qed.
    
