Inductive Nat : Type :=
  | O : Nat
  | S : Nat -> Nat.

Fixpoint plus (n m : Nat) {struct n} : Nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.

Notation "n + m" := (plus n m)
  (at level 50, left associativity).

Fixpoint mul (n m : Nat) {struct n} : Nat :=
  match n with
  | O => O
  | S n' => m + (mul n' m)
  end.


Notation "n * m" := (mul n m)
  (at level 40, left associativity).

Example mul_test_1 : S (S O) * S O = S (S O).
Proof.
  compute.
  trivial.
Qed.

Example mul_test_2 : S (S O) * S (S (S O)) = S (S (S (S (S (S O))))).
Proof.
  compute.
  trivial.
Qed.

Example mul_test_3 : S (S O) * O = O.
Proof.
  compute.
  trivial.
Qed.

Example mul_test_4 : O * S (S O) = O.
Proof.
  compute.
  trivial.
Qed.

Lemma add_associativity (n m o : Nat) : n + (m + o) = (n + m) + o.
Proof.
  intros.
  induction n.
  (* Inductional Hyptothesis *)
    simpl.
    trivial.
  (* Inductional step *)
    simpl.
    rewrite IHn.
    trivial.
Qed.

Lemma add_right_id (a : Nat) : a + O = a.
Proof.
  induction a.
    simpl. trivial.
    simpl. congruence.
Qed.

Lemma add_right_suc (a b : Nat) : a + S b = S a + b.
Proof.
  induction a.
    simpl. trivial.
    simpl. rewrite IHa. simpl. trivial.
Qed.

Lemma add_commutativity (a b: Nat) : a + b = b + a.
Proof.
  induction a.
  (* Inductional Hyptothesis *)
    simpl. rewrite add_right_id. trivial.
  (* Inductional step *)
    simpl. rewrite add_right_suc. simpl. congruence.
Qed.

Lemma add_eq_prop (a x y : Nat) : x = y -> a + x = a + y.
Proof.
  intros.
  induction a.
    simpl. trivial.
    simpl. congruence.
Qed.

Lemma mul_add_distributivity (a b c : Nat) : a * (b + c) = a*b + a*c.
Proof.
  induction a.
  (* IH *)
    simpl. trivial.

  (* step *)
    simpl.
    rewrite IHa.
    rewrite <- add_associativity.
    rewrite <- add_associativity.

    remember (c + (a * b + a * c)) as lhs.
    remember (a * b + (c + a * c)) as rhs.
    assert (reductionH : lhs = rhs).

    rewrite Heqlhs. rewrite Heqrhs.
    rewrite (add_commutativity c _).
    rewrite (add_commutativity c _).
    rewrite (add_associativity _ _ c).
    trivial.

    rewrite (add_eq_prop _ _ _ reductionH).
    trivial.
Qed.


Lemma mul_right_zero (a : Nat) : a * O = O.
Proof.
  induction a.
    trivial.

    trivial.
Qed.

Lemma add_suc (a : Nat) : S a = a + (S O).
Proof.
  rewrite add_right_suc.
  rewrite add_right_id.
  trivial.
Qed.

Lemma mul_right_id (a : Nat) : a * S O = a.
Proof.
  induction a.
    trivial.
    simpl. congruence.
Qed.

Lemma mul_right_suc (a b : Nat) : a * S b = a + a * b.
Proof.
  rewrite (add_suc b).
  rewrite mul_add_distributivity.
  rewrite mul_right_id.
  rewrite add_commutativity.
  trivial.
Qed.

Lemma mul_associativity (a b c : Nat) : a * (b * c) = a * b * c.
Proof.
  induction c.
    simpl.
    rewrite mul_right_zero.
    rewrite mul_right_zero.
    rewrite mul_right_zero.
    trivial.

    rewrite mul_right_suc.
    rewrite mul_add_distributivity.
    rewrite mul_right_suc.
    rewrite IHc.
    trivial.
Qed.

Lemma mul_commutativity (a b : Nat) : a * b = b * a.
Proof.
  induction a.
    rewrite mul_right_zero. trivial.

    simpl. rewrite mul_right_suc.
    rewrite IHa.
    trivial.
Qed.