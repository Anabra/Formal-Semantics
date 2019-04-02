Inductive aexp : Type :=
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

Definition exp_example : aexp :=
  APlus
   (AMult
     (APlus (ANum 1) (ANum 2))
     (ANum 3))
   (AMinus (ANum 4) (ANum 5)).

Fixpoint aeval (a : aexp) : nat :=
  match a with
  | ANum n => n
  | APlus a1 a2 => (aeval a1) + (aeval a2)
  | AMinus a1 a2 => (aeval a1) - (aeval a2)
  | AMult a1 a2 => (aeval a1) * (aeval a2)
  end.

Example test_aeval1:
  aeval (APlus (ANum 2) (ANum 2)) = 4.
Proof. reflexivity. Qed.

Fixpoint leafCount (e : aexp) {struct e} : nat :=
  match e with
  | ANum _ => 1
  | APlus e1 e2 => plus (leafCount e1) (leafCount e2)
  | AMinus e1 e2 => plus (leafCount e1) (leafCount e2)
  | AMult e1 e2 => plus (leafCount e1) (leafCount e2)
end.

Require Import Coq.Arith.Plus.
Require Import Coq.Arith.Minus.
Require Import Coq.Arith.Mult.

Lemma lc_plus_comm (e1 e2 : aexp) :
  leafCount (APlus e1 e2) = leafCount (APlus e2 e1).
Proof.
  intros.
  induction e1.
    (* IH *)
    simpl.
    rewrite plus_comm.
    simpl.
    trivial.

    (* step *)
    simpl.
    rewrite (plus_comm (leafCount e2) (leafCount e1_1 + leafCount e1_2)).
    trivial.

    (* step *)
    simpl.
    rewrite (plus_comm (leafCount e2) (leafCount e1_1 + leafCount e1_2)).
    trivial.

   (* step *)
    simpl.
    rewrite (plus_comm (leafCount e2) (leafCount e1_1 + leafCount e1_2)).
    trivial.
Qed.

Fixpoint optZero (e : aexp) : aexp :=
  match e with
  | ANum n => ANum n
  | APlus n (ANum 0) => optZero n
  | APlus (ANum 0) n => optZero n
  | APlus n m => APlus (optZero n) (optZero m)
  | AMinus n (ANum 0) => optZero n
  | AMinus n m => AMinus (optZero n) (optZero m)
  | AMult n (ANum 0) => ANum 0
  | AMult (ANum 0) n => ANum 0
  | AMult n m => AMult (optZero n) (optZero m)
  end.

Lemma aevalPlus (lhs rhs : aexp) : aeval (APlus lhs rhs) = aeval lhs + aeval rhs.
Proof.
  trivial.
Qed.

Lemma aevalMinus (lhs rhs : aexp) : aeval (AMinus lhs rhs) = aeval lhs - aeval rhs.
Proof.
  trivial.
Qed.

Lemma aevalMult (lhs rhs : aexp) : aeval (AMult lhs rhs) = aeval lhs * aeval rhs.
Proof.
  trivial.
Qed.

Lemma optZeroHomoMinus (e1 e2 : aexp) :
  e2 <> ANum 0 ->
  optZero (AMinus e1 e2) = (AMinus (optZero e1) (optZero e2)).
Proof.
  intro. destruct e2;
    trivial.
    destruct n.
      contradiction.
      trivial.
Qed.

Lemma optZeroHomoPlus (e1 e2 : aexp) :
  e1 <> ANum 0 ->
  e2 <> ANum 0 ->
  optZero (APlus e1 e2) = (APlus (optZero e1) (optZero e2)).
Proof.
  intros. destruct e1; destruct e2. all: try (destruct n). all: try (destruct n0).
    all: trivial.
    all: contradiction.
Qed.

Lemma optZeroHomoMult (e1 e2 : aexp) :
  e1 <> ANum 0 ->
  e2 <> ANum 0 ->
  optZero (AMult e1 e2) = (AMult (optZero e1) (optZero e2)).
Proof.
  intros. destruct e1; destruct e2. all: try (destruct n). all: try (destruct n0).
    all: trivial.
    all: contradiction.
    (* contradiction searches for empty type in the context *)
Qed.

Lemma optZeroMinus_0_r (e1 : aexp) : optZero (AMinus e1 (ANum 0)) = optZero e1.
Proof.
  trivial.
Qed.

Lemma optZeroPlus_0_r (e1 : aexp) : optZero (APlus e1 (ANum 0)) = optZero e1.
Proof.
  destruct e1;
    try trivial.
    destruct n;
      try trivial.
Qed.

Lemma optZeroPlus_0_l (e1 : aexp) : optZero (APlus (ANum 0) e1) = optZero e1.
Proof.
  destruct e1;
    try trivial.
    destruct n;
      try trivial.
Qed.

Lemma optZeroMult_0 (e1 e2 : aexp) :
  e1 = ANum 0 \/ e2 = ANum 0 ->
  optZero (AMult e1 e2) = ANum 0.
Proof.
  intros.
  destruct e1; destruct e2.
    all: try (destruct n).
    all: try (destruct n0).
    all: try trivial.
    all: (decompose [or] H; discriminate H0; discriminate H0).
    (* discriminate is for not true equlaity hypotheses -> can prove anything *)
Qed.

Theorem optZeroSound (e : aexp) : aeval e = aeval (optZero e).
Proof.
  induction e.

  (* NUM - base case *)
  simpl. trivial.

  (* PLUS *)
  destruct e1; destruct e2.
    all: try (destruct n).
    all: try (destruct n0).
    all: try trivial.
    all: try (simpl (aeval (APlus _ (ANum 0))); rewrite plus_0_r; rewrite optZeroPlus_0_r; trivial).
    all: try (rewrite optZeroHomoPlus;
      try (unfold not; intros; discriminate) +
      (rewrite aevalPlus; rewrite IHe1);
      (rewrite (aevalPlus (optZero _)); rewrite IHe2);
      trivial).

  (* MINUS*)
  destruct e2; try (destruct n).
    try (rewrite optZeroMinus_0_r).
    simpl. rewrite <- minus_n_O.
    destruct e1.
      rewrite <- IHe1. trivial.
      1-3: trivial.

      all: try (rewrite optZeroHomoMinus;
        try (unfold not; intros; discriminate) +
        (rewrite aevalMinus; rewrite IHe1);
        (rewrite (aevalMinus (optZero _)); rewrite IHe2);
        trivial).

  (* MULT *)
  destruct e1; destruct e2.
    all: try (destruct n).
    all: try (destruct n0).
    all: try trivial.
    all: try (simpl (aeval (AMult _ (ANum 0))); rewrite mult_0_r; simpl; trivial).
    all: try (rewrite optZeroHomoMult;
      try (unfold not; intros; discriminate) +
      (rewrite aevalMult; rewrite IHe1);
      (rewrite (aevalMult (optZero _)); rewrite IHe2);
      trivial).
Qed.






