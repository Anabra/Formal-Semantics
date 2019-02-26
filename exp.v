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

Notation "x + y" := (APlus x y) (at level 50, left associativity).
Notation "x - y" := (AMinus x y) (at level 50, left associativity).
Notation "x * y" := (AMult x y) (at level 40, left associativity).
Notation "x ≤ y" := (BLe x y) (at level 70, no associativity).
Notation "x = y" := (BEq x y) (at level 70, no associativity).
Notation "x && y" := (BAnd x y) (at level 40, left associativity).
Notation "'¬' b" := (BNot b) (at level 75, right associativity).

Definition notational_example : aexp :=
  (ANum 3 + ANum 5).

Eval compute in notational_example.

Fixpoint leafCount (e : aexp) {struct e} : nat :=
  match e with
  | ANum _ => 1
  | APlus e1 e2 => plus (leafCount e1) (leafCount e2)
  | AMinus e1 e2 => plus (leafCount e1) (leafCount e2)
  | AMult e1 e2 => plus (leafCount e1) (leafCount e2)
end.

Theorem plus_assoc : forall a b c, plus a (plus b c) = plus (plus a b) c.
Proof.
  intros.
  induction a.
    (* Case Z *)   reflexivity.
    (* Case S a *) simpl. rewrite IHa. reflexivity.
Qed.

Theorem plus_comm : forall a b, plus a b = plus b a.
Proof.
  induction a.
    (* Case Z *)
      induction b.
        (* Case Z *)   reflexivity.
        (* Case S b *) simpl. rewrite <- IHb. reflexivity.
    (* Case a = S a *)
      induction b.
        (* Case Z  *)
          simpl. rewrite (IHa 0). reflexivity.
        (* Case S b *)
          simpl. rewrite <- IHb.
          simpl. rewrite (IHa (S b)).
          simpl. rewrite (IHa b).
          reflexivity.
Qed.

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









