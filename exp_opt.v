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

Fixpoint optPlusZero (e : aexp) : aexp :=
  match e with
  | ANum n => ANum n
  | APlus n (ANum 0) => optPlusZero n
  | APlus (ANum 0) n => optPlusZero n
  | APlus n m => APlus (optPlusZero n) (optPlusZero m)
  | AMinus n (ANum 0) => optPlusZero n
  | AMinus n m => AMinus (optPlusZero n) (optPlusZero m)
  | AMult n (ANum 0) => ANum 0
  | AMult (ANum 0) n => ANum 0
  | AMult n m => AMult (optPlusZero n) (optPlusZero m)
  end.

Theorem optPlusZeroSound (e : aexp) : aeval e = aeval (optPlusZero e).
Proof.
  intros.
  induction e.
    simpl. trivial.
    simpl. destruct e1. destruct e2. destruct n.
      destruct n0. simpl. trivial.
      trivial.
      destruct n0. simpl. rewrite plus_0_r. trivial.
      trivial.
      destruct n.
        trivial.
        rewrite IHe2; rewrite IHe1; trivial.
      destruct n.
        trivial.
        rewrite IHe2; rewrite IHe1; trivial.
      destruct n.
        trivial.
        rewrite IHe2; rewrite IHe1; trivial.
      destruct e2.
        destruct n.
          trivial.
          rewrite IHe2; rewrite IHe1; trivial.
      rewrite <- IHe2. simpl (aeval (ANum 0)). rewrite plus_0_r. trivial.
      rewrite IHe1; rewrite IHe2; trivial.
      rewrite IHe1; rewrite IHe2; trivial.
      rewrite IHe1; rewrite IHe2; trivial.
      rewrite IHe1; rewrite IHe2; trivial.
      destruct e2.
        destruct n.
          trivial.
          rewrite IHe2; rewrite IHe1; trivial.
      rewrite <- IHe2; simpl (aeval (ANum 0)); rewrite plus_0_r; trivial.
      rewrite IHe1; rewrite IHe2; trivial.
      rewrite IHe1; rewrite IHe2; trivial.
      rewrite IHe1; rewrite IHe2; trivial.
      rewrite IHe1; rewrite IHe2; trivial.
      rewrite IHe1; rewrite IHe2; trivial.
      destruct e2.
        destruct n.
          trivial.
          rewrite <- IHe2. rewrite <- IHe1. simpl (aeval (ANum 0)). rewrite plus_0_r. trivial.



      



      
      
 

    
      
Qed.






