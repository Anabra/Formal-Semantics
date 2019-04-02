(* BEGIN FIX *)

Definition name : Type := nat.

Inductive aexp : Type :=
  | ANum (n : nat)
  | AVar (x : name)
  | APlus (a a' : aexp).

Coercion ANum : nat >-> aexp.
Coercion AVar : name >-> aexp.
Notation "a1 +' a2" := (APlus a1 a2) (at level 50).

Definition W : name := 1.
Definition X : name := 2.
Definition Y : name := 3.
Definition Z : name := 4.

Definition state : Type := name -> nat.
Definition update (x : name)(n : nat)(s : state)
 : state := fun x' => if Nat.eqb x x' then n else s x'.
Definition empty : state := fun _ => 0.

Inductive fstep : aexp * state -> nat -> Prop :=
  | num (n : nat)(s : state) : fstep (ANum n , s) n
  | var (x : name)(s : state) : fstep (AVar x , s) (s x)
  | fplusr (n i : nat)(a2 : aexp)(s : state) :
           fstep (a2 , s) i ->
           fstep (n +' a2 , s) (n + i)
  | ftrans (w1 w2 : aexp * state)(i : nat) :
            step w1 w2 -> fstep w2 i -> fstep w1 i
with step : aexp * state -> aexp * state -> Prop :=
  | plusl (a1 a2 a1t : aexp)(s : state) :
          step (a1 , s) (a1t , s) ->
          step (a1 +' a2 , s) (a1t +' a2 , s)
  | fplusl (a1 a2 : aexp)(s : state)(i : nat) :
           fstep (a1 , s) i ->
           step (a1 +' a2 , s) (i +' a2 , s)
  | plusr (a2 a2t : aexp)(s : state)(n : nat) :
          step (a2 , s) (a2t , s) ->
          step (n +' a2 , s) (n +' a2t , s)
  | trans (w1 w2 w3 : aexp * state) :
          step w1 w2 -> step w2 w3 -> step w1 w3.

Notation "w f=> i" := (fstep w i) (at level 50).
Notation "w => w'" := (step w w') (at level 50).

Require Import Coq.Arith.Plus.

Lemma zerol (a : aexp)(s : state)(i : nat)(p : (a , s) f=> i) :
  (0 +' a , s) f=> i.
(* END FIX *)
Proof.
  assert (H1 : fstep (0 +' a, s) (0 + i)).
    apply (fplusr _ _ _ _ p).
  rewrite plus_0_l in H1.
  apply H1.
Qed.


(* BEGIN FIX *)
(* HINT: use plus_0_r at some point. *)
Lemma zeror (a : aexp)(s : state)(i : nat)(p : (a , s) f=> i) :
  (a +' 0 , s) f=> i.
(* END FIX *)
Proof.
  assert (H1 : step (a +' 0, s) (i +' 0, s)).
    apply (fplusl _ _ _ _ p).
  assert (H2 : fstep (i +' 0, s) (i + 0)).
    apply fplusr. apply num.
  rewrite plus_0_r in H2.
  apply (ftrans _ _ _ H1 H2).
Qed.

(* BEGIN FIX *)
Example der1 (s : state) : (3 +' 2 , s) f=> 5.
(* END FIX *)
Proof.
  assert (H1 : fstep (3 +' 2, s) (3 + 2)).
    apply fplusr. apply num. simpl in H1.
  exact H1.
Qed.


(* BEGIN FIX *)
Example der2 : (3 +' (X +' 2) , update X 1 empty) f=> 6.
(* END FIX *)
Proof.
  assert (H1 : fstep (X +' 2, update X 1 empty) (3)).
    assert (H2 : fstep (AVar X, update X 1 empty) 1).
      apply (var X).
    assert (H3 : step (X +' 2, update X 1 empty) (1 +' 2, update X 1 empty)).
      apply (fplusl _ _ _ _ H2).
    assert (H4 : forall (s : state), fstep (1 +' 2, s) 3).
      intros. apply fplusr. apply num.

    apply (ftrans _ _ _ H3 (H4 (update X 1 empty))).
  apply (fplusr 3 _ _ _ H1).
Qed.
