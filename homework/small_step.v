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
Proof.

Qed.
(* END FIX *)

(* BEGIN FIX *)
(* HINT: use plus_0_r at some point. *)
Lemma zeror (a : aexp)(s : state)(i : nat)(p : (a , s) f=> i) :
  (a +' 0 , s) f=> i.
(* END FIX *)

(* BEGIN FIX *)
Example der1 (s : state) : (3 +' 2 , s) f=> 5.
(* END FIX *)

(* BEGIN FIX *)
Example der2 : (3 +' (X +' 2) , update X 1 empty) f=> 6.
(* END FIX *)