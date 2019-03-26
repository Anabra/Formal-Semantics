(* BEGIN FIX *)
Require Import Coq.Strings.String.

Inductive aexp : Type :=
  | ANum (n : nat)
  | AVar (x : string)
  | APlus (a a' : aexp)
  | AMult (a a' : aexp).

Definition state : Type := string -> nat.

Fixpoint aeval (e : aexp)(s : state) : nat := match e with
  | ANum n => n
  | AVar x => s x
  | APlus a a' => aeval a s + aeval a' s
  | AMult a a' => aeval a s * aeval a' s
  end.

Inductive zart : aexp -> Prop :=
  | szam (n : nat) : zart (ANum n)
  | osszeg (a a' : aexp)(az : zart a)
           (a'z : zart a') : zart (APlus a a')
  | szorzat (a a' : aexp)(az : zart a)
            (a'z : zart a') : zart (AMult a a').

Lemma zartPlusMult (e1 e2 : aexp)(p1 : zart e1)(p2 : zart e2) :
  zart (APlus e1 (AMult e1 e2)).
Proof.
  exact (osszeg e1 (AMult e1 e2) p1 (szorzat e1 e2 p1 p2)).
Qed.
(* END FIX *)

(* BEGIN FIX *)
Theorem evalZart (a : aexp)(q : zart a)(s1 s2 : state) :
  aeval a s1 = aeval a s2.
Proof.
  induction q; trivial.
  simpl. rewrite IHq1. rewrite IHq2. trivial.
  simpl. rewrite IHq1. rewrite IHq2. trivial.
Qed.
(* END FIX *)

(* BONUS! use assert and discriminate!
Lemma lem (p : forall e1 e2, aeval e1 empty = aeval e2 empty -> e1 = e2) : False.
 *)