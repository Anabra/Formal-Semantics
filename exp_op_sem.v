Require Import Coq.Strings.String.

Inductive exp : Type :=
  | num : nat -> exp
  | var : string -> exp
  | plus : exp -> exp -> exp
  | minus : exp -> exp -> exp.

Definition state : Type := string -> nat.

Fixpoint eval (s : state) (e : exp) : nat := 
  match e with
  | num n => n
  | var v => s v
  | plus lhs rhs => eval s lhs + eval s rhs
  | minus lhs rhs => eval s lhs - eval s rhs
  end.

Definition empty : state := fun v => 0.

Definition update (v : string) (n : nat) (s : state) : state :=
  fun v' => if eqb v v' then n else s v.

Theorem putGet (v : string) (n : nat) (s : state) : (update v n s) v = n.
Proof.
  unfold update. rewrite eqb_refl. trivial.
Qed.

Theorem getPut (v : string) (s : state) : (update v (s v) s) v = (s v).
Proof.
  unfold update. rewrite eqb_refl. trivial.
Qed.

Theorem putPut (v : string) (n1 : nat) (n2 : nat) (s : state) 
  : (update v n2 (update v n1 s)) v = n2.
Proof.
  unfold update. rewrite eqb_refl. trivial.
Qed.

Inductive even : nat -> Prop :=
  | ev0 : even 0
  | evS (n : nat) (H : even n) : even (S (S n)).

Example even4 :
  even 4.
Proof.
  apply evS.
  apply evS.
  apply ev0.
Qed.