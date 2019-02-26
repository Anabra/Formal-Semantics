Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.


Definition aday : day := thursday.

Inductive list (a : Type) : Type :=
  | nil
  | cons : a -> list a -> list a.


Definition xs : list nat := cons nat 5 (nil nat).

Variable A : Type.

Definition length2 (a : Type) (xs : list a) : nat :=
  match xs with
  | nil _ => 0
  | cons _ x xs => 0
  end.

(* Eval compute in length2 nat (cons nat 0 (nil nat)). *)

Inductive Product (a : Type) (b : Type) : Type :=
  P : a -> b -> Product a b.

Definition swap (a:Type) (b:Type) (p : Product a b) : (Product b a) :=
  match p with
  | P _ _ x y => P b a y x
  end.

Eval compute in swap nat day (P nat day 0 monday).

Variable a : Type.
Variable b : Type.
Variable p : Product a b.

Example swap_prop_1: swap b a (swap a b (p : Product a b)) = p.
Proof.
simpl.
destruct p.
simpl.
reflexivity.
Qed.
