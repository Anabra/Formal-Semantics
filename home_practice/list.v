Require Import Coq.Program.Basics.

Inductive List (a : Type) : Type :=
  | nil : List a
  | cons : a -> List a -> List a.

Definition one_to_three : List nat :=
  cons _ 1 (cons _ 2 (cons _ 3 (nil _))).

Eval compute in one_to_three.


Fixpoint map {a b : Type} (f : a -> b) (xs : List a) : List b :=
  match xs with
  | nil _ => nil _
  | cons _ x xs => cons _ (f x) (map f xs)
  end.

Eval compute in map (mult 2) one_to_three.

Theorem functor_id_law (a : Type) (xs : List a) : map (fun x => x) xs = xs.
Proof.
  induction xs.
    simpl. trivial.

    simpl. rewrite IHxs. trivial.
Qed.

Theorem functor_composition_law
  (a b c : Type) (f : b -> c) (g : a -> b) (xs : List a)
  : map f (map g xs) = map (compose f g) xs.
Proof.
  induction xs.
    simpl. trivial.

    simpl. rewrite IHxs. unfold compose. trivial.
Qed.

