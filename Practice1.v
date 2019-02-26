Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.


Definition aday : day := thursday.

Definition next_weekday (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | _ => monday
  end.

Eval compute in (next_weekday friday).

Eval compute in (next_weekday (next_weekday saturday)).

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.
Proof. simpl. reflexivity. Qed.

Inductive bool : Type :=
  | true
  | false.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Example right_id (b:bool) : orb b false = b.
Proof. 
simpl.
intros.
destruct b.
  simpl. reflexivity.
  simpl. reflexivity.
Qed.

Example comm (lhs:bool) (rhs:bool) : orb lhs rhs = orb rhs lhs.
Proof.
intros. 
destruct lhs.
  destruct rhs.
    simpl. reflexivity.
    simpl. reflexivity.
  destruct rhs.
    simpl. reflexivity.
    simpl. reflexivity.
Qed.

Inductive list (a : Type) : Type :=
  | nil
  | cons (x : a) (xs : list a).