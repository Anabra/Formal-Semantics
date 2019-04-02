(* BEGIN FIX *)

Definition name : Type := nat.
Definition state : Type := name -> nat.

Inductive aexp : Type :=
  | Num : nat -> aexp
  | Var : name -> aexp
  | Add : aexp -> aexp -> aexp
  | Mul : aexp -> aexp -> aexp.

Inductive bexp : Type :=
  | True  : bexp
  | False : bexp
  | Not   : bexp -> bexp
  | Or    : bexp -> bexp -> bexp
  | Lt    : aexp -> aexp -> bexp.

Definition W : name := 1.
Definition X : name := 2.
Definition Y : name := 3.
Definition Z : name := 4.

Fixpoint aeval (e : aexp)(s : state) : nat :=
  match e with
  | Num n => n
  | Var x => s x
  | Add e1 e2 => aeval e1 s + aeval e2 s
  | Mul e1 e2 => aeval e1 s * aeval e2 s
  end.

(* N.B. negb    : bool -> bool
        orb     : bool -> bool -> bool
        Nat.ltb : Nat -> Nat -> Bool
*)

Fixpoint beval (e : bexp)(s : state) : bool :=
  match e with
  | True => true
  | False => false
  | Not b => negb (beval b s)
  | Or lhs rhs => orb (beval lhs s) (beval rhs s)
  | Lt lhs rhs => Nat.ltb (aeval lhs s) (aeval rhs s)
  end.
(* END FIX *)

(* BEGIN FIX *)
Definition empty : state := fun x => 0.

Definition update (x : name)(n : nat)(s : state)
 : state := fun x' => if Nat.eqb x x' then n else s x'.

(* Add meg exState-et ugy, hogy ex1 bizonyithato legyen! *)

Example exState : state :=
  fun x => 0.
(* END FIX *)

(* BEGIN FIX *)
Example ex1 :
  beval (Or (Lt (Var X) (Num 0))
            (Or (Lt (Var Y) (Num 0))
                (Not (Lt (Var Z) (Num 1))))) exState = false.
Proof.
  trivial.
Qed.
(* END FIX *)

(* Definialj egy kifejezest ugy, hogy ex2-t, ex3-at es
   ex4-et is be tudd bizonyitani! *)

Example exExp : bexp :=
  Lt (Num 3) (Add (Var X) (Var Y)).
(* END FIX *)

(* BEGIN FIX *)
Example ex2 :
  beval exExp (update X 1 (update Y 2 empty)) = false.
Proof.
  trivial.
Qed.
(* END FIX *)

(* BEGIN FIX *)
Example ex3 :
  beval exExp (update X 0 (update Y 2 empty)) = false.
Proof.
  trivial.
Qed.
(* END FIX *)

(* BEGIN FIX *)
Example ex4 :
  beval exExp (update X 2 (update Y 2 empty)) = true.
Proof.
  trivial.
Qed.
(* END FIX *)