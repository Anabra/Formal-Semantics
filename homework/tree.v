Fixpoint max (n m : nat) {struct n} : nat :=
  match n, m with
  | 0 , _ => m
  | S n' , 0 => n
  | S n' , S m' => S (max n' m')
  end.

Example max_test1 : max 100 200 = 200. simpl. reflexivity. Qed.
Example max_test2 : max 3 3 = 3. simpl. reflexivity. Qed.
Example max_test3 : max 4 3 = 4. simpl. reflexivity. Qed.

Inductive Tree : Type :=
  | Leaf : Tree
  | Node2 : Tree -> Tree -> Tree
  | Node3 : Tree -> Tree -> Tree -> Tree.

Definition exTree1 : Tree := Node2 (Node3 Leaf Leaf Leaf) Leaf.

Definition exTree2 : Tree := Node2 (Node2 Leaf (Node2 (Node2 Leaf Leaf) Leaf)) (Node2 Leaf Leaf).

Fixpoint height (t : Tree) {struct t} : nat :=
  match t with
  | Leaf => 0
  | Node2 lhs rhs => S (max (height lhs) (height rhs))
  | Node3 lhs mid rhs => S (max (max (height lhs) (height mid)) (height rhs))
  end.


(* BEGIN FIX *)
Example height_test_1 : height exTree1 = 2.
Proof.
  trivial.
Qed.
(* END FIX *)

(* BEGIN FIX *)
Example height_test_2 : height exTree2 = 4.
Proof.
  trivial.
Qed.
(* END FIX *)

(* BEGIN FIX *)
Lemma max_0 (m : nat) : max m 0 = m.
Proof.
  induction m.
    trivial.
    simpl. trivial.
Qed.
(* END FIX *)

(* BEGIN FIX *)
Lemma height_Leaf (t : Tree) : height (Node2 t Leaf) = height (Node2 Leaf t).
Proof.
  simpl. rewrite max_0. trivial.
Qed.
(* END FIX *)

(* BEGIN FIX *)
Lemma max_comm : forall (m n : nat),  max m n = max n m.
Proof.
  intro m.
  induction m.
    simpl. intro n. rewrite max_0. trivial.
    (* why do I get a more general IH? *)
    destruct n.
      trivial.
      simpl. rewrite IHm. trivial.
Qed.
(* END FIX *)