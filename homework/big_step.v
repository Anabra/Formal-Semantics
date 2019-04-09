(* BEGIN FIX *)
Definition name : Type := nat.

Inductive aexp : Type :=
  | ANum (n : nat)
  | AVar (x : name)
  | APlus (a a' : aexp)
  | ATimes (a a' : aexp).

Coercion ANum : nat >-> aexp.
Coercion AVar : name >-> aexp.
Notation "a1 +' a2" := (APlus a1 a2) (at level 50).
Notation "a1 *' a2" := (ATimes a1 a2) (at level 60).

Definition W : name := 1.
Definition X : name := 2.
Definition Y : name := 3.
Definition Z : name := 4.

Definition state : Type := name -> nat.
Definition update (x : name)(n : nat)(s : state)
 : state := fun x' => if Nat.eqb x x' then n else s x'.
Definition empty : state := fun _ => 0.

Fixpoint aeval (a : aexp)(s : state) : nat :=
  match a with
  | ANum n => n
  | AVar x => s x
  | APlus a1 a2 => aeval a1 s + aeval a2 s
  | ATimes a1 a2 => aeval a1 s * aeval a2 s
  end.

Inductive bstep : aexp * state -> nat -> Prop :=
  | bnum (n : nat)(s : state) : bstep (ANum n , s) n
  | bvar (x : name)(s : state) : bstep (AVar x , s) (s x)
  | bplus (a1 a2 : aexp)(s : state)(n1 n2 : nat) :
      bstep (a1 , s) n1 ->
      bstep (a2 , s) n2 ->
      bstep (a1 +' a2 , s) (n1 + n2)
  | btimes (a1 a2 : aexp)(s : state)(n1 n2 : nat) :
      bstep (a1 , s) n1 ->
      bstep (a2 , s) n2 ->
      bstep (a1 *' a2 , s) (n1 * n2).

Notation "w ˇ i" := (bstep w i) (at level 50).

Lemma todenot : forall a s n, (a , s) ˇ n -> aeval a s = n.
(* END FIX *)
Proof.
  intros.
  generalize dependent n.
  induction a.
    intros. inversion H. trivial.
    intros. inversion H. trivial.
    intros. simpl. inversion H. rewrite (IHa1 n1 H4). rewrite (IHa2 n2 H5). trivial.

    intros. inversion H. trivial.
    intros. inversion H. trivial.
    intros. simpl. inversion H. rewrite (IHa1 n1 H4). rewrite (IHa2 n2 H5). trivial.
Qed.

(* BEGIN FIX *)
Lemma fromdenot : forall a s n, aeval a s = n -> (a , s) ˇ n.
(* END FIX *)
Proof.
  intros.
  generalize dependent n.
  induction a.
    intros. simpl in H. rewrite H. apply bnum.
    intros. simpl in H. rewrite <- H. apply bvar.
    intros. simpl in H.
      rewrite <- H.
      apply (bplus a1 a2 s (aeval a1 s) (aeval a2 s)).
      apply (IHa1 (aeval a1 s)). trivial.
      apply (IHa2 (aeval a2 s)). trivial.
    intros. simpl in H.
       rewrite <- H.
       apply (btimes a1 a2 s (aeval a1 s) (aeval a2 s)).
       apply (IHa1 (aeval a1 s)). trivial.
       apply (IHa2 (aeval a2 s)). trivial.
Qed.