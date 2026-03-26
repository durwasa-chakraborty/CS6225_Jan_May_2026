(**
Proof by Induction
Ref: Software Foundations Vol.1, Induction.v
*)

From Lectures Require Export W1.

Theorem add_0_first_try : forall n:nat,
  n + 0 = n.
Proof. intros n. destruct n as [|n'] eqn:E.
- reflexivity.
- simpl.
Abort.

(**
Doesn't work because one would need to keep on destructing n'.
*)

(**
Basic induction on natural numbers:
To show that P(n) holds:
- Base case: Show that P(O) holds
- Inductive case: Assume that P(n') holds, and prove that P(S(n')) holds.
*)

Theorem add_0: forall n:nat,
  n + 0 = n.
Proof. intros n. induction n as [|n' IHn'].
- reflexivity.
- simpl. rewrite IHn'. reflexivity.
Qed.

(**
Homework:
Theorem mul_0_r : forall n:nat,
  n * 0 = 0.
*)

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof. intros n m. induction n as [|n' IHn'].
- simpl. reflexivity.
- simpl. rewrite IHn'. reflexivity.
Qed. 


Theorem add_comm : forall n m : nat,
  n + m = m + n.
Proof. intros n m. induction n as [|n' IHn'].
- simpl. rewrite add_0. reflexivity.
- simpl. rewrite IHn'. rewrite plus_n_Sm. reflexivity.
Qed. 

Theorem add_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof. intros. induction n as [|n' IHn'].
- reflexivity.
- simpl. rewrite IHn'. reflexivity.
Qed. 

(**
Using replace to selectively rewrite subterms.
*)

Theorem add_associativity_four_first_try : forall (a b c d : nat),
(a + b + c) + d = a + (b + c + d).
Proof.
intros. rewrite <- add_assoc. rewrite -> add_assoc. Abort.

Theorem plus_associativity_four : forall (a b c d : nat),
(a + b + c) + d = a + (b + c + d).
Proof.
intros. rewrite <- add_assoc. replace (b+c+d) with (b+(c+d)).
 - replace (a + (b + (c + d))) with ((a+b)+(c+d)).
  -- reflexivity.
  -- rewrite <- add_assoc. reflexivity.
 - rewrite add_assoc. reflexivity.
Qed. 
 
 
(** Exercise: Which tactic is needed to prove the following?
- Simplification
- Destruct or
- Induction
*) 

Theorem leb_refl : forall n:nat,
  (leb n n) = true.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem zero_neqb_S : forall n:nat,
  0 =? (S n) = false.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem S_neqb_0 : forall n:nat,
  (S n) =? 0 = false.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof.
  (* FILL IN HERE *) Admitted.

(** Structural induction *)
 
Inductive tree : Type :=
| leaf
| node (val : nat) (lt : tree) (rt : tree).

Fixpoint insert (v : nat) (t : tree) : tree :=
match t with
| leaf => node v leaf leaf
| node n l r => if leb v n then node n (insert v l) r
                else node n l (insert v r)
end.


Fixpoint element (v : nat) (t : tree) : bool :=
match t with
| leaf => false
| node n l r => orb (eqb v n) (orb (element v l) (element v r))
end.

Theorem or_property_2: forall (b : bool), orb b true = true.
Proof. intros b. destruct b.
- reflexivity.
- reflexivity.
Qed. 

Theorem insert_is_correct : forall (v : nat) (t : tree),
element v (insert v t) = true.
Proof.
intros v t. induction t as [| n l IHl r IHr].
- simpl. assert (H: forall n:nat, eqb n n = true).
  {induction n as [| n' IHn'].
    * reflexivity.
    * simpl. rewrite IHn'. reflexivity. }
  rewrite H. reflexivity.
- simpl. destruct (leb v n) eqn:E.
  -- simpl. rewrite IHl. simpl. rewrite or_property_2. reflexivity.
  -- simpl. rewrite IHr. rewrite or_property_2. rewrite or_property_2.
    reflexivity.
Qed.

(** Case Study: Representing Arithmetic and Boolean Expressions in Rocq *)

(** Grammar for arithmetic expressions (in Backus-Naur Form (BNF))
A :: = N
       | A + A
       | A * A
       | A - A
*)

Inductive aexp := 
| ANum (n:nat)
| APlus (a1 a2: aexp)
| AMult (a1 a2: aexp)
| AMinus (a1 a2: aexp).

(** Grammar for boolean expressions (in BNF)
B ::= true
      | false
      | A = A
      | A <= A
      | !B
      | B && B
      | B || B
*)

Inductive bexp :=
| BTrue
| BFalse
| BEq (a1 a2: aexp)
| BLe (a1 a2: aexp)
| BNeg (b: bexp)
| BAnd (b1 b2: bexp)
| BOr (b1 b2: bexp).

Definition a1 := APlus (ANum 1) (AMult (ANum 2) (ANum 3)).

Definition b1 := BEq a1 (ANum 7).

Fixpoint aeval (a : aexp) : nat :=
match a with
| ANum n => n
| APlus a1 a2 => (aeval a1) + (aeval a2)
| AMult a1 a2 => (aeval a1) * (aeval a2)
| AMinus a1 a2 => (aeval a1) - (aeval a2)
end.

Compute (aeval a1).

Fixpoint beval (b : bexp) : bool :=
match b with
| BTrue => true
| BFalse => false
| BEq a1 a2 => eqb (aeval a1) (aeval a2)
| BLe a1 a2 => leb (aeval a1) (aeval a2)
| BNeg b' => negb (beval b')
| BAnd b1 b2 => andb (beval b1) (beval b2)
| BOr b1 b2 => orb (beval b1) (beval b2)
end.

Compute (beval b1).

Fixpoint aexp_opt_zero (a: aexp) : aexp :=
match a with
| ANum n => ANum n
| APlus (ANum 0) e2 => aexp_opt_zero e2
| APlus e1 e2 => APlus (aexp_opt_zero e1) (aexp_opt_zero e2)
| AMult e1 e2 => AMult (aexp_opt_zero e1) (aexp_opt_zero e2)
| AMinus e1 e2 => AMinus (aexp_opt_zero e1) (aexp_opt_zero e2)
end.

Theorem aexp_opt_zero_sound : forall (e : aexp),
 aeval (aexp_opt_zero e) = aeval e.
Proof. induction e as [n|a1 IHa1 a2 IHa2|a1 IHa1 a2 IHa2|a1 IHa1 a2 IHa2].
- reflexivity.
- destruct a1 as [n1 | a11 a12 | a11 a12 | a11 a12] eqn:E.
  * destruct n1 as [| n1'] eqn:E1.
    ** simpl. rewrite IHa2. reflexivity.
    ** simpl. rewrite IHa2. reflexivity.
  * 
  assert (H: aexp_opt_zero (APlus (APlus a11 a12) a2) = 
             APlus (aexp_opt_zero (APlus a11 a12)) (aexp_opt_zero a2)).
   {reflexivity. }
   rewrite H. 
   assert (H1: aeval (APlus (aexp_opt_zero (APlus a11 a12)) (aexp_opt_zero a2)) =
           (aeval (aexp_opt_zero (APlus a11 a12))) + (aeval (aexp_opt_zero a2))).
     { simpl. reflexivity. }
   rewrite H1. rewrite IHa1. rewrite IHa2. reflexivity.
  * simpl. simpl in IHa1. rewrite IHa1. rewrite IHa2. reflexivity.
  * simpl. simpl in IHa1. rewrite IHa1. rewrite IHa2. reflexivity.
- simpl. rewrite IHa1. rewrite IHa2. reflexivity.
- simpl. rewrite IHa1. rewrite IHa2. reflexivity.
Qed.
    
   
   






