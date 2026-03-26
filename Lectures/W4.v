(**
Some more basic tactics in Rocq
- apply, apply with
- symmetry
- injection
- f_equal
- discriminate 
- apply in
- specialize
- generalize dependent
- unfold

Ref.: Software Foundations, Volume 1, Tactics.v
*)

From Lectures Require Export W3.


(** The apply tactic
- Can be used if the goal exactly matches an hypothesis.
- Can also be used if the goal matches the consequent of 
  an implication (i.e., something of the form [A -> B]).
  In this case, the goal will be replaced by the antecedent
  [A].
*)

Theorem silly1 : forall (n m : nat),
  n = m ->
  n = m.
Proof.
  intros n m eq. apply eq.  Qed.

Theorem silly2 : forall (n m o p : nat),
  n = m ->
  (n = m -> [n;o] = [m;p]) ->
  [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2. apply eq2. apply eq1. Qed.

Theorem silly2a : forall (n m : nat),
  (n,n) = (m,m)  ->
  (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
  [n] = [m].
Proof.
  intros n m eq1 eq2. apply eq2. apply eq1. Qed.

(** The symmetry tactic
- Can be used to switch the left hand side and right hand
  side of an equality proposition in the goal *)

Theorem silly3 : forall (n m : nat),
  n = m ->
  m = n.
Proof.
  intros n m H. symmetry. apply H.  Qed.


(** The apply_with tactic
- An extension of [apply] that allows us to specify how to 
  instantiate variables in the applied theorem or hypothesis.
 *)

Theorem trans_eq : forall (X:Type) (x y z : X),
  x = y -> y = z -> x = z.
Proof.
intros X x y z eq1 eq2. rewrite -> eq1. apply eq2. Qed.

Example trans_eq_example' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2. 
  apply trans_eq with (y := [c;d]). apply eq1. apply eq2. Qed.

(**
Injectivity of constructors
*)

Theorem S_injective : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H1.
  assert (H2: n = pred (S n)). { reflexivity. }
  rewrite H2. rewrite H1. simpl. reflexivity.
Qed.

Theorem S_injective' : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H. injection H as Hnm. apply Hnm. Qed.

(** Injection H as ... generates all equations that
  can be derived using the injectivity of constructors in H *)

Theorem injection_ex1 : forall (n m o : nat),
  [n;m] = [o;o] ->
  n = m.
Proof.
  intros n m o H. injection H as H1 H2. 
  rewrite H1. rewrite H2. reflexivity. Qed.

Example injection_ex3 : forall (X : Type) (x y z : X) 
(l j : list X),
  x :: y :: l = z :: j ->
  j = z :: l ->
  x = y.
Proof.
  intros X x y z l j H1.
  injection H1 as Hx Hj. rewrite Hx. rewrite <- Hj.
  intros H2. injection H2 as Hy. symmetry. apply Hy.
Qed.

(** f_equal tactic
- Used to prove goals of the form [f x = f y] by 
  reducing them to [x = y]. *)

 
Theorem func_app : forall (X Y: Type) (f: X -> Y) (x1 x2: X),
  x1 = x2 ->
  f x1 = f x2.
Proof.
 (*intros X Y f x1 x2 H. rewrite H. reflexivity. Qed.*) 
  intros X Y f x1 x2 H. f_equal. apply H. Qed. 

(** Discriminate tactic
- Used to prove goals that are contradictions, by noticing 
  that two sides of an equation were constructed by 
  different constructors. 
  In this case, we can use the discriminate tactic to 
  immediately prove any goal *)

Theorem discriminate_ex1 : forall (n m : nat),
  false = true ->
  n = m.
Proof.
  intros n m contra. discriminate contra. Qed.

(** Also known as principle of explosion: from a false hypothesis, 
anything can be inferred. *)

Theorem discriminate_ex2 : forall (n : nat),
  S n = O ->
  2 + 2 = 5.
Proof.
  intros n contra. discriminate contra. Qed.

Theorem eqb_0_l : forall n,
   0 =? n = true -> n = 0.
Proof.
  intros n H.
  destruct n as [| n'].
  - reflexivity.
  - simpl in H. discriminate H.
Qed.

(** The apply in tactic
- Used to apply a theorem or hypothesis in the context of 
  another hypothesis.
- Forward reasoning : given [X -> Y] and a hypothesis 
  matching [X], it produces a hypothesis matching [Y]. *)

Theorem silly4 : forall (n m p q : nat),
  (n = m -> p = q) ->
  m = n ->
  q = p.
Proof.
  intros n m p q H1 H2. symmetry in H2. apply H1 in H2. 
  symmetry in H2. apply H2. Qed.

(** The specialize tactic
- Used to instantiate a universally quantified variable 
  in a hypothesis with a specific value.
*)

Theorem specialize_example: forall n,
     (forall m, m*n = 0)
  -> n = 0.
Proof.
  intros n H.
  specialize H with (m := 1).
  rewrite mult_1_l in H.
  apply H. Qed.


(** The generalize dependent tactic
- Used to move a variable from the context back into the goal,
  re-adding a universal quantifier.
*)
 
Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Theorem double_injective : forall n m,
  double n = double m ->
  n = m.
Proof.
  intros n m H.
  induction n as [| n' IHn'].
  - destruct m as [| m'].
    + reflexivity.
    + discriminate H.
  - destruct m as [| m'].
    + discriminate H.
    + f_equal. Abort. 

Theorem double_injective_complete : forall n m,
  double n = double m ->
  n = m.
Proof.
  intros n. induction n as [| n' IHn'].
  - intros m H. destruct m as [| m'].
    + reflexivity.
    + simpl in H. discriminate H.
  - intros m H. destruct m as [| m']. 
    + simpl in H. discriminate H.
    + f_equal. apply IHn'. simpl in H. 
      injection H as H1. apply H1. Qed.

Theorem eqb_true : forall n m,
  n =? m = true -> n = m.
Proof.
  intros n. induction n as [| n' IHn'].
  - intros m H. destruct m as [| m'].
    + reflexivity.
    + simpl in H. discriminate H.
  - intros m H. destruct m as [| m'].
    + simpl in H. discriminate H.
    + simpl in H. f_equal. apply IHn'. apply H. Qed.

Theorem double_injective' : forall n m,
  double n = double m ->
  n = m.
Proof. intros n m. generalize dependent n. 
  induction m as [| m' IHm']. 
- intros n H. destruct n as [| n']. 
  + reflexivity. 
  + simpl in H. discriminate H. 
- intros n H. destruct n as [| n']. 
  + simpl in H. discriminate H. 
  + f_equal. apply IHm'. simpl in H. 
    injection H as H1. apply H1. Qed.

Fixpoint minus (n m : nat) : nat :=
  match n, m with
  | O, _ => O
  | S n', O => S n'
  | S n', S m' => minus n' m'
  end.

Theorem add_0_r : forall n:nat, n + 0 = n.
Proof.
  intros n. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.  Qed.

Lemma sub_add_leb : forall n m, leb n m = true -> 
  (m - n) + n = m.
Proof. intros n. induction n as [| n' IHn'].
  - intros m H. destruct m as [| m'].
    + reflexivity.
    + simpl. rewrite add_0_r. reflexivity.
  - intros m H. destruct m as [| m'].
    + simpl in H. discriminate H.
    + simpl. rewrite <- plus_n_Sm. simpl in H. 
    rewrite IHn'.
      ++ reflexivity.
      ++ apply H. 
Qed.

(** The unfold tactic
- Used to replace a defined term with its body.
*)

Definition double_plus n := n + n.

Lemma square_mult : forall n m, double_plus (n + m) 
 = double_plus n + double_plus m.
Proof.
  intros n m.
  simpl. unfold double_plus. rewrite add_assoc. 
  assert (L: n + m + n = n + n + m).
  { rewrite <- add_assoc. replace (m+n) with (n+m). 
  - rewrite add_assoc. reflexivity.
  - apply add_comm. }
rewrite L. rewrite add_assoc. reflexivity. Qed.
