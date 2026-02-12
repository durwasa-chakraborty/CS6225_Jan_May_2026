(**
Propositions in Rocq

Ref. Software Foundations, Volume 1, Logic.v
*)


From LECTURES Require Export W4.

(** The Prop Type in Rocq
- Every statement that we can try to prove is of type Prop.
 *)

Check (forall n m : nat, n + m = m + n).

Check 2 = 2.

Check 3 = 2.

(** Propositions are also first-class members, and hence can be used at
all places where any other type can be used *)

Definition is_three (n : nat) : Prop :=
  n = 3.
  
Check is_three.

Compute is_three 3.

Compute is_three 4.

Definition injective {A B} (f : A -> B) : Prop :=
  forall x y : A, f x = f y -> x = y.

Check @injective.
  
Lemma succ_inj : injective S.
Proof. intros x y H. injection H as Hxy. apply Hxy. Qed.

(** The familiar equality operator [=] is a (binary) function that returns
    a [Prop].

    The expression [n = m] is syntactic sugar for [eq n m].

    Because [eq] can be used with elements of any type, it is also
    polymorphic: *)

Check @eq.

(** Logical Connectives : conjunction
- The /\ operator is used to represent conjunction in propositions.
- Such propositions can be proved using the split tactic *)

Theorem plus_is_O :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof. intros n m H. split.
- destruct n as [| n'].
 -- reflexivity.
 -- discriminate H.
- destruct m as [| m'].
 -- reflexivity.
 -- rewrite <- plus_n_Sm in H. discriminate H.
Qed.

(**
- A conjunctive hypothesis can be broken down using destruct.
*)

Lemma and_example :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m H.
  destruct H as [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

(** Logical Connectives : disjunction
- The /\ operator is used to represent conjunction in propositions.
- Such propositions can be proved by using either of the two tactics: left
or right (depending on which of the two disjuncts needs to be proven).
 *)
 
Lemma zero_or_succ :
  forall n : nat, n = 0 \/ n = S (pred n).
Proof.
  intros [|n'].
  - left. reflexivity.
  - right. reflexivity.
Qed.

Lemma mult_is_O :
  forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof. intros n m H. destruct n as [| n'].
- left. reflexivity.
- destruct m as [| m']. 
  -- right. reflexivity.
  -- discriminate H.
Qed.

(** Logical Connectives : negation
- The negation operator (~) can be used to write negative propositions.
- Rocq uses the principle of explosion to encode negation: if a proposition
does not hold, one can prove anything from such a proposition.
- This is defined using a special proposition called False from which
anything can be inferred.
 *) 
Module NotPlayground.

Definition not (P:Prop) := P -> False.

Check not : Prop -> Prop.

Notation "~ x" := (not x) : type_scope.

End NotPlayground.

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  intros P contra.
  destruct contra.  Qed.
  
Theorem not_implies_our_not : forall (P:Prop),
  ~ P -> (forall (Q:Prop), P -> Q).
Proof. intros P negP. unfold not in negP. 
 intros Q Hp. apply negP in Hp. destruct Hp.
Qed.

(** Inequality is a very common form of negated statement, so there is a
    special notation for it:
*)
Notation "x <> y" := (~(x = y)) : type_scope.

(** For example: *)

Theorem zero_not_one : 0 <> 1.
Proof. unfold not. intros contra. discriminate contra.
Qed.

Theorem not_False :
  ~ False.
Proof.
  unfold not. intros H. destruct H. Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  intros P Q [HP HNP]. unfold not in HNP.
  apply HNP in HP. destruct HP.  Qed.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  intros P H. unfold not. intros G. apply G. apply H.  Qed.

Lemma not_S_pred_n : ~(forall n : nat, S (pred n) = n).
Proof. unfold not. intros H. specialize H with (n := O). 
  discriminate H. Qed.
  
(** If you are trying to prove a goal that is nonsensical (e.g., the
    goal state is [false = true]), the exfalso tactic can be used to
    change the goal to [False].*)
  
Theorem not_true_is_false : forall b : bool,
  b <> true -> b = false.
Proof. intros b H. unfold not in H. destruct b.
- exfalso. apply H. reflexivity.
- reflexivity.
Qed.

(** Logical Connective: If and only if (<->) *)

Theorem iff_sym : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
  intros P Q [HAB HBA]. (* Note the implicit destruct of <-> in the hypothesis*)
  split.
  - (* -> *) apply HBA.
  - (* <- *) apply HAB.  Qed.
  
(** Existential quantification
- To prove a proposition involving existential quantification, a witness
needs to be provided using the exists tactic 
 *)
 
Definition Even x := exists n : nat, x = double n.
Check Even.

Lemma four_is_Even : Even 4.
Proof.
  unfold Even. exists 2. reflexivity.
Qed.

Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  intros n [m Hm]. (* note the implicit [destruct] here *)
  exists (2 + m).
  apply Hm.  Qed.
  
Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  intros X P H. unfold not. intros He. destruct He as [x Hx].
  apply Hx. apply H. Qed.
  
Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros X P Q. split.
  - intros [x Hx]. destruct Hx as [HP | HQ].
    -- left. exists x. apply HP.
    -- right. exists x. apply HQ.
  - intros [HP | HQ]. 
    -- destruct HP as [x HPx]. exists x. left. apply HPx.
    -- destruct HQ as [x HQx]. exists x. right. apply HQx.
Qed.

Theorem leb_plus_exists : forall n m, leb n m = true -> exists x, m = n+x.
Proof. intros n. induction n as [| n' IHn'].
 - intros m. exists m. reflexivity.
 - intros m H. destruct m as [| m'].
   -- discriminate H.
   -- simpl in H. apply IHn' in H. destruct H as [x Hx]. exists x.
      simpl. f_equal. apply Hx.
Qed.

(** Inductively defined Propositions *)

Inductive ev : nat -> Prop :=
| ev_0 : ev 0
| ev_SS (n : nat) (H : ev n) : ev (S (S n)).

Theorem ev_4 : ev 4.
Proof. apply ev_SS. apply ev_SS. apply ev_0. Qed.

Theorem ev_double : forall n, ev (double n).
Proof. intros n. induction n as [| n' IHn']. 
- simpl. apply ev_0.
- simpl. 

Lemma ev_inversion : forall (n : nat),
    ev n ->
    (n = 0) \/ (exists n', n = S (S n') /\ ev n').
Proof. intros n H. destruct H as [| m Hm].
- left. reflexivity.
- right. exists m. split.
  -- reflexivity.
  -- apply Hm.
Qed.

Theorem evSS_ev : forall n, ev (S (S n)) -> ev n.
Proof. intros n H. apply ev_inversion in H. destruct H as [H1 | H2].
- discriminate.
- destruct H2 as [n' [H21 H22]]. injection H21 as H21'. 
  rewrite H21'. apply H22.
Qed.

Theorem evSS_ev' : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E.  inversion E as [| n' E' Hnn']. apply E'. Qed.
  
Theorem one_not_even : ~ ev 1.
Proof. unfold not. intros H. apply ev_inversion in H. destruct H as [H1 | H2].
- discriminate.
- destruct H2 as [n' [H21 H22]]. discriminate H21.
Qed.

Theorem one_not_even' : ~ ev 1.
Proof. unfold not. intros H. inversion H. Qed.

(** The inversion tactic performs a destruct on an inductive proposition
and automatically applies tactics such as discriminate and injection
to discharge as many goals as possible. *)

Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof. intros n H. inversion H as [| n' E' Hnn']. 
 inversion E' as [| n'' E'' Hnn'']. apply E''. Qed.
 
Theorem ev5_nonsense :
  ev 5 -> 2 + 2 = 9.
Proof. intros H. inversion H as [| n' E' H5n']. inversion E' as [| n'' E'' H3n''].
inversion E''. Qed.

Theorem inversion_ex1 : forall (n m o : nat),
  [n; m] = [o; o] -> [n] = [m].
Proof. intros. inversion H.
Qed.

Theorem inversion_ex2 : forall (n m o p: nat),
  [n; m] = [o; p] -> [n] = [o].
Proof. intros. injection H as H1 H2. f_equal. apply H1. Qed. 


Theorem Even_ev_equiv : forall (n:nat), Even n <-> ev n.
Proof. split.
- intros H. unfold Even in H. destruct H as [x Hx]. generalize dependent n. induction x as [| x' IHx'].
  -- intros n H. simpl in H. rewrite H. apply ev_0.
  -- intros n H. rewrite H. simpl. apply ev_SS. apply IHx'. reflexivity.
- intros H. induction H as [| n' H' IHn'].
  -- unfold Even. exists 0. reflexivity.
  -- unfold Even in IHn'. destruct IHn' as [n IHn']. unfold Even.
     exists (S n). simpl. rewrite IHn'. reflexivity.
Qed.

Inductive le : nat -> nat -> Prop :=
| le_0 (n:nat) : le n n
| le_S (n m : nat) (H: le n m) : le n (S m).

Theorem le_3_5 : le 3 5.
Proof. apply le_S. apply le_S. apply le_0.
Qed.




