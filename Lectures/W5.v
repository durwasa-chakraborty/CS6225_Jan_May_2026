(**
Propositions in Rocq

Ref. Software Foundations, Volume 1: Logic.v, IndProp.v, ProofObjects.v, IndPrinicples.v
*)


From Lectures Require Export W4.

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
- The \/ operator is used to represent disjunction in propositions.
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

Theorem or_commut : forall P Q : Prop,
  P \/ Q  -> Q \/ P.
Proof. intros P Q H. destruct H as [HP | HQ].
- right. apply HP.
- left. apply HQ. Qed.

Lemma mult_is_O :
  forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof. intros n m H. destruct n as [| n'].
- left. reflexivity.
- destruct m as [| m']. 
  -- right. reflexivity.
  -- discriminate H.
Qed.

(** Logical Connectives : negation
- The negation operator (~) can be used to write negative propositions, i.e.
propositions which are false.
- Rocq uses the principle of explosion to encode negation: if a proposition
does not hold, one can prove anything from such a proposition.
- This is defined using a special proposition called False from which
anything can be inferred.
 *) 
Module NotPlayground.

Definition not (P:Prop) := P -> False.

Check not.

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
Proof. intros n m H. exists (m-n). rewrite add_comm. rewrite sub_add_leb.
reflexivity. apply H.
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
- simpl. apply ev_SS. apply IHn'.
Qed. 

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


Theorem Even_ev_equiv : forall (n:nat), Even n <-> ev n.
Proof. split.
- intros H. unfold Even in H. destruct H as [n' Hn']. rewrite Hn'. apply ev_double.
- intros H. induction H as [| n' H' IHn'].
  -- unfold Even. exists 0. reflexivity.
  -- unfold Even in IHn'. destruct IHn' as [k Hk]. unfold Even.
     exists (S k). simpl. f_equal. f_equal. apply Hk.
Qed.

Inductive rt_closure {X:Type} (R: X -> X -> Prop) : X -> X -> Prop :=
| rt_refl (x: X) : rt_closure R x x
| rt_step (x y: X) (Hxy: R x y) : rt_closure R x y
| rt_trans (x y z: X) (Hxy: rt_closure R x y) (Hyz: rt_closure R y z) : rt_closure R x z.

Definition isDiagonal {X:Type} (R: X -> X -> Prop) : Prop :=
  forall x y, R x y -> x = y.

Theorem closure_of_diagonal_is_diagonal : forall (X:Type) (R: X -> X -> Prop),
  isDiagonal R -> forall x y, rt_closure R x y -> x = y.
Proof. intros X R Hdiag x y H. induction H as [x | x y Hxy | x y z Hxy IHxy Hyz IHyz].
- reflexivity.
- apply Hdiag in Hxy. apply Hxy.
- rewrite IHxy. apply IHyz.
Qed.

Module Playground.

Inductive le : nat -> nat -> Prop :=
| le_n (n: nat) : le n n
| le_S (n m: nat) (Hnm: le n m) : le n (S m).

Theorem le_3_5 : le 3 5.
Proof. apply le_S. apply le_S. apply le_n.
Qed. 

Definition lt (n m : nat) : Prop := le (S n) m.

Notation "n <= m" := (le n m).

Definition ge (n m :nat) : Prop := le m n.

End Playground.
 

Lemma le_imp : forall n m, (S n) <= m -> n <= m.
Proof. intros n m H . induction H as [| m' Hm' IHm'].
- apply le_S. apply le_n.
- apply le_S. apply IHm'.
Qed.

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof. intros m n o Hmn. induction Hmn as [ | n' Hn' IHn'].
  - intros H. apply H.
  - intros H. apply le_imp in H. apply IHn'. apply H.
Qed.

Theorem O_le_n : forall n,
  0 <= n.
Proof.
  intros n. induction n as [| n' IHn'].
  - apply le_n.
  - apply le_S. apply IHn'.
Qed.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  intros n m H. induction H as [| m' Hm' IHm'].
  - apply le_n.
  - apply le_S. apply IHm'.
Qed.

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
  intros n m H. inversion H.
  - apply le_n.
  - apply le_imp. apply H1.
 Qed. 
  
Theorem le_plus_l : forall a b,
  a <= a + b.
Proof.
  intros a b. induction a as [| a' IHa'].
  - simpl. apply O_le_n.
  - simpl. apply n_le_m__Sn_le_Sm . apply IHa'.
Qed.



(**
Curry-Howard Correspondence
- Propositions as Types: every proposition corresponds 
 to a type, and every proof of a proposition corresponds
 to a value of the corresponding type.

propositions  ~  types
proofs        ~  programs

- The same symbol [->] is used to denote implication in
 propositions, and function types in types because of the
 Curry-Howard correspondence.

- Proving an implication P -> Q is the same as writing a 
 function that takes a proof of P and produces a proof of Q.

*)

Check ev_SS.

Print ev_4.

Definition ev_4' : ev 4 := ev_SS 2 (ev_SS 0 ev_0).

Print ev_4'.

(**
- The tactics used in the proof scripts essentially construct
 a proof object, i.e. a term whose value is the proposition
 that we are trying to prove. 
- However, as shown above, the proof objects can also be 
 constructed directly.
*)

Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof. intros n H. apply ev_SS. apply ev_SS. apply H. Qed.

Definition ev_plus4' : forall n, ev n -> ev (4 + n) :=
 fun n => fun (H: ev n) => ev_SS (2 + n) (ev_SS n H).

Print ev_plus4.

Definition ev_plus4'' (n : nat) (H : ev n) : ev (4 + n) :=
  ev_SS (2 + n) (ev_SS n H).

(**
 Notice that the type of the second argument of ev_plus4''
 uses n which is the first argument. This is an example of
 a so-called dependent type.
*)

Module Eq.

Inductive eq {X:Type} : X -> X -> Prop :=
| eq_refl : forall x, eq x x.

End Eq.

Definition eq_val : forall (X:Type) (x:X), x = x :=
  fun X => fun x => eq_refl x.

Theorem eq_val' : forall (X:Type) (x:X), x = x.
Proof. intros X x. reflexivity. Qed.

Print eq_val.

Module And_Or.
Inductive and (P Q : Prop) : Prop :=
  | conj : P -> Q -> and P Q.
  
Arguments conj [P] [Q]. 
  
Notation "P /\ Q" := (and P Q) : type_scope.

Theorem proj1' : forall P Q,
  P /\ Q -> P.
Proof. intros P Q H. destruct H as [HP HQ].  apply HP.
Qed.

Definition proj1'' (P Q : Prop) (H : P /\ Q) :=
  match H with
  | conj HP HQ => HP
  end. 
  
Print proj1'.

Inductive or (P Q : Prop) : Prop :=
  | or_introl : P -> or P Q
  | or_intror : Q -> or P Q.
Arguments or_introl [P] [Q].
Arguments or_intror [P] [Q].
Notation "P \/ Q" := (or P Q) : type_scope.

Definition inj1 (P Q : Prop) (HP: P) : (P \/ Q) :=
  or_introl HP.
  
Theorem inj1' : forall (P Q : Prop),
  P -> P \/ Q.
Proof. intros P Q HP. left. apply HP. Qed.

Print inj1'.
End And_Or.

Module Nat.

Inductive nat : Type :=
| O : nat
| S : nat -> nat.

Check nat_ind.

End Nat.

Inductive time : Type :=
| day : time
| night : time.

Check time_ind.

Module List.

Inductive list (X: Type) : Type :=
| nil : list X
| cons : X -> list X -> list X.

Check list_ind.

End List.

Check list_ind.

(** The induction principle for nat and time are 
automatically generated by Rocq when the inductive types
 are defined. *)
 
Check ev_ind.
