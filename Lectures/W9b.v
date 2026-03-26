(**

Small-step operational semantics
Ref.: Software Foundations, Volume 2, SmallStep.v

*)


Set Warnings "-notation-overridden".

From PLF Require Import Maps.
Require Import Bool.
Require Import Arith.
Require Import EqNat.
Require Import PeanoNat. Import Nat.
Require Import Lia.
From PLF Require Import Imp.
(**
Small-step operational semantics
--------------------------------------

- The evaluation rules that we have seen so far for the IMP
language are known as 'big-step' operational semantics.
- [st =[c]=> st'] directly relates the final state st' to the 
initial state st.
- Good for whole program reasoning.
- However, we would like to expose the intermediate states that
would be required to reach the final state.
- Useful for finding errors and expressing semantics of concurrent
programs
- This is formalized using 'small-step' semantics.

We will demonstrate small-step semantics with a toy language first,
and then move to IMP.
*)

Inductive tm : Type :=
  | C : nat -> tm         (* Constant *)
  | P : tm -> tm -> tm.   (* Plus *)

Fixpoint evalF (t : tm) : nat :=
  match t with
  | C n => n
  | P t1 t2 => evalF t1 + evalF t2
  end.

Reserved Notation " t '==>' n " (at level 50, left associativity).

Inductive eval : tm -> nat -> Prop :=
  | E_C : forall n,
      C n ==> n
  | E_P : forall t1 t2 n1 n2,
      t1 ==> n1 ->
      t2 ==> n2 ->
      P t1 t2 ==> (n1 + n2)

where " t '==>' n " := (eval t n).

Module SimpleArith1.

Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_PCC : forall n1 n2,
      P (C n1) (C n2) --> C (n1 + n2)
  | ST_P1 : forall t1 t1' t2,
      t1 --> t1' ->
      P t1 t2 --> P t1' t2
  | ST_P2 : forall n1 t2 t2',
      t2 --> t2' ->
      P (C n1) t2 --> P (C n1) t2'

  where " t '-->' t' " := (step t t').

(**
- Notice that step is a binary relation over terms, as compared to the
eval relation which related a term with a number.
- Can be thought of a as a single step in an abstract machine which
is trying to evaluate a term.
*)

Example test_step_1 :
      P
        (P (C 1) (C 3))
        (P (C 2) (C 4))
      -->
      P
        (C 4)
        (P (C 2) (C 4)).
Proof.
  apply ST_P1. apply ST_PCC.  Qed.

Example test_step_2 :
      P
        (C 0)
        (P
          (C 2)
          (P (C 1) (C 3)))
      -->
      P
        (C 0)
        (P
          (C 2)
          (C 4)).
Proof. apply ST_P2. apply ST_P2. apply ST_PCC. Qed. 

End SimpleArith1.

(**
We now define the concept of a value, which a special kind of term
which cannot take a step.
*)

Inductive value : tm -> Prop :=
  | v_C : forall n, value (C n).

  Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_PCC : forall n1 n2,
          P (C n1) (C n2)
      --> C (n1 + n2)
  | ST_P1 : forall t1 t1' t2,
        t1 --> t1' ->
        P t1 t2 --> P t1' t2
  | ST_P2 : forall v1 t2 t2',
        value v1 ->                     (* <--- new *)
        t2 --> t2' ->
        P v1 t2 --> P v1 t2'

  where " t '-->' t' " := (step t t').

Theorem step_deterministic: forall (x y1 y2 : tm),
  step x y1 -> step x y2 -> y1 = y2.
Proof. intros x y1 y2 Hy1. generalize dependent y2. induction Hy1; intros y2 Hy2.
  - inversion Hy2; subst.
    -- reflexivity.
    -- inversion H2.
    -- inversion H3.
  - inversion Hy2; subst.
    -- inversion Hy1.
    -- apply IHHy1 in H2. rewrite H2. reflexivity.
    -- destruct H1. inversion Hy1.
  - inversion Hy2; subst.
    -- inversion Hy1.
    -- destruct H. inversion H3.
    -- apply IHHy1 in H4. rewrite H4. reflexivity.
Qed.

(** While the single-step relation that we have defined is deterministic,
it is possible to define non-deterministic small step operational
semantics *)

Module NonDetStep.

Inductive step : tm -> tm -> Prop :=
  | ST_PCC : forall n1 n2,
          P (C n1) (C n2)
      --> C (n1 + n2)
  | ST_P1 : forall t1 t1' t2,
        t1 --> t1' ->
        P t1 t2 --> P t1' t2
  | ST_P2 : forall t1 t2 t2',
        t2 --> t2' ->
        P t1 t2 --> P t1 t2'

  where " t '-->' t' " := (step t t').

Theorem step_non_deteministic: exists (x y1 y2 : tm),
  x --> y1 /\ x --> y2 /\ y1 <> y2.
Proof. exists (P (P (C 1) (C 1)) (P (C 1) (C 1))).
  exists (P (C 2) (P (C 1) (C 1))). exists (P (P (C 1) (C 1)) (C 2)).
  split.
  - apply ST_P1. constructor.
  - split. 
    -- apply ST_P2. constructor.
    -- unfold not; intros; discriminate H.
Qed.

End NonDetStep.



(**
We can also prove a 'strong progress' property: Either a term is a
value, or it can take a step.
*)

Theorem strong_progress : forall x,
  value x \/ (exists x', x --> x').
Proof.
  induction x.
  - left. constructor.
  - destruct IHx1 as [Iv1 | [x' It1]].
    -- destruct IHx2 as [Iv2 | [x' It2]].
       * inversion Iv1; subst. inversion Iv2; subst. 
         right. exists (C (n + n0)). constructor.
       * right. exists (P x1 x'). constructor; assumption.
    -- right. exists (P x' x2). constructor; assumption.
Qed.   

(**
A term which cannot progress is are said to be in normal form.
We formalize this below:
*)

Definition relation (X : Type) := X -> X -> Prop.

Definition normal_form {X : Type}
              (R : relation X) (t : X) : Prop :=
  ~ exists t', R t t'.

(** For our toy language, values are exactly those terms which are in
normal form. However, this may not be true in general.
 *)

Lemma value_is_nf : forall v,
  value v -> normal_form step v.
Proof.
  unfold normal_form. intros v H contra.
  destruct contra. destruct H. inversion H0.
Qed.

Lemma nf_is_value : forall t,
  normal_form step t -> value t.
Proof. (* a corollary of [strong_progress]... *)
  unfold normal_form. intros t H.
  assert (G : value t \/ exists t', t --> t').
  { apply strong_progress. }
  destruct G as [G | G].
  - (* l *) apply G.
  - (* r *) contradiction.
Qed.

(** Multi-step reduction 

We would like to relate terms t -->* t' where t' can be obtained by
performing multiple (zero or more) steps of reduction from t.

*)

Inductive multi {X : Type} (R : relation X) : relation X :=
| multi_refl : forall (x : X), multi R x x
| multi_step : forall (x y z : X),
                  R x y ->
                  multi R y z ->
                  multi R x z.
                  
Theorem multi_trans : forall (X : Type) (R : relation X)
 (a b c : X), multi R a b -> multi R b c -> multi R a c.
Proof. intros. induction H.
- assumption.
- eapply multi_step. apply H. auto.
Qed. 

Notation " t '-->*' t' " := (multi step t t') (at level 40).

Definition normal_form_of {X : Type} (R : relation X)  (t t' : X) :=
  ((multi R) t t' /\ normal_form R t').

(**
Since the step relation is deterministic, every term also has a
unique normal form:
*)

Theorem normal_forms_unique: forall (x y1 y2 : tm),
 normal_form_of step x y1 -> normal_form_of step x y2 -> y1 = y2.
Proof. unfold normal_form_of. intros. destruct H as [H11 H12].
  destruct H0 as [H21 H22].
  induction H11.
  - apply nf_is_value in H12. inversion H21; subst. reflexivity.
    destruct H12. inversion H.
  - apply IHmulti. assumption. inversion H21; subst.
    -- apply nf_is_value in H22. destruct H22. inversion H.
    -- replace y with y0. assumption. apply step_deterministic with (x := x); assumption.
Qed.     

(** We can also say something stronger: for our language, for any 
term, its normal form can be obtained by applying a *finite* number
of reduction steps. Such a language is called normalizing*)
      
Definition normalizing {X : Type} (R : relation X) :=
  forall t, exists t', normal_form_of R t t'.

Lemma multistep_congr_1 : forall t1 t1' t2,
  t1 -->* t1' -> P t1 t2 -->* P t1' t2.
Proof. intros. induction H.
- constructor.
- eapply multi_step. eapply ST_P1. apply H. assumption.
Qed.

Lemma multistep_congr_2 : forall v1 t2 t2',
  value v1 -> t2 -->* t2' -> P v1 t2 -->* P v1 t2'.
Proof. intros. induction H0.
- constructor.
- eapply multi_step. eapply ST_P2. assumption. apply H0. assumption.
Qed.

Theorem step_normalizing : normalizing step.
Proof. intros t. induction t.
- exists (C n). unfold normal_form_of. split.
  -- constructor.
  -- apply value_is_nf. constructor.
- destruct IHt1 as [v1 IHt1]. destruct IHt2 as [v2 IHt2].
  unfold normal_form_of in *. destruct IHt1 as [H11 H12].
  destruct IHt2 as [H21 H22]. apply nf_is_value in H12.
  apply nf_is_value in H22. destruct H12 as [n1]. destruct H22 as [n2].
  exists (C (n1 + n2)). split.
  * apply multi_trans with (b := P (C n1) t2).
    ** apply multistep_congr_1. assumption.
    ** apply multi_trans with (b := P (C n1) (C n2)).
       *** apply multistep_congr_2. constructor. assumption.
       *** eapply multi_step; constructor.
  * apply value_is_nf. constructor.  
Qed.

(** Homework: We can also prove that the big step and small step 
reductions are equivalent to each other:

t ==> n -> t -->* C n.
*)

(**
Small step semantics for IMP

*)

Inductive aval : aexp -> Prop :=
  | av_num : forall n, aval (ANum n).


Reserved Notation " a '/' st '-->a' a' "
                  (at level 40, st at next level, left associativity).
Inductive astep (st : state) : aexp -> aexp -> Prop :=
  | AS_Id : forall (i : string),
      i / st -->a ANum (st i)
  | AS_P1 : forall a1 a1' a2,
      a1 / st -->a a1' ->
      <{ a1 + a2 }> / st -->a <{ a1' + a2 }>
  | AS_P2 : forall v1 a2 a2',
      aval v1 ->
      a2 / st -->a a2' ->
      <{ v1 + a2 }>  / st -->a <{ v1 + a2' }>
  | AS_P : forall (v1 v2 : nat),
      <{ v1 + v2 }> / st -->a ANum (v1 + v2)
  | AS_Minus1 : forall a1 a1' a2,
      a1 / st -->a a1' ->
      <{ a1 - a2 }> / st -->a <{ a1' - a2 }>
  | AS_Minus2 : forall v1 a2 a2',
      aval v1 ->
      a2 / st -->a a2' ->
      <{ v1 - a2 }>  / st -->a <{ v1 - a2' }>
  | AS_Minus : forall (v1 v2 : nat),
      <{ v1 - v2 }> / st -->a ANum (v1 - v2)
  | AS_Mult1 : forall a1 a1' a2,
      a1 / st -->a a1' ->
      <{ a1 * a2 }> / st -->a <{ a1' * a2 }>
  | AS_Mult2 : forall v1 a2 a2',
      aval v1 ->
      a2 / st -->a a2' ->
      <{ v1 * a2 }>  / st -->a <{ v1 * a2' }>
  | AS_Mult : forall (v1 v2 : nat),
      <{ v1 * v2 }> / st -->a ANum (v1 * v2)

    where " a '/' st '-->a' a' " := (astep st a a').

Reserved Notation " b '/' st '-->b' b' "
                  (at level 40, st at next level, left associativity).
Inductive bstep (st : state) : bexp -> bexp -> Prop :=
| BS_Eq1 : forall a1 a1' a2,
    a1 / st -->a a1' ->
    <{ a1 = a2 }> / st -->b <{ a1' = a2 }>
| BS_Eq2 : forall v1 a2 a2',
    aval v1 ->
    a2 / st -->a a2' ->
    <{ v1 = a2 }> / st -->b <{ v1 = a2' }>
| BS_Eq : forall (v1 v2 : nat),
    <{ v1 = v2 }> / st -->b
    (if (v1 =? v2) then BTrue else BFalse)
| BS_LtEq1 : forall a1 a1' a2,
    a1 / st -->a a1' ->
    <{ a1 <= a2 }> / st -->b <{ a1' <= a2 }>
| BS_LtEq2 : forall v1 a2 a2',
    aval v1 ->
    a2 / st -->a a2' ->
    <{ v1 <= a2 }> / st -->b <{ v1 <= a2' }>
| BS_LtEq : forall (v1 v2 : nat),
    <{ v1 <= v2 }> / st -->b
    (if (v1 <=? v2) then BTrue else BFalse)
| BS_NotStep : forall b1 b1',
    b1 / st -->b b1' ->
    <{ ~ b1 }> / st -->b <{ ~ b1' }>
| BS_NotTrue  : <{ ~ true }> / st  -->b <{ false }>
| BS_NotFalse : <{ ~ false }> / st -->b <{ true }>
| BS_AndStep : forall b1 b1' b2,
    b1 / st -->b b1' ->
    <{ b1 && b2 }> / st -->b <{ b1' && b2 }>
| BS_AndTrueStep : forall b2 b2',
    b2 / st -->b b2' ->
    <{ true && b2 }> / st -->b <{ true && b2' }>
| BS_AndFalse : forall b2,
    <{ false && b2 }> / st -->b <{ false }>
| BS_AndTrueTrue  : <{ true && true  }> / st -->b <{ true }>
| BS_AndTrueFalse : <{ true && false }> / st -->b <{ false }>

where " b '/' st '-->b' b' " := (bstep st b b').

Reserved Notation " t '/' st '-->' t' '/' st' "
                  (at level 40, st at next level, t' at next level, left associativity).
Inductive cstep : (com * state) -> (com * state) -> Prop :=
  | CS_AsgnStep : forall st i a1 a1',
      a1 / st -->a a1' ->
      <{ i := a1 }> / st --> <{ i := a1' }> / st
  | CS_Asgn : forall st i (n : nat),
      <{ i := n }> / st --> <{ skip }> / (i !-> n ; st)
  | CS_SeqStep : forall st c1 c1' st' c2,
      c1 / st --> c1' / st' ->
      <{ c1 ; c2 }> / st --> <{ c1' ; c2 }> / st'
  | CS_SeqFinish : forall st c2,
      <{ skip ; c2 }> / st --> c2 / st
  | CS_IfStep : forall st b1 b1' c1 c2,
      b1 / st -->b b1' ->
      <{ if b1 then c1 else c2 end }> / st
      -->
      <{ if b1' then c1 else c2 end }> / st
  | CS_IfTrue : forall st c1 c2,
      <{ if true then c1 else c2 end }> / st --> c1 / st
  | CS_IfFalse : forall st c1 c2,
      <{ if false then c1 else c2 end }> / st --> c2 / st
  | CS_While : forall st b1 c1,
      <{ while b1 do c1 end }> / st
      -->
      <{ if b1 then c1; while b1 do c1 end else skip end }> / st

  where " t '/' st '-->' t' '/' st' " := (cstep (t,st) (t',st')).

(** Concurrent IMP

We now add parallelism to the IMP language to demonstrate the
power of small-step operational semantics.

     c := skip
        | x := a
        | c ; c
        | if b then c else c end
        | while b do c end
        | c || c                     <---------- new

Example-1:
-------------------

      X := 0 || X := 1

After execution, the value of X in the final state can be either
0 or 1.

Example-2:
-------------------
      X := 0; (X := X+2 || X := X+1 || X := 0)

After execution, the value of X in the final state can be either
0, 1, 2 or 3.
*)

Module CImp.

Inductive com : Type :=
  | CSkip : com
  | CAsgn : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CPar : com -> com -> com.         (* <--- NEW: c1||c2 *)

Notation "x '||' y" := (CPar x y)
  (in custom com at level 100, right associativity,
    format "'[v'   x '/' '||' '/ '  y ']'").
Notation "'skip'"  := CSkip
  (in custom com at level 0) : com_scope.
Notation "x := y"  := (CAsgn x y)
  (in custom com at level 0, x constr at level 0, y at level 85, no associativity,
    format "x  :=  y") : com_scope.
Notation "x ; y" := (CSeq x y)
  (in custom com at level 90,
    right associativity,
    format "'[v' x ; '/' y ']'") : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" := (CIf x y z)
  (in custom com at level 89, x at level 99, y at level 99, z at level 99,
    format "'[v' 'if'  x  'then' '/  ' y '/' 'else' '/  ' z '/' 'end' ']'") : com_scope.
Notation "'while' x 'do' y 'end'" := (CWhile x y)
  (in custom com at level 89, x at level 99, y at level 99,
    format "'[v' 'while'  x  'do' '/  ' y '/' 'end' ']'") : com_scope.

Inductive cstep : (com * state)  -> (com * state) -> Prop :=
    (* Old part: *)
  | CS_AsgnStep : forall st i a1 a1',
      a1 / st -->a a1' ->
      <{ i := a1 }> / st --> <{ i := a1' }> / st
  | CS_Asgn : forall st i (n : nat),
      <{ i := n }> / st --> <{ skip }> / (i !-> n ; st)
  | CS_SeqStep : forall st c1 c1' st' c2,
      c1 / st --> c1' / st' ->
      <{ c1 ; c2 }> / st --> <{ c1' ; c2 }> / st'
  | CS_SeqFinish : forall st c2,
      <{ skip ; c2 }> / st --> c2 / st
  | CS_IfStep : forall st b1 b1' c1 c2,
      b1 / st -->b b1' ->
      <{ if b1 then c1 else c2 end }> / st
      -->
      <{ if b1' then c1 else c2 end }> / st
  | CS_IfTrue : forall st c1 c2,
      <{ if true then c1 else c2 end }> / st --> c1 / st
  | CS_IfFalse : forall st c1 c2,
      <{ if false then c1 else c2 end }> / st --> c2 / st
  | CS_While : forall st b1 c1,
      <{ while b1 do c1 end }> / st
      -->
      <{ if b1 then c1; while b1 do c1 end else skip end }> / st
    (* New part: *)
  | CS_Par1 : forall st c1 c1' c2 st',
      c1 / st --> c1' / st' ->
      <{ c1 || c2 }> / st --> <{ c1' || c2 }> / st'
  | CS_Par2 : forall st c1 c2 c2' st',
      c2 / st --> c2' / st' ->
      <{ c1 || c2 }> / st --> <{ c1 || c2' }> / st'
  | CS_ParDone : forall st,
      <{ skip || skip }> / st --> <{ skip }> / st

  where " t '/' st '-->' t' '/' st' " := (cstep (t,st) (t',st')).

Notation " t '/' st '-->*' t' '/' st' " :=
   (multi cstep  (t,st) (t',st'))
   (at level 40, st at next level, t' at next level, left associativity).

Definition par_ex_1 : com :=
<{ X := 0 || X := 1}>.

Example par_ex_1_exec : 
  (exists st1, par_ex_1/empty_st -->* <{skip}>/st1 /\ st1 X = 0)
  /\ (exists st2, par_ex_1/empty_st -->* <{skip}>/st2 /\ st2 X = 1).
Proof. unfold par_ex_1. split.
  - eexists. split. 
    * eapply multi_step. eapply CS_Par2. apply CS_Asgn. 
      eapply multi_step. eapply CS_Par1. apply CS_Asgn.
      eapply multi_step. apply CS_ParDone. apply multi_refl.
    * apply t_update_eq.
  - eexists. split. 
    * eapply multi_step. eapply CS_Par1. apply CS_Asgn. 
      eapply multi_step. eapply CS_Par2. apply CS_Asgn.
      eapply multi_step. apply CS_ParDone. apply multi_refl.
    * apply t_update_eq.
Qed. 

End CImp.

(**
Homework: Prove the final states for Example-2.
*)
