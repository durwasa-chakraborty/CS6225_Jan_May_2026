(**
Type theory and Lambda Calculus

Ref.: Software Foundations, Vol. 2, StlcProp.v

*)


Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From PLF Require Import Maps.
(* From PLF Require Import Types. *)
From Lectures Require Import W10.
From Lectures Require Import W9b.
Set Default Goal Selector "!".
Module STLCProp.
Import STLC.

(**
- Our goal is to prove that well-typed terms in STLC do not
get stuck during reduction.
- We first consider the well-typed terms which are also
values. Such terms are said to be in canonical forms.

*)

Lemma canonical_forms_bool : forall t,
  <{ empty |-- t \in Bool }> ->
  value t ->
  (t = <{true}>) \/ (t = <{false}>).
Proof.
  intros t HT HVal.
  destruct HVal; auto.
  inversion HT.
Qed.

Lemma canonical_forms_fun : forall t T1 T2,
  <{ empty |-- t \in T1 -> T2 }> ->
  value t ->
  exists x u, t = <{\x:T1, u}>.
Proof.
  intros t T1 T2 HT HVal.
  destruct HVal as [x ? t1| |] ; inversion HT; subst.
  exists x, t1. reflexivity.
Qed.

(**
- We now prove the 'weak progress' theorem, which says that any
well-typed term is either a value or it can take a reduction step.
- We will prove this using structural induction on terms.
*)

Theorem progress : forall t T,
  <{ empty |-- t \in T }> ->
  value t \/ exists t', t --> t'.
Proof. intros t. induction t.
- (* t = tm_var s *) 
  intros. inversion H; subst. discriminate H2.
- (* t = tm_app t1 t2 *) 
  intros. inversion H; subst.
  assert (L: <{ empty |-- t1 \in T2 -> T }>). { assumption. }
  apply IHt1 in H3. 
  destruct H3 as [Ht1v | [t' Ht1nv]].
  -- (* t1 is a value *)
    assert (Lt1: exists x u, t1 = <{\x:T2, u}>).
    { apply canonical_forms_fun with (T2 := T); assumption. }
    destruct Lt1 as [x [u Lt1]].
    right. apply IHt2 in H5. destruct H5 as [Ht2v | [t' Ht2nv]].
    --- (* t2 is a value *)
        exists (<{ [x:=t2]u }>). rewrite Lt1. 
        apply ST_AppAbs; assumption.
    --- (* t2 takes a step *)
        exists (<{ t1 t' }>). apply ST_App2; assumption.
  -- (* t1 takes a step *)
     right. exists (<{ t' t2 }>). apply ST_App1; assumption.
- (* t = t_abs s t t0*)
  intros. left. constructor.
- (* t = tm_true *)
  intros; left; constructor.
- (* t = tm_false *)
  intros; left; constructor.
- (* t = tm_if t1 t2 t3 *)
  intros. inversion H; subst.
  assert (L: <{ empty |-- t1 \in Bool }>). { assumption. }
  apply IHt1 in H4. destruct H4 as [Ht1v | [t' Ht1nv]].
  -- (* t1 is a value *)
    assert (Lt1: (t1 = <{true}>) \/ (t1 = <{false}>)).
    { apply canonical_forms_bool; assumption. }
    right. destruct Lt1 as [Lt1tru | Lt1fls].
    --- exists t2. rewrite Lt1tru. constructor.
    --- exists t3. rewrite Lt1fls. constructor.
  -- (* t1 takes a step *)
     right. exists (<{if t' then t2 else t3}>). 
     constructor; assumption.
Qed.

(**
- We now want to show a well-typed term never gets stuck during
multi-step reduction.

Formally, empty |-- t \in T ->
          t -->* t' ->
          value t' \/ exists t'', t' --> t''.
        
- To prove this, we will first show that if a well-typed term takes
 a step, the resulting term continues to remain well-typed.
  -- In fact, we will show that it will have the same type.
- Also known as preservation theorem.

Formally, empty |-- t \in T ->
          t --> t' ->
          empty |-- t' \in T

- To prove preservation, we first need to show that substitution 
preserves type.

Formally, x |-> U; Gamma |-- t \in T ->
          empty |-- v \in U ->
          Gamma |-- [x := v] t \in T

- To prove that substitution preserves type, we will need to prove 
that a term which is well-typed in a context Gamma continues to remain
well-typed in a context Gamma' which includes all the bindings of 
Gamma,

Formally, includedin Gamma Gamma' ->
          Gamma |-- t \in T ->
          Gamma' |-- t \in T

*)

(** Definition of [includedin] from Maps.v:

Definition includedin {A : Type} (m m' : partial_map A) :=
  forall x v, m x = Some v -> m' x = Some v.

*)

Lemma weakening : forall Gamma Gamma' t T,
     includedin Gamma Gamma' ->
     <{ Gamma  |-- t \in T }>  ->
     <{ Gamma' |-- t \in T }>.
Proof. intros Gamma Gamma' t T Hin HGt. 
  generalize dependent Gamma'. induction HGt.
  - (* t = <{x0}> *) 
    intros. apply T_Var. apply Hin. assumption.
  - (* t = <{\x0 : T2, t1}> *)
    intros. apply T_Abs. apply IHHGt. apply includedin_update.
    assumption.
  - (* t = <{t1 t2}> *) 
    intros. apply T_App with (T2 := T2). 
    -- apply IHHGt1; assumption.
    -- apply IHHGt2; assumption.
  - (* t = <{true}> *) intros; constructor.
  - (* t = <{false}> *)intros; constructor.
  - (* t = <{if t1 then t2 else t3}> *)
    intros; apply T_If; auto.
Qed.

Lemma weakening_empty : forall Gamma t T,
     <{ empty |-- t \in T }> ->
     <{ Gamma |-- t \in T }>.
Proof.
  intros Gamma t T.
  apply weakening.
  discriminate.
Qed.

Theorem substitution_preserves_type: forall (t v : tm) Gamma 
(x : string) (T U : ty) ,
  <{x |-> U ; Gamma |-- t \in T}> ->
  <{empty |-- v \in U}> ->
  <{Gamma |-- [x := v] t \in T}>.
Proof. intros t. induction t; intros v Gamma x T U HTypet HTypev. 
  - (* t = <{s}> *) 
    destruct (String.eqb x s) eqn:E.
    -- simpl. rewrite E. inversion HTypet; subst. 
       apply String.eqb_eq in E. rewrite E in H1. 
       rewrite update_eq in H1. injection H1 as H1. 
       rewrite <- H1. apply weakening_empty; assumption.
    -- simpl. rewrite E. inversion HTypet; subst. apply T_Var.
       rewrite <- H1. apply String.eqb_neq in E. symmetry.
       apply update_neq; assumption.
  - (* t = <{t1 t2}> *)
    inversion HTypet; subst. simpl. 
    apply T_App with (T2 := T2); eauto.
  - (* t = <{\s : t, t0}> *) 
    inversion HTypet; subst. simpl. destruct (String.eqb x s) eqn:E.
    -- apply T_Abs. apply String.eqb_eq in E. rewrite E in H4. 
       rewrite update_shadow in H4. assumption.
    -- apply T_Abs. apply IHt with (U := U).
       * apply String.eqb_neq in E. 
         replace (x |-> U; s |-> t; Gamma) with (s |-> t; x |-> U; Gamma).
         ** assumption.
         ** apply update_permute; assumption.
       * assumption.
  - (* t = <{true}>*)
    inversion HTypet; subst. simpl. constructor.
  - (* t = <{false}>*)
    inversion HTypet; subst; simpl; constructor. 
  - (* t = <{if t1 then t2 else t3}>*)
    simpl. inversion HTypet; subst.  
    apply T_If; eauto.
Qed.


Theorem preservation : forall t t' T,
  <{ empty |-- t \in T }> ->
  t --> t'  ->
  <{ empty |-- t' \in T }>.
Proof. intros t t' T HType Hstep. generalize dependent t'.
 remember empty as Gamma. induction HType; intros.
  - (* t = x0 *)
    inversion Hstep.
  - (* t = \x0 : T2, t1 *)
    inversion Hstep.
  - (* t = t1 t2 *)
    inversion Hstep; subst.
    -- (* t1 --> t1' *)
      apply T_App with (T2 := T2); eauto. 
    -- (* t2 --> t2' *)
      apply T_App with (T2 := T2); eauto. 
    -- (* (\x0 : T, t) t2 --> [x0 := t2] t *)
     inversion HType1; subst. 
     apply substitution_preserves_type with (U := T2); auto.
  - (* t = true *)
    inversion Hstep.
  - (* t = false *)
    inversion Hstep.
  - (* t = if t1 then t2 else t3 *)
    inversion Hstep;subst;eauto.
Qed.

(** The converse of preservation does not necessarily hold:*)
  
Theorem not_subject_expansion:
  exists t t' T, t --> t' /\ <{ empty |-- t' \in T }> 
  /\ ~ <{ empty |-- t \in T }>.
Proof. exists <{(\x : Bool -> Bool, x) true}>. exists <{true}>.
  exists <{{Bool}}>. split.
  - apply ST_AppAbs. constructor.
  - split;auto. intros contra. inversion contra; subst.
    inversion H4; subst. inversion H2; subst.
Qed.

Definition stuck (t:tm) : Prop :=
  (normal_form step) t /\ ~ value t.

Corollary type_soundness : forall t t' T,
  <{ empty |-- t \in T }> ->
  t -->* t' ->
  ~(stuck t').
Proof. intros t t' T Htype Hstep. induction Hstep.
  - unfold stuck, normal_form. intros contra. 
    apply progress in Htype. destruct contra as [C1 C2].
    destruct Htype as [H1 | H2]; auto.
  - apply IHHstep. eapply preservation.
    -- apply Htype.
    -- apply H.
Qed.

(** More on STLC in the book:

- Context Invariance: A more general form of the weakening lemma.
  -- If a term [t] is well-typed under [Gamma], it continues to 
  remain well-typed under 'inessential changes' to [Gamma]. 
  In particlar, the types all of the free variables in [t] should 
  remain the same.
- Adding more features to STLC: numbers, pairs, records, lists,
  recursion, mutable references.
- Adding support for inclusion polymorphism using Subtyping.
- Normalization.
*)




