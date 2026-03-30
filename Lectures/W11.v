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
- Our goal is now to prove that well-typed terms in STLC do not
get stuck during reduction.
- We first consider the form of well-styped terms which are also
values.

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
    




