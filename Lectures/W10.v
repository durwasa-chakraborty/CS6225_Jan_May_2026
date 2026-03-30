(**
Type theory and Lambda Calculus

Ref.: Software Foundations, Vol. 2, Stlc.v

*)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
Require Import Arith.
From PLF Require Import Maps.
Require Import Strings.String.
From Lectures Require Import W9b.
Set Default Goal Selector "!".

Hint Constructors multi : core.

(** Types 
- Types are a static/compile-time mechanism to guarantee simple
properties about run-time behavior of programs, e.g. termination,
no crashes, memory-safety, no overflow, etc.
- To illustrate types, we will use an abstract programming language
called Lambda Calculus, which encapsulates the core ideas of 
functions/abstraction.
- First, we will consider untyped lambda calculus.
*)

Module UnTyped_LC.
(**
   t ::=     x                         (variable)
           | \x,t                      (abstraction)
           | t1 t2                     (application)
           | true                      (constant true)
           | false                     (constant false)
           | if t1 then t2 else t3     (conditional)

*)

(** Some examples:

      - [\x, x]

        The identity function.

      - [(\x, x) true]

        The identity function, applied to the boolean [true].

      - [\x, if x then false else true]

        The boolean "not" function.

      - [\x, true]

        The constant function that takes every argument to
        [true]. *)

(**
      - [\x, \y, x]

        A two-argument function that returns the first one. *)

(** (As in Rocq, a two-argument function in the
    lambda-calculus is really a one-argument function whose body
    is also a one-argument function.) *)

(**   - [(\x, \y, x) false true]

    A two-argument function that returns the first one, 
    applied to the booleans [false] and [true]. *)

(** (As in Rocq, application associates to the left -- i.e., this
    expression is parsed as [((\x, \y, x) false) true].) *)

(**
      - [\f, f (f true)]

      A higher-order function that takes a _function_ [f] 
      as an argument, applies [f] to [true],
      and applies [f] again to the result.

      - [(\f, f (f true)) (\x, false)]

        The same higher-order function, applied to the constantly
        [false] function. *)

Inductive tm : Type :=
  | tm_var   : string -> tm
  | tm_app   : tm -> tm -> tm
  | tm_abs   : string -> tm -> tm
  | tm_true  : tm
  | tm_false : tm
  | tm_if    : tm -> tm -> tm -> tm.

(** Values in Lambda Calculus

- true, false are boolean values.
- An application should not be a value (as it can be simplified 
further).
- An if-then-else term also should not be a value.
- An abstraction is always a value (irrespective of whether its
body can be simplified further).
*)

Inductive value : tm -> Prop :=
  | v_abs : forall x t1,
      value (tm_abs x t1)
  | v_true :
      value tm_true
  | v_false :
      value tm_false.
      
(** The substitution operation
- Goal: to substitute a term at every occurrence of a variable 
in another term.
- Needed to define the operational semantics of function application
- [(\x, t) s] should be reduced to [subst x s t]

For example, we reduce

       (\x, if x then true else x) false

    to

       if false then true else false

Some examples for substitution:

- [subst x true x] should be [true]
- [subst x true y] should be [y]
- [subst x true (if x then true else false)]
     should be [if true then true else false]
- [subst x true (\y, if y then x else false)]
     should be [\y, if y then true else false]
- [subst x true (\y, y)] should be [\y, y]
- [subst x true (\x, x)] should be [\x, x]
*)
      
Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | tm_var y =>
      if String.eqb x y then s else t
  | tm_abs y t1 =>
      if String.eqb x y then t else tm_abs y (subst x s t1)
  | tm_app t1 t2 =>
      tm_app (subst x s t1) (subst x s t2)
  | tm_true =>
      tm_true
  | tm_false =>
      tm_false
  | tm_if t1 t2 t3  =>
      tm_if (subst x s t1) (subst x s t2) (subst x s t3)
  end.
  
Reserved Notation "t '-->' t'" (at level 40).

(**
Note: Substitution becomes trickier when [s] (the term being 
substituted) contains a free variable.

Example:
   subst z (\x, r) (\r, z)
   (where [r] is a _free_ variable) 
   substituted for the free variable [z] in the term

   we would get

     \r, \x, r

    where the free reference to [r] has been "captured" by
    the binder.
    
    This is undesirable because [\w, z] is identical to 
    [\r, z], but [subst z (\x, r) (\w, z)] would yield [\w, \x, r] which is not
    identical to [\r, \x, r].
    
In our setting, we will assume that terms being substituted do
not have free variables. Hence, we don't have to worry about the
above complexity.
*)

(** We can now define the small-step semantics of lambda calculus*)

Inductive step : tm -> tm -> Prop :=
  | ST_App1 : forall t1 t1' t2,
         t1 --> t1' ->
         tm_app t1 t2 --> tm_app t1' t2
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         tm_app v1 t2 --> tm_app v1  t2'
  | ST_AppAbs : forall x t v,
         value v ->
         tm_app (tm_abs x t) v --> subst x v t
  | ST_IfTrue : forall t1 t2,
      tm_if tm_true t1 t2 --> t1
  | ST_IfFalse : forall t1 t2,
       tm_if tm_false t1 t2 --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      tm_if t1 t2 t3 --> tm_if t1' t2 t3

where "t '-->' t'" := (step t t').

(**
To ensure determinism, for an app term [t1 t2], first the function
term [t1] is reduced to a value, then the arguement term [t2] is 
reduced to a value, and finally substitution is performed.
- Known as call-by-value reduction.

*)

(**
While the semantics is deterministic, it does not unfortunately
satisfy the strong progress theorem.

That is, there are non-value terms which cannot take a step.
Such terms are called 'stuck' terms.

Examples:
- true false
- if (\x, x) then true else false

There are terms which are not stuck, but which get stuck after
reduction:
- ((\f, f false) true)
- (if true then true else (\x, x)) false
- (\x, \y, x y) true false
*)

Notation step_normal_form := (normal_form step).

Definition stuck (t : tm) : Prop :=
  step_normal_form t /\ ~ value t.

Example some_term_is_stuck :
  exists t, stuck t.
Proof. exists (tm_app tm_true tm_false). unfold stuck, step_normal_form,
  normal_form. split.
  - intros [t' contra]. inversion contra.
    * inversion H2.
    * inversion H3.
  - intros contra. inversion contra.
Qed.

End UnTyped_LC.
Module STLC.

(* ================================================================= *)
(** 
- Our goal is to use types to define terms in lambda calculus which
never get stuck (even after reduction).
- Terms will now be annotated with types.
  -- Also known as Simply Typed Lambda Calculus (STLC).
- The compiler can check whether a term is 'well-typed'.
- We will formally prove that 'well-typed' terms never get
stuck.
*)

Inductive ty : Type :=
  | Ty_Bool  : ty
  | Ty_Arrow : ty -> ty -> ty.

(* ================================================================= *)
(** ** Terms *)

Inductive tm : Type :=
  | tm_var   : string -> tm
  | tm_app   : tm -> tm -> tm
  | tm_abs   : string -> ty -> tm -> tm
  | tm_true  : tm
  | tm_false : tm
  | tm_if    : tm -> tm -> tm -> tm.

Declare Scope stlc_scope.
Delimit Scope stlc_scope with stlc.
Open Scope stlc_scope.

Declare Custom Entry stlc_ty.
Declare Custom Entry stlc_tm.

Notation "x" := x (in custom stlc_ty at level 0, x global) : stlc_scope.

Notation "<{{ x }}>" := x (x custom stlc_ty).

Notation "( t )" := t (in custom stlc_ty at level 0, t custom stlc_ty) : stlc_scope.
Notation "S -> T" := (Ty_Arrow S T) (in custom stlc_ty at level 99, right associativity) : stlc_scope.

Notation "$( t )" := t (in custom stlc_ty at level 0, t constr) : stlc_scope.

Notation "'Bool'" := Ty_Bool (in custom stlc_ty at level 0) : stlc_scope.
Notation "'if' x 'then' y 'else' z" :=
  (tm_if x y z) (in custom stlc_tm at level 200,
                    x custom stlc_tm,
                    y custom stlc_tm,
                    z custom stlc_tm at level 200,
                    left associativity).
Notation "'true'"  := true (at level 1).
Notation "'true'"  := tm_true (in custom stlc_tm at level 0).
Notation "'false'"  := false (at level 1).
Notation "'false'"  := tm_false (in custom stlc_tm at level 0).

Check <{{ Bool }}>.
Check <{{ Bool -> Bool }}>.
Check <{{ (Bool -> Bool) -> Bool }}>.

Notation "$( x )" := x (in custom stlc_tm at level 0, x constr, only parsing) : stlc_scope.
Notation "x" := x (in custom stlc_tm at level 0, x constr at level 0) : stlc_scope.
Notation "<{ e }>" := e (e custom stlc_tm at level 200) : stlc_scope.
Notation "( x )" := x (in custom stlc_tm at level 0, x custom stlc_tm) : stlc_scope.

Notation "x y" := (tm_app x y) (in custom stlc_tm at level 10, left associativity) : stlc_scope.
Notation "\ x : t , y" :=
  (tm_abs x t y) (in custom stlc_tm at level 200, x global,
                     t custom stlc_ty,
                     y custom stlc_tm at level 200,
                     left associativity).
Coercion tm_var : string >-> tm.
Arguments tm_var _%string.

Definition x : string := "x".
Definition y : string := "y".
Definition z : string := "z".
Hint Unfold x : core.
Hint Unfold y : core.
Hint Unfold z : core.

(** The upshot of these notation definitions is that we can
    write STLC terms in these brackets: [<{ .. }>] 
    (similar to how we wrote Imp commands) and STLC types 
    in these brackets: [<{{ .. }}>]. **)
Notation idB :=
  <{ \x:Bool, x }>.

Notation idBB :=
  <{ \x:Bool->Bool, x }>.

Notation idBBBB :=
  <{ \x: (Bool->Bool)->(Bool->Bool), x}>.

Notation k := <{ \x:Bool, \y:Bool, x }>.

Notation notB := <{ \x:Bool, if x then false else true }>.

(**
Definitions of value, substitution and the small-step operational
semantics remain the same as untyped LC.
*)

Inductive value : tm -> Prop :=
  | v_abs : forall x T2 t1,
      value <{\x:T2, t1}>
  | v_true :
      value <{true}>
  | v_false :
      value <{false}>.

Reserved Notation "'[' x ':=' s ']' t" (in custom stlc_tm at level 5, x global, s custom stlc_tm,
      t custom stlc_tm at next level, right associativity).

Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | tm_var y =>
      if String.eqb x y then s else t
  | <{\y:T, t1}> =>
      if String.eqb x y then t else <{\y:T, [x:=s] t1}>
  | <{t1 t2}> =>
      <{[x:=s] t1 [x:=s] t2}>
  | <{true}> =>
      <{true}>
  | <{false}> =>
      <{false}>
  | <{if t1 then t2 else t3}> =>
      <{if [x:=s] t1 then [x:=s] t2 else [x:=s] t3}>
  end

where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc_tm).

Reserved Notation "t '-->' t'" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_App1 : forall t1 t1' t2,
         t1 --> t1' ->
         <{t1 t2}> --> <{t1' t2}>
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         <{v1 t2}> --> <{v1  t2'}>
  | ST_AppAbs : forall x T t v,
         value v ->
         <{(\x:T, t) v}> --> <{ [x:=v]t }>
  | ST_IfTrue : forall t1 t2,
      <{if true then t1 else t2}> --> t1
  | ST_IfFalse : forall t1 t2,
      <{if false then t1 else t2}> --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      <{if t1 then t2 else t3}> --> <{if t1' then t2 else t3}>

where "t '-->' t'" := (step t t').

Hint Constructors step : core.

Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

Lemma step_example1 :
  <{idBB idB}> -->* idB.
Proof. eapply multi_step.
 - apply ST_AppAbs. constructor.
 - simpl. apply multi_refl.
Qed.  

Lemma step_example2 :
  <{idBB (idBB idB)}> -->* idB.
Proof. eapply multi_step.
  - eapply ST_App2. 
    -- constructor.
    -- apply ST_AppAbs. constructor.
  - simpl. apply step_example1.
Qed.  

Lemma step_example3 :
  <{idBB notB true}> -->* <{false}>.
Proof. eapply multi_step.
  - eapply ST_App1. apply ST_AppAbs. constructor.
  - simpl. eapply multi_step.
    -- apply ST_AppAbs. constructor.
    -- simpl. eapply multi_step.
      --- apply ST_IfTrue.
      --- apply multi_refl.
Qed.

(**
Note that the term below does not type-check.
*)

Lemma step_example4 :
  <{idBB (notB true)}> -->* <{false}>.
Proof. eapply multi_step.
  - eapply ST_App2.
    -- constructor.
    -- apply ST_AppAbs. constructor.
  - simpl. eapply multi_step.
    -- eapply ST_App2.
      --- constructor.
      --- apply ST_IfTrue.
    -- eapply multi_step.
      --- apply ST_AppAbs. constructor.
      --- simpl. apply multi_refl.
Qed. 

(** Typing Relation

We will construct a typing relation of the form 
[Gamma |-- t \in T] which says that under the typing context
[Gamma], term [t] has type [T]. The typing context is a 
map from variable names (i.e strings) to types.

Our goal is to ensure that every term that is typed by the
relation should never get stuck during reduction.
*) 

Definition context := partial_map ty.

(**
A partial_map is defined as follows (in Maps.v):

[Definition partial_map (A : Type) := total_map (option A).]

The empty partial_map maps every string to None. 
*)

Notation "x '|->' v ';' m " := (update m x v)
  (in custom stlc_tm at level 0, x constr at level 0, v  custom stlc_ty, right associativity) : stlc_scope.

Notation "x '|->' v " := (update empty x v)
  (in custom stlc_tm at level 0, x constr at level 0, v custom stlc_ty) : stlc_scope.

Notation "'empty'" := empty (in custom stlc_tm) : stlc_scope.

Reserved Notation "<{ Gamma '|--' t '\in' T }>"
            (at level 0, Gamma custom stlc_tm at level 200, t custom stlc_tm, T custom stlc_ty).

Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T1,
      Gamma x = Some T1 ->
      <{ Gamma |-- x \in T1 }>
  | T_Abs : forall Gamma x T1 T2 t1,
      <{ x |-> T2 ; Gamma |-- t1 \in T1 }> ->
      <{ Gamma |-- \x:T2, t1 \in T2 -> T1 }>
  | T_App : forall T1 T2 Gamma t1 t2,
      <{ Gamma |-- t1 \in T2 -> T1 }> ->
      <{ Gamma |-- t2 \in T2 }> ->
      <{ Gamma |-- t1 t2 \in T1 }>
  | T_True : forall Gamma,
      <{ Gamma |-- true \in Bool }>
  | T_False : forall Gamma,
      <{ Gamma |-- false \in Bool }>
  | T_If : forall t1 t2 t3 T1 Gamma,
       <{ Gamma |-- t1 \in Bool }> ->
       <{ Gamma |-- t2 \in T1 }> ->
       <{ Gamma |-- t3 \in T1 }> ->
       <{ Gamma |-- if t1 then t2 else t3 \in T1 }>

where "<{ Gamma '|--' t '\in' T }>" := (has_type Gamma t T) : stlc_scope.

Hint Constructors has_type : core.

Example typing_example_1 :
  <{ empty |-- \x:Bool, x \in Bool -> Bool }>.
Proof. eauto. Qed.

Example typing_example_2 :
  <{ empty |--
    \x:Bool,
       \y:Bool->Bool,
          (y (y x)) \in
    Bool -> (Bool -> Bool) -> Bool }>.
Proof. eauto 20. Qed.

Example typing_example_3 :
   <{ empty |--
      \x:Bool->Bool,
         \y:Bool->Bool,
            \z:Bool,
               (y (x z)) \in
     (Bool -> Bool) ->  (Bool -> Bool) -> Bool -> Bool  }>.
Proof. apply T_Abs. apply T_Abs. apply T_Abs.
eapply T_App. 
- apply T_Var. rewrite update_neq. 
  * rewrite update_eq. reflexivity.
  * intros contra; discriminate contra. 
- eapply T_App.
  * apply T_Var. rewrite update_neq. 
    ** rewrite update_neq. 
      *** rewrite update_eq. reflexivity.
      *** intros contra; discriminate contra. 
    ** intros contra; discriminate contra.
  * apply T_Var. apply update_eq.   
Qed.

Example typing_nonexample_1:
 ~ exists T, <{ empty |-- true false \in T}>.
Proof. intros [T contra]. inversion contra; subst.
 inversion H2.
Qed.

Example typing_nonexample_2:
 ~ exists T, 
  <{ empty |--
     \x:Bool,
        \y:Bool,
           x y \in T }>.
Proof. intros [T contra]. inversion contra; subst.
  inversion H4; subst. inversion H5; subst.
  inversion H2; subst. discriminate H1.
Qed. 

Example typing_nonexample_3 :
  ~ (exists S T,
      <{ empty |--
          \x:S, x x \in T }>).
Proof. intros [S [T contra]]. inversion contra; subst.
 inversion H4; subst. inversion H2; subst. 
 inversion H5; subst. rewrite H1 in H3. injection H3 as H3.
 assert (L : forall (P1 P2: ty), <{{ P2 -> P1 }}> = P2 -> False).
 { intros. generalize dependent P1. induction P2.
  - intros. discriminate H.
  - intros. injection H as L1 L2. eapply IHP2_1. apply L1.
 }
 eapply L. apply H3.
Qed.

End STLC.
