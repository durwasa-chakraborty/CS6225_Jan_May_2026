(**
Lambda Calculus

Ref.: Software Foundations, Vol. 2, Stlc.v

*)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
Require Import Arith.
From PLF Require Import Maps.
Require Import Strings.String.
From PLF Require Import W9b.
Set Default Goal Selector "!".

Hint Constructors multi : core.

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
   s = \x, r

   (where [r] is a _free_ reference to some global resource) 
   substituted for the free variable [z] in the term

    t = \r, z

    where [r] is a bound variable, we would get

     \r, \x, r

    where the free reference to [r] in [s] has been "captured" by
    the binder at the beginning of [t].
    
    This is undesirable because t' = \w, z is identical to 
    t, but [subst z s t] would yield [\w, \x, r] which is not
    identical to [\r, \x, r].
    
In our setting, we will assume that terms being substituted do
not have free variables. Hence, we don't have to worry about the
above complexity.
*)

(** We can now define the small-step semantics of lambda calculus*)

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x t v,
         value v ->
         tm_app (tm_abs x t) v --> subst x v t
  | ST_App1 : forall t1 t1' t2,
         t1 --> t1' ->
         tm_app t1 t2 --> tm_app t1' t2
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         tm_app v1 t2 --> tm_app v1  t2'
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
(** ** Types *)

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

(** We'll write types inside of [<{{ ... }}>] brackets: *)

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
Arguments tm_var _%_string.

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


(** Types
- While the syntax of a language may allow arbitrary terms, the
semantics may only be defined for a subset of terms.
- Using types allows us to statically identify only those terms 
which are well-behaved.
- More formally, well-typed terms are either values or else they
can take a step according to the operational semantics.
 -- Also known as 'weak progress' property
*)




