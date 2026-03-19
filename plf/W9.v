(**

Hoare Logic
Ref.: Software Foundations, Volume 2, Hoare2.v, SmallStep.v

*)

Set Warnings "-notation-overridden".
From PLF Require Import W7.
From PLF Require Export Maps.
Require Import Bool.
Require Import Arith.
Require Import EqNat.
Require Import PeanoNat. Import Nat.
Require Import Lia.
From PLF Require Export Imp.



(**
A major advantage of using the proof rules of Hoare Logic is that
the structure of the proof of correctness follows the structure of
the program.

We make this connection explicit by 'decorating' a program with 
its proof.
*)

(**
Consider the following swapping program:

{{X = m /\ Y = n}}
X := X + Y;
Y := X - Y;
X := X - Y
{{X = n /\ Y = m}}

Its proof of correctness:
    (1)    {{ X = m /\ Y = n }} ->>
    (2)    {{ (X + Y) - ((X + Y) - Y) = n /\ (X + Y) - Y = m }}
             X := X + Y
    (3)                     {{ X - (X - Y) = n /\ X - Y = m }};
             Y := X - Y
    (4)                     {{ X - Y = n /\ Y = m }};
             X := X - Y
    (5)    {{ X = n /\ Y = m }}
*)

(** Here is a decorated program using conditionals:

      (1)   {{ True }}
              if X <= Y then
      (2)                    {{ True /\ X <= Y }} ->>
      (3)                    {{ (Y - X) + X = Y \/ (Y - X) + Y = X }}
                Z := Y - X
      (4)                    {{ Z + X = Y \/ Z + Y = X }}
              else
      (5)                    {{ True /\ ~(X <= Y) }} ->>
      (6)                    {{ (X - Y) + X = Y \/ (X - Y) + Y = X }}
                Z := X - Y
      (7)                    {{ Z + X = Y \/ Z + Y = X }}
              end
      (8)   {{ Z + X = Y \/ Z + Y = X }}
*)

(** Example with loops:

The following Imp program calculates the integer quotient and
    remainder of parameters [m] and [n].

      {{True}}
       X := m;
       Y := 0;
       while n <= X do
         X := X - n;
         Y := Y + 1
       end;
      {{n * Y + X = m /\ X < n}}
   
   Loop invariant is {{n * Y + X = m}}
   
   Decorated Program:
   
      (1)  {{ True }} ->>
      (2)  {{ n * 0 + m = m }}
             X := m;
      (3)                     {{ n * 0 + X = m }}
             Y := 0;
      (4)                     {{ n * Y + X = m }}
             while n <= X do
      (5)                     {{ n * Y + X = m /\ n <= X }} ->>
      (6)                     {{ n * (Y + 1) + (X - n) = m }}
               X := X - n;
      (7)                     {{ n * (Y + 1) + X = m }}
               Y := Y + 1
      (8)                     {{ n * Y + X = m }}
             end
      (9)  {{ n * Y + X = m /\ ~ (n <= X) }} ->>
     (10)  {{ n * Y + X = m /\ X < n }}
*)

Inductive dcom : Type :=
| DCSkip (Q : Assertion)
  (* skip {{ Q }} *)
| DCSeq (d1 d2 : dcom)
  (* d1 ; d2 *)
| DCAsgn (X : string) (a : aexp) (Q : Assertion)
  (* X := a {{ Q }} *)
| DCIf (b : bexp) (P1 : Assertion) (d1 : dcom)
       (P2 : Assertion) (d2 : dcom) (Q : Assertion)
  (* if b then {{ P1 }} d1 else {{ P2 }} d2 end {{ Q }} *)
| DCWhile (b : bexp) (P : Assertion) (d : dcom)
          (Q : Assertion)
  (* while b do {{ P }} d end {{ Q }} *)
| DCPre (P : Assertion) (d : dcom)
  (* ->> {{ P }} d *)
| DCPost (d : dcom) (Q : Assertion)
  (* d ->> {{ Q }} *).

Inductive decorated : Type :=
  | Decorated : Assertion -> dcom -> decorated.

Declare Scope dcom_scope.
Notation "'skip' '{{' P '}}'" := (DCSkip P)
  (in custom com at level 0,
    P custom assn at level 99,
    format "'[v' 'skip' '/' '{{' P '}}' ']'") : dcom_scope.
Notation "l ':=' a '{{' P '}}'" := (DCAsgn l a P)
  (in custom com at level 0,
    l constr at level 0,
    a custom com at level 85,
    P custom assn at level 99,
    no associativity,
    format "'[v' l  ':='  a '/' '{{'  P  '}}' ']'") : dcom_scope.
Notation "'while' b 'do' '{{' Pbody '}}' d 'end' '{{' Ppost '}}'" := (DCWhile b Pbody d Ppost)
  (in custom com at level 89,
    b custom com at level 99,
    Pbody custom assn at level 99,
    Ppost custom assn at level 99,
    format "'[v' 'while'  b  'do' '/  ' '{{' Pbody '}}' '/  ' d '/' 'end' '/' '{{' Ppost '}}' ']'") : dcom_scope.
Notation "'if' b 'then' {{ P1 }} d1 'else' {{ P2 }} d2 'end' {{ Q }}" := (DCIf b P1 d1 P2 d2 Q)
  (in custom com at level 89,
    b custom com at level 99,
    P1 custom assn at level 99,
    P2 custom assn at level 99,
    Q custom assn at level 99,
    format "'[v' 'if'  b  'then' '/  ' '{{' P1 '}}' '/  ' d1 '/' 'else' '/  ' '{{' P2 '}}' '/  ' d2 '/' 'end' '/' '{{' Q '}}' ']'"): dcom_scope.
Notation "'->>' {{ P }} d"
      := (DCPre P d)
          (in custom com at level 12, right associativity, P custom assn at level 99)
          : dcom_scope.
Notation "d '->>' {{ P }}"
      := (DCPost d P)
           (in custom com at level 10, right associativity, P custom assn at level 99)
           : dcom_scope.
Notation "x ; y" := (DCSeq x y)
  (in custom com at level 90,
    right associativity,
    format "'[v' x ; '/' y ']'") : dcom_scope.
Notation "{{ P }} d" := (Decorated P d)
  (in custom com at level 91,
    P custom assn at level 99,
    format "'[v' '{{'  P  '}}' '/' d ']'"): dcom_scope.

Local Open Scope dcom_scope.

Example dec0 : dcom :=
  <{ skip {{ True }} }>.
Example dec1 : dcom :=
  <{ while true do {{ True }} skip {{ True }} end {{ True }} }>.

Example swap (m n : nat) : decorated :=
 <{
 {{X = m /\ Y = n}} ->>
 {{(X + Y) - ((X + Y) - Y) = n /\ (X + Y) - Y = m}}  
   X := X + Y
   {{X - (X - Y) = n /\ X - Y = m}};
   Y := X - Y
   {{X - Y = n /\ Y = m}};
   X := X - Y
   {{X = n /\ Y = m}}
 }>.

Example dec_while : decorated :=
  <{
  {{ True }}
    while X <> 0
    do
                 {{ True /\ (X <> 0) }}
      X := X - 1
                 {{ True }}
    end
  {{ True /\  X = 0}} ->>
  {{ X = 0 }} }>.
  
(** It is easy to go from a [dcom] to a [com] by erasing all
    annotations. *)

Fixpoint erase (d : dcom) : com :=
  match d with
  | DCSkip _           => CSkip
  | DCSeq d1 d2        => CSeq (erase d1) (erase d2)
  | DCAsgn X a _       => CAsgn X a
  | DCIf b _ d1 _ d2 _ => CIf b (erase d1) (erase d2)
  | DCWhile b _ d _    => CWhile b (erase d)
  | DCPre _ d          => erase d
  | DCPost d _         => erase d
  end.

Definition erase_d (dec : decorated) : com :=
  match dec with
  | Decorated P d => erase d
  end.
  
Example erase_while_ex :
    erase_d dec_while
  = <{while X <> 0 do X := X - 1 end}>.
Proof.
  unfold dec_while.
  reflexivity.
Qed.

(** It is also straightforward to extract the precondition and
    postcondition from a decorated program. *)

Definition precondition_from (dec : decorated) : Assertion :=
  match dec with
  | Decorated P d => P
  end.

Fixpoint post (d : dcom) : Assertion :=
  match d with
  | DCSkip P                => P
  | DCSeq _ d2              => post d2
  | DCAsgn _ _ Q            => Q
  | DCIf  _ _ _ _ _ Q       => Q
  | DCWhile _ _ _ Q         => Q
  | DCPre _ d               => post d
  | DCPost _ Q              => Q
  end.

Definition postcondition_from (dec : decorated) : Assertion :=
  match dec with
  | Decorated P d => post d
  end.
  
(** We can then express what it means for a decorated program to be
    correct as follows: *)

Definition outer_triple_valid (dec : decorated) :=
  {{$(precondition_from dec)}} erase_d dec {{$(postcondition_from dec)}}.

(** For example: *)

Example dec_while_triple_correct :
     outer_triple_valid dec_while
   =
     {{ True }}
       while X <> 0 do X := X - 1 end
     {{ X = 0 }}.
Proof. reflexivity. Qed.

(**
The VC generator takes a [dcom] and a pre-condition [P] and generates
a proposition whose correctness determines the validity of the
Hoare Triple obtained from [dcom] and [P].
*)

Fixpoint verification_conditions (P : Assertion) (d : dcom) : Prop :=
  match d with
  | DCSkip Q =>
         (P ->> Q)
  | DCSeq d1 d2 =>
         verification_conditions P d1
      /\ verification_conditions (post d1) d2
  | DCAsgn X a Q =>
          P ->> {{ Q [X |-> a] }}
  | DCIf b P1 d1 P2 d2 Q =>
         {{ P /\ b }} ->> P1
      /\ {{ P /\ ~ b }}  ->> P2
      /\ (post d1 ->> Q) /\ (post d2 ->> Q)
      /\ verification_conditions P1 d1
      /\ verification_conditions P2 d2
  | DCWhile b Q d R =>
      (* (post d) is both the loop invariant and the initial
         precondition *)
         (P ->> post d)
      /\ {{ $(post d) /\ b }} ->> Q
      /\ {{ $(post d) /\ ~ b }} ->> R
      /\ verification_conditions Q d
  | DCPre P' d =>
         (P ->> P')
      /\ verification_conditions P' d
  | DCPost d Q =>
         verification_conditions P d
      /\ (post d ->> Q)
  end.

Theorem verification_correct : forall d P,
  verification_conditions P d -> {{P}} erase d {{ $(post d) }}.
Proof.
  induction d; intros; simpl in *.
  - (* Skip *)
    eapply hoare_consequence_pre.
      + apply hoare_skip.
      + assumption.
  - (* Seq *)
    destruct H as [H1 H2].
    eapply hoare_seq.
      + apply IHd2. apply H2.
      + apply IHd1. apply H1.
  - (* Asgn *)
    eapply hoare_consequence_pre.
      + apply hoare_asgn.
      + assumption.
  - (* If *)
    destruct H as [HPre1 [HPre2 [Hd1 [Hd2 [HThen HElse] ] ] ] ].
    apply IHd1 in HThen. clear IHd1.
    apply IHd2 in HElse. clear IHd2.
    apply hoare_if.
      + eapply hoare_consequence_pre; eauto.
        eapply hoare_consequence_post; eauto.
      + eapply hoare_consequence_pre; eauto.
        eapply hoare_consequence_post; eauto.
  - (* While *)
    destruct H as [Hpre [Hbody1 [Hpost1  Hd] ] ].
    eapply hoare_consequence_pre; eauto.
    eapply hoare_consequence_post; eauto.
    apply hoare_while.
    eapply hoare_consequence_pre; eauto.
  - (* Pre *)
    destruct H as [HP Hd].
    eapply hoare_consequence_pre; eauto.
  - (* Post *)
    destruct H as [Hd HQ].
    eapply hoare_consequence_post; eauto.
Qed.

Definition verification_conditions_from
              (dec : decorated) : Prop :=
  match dec with
  | Decorated P d => verification_conditions P d
  end.


Corollary verification_conditions_correct : forall dec,
  verification_conditions_from dec ->
  outer_triple_valid dec.
Proof.
  intros [P d]. apply verification_correct.
Qed.

Eval simpl in verification_conditions_from dec_while.

Ltac verify_assertion :=
  repeat split;
  simpl;
  unfold assert_implies;
  unfold bassertion in *; unfold beval in *; unfold aeval in *;
  unfold assertion_sub; intros;
  repeat (simpl in *;
          rewrite t_update_eq ||
          (try rewrite t_update_neq;
          [| (intro X; inversion X; fail)]));
  simpl in *;
  repeat match goal with [H : _ /\ _ |- _] =>
                         destruct H end;
  repeat rewrite not_true_iff_false in *;
  repeat rewrite not_false_iff_true in *;
  repeat rewrite negb_true_iff in *;
  repeat rewrite negb_false_iff in *;
  repeat rewrite eqb_eq in *;
  repeat rewrite eqb_neq in *;
  repeat rewrite leb_iff in *;
  repeat rewrite leb_iff_conv in *;
  try subst;
  simpl in *;
  repeat
    match goal with
      [st : state |- _] =>
        match goal with
        | [H : st _ = _ |- _] =>
            rewrite -> H in *; clear H
        | [H : _ = st _ |- _] =>
            rewrite <- H in *; clear H
        end
    end;
  try eauto;
  try lia.
  
Example vc_dec_while : verification_conditions_from dec_while.
Proof. verify_assertion. Qed.

Definition positive_difference_dec :=
  <{
    {{True}}
    if X <= Y then
          {{(Y - X) + X = Y \/ (Y - X) + Y = X}}
      Z := Y - X
          {{Z + X = Y \/ Z + Y = X}}
    else
          {{(X - Y) + X = Y \/ (X - Y) + Y = X}}
      Z := X - Y
          {{Z + X = Y \/ Z + Y = X}}
    end
    {{Z + X = Y \/ Z + Y = X}}
  }>.
  
Example vc_positive_difference_dec : verification_conditions_from
  positive_difference_dec.
Proof. verify_assertion. Qed.

Definition div_mod_dec (a b : nat) : decorated :=
  <{
  {{ True }} 
    X := a
             {{ 0 * Y + X = a }};
    Y := 0
             {{ b * Y + X = a }};
    while b <= X do
             {{ b * (Y + 1) + (X - b) = a }}
      X := X - b
             {{ b * (Y + 1) + X = a }};
      Y := Y + 1
             {{ b * Y + X = a }}
    end
  {{ b * Y + X = a /\ X < b }} }>.
  
Example vc_div_mod_dec : forall a b, verification_conditions_from
  (div_mod_dec a b).
Proof. verify_assertion. Qed. 

(**
Determining loop invariants
- To prove validity of a hoare triple {{P}} while b do c {{Q}}, we
need to determine a loop invariant I which should satisfy the
following properties:
  * P ->> I
  * I /\ ~b ->> Q
  * {{I /\ b}} c {{I}} should be a valid hoare triple
*)

(**
Example:
          {{ X = m /\ Y = n }}
             while X <> 0 do
               Y := Y - 1;
               X := X - 1
             end
           {{ Y = n - m }}

*)

Example subtract_slowly_dec (m : nat) (n : nat) : decorated :=
  <{
  {{ X = m /\  Y = n }}
    while X <> 0 do
                  {{ (Y - 1) - (X - 1) = n - m  }}
       Y := Y - 1
                  {{ Y - (X - 1) = n - m }} ;
       X := X - 1
                  {{ Y - X = n - m}}
    end
  {{ Y = n - m }} }>.
  
Example vc_subtract_slowly_dec : forall m n, 
verification_conditions_from (subtract_slowly_dec m n).
Proof. verify_assertion. Qed. 


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
