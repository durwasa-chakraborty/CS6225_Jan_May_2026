Set Warnings "-notation-overridden".
From PLF Require Import Maps.
Require Import Bool.
Require Import Arith.
Require Import EqNat.
Require Import PeanoNat. Import Nat.
Require Import Lia.
From PLF Require Export Imp.

(** An _assertion_ is a predicate about the state of a program's
    memory -- formally, a property of [state]s. *)

Definition Assertion := state -> Prop.

Module ExAssertions.
Definition assertion1 : Assertion := fun st => st X <= st Y.
Definition assertion2 : Assertion :=
  fun st => st X = 3 \/ st X <= st Y.
Definition assertion3 : Assertion :=
  fun st => st Z * st Z <= st X /\
            ~ (((S (st Z)) * (S (st Z))) <= st X).
Definition assertion4 : Assertion :=
  fun st => st Z = max (st X) (st Y).

End ExAssertions.

(**
The definitions below perform some syntactic magic so that we can 
factor out common parts of assertions, such as defining it to be a 
function from [state] to [Prop], writing [st X] to denote values of 
variables, etc.
*)

(** Syntax Definitions BEGIN (can be safely skipped) *)

Definition Aexp : Type := state -> nat.

Definition assert_of_Prop (P : Prop) : Assertion := fun _ => P.
Definition Aexp_of_nat (n : nat) : Aexp := fun _ => n.

Definition Aexp_of_aexp (a : aexp) : Aexp := fun st => aeval st a.

Coercion assert_of_Prop : Sortclass >-> Assertion.
Coercion Aexp_of_nat : nat >-> Aexp.
Coercion Aexp_of_aexp : aexp >-> Aexp.

Arguments assert_of_Prop /.
Arguments Aexp_of_nat /.
Arguments Aexp_of_aexp /.

Declare Custom Entry assn. (* The grammar for Hoare logic Assertions *)
Declare Scope assertion_scope.
Bind Scope assertion_scope with Assertion.
Bind Scope assertion_scope with Aexp.
Delimit Scope assertion_scope with assertion.

Notation "# f x .. y" := (fun st => (.. (f ((x:Aexp) st)) .. ((y:Aexp) st)))
                  (in custom assn at level 2,
                  f constr at level 0, x custom assn at level 1,
                  y custom assn at level 1) : assertion_scope.

Notation "P -> Q" := (fun st => (P:Assertion) st -> (Q:Assertion) st) (in custom assn at level 99, right associativity) : assertion_scope.
Notation "P <-> Q" := (fun st => (P:Assertion) st <-> (Q:Assertion) st) (in custom assn at level 95) : assertion_scope.

Notation "P \/ Q" := (fun st => (P:Assertion) st \/ (Q:Assertion) st) (in custom assn at level 85, right associativity) : assertion_scope.
Notation "P /\ Q" := (fun st => (P:Assertion) st /\ (Q:Assertion) st) (in custom assn at level 80, right associativity) : assertion_scope.
Notation "~ P" := (fun st => ~ ((P:Assertion) st)) (in custom assn at level 75, right associativity) : assertion_scope.
Notation "a = b" := (fun st => (a:Aexp) st = (b:Aexp) st) (in custom assn at level 70) : assertion_scope.
Notation "a <> b" := (fun st => (a:Aexp) st <> (b:Aexp) st) (in custom assn at level 70) : assertion_scope.
Notation "a <= b" := (fun st => (a:Aexp) st <= (b:Aexp) st) (in custom assn at level 70) : assertion_scope.
Notation "a < b" := (fun st => (a:Aexp) st < (b:Aexp) st) (in custom assn at level 70) : assertion_scope.
Notation "a >= b" := (fun st => (a:Aexp) st >= (b:Aexp) st) (in custom assn at level 70) : assertion_scope.
Notation "a > b" := (fun st => (a:Aexp) st > (b:Aexp) st) (in custom assn at level 70) : assertion_scope.
Notation "'True'" := True.
Notation "'True'" := (fun st => True) (in custom assn at level 0) : assertion_scope.
Notation "'False'" := False.
Notation "'False'" := (fun st => False) (in custom assn at level 0) : assertion_scope.

Notation "a + b" := (fun st => (a:Aexp) st + (b:Aexp) st) (in custom assn at level 50, left associativity) : assertion_scope.
Notation "a - b" := (fun st => (a:Aexp) st - (b:Aexp) st) (in custom assn at level 50, left associativity) : assertion_scope.
Notation "a * b" := (fun st => (a:Aexp) st * (b:Aexp) st) (in custom assn at level 40, left associativity) : assertion_scope.

Notation "( x )" := x (in custom assn at level 0, x at level 99) : assertion_scope.

Notation "$ f" := f (in custom assn at level 0, f constr at level 0) : assertion_scope.
Notation "x" := (x%assertion) (in custom assn at level 0, x constr at level 0) : assertion_scope.

Declare Scope hoare_spec_scope.
Open Scope hoare_spec_scope.

Notation "{{ e }}" := e (at level 2, e custom assn at level 99) : assertion_scope.
Open Scope assertion_scope.

(** Syntax Definitions END *)

Module  ExamplePrettyAssertions.
Definition assertion1 : Assertion := {{ X = 3 }}.
Definition assertion2 : Assertion := {{ True }}.
Definition assertion3 : Assertion := {{ False }}.
Definition assertion4 : Assertion := {{ True \/ False }}.
Definition assertion5 : Assertion := {{ X <= Y }}.
Definition assertion6 : Assertion := {{ X = 3 \/ X <= Y }}.

(** To use a function f inside an assertion (other than standard 
arithmetic operations like +,-,etc. which are already part of the 
IMP language), we need to use #f *)
Definition assertion7 : Assertion := {{ Z = (#max X Y) }}.
Definition assertion8 : Assertion := {{ Z * Z <= X
                                        /\  ~ (((#S Z) * (#S Z)) <= X) }}.
Definition assertion9 : Assertion := {{ X + Y > #max Y X }}.

(** To use "raw-Rocq" syntax inside an assertion{{  }}, we can use the 
$() syntax:*)

Definition assertion10 : Assertion := {{$(fun st => forall X, st X = 0)}}.

Print assertion1.

Example assertion1_ex : assertion1 (X !-> 3).
Proof. unfold assertion1. unfold t_update. simpl. reflexivity.
Qed.

Example assertion5_ex1 : assertion5 (X !-> 1; Y !-> 2).
Proof. unfold assertion5. unfold t_update. simpl. lia.
Qed. 

Example assertion5_ex2 : assertion5 (X !-> 2; Y !-> 3).
Proof. unfold assertion5. unfold t_update. simpl. lia.
Qed. 

Example assertion10_ex : assertion10 empty_st.
Proof. unfold assertion10. unfold empty_st. intros. unfold t_empty.
reflexivity. Qed. 

End ExamplePrettyAssertions.

(** Given two assertions [P] and [Q], we say that [P] _implies_ [Q],
    written [P ->> Q], if, whenever [P] holds in some state [st], [Q]
    also holds. *)

Definition assert_implies (P Q : Assertion) : Prop :=
  forall st, P st -> Q st.
  
Notation "P ->> Q" := (assert_implies P Q)
                        (at level 80) : hoare_spec_scope.

(** We'll also want the "iff" variant of implication between
    assertions: *)

Notation "P <<->> Q" := (P ->> Q /\ Q ->> P)
                          (at level 80) : hoare_spec_scope.

(** A _Hoare triple_ is a claim about the state before and
    after executing a command.  The standard notation is

      {P} c {Q}

meaning:

  - If command [c] begins execution in a state satisfying assertion [P],
  - and if [c] eventually terminates in some final state,
  - then that final state will satisfy the assertion [Q].

Assertion [P] is called the _precondition_ of the triple, and [Q] is
the _postcondition_.

*)

Definition valid_hoare_triple
           (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st st',
     st =[ c ]=> st' ->
     P st  ->
     Q st'.

(** Notation for Hoare triples *)

Notation "{{ P }} c {{ Q }}" :=
  (valid_hoare_triple P c Q)
    (at level 2, P custom assn at level 99, c custom com at level 99,
     Q custom assn at level 99)
    : hoare_spec_scope.

(** 

    Which of the following Hoare triples are _valid_ -- i.e., the
    claimed relation between [P], [c], and [Q] is true?

   1) {{True}} X := 5 {{X = 5}}

   2) {{X = 2}} X := X + 1 {{X = 3}}

   3) {{True}} X := 5; Y := 0 {{X = 5}}

   4) {{X = 2 /\ X = 3}} X := 5 {{X = 0}}

   5) {{True}} skip {{False}}

   6) {{False}} skip {{True}}

   7) {{True}} while true do skip end {{False}}

   8) {{X = 0}}
        while X = 0 do X := X + 1 end
      {{X = 1}}

   9) {{X = 1}}
        while X <> 0 do X := X + 1 end
      {{X = 100}}
*)

Theorem hoare_post_true : forall (P Q : Assertion) c,
  (forall st, Q st) ->
  {{P}} c {{Q}}.
Proof.
  intros P Q c HQ. unfold valid_hoare_triple. intros. apply HQ. Qed.
  
Theorem hoare_pre_false : forall (P Q : Assertion) c,
  (forall st, ~ (P st)) ->
  {{P}} c {{Q}}.
Proof. intros P Q c HnegP. unfold valid_hoare_triple. intros.
 unfold not in HnegP. apply HnegP in H0. destruct H0. Qed. 
 
 
(** Main Idea:
We will come with proof rules for defining valid hoare triples for
each type of command in IMP.
*)

 
(** Since [skip] doesn't change the state, it preserves any
    assertion [P]:

      --------------------  (hoare_skip)
      {{ P }} skip {{ P }}
*)

Theorem hoare_skip : forall P,
     {{P}} skip {{P}}.
Proof.
  intros P st st' H HP. inversion H; subst. assumption.
Qed.

(** If command [c1] takes any state where [P] holds to a state where
    [Q] holds, and if [c2] takes any state where [Q] holds to one
    where [R] holds, then doing [c1] followed by [c2] will take any
    state where [P] holds to one where [R] holds:

        {{ P }} c1 {{ Q }}
        {{ Q }} c2 {{ R }}
       ----------------------  (hoare_seq)
       {{ P }} c1;c2 {{ R }}
*)

Theorem hoare_seq : forall P Q R c1 c2,
     {{Q}} c2 {{R}} ->
     {{P}} c1 {{Q}} ->
     {{P}} c1; c2 {{R}}.
Proof.
  intros P Q R c1 c2 H1 H2 st st' H12 Pre.
  inversion H12; subst. unfold valid_hoare_triple in H2.
  unfold valid_hoare_triple in H1. apply H1 with (st := st'0).
  apply H6. apply H2 with (st := st). apply H3. apply Pre.
Qed.

Theorem hoare_seq' : forall P Q R c1 c2,
     {{Q}} c2 {{R}} ->
     {{P}} c1 {{Q}} ->
     {{P}} c1; c2 {{R}}.
Proof.
  intros P Q R c1 c2 H1 H2 st st' H12 Pre.
  inversion H12; subst. eauto.
Qed.

(** The auto/eauto tactic
- If the goal can be discharged through any sequence of apply and intros,
then the auto tactic can be used. If the [apply ... with ...] tactic is
required, then eauto can be used. 
*)

(**
  For assignment statement, it's best to think about valid hoare triples
  in the backward direction, i.e. from the post-condition to the pre-
  condition. 
  
  For example, what could be a valid pre-condition in the following triples? 
  {{ ??? }}  X := Y  {{ X = 1 }}
  
  {{ ??? }}  X := X + Y  {{ X = 1 }}
  
  In general,

    {{ Q [X |-> a] }}  X := a  {{ Q }}


    Some more examples:
  1. {{ (X <= 5) [X |-> X + 1] }}         (that is, X + 1 <= 5)
        X := X + 1
      {{ X <= 5 }}

  2. {{ (X = 3) [X |-> 3] }}              (that is, 3 = 3)
        X := 3
      {{ X = 3 }}

  3. {{ (0 <= X /\ X <= 5) [X |-> 3] }}.  (that is, 0 <= 3 /\ 3 <= 5)
        X := 3
      {{ 0 <= X /\ X <= 5 }}

  
*)

(**
 To formalize the meaning of Q[ X |-> a], we essentially apply Q to a state where the variable X is mapped to the value of the arithmetic expression a.
*)

Definition assertion_sub X (a:aexp) (Q:Assertion) : Assertion :=
  fun (st : state) =>
    (Q%_assertion) (X !-> ((a:Aexp) st); st).

Notation "Q [ X |-> a ]" := (assertion_sub X a Q)
                              (in custom assn at level 10, left associativity,
                               Q custom assn, X global, a custom com)
                          : assertion_scope.

Module ExampleAssertionSub.
Example equivalent_assertion1 :
  {{ (X <= 5) [X |-> 3] }} <<->> {{ 3 <= 5 }}.
Proof.
  split. 
  - unfold assert_implies, assertion_sub. intros st H.
  simpl. lia.
  - unfold assert_implies, assertion_sub. intros st H. simpl. rewrite t_update_eq. lia.   
Qed.

Example equivalent_assertion2 :
  {{ (X <= 5) [X |-> X + 1] }} <<->> {{ (X + 1) <= 5 }}.
Proof.
  split; unfold assert_implies, assertion_sub; intros st H;
  simpl in *; apply H.
Qed.
End ExampleAssertionSub.

(** Now, using the substitution operation we've just defined, we can
    give the precise proof rule for assignment:

      ---------------------------- (hoare_asgn)
      {{Q [X |-> a]}} X := a {{Q}}
*)

Theorem hoare_asgn : forall Q X (a:aexp),
  {{Q [X |-> a]}} X := a {{Q}}.
Proof.
  intros Q X a st st' HE HQ.
  inversion HE. subst.
  unfold assertion_sub in HQ. simpl in HQ. assumption.  Qed.

(**
Writing a valid hoare triple for assignment statement in the forward direction is not so straightforward.
*)

Theorem hoare_asgn_wrong : exists a:aexp,
  ~ {{ True }} X := a {{ X = a }}.
Proof. unfold valid_hoare_triple. exists <{X + 1}>.
unfold not. intros. specialize H with (st := empty_st) (st' := (X !-> 1)). assert (C : (X !-> 1) X = aeval (X !-> 1) <{X + 1}>). apply H. constructor. reflexivity. apply I. simpl in C. discriminate C. Qed.

(**
 ------------------------------------------ (hoare_asgn_fwd)
       {{fun st => P st /\ st X = m}}
         X := a
       {{fun st => P (X !-> m ; st) /\ st X = aeval (X !-> m ; st) a }}

Homework: Try to prove this rule
*)

(**
The assignment rule is quite syntactic in nature, and does not consider logical equivalence:

{{(X = 3) [X |-> 3]}} X := 3 {{X = 3}},

follows directly from the assignment rule, but

{{True}} X := 3 {{X = 3}}

However, [True] and [(X = 3) [X |-> 3]] are logically equivalent.

*)

(**
Generalizing this observation gives the two rules of consequence:

                {{P'}} c {{Q}}
                   P ->> P'
         -----------------------------   (hoare_consequence_pre)
                {{P}} c {{Q}}


                {{P}} c {{Q'}}
                  Q' ->> Q
         -----------------------------    (hoare_consequence_post)
                {{P}} c {{Q}}

*)

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  unfold valid_hoare_triple, "->>".
  intros P P' Q c Hhoare Himp st st' Heval Hpre.
  apply Hhoare with (st := st).
  - assumption.
  - apply Himp. assumption.
Qed.

Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof. unfold valid_hoare_triple, "->>".
  intros P Q Q' c HHoare Himp st st' He HP.
  apply Himp. apply HHoare with (st := st).
  - apply He.
  - apply HP.
Qed.

Example hoare_asgn_example1 :
  {{True}} X := 1 {{X = 1}}.
Proof.
  eapply hoare_consequence_pre.
  - apply hoare_asgn.
  - unfold "->>", assertion_sub, t_update; simpl.
    intros st _. reflexivity.
Qed.

Example assertion_sub_example2 :
  {{X < 4}}
    X := X + 1
  {{X < 5}}.
Proof.
  eapply hoare_consequence_pre.
  - apply hoare_asgn.
  - unfold "->>", assertion_sub, t_update.
    intros st H. simpl in *. lia.
Qed.