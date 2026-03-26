(**

Hoare Logic
Ref.: Software Foundations, Volume 2, Hoare.v, Hoare2.v

*)

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

Print assertion5.

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
 To formalize the meaning of Q[ X |-> a], we essentially apply Q to a state
  where the variable X is mapped to the value of the arithmetic expression a.
*)

Definition assertion_sub X (a:aexp) (Q:Assertion) : Assertion :=
  fun (st : state) =>
    (Q%assertion) (X !-> (aeval st a); st).

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
  unfold assertion_sub in HQ. assumption.  Qed.

(**
Writing a valid hoare triple for assignment statement in the forward direction
is not so straightforward.
*)

Theorem hoare_asgn_wrong : exists a:aexp,
  ~ {{ True }} X := a {{ X = a }}.
Proof. unfold valid_hoare_triple. exists <{X + 1}>.
unfold not. intros. specialize H with (st := empty_st) (st' := (X !-> 1)).
 assert (C : (X !-> 1) X = aeval (X !-> 1) <{X + 1}>). apply H. constructor. 
 reflexivity. apply I. simpl in C. discriminate C. Qed.

(**
 ------------------------------------------ (hoare_asgn_fwd)
       {{fun st => P st /\ st X = m}}
         X := a
       {{fun st => P (X !-> m ; st) /\ st X = aeval (X !-> m ; st) a }}

Homework: Try to prove this rule
Hint: The lemmas t_update_shadow and t_update_same defined in Maps.v 
(in the plf folder) will be handy in the proof.
*)

Theorem hoare_asgn_fwd :
  forall (m:nat) (a:aexp) (P : Assertion),
  {{P /\ X = m}}
    X := a
  {{ $(fun st => (P (X !-> m ; st)
             /\ st X = aeval (X !-> m ; st) a)) }}.
Proof.
  (* FILL IN HERE *) Admitted.



(**
The assignment rule is quite syntactic in nature, and does not consider
logical equivalence:

{{(X = 3) [X |-> 3]}} X := 3 {{X = 3}},

follows directly from the assignment rule, but not

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

Example hoare_asgn_example2 :
  {{X < 4}}
    X := X + 1
  {{X < 5}}.
Proof.
  eapply hoare_consequence_pre.
  - apply hoare_asgn.
  - unfold "->>", assertion_sub, t_update.
    intros st H. simpl in *. lia.
Qed.

Definition swap_program : com := 
<{ Z := X;
X := Y;
Y := Z
}>.

Theorem swap_exercise :
  {{X <= Y}}
    swap_program
  {{Y <= X}}.
Proof. eapply hoare_seq.
  - eapply hoare_seq.
    * apply hoare_asgn.
    * unfold assertion_sub. simpl. apply hoare_asgn.
  - unfold assertion_sub; simpl. eapply hoare_consequence_pre.
    * apply hoare_asgn.
    * unfold "->>". intros. apply H.
Qed.

(** Proof rule for if-then-else:

              {{P /\   b}} c1 {{Q}}
              {{P /\ ~ b}} c2 {{Q}}
      ------------------------------------  (hoare_if)
      {{P}} if b then c1 else c2 end {{Q}}
*)

Definition bassertion b : Assertion :=
  fun st => (beval st b = true).

Coercion bassertion : bexp >-> Assertion.

Arguments bassertion /.

(** A useful fact about [bassertion]: *)

Lemma bexp_eval_false : forall b st,
  beval st b = false -> ~ ((bassertion b) st).
Proof. intros. unfold not;intros. unfold bassertion in H0.  
rewrite H in H0; discriminate H0. Qed.

Hint Resolve bexp_eval_false : core.


Theorem hoare_if : forall P Q (b:bexp) c1 c2,
  {{ P /\ b }} c1 {{Q}} ->
  {{ P /\ ~ b}} c2 {{Q}} ->
  {{P}} if b then c1 else c2 end {{Q}}.
Proof.  intros P Q b c1 c2 HTrue HFalse st st' HE HP.
  inversion HE; subst; eauto.
Qed.

Example if_example :
  {{True}}
    if (X = 0)
      then Y := 2
      else Y := X + 1
    end
  {{X <= Y}}.
Proof.
  apply hoare_if.
  - (* Then *)
    eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + unfold "->>", assertion_sub, t_update, bassertion.
      simpl. intros st [_ H]. apply eqb_eq in H.
      rewrite H. lia.
  - (* Else *)
    eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + unfold "->>", assertion_sub, t_update. simpl. lia.  
Qed.

(** Proof rule for while b do c end:

            {{P /\ b}} c {{P}}
      --------------------------------- (hoare_while)
      {{P} while b do c end {{P /\ ~b}}

P is also called an inductive loop invariant.
*)

Theorem hoare_while : forall P (b:bexp) c,
  {{P /\ b}} c {{P}} ->
  {{P}} while b do c end {{P /\ ~ b}}.
Proof.
  intros P b c Hhoare st st' Heval HP.
  remember <{while b do c end}> as original_command eqn:Horig.
  induction Heval; try (discriminate Horig). 
  - split. assumption. injection Horig as H1 H2. subst. auto.  
  - injection Horig as H1 H2; subst; eauto.
Qed. 

Example while_example :
  {{X <= 3}}
    while (X <= 2) do
      X := X + 1
    end
  {{X = 3}}.
 Proof.
  eapply hoare_consequence_post.
  - apply hoare_while.
    eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + unfold "->>", assertion_sub, t_update, bassertion; simpl.
    intros. destruct H as [H1 H2]. apply leb_le in H2. lia.
  - unfold "->>", assertion_sub, t_update, bassertion; simpl.
    intros. destruct H as [H1 H2]. unfold not in H2. rewrite -> leb_le in H2. lia. 
Qed.

Module HoareAssertAssume.

(**
An alternative method of specifying correctness of programs is to 
use the [assume] and [assert] commands.

- [assert P] evaluates P and if it fails, causes the program to go
 into a special error state and exit.
- [assume P] evaluate P, and if it fails, the program gets stuck 
 and has no final state.

*)

Inductive com : Type :=
  | CSkip : com
  | CAsgn : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CAssert : bexp -> com
  | CAssume : bexp -> com.

Notation "'assert' l" := (CAssert l)
                           (in custom com at level 8, l custom com at level 0).
Notation "'assume' l" := (CAssume l)
                          (in custom com at level 8, l custom com at level 0).
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

Inductive result : Type :=
  | RNormal : state -> result
  | RError : result.

(** Now we are ready to give you the ceval relation for the 
    new language. *)

Inductive ceval : com -> state -> result -> Prop :=
  (* Old rules, several modified *)
  | E_Skip : forall st,
      st =[ skip ]=> RNormal st
  | E_Asgn  : forall st a1 n x,
      aeval st a1 = n ->
      st =[ x := a1 ]=> RNormal (x !-> n ; st)
  | E_SeqNormal : forall c1 c2 st st' r,
      st  =[ c1 ]=> RNormal st' ->
      st' =[ c2 ]=> r ->
      st  =[ c1 ; c2 ]=> r
  | E_SeqError : forall c1 c2 st,
      st =[ c1 ]=> RError ->
      st =[ c1 ; c2 ]=> RError
  | E_IfTrue : forall st r b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> r ->
      st =[ if b then c1 else c2 end ]=> r
  | E_IfFalse : forall st r b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> r ->
      st =[ if b then c1 else c2 end ]=> r
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ while b do c end ]=> RNormal st
  | E_WhileTrueNormal : forall st st' r b c,
      beval st b = true ->
      st  =[ c ]=> RNormal st' ->
      st' =[ while b do c end ]=> r ->
      st  =[ while b do c end ]=> r
  | E_WhileTrueError : forall st b c,
      beval st b = true ->
      st =[ c ]=> RError ->
      st =[ while b do c end ]=> RError
  (* Rules for Assert and Assume *)
  | E_AssertTrue : forall st b,
      beval st b = true ->
      st =[ assert b ]=> RNormal st
  | E_AssertFalse : forall st b,
      beval st b = false ->
      st =[ assert b ]=> RError
  | E_Assume : forall st b,
      beval st b = true ->
      st =[ assume b ]=> RNormal st

where "st '=[' c ']=>' r" := (ceval c st r).

(** We redefine hoare triples: Now, [{{P}} c {{Q}}] means that,
    whenever [c] is started in a state satisfying [P], and terminates
    with result [r], then [r] is not an error and the state of [r]
    satisfies [Q]. *)

Definition valid_hoare_triple
           (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st r,
     st =[ c ]=> r  -> P st  ->
     (exists st', r = RNormal st' /\ Q st').

Notation "{{ P }} c {{ Q }}" :=
  (valid_hoare_triple P c Q)
    (at level 2, P custom assn at level 99, c custom com at level 99, Q custom assn at level 99)
    : hoare_spec_scope.

Theorem assert_assume_differ : exists (P:Assertion) b (Q:Assertion),
       ({{P}} assume b {{Q}})
  /\ ~ ({{P}} assert b {{Q}}).
Proof. exists ({{X = 1}}). exists <{ X <> 1 }>. exists ({{X = 1}}).
  split.
  - intros st r He HP. inversion He; subst. simpl in H0. simpl in HP.
   rewrite HP in H0. apply negb_true_iff in H0. simpl in H0.
  discriminate H0.
  - unfold not; intros. unfold valid_hoare_triple in H. 
  specialize H with (st := (X !-> 1)) (r := RError). 
  assert (C : (X !-> 1) =[ assert (X <> 1) ]=> RError).
  { apply E_AssertFalse. reflexivity. }
  apply H in C. destruct C as [st' C]. destruct C as [C1 C2].
  discriminate C1. reflexivity.
Qed.


(* Homework *)
Theorem assert_implies_assume : forall P b Q,
     ({{P}} assert b {{Q}})
  -> ({{P}} assume b {{Q}}).
Proof.
(* FILL IN HERE *) Admitted.

Theorem hoare_assume: forall (P: Assertion) b,
{{P}} assume b {{P /\ b}}.
Proof. intros P b st r HE HP. inversion HE; subst. exists st. split.
  - reflexivity.
  - split; assumption.
Qed.

Theorem hoare_assert: forall (P: Assertion) (b : bexp),
(P ->> b) -> {{P}} assert b {{P}}.
Proof. intros P b H st r HE HP. inversion HE; subst.
  - exists st. split.
    * reflexivity.
    * assumption.
  - unfold "->>" in H. apply H in HP. simpl in HP. rewrite HP in H1.
    discriminate H1.
Qed. 

End HoareAssertAssume.

