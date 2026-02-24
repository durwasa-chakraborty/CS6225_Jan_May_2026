Require Import Bool.
Require Import Init.Nat.
Require Import Arith.
Require Import EqNat. Import Nat.
Require Import Lia.
Require Import List. Import ListNotations.
Require Import Strings.String.

(**
Syntax and Semantics of IMP: a small imperative programming
language

Ref: Software Foundations, Vol 1, Imp.v
*)

(**

Syntax of IMP (in BNF):

C := skip
    | X := A
    | C ; C
    | if (B) then C else C end
    | while (B) do C end

A : = N
     | X
     | A + A
     | A * A
     | A - A
     
B := true
    | false
    | A = A
    | A <> A
    | A <= A
    | A > A
    | !B
    | B && B
    | B || B
*)

(**
Examples of IMP programs:

Example-1:
------------
X := 5;
Z := X;
Y := 1

Note: Destructive state updates by every assignment statement.

Example-2:
------------
X := 2;
if (X <= 1)
  then Y := 3;
       X := 5 - Y
  else
       Z := 4
end;
Y := 4

Example-3:
------------
Z := X;
Y := 1;
while (Z <> 0) do
 Y := Y * Z;
 Z := Z - 1
end

Note: Control flow alteration by if-then-else and while statements. 

*)

(** We will assume that a program is represented in the form 
 of an AST, obtainedby lexical analysis and parsing 
 the source code. More details can be found in the chapter 
 ImpParser.v (optional for reading) *)
 
Inductive aexp : Type :=
| ANum (n : nat)
| AId (x : string)
| APlus (a1 a2 : aexp)
| AMinus (a1 a2 : aexp)
| AMult (a1 a2 : aexp).

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BNeq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BGt (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

Definition total_map (X:Type): Type := string -> X.

Definition lookup {X:Type}(m:total_map X) (s:string) : X := m s.

Definition empty {X:Type} (default: X) : total_map X := 
  fun s => default.

Definition update {X:Type}(m:total_map X) (s:string) (x:X)
 : total_map X :=
  fun s' => if (String.eqb s s') then x else m s'.
   
Notation "'_' '!->' v" := (empty v)
  (at level 100, right associativity).

Notation "x '!->' v ';' m" := (update m x v)
                                (at level 100, x constr, right associativity).
 
  
Definition state := total_map nat.

Definition initial_state := (_ !-> 0).

Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".
Definition W : string := "W".

Notation "x '!->' v" := (x !-> v ; initial_state) (at level 100, v at level 200).

Definition st1 : state := X !-> 1 ; Y !-> 2.


Coercion AId : string >-> aexp.
Coercion ANum : nat >-> aexp.
Declare Custom Entry com.
Declare Scope com_scope.
Notation "<{ e }>" := e
  (e custom com, format "'[hv' <{ '/ ' '[v' e ']' '/' }> ']'") : com_scope.
Notation "( x )" := x (in custom com, x at level 99).
Notation "x" := x (in custom com at level 0, x constr at level 0).
Notation "f x .. y" := (.. (f x) .. y)
                  (in custom com at level 0, only parsing,
                  f constr at level 0, x constr at level 1,
                      y constr at level 1).
Notation "x + y" := (APlus x y) (in custom com at level 50, left associativity).
Notation "x - y" := (AMinus x y) (in custom com at level 50, left associativity).
Notation "x * y" := (AMult x y) (in custom com at level 40, left associativity).
Notation "'true'" := true (at level 1).
Notation "'true'" := BTrue (in custom com at level 0).
Notation "'false'" := false (at level 1).
Notation "'false'" := BFalse (in custom com at level 0).
Notation "x <= y" := (BLe x y) (in custom com at level 70, no associativity).
Notation "x > y" := (BGt x y) (in custom com at level 70, no associativity).
Notation "x = y" := (BEq x y) (in custom com at level 70, no associativity).
Notation "x <> y" := (BNeq x y) (in custom com at level 70, no associativity).
Notation "x && y" := (BAnd x y) (in custom com at level 80, left associativity).
Notation "'~' b" := (BNot b) (in custom com at level 75, right associativity).
Open Scope com_scope.

Definition a1 := APlus (ANum 1) (AMult (ANum 2) (ANum 3)).

Definition a1' := <{1 + (2 * 3)}>.

Print a1.

Definition b1 := <{ true && ~(X <= 4) }>.

Print b1.

Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x
  | <{ a1 + a2 }> => (aeval st a1) + (aeval st a2)
  | <{ a1 - a2 }> => (aeval st a1) - (aeval st a2)
  | <{ a1 * a2 }> => (aeval st a1) * (aeval st a2)
  end.
  
Fixpoint beval (st : state) (b : bexp) : bool :=
match b with
| <{true}> => true
| <{false}> => false
| <{a1 = a2}> => (aeval st a1) =? (aeval st a2)
| <{a1 <> a2}> => negb ((aeval st a1) =? (aeval st a2))
| <{a1 <= a2}> =>  (aeval st a1) <=? (aeval st a2)
| <{a1 > a2}> => negb ((aeval st a1) <=? (aeval st a2))
| <{ ~ b' }> => negb (beval st b')
| <{b1 && b2}> => andb (beval st b1) (beval st b2)
end.

Compute aeval (X !-> 5) <{ 3 + (X * 2) }>.

Compute aeval (X !-> 5 ; Y !-> 4) <{ Z + (X * Y) }>.

Compute beval (X !-> 5) <{ true && ~(X <= 4) }>.

(**
Suppose we want to support assignment of an arbitrary value to a
variable to simulate user inputs.
*)


Module Imp_Extend_Any.

Inductive aexp : Type :=
  | AAny                           (* <--- NEW *)
  | ANum (n : nat)
  | AId (s : string)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

(**
- It is not possible to define the aeval function now, since Rocq
functions must be deterministic while the expression AAny can 
evaluate to any value.

- We will instead use inductively defined propositions to define
the evaluation relation.
*)

Inductive aeval_rel : state -> aexp -> nat -> Prop :=
| ANum_eval (st: state) (n:nat) : aeval_rel st (ANum n) n
| AId_eval (st: state) (s: string) : aeval_rel st (AId s) (st s)
| APlus_eval (st: state) (n1 n2: nat) (a1 a2: aexp) 
  (Ha1: aeval_rel st a1 n1) (Ha2: aeval_rel st a2 n2)
    : aeval_rel st (APlus a1 a2) (n1 + n2)
| AMinus_eval (st: state) (n1 n2: nat) (a1 a2: aexp) 
  (Ha1: aeval_rel st a1 n1) (Ha2: aeval_rel st a2 n2)
    : aeval_rel st (AMinus a1 a2) (n1 - n2)
| AMult_eval (st: state) (n1 n2: nat) (a1 a2: aexp) 
  (Ha1: aeval_rel st a1 n1) (Ha2: aeval_rel st a2 n2)
    : aeval_rel st (AMult a1 a2) (n1 * n2)
| AAny_eval (st: state) (n:nat) : aeval_rel st AAny n.

Example any_example_1 : forall (st: state), aeval_rel st AAny 0.
Proof. intros. apply AAny_eval. Qed.

Example any_example_2 : forall (st: state), aeval_rel st AAny 10.
Proof. intros. apply AAny_eval. Qed.

Example any_example_3: aeval_rel (X !-> 5) (APlus (ANum 3) 
(AMult (AId X) (ANum 2))) 13.
Proof. apply APlus_eval with (n1 := 3) (n2 := 10).
- apply ANum_eval.
- apply AMult_eval with (n1 := 5) (n2 := 2).
  -- apply AId_eval.
  -- apply ANum_eval.
Qed.

End Imp_Extend_Any.

Reserved Notation
         "e '=[' st ']=>' n"
         (at level 40, st custom com at level 99,
          e constr, n constr at next level).

Inductive aevalR : state -> aexp -> nat -> Prop :=
  | E_ANum (n : nat) (st : state) :
      <{n}> =[st]=> n
  | E_AId (x : string) (st : state) :
      <{x}> =[st]=> st x
  | E_APlus (e1 e2 : aexp) (n1 n2 : nat) (st : state) :
      (e1 =[st]=> n1) ->
      (e2 =[st]=> n2) ->
      <{e1 + e2}> =[st]=> (n1 + n2)
  | E_AMinus (e1 e2 : aexp) (n1 n2 : nat) (st : state) :
      (e1 =[st]=> n1) ->
      (e2 =[st]=> n2) ->
      <{e1 - e2}> =[st]=> (n1 - n2)
  | E_AMult (e1 e2 : aexp) (n1 n2 : nat) (st : state) :
      (e1 =[st]=> n1) ->
      (e2 =[st]=> n2) ->
      <{e1 * e2}> =[st]=> (n1 * n2)

  where "e '=[' st ']=>' n" := (aevalR st e n) : type_scope.

Theorem aevalR_iff_aeval : forall a st n,
  (a =[st]=> n) <-> aeval st a = n.
Proof. split.
(* --> *)
- intros H. induction H.
 -- reflexivity.
 -- reflexivity.
 -- simpl. subst. reflexivity.
 -- simpl. subst. reflexivity.
 -- simpl. subst. reflexivity.
(* <-- *)
- generalize dependent n. induction a.
 -- intros. subst. apply E_ANum.
 -- intros. subst. apply E_AId.
 -- intros. subst. simpl. apply E_APlus. 
    + apply IHa1. reflexivity.
    + apply IHa2. reflexivity.
 -- intros. subst. simpl. apply E_AMinus. 
    + apply IHa1. reflexivity.
    + apply IHa2. reflexivity.
 -- intros. subst. simpl. apply E_AMult. 
    + apply IHa1. reflexivity.
    + apply IHa2. reflexivity.
Qed.

Theorem aevalR_iff_aeval' : forall a st n,
  (a =[st]=> n) <-> aeval st a = n.
Proof. split.
  - intros H; induction H; simpl; subst; reflexivity.
  - generalize dependent n. induction a; intros; subst; simpl;
    constructor; try apply IHa1; try apply IHa2; reflexivity.
Qed.

(** Tacticals in Roq: tactics that take as input other tactics.
- The [;] Tactical: The compound tactic [T;T'] first performs [T] and then performs [T'] on _each subgoal_ generated by [T].
- The [try] Tactical: If [T] is a tactic, then [try T] is a tactic that is just like [T] except that, if [T] fails, [try T] _successfully_ does nothing at all (rather than failing).
**)

(** Some other useful tactics:
- subst : substitute away _all_ assumptions of the form [x = e]or [e = x] (where [x] is a variable).
- constructor :   - [constructor]: Try to find a constructor [c] (from some [Inductive] definition in the current environment) that can be applied to solve the current goal.  If one is found, behave like [apply c].
**)

Inductive com : Type :=
  | CSkip
  | CAsgn (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).

Notation "'skip'"  :=
         CSkip (in custom com at level 0) : com_scope.
Notation "x := y"  :=
         (CAsgn x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity) : com_scope.
Notation "x ; y" :=
         (CSeq x y)
           (in custom com at level 90,
            right associativity) : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" :=
         (CIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99) : com_scope.
Notation "'while' x 'do' y 'end'" :=
         (CWhile x y)
           (in custom com at level 89, x at level 99,
            y at level 99) : com_scope.


Definition c1 : com := 
<{
X := 5;
Z := X;
Y := 1
}>.

Definition c2 : com :=
<{
X := 2;
if X <= 1
  then Y := 3;
       X := 5 - Y
  else
       Z := 4
end;
Y := 4
}>.

Definition fact_in_imp : com :=
<{
Z := X;
Y := 1;
while Z <> 0 do
 Y := Y * Z;
 Z := Z - 1
end
}>.

Unset Printing Notations.
Print fact_in_imp.

Set Printing Notations.

Definition loop : com :=
  <{ while true do
       skip
     end }>.

Fixpoint ceval_try (st : state) (c : com) : state :=
match c with
| <{skip}> => st
| <{X := a}> => update st X (aeval st a)
| <{c1 ; c2}> => ceval_try (ceval_try st c1) c2
| <{if b then c1 else c2 end}> => if beval st b then ceval_try st c1 else ceval_try st c2
| <{while b do c end}> => st
end.

Definition s1 := ceval_try initial_state c1.

Compute s1 X.
Compute s1 Y.
Compute s1 Z.

Definition s2 := ceval_try initial_state c2.

Compute s2 X.
Compute s2 Y.
Compute s2 Z.

Reserved Notation
         "st '=[' c ']=>c' st'"
         (at level 40, c custom com at level 99,
          st constr, st' constr at next level).

Inductive cevalR : state -> com -> state -> Prop :=
| E_Skip (st : state) :
  st =[<{skip}>]=>c st
| E_Asgn (st : state) (X : string) (a : aexp) (n : nat) (Ha: aeval st a = n) :
  st =[<{X := a}>]=>c (X !-> n; st)
| E_Seq (st st' st'': state) (c1 c2 : com) (Hc1 : st =[c1]=>c st'') (Hc2 : st'' =[c2]=>c st') :
  st =[<{c1 ; c2}>]=>c st'
| E_IfTrue (st st' : state) (c1 c2 : com) (b : bexp) (HTrue : beval st b = true) (Hc1 : st =[c1]=>c st') :
  st =[<{if b then c1 else c2 end}>]=>c st'
| E_IfFalse (st st' : state) (c1 c2 : com) (b : bexp) (HFalse : beval st b = false) (Hc2 : st =[c2]=>c st') :
  st =[<{if b then c1 else c2 end}>]=>c st'
| E_WhileFalse (st : state) (c : com) (b : bexp) (HFalse : beval st b = false) :
  st =[<{while b do c end}>]=>c st
| E_WhileTrue (st st' st'': state) (c : com) (b : bexp) (HTrue: beval st b = true) (Hc: st =[c]=>c st'') (Hr: st'' =[<{while b do c end}>]=>c st') :
  st =[<{while b do c end}>]=>c st'

where "st =[ c ]=>c st'" := (cevalR st c st').

Example cevalR_example1 : initial_state =[c1]=>c (Y !-> 1; Z !-> 5; X !-> 5).
Proof. apply E_Seq with (st'' := (X !-> 5)).
  - apply E_Asgn. reflexivity.
  - apply E_Seq with (st'' := (Z !-> 5; X !-> 5)).
    -- apply E_Asgn. reflexivity.
    -- apply E_Asgn. reflexivity.
Qed.

Example cevalR_example12: initial_state =[c2]=>c (Y !-> 4; Z !-> 4; X !-> 2).
Proof.  apply E_Seq with (st'' := (X !-> 2)).
  -  apply E_Asgn. reflexivity.
  - apply E_Seq with (st'' := (Z !-> 4; X !-> 2)).
    -- apply E_IfFalse.
      + reflexivity.
      + apply E_Asgn. reflexivity.
    --  apply E_Asgn. reflexivity.
Qed.


Theorem cevalR_deterministic: forall c st st1 st2,
     st =[ c ]=>c st1  ->
     st =[ c ]=>c st2 ->
     st1 = st2.
Proof. intros c st st1 st2 E1 E2. generalize dependent st2.
  induction E1.
- intros st2 E2. inversion E2. reflexivity.
- intros st2 E2. inversion E2. subst. reflexivity.
- intros st2 E2. inversion E2. subst. apply IHE1_1 in Hc1. rewrite <- Hc1 in Hc2. apply IHE1_2 in Hc2. apply Hc2. 
- intros st2 E2. inversion E2. subst. apply IHE1. apply Hc1. rewrite HTrue in HFalse. discriminate HFalse.
- intros st2 E2. inversion E2. subst. rewrite HTrue in HFalse. discriminate HFalse. apply IHE1. apply Hc2.
-  intros st2 E2. inversion E2. reflexivity. rewrite HTrue in HFalse; discriminate HFalse.
-  intros st2 E2. inversion E2. Admitted. 














  






 




