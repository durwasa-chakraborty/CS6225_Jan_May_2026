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





 




