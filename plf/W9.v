(**

Hoare Logic
Ref.: Software Foundations, Volume 2, Hoare2.v

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