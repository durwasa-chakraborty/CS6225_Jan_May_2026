/** Abstract Syntax Trees for Arithmetic Expressions

Recall the definition from Rocq:
Inductive aexp := 
| ANum (n:nat)
| AVar (v:string)
| APlus (a1 a2: aexp)
| AMult (a1 a2: aexp)
| AMinus (a1 a2: aexp).

 */

datatype Expr = Const(n:nat)
| Var(v:string)
| Node(op: Op, args: List<Expr>)

datatype Op = Add | Mul

datatype List<T> = Nil | Cons(head: T, tail: List<T>)

function Eval(e : Expr, env : map<string,nat>) : nat
    decreases e
{
    match e
    case Const(n) => n
    case Var(s) => if s in env.Keys then env[s] else 0
    case Node(op,args) => EvalList(args, op, env)
}

function EvalList(args: List<Expr>, op: Op, env: map<string,nat>):nat
    decreases args
{
    match args
    case Nil => if op == Add then 0 else 1
    case Cons(h,t) => 
        var n1,n2 := Eval(h,env), EvalList(t, op, env); 
            // var bindings inside expressions can be thought of as let expressions.
        if op == Add then n1 + n2 else n1 * n2 
}

/** For mutually recursive functions, the termination argument requires the decreases parameter of every call to be decreasing.

For the call from Eval to EvalList:
Node(op,args) [parameter e of Eval]  > args [parameter args of EvalList]

For the call from EvalList to Eval:
Cons(h,t) [parameter args of EvalList] > h [parameter e of Eval]

For the call from EvalList to EvalList:
Cons(h,t) [parameter args of EvalList] > t [parameter args of Eval]
 */

/** We can enforce a requirement that evaluation of an expression is only possible if its variables have been assigned a value in the environment*/

module EvalWithGoodEnv
{

datatype Expr = Const(n:nat)
| Var(v:string)
| Node(op: Op, args: List<Expr>)

datatype Op = Add | Mul

datatype List<T> = Nil | Cons(head: T, tail: List<T>)


function Eval(e : Expr, env : map<string,nat>) : nat
    requires GoodEnv(env,e)
    decreases e
{
    match e
    case Const(n) => n
    case Var(s) => env[s]
    case Node(op,args) => EvalList(args, op, env)
}

function EvalList(args: List<Expr>, op: Op, env: map<string,nat>):nat
    requires GoodEnvList(env, args)
    decreases args
{
    match args
    case Nil => if op == Add then 0 else 1
    case Cons(h,t) => 
        var n1,n2 := Eval(h,env), EvalList(t, op, env);
        if op == Add then n1 + n2 else n1 * n2 
}

predicate GoodEnv(env: map<string,nat>, e: Expr){
    match e
    case Var(s) => if s in env.Keys then true else false
    case Node(op,args) => GoodEnvList(env,args)
    case _ => true
}

predicate GoodEnvList(env: map<string,nat>, el: List<Expr>){
    match el
    case Nil => true
    case Cons(h,t) => GoodEnv(env,h) && GoodEnvList(env,t)
}
}

/** Lemmas and Proofs */

/** Suppose we want to express that the following function always returns a value greater than its argument */
function More(x: int): int {
    if x <= 0 then 1 else More(x - 2) + 3
}

/** A lemma is similar to a method: it has parameters, a pre-condition/post-condition, as well a body.
- The logical assertion made by the lemma is its post-condition.
- A lemma can be called by any other method, in which case the caller can assume the post-condition of the lemma. */

lemma Increasing(x: int)
    ensures x < More(x)
{

}

method ExampleLemmaUse(a: int) {
    var b := More(a);
    var c := More(b);
    Increasing(a);
    Increasing(b);
    assert 2 <= c - a;
}

lemma {:induction false} Increasing_2(x: int)
    ensures x < More(x)
{
    if x <= 0 { // this case verifies automatically
    } else { // this case does not verify automatically
      Increasing_2(x-2);   // this establishes that x-2 < More(x-2)
    }
}

lemma Increasing_wrong(x: int)
    ensures x < More(x)
{
    Increasing_wrong(x);
}
/** The proof of Increasing_2 as a decorated program:

lemma {:induction false} Increasing(x: int)
    ensures x < More(x)
{
    { { true } }
    if x <= 0 {
        { { x <= 0 } }
        { { x <= 0 && More(x) == 1 } } // def. More for x <= 0
        { { x < More(x) } }
    } else {
        { { 0 < x } }
        { { 0 < x && More(x) == More(x - 2) + 3 } } // def. More for 0 < x
        Increasing(x - 2); // induction hypothesis
        { { 0 < x && More(x) == More(x - 2) + 3 && x - 2 < More(x - 2) } }
        { { More(x) == More(x - 2) + 3 && x + 1 < More(x - 2) + 3 } }
        { { x + 1 < More(x) } }
        { { x < More(x) } }
    }
    { { x < More(x) } }
}

 */

lemma {:induction false} Increasing_verbose(x: int)
    ensures x < More(x)
{
    if x <= 0 {
        assert More(x) == 1; // def. More for x <= 0
    } else {
        assert More(x) == More(x - 2) + 3; // def. More for 0 < x
        Increasing_verbose(x - 2); // induction hypothesis
        assert x - 2 < More(x - 2); // what we get from the recursive call
        assert x + 1 < More(x - 2) + 3; // add 3 to each side
        assert x + 1 < More(x); // previous line and def. More above
    }
}

function Reduce(m: nat, x: int): int {
    if m == 0 then x else Reduce(m / 2, x + 1) - m
}

lemma {:induction false} Decreasing(m:nat, x:int)
    ensures Reduce(m,x) <= x
{
    if m == 0 
    {
        calc{
            Reduce(m,x) == x;
            ==>
            Reduce(m,x) <= x;
        }

    }
    else
    {
        calc{
            true;
             ==> {Decreasing(m/2,x+1);}
            Reduce(m/2,x+1) <= x + 1;
             ==> {assert(m >= 1);}
            Reduce(m/2,x+1) <= x + m; 
             ==>
            Reduce(m/2,x+1) - m <= x;
             ==> {assert(Reduce(m,x) == Reduce(m/2,x+1)-m);}
            Reduce(m,x) <= x;
        }
    }
}

lemma {:induction false} ReduceLowerBound(m: nat, x: int)
    ensures x - 2 * m <= Reduce(m, x)
{
    if m == 0 
    {
        calc{
            Reduce(m,x) == x;
            ==>
            x - 2 * m <= Reduce(m,x);
        }
    }
    else
    {
        calc{
            true; 
            ==> {ReduceLowerBound(m/2,x+1);}
            x + 1 - 2 * (m / 2) <= Reduce(m/2,x+1);
            ==> {assert (2 * (m / 2) <= m);}
            x + 1 - m <= Reduce(m/2,x+1);
            ==> {assert (x - m <= x + 1 - m);}
            x - m <= Reduce(m/2,x+1);
            ==>
            x - 2 * m <= Reduce(m/2,x+1) - m;
            ==>
            x - 2 * m <= Reduce(m,x);
        }
    }
}

function Mult(x: nat, y: nat): nat {
    if y == 0 then 0 else x + Mult(x, y - 1)
}

lemma {:induction false} MultCommutative (x:nat, y:nat)
    ensures Mult(x,y) == Mult(y,x)
{
    if x == y
    {
    }
    else if y == 0
    {
        assert (Mult(x,y) == 0);
        MultCommutative(y,x-1);
        assert(Mult(y,x) == 0);
    }
    else
    {
        assert(Mult(x,y) == x + Mult(x,y-1));
        assert(Mult(y,x) == y + Mult(y,x-1));
        MultCommutative(x,y-1);
    }
}