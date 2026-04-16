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
             ==> //{assert(m >= 1);}
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

lemma MultCommutativeAuto (x:nat, y:nat)
    ensures Mult(x,y) == Mult(y,x)
{
    
}

lemma MultCommutative (x:nat, y:nat)
    ensures Mult(x,y) == Mult(y,x)
{
    if x == y
    {
        // Function congruence
        assert(Mult(x,x) == Mult(x,x));
    }
    else if y == 0
    {
        assert (Mult(x,y) == 0);
        assert (Mult(x-1,y) == 0);
        MultCommutative(y,x-1);
        assert (Mult(y,x-1) == Mult(x-1,y));
        assert (Mult(y,x) == y + Mult(y,x-1));
        assert(Mult(y,x) == 0);
    }
    else if x == 0
    {
        assert (Mult(y,x) == 0);
        assert (Mult(y-1,x) == 0);
        MultCommutative(x,y-1);
        assert (Mult(x,y-1) == Mult(y-1,x));
        assert (Mult(x,y) == x + Mult(x,y-1));
        assert(Mult(x,y) == 0);
    }
    else
    {
        assert(Mult(x,y) == x + Mult(x,y-1));
        MultCommutative(x,y-1);
        assert(Mult(x,y-1) == Mult(y-1,x));
        assert(Mult(y-1,x) == y-1 + Mult(y-1,x-1));
        assert(Mult(x,y) == x + y-1 + Mult(y-1,x-1));

        assert(Mult(y,x) == y + Mult(y,x-1));
        MultCommutative(x-1,y);
        assert(Mult(y,x-1) == Mult(x-1,y));
        assert(Mult(x-1,y) == x-1 + Mult(x-1,y-1));
        assert(Mult(y,x) == y + x-1 + Mult(x-1,y-1));

        MultCommutative(x-1,y-1);
    }
}

lemma MultCommutativeShort (x:nat, y:nat)
    ensures Mult(x,y) == Mult(y,x)
{
    if x == y
    {
        // Function congruence
    }
    else if y == 0
    {
        MultCommutativeShort(y,x-1);
    }
    else if x == 0
    {
        MultCommutativeShort(x,y-1);
    }
    else
    {
        MultCommutativeShort(x,y-1);
        MultCommutativeShort(x-1,y);
        MultCommutativeShort(x-1,y-1);
    }
}

// Proofs about inductive data types
module TreeProofs
{
datatype Tree<T> = Leaf(data: T)
                   | Node(left: Tree<T>, right: Tree<T>)

function Mirror<T>(t: Tree<T>): Tree<T> { 
    match t
    case Leaf(_) => t
    case Node(left, right) => Node(Mirror(right), Mirror(left))
}

lemma {:induction false} MirrorMirror<T>(t: Tree<T>) 
    ensures Mirror(Mirror(t)) == t
{
    if t.Leaf?
    {
        assert(Mirror(t) == t);
    }
    else
    {
        MirrorMirror(t.left);
        MirrorMirror(t.right);
    }
}

function Size<T>(t: Tree<T>): nat {
    match t
    case Leaf(_) => 1
    case Node(left, right) => Size(left) + Size(right) 
}

lemma {:induction false} MirrorSize<T>(t: Tree<T>) 
    ensures Size(Mirror(t)) == Size(t)
{
    match t
    case Leaf(_) => 
    case Node(left,right) => 
        calc{
            Size(Mirror(Node(left,right)));
            ==
            Size(Node(Mirror(right),Mirror(left)));
            ==
            Size(Mirror(right)) + Size(Mirror(left));
            == {MirrorSize(left); MirrorSize(right);}
            Size(right) + Size(left);
            ==
            Size(t);
        }
}
}

method evalTest()
{
    //x + 1 
    var e1 := Node(Add, Cons(Var("x"),(Cons(Const(1),Nil))));
    var env1 := map["x" := 1];
    assert(Eval(e1,env1) == 2);
    //(x + 1) + (y + 1) + (z + 1)
    var e2 := Node(Add, Cons(Node(Add, Cons(Var("x"),(Cons(Const(1),Nil)))),
                        Cons(Node(Add, Cons(Var("y"),(Cons(Const(1),Nil)))),
                        Cons(Node(Add, Cons(Var("z"),(Cons(Const(1),Nil)))),
                        Nil)
    )));
    var env2 := env1["y" := 1]["z" := 1];
    assert(Eval(e2,env2) == 6);
}

/** Suppose we want to perform a peephole optimization on expressions: by removing any subexpression which adds by 0 or multiplies by 1

(x + 0) + (y + 0) --> x + y 
(0 + 0) + (y + 0) --> y
 */

function Unit(op: Op): nat {
    match op 
    case Add => 0 
    case Mul => 1
}

function Optimize(e: Expr): Expr {
     if e.Node? then
        var args := OptimizeAndFilter(e.args, Unit(e.op));
        Shorten(e.op, args)
    else
        e
}

function Shorten(op: Op, args: List<Expr>): Expr{
    match args
    case Nil => Const(Unit(op))
    case Cons(e,Nil) => e
    case _ => Node(op, args)
}

function OptimizeAndFilter(es: List<Expr>, unit: nat): List<Expr> {
    match es
    case Nil => Nil
    case Cons(e, tail) =>
        var e', tail' := Optimize(e), OptimizeAndFilter(tail, unit);
        if e' == Const(unit) then tail' else Cons(e', tail') 
}

lemma OptimizeCorrect(e: Expr, env: map<string,nat>)
    ensures Eval(e,env) == Eval(Optimize(e),env)
{
    if e.Node? 
    {
        var args := OptimizeAndFilter(e.args, Unit(e.op));
        calc{
            Eval(Optimize(e),env);
            == 
            Eval(Shorten(e.op,args), env);
            == {ShortenCorrect(e.op,args,env);}
            Eval(Node(e.op,args),env);
            == {OptimizeAndFilterCorrect(e.op,e.args,env);}
            Eval(Node(e.op,e.args),env);
        }
    }
    else
    {

    }
}

lemma ShortenCorrect(op:Op, args: List<Expr>, env:map<string,nat>)
    ensures Eval(Node(op,args),env) == Eval(Shorten(op,args),env)
{
    match args
    case Nil =>
    case Cons(e,Nil) => 
        assert(Shorten(op,args) == e);
        if (op == Add)
        {
            assert(Eval(Node(op,args),env) == Eval(e,env) + EvalList(Nil,Add,env));
            assert(EvalList(Nil,Add,env) == 0);
        }
        else
        {
            assert(Eval(Node(op,args),env) == Eval(e,env) * EvalList(Nil,Mul,env));
            assert(EvalList(Nil,Mul,env) == 1);
        }
    case _ =>
}

lemma OptimizeAndFilterCorrect(op:Op, args: List<Expr>, env:map<string,nat>)
    ensures Eval(Node(op,args),env) == 
                    Eval(Node(op,OptimizeAndFilter(args,Unit(op))), env)
decreases args
{
    match args
    case Nil =>
    case Cons(e,tail) =>
        OptimizeCorrect(e,env);
        OptimizeAndFilterCorrect(op, tail, env);
}       

/** Lists in Dafny */
module Lists
{

datatype List<T> = Nil | Cons(head: T, tail: List<T>)

function Length<T>(xs: List<T>): nat {
    match xs
    case Nil => 0
    case Cons(_, tail) => 1 + Length(tail)
}

function Snoc<T>(xs: List<T>, y: T): List<T> {
    match xs
    case Nil => Cons(y, Nil)
    case Cons(x, tail) => Cons(x, Snoc(tail, y)) 
}

// The following lemma goes through automatically using induction.
lemma LengthSnoc<T>(xs: List<T>, y:T)
    ensures Length(Snoc(xs,y)) == Length(xs) + 1
{

}

function Append<T>(xs: List<T>, ys: List<T>): List<T> {
    match xs
    case Nil => ys
    case Cons(x, tail) => Cons(x, Append(tail, ys)) 
}

//The following is an example of an extrinsic specification
lemma LengthAppend<T>(xs: List<T>, ys: List<T>)
    ensures Length(Append(xs, ys)) == Length(xs) + Length(ys)
{

}

//The following is an example of an intrinsic specification, i.e. it is included with the definition.
function Append_2<T>(xs: List<T>, ys: List<T>): List<T> 
    ensures Length(Append_2(xs, ys)) == Length(xs) + Length(ys)
{
    match xs
    case Nil => ys
    case Cons(x, tail) => Cons(x, Append_2(tail, ys))
}

/** 
- Since methods in Dafny are opaque, all specifications must be intrinsic for methods. 
- Functions are transparent, so specifications can be intrinsic or extrinsic.
- Intrinsic specifications automatically come into the context on calling a function/method, while extrinsic specifications need to be explicitly loaded by calling lemmas.
- Having too many intrinsic specifications can overload the solver, and increase verification time.
- Hence, a common practice is to keep most specifications extrinsic for functions.
*/ 

function Find<T(==)>(xs: List<T>, y: T): nat 
    ensures Find(xs, y) <= Length(xs)
{
    match xs
    case Nil => 0
    case Cons(x, tail) =>
    if x == y then 0 else 1 + Find(tail, y) 
}

/** 
- The equality operator is automatically defined for every type in Dafny in the ghost context (i.e. in specifications, functions, lemmas, etc.).
- However, in the compiled context, equality operator is only defined for a limited set of types, specified by the type parameter T(==). This does not include for example functions.
- If we want to compile the Find function, we must restrict the type parameter to only those types for which the equality operator is also defined in the compiled context.
 */

function SlowReverse<T>(xs: List<T>): List<T> {
    match xs
    case Nil => Nil
    case Cons(x, tail) => Snoc(SlowReverse(tail), x) 
}

lemma LengthSlowReverse<T>(xs: List<T>)
    ensures Length(SlowReverse(xs)) == Length(xs)
{
    match xs
    case Nil => 
    case Cons(x, tail) => LengthSnoc(SlowReverse(tail),x);
}

function ReverseAux<T>(xs: List<T>, acc: List<T>): List<T>
{
    match xs
    case Nil => acc
    case Cons(x, tail) => ReverseAux(tail, Cons(x, acc))
}

lemma ReverseAuxCorrect<T>(xs: List<T>, acc: List<T>)
    ensures ReverseAux(xs,acc) == Append(SlowReverse(xs), acc)
{
    match xs
    case Nil =>
    case Cons(x, tail) =>
    calc{
        ReverseAux(xs,acc) == Append(SlowReverse(xs), acc);
        <==
        ReverseAux(Cons(x, tail),acc) == Append(SlowReverse(Cons(x, tail)), acc);
        <==
        ReverseAux(tail, Cons(x, acc)) == Append(Snoc(SlowReverse(tail), x), acc);
        <== {AppendSnoc(SlowReverse(tail), acc, x);}
        ReverseAux(tail, Cons(x, acc)) == Append(SlowReverse(tail), Cons(x,acc));
        <== {ReverseAuxCorrect(tail, Cons(x, acc));}
        true;
    }
}

lemma AppendSnoc<T>(xs1: List<T>, xs2: List<T>, x :T)
    ensures Append(Snoc(xs1,x),xs2) == Append(xs1,Cons(x,xs2))
{
    match xs1
    case Nil =>
    case Cons(h,t) => 
    calc{
        Append(Snoc(Cons(h,t),x),xs2);
        ==
        Append(Cons(h,Snoc(t,x)),xs2);
        ==
        Cons(h,Append(Snoc(t,x),xs2));
        == {AppendSnoc(t,xs2,x);}
        Cons(h,Append(t,Cons(x,xs2)));
        ==
        Append(Cons(h,t),Cons(x,xs2));
    }
}

function Reverse<T>(xs: List<T>): List<T> {
    ReverseAux(xs, Nil)
}

lemma ReverseCorrect<T>(xs: List<T>)
    ensures Reverse(xs) == SlowReverse(xs)
{
    calc{
        Reverse(xs);
        ==
        ReverseAux(xs,Nil);
        == {ReverseAuxCorrect(xs,Nil);}
        Append(SlowReverse(xs), Nil);
        == {AppendNil(SlowReverse(xs));}
        SlowReverse(xs);
    }
}

lemma AppendNil<T>(xs: List<T>)
    ensures Append(xs,Nil) == xs
{

}

/** To prove intrinsic specifications, Dafny allows proof-related constructs such as assertions, lemma calls and proof calculations to be directly embedded inside programs/expressions.
 */

function ReverseAuxI<T>(xs: List<T>, acc: List<T>): List<T>
    ensures ReverseAuxI(xs,acc) == Append(SlowReverse(xs), acc)
{
    match xs
    case Nil => acc
    case Cons(x, tail) => 
        calc{
            ReverseAuxI(tail, Cons(x, acc)) == Append(Snoc(SlowReverse(tail), x), acc);
            <== {AppendSnoc(SlowReverse(tail), acc, x);}
            ReverseAuxI(tail, Cons(x, acc)) == Append(SlowReverse(tail), Cons(x,acc));
        }
        ReverseAuxI(tail, Cons(x, acc))
}

/** Sorting */

/** The specification is defined using a recursive predicate which ensures that any two consecutive elements of the list are ordered. */

function At<T>(xs: List, i: nat) : T
    requires i < Length(xs)
{
    match (xs, i)
    case (Cons(x, _), 0) => x
    case (Cons(x, tail), i) => At(tail, i-1)
}

predicate Ordered(xs: List<int>) { 
    match xs
    case Nil => true
    case Cons(x, Nil) => true
    case Cons(x, Cons(y, _)) => x <= y && Ordered(xs.tail)
}

lemma AllOrdered(xs: List<int>, i: nat, j: nat) 
    requires Ordered(xs) && i <= j < Length(xs) 
    ensures At(xs, i) <= At(xs, j)
{
    if (i == j)
    {

    }
    else if (i + 1 == j)
    {

    }
    else
    {
        AllOrdered(xs, i, j-1);
    }
}

/** We also need the sorted output list and the input list to have the same elements.
More precisely, the sorted output list should be a permutation of the input list.
We specify this by saying that the multiset of elements in the input list is the same as the output list. */

function Project(xs: List<int>, p: int): List<int> {
    match xs
    case Nil => Nil
    case Cons(x, tail) =>
        if x == p then Cons(x, Project(tail, p)) else Project(tail, p) }

/** Insertion Sort */

function InsertionSort(xs: List<int>): List<int> {
    match xs
    case Nil => Nil
    case Cons(x, tail) => Insert(x, InsertionSort(tail)) 
}

function Insert(x: int, xs: List<int>): List<int> {
    match xs
    case Nil => Cons(x, Nil) 
    case Cons(y, tail) =>
        if x <= y then Cons(x, xs) else Cons(y, Insert(x, tail)) 
}

lemma InsertionSortOrdered(xs: List<int>) 
    ensures Ordered(InsertionSort(xs))
{
    match xs
    case Nil =>
    case Cons(x, tail) => 
        InsertOrdered(x, InsertionSort(tail));
}

lemma InsertOrdered(x: int, xs: List<int>)
    requires Ordered(xs)
    ensures Ordered(Insert(x, xs))
{

}

lemma InsertionSortSameElements(xs: List<int>, p: int)
    ensures Project(xs, p) == Project(InsertionSort(xs), p)
{
    match xs
    case Nil =>
    case Cons(x, tail) =>
        if x == p
        {
            calc{
                Project(InsertionSort(Cons(x, tail)), p);
                ==
                Project(Insert(x, InsertionSort(tail)), p);
                == {InsertSameElements(x, InsertionSort(tail), p);}
                Project(Cons(x, InsertionSort(tail)), p);
                ==
                Cons(x, Project(InsertionSort(tail), p));
                == {InsertionSortSameElements(tail,p);}
                Cons(x, Project(tail, p));
                ==
                Project(Cons(x,tail), p);
            } 
        }
        else
        {
            calc{
                Project(InsertionSort(Cons(x, tail)), p);
                ==
                Project(Insert(x, InsertionSort(tail)), p);
                == {InsertSameElements(x, InsertionSort(tail), p);}
                Project(Cons(x, InsertionSort(tail)), p);
                ==
                Project(InsertionSort(tail), p);
                == {InsertionSortSameElements(tail,p);}
                Project(tail, p);
                ==
                Project(Cons(x,tail), p);
            }
        }        
}

lemma InsertSameElements(x: int, xs: List<int>, p: int)
    ensures Project(Cons(x, xs), p) == Project(Insert(x, xs), p)
{

}

}

method Main() {
    var xs, i := Lists.Nil, 0; 
    while i < 5 {
        xs, i := Lists.Cons(i, xs), i + 1;
    }
    print xs, "\n"; 
}





