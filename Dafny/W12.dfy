/** 

Methods, Asserts, Pre/post conditions
Termination, Inductive Datatypes

Ref. Programs and Proofs, Chapter 1-4 */


/* Method and assert statements */
method Triple (x : int) returns (r : int){
    var y := 2 * x;
    r := x + y;
    assert r == 3 * x;
    //assert r == 10 * x;
    //assert r < 5;
    //assert false;
}

/* if-else statement */
method Triple_If (x : int) returns (r : int){
    if x == 0 {
        r := 0;
    } else {
        var y := 2 * x;
        r := x + y;
    }
    assert r == 3 * x;
}

/* Methods contracts */

method Triple_Caller ()
{
    var t := Triple(10);
    assert t <= 100; 
}

method Triple_with_contract (x : int) returns (r : int)
  ensures r == 3 * x
{
    var y := 2 * x;
    r := x + y;
    //r := x;
}

method Triple_contract_caller ()
{
    var t := Triple_with_contract(10);
    assert t <= 100; 
}

method Triple_with_pre_post (x : int) returns (r : int)
  requires x % 2 == 0
  ensures r == 3 * x
{
  var y := x / 2;
  r := 6 * y;
}

/* Under-specification in method contracts */

method Index (n : int) returns (i : int)
  requires n >= 1
  ensures 0 <= i < n
{
  i := n/2;
}

method Caller_Index()
{
   var x := Index(50);
   var y := Index(50);
   assert x == y;
}

method MaxSum (x:int, y:int) returns (m : int, s: int)
  ensures m >= x && m >= y && (m == x || m == y)
  ensures s == x + y
{
  s := x + y;
  if x >= y
  {
    m := x;
  } else
  {
    m := y;
  }
}
method ReconstructFromMaxSum(s: int, m: int) returns (x: int, y: int)
    requires 2 * m >= s
    ensures s == x + y
    ensures (m == x || m == y) && x <= m && y <= m
{
    x := m;
    y := s - x;
}

method TestMaxSum(x: int, y: int) {
    var m, s := MaxSum(x, y);
    var xx, yy := ReconstructFromMaxSum(s, m);
    assert (xx == x && yy == y) || (xx == y && yy == x);
}

/** Functions in Dafny */

function abs (x : int) : int{
  if x >= 0 then x else -x
}

method Abs (x : int) returns (y: int)
ensures y >= 0
ensures y == abs(x)
{
  if x >= 0{
    return x;
  }else
  {
    return -x;
  }
}

method Caller_Abs()
{
  var t := Abs(-10);
  assert t == 10;
}

/** Ghost statements in Dafny

 * All statements which are used for specification purposes are called ghost statements.
 * They are ignored by the compiler.
 * Examples: Pre/post conditions, asserts, functions.
 * Variables can also be declared to be ghost, in which case they cannot be used in definition of normal variables.
*/

method Triple_with_ghost (x : int) returns (r : int)
  ensures r == 3*x
{
  var y := 2 * x;
  r := x + y;
  ghost var a,b := DoubleQuadruple(x);
  assert a <= r <= b || b <= r <= a;
}

ghost method DoubleQuadruple(x:int) returns (a:int, b:int)
  ensures a == 2*x && b == 4*x
{
  a := 2 * x;
  b := 2 * a;
}

/** 
- Dafny proves total correctness, and hence verifies that every method/function terminates.
- To help Dafny prove termination, the 'decreases' clause can be used.
- Dafny will check that the parameter of the decreases clause reduces from the original call to the recursive call.
- Note that the parameter of the decreases clause must remain non-negative in all calls.
 */

function Fib (n : nat): nat
  //decreases n
{
  if n < 2 then n else Fib (n-1) + Fib (n-2)
}

/** seq datatype: immutable sequence of elements, which can be accessed in an array-like fashion */
function SeqSum(s: seq<int>, lo: int, hi: int): int
requires 0 <= lo <= hi <= |s|
decreases hi - lo
{
  if lo == hi then 0 else s[lo] + SeqSum(s, lo + 1, hi)
}

/** Well-founded relations:
A binary relation > is well-founded if 
* > is irreflexive
* > is transitive
* > satisfies the descending chain condition: there is no infinite descending chain of values
a0, a1, a2,... such that a0 > a1 > a2 > ... 

Dafny allows the parameter of the decreases clause to have different types. It pre-defines a well-founded relation for different types (here X is the decreases-parameter of the original call, and y is the decreases-parameter of the recursive call):

type of X and y    |      X > y 
------------------------------------
bool                      X && !y
int                       X > y && X >= 0
real                      X - 1.0 >= y && X >= 0.9
seq<T>                    y is a consecutive proper sub-sequence of X
inductive datatypes       y is structurally included in X

Dafny checks the above well-founded relations between the decreases paramter of the original call and the recursive call.
*/

function F(x: int): int {
  if x < 10 then x else F(x - 1)
}

function G(x: int): int {
  if 0 <= x then G(x - 2) else x
}

function H(x: int): int 
  decreases x + 60
{
  if x < -60 then x else H(x - 1)
}

function L(x: int): int
  decreases 99 - x
{
  if x < 100 then L(x + 1) + 10 else x
}

/** Lexicographic tuples in the decreases clause */
function Ack(m: nat, n: nat): nat
decreases m, n
{
  if m == 0 then
    n + 1
  else if n == 0 then
    Ack(m - 1, 1)
  else
    Ack(m-1, Ack(m,n-1))
}

/** Inductive Datatypes */

datatype BYTree = BlueLeaf | YellowLeaf | Node(BYTree, BYTree)

function BlueCount(t: BYTree): nat {
  match t
  case BlueLeaf => 1
  case YellowLeaf => 0
  case Node(left, right) => BlueCount(left) + BlueCount(right)
}

function ReverseColors (t: BYTree): BYTree {
  match t
  case BlueLeaf => YellowLeaf
  case YellowLeaf => BlueLeaf
  case Node(left, right) => Node(ReverseColors(left), ReverseColors(right))
}

/** Discriminators and Destructors */

predicate IsNode (t: BYTree) {
  match t 
  case Node(_,_) => true
  case _ => false
}

/** Dafny pre-defines discriminators (such as the one shown above) for every constructor.
For BYTree, the discriminators are BlueLeaf?, YellowLeaf?, Node?
 */

method discriminators_test() {
  var a := Node(BlueLeaf,YellowLeaf);
  var b := BlueLeaf;
  assert(a.Node?);
  assert(b.Node?);
}

function GetLeft(t: BYTree): BYTree
  requires t.Node?
{
  match t
  case Node(left, _ ) => left
}

/** Dafny pre-defines a destructor such as the one shown above to obtain parameters of a constructor */

datatype BYTree_2 = BlueLeaf_2 | YellowLeaf_2 | Node_2(left: BYTree_2, right: BYTree_2)

function BlueCount_2 (t: BYTree_2):nat{
  if t.BlueLeaf_2? then 1
  else if t.YellowLeaf_2? then 0 
  else BlueCount_2(t.left) + BlueCount_2(t.right)
}

/** Type Parameters in Inductive datatypes */

datatype Tree<T> = LeafT(data : T)
                   | NodeT(left : Tree<T>, right : Tree<T>)

datatype Color = Blue | Yellow | Green | Red

predicate AllBlue(t : Tree<Color>){
  if t.LeafT? then
    (if t.data == Blue then true else false)
  else
    AllBlue(t.left) && AllBlue(t.right)
}

function size<T> (t : Tree<T>) : nat{
  if t.LeafT? 
    then 1
  else
    size<T>(t.left) + size<T>(t.right)
}






