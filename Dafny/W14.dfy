/** Proof by contradiction in Dafny

General shape:

lemma Lem(args)
  requires P(x)
  ensures Q(x)
{
  if !Q(x)
  {
    assert !P(x) && P(x)
    assert false
  }
}

 */

lemma exfalso()
  requires false
  ensures 1 == 2
{
  
}

lemma L(i : int)
  requires i > 42
  ensures i > 0
{
  if i <= 0
  {
    assert(i <= 42 && i > 42);
    assert(false);
    assert(i > 0);
  }
  else
  {

  }
}

lemma isSingle(s: set<int>, i: int)
  requires |s| == 1 && i in s
  ensures s == {i}
{
  if s > {i}
  {
    assert(|s - {i}| >= 1);
    assert(|s| > 1 && |s| == 1);
    assert(false);
  }
  else
  {

  }
}

/** Loops and Loop Invariants */

/**
For a loop:
while B
	invariant J
	decreases D
{
	Body
}

- The code before the loop must ensure that J holds when entering the loop for the first time
	- Essentially, an implicit assert(J) before the loop.
- The code after the loop can assume J && !B
- The loop body must ensure the following Hoare Triple
{{ J && B }}
	ghost var d0 := D;
	Body
{{ J && d0 > D }}
 */

method DivMod(x: nat, y: nat) returns (q: nat, r: nat)
  requires y != 0
  ensures x == q * y + r && r < y
{
	q := 0;
	r := x;
	while(r >= y)
		invariant x == q * y + r
		decreases r
	{
		q := q + 1;
		r := r - y;
	}
}

/** Recursive specifications, iterative implementations */

function Fib(n: nat): nat {
	if n < 2 then n else Fib(n - 2) + Fib(n - 1)
}

method ComputeFib(n: nat) returns (x: nat)
	ensures x == Fib(n)
{
	x := 0;
	var y := 1;
	var i := 0;
	while i < n
		invariant i <= n
		invariant x == Fib(i) && y == Fib(i+1)
	{
		x, y := y, x + y;
		i := i + 1;
	}
}

function Exp(b: nat, n: nat) : nat{
	if n == 0 then 1 else b * Exp(b, n-1)
}

method ComputeExp(b: nat, n: nat) returns (p: nat)
	ensures p == Exp(b, n)
{
	p := 1;
	var i := 0;
	while i != n
		invariant 0 <= i <= n
		invariant p == Exp(b, i)
	{
		p := p * b;
		i := i + 1;
	}
}

/** Arrays and Sequences */

method ArrayIntro()
{
	var a := new int[20](i => 0);   // a is of type array<int>
	var b := a;						// arrays are allocated on the heap
	b[0] := b[0] + 1;				// When copying, only the reference is copied
	assert (a[0] == 1);

	var s := [0, 1, 2];				// s is of type seq<int>
	//s[0] := s[0] + 1;				// gives an error as sequences are immutable
	var t := s;						// a copy of the sequence is created 
	t := t + [3, 4, 5];				// + is the concatenation operator for sequences
	assert (t == [0,1,2,3,4,5]);
	assert (s == [0,1,2]);
}

method LinearSearch1<T>(a: array<T>, P: T -> bool) returns (n: int) 
	ensures 0 <= n <= a.Length
	ensures n == a.Length || P(a[n])
	ensures n == a.Length ==>
			forall i :: 0 <= i < a.Length ==> !P(a[i])
{
	n := 0;
	while n != a.Length
	invariant 0 <= n <= a.Length
	invariant forall i :: 0 <= i < n ==> !P(a[i])
	{
		if P(a[n]){
			return;
		}
		n := n + 1;
	}
}

predicate one(m : int){
	m==1
}

method SearchCaller()
{
	var a := new int[][1,2,3,4,5];
	var n := LinearSearch1(a, one);
	if (n == 5)
	{
		assert(a[0] != 1 && a[0] == 1);
		assert(n == 0);
	}
	else
	{
		assert (n == 0);
	}
}

method LinearSearch2<T>(a: array<T>, P: T -> bool) returns (n: nat)
	requires exists i :: 0 <= i < a.Length && P(a[i])
	ensures 0 <= n < a.Length
	ensures P(a[n])
{
	n := 0;
	while(n != a.Length)
	invariant 0 <= n < a.Length
	invariant exists i :: n <= i < a.Length && P(a[i])
	{
		if (P(a[n]))
		{
			return;
		}
		n := n + 1;
	}
}

method BinarySearch(a: array<int>, key: int) returns (n: int)
  requires forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  ensures 0 <= n <= a.Length
  ensures forall i :: 0 <= i < n ==> a[i] < key
  ensures forall i :: n <= i < a.Length ==> key <= a[i]
{
  var lo, hi := 0, a.Length;
  while lo < hi
    invariant 0 <= lo <= hi <= a.Length
    invariant forall i :: 0 <= i < lo ==> a[i] < key
    invariant forall i :: hi <= i < a.Length ==> key <= a[i]
  {
    var mid := (lo + hi) / 2;
    if a[mid] < key {
      lo := mid + 1;
    } else {
      hi := mid;
    }
  }
  n := lo;
}

method Contains(a: array<int>, key: int)
	requires forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
	requires exists i :: 0 <= i < a.Length && a[i] == key
{
	var n := BinarySearch(a, key);
	assert(a[n] == key);
}

method Min(a: array<int>) returns (m: int)
	requires a.Length != 0
	ensures forall i :: 0 <= i < a.Length ==> m <= a[i]
	ensures exists i :: 0 <= i < a.Length && a[i] == m
{
	m := a[0];
	var n := 1;
	while(n != a.Length)
	invariant 1 <= n <= a.Length
	invariant forall i :: 0 <= i < n ==> m <= a[i]
	invariant exists i :: 0 <= i < n && a[i] == m
	{
		if a[n] < m
		{
			m := a[n];
		}
		n := n + 1;
	}
}

/** Loop frames */

method LoopFrameExample(X: int, Y: int)
  requires 0 <= X <= Y
{
	var i, a, b := 0, X, Y;
  	while i < 100
	invariant Y <= b
  	{
   		i, b := i + 1, b + X;
  	}
  	assert a == X;      //Dafny automatically infers that a and X are unchanged by the loop
  	assert Y <= b; 
}

/**
- Loop frame are variables which are not modified inside a loop.
- Parameters of a function can never be modified, and hence are always part of the loop frame.
- For local variables, Dafny inspects the body and automatically determines which variables are not on the LHS of an assignment statement.
- For arrays, programmers have to write an explicit modifies clause to indicate which array variables would be modified.
 */

method SetEndPoints(a: array<int>, left: int, right: int)
  requires a.Length != 0
  modifies a
{
  a[0] := left;
  a[a.Length - 1] := right;
}

method EndPointCaller()
{
	var a := new int[10] (i => i+1);
	assert(a[0] == 1);
	SetEndPoints(a, 0, 0);
	assert(a[0] == 1);    // SetEndPoints is modifying the array, so all assertions
	assert(a[1] == 2);	  // regarding its elements will fail.
	assert(a[0] == 0);    // The specification of SetEndPoints is not precise enough
}

method Aliases(a: array<int>, b: array<int>)
  requires 100 <= a.Length
  modifies a
{
  a[0] := 10;
  var c := a;
  if b == a {  
	//Dafny is automatically able to infer that a and b are aliases here
    b[10] := b[0] + 1;   
  }
  c[20] := a[14] + 2;
}

method Increment(a: array<int>, i: int)
  requires 0 <= i < a.Length
  modifies a
  ensures a[i] == old(a[i]) + 1 
  // We can use old(a[i]) refer to the value of the array element at index i at the beginning of the method, i.e. the method's pre-state
{
  a[i] := a[i] + 1; 
}

method InitArray(a: array<int>, d: int)
	modifies a
	ensures forall i :: 0 <= i < a.Length ==> a[i] == d
{
	var n := 0;
	while n != a.Length
	invariant 0 <= n <= a.Length
	invariant forall i :: 0 <= i < n ==> a[i] == d
	{
		a[n] := d;
		n := n + 1;
	}
}

method InitArrayWithoutLoops(d: int)
{
	var a := new int[100] (i => d);
	assert (forall i :: 0 <= i < a.Length ==> a[i] == d);
}

method IncrementAll(a: array<int>)
	ensures forall i :: 0 <= i < a.Length ==> a[i] == old(a[i]) + 1
	modifies a
{
	var n := 0;
	while(n != a.Length)
	invariant 0 <= n <= a.Length
	invariant forall i :: 0 <= i < n ==> a[i] == old(a[i]) + 1
	//default modifies clause of a loop is the same as the enclosing method
	{
		//assert(a[n] + 1 == old(a[n]) + 1);
		a[n] := a[n] + 1;
		//assert(forall i :: 0 <= i < n ==> a[i] == old(a[i]) + 1);
		//assert(a[n] == old(a[n]) + 1);
		//assert(forall i :: 0 <= i < n + 1 ==> a[i] == old(a[i]) + 1);
		n := n + 1;
	}
}

method IncrementAllCorrect(a: array<int>)
	ensures forall i :: 0 <= i < a.Length ==> a[i] == old(a[i]) + 1
	modifies a
{
	var n := 0;
	while(n != a.Length)
	invariant 0 <= n <= a.Length
	invariant forall i :: 0 <= i < n ==> a[i] == old(a[i]) + 1
	invariant forall i :: n <= i < a.Length ==> a[i] == old(a[i])
	{
		a[n] := a[n] + 1;
		n := n + 1;
	}
}

method Copy(src: array, dst: array)
	modifies dst
	requires src.Length == dst.Length
	ensures forall i :: 0 <= i < src.Length ==> old(src[i]) == dst[i]
{
	var n := 0;
	while(n != src.Length)
	invariant 0 <= n <= src.Length
	invariant forall i :: 0 <= i < n ==> old(src[i]) == dst[i]
	invariant forall i :: 0 <= i < src.Length ==> old(src[i]) == src[i]
	{
		dst[n] := src[n];
		n := n + 1;
	}
}