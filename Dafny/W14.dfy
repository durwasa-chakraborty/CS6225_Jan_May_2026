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

function Fib(n: nat): nat {
	if n < 2 then n else Fib(n - 2) + Fib(n - 1)
}

method ComputeFib(n: nat) returns (x: nat)
	ensures x == Fib(n)
{
	x := 0;
	var y := 1;
	var i := 0;
	while i != n
		invariant 0 <= i <= n
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


method ArrayIntro()
{
	var a := new int[20](i => 0);   // a is of type array<int>
	var b := a;											// arrays are allocated on the heap
	b[0] := b[0] + 1;								// When copying, only the reference is copied
	assert (a[0] == 1);

	var s := [0, 1, 2];							// s is of type seq<int>
	//s[0] := s[0] + 1;						  // gives an error as sequences are immutable
	s := s + [3, 4, 5];							// + is the concatenation operator for sequences
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
