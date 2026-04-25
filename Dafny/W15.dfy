datatype Color = Red | White | Blue

predicate Below(c: Color, d: Color) {
  c == Red || c == d || d == Blue
}

method DutchFlag(a: array<Color>)
  modifies a
  ensures forall i, j :: 0 <= i < j < a.Length ==> Below(a[i], a[j])
  ensures multiset(a[..]) == old(multiset(a[..]))
{
  var r, w, b := 0, 0, a.Length;
  while w < b
    invariant 0 <= r <= w <= b <= a.Length
    invariant forall i :: 0 <= i < r ==> a[i] == Red
    invariant forall i :: r <= i < w ==> a[i] == White
    invariant forall i :: b <= i < a.Length ==> a[i] == Blue
    invariant multiset(a[..]) == old(multiset(a[..]))
  {
    match a[w]
    case White =>
      w := w + 1;
    case Red =>
      a[r], a[w] := a[w], a[r];
      r, w := r + 1, w + 1;
    case Blue =>
      a[w], a[b-1] := a[b-1], a[w];
      b := b - 1;
  }
}

//Selection Sort, 1st attempt

method SelectionSort1(a: array<int>)
  modifies a
  ensures forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  ensures multiset(a[..]) == old(multiset(a[..]))
{
  var n := 0;
  while n != a.Length
    invariant 0 <= n <= a.Length
    invariant forall i, j :: 0 <= i < j < n ==> a[i] <= a[j] 
    invariant multiset(a[..]) == old(multiset(a[..]))
  {
    var mindex, m := n, n + 1;
    while m != a.Length
      invariant n <= mindex < m <= a.Length
      invariant forall i :: n <= i < m ==> a[mindex] <= a[i]
    {
      if a[m] < a[mindex] {
        mindex := m;
      }
      m := m + 1;
    }
    a[n], a[mindex] := a[mindex], a[n];
    n := n + 1;
  }
}

predicate SplitPoint(a: array<int>, n: int)
  requires 0 <= n <= a.Length
  reads a
{
  forall i, j :: 0 <= i < n <= j < a.Length ==> a[i] <= a[j]
}

method SelectionSort(a: array<int>)
  modifies a
  ensures forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  ensures multiset(a[..]) == old(multiset(a[..]))
{
  var n := 0;
  while n != a.Length
    invariant 0 <= n <= a.Length
    invariant forall i, j :: 0 <= i < j < n ==> a[i] <= a[j]
    invariant multiset(a[..]) == old(multiset(a[..]))
    invariant SplitPoint(a, n)
  {
    var mindex, m := n, n + 1;
    while m != a.Length
      invariant n <= mindex < m <= a.Length
      invariant forall i :: n <= i < m ==> a[mindex] <= a[i]
    {
      if a[m] < a[mindex] {
        mindex := m;
      }
      m := m + 1;
    }
    a[n], a[mindex] := a[mindex], a[n];
    n := n + 1;
  }
}


class ChecksumMachine
{
  ghost var data: string
  var cs: int
  ghost function Hash(s: string): int
  {
    SumChars(s) % 137
  }

  ghost function SumChars(s: string): int
  {
    if |s| == 0 then 0 else
      var last := |s| - 1;
      SumChars(s[..last]) + s[last] as int
  }

  ghost predicate Valid()
    reads this
  {
    cs == Hash(data)
  }

  constructor()
    modifies this
    ensures Valid() && data == ""
  {
    data, cs := "", 0;
  }
}
