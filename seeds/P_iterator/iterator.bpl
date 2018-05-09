// Automatically generated (12/12/2017 1:55:17.236 PM)

// File: /home/caf/tools/eve_96960/library/base/mml/set.bpl

// Finite sets.
// (Originally from Dafny Prelude: Copyright (c) Microsoft)

// Set type
type Set T = [T]bool;

// Cardinality
function Set#Card<T>(Set T): int;
axiom (forall<T> s: Set T :: { Set#Card(s) } 0 <= Set#Card(s));

// Empty set
function Set#Empty<T>(): Set T;
axiom (forall<T> o: T :: { Set#Empty()[o] } !Set#Empty()[o]);
axiom (forall<T> s: Set T :: { Set#Card(s) }
  (Set#Card(s) == 0 <==> s == Set#Empty()));// &&
  // (Set#Card(s) != 0 ==> (exists x: T :: s[x])));
axiom (forall<T> f: Field (Set T) :: { Default(f) } Default(f) == Set#Empty() : Set T);

// Singleton set
function Set#Singleton<T>(T): Set T;
axiom (forall<T> r: T :: { Set#Singleton(r) } Set#Singleton(r)[r]);
axiom (forall<T> r: T, o: T :: { Set#Singleton(r)[o] } Set#Singleton(r)[o] <==> r == o);
axiom (forall<T> r: T :: { Set#Card(Set#Singleton(r)) } Set#Card(Set#Singleton(r)) == 1);
axiom (forall<T> s: Set T, x: T :: { Set#Singleton(x), Set#Card(s) } Set#Card(s) == 1 && s[x]  ==>  s == Set#Singleton(x));

// Is a set empty?
function {: inline } Set#IsEmpty<T>(s: Set T): bool
{ Set#Equal(s, Set#Empty()) }

// An arbitrary element of a nonempty set
function Set#AnyItem<T>(Set T): T;
axiom (forall<T> s: Set T :: { Set#AnyItem(s) }
  !Set#IsEmpty(s) ==> s[Set#AnyItem(s)]);

// Are two sets equal?
function Set#Equal<T>(Set T, Set T): bool;
axiom(forall<T> a: Set T, b: Set T :: { Set#Equal(a,b) }
  Set#Equal(a,b) <==> (forall o: T :: {a[o]} {b[o]} a[o] <==> b[o]));
axiom(forall<T> a: Set T, b: Set T :: { Set#Equal(a,b) }  // extensionality axiom for sets
  Set#Equal(a,b) ==> a == b);

// Is a subset of b?
function Set#Subset<T>(Set T, Set T): bool;
axiom(forall<T> a: Set T, b: Set T :: { Set#Subset(a,b) }
  Set#Subset(a,b) <==> (forall o: T :: {a[o]} {b[o]} a[o] ==> b[o]));
axiom(forall<T> a: Set T, b: Set T :: { Set#Subset(a,b), Set#Card(a) }{ Set#Subset(a,b), Set#Card(b) }
  Set#Subset(a,b) ==> Set#Card(a) <= Set#Card(b));


// Is a superset of b?
function {: inline } Set#Superset<T>(a: Set T, b: Set T): bool
{ Set#Subset(b, a) }

// Are a and b disjoint?
function Set#Disjoint<T>(Set T, Set T): bool;
axiom (forall<T> a: Set T, b: Set T :: { Set#Disjoint(a,b) }
  Set#Disjoint(a,b) <==> (forall o: T :: {a[o]} {b[o]} !a[o] || !b[o]));

// Set extended with one element
function Set#Extended<T>(Set T, T): Set T;
axiom (forall<T> a: Set T, x: T, o: T :: { Set#Extended(a,x)[o] }
  Set#Extended(a,x)[o] <==> o == x || a[o]);
axiom (forall<T> a: Set T, x: T :: { Set#Extended(a, x) }
  Set#Extended(a, x)[x]);
axiom (forall<T> a: Set T, x: T, y: T :: { Set#Extended(a, x), a[y] }
  a[y] ==> Set#Extended(a, x)[y]);
axiom (forall<T> a: Set T, x: T :: { Set#Card(Set#Extended(a, x)) }
  a[x] ==> Set#Card(Set#Extended(a, x)) == Set#Card(a));
axiom (forall<T> a: Set T, x: T :: { Set#Card(Set#Extended(a, x)) }
  !a[x] ==> Set#Card(Set#Extended(a, x)) == Set#Card(a) + 1);

// Set with one element removed
function Set#Removed<T>(Set T, T): Set T;
axiom (forall<T> a: Set T, x: T, o: T :: { Set#Removed(a,x)[o] }
  Set#Removed(a,x)[o] <==> o != x && a[o]);
axiom (forall<T> a: Set T, x: T :: { Set#Removed(a, x) }
  !Set#Removed(a, x)[x]);
// axiom (forall<T> a: Set T, x: T, y: T :: { Set#Removed(a, x), a[y] }
  // Set#Removed(a, x)[y] ==> a[y]);
axiom (forall<T> a: Set T, x: T :: { Set#Card(Set#Removed(a, x)) }
  a[x] ==> Set#Card(Set#Removed(a, x)) == Set#Card(a) - 1);
axiom (forall<T> a: Set T, x: T :: { Set#Card(Set#Removed(a, x)) }
  !a[x] ==> Set#Card(Set#Removed(a, x)) == Set#Card(a));

// Union of two sets
function Set#Union<T>(Set T, Set T): Set T;
axiom (forall<T> a: Set T, b: Set T, o: T :: { Set#Union(a,b)[o] }
  Set#Union(a,b)[o] <==> a[o] || b[o]);
axiom (forall<T> a, b: Set T, y: T :: { Set#Union(a, b), a[y] }
  a[y] ==> Set#Union(a, b)[y]);
axiom (forall<T> a, b: Set T, y: T :: { Set#Union(a, b), b[y] }
  b[y] ==> Set#Union(a, b)[y]);
axiom (forall<T> a, b: Set T :: { Set#Union(a, b) }
  Set#Disjoint(a, b) ==>
    Set#Difference(Set#Union(a, b), a) == b &&
    Set#Difference(Set#Union(a, b), b) == a);

// Intersection of two sets
function Set#Intersection<T>(Set T, Set T): Set T;
axiom (forall<T> a: Set T, b: Set T, o: T :: { Set#Intersection(a,b)[o] }
  Set#Intersection(a,b)[o] <==> a[o] && b[o]);
axiom (forall<T> a, b: Set T :: { Set#Union(Set#Union(a, b), b) }
  Set#Union(Set#Union(a, b), b) == Set#Union(a, b));
axiom (forall<T> a, b: Set T :: { Set#Union(a, Set#Union(a, b)) }
  Set#Union(a, Set#Union(a, b)) == Set#Union(a, b));
axiom (forall<T> a, b: Set T :: { Set#Intersection(Set#Intersection(a, b), b) }
  Set#Intersection(Set#Intersection(a, b), b) == Set#Intersection(a, b));
axiom (forall<T> a, b: Set T :: { Set#Intersection(a, Set#Intersection(a, b)) }
  Set#Intersection(a, Set#Intersection(a, b)) == Set#Intersection(a, b));
axiom (forall<T> a, b: Set T :: { Set#Card(Set#Union(a, b)) }{ Set#Card(Set#Intersection(a, b)) }
  Set#Card(Set#Union(a, b)) + Set#Card(Set#Intersection(a, b)) == Set#Card(a) + Set#Card(b));

// Set a with all elements from b removed
function Set#Difference<T>(Set T, Set T): Set T;
axiom (forall<T> a: Set T, b: Set T, o: T :: { Set#Difference(a,b)[o] }
  Set#Difference(a,b)[o] <==> a[o] && !b[o]);
axiom (forall<T> a, b: Set T, y: T :: { Set#Difference(a, b), b[y] }
  b[y] ==> !Set#Difference(a, b)[y] );
axiom (forall<T> a, b: Set T ::
  { Set#Card(Set#Difference(a, b)) }
  Set#Card(Set#Difference(a, b)) + Set#Card(Set#Difference(b, a))
  + Set#Card(Set#Intersection(a, b))
    == Set#Card(Set#Union(a, b)) &&
  Set#Card(Set#Difference(a, b)) == Set#Card(a) - Set#Card(Set#Intersection(a, b)));
axiom (forall<T> a: Set T :: { Set#Difference(a,Set#Empty()) }
  Set#Equal(Set#Difference(a,Set#Empty()), a));

// Symmetric difference of two sets
function Set#SymDifference<T>(a: Set T, b: Set T): Set T
{ Set#Union(Set#Difference(a, b), Set#Difference(b, a)) }


function Set#Min<T>(Set T): T;
axiom (forall s: Set int :: { Set#Min(s) }
  !Set#IsEmpty(s) ==> s[Set#Min(s)] && (forall x: int :: s[x] ==> x >= Set#Min(s)));

function Set#Max<T>(Set T): T;
axiom (forall s: Set int :: { Set#Max(s) }
  !Set#IsEmpty(s) ==> s[Set#Max(s)] && (forall x: int :: s[x] ==> x <= Set#Max(s)));

function Set#NonNull(s: Set ref): bool
{ (forall x: ref :: { s[x] } s[x] ==> x != Void) }

// Type property
function {: inline } Set#ItemsType(heap: HeapType, s: Set ref, t: Type): bool
{ (forall o: ref :: { s[o] } s[o] ==> detachable(heap, o, t)) }

// Integer intervals
type Interval = Set int;

// Interval [l, u]
function Interval#FromRange(int, int): Interval;
axiom (forall l, u: int :: { Set#Card(Interval#FromRange(l, u)) }
  (u < l ==> Set#Card(Interval#FromRange(l, u)) == 0) &&
  (l <= u ==> Set#Card(Interval#FromRange(l, u)) == u - l + 1));
axiom (forall l, u, x: int :: { Interval#FromRange(l, u)[x] }
  Interval#FromRange(l, u)[x] <==> l <= x && x <= u);

// File: /home/caf/tools/eve_96960/library/base/mml/sequence.bpl

// Finite sequences.
// (Originally from Dafny Prelude: Copyright (c) Microsoft)

// Sequence type
type Seq T;

// Sequence length
function Seq#Length<T>(Seq T): int;
axiom (forall<T> s: Seq T :: { Seq#Length(s) } 0 <= Seq#Length(s));

// Empty sequence
function Seq#Empty<T>(): Seq T;
axiom (forall<T> :: Seq#Length(Seq#Empty(): Seq T) == 0);
axiom (forall<T> s: Seq T :: { Seq#Length(s) } Seq#Length(s) == 0 ==> s == Seq#Empty());
axiom (forall<T> f: Field (Seq T) :: { Default(f) } Default(f) == Seq#Empty() : Seq T);

// Singleton sequence
function Seq#Singleton<T>(T): Seq T;
axiom (forall<T> t: T :: { Seq#Length(Seq#Singleton(t)) } Seq#Length(Seq#Singleton(t)) == 1);

// Constant sequence
function Seq#Constant<T>(T, int): Seq T;
axiom (forall<T> t: T, n: int :: { Seq#Length(Seq#Constant(t, n)) }
  n >= 0 ==> Seq#Length(Seq#Constant(t, n)) == n);
axiom (forall<T> t: T, n: int, i: int :: { Seq#Item(Seq#Constant(t, n), i) }
  1 <= i && i <= n ==> Seq#Item(Seq#Constant(t, n), i) == t);


// Does a sequence contain a given element?
function Seq#Has<T>(s: Seq T, x: T): bool;
axiom (forall<T> s: Seq T, x: T :: { Seq#Has(s,x) }
  Seq#Has(s,x) <==>
    (exists i: int :: { Seq#Item(s,i) } 1 <= i && i <= Seq#Length(s) && Seq#Item(s,i) == x));
// axiom (forall<T> s: Seq T, i: int :: { Seq#Item(s, i) }
  // 1 <= i && i <= Seq#Length(s) ==>
    // Seq#Has(s, Seq#Item(s, i)));
axiom (forall<T> x: T ::
  { Seq#Has(Seq#Empty(), x) }
  !Seq#Has(Seq#Empty(), x));
axiom (forall<T> x, y: T ::
  { Seq#Has(Seq#Singleton(y), x) }
  Seq#Has(Seq#Singleton(y), x) <==> x == y);
axiom (forall<T> s0: Seq T, s1: Seq T, x: T ::
  { Seq#Has(Seq#Concat(s0, s1), x) }
  Seq#Has(Seq#Concat(s0, s1), x) <==>
    Seq#Has(s0, x) || Seq#Has(s1, x));
axiom (forall<T> s: Seq T, v: T, x: T ::
  { Seq#Has(Seq#Extended(s, v), x) }
    Seq#Has(Seq#Extended(s, v), x) <==> (v == x || Seq#Has(s, x)));
axiom (forall<T> s: Seq T, v: T, x: T ::
  { Seq#Has(Seq#Prepended(s, v), x) }
    Seq#Has(Seq#Prepended(s, v), x) <==> (v == x || Seq#Has(s, x)));
axiom (forall<T> s: Seq T, n: int, x: T ::
  { Seq#Has(Seq#Take(s, n), x) }
  Seq#Has(Seq#Take(s, n), x) <==>
    (exists i: int :: { Seq#Item(s, i) }
      1 <= i && i <= n && i <= Seq#Length(s) && Seq#Item(s, i) == x));
axiom (forall<T> s: Seq T, n: int, x: T ::
  { Seq#Has(Seq#Drop(s, n), x) }
  Seq#Has(Seq#Drop(s, n), x) <==>
    (exists i: int :: { Seq#Item(s, i) }
      0 <= n && n + 1 <= i && i <= Seq#Length(s) && Seq#Item(s, i) == x));
axiom (forall<T> s: Seq T, n: int, x: T ::
  { Seq#Has(Seq#RemovedAt(s, n), x) }
  Seq#Has(Seq#RemovedAt(s, n), x) <==>
    (exists i: int :: { Seq#Item(s, i) }
      1 <= n && n <= Seq#Length(s) && n != i && Seq#Item(s, i) == x));

// Is a sequence empty?
function {: inline } Seq#IsEmpty<T>(a: Seq T): bool
{ Seq#Equal(a, Seq#Empty()) }

function Seq#IsConstant<T>(s: Seq T, x: T): bool
{ (forall i: int :: { Seq#Item(s, i) } 1 <= i && i <= Seq#Length(s) ==> Seq#Item(s, i) == x) }

// Element at a given index
function Seq#Item<T>(Seq T, int): T;
axiom (forall<T> t: T :: { Seq#Item(Seq#Singleton(t), 1) } Seq#Item(Seq#Singleton(t), 1) == t);
// axiom (forall<T> s0: Seq T, s1: Seq T, n: int :: { Seq#Item(Seq#Concat(s0,s1), n) }
  // (n <= Seq#Length(s0) ==> Seq#Item(Seq#Concat(s0,s1), n) == Seq#Item(s0, n)) &&
  // (Seq#Length(s0) < n ==> Seq#Item(Seq#Concat(s0,s1), n) == Seq#Item(s1, n - Seq#Length(s0))));
axiom (forall<T> s0: Seq T, s1: Seq T, n: int :: { Seq#Item(Seq#Concat(s0,s1), n) }
  Seq#Item(Seq#Concat(s0,s1), n) == if n <= Seq#Length(s0) then Seq#Item(s0, n) else Seq#Item(s1, n - Seq#Length(s0)));

// Set of indexes
function Seq#Domain<T>(q: Seq T): Set int
{ Interval#FromRange(1, Seq#Length(q)) }

// Set of values
function Seq#Range<T>(Seq T): Set T;
axiom (forall<T> q: Seq T, o: T :: { Seq#Range(q)[o] } Seq#Has(q, o) <==> Seq#Range(q)[o]);
axiom (forall<T> s: Seq T :: { Seq#Range(s) }
  (forall i: int :: 1 <= i && i <= Seq#Length(s) ==> Seq#Range(s)[Seq#Item(s, i)]));
// axiom (forall<T> s: Seq T, i: int :: { Seq#Range(s), Seq#Item(s, i) }
  // 1 <= i && i <= Seq#Length(s) ==> Seq#Range(s)[Seq#Item(s, i)]);


// How many times does x occur in a?
function Seq#Occurrences<T>(Seq T, T): int;
axiom (forall<T> x: T :: {Seq#Occurrences(Seq#Empty(), x)} Seq#Occurrences(Seq#Empty(), x) == 0);
axiom (forall<T> a: Seq T, x: T:: {Seq#Occurrences(Seq#Extended(a, x), x)}
  Seq#Occurrences(Seq#Extended(a, x), x) == Seq#Occurrences(a, x) + 1);
axiom (forall<T> a: Seq T, x: T, y: T :: {Seq#Occurrences(Seq#Extended(a, y), x)}
  x != y ==> Seq#Occurrences(Seq#Extended(a, y), x) == Seq#Occurrences(a, x));
// axiom (forall<T> x: T:: {Seq#Occurrences(Seq#Singleton(x), x)}
  // Seq#Occurrences(Seq#Singleton(x), x) == 1);
// axiom (forall<T> x: T, y: T :: {Seq#Occurrences(Seq#Singleton(x), y)}
  // x != y ==> Seq#Occurrences(Seq#Singleton(x), y) == 0);
 // axiom (forall<T> a: Seq T, x: T :: {Seq#Occurrences(a, x)}
  // !Seq#Has(a, x) ==> Seq#Occurrences(a, x) == 0);

function Seq#IndexOf<T>(Seq T, T): int;
axiom (forall<T> s: Seq T, x: T :: { Seq#IndexOf(s,x) }
  Seq#Has(s,x) ==> 1 <= Seq#IndexOf(s,x) && Seq#IndexOf(s,x) <= Seq#Length(s) && Seq#Item(s, Seq#IndexOf(s,x)) == x);
axiom (forall<T> s: Seq T, x: T :: { Seq#IndexOf(s,x) }
  !Seq#Has(s,x) ==> Seq#IndexOf(s,x) < 1 || Seq#Length(s) < Seq#IndexOf(s,x));

// Are two sequences equal?
function Seq#Equal<T>(Seq T, Seq T): bool;
axiom (forall<T> s0: Seq T, s1: Seq T :: { Seq#Equal(s0,s1) }
  Seq#Equal(s0,s1) <==>
    Seq#Length(s0) == Seq#Length(s1) &&
    (forall j: int :: { Seq#Item(s0,j) } { Seq#Item(s1,j) }
        1 <= j && j <= Seq#Length(s0) ==> Seq#Item(s0,j) == Seq#Item(s1,j)));
axiom (forall<T> a: Seq T, b: Seq T :: { Seq#Equal(a,b) }  // extensionality axiom for sequences
  Seq#Equal(a,b) ==> a == b);

// Is q0 a prefix of q1?
function {: inline } Seq#Prefix<T>(q0: Seq T, q1: Seq T): bool
{ Seq#Equal(q0, Seq#Take(q1, Seq#Length(q0))) }

// Is |q0| <= |q1|?
function {: inline } Seq#LessEqual<T>(q0: Seq T, q1: Seq T): bool
{ Seq#Length(q0) <= Seq#Length(q1) }

// Prefix of length how_many
function Seq#Take<T>(s: Seq T, howMany: int): Seq T;
axiom (forall<T> s: Seq T, n: int :: { Seq#Length(Seq#Take(s,n)) }
  // (n < 0 ==> Seq#Length(Seq#Take(s,n)) == 0) &&
  // (n <= Seq#Length(s) ==> Seq#Length(Seq#Take(s,n)) == n) &&
  // (Seq#Length(s) < n ==> Seq#Length(Seq#Take(s,n)) == Seq#Length(s)));
  0 <= n ==>
    (n <= Seq#Length(s) ==> Seq#Length(Seq#Take(s,n)) == n) &&
    (Seq#Length(s) < n ==> Seq#Length(Seq#Take(s,n)) == Seq#Length(s)));
axiom (forall<T> s: Seq T, n: int, j: int :: { Seq#Item(Seq#Take(s,n), j) } {:weight 25}
  1 <= j && j <= n && j <= Seq#Length(s) ==>
    Seq#Item(Seq#Take(s,n), j) == Seq#Item(s, j));
// axiom (forall<T> s: Seq T, n: int :: {Seq#Take(s,n)}
  // (n < 0 ==> Seq#Take(s,n) == Seq#Empty() : Seq T) &&
  // (n >= Seq#Length(s) ==> Seq#Take(s,n) == s));

// Sequence without its prefix of length howMany
function Seq#Drop<T>(s: Seq T, howMany: int): Seq T;
axiom (forall<T> s: Seq T, n: int :: { Seq#Length(Seq#Drop(s,n)) }
  // (n < 0 ==> Seq#Length(Seq#Drop(s,n)) == Seq#Length(s)) &&
  // (n <= Seq#Length(s) ==> Seq#Length(Seq#Drop(s,n)) == Seq#Length(s) - n) &&
  // (Seq#Length(s) < n ==> Seq#Length(Seq#Drop(s,n)) == 0));
  0 <= n ==>
    (n <= Seq#Length(s) ==> Seq#Length(Seq#Drop(s,n)) == Seq#Length(s) - n) &&
    (Seq#Length(s) < n ==> Seq#Length(Seq#Drop(s,n)) == 0));
axiom (forall<T> s: Seq T, n: int, j: int :: { Seq#Item(Seq#Drop(s,n), j) } {:weight 25}
  0 <= n && 1 <= j && j <= Seq#Length(s)-n ==>
    Seq#Item(Seq#Drop(s,n), j) == Seq#Item(s, j+n));
// axiom (forall<T> s: Seq T, n: int :: {Seq#Drop(s,n)}
  // (n < 0 ==> Seq#Drop(s,n) == s) &&
  // (n >= Seq#Length(s) ==> Seq#Drop(s,n) == Seq#Empty() : Seq T));

// First element
function {: inline } Seq#First<T>(q: Seq T): T
{ Seq#Item(q, 1) }

// Last element
function {: inline } Seq#Last<T>(q: Seq T): T
{ Seq#Item(q, Seq#Length(q)) }

// Sequence with the first element removed
function {: inline } Seq#ButFirst<T>(q: Seq T): Seq T
{ Seq#Drop(q, 1) }

// Sequence with the last element removed
function {: inline } Seq#ButLast<T>(q: Seq T): Seq T
{ Seq#Take(q, Seq#Length(q) - 1) }

// Prefix until upper
function Seq#Front<T>(q: Seq T, upper: int): Seq T
// { Seq#Take(q, upper) }
{ if 0 <= upper then Seq#Take(q, upper) else Seq#Empty() : Seq T }
axiom (forall<T> q: Seq T :: { Seq#Front(q, Seq#Length(q)) } Seq#Front(q, Seq#Length(q)) == q);

// Suffix from lower
function Seq#Tail<T>(q: Seq T, lower: int): Seq T
// { Seq#Drop(q, lower - 1) }
{ if 1 <= lower then Seq#Drop(q, lower - 1) else q }
axiom (forall<T> q: Seq T :: { Seq#Tail(q, 1) } Seq#Tail(q, 1) == q);

// Subsequence from lower to upper
function Seq#Interval<T>(q: Seq T, lower: int, upper: int): Seq T
{ Seq#Tail(Seq#Front(q, upper), lower) }

// Sequence with element at position i removed
// function {: inline } Seq#RemovedAt<T>(q: Seq T, i: int): Seq T
// { Seq#Concat(Seq#Take(q, i - 1), Seq#Drop(q, i)) }
function Seq#RemovedAt<T>(q: Seq T, i: int): Seq T;
axiom (forall<T> q: Seq T, i: int :: { Seq#Length(Seq#RemovedAt(q, i)) }
	Seq#Length(Seq#RemovedAt(q, i)) == Seq#Length(q) - 1);
axiom (forall<T> q: Seq T, i: int, j: int :: { Seq#Item(Seq#RemovedAt(q, i), j) }
	(j < i ==> Seq#Item(Seq#RemovedAt(q, i), j) == Seq#Item(q, j)) &&
	(i <= j ==> Seq#Item(Seq#RemovedAt(q, i), j) == Seq#Item(q, j + 1)));

// Sequence extended with x at the end
function Seq#Extended<T>(s: Seq T, val: T): Seq T;
axiom (forall<T> s: Seq T, v: T :: { Seq#Length(Seq#Extended(s,v)) }
  Seq#Length(Seq#Extended(s,v)) == 1 + Seq#Length(s));
axiom (forall<T> s: Seq T, i: int, v: T :: { Seq#Item(Seq#Extended(s,v), i) }
  (i == Seq#Length(s) + 1 ==> Seq#Item(Seq#Extended(s,v), i) == v) &&
  (i <= Seq#Length(s) ==> Seq#Item(Seq#Extended(s,v), i) == Seq#Item(s, i)));

// Sequence with x inserted at position i
function {: inline } Seq#ExtendedAt<T>(s: Seq T, i: int, val: T): Seq T
{
  Seq#Concat (Seq#Extended(Seq#Take(s, i - 1), val), Seq#Drop(s, i - 1))
}
axiom (forall<T> s: Seq T, i: int, val: T :: { Seq#Length(Seq#ExtendedAt(s, i, val)) }
	Seq#Length(Seq#ExtendedAt(s, i, val)) == Seq#Length(s) + 1);

// Sequence prepended with x at the beginning
function Seq#Prepended<T>(s: Seq T, val: T): Seq T;
// {
  // Seq#Concat (Seq#Singleton(val), s)
// }
axiom (forall<T> s: Seq T, v: T :: { Seq#Length(Seq#Prepended(s, v)) }
	Seq#Length(Seq#Prepended(s, v)) == Seq#Length(s) + 1);
axiom (forall<T> s: Seq T, v: T, i: int :: { Seq#Item(Seq#Prepended(s, v), i) }
  (2 <= i && i <= Seq#Length(s) + 1 ==> Seq#Item(Seq#Prepended(s, v), i) == Seq#Item(s, i - 1)) &&
  (i == 1 ==> Seq#Item(Seq#Prepended(s, v), 1) == v));

// Concatenation of two sequences
function Seq#Concat<T>(Seq T, Seq T): Seq T;
axiom (forall<T> s0: Seq T, s1: Seq T :: { Seq#Length(Seq#Concat(s0,s1)) }
  Seq#Length(Seq#Concat(s0,s1)) == Seq#Length(s0) + Seq#Length(s1));

// Sequence with x at position i.
function Seq#Update<T>(Seq T, int, T): Seq T;
axiom (forall<T> s: Seq T, i: int, v: T :: { Seq#Length(Seq#Update(s,i,v)) }
  1 <= i && i <= Seq#Length(s) ==> Seq#Length(Seq#Update(s,i,v)) == Seq#Length(s));
axiom (forall<T> s: Seq T, i: int, v: T, n: int :: { Seq#Item(Seq#Update(s,i,v),n) }
  1 <= n && n <= Seq#Length(s) ==>
    (i == n ==> Seq#Item(Seq#Update(s,i,v),n) == v) &&
    (i != n ==> Seq#Item(Seq#Update(s,i,v),n) == Seq#Item(s,n)));

// Sequence converted to a bag
function Seq#ToBag<T>(Seq T): Bag T;
axiom (forall<T> s: Seq T :: { Seq#ToBag(s) } Bag#IsValid(Seq#ToBag(s)));
// building axiom
axiom (forall<T> s: Seq T, v: T ::
  { Seq#ToBag(Seq#Extended(s, v)) }
    Seq#ToBag(Seq#Extended(s, v)) == Bag#Extended(Seq#ToBag(s), v)
  );
axiom (forall<T> :: Seq#ToBag(Seq#Empty(): Seq T) == Bag#Empty(): Bag T);
axiom (forall<T> s: Seq T :: { Bag#Card(Seq#ToBag(s)) }
  Bag#Card(Seq#ToBag(s)) == Seq#Length(s));

// concatenation axiom
axiom (forall<T> a: Seq T, b: Seq T, x: T ::
  { Seq#ToBag(Seq#Concat(a, b))[x] }
    Seq#ToBag(Seq#Concat(a, b))[x] == Seq#ToBag(a)[x] + Seq#ToBag(b)[x] );

// update axiom
axiom (forall<T> s: Seq T, i: int, v: T, x: T ::
  { Seq#ToBag(Seq#Update(s, i, v))[x] }
    1 <= i && i <= Seq#Length(s) ==>
    Seq#ToBag(Seq#Update(s, i, v))[x] ==
      Bag#Extended(Bag#Difference(Seq#ToBag(s), Bag#Singleton(Seq#Item(s,i))), v)[x] );
  // i.e. MS(Update(s, i, v)) == MS(s) - {{s[i]}} + {{v}}
axiom (forall<T> s: Seq T, x: T :: { Seq#ToBag(s)[x] } Seq#Has(s, x) <==> 0 < Seq#ToBag(s)[x]);
axiom (forall<T> s: Seq T, x: T :: { Seq#ToBag(s)[x] } Seq#ToBag(s)[x] == Seq#Occurrences(s, x));

// removed axiom
axiom (forall<T> s: Seq T, i: int :: { Seq#ToBag(Seq#RemovedAt(s, i)) }
  1 <= i && i <= Seq#Length(s) ==> Seq#ToBag(Seq#RemovedAt(s, i)) == Bag#Difference(Seq#ToBag(s), Bag#Singleton(Seq#Item(s,i))));
// prepend axiom
axiom (forall<T> s: Seq T, v: T :: { Seq#ToBag(Seq#Prepended(s, v)) }
  Seq#ToBag(Seq#Prepended(s, v)) == Bag#Extended(Seq#ToBag(s), v));

// Sequence converted to map
function Seq#ToMap<T>(Seq T): Map int T;
axiom (forall<T> s: Seq T :: { Map#Equal(Seq#ToMap(s), Map#Empty()) }
  Map#Equal(Seq#ToMap(s), Map#Empty()) <==> Seq#Equal (s, Seq#Empty() : Seq T));
axiom (forall<T> s: Seq T :: { Map#Domain(Seq#ToMap(s)) }
  Map#Domain(Seq#ToMap(s)) == Seq#Domain(s));
axiom (forall<T> s: Seq T :: { Map#Card(Seq#ToMap(s)) }
  Map#Card(Seq#ToMap(s)) == Seq#Length(s));
axiom (forall<T> s: Seq T, i: int :: { Map#Item(Seq#ToMap(s), i) }
  1 <= i && i <= Seq#Length(s) ==> Map#Item(Seq#ToMap(s), i) == Seq#Item(s, i));

axiom (forall<T> s: Seq T :: { Map#ToBag(Seq#ToMap(s)) }
  Bag#Equal(Map#ToBag(Seq#ToMap(s)), Seq#ToBag(s)));


// Additional axioms about common things

// axiom (forall<T> s, t: Seq T ::
  // { Seq#Concat(s, t) }
  // Seq#Take(Seq#Concat(s, t), Seq#Length(s)) == s &&
  // Seq#Drop(Seq#Concat(s, t), Seq#Length(s)) == t);


// Commutability of Take and Drop with Update.
axiom (forall<T> s: Seq T, i: int, v: T, n: int ::
  { Seq#Take(Seq#Update(s, i, v), n) }
    1 <= i && i <= n && n <= Seq#Length(s) ==> Seq#Take(Seq#Update(s, i, v), n) == Seq#Update(Seq#Take(s, n), i, v) );
axiom (forall<T> s: Seq T, i: int, v: T, n: int ::
  { Seq#Take(Seq#Update(s, i, v), n) }
    n < i && i <= Seq#Length(s) ==> Seq#Take(Seq#Update(s, i, v), n) == Seq#Take(s, n));
axiom (forall<T> s: Seq T, i: int, v: T, n: int ::
  { Seq#Drop(Seq#Update(s, i, v), n) }
    0 <= n && n + 1 <= i && i <= Seq#Length(s) ==> Seq#Drop(Seq#Update(s, i, v), n) == Seq#Update(Seq#Drop(s, n), i-n, v) );
axiom (forall<T> s: Seq T, i: int, v: T, n: int ::
  { Seq#Drop(Seq#Update(s, i, v), n) }
    1 <= i && i <= n && n < Seq#Length(s) ==> Seq#Drop(Seq#Update(s, i, v), n) == Seq#Drop(s, n));
// drop commutes with build.
axiom (forall<T> s: Seq T, v: T, n: int ::
  { Seq#Drop(Seq#Extended(s, v), n) }
    0 <= n && n <= Seq#Length(s) ==> Seq#Drop(Seq#Extended(s, v), n) == Seq#Extended(Seq#Drop(s, n), v) );

axiom (forall<T> :: Seq#Take(Seq#Empty() : Seq T, 0) == Seq#Empty() : Seq T);  // [][..0] == []
axiom (forall<T> :: Seq#Drop(Seq#Empty() : Seq T, 0) == Seq#Empty() : Seq T);  // [][0..] == []

// 2 x Take and drop
// axiom (forall<T> s: Seq T, n: int, m: int :: { Seq#Take(Seq#Take(s, n), m) }
	// (n <= m ==> Seq#Equal(Seq#Take(Seq#Take(s, n), m), Seq#Take(s, n))) &&
	// (n >= m ==> Seq#Equal(Seq#Take(Seq#Take(s, n), m), Seq#Take(s, m))));
// axiom (forall<T> s: Seq T, n: int, m: int :: { Seq#Drop(Seq#Drop(s, n), m) }
	// Seq#Equal(Seq#Drop(Seq#Drop(s, n), m), Seq#Drop(s, n + m)));

function Seq#NonNull(s: Seq ref): bool
{ (forall i: int :: { Seq#Item(s, i) } 1 <= i && i <= Seq#Length(s) ==> Seq#Item(s, i) != Void) }

function Seq#NoDuplicates<T>(s: Seq T): bool
{ (forall i, j: int :: { Seq#Item(s, i), Seq#Item(s, j) } 1 <= i && i < j && j <= Seq#Length(s) ==> Seq#Item(s, i) != Seq#Item(s, j)) }
// { (forall i, j: int :: 1 <= i && i <= Seq#Length(s) && 1 <= j && j <= ) }

// Type property
function {: inline } Seq#ItemsType(heap: HeapType, s: Seq ref, t: Type): bool
{ (forall i: int :: { Seq#Item(s, i) } 1 <= i && i <= Seq#Length(s) ==> detachable(heap, Seq#Item(s, i), t)) }

// function Seq#IsSorted<T>(s: Seq T) returns (bool);

//axiom (forall s: Seq int, i: int ::
//    1 <= i && i < Seq#Length(s) && Seq#IsSorted(s) ==> Seq#Item(s, i) <= Seq#Item(s, i+1));
// axiom (forall s: Seq int ::
  // { Seq#IsSorted(s) }
    // Seq#IsSorted(s) ==> (forall i, j: int :: 1 <= i && i <= Seq#Length(s) && i <= j && j <= Seq#Length(s) ==> Seq#Item(s, i) <= Seq#Item(s, j)));
// axiom (forall s: Seq int ::
  // { Seq#IsSorted(s) }
    // Seq#Length(s) <= 1 ==> Seq#IsSorted(s));
// axiom (forall s: Seq int, i: int ::
    // 1 <= i && i < Seq#Length(s) && Seq#IsSorted(Seq#Front(s, i)) && Seq#Item(s, i) <= Seq#Item(s, i+1) ==> Seq#IsSorted(Seq#Front(s, i+1)));

// axiom (forall s: Seq int ::
  // { Seq#Range(s) }
    // (forall i: int, j: int ::
		// 1 <= i && i < Seq#Length(s) && 1 <= j && j < Seq#Length(s) ==>
			// Seq#Range(Seq#Update(Seq#Update(s, i, Seq#Item(s, j)), j, Seq#Item(s, i))) == Seq#Range(s)));





// File: /home/caf/tools/eve_96960/library/base/mml/map.bpl

// Finite maps.
// (Originally from Dafny Prelude: Copyright (c) Microsoft)

// Map type
type Map U V;

// Map domain
function Map#Domain<U, V>(Map U V): Set U;

// Mapping from keys to values
function Map#Elements<U, V>(Map U V): [U]V;

// // Map constructed from domain and elements
// function Map#Glue<U, V>([U] bool, [U]V): Map U V;
// axiom (forall<U, V> a: [U] bool, b:[U]V ::
  // { Map#Domain(Map#Glue(a, b)) }
    // Map#Domain(Map#Glue(a, b)) == a);
// axiom (forall<U, V> a: [U] bool, b:[U]V ::
  // { Map#Elements(Map#Glue(a, b)) }
    // Map#Elements(Map#Glue(a, b)) == b);

// Map cardinality
function Map#Card<U, V>(Map U V): int;
axiom (forall<U, V> m: Map U V :: { Map#Card(m) } 0 <= Map#Card(m));
axiom (forall<U, V> m: Map U V :: { Map#Card(m), Map#Domain(m) } Map#Card(m) == Set#Card(Map#Domain(m)));

// Empty map
function Map#Empty<U, V>(): Map U V;
axiom (forall<U, V> u: U ::
  { Map#Domain(Map#Empty(): Map U V)[u] }
   !Map#Domain(Map#Empty(): Map U V)[u]);
axiom (forall<U, V> m: Map U V :: { Map#Card(m) } Map#Card(m) == 0 <==> m == Map#Empty());
axiom (forall<U, V> f: Field (Map U V) :: { Default(f) } Default(f) == Map#Empty() : Map U V);

// Singleton map
function {: inline } Map#Singleton<U, V>(k: U, x: V): Map U V
{ Map#Update(Map#Empty(), k, x) }

// Does the map contain value x?
function {: inline } Map#Has<U, V>(m: Map U V, x: V): bool
{ Map#Range(m)[x] }

// Is the map empty?
function {: inline } Map#IsEmpty<U, V>(m: Map U V): bool
{ Map#Equal(m, Map#Empty()) }

// Are all values in m equal to c?
function Map#IsConstant<U, V>(m: Map U V, c: V): bool
{ (forall k: U :: Map#Domain(m)[k] ==> Map#Elements(m)[k] == c) }

// Element at a given key
function {: inline } Map#Item<U, V>(m: Map U V, k: U): V
{ Map#Elements(m)[k] }

// Map Range
function {: inline } Map#Range<U, V>(m: Map U V): Set V
{ Map#Image(m, Map#Domain(m)) }

// Image of a set
function Map#Image<U, V>(m: Map U V, s: Set U): Set V;
axiom (forall<U, V> m: Map U V, s: Set U, x: V :: { Map#Image(m, s)[x] }
  Map#Image(m, s)[x] <==> (exists k: U :: s[k] && Map#Elements(m)[k] == x));
axiom (forall<U, V> m: Map U V, s: Set U, k: U :: { Map#Image(m, s)[Map#Elements(m)[k]] }
  s[k] ==> Map#Image(m, s)[Map#Elements(m)[k]]);

// Image of a sequence
function Map#SequenceImage<U, V>(m: Map U V, s: Seq U): Seq V;
axiom (forall<U, V> m: Map U V, s: Seq U :: { Seq#Length(Map#SequenceImage(m, s)) }
  Seq#Length(Map#SequenceImage(m, s)) == Seq#Length(s));
axiom (forall<U, V> m: Map U V, s: Seq U, i: int :: { Seq#Item(Map#SequenceImage(m, s), i) }
  Seq#Item(Map#SequenceImage(m, s), i) == Map#Elements(m)[Seq#Item(s, i)]);

// Bag of map values
function Map#ToBag<U, V>(m: Map U V): Bag V;
axiom (forall<U, V> m: Map U V :: { Map#ToBag(m) } Bag#IsValid(Map#ToBag(m)));
// axiom (forall<U, V> m: Map U V :: { Bag#Equal(Map#ToBag(m), Bag#Empty()) }
  // Bag#Equal(Map#ToBag(m), Bag#Empty() : Bag V) <==> Map#Equal (m, Map#Empty() : Map U V));
axiom (forall<U, V> :: Map#ToBag(Map#Empty() :  Map U V) == Bag#Empty() : Bag V);
axiom (forall<U, V> m: Map U V, x: V :: { Map#ToBag(m)[x] }
  Map#ToBag(m)[x] > 0 <==> Map#Range(m)[x]);
// update axiom
axiom (forall<U, V> m: Map U V, k: U, x: V :: { Map#ToBag(Map#Update(m, k, x)) }
  !Map#Domain(m)[k] ==> Map#ToBag(Map#Update(m, k, x)) == Bag#Extended(Map#ToBag(m), x));
axiom (forall<U, V> m: Map U V, k: U, x: V :: { Map#ToBag(Map#Update(m, k, x)) }
  Map#Domain(m)[k] ==> Map#ToBag(Map#Update(m, k, x)) == Bag#Extended(Bag#Removed(Map#ToBag(m), Map#Elements(m)[k]), x));
// removed axiom
axiom (forall<U, V> m: Map U V, k: U :: { Map#ToBag(Map#Removed(m, k)) }
  Map#Domain(m)[k] ==> Map#ToBag(Map#Removed(m, k)) == Bag#Removed(Map#ToBag(m), Map#Elements(m)[k]));
// cardinality axiom
axiom (forall<U, V> m: Map U V :: { Bag#Card(Map#ToBag(m)) }
  Bag#Card(Map#ToBag(m)) == Map#Card(m));
// disjoint union axiom
axiom (forall<U, V> a: Map U V, b: Map U V, x: V ::
  { Map#ToBag(Map#Override(a, b))[x] }
    Set#Disjoint(Map#Domain(a), Map#Domain(b)) ==> Map#ToBag(Map#Override(a, b))[x] == Map#ToBag(a)[x] + Map#ToBag(b)[x] );


// Equality
function Map#Equal<U, V>(Map U V, Map U V): bool;
axiom (forall<U, V> m: Map U V, m': Map U V::
  { Map#Equal(m, m') }
    Map#Equal(m, m') <==> (forall u : U :: Map#Domain(m)[u] == Map#Domain(m')[u]) &&
                          (forall u : U :: Map#Domain(m)[u] ==> Map#Elements(m)[u] == Map#Elements(m')[u]));
// extensionality
axiom (forall<U, V> m: Map U V, m': Map U V::
  { Map#Equal(m, m') }
    Map#Equal(m, m') ==> m == m');

// Dow two maps have disjoint domains?
function Map#Disjoint<U, V>(Map U V, Map U V): bool;
axiom (forall<U, V> m: Map U V, m': Map U V ::
  { Map#Disjoint(m, m') }
    Map#Disjoint(m, m') <==> (forall o: U :: {Map#Domain(m)[o]} {Map#Domain(m')[o]} !Map#Domain(m)[o] || !Map#Domain(m')[o]));

// Map with a key-value pair updated
function Map#Update<U, V>(Map U V, U, V): Map U V;
/*axiom (forall<U, V> m: Map U V, u: U, v: V ::
  { Map#Domain(Map#Update(m, u, v))[u] } { Map#Elements(Map#Update(m, u, v))[u] }
  Map#Domain(Map#Update(m, u, v))[u] && Map#Elements(Map#Update(m, u, v))[u] == v);*/
axiom (forall<U, V> m: Map U V, u: U, u': U, v: V ::
  { Map#Domain(Map#Update(m, u, v))[u'] } { Map#Elements(Map#Update(m, u, v))[u'] }
  (u' == u ==> Map#Domain(Map#Update(m, u, v))[u'] &&
               Map#Elements(Map#Update(m, u, v))[u'] == v) &&
  (u' != u ==> Map#Domain(Map#Update(m, u, v))[u'] == Map#Domain(m)[u'] &&
               Map#Elements(Map#Update(m, u, v))[u'] == Map#Elements(m)[u']));
axiom (forall<U, V> m: Map U V, u: U, v: V :: { Map#Card(Map#Update(m, u, v)) }
  Map#Domain(m)[u] ==> Map#Card(Map#Update(m, u, v)) == Map#Card(m));
axiom (forall<U, V> m: Map U V, u: U, v: V :: { Map#Card(Map#Update(m, u, v)) }
  !Map#Domain(m)[u] ==> Map#Card(Map#Update(m, u, v)) == Map#Card(m) + 1);

// Map with a key removed
function Map#Removed<U, V>(Map U V, U): Map U V;
axiom (forall<U, V> m: Map U V, k: U :: { Map#Domain(Map#Removed(m, k)) }
  Map#Domain(Map#Removed(m, k)) == Set#Removed(Map#Domain(m), k));
axiom (forall<U, V> m: Map U V, k: U, i: U :: { Map#Elements(Map#Removed(m, k))[i] }
  Map#Elements(Map#Removed(m, k))[i] == Map#Elements(m)[i]);
axiom (forall<U, V> m: Map U V, k: U :: { Map#Domain(m)[k], Map#Removed(m, k) }
  !Map#Domain(m)[k] ==> Map#Removed(m, k) == m);

// Map restricted to a subdomain
function Map#Restricted<U, V>(Map U V, Set U): Map U V;
axiom (forall<U, V> m: Map U V, s: Set U :: { Map#Domain(Map#Restricted(m, s)) }
  Map#Domain(Map#Restricted(m, s)) == Set#Intersection(Map#Domain(m), s));
axiom (forall<U, V> m: Map U V, s: Set U, i: U :: { Map#Elements(Map#Restricted(m, s))[i] }
  Map#Elements(Map#Restricted(m, s))[i] == Map#Elements(m)[i]);

// Map override (right-biased union)
function  Map#Override<U, V>(Map U V, Map U V): Map U V;
axiom (forall<U, V> a: Map U V, b: Map U V :: { Map#Domain(Map#Override(a, b)) }
  Map#Domain(Map#Override(a, b)) == Set#Union(Map#Domain(a), Map#Domain(b)));
axiom (forall<U, V> a: Map U V, b: Map U V, i: U :: { Map#Elements(Map#Override(a, b))[i] }
  Map#Elements(Map#Override(a, b))[i] == if Map#Domain(b)[i] then Map#Elements(b)[i] else Map#Elements(a)[i]);

// Inverse
function Map#Inverse<U, V>(Map U V): Rel V U;
axiom (forall<U, V> a: Map U V, u: U, v: V :: { Map#Inverse(a)[v, u] }
  Map#Inverse(a)[v, u] <==> Map#Domain(a)[u] && Map#Elements(a)[u] == v);
axiom (forall<U, V> a: Map U V :: { Rel#Card(Map#Inverse(a)) }
  Rel#Card(Map#Inverse(a)) == Map#Card(a));
axiom (forall<U, V> a: Map U V :: { Rel#Domain(Map#Inverse(a)) }
  Rel#Domain(Map#Inverse(a)) == Map#Range(a));
axiom (forall<U, V> a: Map U V :: { Rel#Range(Map#Inverse(a)) }
  Rel#Range(Map#Inverse(a)) == Map#Domain(a));

// Type properties

function {: inline } Map#DomainType<T>(heap: HeapType, m: Map ref T, t: Type): bool
{ (forall o: ref :: { Map#Domain(m)[o] } Map#Domain(m)[o] ==> detachable(heap, o, t)) }

function {: inline } Map#RangeType<T>(heap: HeapType, m: Map T ref, t: Type): bool
{ (forall i: T :: { Map#Domain(m)[i] } Map#Domain(m)[i] ==> detachable(heap, Map#Elements(m)[i], t)) }




// File: /home/caf/tools/eve_96960/library/base/mml/relation.bpl

// Finite relation.

// Relation type
type Rel U V = [U, V]bool;

// Domain
function Rel#Domain<U, V>(Rel U V): Set U;
axiom (forall<U, V> r: Rel U V, u: U :: { Rel#Domain(r)[u] }
  Rel#Domain(r)[u] <==> (exists v: V :: r[u, v]));

// Range
function Rel#Range<U, V>(Rel U V): Set V;
axiom (forall<U, V> r: Rel U V, v: V :: { Rel#Range(r)[v] }
  Rel#Range(r)[v] <==> (exists u: U :: r[u, v]));

// Conversion to set
function Rel#ToSet<U, V>(Rel U V): Set (Pair U V);
axiom (forall<U, V> r: Rel U V, u: U, v: V :: { r[u, v] }{ Rel#ToSet(r)[Pair#Make(u, v)] }
  r[u, v] <==> Rel#ToSet(r)[Pair#Make(u, v)]);

// Cardinality
function Rel#Card<U, V>(r: Rel U V): int
{ Set#Card(Rel#ToSet(r)) }
// axiom (forall<U, V> r: Rel U V :: { Rel#Card(r) } 0 <= Rel#Card(r));

// Empty relation
function Rel#Empty<U, V>(): Rel U V;
axiom (forall<U, V> u: U, v: V :: { Rel#Empty()[u, v] } !Rel#Empty()[u, v]);
// axiom (forall<U, V> r: Rel U V :: { Rel#Card(r) }
  // (Rel#Card(r) == 0 <==> r == Rel#Empty()) &&
  // (Rel#Card(r) != 0 ==> (exists u: U, v: V :: r[u, v])));
axiom (forall<U, V> r: Rel U V :: { Rel#Domain(r), Rel#Empty() }{ Set#IsEmpty(Rel#Domain(r)) }
  (Set#IsEmpty(Rel#Domain(r)) <==> r == Rel#Empty()));
axiom (forall<U, V> r: Rel U V :: { Rel#Range(r), Rel#Empty() }{ Set#IsEmpty(Rel#Range(r)) }
  (Set#IsEmpty(Rel#Range(r)) <==> r == Rel#Empty()));
axiom (forall<U, V> r: Rel U V :: { Rel#ToSet(r) }
  (Set#IsEmpty(Rel#ToSet(r)) <==> r == Rel#Empty()));
axiom (forall<U, V> f: Field (Rel U V) :: { Default(f) } Default(f) == Rel#Empty() : Rel U V);

// Singleton relation
function Rel#Singleton<U, V>(U, V): Rel U V;
// axiom (forall<U, V> u: U, v: V :: { Rel#Singleton(u, v) } Rel#Singleton(u, v)[u, v]);
axiom (forall<U, V> u: U, v: V, x: U, y: V :: { Rel#Singleton(u, v)[x, y] } Rel#Singleton(u, v)[x, y] <==> u == x && v == y);
// axiom (forall<U, V> u: U, v: V :: { Rel#Card(Rel#Singleton(u, v)) } Rel#Card(Rel#Singleton(u, v)) == 1);
// axiom (forall<U, V> u: U, v: V :: { Rel#Domain(Rel#Singleton(u, v)) }
  // Rel#Domain(Rel#Singleton(u, v)) == Set#Singleton(u));
// axiom (forall<U, V> u: U, v: V :: { Rel#Range(Rel#Singleton(u, v)) }
  // Rel#Range(Rel#Singleton(u, v)) == Set#Singleton(v));
axiom (forall<U, V> u: U, v: V :: { Rel#ToSet(Rel#Singleton(u, v)) }
  Rel#ToSet(Rel#Singleton(u, v)) == Set#Singleton(Pair#Make(u, v)));

// Is the relation empty?
function {: inline} Rel#IsEmpty<U, V>(r: Rel U V): bool
{ Rel#Equal(Rel#Empty(), r) }

// Image of a domain element
function Rel#ImageOf<U, V>(r: Rel U V, u: U): Set V;
axiom (forall<U, V> r: Rel U V, u: U, v: V :: { Rel#ImageOf(r, u)[v] }
  Rel#ImageOf(r, u)[v] <==> r[u, v]);
axiom (forall<U, V> r: Rel U V, u: U :: { Rel#ImageOf(r, u) }
  Set#Subset(Rel#ImageOf(r, u), Rel#Range(r)));


// Image of a set
function Rel#Image<U, V>(r: Rel U V, s: Set U): Set V;
axiom (forall<U, V> r: Rel U V, s: Set U, v: V :: { Rel#Image(r, s)[v] }
  Rel#Image(r, s)[v] <==> (exists u: U :: s[u] && r[u, v]));
axiom (forall<U, V> r: Rel U V, s: Set U :: { Rel#Image(r, s) }
  Set#Subset(Rel#Image(r, s), Rel#Range(r)));

// Are two relation equal?
function Rel#Equal<U, V>(Rel U V, Rel U V): bool;
axiom(forall<U, V> a: Rel U V, b: Rel U V :: { Rel#Equal(a, b) }
  Rel#Equal(a, b) <==> (forall u: U, v: V :: {a[u, v]} {b[u, v]} a[u, v] <==> b[u, v]));
axiom(forall<U, V> a: Rel U V, b: Rel U V :: { Rel#Equal(a, b), Rel#ToSet(a), Rel#ToSet(b) }
  Rel#Equal(a, b) <==> Set#Equal(Rel#ToSet(a), Rel#ToSet(b)));
axiom(forall<U, V> a: Rel U V, b: Rel U V :: { Rel#Equal(a, b) }  // extensionality axiom for relation
  Rel#Equal(a, b) ==> a == b);

// Relation extended with one element
function Rel#Extended<U, V>(Rel U V, U, V): Rel U V;
axiom (forall<U, V> a: Rel U V, u: U, v: V, x: U, y: V :: { Rel#Extended(a, u, v)[x, y] }
  Rel#Extended(a, u, v)[x, y] <==> (u == x && v == y) || a[x, y]);
// axiom (forall<U, V> a: Rel U V, u: U, v: V :: { Rel#Extended(a, u, v) }
  // Rel#Extended(a, u, v)[u, v]);
// axiom (forall<U, V> a: Rel U V, u: U, v: V, x: U, y: V :: { Rel#Extended(a, u, v), a[x, y] }
  // a[x, y] ==> Rel#Extended(a, u, v)[x, y]);
// axiom (forall<U, V> a: Rel U V, u: U, v: V :: { Rel#Card(Rel#Extended(a, u, v)) }
  // a[u, v] ==> Rel#Card(Rel#Extended(a, u, v)) == Rel#Card(a));
// axiom (forall<U, V> a: Rel U V, u: U, v: V :: { Rel#Card(Rel#Extended(a, u, v)) }
  // !a[u, v] ==> Rel#Card(Rel#Extended(a, u, v)) == Rel#Card(a) + 1);
// axiom (forall<U, V> a: Rel U V, u: U, v: V :: { Rel#Domain(Rel#Extended(a, u, v)) }
  // Rel#Domain(Rel#Extended(a, u, v)) == Set#Extended(Rel#Domain(a), u));
// axiom (forall<U, V> a: Rel U V, u: U, v: V :: { Rel#Range(Rel#Extended(a, u, v)) }
  // Rel#Range(Rel#Extended(a, u, v)) == Set#Extended(Rel#Range(a), v));
axiom (forall<U, V> a: Rel U V, u: U, v: V :: { Rel#ToSet(Rel#Extended(a, u, v)) }
  Rel#ToSet(Rel#Extended(a, u, v)) == Set#Extended(Rel#ToSet(a), Pair#Make(u, v)));


// Relation with one element removed
function Rel#Removed<U, V>(Rel U V, U, V): Rel U V;
axiom (forall<U, V> a: Rel U V, u: U, v: V, x: U, y: V :: { Rel#Removed(a, u, v)[x, y] }
  Rel#Removed(a, u, v)[x, y] <==> (u != x || v != y) && a[x, y]);
// axiom (forall<U, V> a: Rel U V, u: U, v: V  :: { Rel#Removed(a, u, v) }
  // !Rel#Removed(a, u, v)[u, v]);
// axiom (forall<U, V> a: Rel U V, u: U, v: V, x: U, y: V :: { Rel#Removed(a, u, v), a[x, y] }
  // Rel#Removed(a, u, v)[x, y] ==> a[x, y]);
// axiom (forall<U, V> a: Rel U V, u: U, v: V  :: { Rel#Card(Rel#Removed(a, u, v)) }
  // a[u, v] ==> Rel#Card(Rel#Removed(a, u, v)) == Rel#Card(a) - 1);
// axiom (forall<U, V> a: Rel U V, u: U, v: V  :: { Rel#Card(Rel#Removed(a, u, v)) }
  // !a[u, v] ==> Rel#Card(Rel#Removed(a, u, v)) == Rel#Card(a));
axiom (forall<U, V> a: Rel U V, u: U, v: V :: { Rel#ToSet(Rel#Removed(a, u, v)) }
  Rel#ToSet(Rel#Removed(a, u, v)) == Set#Removed(Rel#ToSet(a), Pair#Make(u, v)));

// Restriction on a subdomain
function Rel#Restricted<U, V>(Rel U V, Set U): Rel U V;
axiom (forall<U, V> a: Rel U V, s: Set U, x: U, y: V :: { Rel#Restricted(a, s)[x, y] }
  Rel#Restricted(a, s)[x, y] <==> a[x, y] && s[x]);
axiom (forall<U, V> a: Rel U V, s: Set U :: { Rel#Domain(Rel#Restricted(a, s)) }
  Rel#Domain(Rel#Restricted(a, s)) == Set#Intersection(Rel#Domain(a), s));

// Inverse
function Rel#Inverse<U, V>(Rel U V): Rel V U;
axiom (forall<U, V> a: Rel U V, x: U, y: V :: { Rel#Inverse(a)[y, x] }
  Rel#Inverse(a)[y, x] <==> a[x, y]);
axiom (forall<U, V> a: Rel U V :: { Rel#Card(Rel#Inverse(a)) }
  Rel#Card(Rel#Inverse(a)) == Rel#Card(a));
axiom (forall<U, V> a: Rel U V :: { Rel#Domain(Rel#Inverse(a)) }
  Rel#Domain(Rel#Inverse(a)) == Rel#Range(a));
axiom (forall<U, V> a: Rel U V :: { Rel#Range(Rel#Inverse(a)) }
  Rel#Range(Rel#Inverse(a)) == Rel#Domain(a));

// Union of two relations
function Rel#Union<U, V>(Rel U V, Rel U V): Rel U V;
// axiom (forall<U, V> a: Rel U V, b: Rel U V, u: U, v: V :: { Rel#Union(a, b)[u, v] }
  // Rel#Union(a, b)[u, v] <==> a[u, v] || b[u, v]);
// axiom (forall<U, V> a, b: Rel U V, u: U, v: V :: { Rel#Union(a, b), a[u, v] }
  // a[u, v] ==> Rel#Union(a, b)[u, v]);
// axiom (forall<U, V> a, b: Rel U V, u: U, v: V :: { Rel#Union(a, b), b[u, v] }
  // b[u, v] ==> Rel#Union(a, b)[u, v]);
// // axiom (forall<U, V> a, b: Rel U V :: { Rel#Union(a, b) }
  // // Rel#Disjoint(a, b) ==>
    // // Rel#Difference(Rel#Union(a, b), a) == b &&
    // // Rel#Difference(Rel#Union(a, b), b) == a);
axiom (forall<U, V> a, b: Rel U V :: { Rel#ToSet(Rel#Union(a, b)) }
  Rel#ToSet(Rel#Union(a, b)) == Set#Union(Rel#ToSet(a), Rel#ToSet(b)));

// Intersection of two sets
function Rel#Intersection<U, V>(Rel U V, Rel U V): Rel U V;
// axiom (forall<U, V> a: Rel U V, b: Rel U V, u: U, v: V :: { Rel#Intersection(a, b)[u, v] }
  // Rel#Intersection(a,b)[u, v] <==> a[u, v] && b[u, v]);
axiom (forall<U, V> a, b: Rel U V :: { Rel#ToSet(Rel#Intersection(a, b)) }
  Rel#ToSet(Rel#Intersection(a, b)) == Set#Intersection(Rel#ToSet(a), Rel#ToSet(b)));

// axiom (forall<U, V> a, b: Rel U V :: { Rel#Union(Rel#Union(a, b), b) }
  // Rel#Union(Rel#Union(a, b), b) == Rel#Union(a, b));
// axiom (forall<U, V> a, b: Rel U V :: { Rel#Union(a, Rel#Union(a, b)) }
  // Rel#Union(a, Rel#Union(a, b)) == Rel#Union(a, b));
// axiom (forall<U, V> a, b: Rel U V :: { Rel#Intersection(Rel#Intersection(a, b), b) }
  // Rel#Intersection(Rel#Intersection(a, b), b) == Rel#Intersection(a, b));
// axiom (forall<U, V> a, b: Rel U V :: { Rel#Intersection(a, Rel#Intersection(a, b)) }
  // Rel#Intersection(a, Rel#Intersection(a, b)) == Rel#Intersection(a, b));
// axiom (forall<U, V> a, b: Rel U V :: { Rel#Card(Rel#Union(a, b)) }{ Rel#Card(Rel#Intersection(a, b)) }
  // Rel#Card(Rel#Union(a, b)) + Rel#Card(Rel#Intersection(a, b)) == Rel#Card(a) + Rel#Card(b));

// Relation a with all elements from b removed
function Rel#Difference<U, V>(Rel U V, Rel U V): Rel U V;
// axiom (forall<U, V> a: Rel U V, b: Rel U V, u: U, v: V :: { Rel#Difference(a, b)[u, v] }
  // Rel#Difference(a, b)[u, v] <==> a[u, v] && !b[u, v]);
// axiom (forall<U, V> a, b: Rel U V, u: U, v: V :: { Rel#Difference(a, b), b[u, v] }
  // b[u, v] ==> !Rel#Difference(a, b)[u, v]);
// axiom (forall<U, V> a, b: Rel U V ::
  // { Rel#Card(Rel#Difference(a, b)) }
  // Rel#Card(Rel#Difference(a, b)) + Rel#Card(Rel#Difference(b, a))
  // + Rel#Card(Rel#Intersection(a, b))
    // == Rel#Card(Rel#Union(a, b)) &&
  // Rel#Card(Rel#Difference(a, b)) == Rel#Card(a) - Rel#Card(Rel#Intersection(a, b)));
// axiom (forall<U, V> a: Rel U V :: { Rel#Difference(a,Rel#Empty()) }
  // Rel#Equal(Rel#Difference(a,Rel#Empty()), a));
axiom (forall<U, V> a, b: Rel U V :: { Rel#ToSet(Rel#Difference(a, b)) }
  Rel#ToSet(Rel#Difference(a, b)) == Set#Difference(Rel#ToSet(a), Rel#ToSet(b)));

// Symmetric difference of two relations
function Rel#SymDifference<U, V>(a: Rel U V, b: Rel U V): Rel U V;
// { Rel#Union(Rel#Difference(a, b), Rel#Difference(b, a)) }
axiom (forall<U, V> a, b: Rel U V :: { Rel#ToSet(Rel#SymDifference(a, b)) }
  Rel#ToSet(Rel#SymDifference(a, b)) == Set#SymDifference(Rel#ToSet(a), Rel#ToSet(b)));

// Type properties

function {: inline } Rel#DomainType<T>(heap: HeapType, r: Rel ref T, t: Type): bool
{ (forall o: ref :: { Rel#Domain(r)[o] } Rel#Domain(r)[o] ==> detachable(heap, o, t)) }

function {: inline } Rel#RangeType<T>(heap: HeapType, r: Rel T ref, t: Type): bool
{ (forall o: ref :: { Rel#Range(r)[o] } Rel#Range(r)[o] ==> detachable(heap, o, t)) }

// File: /home/caf/tools/eve_96960/library/base/mml/bag.bpl

// Finite bags.
// (Originally from Dafny Prelude: Copyright (c) Microsoft)

// Bag type
type Bag T = [T]int;

// Bag invariant
function Bag#IsValid<T>(b: Bag T): bool;
// ints are non-negative, used after havocing, and for conversion from sequences to multisets.
axiom (forall<T> b: Bag T :: { Bag#IsValid(b) }
  Bag#IsValid(b) <==> (forall bx: T :: { b[bx] } 0 <= b[bx]));

// Bag size
function Bag#Card<T>(Bag T): int;
axiom (forall<T> s: Bag T :: { Bag#Card(s) } 0 <= Bag#Card(s));
axiom (forall<T> s: Bag T, x: T, n: int :: { Bag#Card(s[x := n]) }
  0 <= n ==> Bag#Card(s[x := n]) == Bag#Card(s) - s[x] + n);

// Empty bag
function Bag#Empty<T>(): Bag T;
axiom (forall<T> o: T :: { Bag#Empty()[o] } Bag#Empty()[o] == 0);
axiom (forall<T> s: Bag T :: { Bag#Card(s) }
  (Bag#Card(s) == 0 <==> s == Bag#Empty()) &&
  (Bag#Card(s) != 0 ==> (exists x: T :: 0 < s[x])));
axiom (forall<T> f: Field (Bag T) :: { Default(f) } Default(f) == Bag#Empty() : Bag T);

// Singleton bag
function Bag#Singleton<T>(T): Bag T;
axiom (forall<T> r: T, o: T :: { Bag#Singleton(r)[o] } (Bag#Singleton(r)[o] == 1 <==> r == o) &&
                                                            (Bag#Singleton(r)[o] == 0 <==> r != o));
axiom (forall<T> r: T :: { Bag#Singleton(r) } Bag#Equal(Bag#Singleton(r), Bag#Extended(Bag#Empty(), r)));

// Bag that contains multiple occurrences of the same element
function Bag#Multiple<T>(T, int): Bag T;
axiom (forall<T> r: T, n: int, o: T :: { Bag#Multiple(r, n)[o] } (Bag#Multiple(r, n)[o] == n <==> r == o) &&
                                                            (Bag#Multiple(r, n)[o] == 0 <==> r != o));
axiom (forall<T> r: T, n: int :: { Bag#Multiple(r, n) } Bag#Equal(Bag#Multiple(r, n), Bag#ExtendedMultiple(Bag#Empty(), r, n)));

// Is x contained in b?
function {: inline } Bag#Has<T>(b: Bag T, x: T): bool
{ b[x] > 0 }

// Is b empty?
function {: inline } Bag#IsEmpty<T>(b: Bag T): bool
{ Bag#Equal(b, Bag#Empty()) }

// Does b contain each element c times?
function Bag#IsConstant<T>(b: Bag T, c: int): bool
{ (forall o: T :: b[o] != 0 ==> b[o] == c )}

// Set of values contained in the bag
function Bag#Domain<T>(Bag T): Set T;
axiom (forall <T> b: Bag T, o: T :: { Bag#Domain(b)[o] } Bag#Domain(b)[o] <==> b[o] > 0 );
axiom (forall <T> b: Bag T :: { Bag#IsEmpty(b), Bag#Domain(b) }{ Set#IsEmpty(Bag#Domain(b)) } Bag#IsEmpty(b) <==> Set#IsEmpty(Bag#Domain(b)) );

// Do two bags contain the same number of the same elements?
function Bag#Equal<T>(Bag T, Bag T): bool;
axiom(forall<T> a: Bag T, b: Bag T :: { Bag#Equal(a,b) }
  Bag#Equal(a,b) <==> (forall o: T :: {a[o]} {b[o]} a[o] == b[o]));
// extensionality axiom for multisets
axiom(forall<T> a: Bag T, b: Bag T :: { Bag#Equal(a,b) }
  Bag#Equal(a,b) ==> a == b);

// Does a have at most as many of each element as b?
function Bag#Subset<T>(Bag T, Bag T): bool;
axiom(forall<T> a: Bag T, b: Bag T :: { Bag#Subset(a,b) }
  Bag#Subset(a,b) <==> (forall o: T :: {a[o]} {b[o]} a[o] <= b[o]));

// Do two bags have no elements in common?
function Bag#Disjoint<T>(Bag T, Bag T): bool;
axiom (forall<T> a: Bag T, b: Bag T :: { Bag#Disjoint(a,b) }
  Bag#Disjoint(a,b) <==> (forall o: T :: {a[o]} {b[o]} a[o] == 0 || b[o] == 0));

// Bag extended with one occurrence of an element
function Bag#Extended<T>(Bag T, T): Bag T;
// pure containment axiom
axiom (forall<T> a: Bag T, x: T, o: T :: { Bag#Extended(a,x)[o] }
  0 < Bag#Extended(a,x)[o] <==> o == x || 0 < a[o]);
// union-ing increases count by one
axiom (forall<T> a: Bag T, x: T :: { Bag#Extended(a, x) }
  Bag#Extended(a, x)[x] == a[x] + 1);
// non-decreasing
axiom (forall<T> a: Bag T, x: T, y: T :: { Bag#Extended(a, x), a[y] }
  0 < a[y] ==> 0 < Bag#Extended(a, x)[y]);
// other elements unchanged
axiom (forall<T> a: Bag T, x: T, y: T :: { Bag#Extended(a, x), a[y] }
  x != y ==> a[y] == Bag#Extended(a, x)[y]);
axiom (forall<T> a: Bag T, x: T :: { Bag#Card(Bag#Extended(a, x)) }
  Bag#Card(Bag#Extended(a, x)) == Bag#Card(a) + 1);

// Bag extended with multiple occurrences of an element
function Bag#ExtendedMultiple<T>(Bag T, T, int): Bag T;
axiom (forall<T> a: Bag T, x: T :: { Bag#ExtendedMultiple(a, x, 0) }
  Bag#Equal(Bag#ExtendedMultiple(a, x, 0), a));
// pure containment axiom
axiom (forall<T> a: Bag T, x: T, n: int, o: T :: { Bag#ExtendedMultiple(a, x, n)[o] }
  n > 0 ==> (0 < Bag#ExtendedMultiple(a, x, n)[o] <==> o == x || 0 < a[o]));
// union-ing increases count by n
axiom (forall<T> a: Bag T, x: T, n: int :: { Bag#ExtendedMultiple(a, x, n) }
  Bag#ExtendedMultiple(a, x, n)[x] == a[x] + n);
// non-decreasing
axiom (forall<T> a: Bag T, x: T, n: int, y: T :: { Bag#ExtendedMultiple(a, x, n), a[y] }
  0 < a[y] ==> 0 < Bag#ExtendedMultiple(a, x, n)[y]);
// other elements unchanged
axiom (forall<T> a: Bag T, x: T, n: int, y: T :: { Bag#ExtendedMultiple(a, x, n), a[y] }
  x != y ==> a[y] == Bag#ExtendedMultiple(a, x, n)[y]);
axiom (forall<T> a: Bag T, x: T, n: int :: { Bag#Card(Bag#ExtendedMultiple(a, x, n)) }
  Bag#Card(Bag#ExtendedMultiple(a, x, n)) == Bag#Card(a) + n);

// Bag with one occurrence of an element removed
function Bag#Removed<T>(Bag T, T): Bag T;
axiom (forall<T> a: Bag T, x: T :: { Bag#Removed(a, x)[x] }
  a[x] > 0 ==> Bag#Removed(a, x)[x] == a[x] - 1);
axiom (forall<T> a: Bag T, x: T :: { Bag#Removed(a, x)[x] }
  a[x] == 0 ==> Bag#Removed(a, x)[x] == 0);
axiom (forall<T> a: Bag T, x: T, y: T :: { Bag#Removed(a, x)[y] }
  x != y ==> a[y] == Bag#Removed(a, x)[y]);
axiom (forall<T> a: Bag T, x: T :: { Bag#Card(Bag#Removed(a, x)) }
  a[x] > 0 ==> Bag#Card(Bag#Removed(a, x)) == Bag#Card(a) - 1);
axiom (forall<T> a: Bag T, x: T :: { Bag#Card(Bag#Removed(a, x)) }
  a[x] == 0 ==> Bag#Card(Bag#Removed(a, x)) == Bag#Card(a));

// Bag with multiple occurrences of an element removed
function Bag#RemovedMultiple<T>(Bag T, T, int): Bag T;
axiom (forall<T> a: Bag T, x: T, n: int :: { Bag#RemovedMultiple(a, x, n)[x] }
  a[x] >= n ==> Bag#RemovedMultiple(a, x, n)[x] == a[x] - n);
axiom (forall<T> a: Bag T, x: T, n: int :: { Bag#RemovedMultiple(a, x, n)[x] }
  a[x] < n ==> Bag#RemovedMultiple(a, x, n)[x] == 0);
axiom (forall<T> a: Bag T, x: T, n: int, y: T :: { Bag#RemovedMultiple(a, x, n), a[y] }
  x != y ==> a[y] == Bag#RemovedMultiple(a, x, n)[y]);
axiom (forall<T> a: Bag T, x: T, n: int :: { Bag#Card(Bag#RemovedMultiple(a, x, n)) }
  a[x] >= n ==> Bag#Card(Bag#RemovedMultiple(a, x, n)) == Bag#Card(a) - n);
axiom (forall<T> a: Bag T, x: T, n: int :: { Bag#Card(Bag#RemovedMultiple(a, x, n)) }
  a[x] < 0 ==> Bag#Card(Bag#Removed(a, x)) == Bag#Card(a) - a[x]);
// special cases
axiom (forall<T> a: Bag T, x: T :: { Bag#RemovedMultiple(a, x, 0) }
  Bag#Equal(Bag#RemovedMultiple(a, x, 0), a));


// Bag with all occurrences of an element removed.
function Bag#RemovedAll<T>(Bag T, T): Bag T;
axiom (forall<T> a: Bag T, x: T :: { Bag#RemovedAll(a, x)[x] }
  Bag#RemovedAll(a, x)[x] == 0);
axiom (forall<T> a: Bag T, x: T, y: T :: { Bag#RemovedAll(a, x), a[y] }
  x != y ==> a[y] == Bag#RemovedAll(a, x)[y]);
axiom (forall<T> a: Bag T, x: T :: {Bag#Card(Bag#RemovedAll(a, x))}
  Bag#Card(Bag#RemovedAll(a, x)) == Bag#Card(a) - a[x]);

// Bag that consists only of those elements of a that are in s.
function Bag#Restricted<T>(Bag T, Set T): Bag T;
axiom (forall<T> a: Bag T, s: Set T, x: T :: { Bag#Restricted(a, s)[x] }
  Bag#Restricted(a, s)[x] == if s[x] then a[x] else 0);

// Union of two bags
function Bag#Union<T>(Bag T, Bag T): Bag T;
// union-ing is the sum of the contents
axiom (forall<T> a: Bag T, b: Bag T, o: T :: { Bag#Union(a,b)[o] }
  Bag#Union(a,b)[o] == a[o] + b[o]);
axiom (forall<T> a: Bag T, b: Bag T :: { Bag#Card(Bag#Union(a,b)) }
  Bag#Card(Bag#Union(a,b)) == Bag#Card(a) + Bag#Card(b));

// Intersection of two bags
function Bag#Intersection<T>(Bag T, Bag T): Bag T;
axiom (forall<T> a: Bag T, b: Bag T, o: T :: { Bag#Intersection(a,b)[o] }
  Bag#Intersection(a,b)[o] == min(a[o],  b[o]));
// left and right pseudo-idempotence
axiom (forall<T> a, b: Bag T :: { Bag#Intersection(Bag#Intersection(a, b), b) }
  Bag#Intersection(Bag#Intersection(a, b), b) == Bag#Intersection(a, b));
axiom (forall<T> a, b: Bag T :: { Bag#Intersection(a, Bag#Intersection(a, b)) }
  Bag#Intersection(a, Bag#Intersection(a, b)) == Bag#Intersection(a, b));

// Difference of two multisets
function Bag#Difference<T>(Bag T, Bag T): Bag T;
axiom (forall<T> a: Bag T, b: Bag T, o: T :: { Bag#Difference(a,b)[o] }
  Bag#Difference(a,b)[o] == Math#clip(a[o] - b[o]));
axiom (forall<T> a, b: Bag T, y: T :: { Bag#Difference(a, b), b[y], a[y] }
  a[y] <= b[y] ==> Bag#Difference(a, b)[y] == 0 );
axiom (forall<T> a, b: Bag T ::
  { Bag#Card(Bag#Difference(a, b)) }
  Bag#Card(Bag#Difference(a, b)) + Bag#Card(Bag#Difference(b, a))
  + 2 * Bag#Card(Bag#Intersection(a, b))
    == Bag#Card(Bag#Union(a, b)) &&
  Bag#Card(Bag#Difference(a, b)) == Bag#Card(a) - Bag#Card(Bag#Intersection(a, b)));

// Conversion from set
function Bag#FromSet<T>(Set T): Bag T;
axiom (forall<T> s: Set T, a: T :: { Bag#FromSet(s)[a] }
  (Bag#FromSet(s)[a] == 0 <==> !s[a]) &&
  (Bag#FromSet(s)[a] == 1 <==> s[a]));
axiom (forall<T> s: Set T :: { Bag#Card(Bag#FromSet(s)) }
  Bag#Card(Bag#FromSet(s)) == Set#Card(s));

// Auxiliary functions

function Math#clip(a: int): int;
axiom (forall a: int :: { Math#clip(a) } 0 <= a ==> Math#clip(a) == a);
axiom (forall a: int :: { Math#clip(a) } a < 0  ==> Math#clip(a) == 0);

// Type property
function {: inline } Bag#DomainType(heap: HeapType, b: Bag ref, t: Type): bool
{ (forall o: ref :: { Bag#Domain(b)[o] }{ b[o] } Bag#Domain(b)[o] ==> detachable(heap, o, t)) }

// File: /home/caf/tools/eve_96960/library/base/mml/pair.bpl

// Pairs.

// Pair type
type Pair G H;

// Constructor
function Pair#Make<G, H>(G, H): Pair G H;
// Left component
function Pair#Left<G, H>(Pair G H): G;
// Right component
function Pair#Right<G, H>(Pair G H): H;

axiom (forall<G, H> x: G, y: H :: { Pair#Left(Pair#Make(x, y)) } Pair#Left(Pair#Make(x, y)) == x);
axiom (forall<G, H> x: G, y: H :: { Pair#Right(Pair#Make(x, y)) } Pair#Right(Pair#Make(x, y)) == y);

// Are two pairs equal?
function Pair#Equal<G, H>(p: Pair G H, q: Pair G H): bool
{ Pair#Left(p) == Pair#Left(q) && Pair#Right(p) == Pair#Right(q) }
axiom(forall<G, H> p: Pair G H, q: Pair G H :: { Pair#Equal(p, q) }  // extensionality axiom for pairs
  Pair#Equal(p, q) ==> p == q);

// Type properties

function {: inline } Pair#LeftType<T>(heap: HeapType, p: Pair ref T, t: Type): bool
{ detachable(heap, Pair#Left(p), t) }

function {: inline } Pair#RightType<T>(heap: HeapType, p: Pair T ref, t: Type): bool
{ detachable(heap, Pair#Right(p), t) }

// File: /home/caf/tools/eve_96960/studio/tools/autoproof/base_theory.bpl

// ----------------------------------------------------------------------
// Reference types

type ref; // Type definition for reference types
const Void: ref; // Constant for Void references

// Is r1 <= r2 in the well-founded order?
function ref_rank_leq(r1, r2: ref): bool
{ r2 == Void ==> r1 == Void }

// ----------------------------------------------------------------------
// Heap and allocation

type Field _; // Type of a field (with open subtype)
// function IsGhostField<alpha>(field: Field alpha): bool; // Is this field a ghost field?
function FieldId<alpha>(field: Field alpha, t: Type): int; // ID of field within t; used to express that all fields of the same class are distinct.

// Default field value
function Default<alpha>(Field alpha): alpha;
axiom (forall f: Field bool :: !Default(f));
axiom (forall f: Field int :: Default(f) == 0);
axiom (forall f: Field ref :: Default(f) == Void);
// axiom (forall f: Field real :: Default(f) == 0.0); // 'real' unsupported

type HeapType = <alpha>[ref, Field alpha]alpha; // Type of a heap (with generic field subtype and generic content type)
const allocated: Field bool; // Ghost field for allocation status of objects

// Function which defines basic properties of a heap
function IsHeap(heap: HeapType): bool;

// The global heap (which is always a heap)
var Heap: HeapType where IsHeap(Heap);

// Function that defines properties of two (transitively) successive heaps
function HeapSucc(HeapType, HeapType): bool;
axiom (forall<alpha> h: HeapType, r: ref, f: Field alpha, x: alpha :: { h[r, f := x] }
  IsHeap(h[r, f := x]) ==>
  HeapSucc(h, h[r, f := x]));
axiom (forall a,b,c: HeapType :: { HeapSucc(a,b), HeapSucc(b,c) }
  HeapSucc(a,b) && HeapSucc(b,c) ==> HeapSucc(a,c));
axiom (forall h: HeapType, k: HeapType :: { HeapSucc(h,k) }
  HeapSucc(h,k) ==> (forall o: ref :: { k[o, allocated] } h[o, allocated] ==> k[o, allocated]));


// ----------------------------------------------------------------------
// Typing

type Type; // Type definition for Eiffel types
const unique ANY: Type; // Type for ANY
const unique NONE: Type; // Type for NONE

// Type function for objects.
function type_of(o: ref): Type;
function is_frozen(t: Type): bool;

// Typing axioms
axiom (forall t: Type :: { ANY <: t } ANY <: t <==> t == ANY);
axiom (forall t: Type :: t <: ANY); // All types inherit from ANY.
// axiom (forall t: Type :: NONE <: t); // NONE inherits from all types.
// axiom (forall h: HeapType :: IsHeap(h) ==> h[Void, allocated]); // Void is always allocated.
axiom (forall h: HeapType, f: Field ref, o: ref :: IsHeap(h) && h[o, allocated] ==> h[h[o, f], allocated]); // All reference fields are allocated.
axiom (forall r: ref :: (r == Void) <==> (type_of(r) == NONE)); // Void is only reference of type NONE.
// axiom (forall a, b: ref :: (type_of(a) != type_of(b)) ==> (a != b)); // Objects that have different dynamic type cannot be aliased.
// axiom (forall t: Type :: is_frozen(t) ==> (forall t2: Type :: t2 <: t ==> t2 == t || t2 == NONE)); // Only NONE inherits from frozen types.
axiom (forall t: Type, r: ref :: { is_frozen(t), type_of(r) } (r != Void && type_of(r) <: t && is_frozen(t)) ==> (type_of(r) == t)); // Non-void references of a frozen type are exact.
// axiom (forall h: HeapType, t: Type, o: ref :: { is_frozen(t), attached_exact(h, o, t) } IsHeap(h) && is_frozen(t) && attached(h, o, t) ==> attached_exact(h, o, t));

// ----------------------------------------------------------------------
// Built-in attributes

const closed: Field bool; // Ghost field for open/closed status of an object.
const owner: Field ref; // Ghost field for owner of an object.
const owns: Field (Set ref); // Ghost field for owns set of an object.
const observers: Field (Set ref); // Ghost field for observers set of an object.
const subjects: Field (Set ref); // Ghost field for subjects set of an object.

// Analogue of `detachable_attribute' and `set_detachable_attribute' for built-in attributes:
axiom (forall heap: HeapType, o: ref :: { heap[o, owner] } IsHeap(heap) && o != Void && heap[o, allocated] ==> heap[heap[o, owner], allocated]);
axiom (forall heap: HeapType, o, o': ref :: { heap[o, owns][o'] } IsHeap(heap) && o != Void && heap[o, allocated] && heap[o, owns][o'] ==> heap[o', allocated]);
axiom (forall heap: HeapType, o, o': ref :: { heap[o, subjects][o'] } IsHeap(heap) && o != Void && heap[o, allocated] && heap[o, subjects][o'] ==> heap[o', allocated]);
axiom (forall heap: HeapType, o, o': ref :: { heap[o, observers][o'] } IsHeap(heap) && o != Void && heap[o, allocated] && heap[o, observers][o'] ==> heap[o', allocated]);

// Is o open in h? (not closed and free)
function is_open(h: HeapType, o: ref): bool {
	!h[o, closed]
}

// Is o closed in h?
function is_closed(h: HeapType, o: ref): bool {
	h[o, closed]
}

// Is o free? (owner is open)
function {:inline} is_free(h: HeapType, o: ref): bool {
  h[o, owner] == Void
}

// Is o wrapped in h? (closed and free)
function is_wrapped(h: HeapType, o: ref): bool {
	h[o, closed] && is_free(h, o)
}

// Is o' in the ownership domain of o? Yes if they are equal, or both closed and o' is transitively owned by o
function in_domain(h: HeapType, o: ref, o': ref): bool
{
	o == o' || ( h[o, closed] && h[o', closed] && in_domain(h, o, h[o', owner]) )
}

axiom (forall h: HeapType, o, o': ref :: { in_domain(h, o, o') } IsHeap(h) && h[o, closed] && h[o, owns][o'] ==> in_domain(h, o, o'));
axiom (forall h: HeapType, o, o': ref :: { in_domain(h, o, o'), trans_owns(h, o) } IsHeap(h) && h[o, closed] ==> (in_trans_owns(h, o, o') <==> in_domain(h, o, o')));
axiom (forall h: HeapType, o, o': ref :: { in_domain(h, o, o') } IsHeap(h) && o != o' && Set#Equal(Set#Empty(), h[o, owns]) ==> !in_domain(h, o, o'));
axiom (forall h: HeapType, o, o', o'': ref :: { in_domain(h, o, o'), Set#Equal(Set#Singleton(o''), h[o, owns]) } IsHeap(h) && h[o, closed] && o != o' && Set#Equal(Set#Singleton(o''), h[o, owns]) ==>
	(in_domain(h, o, o') <==> in_domain(h, o'', o')));


// Frame axiom: domain frames itself
axiom (forall h, h': HeapType, x, x': ref :: { in_domain(h, x, x'), in_domain(h', x, x'), HeapSucc(h, h') }
  IsHeap(h) && IsHeap(h') && HeapSucc(h, h') &&
  h[x, allocated] && h'[x, allocated] &&
  (forall <T> o: ref, f: Field T :: h[o, allocated] ==> h'[o, f] == h[o, f] || !in_domain(h, x, o))
  ==> in_domain(h', x, x') == in_domain(h, x, x'));

function domain(h: HeapType, o: ref): Set ref
{ (lambda o': ref :: in_domain(h, o, o')) }

// Is o' in the transitive owns of o?
// (the same as in_domain if o is closed)
function in_trans_owns(h: HeapType, o: ref, o': ref): bool
{
  o == o' || h[o, owns][o'] || (exists x: ref :: h[o, owns][x] && in_trans_owns(h, x, o'))
}

function trans_owns(h: HeapType, o: ref): Set ref
{ (lambda o': ref :: in_trans_owns(h, o, o')) }

const universe: Set ref;
axiom (forall o: ref :: { universe[o] } universe[o]);

// ----------------------------------------------------------------------
// Models

function IsModelField<alpha>(field: Field alpha, t: Type): bool; // Is this field a model field in class t?

axiom (forall <alpha> f: Field alpha :: { IsModelField(f, ANY) }
  IsModelField(f, ANY) <==> f == closed || f == owner || f == owns || f == observers || f == subjects );

// ----------------------------------------------------------------------
// Frames

// Set of object-field pairs
type Frame = <alpha>[ref, Field alpha]bool;

function Frame#Subset(Frame, Frame): bool;
axiom(forall a: Frame, b: Frame :: { Frame#Subset(a,b) }
  Frame#Subset(a,b) <==> (forall <alpha> o: ref, f: Field alpha :: {a[o, f]} {b[o, f]} a[o, f] ==> b[o, f]));

function Frame#Singleton(ref): Frame;
axiom(forall <alpha> o, o': ref, f: Field alpha :: { Frame#Singleton(o)[o', f] }
  Frame#Singleton(o)[o', f] <==> o == o');

function has_whole_object(frame: Frame, o: ref): bool
{ (forall <alpha> f: Field alpha :: frame[o, f]) }

// Frame is closed under ownership domains and includes all unallocated objects
function { :inline } closed_under_domains(frame: Frame, h: HeapType): bool
{
  (forall <U> o': ref, f': Field U :: {frame[o', f']}
    !h[o', allocated] || (exists <V> o: ref, f: Field V :: frame[o, f] && in_domain(h, o, o') && o != o') ==> frame[o', f'])
}

// Objects outside of ownership domains of frame did not change, unless they were newly allocated
function {: inline } same_outside(h: HeapType, h': HeapType, frame: Frame): bool {
	(forall <T> o: ref, f: Field T :: { h'[o, f] }
    o != Void && h[o, allocated] ==>
      h'[o, f] == h[o, f] ||
      frame[o, f] ||
      (exists o': ref :: {frame[o', closed]} o' != o && frame[o', closed] && in_domain(h, o', o)) // Using extra knowledge here to remove an existential: modifying object's domain requires its closed to be in the frame
  )
}

// Objects outside of frame did not change, unless they were newly allocated
function {: inline } flat_same_outside(h: HeapType, h': HeapType, frame: Frame): bool {
	(forall <T> o: ref, f: Field T :: { h'[o, f] } o != Void && h[o, allocated] ==> h'[o, f] == h[o, f] || frame[o, f])
}

// Objects inside the frame did not change
function same_inside(h: HeapType, h': HeapType, frame: Frame): bool {
	(forall <T> o: ref, f: Field T :: o != Void && h[o, allocated] && h'[o, allocated] && frame [o, f] ==> h'[o, f] == h[o, f])
}
// This version corresponds to the old semantics of read clauses:
// // Objects inside the old ownership domains of frame did not change
// // function same_inside(h: HeapType, h': HeapType, frame: Frame): bool {
	// // (forall <T> o: ref, f: Field T :: { h[o, f] } { h'[o, f] }
    // // h[o, allocated] && h'[o, f] != h[o, f] ==>
      // // !frame [o, f] && (forall<U> o': ref, g: Field U :: frame[o', g] && o != o' ==> !in_domain(h, o', o)))
// // }

// Set of all writable objects
const writable: Frame;

// Set of all readable objects
const readable: Frame;

// ----------------------------------------------------------------------
// Invariants

// Is invariant of object o satisifed?
function user_inv(h: HeapType, o: ref): bool;

// Read frame of user_inv
function user_inv_readable(HeapType, ref): Frame;
axiom (forall<T> h: HeapType, x: ref, o: ref, f: Field T :: { user_inv_readable(h, x)[o, f] }
  IsHeap(h) ==> user_inv_readable(h, x)[o, f] == (in_trans_owns(h, x, o) || h[x, subjects][o]));

// Uninterpreted function to trigger the invariant frame axiom
function inv_frame_trigger(x: ref): bool;

// Frame axiom
axiom (forall h, h': HeapType, x: ref :: { user_inv(h, x), user_inv(h', x), HeapSucc(h, h'), inv_frame_trigger(x) }
  IsHeap(h) && IsHeap(h') && HeapSucc(h, h') && inv_frame_trigger(x) &&
  x != Void && h[x, allocated] && h'[x, allocated] &&
  is_open(h, x) && is_open(h', x) &&
  user_inv(h, x) &&
  (forall <T> o: ref, f: Field T :: h[o, allocated] ==> // every object's field
      h'[o, f] == h[o, f] ||                            // is unchanged
      f == closed || f == owner ||                      // or is outside of the read set of the invariant
      !user_inv_readable(h, x)[o, f]
      // (!in_trans_owns(h, x, o) && guard(h, o, f, h'[o, f], x)) // or changed in a way that conforms to its guard
   )
  ==> user_inv(h', x));

// Is object o closed or the invariant satisfied?
function {:inline true} inv(h: HeapType, o: ref): bool {
	h[o, closed] ==> user_inv(h, o)
}

// Global heap invariants
function {:inline true} global(h: HeapType): bool
{
  h[Void, allocated] && is_open(h, Void) &&
  // (forall o: ref :: h[o, allocated] && is_open(h, o) ==> is_free(h, o)) &&
  // (forall o: ref :: { h[o, owner], is_open(h, o) } h[o, allocated] && is_open(h, o) ==> is_free(h, o)) &&
  (forall o: ref, o': ref :: { h[o, owns][o'] } h[o, allocated] && h[o', allocated] && h[o, closed] && h[o, owns][o'] ==> (h[o', closed] && h[o', owner] == o)) && // G2
  (forall o: ref :: { user_inv(h, o) } h[o, allocated] ==> inv(h, o)) // G1
}

// All objects in valid heaps are valid.
// This function introduces invariants automatically, so should be used with care.
function {: inline } global_permissive(): bool
{ (forall h: HeapType, o: ref :: {is_wrapped (h, o)}{is_closed (h, o)} IsHeap(h) && h[o, allocated] ==> inv(h, o)) }

// Condition under which an update heap[current, f] := v is guaranteed to preserve the invariant of o.
function guard<T>(heap: HeapType, current: ref, f: Field T, v: T, o: ref): bool;

// All subjects know current for an observer
function {: inline } admissibility2 (heap: HeapType, current: ref): bool
{
  (forall s: ref :: heap[current, subjects][s] && s != Void ==> heap[s, observers][current])
}

// Invariant cannot be invalidated by an update that conform to its guard
function {: inline } admissibility3 (heap: HeapType, current: ref): bool
{
  (forall<T> s: ref, f: Field T, v: T ::
    heap[current, subjects][s] && s != current && s != Void && IsHeap(heap[s, f := v]) && guard(heap, s, f, v, current) ==>
      user_inv(heap[s, f := v], current))
}

// ----------------------------------------------------------------------
// Built-in operations

// Allocate fresh object
procedure allocate(t: Type) returns (result: ref);
  modifies Heap;
  ensures global(Heap);
  // ensures !old(Heap[result, allocated]); // AL1
  ensures Heap[result, allocated]; // AL2
  ensures result != Void;
  ensures type_of(result) == t;
  ensures (forall<T> f: Field T :: f != allocated ==> Heap[result, f] == Default(f));
  ensures has_whole_object(writable, result);
  ensures (forall <T> o: ref, f: Field T :: o != result ==> Heap[o, f] == old(Heap[o, f]));
  free ensures HeapSucc(old(Heap), Heap);

// Update Heap position Current.field with value.
procedure update_heap<T>(Current: ref, field: Field T, value: T);
  requires (Current != Void) && (Heap[Current, allocated]); // type:assign tag:attached_and_allocated
  requires field != closed && field != owner; // type:assign tag:closed_or_owner_not_allowed UP4
  requires is_open(Heap, Current); // type:assign tag:target_open UP1
  requires (forall o: ref :: Heap[Current, observers][o] ==> (is_open(Heap, o) || (IsHeap(Heap[Current, field := value]) ==> guard(Heap, Current, field, value, o)))); // type:assign tag:observers_open_or_guard_holds UP2
  requires writable[Current, field]; // type:assign tag:attribute_writable UP3
  modifies Heap;
  ensures global(Heap);
  ensures Heap == old(Heap[Current, field := value]);
  free ensures HeapSucc(old(Heap), Heap);

// Unwrap o
procedure unwrap(o: ref);
  requires (o != Void) && (Heap[o, allocated]); // type:pre tag:attached
  requires is_wrapped(Heap, o); // type:pre tag:wrapped UW1
  requires writable[o, closed]; // type:pre tag:writable UW2
  modifies Heap;
  ensures global(Heap);
  ensures is_open(Heap, o); // UWE1
  ensures (forall o': ref :: old(Heap[o, owns][o']) ==> is_wrapped(Heap, o')); // UWE2
  ensures (forall <T> o': ref, f: Field T :: !(o' == o && f == closed) && !(old(Heap[o, owns][o']) && f == owner) ==> Heap[o', f] == old(Heap[o', f]));
  free ensures HeapSucc(old(Heap), Heap);

procedure unwrap_all (Current: ref, s: Set ref);
  requires (forall o: ref :: s[o] ==> (o != Void) && (Heap[o, allocated])); // type:pre tag:attached
  requires (forall o: ref :: s[o] ==> is_wrapped(Heap, o)); // type:pre tag:wrapped UW1
  requires (forall o: ref :: s[o] ==> writable[o, closed]); // type:pre tag:writable UW2
  modifies Heap;
  ensures global(Heap);
  ensures (forall o: ref :: s[o] ==> is_open(Heap, o)); // UWE1
  ensures (forall o: ref :: s[o] ==> (forall o': ref :: old(Heap[o, owns][o']) ==> is_wrapped(Heap, o'))); // UWE2
  ensures (forall <T> o: ref, f: Field T :: !(f == closed && s[o]) && !(f == owner && (exists o': ref :: s[o'] && old(Heap[o', owns][o]))) ==> Heap[o, f] == old(Heap[o, f]));
  ensures (forall o: ref :: s[o] ==> user_inv(Heap, o) && inv_frame_trigger(o));
  free ensures HeapSucc(old(Heap), Heap);

// Wrap o
procedure wrap(o: ref);
  requires (o != Void) && (Heap[o, allocated]); // type:pre tag:attached
  requires is_open(Heap, o); // type:pre tag:open W1
  requires writable[o, closed]; // type:pre tag:writable W4
  // requires user_inv(Heap, o); // type:pre tag:invariant_holds W2 // Custom check now
  requires (forall o': ref :: { Heap[o, owns][o'] } Heap[o, owns][o'] ==> is_wrapped(Heap, o') && writable[o', owner]); // type:pre tag:owned_objects_wrapped_and_writable W3
  modifies Heap;
  ensures global(Heap);
  ensures (forall o': ref :: old(Heap[o, owns][o']) ==> Heap[o', owner] == o); // WE2
  ensures is_wrapped(Heap, o); // WE3
  ensures (forall <T> o': ref, f: Field T :: !(o' == o && f == closed) && !(old(Heap[o, owns][o']) && f == owner) ==> Heap[o', f] == old(Heap[o', f]));
  free ensures HeapSucc(old(Heap), Heap);

procedure wrap_all(Current: ref, s: Set ref);
  requires (forall o: ref :: s[o] ==> (o != Void) && (Heap[o, allocated])); // type:pre tag:attached
  requires (forall o: ref :: s[o] ==> is_open(Heap, o)); // type:pre tag:open W1
  requires (forall o: ref :: s[o] ==> writable[o, closed]); // type:pre tag:writable W4
  requires (forall o: ref :: s[o] ==> user_inv(Heap, o)); // type:pre tag:invariant_holds W2
  requires (forall o: ref :: s[o] ==> (forall o': ref :: Heap[o, owns][o'] ==> is_wrapped(Heap, o') && writable[o', owner])); // type:pre tag:owned_objects_wrapped_and_writable W3
  modifies Heap;
  ensures global(Heap);
  ensures (forall o: ref :: s[o] ==> (forall o': ref :: old(Heap[o, owns][o']) ==> Heap[o', owner] == o)); // WE2
  ensures (forall o: ref :: s[o] ==> is_wrapped(Heap, o)); // WE3
  ensures (forall <T> o: ref, f: Field T :: !(f == closed && s[o]) && !(f == owner && (exists o': ref :: s[o'] && old(Heap[o', owns][o]))) ==> Heap[o, f] == old(Heap[o, f]));
  free ensures HeapSucc(old(Heap), Heap);

// ----------------------------------------------------------------------
// Attached/Detachable functions

// Reference `o' is attached to an object of type `t' on heap `heap'.
function attached_exact(heap: HeapType, o: ref, t: Type) returns (bool) {
	(o != Void) && (heap[o, allocated]) && (type_of(o) == t)
}

// Reference `o' is either Void or attached to an object of type `t' on heap `heap'.
function detachable_exact(heap: HeapType, o: ref, t: Type) returns (bool) {
	(o == Void) || attached_exact(heap, o, t)
}

// Reference `o' is attached and conforms to type `t' on heap `heap'.
function attached(heap: HeapType, o: ref, t: Type) returns (bool) {
	(o != Void) && (heap[o, allocated]) && (type_of(o) <: t)
}

// Reference `o' is either Void or attached and conforms to `t' on heap `heap'.
function detachable(heap: HeapType, o: ref, t: Type) returns (bool) {
	(o == Void) || attached(heap, o, t)
}

// ----------------------------------------------------------------------
// Basic types

// Integer boxing

const unique INTEGER: Type;

function boxed_int(i: int) returns (ref);
function unboxed_int(r: ref) returns (int);

axiom (forall i: int :: unboxed_int(boxed_int(i)) == i);
axiom (forall i1, i2: int :: (i1 == i2) ==> (boxed_int(i1) == boxed_int(i2)));
axiom (forall i: int :: boxed_int(i) != Void && type_of(boxed_int(i)) == INTEGER);
axiom (forall heap: HeapType, i: int :: IsHeap(heap) ==> heap[boxed_int(i), allocated]);


// Boolean boxing

const unique BOOLEAN: Type;
const unique boxed_true: ref;
const unique boxed_false: ref;

function boxed_bool(b: bool) returns (ref);
function unboxed_bool(r: ref) returns (bool);

axiom (boxed_bool(true) == boxed_true);
axiom (boxed_bool(false) == boxed_false);
axiom (unboxed_bool(boxed_true) == true);
axiom (unboxed_bool(boxed_false) == false);
axiom (boxed_true != boxed_false);
axiom (boxed_true != Void && type_of(boxed_true) == BOOLEAN);
axiom (boxed_false != Void && type_of(boxed_false) == BOOLEAN);
axiom (forall heap: HeapType :: IsHeap(heap) ==> heap[boxed_true, allocated]);
axiom (forall heap: HeapType :: IsHeap(heap) ==> heap[boxed_false, allocated]);

// Bounded integers

function is_integer_8(i: int) returns (bool) {
	(-128 <= i) && (i <= 127)
}
function is_integer_16(i: int) returns (bool) {
	(-32768 <= i) && (i <= 32767)
}
function is_integer_32(i: int) returns (bool) {
	(-2147483648 <= i) && (i <= 2147483647)
}
function is_integer_64(i: int) returns (bool) {
	(-9223372036854775808 <= i) && (i <= 9223372036854775807)
}
function is_natural(i: int) returns (bool) {
	(0 <= i)
}
function is_natural_8(i: int) returns (bool) {
	(0 <= i) && (i <= 255)
}
function is_natural_16(i: int) returns (bool) {
	(0 <= i) && (i <= 65535)
}
function is_natural_32(i: int) returns (bool) {
	(0 <= i) && (i <= 4294967295)
}
function is_natural_64(i: int) returns (bool) {
	(0 <= i) && (i <= 18446744073709551615)
}

// Numeric conversions

function int_to_integer_8(i: int) returns (int);
axiom (forall i: int :: { int_to_integer_8(i) } is_integer_8(i) ==> int_to_integer_8(i) == i);
axiom (forall i: int :: { int_to_integer_8(i) } is_integer_8(int_to_integer_8(i)));

function int_to_integer_16(i: int) returns (int);
axiom (forall i: int :: { int_to_integer_16(i) } is_integer_16(i) ==> int_to_integer_16(i) == i);
axiom (forall i: int :: { int_to_integer_16(i) } is_integer_16(int_to_integer_16(i)));

function int_to_integer_32(i: int) returns (int);
axiom (forall i: int :: { int_to_integer_32(i) } is_integer_32(i) ==> int_to_integer_32(i) == i);
axiom (forall i: int :: { int_to_integer_32(i) } is_integer_32(int_to_integer_32(i)));

function int_to_integer_64(i: int) returns (int);
axiom (forall i: int :: { int_to_integer_64(i) } is_integer_64(i) ==> int_to_integer_64(i) == i);
axiom (forall i: int :: { int_to_integer_64(i) } is_integer_64(int_to_integer_64(i)));

function int_to_natural_8(i: int) returns (int);
axiom (forall i: int :: { int_to_natural_8(i) } is_natural_8(i) ==> int_to_natural_8(i) == i);
axiom (forall i: int :: { int_to_natural_8(i) } is_natural_8(int_to_natural_8(i)));

function int_to_natural_16(i: int) returns (int);
axiom (forall i: int :: { int_to_natural_16(i) } is_natural_16(i) ==> int_to_natural_16(i) == i);
axiom (forall i: int :: { int_to_natural_16(i) } is_natural_16(int_to_natural_16(i)));

function int_to_natural_32(i: int) returns (int);
axiom (forall i: int :: { int_to_natural_32(i) } is_natural_32(i) ==> int_to_natural_32(i) == i);
axiom (forall i: int :: { int_to_natural_32(i) } is_natural_32(int_to_natural_32(i)));

function int_to_natural_64(i: int) returns (int);
axiom (forall i: int :: { int_to_natural_64(i) } is_natural_64(i) ==> int_to_natural_64(i) == i);
axiom (forall i: int :: { int_to_natural_64(i) } is_natural_64(int_to_natural_64(i)));

// function real_to_integer_32(r: real) returns (int); // 'real' unsupported
// axiom (forall r: real :: { real_to_integer_32(r) } is_integer_32(int(r)) ==> real_to_integer_32(r) == int(r)); // 'real' unsupported
// axiom (forall r: real :: { real_to_integer_32(r) } (!is_integer_32(int(r)) && r < 0.0) ==> real_to_integer_32(r) == -2147483648); // 'real' unsupported
// axiom (forall r: real :: { real_to_integer_32(r) } (!is_integer_32(int(r)) && r > 0.0) ==> real_to_integer_32(r) ==  2147483647); // 'real' unsupported

// function real_to_integer_64(r: real) returns (int); // 'real' unsupported
// axiom (forall r: real :: { real_to_integer_64(r) } is_integer_64(int(r)) ==> real_to_integer_64(r) == int(r)); // 'real' unsupported
// axiom (forall r: real :: { real_to_integer_64(r) } (!is_integer_64(int(r)) && r < 0.0) ==> real_to_integer_64(r) == -9223372036854775808); // 'real' unsupported
// axiom (forall r: real :: { real_to_integer_64(r) } (!is_integer_64(int(r)) && r > 0.0) ==> real_to_integer_64(r) ==  9223372036854775807); // 'real' unsupported

// Arithmetic functions

function add(a, b: int): int { a + b }
function subtract(a, b: int): int { a - b }
function multiply(a, b: int): int { a * b }
function modulo(a, b: int): int { a mod b }
function divide(a, b: int): int { a div b }

function min(a, b: int): int { if a <= b then a else b }
function max(a, b: int): int { if a >= b then a else b }
function abs(a: int): int { if a >= 0 then a else -a }
function sign(a: int): int { if a == 0 then 0 else if a > 0 then 1 else -1 }

// function min_real(a, b: real): real { if a <= b then a else b } // 'real' unsupported
// function max_real(a, b: real): real { if a >= b then a else b } // 'real' unsupported
// function abs_real(a: real): real { if a >= 0.0 then a else -a } // 'real' unsupported
// function sign_real(a: real): int { if a == 0.0 then 0 else if a > 0.0 then 1 else -1 } // 'real' unsupported

function bit_and(a, b: int): int;
function bit_or(a, b: int): int;
function bit_xor(a, b: int): int;
function bit_not(a: int): int;
function bit_shift_left(a, n: int): int;
function bit_shift_right(a, n: int): int;

// ----------------------------------------------------------------------
// once procedures

function global_once_value<T>(rid: int): T;
function object_once_value<T>(o: ref, rid: int): T;


// Expanded types

// type unknown;

// Address operator

// function address(a: ref) returns (int);
// axiom (forall a, b: ref :: (a != b) <==> (address(a) != address(b))); // Different objects have different heap addresses.
// axiom (forall a: ref :: is_integer_64(address(a))); // Addresses are 64 bit integers.

// Unsupported

function unsupported<T>() returns (T);


// Custom content

const unique MY_ITERATOR: Type;

axiom ((MY_ITERATOR) <: (ANY));

axiom ((forall t: Type :: { (MY_ITERATOR) <: (t) } ((MY_ITERATOR) <: (t)) <==> (((t) == (MY_ITERATOR)) || ((ANY) <: (t)))));

axiom ((FieldId(allocated, MY_ITERATOR)) == (-1));

axiom ((FieldId(closed, MY_ITERATOR)) == (-2));

axiom ((FieldId(owner, MY_ITERATOR)) == (-3));

axiom ((FieldId(owns, MY_ITERATOR)) == (-4));

axiom ((FieldId(observers, MY_ITERATOR)) == (-5));

axiom ((FieldId(subjects, MY_ITERATOR)) == (-6));

axiom ((forall <T0> $f: Field T0 :: { IsModelField($f, MY_ITERATOR) } (IsModelField($f, MY_ITERATOR)) <==> ((($f) == (subjects)) || (($f) == (observers)))));

function { :inline } MY_ITERATOR.user_inv(heap: HeapType, current: ref) returns (bool) {
  ((heap[current, MY_ITERATOR.target]) != (Void)) && (Set#Equal(heap[current, subjects], Set#Singleton(heap[current, MY_ITERATOR.target]))) && ((0) <= (heap[current, MY_ITERATOR.index])) && ((heap[current, MY_ITERATOR.index]) <= ((heap[heap[current, MY_ITERATOR.target], MY_COLLECTION.count]) + (1))) && ((heap[current, MY_ITERATOR.before]) == ((heap[current, MY_ITERATOR.index]) < (1))) && ((heap[current, MY_ITERATOR.after]) == ((heap[current, MY_ITERATOR.index]) > (heap[heap[current, MY_ITERATOR.target], MY_COLLECTION.count]))) && (Set#IsEmpty(heap[current, observers])) && (Set#IsEmpty(heap[current, owns])) && (admissibility2(heap, current))
}

function MY_ITERATOR.subjects.static(heap: HeapType, current: ref) returns (Set (ref)) {
  Set#Singleton(heap[current, MY_ITERATOR.target])
}

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached_exact(heap, current, MY_ITERATOR)) ==> ((user_inv(heap, current)) <==> (MY_ITERATOR.user_inv(heap, current)))));

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached(heap, current, MY_ITERATOR)) ==> ((user_inv(heap, current)) ==> (MY_ITERATOR.user_inv(heap, current)))));

procedure MY_ITERATOR.invariant_admissibility_check(Current: ref);
  requires attached_exact(Heap, Current, MY_ITERATOR);



implementation MY_ITERATOR.invariant_admissibility_check(Current: ref)
{
  entry:
  goto pre, a2, a3;
  pre:
  assert user_inv_readable(Heap, Current)[Current, MY_ITERATOR.target]; // type:access tag:attribute_readable line:76 cid:404 fid:81
  assume (Heap[Current, MY_ITERATOR.target]) != (Void);
  assert user_inv_readable(Heap, Current)[Current, MY_ITERATOR.target]; // type:access tag:attribute_readable line:77 cid:404 fid:81
  assume Set#Equal(Heap[Current, subjects], Set#Singleton(Heap[Current, MY_ITERATOR.target]));
  assert user_inv_readable(Heap, Current)[Current, MY_ITERATOR.index]; // type:access tag:attribute_readable line:78 cid:404 fid:86
  assert user_inv_readable(Heap, Current)[Current, MY_ITERATOR.index]; // type:access tag:attribute_readable line:78 cid:404 fid:86
  assert user_inv_readable(Heap, Current)[Current, MY_ITERATOR.target]; // type:access tag:attribute_readable line:78 cid:404 fid:81
  assert {:subsumption 0} (Heap[Current, MY_ITERATOR.target]) != (Void); // type:attached tag:index_in_bounds line:78
  assert user_inv_readable(Heap, Current)[Heap[Current, MY_ITERATOR.target], MY_COLLECTION.count]; // type:access tag:attribute_readable line:78 cid:406 fid:81
  assume ((0) <= (Heap[Current, MY_ITERATOR.index])) && ((Heap[Current, MY_ITERATOR.index]) <= ((Heap[Heap[Current, MY_ITERATOR.target], MY_COLLECTION.count]) + (1)));
  assert user_inv_readable(Heap, Current)[Current, MY_ITERATOR.before]; // type:access tag:attribute_readable line:79 cid:404 fid:82
  assert user_inv_readable(Heap, Current)[Current, MY_ITERATOR.index]; // type:access tag:attribute_readable line:79 cid:404 fid:86
  assume (Heap[Current, MY_ITERATOR.before]) == ((Heap[Current, MY_ITERATOR.index]) < (1));
  assert user_inv_readable(Heap, Current)[Current, MY_ITERATOR.after]; // type:access tag:attribute_readable line:80 cid:404 fid:83
  assert user_inv_readable(Heap, Current)[Current, MY_ITERATOR.index]; // type:access tag:attribute_readable line:80 cid:404 fid:86
  assert user_inv_readable(Heap, Current)[Current, MY_ITERATOR.target]; // type:access tag:attribute_readable line:80 cid:404 fid:81
  assert {:subsumption 0} (Heap[Current, MY_ITERATOR.target]) != (Void); // type:attached tag:after_definition line:80
  assert user_inv_readable(Heap, Current)[Heap[Current, MY_ITERATOR.target], MY_COLLECTION.count]; // type:access tag:attribute_readable line:80 cid:406 fid:81
  assume (Heap[Current, MY_ITERATOR.after]) == ((Heap[Current, MY_ITERATOR.index]) > (Heap[Heap[Current, MY_ITERATOR.target], MY_COLLECTION.count]));
  return;
  a2:
  assume user_inv(Heap, Current);
  assert admissibility2(Heap, Current); // type:A2
  return;
  a3:
  assume user_inv(Heap, Current);
  assert admissibility3(Heap, Current); // type:A3
  return;
}

procedure create.MY_ITERATOR.make(Current: ref, t: ref);
  free requires attached_exact(Heap, Current, MY_ITERATOR); // info:type property for argument Current
  free requires detachable_exact(Heap, t, MY_COLLECTION); // info:type property for argument t
  modifies Heap;
  requires (t) != (Void); // type:pre tag:target_exists line:17
  ensures (Heap[Current, MY_ITERATOR.target]) == (t); // type:post tag:target_set line:27
  ensures (Heap[Current, MY_ITERATOR.before]) && (!(Heap[Current, MY_ITERATOR.after])); // type:post tag:before line:28
  ensures (t) != (Void); // type:attached tag:observing_target line:29
  ensures Set#Equal(Heap[t, observers], Set#Extended(old(Heap)[t, observers], Current)); // type:post tag:observing_target line:29
  ensures (fun.MY_COLLECTION.capacity(Heap, t)) == (fun.MY_COLLECTION.capacity(old(Heap), t)); // type:post tag:capacity_unchanged line:30
  requires (forall <T3> $f: Field T3 :: (($f) != (allocated)) ==> ((Heap[Current, $f]) == (Default($f))));
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.MY_ITERATOR.make(Heap, Current, t), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.MY_ITERATOR.make(old(Heap), Current, t));
  free ensures HeapSucc(old(Heap), Heap);
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts
  requires is_wrapped(Heap, t); // type:pre tag:arg_t_is_wrapped default:contracts
  ensures is_wrapped(Heap, t); // type:post tag:arg_t_is_wrapped default:contracts



implementation create.MY_ITERATOR.make(Current: ref, t: ref)
{
  entry:
  assume {:captureState "create.MY_ITERATOR.make"} true;
  // /home/caf/temp/comcom/repo-iterator/my_iterator.e:21
  // target := t
  call update_heap(Current, MY_ITERATOR.target, t); // line:21
  // /home/caf/temp/comcom/repo-iterator/my_iterator.e:22
  // before := True
  call update_heap(Current, MY_ITERATOR.before, true); // line:22
  // /home/caf/temp/comcom/repo-iterator/my_iterator.e:23
  // t.unwrap
  assert {:subsumption 0} (t) != (Void); // type:attached line:23
  call unwrap(t); // line:23 cid:1 rid:57
  assume MY_COLLECTION.user_inv(Heap, t);
  // /home/caf/temp/comcom/repo-iterator/my_iterator.e:24
  // t.set_observers (t.observers & Current)
  assert {:subsumption 0} (t) != (Void); // type:attached line:24
  assert {:subsumption 0} (t) != (Void); // type:attached line:24
  call update_heap(t, observers, Set#Extended(Heap[t, observers], Current)); // line:24
  // /home/caf/temp/comcom/repo-iterator/my_iterator.e:25
  // t.wrap
  assert {:subsumption 0} (t) != (Void); // type:attached line:25
  if (modify.MY_ITERATOR.make(Heap, Current, t)[t, owns]) {
    call update_heap(t, owns, MY_COLLECTION.owns.static(Heap, t)); // default:owns line:25
  }
  if (*) {
    assert (Heap[t, MY_COLLECTION.elements]) != (Void); // type:inv line:25 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#Equal(Heap[t, owns], Set#Singleton(Heap[t, MY_COLLECTION.elements])); // type:inv line:25 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert ((0) <= (Heap[t, MY_COLLECTION.count])) && ((Heap[t, MY_COLLECTION.count]) <= (Seq#Length(Heap[Heap[t, MY_COLLECTION.elements], SIMPLE_ARRAY^INTEGER_32^.sequence]))); // type:inv line:25 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert (forall i_2: ref :: (Heap[t, observers][i_2]) ==> (((i_2) != (Void)) && ((i_2) != (t)))); // type:inv line:25 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[t, subjects]); // type:inv tag:default_subjects line:25 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert admissibility2(Heap, t); // type:inv tag:A2 line:25 cid:1 rid:55
    assume false;
  }
  call wrap(t); // line:25 cid:1 rid:55
  if (modify.MY_ITERATOR.make(Heap, Current, t)[Current, subjects]) {
    call update_heap(Current, subjects, MY_ITERATOR.subjects.static(Heap, Current)); // default:subjects line:31
  }
  if (*) {
    assert (Heap[Current, MY_ITERATOR.target]) != (Void); // type:inv tag:target_exists line:68 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#Equal(Heap[Current, subjects], Set#Singleton(Heap[Current, MY_ITERATOR.target])); // type:inv tag:subjects_structure line:68 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert ((0) <= (Heap[Current, MY_ITERATOR.index])) && ((Heap[Current, MY_ITERATOR.index]) <= ((Heap[Heap[Current, MY_ITERATOR.target], MY_COLLECTION.count]) + (1))); // type:inv tag:index_in_bounds line:68 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert (Heap[Current, MY_ITERATOR.before]) == ((Heap[Current, MY_ITERATOR.index]) < (1)); // type:inv tag:before_definition line:68 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert (Heap[Current, MY_ITERATOR.after]) == ((Heap[Current, MY_ITERATOR.index]) > (Heap[Heap[Current, MY_ITERATOR.target], MY_COLLECTION.count])); // type:inv tag:after_definition line:68 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, observers]); // type:inv tag:default_observers line:68 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, owns]); // type:inv tag:default_owns line:68 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert admissibility2(Heap, Current); // type:inv tag:A2 line:68 cid:1 rid:55
    assume false;
  }
  call wrap(Current); // default:wrapping cid:1 rid:55 line:31
}

function { :inline } MY_COLLECTION.user_inv(heap: HeapType, current: ref) returns (bool) {
  ((heap[current, MY_COLLECTION.elements]) != (Void)) && (Set#Equal(heap[current, owns], Set#Singleton(heap[current, MY_COLLECTION.elements]))) && ((0) <= (heap[current, MY_COLLECTION.count])) && ((heap[current, MY_COLLECTION.count]) <= (Seq#Length(heap[heap[current, MY_COLLECTION.elements], SIMPLE_ARRAY^INTEGER_32^.sequence]))) && ((forall i_1: ref :: (heap[current, observers][i_1]) ==> (((i_1) != (Void)) && ((i_1) != (current))))) && (Set#IsEmpty(heap[current, subjects])) && (admissibility2(heap, current))
}

function MY_COLLECTION.owns.static(heap: HeapType, current: ref) returns (Set (ref)) {
  Set#Singleton(heap[current, MY_COLLECTION.elements])
}

procedure MY_ITERATOR.item(Current: ref) returns (Result: int where is_integer_32(Result));
  free requires attached_exact(Heap, Current, MY_ITERATOR); // info:type property for argument Current
  modifies Heap;
  requires !((Heap[Current, MY_ITERATOR.before]) || (Heap[Current, MY_ITERATOR.after])); // type:pre tag:not_off line:47
  requires (Heap[Current, MY_ITERATOR.target]) != (Void); // type:attached tag:target_closed line:48
  requires is_closed(Heap, Heap[Current, MY_ITERATOR.target]); // type:pre tag:target_closed line:48
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.MY_ITERATOR.item(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.MY_ITERATOR.item(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.MY_ITERATOR.item(Heap, Current), readable);
  requires is_closed(Heap, Current); // type:pre tag:default_is_closed default:contracts
  free ensures (Result) == (fun.MY_ITERATOR.item(old(Heap), Current));



function fun.MY_ITERATOR.item(heap: HeapType, current: ref) returns (int);

axiom ((forall heap: HeapType, current: ref :: { fun.MY_ITERATOR.item(heap, current) } (pre.fun.MY_ITERATOR.item(heap, current)) ==> (is_integer_32(fun.MY_ITERATOR.item(heap, current)))));

axiom ((forall h: HeapType, h': HeapType, current: ref :: { HeapSucc(h, h'), fun.MY_ITERATOR.item(h, current), fun.MY_ITERATOR.item(h', current) } ((HeapSucc(h, h')) && (pre.fun.MY_ITERATOR.item(h, current)) && (pre.fun.MY_ITERATOR.item(h', current)) && (same_inside(h, h', read.fun.MY_ITERATOR.item(h, current)))) ==> ((fun.MY_ITERATOR.item(h, current)) == (fun.MY_ITERATOR.item(h', current)))));

function { :inline } variant.MY_ITERATOR.item.1(heap: HeapType, current: ref) returns (int) {
  0
}

implementation MY_ITERATOR.item(Current: ref) returns (Result: int)
{
  var temp_3: int;

  init_locals:
  temp_3 := 0;
  Result := 0;

  entry:
  assume {:captureState "MY_ITERATOR.item"} true;
  // /home/caf/temp/comcom/repo-iterator/my_iterator.e:50
  // Result := target.elements [index]
  assert readable[Current, MY_ITERATOR.target]; // type:access tag:attribute_readable line:50 cid:404 rid:5409
  assert {:subsumption 0} (Heap[Current, MY_ITERATOR.target]) != (Void); // type:attached line:50
  assert readable[Heap[Current, MY_ITERATOR.target], MY_COLLECTION.elements]; // type:access tag:attribute_readable line:50 cid:406 rid:5406
  assert {:subsumption 0} (Heap[Heap[Current, MY_ITERATOR.target], MY_COLLECTION.elements]) != (Void); // type:attached line:50
  assert readable[Current, MY_ITERATOR.index]; // type:access tag:attribute_readable line:50 cid:404 rid:5414
  assert Frame#Subset(read.fun.SIMPLE_ARRAY^INTEGER_32^.item(Heap, Heap[Heap[Current, MY_ITERATOR.target], MY_COLLECTION.elements], Heap[Current, MY_ITERATOR.index]), readable); // type:access tag:frame_readable line:50 cid:190 rid:3250
  call temp_3 := SIMPLE_ARRAY^INTEGER_32^.item(Heap[Heap[Current, MY_ITERATOR.target], MY_COLLECTION.elements], Heap[Current, MY_ITERATOR.index]); // line:50 cid:190 rid:3250
  Result := temp_3;
}

procedure MY_ITERATOR.forth(Current: ref);
  free requires attached_exact(Heap, Current, MY_ITERATOR); // info:type property for argument Current
  modifies Heap;
  requires !(Heap[Current, MY_ITERATOR.after]); // type:pre tag:not_after line:58
  ensures !(Heap[Current, MY_ITERATOR.before]); // type:post tag:not_before line:66
  ensures (Heap[Current, MY_ITERATOR.target]) == (old(Heap)[Current, MY_ITERATOR.target]); // type:post tag:target_unchanged line:67
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.MY_ITERATOR.forth(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.MY_ITERATOR.forth(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);
  requires is_wrapped(Heap, Current); // type:pre tag:default_is_wrapped default:contracts
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts



function { :inline } variant.MY_ITERATOR.forth.1(heap: HeapType, current: ref) returns (int) {
  0
}

implementation MY_ITERATOR.forth(Current: ref)
{
  entry:
  assume {:captureState "MY_ITERATOR.forth"} true;
  call unwrap(Current); // default:wrapping cid:1 rid:57 line:55
  assume MY_ITERATOR.user_inv(Heap, Current);
  // /home/caf/temp/comcom/repo-iterator/my_iterator.e:60
  // index := index + 1
  call update_heap(Current, MY_ITERATOR.index, (Heap[Current, MY_ITERATOR.index]) + (1)); // line:60
  // /home/caf/temp/comcom/repo-iterator/my_iterator.e:61
  // before := False
  call update_heap(Current, MY_ITERATOR.before, false); // line:61
  // /home/caf/temp/comcom/repo-iterator/my_iterator.e:62
  // if index > target.count then
  assert {:subsumption 0} (Heap[Current, MY_ITERATOR.target]) != (Void); // type:attached line:62
  if ((Heap[Current, MY_ITERATOR.index]) > (Heap[Heap[Current, MY_ITERATOR.target], MY_COLLECTION.count])) {
    // /home/caf/temp/comcom/repo-iterator/my_iterator.e:63
    // after := True
    call update_heap(Current, MY_ITERATOR.after, true); // line:63
  }
  if (modify.MY_ITERATOR.forth(Heap, Current)[Current, subjects]) {
    call update_heap(Current, subjects, MY_ITERATOR.subjects.static(Heap, Current)); // default:subjects line:68
  }
  if (*) {
    assert (Heap[Current, MY_ITERATOR.target]) != (Void); // type:inv tag:target_exists line:68 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#Equal(Heap[Current, subjects], Set#Singleton(Heap[Current, MY_ITERATOR.target])); // type:inv tag:subjects_structure line:68 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert ((0) <= (Heap[Current, MY_ITERATOR.index])) && ((Heap[Current, MY_ITERATOR.index]) <= ((Heap[Heap[Current, MY_ITERATOR.target], MY_COLLECTION.count]) + (1))); // type:inv tag:index_in_bounds line:68 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert (Heap[Current, MY_ITERATOR.before]) == ((Heap[Current, MY_ITERATOR.index]) < (1)); // type:inv tag:before_definition line:68 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert (Heap[Current, MY_ITERATOR.after]) == ((Heap[Current, MY_ITERATOR.index]) > (Heap[Heap[Current, MY_ITERATOR.target], MY_COLLECTION.count])); // type:inv tag:after_definition line:68 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, observers]); // type:inv tag:default_observers line:68 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, owns]); // type:inv tag:default_owns line:68 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert admissibility2(Heap, Current); // type:inv tag:A2 line:68 cid:1 rid:55
    assume false;
  }
  call wrap(Current); // default:wrapping cid:1 rid:55 line:68
}

const unique MY_COLLECTION: Type;

axiom (is_frozen(MY_COLLECTION));

axiom ((MY_COLLECTION) <: (ANY));

axiom ((forall t: Type :: { (MY_COLLECTION) <: (t) } ((MY_COLLECTION) <: (t)) <==> (((t) == (MY_COLLECTION)) || ((ANY) <: (t)))));

axiom ((FieldId(allocated, MY_COLLECTION)) == (-1));

axiom ((FieldId(closed, MY_COLLECTION)) == (-2));

axiom ((FieldId(owner, MY_COLLECTION)) == (-3));

axiom ((FieldId(owns, MY_COLLECTION)) == (-4));

axiom ((FieldId(observers, MY_COLLECTION)) == (-5));

axiom ((FieldId(subjects, MY_COLLECTION)) == (-6));

axiom ((forall <T4> $f: Field T4 :: { IsModelField($f, MY_COLLECTION) } (IsModelField($f, MY_COLLECTION)) <==> ((($f) == (subjects)) || (($f) == (observers)))));

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached_exact(heap, current, MY_COLLECTION)) ==> ((user_inv(heap, current)) <==> (MY_COLLECTION.user_inv(heap, current)))));

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached(heap, current, MY_COLLECTION)) ==> ((user_inv(heap, current)) ==> (MY_COLLECTION.user_inv(heap, current)))));

procedure MY_COLLECTION.invariant_admissibility_check(Current: ref);
  requires attached_exact(Heap, Current, MY_COLLECTION);



implementation MY_COLLECTION.invariant_admissibility_check(Current: ref)
{
  entry:
  goto pre, a2, a3;
  pre:
  assert user_inv_readable(Heap, Current)[Current, MY_COLLECTION.elements]; // type:access tag:attribute_readable line:86 cid:406 fid:85
  assume (Heap[Current, MY_COLLECTION.elements]) != (Void);
  assert user_inv_readable(Heap, Current)[Current, MY_COLLECTION.elements]; // type:access tag:attribute_readable line:87 cid:406 fid:85
  assume Set#Equal(Heap[Current, owns], Set#Singleton(Heap[Current, MY_COLLECTION.elements]));
  assert user_inv_readable(Heap, Current)[Current, MY_COLLECTION.count]; // type:access tag:attribute_readable line:88 cid:406 fid:81
  assert user_inv_readable(Heap, Current)[Current, MY_COLLECTION.count]; // type:access tag:attribute_readable line:88 cid:406 fid:81
  assert user_inv_readable(Heap, Current)[Current, MY_COLLECTION.elements]; // type:access tag:attribute_readable line:88 cid:406 fid:85
  assert {:subsumption 0} (Heap[Current, MY_COLLECTION.elements]) != (Void); // type:attached line:88
  assert user_inv_readable(Heap, Current)[Heap[Current, MY_COLLECTION.elements], SIMPLE_ARRAY^INTEGER_32^.sequence]; // type:access tag:attribute_readable line:88 cid:190 fid:84
  assume ((0) <= (Heap[Current, MY_COLLECTION.count])) && ((Heap[Current, MY_COLLECTION.count]) <= (Seq#Length(Heap[Heap[Current, MY_COLLECTION.elements], SIMPLE_ARRAY^INTEGER_32^.sequence])));
  assume (forall i_4: ref :: (Heap[Current, observers][i_4]) ==> (((i_4) != (Void)) && ((i_4) != (Current))));
  return;
  a2:
  assume user_inv(Heap, Current);
  assert admissibility2(Heap, Current); // type:A2
  return;
  a3:
  assume user_inv(Heap, Current);
  assert admissibility3(Heap, Current); // type:A3
  return;
}

procedure create.MY_COLLECTION.make(Current: ref, c: int);
  free requires attached_exact(Heap, Current, MY_COLLECTION); // info:type property for argument Current
  free requires is_integer_32(c); // info:type property for argument c
  modifies Heap;
  requires (c) >= (0); // type:pre tag:capacity_non_negative line:17
  ensures (fun.MY_COLLECTION.capacity(Heap, Current)) == (c); // type:post tag:capacity_set line:21
  ensures (Heap[Current, MY_COLLECTION.count]) == (0); // type:post tag:empty line:22
  ensures Set#Equal(Heap[Current, observers], Set#Empty()); // type:post tag:no_observers line:23
  requires (forall <T5> $f: Field T5 :: (($f) != (allocated)) ==> ((Heap[Current, $f]) == (Default($f))));
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.MY_COLLECTION.make(Heap, Current, c), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.MY_COLLECTION.make(old(Heap), Current, c));
  free ensures HeapSucc(old(Heap), Heap);
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts



implementation create.MY_COLLECTION.make(Current: ref, c: int)
{
  var temp_5: ref;

  init_locals:
  temp_5 := Void;

  entry:
  assume {:captureState "create.MY_COLLECTION.make"} true;
  // /home/caf/temp/comcom/repo-iterator/my_collection.e:19
  // create elements.make (c)
  call temp_5 := allocate(SIMPLE_ARRAY^INTEGER_32^); // line:-1
  call create.SIMPLE_ARRAY^INTEGER_32^.make(temp_5, c); // line:19 cid:190 rid:3245
  call update_heap(Current, MY_COLLECTION.elements, temp_5); // line:19
  if (modify.MY_COLLECTION.make(Heap, Current, c)[Current, owns]) {
    call update_heap(Current, owns, MY_COLLECTION.owns.static(Heap, Current)); // default:owns line:24
  }
  if (*) {
    assert (Heap[Current, MY_COLLECTION.elements]) != (Void); // type:inv line:78 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#Equal(Heap[Current, owns], Set#Singleton(Heap[Current, MY_COLLECTION.elements])); // type:inv line:78 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert ((0) <= (Heap[Current, MY_COLLECTION.count])) && ((Heap[Current, MY_COLLECTION.count]) <= (Seq#Length(Heap[Heap[Current, MY_COLLECTION.elements], SIMPLE_ARRAY^INTEGER_32^.sequence]))); // type:inv line:78 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert (forall i_6: ref :: (Heap[Current, observers][i_6]) ==> (((i_6) != (Void)) && ((i_6) != (Current)))); // type:inv line:78 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, subjects]); // type:inv tag:default_subjects line:78 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert admissibility2(Heap, Current); // type:inv tag:A2 line:78 cid:1 rid:55
    assume false;
  }
  call wrap(Current); // default:wrapping cid:1 rid:55 line:24
}

procedure MY_COLLECTION.capacity(Current: ref) returns (Result: int where is_integer_32(Result));
  free requires attached_exact(Heap, Current, MY_COLLECTION); // info:type property for argument Current
  modifies Heap;
  ensures (Heap[Current, MY_COLLECTION.elements]) != (Void); // type:attached line:36
  ensures (Result) == (Seq#Length(Heap[Heap[Current, MY_COLLECTION.elements], SIMPLE_ARRAY^INTEGER_32^.sequence])); // type:post line:36
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.MY_COLLECTION.capacity(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.MY_COLLECTION.capacity(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.MY_COLLECTION.capacity(Heap, Current), readable);
  requires is_closed(Heap, Current); // type:pre tag:default_is_closed default:contracts
  free ensures (Result) == (fun.MY_COLLECTION.capacity(old(Heap), Current));



function fun.MY_COLLECTION.capacity(heap: HeapType, current: ref) returns (int);

axiom ((forall heap: HeapType, current: ref :: { fun.MY_COLLECTION.capacity(heap, current) } (pre.fun.MY_COLLECTION.capacity(heap, current)) ==> (((fun.MY_COLLECTION.capacity(heap, current)) == (Seq#Length(heap[heap[current, MY_COLLECTION.elements], SIMPLE_ARRAY^INTEGER_32^.sequence]))) && (is_integer_32(fun.MY_COLLECTION.capacity(heap, current))))));

axiom ((forall h: HeapType, h': HeapType, current: ref :: { HeapSucc(h, h'), fun.MY_COLLECTION.capacity(h, current), fun.MY_COLLECTION.capacity(h', current) } ((HeapSucc(h, h')) && (pre.fun.MY_COLLECTION.capacity(h, current)) && (pre.fun.MY_COLLECTION.capacity(h', current)) && (same_inside(h, h', read.fun.MY_COLLECTION.capacity(h, current)))) ==> ((fun.MY_COLLECTION.capacity(h, current)) == (fun.MY_COLLECTION.capacity(h', current)))));

function { :inline } variant.MY_COLLECTION.capacity.1(heap: HeapType, current: ref) returns (int) {
  0
}

implementation MY_COLLECTION.capacity(Current: ref) returns (Result: int)
{

  init_locals:
  Result := 0;

  entry:
  assume {:captureState "MY_COLLECTION.capacity"} true;
  // /home/caf/temp/comcom/repo-iterator/my_collection.e:34
  // Result := elements.count
  assert readable[Current, MY_COLLECTION.elements]; // type:access tag:attribute_readable line:34 cid:406 rid:5406
  assert {:subsumption 0} (Heap[Current, MY_COLLECTION.elements]) != (Void); // type:attached line:34
  assert pre.fun.SIMPLE_ARRAY^INTEGER_32^.count(Heap, Heap[Current, MY_COLLECTION.elements]); // type:check tag:function_precondition line:34 cid:190 rid:3249
  assert Frame#Subset(read.fun.SIMPLE_ARRAY^INTEGER_32^.count(Heap, Heap[Current, MY_COLLECTION.elements]), readable); // type:access tag:frame_readable line:34 cid:190 rid:3249
  Result := fun.SIMPLE_ARRAY^INTEGER_32^.count(Heap, Heap[Current, MY_COLLECTION.elements]);
}

procedure MY_COLLECTION.add(Current: ref, v: int);
  free requires attached_exact(Heap, Current, MY_COLLECTION); // info:type property for argument Current
  free requires is_integer_32(v); // info:type property for argument v
  modifies Heap;
  requires (forall i_7: ref :: (Heap[Current, observers][i_7]) ==> (is_wrapped(Heap, i_7))); // type:pre tag:observers_wrapped line:44
  requires (Heap[Current, MY_COLLECTION.count]) < (fun.MY_COLLECTION.capacity(Heap, Current)); // type:pre tag:not_full line:45
  ensures (Heap[Current, MY_COLLECTION.count]) == ((old(Heap)[Current, MY_COLLECTION.count]) + (1)); // type:post tag:count_increased line:54
  ensures Set#Equal(Heap[Current, observers], Set#Empty()); // type:post tag:no_observers line:55
  ensures (forall i_8: ref :: (old(Heap)[Current, observers][i_8]) ==> (is_open(Heap, i_8))); // type:post tag:old_observers_open line:56
  ensures (Heap[Current, MY_COLLECTION.elements]) == (old(Heap)[Current, MY_COLLECTION.elements]); // type:post tag:elements_unchanged line:57
  ensures (fun.MY_COLLECTION.capacity(Heap, Current)) == (fun.MY_COLLECTION.capacity(old(Heap), Current)); // type:post tag:capacity_unchanged line:58
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.MY_COLLECTION.add(Heap, Current, v), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.MY_COLLECTION.add(old(Heap), Current, v));
  free ensures HeapSucc(old(Heap), Heap);
  requires is_wrapped(Heap, Current); // type:pre tag:default_is_wrapped default:contracts
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts



function { :inline } variant.MY_COLLECTION.add.1(heap: HeapType, current: ref, v: int) returns (int) {
  v
}

implementation MY_COLLECTION.add(Current: ref, v: int)
{
  entry:
  assume {:captureState "MY_COLLECTION.add"} true;
  call unwrap(Current); // default:wrapping cid:1 rid:57 line:41
  assume MY_COLLECTION.user_inv(Heap, Current);
  // /home/caf/temp/comcom/repo-iterator/my_collection.e:49
  // unwrap_all (observers)
  call unwrap_all(Current, Heap[Current, observers]); // line:49 cid:1 rid:59
  // /home/caf/temp/comcom/repo-iterator/my_collection.e:50
  // set_observers ([])
  call update_heap(Current, observers, Set#Empty()); // line:50
  // /home/caf/temp/comcom/repo-iterator/my_collection.e:51
  // count := count + 1
  call update_heap(Current, MY_COLLECTION.count, (Heap[Current, MY_COLLECTION.count]) + (1)); // line:51
  // /home/caf/temp/comcom/repo-iterator/my_collection.e:52
  // elements.put (v, count)
  assert {:subsumption 0} (Heap[Current, MY_COLLECTION.elements]) != (Void); // type:attached line:52
  call SIMPLE_ARRAY^INTEGER_32^.put(Heap[Current, MY_COLLECTION.elements], v, Heap[Current, MY_COLLECTION.count]); // line:52 cid:190 rid:3254
  if (modify.MY_COLLECTION.add(Heap, Current, v)[Current, owns]) {
    call update_heap(Current, owns, MY_COLLECTION.owns.static(Heap, Current)); // default:owns line:59
  }
  if (*) {
    assert (Heap[Current, MY_COLLECTION.elements]) != (Void); // type:inv line:78 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#Equal(Heap[Current, owns], Set#Singleton(Heap[Current, MY_COLLECTION.elements])); // type:inv line:78 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert ((0) <= (Heap[Current, MY_COLLECTION.count])) && ((Heap[Current, MY_COLLECTION.count]) <= (Seq#Length(Heap[Heap[Current, MY_COLLECTION.elements], SIMPLE_ARRAY^INTEGER_32^.sequence]))); // type:inv line:78 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert (forall i_6: ref :: (Heap[Current, observers][i_6]) ==> (((i_6) != (Void)) && ((i_6) != (Current)))); // type:inv line:78 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, subjects]); // type:inv tag:default_subjects line:78 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert admissibility2(Heap, Current); // type:inv tag:A2 line:78 cid:1 rid:55
    assume false;
  }
  call wrap(Current); // default:wrapping cid:1 rid:55 line:59
}

procedure MY_COLLECTION.remove_last(Current: ref);
  free requires attached_exact(Heap, Current, MY_COLLECTION); // info:type property for argument Current
  modifies Heap;
  requires (forall i_9: ref :: (Heap[Current, observers][i_9]) ==> (is_wrapped(Heap, i_9))); // type:pre tag:observers_wrapped line:64
  requires (Heap[Current, MY_COLLECTION.count]) > (0); // type:pre tag:not_empty line:65
  ensures (Heap[Current, MY_COLLECTION.count]) == ((old(Heap)[Current, MY_COLLECTION.count]) - (1)); // type:post tag:count_decreased line:73
  ensures Set#Equal(Heap[Current, observers], Set#Empty()); // type:post tag:no_observers line:74
  ensures (forall i_10: ref :: (old(Heap)[Current, observers][i_10]) ==> (is_open(Heap, i_10))); // type:post tag:old_observers_open line:75
  ensures (Heap[Current, MY_COLLECTION.elements]) == (old(Heap)[Current, MY_COLLECTION.elements]); // type:post tag:elements_unchanged line:76
  ensures (fun.MY_COLLECTION.capacity(Heap, Current)) == (fun.MY_COLLECTION.capacity(old(Heap), Current)); // type:post tag:capacity_unchanged line:77
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.MY_COLLECTION.remove_last(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.MY_COLLECTION.remove_last(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);
  requires is_wrapped(Heap, Current); // type:pre tag:default_is_wrapped default:contracts
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts



function { :inline } variant.MY_COLLECTION.remove_last.1(heap: HeapType, current: ref) returns (int) {
  0
}

implementation MY_COLLECTION.remove_last(Current: ref)
{
  entry:
  assume {:captureState "MY_COLLECTION.remove_last"} true;
  call unwrap(Current); // default:wrapping cid:1 rid:57 line:61
  assume MY_COLLECTION.user_inv(Heap, Current);
  // /home/caf/temp/comcom/repo-iterator/my_collection.e:69
  // unwrap_all (observers)
  call unwrap_all(Current, Heap[Current, observers]); // line:69 cid:1 rid:59
  // /home/caf/temp/comcom/repo-iterator/my_collection.e:70
  // set_observers ([])
  call update_heap(Current, observers, Set#Empty()); // line:70
  // /home/caf/temp/comcom/repo-iterator/my_collection.e:71
  // count := count - 1
  call update_heap(Current, MY_COLLECTION.count, (Heap[Current, MY_COLLECTION.count]) - (1)); // line:71
  if (modify.MY_COLLECTION.remove_last(Heap, Current)[Current, owns]) {
    call update_heap(Current, owns, MY_COLLECTION.owns.static(Heap, Current)); // default:owns line:78
  }
  if (*) {
    assert (Heap[Current, MY_COLLECTION.elements]) != (Void); // type:inv line:78 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#Equal(Heap[Current, owns], Set#Singleton(Heap[Current, MY_COLLECTION.elements])); // type:inv line:78 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert ((0) <= (Heap[Current, MY_COLLECTION.count])) && ((Heap[Current, MY_COLLECTION.count]) <= (Seq#Length(Heap[Heap[Current, MY_COLLECTION.elements], SIMPLE_ARRAY^INTEGER_32^.sequence]))); // type:inv line:78 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert (forall i_6: ref :: (Heap[Current, observers][i_6]) ==> (((i_6) != (Void)) && ((i_6) != (Current)))); // type:inv line:78 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, subjects]); // type:inv tag:default_subjects line:78 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert admissibility2(Heap, Current); // type:inv tag:A2 line:78 cid:1 rid:55
    assume false;
  }
  call wrap(Current); // default:wrapping cid:1 rid:55 line:78
}

const unique CLIENT: Type;

axiom ((CLIENT) <: (ANY));

axiom ((forall t: Type :: { (CLIENT) <: (t) } ((CLIENT) <: (t)) <==> (((t) == (CLIENT)) || ((ANY) <: (t)))));

axiom ((FieldId(allocated, CLIENT)) == (-1));

axiom ((FieldId(closed, CLIENT)) == (-2));

axiom ((FieldId(owner, CLIENT)) == (-3));

axiom ((FieldId(owns, CLIENT)) == (-4));

axiom ((FieldId(observers, CLIENT)) == (-5));

axiom ((FieldId(subjects, CLIENT)) == (-6));

axiom ((forall <T6> $f: Field T6 :: { IsModelField($f, CLIENT) } (IsModelField($f, CLIENT)) <==> ((($f) == (subjects)) || (($f) == (observers)))));

function { :inline } CLIENT.user_inv(heap: HeapType, current: ref) returns (bool) {
  (Set#IsEmpty(heap[current, observers])) && (Set#IsEmpty(heap[current, subjects])) && (Set#IsEmpty(heap[current, owns])) && (admissibility2(heap, current))
}

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached_exact(heap, current, CLIENT)) ==> ((user_inv(heap, current)) <==> (CLIENT.user_inv(heap, current)))));

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached(heap, current, CLIENT)) ==> ((user_inv(heap, current)) ==> (CLIENT.user_inv(heap, current)))));

procedure CLIENT.invariant_admissibility_check(Current: ref);
  requires attached_exact(Heap, Current, CLIENT);



implementation CLIENT.invariant_admissibility_check(Current: ref)
{
  entry:
  goto pre, a2, a3;
  pre:
  return;
  a2:
  assume user_inv(Heap, Current);
  assert admissibility2(Heap, Current); // type:A2
  return;
  a3:
  assume user_inv(Heap, Current);
  assert admissibility3(Heap, Current); // type:A3
  return;
}

procedure create.CLIENT.default_create(Current: ref);
  free requires attached_exact(Heap, Current, CLIENT); // info:type property for argument Current
  modifies Heap;
  requires (forall <T7> $f: Field T7 :: (($f) != (allocated)) ==> ((Heap[Current, $f]) == (Default($f))));
  ensures (forall <T8> $f: Field T8 :: ((($f) != (allocated)) && (($f) != (closed))) ==> ((Heap[Current, $f]) == (Default($f))));
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.CLIENT.default_create(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.CLIENT.default_create(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts



implementation create.CLIENT.default_create(Current: ref)
{
  entry:
  assume {:captureState "create.CLIENT.default_create"} true;
  if (*) {
    assert Set#IsEmpty(Heap[Current, observers]); // type:inv tag:default_observers line:40 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, subjects]); // type:inv tag:default_subjects line:40 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, owns]); // type:inv tag:default_owns line:40 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert admissibility2(Heap, Current); // type:inv tag:A2 line:40 cid:1 rid:55
    assume false;
  }
  call wrap(Current); // default:wrapping cid:1 rid:55 line:364
}

procedure CLIENT.test(Current: ref);
  free requires attached_exact(Heap, Current, CLIENT); // info:type property for argument Current
  modifies Heap;
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.CLIENT.test(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.CLIENT.test(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);
  requires is_wrapped(Heap, Current); // type:pre tag:default_is_wrapped default:contracts
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts



function { :inline } variant.CLIENT.test.1(heap: HeapType, current: ref) returns (int) {
  0
}

implementation CLIENT.test(Current: ref)
{
  var temp_11: ref;
  var temp_12: ref;
  var temp_13: int;
  var temp_14: ref;
  var temp_15: int;
  var temp_16: ref;
  var local1: ref where detachable_exact(Heap, local1, MY_COLLECTION);
  var local2: ref where detachable(Heap, local2, MY_ITERATOR);
  var local3: ref where detachable(Heap, local3, MY_ITERATOR);
  var local4: int where is_integer_32(local4);

  init_locals:
  temp_11 := Void;
  temp_12 := Void;
  temp_13 := 0;
  temp_14 := Void;
  temp_15 := 0;
  temp_16 := Void;
  local1 := Void;
  local2 := Void;
  local3 := Void;
  local4 := 0;

  entry:
  assume {:captureState "CLIENT.test"} true;
  call unwrap(Current); // default:wrapping cid:1 rid:57 line:9
  assume CLIENT.user_inv(Heap, Current);
  // /home/caf/temp/comcom/repo-iterator/client.e:16
  // create c.make (10)
  call temp_11 := allocate(MY_COLLECTION); // line:-1
  call create.MY_COLLECTION.make(temp_11, 10); // line:16 cid:406 rid:5401
  local1 := temp_11;
  // /home/caf/temp/comcom/repo-iterator/client.e:17
  // c.add (1)
  assert {:subsumption 0} (local1) != (Void); // type:attached line:17
  call MY_COLLECTION.add(local1, 1); // line:17 cid:406 rid:5404
  // /home/caf/temp/comcom/repo-iterator/client.e:18
  // c.add (2)
  assert {:subsumption 0} (local1) != (Void); // type:attached line:18
  call MY_COLLECTION.add(local1, 2); // line:18 cid:406 rid:5404
  // /home/caf/temp/comcom/repo-iterator/client.e:20
  // create i1.make (c)
  call temp_12 := allocate(MY_ITERATOR); // line:-1
  call create.MY_ITERATOR.make(temp_12, local1); // line:20 cid:404 rid:5408
  local2 := temp_12;
  // /home/caf/temp/comcom/repo-iterator/client.e:21
  // i1.forth
  assert {:subsumption 0} (local2) != (Void); // type:attached line:21
  call MY_ITERATOR.forth(local2); // line:21 cid:404 rid:5413
  // /home/caf/temp/comcom/repo-iterator/client.e:22
  // if not i1.after then
  assert {:subsumption 0} (local2) != (Void); // type:attached line:22
  if (!(Heap[local2, MY_ITERATOR.after])) {
    // /home/caf/temp/comcom/repo-iterator/client.e:23
    // v := i1.item
    assert {:subsumption 0} (local2) != (Void); // type:attached line:23
    call temp_13 := MY_ITERATOR.item(local2); // line:23 cid:404 rid:5412
    local4 := temp_13;
  }
  // /home/caf/temp/comcom/repo-iterator/client.e:26
  // create i2.make (c)
  call temp_14 := allocate(MY_ITERATOR); // line:-1
  call create.MY_ITERATOR.make(temp_14, local1); // line:26 cid:404 rid:5408
  local3 := temp_14;
  // /home/caf/temp/comcom/repo-iterator/client.e:27
  // i2.forth
  assert {:subsumption 0} (local3) != (Void); // type:attached line:27
  call MY_ITERATOR.forth(local3); // line:27 cid:404 rid:5413
  // /home/caf/temp/comcom/repo-iterator/client.e:28
  // if not i2.after then
  assert {:subsumption 0} (local3) != (Void); // type:attached line:28
  if (!(Heap[local3, MY_ITERATOR.after])) {
    // /home/caf/temp/comcom/repo-iterator/client.e:29
    // v := i2.item
    assert {:subsumption 0} (local3) != (Void); // type:attached line:29
    call temp_15 := MY_ITERATOR.item(local3); // line:29 cid:404 rid:5412
    local4 := temp_15;
  }
  // /home/caf/temp/comcom/repo-iterator/client.e:32
  // c.remove_last
  assert {:subsumption 0} (local1) != (Void); // type:attached line:32
  call MY_COLLECTION.remove_last(local1); // line:32 cid:406 rid:5405
  // /home/caf/temp/comcom/repo-iterator/client.e:36
  // create i1.make (c)
  call temp_16 := allocate(MY_ITERATOR); // line:-1
  call create.MY_ITERATOR.make(temp_16, local1); // line:36 cid:404 rid:5408
  local2 := temp_16;
  // /home/caf/temp/comcom/repo-iterator/client.e:37
  // if not i1.after then
  assert {:subsumption 0} (local2) != (Void); // type:attached line:37
  if (!(Heap[local2, MY_ITERATOR.after])) {
    // /home/caf/temp/comcom/repo-iterator/client.e:38
    // i1.forth
    assert {:subsumption 0} (local2) != (Void); // type:attached line:38
    call MY_ITERATOR.forth(local2); // line:38 cid:404 rid:5413
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, observers]); // type:inv tag:default_observers line:40 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, subjects]); // type:inv tag:default_subjects line:40 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, owns]); // type:inv tag:default_owns line:40 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert admissibility2(Heap, Current); // type:inv tag:A2 line:40 cid:1 rid:55
    assume false;
  }
  call wrap(Current); // default:wrapping cid:1 rid:55 line:40
}

const MY_ITERATOR.target: Field (ref);

axiom ((FieldId(MY_ITERATOR.target, MY_ITERATOR)) == (81));

axiom ((forall heap: HeapType, o: ref :: { heap[o, MY_ITERATOR.target] } ((IsHeap(heap)) && (attached(heap, o, MY_ITERATOR))) ==> (detachable_exact(heap, heap[o, MY_ITERATOR.target], MY_COLLECTION))));

axiom ((forall heap: HeapType, current: ref, v: ref, o: ref :: { guard(heap, current, MY_ITERATOR.target, v, o) } (attached_exact(heap, current, MY_ITERATOR)) ==> ((guard(heap, current, MY_ITERATOR.target, v, o)) <==> ((user_inv(heap, o)) ==> (user_inv(heap[current, MY_ITERATOR.target := v], o))))));

axiom ((forall heap: HeapType, current: ref, v: ref, o: ref :: { guard(heap, current, MY_ITERATOR.target, v, o) } (attached(heap, current, MY_ITERATOR)) ==> ((guard(heap, current, MY_ITERATOR.target, v, o)) ==> ((user_inv(heap, o)) ==> (user_inv(heap[current, MY_ITERATOR.target := v], o))))));

const MY_ITERATOR.index: Field int;

axiom ((FieldId(MY_ITERATOR.index, MY_ITERATOR)) == (86));

axiom ((forall heap: HeapType, o: ref :: { heap[o, MY_ITERATOR.index] } ((IsHeap(heap)) && (attached(heap, o, MY_ITERATOR))) ==> (is_integer_32(heap[o, MY_ITERATOR.index]))));

axiom ((forall heap: HeapType, current: ref, v: int, o: ref :: { guard(heap, current, MY_ITERATOR.index, v, o) } (attached_exact(heap, current, MY_ITERATOR)) ==> ((guard(heap, current, MY_ITERATOR.index, v, o)) <==> ((user_inv(heap, o)) ==> (user_inv(heap[current, MY_ITERATOR.index := v], o))))));

axiom ((forall heap: HeapType, current: ref, v: int, o: ref :: { guard(heap, current, MY_ITERATOR.index, v, o) } (attached(heap, current, MY_ITERATOR)) ==> ((guard(heap, current, MY_ITERATOR.index, v, o)) ==> ((user_inv(heap, o)) ==> (user_inv(heap[current, MY_ITERATOR.index := v], o))))));

const MY_COLLECTION.count: Field int;

axiom ((FieldId(MY_COLLECTION.count, MY_COLLECTION)) == (81));

axiom ((forall heap: HeapType, o: ref :: { heap[o, MY_COLLECTION.count] } ((IsHeap(heap)) && (attached(heap, o, MY_COLLECTION))) ==> (is_integer_32(heap[o, MY_COLLECTION.count]))));

axiom ((forall heap: HeapType, current: ref, v: int, o: ref :: { guard(heap, current, MY_COLLECTION.count, v, o) } (attached_exact(heap, current, MY_COLLECTION)) ==> ((guard(heap, current, MY_COLLECTION.count, v, o)) <==> ((user_inv(heap, o)) ==> (user_inv(heap[current, MY_COLLECTION.count := v], o))))));

axiom ((forall heap: HeapType, current: ref, v: int, o: ref :: { guard(heap, current, MY_COLLECTION.count, v, o) } (attached(heap, current, MY_COLLECTION)) ==> ((guard(heap, current, MY_COLLECTION.count, v, o)) ==> ((user_inv(heap, o)) ==> (user_inv(heap[current, MY_COLLECTION.count := v], o))))));

const MY_ITERATOR.before: Field bool;

axiom ((FieldId(MY_ITERATOR.before, MY_ITERATOR)) == (82));

axiom ((forall heap: HeapType, current: ref, v: bool, o: ref :: { guard(heap, current, MY_ITERATOR.before, v, o) } (attached_exact(heap, current, MY_ITERATOR)) ==> ((guard(heap, current, MY_ITERATOR.before, v, o)) <==> ((user_inv(heap, o)) ==> (user_inv(heap[current, MY_ITERATOR.before := v], o))))));

axiom ((forall heap: HeapType, current: ref, v: bool, o: ref :: { guard(heap, current, MY_ITERATOR.before, v, o) } (attached(heap, current, MY_ITERATOR)) ==> ((guard(heap, current, MY_ITERATOR.before, v, o)) ==> ((user_inv(heap, o)) ==> (user_inv(heap[current, MY_ITERATOR.before := v], o))))));

const MY_ITERATOR.after: Field bool;

axiom ((FieldId(MY_ITERATOR.after, MY_ITERATOR)) == (83));

axiom ((forall heap: HeapType, current: ref, v: bool, o: ref :: { guard(heap, current, MY_ITERATOR.after, v, o) } (attached_exact(heap, current, MY_ITERATOR)) ==> ((guard(heap, current, MY_ITERATOR.after, v, o)) <==> ((user_inv(heap, o)) ==> (user_inv(heap[current, MY_ITERATOR.after := v], o))))));

axiom ((forall heap: HeapType, current: ref, v: bool, o: ref :: { guard(heap, current, MY_ITERATOR.after, v, o) } (attached(heap, current, MY_ITERATOR)) ==> ((guard(heap, current, MY_ITERATOR.after, v, o)) ==> ((user_inv(heap, o)) ==> (user_inv(heap[current, MY_ITERATOR.after := v], o))))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, owns, v, o) } (attached_exact(heap, current, ANY)) ==> ((guard(heap, current, owns, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, subjects, v, o) } (attached_exact(heap, current, ANY)) ==> ((guard(heap, current, subjects, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached_exact(heap, current, ANY)) ==> ((guard(heap, current, observers, v, o)) <==> (fun.ANY.in_observers(heap, current, v, o)))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached(heap, current, ANY)) ==> ((guard(heap, current, observers, v, o)) ==> (fun.ANY.in_observers(heap, current, v, o)))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, owns, v, o) } (attached_exact(heap, current, MY_ITERATOR)) ==> ((guard(heap, current, owns, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, subjects, v, o) } (attached_exact(heap, current, MY_ITERATOR)) ==> ((guard(heap, current, subjects, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached_exact(heap, current, MY_ITERATOR)) ==> ((guard(heap, current, observers, v, o)) <==> (fun.MY_ITERATOR.in_observers(heap, current, v, o)))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached(heap, current, MY_ITERATOR)) ==> ((guard(heap, current, observers, v, o)) ==> (fun.MY_ITERATOR.in_observers(heap, current, v, o)))));

function modify.MY_ITERATOR.make(heap: HeapType, current: ref, t: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, t: ref :: (IsHeap(heap)) ==> ((forall <T9> $o: ref, $f: Field T9 :: { modify.MY_ITERATOR.make(heap, current, t)[$o, $f] } (modify.MY_ITERATOR.make(heap, current, t)[$o, $f]) <==> (((($o) == (t)) && ((($f) == (observers)) || (($f) == (closed)))) || (($o) == (current)))))));

const MY_COLLECTION.elements: Field (ref);

axiom ((FieldId(MY_COLLECTION.elements, MY_COLLECTION)) == (85));

axiom ((forall heap: HeapType, o: ref :: { heap[o, MY_COLLECTION.elements] } ((IsHeap(heap)) && (attached(heap, o, MY_COLLECTION))) ==> (detachable_exact(heap, heap[o, MY_COLLECTION.elements], SIMPLE_ARRAY^INTEGER_32^))));

axiom ((forall heap: HeapType, current: ref, v: ref, o: ref :: { guard(heap, current, MY_COLLECTION.elements, v, o) } (attached_exact(heap, current, MY_COLLECTION)) ==> ((guard(heap, current, MY_COLLECTION.elements, v, o)) <==> ((user_inv(heap, o)) ==> (user_inv(heap[current, MY_COLLECTION.elements := v], o))))));

axiom ((forall heap: HeapType, current: ref, v: ref, o: ref :: { guard(heap, current, MY_COLLECTION.elements, v, o) } (attached(heap, current, MY_COLLECTION)) ==> ((guard(heap, current, MY_COLLECTION.elements, v, o)) ==> ((user_inv(heap, o)) ==> (user_inv(heap[current, MY_COLLECTION.elements := v], o))))));

const SIMPLE_ARRAY^INTEGER_32^.sequence: Field (Seq int);

axiom ((FieldId(SIMPLE_ARRAY^INTEGER_32^.sequence, SIMPLE_ARRAY^INTEGER_32^)) == (84));

axiom ((forall heap: HeapType, current: ref, v: Seq int, o: ref :: { guard(heap, current, SIMPLE_ARRAY^INTEGER_32^.sequence, v, o) } (attached_exact(heap, current, SIMPLE_ARRAY^INTEGER_32^)) ==> ((guard(heap, current, SIMPLE_ARRAY^INTEGER_32^.sequence, v, o)) <==> ((user_inv(heap, o)) ==> (user_inv(heap[current, SIMPLE_ARRAY^INTEGER_32^.sequence := v], o))))));

axiom ((forall heap: HeapType, current: ref, v: Seq int, o: ref :: { guard(heap, current, SIMPLE_ARRAY^INTEGER_32^.sequence, v, o) } (attached(heap, current, SIMPLE_ARRAY^INTEGER_32^)) ==> ((guard(heap, current, SIMPLE_ARRAY^INTEGER_32^.sequence, v, o)) ==> ((user_inv(heap, o)) ==> (user_inv(heap[current, SIMPLE_ARRAY^INTEGER_32^.sequence := v], o))))));

function modify.MY_ITERATOR.item(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T10> $o: ref, $f: Field T10 :: { modify.MY_ITERATOR.item(heap, current)[$o, $f] } (modify.MY_ITERATOR.item(heap, current)[$o, $f]) <==> (false)))));

function read.fun.MY_ITERATOR.item(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T11> $o: ref, $f: Field T11 :: { read.fun.MY_ITERATOR.item(heap, current)[$o, $f] } (read.fun.MY_ITERATOR.item(heap, current)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.MY_ITERATOR.item(heap: HeapType, current: ref) returns (bool) {
  (!((heap[current, MY_ITERATOR.before]) || (heap[current, MY_ITERATOR.after]))) && (is_closed(heap, heap[current, MY_ITERATOR.target])) && (is_closed(heap, current))
}

function trigger.fun.MY_ITERATOR.item(heap: HeapType, current: ref) returns (bool);

procedure SIMPLE_ARRAY^INTEGER_32^.item(Current: ref, i: int) returns (Result: int where is_integer_32(Result));
  free requires attached_exact(Heap, Current, SIMPLE_ARRAY^INTEGER_32^); // info:type property for argument Current
  free requires is_integer_32(i); // info:type property for argument i
  modifies Heap;
  requires pre.fun.SIMPLE_ARRAY^INTEGER_32^.count(Heap, Current); // type:check tag:function_precondition line:83 cid:190 rid:3249
  requires ((1) <= (i)) && ((i) <= (fun.SIMPLE_ARRAY^INTEGER_32^.count(Heap, Current))); // type:pre tag:in_bounds line:83
  requires pre.fun.SIMPLE_ARRAY^INTEGER_32^.valid_index(Heap, Current, i); // type:check tag:function_precondition line:84 cid:190 rid:3253
  requires fun.SIMPLE_ARRAY^INTEGER_32^.valid_index(Heap, Current, i); // type:pre tag:valid_index line:84
  ensures pre.fun.MML_SEQUENCE^INTEGER_32^.item(Heap[Current, SIMPLE_ARRAY^INTEGER_32^.sequence], i); // type:check tag:function_precondition line:89 cid:125 rid:3286
  ensures (Result) == (Seq#Item(Heap[Current, SIMPLE_ARRAY^INTEGER_32^.sequence], i)); // type:post tag:definition line:89
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.SIMPLE_ARRAY^INTEGER_32^.item(Heap, Current, i), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.SIMPLE_ARRAY^INTEGER_32^.item(old(Heap), Current, i));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.SIMPLE_ARRAY^INTEGER_32^.item(Heap, Current, i), readable);
  requires is_closed(Heap, Current); // type:pre tag:default_is_closed default:contracts
  free ensures (Result) == (fun.SIMPLE_ARRAY^INTEGER_32^.item(old(Heap), Current, i));



function fun.SIMPLE_ARRAY^INTEGER_32^.item(heap: HeapType, current: ref, i: int) returns (int);

axiom ((forall heap: HeapType, current: ref, i: int :: { fun.SIMPLE_ARRAY^INTEGER_32^.item(heap, current, i) } (pre.fun.SIMPLE_ARRAY^INTEGER_32^.item(heap, current, i)) ==> (((fun.SIMPLE_ARRAY^INTEGER_32^.item(heap, current, i)) == (Seq#Item(heap[current, SIMPLE_ARRAY^INTEGER_32^.sequence], i))) && (is_integer_32(fun.SIMPLE_ARRAY^INTEGER_32^.item(heap, current, i))))));

axiom ((forall h: HeapType, h': HeapType, current: ref, i: int :: { HeapSucc(h, h'), fun.SIMPLE_ARRAY^INTEGER_32^.item(h, current, i), fun.SIMPLE_ARRAY^INTEGER_32^.item(h', current, i) } ((HeapSucc(h, h')) && (pre.fun.SIMPLE_ARRAY^INTEGER_32^.item(h, current, i)) && (pre.fun.SIMPLE_ARRAY^INTEGER_32^.item(h', current, i)) && (same_inside(h, h', read.fun.SIMPLE_ARRAY^INTEGER_32^.item(h, current, i)))) ==> ((fun.SIMPLE_ARRAY^INTEGER_32^.item(h, current, i)) == (fun.SIMPLE_ARRAY^INTEGER_32^.item(h', current, i)))));

function modify.MY_ITERATOR.forth(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T12> $o: ref, $f: Field T12 :: { modify.MY_ITERATOR.forth(heap, current)[$o, $f] } (modify.MY_ITERATOR.forth(heap, current)[$o, $f]) <==> (($o) == (current))))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, owns, v, o) } (attached_exact(heap, current, MY_COLLECTION)) ==> ((guard(heap, current, owns, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, subjects, v, o) } (attached_exact(heap, current, MY_COLLECTION)) ==> ((guard(heap, current, subjects, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached_exact(heap, current, MY_COLLECTION)) ==> ((guard(heap, current, observers, v, o)) <==> (fun.MY_COLLECTION.in_observers(heap, current, v, o)))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached(heap, current, MY_COLLECTION)) ==> ((guard(heap, current, observers, v, o)) ==> (fun.MY_COLLECTION.in_observers(heap, current, v, o)))));

function modify.MY_COLLECTION.make(heap: HeapType, current: ref, c: int) returns (Frame);

axiom ((forall heap: HeapType, current: ref, c: int :: (IsHeap(heap)) ==> ((forall <T13> $o: ref, $f: Field T13 :: { modify.MY_COLLECTION.make(heap, current, c)[$o, $f] } (modify.MY_COLLECTION.make(heap, current, c)[$o, $f]) <==> (($o) == (current))))));

const unique SIMPLE_ARRAY^INTEGER_32^: Type;

axiom (is_frozen(SIMPLE_ARRAY^INTEGER_32^));

axiom ((SIMPLE_ARRAY^INTEGER_32^) <: (ITERABLE^INTEGER_32^));

axiom ((forall t: Type :: { (SIMPLE_ARRAY^INTEGER_32^) <: (t) } ((SIMPLE_ARRAY^INTEGER_32^) <: (t)) <==> (((t) == (SIMPLE_ARRAY^INTEGER_32^)) || ((ITERABLE^INTEGER_32^) <: (t)))));

axiom ((FieldId(allocated, SIMPLE_ARRAY^INTEGER_32^)) == (-1));

axiom ((FieldId(closed, SIMPLE_ARRAY^INTEGER_32^)) == (-2));

axiom ((FieldId(owner, SIMPLE_ARRAY^INTEGER_32^)) == (-3));

axiom ((FieldId(owns, SIMPLE_ARRAY^INTEGER_32^)) == (-4));

axiom ((FieldId(observers, SIMPLE_ARRAY^INTEGER_32^)) == (-5));

axiom ((FieldId(subjects, SIMPLE_ARRAY^INTEGER_32^)) == (-6));

axiom ((forall <T14> $f: Field T14 :: { IsModelField($f, SIMPLE_ARRAY^INTEGER_32^) } (IsModelField($f, SIMPLE_ARRAY^INTEGER_32^)) <==> ((($f) == (subjects)) || (($f) == (observers)))));

function { :inline } SIMPLE_ARRAY^INTEGER_32^.user_inv(heap: HeapType, current: ref) returns (bool) {
  ((fun.SIMPLE_ARRAY^INTEGER_32^.count(heap, current)) >= (0)) && ((fun.SIMPLE_ARRAY^INTEGER_32^.count(heap, current)) == (Seq#Length(heap[current, SIMPLE_ARRAY^INTEGER_32^.sequence]))) && (Set#IsEmpty(heap[current, observers])) && (Set#IsEmpty(heap[current, subjects])) && (Set#IsEmpty(heap[current, owns])) && (admissibility2(heap, current))
}

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached_exact(heap, current, SIMPLE_ARRAY^INTEGER_32^)) ==> ((user_inv(heap, current)) <==> (SIMPLE_ARRAY^INTEGER_32^.user_inv(heap, current)))));

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached(heap, current, SIMPLE_ARRAY^INTEGER_32^)) ==> ((user_inv(heap, current)) ==> (SIMPLE_ARRAY^INTEGER_32^.user_inv(heap, current)))));

procedure create.SIMPLE_ARRAY^INTEGER_32^.make(Current: ref, n: int);
  free requires attached_exact(Heap, Current, SIMPLE_ARRAY^INTEGER_32^); // info:type property for argument Current
  free requires is_integer_32(n); // info:type property for argument n
  modifies Heap;
  requires (n) >= (0); // type:pre tag:n_non_negative line:32
  ensures pre.fun.SIMPLE_ARRAY^INTEGER_32^.count(Heap, Current); // type:check tag:function_precondition line:36 cid:190 rid:3249
  ensures (fun.SIMPLE_ARRAY^INTEGER_32^.count(Heap, Current)) == (n); // type:post tag:count_set line:36
  ensures (forall i_17: int :: (Seq#Domain(Heap[Current, SIMPLE_ARRAY^INTEGER_32^.sequence])[i_17]) ==> (pre.fun.MML_SEQUENCE^INTEGER_32^.item(Heap[Current, SIMPLE_ARRAY^INTEGER_32^.sequence], i_17))); // type:check tag:function_precondition line:37 cid:125 rid:3286
  ensures (forall i_17: int :: (Seq#Domain(Heap[Current, SIMPLE_ARRAY^INTEGER_32^.sequence])[i_17]) ==> ((Seq#Item(Heap[Current, SIMPLE_ARRAY^INTEGER_32^.sequence], i_17)) == (0))); // type:post tag:all_default line:37
  requires (forall <T15> $f: Field T15 :: (($f) != (allocated)) ==> ((Heap[Current, $f]) == (Default($f))));
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.SIMPLE_ARRAY^INTEGER_32^.make(Heap, Current, n), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.SIMPLE_ARRAY^INTEGER_32^.make(old(Heap), Current, n));
  free ensures HeapSucc(old(Heap), Heap);
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts



function modify.MY_COLLECTION.capacity(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T16> $o: ref, $f: Field T16 :: { modify.MY_COLLECTION.capacity(heap, current)[$o, $f] } (modify.MY_COLLECTION.capacity(heap, current)[$o, $f]) <==> (false)))));

function read.fun.MY_COLLECTION.capacity(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T17> $o: ref, $f: Field T17 :: { read.fun.MY_COLLECTION.capacity(heap, current)[$o, $f] } (read.fun.MY_COLLECTION.capacity(heap, current)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.MY_COLLECTION.capacity(heap: HeapType, current: ref) returns (bool) {
  is_closed(heap, current)
}

function trigger.fun.MY_COLLECTION.capacity(heap: HeapType, current: ref) returns (bool);

procedure SIMPLE_ARRAY^INTEGER_32^.count(Current: ref) returns (Result: int where is_integer_32(Result));
  free requires attached_exact(Heap, Current, SIMPLE_ARRAY^INTEGER_32^); // info:type property for argument Current
  modifies Heap;
  ensures (Result) == (Seq#Length(Heap[Current, SIMPLE_ARRAY^INTEGER_32^.sequence])); // type:post tag:definition line:77
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.SIMPLE_ARRAY^INTEGER_32^.count(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.SIMPLE_ARRAY^INTEGER_32^.count(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.SIMPLE_ARRAY^INTEGER_32^.count(Heap, Current), readable);



function fun.SIMPLE_ARRAY^INTEGER_32^.count(heap: HeapType, current: ref) returns (int);

function fun0.SIMPLE_ARRAY^INTEGER_32^.count(heap: HeapType, current: ref) returns (int);

axiom ((forall heap: HeapType, current: ref :: { fun.SIMPLE_ARRAY^INTEGER_32^.count(heap, current) } (pre.fun.SIMPLE_ARRAY^INTEGER_32^.count(heap, current)) ==> (((fun.SIMPLE_ARRAY^INTEGER_32^.count(heap, current)) == (Seq#Length(heap[current, SIMPLE_ARRAY^INTEGER_32^.sequence]))) && (is_integer_32(fun.SIMPLE_ARRAY^INTEGER_32^.count(heap, current))))));

axiom ((forall heap: HeapType, current: ref :: { fun.SIMPLE_ARRAY^INTEGER_32^.count(heap, current) } { trigger.fun.SIMPLE_ARRAY^INTEGER_32^.count(heap, current) } (pre.fun.SIMPLE_ARRAY^INTEGER_32^.count(heap, current)) ==> ((fun.SIMPLE_ARRAY^INTEGER_32^.count(heap, current)) == (Seq#Length(heap[current, SIMPLE_ARRAY^INTEGER_32^.sequence])))));

axiom ((forall heap: HeapType, current: ref :: { fun.SIMPLE_ARRAY^INTEGER_32^.count(heap, current) } (fun.SIMPLE_ARRAY^INTEGER_32^.count(heap, current)) == (fun0.SIMPLE_ARRAY^INTEGER_32^.count(heap, current))));

axiom ((forall h: HeapType, h': HeapType, current: ref :: { HeapSucc(h, h'), fun0.SIMPLE_ARRAY^INTEGER_32^.count(h, current), fun0.SIMPLE_ARRAY^INTEGER_32^.count(h', current) } ((HeapSucc(h, h')) && (pre.fun.SIMPLE_ARRAY^INTEGER_32^.count(h, current)) && (pre.fun.SIMPLE_ARRAY^INTEGER_32^.count(h', current)) && (same_inside(h, h', read.fun.SIMPLE_ARRAY^INTEGER_32^.count(h, current)))) ==> ((fun0.SIMPLE_ARRAY^INTEGER_32^.count(h, current)) == (fun0.SIMPLE_ARRAY^INTEGER_32^.count(h', current)))));

function modify.MY_COLLECTION.add(heap: HeapType, current: ref, v: int) returns (Frame);

axiom ((forall heap: HeapType, current: ref, v: int :: (IsHeap(heap)) ==> ((forall <T18> $o: ref, $f: Field T18 :: { modify.MY_COLLECTION.add(heap, current, v)[$o, $f] } (modify.MY_COLLECTION.add(heap, current, v)[$o, $f]) <==> (((heap[current, observers][$o]) && (($f) == (closed))) || (($o) == (current)))))));

procedure SIMPLE_ARRAY^INTEGER_32^.put(Current: ref, v: int, i: int);
  free requires attached_exact(Heap, Current, SIMPLE_ARRAY^INTEGER_32^); // info:type property for argument Current
  free requires is_integer_32(v); // info:type property for argument v
  free requires is_integer_32(i); // info:type property for argument i
  modifies Heap;
  requires pre.fun.SIMPLE_ARRAY^INTEGER_32^.count(Heap, Current); // type:check tag:function_precondition line:141 cid:190 rid:3249
  requires ((1) <= (i)) && ((i) <= (fun.SIMPLE_ARRAY^INTEGER_32^.count(Heap, Current))); // type:pre tag:in_bounds line:141
  requires pre.fun.SIMPLE_ARRAY^INTEGER_32^.valid_index(Heap, Current, i); // type:check tag:function_precondition line:142 cid:190 rid:3253
  requires fun.SIMPLE_ARRAY^INTEGER_32^.valid_index(Heap, Current, i); // type:pre tag:valid_index line:142
  ensures pre.fun.SIMPLE_ARRAY^INTEGER_32^.count(Heap, Current); // type:check tag:function_precondition line:148 cid:190 rid:3249
  ensures pre.fun.SIMPLE_ARRAY^INTEGER_32^.count(old(Heap), Current); // type:check tag:function_precondition line:148 cid:190 rid:3249
  ensures (fun.SIMPLE_ARRAY^INTEGER_32^.count(Heap, Current)) == (fun.SIMPLE_ARRAY^INTEGER_32^.count(old(Heap), Current)); // type:post tag:same_count line:148
  ensures pre.fun.MML_SEQUENCE^INTEGER_32^.replaced_at(old(Heap)[Current, SIMPLE_ARRAY^INTEGER_32^.sequence], i, v); // type:check tag:function_precondition line:149 cid:125 rid:3308
  ensures Seq#Equal(Heap[Current, SIMPLE_ARRAY^INTEGER_32^.sequence], Seq#Update(old(Heap)[Current, SIMPLE_ARRAY^INTEGER_32^.sequence], i, v)); // type:post tag:sequence_effect line:149
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.SIMPLE_ARRAY^INTEGER_32^.put(Heap, Current, v, i), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.SIMPLE_ARRAY^INTEGER_32^.put(old(Heap), Current, v, i));
  free ensures HeapSucc(old(Heap), Heap);
  requires is_wrapped(Heap, Current); // type:pre tag:default_is_wrapped default:contracts
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts



function modify.MY_COLLECTION.remove_last(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T19> $o: ref, $f: Field T19 :: { modify.MY_COLLECTION.remove_last(heap, current)[$o, $f] } (modify.MY_COLLECTION.remove_last(heap, current)[$o, $f]) <==> (((heap[current, observers][$o]) && (($f) == (closed))) || (($o) == (current)))))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, owns, v, o) } (attached_exact(heap, current, CLIENT)) ==> ((guard(heap, current, owns, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, subjects, v, o) } (attached_exact(heap, current, CLIENT)) ==> ((guard(heap, current, subjects, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached_exact(heap, current, CLIENT)) ==> ((guard(heap, current, observers, v, o)) <==> (fun.CLIENT.in_observers(heap, current, v, o)))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached(heap, current, CLIENT)) ==> ((guard(heap, current, observers, v, o)) ==> (fun.CLIENT.in_observers(heap, current, v, o)))));

function modify.CLIENT.default_create(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T20> $o: ref, $f: Field T20 :: { modify.CLIENT.default_create(heap, current)[$o, $f] } (modify.CLIENT.default_create(heap, current)[$o, $f]) <==> (($o) == (current))))));

function modify.CLIENT.test(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T21> $o: ref, $f: Field T21 :: { modify.CLIENT.test(heap, current)[$o, $f] } (modify.CLIENT.test(heap, current)[$o, $f]) <==> (($o) == (current))))));

procedure ANY.in_observers(Current: ref, new_observers: Set (ref), o: ref) returns (Result: bool where true);
  free requires attached_exact(Heap, Current, ANY); // info:type property for argument Current
  free requires Set#ItemsType(Heap, new_observers, ANY); // info:type property for argument new_observers
  free requires Heap[o, allocated]; // info:type property for argument o
  modifies Heap;
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.ANY.in_observers(Heap, Current, new_observers, o), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.ANY.in_observers(old(Heap), Current, new_observers, o));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.ANY.in_observers(Heap, Current, new_observers, o), readable);



function fun.ANY.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function fun0.ANY.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.ANY.in_observers(heap, current, new_observers, o) } { trigger.fun.ANY.in_observers(heap, current, new_observers, o) } (pre.fun.ANY.in_observers(heap, current, new_observers, o)) ==> ((fun.ANY.in_observers(heap, current, new_observers, o)) == (new_observers[o]))));

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.ANY.in_observers(heap, current, new_observers, o) } (fun.ANY.in_observers(heap, current, new_observers, o)) == (fun0.ANY.in_observers(heap, current, new_observers, o))));

axiom ((forall h: HeapType, h': HeapType, current: ref, new_observers: Set (ref), o: ref :: { HeapSucc(h, h'), fun0.ANY.in_observers(h, current, new_observers, o), fun0.ANY.in_observers(h', current, new_observers, o) } ((HeapSucc(h, h')) && (pre.fun.ANY.in_observers(h, current, new_observers, o)) && (pre.fun.ANY.in_observers(h', current, new_observers, o)) && (same_inside(h, h', read.fun.ANY.in_observers(h, current, new_observers, o)))) ==> ((fun0.ANY.in_observers(h, current, new_observers, o)) == (fun0.ANY.in_observers(h', current, new_observers, o)))));

procedure MY_ITERATOR.in_observers(Current: ref, new_observers: Set (ref), o: ref) returns (Result: bool where true);
  free requires attached_exact(Heap, Current, MY_ITERATOR); // info:type property for argument Current
  free requires Set#ItemsType(Heap, new_observers, ANY); // info:type property for argument new_observers
  free requires Heap[o, allocated]; // info:type property for argument o
  modifies Heap;
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.MY_ITERATOR.in_observers(Heap, Current, new_observers, o), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.MY_ITERATOR.in_observers(old(Heap), Current, new_observers, o));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.MY_ITERATOR.in_observers(Heap, Current, new_observers, o), readable);



function fun.MY_ITERATOR.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function fun0.MY_ITERATOR.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.MY_ITERATOR.in_observers(heap, current, new_observers, o) } { trigger.fun.MY_ITERATOR.in_observers(heap, current, new_observers, o) } (pre.fun.MY_ITERATOR.in_observers(heap, current, new_observers, o)) ==> ((fun.MY_ITERATOR.in_observers(heap, current, new_observers, o)) == (new_observers[o]))));

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.MY_ITERATOR.in_observers(heap, current, new_observers, o) } (fun.MY_ITERATOR.in_observers(heap, current, new_observers, o)) == (fun0.MY_ITERATOR.in_observers(heap, current, new_observers, o))));

axiom ((forall h: HeapType, h': HeapType, current: ref, new_observers: Set (ref), o: ref :: { HeapSucc(h, h'), fun0.MY_ITERATOR.in_observers(h, current, new_observers, o), fun0.MY_ITERATOR.in_observers(h', current, new_observers, o) } ((HeapSucc(h, h')) && (pre.fun.MY_ITERATOR.in_observers(h, current, new_observers, o)) && (pre.fun.MY_ITERATOR.in_observers(h', current, new_observers, o)) && (same_inside(h, h', read.fun.MY_ITERATOR.in_observers(h, current, new_observers, o)))) ==> ((fun0.MY_ITERATOR.in_observers(h, current, new_observers, o)) == (fun0.MY_ITERATOR.in_observers(h', current, new_observers, o)))));

procedure SIMPLE_ARRAY^INTEGER_32^.valid_index(Current: ref, i: int) returns (Result: bool where true);
  free requires attached_exact(Heap, Current, SIMPLE_ARRAY^INTEGER_32^); // info:type property for argument Current
  free requires is_integer_32(i); // info:type property for argument i
  modifies Heap;
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.SIMPLE_ARRAY^INTEGER_32^.valid_index(Heap, Current, i), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.SIMPLE_ARRAY^INTEGER_32^.valid_index(old(Heap), Current, i));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.SIMPLE_ARRAY^INTEGER_32^.valid_index(Heap, Current, i), readable);



function fun.SIMPLE_ARRAY^INTEGER_32^.valid_index(heap: HeapType, current: ref, i: int) returns (bool);

function fun0.SIMPLE_ARRAY^INTEGER_32^.valid_index(heap: HeapType, current: ref, i: int) returns (bool);

axiom ((forall heap: HeapType, current: ref, i: int :: { fun.SIMPLE_ARRAY^INTEGER_32^.valid_index(heap, current, i) } { trigger.fun.SIMPLE_ARRAY^INTEGER_32^.valid_index(heap, current, i) } (pre.fun.SIMPLE_ARRAY^INTEGER_32^.valid_index(heap, current, i)) ==> ((fun.SIMPLE_ARRAY^INTEGER_32^.valid_index(heap, current, i)) == (((1) <= (i)) && ((i) <= (Seq#Length(heap[current, SIMPLE_ARRAY^INTEGER_32^.sequence])))))));

axiom ((forall heap: HeapType, current: ref, i: int :: { fun.SIMPLE_ARRAY^INTEGER_32^.valid_index(heap, current, i) } (fun.SIMPLE_ARRAY^INTEGER_32^.valid_index(heap, current, i)) == (fun0.SIMPLE_ARRAY^INTEGER_32^.valid_index(heap, current, i))));

axiom ((forall h: HeapType, h': HeapType, current: ref, i: int :: { HeapSucc(h, h'), fun0.SIMPLE_ARRAY^INTEGER_32^.valid_index(h, current, i), fun0.SIMPLE_ARRAY^INTEGER_32^.valid_index(h', current, i) } ((HeapSucc(h, h')) && (pre.fun.SIMPLE_ARRAY^INTEGER_32^.valid_index(h, current, i)) && (pre.fun.SIMPLE_ARRAY^INTEGER_32^.valid_index(h', current, i)) && (same_inside(h, h', read.fun.SIMPLE_ARRAY^INTEGER_32^.valid_index(h, current, i)))) ==> ((fun0.SIMPLE_ARRAY^INTEGER_32^.valid_index(h, current, i)) == (fun0.SIMPLE_ARRAY^INTEGER_32^.valid_index(h', current, i)))));

function modify.SIMPLE_ARRAY^INTEGER_32^.item(heap: HeapType, current: ref, i: int) returns (Frame);

axiom ((forall heap: HeapType, current: ref, i: int :: (IsHeap(heap)) ==> ((forall <T22> $o: ref, $f: Field T22 :: { modify.SIMPLE_ARRAY^INTEGER_32^.item(heap, current, i)[$o, $f] } (modify.SIMPLE_ARRAY^INTEGER_32^.item(heap, current, i)[$o, $f]) <==> (false)))));

function read.fun.SIMPLE_ARRAY^INTEGER_32^.item(heap: HeapType, current: ref, i: int) returns (Frame);

axiom ((forall heap: HeapType, current: ref, i: int :: (IsHeap(heap)) ==> ((forall <T23> $o: ref, $f: Field T23 :: { read.fun.SIMPLE_ARRAY^INTEGER_32^.item(heap, current, i)[$o, $f] } (read.fun.SIMPLE_ARRAY^INTEGER_32^.item(heap, current, i)[$o, $f]) <==> ((($o) == (current)) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.SIMPLE_ARRAY^INTEGER_32^.item(heap: HeapType, current: ref, i: int) returns (bool) {
  ((1) <= (i)) && ((i) <= (fun.SIMPLE_ARRAY^INTEGER_32^.count(heap, current))) && (fun.SIMPLE_ARRAY^INTEGER_32^.valid_index(heap, current, i)) && (is_closed(heap, current))
}

function trigger.fun.SIMPLE_ARRAY^INTEGER_32^.item(heap: HeapType, current: ref, i: int) returns (bool);

procedure MY_COLLECTION.in_observers(Current: ref, new_observers: Set (ref), o: ref) returns (Result: bool where true);
  free requires attached_exact(Heap, Current, MY_COLLECTION); // info:type property for argument Current
  free requires Set#ItemsType(Heap, new_observers, ANY); // info:type property for argument new_observers
  free requires Heap[o, allocated]; // info:type property for argument o
  modifies Heap;
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.MY_COLLECTION.in_observers(Heap, Current, new_observers, o), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.MY_COLLECTION.in_observers(old(Heap), Current, new_observers, o));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.MY_COLLECTION.in_observers(Heap, Current, new_observers, o), readable);



function fun.MY_COLLECTION.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function fun0.MY_COLLECTION.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.MY_COLLECTION.in_observers(heap, current, new_observers, o) } { trigger.fun.MY_COLLECTION.in_observers(heap, current, new_observers, o) } (pre.fun.MY_COLLECTION.in_observers(heap, current, new_observers, o)) ==> ((fun.MY_COLLECTION.in_observers(heap, current, new_observers, o)) == (new_observers[o]))));

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.MY_COLLECTION.in_observers(heap, current, new_observers, o) } (fun.MY_COLLECTION.in_observers(heap, current, new_observers, o)) == (fun0.MY_COLLECTION.in_observers(heap, current, new_observers, o))));

axiom ((forall h: HeapType, h': HeapType, current: ref, new_observers: Set (ref), o: ref :: { HeapSucc(h, h'), fun0.MY_COLLECTION.in_observers(h, current, new_observers, o), fun0.MY_COLLECTION.in_observers(h', current, new_observers, o) } ((HeapSucc(h, h')) && (pre.fun.MY_COLLECTION.in_observers(h, current, new_observers, o)) && (pre.fun.MY_COLLECTION.in_observers(h', current, new_observers, o)) && (same_inside(h, h', read.fun.MY_COLLECTION.in_observers(h, current, new_observers, o)))) ==> ((fun0.MY_COLLECTION.in_observers(h, current, new_observers, o)) == (fun0.MY_COLLECTION.in_observers(h', current, new_observers, o)))));

const unique ITERABLE^INTEGER_32^: Type;

axiom ((ITERABLE^INTEGER_32^) <: (ANY));

axiom ((forall t: Type :: { (ITERABLE^INTEGER_32^) <: (t) } ((ITERABLE^INTEGER_32^) <: (t)) <==> (((t) == (ITERABLE^INTEGER_32^)) || ((ANY) <: (t)))));

axiom ((FieldId(allocated, ITERABLE^INTEGER_32^)) == (-1));

axiom ((FieldId(closed, ITERABLE^INTEGER_32^)) == (-2));

axiom ((FieldId(owner, ITERABLE^INTEGER_32^)) == (-3));

axiom ((FieldId(owns, ITERABLE^INTEGER_32^)) == (-4));

axiom ((FieldId(observers, ITERABLE^INTEGER_32^)) == (-5));

axiom ((FieldId(subjects, ITERABLE^INTEGER_32^)) == (-6));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, owns, v, o) } (attached_exact(heap, current, SIMPLE_ARRAY^INTEGER_32^)) ==> ((guard(heap, current, owns, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, subjects, v, o) } (attached_exact(heap, current, SIMPLE_ARRAY^INTEGER_32^)) ==> ((guard(heap, current, subjects, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached_exact(heap, current, SIMPLE_ARRAY^INTEGER_32^)) ==> ((guard(heap, current, observers, v, o)) <==> (fun.SIMPLE_ARRAY^INTEGER_32^.in_observers(heap, current, v, o)))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached(heap, current, SIMPLE_ARRAY^INTEGER_32^)) ==> ((guard(heap, current, observers, v, o)) ==> (fun.SIMPLE_ARRAY^INTEGER_32^.in_observers(heap, current, v, o)))));

function modify.SIMPLE_ARRAY^INTEGER_32^.make(heap: HeapType, current: ref, n: int) returns (Frame);

axiom ((forall heap: HeapType, current: ref, n: int :: (IsHeap(heap)) ==> ((forall <T24> $o: ref, $f: Field T24 :: { modify.SIMPLE_ARRAY^INTEGER_32^.make(heap, current, n)[$o, $f] } (modify.SIMPLE_ARRAY^INTEGER_32^.make(heap, current, n)[$o, $f]) <==> (($o) == (current))))));

function modify.SIMPLE_ARRAY^INTEGER_32^.count(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T25> $o: ref, $f: Field T25 :: { modify.SIMPLE_ARRAY^INTEGER_32^.count(heap, current)[$o, $f] } (modify.SIMPLE_ARRAY^INTEGER_32^.count(heap, current)[$o, $f]) <==> (false)))));

function read.fun.SIMPLE_ARRAY^INTEGER_32^.count(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T26> $o: ref, $f: Field T26 :: { read.fun.SIMPLE_ARRAY^INTEGER_32^.count(heap, current)[$o, $f] } (read.fun.SIMPLE_ARRAY^INTEGER_32^.count(heap, current)[$o, $f]) <==> ((($o) == (current)) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.SIMPLE_ARRAY^INTEGER_32^.count(heap: HeapType, current: ref) returns (bool) {
  true
}

function trigger.fun.SIMPLE_ARRAY^INTEGER_32^.count(heap: HeapType, current: ref) returns (bool);

function modify.SIMPLE_ARRAY^INTEGER_32^.put(heap: HeapType, current: ref, v: int, i: int) returns (Frame);

axiom ((forall heap: HeapType, current: ref, v: int, i: int :: (IsHeap(heap)) ==> ((forall <T27> $o: ref, $f: Field T27 :: { modify.SIMPLE_ARRAY^INTEGER_32^.put(heap, current, v, i)[$o, $f] } (modify.SIMPLE_ARRAY^INTEGER_32^.put(heap, current, v, i)[$o, $f]) <==> (($o) == (current))))));

procedure CLIENT.in_observers(Current: ref, new_observers: Set (ref), o: ref) returns (Result: bool where true);
  free requires attached_exact(Heap, Current, CLIENT); // info:type property for argument Current
  free requires Set#ItemsType(Heap, new_observers, ANY); // info:type property for argument new_observers
  free requires Heap[o, allocated]; // info:type property for argument o
  modifies Heap;
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.CLIENT.in_observers(Heap, Current, new_observers, o), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.CLIENT.in_observers(old(Heap), Current, new_observers, o));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.CLIENT.in_observers(Heap, Current, new_observers, o), readable);



function fun.CLIENT.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function fun0.CLIENT.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.CLIENT.in_observers(heap, current, new_observers, o) } { trigger.fun.CLIENT.in_observers(heap, current, new_observers, o) } (pre.fun.CLIENT.in_observers(heap, current, new_observers, o)) ==> ((fun.CLIENT.in_observers(heap, current, new_observers, o)) == (new_observers[o]))));

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.CLIENT.in_observers(heap, current, new_observers, o) } (fun.CLIENT.in_observers(heap, current, new_observers, o)) == (fun0.CLIENT.in_observers(heap, current, new_observers, o))));

axiom ((forall h: HeapType, h': HeapType, current: ref, new_observers: Set (ref), o: ref :: { HeapSucc(h, h'), fun0.CLIENT.in_observers(h, current, new_observers, o), fun0.CLIENT.in_observers(h', current, new_observers, o) } ((HeapSucc(h, h')) && (pre.fun.CLIENT.in_observers(h, current, new_observers, o)) && (pre.fun.CLIENT.in_observers(h', current, new_observers, o)) && (same_inside(h, h', read.fun.CLIENT.in_observers(h, current, new_observers, o)))) ==> ((fun0.CLIENT.in_observers(h, current, new_observers, o)) == (fun0.CLIENT.in_observers(h', current, new_observers, o)))));

function modify.ANY.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T28> $o: ref, $f: Field T28 :: { modify.ANY.in_observers(heap, current, new_observers, o)[$o, $f] } (modify.ANY.in_observers(heap, current, new_observers, o)[$o, $f]) <==> (false)))));

function read.fun.ANY.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T29> $o: ref, $f: Field T29 :: { read.fun.ANY.in_observers(heap, current, new_observers, o)[$o, $f] } (read.fun.ANY.in_observers(heap, current, new_observers, o)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.ANY.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool) {
  true
}

function trigger.fun.ANY.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function modify.MY_ITERATOR.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T30> $o: ref, $f: Field T30 :: { modify.MY_ITERATOR.in_observers(heap, current, new_observers, o)[$o, $f] } (modify.MY_ITERATOR.in_observers(heap, current, new_observers, o)[$o, $f]) <==> (false)))));

function read.fun.MY_ITERATOR.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T31> $o: ref, $f: Field T31 :: { read.fun.MY_ITERATOR.in_observers(heap, current, new_observers, o)[$o, $f] } (read.fun.MY_ITERATOR.in_observers(heap, current, new_observers, o)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.MY_ITERATOR.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool) {
  true
}

function trigger.fun.MY_ITERATOR.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function modify.SIMPLE_ARRAY^INTEGER_32^.valid_index(heap: HeapType, current: ref, i: int) returns (Frame);

axiom ((forall heap: HeapType, current: ref, i: int :: (IsHeap(heap)) ==> ((forall <T32> $o: ref, $f: Field T32 :: { modify.SIMPLE_ARRAY^INTEGER_32^.valid_index(heap, current, i)[$o, $f] } (modify.SIMPLE_ARRAY^INTEGER_32^.valid_index(heap, current, i)[$o, $f]) <==> (false)))));

function read.fun.SIMPLE_ARRAY^INTEGER_32^.valid_index(heap: HeapType, current: ref, i: int) returns (Frame);

axiom ((forall heap: HeapType, current: ref, i: int :: (IsHeap(heap)) ==> ((forall <T33> $o: ref, $f: Field T33 :: { read.fun.SIMPLE_ARRAY^INTEGER_32^.valid_index(heap, current, i)[$o, $f] } (read.fun.SIMPLE_ARRAY^INTEGER_32^.valid_index(heap, current, i)[$o, $f]) <==> ((($o) == (current)) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.SIMPLE_ARRAY^INTEGER_32^.valid_index(heap: HeapType, current: ref, i: int) returns (bool) {
  true
}

function trigger.fun.SIMPLE_ARRAY^INTEGER_32^.valid_index(heap: HeapType, current: ref, i: int) returns (bool);

function pre.fun.MML_SEQUENCE^INTEGER_32^.item(current: Seq int, i: int) returns (bool) {
  ((1) <= (i)) && ((i) <= (Seq#Length(current)))
}

function trigger.fun.MML_SEQUENCE^INTEGER_32^.item(current: Seq int, i: int) returns (bool);

function modify.MY_COLLECTION.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T34> $o: ref, $f: Field T34 :: { modify.MY_COLLECTION.in_observers(heap, current, new_observers, o)[$o, $f] } (modify.MY_COLLECTION.in_observers(heap, current, new_observers, o)[$o, $f]) <==> (false)))));

function read.fun.MY_COLLECTION.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T35> $o: ref, $f: Field T35 :: { read.fun.MY_COLLECTION.in_observers(heap, current, new_observers, o)[$o, $f] } (read.fun.MY_COLLECTION.in_observers(heap, current, new_observers, o)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.MY_COLLECTION.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool) {
  true
}

function trigger.fun.MY_COLLECTION.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

procedure SIMPLE_ARRAY^INTEGER_32^.in_observers(Current: ref, new_observers: Set (ref), o: ref) returns (Result: bool where true);
  free requires attached_exact(Heap, Current, SIMPLE_ARRAY^INTEGER_32^); // info:type property for argument Current
  free requires Set#ItemsType(Heap, new_observers, ANY); // info:type property for argument new_observers
  free requires Heap[o, allocated]; // info:type property for argument o
  modifies Heap;
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.SIMPLE_ARRAY^INTEGER_32^.in_observers(Heap, Current, new_observers, o), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.SIMPLE_ARRAY^INTEGER_32^.in_observers(old(Heap), Current, new_observers, o));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.SIMPLE_ARRAY^INTEGER_32^.in_observers(Heap, Current, new_observers, o), readable);



function fun.SIMPLE_ARRAY^INTEGER_32^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function fun0.SIMPLE_ARRAY^INTEGER_32^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.SIMPLE_ARRAY^INTEGER_32^.in_observers(heap, current, new_observers, o) } { trigger.fun.SIMPLE_ARRAY^INTEGER_32^.in_observers(heap, current, new_observers, o) } (pre.fun.SIMPLE_ARRAY^INTEGER_32^.in_observers(heap, current, new_observers, o)) ==> ((fun.SIMPLE_ARRAY^INTEGER_32^.in_observers(heap, current, new_observers, o)) == (new_observers[o]))));

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.SIMPLE_ARRAY^INTEGER_32^.in_observers(heap, current, new_observers, o) } (fun.SIMPLE_ARRAY^INTEGER_32^.in_observers(heap, current, new_observers, o)) == (fun0.SIMPLE_ARRAY^INTEGER_32^.in_observers(heap, current, new_observers, o))));

axiom ((forall h: HeapType, h': HeapType, current: ref, new_observers: Set (ref), o: ref :: { HeapSucc(h, h'), fun0.SIMPLE_ARRAY^INTEGER_32^.in_observers(h, current, new_observers, o), fun0.SIMPLE_ARRAY^INTEGER_32^.in_observers(h', current, new_observers, o) } ((HeapSucc(h, h')) && (pre.fun.SIMPLE_ARRAY^INTEGER_32^.in_observers(h, current, new_observers, o)) && (pre.fun.SIMPLE_ARRAY^INTEGER_32^.in_observers(h', current, new_observers, o)) && (same_inside(h, h', read.fun.SIMPLE_ARRAY^INTEGER_32^.in_observers(h, current, new_observers, o)))) ==> ((fun0.SIMPLE_ARRAY^INTEGER_32^.in_observers(h, current, new_observers, o)) == (fun0.SIMPLE_ARRAY^INTEGER_32^.in_observers(h', current, new_observers, o)))));

function pre.fun.MML_SEQUENCE^INTEGER_32^.replaced_at(current: Seq int, i: int, x: int) returns (bool) {
  Seq#Domain(current)[i]
}

function trigger.fun.MML_SEQUENCE^INTEGER_32^.replaced_at(current: Seq int, i: int, x: int) returns (bool);

function modify.CLIENT.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T36> $o: ref, $f: Field T36 :: { modify.CLIENT.in_observers(heap, current, new_observers, o)[$o, $f] } (modify.CLIENT.in_observers(heap, current, new_observers, o)[$o, $f]) <==> (false)))));

function read.fun.CLIENT.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T37> $o: ref, $f: Field T37 :: { read.fun.CLIENT.in_observers(heap, current, new_observers, o)[$o, $f] } (read.fun.CLIENT.in_observers(heap, current, new_observers, o)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.CLIENT.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool) {
  true
}

function trigger.fun.CLIENT.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function modify.SIMPLE_ARRAY^INTEGER_32^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T38> $o: ref, $f: Field T38 :: { modify.SIMPLE_ARRAY^INTEGER_32^.in_observers(heap, current, new_observers, o)[$o, $f] } (modify.SIMPLE_ARRAY^INTEGER_32^.in_observers(heap, current, new_observers, o)[$o, $f]) <==> (false)))));

function read.fun.SIMPLE_ARRAY^INTEGER_32^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T39> $o: ref, $f: Field T39 :: { read.fun.SIMPLE_ARRAY^INTEGER_32^.in_observers(heap, current, new_observers, o)[$o, $f] } (read.fun.SIMPLE_ARRAY^INTEGER_32^.in_observers(heap, current, new_observers, o)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.SIMPLE_ARRAY^INTEGER_32^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool) {
  true
}

function trigger.fun.SIMPLE_ARRAY^INTEGER_32^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);
