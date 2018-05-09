// Automatically generated (12/12/2017 1:55:03.663 PM)

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

const unique HS_LOCK^HS_HASHABLE^: Type;

axiom (is_frozen(HS_LOCK^HS_HASHABLE^));

axiom ((HS_LOCK^HS_HASHABLE^) <: (ANY));

axiom ((forall t: Type :: { (HS_LOCK^HS_HASHABLE^) <: (t) } ((HS_LOCK^HS_HASHABLE^) <: (t)) <==> (((t) == (HS_LOCK^HS_HASHABLE^)) || ((ANY) <: (t)))));

axiom ((FieldId(allocated, HS_LOCK^HS_HASHABLE^)) == (-1));

axiom ((FieldId(closed, HS_LOCK^HS_HASHABLE^)) == (-2));

axiom ((FieldId(owner, HS_LOCK^HS_HASHABLE^)) == (-3));

axiom ((FieldId(owns, HS_LOCK^HS_HASHABLE^)) == (-4));

axiom ((FieldId(observers, HS_LOCK^HS_HASHABLE^)) == (-5));

axiom ((FieldId(subjects, HS_LOCK^HS_HASHABLE^)) == (-6));

axiom ((forall <T0> $f: Field T0 :: { IsModelField($f, HS_LOCK^HS_HASHABLE^) } (IsModelField($f, HS_LOCK^HS_HASHABLE^)) <==> ((($f) == (subjects)) || (($f) == (observers)))));

function { :inline } HS_LOCK^HS_HASHABLE^.user_inv(heap: HeapType, current: ref) returns (bool) {
  (Set#Equal(heap[current, subjects], heap[current, HS_LOCK^HS_HASHABLE^.sets])) && ((forall i_1: ref :: (heap[current, HS_LOCK^HS_HASHABLE^.sets][i_1]) ==> ((heap[i_1, HS_SET^HS_HASHABLE^.lock]) == (current)))) && ((forall i_2: ref :: (heap[current, HS_LOCK^HS_HASHABLE^.sets][i_2]) ==> ((forall i_3: ref :: (heap[i_2, HS_SET^HS_HASHABLE^.set][i_3]) ==> (heap[current, owns][i_3]))))) && (Set#Disjoint(heap[current, subjects], heap[current, owns])) && ((forall i_4: ref :: (heap[current, HS_LOCK^HS_HASHABLE^.sets][i_4]) ==> ((forall i_5: ref :: (heap[i_4, HS_SET^HS_HASHABLE^.set][i_5]) ==> (((Seq#Length(heap[i_4, HS_SET^HS_HASHABLE^.buckets])) > (0)) && (Seq#Has(Seq#Item(heap[i_4, HS_SET^HS_HASHABLE^.buckets], fun.HS_SET^HS_HASHABLE^.bucket_index(heap, i_4, fun.HS_HASHABLE.hash_code_(heap, i_5), Seq#Length(heap[i_4, HS_SET^HS_HASHABLE^.buckets]))), i_5))))))) && ((forall i_6: ref :: (heap[current, HS_LOCK^HS_HASHABLE^.sets][i_6]) ==> ((forall i_7: ref :: (heap[i_6, HS_SET^HS_HASHABLE^.set][i_7]) ==> ((forall i_8: ref :: (heap[i_6, HS_SET^HS_HASHABLE^.set][i_8]) ==> (((i_7) != (Void)) && ((i_8) != (Void)) && (((i_7) != (i_8)) ==> (!(fun.HS_HASHABLE.is_model_equal(heap, i_7, i_8))))))))))) && ((forall i_9: ref :: (heap[current, HS_LOCK^HS_HASHABLE^.sets][i_9]) ==> (heap[i_9, observers][current]))) && (Set#IsEmpty(heap[current, observers]))
}

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached_exact(heap, current, HS_LOCK^HS_HASHABLE^)) ==> ((user_inv(heap, current)) <==> (HS_LOCK^HS_HASHABLE^.user_inv(heap, current)))));

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached(heap, current, HS_LOCK^HS_HASHABLE^)) ==> ((user_inv(heap, current)) ==> (HS_LOCK^HS_HASHABLE^.user_inv(heap, current)))));

procedure HS_LOCK.invariant_admissibility_check(Current: ref);
  requires attached_exact(Heap, Current, HS_LOCK^HS_HASHABLE^);



implementation HS_LOCK.invariant_admissibility_check(Current: ref)
{
  entry:
  goto pre, a2, a3;
  pre:
  assert user_inv_readable(Heap, Current)[Current, HS_LOCK^HS_HASHABLE^.sets]; // type:access tag:attribute_readable line:80 cid:408 fid:80
  assume Set#Equal(Heap[Current, subjects], Heap[Current, HS_LOCK^HS_HASHABLE^.sets]);
  assert user_inv_readable(Heap, Current)[Current, HS_LOCK^HS_HASHABLE^.sets]; // type:access tag:attribute_readable line:81 cid:408 fid:80
  assert (forall i_10: ref :: (Heap[Current, HS_LOCK^HS_HASHABLE^.sets][i_10]) ==> (user_inv_readable(Heap, Current)[i_10, HS_SET^HS_HASHABLE^.lock])); // type:access tag:attribute_readable line:81 cid:405 fid:90
  assume (forall i_10: ref :: (Heap[Current, HS_LOCK^HS_HASHABLE^.sets][i_10]) ==> ((Heap[i_10, HS_SET^HS_HASHABLE^.lock]) == (Current)));
  assert user_inv_readable(Heap, Current)[Current, HS_LOCK^HS_HASHABLE^.sets]; // type:access tag:attribute_readable line:82 cid:408 fid:80
  assert (forall i_11: ref :: (Heap[Current, HS_LOCK^HS_HASHABLE^.sets][i_11]) ==> (user_inv_readable(Heap, Current)[i_11, HS_SET^HS_HASHABLE^.set])); // type:access tag:attribute_readable line:82 cid:405 fid:88
  assume (forall i_11: ref :: (Heap[Current, HS_LOCK^HS_HASHABLE^.sets][i_11]) ==> ((forall i_12: ref :: (Heap[i_11, HS_SET^HS_HASHABLE^.set][i_12]) ==> (Heap[Current, owns][i_12]))));
  assume Set#Disjoint(Heap[Current, subjects], Heap[Current, owns]);
  assert user_inv_readable(Heap, Current)[Current, HS_LOCK^HS_HASHABLE^.sets]; // type:access tag:attribute_readable line:85 cid:408 fid:80
  assert (forall i_13: ref :: (Heap[Current, HS_LOCK^HS_HASHABLE^.sets][i_13]) ==> (user_inv_readable(Heap, Current)[i_13, HS_SET^HS_HASHABLE^.set])); // type:access tag:attribute_readable line:85 cid:405 fid:88
  assert (forall i_13: ref :: (Heap[Current, HS_LOCK^HS_HASHABLE^.sets][i_13]) ==> (user_inv_readable(Heap, Current)[i_13, HS_SET^HS_HASHABLE^.buckets])); // type:access tag:attribute_readable line:85 cid:405 fid:89
  assert (forall i_13: ref :: (Heap[Current, HS_LOCK^HS_HASHABLE^.sets][i_13]) ==> (((Seq#Length(Heap[i_13, HS_SET^HS_HASHABLE^.buckets])) > (0)) ==> (user_inv_readable(Heap, Current)[i_13, HS_SET^HS_HASHABLE^.buckets]))); // type:access tag:attribute_readable line:85 cid:405 fid:89
  assert (forall i_13: ref :: (Heap[Current, HS_LOCK^HS_HASHABLE^.sets][i_13]) ==> ((forall i_14: ref :: (Heap[i_13, HS_SET^HS_HASHABLE^.set][i_14]) ==> (((Seq#Length(Heap[i_13, HS_SET^HS_HASHABLE^.buckets])) > (0)) ==> (Frame#Subset(read.fun.HS_HASHABLE.hash_code_(Heap, i_14), user_inv_readable(Heap, Current))))))); // type:access tag:frame_readable line:85 cid:406 rid:5424
  assert (forall i_13: ref :: (Heap[Current, HS_LOCK^HS_HASHABLE^.sets][i_13]) ==> ((forall i_14: ref :: (Heap[i_13, HS_SET^HS_HASHABLE^.set][i_14]) ==> (((Seq#Length(Heap[i_13, HS_SET^HS_HASHABLE^.buckets])) > (0)) ==> (pre.fun.HS_HASHABLE.hash_code_(Heap, i_14)))))); // type:check tag:function_precondition line:85 cid:406 rid:5424
  assert (forall i_13: ref :: (Heap[Current, HS_LOCK^HS_HASHABLE^.sets][i_13]) ==> (((Seq#Length(Heap[i_13, HS_SET^HS_HASHABLE^.buckets])) > (0)) ==> (user_inv_readable(Heap, Current)[i_13, HS_SET^HS_HASHABLE^.buckets]))); // type:access tag:attribute_readable line:85 cid:405 fid:89
  assert (forall i_13: ref :: (Heap[Current, HS_LOCK^HS_HASHABLE^.sets][i_13]) ==> ((forall i_14: ref :: (Heap[i_13, HS_SET^HS_HASHABLE^.set][i_14]) ==> (((Seq#Length(Heap[i_13, HS_SET^HS_HASHABLE^.buckets])) > (0)) ==> (Frame#Subset(read.fun.HS_SET^HS_HASHABLE^.bucket_index(Heap, i_13, fun.HS_HASHABLE.hash_code_(Heap, i_14), Seq#Length(Heap[i_13, HS_SET^HS_HASHABLE^.buckets])), user_inv_readable(Heap, Current))))))); // type:access tag:frame_readable line:85 cid:405 rid:5415
  assert (forall i_13: ref :: (Heap[Current, HS_LOCK^HS_HASHABLE^.sets][i_13]) ==> ((forall i_14: ref :: (Heap[i_13, HS_SET^HS_HASHABLE^.set][i_14]) ==> (((Seq#Length(Heap[i_13, HS_SET^HS_HASHABLE^.buckets])) > (0)) ==> (pre.fun.HS_SET^HS_HASHABLE^.bucket_index(Heap, i_13, fun.HS_HASHABLE.hash_code_(Heap, i_14), Seq#Length(Heap[i_13, HS_SET^HS_HASHABLE^.buckets]))))))); // type:check tag:function_precondition line:85 cid:405 rid:5415
  assert (forall i_13: ref :: (Heap[Current, HS_LOCK^HS_HASHABLE^.sets][i_13]) ==> ((forall i_14: ref :: (Heap[i_13, HS_SET^HS_HASHABLE^.set][i_14]) ==> (((Seq#Length(Heap[i_13, HS_SET^HS_HASHABLE^.buckets])) > (0)) ==> (pre.fun.MML_SEQUENCE^MML_SEQUENCE^HS_HASHABLE^^.item(Heap[i_13, HS_SET^HS_HASHABLE^.buckets], fun.HS_SET^HS_HASHABLE^.bucket_index(Heap, i_13, fun.HS_HASHABLE.hash_code_(Heap, i_14), Seq#Length(Heap[i_13, HS_SET^HS_HASHABLE^.buckets])))))))); // type:check tag:function_precondition line:85 cid:125 rid:3286
  assume (forall i_13: ref :: (Heap[Current, HS_LOCK^HS_HASHABLE^.sets][i_13]) ==> ((forall i_14: ref :: (Heap[i_13, HS_SET^HS_HASHABLE^.set][i_14]) ==> (((Seq#Length(Heap[i_13, HS_SET^HS_HASHABLE^.buckets])) > (0)) && (Seq#Has(Seq#Item(Heap[i_13, HS_SET^HS_HASHABLE^.buckets], fun.HS_SET^HS_HASHABLE^.bucket_index(Heap, i_13, fun.HS_HASHABLE.hash_code_(Heap, i_14), Seq#Length(Heap[i_13, HS_SET^HS_HASHABLE^.buckets]))), i_14))))));
  assert user_inv_readable(Heap, Current)[Current, HS_LOCK^HS_HASHABLE^.sets]; // type:access tag:attribute_readable line:90 cid:408 fid:80
  assert (forall i_15: ref :: (Heap[Current, HS_LOCK^HS_HASHABLE^.sets][i_15]) ==> (user_inv_readable(Heap, Current)[i_15, HS_SET^HS_HASHABLE^.set])); // type:access tag:attribute_readable line:90 cid:405 fid:88
  assert (forall i_15: ref :: (Heap[Current, HS_LOCK^HS_HASHABLE^.sets][i_15]) ==> (user_inv_readable(Heap, Current)[i_15, HS_SET^HS_HASHABLE^.set])); // type:access tag:attribute_readable line:90 cid:405 fid:88
  assert (forall i_15: ref :: (Heap[Current, HS_LOCK^HS_HASHABLE^.sets][i_15]) ==> ((forall i_16: ref :: (Heap[i_15, HS_SET^HS_HASHABLE^.set][i_16]) ==> ((forall i_17: ref :: (Heap[i_15, HS_SET^HS_HASHABLE^.set][i_17]) ==> ((((i_16) != (Void)) && ((i_17) != (Void)) && ((i_16) != (i_17))) ==> (Frame#Subset(read.fun.HS_HASHABLE.is_model_equal(Heap, i_16, i_17), user_inv_readable(Heap, Current))))))))); // type:access tag:frame_readable line:90 cid:406 rid:81
  assert (forall i_15: ref :: (Heap[Current, HS_LOCK^HS_HASHABLE^.sets][i_15]) ==> ((forall i_16: ref :: (Heap[i_15, HS_SET^HS_HASHABLE^.set][i_16]) ==> ((forall i_17: ref :: (Heap[i_15, HS_SET^HS_HASHABLE^.set][i_17]) ==> ((((i_16) != (Void)) && ((i_17) != (Void)) && ((i_16) != (i_17))) ==> (pre.fun.HS_HASHABLE.is_model_equal(Heap, i_16, i_17)))))))); // type:check tag:function_precondition line:90 cid:406 rid:81
  assume (forall i_15: ref :: (Heap[Current, HS_LOCK^HS_HASHABLE^.sets][i_15]) ==> ((forall i_16: ref :: (Heap[i_15, HS_SET^HS_HASHABLE^.set][i_16]) ==> ((forall i_17: ref :: (Heap[i_15, HS_SET^HS_HASHABLE^.set][i_17]) ==> (((i_16) != (Void)) && ((i_17) != (Void)) && (((i_16) != (i_17)) ==> (!(fun.HS_HASHABLE.is_model_equal(Heap, i_16, i_17))))))))));
  assert user_inv_readable(Heap, Current)[Current, HS_LOCK^HS_HASHABLE^.sets]; // type:access tag:attribute_readable line:94 cid:408 fid:80
  assume (forall i_18: ref :: (Heap[Current, HS_LOCK^HS_HASHABLE^.sets][i_18]) ==> (Heap[i_18, observers][Current]));
  assume Set#IsEmpty(Heap[Current, observers]);
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

procedure create.HS_LOCK^HS_HASHABLE^.default_create(Current: ref);
  free requires attached_exact(Heap, Current, HS_LOCK^HS_HASHABLE^); // info:type property for argument Current
  modifies Heap;
  requires (forall <T3> $f: Field T3 :: (($f) != (allocated)) ==> ((Heap[Current, $f]) == (Default($f))));
  ensures (forall <T4> $f: Field T4 :: ((($f) != (allocated)) && (($f) != (closed))) ==> ((Heap[Current, $f]) == (Default($f))));
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.HS_LOCK^HS_HASHABLE^.default_create(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.HS_LOCK^HS_HASHABLE^.default_create(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts



implementation create.HS_LOCK^HS_HASHABLE^.default_create(Current: ref)
{
  entry:
  assume {:captureState "create.HS_LOCK^HS_HASHABLE^.default_create"} true;
  if (*) {
    assert Set#Equal(Heap[Current, subjects], Heap[Current, HS_LOCK^HS_HASHABLE^.sets]); // type:inv tag:subjects_definition line:364 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert (forall i_19: ref :: (Heap[Current, HS_LOCK^HS_HASHABLE^.sets][i_19]) ==> ((Heap[i_19, HS_SET^HS_HASHABLE^.lock]) == (Current))); // type:inv tag:subjects_lock line:364 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert (forall i_20: ref :: (Heap[Current, HS_LOCK^HS_HASHABLE^.sets][i_20]) ==> ((forall i_21: ref :: (Heap[i_20, HS_SET^HS_HASHABLE^.set][i_21]) ==> (Heap[Current, owns][i_21])))); // type:inv tag:owns_items line:364 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#Disjoint(Heap[Current, subjects], Heap[Current, owns]); // type:inv tag:no_owned_sets line:364 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert (forall i_22: ref :: (Heap[Current, HS_LOCK^HS_HASHABLE^.sets][i_22]) ==> ((forall i_23: ref :: (Heap[i_22, HS_SET^HS_HASHABLE^.set][i_23]) ==> (((Seq#Length(Heap[i_22, HS_SET^HS_HASHABLE^.buckets])) > (0)) && (Seq#Has(Seq#Item(Heap[i_22, HS_SET^HS_HASHABLE^.buckets], fun.HS_SET^HS_HASHABLE^.bucket_index(Heap, i_22, fun.HS_HASHABLE.hash_code_(Heap, i_23), Seq#Length(Heap[i_22, HS_SET^HS_HASHABLE^.buckets]))), i_23)))))); // type:inv tag:valid_buckets line:364 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert (forall i_24: ref :: (Heap[Current, HS_LOCK^HS_HASHABLE^.sets][i_24]) ==> ((forall i_25: ref :: (Heap[i_24, HS_SET^HS_HASHABLE^.set][i_25]) ==> ((forall i_26: ref :: (Heap[i_24, HS_SET^HS_HASHABLE^.set][i_26]) ==> (((i_25) != (Void)) && ((i_26) != (Void)) && (((i_25) != (i_26)) ==> (!(fun.HS_HASHABLE.is_model_equal(Heap, i_25, i_26)))))))))); // type:inv tag:no_duplicates line:364 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert (forall i_27: ref :: (Heap[Current, HS_LOCK^HS_HASHABLE^.sets][i_27]) ==> (Heap[i_27, observers][Current])); // type:inv tag:adm2 line:364 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, observers]); // type:inv tag:no_observers line:364 cid:1 rid:55
    assume false;
  }
  call wrap(Current); // default:wrapping cid:1 rid:55 line:364
}

procedure HS_LOCK^HS_HASHABLE^.add_set(Current: ref, s: ref);
  free requires attached_exact(Heap, Current, HS_LOCK^HS_HASHABLE^); // info:type property for argument Current
  free requires detachable(Heap, s, HS_SET^HS_HASHABLE^); // info:type property for argument s
  modifies Heap;
  requires is_wrapped(Heap, Current); // type:pre tag:wrapped line:23
  requires (s) != (Void); // type:attached tag:s_wrapped line:24
  requires is_wrapped(Heap, s); // type:pre tag:s_wrapped line:24
  requires (Heap[s, HS_SET^HS_HASHABLE^.lock]) == (Current); // type:pre tag:valid_lock line:25
  requires Heap[s, observers][Current]; // type:pre tag:valid_observers line:26
  requires Set#IsEmpty(Heap[s, HS_SET^HS_HASHABLE^.set]); // type:pre tag:empty_set line:27
  ensures Set#Equal(Heap[Current, HS_LOCK^HS_HASHABLE^.sets], Set#Extended(old(Heap)[Current, HS_LOCK^HS_HASHABLE^.sets], s)); // type:post tag:sets_effect line:36
  ensures is_wrapped(Heap, Current); // type:post tag:wrapped line:37
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.HS_LOCK^HS_HASHABLE^.add_set(Heap, Current, s), writable); // type:pre tag:frame_writable
  free ensures flat_same_outside(old(Heap), Heap, modify.HS_LOCK^HS_HASHABLE^.add_set(old(Heap), Current, s));
  free ensures HeapSucc(old(Heap), Heap);



function { :inline } variant.HS_LOCK^HS_HASHABLE^.add_set.1(heap: HeapType, current: ref, s: ref) returns (ref) {
  s
}

implementation HS_LOCK^HS_HASHABLE^.add_set(Current: ref, s: ref)
{
  entry:
  assume {:captureState "HS_LOCK^HS_HASHABLE^.add_set"} true;
  // /home/caf/temp/comcom/repo-hash_set/hs_lock.e:31
  // unwrap
  call unwrap(Current); // line:31 cid:1 rid:57
  assume HS_LOCK^HS_HASHABLE^.user_inv(Heap, Current);
  // /home/caf/temp/comcom/repo-hash_set/hs_lock.e:32
  // sets := sets & s
  call update_heap(Current, HS_LOCK^HS_HASHABLE^.sets, Set#Extended(Heap[Current, HS_LOCK^HS_HASHABLE^.sets], s)); // line:32
  // /home/caf/temp/comcom/repo-hash_set/hs_lock.e:33
  // set_subjects (subjects & s)
  call update_heap(Current, subjects, Set#Extended(Heap[Current, subjects], s)); // line:33
  // /home/caf/temp/comcom/repo-hash_set/hs_lock.e:34
  // wrap
  if (*) {
    assert Set#Equal(Heap[Current, subjects], Heap[Current, HS_LOCK^HS_HASHABLE^.sets]); // type:inv tag:subjects_definition line:34 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert (forall i_28: ref :: (Heap[Current, HS_LOCK^HS_HASHABLE^.sets][i_28]) ==> ((Heap[i_28, HS_SET^HS_HASHABLE^.lock]) == (Current))); // type:inv tag:subjects_lock line:34 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert (forall i_29: ref :: (Heap[Current, HS_LOCK^HS_HASHABLE^.sets][i_29]) ==> ((forall i_30: ref :: (Heap[i_29, HS_SET^HS_HASHABLE^.set][i_30]) ==> (Heap[Current, owns][i_30])))); // type:inv tag:owns_items line:34 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#Disjoint(Heap[Current, subjects], Heap[Current, owns]); // type:inv tag:no_owned_sets line:34 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert (forall i_31: ref :: (Heap[Current, HS_LOCK^HS_HASHABLE^.sets][i_31]) ==> ((forall i_32: ref :: (Heap[i_31, HS_SET^HS_HASHABLE^.set][i_32]) ==> (((Seq#Length(Heap[i_31, HS_SET^HS_HASHABLE^.buckets])) > (0)) && (Seq#Has(Seq#Item(Heap[i_31, HS_SET^HS_HASHABLE^.buckets], fun.HS_SET^HS_HASHABLE^.bucket_index(Heap, i_31, fun.HS_HASHABLE.hash_code_(Heap, i_32), Seq#Length(Heap[i_31, HS_SET^HS_HASHABLE^.buckets]))), i_32)))))); // type:inv tag:valid_buckets line:34 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert (forall i_33: ref :: (Heap[Current, HS_LOCK^HS_HASHABLE^.sets][i_33]) ==> ((forall i_34: ref :: (Heap[i_33, HS_SET^HS_HASHABLE^.set][i_34]) ==> ((forall i_35: ref :: (Heap[i_33, HS_SET^HS_HASHABLE^.set][i_35]) ==> (((i_34) != (Void)) && ((i_35) != (Void)) && (((i_34) != (i_35)) ==> (!(fun.HS_HASHABLE.is_model_equal(Heap, i_34, i_35)))))))))); // type:inv tag:no_duplicates line:34 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert (forall i_36: ref :: (Heap[Current, HS_LOCK^HS_HASHABLE^.sets][i_36]) ==> (Heap[i_36, observers][Current])); // type:inv tag:adm2 line:34 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, observers]); // type:inv tag:no_observers line:34 cid:1 rid:55
    assume false;
  }
  call wrap(Current); // line:34 cid:1 rid:55
}

procedure HS_LOCK^HS_HASHABLE^.lock(Current: ref, item: ref);
  free requires attached_exact(Heap, Current, HS_LOCK^HS_HASHABLE^); // info:type property for argument Current
  free requires detachable(Heap, item, HS_HASHABLE); // info:type property for argument item
  modifies Heap;
  requires is_wrapped(Heap, Current); // type:pre tag:wrapped line:45
  requires (item) != (Void); // type:attached tag:item_wrapped line:46
  requires is_wrapped(Heap, item); // type:pre tag:item_wrapped line:46
  requires !(Heap[Current, subjects][item]); // type:pre tag:item_not_set line:47
  ensures Set#Equal(Heap[Current, owns], Set#Extended(old(Heap)[Current, owns], item)); // type:post tag:owns_effect line:55
  ensures is_wrapped(Heap, Current); // type:post tag:wrapped line:56
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.HS_LOCK^HS_HASHABLE^.lock(Heap, Current, item), writable); // type:pre tag:frame_writable
  free ensures flat_same_outside(old(Heap), Heap, modify.HS_LOCK^HS_HASHABLE^.lock(old(Heap), Current, item));
  free ensures HeapSucc(old(Heap), Heap);



function { :inline } variant.HS_LOCK^HS_HASHABLE^.lock.1(heap: HeapType, current: ref, item: ref) returns (ref) {
  item
}

implementation HS_LOCK^HS_HASHABLE^.lock(Current: ref, item: ref)
{
  entry:
  assume {:captureState "HS_LOCK^HS_HASHABLE^.lock"} true;
  // /home/caf/temp/comcom/repo-hash_set/hs_lock.e:51
  // unwrap
  call unwrap(Current); // line:51 cid:1 rid:57
  assume HS_LOCK^HS_HASHABLE^.user_inv(Heap, Current);
  // /home/caf/temp/comcom/repo-hash_set/hs_lock.e:52
  // set_owns (owns & item)
  call update_heap(Current, owns, Set#Extended(Heap[Current, owns], item)); // line:52
  // /home/caf/temp/comcom/repo-hash_set/hs_lock.e:53
  // wrap
  if (*) {
    assert Set#Equal(Heap[Current, subjects], Heap[Current, HS_LOCK^HS_HASHABLE^.sets]); // type:inv tag:subjects_definition line:53 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert (forall i_37: ref :: (Heap[Current, HS_LOCK^HS_HASHABLE^.sets][i_37]) ==> ((Heap[i_37, HS_SET^HS_HASHABLE^.lock]) == (Current))); // type:inv tag:subjects_lock line:53 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert (forall i_38: ref :: (Heap[Current, HS_LOCK^HS_HASHABLE^.sets][i_38]) ==> ((forall i_39: ref :: (Heap[i_38, HS_SET^HS_HASHABLE^.set][i_39]) ==> (Heap[Current, owns][i_39])))); // type:inv tag:owns_items line:53 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#Disjoint(Heap[Current, subjects], Heap[Current, owns]); // type:inv tag:no_owned_sets line:53 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert (forall i_40: ref :: (Heap[Current, HS_LOCK^HS_HASHABLE^.sets][i_40]) ==> ((forall i_41: ref :: (Heap[i_40, HS_SET^HS_HASHABLE^.set][i_41]) ==> (((Seq#Length(Heap[i_40, HS_SET^HS_HASHABLE^.buckets])) > (0)) && (Seq#Has(Seq#Item(Heap[i_40, HS_SET^HS_HASHABLE^.buckets], fun.HS_SET^HS_HASHABLE^.bucket_index(Heap, i_40, fun.HS_HASHABLE.hash_code_(Heap, i_41), Seq#Length(Heap[i_40, HS_SET^HS_HASHABLE^.buckets]))), i_41)))))); // type:inv tag:valid_buckets line:53 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert (forall i_42: ref :: (Heap[Current, HS_LOCK^HS_HASHABLE^.sets][i_42]) ==> ((forall i_43: ref :: (Heap[i_42, HS_SET^HS_HASHABLE^.set][i_43]) ==> ((forall i_44: ref :: (Heap[i_42, HS_SET^HS_HASHABLE^.set][i_44]) ==> (((i_43) != (Void)) && ((i_44) != (Void)) && (((i_43) != (i_44)) ==> (!(fun.HS_HASHABLE.is_model_equal(Heap, i_43, i_44)))))))))); // type:inv tag:no_duplicates line:53 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert (forall i_45: ref :: (Heap[Current, HS_LOCK^HS_HASHABLE^.sets][i_45]) ==> (Heap[i_45, observers][Current])); // type:inv tag:adm2 line:53 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, observers]); // type:inv tag:no_observers line:53 cid:1 rid:55
    assume false;
  }
  call wrap(Current); // line:53 cid:1 rid:55
}

procedure HS_LOCK^HS_HASHABLE^.unlock(Current: ref, item: ref);
  free requires attached_exact(Heap, Current, HS_LOCK^HS_HASHABLE^); // info:type property for argument Current
  free requires detachable(Heap, item, HS_HASHABLE); // info:type property for argument item
  modifies Heap;
  requires is_wrapped(Heap, Current); // type:pre tag:wrapped line:64
  requires Heap[Current, owns][item]; // type:pre tag:item_locked line:65
  requires (forall i_46: ref :: (Heap[Current, HS_LOCK^HS_HASHABLE^.sets][i_46]) ==> (!(Heap[i_46, HS_SET^HS_HASHABLE^.set][item]))); // type:pre tag:not_in_set line:66
  ensures Set#Equal(Heap[Current, owns], Set#Removed(old(Heap)[Current, owns], item)); // type:post tag:owns_effect line:74
  ensures (item) != (Void); // type:attached tag:item_wrapped line:75
  ensures is_wrapped(Heap, item); // type:post tag:item_wrapped line:75
  ensures is_wrapped(Heap, Current); // type:post tag:wrapped line:76
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.HS_LOCK^HS_HASHABLE^.unlock(Heap, Current, item), writable); // type:pre tag:frame_writable
  free ensures flat_same_outside(old(Heap), Heap, modify.HS_LOCK^HS_HASHABLE^.unlock(old(Heap), Current, item));
  free ensures HeapSucc(old(Heap), Heap);



function { :inline } variant.HS_LOCK^HS_HASHABLE^.unlock.1(heap: HeapType, current: ref, item: ref) returns (ref) {
  item
}

implementation HS_LOCK^HS_HASHABLE^.unlock(Current: ref, item: ref)
{
  entry:
  assume {:captureState "HS_LOCK^HS_HASHABLE^.unlock"} true;
  // /home/caf/temp/comcom/repo-hash_set/hs_lock.e:70
  // unwrap
  call unwrap(Current); // line:70 cid:1 rid:57
  assume HS_LOCK^HS_HASHABLE^.user_inv(Heap, Current);
  // /home/caf/temp/comcom/repo-hash_set/hs_lock.e:71
  // set_owns (owns / item)
  call update_heap(Current, owns, Set#Removed(Heap[Current, owns], item)); // line:71
  // /home/caf/temp/comcom/repo-hash_set/hs_lock.e:72
  // wrap
  if (*) {
    assert Set#Equal(Heap[Current, subjects], Heap[Current, HS_LOCK^HS_HASHABLE^.sets]); // type:inv tag:subjects_definition line:72 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert (forall i_47: ref :: (Heap[Current, HS_LOCK^HS_HASHABLE^.sets][i_47]) ==> ((Heap[i_47, HS_SET^HS_HASHABLE^.lock]) == (Current))); // type:inv tag:subjects_lock line:72 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert (forall i_48: ref :: (Heap[Current, HS_LOCK^HS_HASHABLE^.sets][i_48]) ==> ((forall i_49: ref :: (Heap[i_48, HS_SET^HS_HASHABLE^.set][i_49]) ==> (Heap[Current, owns][i_49])))); // type:inv tag:owns_items line:72 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#Disjoint(Heap[Current, subjects], Heap[Current, owns]); // type:inv tag:no_owned_sets line:72 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert (forall i_50: ref :: (Heap[Current, HS_LOCK^HS_HASHABLE^.sets][i_50]) ==> ((forall i_51: ref :: (Heap[i_50, HS_SET^HS_HASHABLE^.set][i_51]) ==> (((Seq#Length(Heap[i_50, HS_SET^HS_HASHABLE^.buckets])) > (0)) && (Seq#Has(Seq#Item(Heap[i_50, HS_SET^HS_HASHABLE^.buckets], fun.HS_SET^HS_HASHABLE^.bucket_index(Heap, i_50, fun.HS_HASHABLE.hash_code_(Heap, i_51), Seq#Length(Heap[i_50, HS_SET^HS_HASHABLE^.buckets]))), i_51)))))); // type:inv tag:valid_buckets line:72 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert (forall i_52: ref :: (Heap[Current, HS_LOCK^HS_HASHABLE^.sets][i_52]) ==> ((forall i_53: ref :: (Heap[i_52, HS_SET^HS_HASHABLE^.set][i_53]) ==> ((forall i_54: ref :: (Heap[i_52, HS_SET^HS_HASHABLE^.set][i_54]) ==> (((i_53) != (Void)) && ((i_54) != (Void)) && (((i_53) != (i_54)) ==> (!(fun.HS_HASHABLE.is_model_equal(Heap, i_53, i_54)))))))))); // type:inv tag:no_duplicates line:72 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert (forall i_55: ref :: (Heap[Current, HS_LOCK^HS_HASHABLE^.sets][i_55]) ==> (Heap[i_55, observers][Current])); // type:inv tag:adm2 line:72 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, observers]); // type:inv tag:no_observers line:72 cid:1 rid:55
    assume false;
  }
  call wrap(Current); // line:72 cid:1 rid:55
}

const unique HS_CLIENT: Type;

axiom ((HS_CLIENT) <: (ANY));

axiom ((forall t: Type :: { (HS_CLIENT) <: (t) } ((HS_CLIENT) <: (t)) <==> (((t) == (HS_CLIENT)) || ((ANY) <: (t)))));

axiom ((FieldId(allocated, HS_CLIENT)) == (-1));

axiom ((FieldId(closed, HS_CLIENT)) == (-2));

axiom ((FieldId(owner, HS_CLIENT)) == (-3));

axiom ((FieldId(owns, HS_CLIENT)) == (-4));

axiom ((FieldId(observers, HS_CLIENT)) == (-5));

axiom ((FieldId(subjects, HS_CLIENT)) == (-6));

axiom ((forall <T5> $f: Field T5 :: { IsModelField($f, HS_CLIENT) } (IsModelField($f, HS_CLIENT)) <==> ((($f) == (subjects)) || (($f) == (observers)))));

function { :inline } HS_CLIENT.user_inv(heap: HeapType, current: ref) returns (bool) {
  (Set#IsEmpty(heap[current, observers])) && (Set#IsEmpty(heap[current, subjects])) && (Set#IsEmpty(heap[current, owns])) && (admissibility2(heap, current))
}

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached_exact(heap, current, HS_CLIENT)) ==> ((user_inv(heap, current)) <==> (HS_CLIENT.user_inv(heap, current)))));

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached(heap, current, HS_CLIENT)) ==> ((user_inv(heap, current)) ==> (HS_CLIENT.user_inv(heap, current)))));

procedure HS_CLIENT.invariant_admissibility_check(Current: ref);
  requires attached_exact(Heap, Current, HS_CLIENT);



implementation HS_CLIENT.invariant_admissibility_check(Current: ref)
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

procedure create.HS_CLIENT.default_create(Current: ref);
  free requires attached_exact(Heap, Current, HS_CLIENT); // info:type property for argument Current
  modifies Heap;
  requires (forall <T6> $f: Field T6 :: (($f) != (allocated)) ==> ((Heap[Current, $f]) == (Default($f))));
  ensures (forall <T7> $f: Field T7 :: ((($f) != (allocated)) && (($f) != (closed))) ==> ((Heap[Current, $f]) == (Default($f))));
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.HS_CLIENT.default_create(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.HS_CLIENT.default_create(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts



implementation create.HS_CLIENT.default_create(Current: ref)
{
  entry:
  assume {:captureState "create.HS_CLIENT.default_create"} true;
  if (*) {
    assert Set#IsEmpty(Heap[Current, observers]); // type:inv tag:default_observers line:132 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, subjects]); // type:inv tag:default_subjects line:132 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, owns]); // type:inv tag:default_owns line:132 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert admissibility2(Heap, Current); // type:inv tag:A2 line:132 cid:1 rid:55
    assume false;
  }
  call wrap(Current); // default:wrapping cid:1 rid:55 line:364
}

procedure HS_CLIENT.test(Current: ref);
  free requires attached_exact(Heap, Current, HS_CLIENT); // info:type property for argument Current
  modifies Heap;
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.HS_CLIENT.test(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.HS_CLIENT.test(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);
  requires is_wrapped(Heap, Current); // type:pre tag:default_is_wrapped default:contracts
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts



function { :inline } variant.HS_CLIENT.test.1(heap: HeapType, current: ref) returns (int) {
  0
}

implementation HS_CLIENT.test(Current: ref)
{
  var temp_56: ref;
  var temp_57: ref;
  var temp_58: ref;
  var temp_59: ref;
  var temp_60: ref;
  var temp_61: ref;
  var local1: ref where detachable(Heap, local1, HS_KEY);
  var local2: ref where detachable(Heap, local2, HS_KEY);
  var local3: ref where detachable(Heap, local3, HS_KEY);
  var local4: ref where detachable_exact(Heap, local4, HS_LOCK^HS_KEY^);
  var local5: ref where detachable(Heap, local5, HS_SET^HS_KEY^);
  var local6: ref where detachable(Heap, local6, HS_SET^HS_KEY^);

  init_locals:
  temp_56 := Void;
  temp_57 := Void;
  temp_58 := Void;
  temp_59 := Void;
  temp_60 := Void;
  temp_61 := Void;
  local1 := Void;
  local2 := Void;
  local3 := Void;
  local4 := Void;
  local5 := Void;
  local6 := Void;

  entry:
  assume {:captureState "HS_CLIENT.test"} true;
  call unwrap(Current); // default:wrapping cid:1 rid:57 line:10
  assume HS_CLIENT.user_inv(Heap, Current);
  // /home/caf/temp/comcom/repo-hash_set/hs_client.e:19
  // create lock
  call temp_56 := allocate(HS_LOCK^HS_KEY^); // line:-1
  call create.HS_LOCK^HS_KEY^.default_create(temp_56); // line:19 cid:408 rid:35
  local4 := temp_56;
  // /home/caf/temp/comcom/repo-hash_set/hs_client.e:21
  // create s1.make (lock)
  call temp_57 := allocate(HS_SET^HS_KEY^); // line:-1
  call create.HS_SET^HS_KEY^.make(temp_57, local4); // line:21 cid:405 rid:5409
  local5 := temp_57;
  // /home/caf/temp/comcom/repo-hash_set/hs_client.e:22
  // check s1.inv end
  assert {:subsumption 0} (local5) != (Void); // type:attached line:22
  assert user_inv(Heap, local5); // type:check line:22
  // /home/caf/temp/comcom/repo-hash_set/hs_client.e:23
  // lock.add_set (s1)
  assert {:subsumption 0} (local4) != (Void); // type:attached line:23
  call HS_LOCK^HS_KEY^.add_set(local4, local5); // line:23 cid:408 rid:5402
  // /home/caf/temp/comcom/repo-hash_set/hs_client.e:25
  // create s2.make (lock)
  call temp_58 := allocate(HS_SET^HS_KEY^); // line:-1
  call create.HS_SET^HS_KEY^.make(temp_58, local4); // line:25 cid:405 rid:5409
  local6 := temp_58;
  // /home/caf/temp/comcom/repo-hash_set/hs_client.e:26
  // check s2.inv end
  assert {:subsumption 0} (local6) != (Void); // type:attached line:26
  assert user_inv(Heap, local6); // type:check line:26
  // /home/caf/temp/comcom/repo-hash_set/hs_client.e:27
  // lock.add_set (s2)
  assert {:subsumption 0} (local4) != (Void); // type:attached line:27
  call HS_LOCK^HS_KEY^.add_set(local4, local6); // line:27 cid:408 rid:5402
  // /home/caf/temp/comcom/repo-hash_set/hs_client.e:31
  // create i.set_value (1)
  call temp_59 := allocate(HS_KEY); // line:-1
  call create.HS_KEY.set_value(temp_59, 1); // line:31 cid:404 rid:5426
  local1 := temp_59;
  // /home/caf/temp/comcom/repo-hash_set/hs_client.e:32
  // create j.set_value (2)
  call temp_60 := allocate(HS_KEY); // line:-1
  call create.HS_KEY.set_value(temp_60, 2); // line:32 cid:404 rid:5426
  local2 := temp_60;
  // /home/caf/temp/comcom/repo-hash_set/hs_client.e:33
  // lock.lock (i)
  assert {:subsumption 0} (local4) != (Void); // type:attached line:33
  call HS_LOCK^HS_KEY^.lock(local4, local1); // line:33 cid:408 rid:5403
  // /home/caf/temp/comcom/repo-hash_set/hs_client.e:34
  // lock.lock (j)
  assert {:subsumption 0} (local4) != (Void); // type:attached line:34
  call HS_LOCK^HS_KEY^.lock(local4, local2); // line:34 cid:408 rid:5403
  // /home/caf/temp/comcom/repo-hash_set/hs_client.e:35
  // check i.value = 1 end
  assert {:subsumption 0} (local1) != (Void); // type:attached line:35
  assert (Heap[local1, HS_KEY.value]) == (1); // type:check line:35
  // /home/caf/temp/comcom/repo-hash_set/hs_client.e:36
  // check j.value = 2 end
  assert {:subsumption 0} (local2) != (Void); // type:attached line:36
  assert (Heap[local2, HS_KEY.value]) == (2); // type:check line:36
  // /home/caf/temp/comcom/repo-hash_set/hs_client.e:38
  // s1.extend (i)
  assert {:subsumption 0} (local5) != (Void); // type:attached line:38
  call HS_SET^HS_KEY^.extend(local5, local1); // line:38 cid:405 rid:5411
  // /home/caf/temp/comcom/repo-hash_set/hs_client.e:39
  // check s1.set.count = 1 end
  assert {:subsumption 0} (local5) != (Void); // type:attached line:39
  assert (Set#Card(Heap[local5, HS_SET^HS_KEY^.set])) == (1); // type:check line:39
  // /home/caf/temp/comcom/repo-hash_set/hs_client.e:40
  // check s1.set_has (i) end
  assert {:subsumption 0} (local5) != (Void); // type:attached line:40
  assert pre.fun.HS_SET^HS_KEY^.set_has(Heap, local5, local1); // type:check tag:function_precondition line:40 cid:405 rid:5420
  assert fun.HS_SET^HS_KEY^.set_has(Heap, local5, local1); // type:check line:40
  // /home/caf/temp/comcom/repo-hash_set/hs_client.e:41
  // check not s1.set_has (j) end
  assert {:subsumption 0} (local5) != (Void); // type:attached line:41
  assert pre.fun.HS_SET^HS_KEY^.set_has(Heap, local5, local2); // type:check tag:function_precondition line:41 cid:405 rid:5420
  assert !(fun.HS_SET^HS_KEY^.set_has(Heap, local5, local2)); // type:check line:41
  // /home/caf/temp/comcom/repo-hash_set/hs_client.e:43
  // s1.extend (j)
  assert {:subsumption 0} (local5) != (Void); // type:attached line:43
  call HS_SET^HS_KEY^.extend(local5, local2); // line:43 cid:405 rid:5411
  // /home/caf/temp/comcom/repo-hash_set/hs_client.e:44
  // check s1.set_has (i) end
  assert {:subsumption 0} (local5) != (Void); // type:attached line:44
  assert pre.fun.HS_SET^HS_KEY^.set_has(Heap, local5, local1); // type:check tag:function_precondition line:44 cid:405 rid:5420
  assert fun.HS_SET^HS_KEY^.set_has(Heap, local5, local1); // type:check line:44
  // /home/caf/temp/comcom/repo-hash_set/hs_client.e:45
  // check s1.set_has (j) end
  assert {:subsumption 0} (local5) != (Void); // type:attached line:45
  assert pre.fun.HS_SET^HS_KEY^.set_has(Heap, local5, local2); // type:check tag:function_precondition line:45 cid:405 rid:5420
  assert fun.HS_SET^HS_KEY^.set_has(Heap, local5, local2); // type:check line:45
  // /home/caf/temp/comcom/repo-hash_set/hs_client.e:49
  // s2.extend (j)
  assert {:subsumption 0} (local6) != (Void); // type:attached line:49
  call HS_SET^HS_KEY^.extend(local6, local2); // line:49 cid:405 rid:5411
  // /home/caf/temp/comcom/repo-hash_set/hs_client.e:50
  // check s2.set_has (j) end
  assert {:subsumption 0} (local6) != (Void); // type:attached line:50
  assert pre.fun.HS_SET^HS_KEY^.set_has(Heap, local6, local2); // type:check tag:function_precondition line:50 cid:405 rid:5420
  assert fun.HS_SET^HS_KEY^.set_has(Heap, local6, local2); // type:check line:50
  // /home/caf/temp/comcom/repo-hash_set/hs_client.e:51
  // check not s2.set_has (i) end
  assert {:subsumption 0} (local6) != (Void); // type:attached line:51
  assert pre.fun.HS_SET^HS_KEY^.set_has(Heap, local6, local1); // type:check tag:function_precondition line:51 cid:405 rid:5420
  assert !(fun.HS_SET^HS_KEY^.set_has(Heap, local6, local1)); // type:check line:51
  // /home/caf/temp/comcom/repo-hash_set/hs_client.e:52
  // check s1.set_has (i) end
  assert {:subsumption 0} (local5) != (Void); // type:attached line:52
  assert pre.fun.HS_SET^HS_KEY^.set_has(Heap, local5, local1); // type:check tag:function_precondition line:52 cid:405 rid:5420
  assert fun.HS_SET^HS_KEY^.set_has(Heap, local5, local1); // type:check line:52
  // /home/caf/temp/comcom/repo-hash_set/hs_client.e:53
  // check s1.set_has (j) end
  assert {:subsumption 0} (local5) != (Void); // type:attached line:53
  assert pre.fun.HS_SET^HS_KEY^.set_has(Heap, local5, local2); // type:check tag:function_precondition line:53 cid:405 rid:5420
  assert fun.HS_SET^HS_KEY^.set_has(Heap, local5, local2); // type:check line:53
  // /home/caf/temp/comcom/repo-hash_set/hs_client.e:57
  // s2.join (s1)
  assert {:subsumption 0} (local6) != (Void); // type:attached line:57
  call HS_SET^HS_KEY^.join(local6, local5); // line:57 cid:405 rid:5412
  // /home/caf/temp/comcom/repo-hash_set/hs_client.e:58
  // check s2.set_has (i) end
  assert {:subsumption 0} (local6) != (Void); // type:attached line:58
  assert pre.fun.HS_SET^HS_KEY^.set_has(Heap, local6, local1); // type:check tag:function_precondition line:58 cid:405 rid:5420
  assert fun.HS_SET^HS_KEY^.set_has(Heap, local6, local1); // type:check line:58
  // /home/caf/temp/comcom/repo-hash_set/hs_client.e:59
  // check s2.set_has (j) end
  assert {:subsumption 0} (local6) != (Void); // type:attached line:59
  assert pre.fun.HS_SET^HS_KEY^.set_has(Heap, local6, local2); // type:check tag:function_precondition line:59 cid:405 rid:5420
  assert fun.HS_SET^HS_KEY^.set_has(Heap, local6, local2); // type:check line:59
  // /home/caf/temp/comcom/repo-hash_set/hs_client.e:60
  // check s1.set_has (i) end
  assert {:subsumption 0} (local5) != (Void); // type:attached line:60
  assert pre.fun.HS_SET^HS_KEY^.set_has(Heap, local5, local1); // type:check tag:function_precondition line:60 cid:405 rid:5420
  assert fun.HS_SET^HS_KEY^.set_has(Heap, local5, local1); // type:check line:60
  // /home/caf/temp/comcom/repo-hash_set/hs_client.e:61
  // check s1.set_has (j) end
  assert {:subsumption 0} (local5) != (Void); // type:attached line:61
  assert pre.fun.HS_SET^HS_KEY^.set_has(Heap, local5, local2); // type:check tag:function_precondition line:61 cid:405 rid:5420
  assert fun.HS_SET^HS_KEY^.set_has(Heap, local5, local2); // type:check line:61
  // /home/caf/temp/comcom/repo-hash_set/hs_client.e:65
  // s1.extend (i)
  assert {:subsumption 0} (local5) != (Void); // type:attached line:65
  call HS_SET^HS_KEY^.extend(local5, local1); // line:65 cid:405 rid:5411
  // /home/caf/temp/comcom/repo-hash_set/hs_client.e:66
  // check s1.set.count = 2 end
  assert {:subsumption 0} (local5) != (Void); // type:attached line:66
  assert (Set#Card(Heap[local5, HS_SET^HS_KEY^.set])) == (2); // type:check line:66
  // /home/caf/temp/comcom/repo-hash_set/hs_client.e:68
  // create k.set_value (1)  	-- `k' is a duplicate of `i'...
  call temp_61 := allocate(HS_KEY); // line:-1
  call create.HS_KEY.set_value(temp_61, 1); // line:68 cid:404 rid:5426
  local3 := temp_61;
  // /home/caf/temp/comcom/repo-hash_set/hs_client.e:69
  // lock.lock (k)
  assert {:subsumption 0} (local4) != (Void); // type:attached line:69
  call HS_LOCK^HS_KEY^.lock(local4, local3); // line:69 cid:408 rid:5403
  // /home/caf/temp/comcom/repo-hash_set/hs_client.e:70
  // s1.extend (k)
  assert {:subsumption 0} (local5) != (Void); // type:attached line:70
  call HS_SET^HS_KEY^.extend(local5, local3); // line:70 cid:405 rid:5411
  // /home/caf/temp/comcom/repo-hash_set/hs_client.e:71
  // check s1.set_has (k) end
  assert {:subsumption 0} (local5) != (Void); // type:attached line:71
  assert pre.fun.HS_SET^HS_KEY^.set_has(Heap, local5, local3); // type:check tag:function_precondition line:71 cid:405 rid:5420
  assert fun.HS_SET^HS_KEY^.set_has(Heap, local5, local3); // type:check line:71
  // /home/caf/temp/comcom/repo-hash_set/hs_client.e:72
  // check s1.set.count = 2 end 	-- so not really added
  assert {:subsumption 0} (local5) != (Void); // type:attached line:72
  assert (Set#Card(Heap[local5, HS_SET^HS_KEY^.set])) == (2); // type:check line:72
  // /home/caf/temp/comcom/repo-hash_set/hs_client.e:76
  // s1.wipe_out
  assert {:subsumption 0} (local5) != (Void); // type:attached line:76
  call HS_SET^HS_KEY^.wipe_out(local5); // line:76 cid:405 rid:5414
  // /home/caf/temp/comcom/repo-hash_set/hs_client.e:77
  // s2.wipe_out
  assert {:subsumption 0} (local6) != (Void); // type:attached line:77
  call HS_SET^HS_KEY^.wipe_out(local6); // line:77 cid:405 rid:5414
  // /home/caf/temp/comcom/repo-hash_set/hs_client.e:78
  // lock.unlock (i) 			-- Not used by the sets anymore
  assert {:subsumption 0} (local4) != (Void); // type:attached line:78
  call HS_LOCK^HS_KEY^.unlock(local4, local1); // line:78 cid:408 rid:5404
  // /home/caf/temp/comcom/repo-hash_set/hs_client.e:79
  // lock.unlock (j) 			-- so can now be unlocked
  assert {:subsumption 0} (local4) != (Void); // type:attached line:79
  call HS_LOCK^HS_KEY^.unlock(local4, local2); // line:79 cid:408 rid:5404
  // /home/caf/temp/comcom/repo-hash_set/hs_client.e:80
  // check i.is_wrapped end		-- and reused for something else
  assert {:subsumption 0} (local1) != (Void); // type:attached line:80
  assert is_wrapped(Heap, local1); // type:check line:80
  // /home/caf/temp/comcom/repo-hash_set/hs_client.e:81
  // check j.is_wrapped end
  assert {:subsumption 0} (local2) != (Void); // type:attached line:81
  assert is_wrapped(Heap, local2); // type:check line:81
  if (*) {
    assert Set#IsEmpty(Heap[Current, observers]); // type:inv tag:default_observers line:132 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, subjects]); // type:inv tag:default_subjects line:132 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, owns]); // type:inv tag:default_owns line:132 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert admissibility2(Heap, Current); // type:inv tag:A2 line:132 cid:1 rid:55
    assume false;
  }
  call wrap(Current); // default:wrapping cid:1 rid:55 line:82
}

procedure HS_CLIENT.test_modification(Current: ref);
  free requires attached_exact(Heap, Current, HS_CLIENT); // info:type property for argument Current
  modifies Heap;
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.HS_CLIENT.test_modification(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.HS_CLIENT.test_modification(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);
  requires is_wrapped(Heap, Current); // type:pre tag:default_is_wrapped default:contracts
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts



function { :inline } variant.HS_CLIENT.test_modification.1(heap: HeapType, current: ref) returns (int) {
  0
}

implementation HS_CLIENT.test_modification(Current: ref)
{
  var temp_62: ref;
  var temp_63: ref;
  var temp_64: ref;
  var temp_65: ref;
  var local1: ref where detachable(Heap, local1, HS_KEY);
  var local2: ref where detachable(Heap, local2, HS_KEY);
  var local3: ref where detachable_exact(Heap, local3, HS_LOCK^HS_KEY^);
  var local4: ref where detachable(Heap, local4, HS_SET^HS_KEY^);

  init_locals:
  temp_62 := Void;
  temp_63 := Void;
  temp_64 := Void;
  temp_65 := Void;
  local1 := Void;
  local2 := Void;
  local3 := Void;
  local4 := Void;

  entry:
  assume {:captureState "HS_CLIENT.test_modification"} true;
  call unwrap(Current); // default:wrapping cid:1 rid:57 line:84
  assume HS_CLIENT.user_inv(Heap, Current);
  // /home/caf/temp/comcom/repo-hash_set/hs_client.e:91
  // create lock
  call temp_62 := allocate(HS_LOCK^HS_KEY^); // line:-1
  call create.HS_LOCK^HS_KEY^.default_create(temp_62); // line:91 cid:408 rid:35
  local3 := temp_62;
  // /home/caf/temp/comcom/repo-hash_set/hs_client.e:92
  // create i.set_value (1)
  call temp_63 := allocate(HS_KEY); // line:-1
  call create.HS_KEY.set_value(temp_63, 1); // line:92 cid:404 rid:5426
  local1 := temp_63;
  // /home/caf/temp/comcom/repo-hash_set/hs_client.e:93
  // create j.set_value (2)
  call temp_64 := allocate(HS_KEY); // line:-1
  call create.HS_KEY.set_value(temp_64, 2); // line:93 cid:404 rid:5426
  local2 := temp_64;
  // /home/caf/temp/comcom/repo-hash_set/hs_client.e:94
  // lock.lock (i)
  assert {:subsumption 0} (local3) != (Void); // type:attached line:94
  call HS_LOCK^HS_KEY^.lock(local3, local1); // line:94 cid:408 rid:5403
  // /home/caf/temp/comcom/repo-hash_set/hs_client.e:95
  // lock.lock (j)
  assert {:subsumption 0} (local3) != (Void); // type:attached line:95
  call HS_LOCK^HS_KEY^.lock(local3, local2); // line:95 cid:408 rid:5403
  // /home/caf/temp/comcom/repo-hash_set/hs_client.e:97
  // create s.make (lock)
  call temp_65 := allocate(HS_SET^HS_KEY^); // line:-1
  call create.HS_SET^HS_KEY^.make(temp_65, local3); // line:97 cid:405 rid:5409
  local4 := temp_65;
  // /home/caf/temp/comcom/repo-hash_set/hs_client.e:98
  // check s.inv end
  assert {:subsumption 0} (local4) != (Void); // type:attached line:98
  assert user_inv(Heap, local4); // type:check line:98
  // /home/caf/temp/comcom/repo-hash_set/hs_client.e:99
  // lock.add_set (s)
  assert {:subsumption 0} (local3) != (Void); // type:attached line:99
  call HS_LOCK^HS_KEY^.add_set(local3, local4); // line:99 cid:408 rid:5402
  // /home/caf/temp/comcom/repo-hash_set/hs_client.e:100
  // s.extend (i)
  assert {:subsumption 0} (local4) != (Void); // type:attached line:100
  call HS_SET^HS_KEY^.extend(local4, local1); // line:100 cid:405 rid:5411
  // /home/caf/temp/comcom/repo-hash_set/hs_client.e:102
  // lock.unwrap
  assert {:subsumption 0} (local3) != (Void); // type:attached line:102
  call unwrap(local3); // line:102 cid:1 rid:57
  assume HS_LOCK^HS_KEY^.user_inv(Heap, local3);
  // /home/caf/temp/comcom/repo-hash_set/hs_client.e:103
  // i.set_value (-1) 	-- OK, no_duplicates and valid_buckets invariants are preserved
  assert {:subsumption 0} (local1) != (Void); // type:attached line:103
  call HS_KEY.set_value(local1, -1); // line:103 cid:404 rid:5426
  // /home/caf/temp/comcom/repo-hash_set/hs_client.e:104
  // j.set_value (3) 	-- OK, `j' is not contained in any set
  assert {:subsumption 0} (local2) != (Void); // type:attached line:104
  call HS_KEY.set_value(local2, 3); // line:104 cid:404 rid:5426
  // /home/caf/temp/comcom/repo-hash_set/hs_client.e:105
  // lock.wrap
  assert {:subsumption 0} (local3) != (Void); // type:attached line:105
  if (*) {
    assert Set#Equal(Heap[local3, subjects], Heap[local3, HS_LOCK^HS_KEY^.sets]); // type:inv tag:subjects_definition line:105 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert (forall i_75: ref :: (Heap[local3, HS_LOCK^HS_KEY^.sets][i_75]) ==> ((Heap[i_75, HS_SET^HS_KEY^.lock]) == (local3))); // type:inv tag:subjects_lock line:105 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert (forall i_76: ref :: (Heap[local3, HS_LOCK^HS_KEY^.sets][i_76]) ==> ((forall i_77: ref :: (Heap[i_76, HS_SET^HS_KEY^.set][i_77]) ==> (Heap[local3, owns][i_77])))); // type:inv tag:owns_items line:105 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#Disjoint(Heap[local3, subjects], Heap[local3, owns]); // type:inv tag:no_owned_sets line:105 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert (forall i_78: ref :: (Heap[local3, HS_LOCK^HS_KEY^.sets][i_78]) ==> ((forall i_79: ref :: (Heap[i_78, HS_SET^HS_KEY^.set][i_79]) ==> (((Seq#Length(Heap[i_78, HS_SET^HS_KEY^.buckets])) > (0)) && (Seq#Has(Seq#Item(Heap[i_78, HS_SET^HS_KEY^.buckets], fun.HS_SET^HS_KEY^.bucket_index(Heap, i_78, fun.HS_KEY.hash_code_(Heap, i_79), Seq#Length(Heap[i_78, HS_SET^HS_KEY^.buckets]))), i_79)))))); // type:inv tag:valid_buckets line:105 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert (forall i_80: ref :: (Heap[local3, HS_LOCK^HS_KEY^.sets][i_80]) ==> ((forall i_81: ref :: (Heap[i_80, HS_SET^HS_KEY^.set][i_81]) ==> ((forall i_82: ref :: (Heap[i_80, HS_SET^HS_KEY^.set][i_82]) ==> (((i_81) != (Void)) && ((i_82) != (Void)) && (((i_81) != (i_82)) ==> (!(fun.HS_KEY.is_model_equal(Heap, i_81, i_82)))))))))); // type:inv tag:no_duplicates line:105 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert (forall i_83: ref :: (Heap[local3, HS_LOCK^HS_KEY^.sets][i_83]) ==> (Heap[i_83, observers][local3])); // type:inv tag:adm2 line:105 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[local3, observers]); // type:inv tag:no_observers line:105 cid:1 rid:55
    assume false;
  }
  call wrap(local3); // line:105 cid:1 rid:55
  // /home/caf/temp/comcom/repo-hash_set/hs_client.e:107
  // s.wipe_out
  assert {:subsumption 0} (local4) != (Void); // type:attached line:107
  call HS_SET^HS_KEY^.wipe_out(local4); // line:107 cid:405 rid:5414
  // /home/caf/temp/comcom/repo-hash_set/hs_client.e:108
  // lock.unwrap
  assert {:subsumption 0} (local3) != (Void); // type:attached line:108
  call unwrap(local3); // line:108 cid:1 rid:57
  assume HS_LOCK^HS_KEY^.user_inv(Heap, local3);
  // /home/caf/temp/comcom/repo-hash_set/hs_client.e:109
  // i.set_value (3) 	-- OK, `i' is not contained in any set
  assert {:subsumption 0} (local1) != (Void); // type:attached line:109
  call HS_KEY.set_value(local1, 3); // line:109 cid:404 rid:5426
  // /home/caf/temp/comcom/repo-hash_set/hs_client.e:110
  // lock.wrap
  assert {:subsumption 0} (local3) != (Void); // type:attached line:110
  if (*) {
    assert Set#Equal(Heap[local3, subjects], Heap[local3, HS_LOCK^HS_KEY^.sets]); // type:inv tag:subjects_definition line:110 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert (forall i_84: ref :: (Heap[local3, HS_LOCK^HS_KEY^.sets][i_84]) ==> ((Heap[i_84, HS_SET^HS_KEY^.lock]) == (local3))); // type:inv tag:subjects_lock line:110 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert (forall i_85: ref :: (Heap[local3, HS_LOCK^HS_KEY^.sets][i_85]) ==> ((forall i_86: ref :: (Heap[i_85, HS_SET^HS_KEY^.set][i_86]) ==> (Heap[local3, owns][i_86])))); // type:inv tag:owns_items line:110 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#Disjoint(Heap[local3, subjects], Heap[local3, owns]); // type:inv tag:no_owned_sets line:110 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert (forall i_87: ref :: (Heap[local3, HS_LOCK^HS_KEY^.sets][i_87]) ==> ((forall i_88: ref :: (Heap[i_87, HS_SET^HS_KEY^.set][i_88]) ==> (((Seq#Length(Heap[i_87, HS_SET^HS_KEY^.buckets])) > (0)) && (Seq#Has(Seq#Item(Heap[i_87, HS_SET^HS_KEY^.buckets], fun.HS_SET^HS_KEY^.bucket_index(Heap, i_87, fun.HS_KEY.hash_code_(Heap, i_88), Seq#Length(Heap[i_87, HS_SET^HS_KEY^.buckets]))), i_88)))))); // type:inv tag:valid_buckets line:110 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert (forall i_89: ref :: (Heap[local3, HS_LOCK^HS_KEY^.sets][i_89]) ==> ((forall i_90: ref :: (Heap[i_89, HS_SET^HS_KEY^.set][i_90]) ==> ((forall i_91: ref :: (Heap[i_89, HS_SET^HS_KEY^.set][i_91]) ==> (((i_90) != (Void)) && ((i_91) != (Void)) && (((i_90) != (i_91)) ==> (!(fun.HS_KEY.is_model_equal(Heap, i_90, i_91)))))))))); // type:inv tag:no_duplicates line:110 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert (forall i_92: ref :: (Heap[local3, HS_LOCK^HS_KEY^.sets][i_92]) ==> (Heap[i_92, observers][local3])); // type:inv tag:adm2 line:110 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[local3, observers]); // type:inv tag:no_observers line:110 cid:1 rid:55
    assume false;
  }
  call wrap(local3); // line:110 cid:1 rid:55
  if (*) {
    assert Set#IsEmpty(Heap[Current, observers]); // type:inv tag:default_observers line:132 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, subjects]); // type:inv tag:default_subjects line:132 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, owns]); // type:inv tag:default_owns line:132 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert admissibility2(Heap, Current); // type:inv tag:A2 line:132 cid:1 rid:55
    assume false;
  }
  call wrap(Current); // default:wrapping cid:1 rid:55 line:111
}

function { :inline } HS_LOCK^HS_KEY^.user_inv(heap: HeapType, current: ref) returns (bool) {
  (Set#Equal(heap[current, subjects], heap[current, HS_LOCK^HS_KEY^.sets])) && ((forall i_66: ref :: (heap[current, HS_LOCK^HS_KEY^.sets][i_66]) ==> ((heap[i_66, HS_SET^HS_KEY^.lock]) == (current)))) && ((forall i_67: ref :: (heap[current, HS_LOCK^HS_KEY^.sets][i_67]) ==> ((forall i_68: ref :: (heap[i_67, HS_SET^HS_KEY^.set][i_68]) ==> (heap[current, owns][i_68]))))) && (Set#Disjoint(heap[current, subjects], heap[current, owns])) && ((forall i_69: ref :: (heap[current, HS_LOCK^HS_KEY^.sets][i_69]) ==> ((forall i_70: ref :: (heap[i_69, HS_SET^HS_KEY^.set][i_70]) ==> (((Seq#Length(heap[i_69, HS_SET^HS_KEY^.buckets])) > (0)) && (Seq#Has(Seq#Item(heap[i_69, HS_SET^HS_KEY^.buckets], fun.HS_SET^HS_KEY^.bucket_index(heap, i_69, fun.HS_KEY.hash_code_(heap, i_70), Seq#Length(heap[i_69, HS_SET^HS_KEY^.buckets]))), i_70))))))) && ((forall i_71: ref :: (heap[current, HS_LOCK^HS_KEY^.sets][i_71]) ==> ((forall i_72: ref :: (heap[i_71, HS_SET^HS_KEY^.set][i_72]) ==> ((forall i_73: ref :: (heap[i_71, HS_SET^HS_KEY^.set][i_73]) ==> (((i_72) != (Void)) && ((i_73) != (Void)) && (((i_72) != (i_73)) ==> (!(fun.HS_KEY.is_model_equal(heap, i_72, i_73))))))))))) && ((forall i_74: ref :: (heap[current, HS_LOCK^HS_KEY^.sets][i_74]) ==> (heap[i_74, observers][current]))) && (Set#IsEmpty(heap[current, observers]))
}

procedure HS_CLIENT.test_modification_fail(Current: ref);
  free requires attached_exact(Heap, Current, HS_CLIENT); // info:type property for argument Current
  modifies Heap;
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.HS_CLIENT.test_modification_fail(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.HS_CLIENT.test_modification_fail(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);
  requires is_wrapped(Heap, Current); // type:pre tag:default_is_wrapped default:contracts
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts



function { :inline } variant.HS_CLIENT.test_modification_fail.1(heap: HeapType, current: ref) returns (int) {
  0
}

implementation HS_CLIENT.test_modification_fail(Current: ref)
{
  var temp_93: ref;
  var temp_94: ref;
  var temp_95: ref;
  var local1: ref where detachable(Heap, local1, HS_KEY);
  var local2: ref where detachable_exact(Heap, local2, HS_LOCK^HS_KEY^);
  var local3: ref where detachable(Heap, local3, HS_SET^HS_KEY^);

  init_locals:
  temp_93 := Void;
  temp_94 := Void;
  temp_95 := Void;
  local1 := Void;
  local2 := Void;
  local3 := Void;

  entry:
  assume {:captureState "HS_CLIENT.test_modification_fail"} true;
  call unwrap(Current); // default:wrapping cid:1 rid:57 line:113
  assume HS_CLIENT.user_inv(Heap, Current);
  // /home/caf/temp/comcom/repo-hash_set/hs_client.e:120
  // create lock
  call temp_93 := allocate(HS_LOCK^HS_KEY^); // line:-1
  call create.HS_LOCK^HS_KEY^.default_create(temp_93); // line:120 cid:408 rid:35
  local2 := temp_93;
  // /home/caf/temp/comcom/repo-hash_set/hs_client.e:121
  // create i.set_value (1)
  call temp_94 := allocate(HS_KEY); // line:-1
  call create.HS_KEY.set_value(temp_94, 1); // line:121 cid:404 rid:5426
  local1 := temp_94;
  // /home/caf/temp/comcom/repo-hash_set/hs_client.e:122
  // lock.lock (i)
  assert {:subsumption 0} (local2) != (Void); // type:attached line:122
  call HS_LOCK^HS_KEY^.lock(local2, local1); // line:122 cid:408 rid:5403
  // /home/caf/temp/comcom/repo-hash_set/hs_client.e:124
  // create s.make (lock)
  call temp_95 := allocate(HS_SET^HS_KEY^); // line:-1
  call create.HS_SET^HS_KEY^.make(temp_95, local2); // line:124 cid:405 rid:5409
  local3 := temp_95;
  // /home/caf/temp/comcom/repo-hash_set/hs_client.e:125
  // check s.inv end
  assert {:subsumption 0} (local3) != (Void); // type:attached line:125
  assert user_inv(Heap, local3); // type:check line:125
  // /home/caf/temp/comcom/repo-hash_set/hs_client.e:126
  // lock.add_set (s)
  assert {:subsumption 0} (local2) != (Void); // type:attached line:126
  call HS_LOCK^HS_KEY^.add_set(local2, local3); // line:126 cid:408 rid:5402
  // /home/caf/temp/comcom/repo-hash_set/hs_client.e:127
  // s.extend (i)
  assert {:subsumption 0} (local3) != (Void); // type:attached line:127
  call HS_SET^HS_KEY^.extend(local3, local1); // line:127 cid:405 rid:5411
  // /home/caf/temp/comcom/repo-hash_set/hs_client.e:129
  // lock.unwrap
  assert {:subsumption 0} (local2) != (Void); // type:attached line:129
  call unwrap(local2); // line:129 cid:1 rid:57
  assume HS_LOCK^HS_KEY^.user_inv(Heap, local2);
  // /home/caf/temp/comcom/repo-hash_set/hs_client.e:130
  // i.set_value (3) 	-- Bad: `i' will be in a wrong bucket for `s'
  assert {:subsumption 0} (local1) != (Void); // type:attached line:130
  call HS_KEY.set_value(local1, 3); // line:130 cid:404 rid:5426
  // /home/caf/temp/comcom/repo-hash_set/hs_client.e:131
  // lock.wrap			-- so we cannot wrap the lock here
  assert {:subsumption 0} (local2) != (Void); // type:attached line:131
  if (*) {
    assert Set#Equal(Heap[local2, subjects], Heap[local2, HS_LOCK^HS_KEY^.sets]); // type:inv tag:subjects_definition line:131 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert (forall i_96: ref :: (Heap[local2, HS_LOCK^HS_KEY^.sets][i_96]) ==> ((Heap[i_96, HS_SET^HS_KEY^.lock]) == (local2))); // type:inv tag:subjects_lock line:131 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert (forall i_97: ref :: (Heap[local2, HS_LOCK^HS_KEY^.sets][i_97]) ==> ((forall i_98: ref :: (Heap[i_97, HS_SET^HS_KEY^.set][i_98]) ==> (Heap[local2, owns][i_98])))); // type:inv tag:owns_items line:131 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#Disjoint(Heap[local2, subjects], Heap[local2, owns]); // type:inv tag:no_owned_sets line:131 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert (forall i_99: ref :: (Heap[local2, HS_LOCK^HS_KEY^.sets][i_99]) ==> ((forall i_100: ref :: (Heap[i_99, HS_SET^HS_KEY^.set][i_100]) ==> (((Seq#Length(Heap[i_99, HS_SET^HS_KEY^.buckets])) > (0)) && (Seq#Has(Seq#Item(Heap[i_99, HS_SET^HS_KEY^.buckets], fun.HS_SET^HS_KEY^.bucket_index(Heap, i_99, fun.HS_KEY.hash_code_(Heap, i_100), Seq#Length(Heap[i_99, HS_SET^HS_KEY^.buckets]))), i_100)))))); // type:inv tag:valid_buckets line:131 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert (forall i_101: ref :: (Heap[local2, HS_LOCK^HS_KEY^.sets][i_101]) ==> ((forall i_102: ref :: (Heap[i_101, HS_SET^HS_KEY^.set][i_102]) ==> ((forall i_103: ref :: (Heap[i_101, HS_SET^HS_KEY^.set][i_103]) ==> (((i_102) != (Void)) && ((i_103) != (Void)) && (((i_102) != (i_103)) ==> (!(fun.HS_KEY.is_model_equal(Heap, i_102, i_103)))))))))); // type:inv tag:no_duplicates line:131 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert (forall i_104: ref :: (Heap[local2, HS_LOCK^HS_KEY^.sets][i_104]) ==> (Heap[i_104, observers][local2])); // type:inv tag:adm2 line:131 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[local2, observers]); // type:inv tag:no_observers line:131 cid:1 rid:55
    assume false;
  }
  call wrap(local2); // line:131 cid:1 rid:55
  if (*) {
    assert Set#IsEmpty(Heap[Current, observers]); // type:inv tag:default_observers line:132 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, subjects]); // type:inv tag:default_subjects line:132 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, owns]); // type:inv tag:default_owns line:132 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert admissibility2(Heap, Current); // type:inv tag:A2 line:132 cid:1 rid:55
    assume false;
  }
  call wrap(Current); // default:wrapping cid:1 rid:55 line:132
}

const unique HS_KEY: Type;

axiom ((HS_KEY) <: (HS_HASHABLE));

axiom ((forall t: Type :: { (HS_KEY) <: (t) } ((HS_KEY) <: (t)) <==> (((t) == (HS_KEY)) || ((HS_HASHABLE) <: (t)))));

axiom ((FieldId(allocated, HS_KEY)) == (-1));

axiom ((FieldId(closed, HS_KEY)) == (-2));

axiom ((FieldId(owner, HS_KEY)) == (-3));

axiom ((FieldId(owns, HS_KEY)) == (-4));

axiom ((FieldId(observers, HS_KEY)) == (-5));

axiom ((FieldId(subjects, HS_KEY)) == (-6));

axiom ((forall <T8> $f: Field T8 :: { IsModelField($f, HS_KEY) } (IsModelField($f, HS_KEY)) <==> ((($f) == (subjects)) || (($f) == (observers)))));

function { :inline } HS_KEY.user_inv(heap: HeapType, current: ref) returns (bool) {
  (Set#IsEmpty(heap[current, observers])) && (Set#IsEmpty(heap[current, subjects])) && (Set#IsEmpty(heap[current, owns])) && (admissibility2(heap, current))
}

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached_exact(heap, current, HS_KEY)) ==> ((user_inv(heap, current)) <==> (HS_KEY.user_inv(heap, current)))));

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached(heap, current, HS_KEY)) ==> ((user_inv(heap, current)) ==> (HS_KEY.user_inv(heap, current)))));

procedure HS_KEY.invariant_admissibility_check(Current: ref);
  requires attached_exact(Heap, Current, HS_KEY);



implementation HS_KEY.invariant_admissibility_check(Current: ref)
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

procedure HS_KEY.hash_code(Current: ref) returns (Result: int where is_integer_32(Result));
  free requires attached_exact(Heap, Current, HS_KEY); // info:type property for argument Current
  modifies Heap;
  requires is_closed(Heap, Current); // type:pre line:19
  ensures pre.fun.HS_KEY.hash_code_(Heap, Current); // type:check tag:function_precondition line:23 cid:404 rid:5424
  ensures (Result) == (fun.HS_KEY.hash_code_(Heap, Current)); // type:post line:23
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.HS_KEY.hash_code(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.HS_KEY.hash_code(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.HS_KEY.hash_code(Heap, Current), readable);
  free ensures (Result) == (fun.HS_KEY.hash_code(old(Heap), Current));



function fun.HS_KEY.hash_code(heap: HeapType, current: ref) returns (int);

axiom ((forall heap: HeapType, current: ref :: { fun.HS_KEY.hash_code(heap, current) } (pre.fun.HS_KEY.hash_code(heap, current)) ==> (((fun.HS_KEY.hash_code(heap, current)) == (fun.HS_KEY.hash_code_(heap, current))) && (is_integer_32(fun.HS_KEY.hash_code(heap, current))))));

axiom ((forall h: HeapType, h': HeapType, current: ref :: { HeapSucc(h, h'), fun.HS_KEY.hash_code(h, current), fun.HS_KEY.hash_code(h', current) } ((HeapSucc(h, h')) && (pre.fun.HS_KEY.hash_code(h, current)) && (pre.fun.HS_KEY.hash_code(h', current)) && (same_inside(h, h', read.fun.HS_KEY.hash_code(h, current)))) ==> ((fun.HS_KEY.hash_code(h, current)) == (fun.HS_KEY.hash_code(h', current)))));

function { :inline } variant.HS_KEY.hash_code.1(heap: HeapType, current: ref) returns (int) {
  0
}

implementation HS_KEY.hash_code(Current: ref) returns (Result: int)
{

  init_locals:
  Result := 0;

  entry:
  assume {:captureState "HS_KEY.hash_code"} true;
  // /home/caf/temp/comcom/repo-hash_set/hs_key.e:24
  // Result := value.abs
  assert readable[Current, HS_KEY.value]; // type:access tag:attribute_readable line:24 cid:404 rid:5425
  Result := abs(Heap[Current, HS_KEY.value]);
}

procedure create.HS_KEY.set_value(Current: ref, v: int);
  free requires attached_exact(Heap, Current, HS_KEY); // info:type property for argument Current
  free requires is_integer_32(v); // info:type property for argument v
  modifies Heap;
  ensures (Heap[Current, HS_KEY.value]) == (v); // type:post line:34
  requires (forall <T9> $f: Field T9 :: (($f) != (allocated)) ==> ((Heap[Current, $f]) == (Default($f))));
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.HS_KEY.set_value(Heap, Current, v), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.HS_KEY.set_value(old(Heap), Current, v));
  free ensures HeapSucc(old(Heap), Heap);
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts



implementation create.HS_KEY.set_value(Current: ref, v: int)
{
  entry:
  assume {:captureState "create.HS_KEY.set_value"} true;
  // /home/caf/temp/comcom/repo-hash_set/hs_key.e:32
  // value := v
  call update_heap(Current, HS_KEY.value, v); // line:32
  if (*) {
    assert Set#IsEmpty(Heap[Current, observers]); // type:inv tag:default_observers line:35 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, subjects]); // type:inv tag:default_subjects line:35 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, owns]); // type:inv tag:default_owns line:35 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert admissibility2(Heap, Current); // type:inv tag:A2 line:35 cid:1 rid:55
    assume false;
  }
  call wrap(Current); // default:wrapping cid:1 rid:55 line:35
}

procedure HS_KEY.set_value(Current: ref, v: int);
  free requires attached_exact(Heap, Current, HS_KEY); // info:type property for argument Current
  free requires is_integer_32(v); // info:type property for argument v
  modifies Heap;
  ensures (Heap[Current, HS_KEY.value]) == (v); // type:post line:34
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.HS_KEY.set_value(Heap, Current, v), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.HS_KEY.set_value(old(Heap), Current, v));
  free ensures HeapSucc(old(Heap), Heap);
  requires is_wrapped(Heap, Current); // type:pre tag:default_is_wrapped default:contracts
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts



function { :inline } variant.HS_KEY.set_value.1(heap: HeapType, current: ref, v: int) returns (int) {
  v
}

implementation HS_KEY.set_value(Current: ref, v: int)
{
  entry:
  assume {:captureState "HS_KEY.set_value"} true;
  call unwrap(Current); // default:wrapping cid:1 rid:57 line:29
  assume HS_KEY.user_inv(Heap, Current);
  // /home/caf/temp/comcom/repo-hash_set/hs_key.e:32
  // value := v
  call update_heap(Current, HS_KEY.value, v); // line:32
  if (*) {
    assert Set#IsEmpty(Heap[Current, observers]); // type:inv tag:default_observers line:35 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, subjects]); // type:inv tag:default_subjects line:35 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, owns]); // type:inv tag:default_owns line:35 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert admissibility2(Heap, Current); // type:inv tag:A2 line:35 cid:1 rid:55
    assume false;
  }
  call wrap(Current); // default:wrapping cid:1 rid:55 line:35
}

procedure HS_KEY.hash_code_(Current: ref) returns (Result: int where is_integer_32(Result));
  free requires attached_exact(Heap, Current, HS_KEY); // info:type property for argument Current
  modifies Heap;
  ensures (0) <= (Result); // type:post tag:non_negative line:37
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.HS_KEY.hash_code_(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.HS_KEY.hash_code_(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.HS_KEY.hash_code_(Heap, Current), readable);



function fun.HS_KEY.hash_code_(heap: HeapType, current: ref) returns (int);

function fun0.HS_KEY.hash_code_(heap: HeapType, current: ref) returns (int);

axiom ((forall heap: HeapType, current: ref :: { fun.HS_KEY.hash_code_(heap, current) } (pre.fun.HS_KEY.hash_code_(heap, current)) ==> (((0) <= (fun.HS_KEY.hash_code_(heap, current))) && (is_integer_32(fun.HS_KEY.hash_code_(heap, current))))));

axiom ((forall heap: HeapType, current: ref :: { fun.HS_KEY.hash_code_(heap, current) } { trigger.fun.HS_KEY.hash_code_(heap, current) } (pre.fun.HS_KEY.hash_code_(heap, current)) ==> ((fun.HS_KEY.hash_code_(heap, current)) == (abs(heap[current, HS_KEY.value])))));

axiom ((forall heap: HeapType, current: ref :: { fun.HS_KEY.hash_code_(heap, current) } (fun.HS_KEY.hash_code_(heap, current)) == (fun0.HS_KEY.hash_code_(heap, current))));

axiom ((forall h: HeapType, h': HeapType, current: ref :: { HeapSucc(h, h'), fun0.HS_KEY.hash_code_(h, current), fun0.HS_KEY.hash_code_(h', current) } ((HeapSucc(h, h')) && (pre.fun.HS_KEY.hash_code_(h, current)) && (pre.fun.HS_KEY.hash_code_(h', current)) && (same_inside(h, h', read.fun.HS_KEY.hash_code_(h, current)))) ==> ((fun0.HS_KEY.hash_code_(h, current)) == (fun0.HS_KEY.hash_code_(h', current)))));

function { :inline } variant.HS_KEY.hash_code_.1(heap: HeapType, current: ref) returns (int) {
  0
}

implementation HS_KEY.hash_code_(Current: ref) returns (Result: int)
{

  init_locals:
  Result := 0;

  entry:
  assume {:captureState "HS_KEY.hash_code_"} true;
  // /home/caf/temp/comcom/repo-hash_set/hs_key.e:44
  // Result := value.abs
  assert readable[Current, HS_KEY.value]; // type:access tag:attribute_readable line:44 cid:404 fid:78
  Result := abs(Heap[Current, HS_KEY.value]);
}

procedure HS_KEY.is_model_equal(Current: ref, other: ref) returns (Result: bool where true);
  free requires attached_exact(Heap, Current, HS_KEY); // info:type property for argument Current
  free requires detachable_exact(Heap, other, HS_KEY); // info:type property for argument other
  modifies Heap;
  requires (other) != (Void); // type:pre line:673
  ensures (other) != (Void); // type:attached tag:definition line:55
  ensures (Result) == ((abs(Heap[Current, HS_KEY.value])) == (abs(Heap[other, HS_KEY.value]))); // type:post tag:definition line:55
  ensures ((other) == (Current)) ==> (Result); // type:post tag:reflexive line:679
  ensures pre.fun.HS_KEY.is_model_equal(Heap, other, Current); // type:check tag:function_precondition line:680 cid:404 rid:81
  ensures (Result) == (fun.HS_KEY.is_model_equal(Heap, other, Current)); // type:post tag:symmetric line:680
  ensures (Result) ==> (pre.fun.HS_KEY.hash_code_(Heap, Current)); // type:check tag:function_precondition line:47 cid:404 rid:5424
  ensures (Result) ==> ((other) != (Void)); // type:attached tag:agrees_with_hash line:47
  ensures (Result) ==> (pre.fun.HS_KEY.hash_code_(Heap, other)); // type:check tag:function_precondition line:47 cid:404 rid:5424
  ensures (Result) ==> ((fun.HS_KEY.hash_code_(Heap, Current)) == (fun.HS_KEY.hash_code_(Heap, other))); // type:post tag:agrees_with_hash line:47
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.HS_KEY.is_model_equal(Heap, Current, other), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.HS_KEY.is_model_equal(old(Heap), Current, other));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.HS_KEY.is_model_equal(Heap, Current, other), readable);
  free ensures (Result) == (fun.HS_KEY.is_model_equal(old(Heap), Current, other));



function fun.HS_KEY.is_model_equal(heap: HeapType, current: ref, other: ref) returns (bool);

axiom ((forall heap: HeapType, current: ref, other: ref :: { fun.HS_KEY.is_model_equal(heap, current, other) } (pre.fun.HS_KEY.is_model_equal(heap, current, other)) ==> (((fun.HS_KEY.is_model_equal(heap, current, other)) == ((abs(heap[current, HS_KEY.value])) == (abs(heap[other, HS_KEY.value])))) && (((other) == (current)) ==> (fun.HS_KEY.is_model_equal(heap, current, other))) && ((fun.HS_KEY.is_model_equal(heap, current, other)) == (fun.HS_KEY.is_model_equal(heap, other, current))) && ((fun.HS_KEY.is_model_equal(heap, current, other)) ==> ((fun.HS_KEY.hash_code_(heap, current)) == (fun.HS_KEY.hash_code_(heap, other)))))));

axiom ((forall h: HeapType, h': HeapType, current: ref, other: ref :: { HeapSucc(h, h'), fun.HS_KEY.is_model_equal(h, current, other), fun.HS_KEY.is_model_equal(h', current, other) } ((HeapSucc(h, h')) && (pre.fun.HS_KEY.is_model_equal(h, current, other)) && (pre.fun.HS_KEY.is_model_equal(h', current, other)) && (same_inside(h, h', read.fun.HS_KEY.is_model_equal(h, current, other)))) ==> ((fun.HS_KEY.is_model_equal(h, current, other)) == (fun.HS_KEY.is_model_equal(h', current, other)))));

function { :inline } variant.HS_KEY.is_model_equal.1(heap: HeapType, current: ref, other: ref) returns (ref) {
  other
}

implementation HS_KEY.is_model_equal(Current: ref, other: ref) returns (Result: bool)
{

  init_locals:
  Result := false;

  entry:
  assume {:captureState "HS_KEY.is_model_equal"} true;
  // /home/caf/temp/comcom/repo-hash_set/hs_key.e:53
  // Result := value.abs = other.value.abs
  assert readable[Current, HS_KEY.value]; // type:access tag:attribute_readable line:53 cid:404 rid:5425
  assert {:subsumption 0} (other) != (Void); // type:attached line:53
  assert readable[other, HS_KEY.value]; // type:access tag:attribute_readable line:53 cid:404 rid:5425
  Result := (abs(Heap[Current, HS_KEY.value])) == (abs(Heap[other, HS_KEY.value]));
}

procedure HS_KEY.lemma_transitive(Current: ref, x: ref, ys: Set (ref));
  free requires attached_exact(Heap, Current, HS_KEY); // info:type property for argument Current
  free requires detachable_exact(Heap, x, HS_KEY); // info:type property for argument x
  free requires Set#ItemsType(Heap, ys, HS_KEY); // info:type property for argument ys
  requires pre.fun.HS_KEY.is_model_equal(Heap, Current, x); // type:check tag:function_precondition line:689 cid:404 rid:81
  requires fun.HS_KEY.is_model_equal(Heap, Current, x); // type:pre tag:equal_x line:689
  requires Set#NonNull(ys); // type:pre tag:ys_exist line:690
  ensures (forall i_105: ref :: (ys[i_105]) ==> (pre.fun.HS_KEY.is_model_equal(Heap, Current, i_105))); // type:check tag:function_precondition line:693 cid:404 rid:81
  ensures (x) != (Void); // type:attached tag:x_in_ys_iff_current_in_ys line:693
  ensures (forall i_106: ref :: (ys[i_106]) ==> (pre.fun.HS_KEY.is_model_equal(Heap, x, i_106))); // type:check tag:function_precondition line:693 cid:404 rid:81
  ensures ((exists i_105: ref :: (ys[i_105]) && (fun.HS_KEY.is_model_equal(Heap, Current, i_105)))) == ((exists i_106: ref :: (ys[i_106]) && (fun.HS_KEY.is_model_equal(Heap, x, i_106)))); // type:post tag:x_in_ys_iff_current_in_ys line:693
  free requires global(Heap);
  free requires global_permissive();



function { :inline } variant.HS_KEY.lemma_transitive.1(heap: HeapType, current: ref, x: ref, ys: Set (ref)) returns (ref) {
  x
}

function { :inline } variant.HS_KEY.lemma_transitive.2(heap: HeapType, current: ref, x: ref, ys: Set (ref)) returns (Set (ref)) {
  ys
}

implementation HS_KEY.lemma_transitive(Current: ref, x: ref, ys: Set (ref))
{
  entry:
  assume {:captureState "HS_KEY.lemma_transitive"} true;
}

const unique HS_HASHABLE: Type;

axiom ((HS_HASHABLE) <: (ANY));

axiom ((forall t: Type :: { (HS_HASHABLE) <: (t) } ((HS_HASHABLE) <: (t)) <==> (((t) == (HS_HASHABLE)) || ((ANY) <: (t)))));

axiom ((FieldId(allocated, HS_HASHABLE)) == (-1));

axiom ((FieldId(closed, HS_HASHABLE)) == (-2));

axiom ((FieldId(owner, HS_HASHABLE)) == (-3));

axiom ((FieldId(owns, HS_HASHABLE)) == (-4));

axiom ((FieldId(observers, HS_HASHABLE)) == (-5));

axiom ((FieldId(subjects, HS_HASHABLE)) == (-6));

axiom ((forall <T10> $f: Field T10 :: { IsModelField($f, HS_HASHABLE) } (IsModelField($f, HS_HASHABLE)) <==> ((($f) == (subjects)) || (($f) == (observers)))));

function { :inline } HS_HASHABLE.user_inv(heap: HeapType, current: ref) returns (bool) {
  admissibility2(heap, current)
}

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached_exact(heap, current, HS_HASHABLE)) ==> ((user_inv(heap, current)) <==> (HS_HASHABLE.user_inv(heap, current)))));

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached(heap, current, HS_HASHABLE)) ==> ((user_inv(heap, current)) ==> (HS_HASHABLE.user_inv(heap, current)))));

procedure HS_HASHABLE.invariant_admissibility_check(Current: ref);
  requires attached_exact(Heap, Current, HS_HASHABLE);



implementation HS_HASHABLE.invariant_admissibility_check(Current: ref)
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

procedure HS_HASHABLE.hash_code(Current: ref) returns (Result: int where is_integer_32(Result));
  free requires attached_exact(Heap, Current, HS_HASHABLE); // info:type property for argument Current
  modifies Heap;
  requires is_closed(Heap, Current); // type:pre line:19
  ensures pre.fun.HS_HASHABLE.hash_code_(Heap, Current); // type:check tag:function_precondition line:23 cid:406 rid:5424
  ensures (Result) == (fun.HS_HASHABLE.hash_code_(Heap, Current)); // type:post line:23
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.HS_HASHABLE.hash_code(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.HS_HASHABLE.hash_code(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.HS_HASHABLE.hash_code(Heap, Current), readable);
  free ensures (Result) == (fun.HS_HASHABLE.hash_code(old(Heap), Current));



function fun.HS_HASHABLE.hash_code(heap: HeapType, current: ref) returns (int);

axiom ((forall heap: HeapType, current: ref :: { fun.HS_HASHABLE.hash_code(heap, current) } (pre.fun.HS_HASHABLE.hash_code(heap, current)) ==> (((fun.HS_HASHABLE.hash_code(heap, current)) == (fun.HS_HASHABLE.hash_code_(heap, current))) && (is_integer_32(fun.HS_HASHABLE.hash_code(heap, current))))));

axiom ((forall h: HeapType, h': HeapType, current: ref :: { HeapSucc(h, h'), fun.HS_HASHABLE.hash_code(h, current), fun.HS_HASHABLE.hash_code(h', current) } ((HeapSucc(h, h')) && (pre.fun.HS_HASHABLE.hash_code(h, current)) && (pre.fun.HS_HASHABLE.hash_code(h', current)) && (same_inside(h, h', read.fun.HS_HASHABLE.hash_code(h, current)))) ==> ((fun.HS_HASHABLE.hash_code(h, current)) == (fun.HS_HASHABLE.hash_code(h', current)))));

procedure HS_HASHABLE.hash_code_(Current: ref) returns (Result: int where is_integer_32(Result));
  free requires attached_exact(Heap, Current, HS_HASHABLE); // info:type property for argument Current
  modifies Heap;
  ensures (0) <= (Result); // type:post tag:non_negative line:37
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.HS_HASHABLE.hash_code_(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.HS_HASHABLE.hash_code_(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.HS_HASHABLE.hash_code_(Heap, Current), readable);
  free ensures (Result) == (fun.HS_HASHABLE.hash_code_(old(Heap), Current));



function fun.HS_HASHABLE.hash_code_(heap: HeapType, current: ref) returns (int);

axiom ((forall heap: HeapType, current: ref :: { fun.HS_HASHABLE.hash_code_(heap, current) } (pre.fun.HS_HASHABLE.hash_code_(heap, current)) ==> (((0) <= (fun.HS_HASHABLE.hash_code_(heap, current))) && (is_integer_32(fun.HS_HASHABLE.hash_code_(heap, current))))));

axiom ((forall h: HeapType, h': HeapType, current: ref :: { HeapSucc(h, h'), fun.HS_HASHABLE.hash_code_(h, current), fun.HS_HASHABLE.hash_code_(h', current) } ((HeapSucc(h, h')) && (pre.fun.HS_HASHABLE.hash_code_(h, current)) && (pre.fun.HS_HASHABLE.hash_code_(h', current)) && (same_inside(h, h', read.fun.HS_HASHABLE.hash_code_(h, current)))) ==> ((fun.HS_HASHABLE.hash_code_(h, current)) == (fun.HS_HASHABLE.hash_code_(h', current)))));

procedure HS_HASHABLE.is_model_equal(Current: ref, other: ref) returns (Result: bool where true);
  free requires attached_exact(Heap, Current, HS_HASHABLE); // info:type property for argument Current
  free requires detachable_exact(Heap, other, HS_HASHABLE); // info:type property for argument other
  modifies Heap;
  requires (other) != (Void); // type:pre line:673
  ensures (Result) ==> (pre.fun.HS_HASHABLE.hash_code_(Heap, Current)); // type:check tag:function_precondition line:47 cid:406 rid:5424
  ensures (Result) ==> ((other) != (Void)); // type:attached tag:agrees_with_hash line:47
  ensures (Result) ==> (pre.fun.HS_HASHABLE.hash_code_(Heap, other)); // type:check tag:function_precondition line:47 cid:406 rid:5424
  ensures (Result) ==> ((fun.HS_HASHABLE.hash_code_(Heap, Current)) == (fun.HS_HASHABLE.hash_code_(Heap, other))); // type:post tag:agrees_with_hash line:47
  ensures ((other) == (Current)) ==> (Result); // type:post tag:reflexive line:679
  ensures (other) != (Void); // type:attached tag:symmetric line:680
  ensures pre.fun.HS_HASHABLE.is_model_equal(Heap, other, Current); // type:check tag:function_precondition line:680 cid:406 rid:81
  ensures (Result) == (fun.HS_HASHABLE.is_model_equal(Heap, other, Current)); // type:post tag:symmetric line:680
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.HS_HASHABLE.is_model_equal(Heap, Current, other), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.HS_HASHABLE.is_model_equal(old(Heap), Current, other));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.HS_HASHABLE.is_model_equal(Heap, Current, other), readable);
  free ensures (Result) == (fun.HS_HASHABLE.is_model_equal(old(Heap), Current, other));



function fun.HS_HASHABLE.is_model_equal(heap: HeapType, current: ref, other: ref) returns (bool);

axiom ((forall heap: HeapType, current: ref, other: ref :: { fun.HS_HASHABLE.is_model_equal(heap, current, other) } (pre.fun.HS_HASHABLE.is_model_equal(heap, current, other)) ==> (((fun.HS_HASHABLE.is_model_equal(heap, current, other)) ==> ((fun.HS_HASHABLE.hash_code_(heap, current)) == (fun.HS_HASHABLE.hash_code_(heap, other)))) && (((other) == (current)) ==> (fun.HS_HASHABLE.is_model_equal(heap, current, other))) && ((fun.HS_HASHABLE.is_model_equal(heap, current, other)) == (fun.HS_HASHABLE.is_model_equal(heap, other, current))))));

axiom ((forall h: HeapType, h': HeapType, current: ref, other: ref :: { HeapSucc(h, h'), fun.HS_HASHABLE.is_model_equal(h, current, other), fun.HS_HASHABLE.is_model_equal(h', current, other) } ((HeapSucc(h, h')) && (pre.fun.HS_HASHABLE.is_model_equal(h, current, other)) && (pre.fun.HS_HASHABLE.is_model_equal(h', current, other)) && (same_inside(h, h', read.fun.HS_HASHABLE.is_model_equal(h, current, other)))) ==> ((fun.HS_HASHABLE.is_model_equal(h, current, other)) == (fun.HS_HASHABLE.is_model_equal(h', current, other)))));

const unique HS_SET^HS_HASHABLE^: Type;

axiom ((HS_SET^HS_HASHABLE^) <: (ANY));

axiom ((forall t: Type :: { (HS_SET^HS_HASHABLE^) <: (t) } ((HS_SET^HS_HASHABLE^) <: (t)) <==> (((t) == (HS_SET^HS_HASHABLE^)) || ((ANY) <: (t)))));

axiom ((FieldId(allocated, HS_SET^HS_HASHABLE^)) == (-1));

axiom ((FieldId(closed, HS_SET^HS_HASHABLE^)) == (-2));

axiom ((FieldId(owner, HS_SET^HS_HASHABLE^)) == (-3));

axiom ((FieldId(owns, HS_SET^HS_HASHABLE^)) == (-4));

axiom ((FieldId(observers, HS_SET^HS_HASHABLE^)) == (-5));

axiom ((FieldId(subjects, HS_SET^HS_HASHABLE^)) == (-6));

axiom ((forall <T11> $f: Field T11 :: { IsModelField($f, HS_SET^HS_HASHABLE^) } (IsModelField($f, HS_SET^HS_HASHABLE^)) <==> ((($f) == (HS_SET^HS_HASHABLE^.set)) || (($f) == (HS_SET^HS_HASHABLE^.lock)) || (($f) == (subjects)) || (($f) == (observers)))));

function { :inline } HS_SET^HS_HASHABLE^.user_inv(heap: HeapType, current: ref) returns (bool) {
  (!(Seq#IsEmpty(heap[current, HS_SET^HS_HASHABLE^.buckets]))) && (Set#Equal(heap[current, observers], Set#Singleton(heap[current, HS_SET^HS_HASHABLE^.lock]))) && (Set#NonNull(heap[current, HS_SET^HS_HASHABLE^.set])) && ((forall i_107: int :: (((1) <= (i_107)) && ((i_107) <= (Seq#Length(heap[current, HS_SET^HS_HASHABLE^.buckets])))) ==> ((forall i_108: int :: (((1) <= (i_108)) && ((i_108) <= (Seq#Length(Seq#Item(heap[current, HS_SET^HS_HASHABLE^.buckets], i_107))))) ==> (heap[current, HS_SET^HS_HASHABLE^.set][Seq#Item(Seq#Item(heap[current, HS_SET^HS_HASHABLE^.buckets], i_107), i_108)]))))) && ((forall i_109: int :: (((1) <= (i_109)) && ((i_109) <= (Seq#Length(heap[current, HS_SET^HS_HASHABLE^.buckets])))) ==> ((forall i_110: int :: (((1) <= (i_110)) && ((i_110) <= (Seq#Length(heap[current, HS_SET^HS_HASHABLE^.buckets])))) ==> ((forall i_111: int :: (((1) <= (i_111)) && ((i_111) <= (Seq#Length(Seq#Item(heap[current, HS_SET^HS_HASHABLE^.buckets], i_109))))) ==> ((forall i_112: int :: (((1) <= (i_112)) && ((i_112) <= (Seq#Length(Seq#Item(heap[current, HS_SET^HS_HASHABLE^.buckets], i_110))))) ==> ((((i_109) != (i_110)) || ((i_111) != (i_112))) ==> ((Seq#Item(Seq#Item(heap[current, HS_SET^HS_HASHABLE^.buckets], i_109), i_111)) != (Seq#Item(Seq#Item(heap[current, HS_SET^HS_HASHABLE^.buckets], i_110), i_112)))))))))))) && (Set#IsEmpty(heap[current, subjects])) && (Set#IsEmpty(heap[current, owns])) && (admissibility2(heap, current))
}

function HS_SET^HS_HASHABLE^.observers.static(heap: HeapType, current: ref) returns (Set (ref)) {
  Set#Singleton(heap[current, HS_SET^HS_HASHABLE^.lock])
}

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached_exact(heap, current, HS_SET^HS_HASHABLE^)) ==> ((user_inv(heap, current)) <==> (HS_SET^HS_HASHABLE^.user_inv(heap, current)))));

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached(heap, current, HS_SET^HS_HASHABLE^)) ==> ((user_inv(heap, current)) ==> (HS_SET^HS_HASHABLE^.user_inv(heap, current)))));

procedure HS_SET.invariant_admissibility_check(Current: ref);
  requires attached_exact(Heap, Current, HS_SET^HS_HASHABLE^);



implementation HS_SET.invariant_admissibility_check(Current: ref)
{
  entry:
  goto pre, a2, a3;
  pre:
  assert user_inv_readable(Heap, Current)[Current, HS_SET^HS_HASHABLE^.buckets]; // type:access tag:attribute_readable line:263 cid:405 fid:89
  assume !(Seq#IsEmpty(Heap[Current, HS_SET^HS_HASHABLE^.buckets]));
  assert user_inv_readable(Heap, Current)[Current, HS_SET^HS_HASHABLE^.lock]; // type:access tag:attribute_readable line:264 cid:405 fid:90
  assume Set#Equal(Heap[Current, observers], Set#Singleton(Heap[Current, HS_SET^HS_HASHABLE^.lock]));
  assert user_inv_readable(Heap, Current)[Current, HS_SET^HS_HASHABLE^.set]; // type:access tag:attribute_readable line:265 cid:405 fid:88
  assume Set#NonNull(Heap[Current, HS_SET^HS_HASHABLE^.set]);
  assert user_inv_readable(Heap, Current)[Current, HS_SET^HS_HASHABLE^.buckets]; // type:access tag:attribute_readable line:266 cid:405 fid:89
  assert user_inv_readable(Heap, Current)[Current, HS_SET^HS_HASHABLE^.buckets]; // type:access tag:attribute_readable line:266 cid:405 fid:89
  assert (forall i_113: int :: (((1) <= (i_113)) && ((i_113) <= (Seq#Length(Heap[Current, HS_SET^HS_HASHABLE^.buckets])))) ==> (pre.fun.MML_SEQUENCE^MML_SEQUENCE^HS_HASHABLE^^.item(Heap[Current, HS_SET^HS_HASHABLE^.buckets], i_113))); // type:check tag:function_precondition line:266 cid:125 rid:3286
  assert user_inv_readable(Heap, Current)[Current, HS_SET^HS_HASHABLE^.set]; // type:access tag:attribute_readable line:266 cid:405 fid:88
  assert user_inv_readable(Heap, Current)[Current, HS_SET^HS_HASHABLE^.buckets]; // type:access tag:attribute_readable line:266 cid:405 fid:89
  assert (forall i_113: int :: (((1) <= (i_113)) && ((i_113) <= (Seq#Length(Heap[Current, HS_SET^HS_HASHABLE^.buckets])))) ==> (pre.fun.MML_SEQUENCE^MML_SEQUENCE^HS_HASHABLE^^.item(Heap[Current, HS_SET^HS_HASHABLE^.buckets], i_113))); // type:check tag:function_precondition line:266 cid:125 rid:3286
  assert (forall i_113: int :: (((1) <= (i_113)) && ((i_113) <= (Seq#Length(Heap[Current, HS_SET^HS_HASHABLE^.buckets])))) ==> ((forall i_114: int :: (((1) <= (i_114)) && ((i_114) <= (Seq#Length(Seq#Item(Heap[Current, HS_SET^HS_HASHABLE^.buckets], i_113))))) ==> (pre.fun.MML_SEQUENCE^HS_HASHABLE^.item(Seq#Item(Heap[Current, HS_SET^HS_HASHABLE^.buckets], i_113), i_114))))); // type:check tag:function_precondition line:266 cid:125 rid:3286
  assume (forall i_113: int :: (((1) <= (i_113)) && ((i_113) <= (Seq#Length(Heap[Current, HS_SET^HS_HASHABLE^.buckets])))) ==> ((forall i_114: int :: (((1) <= (i_114)) && ((i_114) <= (Seq#Length(Seq#Item(Heap[Current, HS_SET^HS_HASHABLE^.buckets], i_113))))) ==> (Heap[Current, HS_SET^HS_HASHABLE^.set][Seq#Item(Seq#Item(Heap[Current, HS_SET^HS_HASHABLE^.buckets], i_113), i_114)]))));
  assert user_inv_readable(Heap, Current)[Current, HS_SET^HS_HASHABLE^.buckets]; // type:access tag:attribute_readable line:268 cid:405 fid:89
  assert user_inv_readable(Heap, Current)[Current, HS_SET^HS_HASHABLE^.buckets]; // type:access tag:attribute_readable line:268 cid:405 fid:89
  assert user_inv_readable(Heap, Current)[Current, HS_SET^HS_HASHABLE^.buckets]; // type:access tag:attribute_readable line:268 cid:405 fid:89
  assert (forall i_115: int :: (((1) <= (i_115)) && ((i_115) <= (Seq#Length(Heap[Current, HS_SET^HS_HASHABLE^.buckets])))) ==> (pre.fun.MML_SEQUENCE^MML_SEQUENCE^HS_HASHABLE^^.item(Heap[Current, HS_SET^HS_HASHABLE^.buckets], i_115))); // type:check tag:function_precondition line:268 cid:125 rid:3286
  assert user_inv_readable(Heap, Current)[Current, HS_SET^HS_HASHABLE^.buckets]; // type:access tag:attribute_readable line:268 cid:405 fid:89
  assert (forall i_116: int :: (((1) <= (i_116)) && ((i_116) <= (Seq#Length(Heap[Current, HS_SET^HS_HASHABLE^.buckets])))) ==> (pre.fun.MML_SEQUENCE^MML_SEQUENCE^HS_HASHABLE^^.item(Heap[Current, HS_SET^HS_HASHABLE^.buckets], i_116))); // type:check tag:function_precondition line:268 cid:125 rid:3286
  assert (true) ==> (user_inv_readable(Heap, Current)[Current, HS_SET^HS_HASHABLE^.buckets]); // type:access tag:attribute_readable line:268 cid:405 fid:89
  assert (forall i_115: int :: (((1) <= (i_115)) && ((i_115) <= (Seq#Length(Heap[Current, HS_SET^HS_HASHABLE^.buckets])))) ==> ((true) ==> (pre.fun.MML_SEQUENCE^MML_SEQUENCE^HS_HASHABLE^^.item(Heap[Current, HS_SET^HS_HASHABLE^.buckets], i_115)))); // type:check tag:function_precondition line:268 cid:125 rid:3286
  assert (forall i_115: int :: (((1) <= (i_115)) && ((i_115) <= (Seq#Length(Heap[Current, HS_SET^HS_HASHABLE^.buckets])))) ==> ((forall i_117: int :: (((1) <= (i_117)) && ((i_117) <= (Seq#Length(Seq#Item(Heap[Current, HS_SET^HS_HASHABLE^.buckets], i_115))))) ==> ((true) ==> (pre.fun.MML_SEQUENCE^HS_HASHABLE^.item(Seq#Item(Heap[Current, HS_SET^HS_HASHABLE^.buckets], i_115), i_117)))))); // type:check tag:function_precondition line:268 cid:125 rid:3286
  assert (true) ==> (user_inv_readable(Heap, Current)[Current, HS_SET^HS_HASHABLE^.buckets]); // type:access tag:attribute_readable line:268 cid:405 fid:89
  assert (forall i_116: int :: (((1) <= (i_116)) && ((i_116) <= (Seq#Length(Heap[Current, HS_SET^HS_HASHABLE^.buckets])))) ==> ((true) ==> (pre.fun.MML_SEQUENCE^MML_SEQUENCE^HS_HASHABLE^^.item(Heap[Current, HS_SET^HS_HASHABLE^.buckets], i_116)))); // type:check tag:function_precondition line:268 cid:125 rid:3286
  assert (forall i_115: int :: (((1) <= (i_115)) && ((i_115) <= (Seq#Length(Heap[Current, HS_SET^HS_HASHABLE^.buckets])))) ==> ((forall i_116: int :: (((1) <= (i_116)) && ((i_116) <= (Seq#Length(Heap[Current, HS_SET^HS_HASHABLE^.buckets])))) ==> ((forall i_117: int :: (((1) <= (i_117)) && ((i_117) <= (Seq#Length(Seq#Item(Heap[Current, HS_SET^HS_HASHABLE^.buckets], i_115))))) ==> ((forall i_118: int :: (((1) <= (i_118)) && ((i_118) <= (Seq#Length(Seq#Item(Heap[Current, HS_SET^HS_HASHABLE^.buckets], i_116))))) ==> ((((i_115) != (i_116)) || ((i_117) != (i_118))) ==> (pre.fun.MML_SEQUENCE^HS_HASHABLE^.item(Seq#Item(Heap[Current, HS_SET^HS_HASHABLE^.buckets], i_116), i_118)))))))))); // type:check tag:function_precondition line:268 cid:125 rid:3286
  assume (forall i_115: int :: (((1) <= (i_115)) && ((i_115) <= (Seq#Length(Heap[Current, HS_SET^HS_HASHABLE^.buckets])))) ==> ((forall i_116: int :: (((1) <= (i_116)) && ((i_116) <= (Seq#Length(Heap[Current, HS_SET^HS_HASHABLE^.buckets])))) ==> ((forall i_117: int :: (((1) <= (i_117)) && ((i_117) <= (Seq#Length(Seq#Item(Heap[Current, HS_SET^HS_HASHABLE^.buckets], i_115))))) ==> ((forall i_118: int :: (((1) <= (i_118)) && ((i_118) <= (Seq#Length(Seq#Item(Heap[Current, HS_SET^HS_HASHABLE^.buckets], i_116))))) ==> ((((i_115) != (i_116)) || ((i_117) != (i_118))) ==> ((Seq#Item(Seq#Item(Heap[Current, HS_SET^HS_HASHABLE^.buckets], i_115), i_117)) != (Seq#Item(Seq#Item(Heap[Current, HS_SET^HS_HASHABLE^.buckets], i_116), i_118)))))))))));
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

procedure create.HS_SET^HS_HASHABLE^.make(Current: ref, l: ref);
  free requires attached_exact(Heap, Current, HS_SET^HS_HASHABLE^); // info:type property for argument Current
  free requires detachable_exact(Heap, l, HS_LOCK^HS_HASHABLE^); // info:type property for argument l
  modifies Heap;
  ensures Set#IsEmpty(Heap[Current, HS_SET^HS_HASHABLE^.set]); // type:post tag:set_empty line:24
  ensures (Heap[Current, HS_SET^HS_HASHABLE^.lock]) == (l); // type:post tag:lock_set line:25
  requires (forall <T12> $f: Field T12 :: (($f) != (allocated)) ==> ((Heap[Current, $f]) == (Default($f))));
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.HS_SET^HS_HASHABLE^.make(Heap, Current, l), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.HS_SET^HS_HASHABLE^.make(old(Heap), Current, l));
  free ensures HeapSucc(old(Heap), Heap);
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts
  requires is_wrapped(Heap, l); // type:pre tag:arg_l_is_wrapped default:contracts
  ensures is_wrapped(Heap, l); // type:post tag:arg_l_is_wrapped default:contracts



implementation create.HS_SET^HS_HASHABLE^.make(Current: ref, l: ref)
{
  var temp_119: Seq (Seq (ref));

  init_locals:
  temp_119 := Seq#Empty();

  entry:
  assume {:captureState "create.HS_SET^HS_HASHABLE^.make"} true;
  // /home/caf/temp/comcom/repo-hash_set/hs_set.e:20
  // create buckets.constant ({MML_SEQUENCE [G]}.empty_sequence, 10)
  assert pre.fun.MML_SEQUENCE^MML_SEQUENCE^HS_HASHABLE^^.constant(Seq#Empty(), 10); // type:check tag:function_precondition line:20 cid:125 rid:3282
  call update_heap(Current, HS_SET^HS_HASHABLE^.buckets, Seq#Constant(Seq#Empty(), 10)); // line:20
  // /home/caf/temp/comcom/repo-hash_set/hs_set.e:21
  // lock := l
  call update_heap(Current, HS_SET^HS_HASHABLE^.lock, l); // line:21
  // /home/caf/temp/comcom/repo-hash_set/hs_set.e:22
  // set_observers ([lock])
  call update_heap(Current, observers, Set#Singleton(Heap[Current, HS_SET^HS_HASHABLE^.lock])); // line:22
  if (modify.HS_SET^HS_HASHABLE^.make(Heap, Current, l)[Current, observers]) {
    call update_heap(Current, observers, HS_SET^HS_HASHABLE^.observers.static(Heap, Current)); // default:observers line:26
  }
  if (*) {
    assert !(Seq#IsEmpty(Heap[Current, HS_SET^HS_HASHABLE^.buckets])); // type:inv tag:buckets_non_empty line:26 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#Equal(Heap[Current, observers], Set#Singleton(Heap[Current, HS_SET^HS_HASHABLE^.lock])); // type:inv tag:observers_definition line:26 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#NonNull(Heap[Current, HS_SET^HS_HASHABLE^.set]); // type:inv tag:set_non_void line:26 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert (forall i_120: int :: (((1) <= (i_120)) && ((i_120) <= (Seq#Length(Heap[Current, HS_SET^HS_HASHABLE^.buckets])))) ==> ((forall i_121: int :: (((1) <= (i_121)) && ((i_121) <= (Seq#Length(Seq#Item(Heap[Current, HS_SET^HS_HASHABLE^.buckets], i_120))))) ==> (Heap[Current, HS_SET^HS_HASHABLE^.set][Seq#Item(Seq#Item(Heap[Current, HS_SET^HS_HASHABLE^.buckets], i_120), i_121)])))); // type:inv tag:set_not_too_small line:26 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert (forall i_122: int :: (((1) <= (i_122)) && ((i_122) <= (Seq#Length(Heap[Current, HS_SET^HS_HASHABLE^.buckets])))) ==> ((forall i_123: int :: (((1) <= (i_123)) && ((i_123) <= (Seq#Length(Heap[Current, HS_SET^HS_HASHABLE^.buckets])))) ==> ((forall i_124: int :: (((1) <= (i_124)) && ((i_124) <= (Seq#Length(Seq#Item(Heap[Current, HS_SET^HS_HASHABLE^.buckets], i_122))))) ==> ((forall i_125: int :: (((1) <= (i_125)) && ((i_125) <= (Seq#Length(Seq#Item(Heap[Current, HS_SET^HS_HASHABLE^.buckets], i_123))))) ==> ((((i_122) != (i_123)) || ((i_124) != (i_125))) ==> ((Seq#Item(Seq#Item(Heap[Current, HS_SET^HS_HASHABLE^.buckets], i_122), i_124)) != (Seq#Item(Seq#Item(Heap[Current, HS_SET^HS_HASHABLE^.buckets], i_123), i_125))))))))))); // type:inv tag:no_precise_duplicates line:26 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, subjects]); // type:inv tag:default_subjects line:26 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, owns]); // type:inv tag:default_owns line:26 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert admissibility2(Heap, Current); // type:inv tag:A2 line:26 cid:1 rid:55
    assume false;
  }
  call wrap(Current); // default:wrapping cid:1 rid:55 line:26
}

procedure HS_SET^HS_HASHABLE^.has(Current: ref, v: ref) returns (Result: bool where true);
  free requires attached_exact(Heap, Current, HS_SET^HS_HASHABLE^); // info:type property for argument Current
  free requires detachable(Heap, v, HS_HASHABLE); // info:type property for argument v
  modifies Heap;
  requires (v) != (Void); // type:attached tag:v_closed line:33
  requires is_closed(Heap, v); // type:pre tag:v_closed line:33
  requires (Heap[Current, HS_SET^HS_HASHABLE^.lock]) != (Void); // type:attached tag:lock_wrapped line:34
  requires is_wrapped(Heap, Heap[Current, HS_SET^HS_HASHABLE^.lock]); // type:pre tag:lock_wrapped line:34
  requires Heap[Heap[Current, HS_SET^HS_HASHABLE^.lock], HS_LOCK^HS_HASHABLE^.sets][Current]; // type:pre tag:set_registered line:35
  ensures pre.fun.HS_SET^HS_HASHABLE^.set_has(Heap, Current, v); // type:check tag:function_precondition line:43 cid:405 rid:5420
  ensures (Result) == (fun.HS_SET^HS_HASHABLE^.set_has(Heap, Current, v)); // type:post tag:definition line:43
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.HS_SET^HS_HASHABLE^.has(Heap, Current, v), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.HS_SET^HS_HASHABLE^.has(old(Heap), Current, v));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.HS_SET^HS_HASHABLE^.has(Heap, Current, v), readable);
  requires is_closed(Heap, Current); // type:pre tag:default_is_closed default:contracts
  free ensures (Result) == (fun.HS_SET^HS_HASHABLE^.has(old(Heap), Current, v));



function fun.HS_SET^HS_HASHABLE^.has(heap: HeapType, current: ref, v: ref) returns (bool);

axiom ((forall heap: HeapType, current: ref, v: ref :: { fun.HS_SET^HS_HASHABLE^.has(heap, current, v) } (pre.fun.HS_SET^HS_HASHABLE^.has(heap, current, v)) ==> ((fun.HS_SET^HS_HASHABLE^.has(heap, current, v)) == (fun.HS_SET^HS_HASHABLE^.set_has(heap, current, v)))));

axiom ((forall h: HeapType, h': HeapType, current: ref, v: ref :: { HeapSucc(h, h'), fun.HS_SET^HS_HASHABLE^.has(h, current, v), fun.HS_SET^HS_HASHABLE^.has(h', current, v) } ((HeapSucc(h, h')) && (pre.fun.HS_SET^HS_HASHABLE^.has(h, current, v)) && (pre.fun.HS_SET^HS_HASHABLE^.has(h', current, v)) && (same_inside(h, h', read.fun.HS_SET^HS_HASHABLE^.has(h, current, v)))) ==> ((fun.HS_SET^HS_HASHABLE^.has(h, current, v)) == (fun.HS_SET^HS_HASHABLE^.has(h', current, v)))));

function { :inline } variant.HS_SET^HS_HASHABLE^.has.1(heap: HeapType, current: ref, v: ref) returns (ref) {
  v
}

implementation HS_SET^HS_HASHABLE^.has(Current: ref, v: ref) returns (Result: bool)
{
  var temp_126: int;
  var temp_127: int;
  var temp_128: int;
  var local1: Seq (ref) where Seq#ItemsType(Heap, local1, HS_HASHABLE);

  init_locals:
  temp_126 := 0;
  temp_127 := 0;
  temp_128 := 0;
  local1 := Seq#Empty();
  Result := false;

  entry:
  assume {:captureState "HS_SET^HS_HASHABLE^.has"} true;
  // /home/caf/temp/comcom/repo-hash_set/hs_set.e:39
  // check inv; lock.inv_only ("owns_items", "valid_buckets") end
  assert user_inv(Heap, Current); // type:check line:39
  // /home/caf/temp/comcom/repo-hash_set/hs_set.e:39
  // check inv; lock.inv_only ("owns_items", "valid_buckets") end
  assert readable[Current, HS_SET^HS_HASHABLE^.lock]; // type:access tag:attribute_readable line:39 cid:405 fid:90
  assert {:subsumption 0} (Heap[Current, HS_SET^HS_HASHABLE^.lock]) != (Void); // type:attached line:39
  assert HS_LOCK^HS_HASHABLE^#I#owns_items#valid_buckets.filtered_inv(Heap, Heap[Current, HS_SET^HS_HASHABLE^.lock]); // type:check line:39
  // /home/caf/temp/comcom/repo-hash_set/hs_set.e:40
  // b := buckets [bucket_index (v.hash_code, buckets.count)]
  assert readable[Current, HS_SET^HS_HASHABLE^.buckets]; // type:access tag:attribute_readable line:40 cid:405 rid:5418
  assert {:subsumption 0} (v) != (Void); // type:attached line:40
  assert Frame#Subset(read.fun.HS_HASHABLE.hash_code(Heap, v), readable); // type:access tag:frame_readable line:40 cid:406 rid:5423
  call temp_126 := HS_HASHABLE.hash_code(v); // line:40 cid:406 rid:5423
  assert readable[Current, HS_SET^HS_HASHABLE^.buckets]; // type:access tag:attribute_readable line:40 cid:405 rid:5418
  assert Frame#Subset(read.fun.HS_SET^HS_HASHABLE^.bucket_index(Heap, Current, temp_126, Seq#Length(Heap[Current, HS_SET^HS_HASHABLE^.buckets])), readable); // type:access tag:frame_readable line:40 cid:405 rid:5415
  call temp_127 := HS_SET^HS_HASHABLE^.bucket_index(Current, temp_126, Seq#Length(Heap[Current, HS_SET^HS_HASHABLE^.buckets])); // line:40 cid:405 rid:5415
  assert pre.fun.MML_SEQUENCE^MML_SEQUENCE^HS_HASHABLE^^.item(Heap[Current, HS_SET^HS_HASHABLE^.buckets], temp_127); // type:check tag:function_precondition line:40 cid:125 rid:3286
  local1 := Seq#Item(Heap[Current, HS_SET^HS_HASHABLE^.buckets], temp_127);
  // /home/caf/temp/comcom/repo-hash_set/hs_set.e:41
  // Result := b.domain [index_of (b, v)]
  assert Frame#Subset(read.fun.HS_SET^HS_HASHABLE^.index_of(Heap, Current, local1, v), readable); // type:access tag:frame_readable line:41 cid:405 rid:5416
  call temp_128 := HS_SET^HS_HASHABLE^.index_of(Current, local1, v); // line:41 cid:405 rid:5416
  Result := Seq#Domain(local1)[temp_128];
}

procedure HS_SET^HS_HASHABLE^.extend(Current: ref, v: ref);
  free requires attached_exact(Heap, Current, HS_SET^HS_HASHABLE^); // info:type property for argument Current
  free requires detachable(Heap, v, HS_HASHABLE); // info:type property for argument v
  modifies Heap;
  requires (Heap[Current, HS_SET^HS_HASHABLE^.lock]) != (Void); // type:attached tag:v_locked line:51
  requires Heap[Heap[Current, HS_SET^HS_HASHABLE^.lock], owns][v]; // type:pre tag:v_locked line:51
  requires is_wrapped(Heap, Heap[Current, HS_SET^HS_HASHABLE^.lock]); // type:pre tag:lock_wrapped line:52
  requires Heap[Heap[Current, HS_SET^HS_HASHABLE^.lock], HS_LOCK^HS_HASHABLE^.sets][Current]; // type:pre tag:set_registered line:53
  ensures pre.fun.HS_SET^HS_HASHABLE^.set_has(Heap, Current, v); // type:check tag:function_precondition line:69 cid:405 rid:5420
  ensures fun.HS_SET^HS_HASHABLE^.set_has(Heap, Current, v); // type:post tag:abstract_effect line:69
  ensures pre.fun.HS_SET^HS_HASHABLE^.set_has(old(Heap), Current, v); // type:check tag:function_precondition line:70 cid:405 rid:5420
  ensures (fun.HS_SET^HS_HASHABLE^.set_has(old(Heap), Current, v)) ==> (Set#Equal(Heap[Current, HS_SET^HS_HASHABLE^.set], old(Heap)[Current, HS_SET^HS_HASHABLE^.set])); // type:post tag:precise_effect_has line:70
  ensures (!(fun.HS_SET^HS_HASHABLE^.set_has(old(Heap), Current, v))) ==> (Set#Equal(Heap[Current, HS_SET^HS_HASHABLE^.set], Set#Extended(old(Heap)[Current, HS_SET^HS_HASHABLE^.set], v))); // type:post tag:precise_effect_new line:71
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.HS_SET^HS_HASHABLE^.extend(Heap, Current, v), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.HS_SET^HS_HASHABLE^.extend(old(Heap), Current, v));
  free ensures HeapSucc(old(Heap), Heap);
  requires is_wrapped(Heap, Current); // type:pre tag:default_is_wrapped default:contracts
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts



function { :inline } variant.HS_SET^HS_HASHABLE^.extend.1(heap: HeapType, current: ref, v: ref) returns (ref) {
  v
}

implementation HS_SET^HS_HASHABLE^.extend(Current: ref, v: ref)
{
  var temp_129: int;
  var temp_130: int;
  var temp_131: int;
  var local1: int where is_integer_32(local1);
  var local2: Seq (ref) where Seq#ItemsType(Heap, local2, HS_HASHABLE);

  init_locals:
  temp_129 := 0;
  temp_130 := 0;
  temp_131 := 0;
  local1 := 0;
  local2 := Seq#Empty();

  entry:
  assume {:captureState "HS_SET^HS_HASHABLE^.extend"} true;
  call unwrap(Current); // default:wrapping cid:1 rid:57 line:48
  assume HS_SET^HS_HASHABLE^.user_inv(Heap, Current);
  // /home/caf/temp/comcom/repo-hash_set/hs_set.e:59
  // check lock.inv_only ("owns_items", "valid_buckets") end
  assert {:subsumption 0} (Heap[Current, HS_SET^HS_HASHABLE^.lock]) != (Void); // type:attached line:59
  assert HS_LOCK^HS_HASHABLE^#I#owns_items#valid_buckets.filtered_inv(Heap, Heap[Current, HS_SET^HS_HASHABLE^.lock]); // type:check line:59
  // /home/caf/temp/comcom/repo-hash_set/hs_set.e:60
  // idx := bucket_index (v.hash_code, buckets.count)
  assert {:subsumption 0} (v) != (Void); // type:attached line:60
  call temp_129 := HS_HASHABLE.hash_code(v); // line:60 cid:406 rid:5423
  call temp_130 := HS_SET^HS_HASHABLE^.bucket_index(Current, temp_129, Seq#Length(Heap[Current, HS_SET^HS_HASHABLE^.buckets])); // line:60 cid:405 rid:5415
  local1 := temp_130;
  // /home/caf/temp/comcom/repo-hash_set/hs_set.e:61
  // b := buckets [idx]
  assert pre.fun.MML_SEQUENCE^MML_SEQUENCE^HS_HASHABLE^^.item(Heap[Current, HS_SET^HS_HASHABLE^.buckets], local1); // type:check tag:function_precondition line:61 cid:125 rid:3286
  local2 := Seq#Item(Heap[Current, HS_SET^HS_HASHABLE^.buckets], local1);
  // /home/caf/temp/comcom/repo-hash_set/hs_set.e:62
  // if not b.domain [index_of (b, v)] then
  call temp_131 := HS_SET^HS_HASHABLE^.index_of(Current, local2, v); // line:62 cid:405 rid:5416
  if (!(Seq#Domain(local2)[temp_131])) {
    // /home/caf/temp/comcom/repo-hash_set/hs_set.e:63
    // buckets := buckets.replaced_at (idx, b & v)
    assert pre.fun.MML_SEQUENCE^MML_SEQUENCE^HS_HASHABLE^^.replaced_at(Heap[Current, HS_SET^HS_HASHABLE^.buckets], local1, Seq#Extended(local2, v)); // type:check tag:function_precondition line:63 cid:125 rid:3308
    call update_heap(Current, HS_SET^HS_HASHABLE^.buckets, Seq#Update(Heap[Current, HS_SET^HS_HASHABLE^.buckets], local1, Seq#Extended(local2, v))); // line:63
    // /home/caf/temp/comcom/repo-hash_set/hs_set.e:64
    // set := set & v
    call update_heap(Current, HS_SET^HS_HASHABLE^.set, Set#Extended(Heap[Current, HS_SET^HS_HASHABLE^.set], v)); // line:64
    // /home/caf/temp/comcom/repo-hash_set/hs_set.e:65
    // check set [v] end
    assert Heap[Current, HS_SET^HS_HASHABLE^.set][v]; // type:check line:65
  }
  // /home/caf/temp/comcom/repo-hash_set/hs_set.e:67
  // check set_has (v) end
  assert pre.fun.HS_SET^HS_HASHABLE^.set_has(Heap, Current, v); // type:check tag:function_precondition line:67 cid:405 rid:5420
  assert fun.HS_SET^HS_HASHABLE^.set_has(Heap, Current, v); // type:check line:67
  if (modify.HS_SET^HS_HASHABLE^.extend(Heap, Current, v)[Current, observers]) {
    call update_heap(Current, observers, HS_SET^HS_HASHABLE^.observers.static(Heap, Current)); // default:observers line:72
  }
  if (*) {
    assert !(Seq#IsEmpty(Heap[Current, HS_SET^HS_HASHABLE^.buckets])); // type:inv tag:buckets_non_empty line:72 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#Equal(Heap[Current, observers], Set#Singleton(Heap[Current, HS_SET^HS_HASHABLE^.lock])); // type:inv tag:observers_definition line:72 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#NonNull(Heap[Current, HS_SET^HS_HASHABLE^.set]); // type:inv tag:set_non_void line:72 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert (forall i_132: int :: (((1) <= (i_132)) && ((i_132) <= (Seq#Length(Heap[Current, HS_SET^HS_HASHABLE^.buckets])))) ==> ((forall i_133: int :: (((1) <= (i_133)) && ((i_133) <= (Seq#Length(Seq#Item(Heap[Current, HS_SET^HS_HASHABLE^.buckets], i_132))))) ==> (Heap[Current, HS_SET^HS_HASHABLE^.set][Seq#Item(Seq#Item(Heap[Current, HS_SET^HS_HASHABLE^.buckets], i_132), i_133)])))); // type:inv tag:set_not_too_small line:72 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert (forall i_134: int :: (((1) <= (i_134)) && ((i_134) <= (Seq#Length(Heap[Current, HS_SET^HS_HASHABLE^.buckets])))) ==> ((forall i_135: int :: (((1) <= (i_135)) && ((i_135) <= (Seq#Length(Heap[Current, HS_SET^HS_HASHABLE^.buckets])))) ==> ((forall i_136: int :: (((1) <= (i_136)) && ((i_136) <= (Seq#Length(Seq#Item(Heap[Current, HS_SET^HS_HASHABLE^.buckets], i_134))))) ==> ((forall i_137: int :: (((1) <= (i_137)) && ((i_137) <= (Seq#Length(Seq#Item(Heap[Current, HS_SET^HS_HASHABLE^.buckets], i_135))))) ==> ((((i_134) != (i_135)) || ((i_136) != (i_137))) ==> ((Seq#Item(Seq#Item(Heap[Current, HS_SET^HS_HASHABLE^.buckets], i_134), i_136)) != (Seq#Item(Seq#Item(Heap[Current, HS_SET^HS_HASHABLE^.buckets], i_135), i_137))))))))))); // type:inv tag:no_precise_duplicates line:72 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, subjects]); // type:inv tag:default_subjects line:72 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, owns]); // type:inv tag:default_owns line:72 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert admissibility2(Heap, Current); // type:inv tag:A2 line:72 cid:1 rid:55
    assume false;
  }
  call wrap(Current); // default:wrapping cid:1 rid:55 line:72
}

procedure HS_SET^HS_HASHABLE^.join(Current: ref, other: ref);
  free requires attached_exact(Heap, Current, HS_SET^HS_HASHABLE^); // info:type property for argument Current
  free requires detachable(Heap, other, HS_SET^HS_HASHABLE^); // info:type property for argument other
  modifies Heap;
  requires (Heap[Current, HS_SET^HS_HASHABLE^.lock]) != (Void); // type:attached tag:lock_wrapped line:80
  requires is_wrapped(Heap, Heap[Current, HS_SET^HS_HASHABLE^.lock]); // type:pre tag:lock_wrapped line:80
  requires Heap[Heap[Current, HS_SET^HS_HASHABLE^.lock], HS_LOCK^HS_HASHABLE^.sets][Current]; // type:pre tag:set_registered line:81
  requires Heap[Heap[Current, HS_SET^HS_HASHABLE^.lock], HS_LOCK^HS_HASHABLE^.sets][other]; // type:pre tag:other_registered line:82
  ensures Set#Subset(old(Heap)[Current, HS_SET^HS_HASHABLE^.set], Heap[Current, HS_SET^HS_HASHABLE^.set]); // type:post tag:has_old line:128
  ensures (other) != (Void); // type:attached tag:has_other line:129
  ensures (forall i_138: ref :: (old(Heap)[other, HS_SET^HS_HASHABLE^.set][i_138]) ==> (((i_138) != (Void)) ==> (pre.fun.HS_SET^HS_HASHABLE^.set_has(Heap, Current, i_138)))); // type:check tag:function_precondition line:129 cid:405 rid:5420
  ensures (forall i_138: ref :: (old(Heap)[other, HS_SET^HS_HASHABLE^.set][i_138]) ==> (((i_138) != (Void)) && (fun.HS_SET^HS_HASHABLE^.set_has(Heap, Current, i_138)))); // type:post tag:has_other line:129
  ensures (forall i_139: ref :: (Heap[Current, HS_SET^HS_HASHABLE^.set][i_139]) ==> (pre.fun.HS_SET^HS_HASHABLE^.set_has(old(Heap), Current, i_139))); // type:check tag:function_precondition line:130 cid:405 rid:5420
  ensures (forall i_139: ref :: (Heap[Current, HS_SET^HS_HASHABLE^.set][i_139]) ==> (pre.fun.HS_SET^HS_HASHABLE^.set_has(old(Heap), other, i_139))); // type:check tag:function_precondition line:130 cid:405 rid:5420
  ensures (forall i_139: ref :: (Heap[Current, HS_SET^HS_HASHABLE^.set][i_139]) ==> ((fun.HS_SET^HS_HASHABLE^.set_has(old(Heap), Current, i_139)) || (fun.HS_SET^HS_HASHABLE^.set_has(old(Heap), other, i_139)))); // type:post tag:no_extra line:130
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.HS_SET^HS_HASHABLE^.join(Heap, Current, other), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.HS_SET^HS_HASHABLE^.join(old(Heap), Current, other));
  free ensures HeapSucc(old(Heap), Heap);
  requires is_wrapped(Heap, Current); // type:pre tag:default_is_wrapped default:contracts
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts
  requires is_wrapped(Heap, other); // type:pre tag:arg_other_is_wrapped default:contracts
  ensures is_wrapped(Heap, other); // type:post tag:arg_other_is_wrapped default:contracts



function { :inline } variant.HS_SET^HS_HASHABLE^.join.1(heap: HeapType, current: ref, other: ref) returns (ref) {
  other
}

implementation HS_SET^HS_HASHABLE^.join(Current: ref, other: ref)
{
  var PreLoopHeap_143: HeapType;
  var variant_147: int;
  var PreLoopHeap_151: HeapType;
  var variant_156: int;
  var local1: int where is_integer_32(local1);
  var local2: int where is_integer_32(local2);
  var local3: Seq (Seq (ref)) where true;
  var local4: Seq (ref) where Seq#ItemsType(Heap, local4, HS_HASHABLE);

  init_locals:
  variant_147 := 0;
  variant_156 := 0;
  local1 := 0;
  local2 := 0;
  local3 := Seq#Empty();
  local4 := Seq#Empty();

  entry:
  assume {:captureState "HS_SET^HS_HASHABLE^.join"} true;
  // /home/caf/temp/comcom/repo-hash_set/hs_set.e:89
  // check inv_only ("set_non_void") end
  assert HS_SET^HS_HASHABLE^#I#set_non_void.filtered_inv(Heap, Current); // type:check line:89
  // /home/caf/temp/comcom/repo-hash_set/hs_set.e:90
  // if other /= Current then
  if ((other) != (Current)) {
    // /home/caf/temp/comcom/repo-hash_set/hs_set.e:92
    // i := 1
    local1 := 1;
    // /home/caf/temp/comcom/repo-hash_set/hs_set.e:93
    // ss := other.buckets
    assert {:subsumption 0} (other) != (Void); // type:attached line:93
    local3 := Heap[other, HS_SET^HS_HASHABLE^.buckets];
    PreLoopHeap_143 := Heap;
    goto loop_head_140;
    loop_head_140:
    // /home/caf/temp/comcom/repo-hash_set/hs_set.e:95
    // is_wrapped
    assert is_wrapped(Heap, Current); // type:loop_inv line:95
    // /home/caf/temp/comcom/repo-hash_set/hs_set.e:96
    // other.inv
    assert {:subsumption 0} (other) != (Void); // type:attached line:96
    assert user_inv(Heap, other); // type:loop_inv line:96
    // /home/caf/temp/comcom/repo-hash_set/hs_set.e:97
    // 1 <= i and i <= ss.count + 1
    assert ((1) <= (local1)) && ((local1) <= ((Seq#Length(local3)) + (1))); // type:loop_inv line:97
    // /home/caf/temp/comcom/repo-hash_set/hs_set.e:98
    // across 1 |..| (i - 1) as k all
    assert (forall i_144: int :: (((1) <= (i_144)) && ((i_144) <= ((local1) - (1)))) ==> (pre.fun.MML_SEQUENCE^MML_SEQUENCE^HS_HASHABLE^^.item(local3, i_144))); // type:check tag:function_precondition line:98 cid:125 rid:3286
    assert (forall i_144: int :: (((1) <= (i_144)) && ((i_144) <= ((local1) - (1)))) ==> (pre.fun.MML_SEQUENCE^MML_SEQUENCE^HS_HASHABLE^^.item(local3, i_144))); // type:check tag:function_precondition line:98 cid:125 rid:3286
    assert (forall i_144: int :: (((1) <= (i_144)) && ((i_144) <= ((local1) - (1)))) ==> ((forall i_145: int :: (((1) <= (i_145)) && ((i_145) <= (Seq#Length(Seq#Item(local3, i_144))))) ==> (pre.fun.MML_SEQUENCE^HS_HASHABLE^.item(Seq#Item(local3, i_144), i_145))))); // type:check tag:function_precondition line:98 cid:125 rid:3286
    assert (forall i_144: int :: (((1) <= (i_144)) && ((i_144) <= ((local1) - (1)))) ==> ((forall i_145: int :: (((1) <= (i_145)) && ((i_145) <= (Seq#Length(Seq#Item(local3, i_144))))) ==> (pre.fun.HS_SET^HS_HASHABLE^.set_has(Heap, Current, Seq#Item(Seq#Item(local3, i_144), i_145)))))); // type:check tag:function_precondition line:98 cid:405 rid:5420
    assert (forall i_144: int :: (((1) <= (i_144)) && ((i_144) <= ((local1) - (1)))) ==> ((forall i_145: int :: (((1) <= (i_145)) && ((i_145) <= (Seq#Length(Seq#Item(local3, i_144))))) ==> (fun.HS_SET^HS_HASHABLE^.set_has(Heap, Current, Seq#Item(Seq#Item(local3, i_144), i_145)))))); // type:loop_inv line:98
    // /home/caf/temp/comcom/repo-hash_set/hs_set.e:100
    // set.old_ <= set
    assert Set#Subset(old(Heap)[Current, HS_SET^HS_HASHABLE^.set], Heap[Current, HS_SET^HS_HASHABLE^.set]); // type:loop_inv line:100
    // /home/caf/temp/comcom/repo-hash_set/hs_set.e:101
    // across set as x all x.item /= Void and then (set.old_ [x.item] or other.set_has (x.item).old_) end
    assert (true) ==> ((other) != (Void)); // type:attached line:101
    assert (forall i_146: ref :: (Heap[Current, HS_SET^HS_HASHABLE^.set][i_146]) ==> (((i_146) != (Void)) ==> (pre.fun.HS_SET^HS_HASHABLE^.set_has(old(Heap), other, i_146)))); // type:check tag:function_precondition line:101 cid:405 rid:5420
    assert (forall i_146: ref :: (Heap[Current, HS_SET^HS_HASHABLE^.set][i_146]) ==> (((i_146) != (Void)) && ((old(Heap)[Current, HS_SET^HS_HASHABLE^.set][i_146]) || (fun.HS_SET^HS_HASHABLE^.set_has(old(Heap), other, i_146))))); // type:loop_inv line:101
    assume HeapSucc(PreLoopHeap_143, Heap);
    assume same_outside(old(Heap), Heap, modify.HS_SET^HS_HASHABLE^.join(old(Heap), Current, other));
    assume global(Heap);
    // /home/caf/temp/comcom/repo-hash_set/hs_set.e:-1
    goto loop_body_141, loop_end_142;
    loop_body_141:
    assume !((local1) > (Seq#Length(local3)));
    variant_147 := (Seq#Length(local3)) - (local1);
    // /home/caf/temp/comcom/repo-hash_set/hs_set.e:105
    // s := other.buckets [i]
    assert {:subsumption 0} (other) != (Void); // type:attached line:105
    assert pre.fun.MML_SEQUENCE^MML_SEQUENCE^HS_HASHABLE^^.item(Heap[other, HS_SET^HS_HASHABLE^.buckets], local1); // type:check tag:function_precondition line:105 cid:125 rid:3286
    local4 := Seq#Item(Heap[other, HS_SET^HS_HASHABLE^.buckets], local1);
    // /home/caf/temp/comcom/repo-hash_set/hs_set.e:107
    // j := 1
    local2 := 1;
    PreLoopHeap_151 := Heap;
    goto loop_head_148;
    loop_head_148:
    // /home/caf/temp/comcom/repo-hash_set/hs_set.e:109
    // is_wrapped
    assert is_wrapped(Heap, Current); // type:loop_inv line:109
    // /home/caf/temp/comcom/repo-hash_set/hs_set.e:110
    // lock.inv_only ("owns_items")
    assert {:subsumption 0} (Heap[Current, HS_SET^HS_HASHABLE^.lock]) != (Void); // type:attached line:110
    assert HS_LOCK^HS_HASHABLE^#I#owns_items.filtered_inv(Heap, Heap[Current, HS_SET^HS_HASHABLE^.lock]); // type:loop_inv line:110
    // /home/caf/temp/comcom/repo-hash_set/hs_set.e:111
    // 1 <= j and j <= s.count + 1
    assert ((1) <= (local2)) && ((local2) <= ((Seq#Length(local4)) + (1))); // type:loop_inv line:111
    // /home/caf/temp/comcom/repo-hash_set/hs_set.e:112
    // set.old_ <= set
    assert Set#Subset(old(Heap)[Current, HS_SET^HS_HASHABLE^.set], Heap[Current, HS_SET^HS_HASHABLE^.set]); // type:loop_inv line:112
    // /home/caf/temp/comcom/repo-hash_set/hs_set.e:113
    // across 1 |..| (j - 1) as l all set_has (s [l.item]) end
    assert (forall i_152: int :: (((1) <= (i_152)) && ((i_152) <= ((local2) - (1)))) ==> (pre.fun.MML_SEQUENCE^HS_HASHABLE^.item(local4, i_152))); // type:check tag:function_precondition line:113 cid:125 rid:3286
    assert (forall i_152: int :: (((1) <= (i_152)) && ((i_152) <= ((local2) - (1)))) ==> (pre.fun.HS_SET^HS_HASHABLE^.set_has(Heap, Current, Seq#Item(local4, i_152)))); // type:check tag:function_precondition line:113 cid:405 rid:5420
    assert (forall i_152: int :: (((1) <= (i_152)) && ((i_152) <= ((local2) - (1)))) ==> (fun.HS_SET^HS_HASHABLE^.set_has(Heap, Current, Seq#Item(local4, i_152)))); // type:loop_inv line:113
    // /home/caf/temp/comcom/repo-hash_set/hs_set.e:114
    // across 1 |..| (i - 1) as k all
    assert (forall i_153: int :: (((1) <= (i_153)) && ((i_153) <= ((local1) - (1)))) ==> (pre.fun.MML_SEQUENCE^MML_SEQUENCE^HS_HASHABLE^^.item(local3, i_153))); // type:check tag:function_precondition line:114 cid:125 rid:3286
    assert (forall i_153: int :: (((1) <= (i_153)) && ((i_153) <= ((local1) - (1)))) ==> (pre.fun.MML_SEQUENCE^MML_SEQUENCE^HS_HASHABLE^^.item(local3, i_153))); // type:check tag:function_precondition line:114 cid:125 rid:3286
    assert (forall i_153: int :: (((1) <= (i_153)) && ((i_153) <= ((local1) - (1)))) ==> ((forall i_154: int :: (((1) <= (i_154)) && ((i_154) <= (Seq#Length(Seq#Item(local3, i_153))))) ==> (pre.fun.MML_SEQUENCE^HS_HASHABLE^.item(Seq#Item(local3, i_153), i_154))))); // type:check tag:function_precondition line:114 cid:125 rid:3286
    assert (forall i_153: int :: (((1) <= (i_153)) && ((i_153) <= ((local1) - (1)))) ==> ((forall i_154: int :: (((1) <= (i_154)) && ((i_154) <= (Seq#Length(Seq#Item(local3, i_153))))) ==> (pre.fun.HS_SET^HS_HASHABLE^.set_has(Heap, Current, Seq#Item(Seq#Item(local3, i_153), i_154)))))); // type:check tag:function_precondition line:114 cid:405 rid:5420
    assert (forall i_153: int :: (((1) <= (i_153)) && ((i_153) <= ((local1) - (1)))) ==> ((forall i_154: int :: (((1) <= (i_154)) && ((i_154) <= (Seq#Length(Seq#Item(local3, i_153))))) ==> (fun.HS_SET^HS_HASHABLE^.set_has(Heap, Current, Seq#Item(Seq#Item(local3, i_153), i_154)))))); // type:loop_inv line:114
    // /home/caf/temp/comcom/repo-hash_set/hs_set.e:116
    // across set as x all x.item /= Void and then (set.old_ [x.item] or other.set_has (x.item).old_) end
    assert (true) ==> ((other) != (Void)); // type:attached line:116
    assert (forall i_155: ref :: (Heap[Current, HS_SET^HS_HASHABLE^.set][i_155]) ==> (((i_155) != (Void)) ==> (pre.fun.HS_SET^HS_HASHABLE^.set_has(old(Heap), other, i_155)))); // type:check tag:function_precondition line:116 cid:405 rid:5420
    assert (forall i_155: ref :: (Heap[Current, HS_SET^HS_HASHABLE^.set][i_155]) ==> (((i_155) != (Void)) && ((old(Heap)[Current, HS_SET^HS_HASHABLE^.set][i_155]) || (fun.HS_SET^HS_HASHABLE^.set_has(old(Heap), other, i_155))))); // type:loop_inv line:116
    assume HeapSucc(PreLoopHeap_151, Heap);
    assume same_outside(old(Heap), Heap, modify.HS_SET^HS_HASHABLE^.join(old(Heap), Current, other));
    assume global(Heap);
    // /home/caf/temp/comcom/repo-hash_set/hs_set.e:-1
    goto loop_body_149, loop_end_150;
    loop_body_149:
    assume !((local2) > (Seq#Length(local4)));
    variant_156 := (Seq#Length(local4)) - (local2);
    // /home/caf/temp/comcom/repo-hash_set/hs_set.e:120
    // extend (s [j])
    assert pre.fun.MML_SEQUENCE^HS_HASHABLE^.item(local4, local2); // type:check tag:function_precondition line:120 cid:125 rid:3286
    call HS_SET^HS_HASHABLE^.extend(Current, Seq#Item(local4, local2)); // line:120 cid:405 rid:5411
    // /home/caf/temp/comcom/repo-hash_set/hs_set.e:121
    // j := j + 1
    local2 := (local2) + (1);
    // /home/caf/temp/comcom/repo-hash_set/hs_set.e:120
    // extend (s [j])
    assert {:subsumption 0} ((((Seq#Length(local4)) - (local2)) <= (variant_156)) && ((variant_156) <= ((Seq#Length(local4)) - (local2)))) || ((0) <= (variant_156)); // type:termination tag:bounded line:120 varid:1
    assert {:subsumption 0} (((Seq#Length(local4)) - (local2)) <= (variant_156)) && (!((variant_156) <= ((Seq#Length(local4)) - (local2)))); // type:termination tag:variant_decreases line:120
    goto loop_head_148;
    loop_end_150:
    assume (local2) > (Seq#Length(local4));
    // /home/caf/temp/comcom/repo-hash_set/hs_set.e:123
    // i := i + 1
    local1 := (local1) + (1);
    // /home/caf/temp/comcom/repo-hash_set/hs_set.e:105
    // s := other.buckets [i]
    assert {:subsumption 0} ((((Seq#Length(local3)) - (local1)) <= (variant_147)) && ((variant_147) <= ((Seq#Length(local3)) - (local1)))) || ((0) <= (variant_147)); // type:termination tag:bounded line:105 varid:1
    assert {:subsumption 0} (((Seq#Length(local3)) - (local1)) <= (variant_147)) && (!((variant_147) <= ((Seq#Length(local3)) - (local1)))); // type:termination tag:variant_decreases line:105
    goto loop_head_140;
    loop_end_142:
    assume (local1) > (Seq#Length(local3));
    // /home/caf/temp/comcom/repo-hash_set/hs_set.e:125
    // check lock.inv_only ("valid_buckets") end
    assert {:subsumption 0} (Heap[Current, HS_SET^HS_HASHABLE^.lock]) != (Void); // type:attached line:125
    assert HS_LOCK^HS_HASHABLE^#I#valid_buckets.filtered_inv(Heap, Heap[Current, HS_SET^HS_HASHABLE^.lock]); // type:check line:125
  }
}

procedure HS_SET^HS_HASHABLE^.remove(Current: ref, v: ref);
  free requires attached_exact(Heap, Current, HS_SET^HS_HASHABLE^); // info:type property for argument Current
  free requires detachable(Heap, v, HS_HASHABLE); // info:type property for argument v
  modifies Heap;
  requires (Heap[Current, HS_SET^HS_HASHABLE^.lock]) != (Void); // type:attached tag:v_locked line:136
  requires Heap[Heap[Current, HS_SET^HS_HASHABLE^.lock], owns][v]; // type:pre tag:v_locked line:136
  requires is_wrapped(Heap, Heap[Current, HS_SET^HS_HASHABLE^.lock]); // type:pre tag:lock_wrapped line:137
  requires Heap[Heap[Current, HS_SET^HS_HASHABLE^.lock], HS_LOCK^HS_HASHABLE^.sets][Current]; // type:pre tag:set_registered line:138
  ensures pre.fun.HS_SET^HS_HASHABLE^.set_has(Heap, Current, v); // type:check tag:function_precondition line:156 cid:405 rid:5420
  ensures !(fun.HS_SET^HS_HASHABLE^.set_has(Heap, Current, v)); // type:post tag:abstract_effect line:156
  ensures pre.fun.HS_SET^HS_HASHABLE^.set_has(old(Heap), Current, v); // type:check tag:function_precondition line:157 cid:405 rid:5420
  ensures (!(fun.HS_SET^HS_HASHABLE^.set_has(old(Heap), Current, v))) ==> (Set#Equal(Heap[Current, HS_SET^HS_HASHABLE^.set], old(Heap)[Current, HS_SET^HS_HASHABLE^.set])); // type:post tag:precise_effect_not_found line:157
  ensures (fun.HS_SET^HS_HASHABLE^.set_has(old(Heap), Current, v)) ==> ((v) != (Void)); // type:attached tag:precise_effect_found line:158
  ensures (forall i_157: ref :: (old(Heap)[Current, HS_SET^HS_HASHABLE^.set][i_157]) ==> ((fun.HS_SET^HS_HASHABLE^.set_has(old(Heap), Current, v)) ==> (pre.fun.HS_HASHABLE.is_model_equal(Heap, v, i_157)))); // type:check tag:function_precondition line:158 cid:406 rid:81
  ensures (fun.HS_SET^HS_HASHABLE^.set_has(old(Heap), Current, v)) ==> ((exists i_157: ref :: (old(Heap)[Current, HS_SET^HS_HASHABLE^.set][i_157]) && (Set#Equal(Heap[Current, HS_SET^HS_HASHABLE^.set], Set#Removed(old(Heap)[Current, HS_SET^HS_HASHABLE^.set], i_157))) && (fun.HS_HASHABLE.is_model_equal(Heap, v, i_157)))); // type:post tag:precise_effect_found line:158
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.HS_SET^HS_HASHABLE^.remove(Heap, Current, v), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.HS_SET^HS_HASHABLE^.remove(old(Heap), Current, v));
  free ensures HeapSucc(old(Heap), Heap);
  requires is_wrapped(Heap, Current); // type:pre tag:default_is_wrapped default:contracts
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts



function { :inline } variant.HS_SET^HS_HASHABLE^.remove.1(heap: HeapType, current: ref, v: ref) returns (ref) {
  v
}

implementation HS_SET^HS_HASHABLE^.remove(Current: ref, v: ref)
{
  var temp_158: int;
  var temp_159: int;
  var temp_160: int;
  var local1: Seq (ref) where Seq#ItemsType(Heap, local1, HS_HASHABLE);
  var local2: int where is_integer_32(local2);
  var local3: int where is_integer_32(local3);
  var local4: ref where detachable(Heap, local4, HS_HASHABLE);

  init_locals:
  temp_158 := 0;
  temp_159 := 0;
  temp_160 := 0;
  local1 := Seq#Empty();
  local2 := 0;
  local3 := 0;
  local4 := Void;

  entry:
  assume {:captureState "HS_SET^HS_HASHABLE^.remove"} true;
  call unwrap(Current); // default:wrapping cid:1 rid:57 line:133
  assume HS_SET^HS_HASHABLE^.user_inv(Heap, Current);
  // /home/caf/temp/comcom/repo-hash_set/hs_set.e:145
  // check lock.inv_only ("owns_items", "valid_buckets", "no_duplicates") end
  assert {:subsumption 0} (Heap[Current, HS_SET^HS_HASHABLE^.lock]) != (Void); // type:attached line:145
  assert HS_LOCK^HS_HASHABLE^#I#owns_items#valid_buckets#no_duplicates.filtered_inv(Heap, Heap[Current, HS_SET^HS_HASHABLE^.lock]); // type:check line:145
  // /home/caf/temp/comcom/repo-hash_set/hs_set.e:146
  // idx := bucket_index (v.hash_code, buckets.count)
  assert {:subsumption 0} (v) != (Void); // type:attached line:146
  call temp_158 := HS_HASHABLE.hash_code(v); // line:146 cid:406 rid:5423
  call temp_159 := HS_SET^HS_HASHABLE^.bucket_index(Current, temp_158, Seq#Length(Heap[Current, HS_SET^HS_HASHABLE^.buckets])); // line:146 cid:405 rid:5415
  local2 := temp_159;
  // /home/caf/temp/comcom/repo-hash_set/hs_set.e:147
  // b := buckets [idx]
  assert pre.fun.MML_SEQUENCE^MML_SEQUENCE^HS_HASHABLE^^.item(Heap[Current, HS_SET^HS_HASHABLE^.buckets], local2); // type:check tag:function_precondition line:147 cid:125 rid:3286
  local1 := Seq#Item(Heap[Current, HS_SET^HS_HASHABLE^.buckets], local2);
  // /home/caf/temp/comcom/repo-hash_set/hs_set.e:148
  // i := index_of (b, v)
  call temp_160 := HS_SET^HS_HASHABLE^.index_of(Current, local1, v); // line:148 cid:405 rid:5416
  local3 := temp_160;
  // /home/caf/temp/comcom/repo-hash_set/hs_set.e:149
  // if b.domain [i] then
  if (Seq#Domain(local1)[local3]) {
    // /home/caf/temp/comcom/repo-hash_set/hs_set.e:150
    // x := b [i]
    assert pre.fun.MML_SEQUENCE^HS_HASHABLE^.item(local1, local3); // type:check tag:function_precondition line:150 cid:125 rid:3286
    local4 := Seq#Item(local1, local3);
    // /home/caf/temp/comcom/repo-hash_set/hs_set.e:151
    // set := set / x
    call update_heap(Current, HS_SET^HS_HASHABLE^.set, Set#Removed(Heap[Current, HS_SET^HS_HASHABLE^.set], local4)); // line:151
    // /home/caf/temp/comcom/repo-hash_set/hs_set.e:152
    // buckets := buckets.replaced_at (idx, b.removed_at (i))
    assert pre.fun.MML_SEQUENCE^HS_HASHABLE^.removed_at(local1, local3); // type:check tag:function_precondition line:152 cid:125 rid:3303
    assert pre.fun.MML_SEQUENCE^MML_SEQUENCE^HS_HASHABLE^^.replaced_at(Heap[Current, HS_SET^HS_HASHABLE^.buckets], local2, Seq#RemovedAt(local1, local3)); // type:check tag:function_precondition line:152 cid:125 rid:3308
    call update_heap(Current, HS_SET^HS_HASHABLE^.buckets, Seq#Update(Heap[Current, HS_SET^HS_HASHABLE^.buckets], local2, Seq#RemovedAt(local1, local3))); // line:152
    // /home/caf/temp/comcom/repo-hash_set/hs_set.e:153
    // x.lemma_transitive (v, set)
    assert {:subsumption 0} (local4) != (Void); // type:attached line:153
    call HS_HASHABLE.lemma_transitive(local4, v, Heap[Current, HS_SET^HS_HASHABLE^.set]); // line:153 cid:406 rid:82
  }
  if (modify.HS_SET^HS_HASHABLE^.remove(Heap, Current, v)[Current, observers]) {
    call update_heap(Current, observers, HS_SET^HS_HASHABLE^.observers.static(Heap, Current)); // default:observers line:160
  }
  if (*) {
    assert !(Seq#IsEmpty(Heap[Current, HS_SET^HS_HASHABLE^.buckets])); // type:inv tag:buckets_non_empty line:160 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#Equal(Heap[Current, observers], Set#Singleton(Heap[Current, HS_SET^HS_HASHABLE^.lock])); // type:inv tag:observers_definition line:160 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#NonNull(Heap[Current, HS_SET^HS_HASHABLE^.set]); // type:inv tag:set_non_void line:160 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert (forall i_161: int :: (((1) <= (i_161)) && ((i_161) <= (Seq#Length(Heap[Current, HS_SET^HS_HASHABLE^.buckets])))) ==> ((forall i_162: int :: (((1) <= (i_162)) && ((i_162) <= (Seq#Length(Seq#Item(Heap[Current, HS_SET^HS_HASHABLE^.buckets], i_161))))) ==> (Heap[Current, HS_SET^HS_HASHABLE^.set][Seq#Item(Seq#Item(Heap[Current, HS_SET^HS_HASHABLE^.buckets], i_161), i_162)])))); // type:inv tag:set_not_too_small line:160 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert (forall i_163: int :: (((1) <= (i_163)) && ((i_163) <= (Seq#Length(Heap[Current, HS_SET^HS_HASHABLE^.buckets])))) ==> ((forall i_164: int :: (((1) <= (i_164)) && ((i_164) <= (Seq#Length(Heap[Current, HS_SET^HS_HASHABLE^.buckets])))) ==> ((forall i_165: int :: (((1) <= (i_165)) && ((i_165) <= (Seq#Length(Seq#Item(Heap[Current, HS_SET^HS_HASHABLE^.buckets], i_163))))) ==> ((forall i_166: int :: (((1) <= (i_166)) && ((i_166) <= (Seq#Length(Seq#Item(Heap[Current, HS_SET^HS_HASHABLE^.buckets], i_164))))) ==> ((((i_163) != (i_164)) || ((i_165) != (i_166))) ==> ((Seq#Item(Seq#Item(Heap[Current, HS_SET^HS_HASHABLE^.buckets], i_163), i_165)) != (Seq#Item(Seq#Item(Heap[Current, HS_SET^HS_HASHABLE^.buckets], i_164), i_166))))))))))); // type:inv tag:no_precise_duplicates line:160 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, subjects]); // type:inv tag:default_subjects line:160 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, owns]); // type:inv tag:default_owns line:160 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert admissibility2(Heap, Current); // type:inv tag:A2 line:160 cid:1 rid:55
    assume false;
  }
  call wrap(Current); // default:wrapping cid:1 rid:55 line:160
}

procedure HS_SET^HS_HASHABLE^.wipe_out(Current: ref);
  free requires attached_exact(Heap, Current, HS_SET^HS_HASHABLE^); // info:type property for argument Current
  modifies Heap;
  requires (Heap[Current, HS_SET^HS_HASHABLE^.lock]) != (Void); // type:attached tag:lock_wrapped line:165
  requires is_wrapped(Heap, Heap[Current, HS_SET^HS_HASHABLE^.lock]); // type:pre tag:lock_wrapped line:165
  requires Heap[Heap[Current, HS_SET^HS_HASHABLE^.lock], HS_LOCK^HS_HASHABLE^.sets][Current]; // type:pre tag:set_registered line:166
  ensures Set#IsEmpty(Heap[Current, HS_SET^HS_HASHABLE^.set]); // type:post tag:set_empty line:172
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.HS_SET^HS_HASHABLE^.wipe_out(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.HS_SET^HS_HASHABLE^.wipe_out(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);
  requires is_wrapped(Heap, Current); // type:pre tag:default_is_wrapped default:contracts
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts



function { :inline } variant.HS_SET^HS_HASHABLE^.wipe_out.1(heap: HeapType, current: ref) returns (int) {
  0
}

implementation HS_SET^HS_HASHABLE^.wipe_out(Current: ref)
{
  var temp_167: Set (ref);
  var temp_168: Seq (Seq (ref));

  init_locals:
  temp_167 := Set#Empty();
  temp_168 := Seq#Empty();

  entry:
  assume {:captureState "HS_SET^HS_HASHABLE^.wipe_out"} true;
  call unwrap(Current); // default:wrapping cid:1 rid:57 line:162
  assume HS_SET^HS_HASHABLE^.user_inv(Heap, Current);
  // /home/caf/temp/comcom/repo-hash_set/hs_set.e:169
  // create set
  assert pre.fun.MML_SET^HS_HASHABLE^.default_create(); // type:check tag:function_precondition line:169 cid:166 rid:35
  call update_heap(Current, HS_SET^HS_HASHABLE^.set, Set#Empty()); // line:169
  // /home/caf/temp/comcom/repo-hash_set/hs_set.e:170
  // create buckets.constant ({MML_SEQUENCE [G]}.empty_sequence, buckets.count)
  assert pre.fun.MML_SEQUENCE^MML_SEQUENCE^HS_HASHABLE^^.constant(Seq#Empty(), Seq#Length(Heap[Current, HS_SET^HS_HASHABLE^.buckets])); // type:check tag:function_precondition line:170 cid:125 rid:3282
  call update_heap(Current, HS_SET^HS_HASHABLE^.buckets, Seq#Constant(Seq#Empty(), Seq#Length(Heap[Current, HS_SET^HS_HASHABLE^.buckets]))); // line:170
  if (modify.HS_SET^HS_HASHABLE^.wipe_out(Heap, Current)[Current, observers]) {
    call update_heap(Current, observers, HS_SET^HS_HASHABLE^.observers.static(Heap, Current)); // default:observers line:173
  }
  if (*) {
    assert !(Seq#IsEmpty(Heap[Current, HS_SET^HS_HASHABLE^.buckets])); // type:inv tag:buckets_non_empty line:173 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#Equal(Heap[Current, observers], Set#Singleton(Heap[Current, HS_SET^HS_HASHABLE^.lock])); // type:inv tag:observers_definition line:173 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#NonNull(Heap[Current, HS_SET^HS_HASHABLE^.set]); // type:inv tag:set_non_void line:173 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert (forall i_169: int :: (((1) <= (i_169)) && ((i_169) <= (Seq#Length(Heap[Current, HS_SET^HS_HASHABLE^.buckets])))) ==> ((forall i_170: int :: (((1) <= (i_170)) && ((i_170) <= (Seq#Length(Seq#Item(Heap[Current, HS_SET^HS_HASHABLE^.buckets], i_169))))) ==> (Heap[Current, HS_SET^HS_HASHABLE^.set][Seq#Item(Seq#Item(Heap[Current, HS_SET^HS_HASHABLE^.buckets], i_169), i_170)])))); // type:inv tag:set_not_too_small line:173 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert (forall i_171: int :: (((1) <= (i_171)) && ((i_171) <= (Seq#Length(Heap[Current, HS_SET^HS_HASHABLE^.buckets])))) ==> ((forall i_172: int :: (((1) <= (i_172)) && ((i_172) <= (Seq#Length(Heap[Current, HS_SET^HS_HASHABLE^.buckets])))) ==> ((forall i_173: int :: (((1) <= (i_173)) && ((i_173) <= (Seq#Length(Seq#Item(Heap[Current, HS_SET^HS_HASHABLE^.buckets], i_171))))) ==> ((forall i_174: int :: (((1) <= (i_174)) && ((i_174) <= (Seq#Length(Seq#Item(Heap[Current, HS_SET^HS_HASHABLE^.buckets], i_172))))) ==> ((((i_171) != (i_172)) || ((i_173) != (i_174))) ==> ((Seq#Item(Seq#Item(Heap[Current, HS_SET^HS_HASHABLE^.buckets], i_171), i_173)) != (Seq#Item(Seq#Item(Heap[Current, HS_SET^HS_HASHABLE^.buckets], i_172), i_174))))))))))); // type:inv tag:no_precise_duplicates line:173 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, subjects]); // type:inv tag:default_subjects line:173 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, owns]); // type:inv tag:default_owns line:173 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert admissibility2(Heap, Current); // type:inv tag:A2 line:173 cid:1 rid:55
    assume false;
  }
  call wrap(Current); // default:wrapping cid:1 rid:55 line:173
}

procedure HS_SET^HS_HASHABLE^.bucket_index(Current: ref, hc: int, n: int) returns (Result: int where is_integer_32(Result));
  free requires attached_exact(Heap, Current, HS_SET^HS_HASHABLE^); // info:type property for argument Current
  free requires is_integer_32(hc); // info:type property for argument hc
  free requires is_integer_32(n); // info:type property for argument n
  modifies Heap;
  requires (n) > (0); // type:pre tag:n_positive line:184
  requires (0) <= (hc); // type:pre tag:hc_non_negative line:185
  ensures ((1) <= (Result)) && ((Result) <= (n)); // type:post tag:in_bounds line:189
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.HS_SET^HS_HASHABLE^.bucket_index(Heap, Current, hc, n), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.HS_SET^HS_HASHABLE^.bucket_index(old(Heap), Current, hc, n));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.HS_SET^HS_HASHABLE^.bucket_index(Heap, Current, hc, n), readable);
  free ensures (Result) == (fun.HS_SET^HS_HASHABLE^.bucket_index(old(Heap), Current, hc, n));



function fun.HS_SET^HS_HASHABLE^.bucket_index(heap: HeapType, current: ref, hc: int, n: int) returns (int);

axiom ((forall heap: HeapType, current: ref, hc: int, n: int :: { fun.HS_SET^HS_HASHABLE^.bucket_index(heap, current, hc, n) } (pre.fun.HS_SET^HS_HASHABLE^.bucket_index(heap, current, hc, n)) ==> (((1) <= (fun.HS_SET^HS_HASHABLE^.bucket_index(heap, current, hc, n))) && ((fun.HS_SET^HS_HASHABLE^.bucket_index(heap, current, hc, n)) <= (n)) && (is_integer_32(fun.HS_SET^HS_HASHABLE^.bucket_index(heap, current, hc, n))))));

axiom ((forall h: HeapType, h': HeapType, current: ref, hc: int, n: int :: { HeapSucc(h, h'), fun.HS_SET^HS_HASHABLE^.bucket_index(h, current, hc, n), fun.HS_SET^HS_HASHABLE^.bucket_index(h', current, hc, n) } ((HeapSucc(h, h')) && (pre.fun.HS_SET^HS_HASHABLE^.bucket_index(h, current, hc, n)) && (pre.fun.HS_SET^HS_HASHABLE^.bucket_index(h', current, hc, n)) && (same_inside(h, h', read.fun.HS_SET^HS_HASHABLE^.bucket_index(h, current, hc, n)))) ==> ((fun.HS_SET^HS_HASHABLE^.bucket_index(h, current, hc, n)) == (fun.HS_SET^HS_HASHABLE^.bucket_index(h', current, hc, n)))));

function { :inline } variant.HS_SET^HS_HASHABLE^.bucket_index.1(heap: HeapType, current: ref, hc: int, n: int) returns (int) {
  hc
}

function { :inline } variant.HS_SET^HS_HASHABLE^.bucket_index.2(heap: HeapType, current: ref, hc: int, n: int) returns (int) {
  n
}

implementation HS_SET^HS_HASHABLE^.bucket_index(Current: ref, hc: int, n: int) returns (Result: int)
{

  init_locals:
  Result := 0;

  entry:
  assume {:captureState "HS_SET^HS_HASHABLE^.bucket_index"} true;
  // /home/caf/temp/comcom/repo-hash_set/hs_set.e:187
  // Result := (hc \\ n) + 1
  Result := ((hc) mod (n)) + (1);
}

procedure HS_SET^HS_HASHABLE^.index_of(Current: ref, b: Seq (ref), v: ref) returns (Result: int where is_integer_32(Result));
  free requires attached_exact(Heap, Current, HS_SET^HS_HASHABLE^); // info:type property for argument Current
  free requires Seq#ItemsType(Heap, b, HS_HASHABLE); // info:type property for argument b
  free requires detachable(Heap, v, HS_HASHABLE); // info:type property for argument v
  modifies Heap;
  requires (v) != (Void); // type:attached tag:v_closed line:195
  requires is_closed(Heap, v); // type:pre tag:v_closed line:195
  requires (forall i_175: int :: (((1) <= (i_175)) && ((i_175) <= (Seq#Length(b)))) ==> (pre.fun.MML_SEQUENCE^HS_HASHABLE^.item(b, i_175))); // type:check tag:function_precondition line:196 cid:125 rid:3286
  requires (forall i_175: int :: (((1) <= (i_175)) && ((i_175) <= (Seq#Length(b)))) ==> ((Seq#Item(b, i_175)) != (Void))); // type:attached tag:items_closed line:196
  requires (forall i_175: int :: (((1) <= (i_175)) && ((i_175) <= (Seq#Length(b)))) ==> (is_closed(Heap, Seq#Item(b, i_175)))); // type:pre tag:items_closed line:196
  ensures (Seq#Domain(b)[Result]) ==> ((v) != (Void)); // type:attached tag:definition_found line:211
  ensures (Seq#Domain(b)[Result]) ==> (pre.fun.MML_SEQUENCE^HS_HASHABLE^.item(b, Result)); // type:check tag:function_precondition line:211 cid:125 rid:3286
  ensures (Seq#Domain(b)[Result]) ==> (pre.fun.HS_HASHABLE.is_model_equal(Heap, v, Seq#Item(b, Result))); // type:check tag:function_precondition line:211 cid:406 rid:81
  ensures (Seq#Domain(b)[Result]) ==> (fun.HS_HASHABLE.is_model_equal(Heap, v, Seq#Item(b, Result))); // type:post tag:definition_found line:211
  ensures (!(Seq#Domain(b)[Result])) ==> ((v) != (Void)); // type:attached tag:definition_not_found line:212
  ensures (forall i_176: int :: (((1) <= (i_176)) && ((i_176) <= (Seq#Length(b)))) ==> ((!(Seq#Domain(b)[Result])) ==> (pre.fun.MML_SEQUENCE^HS_HASHABLE^.item(b, i_176)))); // type:check tag:function_precondition line:212 cid:125 rid:3286
  ensures (forall i_176: int :: (((1) <= (i_176)) && ((i_176) <= (Seq#Length(b)))) ==> ((!(Seq#Domain(b)[Result])) ==> (pre.fun.HS_HASHABLE.is_model_equal(Heap, v, Seq#Item(b, i_176))))); // type:check tag:function_precondition line:212 cid:406 rid:81
  ensures (!(Seq#Domain(b)[Result])) ==> ((forall i_176: int :: (((1) <= (i_176)) && ((i_176) <= (Seq#Length(b)))) ==> (!(fun.HS_HASHABLE.is_model_equal(Heap, v, Seq#Item(b, i_176)))))); // type:post tag:definition_not_found line:212
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.HS_SET^HS_HASHABLE^.index_of(Heap, Current, b, v), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.HS_SET^HS_HASHABLE^.index_of(old(Heap), Current, b, v));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.HS_SET^HS_HASHABLE^.index_of(Heap, Current, b, v), readable);
  free ensures (Result) == (fun.HS_SET^HS_HASHABLE^.index_of(old(Heap), Current, b, v));



function fun.HS_SET^HS_HASHABLE^.index_of(heap: HeapType, current: ref, b: Seq (ref), v: ref) returns (int);

axiom ((forall heap: HeapType, current: ref, b: Seq (ref), v: ref :: { fun.HS_SET^HS_HASHABLE^.index_of(heap, current, b, v) } (pre.fun.HS_SET^HS_HASHABLE^.index_of(heap, current, b, v)) ==> (((Seq#Domain(b)[fun.HS_SET^HS_HASHABLE^.index_of(heap, current, b, v)]) ==> (fun.HS_HASHABLE.is_model_equal(heap, v, Seq#Item(b, fun.HS_SET^HS_HASHABLE^.index_of(heap, current, b, v))))) && ((!(Seq#Domain(b)[fun.HS_SET^HS_HASHABLE^.index_of(heap, current, b, v)])) ==> ((forall i_178: int :: (((1) <= (i_178)) && ((i_178) <= (Seq#Length(b)))) ==> (!(fun.HS_HASHABLE.is_model_equal(heap, v, Seq#Item(b, i_178))))))) && (is_integer_32(fun.HS_SET^HS_HASHABLE^.index_of(heap, current, b, v))))));

axiom ((forall h: HeapType, h': HeapType, current: ref, b: Seq (ref), v: ref :: { HeapSucc(h, h'), fun.HS_SET^HS_HASHABLE^.index_of(h, current, b, v), fun.HS_SET^HS_HASHABLE^.index_of(h', current, b, v) } ((HeapSucc(h, h')) && (pre.fun.HS_SET^HS_HASHABLE^.index_of(h, current, b, v)) && (pre.fun.HS_SET^HS_HASHABLE^.index_of(h', current, b, v)) && (same_inside(h, h', read.fun.HS_SET^HS_HASHABLE^.index_of(h, current, b, v)))) ==> ((fun.HS_SET^HS_HASHABLE^.index_of(h, current, b, v)) == (fun.HS_SET^HS_HASHABLE^.index_of(h', current, b, v)))));

function { :inline } variant.HS_SET^HS_HASHABLE^.index_of.1(heap: HeapType, current: ref, b: Seq (ref), v: ref) returns (Seq (ref)) {
  b
}

function { :inline } variant.HS_SET^HS_HASHABLE^.index_of.2(heap: HeapType, current: ref, b: Seq (ref), v: ref) returns (ref) {
  v
}

implementation HS_SET^HS_HASHABLE^.index_of(Current: ref, b: Seq (ref), v: ref) returns (Result: int)
{
  var PreLoopHeap_182: HeapType;
  var variant_184: int;

  init_locals:
  variant_184 := 0;
  Result := 0;

  entry:
  assume {:captureState "HS_SET^HS_HASHABLE^.index_of"} true;
  // /home/caf/temp/comcom/repo-hash_set/hs_set.e:199
  // Result := 1
  Result := 1;
  PreLoopHeap_182 := Heap;
  goto loop_head_179;
  loop_head_179:
  // /home/caf/temp/comcom/repo-hash_set/hs_set.e:201
  // 1 <= Result and Result <= b.count + 1
  assert ((1) <= (Result)) && ((Result) <= ((Seq#Length(b)) + (1))); // type:loop_inv line:201
  // /home/caf/temp/comcom/repo-hash_set/hs_set.e:202
  // across 1 |..| (Result - 1) as j all not v.is_model_equal (b [j.item]) end
  assert {:subsumption 0} (v) != (Void); // type:attached line:202
  assert (forall i_183: int :: (((1) <= (i_183)) && ((i_183) <= ((Result) - (1)))) ==> (pre.fun.MML_SEQUENCE^HS_HASHABLE^.item(b, i_183))); // type:check tag:function_precondition line:202 cid:125 rid:3286
  assert (forall i_183: int :: (((1) <= (i_183)) && ((i_183) <= ((Result) - (1)))) ==> (Frame#Subset(read.fun.HS_HASHABLE.is_model_equal(Heap, v, Seq#Item(b, i_183)), readable))); // type:access tag:frame_readable line:202 cid:406 rid:81
  assert (forall i_183: int :: (((1) <= (i_183)) && ((i_183) <= ((Result) - (1)))) ==> (pre.fun.HS_HASHABLE.is_model_equal(Heap, v, Seq#Item(b, i_183)))); // type:check tag:function_precondition line:202 cid:406 rid:81
  assert (forall i_183: int :: (((1) <= (i_183)) && ((i_183) <= ((Result) - (1)))) ==> (!(fun.HS_HASHABLE.is_model_equal(Heap, v, Seq#Item(b, i_183))))); // type:loop_inv line:202
  assume HeapSucc(PreLoopHeap_182, Heap);
  assume same_outside(old(Heap), Heap, modify.HS_SET^HS_HASHABLE^.index_of(old(Heap), Current, b, v));
  assume global(Heap);
  // /home/caf/temp/comcom/repo-hash_set/hs_set.e:-1
  assert {:subsumption 0} (!((Result) > (Seq#Length(b)))) ==> ((v) != (Void)); // type:attached line:-1
  assert (!((Result) > (Seq#Length(b)))) ==> (pre.fun.MML_SEQUENCE^HS_HASHABLE^.item(b, Result)); // type:check tag:function_precondition line:-1 cid:125 rid:3286
  assert (!((Result) > (Seq#Length(b)))) ==> (Frame#Subset(read.fun.HS_HASHABLE.is_model_equal(Heap, v, Seq#Item(b, Result)), readable)); // type:access tag:frame_readable line:-1 cid:406 rid:81
  assert (!((Result) > (Seq#Length(b)))) ==> (pre.fun.HS_HASHABLE.is_model_equal(Heap, v, Seq#Item(b, Result))); // type:check tag:function_precondition line:-1 cid:406 rid:81
  goto loop_body_180, loop_end_181;
  loop_body_180:
  assume !(((Result) > (Seq#Length(b))) || (fun.HS_HASHABLE.is_model_equal(Heap, v, Seq#Item(b, Result))));
  // /home/caf/temp/comcom/repo-hash_set/hs_set.e:208
  // b.count - Result
  variant_184 := (Seq#Length(b)) - (Result);
  // /home/caf/temp/comcom/repo-hash_set/hs_set.e:206
  // Result := Result + 1
  Result := (Result) + (1);
  // /home/caf/temp/comcom/repo-hash_set/hs_set.e:208
  // b.count - Result
  assert {:subsumption 0} ((((Seq#Length(b)) - (Result)) <= (variant_184)) && ((variant_184) <= ((Seq#Length(b)) - (Result)))) || ((0) <= (variant_184)); // type:termination tag:bounded line:208 varid:1
  assert {:subsumption 0} (((Seq#Length(b)) - (Result)) <= (variant_184)) && (!((variant_184) <= ((Seq#Length(b)) - (Result)))); // type:termination tag:variant_decreases line:208
  goto loop_head_179;
  loop_end_181:
  assume ((Result) > (Seq#Length(b))) || (fun.HS_HASHABLE.is_model_equal(Heap, v, Seq#Item(b, Result)));
}

procedure HS_SET^HS_HASHABLE^.set_has(Current: ref, v: ref) returns (Result: bool where true);
  free requires attached_exact(Heap, Current, HS_SET^HS_HASHABLE^); // info:type property for argument Current
  free requires detachable(Heap, v, HS_HASHABLE); // info:type property for argument v
  modifies Heap;
  requires (v) != (Void); // type:pre tag:v_exists line:244
  requires Set#NonNull(Heap[Current, HS_SET^HS_HASHABLE^.set]); // type:pre tag:set_non_void line:245
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.HS_SET^HS_HASHABLE^.set_has(Heap, Current, v), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.HS_SET^HS_HASHABLE^.set_has(old(Heap), Current, v));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.HS_SET^HS_HASHABLE^.set_has(Heap, Current, v), readable);



function fun.HS_SET^HS_HASHABLE^.set_has(heap: HeapType, current: ref, v: ref) returns (bool);

function fun0.HS_SET^HS_HASHABLE^.set_has(heap: HeapType, current: ref, v: ref) returns (bool);

axiom ((forall heap: HeapType, current: ref, v: ref :: { fun.HS_SET^HS_HASHABLE^.set_has(heap, current, v) } { trigger.fun.HS_SET^HS_HASHABLE^.set_has(heap, current, v) } (pre.fun.HS_SET^HS_HASHABLE^.set_has(heap, current, v)) ==> ((fun.HS_SET^HS_HASHABLE^.set_has(heap, current, v)) == ((exists i_185: ref :: (heap[current, HS_SET^HS_HASHABLE^.set][i_185]) && (fun.HS_HASHABLE.is_model_equal(heap, v, i_185)))))));

axiom ((forall heap: HeapType, current: ref, v: ref :: { fun.HS_SET^HS_HASHABLE^.set_has(heap, current, v) } (fun.HS_SET^HS_HASHABLE^.set_has(heap, current, v)) == (fun0.HS_SET^HS_HASHABLE^.set_has(heap, current, v))));

axiom ((forall h: HeapType, h': HeapType, current: ref, v: ref :: { HeapSucc(h, h'), fun0.HS_SET^HS_HASHABLE^.set_has(h, current, v), fun0.HS_SET^HS_HASHABLE^.set_has(h', current, v) } ((HeapSucc(h, h')) && (pre.fun.HS_SET^HS_HASHABLE^.set_has(h, current, v)) && (pre.fun.HS_SET^HS_HASHABLE^.set_has(h', current, v)) && (same_inside(h, h', read.fun.HS_SET^HS_HASHABLE^.set_has(h, current, v)))) ==> ((fun0.HS_SET^HS_HASHABLE^.set_has(h, current, v)) == (fun0.HS_SET^HS_HASHABLE^.set_has(h', current, v)))));

function { :inline } variant.HS_SET^HS_HASHABLE^.set_has.1(heap: HeapType, current: ref, v: ref) returns (ref) {
  v
}

implementation HS_SET^HS_HASHABLE^.set_has(Current: ref, v: ref) returns (Result: bool)
{

  init_locals:
  Result := false;

  entry:
  assume {:captureState "HS_SET^HS_HASHABLE^.set_has"} true;
  // /home/caf/temp/comcom/repo-hash_set/hs_set.e:248
  // Result := across set as x some v.is_model_equal (x.item) end
  assert readable[Current, HS_SET^HS_HASHABLE^.set]; // type:access tag:attribute_readable line:248 cid:405 fid:88
  assert {:subsumption 0} (v) != (Void); // type:attached line:248
  assert (forall i_186: ref :: (Heap[Current, HS_SET^HS_HASHABLE^.set][i_186]) ==> (Frame#Subset(read.fun.HS_HASHABLE.is_model_equal(Heap, v, i_186), readable))); // type:access tag:frame_readable line:248 cid:406 rid:81
  assert (forall i_186: ref :: (Heap[Current, HS_SET^HS_HASHABLE^.set][i_186]) ==> (pre.fun.HS_HASHABLE.is_model_equal(Heap, v, i_186))); // type:check tag:function_precondition line:248 cid:406 rid:81
  Result := (exists i_186: ref :: (Heap[Current, HS_SET^HS_HASHABLE^.set][i_186]) && (fun.HS_HASHABLE.is_model_equal(Heap, v, i_186)));
}

procedure HS_SET^HS_HASHABLE^.no_duplicates(Current: ref, s: Set (ref)) returns (Result: bool where true);
  free requires attached_exact(Heap, Current, HS_SET^HS_HASHABLE^); // info:type property for argument Current
  free requires Set#ItemsType(Heap, s, HS_HASHABLE); // info:type property for argument s
  modifies Heap;
  requires Set#NonNull(s); // type:pre tag:non_void line:256
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.HS_SET^HS_HASHABLE^.no_duplicates(Heap, Current, s), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.HS_SET^HS_HASHABLE^.no_duplicates(old(Heap), Current, s));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.HS_SET^HS_HASHABLE^.no_duplicates(Heap, Current, s), readable);



function fun.HS_SET^HS_HASHABLE^.no_duplicates(heap: HeapType, current: ref, s: Set (ref)) returns (bool);

function fun0.HS_SET^HS_HASHABLE^.no_duplicates(heap: HeapType, current: ref, s: Set (ref)) returns (bool);

axiom ((forall heap: HeapType, current: ref, s: Set (ref) :: { fun.HS_SET^HS_HASHABLE^.no_duplicates(heap, current, s) } { trigger.fun.HS_SET^HS_HASHABLE^.no_duplicates(heap, current, s) } (pre.fun.HS_SET^HS_HASHABLE^.no_duplicates(heap, current, s)) ==> ((fun.HS_SET^HS_HASHABLE^.no_duplicates(heap, current, s)) == ((forall i_187: ref :: (s[i_187]) ==> ((forall i_188: ref :: (s[i_188]) ==> (((i_187) != (i_188)) ==> (!(fun.HS_HASHABLE.is_model_equal(heap, i_187, i_188)))))))))));

axiom ((forall heap: HeapType, current: ref, s: Set (ref) :: { fun.HS_SET^HS_HASHABLE^.no_duplicates(heap, current, s) } (fun.HS_SET^HS_HASHABLE^.no_duplicates(heap, current, s)) == (fun0.HS_SET^HS_HASHABLE^.no_duplicates(heap, current, s))));

axiom ((forall h: HeapType, h': HeapType, current: ref, s: Set (ref) :: { HeapSucc(h, h'), fun0.HS_SET^HS_HASHABLE^.no_duplicates(h, current, s), fun0.HS_SET^HS_HASHABLE^.no_duplicates(h', current, s) } ((HeapSucc(h, h')) && (pre.fun.HS_SET^HS_HASHABLE^.no_duplicates(h, current, s)) && (pre.fun.HS_SET^HS_HASHABLE^.no_duplicates(h', current, s)) && (same_inside(h, h', read.fun.HS_SET^HS_HASHABLE^.no_duplicates(h, current, s)))) ==> ((fun0.HS_SET^HS_HASHABLE^.no_duplicates(h, current, s)) == (fun0.HS_SET^HS_HASHABLE^.no_duplicates(h', current, s)))));

function { :inline } variant.HS_SET^HS_HASHABLE^.no_duplicates.1(heap: HeapType, current: ref, s: Set (ref)) returns (Set (ref)) {
  s
}

implementation HS_SET^HS_HASHABLE^.no_duplicates(Current: ref, s: Set (ref)) returns (Result: bool)
{

  init_locals:
  Result := false;

  entry:
  assume {:captureState "HS_SET^HS_HASHABLE^.no_duplicates"} true;
  // /home/caf/temp/comcom/repo-hash_set/hs_set.e:259
  // Result := across s as x all across s as y all x.item /= y.item implies not x.item.is_model_equal (y.item) end end
  assert (forall i_189: ref :: (s[i_189]) ==> ((forall i_190: ref :: (s[i_190]) ==> (((i_189) != (i_190)) ==> (Frame#Subset(read.fun.HS_HASHABLE.is_model_equal(Heap, i_189, i_190), readable)))))); // type:access tag:frame_readable line:259 cid:406 rid:81
  assert (forall i_189: ref :: (s[i_189]) ==> ((forall i_190: ref :: (s[i_190]) ==> (((i_189) != (i_190)) ==> (pre.fun.HS_HASHABLE.is_model_equal(Heap, i_189, i_190)))))); // type:check tag:function_precondition line:259 cid:406 rid:81
  Result := (forall i_189: ref :: (s[i_189]) ==> ((forall i_190: ref :: (s[i_190]) ==> (((i_189) != (i_190)) ==> (!(fun.HS_HASHABLE.is_model_equal(Heap, i_189, i_190)))))));
}

const HS_LOCK^HS_HASHABLE^.sets: Field (Set (ref));

axiom ((FieldId(HS_LOCK^HS_HASHABLE^.sets, HS_LOCK^HS_HASHABLE^)) == (80));

axiom ((forall heap: HeapType, o: ref :: { heap[o, HS_LOCK^HS_HASHABLE^.sets] } ((IsHeap(heap)) && (attached(heap, o, HS_LOCK^HS_HASHABLE^))) ==> (Set#ItemsType(heap, heap[o, HS_LOCK^HS_HASHABLE^.sets], HS_SET^HS_HASHABLE^))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, HS_LOCK^HS_HASHABLE^.sets, v, o) } (attached_exact(heap, current, HS_LOCK^HS_HASHABLE^)) ==> ((guard(heap, current, HS_LOCK^HS_HASHABLE^.sets, v, o)) <==> (false))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, HS_LOCK^HS_HASHABLE^.sets, v, o) } (attached(heap, current, HS_LOCK^HS_HASHABLE^)) ==> ((guard(heap, current, HS_LOCK^HS_HASHABLE^.sets, v, o)) ==> (false))));

const HS_SET^HS_HASHABLE^.lock: Field (ref);

axiom ((FieldId(HS_SET^HS_HASHABLE^.lock, HS_SET^HS_HASHABLE^)) == (90));

axiom ((forall heap: HeapType, o: ref :: { heap[o, HS_SET^HS_HASHABLE^.lock] } ((IsHeap(heap)) && (attached(heap, o, HS_SET^HS_HASHABLE^))) ==> (detachable_exact(heap, heap[o, HS_SET^HS_HASHABLE^.lock], HS_LOCK^HS_HASHABLE^))));

axiom ((forall heap: HeapType, current: ref, v: ref, o: ref :: { guard(heap, current, HS_SET^HS_HASHABLE^.lock, v, o) } (attached_exact(heap, current, HS_SET^HS_HASHABLE^)) ==> ((guard(heap, current, HS_SET^HS_HASHABLE^.lock, v, o)) <==> (false))));

axiom ((forall heap: HeapType, current: ref, v: ref, o: ref :: { guard(heap, current, HS_SET^HS_HASHABLE^.lock, v, o) } (attached(heap, current, HS_SET^HS_HASHABLE^)) ==> ((guard(heap, current, HS_SET^HS_HASHABLE^.lock, v, o)) ==> (false))));

const HS_SET^HS_HASHABLE^.set: Field (Set (ref));

axiom ((FieldId(HS_SET^HS_HASHABLE^.set, HS_SET^HS_HASHABLE^)) == (88));

axiom ((forall heap: HeapType, o: ref :: { heap[o, HS_SET^HS_HASHABLE^.set] } ((IsHeap(heap)) && (attached(heap, o, HS_SET^HS_HASHABLE^))) ==> (Set#ItemsType(heap, heap[o, HS_SET^HS_HASHABLE^.set], HS_HASHABLE))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, HS_SET^HS_HASHABLE^.set, v, o) } (attached_exact(heap, current, HS_SET^HS_HASHABLE^)) ==> ((guard(heap, current, HS_SET^HS_HASHABLE^.set, v, o)) <==> ((user_inv(heap, o)) ==> (user_inv(heap[current, HS_SET^HS_HASHABLE^.set := v], o))))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, HS_SET^HS_HASHABLE^.set, v, o) } (attached(heap, current, HS_SET^HS_HASHABLE^)) ==> ((guard(heap, current, HS_SET^HS_HASHABLE^.set, v, o)) ==> ((user_inv(heap, o)) ==> (user_inv(heap[current, HS_SET^HS_HASHABLE^.set := v], o))))));

const HS_SET^HS_HASHABLE^.buckets: Field (Seq (Seq (ref)));

axiom ((FieldId(HS_SET^HS_HASHABLE^.buckets, HS_SET^HS_HASHABLE^)) == (89));

axiom ((forall heap: HeapType, current: ref, v: Seq (Seq (ref)), o: ref :: { guard(heap, current, HS_SET^HS_HASHABLE^.buckets, v, o) } (attached_exact(heap, current, HS_SET^HS_HASHABLE^)) ==> ((guard(heap, current, HS_SET^HS_HASHABLE^.buckets, v, o)) <==> ((user_inv(heap, o)) ==> (user_inv(heap[current, HS_SET^HS_HASHABLE^.buckets := v], o))))));

axiom ((forall heap: HeapType, current: ref, v: Seq (Seq (ref)), o: ref :: { guard(heap, current, HS_SET^HS_HASHABLE^.buckets, v, o) } (attached(heap, current, HS_SET^HS_HASHABLE^)) ==> ((guard(heap, current, HS_SET^HS_HASHABLE^.buckets, v, o)) ==> ((user_inv(heap, o)) ==> (user_inv(heap[current, HS_SET^HS_HASHABLE^.buckets := v], o))))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, owns, v, o) } (attached_exact(heap, current, ANY)) ==> ((guard(heap, current, owns, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, subjects, v, o) } (attached_exact(heap, current, ANY)) ==> ((guard(heap, current, subjects, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached_exact(heap, current, ANY)) ==> ((guard(heap, current, observers, v, o)) <==> (fun.ANY.in_observers(heap, current, v, o)))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached(heap, current, ANY)) ==> ((guard(heap, current, observers, v, o)) ==> (fun.ANY.in_observers(heap, current, v, o)))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, owns, v, o) } (attached_exact(heap, current, HS_LOCK^HS_HASHABLE^)) ==> ((guard(heap, current, owns, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, subjects, v, o) } (attached_exact(heap, current, HS_LOCK^HS_HASHABLE^)) ==> ((guard(heap, current, subjects, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached_exact(heap, current, HS_LOCK^HS_HASHABLE^)) ==> ((guard(heap, current, observers, v, o)) <==> (fun.HS_LOCK^HS_HASHABLE^.in_observers(heap, current, v, o)))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached(heap, current, HS_LOCK^HS_HASHABLE^)) ==> ((guard(heap, current, observers, v, o)) ==> (fun.HS_LOCK^HS_HASHABLE^.in_observers(heap, current, v, o)))));

function modify.HS_LOCK^HS_HASHABLE^.default_create(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T13> $o: ref, $f: Field T13 :: { modify.HS_LOCK^HS_HASHABLE^.default_create(heap, current)[$o, $f] } (modify.HS_LOCK^HS_HASHABLE^.default_create(heap, current)[$o, $f]) <==> (($o) == (current))))));

function modify.HS_LOCK^HS_HASHABLE^.add_set(heap: HeapType, current: ref, s: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, s: ref :: (IsHeap(heap)) ==> ((forall <T14> $o: ref, $f: Field T14 :: { modify.HS_LOCK^HS_HASHABLE^.add_set(heap, current, s)[$o, $f] } (modify.HS_LOCK^HS_HASHABLE^.add_set(heap, current, s)[$o, $f]) <==> (((($o) == (current)) && ((($f) == (HS_LOCK^HS_HASHABLE^.sets)) || (($f) == (subjects)) || (($f) == (closed)))) || ((heap[current, owns][$o]) && (($f) == (owner))))))));

function modify.HS_LOCK^HS_HASHABLE^.lock(heap: HeapType, current: ref, item: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, item: ref :: (IsHeap(heap)) ==> ((forall <T15> $o: ref, $f: Field T15 :: { modify.HS_LOCK^HS_HASHABLE^.lock(heap, current, item)[$o, $f] } (modify.HS_LOCK^HS_HASHABLE^.lock(heap, current, item)[$o, $f]) <==> (((($o) == (current)) && ((($f) == (owns)) || (($f) == (closed)))) || (((($o) == (item)) || (heap[current, owns][$o])) && (($f) == (owner))))))));

function modify.HS_LOCK^HS_HASHABLE^.unlock(heap: HeapType, current: ref, item: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, item: ref :: (IsHeap(heap)) ==> ((forall <T16> $o: ref, $f: Field T16 :: { modify.HS_LOCK^HS_HASHABLE^.unlock(heap, current, item)[$o, $f] } (modify.HS_LOCK^HS_HASHABLE^.unlock(heap, current, item)[$o, $f]) <==> (((($o) == (current)) && ((($f) == (owns)) || (($f) == (closed)))) || (((($o) == (item)) || (heap[current, owns][$o])) && (($f) == (owner))))))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, owns, v, o) } (attached_exact(heap, current, HS_CLIENT)) ==> ((guard(heap, current, owns, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, subjects, v, o) } (attached_exact(heap, current, HS_CLIENT)) ==> ((guard(heap, current, subjects, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached_exact(heap, current, HS_CLIENT)) ==> ((guard(heap, current, observers, v, o)) <==> (fun.HS_CLIENT.in_observers(heap, current, v, o)))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached(heap, current, HS_CLIENT)) ==> ((guard(heap, current, observers, v, o)) ==> (fun.HS_CLIENT.in_observers(heap, current, v, o)))));

function modify.HS_CLIENT.default_create(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T17> $o: ref, $f: Field T17 :: { modify.HS_CLIENT.default_create(heap, current)[$o, $f] } (modify.HS_CLIENT.default_create(heap, current)[$o, $f]) <==> (($o) == (current))))));

function modify.HS_CLIENT.test(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T18> $o: ref, $f: Field T18 :: { modify.HS_CLIENT.test(heap, current)[$o, $f] } (modify.HS_CLIENT.test(heap, current)[$o, $f]) <==> (($o) == (current))))));

const unique HS_LOCK^HS_KEY^: Type;

axiom (is_frozen(HS_LOCK^HS_KEY^));

axiom ((HS_LOCK^HS_KEY^) <: (ANY));

axiom ((forall t: Type :: { (HS_LOCK^HS_KEY^) <: (t) } ((HS_LOCK^HS_KEY^) <: (t)) <==> (((t) == (HS_LOCK^HS_KEY^)) || ((ANY) <: (t)))));

axiom ((FieldId(allocated, HS_LOCK^HS_KEY^)) == (-1));

axiom ((FieldId(closed, HS_LOCK^HS_KEY^)) == (-2));

axiom ((FieldId(owner, HS_LOCK^HS_KEY^)) == (-3));

axiom ((FieldId(owns, HS_LOCK^HS_KEY^)) == (-4));

axiom ((FieldId(observers, HS_LOCK^HS_KEY^)) == (-5));

axiom ((FieldId(subjects, HS_LOCK^HS_KEY^)) == (-6));

axiom ((forall <T19> $f: Field T19 :: { IsModelField($f, HS_LOCK^HS_KEY^) } (IsModelField($f, HS_LOCK^HS_KEY^)) <==> ((($f) == (subjects)) || (($f) == (observers)))));

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached_exact(heap, current, HS_LOCK^HS_KEY^)) ==> ((user_inv(heap, current)) <==> (HS_LOCK^HS_KEY^.user_inv(heap, current)))));

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached(heap, current, HS_LOCK^HS_KEY^)) ==> ((user_inv(heap, current)) ==> (HS_LOCK^HS_KEY^.user_inv(heap, current)))));

procedure create.HS_LOCK^HS_KEY^.default_create(Current: ref);
  free requires attached_exact(Heap, Current, HS_LOCK^HS_KEY^); // info:type property for argument Current
  modifies Heap;
  requires (forall <T20> $f: Field T20 :: (($f) != (allocated)) ==> ((Heap[Current, $f]) == (Default($f))));
  ensures (forall <T21> $f: Field T21 :: ((($f) != (allocated)) && (($f) != (closed))) ==> ((Heap[Current, $f]) == (Default($f))));
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.HS_LOCK^HS_KEY^.default_create(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.HS_LOCK^HS_KEY^.default_create(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts



const unique HS_SET^HS_KEY^: Type;

axiom ((HS_SET^HS_KEY^) <: (ANY));

axiom ((forall t: Type :: { (HS_SET^HS_KEY^) <: (t) } ((HS_SET^HS_KEY^) <: (t)) <==> (((t) == (HS_SET^HS_KEY^)) || ((ANY) <: (t)))));

axiom ((FieldId(allocated, HS_SET^HS_KEY^)) == (-1));

axiom ((FieldId(closed, HS_SET^HS_KEY^)) == (-2));

axiom ((FieldId(owner, HS_SET^HS_KEY^)) == (-3));

axiom ((FieldId(owns, HS_SET^HS_KEY^)) == (-4));

axiom ((FieldId(observers, HS_SET^HS_KEY^)) == (-5));

axiom ((FieldId(subjects, HS_SET^HS_KEY^)) == (-6));

axiom ((forall <T22> $f: Field T22 :: { IsModelField($f, HS_SET^HS_KEY^) } (IsModelField($f, HS_SET^HS_KEY^)) <==> ((($f) == (HS_SET^HS_KEY^.set)) || (($f) == (HS_SET^HS_KEY^.lock)) || (($f) == (subjects)) || (($f) == (observers)))));

function { :inline } HS_SET^HS_KEY^.user_inv(heap: HeapType, current: ref) returns (bool) {
  (!(Seq#IsEmpty(heap[current, HS_SET^HS_KEY^.buckets]))) && (Set#Equal(heap[current, observers], Set#Singleton(heap[current, HS_SET^HS_KEY^.lock]))) && (Set#NonNull(heap[current, HS_SET^HS_KEY^.set])) && ((forall i_191: int :: (((1) <= (i_191)) && ((i_191) <= (Seq#Length(heap[current, HS_SET^HS_KEY^.buckets])))) ==> ((forall i_192: int :: (((1) <= (i_192)) && ((i_192) <= (Seq#Length(Seq#Item(heap[current, HS_SET^HS_KEY^.buckets], i_191))))) ==> (heap[current, HS_SET^HS_KEY^.set][Seq#Item(Seq#Item(heap[current, HS_SET^HS_KEY^.buckets], i_191), i_192)]))))) && ((forall i_193: int :: (((1) <= (i_193)) && ((i_193) <= (Seq#Length(heap[current, HS_SET^HS_KEY^.buckets])))) ==> ((forall i_194: int :: (((1) <= (i_194)) && ((i_194) <= (Seq#Length(heap[current, HS_SET^HS_KEY^.buckets])))) ==> ((forall i_195: int :: (((1) <= (i_195)) && ((i_195) <= (Seq#Length(Seq#Item(heap[current, HS_SET^HS_KEY^.buckets], i_193))))) ==> ((forall i_196: int :: (((1) <= (i_196)) && ((i_196) <= (Seq#Length(Seq#Item(heap[current, HS_SET^HS_KEY^.buckets], i_194))))) ==> ((((i_193) != (i_194)) || ((i_195) != (i_196))) ==> ((Seq#Item(Seq#Item(heap[current, HS_SET^HS_KEY^.buckets], i_193), i_195)) != (Seq#Item(Seq#Item(heap[current, HS_SET^HS_KEY^.buckets], i_194), i_196)))))))))))) && (Set#IsEmpty(heap[current, subjects])) && (Set#IsEmpty(heap[current, owns])) && (admissibility2(heap, current))
}

function HS_SET^HS_KEY^.observers.static(heap: HeapType, current: ref) returns (Set (ref)) {
  Set#Singleton(heap[current, HS_SET^HS_KEY^.lock])
}

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached_exact(heap, current, HS_SET^HS_KEY^)) ==> ((user_inv(heap, current)) <==> (HS_SET^HS_KEY^.user_inv(heap, current)))));

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached(heap, current, HS_SET^HS_KEY^)) ==> ((user_inv(heap, current)) ==> (HS_SET^HS_KEY^.user_inv(heap, current)))));

procedure create.HS_SET^HS_KEY^.make(Current: ref, l: ref);
  free requires attached_exact(Heap, Current, HS_SET^HS_KEY^); // info:type property for argument Current
  free requires detachable_exact(Heap, l, HS_LOCK^HS_KEY^); // info:type property for argument l
  modifies Heap;
  ensures Set#IsEmpty(Heap[Current, HS_SET^HS_KEY^.set]); // type:post tag:set_empty line:24
  ensures (Heap[Current, HS_SET^HS_KEY^.lock]) == (l); // type:post tag:lock_set line:25
  requires (forall <T23> $f: Field T23 :: (($f) != (allocated)) ==> ((Heap[Current, $f]) == (Default($f))));
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.HS_SET^HS_KEY^.make(Heap, Current, l), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.HS_SET^HS_KEY^.make(old(Heap), Current, l));
  free ensures HeapSucc(old(Heap), Heap);
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts
  requires is_wrapped(Heap, l); // type:pre tag:arg_l_is_wrapped default:contracts
  ensures is_wrapped(Heap, l); // type:post tag:arg_l_is_wrapped default:contracts



procedure HS_LOCK^HS_KEY^.add_set(Current: ref, s: ref);
  free requires attached_exact(Heap, Current, HS_LOCK^HS_KEY^); // info:type property for argument Current
  free requires detachable(Heap, s, HS_SET^HS_KEY^); // info:type property for argument s
  modifies Heap;
  requires is_wrapped(Heap, Current); // type:pre tag:wrapped line:23
  requires (s) != (Void); // type:attached tag:s_wrapped line:24
  requires is_wrapped(Heap, s); // type:pre tag:s_wrapped line:24
  requires (Heap[s, HS_SET^HS_KEY^.lock]) == (Current); // type:pre tag:valid_lock line:25
  requires Heap[s, observers][Current]; // type:pre tag:valid_observers line:26
  requires Set#IsEmpty(Heap[s, HS_SET^HS_KEY^.set]); // type:pre tag:empty_set line:27
  ensures Set#Equal(Heap[Current, HS_LOCK^HS_KEY^.sets], Set#Extended(old(Heap)[Current, HS_LOCK^HS_KEY^.sets], s)); // type:post tag:sets_effect line:36
  ensures is_wrapped(Heap, Current); // type:post tag:wrapped line:37
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.HS_LOCK^HS_KEY^.add_set(Heap, Current, s), writable); // type:pre tag:frame_writable
  free ensures flat_same_outside(old(Heap), Heap, modify.HS_LOCK^HS_KEY^.add_set(old(Heap), Current, s));
  free ensures HeapSucc(old(Heap), Heap);



procedure HS_LOCK^HS_KEY^.lock(Current: ref, item: ref);
  free requires attached_exact(Heap, Current, HS_LOCK^HS_KEY^); // info:type property for argument Current
  free requires detachable(Heap, item, HS_KEY); // info:type property for argument item
  modifies Heap;
  requires is_wrapped(Heap, Current); // type:pre tag:wrapped line:45
  requires (item) != (Void); // type:attached tag:item_wrapped line:46
  requires is_wrapped(Heap, item); // type:pre tag:item_wrapped line:46
  requires !(Heap[Current, subjects][item]); // type:pre tag:item_not_set line:47
  ensures Set#Equal(Heap[Current, owns], Set#Extended(old(Heap)[Current, owns], item)); // type:post tag:owns_effect line:55
  ensures is_wrapped(Heap, Current); // type:post tag:wrapped line:56
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.HS_LOCK^HS_KEY^.lock(Heap, Current, item), writable); // type:pre tag:frame_writable
  free ensures flat_same_outside(old(Heap), Heap, modify.HS_LOCK^HS_KEY^.lock(old(Heap), Current, item));
  free ensures HeapSucc(old(Heap), Heap);



const HS_KEY.value: Field int;

axiom ((FieldId(HS_KEY.value, HS_KEY)) == (78));

axiom ((forall heap: HeapType, o: ref :: { heap[o, HS_KEY.value] } ((IsHeap(heap)) && (attached(heap, o, HS_KEY))) ==> (is_integer_32(heap[o, HS_KEY.value]))));

axiom ((forall heap: HeapType, current: ref, v: int, o: ref :: { guard(heap, current, HS_KEY.value, v, o) } (attached_exact(heap, current, HS_KEY)) ==> ((guard(heap, current, HS_KEY.value, v, o)) <==> ((user_inv(heap, o)) ==> (user_inv(heap[current, HS_KEY.value := v], o))))));

axiom ((forall heap: HeapType, current: ref, v: int, o: ref :: { guard(heap, current, HS_KEY.value, v, o) } (attached(heap, current, HS_KEY)) ==> ((guard(heap, current, HS_KEY.value, v, o)) ==> ((user_inv(heap, o)) ==> (user_inv(heap[current, HS_KEY.value := v], o))))));

procedure HS_SET^HS_KEY^.extend(Current: ref, v: ref);
  free requires attached_exact(Heap, Current, HS_SET^HS_KEY^); // info:type property for argument Current
  free requires detachable(Heap, v, HS_KEY); // info:type property for argument v
  modifies Heap;
  requires (Heap[Current, HS_SET^HS_KEY^.lock]) != (Void); // type:attached tag:v_locked line:51
  requires Heap[Heap[Current, HS_SET^HS_KEY^.lock], owns][v]; // type:pre tag:v_locked line:51
  requires is_wrapped(Heap, Heap[Current, HS_SET^HS_KEY^.lock]); // type:pre tag:lock_wrapped line:52
  requires Heap[Heap[Current, HS_SET^HS_KEY^.lock], HS_LOCK^HS_KEY^.sets][Current]; // type:pre tag:set_registered line:53
  ensures pre.fun.HS_SET^HS_KEY^.set_has(Heap, Current, v); // type:check tag:function_precondition line:69 cid:405 rid:5420
  ensures fun.HS_SET^HS_KEY^.set_has(Heap, Current, v); // type:post tag:abstract_effect line:69
  ensures pre.fun.HS_SET^HS_KEY^.set_has(old(Heap), Current, v); // type:check tag:function_precondition line:70 cid:405 rid:5420
  ensures (fun.HS_SET^HS_KEY^.set_has(old(Heap), Current, v)) ==> (Set#Equal(Heap[Current, HS_SET^HS_KEY^.set], old(Heap)[Current, HS_SET^HS_KEY^.set])); // type:post tag:precise_effect_has line:70
  ensures (!(fun.HS_SET^HS_KEY^.set_has(old(Heap), Current, v))) ==> (Set#Equal(Heap[Current, HS_SET^HS_KEY^.set], Set#Extended(old(Heap)[Current, HS_SET^HS_KEY^.set], v))); // type:post tag:precise_effect_new line:71
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.HS_SET^HS_KEY^.extend(Heap, Current, v), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.HS_SET^HS_KEY^.extend(old(Heap), Current, v));
  free ensures HeapSucc(old(Heap), Heap);
  requires is_wrapped(Heap, Current); // type:pre tag:default_is_wrapped default:contracts
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts



const HS_SET^HS_KEY^.set: Field (Set (ref));

axiom ((FieldId(HS_SET^HS_KEY^.set, HS_SET^HS_KEY^)) == (88));

axiom ((forall heap: HeapType, o: ref :: { heap[o, HS_SET^HS_KEY^.set] } ((IsHeap(heap)) && (attached(heap, o, HS_SET^HS_KEY^))) ==> (Set#ItemsType(heap, heap[o, HS_SET^HS_KEY^.set], HS_KEY))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, HS_SET^HS_KEY^.set, v, o) } (attached_exact(heap, current, HS_SET^HS_KEY^)) ==> ((guard(heap, current, HS_SET^HS_KEY^.set, v, o)) <==> ((user_inv(heap, o)) ==> (user_inv(heap[current, HS_SET^HS_KEY^.set := v], o))))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, HS_SET^HS_KEY^.set, v, o) } (attached(heap, current, HS_SET^HS_KEY^)) ==> ((guard(heap, current, HS_SET^HS_KEY^.set, v, o)) ==> ((user_inv(heap, o)) ==> (user_inv(heap[current, HS_SET^HS_KEY^.set := v], o))))));

procedure HS_SET^HS_KEY^.set_has(Current: ref, v: ref) returns (Result: bool where true);
  free requires attached_exact(Heap, Current, HS_SET^HS_KEY^); // info:type property for argument Current
  free requires detachable(Heap, v, HS_KEY); // info:type property for argument v
  modifies Heap;
  requires (v) != (Void); // type:pre tag:v_exists line:244
  requires Set#NonNull(Heap[Current, HS_SET^HS_KEY^.set]); // type:pre tag:set_non_void line:245
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.HS_SET^HS_KEY^.set_has(Heap, Current, v), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.HS_SET^HS_KEY^.set_has(old(Heap), Current, v));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.HS_SET^HS_KEY^.set_has(Heap, Current, v), readable);



function fun.HS_SET^HS_KEY^.set_has(heap: HeapType, current: ref, v: ref) returns (bool);

function fun0.HS_SET^HS_KEY^.set_has(heap: HeapType, current: ref, v: ref) returns (bool);

axiom ((forall heap: HeapType, current: ref, v: ref :: { fun.HS_SET^HS_KEY^.set_has(heap, current, v) } { trigger.fun.HS_SET^HS_KEY^.set_has(heap, current, v) } (pre.fun.HS_SET^HS_KEY^.set_has(heap, current, v)) ==> ((fun.HS_SET^HS_KEY^.set_has(heap, current, v)) == ((exists i_197: ref :: (heap[current, HS_SET^HS_KEY^.set][i_197]) && (fun.HS_KEY.is_model_equal(heap, v, i_197)))))));

axiom ((forall heap: HeapType, current: ref, v: ref :: { fun.HS_SET^HS_KEY^.set_has(heap, current, v) } (fun.HS_SET^HS_KEY^.set_has(heap, current, v)) == (fun0.HS_SET^HS_KEY^.set_has(heap, current, v))));

axiom ((forall h: HeapType, h': HeapType, current: ref, v: ref :: { HeapSucc(h, h'), fun0.HS_SET^HS_KEY^.set_has(h, current, v), fun0.HS_SET^HS_KEY^.set_has(h', current, v) } ((HeapSucc(h, h')) && (pre.fun.HS_SET^HS_KEY^.set_has(h, current, v)) && (pre.fun.HS_SET^HS_KEY^.set_has(h', current, v)) && (same_inside(h, h', read.fun.HS_SET^HS_KEY^.set_has(h, current, v)))) ==> ((fun0.HS_SET^HS_KEY^.set_has(h, current, v)) == (fun0.HS_SET^HS_KEY^.set_has(h', current, v)))));

procedure HS_SET^HS_KEY^.join(Current: ref, other: ref);
  free requires attached_exact(Heap, Current, HS_SET^HS_KEY^); // info:type property for argument Current
  free requires detachable(Heap, other, HS_SET^HS_KEY^); // info:type property for argument other
  modifies Heap;
  requires (Heap[Current, HS_SET^HS_KEY^.lock]) != (Void); // type:attached tag:lock_wrapped line:80
  requires is_wrapped(Heap, Heap[Current, HS_SET^HS_KEY^.lock]); // type:pre tag:lock_wrapped line:80
  requires Heap[Heap[Current, HS_SET^HS_KEY^.lock], HS_LOCK^HS_KEY^.sets][Current]; // type:pre tag:set_registered line:81
  requires Heap[Heap[Current, HS_SET^HS_KEY^.lock], HS_LOCK^HS_KEY^.sets][other]; // type:pre tag:other_registered line:82
  ensures Set#Subset(old(Heap)[Current, HS_SET^HS_KEY^.set], Heap[Current, HS_SET^HS_KEY^.set]); // type:post tag:has_old line:128
  ensures (other) != (Void); // type:attached tag:has_other line:129
  ensures (forall i_198: ref :: (old(Heap)[other, HS_SET^HS_KEY^.set][i_198]) ==> (((i_198) != (Void)) ==> (pre.fun.HS_SET^HS_KEY^.set_has(Heap, Current, i_198)))); // type:check tag:function_precondition line:129 cid:405 rid:5420
  ensures (forall i_198: ref :: (old(Heap)[other, HS_SET^HS_KEY^.set][i_198]) ==> (((i_198) != (Void)) && (fun.HS_SET^HS_KEY^.set_has(Heap, Current, i_198)))); // type:post tag:has_other line:129
  ensures (forall i_199: ref :: (Heap[Current, HS_SET^HS_KEY^.set][i_199]) ==> (pre.fun.HS_SET^HS_KEY^.set_has(old(Heap), Current, i_199))); // type:check tag:function_precondition line:130 cid:405 rid:5420
  ensures (forall i_199: ref :: (Heap[Current, HS_SET^HS_KEY^.set][i_199]) ==> (pre.fun.HS_SET^HS_KEY^.set_has(old(Heap), other, i_199))); // type:check tag:function_precondition line:130 cid:405 rid:5420
  ensures (forall i_199: ref :: (Heap[Current, HS_SET^HS_KEY^.set][i_199]) ==> ((fun.HS_SET^HS_KEY^.set_has(old(Heap), Current, i_199)) || (fun.HS_SET^HS_KEY^.set_has(old(Heap), other, i_199)))); // type:post tag:no_extra line:130
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.HS_SET^HS_KEY^.join(Heap, Current, other), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.HS_SET^HS_KEY^.join(old(Heap), Current, other));
  free ensures HeapSucc(old(Heap), Heap);
  requires is_wrapped(Heap, Current); // type:pre tag:default_is_wrapped default:contracts
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts
  requires is_wrapped(Heap, other); // type:pre tag:arg_other_is_wrapped default:contracts
  ensures is_wrapped(Heap, other); // type:post tag:arg_other_is_wrapped default:contracts



procedure HS_SET^HS_KEY^.wipe_out(Current: ref);
  free requires attached_exact(Heap, Current, HS_SET^HS_KEY^); // info:type property for argument Current
  modifies Heap;
  requires (Heap[Current, HS_SET^HS_KEY^.lock]) != (Void); // type:attached tag:lock_wrapped line:165
  requires is_wrapped(Heap, Heap[Current, HS_SET^HS_KEY^.lock]); // type:pre tag:lock_wrapped line:165
  requires Heap[Heap[Current, HS_SET^HS_KEY^.lock], HS_LOCK^HS_KEY^.sets][Current]; // type:pre tag:set_registered line:166
  ensures Set#IsEmpty(Heap[Current, HS_SET^HS_KEY^.set]); // type:post tag:set_empty line:172
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.HS_SET^HS_KEY^.wipe_out(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.HS_SET^HS_KEY^.wipe_out(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);
  requires is_wrapped(Heap, Current); // type:pre tag:default_is_wrapped default:contracts
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts



procedure HS_LOCK^HS_KEY^.unlock(Current: ref, item: ref);
  free requires attached_exact(Heap, Current, HS_LOCK^HS_KEY^); // info:type property for argument Current
  free requires detachable(Heap, item, HS_KEY); // info:type property for argument item
  modifies Heap;
  requires is_wrapped(Heap, Current); // type:pre tag:wrapped line:64
  requires Heap[Current, owns][item]; // type:pre tag:item_locked line:65
  requires (forall i_200: ref :: (Heap[Current, HS_LOCK^HS_KEY^.sets][i_200]) ==> (!(Heap[i_200, HS_SET^HS_KEY^.set][item]))); // type:pre tag:not_in_set line:66
  ensures Set#Equal(Heap[Current, owns], Set#Removed(old(Heap)[Current, owns], item)); // type:post tag:owns_effect line:74
  ensures (item) != (Void); // type:attached tag:item_wrapped line:75
  ensures is_wrapped(Heap, item); // type:post tag:item_wrapped line:75
  ensures is_wrapped(Heap, Current); // type:post tag:wrapped line:76
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.HS_LOCK^HS_KEY^.unlock(Heap, Current, item), writable); // type:pre tag:frame_writable
  free ensures flat_same_outside(old(Heap), Heap, modify.HS_LOCK^HS_KEY^.unlock(old(Heap), Current, item));
  free ensures HeapSucc(old(Heap), Heap);



function modify.HS_CLIENT.test_modification(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T24> $o: ref, $f: Field T24 :: { modify.HS_CLIENT.test_modification(heap, current)[$o, $f] } (modify.HS_CLIENT.test_modification(heap, current)[$o, $f]) <==> (($o) == (current))))));

const HS_LOCK^HS_KEY^.sets: Field (Set (ref));

axiom ((FieldId(HS_LOCK^HS_KEY^.sets, HS_LOCK^HS_KEY^)) == (80));

axiom ((forall heap: HeapType, o: ref :: { heap[o, HS_LOCK^HS_KEY^.sets] } ((IsHeap(heap)) && (attached(heap, o, HS_LOCK^HS_KEY^))) ==> (Set#ItemsType(heap, heap[o, HS_LOCK^HS_KEY^.sets], HS_SET^HS_KEY^))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, HS_LOCK^HS_KEY^.sets, v, o) } (attached_exact(heap, current, HS_LOCK^HS_KEY^)) ==> ((guard(heap, current, HS_LOCK^HS_KEY^.sets, v, o)) <==> (false))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, HS_LOCK^HS_KEY^.sets, v, o) } (attached(heap, current, HS_LOCK^HS_KEY^)) ==> ((guard(heap, current, HS_LOCK^HS_KEY^.sets, v, o)) ==> (false))));

const HS_SET^HS_KEY^.lock: Field (ref);

axiom ((FieldId(HS_SET^HS_KEY^.lock, HS_SET^HS_KEY^)) == (90));

axiom ((forall heap: HeapType, o: ref :: { heap[o, HS_SET^HS_KEY^.lock] } ((IsHeap(heap)) && (attached(heap, o, HS_SET^HS_KEY^))) ==> (detachable_exact(heap, heap[o, HS_SET^HS_KEY^.lock], HS_LOCK^HS_KEY^))));

axiom ((forall heap: HeapType, current: ref, v: ref, o: ref :: { guard(heap, current, HS_SET^HS_KEY^.lock, v, o) } (attached_exact(heap, current, HS_SET^HS_KEY^)) ==> ((guard(heap, current, HS_SET^HS_KEY^.lock, v, o)) <==> (false))));

axiom ((forall heap: HeapType, current: ref, v: ref, o: ref :: { guard(heap, current, HS_SET^HS_KEY^.lock, v, o) } (attached(heap, current, HS_SET^HS_KEY^)) ==> ((guard(heap, current, HS_SET^HS_KEY^.lock, v, o)) ==> (false))));

const HS_SET^HS_KEY^.buckets: Field (Seq (Seq (ref)));

axiom ((FieldId(HS_SET^HS_KEY^.buckets, HS_SET^HS_KEY^)) == (89));

axiom ((forall heap: HeapType, current: ref, v: Seq (Seq (ref)), o: ref :: { guard(heap, current, HS_SET^HS_KEY^.buckets, v, o) } (attached_exact(heap, current, HS_SET^HS_KEY^)) ==> ((guard(heap, current, HS_SET^HS_KEY^.buckets, v, o)) <==> ((user_inv(heap, o)) ==> (user_inv(heap[current, HS_SET^HS_KEY^.buckets := v], o))))));

axiom ((forall heap: HeapType, current: ref, v: Seq (Seq (ref)), o: ref :: { guard(heap, current, HS_SET^HS_KEY^.buckets, v, o) } (attached(heap, current, HS_SET^HS_KEY^)) ==> ((guard(heap, current, HS_SET^HS_KEY^.buckets, v, o)) ==> ((user_inv(heap, o)) ==> (user_inv(heap[current, HS_SET^HS_KEY^.buckets := v], o))))));

procedure HS_SET^HS_KEY^.bucket_index(Current: ref, hc: int, n: int) returns (Result: int where is_integer_32(Result));
  free requires attached_exact(Heap, Current, HS_SET^HS_KEY^); // info:type property for argument Current
  free requires is_integer_32(hc); // info:type property for argument hc
  free requires is_integer_32(n); // info:type property for argument n
  modifies Heap;
  requires (n) > (0); // type:pre tag:n_positive line:184
  requires (0) <= (hc); // type:pre tag:hc_non_negative line:185
  ensures ((1) <= (Result)) && ((Result) <= (n)); // type:post tag:in_bounds line:189
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.HS_SET^HS_KEY^.bucket_index(Heap, Current, hc, n), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.HS_SET^HS_KEY^.bucket_index(old(Heap), Current, hc, n));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.HS_SET^HS_KEY^.bucket_index(Heap, Current, hc, n), readable);
  free ensures (Result) == (fun.HS_SET^HS_KEY^.bucket_index(old(Heap), Current, hc, n));



function fun.HS_SET^HS_KEY^.bucket_index(heap: HeapType, current: ref, hc: int, n: int) returns (int);

axiom ((forall heap: HeapType, current: ref, hc: int, n: int :: { fun.HS_SET^HS_KEY^.bucket_index(heap, current, hc, n) } (pre.fun.HS_SET^HS_KEY^.bucket_index(heap, current, hc, n)) ==> (((1) <= (fun.HS_SET^HS_KEY^.bucket_index(heap, current, hc, n))) && ((fun.HS_SET^HS_KEY^.bucket_index(heap, current, hc, n)) <= (n)) && (is_integer_32(fun.HS_SET^HS_KEY^.bucket_index(heap, current, hc, n))))));

axiom ((forall h: HeapType, h': HeapType, current: ref, hc: int, n: int :: { HeapSucc(h, h'), fun.HS_SET^HS_KEY^.bucket_index(h, current, hc, n), fun.HS_SET^HS_KEY^.bucket_index(h', current, hc, n) } ((HeapSucc(h, h')) && (pre.fun.HS_SET^HS_KEY^.bucket_index(h, current, hc, n)) && (pre.fun.HS_SET^HS_KEY^.bucket_index(h', current, hc, n)) && (same_inside(h, h', read.fun.HS_SET^HS_KEY^.bucket_index(h, current, hc, n)))) ==> ((fun.HS_SET^HS_KEY^.bucket_index(h, current, hc, n)) == (fun.HS_SET^HS_KEY^.bucket_index(h', current, hc, n)))));

function modify.HS_CLIENT.test_modification_fail(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T25> $o: ref, $f: Field T25 :: { modify.HS_CLIENT.test_modification_fail(heap, current)[$o, $f] } (modify.HS_CLIENT.test_modification_fail(heap, current)[$o, $f]) <==> (($o) == (current))))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, owns, v, o) } (attached_exact(heap, current, HS_KEY)) ==> ((guard(heap, current, owns, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, subjects, v, o) } (attached_exact(heap, current, HS_KEY)) ==> ((guard(heap, current, subjects, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached_exact(heap, current, HS_KEY)) ==> ((guard(heap, current, observers, v, o)) <==> (fun.HS_KEY.in_observers(heap, current, v, o)))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached(heap, current, HS_KEY)) ==> ((guard(heap, current, observers, v, o)) ==> (fun.HS_KEY.in_observers(heap, current, v, o)))));

function modify.HS_KEY.hash_code(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T26> $o: ref, $f: Field T26 :: { modify.HS_KEY.hash_code(heap, current)[$o, $f] } (modify.HS_KEY.hash_code(heap, current)[$o, $f]) <==> (false)))));

function read.fun.HS_KEY.hash_code(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T27> $o: ref, $f: Field T27 :: { read.fun.HS_KEY.hash_code(heap, current)[$o, $f] } (read.fun.HS_KEY.hash_code(heap, current)[$o, $f]) <==> (((domain(heap, current)[$o]) || (heap[current, subjects][$o])) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.HS_KEY.hash_code(heap: HeapType, current: ref) returns (bool) {
  (is_closed(heap, current)) && (is_closed(heap, current))
}

function trigger.fun.HS_KEY.hash_code(heap: HeapType, current: ref) returns (bool);

function modify.HS_KEY.set_value(heap: HeapType, current: ref, v: int) returns (Frame);

axiom ((forall heap: HeapType, current: ref, v: int :: (IsHeap(heap)) ==> ((forall <T28> $o: ref, $f: Field T28 :: { modify.HS_KEY.set_value(heap, current, v)[$o, $f] } (modify.HS_KEY.set_value(heap, current, v)[$o, $f]) <==> (($o) == (current))))));

function modify.HS_KEY.hash_code_(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T29> $o: ref, $f: Field T29 :: { modify.HS_KEY.hash_code_(heap, current)[$o, $f] } (modify.HS_KEY.hash_code_(heap, current)[$o, $f]) <==> (false)))));

function read.fun.HS_KEY.hash_code_(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T30> $o: ref, $f: Field T30 :: { read.fun.HS_KEY.hash_code_(heap, current)[$o, $f] } (read.fun.HS_KEY.hash_code_(heap, current)[$o, $f]) <==> ((($o) == (current)) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.HS_KEY.hash_code_(heap: HeapType, current: ref) returns (bool) {
  true
}

function trigger.fun.HS_KEY.hash_code_(heap: HeapType, current: ref) returns (bool);

function modify.HS_KEY.is_model_equal(heap: HeapType, current: ref, other: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, other: ref :: (IsHeap(heap)) ==> ((forall <T31> $o: ref, $f: Field T31 :: { modify.HS_KEY.is_model_equal(heap, current, other)[$o, $f] } (modify.HS_KEY.is_model_equal(heap, current, other)[$o, $f]) <==> (false)))));

function read.fun.HS_KEY.is_model_equal(heap: HeapType, current: ref, other: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, other: ref :: (IsHeap(heap)) ==> ((forall <T32> $o: ref, $f: Field T32 :: { read.fun.HS_KEY.is_model_equal(heap, current, other)[$o, $f] } (read.fun.HS_KEY.is_model_equal(heap, current, other)[$o, $f]) <==> (((($o) == (current)) || (($o) == (other))) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.HS_KEY.is_model_equal(heap: HeapType, current: ref, other: ref) returns (bool) {
  (other) != (Void)
}

function trigger.fun.HS_KEY.is_model_equal(heap: HeapType, current: ref, other: ref) returns (bool);

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, owns, v, o) } (attached_exact(heap, current, HS_HASHABLE)) ==> ((guard(heap, current, owns, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, subjects, v, o) } (attached_exact(heap, current, HS_HASHABLE)) ==> ((guard(heap, current, subjects, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached_exact(heap, current, HS_HASHABLE)) ==> ((guard(heap, current, observers, v, o)) <==> (fun.HS_HASHABLE.in_observers(heap, current, v, o)))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached(heap, current, HS_HASHABLE)) ==> ((guard(heap, current, observers, v, o)) ==> (fun.HS_HASHABLE.in_observers(heap, current, v, o)))));

function modify.HS_HASHABLE.hash_code(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T33> $o: ref, $f: Field T33 :: { modify.HS_HASHABLE.hash_code(heap, current)[$o, $f] } (modify.HS_HASHABLE.hash_code(heap, current)[$o, $f]) <==> (false)))));

function read.fun.HS_HASHABLE.hash_code(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T34> $o: ref, $f: Field T34 :: { read.fun.HS_HASHABLE.hash_code(heap, current)[$o, $f] } (read.fun.HS_HASHABLE.hash_code(heap, current)[$o, $f]) <==> (((domain(heap, current)[$o]) || (heap[current, subjects][$o])) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.HS_HASHABLE.hash_code(heap: HeapType, current: ref) returns (bool) {
  (is_closed(heap, current)) && (is_closed(heap, current))
}

function trigger.fun.HS_HASHABLE.hash_code(heap: HeapType, current: ref) returns (bool);

function modify.HS_HASHABLE.hash_code_(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T35> $o: ref, $f: Field T35 :: { modify.HS_HASHABLE.hash_code_(heap, current)[$o, $f] } (modify.HS_HASHABLE.hash_code_(heap, current)[$o, $f]) <==> (false)))));

function read.fun.HS_HASHABLE.hash_code_(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T36> $o: ref, $f: Field T36 :: { read.fun.HS_HASHABLE.hash_code_(heap, current)[$o, $f] } (read.fun.HS_HASHABLE.hash_code_(heap, current)[$o, $f]) <==> ((($o) == (current)) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.HS_HASHABLE.hash_code_(heap: HeapType, current: ref) returns (bool) {
  true
}

function trigger.fun.HS_HASHABLE.hash_code_(heap: HeapType, current: ref) returns (bool);

function modify.HS_HASHABLE.is_model_equal(heap: HeapType, current: ref, other: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, other: ref :: (IsHeap(heap)) ==> ((forall <T37> $o: ref, $f: Field T37 :: { modify.HS_HASHABLE.is_model_equal(heap, current, other)[$o, $f] } (modify.HS_HASHABLE.is_model_equal(heap, current, other)[$o, $f]) <==> (false)))));

function read.fun.HS_HASHABLE.is_model_equal(heap: HeapType, current: ref, other: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, other: ref :: (IsHeap(heap)) ==> ((forall <T38> $o: ref, $f: Field T38 :: { read.fun.HS_HASHABLE.is_model_equal(heap, current, other)[$o, $f] } (read.fun.HS_HASHABLE.is_model_equal(heap, current, other)[$o, $f]) <==> (((($o) == (current)) || (($o) == (other))) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.HS_HASHABLE.is_model_equal(heap: HeapType, current: ref, other: ref) returns (bool) {
  (other) != (Void)
}

function trigger.fun.HS_HASHABLE.is_model_equal(heap: HeapType, current: ref, other: ref) returns (bool);

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, owns, v, o) } (attached_exact(heap, current, HS_SET^HS_HASHABLE^)) ==> ((guard(heap, current, owns, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, subjects, v, o) } (attached_exact(heap, current, HS_SET^HS_HASHABLE^)) ==> ((guard(heap, current, subjects, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached_exact(heap, current, HS_SET^HS_HASHABLE^)) ==> ((guard(heap, current, observers, v, o)) <==> (fun.HS_SET^HS_HASHABLE^.in_observers(heap, current, v, o)))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached(heap, current, HS_SET^HS_HASHABLE^)) ==> ((guard(heap, current, observers, v, o)) ==> (fun.HS_SET^HS_HASHABLE^.in_observers(heap, current, v, o)))));

function modify.HS_SET^HS_HASHABLE^.make(heap: HeapType, current: ref, l: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, l: ref :: (IsHeap(heap)) ==> ((forall <T39> $o: ref, $f: Field T39 :: { modify.HS_SET^HS_HASHABLE^.make(heap, current, l)[$o, $f] } (modify.HS_SET^HS_HASHABLE^.make(heap, current, l)[$o, $f]) <==> (($o) == (current))))));

function modify.HS_SET^HS_HASHABLE^.has(heap: HeapType, current: ref, v: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, v: ref :: (IsHeap(heap)) ==> ((forall <T40> $o: ref, $f: Field T40 :: { modify.HS_SET^HS_HASHABLE^.has(heap, current, v)[$o, $f] } (modify.HS_SET^HS_HASHABLE^.has(heap, current, v)[$o, $f]) <==> (false)))));

function read.fun.HS_SET^HS_HASHABLE^.has(heap: HeapType, current: ref, v: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, v: ref :: (IsHeap(heap)) ==> ((forall <T41> $o: ref, $f: Field T41 :: { read.fun.HS_SET^HS_HASHABLE^.has(heap, current, v)[$o, $f] } (read.fun.HS_SET^HS_HASHABLE^.has(heap, current, v)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.HS_SET^HS_HASHABLE^.has(heap: HeapType, current: ref, v: ref) returns (bool) {
  (is_closed(heap, v)) && (is_wrapped(heap, heap[current, HS_SET^HS_HASHABLE^.lock])) && (heap[heap[current, HS_SET^HS_HASHABLE^.lock], HS_LOCK^HS_HASHABLE^.sets][current]) && (is_closed(heap, current))
}

function trigger.fun.HS_SET^HS_HASHABLE^.has(heap: HeapType, current: ref, v: ref) returns (bool);

function HS_LOCK^HS_HASHABLE^#I#owns_items#valid_buckets.filtered_inv(heap: HeapType, current: ref) returns (bool) {
  ((forall i_201: ref :: (heap[current, HS_LOCK^HS_HASHABLE^.sets][i_201]) ==> ((forall i_202: ref :: (heap[i_201, HS_SET^HS_HASHABLE^.set][i_202]) ==> (heap[current, owns][i_202]))))) && ((forall i_203: ref :: (heap[current, HS_LOCK^HS_HASHABLE^.sets][i_203]) ==> ((forall i_204: ref :: (heap[i_203, HS_SET^HS_HASHABLE^.set][i_204]) ==> (((Seq#Length(heap[i_203, HS_SET^HS_HASHABLE^.buckets])) > (0)) && (Seq#Has(Seq#Item(heap[i_203, HS_SET^HS_HASHABLE^.buckets], fun.HS_SET^HS_HASHABLE^.bucket_index(heap, i_203, fun.HS_HASHABLE.hash_code_(heap, i_204), Seq#Length(heap[i_203, HS_SET^HS_HASHABLE^.buckets]))), i_204)))))))
}

axiom ((forall h: HeapType, o: ref :: { HS_LOCK^HS_HASHABLE^#I#owns_items#valid_buckets.filtered_inv(h, o) } ((IsHeap(h)) && (attached(h, o, HS_LOCK^HS_HASHABLE^)) && (h[o, closed])) ==> (HS_LOCK^HS_HASHABLE^#I#owns_items#valid_buckets.filtered_inv(h, o))));

function modify.HS_SET^HS_HASHABLE^.extend(heap: HeapType, current: ref, v: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, v: ref :: (IsHeap(heap)) ==> ((forall <T42> $o: ref, $f: Field T42 :: { modify.HS_SET^HS_HASHABLE^.extend(heap, current, v)[$o, $f] } (modify.HS_SET^HS_HASHABLE^.extend(heap, current, v)[$o, $f]) <==> ((($o) == (current)) && ((!(IsModelField($f, HS_SET^HS_HASHABLE^))) || (($f) == (HS_SET^HS_HASHABLE^.set))))))));

function modify.HS_SET^HS_HASHABLE^.join(heap: HeapType, current: ref, other: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, other: ref :: (IsHeap(heap)) ==> ((forall <T43> $o: ref, $f: Field T43 :: { modify.HS_SET^HS_HASHABLE^.join(heap, current, other)[$o, $f] } (modify.HS_SET^HS_HASHABLE^.join(heap, current, other)[$o, $f]) <==> ((($o) == (current)) && ((!(IsModelField($f, HS_SET^HS_HASHABLE^))) || (($f) == (HS_SET^HS_HASHABLE^.set))))))));

function HS_SET^HS_HASHABLE^#I#set_non_void.filtered_inv(heap: HeapType, current: ref) returns (bool) {
  Set#NonNull(heap[current, HS_SET^HS_HASHABLE^.set])
}

axiom ((forall h: HeapType, o: ref :: { HS_SET^HS_HASHABLE^#I#set_non_void.filtered_inv(h, o) } ((IsHeap(h)) && (attached(h, o, HS_SET^HS_HASHABLE^)) && (h[o, closed])) ==> (HS_SET^HS_HASHABLE^#I#set_non_void.filtered_inv(h, o))));

function HS_LOCK^HS_HASHABLE^#I#owns_items.filtered_inv(heap: HeapType, current: ref) returns (bool) {
  (forall i_205: ref :: (heap[current, HS_LOCK^HS_HASHABLE^.sets][i_205]) ==> ((forall i_206: ref :: (heap[i_205, HS_SET^HS_HASHABLE^.set][i_206]) ==> (heap[current, owns][i_206]))))
}

axiom ((forall h: HeapType, o: ref :: { HS_LOCK^HS_HASHABLE^#I#owns_items.filtered_inv(h, o) } ((IsHeap(h)) && (attached(h, o, HS_LOCK^HS_HASHABLE^)) && (h[o, closed])) ==> (HS_LOCK^HS_HASHABLE^#I#owns_items.filtered_inv(h, o))));

function HS_LOCK^HS_HASHABLE^#I#valid_buckets.filtered_inv(heap: HeapType, current: ref) returns (bool) {
  (forall i_207: ref :: (heap[current, HS_LOCK^HS_HASHABLE^.sets][i_207]) ==> ((forall i_208: ref :: (heap[i_207, HS_SET^HS_HASHABLE^.set][i_208]) ==> (((Seq#Length(heap[i_207, HS_SET^HS_HASHABLE^.buckets])) > (0)) && (Seq#Has(Seq#Item(heap[i_207, HS_SET^HS_HASHABLE^.buckets], fun.HS_SET^HS_HASHABLE^.bucket_index(heap, i_207, fun.HS_HASHABLE.hash_code_(heap, i_208), Seq#Length(heap[i_207, HS_SET^HS_HASHABLE^.buckets]))), i_208))))))
}

axiom ((forall h: HeapType, o: ref :: { HS_LOCK^HS_HASHABLE^#I#valid_buckets.filtered_inv(h, o) } ((IsHeap(h)) && (attached(h, o, HS_LOCK^HS_HASHABLE^)) && (h[o, closed])) ==> (HS_LOCK^HS_HASHABLE^#I#valid_buckets.filtered_inv(h, o))));

function modify.HS_SET^HS_HASHABLE^.remove(heap: HeapType, current: ref, v: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, v: ref :: (IsHeap(heap)) ==> ((forall <T44> $o: ref, $f: Field T44 :: { modify.HS_SET^HS_HASHABLE^.remove(heap, current, v)[$o, $f] } (modify.HS_SET^HS_HASHABLE^.remove(heap, current, v)[$o, $f]) <==> ((($o) == (current)) && ((!(IsModelField($f, HS_SET^HS_HASHABLE^))) || (($f) == (HS_SET^HS_HASHABLE^.set))))))));

function HS_LOCK^HS_HASHABLE^#I#owns_items#valid_buckets#no_duplicates.filtered_inv(heap: HeapType, current: ref) returns (bool) {
  ((forall i_209: ref :: (heap[current, HS_LOCK^HS_HASHABLE^.sets][i_209]) ==> ((forall i_210: ref :: (heap[i_209, HS_SET^HS_HASHABLE^.set][i_210]) ==> (heap[current, owns][i_210]))))) && ((forall i_211: ref :: (heap[current, HS_LOCK^HS_HASHABLE^.sets][i_211]) ==> ((forall i_212: ref :: (heap[i_211, HS_SET^HS_HASHABLE^.set][i_212]) ==> (((Seq#Length(heap[i_211, HS_SET^HS_HASHABLE^.buckets])) > (0)) && (Seq#Has(Seq#Item(heap[i_211, HS_SET^HS_HASHABLE^.buckets], fun.HS_SET^HS_HASHABLE^.bucket_index(heap, i_211, fun.HS_HASHABLE.hash_code_(heap, i_212), Seq#Length(heap[i_211, HS_SET^HS_HASHABLE^.buckets]))), i_212))))))) && ((forall i_213: ref :: (heap[current, HS_LOCK^HS_HASHABLE^.sets][i_213]) ==> ((forall i_214: ref :: (heap[i_213, HS_SET^HS_HASHABLE^.set][i_214]) ==> ((forall i_215: ref :: (heap[i_213, HS_SET^HS_HASHABLE^.set][i_215]) ==> (((i_214) != (Void)) && ((i_215) != (Void)) && (((i_214) != (i_215)) ==> (!(fun.HS_HASHABLE.is_model_equal(heap, i_214, i_215)))))))))))
}

axiom ((forall h: HeapType, o: ref :: { HS_LOCK^HS_HASHABLE^#I#owns_items#valid_buckets#no_duplicates.filtered_inv(h, o) } ((IsHeap(h)) && (attached(h, o, HS_LOCK^HS_HASHABLE^)) && (h[o, closed])) ==> (HS_LOCK^HS_HASHABLE^#I#owns_items#valid_buckets#no_duplicates.filtered_inv(h, o))));

procedure HS_HASHABLE.lemma_transitive(Current: ref, x: ref, ys: Set (ref));
  free requires attached_exact(Heap, Current, HS_HASHABLE); // info:type property for argument Current
  free requires detachable(Heap, x, HS_HASHABLE); // info:type property for argument x
  free requires Set#ItemsType(Heap, ys, ANY); // info:type property for argument ys
  requires pre.fun.HS_HASHABLE.is_model_equal(Heap, Current, x); // type:check tag:function_precondition line:689 cid:406 rid:81
  requires fun.HS_HASHABLE.is_model_equal(Heap, Current, x); // type:pre tag:equal_x line:689
  requires Set#NonNull(ys); // type:pre tag:ys_exist line:690
  ensures (forall i_216: ref :: (ys[i_216]) ==> (pre.fun.HS_HASHABLE.is_model_equal(Heap, Current, i_216))); // type:check tag:function_precondition line:693 cid:406 rid:81
  ensures (x) != (Void); // type:attached tag:x_in_ys_iff_current_in_ys line:693
  ensures (forall i_217: ref :: (ys[i_217]) ==> (pre.fun.HS_HASHABLE.is_model_equal(Heap, x, i_217))); // type:check tag:function_precondition line:693 cid:406 rid:81
  ensures ((exists i_216: ref :: (ys[i_216]) && (fun.HS_HASHABLE.is_model_equal(Heap, Current, i_216)))) == ((exists i_217: ref :: (ys[i_217]) && (fun.HS_HASHABLE.is_model_equal(Heap, x, i_217)))); // type:post tag:x_in_ys_iff_current_in_ys line:693
  free requires global(Heap);
  free requires global_permissive();



function modify.HS_SET^HS_HASHABLE^.wipe_out(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T45> $o: ref, $f: Field T45 :: { modify.HS_SET^HS_HASHABLE^.wipe_out(heap, current)[$o, $f] } (modify.HS_SET^HS_HASHABLE^.wipe_out(heap, current)[$o, $f]) <==> ((($o) == (current)) && ((!(IsModelField($f, HS_SET^HS_HASHABLE^))) || (($f) == (HS_SET^HS_HASHABLE^.set))))))));

function modify.HS_SET^HS_HASHABLE^.bucket_index(heap: HeapType, current: ref, hc: int, n: int) returns (Frame);

axiom ((forall heap: HeapType, current: ref, hc: int, n: int :: (IsHeap(heap)) ==> ((forall <T46> $o: ref, $f: Field T46 :: { modify.HS_SET^HS_HASHABLE^.bucket_index(heap, current, hc, n)[$o, $f] } (modify.HS_SET^HS_HASHABLE^.bucket_index(heap, current, hc, n)[$o, $f]) <==> (false)))));

function read.fun.HS_SET^HS_HASHABLE^.bucket_index(heap: HeapType, current: ref, hc: int, n: int) returns (Frame);

axiom ((forall heap: HeapType, current: ref, hc: int, n: int :: (IsHeap(heap)) ==> ((forall <T47> $o: ref, $f: Field T47 :: { read.fun.HS_SET^HS_HASHABLE^.bucket_index(heap, current, hc, n)[$o, $f] } (read.fun.HS_SET^HS_HASHABLE^.bucket_index(heap, current, hc, n)[$o, $f]) <==> ((false) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.HS_SET^HS_HASHABLE^.bucket_index(heap: HeapType, current: ref, hc: int, n: int) returns (bool) {
  ((n) > (0)) && ((0) <= (hc))
}

function trigger.fun.HS_SET^HS_HASHABLE^.bucket_index(heap: HeapType, current: ref, hc: int, n: int) returns (bool);

function modify.HS_SET^HS_HASHABLE^.index_of(heap: HeapType, current: ref, b: Seq (ref), v: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, b: Seq (ref), v: ref :: (IsHeap(heap)) ==> ((forall <T48> $o: ref, $f: Field T48 :: { modify.HS_SET^HS_HASHABLE^.index_of(heap, current, b, v)[$o, $f] } (modify.HS_SET^HS_HASHABLE^.index_of(heap, current, b, v)[$o, $f]) <==> (false)))));

function read.fun.HS_SET^HS_HASHABLE^.index_of(heap: HeapType, current: ref, b: Seq (ref), v: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, b: Seq (ref), v: ref :: (IsHeap(heap)) ==> ((forall <T49> $o: ref, $f: Field T49 :: { read.fun.HS_SET^HS_HASHABLE^.index_of(heap, current, b, v)[$o, $f] } (read.fun.HS_SET^HS_HASHABLE^.index_of(heap, current, b, v)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.HS_SET^HS_HASHABLE^.index_of(heap: HeapType, current: ref, b: Seq (ref), v: ref) returns (bool) {
  (is_closed(heap, v)) && ((forall i_218: int :: (((1) <= (i_218)) && ((i_218) <= (Seq#Length(b)))) ==> (is_closed(heap, Seq#Item(b, i_218)))))
}

function trigger.fun.HS_SET^HS_HASHABLE^.index_of(heap: HeapType, current: ref, b: Seq (ref), v: ref) returns (bool);

function modify.HS_SET^HS_HASHABLE^.set_has(heap: HeapType, current: ref, v: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, v: ref :: (IsHeap(heap)) ==> ((forall <T50> $o: ref, $f: Field T50 :: { modify.HS_SET^HS_HASHABLE^.set_has(heap, current, v)[$o, $f] } (modify.HS_SET^HS_HASHABLE^.set_has(heap, current, v)[$o, $f]) <==> (false)))));

function read.fun.HS_SET^HS_HASHABLE^.set_has(heap: HeapType, current: ref, v: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, v: ref :: (IsHeap(heap)) ==> ((forall <T51> $o: ref, $f: Field T51 :: { read.fun.HS_SET^HS_HASHABLE^.set_has(heap, current, v)[$o, $f] } (read.fun.HS_SET^HS_HASHABLE^.set_has(heap, current, v)[$o, $f]) <==> (((($o) == (current)) || (heap[current, HS_SET^HS_HASHABLE^.set][$o]) || (($o) == (v))) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.HS_SET^HS_HASHABLE^.set_has(heap: HeapType, current: ref, v: ref) returns (bool) {
  ((v) != (Void)) && (Set#NonNull(heap[current, HS_SET^HS_HASHABLE^.set]))
}

function trigger.fun.HS_SET^HS_HASHABLE^.set_has(heap: HeapType, current: ref, v: ref) returns (bool);

function modify.HS_SET^HS_HASHABLE^.no_duplicates(heap: HeapType, current: ref, s: Set (ref)) returns (Frame);

axiom ((forall heap: HeapType, current: ref, s: Set (ref) :: (IsHeap(heap)) ==> ((forall <T52> $o: ref, $f: Field T52 :: { modify.HS_SET^HS_HASHABLE^.no_duplicates(heap, current, s)[$o, $f] } (modify.HS_SET^HS_HASHABLE^.no_duplicates(heap, current, s)[$o, $f]) <==> (false)))));

function read.fun.HS_SET^HS_HASHABLE^.no_duplicates(heap: HeapType, current: ref, s: Set (ref)) returns (Frame);

axiom ((forall heap: HeapType, current: ref, s: Set (ref) :: (IsHeap(heap)) ==> ((forall <T53> $o: ref, $f: Field T53 :: { read.fun.HS_SET^HS_HASHABLE^.no_duplicates(heap, current, s)[$o, $f] } (read.fun.HS_SET^HS_HASHABLE^.no_duplicates(heap, current, s)[$o, $f]) <==> ((s[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.HS_SET^HS_HASHABLE^.no_duplicates(heap: HeapType, current: ref, s: Set (ref)) returns (bool) {
  Set#NonNull(s)
}

function trigger.fun.HS_SET^HS_HASHABLE^.no_duplicates(heap: HeapType, current: ref, s: Set (ref)) returns (bool);

function pre.fun.MML_SEQUENCE^MML_SEQUENCE^HS_HASHABLE^^.item(current: Seq (Seq (ref)), i: int) returns (bool) {
  ((1) <= (i)) && ((i) <= (Seq#Length(current)))
}

function trigger.fun.MML_SEQUENCE^MML_SEQUENCE^HS_HASHABLE^^.item(current: Seq (Seq (ref)), i: int) returns (bool);

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

procedure HS_LOCK^HS_HASHABLE^.in_observers(Current: ref, new_observers: Set (ref), o: ref) returns (Result: bool where true);
  free requires attached_exact(Heap, Current, HS_LOCK^HS_HASHABLE^); // info:type property for argument Current
  free requires Set#ItemsType(Heap, new_observers, ANY); // info:type property for argument new_observers
  free requires Heap[o, allocated]; // info:type property for argument o
  modifies Heap;
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.HS_LOCK^HS_HASHABLE^.in_observers(Heap, Current, new_observers, o), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.HS_LOCK^HS_HASHABLE^.in_observers(old(Heap), Current, new_observers, o));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.HS_LOCK^HS_HASHABLE^.in_observers(Heap, Current, new_observers, o), readable);



function fun.HS_LOCK^HS_HASHABLE^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function fun0.HS_LOCK^HS_HASHABLE^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.HS_LOCK^HS_HASHABLE^.in_observers(heap, current, new_observers, o) } { trigger.fun.HS_LOCK^HS_HASHABLE^.in_observers(heap, current, new_observers, o) } (pre.fun.HS_LOCK^HS_HASHABLE^.in_observers(heap, current, new_observers, o)) ==> ((fun.HS_LOCK^HS_HASHABLE^.in_observers(heap, current, new_observers, o)) == (new_observers[o]))));

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.HS_LOCK^HS_HASHABLE^.in_observers(heap, current, new_observers, o) } (fun.HS_LOCK^HS_HASHABLE^.in_observers(heap, current, new_observers, o)) == (fun0.HS_LOCK^HS_HASHABLE^.in_observers(heap, current, new_observers, o))));

axiom ((forall h: HeapType, h': HeapType, current: ref, new_observers: Set (ref), o: ref :: { HeapSucc(h, h'), fun0.HS_LOCK^HS_HASHABLE^.in_observers(h, current, new_observers, o), fun0.HS_LOCK^HS_HASHABLE^.in_observers(h', current, new_observers, o) } ((HeapSucc(h, h')) && (pre.fun.HS_LOCK^HS_HASHABLE^.in_observers(h, current, new_observers, o)) && (pre.fun.HS_LOCK^HS_HASHABLE^.in_observers(h', current, new_observers, o)) && (same_inside(h, h', read.fun.HS_LOCK^HS_HASHABLE^.in_observers(h, current, new_observers, o)))) ==> ((fun0.HS_LOCK^HS_HASHABLE^.in_observers(h, current, new_observers, o)) == (fun0.HS_LOCK^HS_HASHABLE^.in_observers(h', current, new_observers, o)))));

procedure HS_CLIENT.in_observers(Current: ref, new_observers: Set (ref), o: ref) returns (Result: bool where true);
  free requires attached_exact(Heap, Current, HS_CLIENT); // info:type property for argument Current
  free requires Set#ItemsType(Heap, new_observers, ANY); // info:type property for argument new_observers
  free requires Heap[o, allocated]; // info:type property for argument o
  modifies Heap;
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.HS_CLIENT.in_observers(Heap, Current, new_observers, o), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.HS_CLIENT.in_observers(old(Heap), Current, new_observers, o));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.HS_CLIENT.in_observers(Heap, Current, new_observers, o), readable);



function fun.HS_CLIENT.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function fun0.HS_CLIENT.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.HS_CLIENT.in_observers(heap, current, new_observers, o) } { trigger.fun.HS_CLIENT.in_observers(heap, current, new_observers, o) } (pre.fun.HS_CLIENT.in_observers(heap, current, new_observers, o)) ==> ((fun.HS_CLIENT.in_observers(heap, current, new_observers, o)) == (new_observers[o]))));

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.HS_CLIENT.in_observers(heap, current, new_observers, o) } (fun.HS_CLIENT.in_observers(heap, current, new_observers, o)) == (fun0.HS_CLIENT.in_observers(heap, current, new_observers, o))));

axiom ((forall h: HeapType, h': HeapType, current: ref, new_observers: Set (ref), o: ref :: { HeapSucc(h, h'), fun0.HS_CLIENT.in_observers(h, current, new_observers, o), fun0.HS_CLIENT.in_observers(h', current, new_observers, o) } ((HeapSucc(h, h')) && (pre.fun.HS_CLIENT.in_observers(h, current, new_observers, o)) && (pre.fun.HS_CLIENT.in_observers(h', current, new_observers, o)) && (same_inside(h, h', read.fun.HS_CLIENT.in_observers(h, current, new_observers, o)))) ==> ((fun0.HS_CLIENT.in_observers(h, current, new_observers, o)) == (fun0.HS_CLIENT.in_observers(h', current, new_observers, o)))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, owns, v, o) } (attached_exact(heap, current, HS_LOCK^HS_KEY^)) ==> ((guard(heap, current, owns, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, subjects, v, o) } (attached_exact(heap, current, HS_LOCK^HS_KEY^)) ==> ((guard(heap, current, subjects, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached_exact(heap, current, HS_LOCK^HS_KEY^)) ==> ((guard(heap, current, observers, v, o)) <==> (fun.HS_LOCK^HS_KEY^.in_observers(heap, current, v, o)))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached(heap, current, HS_LOCK^HS_KEY^)) ==> ((guard(heap, current, observers, v, o)) ==> (fun.HS_LOCK^HS_KEY^.in_observers(heap, current, v, o)))));

function modify.HS_LOCK^HS_KEY^.default_create(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T54> $o: ref, $f: Field T54 :: { modify.HS_LOCK^HS_KEY^.default_create(heap, current)[$o, $f] } (modify.HS_LOCK^HS_KEY^.default_create(heap, current)[$o, $f]) <==> (($o) == (current))))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, owns, v, o) } (attached_exact(heap, current, HS_SET^HS_KEY^)) ==> ((guard(heap, current, owns, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, subjects, v, o) } (attached_exact(heap, current, HS_SET^HS_KEY^)) ==> ((guard(heap, current, subjects, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached_exact(heap, current, HS_SET^HS_KEY^)) ==> ((guard(heap, current, observers, v, o)) <==> (fun.HS_SET^HS_KEY^.in_observers(heap, current, v, o)))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached(heap, current, HS_SET^HS_KEY^)) ==> ((guard(heap, current, observers, v, o)) ==> (fun.HS_SET^HS_KEY^.in_observers(heap, current, v, o)))));

function modify.HS_SET^HS_KEY^.make(heap: HeapType, current: ref, l: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, l: ref :: (IsHeap(heap)) ==> ((forall <T55> $o: ref, $f: Field T55 :: { modify.HS_SET^HS_KEY^.make(heap, current, l)[$o, $f] } (modify.HS_SET^HS_KEY^.make(heap, current, l)[$o, $f]) <==> (($o) == (current))))));

function modify.HS_LOCK^HS_KEY^.add_set(heap: HeapType, current: ref, s: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, s: ref :: (IsHeap(heap)) ==> ((forall <T56> $o: ref, $f: Field T56 :: { modify.HS_LOCK^HS_KEY^.add_set(heap, current, s)[$o, $f] } (modify.HS_LOCK^HS_KEY^.add_set(heap, current, s)[$o, $f]) <==> (((($o) == (current)) && ((($f) == (HS_LOCK^HS_KEY^.sets)) || (($f) == (subjects)) || (($f) == (closed)))) || ((heap[current, owns][$o]) && (($f) == (owner))))))));

function modify.HS_LOCK^HS_KEY^.lock(heap: HeapType, current: ref, item: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, item: ref :: (IsHeap(heap)) ==> ((forall <T57> $o: ref, $f: Field T57 :: { modify.HS_LOCK^HS_KEY^.lock(heap, current, item)[$o, $f] } (modify.HS_LOCK^HS_KEY^.lock(heap, current, item)[$o, $f]) <==> (((($o) == (current)) && ((($f) == (owns)) || (($f) == (closed)))) || (((($o) == (item)) || (heap[current, owns][$o])) && (($f) == (owner))))))));

function modify.HS_SET^HS_KEY^.extend(heap: HeapType, current: ref, v: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, v: ref :: (IsHeap(heap)) ==> ((forall <T58> $o: ref, $f: Field T58 :: { modify.HS_SET^HS_KEY^.extend(heap, current, v)[$o, $f] } (modify.HS_SET^HS_KEY^.extend(heap, current, v)[$o, $f]) <==> ((($o) == (current)) && ((!(IsModelField($f, HS_SET^HS_KEY^))) || (($f) == (HS_SET^HS_KEY^.set))))))));

function modify.HS_SET^HS_KEY^.set_has(heap: HeapType, current: ref, v: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, v: ref :: (IsHeap(heap)) ==> ((forall <T59> $o: ref, $f: Field T59 :: { modify.HS_SET^HS_KEY^.set_has(heap, current, v)[$o, $f] } (modify.HS_SET^HS_KEY^.set_has(heap, current, v)[$o, $f]) <==> (false)))));

function read.fun.HS_SET^HS_KEY^.set_has(heap: HeapType, current: ref, v: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, v: ref :: (IsHeap(heap)) ==> ((forall <T60> $o: ref, $f: Field T60 :: { read.fun.HS_SET^HS_KEY^.set_has(heap, current, v)[$o, $f] } (read.fun.HS_SET^HS_KEY^.set_has(heap, current, v)[$o, $f]) <==> (((($o) == (current)) || (heap[current, HS_SET^HS_KEY^.set][$o]) || (($o) == (v))) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.HS_SET^HS_KEY^.set_has(heap: HeapType, current: ref, v: ref) returns (bool) {
  ((v) != (Void)) && (Set#NonNull(heap[current, HS_SET^HS_KEY^.set]))
}

function trigger.fun.HS_SET^HS_KEY^.set_has(heap: HeapType, current: ref, v: ref) returns (bool);

function modify.HS_SET^HS_KEY^.join(heap: HeapType, current: ref, other: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, other: ref :: (IsHeap(heap)) ==> ((forall <T61> $o: ref, $f: Field T61 :: { modify.HS_SET^HS_KEY^.join(heap, current, other)[$o, $f] } (modify.HS_SET^HS_KEY^.join(heap, current, other)[$o, $f]) <==> ((($o) == (current)) && ((!(IsModelField($f, HS_SET^HS_KEY^))) || (($f) == (HS_SET^HS_KEY^.set))))))));

function modify.HS_SET^HS_KEY^.wipe_out(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T62> $o: ref, $f: Field T62 :: { modify.HS_SET^HS_KEY^.wipe_out(heap, current)[$o, $f] } (modify.HS_SET^HS_KEY^.wipe_out(heap, current)[$o, $f]) <==> ((($o) == (current)) && ((!(IsModelField($f, HS_SET^HS_KEY^))) || (($f) == (HS_SET^HS_KEY^.set))))))));

function modify.HS_LOCK^HS_KEY^.unlock(heap: HeapType, current: ref, item: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, item: ref :: (IsHeap(heap)) ==> ((forall <T63> $o: ref, $f: Field T63 :: { modify.HS_LOCK^HS_KEY^.unlock(heap, current, item)[$o, $f] } (modify.HS_LOCK^HS_KEY^.unlock(heap, current, item)[$o, $f]) <==> (((($o) == (current)) && ((($f) == (owns)) || (($f) == (closed)))) || (((($o) == (item)) || (heap[current, owns][$o])) && (($f) == (owner))))))));

function pre.fun.MML_SEQUENCE^MML_SEQUENCE^HS_KEY^^.item(current: Seq (Seq (ref)), i: int) returns (bool) {
  ((1) <= (i)) && ((i) <= (Seq#Length(current)))
}

function trigger.fun.MML_SEQUENCE^MML_SEQUENCE^HS_KEY^^.item(current: Seq (Seq (ref)), i: int) returns (bool);

function modify.HS_SET^HS_KEY^.bucket_index(heap: HeapType, current: ref, hc: int, n: int) returns (Frame);

axiom ((forall heap: HeapType, current: ref, hc: int, n: int :: (IsHeap(heap)) ==> ((forall <T64> $o: ref, $f: Field T64 :: { modify.HS_SET^HS_KEY^.bucket_index(heap, current, hc, n)[$o, $f] } (modify.HS_SET^HS_KEY^.bucket_index(heap, current, hc, n)[$o, $f]) <==> (false)))));

function read.fun.HS_SET^HS_KEY^.bucket_index(heap: HeapType, current: ref, hc: int, n: int) returns (Frame);

axiom ((forall heap: HeapType, current: ref, hc: int, n: int :: (IsHeap(heap)) ==> ((forall <T65> $o: ref, $f: Field T65 :: { read.fun.HS_SET^HS_KEY^.bucket_index(heap, current, hc, n)[$o, $f] } (read.fun.HS_SET^HS_KEY^.bucket_index(heap, current, hc, n)[$o, $f]) <==> ((false) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.HS_SET^HS_KEY^.bucket_index(heap: HeapType, current: ref, hc: int, n: int) returns (bool) {
  ((n) > (0)) && ((0) <= (hc))
}

function trigger.fun.HS_SET^HS_KEY^.bucket_index(heap: HeapType, current: ref, hc: int, n: int) returns (bool);

procedure HS_KEY.in_observers(Current: ref, new_observers: Set (ref), o: ref) returns (Result: bool where true);
  free requires attached_exact(Heap, Current, HS_KEY); // info:type property for argument Current
  free requires Set#ItemsType(Heap, new_observers, ANY); // info:type property for argument new_observers
  free requires Heap[o, allocated]; // info:type property for argument o
  modifies Heap;
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.HS_KEY.in_observers(Heap, Current, new_observers, o), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.HS_KEY.in_observers(old(Heap), Current, new_observers, o));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.HS_KEY.in_observers(Heap, Current, new_observers, o), readable);



function fun.HS_KEY.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function fun0.HS_KEY.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.HS_KEY.in_observers(heap, current, new_observers, o) } { trigger.fun.HS_KEY.in_observers(heap, current, new_observers, o) } (pre.fun.HS_KEY.in_observers(heap, current, new_observers, o)) ==> ((fun.HS_KEY.in_observers(heap, current, new_observers, o)) == (new_observers[o]))));

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.HS_KEY.in_observers(heap, current, new_observers, o) } (fun.HS_KEY.in_observers(heap, current, new_observers, o)) == (fun0.HS_KEY.in_observers(heap, current, new_observers, o))));

axiom ((forall h: HeapType, h': HeapType, current: ref, new_observers: Set (ref), o: ref :: { HeapSucc(h, h'), fun0.HS_KEY.in_observers(h, current, new_observers, o), fun0.HS_KEY.in_observers(h', current, new_observers, o) } ((HeapSucc(h, h')) && (pre.fun.HS_KEY.in_observers(h, current, new_observers, o)) && (pre.fun.HS_KEY.in_observers(h', current, new_observers, o)) && (same_inside(h, h', read.fun.HS_KEY.in_observers(h, current, new_observers, o)))) ==> ((fun0.HS_KEY.in_observers(h, current, new_observers, o)) == (fun0.HS_KEY.in_observers(h', current, new_observers, o)))));

procedure HS_HASHABLE.in_observers(Current: ref, new_observers: Set (ref), o: ref) returns (Result: bool where true);
  free requires attached_exact(Heap, Current, HS_HASHABLE); // info:type property for argument Current
  free requires Set#ItemsType(Heap, new_observers, ANY); // info:type property for argument new_observers
  free requires Heap[o, allocated]; // info:type property for argument o
  modifies Heap;
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.HS_HASHABLE.in_observers(Heap, Current, new_observers, o), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.HS_HASHABLE.in_observers(old(Heap), Current, new_observers, o));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.HS_HASHABLE.in_observers(Heap, Current, new_observers, o), readable);



function fun.HS_HASHABLE.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function fun0.HS_HASHABLE.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.HS_HASHABLE.in_observers(heap, current, new_observers, o) } { trigger.fun.HS_HASHABLE.in_observers(heap, current, new_observers, o) } (pre.fun.HS_HASHABLE.in_observers(heap, current, new_observers, o)) ==> ((fun.HS_HASHABLE.in_observers(heap, current, new_observers, o)) == (new_observers[o]))));

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.HS_HASHABLE.in_observers(heap, current, new_observers, o) } (fun.HS_HASHABLE.in_observers(heap, current, new_observers, o)) == (fun0.HS_HASHABLE.in_observers(heap, current, new_observers, o))));

axiom ((forall h: HeapType, h': HeapType, current: ref, new_observers: Set (ref), o: ref :: { HeapSucc(h, h'), fun0.HS_HASHABLE.in_observers(h, current, new_observers, o), fun0.HS_HASHABLE.in_observers(h', current, new_observers, o) } ((HeapSucc(h, h')) && (pre.fun.HS_HASHABLE.in_observers(h, current, new_observers, o)) && (pre.fun.HS_HASHABLE.in_observers(h', current, new_observers, o)) && (same_inside(h, h', read.fun.HS_HASHABLE.in_observers(h, current, new_observers, o)))) ==> ((fun0.HS_HASHABLE.in_observers(h, current, new_observers, o)) == (fun0.HS_HASHABLE.in_observers(h', current, new_observers, o)))));

function pre.fun.MML_SEQUENCE^HS_HASHABLE^.item(current: Seq (ref), i: int) returns (bool) {
  ((1) <= (i)) && ((i) <= (Seq#Length(current)))
}

function trigger.fun.MML_SEQUENCE^HS_HASHABLE^.item(current: Seq (ref), i: int) returns (bool);

procedure HS_SET^HS_HASHABLE^.in_observers(Current: ref, new_observers: Set (ref), o: ref) returns (Result: bool where true);
  free requires attached_exact(Heap, Current, HS_SET^HS_HASHABLE^); // info:type property for argument Current
  free requires Set#ItemsType(Heap, new_observers, ANY); // info:type property for argument new_observers
  free requires Heap[o, allocated]; // info:type property for argument o
  modifies Heap;
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.HS_SET^HS_HASHABLE^.in_observers(Heap, Current, new_observers, o), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.HS_SET^HS_HASHABLE^.in_observers(old(Heap), Current, new_observers, o));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.HS_SET^HS_HASHABLE^.in_observers(Heap, Current, new_observers, o), readable);



function fun.HS_SET^HS_HASHABLE^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function fun0.HS_SET^HS_HASHABLE^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.HS_SET^HS_HASHABLE^.in_observers(heap, current, new_observers, o) } { trigger.fun.HS_SET^HS_HASHABLE^.in_observers(heap, current, new_observers, o) } (pre.fun.HS_SET^HS_HASHABLE^.in_observers(heap, current, new_observers, o)) ==> ((fun.HS_SET^HS_HASHABLE^.in_observers(heap, current, new_observers, o)) == (new_observers[o]))));

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.HS_SET^HS_HASHABLE^.in_observers(heap, current, new_observers, o) } (fun.HS_SET^HS_HASHABLE^.in_observers(heap, current, new_observers, o)) == (fun0.HS_SET^HS_HASHABLE^.in_observers(heap, current, new_observers, o))));

axiom ((forall h: HeapType, h': HeapType, current: ref, new_observers: Set (ref), o: ref :: { HeapSucc(h, h'), fun0.HS_SET^HS_HASHABLE^.in_observers(h, current, new_observers, o), fun0.HS_SET^HS_HASHABLE^.in_observers(h', current, new_observers, o) } ((HeapSucc(h, h')) && (pre.fun.HS_SET^HS_HASHABLE^.in_observers(h, current, new_observers, o)) && (pre.fun.HS_SET^HS_HASHABLE^.in_observers(h', current, new_observers, o)) && (same_inside(h, h', read.fun.HS_SET^HS_HASHABLE^.in_observers(h, current, new_observers, o)))) ==> ((fun0.HS_SET^HS_HASHABLE^.in_observers(h, current, new_observers, o)) == (fun0.HS_SET^HS_HASHABLE^.in_observers(h', current, new_observers, o)))));

function pre.fun.MML_SEQUENCE^MML_SEQUENCE^HS_HASHABLE^^.constant(x: Seq (ref), n: int) returns (bool) {
  (n) >= (0)
}

function trigger.fun.MML_SEQUENCE^MML_SEQUENCE^HS_HASHABLE^^.constant(x: Seq (ref), n: int) returns (bool);

function pre.fun.MML_SEQUENCE^MML_SEQUENCE^HS_HASHABLE^^.replaced_at(current: Seq (Seq (ref)), i: int, x: Seq (ref)) returns (bool) {
  Seq#Domain(current)[i]
}

function trigger.fun.MML_SEQUENCE^MML_SEQUENCE^HS_HASHABLE^^.replaced_at(current: Seq (Seq (ref)), i: int, x: Seq (ref)) returns (bool);

function pre.fun.MML_SEQUENCE^HS_HASHABLE^.removed_at(current: Seq (ref), i: int) returns (bool) {
  Seq#Domain(current)[i]
}

function trigger.fun.MML_SEQUENCE^HS_HASHABLE^.removed_at(current: Seq (ref), i: int) returns (bool);

function pre.fun.MML_SET^HS_HASHABLE^.default_create() returns (bool) {
  true
}

function trigger.fun.MML_SET^HS_HASHABLE^.default_create() returns (bool);

function modify.ANY.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T66> $o: ref, $f: Field T66 :: { modify.ANY.in_observers(heap, current, new_observers, o)[$o, $f] } (modify.ANY.in_observers(heap, current, new_observers, o)[$o, $f]) <==> (false)))));

function read.fun.ANY.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T67> $o: ref, $f: Field T67 :: { read.fun.ANY.in_observers(heap, current, new_observers, o)[$o, $f] } (read.fun.ANY.in_observers(heap, current, new_observers, o)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.ANY.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool) {
  true
}

function trigger.fun.ANY.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function modify.HS_LOCK^HS_HASHABLE^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T68> $o: ref, $f: Field T68 :: { modify.HS_LOCK^HS_HASHABLE^.in_observers(heap, current, new_observers, o)[$o, $f] } (modify.HS_LOCK^HS_HASHABLE^.in_observers(heap, current, new_observers, o)[$o, $f]) <==> (false)))));

function read.fun.HS_LOCK^HS_HASHABLE^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T69> $o: ref, $f: Field T69 :: { read.fun.HS_LOCK^HS_HASHABLE^.in_observers(heap, current, new_observers, o)[$o, $f] } (read.fun.HS_LOCK^HS_HASHABLE^.in_observers(heap, current, new_observers, o)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.HS_LOCK^HS_HASHABLE^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool) {
  true
}

function trigger.fun.HS_LOCK^HS_HASHABLE^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function modify.HS_CLIENT.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T70> $o: ref, $f: Field T70 :: { modify.HS_CLIENT.in_observers(heap, current, new_observers, o)[$o, $f] } (modify.HS_CLIENT.in_observers(heap, current, new_observers, o)[$o, $f]) <==> (false)))));

function read.fun.HS_CLIENT.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T71> $o: ref, $f: Field T71 :: { read.fun.HS_CLIENT.in_observers(heap, current, new_observers, o)[$o, $f] } (read.fun.HS_CLIENT.in_observers(heap, current, new_observers, o)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.HS_CLIENT.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool) {
  true
}

function trigger.fun.HS_CLIENT.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

procedure HS_LOCK^HS_KEY^.in_observers(Current: ref, new_observers: Set (ref), o: ref) returns (Result: bool where true);
  free requires attached_exact(Heap, Current, HS_LOCK^HS_KEY^); // info:type property for argument Current
  free requires Set#ItemsType(Heap, new_observers, ANY); // info:type property for argument new_observers
  free requires Heap[o, allocated]; // info:type property for argument o
  modifies Heap;
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.HS_LOCK^HS_KEY^.in_observers(Heap, Current, new_observers, o), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.HS_LOCK^HS_KEY^.in_observers(old(Heap), Current, new_observers, o));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.HS_LOCK^HS_KEY^.in_observers(Heap, Current, new_observers, o), readable);



function fun.HS_LOCK^HS_KEY^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function fun0.HS_LOCK^HS_KEY^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.HS_LOCK^HS_KEY^.in_observers(heap, current, new_observers, o) } { trigger.fun.HS_LOCK^HS_KEY^.in_observers(heap, current, new_observers, o) } (pre.fun.HS_LOCK^HS_KEY^.in_observers(heap, current, new_observers, o)) ==> ((fun.HS_LOCK^HS_KEY^.in_observers(heap, current, new_observers, o)) == (new_observers[o]))));

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.HS_LOCK^HS_KEY^.in_observers(heap, current, new_observers, o) } (fun.HS_LOCK^HS_KEY^.in_observers(heap, current, new_observers, o)) == (fun0.HS_LOCK^HS_KEY^.in_observers(heap, current, new_observers, o))));

axiom ((forall h: HeapType, h': HeapType, current: ref, new_observers: Set (ref), o: ref :: { HeapSucc(h, h'), fun0.HS_LOCK^HS_KEY^.in_observers(h, current, new_observers, o), fun0.HS_LOCK^HS_KEY^.in_observers(h', current, new_observers, o) } ((HeapSucc(h, h')) && (pre.fun.HS_LOCK^HS_KEY^.in_observers(h, current, new_observers, o)) && (pre.fun.HS_LOCK^HS_KEY^.in_observers(h', current, new_observers, o)) && (same_inside(h, h', read.fun.HS_LOCK^HS_KEY^.in_observers(h, current, new_observers, o)))) ==> ((fun0.HS_LOCK^HS_KEY^.in_observers(h, current, new_observers, o)) == (fun0.HS_LOCK^HS_KEY^.in_observers(h', current, new_observers, o)))));

function pre.fun.MML_SEQUENCE^HS_KEY^.item(current: Seq (ref), i: int) returns (bool) {
  ((1) <= (i)) && ((i) <= (Seq#Length(current)))
}

function trigger.fun.MML_SEQUENCE^HS_KEY^.item(current: Seq (ref), i: int) returns (bool);

procedure HS_SET^HS_KEY^.in_observers(Current: ref, new_observers: Set (ref), o: ref) returns (Result: bool where true);
  free requires attached_exact(Heap, Current, HS_SET^HS_KEY^); // info:type property for argument Current
  free requires Set#ItemsType(Heap, new_observers, ANY); // info:type property for argument new_observers
  free requires Heap[o, allocated]; // info:type property for argument o
  modifies Heap;
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.HS_SET^HS_KEY^.in_observers(Heap, Current, new_observers, o), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.HS_SET^HS_KEY^.in_observers(old(Heap), Current, new_observers, o));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.HS_SET^HS_KEY^.in_observers(Heap, Current, new_observers, o), readable);



function fun.HS_SET^HS_KEY^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function fun0.HS_SET^HS_KEY^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.HS_SET^HS_KEY^.in_observers(heap, current, new_observers, o) } { trigger.fun.HS_SET^HS_KEY^.in_observers(heap, current, new_observers, o) } (pre.fun.HS_SET^HS_KEY^.in_observers(heap, current, new_observers, o)) ==> ((fun.HS_SET^HS_KEY^.in_observers(heap, current, new_observers, o)) == (new_observers[o]))));

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.HS_SET^HS_KEY^.in_observers(heap, current, new_observers, o) } (fun.HS_SET^HS_KEY^.in_observers(heap, current, new_observers, o)) == (fun0.HS_SET^HS_KEY^.in_observers(heap, current, new_observers, o))));

axiom ((forall h: HeapType, h': HeapType, current: ref, new_observers: Set (ref), o: ref :: { HeapSucc(h, h'), fun0.HS_SET^HS_KEY^.in_observers(h, current, new_observers, o), fun0.HS_SET^HS_KEY^.in_observers(h', current, new_observers, o) } ((HeapSucc(h, h')) && (pre.fun.HS_SET^HS_KEY^.in_observers(h, current, new_observers, o)) && (pre.fun.HS_SET^HS_KEY^.in_observers(h', current, new_observers, o)) && (same_inside(h, h', read.fun.HS_SET^HS_KEY^.in_observers(h, current, new_observers, o)))) ==> ((fun0.HS_SET^HS_KEY^.in_observers(h, current, new_observers, o)) == (fun0.HS_SET^HS_KEY^.in_observers(h', current, new_observers, o)))));

function modify.HS_KEY.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T72> $o: ref, $f: Field T72 :: { modify.HS_KEY.in_observers(heap, current, new_observers, o)[$o, $f] } (modify.HS_KEY.in_observers(heap, current, new_observers, o)[$o, $f]) <==> (false)))));

function read.fun.HS_KEY.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T73> $o: ref, $f: Field T73 :: { read.fun.HS_KEY.in_observers(heap, current, new_observers, o)[$o, $f] } (read.fun.HS_KEY.in_observers(heap, current, new_observers, o)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.HS_KEY.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool) {
  true
}

function trigger.fun.HS_KEY.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function modify.HS_HASHABLE.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T74> $o: ref, $f: Field T74 :: { modify.HS_HASHABLE.in_observers(heap, current, new_observers, o)[$o, $f] } (modify.HS_HASHABLE.in_observers(heap, current, new_observers, o)[$o, $f]) <==> (false)))));

function read.fun.HS_HASHABLE.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T75> $o: ref, $f: Field T75 :: { read.fun.HS_HASHABLE.in_observers(heap, current, new_observers, o)[$o, $f] } (read.fun.HS_HASHABLE.in_observers(heap, current, new_observers, o)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.HS_HASHABLE.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool) {
  true
}

function trigger.fun.HS_HASHABLE.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function modify.HS_SET^HS_HASHABLE^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T76> $o: ref, $f: Field T76 :: { modify.HS_SET^HS_HASHABLE^.in_observers(heap, current, new_observers, o)[$o, $f] } (modify.HS_SET^HS_HASHABLE^.in_observers(heap, current, new_observers, o)[$o, $f]) <==> (false)))));

function read.fun.HS_SET^HS_HASHABLE^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T77> $o: ref, $f: Field T77 :: { read.fun.HS_SET^HS_HASHABLE^.in_observers(heap, current, new_observers, o)[$o, $f] } (read.fun.HS_SET^HS_HASHABLE^.in_observers(heap, current, new_observers, o)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.HS_SET^HS_HASHABLE^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool) {
  true
}

function trigger.fun.HS_SET^HS_HASHABLE^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function modify.HS_LOCK^HS_KEY^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T78> $o: ref, $f: Field T78 :: { modify.HS_LOCK^HS_KEY^.in_observers(heap, current, new_observers, o)[$o, $f] } (modify.HS_LOCK^HS_KEY^.in_observers(heap, current, new_observers, o)[$o, $f]) <==> (false)))));

function read.fun.HS_LOCK^HS_KEY^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T79> $o: ref, $f: Field T79 :: { read.fun.HS_LOCK^HS_KEY^.in_observers(heap, current, new_observers, o)[$o, $f] } (read.fun.HS_LOCK^HS_KEY^.in_observers(heap, current, new_observers, o)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.HS_LOCK^HS_KEY^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool) {
  true
}

function trigger.fun.HS_LOCK^HS_KEY^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function modify.HS_SET^HS_KEY^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T80> $o: ref, $f: Field T80 :: { modify.HS_SET^HS_KEY^.in_observers(heap, current, new_observers, o)[$o, $f] } (modify.HS_SET^HS_KEY^.in_observers(heap, current, new_observers, o)[$o, $f]) <==> (false)))));

function read.fun.HS_SET^HS_KEY^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T81> $o: ref, $f: Field T81 :: { read.fun.HS_SET^HS_KEY^.in_observers(heap, current, new_observers, o)[$o, $f] } (read.fun.HS_SET^HS_KEY^.in_observers(heap, current, new_observers, o)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.HS_SET^HS_KEY^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool) {
  true
}

function trigger.fun.HS_SET^HS_KEY^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);
