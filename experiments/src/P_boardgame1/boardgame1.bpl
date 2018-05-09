// Automatically generated (12/12/2017 1:55:29.686 PM)

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

const unique PLAYER: Type;

axiom ((PLAYER) <: (ANY));

axiom ((forall t: Type :: { (PLAYER) <: (t) } ((PLAYER) <: (t)) <==> (((t) == (PLAYER)) || ((ANY) <: (t)))));

axiom ((FieldId(allocated, PLAYER)) == (-1));

axiom ((FieldId(closed, PLAYER)) == (-2));

axiom ((FieldId(owner, PLAYER)) == (-3));

axiom ((FieldId(owns, PLAYER)) == (-4));

axiom ((FieldId(observers, PLAYER)) == (-5));

axiom ((FieldId(subjects, PLAYER)) == (-6));

axiom ((forall <T0> $f: Field T0 :: { IsModelField($f, PLAYER) } (IsModelField($f, PLAYER)) <==> ((($f) == (subjects)) || (($f) == (observers)))));

function { :inline } PLAYER.user_inv(heap: HeapType, current: ref) returns (bool) {
  ((heap[current, PLAYER.position]) >= (0)) && ((heap[current, PLAYER.name]) != (Void)) && (Set#Equal(heap[current, owns], Set#Singleton(heap[current, PLAYER.name]))) && (!(Seq#IsEmpty(heap[heap[current, PLAYER.name], V_STRING.sequence]))) && (Set#IsEmpty(heap[current, observers])) && (Set#IsEmpty(heap[current, subjects])) && (admissibility2(heap, current))
}

function PLAYER.owns.static(heap: HeapType, current: ref) returns (Set (ref)) {
  Set#Singleton(heap[current, PLAYER.name])
}

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached_exact(heap, current, PLAYER)) ==> ((user_inv(heap, current)) <==> (PLAYER.user_inv(heap, current)))));

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached(heap, current, PLAYER)) ==> ((user_inv(heap, current)) ==> (PLAYER.user_inv(heap, current)))));

procedure PLAYER.invariant_admissibility_check(Current: ref);
  requires attached_exact(Heap, Current, PLAYER);



implementation PLAYER.invariant_admissibility_check(Current: ref)
{
  entry:
  goto pre, a2, a3;
  pre:
  assert user_inv_readable(Heap, Current)[Current, PLAYER.position]; // type:access tag:attribute_readable line:61 cid:404 fid:82
  assume (Heap[Current, PLAYER.position]) >= (0);
  assert user_inv_readable(Heap, Current)[Current, PLAYER.name]; // type:access tag:attribute_readable line:62 cid:404 fid:81
  assume (Heap[Current, PLAYER.name]) != (Void);
  assert user_inv_readable(Heap, Current)[Current, PLAYER.name]; // type:access tag:attribute_readable line:63 cid:404 fid:81
  assume Set#Equal(Heap[Current, owns], Set#Singleton(Heap[Current, PLAYER.name]));
  assert user_inv_readable(Heap, Current)[Current, PLAYER.name]; // type:access tag:attribute_readable line:64 cid:404 fid:81
  assert {:subsumption 0} (Heap[Current, PLAYER.name]) != (Void); // type:attached tag:name_exists line:64
  assert user_inv_readable(Heap, Current)[Heap[Current, PLAYER.name], V_STRING.sequence]; // type:access tag:attribute_readable line:64 cid:130 fid:94
  assume !(Seq#IsEmpty(Heap[Heap[Current, PLAYER.name], V_STRING.sequence]));
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

procedure create.PLAYER.make(Current: ref, n: ref);
  free requires attached_exact(Heap, Current, PLAYER); // info:type property for argument Current
  free requires detachable_exact(Heap, n, V_STRING); // info:type property for argument n
  modifies Heap;
  requires (n) != (Void); // type:attached tag:name_valid line:14
  requires is_wrapped(Heap, n); // type:pre tag:name_valid line:14
  requires !(Seq#IsEmpty(Heap[n, V_STRING.sequence])); // type:pre tag:name_exists line:15
  ensures (Heap[Current, PLAYER.name]) != (Void); // type:attached tag:name_set line:19
  ensures (n) != (Void); // type:attached tag:name_set line:19
  ensures Seq#Equal(Heap[Heap[Current, PLAYER.name], V_STRING.sequence], Heap[n, V_STRING.sequence]); // type:post tag:name_set line:19
  requires (forall <T3> $f: Field T3 :: (($f) != (allocated)) ==> ((Heap[Current, $f]) == (Default($f))));
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.PLAYER.make(Heap, Current, n), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.PLAYER.make(old(Heap), Current, n));
  free ensures HeapSucc(old(Heap), Heap);
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts
  ensures is_wrapped(Heap, n); // type:post tag:arg_n_is_wrapped default:contracts



implementation create.PLAYER.make(Current: ref, n: ref)
{
  var temp_1: ref;

  init_locals:
  temp_1 := Void;

  entry:
  assume {:captureState "create.PLAYER.make"} true;
  // /home/caf/temp/comcom/repo-boardgame1/player.e:17
  // create name.make_from_v_string (n)
  call temp_1 := allocate(V_STRING); // line:-1
  call create.V_STRING.make_from_v_string(temp_1, n); // line:17 cid:130 rid:797
  call update_heap(Current, PLAYER.name, temp_1); // line:17
  if (modify.PLAYER.make(Heap, Current, n)[Current, owns]) {
    call update_heap(Current, owns, PLAYER.owns.static(Heap, Current)); // default:owns line:20
  }
  if (*) {
    assert (Heap[Current, PLAYER.position]) >= (0); // type:inv tag:position_not_negative line:40 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert (Heap[Current, PLAYER.name]) != (Void); // type:inv tag:name_not_void line:40 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#Equal(Heap[Current, owns], Set#Singleton(Heap[Current, PLAYER.name])); // type:inv tag:owns_def line:40 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert !(Seq#IsEmpty(Heap[Heap[Current, PLAYER.name], V_STRING.sequence])); // type:inv tag:name_exists line:40 cid:1 rid:55
    assume false;
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
    assert admissibility2(Heap, Current); // type:inv tag:A2 line:40 cid:1 rid:55
    assume false;
  }
  call wrap(Current); // default:wrapping cid:1 rid:55 line:20
}

procedure PLAYER.set_position(Current: ref, pos: int);
  free requires attached_exact(Heap, Current, PLAYER); // info:type property for argument Current
  free requires is_integer_32(pos); // info:type property for argument pos
  modifies Heap;
  requires (pos) >= (0); // type:pre tag:pos_not_negative line:35
  ensures (Heap[Current, PLAYER.position]) == (pos); // type:post tag:position_set line:39
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.PLAYER.set_position(Heap, Current, pos), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.PLAYER.set_position(old(Heap), Current, pos));
  free ensures HeapSucc(old(Heap), Heap);
  requires is_wrapped(Heap, Current); // type:pre tag:default_is_wrapped default:contracts
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts



function { :inline } variant.PLAYER.set_position.1(heap: HeapType, current: ref, pos: int) returns (int) {
  pos
}

implementation PLAYER.set_position(Current: ref, pos: int)
{
  entry:
  assume {:captureState "PLAYER.set_position"} true;
  call unwrap(Current); // default:wrapping cid:1 rid:57 line:32
  assume PLAYER.user_inv(Heap, Current);
  // /home/caf/temp/comcom/repo-boardgame1/player.e:37
  // position := pos
  call update_heap(Current, PLAYER.position, pos); // line:37
  if (modify.PLAYER.set_position(Heap, Current, pos)[Current, owns]) {
    call update_heap(Current, owns, PLAYER.owns.static(Heap, Current)); // default:owns line:40
  }
  if (*) {
    assert (Heap[Current, PLAYER.position]) >= (0); // type:inv tag:position_not_negative line:40 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert (Heap[Current, PLAYER.name]) != (Void); // type:inv tag:name_not_void line:40 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#Equal(Heap[Current, owns], Set#Singleton(Heap[Current, PLAYER.name])); // type:inv tag:owns_def line:40 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert !(Seq#IsEmpty(Heap[Heap[Current, PLAYER.name], V_STRING.sequence])); // type:inv tag:name_exists line:40 cid:1 rid:55
    assume false;
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
    assert admissibility2(Heap, Current); // type:inv tag:A2 line:40 cid:1 rid:55
    assume false;
  }
  call wrap(Current); // default:wrapping cid:1 rid:55 line:40
}

procedure PLAYER.play(Current: ref, d1: ref, d2: ref);
  free requires attached_exact(Heap, Current, PLAYER); // info:type property for argument Current
  free requires detachable(Heap, d1, DIE); // info:type property for argument d1
  free requires detachable(Heap, d2, DIE); // info:type property for argument d2
  modifies Heap;
  requires ((d1) != (Void)) && ((d2) != (Void)); // type:pre tag:dice_exist line:49
  ensures ((((old(Heap)[Current, PLAYER.position]) + (6)) + (6)) >= (Heap[Current, PLAYER.position])) && ((Heap[Current, PLAYER.position]) >= ((old(Heap)[Current, PLAYER.position]) + (2))); // type:post tag:position_increased line:57
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.PLAYER.play(Heap, Current, d1, d2), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.PLAYER.play(old(Heap), Current, d1, d2));
  free ensures HeapSucc(old(Heap), Heap);
  requires is_wrapped(Heap, Current); // type:pre tag:default_is_wrapped default:contracts
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts
  requires is_wrapped(Heap, d1); // type:pre tag:arg_d1_is_wrapped default:contracts
  ensures is_wrapped(Heap, d1); // type:post tag:arg_d1_is_wrapped default:contracts
  requires is_wrapped(Heap, d2); // type:pre tag:arg_d2_is_wrapped default:contracts
  ensures is_wrapped(Heap, d2); // type:post tag:arg_d2_is_wrapped default:contracts



function { :inline } variant.PLAYER.play.1(heap: HeapType, current: ref, d1: ref, d2: ref) returns (ref) {
  d1
}

function { :inline } variant.PLAYER.play.2(heap: HeapType, current: ref, d1: ref, d2: ref) returns (ref) {
  d2
}

implementation PLAYER.play(Current: ref, d1: ref, d2: ref)
{
  var temp_2: ref;
  var temp_3: ref;
  var temp_4: ref;
  var temp_5: ref;
  var temp_6: ref;
  var temp_7: ref;
  var temp_8: ref;
  var temp_9: ref;
  var temp_10: ref;
  var temp_11: ref;
  var temp_12: ref;
  var temp_13: ref;
  var temp_14: ref;
  var temp_15: ref;

  init_locals:
  temp_2 := Void;
  temp_3 := Void;
  temp_4 := Void;
  temp_5 := Void;
  temp_6 := Void;
  temp_7 := Void;
  temp_8 := Void;
  temp_9 := Void;
  temp_10 := Void;
  temp_11 := Void;
  temp_12 := Void;
  temp_13 := Void;
  temp_14 := Void;
  temp_15 := Void;

  entry:
  assume {:captureState "PLAYER.play"} true;
  // /home/caf/temp/comcom/repo-boardgame1/player.e:52
  // d1.roll
  assert {:subsumption 0} (d1) != (Void); // type:attached line:52
  call DIE.roll(d1); // line:52 cid:406 rid:5404
  // /home/caf/temp/comcom/repo-boardgame1/player.e:53
  // d2.roll
  assert {:subsumption 0} (d2) != (Void); // type:attached line:53
  call DIE.roll(d2); // line:53 cid:406 rid:5404
  // /home/caf/temp/comcom/repo-boardgame1/player.e:54
  // set_position (position + d1.face_value + d2.face_value)
  assert {:subsumption 0} (d1) != (Void); // type:attached line:54
  assert {:subsumption 0} (d2) != (Void); // type:attached line:54
  call PLAYER.set_position(Current, ((Heap[Current, PLAYER.position]) + (Heap[d1, DIE.face_value])) + (Heap[d2, DIE.face_value])); // line:54 cid:404 rid:5419
  // /home/caf/temp/comcom/repo-boardgame1/player.e:55
  // print (name + " rolled " + d1.face_value.out_ + " and " + d2.face_value.out_ + ". Moves to " + position.out_ + ".%N")
  assert {:subsumption 0} (Heap[Current, PLAYER.name]) != (Void); // type:attached line:55
  call temp_2 := allocate(V_STRING); // line:-1
  call create.V_STRING.init(temp_2, Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Singleton(32), 114), 111), 108), 108), 101), 100), 32));
  call temp_3 := V_STRING.plus(Heap[Current, PLAYER.name], temp_2); // line:55 cid:130 rid:810
  assert {:subsumption 0} (temp_3) != (Void); // type:attached line:55
  assert {:subsumption 0} (d1) != (Void); // type:attached line:55
  call temp_4 := INTEGER_32.out_(Heap[d1, DIE.face_value]); // line:55 cid:23 rid:31
  call temp_5 := V_STRING.plus(temp_3, temp_4); // line:55 cid:130 rid:810
  assert {:subsumption 0} (temp_5) != (Void); // type:attached line:55
  call temp_6 := allocate(V_STRING); // line:-1
  call create.V_STRING.init(temp_6, Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Singleton(32), 97), 110), 100), 32));
  call temp_7 := V_STRING.plus(temp_5, temp_6); // line:55 cid:130 rid:810
  assert {:subsumption 0} (temp_7) != (Void); // type:attached line:55
  assert {:subsumption 0} (d2) != (Void); // type:attached line:55
  call temp_8 := INTEGER_32.out_(Heap[d2, DIE.face_value]); // line:55 cid:23 rid:31
  call temp_9 := V_STRING.plus(temp_7, temp_8); // line:55 cid:130 rid:810
  assert {:subsumption 0} (temp_9) != (Void); // type:attached line:55
  call temp_10 := allocate(V_STRING); // line:-1
  call create.V_STRING.init(temp_10, Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Singleton(46), 32), 77), 111), 118), 101), 115), 32), 116), 111), 32));
  call temp_11 := V_STRING.plus(temp_9, temp_10); // line:55 cid:130 rid:810
  assert {:subsumption 0} (temp_11) != (Void); // type:attached line:55
  call temp_12 := INTEGER_32.out_(Heap[Current, PLAYER.position]); // line:55 cid:23 rid:31
  call temp_13 := V_STRING.plus(temp_11, temp_12); // line:55 cid:130 rid:810
  assert {:subsumption 0} (temp_13) != (Void); // type:attached line:55
  call temp_14 := allocate(V_STRING); // line:-1
  call create.V_STRING.init(temp_14, Seq#Extended(Seq#Singleton(46), 10));
  call temp_15 := V_STRING.plus(temp_13, temp_14); // line:55 cid:130 rid:810
  call PLAYER.print(Current, temp_15); // line:55 cid:404 rid:33
}

const unique APPLICATION: Type;

axiom ((APPLICATION) <: (ANY));

axiom ((forall t: Type :: { (APPLICATION) <: (t) } ((APPLICATION) <: (t)) <==> (((t) == (APPLICATION)) || ((ANY) <: (t)))));

axiom ((FieldId(allocated, APPLICATION)) == (-1));

axiom ((FieldId(closed, APPLICATION)) == (-2));

axiom ((FieldId(owner, APPLICATION)) == (-3));

axiom ((FieldId(owns, APPLICATION)) == (-4));

axiom ((FieldId(observers, APPLICATION)) == (-5));

axiom ((FieldId(subjects, APPLICATION)) == (-6));

axiom ((forall <T4> $f: Field T4 :: { IsModelField($f, APPLICATION) } (IsModelField($f, APPLICATION)) <==> ((($f) == (subjects)) || (($f) == (observers)))));

function { :inline } APPLICATION.user_inv(heap: HeapType, current: ref) returns (bool) {
  (Set#IsEmpty(heap[current, observers])) && (Set#IsEmpty(heap[current, subjects])) && (Set#IsEmpty(heap[current, owns])) && (admissibility2(heap, current))
}

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached_exact(heap, current, APPLICATION)) ==> ((user_inv(heap, current)) <==> (APPLICATION.user_inv(heap, current)))));

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached(heap, current, APPLICATION)) ==> ((user_inv(heap, current)) ==> (APPLICATION.user_inv(heap, current)))));

procedure APPLICATION.invariant_admissibility_check(Current: ref);
  requires attached_exact(Heap, Current, APPLICATION);



implementation APPLICATION.invariant_admissibility_check(Current: ref)
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

procedure create.APPLICATION.make(Current: ref);
  free requires attached_exact(Heap, Current, APPLICATION); // info:type property for argument Current
  modifies Heap;
  requires (forall <T5> $f: Field T5 :: (($f) != (allocated)) ==> ((Heap[Current, $f]) == (Default($f))));
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.APPLICATION.make(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.APPLICATION.make(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);



implementation create.APPLICATION.make(Current: ref)
{
  var PreLoopHeap_19: HeapType;
  var temp_20: ref;
  var temp_21: ref;
  var temp_22: ref;
  var temp_23: ref;
  var temp_24: ref;
  var temp_25: ref;
  var temp_26: ref;
  var temp_27: ref;
  var temp_28: ref;
  var temp_29: ref;
  var temp_30: ref;
  var temp_31: int;
  var temp_32: ref;
  var temp_33: ref;
  var temp_34: ref;
  var temp_35: ref;
  var local1: int where is_integer_32(local1);
  var local2: ref where detachable_exact(Heap, local2, GAME);

  init_locals:
  temp_20 := Void;
  temp_21 := Void;
  temp_22 := Void;
  temp_23 := Void;
  temp_24 := Void;
  temp_25 := Void;
  temp_26 := Void;
  temp_27 := Void;
  temp_28 := Void;
  temp_29 := Void;
  temp_30 := Void;
  temp_31 := 0;
  temp_32 := Void;
  temp_33 := Void;
  temp_34 := Void;
  temp_35 := Void;
  local1 := 0;
  local2 := Void;

  entry:
  assume {:captureState "create.APPLICATION.make"} true;
  // /home/caf/temp/comcom/repo-boardgame1/application.e:19
  // count := {GAME}.Min_player_count - 1
  local1 := (2) - (1);
  PreLoopHeap_19 := Heap;
  goto loop_head_16;
  loop_head_16:
  assume HeapSucc(PreLoopHeap_19, Heap);
  assume same_outside(old(Heap), Heap, modify.APPLICATION.make(old(Heap), Current));
  assume global(Heap);
  // /home/caf/temp/comcom/repo-boardgame1/application.e:-1
  goto loop_body_17, loop_end_18;
  loop_body_17:
  assume !(((2) <= (local1)) && ((local1) <= (6)));
  // /home/caf/temp/comcom/repo-boardgame1/application.e:25
  // print ("Enter number of players between " + {GAME}.Min_player_count.out_ + " and " + {GAME}.Max_player_count.out_ + ": ")
  call temp_20 := allocate(V_STRING); // line:-1
  call create.V_STRING.init(temp_20, Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Singleton(69), 110), 116), 101), 114), 32), 110), 117), 109), 98), 101), 114), 32), 111), 102), 32), 112), 108), 97), 121), 101), 114), 115), 32), 98), 101), 116), 119), 101), 101), 110), 32));
  assert {:subsumption 0} (temp_20) != (Void); // type:attached line:25
  call temp_21 := INTEGER_32.out_(2); // line:25 cid:23 rid:31
  call temp_22 := V_STRING.plus(temp_20, temp_21); // line:25 cid:130 rid:810
  assert {:subsumption 0} (temp_22) != (Void); // type:attached line:25
  call temp_23 := allocate(V_STRING); // line:-1
  call create.V_STRING.init(temp_23, Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Singleton(32), 97), 110), 100), 32));
  call temp_24 := V_STRING.plus(temp_22, temp_23); // line:25 cid:130 rid:810
  assert {:subsumption 0} (temp_24) != (Void); // type:attached line:25
  call temp_25 := INTEGER_32.out_(6); // line:25 cid:23 rid:31
  call temp_26 := V_STRING.plus(temp_24, temp_25); // line:25 cid:130 rid:810
  assert {:subsumption 0} (temp_26) != (Void); // type:attached line:25
  call temp_27 := allocate(V_STRING); // line:-1
  call create.V_STRING.init(temp_27, Seq#Extended(Seq#Singleton(58), 32));
  call temp_28 := V_STRING.plus(temp_26, temp_27); // line:25 cid:130 rid:810
  call APPLICATION.print(Current, temp_28); // line:25 cid:407 rid:33
  // /home/caf/temp/comcom/repo-boardgame1/application.e:26
  // io.read_integer
  call temp_29 := APPLICATION.io(Current); // line:26 cid:407 rid:29
  assert {:subsumption 0} (temp_29) != (Void); // type:attached line:26
  call STD_FILES.read_integer(temp_29); // line:26 cid:237 rid:371
  // /home/caf/temp/comcom/repo-boardgame1/application.e:27
  // count := io.last_integer
  call temp_30 := APPLICATION.io(Current); // line:27 cid:407 rid:29
  assert {:subsumption 0} (temp_30) != (Void); // type:attached line:27
  call temp_31 := STD_FILES.last_integer(temp_30); // line:27 cid:237 rid:363
  local1 := temp_31;
  // /home/caf/temp/comcom/repo-boardgame1/application.e:25
  // print ("Enter number of players between " + {GAME}.Min_player_count.out_ + " and " + {GAME}.Max_player_count.out_ + ": ")
  goto loop_head_16;
  loop_end_18:
  assume ((2) <= (local1)) && ((local1) <= (6));
  // /home/caf/temp/comcom/repo-boardgame1/application.e:30
  // create game.make (count)
  call temp_32 := allocate(GAME); // line:-1
  call create.GAME.make(temp_32, local1); // line:30 cid:405 rid:5406
  local2 := temp_32;
  // /home/caf/temp/comcom/repo-boardgame1/application.e:31
  // game.play
  assert {:subsumption 0} (local2) != (Void); // type:attached line:31
  call GAME.play(local2); // line:31 cid:405 rid:5407
  // /home/caf/temp/comcom/repo-boardgame1/application.e:32
  // check game.winner.inv end
  assert {:subsumption 0} (local2) != (Void); // type:attached line:32
  assert {:subsumption 0} (Heap[local2, GAME.winner]) != (Void); // type:attached line:32
  assert user_inv(Heap, Heap[local2, GAME.winner]); // type:check line:32
  // /home/caf/temp/comcom/repo-boardgame1/application.e:33
  // print ("%NAnd the winner is: " + game.winner.name)
  call temp_33 := allocate(V_STRING); // line:-1
  call create.V_STRING.init(temp_33, Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Singleton(10), 65), 110), 100), 32), 116), 104), 101), 32), 119), 105), 110), 110), 101), 114), 32), 105), 115), 58), 32));
  assert {:subsumption 0} (temp_33) != (Void); // type:attached line:33
  assert {:subsumption 0} (local2) != (Void); // type:attached line:33
  assert {:subsumption 0} (Heap[local2, GAME.winner]) != (Void); // type:attached line:33
  call temp_34 := V_STRING.plus(temp_33, Heap[Heap[local2, GAME.winner], PLAYER.name]); // line:33 cid:130 rid:810
  call APPLICATION.print(Current, temp_34); // line:33 cid:407 rid:33
  // /home/caf/temp/comcom/repo-boardgame1/application.e:34
  // print ("%N*** Game Over ***")
  call temp_35 := allocate(V_STRING);
  call create.V_STRING.init(temp_35, Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Singleton(10), 42), 42), 42), 32), 71), 97), 109), 101), 32), 79), 118), 101), 114), 32), 42), 42), 42));
  call APPLICATION.print(Current, temp_35); // line:34 cid:407 rid:33
}

const unique DIE: Type;

axiom ((DIE) <: (ANY));

axiom ((forall t: Type :: { (DIE) <: (t) } ((DIE) <: (t)) <==> (((t) == (DIE)) || ((ANY) <: (t)))));

axiom ((FieldId(allocated, DIE)) == (-1));

axiom ((FieldId(closed, DIE)) == (-2));

axiom ((FieldId(owner, DIE)) == (-3));

axiom ((FieldId(owns, DIE)) == (-4));

axiom ((FieldId(observers, DIE)) == (-5));

axiom ((FieldId(subjects, DIE)) == (-6));

axiom ((forall <T6> $f: Field T6 :: { IsModelField($f, DIE) } (IsModelField($f, DIE)) <==> ((($f) == (subjects)) || (($f) == (observers)))));

function { :inline } DIE.user_inv(heap: HeapType, current: ref) returns (bool) {
  (Set#Equal(heap[current, owns], Set#Singleton(heap[current, DIE.random]))) && ((heap[current, DIE.face_value]) >= (1)) && ((heap[current, DIE.face_value]) <= (6)) && (Set#IsEmpty(heap[current, observers])) && (Set#IsEmpty(heap[current, subjects])) && (admissibility2(heap, current))
}

function DIE.owns.static(heap: HeapType, current: ref) returns (Set (ref)) {
  Set#Singleton(heap[current, DIE.random])
}

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached_exact(heap, current, DIE)) ==> ((user_inv(heap, current)) <==> (DIE.user_inv(heap, current)))));

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached(heap, current, DIE)) ==> ((user_inv(heap, current)) ==> (DIE.user_inv(heap, current)))));

procedure DIE.invariant_admissibility_check(Current: ref);
  requires attached_exact(Heap, Current, DIE);



implementation DIE.invariant_admissibility_check(Current: ref)
{
  entry:
  goto pre, a2, a3;
  pre:
  assert user_inv_readable(Heap, Current)[Current, DIE.random]; // type:access tag:attribute_readable line:33 cid:406 fid:83
  assume Set#Equal(Heap[Current, owns], Set#Singleton(Heap[Current, DIE.random]));
  assert user_inv_readable(Heap, Current)[Current, DIE.face_value]; // type:access tag:attribute_readable line:34 cid:406 fid:81
  assert user_inv_readable(Heap, Current)[Current, DIE.face_value]; // type:access tag:attribute_readable line:34 cid:406 fid:81
  assume ((Heap[Current, DIE.face_value]) >= (1)) && ((Heap[Current, DIE.face_value]) <= (6));
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

procedure create.DIE.roll(Current: ref);
  free requires attached_exact(Heap, Current, DIE); // info:type property for argument Current
  modifies Heap;
  requires (forall <T7> $f: Field T7 :: (($f) != (allocated)) ==> ((Heap[Current, $f]) == (Default($f))));
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.DIE.roll(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.DIE.roll(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts



implementation create.DIE.roll(Current: ref)
{
  var temp_36: ref;
  var temp_37: int;

  init_locals:
  temp_36 := Void;
  temp_37 := 0;

  entry:
  assume {:captureState "create.DIE.roll"} true;
  // /home/caf/temp/comcom/repo-boardgame1/die.e:20
  // if random = Void then
  if ((Heap[Current, DIE.random]) == (Void)) {
    // /home/caf/temp/comcom/repo-boardgame1/die.e:21
    // create random
    call temp_36 := allocate(V_RANDOM); // line:-1
    call create.V_RANDOM.default_create(temp_36); // line:21 cid:135 rid:35
    call update_heap(Current, DIE.random, temp_36); // line:21
  }
  // /home/caf/temp/comcom/repo-boardgame1/die.e:23
  // random.forth
  assert {:subsumption 0} (Heap[Current, DIE.random]) != (Void); // type:attached line:23
  call V_RANDOM.forth(Heap[Current, DIE.random]); // line:23 cid:135 rid:1573
  // /home/caf/temp/comcom/repo-boardgame1/die.e:24
  // face_value := random.bounded_item (1, Face_count)
  assert {:subsumption 0} (Heap[Current, DIE.random]) != (Void); // type:attached line:24
  call temp_37 := V_RANDOM.bounded_item(Heap[Current, DIE.random], 1, 6); // line:24 cid:135 rid:1578
  call update_heap(Current, DIE.face_value, temp_37); // line:24
  if (modify.DIE.roll(Heap, Current)[Current, owns]) {
    call update_heap(Current, owns, DIE.owns.static(Heap, Current)); // default:owns line:25
  }
  if (*) {
    assert Set#Equal(Heap[Current, owns], Set#Singleton(Heap[Current, DIE.random])); // type:inv tag:owns_def line:25 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert ((Heap[Current, DIE.face_value]) >= (1)) && ((Heap[Current, DIE.face_value]) <= (6)); // type:inv tag:face_value_valid line:25 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, observers]); // type:inv tag:default_observers line:25 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, subjects]); // type:inv tag:default_subjects line:25 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert admissibility2(Heap, Current); // type:inv tag:A2 line:25 cid:1 rid:55
    assume false;
  }
  call wrap(Current); // default:wrapping cid:1 rid:55 line:25
}

procedure DIE.roll(Current: ref);
  free requires attached_exact(Heap, Current, DIE); // info:type property for argument Current
  modifies Heap;
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.DIE.roll(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.DIE.roll(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);
  requires is_wrapped(Heap, Current); // type:pre tag:default_is_wrapped default:contracts
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts



function { :inline } variant.DIE.roll.1(heap: HeapType, current: ref) returns (int) {
  0
}

implementation DIE.roll(Current: ref)
{
  var temp_38: ref;
  var temp_39: int;

  init_locals:
  temp_38 := Void;
  temp_39 := 0;

  entry:
  assume {:captureState "DIE.roll"} true;
  call unwrap(Current); // default:wrapping cid:1 rid:57 line:17
  assume DIE.user_inv(Heap, Current);
  // /home/caf/temp/comcom/repo-boardgame1/die.e:20
  // if random = Void then
  if ((Heap[Current, DIE.random]) == (Void)) {
    // /home/caf/temp/comcom/repo-boardgame1/die.e:21
    // create random
    call temp_38 := allocate(V_RANDOM); // line:-1
    call create.V_RANDOM.default_create(temp_38); // line:21 cid:135 rid:35
    call update_heap(Current, DIE.random, temp_38); // line:21
  }
  // /home/caf/temp/comcom/repo-boardgame1/die.e:23
  // random.forth
  assert {:subsumption 0} (Heap[Current, DIE.random]) != (Void); // type:attached line:23
  call V_RANDOM.forth(Heap[Current, DIE.random]); // line:23 cid:135 rid:1573
  // /home/caf/temp/comcom/repo-boardgame1/die.e:24
  // face_value := random.bounded_item (1, Face_count)
  assert {:subsumption 0} (Heap[Current, DIE.random]) != (Void); // type:attached line:24
  call temp_39 := V_RANDOM.bounded_item(Heap[Current, DIE.random], 1, 6); // line:24 cid:135 rid:1578
  call update_heap(Current, DIE.face_value, temp_39); // line:24
  if (modify.DIE.roll(Heap, Current)[Current, owns]) {
    call update_heap(Current, owns, DIE.owns.static(Heap, Current)); // default:owns line:25
  }
  if (*) {
    assert Set#Equal(Heap[Current, owns], Set#Singleton(Heap[Current, DIE.random])); // type:inv tag:owns_def line:25 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert ((Heap[Current, DIE.face_value]) >= (1)) && ((Heap[Current, DIE.face_value]) <= (6)); // type:inv tag:face_value_valid line:25 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, observers]); // type:inv tag:default_observers line:25 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, subjects]); // type:inv tag:default_subjects line:25 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert admissibility2(Heap, Current); // type:inv tag:A2 line:25 cid:1 rid:55
    assume false;
  }
  call wrap(Current); // default:wrapping cid:1 rid:55 line:25
}

const unique GAME: Type;

axiom (is_frozen(GAME));

axiom ((GAME) <: (ANY));

axiom ((forall t: Type :: { (GAME) <: (t) } ((GAME) <: (t)) <==> (((t) == (GAME)) || ((ANY) <: (t)))));

axiom ((FieldId(allocated, GAME)) == (-1));

axiom ((FieldId(closed, GAME)) == (-2));

axiom ((FieldId(owner, GAME)) == (-3));

axiom ((FieldId(owns, GAME)) == (-4));

axiom ((FieldId(observers, GAME)) == (-5));

axiom ((FieldId(subjects, GAME)) == (-6));

axiom ((forall <T8> $f: Field T8 :: { IsModelField($f, GAME) } (IsModelField($f, GAME)) <==> ((($f) == (subjects)) || (($f) == (observers)))));

function { :inline } GAME.user_inv(heap: HeapType, current: ref) returns (bool) {
  ((heap[current, GAME.die_1]) != (Void)) && ((heap[current, GAME.die_2]) != (Void)) && ((heap[current, GAME.players]) != (Void)) && (heap[current, owns][heap[current, GAME.players]]) && (Set#Equal(heap[current, owns], Set#Union(Seq#Range(heap[heap[current, GAME.players], V_ARRAY^PLAYER^.sequence]), Set#Extended(Set#Extended(Set#Singleton(heap[current, GAME.players]), heap[current, GAME.die_1]), heap[current, GAME.die_2])))) && ((heap[heap[current, GAME.players], V_ARRAY^PLAYER^.lower_]) == (1)) && ((2) <= (Seq#Length(heap[heap[current, GAME.players], V_ARRAY^PLAYER^.sequence]))) && ((Seq#Length(heap[heap[current, GAME.players], V_ARRAY^PLAYER^.sequence])) <= (6)) && (Seq#NonNull(heap[heap[current, GAME.players], V_ARRAY^PLAYER^.sequence])) && (Seq#NoDuplicates(heap[heap[current, GAME.players], V_ARRAY^PLAYER^.sequence])) && (Set#IsEmpty(heap[current, observers])) && (Set#IsEmpty(heap[current, subjects])) && (admissibility2(heap, current))
}

function GAME.owns.static(heap: HeapType, current: ref) returns (Set (ref)) {
  Set#Union(Seq#Range(heap[heap[current, GAME.players], V_ARRAY^PLAYER^.sequence]), Set#Extended(Set#Extended(Set#Singleton(heap[current, GAME.players]), heap[current, GAME.die_1]), heap[current, GAME.die_2]))
}

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached_exact(heap, current, GAME)) ==> ((user_inv(heap, current)) <==> (GAME.user_inv(heap, current)))));

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached(heap, current, GAME)) ==> ((user_inv(heap, current)) ==> (GAME.user_inv(heap, current)))));

procedure GAME.invariant_admissibility_check(Current: ref);
  requires attached_exact(Heap, Current, GAME);



implementation GAME.invariant_admissibility_check(Current: ref)
{
  entry:
  goto pre, a2, a3;
  pre:
  assert user_inv_readable(Heap, Current)[Current, GAME.die_1]; // type:access tag:attribute_readable line:189 cid:405 fid:86
  assert user_inv_readable(Heap, Current)[Current, GAME.die_2]; // type:access tag:attribute_readable line:189 cid:405 fid:87
  assume ((Heap[Current, GAME.die_1]) != (Void)) && ((Heap[Current, GAME.die_2]) != (Void));
  assert user_inv_readable(Heap, Current)[Current, GAME.players]; // type:access tag:attribute_readable line:190 cid:405 fid:85
  assume (Heap[Current, GAME.players]) != (Void);
  assert user_inv_readable(Heap, Current)[Current, GAME.players]; // type:access tag:attribute_readable line:191 cid:405 fid:85
  assume Heap[Current, owns][Heap[Current, GAME.players]];
  assert user_inv_readable(Heap, Current)[Current, GAME.players]; // type:access tag:attribute_readable line:192 cid:405 fid:85
  assert {:subsumption 0} (Heap[Current, GAME.players]) != (Void); // type:attached tag:owns_def line:192
  assert user_inv_readable(Heap, Current)[Heap[Current, GAME.players], V_ARRAY^PLAYER^.sequence]; // type:access tag:attribute_readable line:192 cid:61 fid:90
  assert user_inv_readable(Heap, Current)[Current, GAME.players]; // type:access tag:attribute_readable line:192 cid:405 fid:85
  assert user_inv_readable(Heap, Current)[Current, GAME.die_1]; // type:access tag:attribute_readable line:192 cid:405 fid:86
  assert user_inv_readable(Heap, Current)[Current, GAME.die_2]; // type:access tag:attribute_readable line:192 cid:405 fid:87
  assume Set#Equal(Heap[Current, owns], Set#Union(Seq#Range(Heap[Heap[Current, GAME.players], V_ARRAY^PLAYER^.sequence]), Set#Extended(Set#Extended(Set#Singleton(Heap[Current, GAME.players]), Heap[Current, GAME.die_1]), Heap[Current, GAME.die_2])));
  assert user_inv_readable(Heap, Current)[Current, GAME.players]; // type:access tag:attribute_readable line:193 cid:405 fid:85
  assert {:subsumption 0} (Heap[Current, GAME.players]) != (Void); // type:attached tag:players_bounds line:193
  assert user_inv_readable(Heap, Current)[Heap[Current, GAME.players], V_ARRAY^PLAYER^.lower_]; // type:access tag:attribute_readable line:193 cid:61 fid:95
  assert user_inv_readable(Heap, Current)[Current, GAME.players]; // type:access tag:attribute_readable line:193 cid:405 fid:85
  assert {:subsumption 0} (Heap[Current, GAME.players]) != (Void); // type:attached tag:players_bounds line:193
  assert user_inv_readable(Heap, Current)[Heap[Current, GAME.players], V_ARRAY^PLAYER^.sequence]; // type:access tag:attribute_readable line:193 cid:61 fid:90
  assert user_inv_readable(Heap, Current)[Current, GAME.players]; // type:access tag:attribute_readable line:193 cid:405 fid:85
  assert {:subsumption 0} (Heap[Current, GAME.players]) != (Void); // type:attached tag:players_bounds line:193
  assert user_inv_readable(Heap, Current)[Heap[Current, GAME.players], V_ARRAY^PLAYER^.sequence]; // type:access tag:attribute_readable line:193 cid:61 fid:90
  assume ((Heap[Heap[Current, GAME.players], V_ARRAY^PLAYER^.lower_]) == (1)) && ((2) <= (Seq#Length(Heap[Heap[Current, GAME.players], V_ARRAY^PLAYER^.sequence]))) && ((Seq#Length(Heap[Heap[Current, GAME.players], V_ARRAY^PLAYER^.sequence])) <= (6));
  assert user_inv_readable(Heap, Current)[Current, GAME.players]; // type:access tag:attribute_readable line:194 cid:405 fid:85
  assert {:subsumption 0} (Heap[Current, GAME.players]) != (Void); // type:attached tag:players_nonvoid line:194
  assert user_inv_readable(Heap, Current)[Heap[Current, GAME.players], V_ARRAY^PLAYER^.sequence]; // type:access tag:attribute_readable line:194 cid:61 fid:90
  assume Seq#NonNull(Heap[Heap[Current, GAME.players], V_ARRAY^PLAYER^.sequence]);
  assert user_inv_readable(Heap, Current)[Current, GAME.players]; // type:access tag:attribute_readable line:195 cid:405 fid:85
  assert {:subsumption 0} (Heap[Current, GAME.players]) != (Void); // type:attached tag:players_distinct line:195
  assert user_inv_readable(Heap, Current)[Heap[Current, GAME.players], V_ARRAY^PLAYER^.sequence]; // type:access tag:attribute_readable line:195 cid:61 fid:90
  assume Seq#NoDuplicates(Heap[Heap[Current, GAME.players], V_ARRAY^PLAYER^.sequence]);
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

procedure create.GAME.make(Current: ref, n: int);
  free requires attached_exact(Heap, Current, GAME); // info:type property for argument Current
  free requires is_integer_32(n); // info:type property for argument n
  modifies Heap;
  requires ((2) <= (n)) && ((n) <= (6)); // type:pre tag:n_in_bounds line:18
  ensures (Heap[Current, GAME.winner]) == (Void); // type:post tag:not_yet_played line:57
  ensures (Heap[Current, GAME.players]) != (Void); // type:attached tag:fair_start line:58
  ensures (forall i_40: ref :: (Seq#Range(Heap[Heap[Current, GAME.players], V_ARRAY^PLAYER^.sequence])[i_40]) ==> ((Heap[i_40, PLAYER.position]) == (1))); // type:post tag:fair_start line:58
  requires (forall <T9> $f: Field T9 :: (($f) != (allocated)) ==> ((Heap[Current, $f]) == (Default($f))));
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.GAME.make(Heap, Current, n), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.GAME.make(old(Heap), Current, n));
  free ensures HeapSucc(old(Heap), Heap);
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts



implementation create.GAME.make(Current: ref, n: int)
{
  var temp_41: ref;
  var PreLoopHeap_45: HeapType;
  var LoopFrame_46: Frame;
  var LoopWritable_47: Frame;
  var variant_51: int;
  var temp_52: ref;
  var temp_53: ref;
  var temp_54: ref;
  var temp_55: ref;
  var temp_56: ref;
  var temp_57: ref;
  var temp_58: ref;
  var temp_59: ref;
  var temp_60: ref;
  var local1: int where is_integer_32(local1);
  var local2: ref where detachable(Heap, local2, PLAYER);

  init_locals:
  temp_41 := Void;
  variant_51 := 0;
  temp_52 := Void;
  temp_53 := Void;
  temp_54 := Void;
  temp_55 := Void;
  temp_56 := Void;
  temp_57 := Void;
  temp_58 := Void;
  temp_59 := Void;
  temp_60 := Void;
  local1 := 0;
  local2 := Void;

  entry:
  assume {:captureState "create.GAME.make"} true;
  // /home/caf/temp/comcom/repo-boardgame1/game.e:23
  // create players.make (1, n)
  call temp_41 := allocate(V_ARRAY^PLAYER^); // line:-1
  call create.V_ARRAY^PLAYER^.make(temp_41, 1, n); // line:23 cid:61 rid:3422
  call update_heap(Current, GAME.players, temp_41); // line:23
  // /home/caf/temp/comcom/repo-boardgame1/game.e:25
  // i := 1
  local1 := 1;
  PreLoopHeap_45 := Heap;
  havoc LoopFrame_46;
  assume (forall <T10> $o: ref, $f: Field T10 :: { LoopFrame_46[$o, $f] } (LoopFrame_46[$o, $f]) <==> (($o) == (Heap[Current, GAME.players])));
  assert {:subsumption 0} Frame#Subset(LoopFrame_46, writable); // type:check tag:frame_writable line:41
  havoc LoopWritable_47;
  assume Frame#Subset(LoopFrame_46, LoopWritable_47);
  assume closed_under_domains(LoopWritable_47, Heap);
  goto loop_head_42;
  loop_head_42:
  // /home/caf/temp/comcom/repo-boardgame1/game.e:27
  // players.is_fully_writable and players.is_wrapped
  assert {:subsumption 0} (Heap[Current, GAME.players]) != (Void); // type:attached line:27
  assert {:subsumption 0} (Heap[Current, GAME.players]) != (Void); // type:attached line:27
  assert (has_whole_object(LoopWritable_47, Heap[Current, GAME.players])) && (is_wrapped(Heap, Heap[Current, GAME.players])); // type:loop_inv line:27
  // /home/caf/temp/comcom/repo-boardgame1/game.e:28
  // inv_only ("players_bounds")
  assert GAME#I#players_bounds.filtered_inv(Heap, Current); // type:loop_inv line:28
  // /home/caf/temp/comcom/repo-boardgame1/game.e:29
  // players.observers = []
  assert {:subsumption 0} (Heap[Current, GAME.players]) != (Void); // type:attached line:29
  assert Set#Equal(Heap[Heap[Current, GAME.players], observers], Set#Empty()); // type:loop_inv line:29
  // /home/caf/temp/comcom/repo-boardgame1/game.e:30
  // 1 <=  i and i <= players.count + 1
  assert {:subsumption 0} (Heap[Current, GAME.players]) != (Void); // type:attached line:30
  assert pre.fun.V_ARRAY^PLAYER^.count(Heap, Heap[Current, GAME.players]); // type:check tag:function_precondition line:30 cid:61 rid:3382
  assert ((1) <= (local1)) && ((local1) <= ((fun.V_ARRAY^PLAYER^.count(Heap, Heap[Current, GAME.players])) + (1))); // type:loop_inv line:30
  // /home/caf/temp/comcom/repo-boardgame1/game.e:31
  // across 1 |..| (i-1) as k all
  assert {:subsumption 0} (Heap[Current, GAME.players]) != (Void); // type:attached line:31
  assert (forall i_48: int :: (((1) <= (i_48)) && ((i_48) <= ((local1) - (1)))) ==> (pre.fun.MML_SEQUENCE^PLAYER^.item(Heap[Heap[Current, GAME.players], V_ARRAY^PLAYER^.sequence], i_48))); // type:check tag:function_precondition line:31 cid:125 rid:3286
  assert {:subsumption 0} (Heap[Current, GAME.players]) != (Void); // type:attached line:31
  assert (forall i_48: int :: (((1) <= (i_48)) && ((i_48) <= ((local1) - (1)))) ==> (pre.fun.MML_SEQUENCE^PLAYER^.item(Heap[Heap[Current, GAME.players], V_ARRAY^PLAYER^.sequence], i_48))); // type:check tag:function_precondition line:31 cid:125 rid:3286
  assert (forall i_48: int :: (((1) <= (i_48)) && ((i_48) <= ((local1) - (1)))) ==> ((Seq#Item(Heap[Heap[Current, GAME.players], V_ARRAY^PLAYER^.sequence], i_48)) != (Void))); // type:attached line:31
  assert {:subsumption 0} (Heap[Current, GAME.players]) != (Void); // type:attached line:31
  assert (forall i_48: int :: (((1) <= (i_48)) && ((i_48) <= ((local1) - (1)))) ==> (pre.fun.MML_SEQUENCE^PLAYER^.item(Heap[Heap[Current, GAME.players], V_ARRAY^PLAYER^.sequence], i_48))); // type:check tag:function_precondition line:31 cid:125 rid:3286
  assert (forall i_48: int :: (((1) <= (i_48)) && ((i_48) <= ((local1) - (1)))) ==> ((Seq#Item(Heap[Heap[Current, GAME.players], V_ARRAY^PLAYER^.sequence], i_48)) != (Void))); // type:attached line:31
  assert {:subsumption 0} (Heap[Current, GAME.players]) != (Void); // type:attached line:31
  assert (forall i_48: int :: (((1) <= (i_48)) && ((i_48) <= ((local1) - (1)))) ==> (pre.fun.MML_SEQUENCE^PLAYER^.item(Heap[Heap[Current, GAME.players], V_ARRAY^PLAYER^.sequence], i_48))); // type:check tag:function_precondition line:31 cid:125 rid:3286
  assert (forall i_48: int :: (((1) <= (i_48)) && ((i_48) <= ((local1) - (1)))) ==> ((Seq#Item(Heap[Heap[Current, GAME.players], V_ARRAY^PLAYER^.sequence], i_48)) != (Void))); // type:attached line:31
  assert (forall i_48: int :: (((1) <= (i_48)) && ((i_48) <= ((local1) - (1)))) ==> (((Seq#Item(Heap[Heap[Current, GAME.players], V_ARRAY^PLAYER^.sequence], i_48)) != (Void)) && (is_wrapped(Heap, Seq#Item(Heap[Heap[Current, GAME.players], V_ARRAY^PLAYER^.sequence], i_48))) && (!(old(Heap)[Seq#Item(Heap[Heap[Current, GAME.players], V_ARRAY^PLAYER^.sequence], i_48), allocated])) && ((Heap[Seq#Item(Heap[Heap[Current, GAME.players], V_ARRAY^PLAYER^.sequence], i_48), PLAYER.position]) == (1)))); // type:loop_inv line:31
  // /home/caf/temp/comcom/repo-boardgame1/game.e:37
  // across 1 |..| (i-1) as j all
  assert (true) ==> ((Heap[Current, GAME.players]) != (Void)); // type:attached line:37
  assert (forall i_49: int :: (((1) <= (i_49)) && ((i_49) <= ((local1) - (1)))) ==> ((true) ==> (pre.fun.MML_SEQUENCE^PLAYER^.item(Heap[Heap[Current, GAME.players], V_ARRAY^PLAYER^.sequence], i_49)))); // type:check tag:function_precondition line:37 cid:125 rid:3286
  assert (true) ==> ((Heap[Current, GAME.players]) != (Void)); // type:attached line:37
  assert (forall i_49: int :: (((1) <= (i_49)) && ((i_49) <= ((local1) - (1)))) ==> ((forall i_50: int :: (((1) <= (i_50)) && ((i_50) <= ((local1) - (1)))) ==> (((i_49) != (i_50)) ==> (pre.fun.MML_SEQUENCE^PLAYER^.item(Heap[Heap[Current, GAME.players], V_ARRAY^PLAYER^.sequence], i_50)))))); // type:check tag:function_precondition line:37 cid:125 rid:3286
  assert (forall i_49: int :: (((1) <= (i_49)) && ((i_49) <= ((local1) - (1)))) ==> ((forall i_50: int :: (((1) <= (i_50)) && ((i_50) <= ((local1) - (1)))) ==> (((i_49) != (i_50)) ==> ((Seq#Item(Heap[Heap[Current, GAME.players], V_ARRAY^PLAYER^.sequence], i_49)) != (Seq#Item(Heap[Heap[Current, GAME.players], V_ARRAY^PLAYER^.sequence], i_50))))))); // type:loop_inv line:37
  assume HeapSucc(PreLoopHeap_45, Heap);
  assume same_outside(PreLoopHeap_45, Heap, LoopFrame_46);
  assume global(Heap);
  // /home/caf/temp/comcom/repo-boardgame1/game.e:-1
  assert {:subsumption 0} (Heap[Current, GAME.players]) != (Void); // type:attached line:-1
  assert pre.fun.V_ARRAY^PLAYER^.count(Heap, Heap[Current, GAME.players]); // type:check tag:function_precondition line:-1 cid:61 rid:3382
  goto loop_body_43, loop_end_44;
  loop_body_43:
  assume !((local1) > (fun.V_ARRAY^PLAYER^.count(Heap, Heap[Current, GAME.players])));
  variant_51 := (fun.V_ARRAY^PLAYER^.count(Heap, Heap[Current, GAME.players])) - (local1);
  // /home/caf/temp/comcom/repo-boardgame1/game.e:45
  // create p.make ("Player" + i.out_)
  call temp_52 := allocate(PLAYER); // line:-1
  call temp_53 := allocate(V_STRING); // line:-1
  call create.V_STRING.init(temp_53, Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Singleton(80), 108), 97), 121), 101), 114));
  assert {:subsumption 0} (temp_53) != (Void); // type:attached line:45
  assert {:subsumption 0} Frame#Subset(modify.INTEGER_32.out_(Heap, local1), LoopWritable_47); // type:check tag:frame_writable line:45
  call temp_54 := INTEGER_32.out_(local1); // line:45 cid:23 rid:31
  assert {:subsumption 0} Frame#Subset(modify.V_STRING.plus(Heap, temp_53, temp_54), LoopWritable_47); // type:check tag:frame_writable line:45
  call temp_55 := V_STRING.plus(temp_53, temp_54); // line:45 cid:130 rid:810
  assert {:subsumption 0} Frame#Subset(modify.PLAYER.make(Heap, temp_52, temp_55), LoopWritable_47); // type:check tag:frame_writable line:45
  call create.PLAYER.make(temp_52, temp_55); // line:45 cid:404 rid:5416
  local2 := temp_52;
  // /home/caf/temp/comcom/repo-boardgame1/game.e:46
  // p.set_position (1)
  assert {:subsumption 0} (local2) != (Void); // type:attached line:46
  assert {:subsumption 0} Frame#Subset(modify.PLAYER.set_position(Heap, local2, 1), LoopWritable_47); // type:check tag:frame_writable line:46
  call PLAYER.set_position(local2, 1); // line:46 cid:404 rid:5419
  // /home/caf/temp/comcom/repo-boardgame1/game.e:47
  // players [i] := p
  assert {:subsumption 0} (Heap[Current, GAME.players]) != (Void); // type:attached line:47
  assert {:subsumption 0} Frame#Subset(modify.V_ARRAY^PLAYER^.put(Heap, Heap[Current, GAME.players], local2, local1), LoopWritable_47); // type:check tag:frame_writable line:47
  call V_ARRAY^PLAYER^.put(Heap[Current, GAME.players], local2, local1); // line:47 cid:61 rid:3403
  // /home/caf/temp/comcom/repo-boardgame1/game.e:48
  // check p.inv_only ("name_not_void", "owns_def") end
  assert {:subsumption 0} (local2) != (Void); // type:attached line:48
  assert PLAYER#I#name_not_void#owns_def.filtered_inv(Heap, local2); // type:check line:48
  // /home/caf/temp/comcom/repo-boardgame1/game.e:49
  // print (p.name + " joined the game.%N")
  assert {:subsumption 0} (local2) != (Void); // type:attached line:49
  assert {:subsumption 0} (Heap[local2, PLAYER.name]) != (Void); // type:attached line:49
  call temp_56 := allocate(V_STRING); // line:-1
  call create.V_STRING.init(temp_56, Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Singleton(32), 106), 111), 105), 110), 101), 100), 32), 116), 104), 101), 32), 103), 97), 109), 101), 46), 10));
  assert {:subsumption 0} Frame#Subset(modify.V_STRING.plus(Heap, Heap[local2, PLAYER.name], temp_56), LoopWritable_47); // type:check tag:frame_writable line:49
  call temp_57 := V_STRING.plus(Heap[local2, PLAYER.name], temp_56); // line:49 cid:130 rid:810
  assert {:subsumption 0} Frame#Subset(modify.GAME.print(Heap, Current, temp_57), LoopWritable_47); // type:check tag:frame_writable line:49
  call GAME.print(Current, temp_57); // line:49 cid:405 rid:33
  // /home/caf/temp/comcom/repo-boardgame1/game.e:50
  // i := i + 1
  local1 := (local1) + (1);
  // /home/caf/temp/comcom/repo-boardgame1/game.e:45
  // create p.make ("Player" + i.out_)
  assert {:subsumption 0} ((((fun.V_ARRAY^PLAYER^.count(Heap, Heap[Current, GAME.players])) - (local1)) <= (variant_51)) && ((variant_51) <= ((fun.V_ARRAY^PLAYER^.count(Heap, Heap[Current, GAME.players])) - (local1)))) || ((0) <= (variant_51)); // type:termination tag:bounded line:45 varid:1
  assert {:subsumption 0} (((fun.V_ARRAY^PLAYER^.count(Heap, Heap[Current, GAME.players])) - (local1)) <= (variant_51)) && (!((variant_51) <= ((fun.V_ARRAY^PLAYER^.count(Heap, Heap[Current, GAME.players])) - (local1)))); // type:termination tag:variant_decreases line:45
  goto loop_head_42;
  loop_end_44:
  assume (local1) > (fun.V_ARRAY^PLAYER^.count(Heap, Heap[Current, GAME.players]));
  // /home/caf/temp/comcom/repo-boardgame1/game.e:52
  // print ("%N")
  call temp_58 := allocate(V_STRING);
  call create.V_STRING.init(temp_58, Seq#Singleton(10));
  call GAME.print(Current, temp_58); // line:52 cid:405 rid:33
  // /home/caf/temp/comcom/repo-boardgame1/game.e:54
  // create die_1.roll
  call temp_59 := allocate(DIE); // line:-1
  call create.DIE.roll(temp_59); // line:54 cid:406 rid:5404
  call update_heap(Current, GAME.die_1, temp_59); // line:54
  // /home/caf/temp/comcom/repo-boardgame1/game.e:55
  // create die_2.roll
  call temp_60 := allocate(DIE); // line:-1
  call create.DIE.roll(temp_60); // line:55 cid:406 rid:5404
  call update_heap(Current, GAME.die_2, temp_60); // line:55
  if (modify.GAME.make(Heap, Current, n)[Current, owns]) {
    call update_heap(Current, owns, GAME.owns.static(Heap, Current)); // default:owns line:59
  }
  if (*) {
    assert ((Heap[Current, GAME.die_1]) != (Void)) && ((Heap[Current, GAME.die_2]) != (Void)); // type:inv tag:dice_exist line:124 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert (Heap[Current, GAME.players]) != (Void); // type:inv tag:players_exist line:124 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Heap[Current, owns][Heap[Current, GAME.players]]; // type:inv tag:owns_players line:124 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#Equal(Heap[Current, owns], Set#Union(Seq#Range(Heap[Heap[Current, GAME.players], V_ARRAY^PLAYER^.sequence]), Set#Extended(Set#Extended(Set#Singleton(Heap[Current, GAME.players]), Heap[Current, GAME.die_1]), Heap[Current, GAME.die_2]))); // type:inv tag:owns_def line:124 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert ((Heap[Heap[Current, GAME.players], V_ARRAY^PLAYER^.lower_]) == (1)) && ((2) <= (Seq#Length(Heap[Heap[Current, GAME.players], V_ARRAY^PLAYER^.sequence]))) && ((Seq#Length(Heap[Heap[Current, GAME.players], V_ARRAY^PLAYER^.sequence])) <= (6)); // type:inv tag:players_bounds line:124 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Seq#NonNull(Heap[Heap[Current, GAME.players], V_ARRAY^PLAYER^.sequence]); // type:inv tag:players_nonvoid line:124 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Seq#NoDuplicates(Heap[Heap[Current, GAME.players], V_ARRAY^PLAYER^.sequence]); // type:inv tag:players_distinct line:124 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, observers]); // type:inv tag:default_observers line:124 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, subjects]); // type:inv tag:default_subjects line:124 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert admissibility2(Heap, Current); // type:inv tag:A2 line:124 cid:1 rid:55
    assume false;
  }
  call wrap(Current); // default:wrapping cid:1 rid:55 line:59
}

procedure GAME.play(Current: ref);
  free requires attached_exact(Heap, Current, GAME); // info:type property for argument Current
  modifies Heap;
  requires (Heap[Current, GAME.winner]) == (Void); // type:pre tag:not_yet_played line:66
  requires (Heap[Current, GAME.players]) != (Void); // type:attached tag:fair_start line:67
  requires (forall i_61: ref :: (Seq#Range(Heap[Heap[Current, GAME.players], V_ARRAY^PLAYER^.sequence])[i_61]) ==> ((Heap[i_61, PLAYER.position]) == (1))); // type:pre tag:fair_start line:67
  ensures (Heap[Current, GAME.players]) != (Void); // type:attached line:121
  ensures (old(Heap)[Current, GAME.players]) != (Void); // type:attached line:121
  ensures Seq#Equal(Heap[Heap[Current, GAME.players], V_ARRAY^PLAYER^.sequence], old(Heap)[old(Heap)[Current, GAME.players], V_ARRAY^PLAYER^.sequence]); // type:post line:121
  ensures (Heap[Current, GAME.winner]) != (Void); // type:attached tag:is_winner line:122
  ensures (Heap[Heap[Current, GAME.winner], PLAYER.position]) > (40); // type:post tag:is_winner line:122
  ensures ((Heap[Current, GAME.winner]) != (Void)) && (Seq#Has(Heap[Heap[Current, GAME.players], V_ARRAY^PLAYER^.sequence], Heap[Current, GAME.winner])); // type:post tag:has_winner line:123
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.GAME.play(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.GAME.play(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);
  requires is_wrapped(Heap, Current); // type:pre tag:default_is_wrapped default:contracts
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts



function { :inline } variant.GAME.play.1(heap: HeapType, current: ref) returns (int) {
  0
}

implementation GAME.play(Current: ref)
{
  var temp_65: ref;
  var PreLoopHeap_66: HeapType;
  var temp_69: ref;
  var temp_70: ref;
  var temp_71: ref;
  var temp_72: ref;
  var temp_73: ref;
  var PreLoopHeap_77: HeapType;
  var variant_80: int;
  var temp_81: ref;
  var temp_82: ref;
  var temp_83: ref;
  var local1: int where is_integer_32(local1);
  var local2: int where is_integer_32(local2);

  init_locals:
  temp_65 := Void;
  temp_69 := Void;
  temp_70 := Void;
  temp_71 := Void;
  temp_72 := Void;
  temp_73 := Void;
  variant_80 := 0;
  temp_81 := Void;
  temp_82 := Void;
  temp_83 := Void;
  local1 := 0;
  local2 := 0;

  entry:
  assume {:captureState "GAME.play"} true;
  call unwrap(Current); // default:wrapping cid:1 rid:57 line:63
  assume GAME.user_inv(Heap, Current);
  // /home/caf/temp/comcom/repo-boardgame1/game.e:75
  // round := 1
  local1 := 1;
  // /home/caf/temp/comcom/repo-boardgame1/game.e:76
  // print ("The game begins.%N")
  call temp_65 := allocate(V_STRING);
  call create.V_STRING.init(temp_65, Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Singleton(84), 104), 101), 32), 103), 97), 109), 101), 32), 98), 101), 103), 105), 110), 115), 46), 10));
  call GAME.print(Current, temp_65); // line:76 cid:405 rid:33
  // /home/caf/temp/comcom/repo-boardgame1/game.e:77
  // print_board
  call GAME.print_board(Current); // line:77 cid:405 rid:5415
  PreLoopHeap_66 := Heap;
  goto loop_head_62;
  loop_head_62:
  // /home/caf/temp/comcom/repo-boardgame1/game.e:79
  // players.sequence = players.sequence.old_
  assert {:subsumption 0} (Heap[Current, GAME.players]) != (Void); // type:attached line:79
  assert {:subsumption 0} (old(Heap)[Current, GAME.players]) != (Void); // type:attached line:79
  assert Seq#Equal(Heap[Heap[Current, GAME.players], V_ARRAY^PLAYER^.sequence], old(Heap)[old(Heap)[Current, GAME.players], V_ARRAY^PLAYER^.sequence]); // type:loop_inv line:79
  // /home/caf/temp/comcom/repo-boardgame1/game.e:80
  // inv_only("players_bounds", "owns_def")
  assert GAME#I#players_bounds#owns_def.filtered_inv(Heap, Current); // type:loop_inv line:80
  // /home/caf/temp/comcom/repo-boardgame1/game.e:81
  // across owns as o all o.item.is_wrapped end
  assert (forall i_67: ref :: (Heap[Current, owns][i_67]) ==> (is_wrapped(Heap, i_67))); // type:loop_inv line:81
  // /home/caf/temp/comcom/repo-boardgame1/game.e:82
  // across owns as o all o.item.is_fully_writable end
  assert (forall i_68: ref :: (Heap[Current, owns][i_68]) ==> (has_whole_object(writable, i_68))); // type:loop_inv line:82
  // /home/caf/temp/comcom/repo-boardgame1/game.e:83
  // players.inv_only ("lower_definition", "upper_definition")
  assert {:subsumption 0} (Heap[Current, GAME.players]) != (Void); // type:attached line:83
  assert V_ARRAY^PLAYER^#I#lower_definition#upper_definition.filtered_inv(Heap, Heap[Current, GAME.players]); // type:loop_inv line:83
  // /home/caf/temp/comcom/repo-boardgame1/game.e:85
  // is_winner: winner /= Void implies winner.position > Square_count
  assert {:subsumption 0} ((Heap[Current, GAME.winner]) != (Void)) ==> ((Heap[Current, GAME.winner]) != (Void)); // type:attached line:85
  assert ((Heap[Current, GAME.winner]) != (Void)) ==> ((Heap[Heap[Current, GAME.winner], PLAYER.position]) > (40)); // type:loop_inv tag:is_winner line:85
  // /home/caf/temp/comcom/repo-boardgame1/game.e:86
  // has_winner: winner /= Void implies players.sequence.has (winner)
  assert {:subsumption 0} ((Heap[Current, GAME.winner]) != (Void)) ==> ((Heap[Current, GAME.players]) != (Void)); // type:attached line:86
  assert ((Heap[Current, GAME.winner]) != (Void)) ==> (Seq#Has(Heap[Heap[Current, GAME.players], V_ARRAY^PLAYER^.sequence], Heap[Current, GAME.winner])); // type:loop_inv tag:has_winner line:86
  assume HeapSucc(PreLoopHeap_66, Heap);
  assume same_outside(old(Heap), Heap, modify.GAME.play(old(Heap), Current));
  assume global(Heap);
  // /home/caf/temp/comcom/repo-boardgame1/game.e:-1
  goto loop_body_63, loop_end_64;
  loop_body_63:
  assume !((Heap[Current, GAME.winner]) != (Void));
  // /home/caf/temp/comcom/repo-boardgame1/game.e:92
  // check players.is_wrapped end
  assert {:subsumption 0} (Heap[Current, GAME.players]) != (Void); // type:attached line:92
  assert is_wrapped(Heap, Heap[Current, GAME.players]); // type:check line:92
  // /home/caf/temp/comcom/repo-boardgame1/game.e:93
  // print ("%NRound #" + round.out_ + "%N%N")
  call temp_69 := allocate(V_STRING); // line:-1
  call create.V_STRING.init(temp_69, Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Extended(Seq#Singleton(10), 82), 111), 117), 110), 100), 32), 35));
  assert {:subsumption 0} (temp_69) != (Void); // type:attached line:93
  call temp_70 := INTEGER_32.out_(local1); // line:93 cid:23 rid:31
  call temp_71 := V_STRING.plus(temp_69, temp_70); // line:93 cid:130 rid:810
  assert {:subsumption 0} (temp_71) != (Void); // type:attached line:93
  call temp_72 := allocate(V_STRING); // line:-1
  call create.V_STRING.init(temp_72, Seq#Extended(Seq#Singleton(10), 10));
  call temp_73 := V_STRING.plus(temp_71, temp_72); // line:93 cid:130 rid:810
  call GAME.print(Current, temp_73); // line:93 cid:405 rid:33
  // /home/caf/temp/comcom/repo-boardgame1/game.e:95
  // i := 1
  local2 := 1;
  PreLoopHeap_77 := Heap;
  goto loop_head_74;
  loop_head_74:
  // /home/caf/temp/comcom/repo-boardgame1/game.e:97
  // players.sequence = players.sequence.old_
  assert {:subsumption 0} (Heap[Current, GAME.players]) != (Void); // type:attached line:97
  assert {:subsumption 0} (old(Heap)[Current, GAME.players]) != (Void); // type:attached line:97
  assert Seq#Equal(Heap[Heap[Current, GAME.players], V_ARRAY^PLAYER^.sequence], old(Heap)[old(Heap)[Current, GAME.players], V_ARRAY^PLAYER^.sequence]); // type:loop_inv line:97
  // /home/caf/temp/comcom/repo-boardgame1/game.e:98
  // inv_only("players_bounds", "owns_def")
  assert GAME#I#players_bounds#owns_def.filtered_inv(Heap, Current); // type:loop_inv line:98
  // /home/caf/temp/comcom/repo-boardgame1/game.e:99
  // across owns as o all o.item.is_wrapped end
  assert (forall i_78: ref :: (Heap[Current, owns][i_78]) ==> (is_wrapped(Heap, i_78))); // type:loop_inv line:99
  // /home/caf/temp/comcom/repo-boardgame1/game.e:100
  // across owns as o all o.item.is_fully_writable end
  assert (forall i_79: ref :: (Heap[Current, owns][i_79]) ==> (has_whole_object(writable, i_79))); // type:loop_inv line:100
  // /home/caf/temp/comcom/repo-boardgame1/game.e:101
  // players.inv_only ("lower_definition", "upper_definition")
  assert {:subsumption 0} (Heap[Current, GAME.players]) != (Void); // type:attached line:101
  assert V_ARRAY^PLAYER^#I#lower_definition#upper_definition.filtered_inv(Heap, Heap[Current, GAME.players]); // type:loop_inv line:101
  // /home/caf/temp/comcom/repo-boardgame1/game.e:103
  // 1 <= i and i <= players.count + 1
  assert {:subsumption 0} (Heap[Current, GAME.players]) != (Void); // type:attached line:103
  assert pre.fun.V_ARRAY^PLAYER^.count(Heap, Heap[Current, GAME.players]); // type:check tag:function_precondition line:103 cid:61 rid:3382
  assert ((1) <= (local2)) && ((local2) <= ((fun.V_ARRAY^PLAYER^.count(Heap, Heap[Current, GAME.players])) + (1))); // type:loop_inv line:103
  // /home/caf/temp/comcom/repo-boardgame1/game.e:104
  // is_winner: winner /= Void implies winner.position > Square_count
  assert {:subsumption 0} ((Heap[Current, GAME.winner]) != (Void)) ==> ((Heap[Current, GAME.winner]) != (Void)); // type:attached line:104
  assert ((Heap[Current, GAME.winner]) != (Void)) ==> ((Heap[Heap[Current, GAME.winner], PLAYER.position]) > (40)); // type:loop_inv tag:is_winner line:104
  // /home/caf/temp/comcom/repo-boardgame1/game.e:105
  // has_winner: winner /= Void implies players.sequence.has (winner)
  assert {:subsumption 0} ((Heap[Current, GAME.winner]) != (Void)) ==> ((Heap[Current, GAME.players]) != (Void)); // type:attached line:105
  assert ((Heap[Current, GAME.winner]) != (Void)) ==> (Seq#Has(Heap[Heap[Current, GAME.players], V_ARRAY^PLAYER^.sequence], Heap[Current, GAME.winner])); // type:loop_inv tag:has_winner line:105
  assume HeapSucc(PreLoopHeap_77, Heap);
  assume same_outside(old(Heap), Heap, modify.GAME.play(old(Heap), Current));
  assume global(Heap);
  // /home/caf/temp/comcom/repo-boardgame1/game.e:-1
  assert {:subsumption 0} (!((Heap[Current, GAME.winner]) != (Void))) ==> ((Heap[Current, GAME.players]) != (Void)); // type:attached line:-1
  assert (!((Heap[Current, GAME.winner]) != (Void))) ==> (pre.fun.V_ARRAY^PLAYER^.count(Heap, Heap[Current, GAME.players])); // type:check tag:function_precondition line:-1 cid:61 rid:3382
  goto loop_body_75, loop_end_76;
  loop_body_75:
  assume !(((Heap[Current, GAME.winner]) != (Void)) || ((local2) > (fun.V_ARRAY^PLAYER^.count(Heap, Heap[Current, GAME.players]))));
  // /home/caf/temp/comcom/repo-boardgame1/game.e:115
  // players.count - i
  variant_80 := (fun.V_ARRAY^PLAYER^.count(Heap, Heap[Current, GAME.players])) - (local2);
  // /home/caf/temp/comcom/repo-boardgame1/game.e:109
  // players [i].play (die_1, die_2)
  assert {:subsumption 0} (Heap[Current, GAME.players]) != (Void); // type:attached line:109
  call temp_81 := V_ARRAY^PLAYER^.item(Heap[Current, GAME.players], local2); // line:109 cid:61 rid:3389
  assert {:subsumption 0} (temp_81) != (Void); // type:attached line:109
  call PLAYER.play(temp_81, Heap[Current, GAME.die_1], Heap[Current, GAME.die_2]); // line:109 cid:404 rid:5420
  // /home/caf/temp/comcom/repo-boardgame1/game.e:110
  // if players [i].position > Square_count then
  assert {:subsumption 0} (Heap[Current, GAME.players]) != (Void); // type:attached line:110
  call temp_82 := V_ARRAY^PLAYER^.item(Heap[Current, GAME.players], local2); // line:110 cid:61 rid:3389
  assert {:subsumption 0} (temp_82) != (Void); // type:attached line:110
  if ((Heap[temp_82, PLAYER.position]) > (40)) {
    // /home/caf/temp/comcom/repo-boardgame1/game.e:111
    // winner := players [i]
    assert {:subsumption 0} (Heap[Current, GAME.players]) != (Void); // type:attached line:111
    call temp_83 := V_ARRAY^PLAYER^.item(Heap[Current, GAME.players], local2); // line:111 cid:61 rid:3389
    call update_heap(Current, GAME.winner, temp_83); // line:111
  }
  // /home/caf/temp/comcom/repo-boardgame1/game.e:113
  // i := i + 1
  local2 := (local2) + (1);
  // /home/caf/temp/comcom/repo-boardgame1/game.e:115
  // players.count - i
  assert {:subsumption 0} ((((fun.V_ARRAY^PLAYER^.count(Heap, Heap[Current, GAME.players])) - (local2)) <= (variant_80)) && ((variant_80) <= ((fun.V_ARRAY^PLAYER^.count(Heap, Heap[Current, GAME.players])) - (local2)))) || ((0) <= (variant_80)); // type:termination tag:bounded line:115 varid:1
  assert {:subsumption 0} (((fun.V_ARRAY^PLAYER^.count(Heap, Heap[Current, GAME.players])) - (local2)) <= (variant_80)) && (!((variant_80) <= ((fun.V_ARRAY^PLAYER^.count(Heap, Heap[Current, GAME.players])) - (local2)))); // type:termination tag:variant_decreases line:115
  goto loop_head_74;
  loop_end_76:
  assume ((Heap[Current, GAME.winner]) != (Void)) || ((local2) > (fun.V_ARRAY^PLAYER^.count(Heap, Heap[Current, GAME.players])));
  // /home/caf/temp/comcom/repo-boardgame1/game.e:117
  // print_board
  call GAME.print_board(Current); // line:117 cid:405 rid:5415
  // /home/caf/temp/comcom/repo-boardgame1/game.e:118
  // round := round + 1
  local1 := (local1) + (1);
  // /home/caf/temp/comcom/repo-boardgame1/game.e:92
  // check players.is_wrapped end
  goto loop_head_62;
  loop_end_64:
  assume (Heap[Current, GAME.winner]) != (Void);
  if (modify.GAME.play(Heap, Current)[Current, owns]) {
    call update_heap(Current, owns, GAME.owns.static(Heap, Current)); // default:owns line:124
  }
  if (*) {
    assert ((Heap[Current, GAME.die_1]) != (Void)) && ((Heap[Current, GAME.die_2]) != (Void)); // type:inv tag:dice_exist line:124 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert (Heap[Current, GAME.players]) != (Void); // type:inv tag:players_exist line:124 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Heap[Current, owns][Heap[Current, GAME.players]]; // type:inv tag:owns_players line:124 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#Equal(Heap[Current, owns], Set#Union(Seq#Range(Heap[Heap[Current, GAME.players], V_ARRAY^PLAYER^.sequence]), Set#Extended(Set#Extended(Set#Singleton(Heap[Current, GAME.players]), Heap[Current, GAME.die_1]), Heap[Current, GAME.die_2]))); // type:inv tag:owns_def line:124 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert ((Heap[Heap[Current, GAME.players], V_ARRAY^PLAYER^.lower_]) == (1)) && ((2) <= (Seq#Length(Heap[Heap[Current, GAME.players], V_ARRAY^PLAYER^.sequence]))) && ((Seq#Length(Heap[Heap[Current, GAME.players], V_ARRAY^PLAYER^.sequence])) <= (6)); // type:inv tag:players_bounds line:124 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Seq#NonNull(Heap[Heap[Current, GAME.players], V_ARRAY^PLAYER^.sequence]); // type:inv tag:players_nonvoid line:124 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Seq#NoDuplicates(Heap[Heap[Current, GAME.players], V_ARRAY^PLAYER^.sequence]); // type:inv tag:players_distinct line:124 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, observers]); // type:inv tag:default_observers line:124 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, subjects]); // type:inv tag:default_subjects line:124 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert admissibility2(Heap, Current); // type:inv tag:A2 line:124 cid:1 rid:55
    assume false;
  }
  call wrap(Current); // default:wrapping cid:1 rid:55 line:124
}

procedure GAME.print_board(Current: ref);
  free requires attached_exact(Heap, Current, GAME); // info:type property for argument Current
  modifies Heap;
  requires GAME#I#players_bounds#owns_def.filtered_inv(Heap, Current); // type:pre line:156
  requires (Heap[Current, GAME.players]) != (Void); // type:attached line:157
  requires V_ARRAY^PLAYER^#I#lower_definition#upper_definition.filtered_inv(Heap, Heap[Current, GAME.players]); // type:pre line:157
  requires (forall i_84: ref :: (Heap[Current, owns][i_84]) ==> (is_wrapped(Heap, i_84))); // type:pre line:158
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.GAME.print_board(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.GAME.print_board(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);
  requires is_open(Heap, Current); // type:pre tag:default_is_open default:contracts
  ensures is_open(Heap, Current); // type:post tag:default_is_open default:contracts



function { :inline } variant.GAME.print_board.1(heap: HeapType, current: ref) returns (int) {
  0
}

implementation GAME.print_board(Current: ref)
{
  var temp_85: ref;
  var temp_86: ref;
  var temp_87: ref;
  var PreLoopHeap_91: HeapType;
  var variant_92: int;
  var PreLoopHeap_96: HeapType;
  var variant_97: int;
  var temp_98: ref;
  var temp_99: ref;
  var temp_100: ref;
  var local1: int where is_integer_32(local1);
  var local2: int where is_integer_32(local2);
  var local3: ref where detachable_exact(Heap, local3, V_STRING);

  init_locals:
  temp_85 := Void;
  temp_86 := Void;
  temp_87 := Void;
  variant_92 := 0;
  variant_97 := 0;
  temp_98 := Void;
  temp_99 := Void;
  temp_100 := Void;
  local1 := 0;
  local2 := 0;
  local3 := Void;

  entry:
  assume {:captureState "GAME.print_board"} true;
  // /home/caf/temp/comcom/repo-boardgame1/game.e:164
  // io.put_new_line
  call temp_85 := GAME.io(Current); // line:164 cid:405 rid:29
  assert {:subsumption 0} (temp_85) != (Void); // type:attached line:164
  call STD_FILES.put_new_line(temp_85); // line:164 cid:237 rid:370
  // /home/caf/temp/comcom/repo-boardgame1/game.e:165
  // board := "."
  call temp_86 := allocate(V_STRING); // line:-1
  call create.V_STRING.init(temp_86, Seq#Singleton(46));
  local3 := temp_86;
  // /home/caf/temp/comcom/repo-boardgame1/game.e:166
  // board.multiply (Square_count)
  assert {:subsumption 0} (local3) != (Void); // type:attached line:166
  call V_STRING.multiply(local3, 40); // line:166 cid:130 rid:804
  // /home/caf/temp/comcom/repo-boardgame1/game.e:167
  // print (board)
  call GAME.print(Current, local3); // line:167 cid:405 rid:33
  // /home/caf/temp/comcom/repo-boardgame1/game.e:168
  // io.put_new_line
  call temp_87 := GAME.io(Current); // line:168 cid:405 rid:29
  assert {:subsumption 0} (temp_87) != (Void); // type:attached line:168
  call STD_FILES.put_new_line(temp_87); // line:168 cid:237 rid:370
  // /home/caf/temp/comcom/repo-boardgame1/game.e:170
  // i := 1
  local1 := 1;
  PreLoopHeap_91 := Heap;
  goto loop_head_88;
  loop_head_88:
  assume HeapSucc(PreLoopHeap_91, Heap);
  assume same_outside(old(Heap), Heap, modify.GAME.print_board(old(Heap), Current));
  assume global(Heap);
  // /home/caf/temp/comcom/repo-boardgame1/game.e:-1
  assert {:subsumption 0} (Heap[Current, GAME.players]) != (Void); // type:attached line:-1
  assert pre.fun.V_ARRAY^PLAYER^.count(Heap, Heap[Current, GAME.players]); // type:check tag:function_precondition line:-1 cid:61 rid:3382
  goto loop_body_89, loop_end_90;
  loop_body_89:
  assume !((local1) > (fun.V_ARRAY^PLAYER^.count(Heap, Heap[Current, GAME.players])));
  variant_92 := (fun.V_ARRAY^PLAYER^.count(Heap, Heap[Current, GAME.players])) - (local1);
  // /home/caf/temp/comcom/repo-boardgame1/game.e:175
  // j := 1
  local2 := 1;
  PreLoopHeap_96 := Heap;
  goto loop_head_93;
  loop_head_93:
  assume HeapSucc(PreLoopHeap_96, Heap);
  assume same_outside(old(Heap), Heap, modify.GAME.print_board(old(Heap), Current));
  assume global(Heap);
  // /home/caf/temp/comcom/repo-boardgame1/game.e:-1
  assert {:subsumption 0} (Heap[Current, GAME.players]) != (Void); // type:attached line:-1
  assert pre.fun.V_ARRAY^PLAYER^.item(Heap, Heap[Current, GAME.players], local1); // type:check tag:function_precondition line:-1 cid:61 rid:3389
  assert {:subsumption 0} (fun.V_ARRAY^PLAYER^.item(Heap, Heap[Current, GAME.players], local1)) != (Void); // type:attached line:-1
  goto loop_body_94, loop_end_95;
  loop_body_94:
  assume !((local2) >= (Heap[fun.V_ARRAY^PLAYER^.item(Heap, Heap[Current, GAME.players], local1), PLAYER.position]));
  variant_97 := (Heap[fun.V_ARRAY^PLAYER^.item(Heap, Heap[Current, GAME.players], local1), PLAYER.position]) - (local2);
  // /home/caf/temp/comcom/repo-boardgame1/game.e:179
  // print (" ")
  call temp_98 := allocate(V_STRING);
  call create.V_STRING.init(temp_98, Seq#Singleton(32));
  call GAME.print(Current, temp_98); // line:179 cid:405 rid:33
  // /home/caf/temp/comcom/repo-boardgame1/game.e:180
  // j := j + 1
  local2 := (local2) + (1);
  // /home/caf/temp/comcom/repo-boardgame1/game.e:179
  // print (" ")
  assert {:subsumption 0} ((((Heap[fun.V_ARRAY^PLAYER^.item(Heap, Heap[Current, GAME.players], local1), PLAYER.position]) - (local2)) <= (variant_97)) && ((variant_97) <= ((Heap[fun.V_ARRAY^PLAYER^.item(Heap, Heap[Current, GAME.players], local1), PLAYER.position]) - (local2)))) || ((0) <= (variant_97)); // type:termination tag:bounded line:179 varid:1
  assert {:subsumption 0} (((Heap[fun.V_ARRAY^PLAYER^.item(Heap, Heap[Current, GAME.players], local1), PLAYER.position]) - (local2)) <= (variant_97)) && (!((variant_97) <= ((Heap[fun.V_ARRAY^PLAYER^.item(Heap, Heap[Current, GAME.players], local1), PLAYER.position]) - (local2)))); // type:termination tag:variant_decreases line:179
  goto loop_head_93;
  loop_end_95:
  assume (local2) >= (Heap[fun.V_ARRAY^PLAYER^.item(Heap, Heap[Current, GAME.players], local1), PLAYER.position]);
  // /home/caf/temp/comcom/repo-boardgame1/game.e:182
  // print (i.out_)
  call temp_99 := INTEGER_32.out_(local1); // line:182 cid:23 rid:31
  call GAME.print(Current, temp_99); // line:182 cid:405 rid:33
  // /home/caf/temp/comcom/repo-boardgame1/game.e:183
  // io.put_new_line
  call temp_100 := GAME.io(Current); // line:183 cid:405 rid:29
  assert {:subsumption 0} (temp_100) != (Void); // type:attached line:183
  call STD_FILES.put_new_line(temp_100); // line:183 cid:237 rid:370
  // /home/caf/temp/comcom/repo-boardgame1/game.e:184
  // i := i + 1
  local1 := (local1) + (1);
  // /home/caf/temp/comcom/repo-boardgame1/game.e:177
  // j >= players [i].position
  assert {:subsumption 0} ((((fun.V_ARRAY^PLAYER^.count(Heap, Heap[Current, GAME.players])) - (local1)) <= (variant_92)) && ((variant_92) <= ((fun.V_ARRAY^PLAYER^.count(Heap, Heap[Current, GAME.players])) - (local1)))) || ((0) <= (variant_92)); // type:termination tag:bounded line:177 varid:1
  assert {:subsumption 0} (((fun.V_ARRAY^PLAYER^.count(Heap, Heap[Current, GAME.players])) - (local1)) <= (variant_92)) && (!((variant_92) <= ((fun.V_ARRAY^PLAYER^.count(Heap, Heap[Current, GAME.players])) - (local1)))); // type:termination tag:variant_decreases line:177
  goto loop_head_88;
  loop_end_90:
  assume (local1) > (fun.V_ARRAY^PLAYER^.count(Heap, Heap[Current, GAME.players]));
}

const PLAYER.position: Field int;

axiom ((FieldId(PLAYER.position, PLAYER)) == (82));

axiom ((forall heap: HeapType, o: ref :: { heap[o, PLAYER.position] } ((IsHeap(heap)) && (attached(heap, o, PLAYER))) ==> (is_integer_32(heap[o, PLAYER.position]))));

axiom ((forall heap: HeapType, current: ref, v: int, o: ref :: { guard(heap, current, PLAYER.position, v, o) } (attached_exact(heap, current, PLAYER)) ==> ((guard(heap, current, PLAYER.position, v, o)) <==> ((user_inv(heap, o)) ==> (user_inv(heap[current, PLAYER.position := v], o))))));

axiom ((forall heap: HeapType, current: ref, v: int, o: ref :: { guard(heap, current, PLAYER.position, v, o) } (attached(heap, current, PLAYER)) ==> ((guard(heap, current, PLAYER.position, v, o)) ==> ((user_inv(heap, o)) ==> (user_inv(heap[current, PLAYER.position := v], o))))));

const PLAYER.name: Field (ref);

axiom ((FieldId(PLAYER.name, PLAYER)) == (81));

axiom ((forall heap: HeapType, o: ref :: { heap[o, PLAYER.name] } ((IsHeap(heap)) && (attached(heap, o, PLAYER))) ==> (detachable_exact(heap, heap[o, PLAYER.name], V_STRING))));

axiom ((forall heap: HeapType, current: ref, v: ref, o: ref :: { guard(heap, current, PLAYER.name, v, o) } (attached_exact(heap, current, PLAYER)) ==> ((guard(heap, current, PLAYER.name, v, o)) <==> ((user_inv(heap, o)) ==> (user_inv(heap[current, PLAYER.name := v], o))))));

axiom ((forall heap: HeapType, current: ref, v: ref, o: ref :: { guard(heap, current, PLAYER.name, v, o) } (attached(heap, current, PLAYER)) ==> ((guard(heap, current, PLAYER.name, v, o)) ==> ((user_inv(heap, o)) ==> (user_inv(heap[current, PLAYER.name := v], o))))));

const V_STRING.sequence: Field (Seq int);

axiom ((FieldId(V_STRING.sequence, V_STRING)) == (94));

axiom ((forall heap: HeapType, current: ref, v: Seq int, o: ref :: { guard(heap, current, V_STRING.sequence, v, o) } (attached_exact(heap, current, V_STRING)) ==> ((guard(heap, current, V_STRING.sequence, v, o)) <==> ((user_inv(heap, o)) ==> (user_inv(heap[current, V_STRING.sequence := v], o))))));

axiom ((forall heap: HeapType, current: ref, v: Seq int, o: ref :: { guard(heap, current, V_STRING.sequence, v, o) } (attached(heap, current, V_STRING)) ==> ((guard(heap, current, V_STRING.sequence, v, o)) ==> ((user_inv(heap, o)) ==> (user_inv(heap[current, V_STRING.sequence := v], o))))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, owns, v, o) } (attached_exact(heap, current, ANY)) ==> ((guard(heap, current, owns, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, subjects, v, o) } (attached_exact(heap, current, ANY)) ==> ((guard(heap, current, subjects, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached_exact(heap, current, ANY)) ==> ((guard(heap, current, observers, v, o)) <==> (fun.ANY.in_observers(heap, current, v, o)))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached(heap, current, ANY)) ==> ((guard(heap, current, observers, v, o)) ==> (fun.ANY.in_observers(heap, current, v, o)))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, owns, v, o) } (attached_exact(heap, current, PLAYER)) ==> ((guard(heap, current, owns, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, subjects, v, o) } (attached_exact(heap, current, PLAYER)) ==> ((guard(heap, current, subjects, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached_exact(heap, current, PLAYER)) ==> ((guard(heap, current, observers, v, o)) <==> (fun.PLAYER.in_observers(heap, current, v, o)))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached(heap, current, PLAYER)) ==> ((guard(heap, current, observers, v, o)) ==> (fun.PLAYER.in_observers(heap, current, v, o)))));

const unique V_STRING: Type;

axiom (is_frozen(V_STRING));

axiom ((V_STRING) <: (V_HASHABLE));

axiom ((forall t: Type :: { (V_STRING) <: (t) } ((V_STRING) <: (t)) <==> (((t) == (V_STRING)) || ((V_HASHABLE) <: (t)))));

axiom ((FieldId(allocated, V_STRING)) == (-1));

axiom ((FieldId(closed, V_STRING)) == (-2));

axiom ((FieldId(owner, V_STRING)) == (-3));

axiom ((FieldId(owns, V_STRING)) == (-4));

axiom ((FieldId(observers, V_STRING)) == (-5));

axiom ((FieldId(subjects, V_STRING)) == (-6));

axiom ((forall <T11> $f: Field T11 :: { IsModelField($f, V_STRING) } (IsModelField($f, V_STRING)) <==> ((($f) == (V_STRING.sequence)) || (($f) == (subjects)) || (($f) == (observers)))));

function { :inline } V_STRING.user_inv(heap: HeapType, current: ref) returns (bool) {
  ((heap[current, V_STRING.internal_string]) != (Void)) && (Set#IsEmpty(heap[current, observers])) && (Set#IsEmpty(heap[current, subjects])) && (Set#IsEmpty(heap[current, owns])) && (admissibility2(heap, current))
}

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached_exact(heap, current, V_STRING)) ==> ((user_inv(heap, current)) <==> (V_STRING.user_inv(heap, current)))));

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached(heap, current, V_STRING)) ==> ((user_inv(heap, current)) ==> (V_STRING.user_inv(heap, current)))));

function modify.PLAYER.make(heap: HeapType, current: ref, n: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, n: ref :: (IsHeap(heap)) ==> ((forall <T12> $o: ref, $f: Field T12 :: { modify.PLAYER.make(heap, current, n)[$o, $f] } (modify.PLAYER.make(heap, current, n)[$o, $f]) <==> (($o) == (current))))));

procedure create.V_STRING.make_from_v_string(Current: ref, a_string: ref);
  free requires attached_exact(Heap, Current, V_STRING); // info:type property for argument Current
  free requires detachable_exact(Heap, a_string, V_STRING); // info:type property for argument a_string
  modifies Heap;
  requires (a_string) != (Void); // type:pre tag:a_string_not_void line:38
  ensures (a_string) != (Void); // type:attached tag:same_string line:42
  ensures Seq#Equal(Heap[Current, V_STRING.sequence], Heap[a_string, V_STRING.sequence]); // type:post tag:same_string line:42
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped line:43
  requires (forall <T13> $f: Field T13 :: (($f) != (allocated)) ==> ((Heap[Current, $f]) == (Default($f))));
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.V_STRING.make_from_v_string(Heap, Current, a_string), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.V_STRING.make_from_v_string(old(Heap), Current, a_string));
  free ensures HeapSucc(old(Heap), Heap);



function modify.PLAYER.set_position(heap: HeapType, current: ref, pos: int) returns (Frame);

axiom ((forall heap: HeapType, current: ref, pos: int :: (IsHeap(heap)) ==> ((forall <T14> $o: ref, $f: Field T14 :: { modify.PLAYER.set_position(heap, current, pos)[$o, $f] } (modify.PLAYER.set_position(heap, current, pos)[$o, $f]) <==> (($o) == (current))))));

function modify.PLAYER.play(heap: HeapType, current: ref, d1: ref, d2: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, d1: ref, d2: ref :: (IsHeap(heap)) ==> ((forall <T15> $o: ref, $f: Field T15 :: { modify.PLAYER.play(heap, current, d1, d2)[$o, $f] } (modify.PLAYER.play(heap, current, d1, d2)[$o, $f]) <==> ((($o) == (current)) || (($o) == (d1)) || (($o) == (d2)))))));

const DIE.face_value: Field int;

axiom ((FieldId(DIE.face_value, DIE)) == (81));

axiom ((forall heap: HeapType, o: ref :: { heap[o, DIE.face_value] } ((IsHeap(heap)) && (attached(heap, o, DIE))) ==> (is_integer_32(heap[o, DIE.face_value]))));

axiom ((forall heap: HeapType, current: ref, v: int, o: ref :: { guard(heap, current, DIE.face_value, v, o) } (attached_exact(heap, current, DIE)) ==> ((guard(heap, current, DIE.face_value, v, o)) <==> ((user_inv(heap, o)) ==> (user_inv(heap[current, DIE.face_value := v], o))))));

axiom ((forall heap: HeapType, current: ref, v: int, o: ref :: { guard(heap, current, DIE.face_value, v, o) } (attached(heap, current, DIE)) ==> ((guard(heap, current, DIE.face_value, v, o)) ==> ((user_inv(heap, o)) ==> (user_inv(heap[current, DIE.face_value := v], o))))));

procedure PLAYER.print(Current: ref, o: ref);
  free requires attached_exact(Heap, Current, PLAYER); // info:type property for argument Current
  free requires Heap[o, allocated]; // info:type property for argument o
  modifies Heap;
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.PLAYER.print(Heap, Current, o), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.PLAYER.print(old(Heap), Current, o));
  free ensures HeapSucc(old(Heap), Heap);



procedure V_STRING.plus(Current: ref, other: ref) returns (Result: ref where detachable_exact(Heap, Result, V_STRING));
  free requires attached_exact(Heap, Current, V_STRING); // info:type property for argument Current
  free requires detachable_exact(Heap, other, V_STRING); // info:type property for argument other
  modifies Heap;
  requires (other) != (Void); // type:pre tag:other_not_void line:207
  requires is_closed(Heap, Current); // type:pre tag:closed line:208
  ensures (Result) != (Void); // type:attached tag:fresh line:213
  ensures !(old(Heap)[Result, allocated]); // type:post tag:fresh line:213
  ensures is_wrapped(Heap, Result); // type:post tag:wrapped line:214
  ensures (other) != (Void); // type:attached tag:definition line:215
  ensures Seq#Equal(Heap[Result, V_STRING.sequence], Seq#Concat(Heap[Current, V_STRING.sequence], Heap[other, V_STRING.sequence])); // type:post tag:definition line:215
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.V_STRING.plus(Heap, Current, other), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.V_STRING.plus(old(Heap), Current, other));
  free ensures HeapSucc(old(Heap), Heap);



procedure create.V_STRING.init(Current: ref, a_sequence: Seq int);
  free requires attached_exact(Heap, Current, V_STRING); // info:type property for argument Current
  free requires true; // info:type property for argument a_sequence
  modifies Heap;
  ensures Seq#Equal(Heap[Current, V_STRING.sequence], a_sequence); // type:post tag:same_string line:54
  requires (forall <T16> $f: Field T16 :: (($f) != (allocated)) ==> ((Heap[Current, $f]) == (Default($f))));
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.V_STRING.init(Heap, Current, a_sequence), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.V_STRING.init(old(Heap), Current, a_sequence));
  free ensures HeapSucc(old(Heap), Heap);
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts



procedure INTEGER_32.out_(Current: int) returns (Result: ref where detachable_exact(Heap, Result, V_STRING));
  free requires is_integer_32(Current); // info:type property for argument Current
  modifies Heap;
  ensures (Result) != (Void); // type:attached tag:out_fresh line:320
  ensures !(old(Heap)[Result, allocated]); // type:post tag:out_fresh line:320
  ensures is_wrapped(Heap, Result); // type:post tag:out_wrapped line:321
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.INTEGER_32.out_(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.INTEGER_32.out_(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);



axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, owns, v, o) } (attached_exact(heap, current, APPLICATION)) ==> ((guard(heap, current, owns, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, subjects, v, o) } (attached_exact(heap, current, APPLICATION)) ==> ((guard(heap, current, subjects, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached_exact(heap, current, APPLICATION)) ==> ((guard(heap, current, observers, v, o)) <==> (fun.APPLICATION.in_observers(heap, current, v, o)))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached(heap, current, APPLICATION)) ==> ((guard(heap, current, observers, v, o)) ==> (fun.APPLICATION.in_observers(heap, current, v, o)))));

function modify.APPLICATION.make(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T17> $o: ref, $f: Field T17 :: { modify.APPLICATION.make(heap, current)[$o, $f] } (modify.APPLICATION.make(heap, current)[$o, $f]) <==> (($o) == (current))))));

procedure APPLICATION.print(Current: ref, o: ref);
  free requires attached_exact(Heap, Current, APPLICATION); // info:type property for argument Current
  free requires Heap[o, allocated]; // info:type property for argument o
  modifies Heap;
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.APPLICATION.print(Heap, Current, o), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.APPLICATION.print(old(Heap), Current, o));
  free ensures HeapSucc(old(Heap), Heap);



procedure APPLICATION.io(Current: ref) returns (Result: ref where detachable_exact(Heap, Result, STD_FILES));
  free requires attached_exact(Heap, Current, APPLICATION); // info:type property for argument Current
  modifies Heap;
  ensures (Result) != (Void); // type:attached tag:is_writable line:298
  ensures has_whole_object(writable, Result); // type:post tag:is_writable line:298
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.APPLICATION.io(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.APPLICATION.io(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);
  free ensures (Result) == (global_once_value(29));



procedure STD_FILES.read_integer(Current: ref);
  free requires attached_exact(Heap, Current, STD_FILES); // info:type property for argument Current
  modifies Heap;
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.STD_FILES.read_integer(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.STD_FILES.read_integer(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);



procedure STD_FILES.last_integer(Current: ref) returns (Result: int where is_integer_32(Result));
  free requires attached_exact(Heap, Current, STD_FILES); // info:type property for argument Current
  modifies Heap;
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.STD_FILES.last_integer(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.STD_FILES.last_integer(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.STD_FILES.last_integer(Heap, Current), readable);
  free ensures (Result) == (fun.STD_FILES.last_integer(old(Heap), Current));



function fun.STD_FILES.last_integer(heap: HeapType, current: ref) returns (int);

axiom ((forall heap: HeapType, current: ref :: { fun.STD_FILES.last_integer(heap, current) } (pre.fun.STD_FILES.last_integer(heap, current)) ==> (is_integer_32(fun.STD_FILES.last_integer(heap, current)))));

axiom ((forall h: HeapType, h': HeapType, current: ref :: { HeapSucc(h, h'), fun.STD_FILES.last_integer(h, current), fun.STD_FILES.last_integer(h', current) } ((HeapSucc(h, h')) && (pre.fun.STD_FILES.last_integer(h, current)) && (pre.fun.STD_FILES.last_integer(h', current)) && (same_inside(h, h', read.fun.STD_FILES.last_integer(h, current)))) ==> ((fun.STD_FILES.last_integer(h, current)) == (fun.STD_FILES.last_integer(h', current)))));

const GAME.winner: Field (ref);

axiom ((FieldId(GAME.winner, GAME)) == (88));

axiom ((forall heap: HeapType, o: ref :: { heap[o, GAME.winner] } ((IsHeap(heap)) && (attached(heap, o, GAME))) ==> (detachable(heap, heap[o, GAME.winner], PLAYER))));

axiom ((forall heap: HeapType, current: ref, v: ref, o: ref :: { guard(heap, current, GAME.winner, v, o) } (attached_exact(heap, current, GAME)) ==> ((guard(heap, current, GAME.winner, v, o)) <==> (false))));

axiom ((forall heap: HeapType, current: ref, v: ref, o: ref :: { guard(heap, current, GAME.winner, v, o) } (attached(heap, current, GAME)) ==> ((guard(heap, current, GAME.winner, v, o)) ==> (false))));

const DIE.random: Field (ref);

axiom ((FieldId(DIE.random, DIE)) == (83));

axiom ((forall heap: HeapType, o: ref :: { heap[o, DIE.random] } ((IsHeap(heap)) && (attached(heap, o, DIE))) ==> (detachable(heap, heap[o, DIE.random], V_RANDOM))));

axiom ((forall heap: HeapType, current: ref, v: ref, o: ref :: { guard(heap, current, DIE.random, v, o) } (attached_exact(heap, current, DIE)) ==> ((guard(heap, current, DIE.random, v, o)) <==> ((user_inv(heap, o)) ==> (user_inv(heap[current, DIE.random := v], o))))));

axiom ((forall heap: HeapType, current: ref, v: ref, o: ref :: { guard(heap, current, DIE.random, v, o) } (attached(heap, current, DIE)) ==> ((guard(heap, current, DIE.random, v, o)) ==> ((user_inv(heap, o)) ==> (user_inv(heap[current, DIE.random := v], o))))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, owns, v, o) } (attached_exact(heap, current, DIE)) ==> ((guard(heap, current, owns, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, subjects, v, o) } (attached_exact(heap, current, DIE)) ==> ((guard(heap, current, subjects, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached_exact(heap, current, DIE)) ==> ((guard(heap, current, observers, v, o)) <==> (fun.DIE.in_observers(heap, current, v, o)))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached(heap, current, DIE)) ==> ((guard(heap, current, observers, v, o)) ==> (fun.DIE.in_observers(heap, current, v, o)))));

function modify.DIE.roll(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T18> $o: ref, $f: Field T18 :: { modify.DIE.roll(heap, current)[$o, $f] } (modify.DIE.roll(heap, current)[$o, $f]) <==> (($o) == (current))))));

const unique V_RANDOM: Type;

axiom ((V_RANDOM) <: (V_INPUT_STREAM^INTEGER_32^));

axiom ((forall t: Type :: { (V_RANDOM) <: (t) } ((V_RANDOM) <: (t)) <==> (((t) == (V_RANDOM)) || ((V_INPUT_STREAM^INTEGER_32^) <: (t)))));

axiom ((FieldId(allocated, V_RANDOM)) == (-1));

axiom ((FieldId(closed, V_RANDOM)) == (-2));

axiom ((FieldId(owner, V_RANDOM)) == (-3));

axiom ((FieldId(owns, V_RANDOM)) == (-4));

axiom ((FieldId(observers, V_RANDOM)) == (-5));

axiom ((FieldId(subjects, V_RANDOM)) == (-6));

axiom ((forall <T19> $f: Field T19 :: { IsModelField($f, V_RANDOM) } (IsModelField($f, V_RANDOM)) <==> ((($f) == (V_RANDOM.box)) || (($f) == (subjects)) || (($f) == (observers)))));

function { :inline } V_RANDOM.user_inv(heap: HeapType, current: ref) returns (bool) {
  ((Set#Card(heap[current, V_RANDOM.box])) <= (1)) && (Set#Equal(heap[current, observers], Set#Empty())) && (Set#Equal(heap[current, V_RANDOM.box], Set#Singleton(fun.V_RANDOM.random_bits(heap, current, heap[current, V_RANDOM.value], 32)))) && (Set#IsEmpty(heap[current, subjects])) && (Set#IsEmpty(heap[current, owns])) && (admissibility2(heap, current))
}

function V_RANDOM.observers.static(heap: HeapType, current: ref) returns (Set (ref)) {
  Set#Empty()
}

function V_RANDOM.V_RANDOM.box.static(heap: HeapType, current: ref) returns (Set int) {
  Set#Singleton(fun.V_RANDOM.random_bits(heap, current, heap[current, V_RANDOM.value], 32))
}

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached_exact(heap, current, V_RANDOM)) ==> ((user_inv(heap, current)) <==> (V_RANDOM.user_inv(heap, current)))));

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached(heap, current, V_RANDOM)) ==> ((user_inv(heap, current)) ==> (V_RANDOM.user_inv(heap, current)))));

procedure create.V_RANDOM.default_create(Current: ref);
  free requires attached_exact(Heap, Current, V_RANDOM); // info:type property for argument Current
  modifies Heap;
  requires (forall <T20> $f: Field T20 :: (($f) != (allocated)) ==> ((Heap[Current, $f]) == (Default($f))));
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.V_RANDOM.default_create(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.V_RANDOM.default_create(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts



procedure V_RANDOM.forth(Current: ref);
  free requires attached_exact(Heap, Current, V_RANDOM); // info:type property for argument Current
  modifies Heap;
  requires (forall i_101: ref :: (Heap[Current, subjects][i_101]) ==> (is_closed(Heap, i_101))); // type:pre tag:subjects_closed line:39
  requires pre.fun.V_RANDOM.off(Heap, Current); // type:check tag:function_precondition line:40 cid:135 rid:1572
  requires !(fun.V_RANDOM.off(Heap, Current)); // type:pre tag:not_off line:40
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.V_RANDOM.forth(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.V_RANDOM.forth(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);
  requires is_wrapped(Heap, Current); // type:pre tag:default_is_wrapped default:contracts
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts



procedure V_RANDOM.bounded_item(Current: ref, min: int, max: int) returns (Result: int where is_integer_32(Result));
  free requires attached_exact(Heap, Current, V_RANDOM); // info:type property for argument Current
  free requires is_integer_32(min); // info:type property for argument min
  free requires is_integer_32(max); // info:type property for argument max
  modifies Heap;
  requires (max) >= (min); // type:pre tag:bounds_valid line:53
  ensures ((min) <= (Result)) && ((Result) <= (max)); // type:post tag:result_in_bounds line:64
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.V_RANDOM.bounded_item(Heap, Current, min, max), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.V_RANDOM.bounded_item(old(Heap), Current, min, max));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.V_RANDOM.bounded_item(Heap, Current, min, max), readable);
  requires is_closed(Heap, Current); // type:pre tag:default_is_closed default:contracts
  free ensures (Result) == (fun.V_RANDOM.bounded_item(old(Heap), Current, min, max));



function fun.V_RANDOM.bounded_item(heap: HeapType, current: ref, min: int, max: int) returns (int);

axiom ((forall heap: HeapType, current: ref, min: int, max: int :: { fun.V_RANDOM.bounded_item(heap, current, min, max) } (pre.fun.V_RANDOM.bounded_item(heap, current, min, max)) ==> (((min) <= (fun.V_RANDOM.bounded_item(heap, current, min, max))) && ((fun.V_RANDOM.bounded_item(heap, current, min, max)) <= (max)) && (is_integer_32(fun.V_RANDOM.bounded_item(heap, current, min, max))))));

axiom ((forall h: HeapType, h': HeapType, current: ref, min: int, max: int :: { HeapSucc(h, h'), fun.V_RANDOM.bounded_item(h, current, min, max), fun.V_RANDOM.bounded_item(h', current, min, max) } ((HeapSucc(h, h')) && (pre.fun.V_RANDOM.bounded_item(h, current, min, max)) && (pre.fun.V_RANDOM.bounded_item(h', current, min, max)) && (same_inside(h, h', read.fun.V_RANDOM.bounded_item(h, current, min, max)))) ==> ((fun.V_RANDOM.bounded_item(h, current, min, max)) == (fun.V_RANDOM.bounded_item(h', current, min, max)))));

const GAME.die_1: Field (ref);

axiom ((FieldId(GAME.die_1, GAME)) == (86));

axiom ((forall heap: HeapType, o: ref :: { heap[o, GAME.die_1] } ((IsHeap(heap)) && (attached(heap, o, GAME))) ==> (detachable(heap, heap[o, GAME.die_1], DIE))));

axiom ((forall heap: HeapType, current: ref, v: ref, o: ref :: { guard(heap, current, GAME.die_1, v, o) } (attached_exact(heap, current, GAME)) ==> ((guard(heap, current, GAME.die_1, v, o)) <==> (false))));

axiom ((forall heap: HeapType, current: ref, v: ref, o: ref :: { guard(heap, current, GAME.die_1, v, o) } (attached(heap, current, GAME)) ==> ((guard(heap, current, GAME.die_1, v, o)) ==> (false))));

const GAME.die_2: Field (ref);

axiom ((FieldId(GAME.die_2, GAME)) == (87));

axiom ((forall heap: HeapType, o: ref :: { heap[o, GAME.die_2] } ((IsHeap(heap)) && (attached(heap, o, GAME))) ==> (detachable(heap, heap[o, GAME.die_2], DIE))));

axiom ((forall heap: HeapType, current: ref, v: ref, o: ref :: { guard(heap, current, GAME.die_2, v, o) } (attached_exact(heap, current, GAME)) ==> ((guard(heap, current, GAME.die_2, v, o)) <==> (false))));

axiom ((forall heap: HeapType, current: ref, v: ref, o: ref :: { guard(heap, current, GAME.die_2, v, o) } (attached(heap, current, GAME)) ==> ((guard(heap, current, GAME.die_2, v, o)) ==> (false))));

const GAME.players: Field (ref);

axiom ((FieldId(GAME.players, GAME)) == (85));

axiom ((forall heap: HeapType, o: ref :: { heap[o, GAME.players] } ((IsHeap(heap)) && (attached(heap, o, GAME))) ==> (detachable_exact(heap, heap[o, GAME.players], V_ARRAY^PLAYER^))));

axiom ((forall heap: HeapType, current: ref, v: ref, o: ref :: { guard(heap, current, GAME.players, v, o) } (attached_exact(heap, current, GAME)) ==> ((guard(heap, current, GAME.players, v, o)) <==> (false))));

axiom ((forall heap: HeapType, current: ref, v: ref, o: ref :: { guard(heap, current, GAME.players, v, o) } (attached(heap, current, GAME)) ==> ((guard(heap, current, GAME.players, v, o)) ==> (false))));

const V_ARRAY^PLAYER^.sequence: Field (Seq (ref));

axiom ((FieldId(V_ARRAY^PLAYER^.sequence, V_ARRAY^PLAYER^)) == (90));

const V_MUTABLE_SEQUENCE^PLAYER^.sequence: Field (Seq (ref));

axiom ((V_ARRAY^PLAYER^.sequence) == (V_MUTABLE_SEQUENCE^PLAYER^.sequence));

const V_SEQUENCE^PLAYER^.sequence: Field (Seq (ref));

axiom ((V_ARRAY^PLAYER^.sequence) == (V_SEQUENCE^PLAYER^.sequence));

axiom ((forall heap: HeapType, o: ref :: { heap[o, V_ARRAY^PLAYER^.sequence] } ((IsHeap(heap)) && (attached(heap, o, V_ARRAY^PLAYER^))) ==> (Seq#ItemsType(heap, heap[o, V_ARRAY^PLAYER^.sequence], PLAYER))));

axiom ((forall heap: HeapType, current: ref, v: Seq (ref), o: ref :: { guard(heap, current, V_ARRAY^PLAYER^.sequence, v, o) } (attached_exact(heap, current, V_ARRAY^PLAYER^)) ==> ((guard(heap, current, V_ARRAY^PLAYER^.sequence, v, o)) <==> (false))));

axiom ((forall heap: HeapType, current: ref, v: Seq (ref), o: ref :: { guard(heap, current, V_ARRAY^PLAYER^.sequence, v, o) } (attached(heap, current, V_ARRAY^PLAYER^)) ==> ((guard(heap, current, V_ARRAY^PLAYER^.sequence, v, o)) ==> (false))));

const V_ARRAY^PLAYER^.lower_: Field int;

axiom ((FieldId(V_ARRAY^PLAYER^.lower_, V_ARRAY^PLAYER^)) == (95));

const V_MUTABLE_SEQUENCE^PLAYER^.lower_: Field int;

axiom ((V_ARRAY^PLAYER^.lower_) == (V_MUTABLE_SEQUENCE^PLAYER^.lower_));

const V_SEQUENCE^PLAYER^.lower_: Field int;

axiom ((V_ARRAY^PLAYER^.lower_) == (V_SEQUENCE^PLAYER^.lower_));

axiom ((forall heap: HeapType, o: ref :: { heap[o, V_ARRAY^PLAYER^.lower_] } ((IsHeap(heap)) && (attached(heap, o, V_ARRAY^PLAYER^))) ==> (is_integer_32(heap[o, V_ARRAY^PLAYER^.lower_]))));

axiom ((forall heap: HeapType, current: ref, v: int, o: ref :: { guard(heap, current, V_ARRAY^PLAYER^.lower_, v, o) } (attached_exact(heap, current, V_ARRAY^PLAYER^)) ==> ((guard(heap, current, V_ARRAY^PLAYER^.lower_, v, o)) <==> (false))));

axiom ((forall heap: HeapType, current: ref, v: int, o: ref :: { guard(heap, current, V_ARRAY^PLAYER^.lower_, v, o) } (attached(heap, current, V_ARRAY^PLAYER^)) ==> ((guard(heap, current, V_ARRAY^PLAYER^.lower_, v, o)) ==> (false))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, owns, v, o) } (attached_exact(heap, current, GAME)) ==> ((guard(heap, current, owns, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, subjects, v, o) } (attached_exact(heap, current, GAME)) ==> ((guard(heap, current, subjects, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached_exact(heap, current, GAME)) ==> ((guard(heap, current, observers, v, o)) <==> (fun.GAME.in_observers(heap, current, v, o)))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached(heap, current, GAME)) ==> ((guard(heap, current, observers, v, o)) ==> (fun.GAME.in_observers(heap, current, v, o)))));

function modify.GAME.make(heap: HeapType, current: ref, n: int) returns (Frame);

axiom ((forall heap: HeapType, current: ref, n: int :: (IsHeap(heap)) ==> ((forall <T21> $o: ref, $f: Field T21 :: { modify.GAME.make(heap, current, n)[$o, $f] } (modify.GAME.make(heap, current, n)[$o, $f]) <==> (($o) == (current))))));

const unique V_ARRAY^PLAYER^: Type;

axiom (is_frozen(V_ARRAY^PLAYER^));

axiom ((V_ARRAY^PLAYER^) <: (V_MUTABLE_SEQUENCE^PLAYER^));

axiom ((forall t: Type :: { (V_ARRAY^PLAYER^) <: (t) } ((V_ARRAY^PLAYER^) <: (t)) <==> (((t) == (V_ARRAY^PLAYER^)) || ((V_MUTABLE_SEQUENCE^PLAYER^) <: (t)))));

axiom ((FieldId(allocated, V_ARRAY^PLAYER^)) == (-1));

axiom ((FieldId(closed, V_ARRAY^PLAYER^)) == (-2));

axiom ((FieldId(owner, V_ARRAY^PLAYER^)) == (-3));

axiom ((FieldId(owns, V_ARRAY^PLAYER^)) == (-4));

axiom ((FieldId(observers, V_ARRAY^PLAYER^)) == (-5));

axiom ((FieldId(subjects, V_ARRAY^PLAYER^)) == (-6));

axiom ((forall <T22> $f: Field T22 :: { IsModelField($f, V_ARRAY^PLAYER^) } (IsModelField($f, V_ARRAY^PLAYER^)) <==> ((($f) == (V_ARRAY^PLAYER^.sequence)) || (($f) == (V_ARRAY^PLAYER^.lower_)) || (($f) == (V_ARRAY^PLAYER^.bag)) || (($f) == (subjects)) || (($f) == (observers)))));

function { :inline } V_ARRAY^PLAYER^.user_inv(heap: HeapType, current: ref) returns (bool) {
  (!(heap[current, observers][current])) && ((Seq#IsEmpty(heap[current, V_ARRAY^PLAYER^.sequence])) ==> ((heap[current, V_ARRAY^PLAYER^.lower_]) == (1))) && (Bag#Equal(heap[current, V_ARRAY^PLAYER^.bag], Seq#ToBag(heap[current, V_ARRAY^PLAYER^.sequence]))) && ((heap[current, V_ARRAY^PLAYER^.area]) != (Void)) && ((heap[current, V_ARRAY^PLAYER^.lower_]) == (heap[current, V_ARRAY^PLAYER^.lower])) && ((heap[current, V_ARRAY^PLAYER^.upper]) == (((heap[current, V_ARRAY^PLAYER^.lower_]) + (Seq#Length(heap[current, V_ARRAY^PLAYER^.sequence]))) - (1))) && (Set#Equal(heap[current, owns], Set#Singleton(heap[current, V_ARRAY^PLAYER^.area]))) && (Seq#Equal(heap[current, V_ARRAY^PLAYER^.sequence], heap[heap[current, V_ARRAY^PLAYER^.area], V_SPECIAL^PLAYER^.sequence])) && (Set#IsEmpty(heap[current, subjects])) && (admissibility2(heap, current))
}

function V_ARRAY^PLAYER^.V_ARRAY^PLAYER^.bag.static(heap: HeapType, current: ref) returns (Bag (ref)) {
  Seq#ToBag(heap[current, V_ARRAY^PLAYER^.sequence])
}

function V_ARRAY^PLAYER^.V_ARRAY^PLAYER^.lower_.static(heap: HeapType, current: ref) returns (int) {
  heap[current, V_ARRAY^PLAYER^.lower]
}

function V_ARRAY^PLAYER^.owns.static(heap: HeapType, current: ref) returns (Set (ref)) {
  Set#Singleton(heap[current, V_ARRAY^PLAYER^.area])
}

function V_ARRAY^PLAYER^.V_ARRAY^PLAYER^.sequence.static(heap: HeapType, current: ref) returns (Seq (ref)) {
  heap[heap[current, V_ARRAY^PLAYER^.area], V_SPECIAL^PLAYER^.sequence]
}

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached_exact(heap, current, V_ARRAY^PLAYER^)) ==> ((user_inv(heap, current)) <==> (V_ARRAY^PLAYER^.user_inv(heap, current)))));

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached(heap, current, V_ARRAY^PLAYER^)) ==> ((user_inv(heap, current)) ==> (V_ARRAY^PLAYER^.user_inv(heap, current)))));

procedure create.V_ARRAY^PLAYER^.make(Current: ref, l: int, u: int);
  free requires attached_exact(Heap, Current, V_ARRAY^PLAYER^); // info:type property for argument Current
  free requires is_integer_32(l); // info:type property for argument l
  free requires is_integer_32(u); // info:type property for argument u
  modifies Heap;
  requires (l) <= ((u) + (1)); // type:pre tag:valid_indexes line:40
  ensures (Seq#Length(Heap[Current, V_ARRAY^PLAYER^.sequence])) == (((u) - (l)) + (1)); // type:post tag:sequence_domain_definition line:51
  ensures (forall i_102: int :: (((1) <= (i_102)) && ((i_102) <= (Seq#Length(Heap[Current, V_ARRAY^PLAYER^.sequence])))) ==> (pre.fun.MML_SEQUENCE^PLAYER^.item(Heap[Current, V_ARRAY^PLAYER^.sequence], i_102))); // type:check tag:function_precondition line:52 cid:125 rid:3286
  ensures (forall i_102: int :: (((1) <= (i_102)) && ((i_102) <= (Seq#Length(Heap[Current, V_ARRAY^PLAYER^.sequence])))) ==> ((Seq#Item(Heap[Current, V_ARRAY^PLAYER^.sequence], i_102)) == (Void))); // type:post tag:sequence_definition line:52
  ensures (Heap[Current, V_ARRAY^PLAYER^.lower_]) == ((if (l) <= (u) then l else 1)); // type:post tag:lower_definition line:53
  ensures Set#IsEmpty(Heap[Current, observers]); // type:post tag:no_observers line:54
  requires (forall <T23> $f: Field T23 :: (($f) != (allocated)) ==> ((Heap[Current, $f]) == (Default($f))));
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.V_ARRAY^PLAYER^.make(Heap, Current, l, u), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.V_ARRAY^PLAYER^.make(old(Heap), Current, l, u));
  free ensures HeapSucc(old(Heap), Heap);
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts



function GAME#I#players_bounds.filtered_inv(heap: HeapType, current: ref) returns (bool) {
  ((heap[heap[current, GAME.players], V_ARRAY^PLAYER^.lower_]) == (1)) && ((2) <= (Seq#Length(heap[heap[current, GAME.players], V_ARRAY^PLAYER^.sequence]))) && ((Seq#Length(heap[heap[current, GAME.players], V_ARRAY^PLAYER^.sequence])) <= (6))
}

axiom ((forall h: HeapType, o: ref :: { GAME#I#players_bounds.filtered_inv(h, o) } ((IsHeap(h)) && (attached(h, o, GAME)) && (h[o, closed])) ==> (GAME#I#players_bounds.filtered_inv(h, o))));

procedure V_ARRAY^PLAYER^.count(Current: ref) returns (Result: int where is_integer_32(Result));
  free requires attached_exact(Heap, Current, V_ARRAY^PLAYER^); // info:type property for argument Current
  modifies Heap;
  ensures (Result) == (Bag#Card(Heap[Current, V_ARRAY^PLAYER^.bag])); // type:post tag:definition line:23
  ensures (Result) == (Seq#Length(Heap[Current, V_ARRAY^PLAYER^.sequence])); // type:post tag:definition_sequence line:81
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.V_ARRAY^PLAYER^.count(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.V_ARRAY^PLAYER^.count(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.V_ARRAY^PLAYER^.count(Heap, Current), readable);
  requires is_closed(Heap, Current); // type:pre tag:default_is_closed default:contracts
  free ensures (Result) == (fun.V_ARRAY^PLAYER^.count(old(Heap), Current));



function fun.V_ARRAY^PLAYER^.count(heap: HeapType, current: ref) returns (int);

axiom ((forall heap: HeapType, current: ref :: { fun.V_ARRAY^PLAYER^.count(heap, current) } (pre.fun.V_ARRAY^PLAYER^.count(heap, current)) ==> (((fun.V_ARRAY^PLAYER^.count(heap, current)) == (Bag#Card(heap[current, V_ARRAY^PLAYER^.bag]))) && ((fun.V_ARRAY^PLAYER^.count(heap, current)) == (Seq#Length(heap[current, V_ARRAY^PLAYER^.sequence]))) && (is_integer_32(fun.V_ARRAY^PLAYER^.count(heap, current))))));

axiom ((forall h: HeapType, h': HeapType, current: ref :: { HeapSucc(h, h'), fun.V_ARRAY^PLAYER^.count(h, current), fun.V_ARRAY^PLAYER^.count(h', current) } ((HeapSucc(h, h')) && (pre.fun.V_ARRAY^PLAYER^.count(h, current)) && (pre.fun.V_ARRAY^PLAYER^.count(h', current)) && (same_inside(h, h', read.fun.V_ARRAY^PLAYER^.count(h, current)))) ==> ((fun.V_ARRAY^PLAYER^.count(h, current)) == (fun.V_ARRAY^PLAYER^.count(h', current)))));

procedure V_ARRAY^PLAYER^.put(Current: ref, v: ref, i: int);
  free requires attached_exact(Heap, Current, V_ARRAY^PLAYER^); // info:type property for argument Current
  free requires detachable(Heap, v, PLAYER); // info:type property for argument v
  free requires is_integer_32(i); // info:type property for argument i
  modifies Heap;
  requires fun.V_ARRAY^PLAYER^.has_index(Heap, Current, i); // type:pre tag:has_index line:38
  requires (forall i_103: ref :: (Heap[Current, observers][i_103]) ==> (is_open(Heap, i_103))); // type:pre tag:observers_open line:39
  ensures pre.fun.MML_SEQUENCE^PLAYER^.replaced_at(old(Heap)[Current, V_ARRAY^PLAYER^.sequence], fun.V_ARRAY^PLAYER^.idx(old(Heap), Current, i), v); // type:check tag:function_precondition line:43 cid:125 rid:3308
  ensures Seq#Equal(Heap[Current, V_ARRAY^PLAYER^.sequence], Seq#Update(old(Heap)[Current, V_ARRAY^PLAYER^.sequence], fun.V_ARRAY^PLAYER^.idx(old(Heap), Current, i), v)); // type:post tag:sequence_effect line:43
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.V_ARRAY^PLAYER^.put(Heap, Current, v, i), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.V_ARRAY^PLAYER^.put(old(Heap), Current, v, i));
  free ensures HeapSucc(old(Heap), Heap);
  requires is_wrapped(Heap, Current); // type:pre tag:default_is_wrapped default:contracts
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts



function PLAYER#I#name_not_void#owns_def.filtered_inv(heap: HeapType, current: ref) returns (bool) {
  ((heap[current, PLAYER.name]) != (Void)) && (Set#Equal(heap[current, owns], Set#Singleton(heap[current, PLAYER.name])))
}

axiom ((forall h: HeapType, o: ref :: { PLAYER#I#name_not_void#owns_def.filtered_inv(h, o) } ((IsHeap(h)) && (attached(h, o, PLAYER)) && (h[o, closed])) ==> (PLAYER#I#name_not_void#owns_def.filtered_inv(h, o))));

procedure GAME.print(Current: ref, o: ref);
  free requires attached_exact(Heap, Current, GAME); // info:type property for argument Current
  free requires Heap[o, allocated]; // info:type property for argument o
  modifies Heap;
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.GAME.print(Heap, Current, o), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.GAME.print(old(Heap), Current, o));
  free ensures HeapSucc(old(Heap), Heap);



function modify.GAME.play(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T24> $o: ref, $f: Field T24 :: { modify.GAME.play(heap, current)[$o, $f] } (modify.GAME.play(heap, current)[$o, $f]) <==> ((($o) == (current)) && ((($f) == (closed)) || (($f) == (GAME.winner))))))));

function GAME#I#players_bounds#owns_def.filtered_inv(heap: HeapType, current: ref) returns (bool) {
  (Set#Equal(heap[current, owns], Set#Union(Seq#Range(heap[heap[current, GAME.players], V_ARRAY^PLAYER^.sequence]), Set#Extended(Set#Extended(Set#Singleton(heap[current, GAME.players]), heap[current, GAME.die_1]), heap[current, GAME.die_2])))) && ((heap[heap[current, GAME.players], V_ARRAY^PLAYER^.lower_]) == (1)) && ((2) <= (Seq#Length(heap[heap[current, GAME.players], V_ARRAY^PLAYER^.sequence]))) && ((Seq#Length(heap[heap[current, GAME.players], V_ARRAY^PLAYER^.sequence])) <= (6))
}

axiom ((forall h: HeapType, o: ref :: { GAME#I#players_bounds#owns_def.filtered_inv(h, o) } ((IsHeap(h)) && (attached(h, o, GAME)) && (h[o, closed])) ==> (GAME#I#players_bounds#owns_def.filtered_inv(h, o))));

function V_ARRAY^PLAYER^#I#lower_definition#upper_definition.filtered_inv(heap: HeapType, current: ref) returns (bool) {
  ((heap[current, V_ARRAY^PLAYER^.lower_]) == (heap[current, V_ARRAY^PLAYER^.lower])) && ((heap[current, V_ARRAY^PLAYER^.upper]) == (((heap[current, V_ARRAY^PLAYER^.lower_]) + (Seq#Length(heap[current, V_ARRAY^PLAYER^.sequence]))) - (1)))
}

axiom ((forall h: HeapType, o: ref :: { V_ARRAY^PLAYER^#I#lower_definition#upper_definition.filtered_inv(h, o) } ((IsHeap(h)) && (attached(h, o, V_ARRAY^PLAYER^)) && (h[o, closed])) ==> (V_ARRAY^PLAYER^#I#lower_definition#upper_definition.filtered_inv(h, o))));

procedure V_ARRAY^PLAYER^.item(Current: ref, i: int) returns (Result: ref where detachable(Heap, Result, PLAYER));
  free requires attached_exact(Heap, Current, V_ARRAY^PLAYER^); // info:type property for argument Current
  free requires is_integer_32(i); // info:type property for argument i
  modifies Heap;
  requires fun.V_ARRAY^PLAYER^.has_index(Heap, Current, i); // type:pre tag:has_index line:25
  ensures pre.fun.MML_SEQUENCE^PLAYER^.item(Heap[Current, V_ARRAY^PLAYER^.sequence], ((i) - (Heap[Current, V_ARRAY^PLAYER^.lower_])) + (1)); // type:check tag:function_precondition line:28 cid:125 rid:3286
  ensures (Result) == (Seq#Item(Heap[Current, V_ARRAY^PLAYER^.sequence], ((i) - (Heap[Current, V_ARRAY^PLAYER^.lower_])) + (1))); // type:post tag:definition line:28
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.V_ARRAY^PLAYER^.item(Heap, Current, i), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.V_ARRAY^PLAYER^.item(old(Heap), Current, i));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.V_ARRAY^PLAYER^.item(Heap, Current, i), readable);
  requires is_closed(Heap, Current); // type:pre tag:default_is_closed default:contracts
  free ensures (Result) == (fun.V_ARRAY^PLAYER^.item(old(Heap), Current, i));



function fun.V_ARRAY^PLAYER^.item(heap: HeapType, current: ref, i: int) returns (ref);

axiom ((forall heap: HeapType, current: ref, i: int :: { fun.V_ARRAY^PLAYER^.item(heap, current, i) } (pre.fun.V_ARRAY^PLAYER^.item(heap, current, i)) ==> (((fun.V_ARRAY^PLAYER^.item(heap, current, i)) == (Seq#Item(heap[current, V_ARRAY^PLAYER^.sequence], ((i) - (heap[current, V_ARRAY^PLAYER^.lower_])) + (1)))) && (detachable(heap, fun.V_ARRAY^PLAYER^.item(heap, current, i), PLAYER)))));

axiom ((forall h: HeapType, h': HeapType, current: ref, i: int :: { HeapSucc(h, h'), fun.V_ARRAY^PLAYER^.item(h, current, i), fun.V_ARRAY^PLAYER^.item(h', current, i) } ((HeapSucc(h, h')) && (pre.fun.V_ARRAY^PLAYER^.item(h, current, i)) && (pre.fun.V_ARRAY^PLAYER^.item(h', current, i)) && (same_inside(h, h', read.fun.V_ARRAY^PLAYER^.item(h, current, i)))) ==> ((fun.V_ARRAY^PLAYER^.item(h, current, i)) == (fun.V_ARRAY^PLAYER^.item(h', current, i)))));

function modify.GAME.print_board(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T25> $o: ref, $f: Field T25 :: { modify.GAME.print_board(heap, current)[$o, $f] } (modify.GAME.print_board(heap, current)[$o, $f]) <==> (false)))));

procedure GAME.io(Current: ref) returns (Result: ref where detachable_exact(Heap, Result, STD_FILES));
  free requires attached_exact(Heap, Current, GAME); // info:type property for argument Current
  modifies Heap;
  ensures (Result) != (Void); // type:attached tag:is_writable line:298
  ensures has_whole_object(writable, Result); // type:post tag:is_writable line:298
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.GAME.io(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.GAME.io(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);
  free ensures (Result) == (global_once_value(29));



procedure STD_FILES.put_new_line(Current: ref);
  free requires attached_exact(Heap, Current, STD_FILES); // info:type property for argument Current
  modifies Heap;
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.STD_FILES.put_new_line(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.STD_FILES.put_new_line(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);



procedure V_STRING.multiply(Current: ref, n: int);
  free requires attached_exact(Heap, Current, V_STRING); // info:type property for argument Current
  free requires is_integer_32(n); // info:type property for argument n
  modifies Heap;
  requires (n) >= (1); // type:pre line:132
  ensures (Seq#Length(Heap[Current, V_STRING.sequence])) == ((Seq#Length(old(Heap)[Current, V_STRING.sequence])) * (n)); // type:post tag:length line:136
  ensures Seq#Equal(Seq#Front(Heap[Current, V_STRING.sequence], Seq#Length(old(Heap)[Current, V_STRING.sequence])), old(Heap)[Current, V_STRING.sequence]); // type:post tag:front_same line:137
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.V_STRING.multiply(Heap, Current, n), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.V_STRING.multiply(old(Heap), Current, n));
  free ensures HeapSucc(old(Heap), Heap);
  requires is_wrapped(Heap, Current); // type:pre tag:default_is_wrapped default:contracts
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts



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

procedure PLAYER.in_observers(Current: ref, new_observers: Set (ref), o: ref) returns (Result: bool where true);
  free requires attached_exact(Heap, Current, PLAYER); // info:type property for argument Current
  free requires Set#ItemsType(Heap, new_observers, ANY); // info:type property for argument new_observers
  free requires Heap[o, allocated]; // info:type property for argument o
  modifies Heap;
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.PLAYER.in_observers(Heap, Current, new_observers, o), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.PLAYER.in_observers(old(Heap), Current, new_observers, o));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.PLAYER.in_observers(Heap, Current, new_observers, o), readable);



function fun.PLAYER.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function fun0.PLAYER.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.PLAYER.in_observers(heap, current, new_observers, o) } { trigger.fun.PLAYER.in_observers(heap, current, new_observers, o) } (pre.fun.PLAYER.in_observers(heap, current, new_observers, o)) ==> ((fun.PLAYER.in_observers(heap, current, new_observers, o)) == (new_observers[o]))));

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.PLAYER.in_observers(heap, current, new_observers, o) } (fun.PLAYER.in_observers(heap, current, new_observers, o)) == (fun0.PLAYER.in_observers(heap, current, new_observers, o))));

axiom ((forall h: HeapType, h': HeapType, current: ref, new_observers: Set (ref), o: ref :: { HeapSucc(h, h'), fun0.PLAYER.in_observers(h, current, new_observers, o), fun0.PLAYER.in_observers(h', current, new_observers, o) } ((HeapSucc(h, h')) && (pre.fun.PLAYER.in_observers(h, current, new_observers, o)) && (pre.fun.PLAYER.in_observers(h', current, new_observers, o)) && (same_inside(h, h', read.fun.PLAYER.in_observers(h, current, new_observers, o)))) ==> ((fun0.PLAYER.in_observers(h, current, new_observers, o)) == (fun0.PLAYER.in_observers(h', current, new_observers, o)))));

const unique V_HASHABLE: Type;

axiom ((V_HASHABLE) <: (ANY));

axiom ((forall t: Type :: { (V_HASHABLE) <: (t) } ((V_HASHABLE) <: (t)) <==> (((t) == (V_HASHABLE)) || ((ANY) <: (t)))));

axiom ((FieldId(allocated, V_HASHABLE)) == (-1));

axiom ((FieldId(closed, V_HASHABLE)) == (-2));

axiom ((FieldId(owner, V_HASHABLE)) == (-3));

axiom ((FieldId(owns, V_HASHABLE)) == (-4));

axiom ((FieldId(observers, V_HASHABLE)) == (-5));

axiom ((FieldId(subjects, V_HASHABLE)) == (-6));

const V_STRING.internal_string: Field (ref);

axiom ((FieldId(V_STRING.internal_string, V_STRING)) == (99));

axiom ((forall heap: HeapType, o: ref :: { heap[o, V_STRING.internal_string] } ((IsHeap(heap)) && (attached(heap, o, V_STRING))) ==> (detachable(heap, heap[o, V_STRING.internal_string], STRING_8))));

axiom ((forall heap: HeapType, current: ref, v: ref, o: ref :: { guard(heap, current, V_STRING.internal_string, v, o) } (attached_exact(heap, current, V_STRING)) ==> ((guard(heap, current, V_STRING.internal_string, v, o)) <==> ((user_inv(heap, o)) ==> (user_inv(heap[current, V_STRING.internal_string := v], o))))));

axiom ((forall heap: HeapType, current: ref, v: ref, o: ref :: { guard(heap, current, V_STRING.internal_string, v, o) } (attached(heap, current, V_STRING)) ==> ((guard(heap, current, V_STRING.internal_string, v, o)) ==> ((user_inv(heap, o)) ==> (user_inv(heap[current, V_STRING.internal_string := v], o))))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, owns, v, o) } (attached_exact(heap, current, V_STRING)) ==> ((guard(heap, current, owns, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, subjects, v, o) } (attached_exact(heap, current, V_STRING)) ==> ((guard(heap, current, subjects, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached_exact(heap, current, V_STRING)) ==> ((guard(heap, current, observers, v, o)) <==> (fun.V_STRING.in_observers(heap, current, v, o)))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached(heap, current, V_STRING)) ==> ((guard(heap, current, observers, v, o)) ==> (fun.V_STRING.in_observers(heap, current, v, o)))));

function modify.V_STRING.make_from_v_string(heap: HeapType, current: ref, a_string: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, a_string: ref :: (IsHeap(heap)) ==> ((forall <T26> $o: ref, $f: Field T26 :: { modify.V_STRING.make_from_v_string(heap, current, a_string)[$o, $f] } (modify.V_STRING.make_from_v_string(heap, current, a_string)[$o, $f]) <==> (($o) == (current))))));

function modify.PLAYER.print(heap: HeapType, current: ref, o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, o: ref :: (IsHeap(heap)) ==> ((forall <T27> $o: ref, $f: Field T27 :: { modify.PLAYER.print(heap, current, o)[$o, $f] } (modify.PLAYER.print(heap, current, o)[$o, $f]) <==> (false)))));

function modify.V_STRING.plus(heap: HeapType, current: ref, other: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, other: ref :: (IsHeap(heap)) ==> ((forall <T28> $o: ref, $f: Field T28 :: { modify.V_STRING.plus(heap, current, other)[$o, $f] } (modify.V_STRING.plus(heap, current, other)[$o, $f]) <==> (false)))));

function modify.V_STRING.init(heap: HeapType, current: ref, a_sequence: Seq int) returns (Frame);

axiom ((forall heap: HeapType, current: ref, a_sequence: Seq int :: (IsHeap(heap)) ==> ((forall <T29> $o: ref, $f: Field T29 :: { modify.V_STRING.init(heap, current, a_sequence)[$o, $f] } (modify.V_STRING.init(heap, current, a_sequence)[$o, $f]) <==> (($o) == (current))))));

function modify.INTEGER_32.out_(heap: HeapType, current: int) returns (Frame);

axiom ((forall heap: HeapType, current: int :: (IsHeap(heap)) ==> ((forall <T30> $o: ref, $f: Field T30 :: { modify.INTEGER_32.out_(heap, current)[$o, $f] } (modify.INTEGER_32.out_(heap, current)[$o, $f]) <==> (false)))));

procedure APPLICATION.in_observers(Current: ref, new_observers: Set (ref), o: ref) returns (Result: bool where true);
  free requires attached_exact(Heap, Current, APPLICATION); // info:type property for argument Current
  free requires Set#ItemsType(Heap, new_observers, ANY); // info:type property for argument new_observers
  free requires Heap[o, allocated]; // info:type property for argument o
  modifies Heap;
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.APPLICATION.in_observers(Heap, Current, new_observers, o), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.APPLICATION.in_observers(old(Heap), Current, new_observers, o));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.APPLICATION.in_observers(Heap, Current, new_observers, o), readable);



function fun.APPLICATION.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function fun0.APPLICATION.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.APPLICATION.in_observers(heap, current, new_observers, o) } { trigger.fun.APPLICATION.in_observers(heap, current, new_observers, o) } (pre.fun.APPLICATION.in_observers(heap, current, new_observers, o)) ==> ((fun.APPLICATION.in_observers(heap, current, new_observers, o)) == (new_observers[o]))));

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.APPLICATION.in_observers(heap, current, new_observers, o) } (fun.APPLICATION.in_observers(heap, current, new_observers, o)) == (fun0.APPLICATION.in_observers(heap, current, new_observers, o))));

axiom ((forall h: HeapType, h': HeapType, current: ref, new_observers: Set (ref), o: ref :: { HeapSucc(h, h'), fun0.APPLICATION.in_observers(h, current, new_observers, o), fun0.APPLICATION.in_observers(h', current, new_observers, o) } ((HeapSucc(h, h')) && (pre.fun.APPLICATION.in_observers(h, current, new_observers, o)) && (pre.fun.APPLICATION.in_observers(h', current, new_observers, o)) && (same_inside(h, h', read.fun.APPLICATION.in_observers(h, current, new_observers, o)))) ==> ((fun0.APPLICATION.in_observers(h, current, new_observers, o)) == (fun0.APPLICATION.in_observers(h', current, new_observers, o)))));

function modify.APPLICATION.print(heap: HeapType, current: ref, o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, o: ref :: (IsHeap(heap)) ==> ((forall <T31> $o: ref, $f: Field T31 :: { modify.APPLICATION.print(heap, current, o)[$o, $f] } (modify.APPLICATION.print(heap, current, o)[$o, $f]) <==> (false)))));

const unique STD_FILES: Type;

axiom (is_frozen(STD_FILES));

axiom ((STD_FILES) <: (ANY));

axiom ((forall t: Type :: { (STD_FILES) <: (t) } ((STD_FILES) <: (t)) <==> (((t) == (STD_FILES)) || ((ANY) <: (t)))));

axiom ((FieldId(allocated, STD_FILES)) == (-1));

axiom ((FieldId(closed, STD_FILES)) == (-2));

axiom ((FieldId(owner, STD_FILES)) == (-3));

axiom ((FieldId(owns, STD_FILES)) == (-4));

axiom ((FieldId(observers, STD_FILES)) == (-5));

axiom ((FieldId(subjects, STD_FILES)) == (-6));

axiom ((forall <T32> $f: Field T32 :: { IsModelField($f, STD_FILES) } (IsModelField($f, STD_FILES)) <==> ((($f) == (subjects)) || (($f) == (observers)))));

function { :inline } STD_FILES.user_inv(heap: HeapType, current: ref) returns (bool) {
  (Set#IsEmpty(heap[current, observers])) && (Set#IsEmpty(heap[current, subjects])) && (Set#IsEmpty(heap[current, owns])) && (admissibility2(heap, current))
}

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached_exact(heap, current, STD_FILES)) ==> ((user_inv(heap, current)) <==> (STD_FILES.user_inv(heap, current)))));

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached(heap, current, STD_FILES)) ==> ((user_inv(heap, current)) ==> (STD_FILES.user_inv(heap, current)))));

function modify.APPLICATION.io(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T33> $o: ref, $f: Field T33 :: { modify.APPLICATION.io(heap, current)[$o, $f] } (modify.APPLICATION.io(heap, current)[$o, $f]) <==> (false)))));

function modify.STD_FILES.read_integer(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T34> $o: ref, $f: Field T34 :: { modify.STD_FILES.read_integer(heap, current)[$o, $f] } (modify.STD_FILES.read_integer(heap, current)[$o, $f]) <==> (($o) == (current))))));

function modify.STD_FILES.last_integer(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T35> $o: ref, $f: Field T35 :: { modify.STD_FILES.last_integer(heap, current)[$o, $f] } (modify.STD_FILES.last_integer(heap, current)[$o, $f]) <==> (false)))));

function read.fun.STD_FILES.last_integer(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T36> $o: ref, $f: Field T36 :: { read.fun.STD_FILES.last_integer(heap, current)[$o, $f] } (read.fun.STD_FILES.last_integer(heap, current)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.STD_FILES.last_integer(heap: HeapType, current: ref) returns (bool) {
  true
}

function trigger.fun.STD_FILES.last_integer(heap: HeapType, current: ref) returns (bool);

procedure DIE.in_observers(Current: ref, new_observers: Set (ref), o: ref) returns (Result: bool where true);
  free requires attached_exact(Heap, Current, DIE); // info:type property for argument Current
  free requires Set#ItemsType(Heap, new_observers, ANY); // info:type property for argument new_observers
  free requires Heap[o, allocated]; // info:type property for argument o
  modifies Heap;
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.DIE.in_observers(Heap, Current, new_observers, o), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.DIE.in_observers(old(Heap), Current, new_observers, o));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.DIE.in_observers(Heap, Current, new_observers, o), readable);



function fun.DIE.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function fun0.DIE.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.DIE.in_observers(heap, current, new_observers, o) } { trigger.fun.DIE.in_observers(heap, current, new_observers, o) } (pre.fun.DIE.in_observers(heap, current, new_observers, o)) ==> ((fun.DIE.in_observers(heap, current, new_observers, o)) == (new_observers[o]))));

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.DIE.in_observers(heap, current, new_observers, o) } (fun.DIE.in_observers(heap, current, new_observers, o)) == (fun0.DIE.in_observers(heap, current, new_observers, o))));

axiom ((forall h: HeapType, h': HeapType, current: ref, new_observers: Set (ref), o: ref :: { HeapSucc(h, h'), fun0.DIE.in_observers(h, current, new_observers, o), fun0.DIE.in_observers(h', current, new_observers, o) } ((HeapSucc(h, h')) && (pre.fun.DIE.in_observers(h, current, new_observers, o)) && (pre.fun.DIE.in_observers(h', current, new_observers, o)) && (same_inside(h, h', read.fun.DIE.in_observers(h, current, new_observers, o)))) ==> ((fun0.DIE.in_observers(h, current, new_observers, o)) == (fun0.DIE.in_observers(h', current, new_observers, o)))));

const unique V_INPUT_STREAM^INTEGER_32^: Type;

axiom ((V_INPUT_STREAM^INTEGER_32^) <: (ANY));

axiom ((forall t: Type :: { (V_INPUT_STREAM^INTEGER_32^) <: (t) } ((V_INPUT_STREAM^INTEGER_32^) <: (t)) <==> (((t) == (V_INPUT_STREAM^INTEGER_32^)) || ((ANY) <: (t)))));

axiom ((FieldId(allocated, V_INPUT_STREAM^INTEGER_32^)) == (-1));

axiom ((FieldId(closed, V_INPUT_STREAM^INTEGER_32^)) == (-2));

axiom ((FieldId(owner, V_INPUT_STREAM^INTEGER_32^)) == (-3));

axiom ((FieldId(owns, V_INPUT_STREAM^INTEGER_32^)) == (-4));

axiom ((FieldId(observers, V_INPUT_STREAM^INTEGER_32^)) == (-5));

axiom ((FieldId(subjects, V_INPUT_STREAM^INTEGER_32^)) == (-6));

const V_RANDOM.box: Field (Set int);

axiom ((FieldId(V_RANDOM.box, V_RANDOM)) == (80));

const V_INPUT_STREAM^INTEGER_32^.box: Field (Set int);

axiom ((V_RANDOM.box) == (V_INPUT_STREAM^INTEGER_32^.box));

axiom ((forall heap: HeapType, current: ref, v: Set int, o: ref :: { guard(heap, current, V_RANDOM.box, v, o) } (attached_exact(heap, current, V_RANDOM)) ==> ((guard(heap, current, V_RANDOM.box, v, o)) <==> (false))));

axiom ((forall heap: HeapType, current: ref, v: Set int, o: ref :: { guard(heap, current, V_RANDOM.box, v, o) } (attached(heap, current, V_RANDOM)) ==> ((guard(heap, current, V_RANDOM.box, v, o)) ==> (false))));

procedure V_RANDOM.random_bits(Current: ref, v: int, n: int) returns (Result: int where is_integer_32(Result));
  free requires attached_exact(Heap, Current, V_RANDOM); // info:type property for argument Current
  free requires is_natural_64(v); // info:type property for argument v
  free requires is_integer_32(n); // info:type property for argument n
  modifies Heap;
  requires ((1) <= (n)) && ((n) <= (32)); // type:pre tag:n_in_bounds line:143
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.V_RANDOM.random_bits(Heap, Current, v, n), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.V_RANDOM.random_bits(old(Heap), Current, v, n));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.V_RANDOM.random_bits(Heap, Current, v, n), readable);
  free ensures (Result) == (fun.V_RANDOM.random_bits(old(Heap), Current, v, n));



function fun.V_RANDOM.random_bits(heap: HeapType, current: ref, v: int, n: int) returns (int);

axiom ((forall heap: HeapType, current: ref, v: int, n: int :: { fun.V_RANDOM.random_bits(heap, current, v, n) } (pre.fun.V_RANDOM.random_bits(heap, current, v, n)) ==> (is_integer_32(fun.V_RANDOM.random_bits(heap, current, v, n)))));

axiom ((forall h: HeapType, h': HeapType, current: ref, v: int, n: int :: { HeapSucc(h, h'), fun.V_RANDOM.random_bits(h, current, v, n), fun.V_RANDOM.random_bits(h', current, v, n) } ((HeapSucc(h, h')) && (pre.fun.V_RANDOM.random_bits(h, current, v, n)) && (pre.fun.V_RANDOM.random_bits(h', current, v, n)) && (same_inside(h, h', read.fun.V_RANDOM.random_bits(h, current, v, n)))) ==> ((fun.V_RANDOM.random_bits(h, current, v, n)) == (fun.V_RANDOM.random_bits(h', current, v, n)))));

const V_RANDOM.value: Field int;

axiom ((FieldId(V_RANDOM.value, V_RANDOM)) == (89));

axiom ((forall heap: HeapType, o: ref :: { heap[o, V_RANDOM.value] } ((IsHeap(heap)) && (attached(heap, o, V_RANDOM))) ==> (is_natural_64(heap[o, V_RANDOM.value]))));

axiom ((forall heap: HeapType, current: ref, v: int, o: ref :: { guard(heap, current, V_RANDOM.value, v, o) } (attached_exact(heap, current, V_RANDOM)) ==> ((guard(heap, current, V_RANDOM.value, v, o)) <==> ((user_inv(heap, o)) ==> (user_inv(heap[current, V_RANDOM.value := v], o))))));

axiom ((forall heap: HeapType, current: ref, v: int, o: ref :: { guard(heap, current, V_RANDOM.value, v, o) } (attached(heap, current, V_RANDOM)) ==> ((guard(heap, current, V_RANDOM.value, v, o)) ==> ((user_inv(heap, o)) ==> (user_inv(heap[current, V_RANDOM.value := v], o))))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, owns, v, o) } (attached_exact(heap, current, V_RANDOM)) ==> ((guard(heap, current, owns, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, subjects, v, o) } (attached_exact(heap, current, V_RANDOM)) ==> ((guard(heap, current, subjects, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached_exact(heap, current, V_RANDOM)) ==> ((guard(heap, current, observers, v, o)) <==> (fun.V_RANDOM.in_observers(heap, current, v, o)))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached(heap, current, V_RANDOM)) ==> ((guard(heap, current, observers, v, o)) ==> (fun.V_RANDOM.in_observers(heap, current, v, o)))));

function modify.V_RANDOM.default_create(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T37> $o: ref, $f: Field T37 :: { modify.V_RANDOM.default_create(heap, current)[$o, $f] } (modify.V_RANDOM.default_create(heap, current)[$o, $f]) <==> (($o) == (current))))));

procedure V_RANDOM.off(Current: ref) returns (Result: bool where true);
  free requires attached_exact(Heap, Current, V_RANDOM); // info:type property for argument Current
  modifies Heap;
  requires (forall i_104: ref :: (Heap[Current, subjects][i_104]) ==> (is_closed(Heap, i_104))); // type:pre tag:subjects_closed line:28
  ensures (Result) == (Set#IsEmpty(Heap[Current, V_RANDOM.box])); // type:post tag:definition line:31
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.V_RANDOM.off(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.V_RANDOM.off(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.V_RANDOM.off(Heap, Current), readable);
  requires is_closed(Heap, Current); // type:pre tag:default_is_closed default:contracts
  free ensures (Result) == (fun.V_RANDOM.off(old(Heap), Current));



function fun.V_RANDOM.off(heap: HeapType, current: ref) returns (bool);

axiom ((forall heap: HeapType, current: ref :: { fun.V_RANDOM.off(heap, current) } (pre.fun.V_RANDOM.off(heap, current)) ==> ((fun.V_RANDOM.off(heap, current)) == (Set#IsEmpty(heap[current, V_RANDOM.box])))));

axiom ((forall h: HeapType, h': HeapType, current: ref :: { HeapSucc(h, h'), fun.V_RANDOM.off(h, current), fun.V_RANDOM.off(h', current) } ((HeapSucc(h, h')) && (pre.fun.V_RANDOM.off(h, current)) && (pre.fun.V_RANDOM.off(h', current)) && (same_inside(h, h', read.fun.V_RANDOM.off(h, current)))) ==> ((fun.V_RANDOM.off(h, current)) == (fun.V_RANDOM.off(h', current)))));

function modify.V_RANDOM.forth(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T38> $o: ref, $f: Field T38 :: { modify.V_RANDOM.forth(heap, current)[$o, $f] } (modify.V_RANDOM.forth(heap, current)[$o, $f]) <==> ((($o) == (current)) && ((!(IsModelField($f, V_RANDOM))) || (($f) == (V_RANDOM.box))))))));

function modify.V_RANDOM.bounded_item(heap: HeapType, current: ref, min: int, max: int) returns (Frame);

axiom ((forall heap: HeapType, current: ref, min: int, max: int :: (IsHeap(heap)) ==> ((forall <T39> $o: ref, $f: Field T39 :: { modify.V_RANDOM.bounded_item(heap, current, min, max)[$o, $f] } (modify.V_RANDOM.bounded_item(heap, current, min, max)[$o, $f]) <==> (false)))));

function read.fun.V_RANDOM.bounded_item(heap: HeapType, current: ref, min: int, max: int) returns (Frame);

axiom ((forall heap: HeapType, current: ref, min: int, max: int :: (IsHeap(heap)) ==> ((forall <T40> $o: ref, $f: Field T40 :: { read.fun.V_RANDOM.bounded_item(heap, current, min, max)[$o, $f] } (read.fun.V_RANDOM.bounded_item(heap, current, min, max)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.V_RANDOM.bounded_item(heap: HeapType, current: ref, min: int, max: int) returns (bool) {
  ((max) >= (min)) && (is_closed(heap, current))
}

function trigger.fun.V_RANDOM.bounded_item(heap: HeapType, current: ref, min: int, max: int) returns (bool);

const unique V_MUTABLE_SEQUENCE^PLAYER^: Type;

axiom ((V_MUTABLE_SEQUENCE^PLAYER^) <: (V_SEQUENCE^PLAYER^));

axiom ((forall t: Type :: { (V_MUTABLE_SEQUENCE^PLAYER^) <: (t) } ((V_MUTABLE_SEQUENCE^PLAYER^) <: (t)) <==> (((t) == (V_MUTABLE_SEQUENCE^PLAYER^)) || ((V_SEQUENCE^PLAYER^) <: (t)))));

axiom ((FieldId(allocated, V_MUTABLE_SEQUENCE^PLAYER^)) == (-1));

axiom ((FieldId(closed, V_MUTABLE_SEQUENCE^PLAYER^)) == (-2));

axiom ((FieldId(owner, V_MUTABLE_SEQUENCE^PLAYER^)) == (-3));

axiom ((FieldId(owns, V_MUTABLE_SEQUENCE^PLAYER^)) == (-4));

axiom ((FieldId(observers, V_MUTABLE_SEQUENCE^PLAYER^)) == (-5));

axiom ((FieldId(subjects, V_MUTABLE_SEQUENCE^PLAYER^)) == (-6));

const unique V_SEQUENCE^PLAYER^: Type;

axiom ((V_SEQUENCE^PLAYER^) <: (V_CONTAINER^PLAYER^));

axiom ((forall t: Type :: { (V_SEQUENCE^PLAYER^) <: (t) } ((V_SEQUENCE^PLAYER^) <: (t)) <==> (((t) == (V_SEQUENCE^PLAYER^)) || ((V_CONTAINER^PLAYER^) <: (t)))));

axiom ((FieldId(allocated, V_SEQUENCE^PLAYER^)) == (-1));

axiom ((FieldId(closed, V_SEQUENCE^PLAYER^)) == (-2));

axiom ((FieldId(owner, V_SEQUENCE^PLAYER^)) == (-3));

axiom ((FieldId(owns, V_SEQUENCE^PLAYER^)) == (-4));

axiom ((FieldId(observers, V_SEQUENCE^PLAYER^)) == (-5));

axiom ((FieldId(subjects, V_SEQUENCE^PLAYER^)) == (-6));

procedure GAME.in_observers(Current: ref, new_observers: Set (ref), o: ref) returns (Result: bool where true);
  free requires attached_exact(Heap, Current, GAME); // info:type property for argument Current
  free requires Set#ItemsType(Heap, new_observers, ANY); // info:type property for argument new_observers
  free requires Heap[o, allocated]; // info:type property for argument o
  modifies Heap;
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.GAME.in_observers(Heap, Current, new_observers, o), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.GAME.in_observers(old(Heap), Current, new_observers, o));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.GAME.in_observers(Heap, Current, new_observers, o), readable);



function fun.GAME.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function fun0.GAME.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.GAME.in_observers(heap, current, new_observers, o) } { trigger.fun.GAME.in_observers(heap, current, new_observers, o) } (pre.fun.GAME.in_observers(heap, current, new_observers, o)) ==> ((fun.GAME.in_observers(heap, current, new_observers, o)) == (new_observers[o]))));

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.GAME.in_observers(heap, current, new_observers, o) } (fun.GAME.in_observers(heap, current, new_observers, o)) == (fun0.GAME.in_observers(heap, current, new_observers, o))));

axiom ((forall h: HeapType, h': HeapType, current: ref, new_observers: Set (ref), o: ref :: { HeapSucc(h, h'), fun0.GAME.in_observers(h, current, new_observers, o), fun0.GAME.in_observers(h', current, new_observers, o) } ((HeapSucc(h, h')) && (pre.fun.GAME.in_observers(h, current, new_observers, o)) && (pre.fun.GAME.in_observers(h', current, new_observers, o)) && (same_inside(h, h', read.fun.GAME.in_observers(h, current, new_observers, o)))) ==> ((fun0.GAME.in_observers(h, current, new_observers, o)) == (fun0.GAME.in_observers(h', current, new_observers, o)))));

const V_ARRAY^PLAYER^.bag: Field (Bag (ref));

axiom ((FieldId(V_ARRAY^PLAYER^.bag, V_ARRAY^PLAYER^)) == (80));

const V_MUTABLE_SEQUENCE^PLAYER^.bag: Field (Bag (ref));

axiom ((V_ARRAY^PLAYER^.bag) == (V_MUTABLE_SEQUENCE^PLAYER^.bag));

const V_SEQUENCE^PLAYER^.bag: Field (Bag (ref));

axiom ((V_ARRAY^PLAYER^.bag) == (V_SEQUENCE^PLAYER^.bag));

const V_CONTAINER^PLAYER^.bag: Field (Bag (ref));

axiom ((V_ARRAY^PLAYER^.bag) == (V_CONTAINER^PLAYER^.bag));

axiom ((forall heap: HeapType, o: ref :: { heap[o, V_ARRAY^PLAYER^.bag] } ((IsHeap(heap)) && (attached(heap, o, V_ARRAY^PLAYER^))) ==> ((Bag#DomainType(heap, heap[o, V_ARRAY^PLAYER^.bag], PLAYER)) && (Bag#IsValid(heap[o, V_ARRAY^PLAYER^.bag])))));

axiom ((forall heap: HeapType, current: ref, v: Bag (ref), o: ref :: { guard(heap, current, V_ARRAY^PLAYER^.bag, v, o) } (attached_exact(heap, current, V_ARRAY^PLAYER^)) ==> ((guard(heap, current, V_ARRAY^PLAYER^.bag, v, o)) <==> (false))));

axiom ((forall heap: HeapType, current: ref, v: Bag (ref), o: ref :: { guard(heap, current, V_ARRAY^PLAYER^.bag, v, o) } (attached(heap, current, V_ARRAY^PLAYER^)) ==> ((guard(heap, current, V_ARRAY^PLAYER^.bag, v, o)) ==> (false))));

const V_ARRAY^PLAYER^.area: Field (ref);

axiom ((FieldId(V_ARRAY^PLAYER^.area, V_ARRAY^PLAYER^)) == (116));

axiom ((forall heap: HeapType, o: ref :: { heap[o, V_ARRAY^PLAYER^.area] } ((IsHeap(heap)) && (attached(heap, o, V_ARRAY^PLAYER^))) ==> (detachable(heap, heap[o, V_ARRAY^PLAYER^.area], V_SPECIAL^PLAYER^))));

axiom ((forall heap: HeapType, current: ref, v: ref, o: ref :: { guard(heap, current, V_ARRAY^PLAYER^.area, v, o) } (attached_exact(heap, current, V_ARRAY^PLAYER^)) ==> ((guard(heap, current, V_ARRAY^PLAYER^.area, v, o)) <==> (false))));

axiom ((forall heap: HeapType, current: ref, v: ref, o: ref :: { guard(heap, current, V_ARRAY^PLAYER^.area, v, o) } (attached(heap, current, V_ARRAY^PLAYER^)) ==> ((guard(heap, current, V_ARRAY^PLAYER^.area, v, o)) ==> (false))));

const V_ARRAY^PLAYER^.lower: Field int;

axiom ((FieldId(V_ARRAY^PLAYER^.lower, V_ARRAY^PLAYER^)) == (103));

axiom ((forall heap: HeapType, o: ref :: { heap[o, V_ARRAY^PLAYER^.lower] } ((IsHeap(heap)) && (attached(heap, o, V_ARRAY^PLAYER^))) ==> (is_integer_32(heap[o, V_ARRAY^PLAYER^.lower]))));

axiom ((forall heap: HeapType, current: ref, v: int, o: ref :: { guard(heap, current, V_ARRAY^PLAYER^.lower, v, o) } (attached_exact(heap, current, V_ARRAY^PLAYER^)) ==> ((guard(heap, current, V_ARRAY^PLAYER^.lower, v, o)) <==> (false))));

axiom ((forall heap: HeapType, current: ref, v: int, o: ref :: { guard(heap, current, V_ARRAY^PLAYER^.lower, v, o) } (attached(heap, current, V_ARRAY^PLAYER^)) ==> ((guard(heap, current, V_ARRAY^PLAYER^.lower, v, o)) ==> (false))));

const V_ARRAY^PLAYER^.upper: Field int;

axiom ((FieldId(V_ARRAY^PLAYER^.upper, V_ARRAY^PLAYER^)) == (104));

axiom ((forall heap: HeapType, o: ref :: { heap[o, V_ARRAY^PLAYER^.upper] } ((IsHeap(heap)) && (attached(heap, o, V_ARRAY^PLAYER^))) ==> (is_integer_32(heap[o, V_ARRAY^PLAYER^.upper]))));

axiom ((forall heap: HeapType, current: ref, v: int, o: ref :: { guard(heap, current, V_ARRAY^PLAYER^.upper, v, o) } (attached_exact(heap, current, V_ARRAY^PLAYER^)) ==> ((guard(heap, current, V_ARRAY^PLAYER^.upper, v, o)) <==> (false))));

axiom ((forall heap: HeapType, current: ref, v: int, o: ref :: { guard(heap, current, V_ARRAY^PLAYER^.upper, v, o) } (attached(heap, current, V_ARRAY^PLAYER^)) ==> ((guard(heap, current, V_ARRAY^PLAYER^.upper, v, o)) ==> (false))));

const V_SPECIAL^PLAYER^.sequence: Field (Seq (ref));

axiom ((FieldId(V_SPECIAL^PLAYER^.sequence, V_SPECIAL^PLAYER^)) == (96));

axiom ((forall heap: HeapType, o: ref :: { heap[o, V_SPECIAL^PLAYER^.sequence] } ((IsHeap(heap)) && (attached(heap, o, V_SPECIAL^PLAYER^))) ==> (Seq#ItemsType(heap, heap[o, V_SPECIAL^PLAYER^.sequence], PLAYER))));

axiom ((forall heap: HeapType, current: ref, v: Seq (ref), o: ref :: { guard(heap, current, V_SPECIAL^PLAYER^.sequence, v, o) } (attached_exact(heap, current, V_SPECIAL^PLAYER^)) ==> ((guard(heap, current, V_SPECIAL^PLAYER^.sequence, v, o)) <==> (false))));

axiom ((forall heap: HeapType, current: ref, v: Seq (ref), o: ref :: { guard(heap, current, V_SPECIAL^PLAYER^.sequence, v, o) } (attached(heap, current, V_SPECIAL^PLAYER^)) ==> ((guard(heap, current, V_SPECIAL^PLAYER^.sequence, v, o)) ==> (false))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, owns, v, o) } (attached_exact(heap, current, V_ARRAY^PLAYER^)) ==> ((guard(heap, current, owns, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, subjects, v, o) } (attached_exact(heap, current, V_ARRAY^PLAYER^)) ==> ((guard(heap, current, subjects, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached_exact(heap, current, V_ARRAY^PLAYER^)) ==> ((guard(heap, current, observers, v, o)) <==> (fun.V_ARRAY^PLAYER^.in_observers(heap, current, v, o)))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached(heap, current, V_ARRAY^PLAYER^)) ==> ((guard(heap, current, observers, v, o)) ==> (fun.V_ARRAY^PLAYER^.in_observers(heap, current, v, o)))));

function modify.V_ARRAY^PLAYER^.make(heap: HeapType, current: ref, l: int, u: int) returns (Frame);

axiom ((forall heap: HeapType, current: ref, l: int, u: int :: (IsHeap(heap)) ==> ((forall <T41> $o: ref, $f: Field T41 :: { modify.V_ARRAY^PLAYER^.make(heap, current, l, u)[$o, $f] } (modify.V_ARRAY^PLAYER^.make(heap, current, l, u)[$o, $f]) <==> (($o) == (current))))));

function modify.V_ARRAY^PLAYER^.count(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T42> $o: ref, $f: Field T42 :: { modify.V_ARRAY^PLAYER^.count(heap, current)[$o, $f] } (modify.V_ARRAY^PLAYER^.count(heap, current)[$o, $f]) <==> (false)))));

function read.fun.V_ARRAY^PLAYER^.count(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T43> $o: ref, $f: Field T43 :: { read.fun.V_ARRAY^PLAYER^.count(heap, current)[$o, $f] } (read.fun.V_ARRAY^PLAYER^.count(heap, current)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.V_ARRAY^PLAYER^.count(heap: HeapType, current: ref) returns (bool) {
  is_closed(heap, current)
}

function trigger.fun.V_ARRAY^PLAYER^.count(heap: HeapType, current: ref) returns (bool);

function pre.fun.MML_SEQUENCE^PLAYER^.item(current: Seq (ref), i: int) returns (bool) {
  ((1) <= (i)) && ((i) <= (Seq#Length(current)))
}

function trigger.fun.MML_SEQUENCE^PLAYER^.item(current: Seq (ref), i: int) returns (bool);

procedure V_ARRAY^PLAYER^.has_index(Current: ref, i: int) returns (Result: bool where true);
  free requires attached_exact(Heap, Current, V_ARRAY^PLAYER^); // info:type property for argument Current
  free requires is_integer_32(i); // info:type property for argument i
  modifies Heap;
  ensures (Result) == (((Heap[Current, V_ARRAY^PLAYER^.lower_]) <= (i)) && ((i) <= (fun.V_ARRAY^PLAYER^.upper_(Heap, Current)))); // type:post line:92
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.V_ARRAY^PLAYER^.has_index(Heap, Current, i), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.V_ARRAY^PLAYER^.has_index(old(Heap), Current, i));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.V_ARRAY^PLAYER^.has_index(Heap, Current, i), readable);
  requires is_closed(Heap, Current); // type:pre tag:default_is_closed default:contracts
  free ensures (Result) == (fun.V_ARRAY^PLAYER^.has_index(old(Heap), Current, i));



function fun.V_ARRAY^PLAYER^.has_index(heap: HeapType, current: ref, i: int) returns (bool);

axiom ((forall heap: HeapType, current: ref, i: int :: { fun.V_ARRAY^PLAYER^.has_index(heap, current, i) } (pre.fun.V_ARRAY^PLAYER^.has_index(heap, current, i)) ==> ((fun.V_ARRAY^PLAYER^.has_index(heap, current, i)) == (((heap[current, V_ARRAY^PLAYER^.lower_]) <= (i)) && ((i) <= (fun.V_ARRAY^PLAYER^.upper_(heap, current)))))));

axiom ((forall h: HeapType, h': HeapType, current: ref, i: int :: { HeapSucc(h, h'), fun.V_ARRAY^PLAYER^.has_index(h, current, i), fun.V_ARRAY^PLAYER^.has_index(h', current, i) } ((HeapSucc(h, h')) && (pre.fun.V_ARRAY^PLAYER^.has_index(h, current, i)) && (pre.fun.V_ARRAY^PLAYER^.has_index(h', current, i)) && (same_inside(h, h', read.fun.V_ARRAY^PLAYER^.has_index(h, current, i)))) ==> ((fun.V_ARRAY^PLAYER^.has_index(h, current, i)) == (fun.V_ARRAY^PLAYER^.has_index(h', current, i)))));

procedure V_ARRAY^PLAYER^.idx(Current: ref, i: int) returns (Result: int where is_integer_32(Result));
  free requires attached_exact(Heap, Current, V_ARRAY^PLAYER^); // info:type property for argument Current
  free requires is_integer_32(i); // info:type property for argument i
  modifies Heap;
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.V_ARRAY^PLAYER^.idx(Heap, Current, i), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.V_ARRAY^PLAYER^.idx(old(Heap), Current, i));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.V_ARRAY^PLAYER^.idx(Heap, Current, i), readable);



function fun.V_ARRAY^PLAYER^.idx(heap: HeapType, current: ref, i: int) returns (int);

function fun0.V_ARRAY^PLAYER^.idx(heap: HeapType, current: ref, i: int) returns (int);

axiom ((forall heap: HeapType, current: ref, i: int :: { fun.V_ARRAY^PLAYER^.idx(heap, current, i) } (pre.fun.V_ARRAY^PLAYER^.idx(heap, current, i)) ==> (is_integer_32(fun.V_ARRAY^PLAYER^.idx(heap, current, i)))));

axiom ((forall heap: HeapType, current: ref, i: int :: { fun.V_ARRAY^PLAYER^.idx(heap, current, i) } { trigger.fun.V_ARRAY^PLAYER^.idx(heap, current, i) } (pre.fun.V_ARRAY^PLAYER^.idx(heap, current, i)) ==> ((fun.V_ARRAY^PLAYER^.idx(heap, current, i)) == (((i) - (heap[current, V_ARRAY^PLAYER^.lower_])) + (1)))));

axiom ((forall heap: HeapType, current: ref, i: int :: { fun.V_ARRAY^PLAYER^.idx(heap, current, i) } (fun.V_ARRAY^PLAYER^.idx(heap, current, i)) == (fun0.V_ARRAY^PLAYER^.idx(heap, current, i))));

axiom ((forall h: HeapType, h': HeapType, current: ref, i: int :: { HeapSucc(h, h'), fun0.V_ARRAY^PLAYER^.idx(h, current, i), fun0.V_ARRAY^PLAYER^.idx(h', current, i) } ((HeapSucc(h, h')) && (pre.fun.V_ARRAY^PLAYER^.idx(h, current, i)) && (pre.fun.V_ARRAY^PLAYER^.idx(h', current, i)) && (same_inside(h, h', read.fun.V_ARRAY^PLAYER^.idx(h, current, i)))) ==> ((fun0.V_ARRAY^PLAYER^.idx(h, current, i)) == (fun0.V_ARRAY^PLAYER^.idx(h', current, i)))));

function modify.V_ARRAY^PLAYER^.put(heap: HeapType, current: ref, v: ref, i: int) returns (Frame);

axiom ((forall heap: HeapType, current: ref, v: ref, i: int :: (IsHeap(heap)) ==> ((forall <T44> $o: ref, $f: Field T44 :: { modify.V_ARRAY^PLAYER^.put(heap, current, v, i)[$o, $f] } (modify.V_ARRAY^PLAYER^.put(heap, current, v, i)[$o, $f]) <==> ((($o) == (current)) && ((!(IsModelField($f, V_ARRAY^PLAYER^))) || (($f) == (V_ARRAY^PLAYER^.sequence)) || (($f) == (V_ARRAY^PLAYER^.bag))))))));

function modify.GAME.print(heap: HeapType, current: ref, o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, o: ref :: (IsHeap(heap)) ==> ((forall <T45> $o: ref, $f: Field T45 :: { modify.GAME.print(heap, current, o)[$o, $f] } (modify.GAME.print(heap, current, o)[$o, $f]) <==> (false)))));

function modify.V_ARRAY^PLAYER^.item(heap: HeapType, current: ref, i: int) returns (Frame);

axiom ((forall heap: HeapType, current: ref, i: int :: (IsHeap(heap)) ==> ((forall <T46> $o: ref, $f: Field T46 :: { modify.V_ARRAY^PLAYER^.item(heap, current, i)[$o, $f] } (modify.V_ARRAY^PLAYER^.item(heap, current, i)[$o, $f]) <==> (false)))));

function read.fun.V_ARRAY^PLAYER^.item(heap: HeapType, current: ref, i: int) returns (Frame);

axiom ((forall heap: HeapType, current: ref, i: int :: (IsHeap(heap)) ==> ((forall <T47> $o: ref, $f: Field T47 :: { read.fun.V_ARRAY^PLAYER^.item(heap, current, i)[$o, $f] } (read.fun.V_ARRAY^PLAYER^.item(heap, current, i)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.V_ARRAY^PLAYER^.item(heap: HeapType, current: ref, i: int) returns (bool) {
  (fun.V_ARRAY^PLAYER^.has_index(heap, current, i)) && (is_closed(heap, current))
}

function trigger.fun.V_ARRAY^PLAYER^.item(heap: HeapType, current: ref, i: int) returns (bool);

function modify.GAME.io(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T48> $o: ref, $f: Field T48 :: { modify.GAME.io(heap, current)[$o, $f] } (modify.GAME.io(heap, current)[$o, $f]) <==> (false)))));

function modify.STD_FILES.put_new_line(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T49> $o: ref, $f: Field T49 :: { modify.STD_FILES.put_new_line(heap, current)[$o, $f] } (modify.STD_FILES.put_new_line(heap, current)[$o, $f]) <==> (($o) == (current))))));

function modify.V_STRING.multiply(heap: HeapType, current: ref, n: int) returns (Frame);

axiom ((forall heap: HeapType, current: ref, n: int :: (IsHeap(heap)) ==> ((forall <T50> $o: ref, $f: Field T50 :: { modify.V_STRING.multiply(heap, current, n)[$o, $f] } (modify.V_STRING.multiply(heap, current, n)[$o, $f]) <==> (($o) == (current))))));

function modify.ANY.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T51> $o: ref, $f: Field T51 :: { modify.ANY.in_observers(heap, current, new_observers, o)[$o, $f] } (modify.ANY.in_observers(heap, current, new_observers, o)[$o, $f]) <==> (false)))));

function read.fun.ANY.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T52> $o: ref, $f: Field T52 :: { read.fun.ANY.in_observers(heap, current, new_observers, o)[$o, $f] } (read.fun.ANY.in_observers(heap, current, new_observers, o)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.ANY.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool) {
  true
}

function trigger.fun.ANY.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function modify.PLAYER.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T53> $o: ref, $f: Field T53 :: { modify.PLAYER.in_observers(heap, current, new_observers, o)[$o, $f] } (modify.PLAYER.in_observers(heap, current, new_observers, o)[$o, $f]) <==> (false)))));

function read.fun.PLAYER.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T54> $o: ref, $f: Field T54 :: { read.fun.PLAYER.in_observers(heap, current, new_observers, o)[$o, $f] } (read.fun.PLAYER.in_observers(heap, current, new_observers, o)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.PLAYER.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool) {
  true
}

function trigger.fun.PLAYER.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

const unique STRING_8: Type;

axiom ((STRING_8) <: (READABLE_STRING_8));

axiom ((STRING_8) <: (STRING_GENERAL));

axiom ((STRING_8) <: (INDEXABLE^CHARACTER_8#INTEGER_32^));

axiom ((STRING_8) <: (RESIZABLE^CHARACTER_8^));

axiom ((STRING_8) <: (TO_SPECIAL^CHARACTER_8^));

axiom ((STRING_8) <: (MISMATCH_CORRECTOR));

axiom ((forall t: Type :: { (STRING_8) <: (t) } ((STRING_8) <: (t)) <==> (((t) == (STRING_8)) || ((READABLE_STRING_8) <: (t)) || ((STRING_GENERAL) <: (t)) || ((INDEXABLE^CHARACTER_8#INTEGER_32^) <: (t)) || ((RESIZABLE^CHARACTER_8^) <: (t)) || ((TO_SPECIAL^CHARACTER_8^) <: (t)) || ((MISMATCH_CORRECTOR) <: (t)))));

axiom ((FieldId(allocated, STRING_8)) == (-1));

axiom ((FieldId(closed, STRING_8)) == (-2));

axiom ((FieldId(owner, STRING_8)) == (-3));

axiom ((FieldId(owns, STRING_8)) == (-4));

axiom ((FieldId(observers, STRING_8)) == (-5));

axiom ((FieldId(subjects, STRING_8)) == (-6));

axiom ((forall <T55> $f: Field T55 :: { IsModelField($f, STRING_8) } (IsModelField($f, STRING_8)) <==> ((($f) == (subjects)) || (($f) == (observers)))));

function { :inline } STRING_8.user_inv(heap: HeapType, current: ref) returns (bool) {
  (!(fun.STRING_8.is_less(heap, current, current))) && ((heap[current, STRING_8.area]) != (Void)) && (!(fun.STRING_8.is_immutable(heap, current))) && ((fun.STRING_8.is_empty(heap, current)) == ((heap[current, STRING_8.count]) == (0))) && ((heap[current, STRING_8.count]) <= (fun.STRING_8.capacity(heap, current))) && ((fun.STRING_8.full(heap, current)) == ((heap[current, STRING_8.count]) == (fun.STRING_8.capacity(heap, current)))) && ((5) >= (1)) && (!(heap[current, STRING_8.object_comparison])) && (Set#IsEmpty(heap[current, observers])) && (Set#IsEmpty(heap[current, subjects])) && (Set#IsEmpty(heap[current, owns])) && (admissibility2(heap, current))
}

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached_exact(heap, current, STRING_8)) ==> ((user_inv(heap, current)) <==> (STRING_8.user_inv(heap, current)))));

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached(heap, current, STRING_8)) ==> ((user_inv(heap, current)) ==> (STRING_8.user_inv(heap, current)))));

procedure V_STRING.in_observers(Current: ref, new_observers: Set (ref), o: ref) returns (Result: bool where true);
  free requires attached_exact(Heap, Current, V_STRING); // info:type property for argument Current
  free requires Set#ItemsType(Heap, new_observers, ANY); // info:type property for argument new_observers
  free requires Heap[o, allocated]; // info:type property for argument o
  modifies Heap;
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.V_STRING.in_observers(Heap, Current, new_observers, o), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.V_STRING.in_observers(old(Heap), Current, new_observers, o));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.V_STRING.in_observers(Heap, Current, new_observers, o), readable);



function fun.V_STRING.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function fun0.V_STRING.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.V_STRING.in_observers(heap, current, new_observers, o) } { trigger.fun.V_STRING.in_observers(heap, current, new_observers, o) } (pre.fun.V_STRING.in_observers(heap, current, new_observers, o)) ==> ((fun.V_STRING.in_observers(heap, current, new_observers, o)) == (new_observers[o]))));

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.V_STRING.in_observers(heap, current, new_observers, o) } (fun.V_STRING.in_observers(heap, current, new_observers, o)) == (fun0.V_STRING.in_observers(heap, current, new_observers, o))));

axiom ((forall h: HeapType, h': HeapType, current: ref, new_observers: Set (ref), o: ref :: { HeapSucc(h, h'), fun0.V_STRING.in_observers(h, current, new_observers, o), fun0.V_STRING.in_observers(h', current, new_observers, o) } ((HeapSucc(h, h')) && (pre.fun.V_STRING.in_observers(h, current, new_observers, o)) && (pre.fun.V_STRING.in_observers(h', current, new_observers, o)) && (same_inside(h, h', read.fun.V_STRING.in_observers(h, current, new_observers, o)))) ==> ((fun0.V_STRING.in_observers(h, current, new_observers, o)) == (fun0.V_STRING.in_observers(h', current, new_observers, o)))));

function modify.APPLICATION.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T56> $o: ref, $f: Field T56 :: { modify.APPLICATION.in_observers(heap, current, new_observers, o)[$o, $f] } (modify.APPLICATION.in_observers(heap, current, new_observers, o)[$o, $f]) <==> (false)))));

function read.fun.APPLICATION.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T57> $o: ref, $f: Field T57 :: { read.fun.APPLICATION.in_observers(heap, current, new_observers, o)[$o, $f] } (read.fun.APPLICATION.in_observers(heap, current, new_observers, o)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.APPLICATION.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool) {
  true
}

function trigger.fun.APPLICATION.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, owns, v, o) } (attached_exact(heap, current, STD_FILES)) ==> ((guard(heap, current, owns, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, subjects, v, o) } (attached_exact(heap, current, STD_FILES)) ==> ((guard(heap, current, subjects, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached_exact(heap, current, STD_FILES)) ==> ((guard(heap, current, observers, v, o)) <==> (fun.STD_FILES.in_observers(heap, current, v, o)))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached(heap, current, STD_FILES)) ==> ((guard(heap, current, observers, v, o)) ==> (fun.STD_FILES.in_observers(heap, current, v, o)))));

function modify.DIE.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T58> $o: ref, $f: Field T58 :: { modify.DIE.in_observers(heap, current, new_observers, o)[$o, $f] } (modify.DIE.in_observers(heap, current, new_observers, o)[$o, $f]) <==> (false)))));

function read.fun.DIE.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T59> $o: ref, $f: Field T59 :: { read.fun.DIE.in_observers(heap, current, new_observers, o)[$o, $f] } (read.fun.DIE.in_observers(heap, current, new_observers, o)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.DIE.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool) {
  true
}

function trigger.fun.DIE.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function modify.V_RANDOM.random_bits(heap: HeapType, current: ref, v: int, n: int) returns (Frame);

axiom ((forall heap: HeapType, current: ref, v: int, n: int :: (IsHeap(heap)) ==> ((forall <T60> $o: ref, $f: Field T60 :: { modify.V_RANDOM.random_bits(heap, current, v, n)[$o, $f] } (modify.V_RANDOM.random_bits(heap, current, v, n)[$o, $f]) <==> (false)))));

function read.fun.V_RANDOM.random_bits(heap: HeapType, current: ref, v: int, n: int) returns (Frame);

axiom ((forall heap: HeapType, current: ref, v: int, n: int :: (IsHeap(heap)) ==> ((forall <T61> $o: ref, $f: Field T61 :: { read.fun.V_RANDOM.random_bits(heap, current, v, n)[$o, $f] } (read.fun.V_RANDOM.random_bits(heap, current, v, n)[$o, $f]) <==> ((false) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.V_RANDOM.random_bits(heap: HeapType, current: ref, v: int, n: int) returns (bool) {
  ((1) <= (n)) && ((n) <= (32))
}

function trigger.fun.V_RANDOM.random_bits(heap: HeapType, current: ref, v: int, n: int) returns (bool);

procedure V_RANDOM.in_observers(Current: ref, new_observers: Set (ref), o: ref) returns (Result: bool where true);
  free requires attached_exact(Heap, Current, V_RANDOM); // info:type property for argument Current
  free requires Set#ItemsType(Heap, new_observers, ANY); // info:type property for argument new_observers
  free requires Heap[o, allocated]; // info:type property for argument o
  modifies Heap;
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.V_RANDOM.in_observers(Heap, Current, new_observers, o), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.V_RANDOM.in_observers(old(Heap), Current, new_observers, o));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.V_RANDOM.in_observers(Heap, Current, new_observers, o), readable);



function fun.V_RANDOM.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function fun0.V_RANDOM.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.V_RANDOM.in_observers(heap, current, new_observers, o) } { trigger.fun.V_RANDOM.in_observers(heap, current, new_observers, o) } (pre.fun.V_RANDOM.in_observers(heap, current, new_observers, o)) ==> ((fun.V_RANDOM.in_observers(heap, current, new_observers, o)) == (new_observers[o]))));

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.V_RANDOM.in_observers(heap, current, new_observers, o) } (fun.V_RANDOM.in_observers(heap, current, new_observers, o)) == (fun0.V_RANDOM.in_observers(heap, current, new_observers, o))));

axiom ((forall h: HeapType, h': HeapType, current: ref, new_observers: Set (ref), o: ref :: { HeapSucc(h, h'), fun0.V_RANDOM.in_observers(h, current, new_observers, o), fun0.V_RANDOM.in_observers(h', current, new_observers, o) } ((HeapSucc(h, h')) && (pre.fun.V_RANDOM.in_observers(h, current, new_observers, o)) && (pre.fun.V_RANDOM.in_observers(h', current, new_observers, o)) && (same_inside(h, h', read.fun.V_RANDOM.in_observers(h, current, new_observers, o)))) ==> ((fun0.V_RANDOM.in_observers(h, current, new_observers, o)) == (fun0.V_RANDOM.in_observers(h', current, new_observers, o)))));

function modify.V_RANDOM.off(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T62> $o: ref, $f: Field T62 :: { modify.V_RANDOM.off(heap, current)[$o, $f] } (modify.V_RANDOM.off(heap, current)[$o, $f]) <==> (false)))));

function read.fun.V_RANDOM.off(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T63> $o: ref, $f: Field T63 :: { read.fun.V_RANDOM.off(heap, current)[$o, $f] } (read.fun.V_RANDOM.off(heap, current)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.V_RANDOM.off(heap: HeapType, current: ref) returns (bool) {
  ((forall i_106: ref :: (heap[current, subjects][i_106]) ==> (is_closed(heap, i_106)))) && (is_closed(heap, current))
}

function trigger.fun.V_RANDOM.off(heap: HeapType, current: ref) returns (bool);

const unique V_CONTAINER^PLAYER^: Type;

axiom ((V_CONTAINER^PLAYER^) <: (ITERABLE^PLAYER^));

axiom ((forall t: Type :: { (V_CONTAINER^PLAYER^) <: (t) } ((V_CONTAINER^PLAYER^) <: (t)) <==> (((t) == (V_CONTAINER^PLAYER^)) || ((ITERABLE^PLAYER^) <: (t)))));

axiom ((FieldId(allocated, V_CONTAINER^PLAYER^)) == (-1));

axiom ((FieldId(closed, V_CONTAINER^PLAYER^)) == (-2));

axiom ((FieldId(owner, V_CONTAINER^PLAYER^)) == (-3));

axiom ((FieldId(owns, V_CONTAINER^PLAYER^)) == (-4));

axiom ((FieldId(observers, V_CONTAINER^PLAYER^)) == (-5));

axiom ((FieldId(subjects, V_CONTAINER^PLAYER^)) == (-6));

function modify.GAME.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T64> $o: ref, $f: Field T64 :: { modify.GAME.in_observers(heap, current, new_observers, o)[$o, $f] } (modify.GAME.in_observers(heap, current, new_observers, o)[$o, $f]) <==> (false)))));

function read.fun.GAME.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T65> $o: ref, $f: Field T65 :: { read.fun.GAME.in_observers(heap, current, new_observers, o)[$o, $f] } (read.fun.GAME.in_observers(heap, current, new_observers, o)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.GAME.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool) {
  true
}

function trigger.fun.GAME.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

const unique V_SPECIAL^PLAYER^: Type;

axiom ((V_SPECIAL^PLAYER^) <: (ANY));

axiom ((forall t: Type :: { (V_SPECIAL^PLAYER^) <: (t) } ((V_SPECIAL^PLAYER^) <: (t)) <==> (((t) == (V_SPECIAL^PLAYER^)) || ((ANY) <: (t)))));

axiom ((FieldId(allocated, V_SPECIAL^PLAYER^)) == (-1));

axiom ((FieldId(closed, V_SPECIAL^PLAYER^)) == (-2));

axiom ((FieldId(owner, V_SPECIAL^PLAYER^)) == (-3));

axiom ((FieldId(owns, V_SPECIAL^PLAYER^)) == (-4));

axiom ((FieldId(observers, V_SPECIAL^PLAYER^)) == (-5));

axiom ((FieldId(subjects, V_SPECIAL^PLAYER^)) == (-6));

axiom ((forall <T66> $f: Field T66 :: { IsModelField($f, V_SPECIAL^PLAYER^) } (IsModelField($f, V_SPECIAL^PLAYER^)) <==> ((($f) == (V_SPECIAL^PLAYER^.sequence)) || (($f) == (V_SPECIAL^PLAYER^.capacity)) || (($f) == (subjects)) || (($f) == (observers)))));

function { :inline } V_SPECIAL^PLAYER^.user_inv(heap: HeapType, current: ref) returns (bool) {
  ((Seq#Length(heap[current, V_SPECIAL^PLAYER^.sequence])) <= (heap[current, V_SPECIAL^PLAYER^.capacity])) && (Set#IsEmpty(heap[current, observers])) && (Set#IsEmpty(heap[current, subjects])) && (Set#IsEmpty(heap[current, owns])) && (admissibility2(heap, current))
}

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached_exact(heap, current, V_SPECIAL^PLAYER^)) ==> ((user_inv(heap, current)) <==> (V_SPECIAL^PLAYER^.user_inv(heap, current)))));

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached(heap, current, V_SPECIAL^PLAYER^)) ==> ((user_inv(heap, current)) ==> (V_SPECIAL^PLAYER^.user_inv(heap, current)))));

procedure V_ARRAY^PLAYER^.in_observers(Current: ref, new_observers: Set (ref), o: ref) returns (Result: bool where true);
  free requires attached_exact(Heap, Current, V_ARRAY^PLAYER^); // info:type property for argument Current
  free requires Set#ItemsType(Heap, new_observers, ANY); // info:type property for argument new_observers
  free requires Heap[o, allocated]; // info:type property for argument o
  modifies Heap;
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.V_ARRAY^PLAYER^.in_observers(Heap, Current, new_observers, o), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.V_ARRAY^PLAYER^.in_observers(old(Heap), Current, new_observers, o));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.V_ARRAY^PLAYER^.in_observers(Heap, Current, new_observers, o), readable);



function fun.V_ARRAY^PLAYER^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function fun0.V_ARRAY^PLAYER^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.V_ARRAY^PLAYER^.in_observers(heap, current, new_observers, o) } { trigger.fun.V_ARRAY^PLAYER^.in_observers(heap, current, new_observers, o) } (pre.fun.V_ARRAY^PLAYER^.in_observers(heap, current, new_observers, o)) ==> ((fun.V_ARRAY^PLAYER^.in_observers(heap, current, new_observers, o)) == (new_observers[o]))));

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.V_ARRAY^PLAYER^.in_observers(heap, current, new_observers, o) } (fun.V_ARRAY^PLAYER^.in_observers(heap, current, new_observers, o)) == (fun0.V_ARRAY^PLAYER^.in_observers(heap, current, new_observers, o))));

axiom ((forall h: HeapType, h': HeapType, current: ref, new_observers: Set (ref), o: ref :: { HeapSucc(h, h'), fun0.V_ARRAY^PLAYER^.in_observers(h, current, new_observers, o), fun0.V_ARRAY^PLAYER^.in_observers(h', current, new_observers, o) } ((HeapSucc(h, h')) && (pre.fun.V_ARRAY^PLAYER^.in_observers(h, current, new_observers, o)) && (pre.fun.V_ARRAY^PLAYER^.in_observers(h', current, new_observers, o)) && (same_inside(h, h', read.fun.V_ARRAY^PLAYER^.in_observers(h, current, new_observers, o)))) ==> ((fun0.V_ARRAY^PLAYER^.in_observers(h, current, new_observers, o)) == (fun0.V_ARRAY^PLAYER^.in_observers(h', current, new_observers, o)))));

procedure V_ARRAY^PLAYER^.upper_(Current: ref) returns (Result: int where is_integer_32(Result));
  free requires attached_exact(Heap, Current, V_ARRAY^PLAYER^); // info:type property for argument Current
  modifies Heap;
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.V_ARRAY^PLAYER^.upper_(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.V_ARRAY^PLAYER^.upper_(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.V_ARRAY^PLAYER^.upper_(Heap, Current), readable);



function fun.V_ARRAY^PLAYER^.upper_(heap: HeapType, current: ref) returns (int);

function fun0.V_ARRAY^PLAYER^.upper_(heap: HeapType, current: ref) returns (int);

axiom ((forall heap: HeapType, current: ref :: { fun.V_ARRAY^PLAYER^.upper_(heap, current) } (pre.fun.V_ARRAY^PLAYER^.upper_(heap, current)) ==> (is_integer_32(fun.V_ARRAY^PLAYER^.upper_(heap, current)))));

axiom ((forall heap: HeapType, current: ref :: { fun.V_ARRAY^PLAYER^.upper_(heap, current) } { trigger.fun.V_ARRAY^PLAYER^.upper_(heap, current) } (pre.fun.V_ARRAY^PLAYER^.upper_(heap, current)) ==> ((fun.V_ARRAY^PLAYER^.upper_(heap, current)) == (((heap[current, V_ARRAY^PLAYER^.lower_]) + (Seq#Length(heap[current, V_ARRAY^PLAYER^.sequence]))) - (1)))));

axiom ((forall heap: HeapType, current: ref :: { fun.V_ARRAY^PLAYER^.upper_(heap, current) } (fun.V_ARRAY^PLAYER^.upper_(heap, current)) == (fun0.V_ARRAY^PLAYER^.upper_(heap, current))));

axiom ((forall h: HeapType, h': HeapType, current: ref :: { HeapSucc(h, h'), fun0.V_ARRAY^PLAYER^.upper_(h, current), fun0.V_ARRAY^PLAYER^.upper_(h', current) } ((HeapSucc(h, h')) && (pre.fun.V_ARRAY^PLAYER^.upper_(h, current)) && (pre.fun.V_ARRAY^PLAYER^.upper_(h', current)) && (same_inside(h, h', read.fun.V_ARRAY^PLAYER^.upper_(h, current)))) ==> ((fun0.V_ARRAY^PLAYER^.upper_(h, current)) == (fun0.V_ARRAY^PLAYER^.upper_(h', current)))));

function modify.V_ARRAY^PLAYER^.has_index(heap: HeapType, current: ref, i: int) returns (Frame);

axiom ((forall heap: HeapType, current: ref, i: int :: (IsHeap(heap)) ==> ((forall <T67> $o: ref, $f: Field T67 :: { modify.V_ARRAY^PLAYER^.has_index(heap, current, i)[$o, $f] } (modify.V_ARRAY^PLAYER^.has_index(heap, current, i)[$o, $f]) <==> (false)))));

function read.fun.V_ARRAY^PLAYER^.has_index(heap: HeapType, current: ref, i: int) returns (Frame);

axiom ((forall heap: HeapType, current: ref, i: int :: (IsHeap(heap)) ==> ((forall <T68> $o: ref, $f: Field T68 :: { read.fun.V_ARRAY^PLAYER^.has_index(heap, current, i)[$o, $f] } (read.fun.V_ARRAY^PLAYER^.has_index(heap, current, i)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.V_ARRAY^PLAYER^.has_index(heap: HeapType, current: ref, i: int) returns (bool) {
  is_closed(heap, current)
}

function trigger.fun.V_ARRAY^PLAYER^.has_index(heap: HeapType, current: ref, i: int) returns (bool);

function pre.fun.MML_SEQUENCE^PLAYER^.replaced_at(current: Seq (ref), i: int, x: ref) returns (bool) {
  Seq#Domain(current)[i]
}

function trigger.fun.MML_SEQUENCE^PLAYER^.replaced_at(current: Seq (ref), i: int, x: ref) returns (bool);

function modify.V_ARRAY^PLAYER^.idx(heap: HeapType, current: ref, i: int) returns (Frame);

axiom ((forall heap: HeapType, current: ref, i: int :: (IsHeap(heap)) ==> ((forall <T69> $o: ref, $f: Field T69 :: { modify.V_ARRAY^PLAYER^.idx(heap, current, i)[$o, $f] } (modify.V_ARRAY^PLAYER^.idx(heap, current, i)[$o, $f]) <==> (false)))));

function read.fun.V_ARRAY^PLAYER^.idx(heap: HeapType, current: ref, i: int) returns (Frame);

axiom ((forall heap: HeapType, current: ref, i: int :: (IsHeap(heap)) ==> ((forall <T70> $o: ref, $f: Field T70 :: { read.fun.V_ARRAY^PLAYER^.idx(heap, current, i)[$o, $f] } (read.fun.V_ARRAY^PLAYER^.idx(heap, current, i)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.V_ARRAY^PLAYER^.idx(heap: HeapType, current: ref, i: int) returns (bool) {
  true
}

function trigger.fun.V_ARRAY^PLAYER^.idx(heap: HeapType, current: ref, i: int) returns (bool);

const unique READABLE_STRING_8: Type;

axiom ((READABLE_STRING_8) <: (READABLE_STRING_GENERAL));

axiom ((READABLE_STRING_8) <: (READABLE_INDEXABLE^CHARACTER_8^));

axiom ((forall t: Type :: { (READABLE_STRING_8) <: (t) } ((READABLE_STRING_8) <: (t)) <==> (((t) == (READABLE_STRING_8)) || ((READABLE_STRING_GENERAL) <: (t)) || ((READABLE_INDEXABLE^CHARACTER_8^) <: (t)))));

axiom ((FieldId(allocated, READABLE_STRING_8)) == (-1));

axiom ((FieldId(closed, READABLE_STRING_8)) == (-2));

axiom ((FieldId(owner, READABLE_STRING_8)) == (-3));

axiom ((FieldId(owns, READABLE_STRING_8)) == (-4));

axiom ((FieldId(observers, READABLE_STRING_8)) == (-5));

axiom ((FieldId(subjects, READABLE_STRING_8)) == (-6));

const unique STRING_GENERAL: Type;

axiom ((STRING_GENERAL) <: (READABLE_STRING_GENERAL));

axiom ((forall t: Type :: { (STRING_GENERAL) <: (t) } ((STRING_GENERAL) <: (t)) <==> (((t) == (STRING_GENERAL)) || ((READABLE_STRING_GENERAL) <: (t)))));

axiom ((FieldId(allocated, STRING_GENERAL)) == (-1));

axiom ((FieldId(closed, STRING_GENERAL)) == (-2));

axiom ((FieldId(owner, STRING_GENERAL)) == (-3));

axiom ((FieldId(owns, STRING_GENERAL)) == (-4));

axiom ((FieldId(observers, STRING_GENERAL)) == (-5));

axiom ((FieldId(subjects, STRING_GENERAL)) == (-6));

const unique INDEXABLE^CHARACTER_8#INTEGER_32^: Type;

axiom ((INDEXABLE^CHARACTER_8#INTEGER_32^) <: (TABLE^CHARACTER_8#INTEGER_32^));

axiom ((INDEXABLE^CHARACTER_8#INTEGER_32^) <: (READABLE_INDEXABLE^CHARACTER_8^));

axiom ((forall t: Type :: { (INDEXABLE^CHARACTER_8#INTEGER_32^) <: (t) } ((INDEXABLE^CHARACTER_8#INTEGER_32^) <: (t)) <==> (((t) == (INDEXABLE^CHARACTER_8#INTEGER_32^)) || ((TABLE^CHARACTER_8#INTEGER_32^) <: (t)) || ((READABLE_INDEXABLE^CHARACTER_8^) <: (t)))));

axiom ((FieldId(allocated, INDEXABLE^CHARACTER_8#INTEGER_32^)) == (-1));

axiom ((FieldId(closed, INDEXABLE^CHARACTER_8#INTEGER_32^)) == (-2));

axiom ((FieldId(owner, INDEXABLE^CHARACTER_8#INTEGER_32^)) == (-3));

axiom ((FieldId(owns, INDEXABLE^CHARACTER_8#INTEGER_32^)) == (-4));

axiom ((FieldId(observers, INDEXABLE^CHARACTER_8#INTEGER_32^)) == (-5));

axiom ((FieldId(subjects, INDEXABLE^CHARACTER_8#INTEGER_32^)) == (-6));

const unique RESIZABLE^CHARACTER_8^: Type;

axiom ((RESIZABLE^CHARACTER_8^) <: (BOUNDED^CHARACTER_8^));

axiom ((forall t: Type :: { (RESIZABLE^CHARACTER_8^) <: (t) } ((RESIZABLE^CHARACTER_8^) <: (t)) <==> (((t) == (RESIZABLE^CHARACTER_8^)) || ((BOUNDED^CHARACTER_8^) <: (t)))));

axiom ((FieldId(allocated, RESIZABLE^CHARACTER_8^)) == (-1));

axiom ((FieldId(closed, RESIZABLE^CHARACTER_8^)) == (-2));

axiom ((FieldId(owner, RESIZABLE^CHARACTER_8^)) == (-3));

axiom ((FieldId(owns, RESIZABLE^CHARACTER_8^)) == (-4));

axiom ((FieldId(observers, RESIZABLE^CHARACTER_8^)) == (-5));

axiom ((FieldId(subjects, RESIZABLE^CHARACTER_8^)) == (-6));

const unique TO_SPECIAL^CHARACTER_8^: Type;

axiom ((TO_SPECIAL^CHARACTER_8^) <: (ANY));

axiom ((forall t: Type :: { (TO_SPECIAL^CHARACTER_8^) <: (t) } ((TO_SPECIAL^CHARACTER_8^) <: (t)) <==> (((t) == (TO_SPECIAL^CHARACTER_8^)) || ((ANY) <: (t)))));

axiom ((FieldId(allocated, TO_SPECIAL^CHARACTER_8^)) == (-1));

axiom ((FieldId(closed, TO_SPECIAL^CHARACTER_8^)) == (-2));

axiom ((FieldId(owner, TO_SPECIAL^CHARACTER_8^)) == (-3));

axiom ((FieldId(owns, TO_SPECIAL^CHARACTER_8^)) == (-4));

axiom ((FieldId(observers, TO_SPECIAL^CHARACTER_8^)) == (-5));

axiom ((FieldId(subjects, TO_SPECIAL^CHARACTER_8^)) == (-6));

const unique MISMATCH_CORRECTOR: Type;

axiom ((MISMATCH_CORRECTOR) <: (ANY));

axiom ((forall t: Type :: { (MISMATCH_CORRECTOR) <: (t) } ((MISMATCH_CORRECTOR) <: (t)) <==> (((t) == (MISMATCH_CORRECTOR)) || ((ANY) <: (t)))));

axiom ((FieldId(allocated, MISMATCH_CORRECTOR)) == (-1));

axiom ((FieldId(closed, MISMATCH_CORRECTOR)) == (-2));

axiom ((FieldId(owner, MISMATCH_CORRECTOR)) == (-3));

axiom ((FieldId(owns, MISMATCH_CORRECTOR)) == (-4));

axiom ((FieldId(observers, MISMATCH_CORRECTOR)) == (-5));

axiom ((FieldId(subjects, MISMATCH_CORRECTOR)) == (-6));

procedure STRING_8.is_less(Current: ref, other: ref) returns (Result: bool where true);
  free requires attached_exact(Heap, Current, STRING_8); // info:type property for argument Current
  free requires detachable(Heap, other, STRING_8); // info:type property for argument other
  modifies Heap;
  requires (other) != (Void); // type:pre tag:other_exists line:17
  ensures (Result) ==> ((other) != (Void)); // type:attached tag:asymmetric line:29
  ensures (Result) ==> (pre.fun.STRING_8.is_less(Heap, other, Current)); // type:check tag:function_precondition line:29 cid:13 rid:1453
  ensures (Result) ==> (!(fun.STRING_8.is_less(Heap, other, Current))); // type:post tag:asymmetric line:29
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.STRING_8.is_less(Heap, Current, other), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.STRING_8.is_less(old(Heap), Current, other));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.STRING_8.is_less(Heap, Current, other), readable);
  requires is_closed(Heap, Current); // type:pre tag:default_is_closed default:contracts
  requires is_closed(Heap, other); // type:pre tag:arg_other_is_closed default:contracts
  free ensures (Result) == (fun.STRING_8.is_less(old(Heap), Current, other));



function fun.STRING_8.is_less(heap: HeapType, current: ref, other: ref) returns (bool);

axiom ((forall heap: HeapType, current: ref, other: ref :: { fun.STRING_8.is_less(heap, current, other) } (pre.fun.STRING_8.is_less(heap, current, other)) ==> ((fun.STRING_8.is_less(heap, current, other)) ==> (!(fun.STRING_8.is_less(heap, other, current))))));

axiom ((forall h: HeapType, h': HeapType, current: ref, other: ref :: { HeapSucc(h, h'), fun.STRING_8.is_less(h, current, other), fun.STRING_8.is_less(h', current, other) } ((HeapSucc(h, h')) && (pre.fun.STRING_8.is_less(h, current, other)) && (pre.fun.STRING_8.is_less(h', current, other)) && (same_inside(h, h', read.fun.STRING_8.is_less(h, current, other)))) ==> ((fun.STRING_8.is_less(h, current, other)) == (fun.STRING_8.is_less(h', current, other)))));

const STRING_8.area: Field (ref);

axiom ((FieldId(STRING_8.area, STRING_8)) == (236));

const READABLE_STRING_8.area: Field (ref);

axiom ((STRING_8.area) == (READABLE_STRING_8.area));

const TO_SPECIAL^CHARACTER_8^.area: Field (ref);

axiom ((STRING_8.area) == (TO_SPECIAL^CHARACTER_8^.area));

axiom ((forall heap: HeapType, o: ref :: { heap[o, STRING_8.area] } ((IsHeap(heap)) && (attached(heap, o, STRING_8))) ==> (detachable_exact(heap, heap[o, STRING_8.area], SPECIAL^CHARACTER_8^))));

axiom ((forall heap: HeapType, current: ref, v: ref, o: ref :: { guard(heap, current, STRING_8.area, v, o) } (attached_exact(heap, current, STRING_8)) ==> ((guard(heap, current, STRING_8.area, v, o)) <==> (((user_inv(heap, o)) ==> (user_inv(heap[current, STRING_8.area := v], o))) && ((user_inv(heap, o)) ==> (user_inv(heap[current, STRING_8.area := v], o)))))));

axiom ((forall heap: HeapType, current: ref, v: ref, o: ref :: { guard(heap, current, STRING_8.area, v, o) } (attached(heap, current, STRING_8)) ==> ((guard(heap, current, STRING_8.area, v, o)) ==> (((user_inv(heap, o)) ==> (user_inv(heap[current, STRING_8.area := v], o))) && ((user_inv(heap, o)) ==> (user_inv(heap[current, STRING_8.area := v], o)))))));

procedure STRING_8.is_immutable(Current: ref) returns (Result: bool where true);
  free requires attached_exact(Heap, Current, STRING_8); // info:type property for argument Current
  modifies Heap;
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.STRING_8.is_immutable(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.STRING_8.is_immutable(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.STRING_8.is_immutable(Heap, Current), readable);
  requires is_closed(Heap, Current); // type:pre tag:default_is_closed default:contracts
  free ensures (Result) == (fun.STRING_8.is_immutable(old(Heap), Current));



function fun.STRING_8.is_immutable(heap: HeapType, current: ref) returns (bool);

axiom ((forall h: HeapType, h': HeapType, current: ref :: { HeapSucc(h, h'), fun.STRING_8.is_immutable(h, current), fun.STRING_8.is_immutable(h', current) } ((HeapSucc(h, h')) && (pre.fun.STRING_8.is_immutable(h, current)) && (pre.fun.STRING_8.is_immutable(h', current)) && (same_inside(h, h', read.fun.STRING_8.is_immutable(h, current)))) ==> ((fun.STRING_8.is_immutable(h, current)) == (fun.STRING_8.is_immutable(h', current)))));

procedure STRING_8.is_empty(Current: ref) returns (Result: bool where true);
  free requires attached_exact(Heap, Current, STRING_8); // info:type property for argument Current
  modifies Heap;
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.STRING_8.is_empty(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.STRING_8.is_empty(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.STRING_8.is_empty(Heap, Current), readable);
  requires is_closed(Heap, Current); // type:pre tag:default_is_closed default:contracts
  free ensures (Result) == (fun.STRING_8.is_empty(old(Heap), Current));



function fun.STRING_8.is_empty(heap: HeapType, current: ref) returns (bool);

axiom ((forall h: HeapType, h': HeapType, current: ref :: { HeapSucc(h, h'), fun.STRING_8.is_empty(h, current), fun.STRING_8.is_empty(h', current) } ((HeapSucc(h, h')) && (pre.fun.STRING_8.is_empty(h, current)) && (pre.fun.STRING_8.is_empty(h', current)) && (same_inside(h, h', read.fun.STRING_8.is_empty(h, current)))) ==> ((fun.STRING_8.is_empty(h, current)) == (fun.STRING_8.is_empty(h', current)))));

const STRING_8.count: Field int;

axiom ((FieldId(STRING_8.count, STRING_8)) == (179));

const READABLE_STRING_8.count: Field int;

axiom ((STRING_8.count) == (READABLE_STRING_8.count));

axiom ((forall heap: HeapType, o: ref :: { heap[o, STRING_8.count] } ((IsHeap(heap)) && (attached(heap, o, STRING_8))) ==> (is_integer_32(heap[o, STRING_8.count]))));

axiom ((forall heap: HeapType, current: ref, v: int, o: ref :: { guard(heap, current, STRING_8.count, v, o) } (attached_exact(heap, current, STRING_8)) ==> ((guard(heap, current, STRING_8.count, v, o)) <==> (((user_inv(heap, o)) ==> (user_inv(heap[current, STRING_8.count := v], o))) && ((user_inv(heap, o)) ==> (user_inv(heap[current, STRING_8.count := v], o)))))));

axiom ((forall heap: HeapType, current: ref, v: int, o: ref :: { guard(heap, current, STRING_8.count, v, o) } (attached(heap, current, STRING_8)) ==> ((guard(heap, current, STRING_8.count, v, o)) ==> (((user_inv(heap, o)) ==> (user_inv(heap[current, STRING_8.count := v], o))) && ((user_inv(heap, o)) ==> (user_inv(heap[current, STRING_8.count := v], o)))))));

procedure STRING_8.capacity(Current: ref) returns (Result: int where is_integer_32(Result));
  free requires attached_exact(Heap, Current, STRING_8); // info:type property for argument Current
  modifies Heap;
  ensures (Result) >= (0); // type:post tag:capacity_non_negative line:509
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.STRING_8.capacity(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.STRING_8.capacity(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.STRING_8.capacity(Heap, Current), readable);
  requires is_closed(Heap, Current); // type:pre tag:default_is_closed default:contracts
  free ensures (Result) == (fun.STRING_8.capacity(old(Heap), Current));



function fun.STRING_8.capacity(heap: HeapType, current: ref) returns (int);

axiom ((forall heap: HeapType, current: ref :: { fun.STRING_8.capacity(heap, current) } (pre.fun.STRING_8.capacity(heap, current)) ==> (((fun.STRING_8.capacity(heap, current)) >= (0)) && ((fun.STRING_8.capacity(heap, current)) >= (0)) && (is_integer_32(fun.STRING_8.capacity(heap, current))))));

axiom ((forall h: HeapType, h': HeapType, current: ref :: { HeapSucc(h, h'), fun.STRING_8.capacity(h, current), fun.STRING_8.capacity(h', current) } ((HeapSucc(h, h')) && (pre.fun.STRING_8.capacity(h, current)) && (pre.fun.STRING_8.capacity(h', current)) && (same_inside(h, h', read.fun.STRING_8.capacity(h, current)))) ==> ((fun.STRING_8.capacity(h, current)) == (fun.STRING_8.capacity(h', current)))));

procedure STRING_8.full(Current: ref) returns (Result: bool where true);
  free requires attached_exact(Heap, Current, STRING_8); // info:type property for argument Current
  modifies Heap;
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.STRING_8.full(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.STRING_8.full(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.STRING_8.full(Heap, Current), readable);
  requires is_closed(Heap, Current); // type:pre tag:default_is_closed default:contracts
  free ensures (Result) == (fun.STRING_8.full(old(Heap), Current));



function fun.STRING_8.full(heap: HeapType, current: ref) returns (bool);

axiom ((forall h: HeapType, h': HeapType, current: ref :: { HeapSucc(h, h'), fun.STRING_8.full(h, current), fun.STRING_8.full(h', current) } ((HeapSucc(h, h')) && (pre.fun.STRING_8.full(h, current)) && (pre.fun.STRING_8.full(h', current)) && (same_inside(h, h', read.fun.STRING_8.full(h, current)))) ==> ((fun.STRING_8.full(h, current)) == (fun.STRING_8.full(h', current)))));

const STRING_8.object_comparison: Field bool;

axiom ((FieldId(STRING_8.object_comparison, STRING_8)) == (81));

const INDEXABLE^CHARACTER_8#INTEGER_32^.object_comparison: Field bool;

axiom ((STRING_8.object_comparison) == (INDEXABLE^CHARACTER_8#INTEGER_32^.object_comparison));

const TABLE^CHARACTER_8#INTEGER_32^.object_comparison: Field bool;

axiom ((STRING_8.object_comparison) == (TABLE^CHARACTER_8#INTEGER_32^.object_comparison));

const BAG^CHARACTER_8^.object_comparison: Field bool;

axiom ((STRING_8.object_comparison) == (BAG^CHARACTER_8^.object_comparison));

const COLLECTION^CHARACTER_8^.object_comparison: Field bool;

axiom ((STRING_8.object_comparison) == (COLLECTION^CHARACTER_8^.object_comparison));

const CONTAINER^CHARACTER_8^.object_comparison: Field bool;

axiom ((STRING_8.object_comparison) == (CONTAINER^CHARACTER_8^.object_comparison));

const RESIZABLE^CHARACTER_8^.object_comparison: Field bool;

axiom ((STRING_8.object_comparison) == (RESIZABLE^CHARACTER_8^.object_comparison));

const BOUNDED^CHARACTER_8^.object_comparison: Field bool;

axiom ((STRING_8.object_comparison) == (BOUNDED^CHARACTER_8^.object_comparison));

const FINITE^CHARACTER_8^.object_comparison: Field bool;

axiom ((STRING_8.object_comparison) == (FINITE^CHARACTER_8^.object_comparison));

const BOX^CHARACTER_8^.object_comparison: Field bool;

axiom ((STRING_8.object_comparison) == (BOX^CHARACTER_8^.object_comparison));

axiom ((STRING_8.object_comparison) == (CONTAINER^CHARACTER_8^.object_comparison));

axiom ((forall heap: HeapType, current: ref, v: bool, o: ref :: { guard(heap, current, STRING_8.object_comparison, v, o) } (attached_exact(heap, current, STRING_8)) ==> ((guard(heap, current, STRING_8.object_comparison, v, o)) <==> ((user_inv(heap, o)) ==> (user_inv(heap[current, STRING_8.object_comparison := v], o))))));

axiom ((forall heap: HeapType, current: ref, v: bool, o: ref :: { guard(heap, current, STRING_8.object_comparison, v, o) } (attached(heap, current, STRING_8)) ==> ((guard(heap, current, STRING_8.object_comparison, v, o)) ==> ((user_inv(heap, o)) ==> (user_inv(heap[current, STRING_8.object_comparison := v], o))))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, owns, v, o) } (attached_exact(heap, current, STRING_8)) ==> ((guard(heap, current, owns, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, subjects, v, o) } (attached_exact(heap, current, STRING_8)) ==> ((guard(heap, current, subjects, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached_exact(heap, current, STRING_8)) ==> ((guard(heap, current, observers, v, o)) <==> (fun.STRING_8.in_observers(heap, current, v, o)))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached(heap, current, STRING_8)) ==> ((guard(heap, current, observers, v, o)) ==> (fun.STRING_8.in_observers(heap, current, v, o)))));

function modify.V_STRING.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T71> $o: ref, $f: Field T71 :: { modify.V_STRING.in_observers(heap, current, new_observers, o)[$o, $f] } (modify.V_STRING.in_observers(heap, current, new_observers, o)[$o, $f]) <==> (false)))));

function read.fun.V_STRING.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T72> $o: ref, $f: Field T72 :: { read.fun.V_STRING.in_observers(heap, current, new_observers, o)[$o, $f] } (read.fun.V_STRING.in_observers(heap, current, new_observers, o)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.V_STRING.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool) {
  true
}

function trigger.fun.V_STRING.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

procedure STD_FILES.in_observers(Current: ref, new_observers: Set (ref), o: ref) returns (Result: bool where true);
  free requires attached_exact(Heap, Current, STD_FILES); // info:type property for argument Current
  free requires Set#ItemsType(Heap, new_observers, ANY); // info:type property for argument new_observers
  free requires Heap[o, allocated]; // info:type property for argument o
  modifies Heap;
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.STD_FILES.in_observers(Heap, Current, new_observers, o), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.STD_FILES.in_observers(old(Heap), Current, new_observers, o));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.STD_FILES.in_observers(Heap, Current, new_observers, o), readable);



function fun.STD_FILES.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function fun0.STD_FILES.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.STD_FILES.in_observers(heap, current, new_observers, o) } { trigger.fun.STD_FILES.in_observers(heap, current, new_observers, o) } (pre.fun.STD_FILES.in_observers(heap, current, new_observers, o)) ==> ((fun.STD_FILES.in_observers(heap, current, new_observers, o)) == (new_observers[o]))));

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.STD_FILES.in_observers(heap, current, new_observers, o) } (fun.STD_FILES.in_observers(heap, current, new_observers, o)) == (fun0.STD_FILES.in_observers(heap, current, new_observers, o))));

axiom ((forall h: HeapType, h': HeapType, current: ref, new_observers: Set (ref), o: ref :: { HeapSucc(h, h'), fun0.STD_FILES.in_observers(h, current, new_observers, o), fun0.STD_FILES.in_observers(h', current, new_observers, o) } ((HeapSucc(h, h')) && (pre.fun.STD_FILES.in_observers(h, current, new_observers, o)) && (pre.fun.STD_FILES.in_observers(h', current, new_observers, o)) && (same_inside(h, h', read.fun.STD_FILES.in_observers(h, current, new_observers, o)))) ==> ((fun0.STD_FILES.in_observers(h, current, new_observers, o)) == (fun0.STD_FILES.in_observers(h', current, new_observers, o)))));

function modify.V_RANDOM.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T73> $o: ref, $f: Field T73 :: { modify.V_RANDOM.in_observers(heap, current, new_observers, o)[$o, $f] } (modify.V_RANDOM.in_observers(heap, current, new_observers, o)[$o, $f]) <==> (false)))));

function read.fun.V_RANDOM.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T74> $o: ref, $f: Field T74 :: { read.fun.V_RANDOM.in_observers(heap, current, new_observers, o)[$o, $f] } (read.fun.V_RANDOM.in_observers(heap, current, new_observers, o)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.V_RANDOM.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool) {
  true
}

function trigger.fun.V_RANDOM.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

const unique ITERABLE^PLAYER^: Type;

axiom ((ITERABLE^PLAYER^) <: (ANY));

axiom ((forall t: Type :: { (ITERABLE^PLAYER^) <: (t) } ((ITERABLE^PLAYER^) <: (t)) <==> (((t) == (ITERABLE^PLAYER^)) || ((ANY) <: (t)))));

axiom ((FieldId(allocated, ITERABLE^PLAYER^)) == (-1));

axiom ((FieldId(closed, ITERABLE^PLAYER^)) == (-2));

axiom ((FieldId(owner, ITERABLE^PLAYER^)) == (-3));

axiom ((FieldId(owns, ITERABLE^PLAYER^)) == (-4));

axiom ((FieldId(observers, ITERABLE^PLAYER^)) == (-5));

axiom ((FieldId(subjects, ITERABLE^PLAYER^)) == (-6));

const V_SPECIAL^PLAYER^.capacity: Field int;

axiom ((FieldId(V_SPECIAL^PLAYER^.capacity, V_SPECIAL^PLAYER^)) == (84));

axiom ((forall heap: HeapType, o: ref :: { heap[o, V_SPECIAL^PLAYER^.capacity] } ((IsHeap(heap)) && (attached(heap, o, V_SPECIAL^PLAYER^))) ==> (is_integer_32(heap[o, V_SPECIAL^PLAYER^.capacity]))));

axiom ((forall heap: HeapType, current: ref, v: int, o: ref :: { guard(heap, current, V_SPECIAL^PLAYER^.capacity, v, o) } (attached_exact(heap, current, V_SPECIAL^PLAYER^)) ==> ((guard(heap, current, V_SPECIAL^PLAYER^.capacity, v, o)) <==> (false))));

axiom ((forall heap: HeapType, current: ref, v: int, o: ref :: { guard(heap, current, V_SPECIAL^PLAYER^.capacity, v, o) } (attached(heap, current, V_SPECIAL^PLAYER^)) ==> ((guard(heap, current, V_SPECIAL^PLAYER^.capacity, v, o)) ==> (false))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, owns, v, o) } (attached_exact(heap, current, V_SPECIAL^PLAYER^)) ==> ((guard(heap, current, owns, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, subjects, v, o) } (attached_exact(heap, current, V_SPECIAL^PLAYER^)) ==> ((guard(heap, current, subjects, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached_exact(heap, current, V_SPECIAL^PLAYER^)) ==> ((guard(heap, current, observers, v, o)) <==> (fun.V_SPECIAL^PLAYER^.in_observers(heap, current, v, o)))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached(heap, current, V_SPECIAL^PLAYER^)) ==> ((guard(heap, current, observers, v, o)) ==> (fun.V_SPECIAL^PLAYER^.in_observers(heap, current, v, o)))));

function modify.V_ARRAY^PLAYER^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T75> $o: ref, $f: Field T75 :: { modify.V_ARRAY^PLAYER^.in_observers(heap, current, new_observers, o)[$o, $f] } (modify.V_ARRAY^PLAYER^.in_observers(heap, current, new_observers, o)[$o, $f]) <==> (false)))));

function read.fun.V_ARRAY^PLAYER^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T76> $o: ref, $f: Field T76 :: { read.fun.V_ARRAY^PLAYER^.in_observers(heap, current, new_observers, o)[$o, $f] } (read.fun.V_ARRAY^PLAYER^.in_observers(heap, current, new_observers, o)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.V_ARRAY^PLAYER^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool) {
  true
}

function trigger.fun.V_ARRAY^PLAYER^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function modify.V_ARRAY^PLAYER^.upper_(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T77> $o: ref, $f: Field T77 :: { modify.V_ARRAY^PLAYER^.upper_(heap, current)[$o, $f] } (modify.V_ARRAY^PLAYER^.upper_(heap, current)[$o, $f]) <==> (false)))));

function read.fun.V_ARRAY^PLAYER^.upper_(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T78> $o: ref, $f: Field T78 :: { read.fun.V_ARRAY^PLAYER^.upper_(heap, current)[$o, $f] } (read.fun.V_ARRAY^PLAYER^.upper_(heap, current)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.V_ARRAY^PLAYER^.upper_(heap: HeapType, current: ref) returns (bool) {
  true
}

function trigger.fun.V_ARRAY^PLAYER^.upper_(heap: HeapType, current: ref) returns (bool);

const unique READABLE_STRING_GENERAL: Type;

axiom ((READABLE_STRING_GENERAL) <: (COMPARABLE));

axiom ((READABLE_STRING_GENERAL) <: (HASHABLE));

axiom ((READABLE_STRING_GENERAL) <: (STRING_HANDLER));

axiom ((forall t: Type :: { (READABLE_STRING_GENERAL) <: (t) } ((READABLE_STRING_GENERAL) <: (t)) <==> (((t) == (READABLE_STRING_GENERAL)) || ((COMPARABLE) <: (t)) || ((HASHABLE) <: (t)) || ((STRING_HANDLER) <: (t)))));

axiom ((FieldId(allocated, READABLE_STRING_GENERAL)) == (-1));

axiom ((FieldId(closed, READABLE_STRING_GENERAL)) == (-2));

axiom ((FieldId(owner, READABLE_STRING_GENERAL)) == (-3));

axiom ((FieldId(owns, READABLE_STRING_GENERAL)) == (-4));

axiom ((FieldId(observers, READABLE_STRING_GENERAL)) == (-5));

axiom ((FieldId(subjects, READABLE_STRING_GENERAL)) == (-6));

const unique READABLE_INDEXABLE^CHARACTER_8^: Type;

axiom ((READABLE_INDEXABLE^CHARACTER_8^) <: (ITERABLE^CHARACTER_8^));

axiom ((forall t: Type :: { (READABLE_INDEXABLE^CHARACTER_8^) <: (t) } ((READABLE_INDEXABLE^CHARACTER_8^) <: (t)) <==> (((t) == (READABLE_INDEXABLE^CHARACTER_8^)) || ((ITERABLE^CHARACTER_8^) <: (t)))));

axiom ((FieldId(allocated, READABLE_INDEXABLE^CHARACTER_8^)) == (-1));

axiom ((FieldId(closed, READABLE_INDEXABLE^CHARACTER_8^)) == (-2));

axiom ((FieldId(owner, READABLE_INDEXABLE^CHARACTER_8^)) == (-3));

axiom ((FieldId(owns, READABLE_INDEXABLE^CHARACTER_8^)) == (-4));

axiom ((FieldId(observers, READABLE_INDEXABLE^CHARACTER_8^)) == (-5));

axiom ((FieldId(subjects, READABLE_INDEXABLE^CHARACTER_8^)) == (-6));

const unique TABLE^CHARACTER_8#INTEGER_32^: Type;

axiom ((TABLE^CHARACTER_8#INTEGER_32^) <: (BAG^CHARACTER_8^));

axiom ((forall t: Type :: { (TABLE^CHARACTER_8#INTEGER_32^) <: (t) } ((TABLE^CHARACTER_8#INTEGER_32^) <: (t)) <==> (((t) == (TABLE^CHARACTER_8#INTEGER_32^)) || ((BAG^CHARACTER_8^) <: (t)))));

axiom ((FieldId(allocated, TABLE^CHARACTER_8#INTEGER_32^)) == (-1));

axiom ((FieldId(closed, TABLE^CHARACTER_8#INTEGER_32^)) == (-2));

axiom ((FieldId(owner, TABLE^CHARACTER_8#INTEGER_32^)) == (-3));

axiom ((FieldId(owns, TABLE^CHARACTER_8#INTEGER_32^)) == (-4));

axiom ((FieldId(observers, TABLE^CHARACTER_8#INTEGER_32^)) == (-5));

axiom ((FieldId(subjects, TABLE^CHARACTER_8#INTEGER_32^)) == (-6));

const unique BOUNDED^CHARACTER_8^: Type;

axiom ((BOUNDED^CHARACTER_8^) <: (FINITE^CHARACTER_8^));

axiom ((forall t: Type :: { (BOUNDED^CHARACTER_8^) <: (t) } ((BOUNDED^CHARACTER_8^) <: (t)) <==> (((t) == (BOUNDED^CHARACTER_8^)) || ((FINITE^CHARACTER_8^) <: (t)))));

axiom ((FieldId(allocated, BOUNDED^CHARACTER_8^)) == (-1));

axiom ((FieldId(closed, BOUNDED^CHARACTER_8^)) == (-2));

axiom ((FieldId(owner, BOUNDED^CHARACTER_8^)) == (-3));

axiom ((FieldId(owns, BOUNDED^CHARACTER_8^)) == (-4));

axiom ((FieldId(observers, BOUNDED^CHARACTER_8^)) == (-5));

axiom ((FieldId(subjects, BOUNDED^CHARACTER_8^)) == (-6));

function modify.STRING_8.is_less(heap: HeapType, current: ref, other: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, other: ref :: (IsHeap(heap)) ==> ((forall <T79> $o: ref, $f: Field T79 :: { modify.STRING_8.is_less(heap, current, other)[$o, $f] } (modify.STRING_8.is_less(heap, current, other)[$o, $f]) <==> (false)))));

function read.fun.STRING_8.is_less(heap: HeapType, current: ref, other: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, other: ref :: (IsHeap(heap)) ==> ((forall <T80> $o: ref, $f: Field T80 :: { read.fun.STRING_8.is_less(heap, current, other)[$o, $f] } (read.fun.STRING_8.is_less(heap, current, other)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.STRING_8.is_less(heap: HeapType, current: ref, other: ref) returns (bool) {
  ((other) != (Void)) && (is_closed(heap, current)) && (is_closed(heap, other))
}

function trigger.fun.STRING_8.is_less(heap: HeapType, current: ref, other: ref) returns (bool);

const unique SPECIAL^CHARACTER_8^: Type;

axiom (is_frozen(SPECIAL^CHARACTER_8^));

axiom ((SPECIAL^CHARACTER_8^) <: (ABSTRACT_SPECIAL));

axiom ((SPECIAL^CHARACTER_8^) <: (READABLE_INDEXABLE^CHARACTER_8^));

axiom ((forall t: Type :: { (SPECIAL^CHARACTER_8^) <: (t) } ((SPECIAL^CHARACTER_8^) <: (t)) <==> (((t) == (SPECIAL^CHARACTER_8^)) || ((ABSTRACT_SPECIAL) <: (t)) || ((READABLE_INDEXABLE^CHARACTER_8^) <: (t)))));

axiom ((FieldId(allocated, SPECIAL^CHARACTER_8^)) == (-1));

axiom ((FieldId(closed, SPECIAL^CHARACTER_8^)) == (-2));

axiom ((FieldId(owner, SPECIAL^CHARACTER_8^)) == (-3));

axiom ((FieldId(owns, SPECIAL^CHARACTER_8^)) == (-4));

axiom ((FieldId(observers, SPECIAL^CHARACTER_8^)) == (-5));

axiom ((FieldId(subjects, SPECIAL^CHARACTER_8^)) == (-6));

axiom ((forall <T81> $f: Field T81 :: { IsModelField($f, SPECIAL^CHARACTER_8^) } (IsModelField($f, SPECIAL^CHARACTER_8^)) <==> ((($f) == (subjects)) || (($f) == (observers)))));

function { :inline } SPECIAL^CHARACTER_8^.user_inv(heap: HeapType, current: ref) returns (bool) {
  ((fun.SPECIAL^CHARACTER_8^.count(heap, current)) <= (fun.SPECIAL^CHARACTER_8^.capacity(heap, current))) && (Set#IsEmpty(heap[current, observers])) && (Set#IsEmpty(heap[current, subjects])) && (Set#IsEmpty(heap[current, owns])) && (admissibility2(heap, current))
}

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached_exact(heap, current, SPECIAL^CHARACTER_8^)) ==> ((user_inv(heap, current)) <==> (SPECIAL^CHARACTER_8^.user_inv(heap, current)))));

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached(heap, current, SPECIAL^CHARACTER_8^)) ==> ((user_inv(heap, current)) ==> (SPECIAL^CHARACTER_8^.user_inv(heap, current)))));

function modify.STRING_8.is_immutable(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T82> $o: ref, $f: Field T82 :: { modify.STRING_8.is_immutable(heap, current)[$o, $f] } (modify.STRING_8.is_immutable(heap, current)[$o, $f]) <==> (false)))));

function read.fun.STRING_8.is_immutable(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T83> $o: ref, $f: Field T83 :: { read.fun.STRING_8.is_immutable(heap, current)[$o, $f] } (read.fun.STRING_8.is_immutable(heap, current)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.STRING_8.is_immutable(heap: HeapType, current: ref) returns (bool) {
  is_closed(heap, current)
}

function trigger.fun.STRING_8.is_immutable(heap: HeapType, current: ref) returns (bool);

function modify.STRING_8.is_empty(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T84> $o: ref, $f: Field T84 :: { modify.STRING_8.is_empty(heap, current)[$o, $f] } (modify.STRING_8.is_empty(heap, current)[$o, $f]) <==> (false)))));

function read.fun.STRING_8.is_empty(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T85> $o: ref, $f: Field T85 :: { read.fun.STRING_8.is_empty(heap, current)[$o, $f] } (read.fun.STRING_8.is_empty(heap, current)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.STRING_8.is_empty(heap: HeapType, current: ref) returns (bool) {
  is_closed(heap, current)
}

function trigger.fun.STRING_8.is_empty(heap: HeapType, current: ref) returns (bool);

function modify.STRING_8.capacity(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T86> $o: ref, $f: Field T86 :: { modify.STRING_8.capacity(heap, current)[$o, $f] } (modify.STRING_8.capacity(heap, current)[$o, $f]) <==> (false)))));

function read.fun.STRING_8.capacity(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T87> $o: ref, $f: Field T87 :: { read.fun.STRING_8.capacity(heap, current)[$o, $f] } (read.fun.STRING_8.capacity(heap, current)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.STRING_8.capacity(heap: HeapType, current: ref) returns (bool) {
  is_closed(heap, current)
}

function trigger.fun.STRING_8.capacity(heap: HeapType, current: ref) returns (bool);

function modify.STRING_8.full(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T88> $o: ref, $f: Field T88 :: { modify.STRING_8.full(heap, current)[$o, $f] } (modify.STRING_8.full(heap, current)[$o, $f]) <==> (false)))));

function read.fun.STRING_8.full(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T89> $o: ref, $f: Field T89 :: { read.fun.STRING_8.full(heap, current)[$o, $f] } (read.fun.STRING_8.full(heap, current)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.STRING_8.full(heap: HeapType, current: ref) returns (bool) {
  is_closed(heap, current)
}

function trigger.fun.STRING_8.full(heap: HeapType, current: ref) returns (bool);

const unique BAG^CHARACTER_8^: Type;

axiom ((BAG^CHARACTER_8^) <: (COLLECTION^CHARACTER_8^));

axiom ((forall t: Type :: { (BAG^CHARACTER_8^) <: (t) } ((BAG^CHARACTER_8^) <: (t)) <==> (((t) == (BAG^CHARACTER_8^)) || ((COLLECTION^CHARACTER_8^) <: (t)))));

axiom ((FieldId(allocated, BAG^CHARACTER_8^)) == (-1));

axiom ((FieldId(closed, BAG^CHARACTER_8^)) == (-2));

axiom ((FieldId(owner, BAG^CHARACTER_8^)) == (-3));

axiom ((FieldId(owns, BAG^CHARACTER_8^)) == (-4));

axiom ((FieldId(observers, BAG^CHARACTER_8^)) == (-5));

axiom ((FieldId(subjects, BAG^CHARACTER_8^)) == (-6));

const unique COLLECTION^CHARACTER_8^: Type;

axiom ((COLLECTION^CHARACTER_8^) <: (CONTAINER^CHARACTER_8^));

axiom ((forall t: Type :: { (COLLECTION^CHARACTER_8^) <: (t) } ((COLLECTION^CHARACTER_8^) <: (t)) <==> (((t) == (COLLECTION^CHARACTER_8^)) || ((CONTAINER^CHARACTER_8^) <: (t)))));

axiom ((FieldId(allocated, COLLECTION^CHARACTER_8^)) == (-1));

axiom ((FieldId(closed, COLLECTION^CHARACTER_8^)) == (-2));

axiom ((FieldId(owner, COLLECTION^CHARACTER_8^)) == (-3));

axiom ((FieldId(owns, COLLECTION^CHARACTER_8^)) == (-4));

axiom ((FieldId(observers, COLLECTION^CHARACTER_8^)) == (-5));

axiom ((FieldId(subjects, COLLECTION^CHARACTER_8^)) == (-6));

const unique CONTAINER^CHARACTER_8^: Type;

axiom ((CONTAINER^CHARACTER_8^) <: (ANY));

axiom ((forall t: Type :: { (CONTAINER^CHARACTER_8^) <: (t) } ((CONTAINER^CHARACTER_8^) <: (t)) <==> (((t) == (CONTAINER^CHARACTER_8^)) || ((ANY) <: (t)))));

axiom ((FieldId(allocated, CONTAINER^CHARACTER_8^)) == (-1));

axiom ((FieldId(closed, CONTAINER^CHARACTER_8^)) == (-2));

axiom ((FieldId(owner, CONTAINER^CHARACTER_8^)) == (-3));

axiom ((FieldId(owns, CONTAINER^CHARACTER_8^)) == (-4));

axiom ((FieldId(observers, CONTAINER^CHARACTER_8^)) == (-5));

axiom ((FieldId(subjects, CONTAINER^CHARACTER_8^)) == (-6));

const unique FINITE^CHARACTER_8^: Type;

axiom ((FINITE^CHARACTER_8^) <: (BOX^CHARACTER_8^));

axiom ((forall t: Type :: { (FINITE^CHARACTER_8^) <: (t) } ((FINITE^CHARACTER_8^) <: (t)) <==> (((t) == (FINITE^CHARACTER_8^)) || ((BOX^CHARACTER_8^) <: (t)))));

axiom ((FieldId(allocated, FINITE^CHARACTER_8^)) == (-1));

axiom ((FieldId(closed, FINITE^CHARACTER_8^)) == (-2));

axiom ((FieldId(owner, FINITE^CHARACTER_8^)) == (-3));

axiom ((FieldId(owns, FINITE^CHARACTER_8^)) == (-4));

axiom ((FieldId(observers, FINITE^CHARACTER_8^)) == (-5));

axiom ((FieldId(subjects, FINITE^CHARACTER_8^)) == (-6));

const unique BOX^CHARACTER_8^: Type;

axiom ((BOX^CHARACTER_8^) <: (CONTAINER^CHARACTER_8^));

axiom ((forall t: Type :: { (BOX^CHARACTER_8^) <: (t) } ((BOX^CHARACTER_8^) <: (t)) <==> (((t) == (BOX^CHARACTER_8^)) || ((CONTAINER^CHARACTER_8^) <: (t)))));

axiom ((FieldId(allocated, BOX^CHARACTER_8^)) == (-1));

axiom ((FieldId(closed, BOX^CHARACTER_8^)) == (-2));

axiom ((FieldId(owner, BOX^CHARACTER_8^)) == (-3));

axiom ((FieldId(owns, BOX^CHARACTER_8^)) == (-4));

axiom ((FieldId(observers, BOX^CHARACTER_8^)) == (-5));

axiom ((FieldId(subjects, BOX^CHARACTER_8^)) == (-6));

procedure STRING_8.in_observers(Current: ref, new_observers: Set (ref), o: ref) returns (Result: bool where true);
  free requires attached_exact(Heap, Current, STRING_8); // info:type property for argument Current
  free requires Set#ItemsType(Heap, new_observers, ANY); // info:type property for argument new_observers
  free requires Heap[o, allocated]; // info:type property for argument o
  modifies Heap;
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.STRING_8.in_observers(Heap, Current, new_observers, o), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.STRING_8.in_observers(old(Heap), Current, new_observers, o));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.STRING_8.in_observers(Heap, Current, new_observers, o), readable);



function fun.STRING_8.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function fun0.STRING_8.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.STRING_8.in_observers(heap, current, new_observers, o) } { trigger.fun.STRING_8.in_observers(heap, current, new_observers, o) } (pre.fun.STRING_8.in_observers(heap, current, new_observers, o)) ==> ((fun.STRING_8.in_observers(heap, current, new_observers, o)) == (new_observers[o]))));

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.STRING_8.in_observers(heap, current, new_observers, o) } (fun.STRING_8.in_observers(heap, current, new_observers, o)) == (fun0.STRING_8.in_observers(heap, current, new_observers, o))));

axiom ((forall h: HeapType, h': HeapType, current: ref, new_observers: Set (ref), o: ref :: { HeapSucc(h, h'), fun0.STRING_8.in_observers(h, current, new_observers, o), fun0.STRING_8.in_observers(h', current, new_observers, o) } ((HeapSucc(h, h')) && (pre.fun.STRING_8.in_observers(h, current, new_observers, o)) && (pre.fun.STRING_8.in_observers(h', current, new_observers, o)) && (same_inside(h, h', read.fun.STRING_8.in_observers(h, current, new_observers, o)))) ==> ((fun0.STRING_8.in_observers(h, current, new_observers, o)) == (fun0.STRING_8.in_observers(h', current, new_observers, o)))));

function modify.STD_FILES.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T90> $o: ref, $f: Field T90 :: { modify.STD_FILES.in_observers(heap, current, new_observers, o)[$o, $f] } (modify.STD_FILES.in_observers(heap, current, new_observers, o)[$o, $f]) <==> (false)))));

function read.fun.STD_FILES.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T91> $o: ref, $f: Field T91 :: { read.fun.STD_FILES.in_observers(heap, current, new_observers, o)[$o, $f] } (read.fun.STD_FILES.in_observers(heap, current, new_observers, o)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.STD_FILES.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool) {
  true
}

function trigger.fun.STD_FILES.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

procedure V_SPECIAL^PLAYER^.in_observers(Current: ref, new_observers: Set (ref), o: ref) returns (Result: bool where true);
  free requires attached_exact(Heap, Current, V_SPECIAL^PLAYER^); // info:type property for argument Current
  free requires Set#ItemsType(Heap, new_observers, ANY); // info:type property for argument new_observers
  free requires Heap[o, allocated]; // info:type property for argument o
  modifies Heap;
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.V_SPECIAL^PLAYER^.in_observers(Heap, Current, new_observers, o), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.V_SPECIAL^PLAYER^.in_observers(old(Heap), Current, new_observers, o));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.V_SPECIAL^PLAYER^.in_observers(Heap, Current, new_observers, o), readable);



function fun.V_SPECIAL^PLAYER^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function fun0.V_SPECIAL^PLAYER^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.V_SPECIAL^PLAYER^.in_observers(heap, current, new_observers, o) } { trigger.fun.V_SPECIAL^PLAYER^.in_observers(heap, current, new_observers, o) } (pre.fun.V_SPECIAL^PLAYER^.in_observers(heap, current, new_observers, o)) ==> ((fun.V_SPECIAL^PLAYER^.in_observers(heap, current, new_observers, o)) == (new_observers[o]))));

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.V_SPECIAL^PLAYER^.in_observers(heap, current, new_observers, o) } (fun.V_SPECIAL^PLAYER^.in_observers(heap, current, new_observers, o)) == (fun0.V_SPECIAL^PLAYER^.in_observers(heap, current, new_observers, o))));

axiom ((forall h: HeapType, h': HeapType, current: ref, new_observers: Set (ref), o: ref :: { HeapSucc(h, h'), fun0.V_SPECIAL^PLAYER^.in_observers(h, current, new_observers, o), fun0.V_SPECIAL^PLAYER^.in_observers(h', current, new_observers, o) } ((HeapSucc(h, h')) && (pre.fun.V_SPECIAL^PLAYER^.in_observers(h, current, new_observers, o)) && (pre.fun.V_SPECIAL^PLAYER^.in_observers(h', current, new_observers, o)) && (same_inside(h, h', read.fun.V_SPECIAL^PLAYER^.in_observers(h, current, new_observers, o)))) ==> ((fun0.V_SPECIAL^PLAYER^.in_observers(h, current, new_observers, o)) == (fun0.V_SPECIAL^PLAYER^.in_observers(h', current, new_observers, o)))));

const unique COMPARABLE: Type;

axiom ((COMPARABLE) <: (PART_COMPARABLE));

axiom ((forall t: Type :: { (COMPARABLE) <: (t) } ((COMPARABLE) <: (t)) <==> (((t) == (COMPARABLE)) || ((PART_COMPARABLE) <: (t)))));

axiom ((FieldId(allocated, COMPARABLE)) == (-1));

axiom ((FieldId(closed, COMPARABLE)) == (-2));

axiom ((FieldId(owner, COMPARABLE)) == (-3));

axiom ((FieldId(owns, COMPARABLE)) == (-4));

axiom ((FieldId(observers, COMPARABLE)) == (-5));

axiom ((FieldId(subjects, COMPARABLE)) == (-6));

const unique HASHABLE: Type;

axiom ((HASHABLE) <: (ANY));

axiom ((forall t: Type :: { (HASHABLE) <: (t) } ((HASHABLE) <: (t)) <==> (((t) == (HASHABLE)) || ((ANY) <: (t)))));

axiom ((FieldId(allocated, HASHABLE)) == (-1));

axiom ((FieldId(closed, HASHABLE)) == (-2));

axiom ((FieldId(owner, HASHABLE)) == (-3));

axiom ((FieldId(owns, HASHABLE)) == (-4));

axiom ((FieldId(observers, HASHABLE)) == (-5));

axiom ((FieldId(subjects, HASHABLE)) == (-6));

const unique STRING_HANDLER: Type;

axiom ((STRING_HANDLER) <: (ANY));

axiom ((forall t: Type :: { (STRING_HANDLER) <: (t) } ((STRING_HANDLER) <: (t)) <==> (((t) == (STRING_HANDLER)) || ((ANY) <: (t)))));

axiom ((FieldId(allocated, STRING_HANDLER)) == (-1));

axiom ((FieldId(closed, STRING_HANDLER)) == (-2));

axiom ((FieldId(owner, STRING_HANDLER)) == (-3));

axiom ((FieldId(owns, STRING_HANDLER)) == (-4));

axiom ((FieldId(observers, STRING_HANDLER)) == (-5));

axiom ((FieldId(subjects, STRING_HANDLER)) == (-6));

const unique ITERABLE^CHARACTER_8^: Type;

axiom ((ITERABLE^CHARACTER_8^) <: (ANY));

axiom ((forall t: Type :: { (ITERABLE^CHARACTER_8^) <: (t) } ((ITERABLE^CHARACTER_8^) <: (t)) <==> (((t) == (ITERABLE^CHARACTER_8^)) || ((ANY) <: (t)))));

axiom ((FieldId(allocated, ITERABLE^CHARACTER_8^)) == (-1));

axiom ((FieldId(closed, ITERABLE^CHARACTER_8^)) == (-2));

axiom ((FieldId(owner, ITERABLE^CHARACTER_8^)) == (-3));

axiom ((FieldId(owns, ITERABLE^CHARACTER_8^)) == (-4));

axiom ((FieldId(observers, ITERABLE^CHARACTER_8^)) == (-5));

axiom ((FieldId(subjects, ITERABLE^CHARACTER_8^)) == (-6));

const unique ABSTRACT_SPECIAL: Type;

axiom ((ABSTRACT_SPECIAL) <: (DEBUG_OUTPUT));

axiom ((forall t: Type :: { (ABSTRACT_SPECIAL) <: (t) } ((ABSTRACT_SPECIAL) <: (t)) <==> (((t) == (ABSTRACT_SPECIAL)) || ((DEBUG_OUTPUT) <: (t)))));

axiom ((FieldId(allocated, ABSTRACT_SPECIAL)) == (-1));

axiom ((FieldId(closed, ABSTRACT_SPECIAL)) == (-2));

axiom ((FieldId(owner, ABSTRACT_SPECIAL)) == (-3));

axiom ((FieldId(owns, ABSTRACT_SPECIAL)) == (-4));

axiom ((FieldId(observers, ABSTRACT_SPECIAL)) == (-5));

axiom ((FieldId(subjects, ABSTRACT_SPECIAL)) == (-6));

procedure SPECIAL^CHARACTER_8^.count(Current: ref) returns (Result: int where is_integer_32(Result));
  free requires attached_exact(Heap, Current, SPECIAL^CHARACTER_8^); // info:type property for argument Current
  modifies Heap;
  ensures (Result) >= (0); // type:post tag:count_non_negative line:21
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.SPECIAL^CHARACTER_8^.count(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.SPECIAL^CHARACTER_8^.count(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.SPECIAL^CHARACTER_8^.count(Heap, Current), readable);
  requires is_closed(Heap, Current); // type:pre tag:default_is_closed default:contracts
  free ensures (Result) == (fun.SPECIAL^CHARACTER_8^.count(old(Heap), Current));



function fun.SPECIAL^CHARACTER_8^.count(heap: HeapType, current: ref) returns (int);

axiom ((forall heap: HeapType, current: ref :: { fun.SPECIAL^CHARACTER_8^.count(heap, current) } (pre.fun.SPECIAL^CHARACTER_8^.count(heap, current)) ==> (((fun.SPECIAL^CHARACTER_8^.count(heap, current)) >= (0)) && (is_integer_32(fun.SPECIAL^CHARACTER_8^.count(heap, current))))));

axiom ((forall h: HeapType, h': HeapType, current: ref :: { HeapSucc(h, h'), fun.SPECIAL^CHARACTER_8^.count(h, current), fun.SPECIAL^CHARACTER_8^.count(h', current) } ((HeapSucc(h, h')) && (pre.fun.SPECIAL^CHARACTER_8^.count(h, current)) && (pre.fun.SPECIAL^CHARACTER_8^.count(h', current)) && (same_inside(h, h', read.fun.SPECIAL^CHARACTER_8^.count(h, current)))) ==> ((fun.SPECIAL^CHARACTER_8^.count(h, current)) == (fun.SPECIAL^CHARACTER_8^.count(h', current)))));

procedure SPECIAL^CHARACTER_8^.capacity(Current: ref) returns (Result: int where is_integer_32(Result));
  free requires attached_exact(Heap, Current, SPECIAL^CHARACTER_8^); // info:type property for argument Current
  modifies Heap;
  ensures (Result) >= (0); // type:post tag:count_non_negative line:28
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.SPECIAL^CHARACTER_8^.capacity(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.SPECIAL^CHARACTER_8^.capacity(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.SPECIAL^CHARACTER_8^.capacity(Heap, Current), readable);
  requires is_closed(Heap, Current); // type:pre tag:default_is_closed default:contracts
  free ensures (Result) == (fun.SPECIAL^CHARACTER_8^.capacity(old(Heap), Current));



function fun.SPECIAL^CHARACTER_8^.capacity(heap: HeapType, current: ref) returns (int);

axiom ((forall heap: HeapType, current: ref :: { fun.SPECIAL^CHARACTER_8^.capacity(heap, current) } (pre.fun.SPECIAL^CHARACTER_8^.capacity(heap, current)) ==> (((fun.SPECIAL^CHARACTER_8^.capacity(heap, current)) >= (0)) && (is_integer_32(fun.SPECIAL^CHARACTER_8^.capacity(heap, current))))));

axiom ((forall h: HeapType, h': HeapType, current: ref :: { HeapSucc(h, h'), fun.SPECIAL^CHARACTER_8^.capacity(h, current), fun.SPECIAL^CHARACTER_8^.capacity(h', current) } ((HeapSucc(h, h')) && (pre.fun.SPECIAL^CHARACTER_8^.capacity(h, current)) && (pre.fun.SPECIAL^CHARACTER_8^.capacity(h', current)) && (same_inside(h, h', read.fun.SPECIAL^CHARACTER_8^.capacity(h, current)))) ==> ((fun.SPECIAL^CHARACTER_8^.capacity(h, current)) == (fun.SPECIAL^CHARACTER_8^.capacity(h', current)))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, owns, v, o) } (attached_exact(heap, current, SPECIAL^CHARACTER_8^)) ==> ((guard(heap, current, owns, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, subjects, v, o) } (attached_exact(heap, current, SPECIAL^CHARACTER_8^)) ==> ((guard(heap, current, subjects, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached_exact(heap, current, SPECIAL^CHARACTER_8^)) ==> ((guard(heap, current, observers, v, o)) <==> (fun.SPECIAL^CHARACTER_8^.in_observers(heap, current, v, o)))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached(heap, current, SPECIAL^CHARACTER_8^)) ==> ((guard(heap, current, observers, v, o)) ==> (fun.SPECIAL^CHARACTER_8^.in_observers(heap, current, v, o)))));

function modify.STRING_8.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T92> $o: ref, $f: Field T92 :: { modify.STRING_8.in_observers(heap, current, new_observers, o)[$o, $f] } (modify.STRING_8.in_observers(heap, current, new_observers, o)[$o, $f]) <==> (false)))));

function read.fun.STRING_8.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T93> $o: ref, $f: Field T93 :: { read.fun.STRING_8.in_observers(heap, current, new_observers, o)[$o, $f] } (read.fun.STRING_8.in_observers(heap, current, new_observers, o)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.STRING_8.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool) {
  true
}

function trigger.fun.STRING_8.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function modify.V_SPECIAL^PLAYER^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T94> $o: ref, $f: Field T94 :: { modify.V_SPECIAL^PLAYER^.in_observers(heap, current, new_observers, o)[$o, $f] } (modify.V_SPECIAL^PLAYER^.in_observers(heap, current, new_observers, o)[$o, $f]) <==> (false)))));

function read.fun.V_SPECIAL^PLAYER^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T95> $o: ref, $f: Field T95 :: { read.fun.V_SPECIAL^PLAYER^.in_observers(heap, current, new_observers, o)[$o, $f] } (read.fun.V_SPECIAL^PLAYER^.in_observers(heap, current, new_observers, o)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.V_SPECIAL^PLAYER^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool) {
  true
}

function trigger.fun.V_SPECIAL^PLAYER^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

const unique PART_COMPARABLE: Type;

axiom ((PART_COMPARABLE) <: (ANY));

axiom ((forall t: Type :: { (PART_COMPARABLE) <: (t) } ((PART_COMPARABLE) <: (t)) <==> (((t) == (PART_COMPARABLE)) || ((ANY) <: (t)))));

axiom ((FieldId(allocated, PART_COMPARABLE)) == (-1));

axiom ((FieldId(closed, PART_COMPARABLE)) == (-2));

axiom ((FieldId(owner, PART_COMPARABLE)) == (-3));

axiom ((FieldId(owns, PART_COMPARABLE)) == (-4));

axiom ((FieldId(observers, PART_COMPARABLE)) == (-5));

axiom ((FieldId(subjects, PART_COMPARABLE)) == (-6));

const unique DEBUG_OUTPUT: Type;

axiom ((DEBUG_OUTPUT) <: (ANY));

axiom ((forall t: Type :: { (DEBUG_OUTPUT) <: (t) } ((DEBUG_OUTPUT) <: (t)) <==> (((t) == (DEBUG_OUTPUT)) || ((ANY) <: (t)))));

axiom ((FieldId(allocated, DEBUG_OUTPUT)) == (-1));

axiom ((FieldId(closed, DEBUG_OUTPUT)) == (-2));

axiom ((FieldId(owner, DEBUG_OUTPUT)) == (-3));

axiom ((FieldId(owns, DEBUG_OUTPUT)) == (-4));

axiom ((FieldId(observers, DEBUG_OUTPUT)) == (-5));

axiom ((FieldId(subjects, DEBUG_OUTPUT)) == (-6));

function modify.SPECIAL^CHARACTER_8^.count(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T96> $o: ref, $f: Field T96 :: { modify.SPECIAL^CHARACTER_8^.count(heap, current)[$o, $f] } (modify.SPECIAL^CHARACTER_8^.count(heap, current)[$o, $f]) <==> (false)))));

function read.fun.SPECIAL^CHARACTER_8^.count(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T97> $o: ref, $f: Field T97 :: { read.fun.SPECIAL^CHARACTER_8^.count(heap, current)[$o, $f] } (read.fun.SPECIAL^CHARACTER_8^.count(heap, current)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.SPECIAL^CHARACTER_8^.count(heap: HeapType, current: ref) returns (bool) {
  is_closed(heap, current)
}

function trigger.fun.SPECIAL^CHARACTER_8^.count(heap: HeapType, current: ref) returns (bool);

function modify.SPECIAL^CHARACTER_8^.capacity(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T98> $o: ref, $f: Field T98 :: { modify.SPECIAL^CHARACTER_8^.capacity(heap, current)[$o, $f] } (modify.SPECIAL^CHARACTER_8^.capacity(heap, current)[$o, $f]) <==> (false)))));

function read.fun.SPECIAL^CHARACTER_8^.capacity(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T99> $o: ref, $f: Field T99 :: { read.fun.SPECIAL^CHARACTER_8^.capacity(heap, current)[$o, $f] } (read.fun.SPECIAL^CHARACTER_8^.capacity(heap, current)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.SPECIAL^CHARACTER_8^.capacity(heap: HeapType, current: ref) returns (bool) {
  is_closed(heap, current)
}

function trigger.fun.SPECIAL^CHARACTER_8^.capacity(heap: HeapType, current: ref) returns (bool);

procedure SPECIAL^CHARACTER_8^.in_observers(Current: ref, new_observers: Set (ref), o: ref) returns (Result: bool where true);
  free requires attached_exact(Heap, Current, SPECIAL^CHARACTER_8^); // info:type property for argument Current
  free requires Set#ItemsType(Heap, new_observers, ANY); // info:type property for argument new_observers
  free requires Heap[o, allocated]; // info:type property for argument o
  modifies Heap;
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.SPECIAL^CHARACTER_8^.in_observers(Heap, Current, new_observers, o), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.SPECIAL^CHARACTER_8^.in_observers(old(Heap), Current, new_observers, o));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.SPECIAL^CHARACTER_8^.in_observers(Heap, Current, new_observers, o), readable);



function fun.SPECIAL^CHARACTER_8^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function fun0.SPECIAL^CHARACTER_8^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.SPECIAL^CHARACTER_8^.in_observers(heap, current, new_observers, o) } { trigger.fun.SPECIAL^CHARACTER_8^.in_observers(heap, current, new_observers, o) } (pre.fun.SPECIAL^CHARACTER_8^.in_observers(heap, current, new_observers, o)) ==> ((fun.SPECIAL^CHARACTER_8^.in_observers(heap, current, new_observers, o)) == (new_observers[o]))));

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.SPECIAL^CHARACTER_8^.in_observers(heap, current, new_observers, o) } (fun.SPECIAL^CHARACTER_8^.in_observers(heap, current, new_observers, o)) == (fun0.SPECIAL^CHARACTER_8^.in_observers(heap, current, new_observers, o))));

axiom ((forall h: HeapType, h': HeapType, current: ref, new_observers: Set (ref), o: ref :: { HeapSucc(h, h'), fun0.SPECIAL^CHARACTER_8^.in_observers(h, current, new_observers, o), fun0.SPECIAL^CHARACTER_8^.in_observers(h', current, new_observers, o) } ((HeapSucc(h, h')) && (pre.fun.SPECIAL^CHARACTER_8^.in_observers(h, current, new_observers, o)) && (pre.fun.SPECIAL^CHARACTER_8^.in_observers(h', current, new_observers, o)) && (same_inside(h, h', read.fun.SPECIAL^CHARACTER_8^.in_observers(h, current, new_observers, o)))) ==> ((fun0.SPECIAL^CHARACTER_8^.in_observers(h, current, new_observers, o)) == (fun0.SPECIAL^CHARACTER_8^.in_observers(h', current, new_observers, o)))));

function modify.SPECIAL^CHARACTER_8^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T100> $o: ref, $f: Field T100 :: { modify.SPECIAL^CHARACTER_8^.in_observers(heap, current, new_observers, o)[$o, $f] } (modify.SPECIAL^CHARACTER_8^.in_observers(heap, current, new_observers, o)[$o, $f]) <==> (false)))));

function read.fun.SPECIAL^CHARACTER_8^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T101> $o: ref, $f: Field T101 :: { read.fun.SPECIAL^CHARACTER_8^.in_observers(heap, current, new_observers, o)[$o, $f] } (read.fun.SPECIAL^CHARACTER_8^.in_observers(heap, current, new_observers, o)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.SPECIAL^CHARACTER_8^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool) {
  true
}

function trigger.fun.SPECIAL^CHARACTER_8^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);
