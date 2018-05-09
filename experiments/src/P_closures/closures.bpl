// Automatically generated (12/12/2017 1:55:13.483 PM)

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

// File: /home/caf/tools/eve_96960/studio/tools/autoproof/agents.bpl

// ----------------------------------------------------------------------
// Agent theory

const unique ROUTINE: Type;
axiom (ROUTINE <: ANY);

const unique PROCEDURE: Type;
axiom (PROCEDURE <: ROUTINE);

const unique FUNCTION: Type;
axiom (FUNCTION <: ROUTINE);

// Precondition functions for different number of arguments

function routine.precondition_0 (heap: HeapType, agent: ref) returns (bool);
function routine.precondition_1<T1> (heap: HeapType, agent: ref, arg1: T1) returns (bool);
function routine.precondition_2<T1, T2> (heap: HeapType, agent: ref, arg1: T1, arg2: T2) returns (bool);

// Postcondition functions for different number of arguments

function routine.postcondition_0 (heap: HeapType, old_heap: HeapType, agent: ref) returns (bool);
function routine.postcondition_1<T1> (heap: HeapType, old_heap: HeapType, agent: ref, arg1: T1) returns (bool);
function routine.postcondition_2<T1, T2> (heap: HeapType, old_heap: HeapType, agent: ref, arg1: T1, arg2: T2) returns (bool);

// Postcondition functions for different number of arguments and return values

function function.postcondition_0<R> (heap: HeapType, old_heap: HeapType, agent: ref, result: R) returns (bool);
function function.postcondition_1<T1, R> (heap: HeapType, old_heap: HeapType, agent: ref, arg1: T1, result: R) returns (bool);
function function.postcondition_2<T1, T2, R> (heap: HeapType, old_heap: HeapType, agent: ref, arg1: T1, arg2: T2, result: R) returns (bool);

// Frame condition function

function routine.modify_0 (heap: HeapType, agent: ref) returns (Frame);
function routine.modify_1<T1> (heap: HeapType, agent: ref, arg1: T1) returns (Frame);
function routine.modify_2<T1, T2> (heap: HeapType, agent: ref, arg1: T1, arg2: T2) returns (Frame);

// Call functions for different number of arguments

procedure routine.call_0 (Current: ref);
  requires attached(Heap, Current, ROUTINE); // info:type property for argument Current
  requires routine.precondition_0(Heap, Current); // type:pre tag:routine_precondition R1
  modifies Heap;
  ensures routine.postcondition_0(Heap, old(Heap), Current);
  free ensures global(Heap);
  requires Frame#Subset(routine.modify_0(Heap, Current), writable); // type:pre tag:frame_writable
  free ensures same_outside(old(Heap), Heap, routine.modify_0(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);

procedure routine.call_1<T1> (Current: ref, arg1: T1);
  requires attached(Heap, Current, ROUTINE); // info:type property for argument Current
  requires routine.precondition_1(Heap, Current, arg1); // type:pre tag:routine_precondition R1
  modifies Heap;
  ensures routine.postcondition_1(Heap, old(Heap), Current, arg1);
  free ensures global(Heap);
  requires Frame#Subset(routine.modify_1(Heap, Current, arg1), writable); // type:pre tag:frame_writable
  free ensures same_outside(old(Heap), Heap, routine.modify_1(old(Heap), Current, arg1));
  free ensures HeapSucc(old(Heap), Heap);

procedure routine.call_2<T1, T2> (Current: ref, arg1: T1, arg2: T2);
  requires attached(Heap, Current, ROUTINE); // info:type property for argument Current
  requires routine.precondition_2(Heap, Current, arg1, arg2); // pre ROUTINE:call tag:precondition
  modifies Heap;
  ensures routine.postcondition_2(Heap, old(Heap), Current, arg1, arg2);
  free ensures global(Heap);
  requires Frame#Subset(routine.modify_2(Heap, Current, arg1, arg2), writable); // type:pre tag:frame_writable
  free ensures same_outside(old(Heap), Heap, routine.modify_2(old(Heap), Current, arg1, arg2));
  free ensures HeapSucc(old(Heap), Heap);

procedure function.item_0<R> (Current: ref) returns (Result: R);
  requires attached(Heap, Current, FUNCTION); // info:type property for argument Current
  requires routine.precondition_0(Heap, Current);
  modifies Heap;
  ensures function.postcondition_0(Heap, old(Heap), Current, Result);
  requires Frame#Subset(routine.modify_0(Heap, Current), writable); // type:pre tag:frame_writable
  free ensures same_outside(old(Heap), Heap, routine.modify_0(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);

procedure function.item_1<T1, R> (Current: ref, arg1: T1) returns (Result: R);
  requires attached(Heap, Current, FUNCTION); // info:type property for argument Current
  requires routine.precondition_1(Heap, Current, arg1);
  modifies Heap;
  ensures function.postcondition_1(Heap, old(Heap), Current, arg1, Result);
  free ensures global(Heap);
  requires Frame#Subset(routine.modify_1(Heap, Current, arg1), writable); // type:pre tag:frame_writable
  free ensures same_outside(old(Heap), Heap, routine.modify_1(old(Heap), Current, arg1));
  free ensures HeapSucc(old(Heap), Heap);

procedure function.item_2<T1, T2, R> (Current: ref, arg1: T1, arg2: T2) returns (Result: R);
  requires attached(Heap, Current, FUNCTION); // info:type property for argument Current
  requires routine.precondition_2(Heap, Current, arg1, arg2);
  modifies Heap;
  ensures function.postcondition_2(Heap, old(Heap), Current, arg1, arg2, Result);
  free ensures global(Heap);
  requires Frame#Subset(routine.modify_2(Heap, Current, arg1, arg2), writable); // type:pre tag:frame_writable
  free ensures same_outside(old(Heap), Heap, routine.modify_2(old(Heap), Current, arg1, arg2));
  free ensures HeapSucc(old(Heap), Heap);

procedure create.routine(Current: ref);
  free requires attached(Heap, Current, ROUTINE); // info:type property for argument Current
  modifies Heap;
  requires (forall <T3> $f: Field T3 :: (($f) != (allocated)) ==> ((Heap[Current, $f]) == (Default($f))));
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.create.routine(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.create.routine(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts

function modify.create.routine(heap: HeapType, current: ref) returns (Frame);
axiom (forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T6> $o: ref, $f: Field T6 :: { modify.create.routine(heap, current)[$o, $f] } (modify.create.routine(heap, current)[$o, $f]) <==> (($o) == (current)))));



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

const unique FORMATTER_APPLICATION: Type;

axiom ((FORMATTER_APPLICATION) <: (ANY));

axiom ((forall t: Type :: { (FORMATTER_APPLICATION) <: (t) } ((FORMATTER_APPLICATION) <: (t)) <==> (((t) == (FORMATTER_APPLICATION)) || ((ANY) <: (t)))));

axiom ((FieldId(allocated, FORMATTER_APPLICATION)) == (-1));

axiom ((FieldId(closed, FORMATTER_APPLICATION)) == (-2));

axiom ((FieldId(owner, FORMATTER_APPLICATION)) == (-3));

axiom ((FieldId(owns, FORMATTER_APPLICATION)) == (-4));

axiom ((FieldId(observers, FORMATTER_APPLICATION)) == (-5));

axiom ((FieldId(subjects, FORMATTER_APPLICATION)) == (-6));

axiom ((forall <T0> $f: Field T0 :: { IsModelField($f, FORMATTER_APPLICATION) } (IsModelField($f, FORMATTER_APPLICATION)) <==> ((($f) == (subjects)) || (($f) == (observers)))));

function { :inline } FORMATTER_APPLICATION.user_inv(heap: HeapType, current: ref) returns (bool) {
  (Set#IsEmpty(heap[current, observers])) && (Set#IsEmpty(heap[current, subjects])) && (Set#IsEmpty(heap[current, owns])) && (admissibility2(heap, current))
}

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached_exact(heap, current, FORMATTER_APPLICATION)) ==> ((user_inv(heap, current)) <==> (FORMATTER_APPLICATION.user_inv(heap, current)))));

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached(heap, current, FORMATTER_APPLICATION)) ==> ((user_inv(heap, current)) ==> (FORMATTER_APPLICATION.user_inv(heap, current)))));

procedure FORMATTER_APPLICATION.invariant_admissibility_check(Current: ref);
  requires attached_exact(Heap, Current, FORMATTER_APPLICATION);



implementation FORMATTER_APPLICATION.invariant_admissibility_check(Current: ref)
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

procedure create.FORMATTER_APPLICATION.default_create(Current: ref);
  free requires attached_exact(Heap, Current, FORMATTER_APPLICATION); // info:type property for argument Current
  modifies Heap;
  requires (forall <T2> $f: Field T2 :: (($f) != (allocated)) ==> ((Heap[Current, $f]) == (Default($f))));
  ensures (forall <T3> $f: Field T3 :: ((($f) != (allocated)) && (($f) != (closed))) ==> ((Heap[Current, $f]) == (Default($f))));
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.FORMATTER_APPLICATION.default_create(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.FORMATTER_APPLICATION.default_create(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts



implementation create.FORMATTER_APPLICATION.default_create(Current: ref)
{
  entry:
  assume {:captureState "create.FORMATTER_APPLICATION.default_create"} true;
  if (*) {
    assert Set#IsEmpty(Heap[Current, observers]); // type:inv tag:default_observers line:364 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, subjects]); // type:inv tag:default_subjects line:364 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, owns]); // type:inv tag:default_owns line:364 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert admissibility2(Heap, Current); // type:inv tag:A2 line:364 cid:1 rid:55
    assume false;
  }
  call wrap(Current); // default:wrapping cid:1 rid:55 line:364
}

procedure FORMATTER_APPLICATION.apply_align_left(Current: ref, a_formatter: ref, a_paragraph: ref);
  free requires attached_exact(Heap, Current, FORMATTER_APPLICATION); // info:type property for argument Current
  free requires detachable(Heap, a_formatter, FORMATTER); // info:type property for argument a_formatter
  free requires detachable(Heap, a_paragraph, PARAGRAPH); // info:type property for argument a_paragraph
  modifies Heap;
  requires (a_formatter) != (Void); // type:pre line:10
  requires (a_paragraph) != (Void); // type:pre line:11
  requires !(Heap[a_paragraph, PARAGRAPH.is_left_aligned]); // type:pre line:12
  ensures (a_paragraph) != (Void); // type:attached line:21
  ensures Heap[a_paragraph, PARAGRAPH.is_left_aligned]; // type:post line:21
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.FORMATTER_APPLICATION.apply_align_left(Heap, Current, a_formatter, a_paragraph), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.FORMATTER_APPLICATION.apply_align_left(old(Heap), Current, a_formatter, a_paragraph));
  free ensures HeapSucc(old(Heap), Heap);
  requires is_wrapped(Heap, Current); // type:pre tag:default_is_wrapped default:contracts
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts
  requires is_wrapped(Heap, a_formatter); // type:pre tag:arg_a_formatter_is_wrapped default:contracts
  ensures is_wrapped(Heap, a_formatter); // type:post tag:arg_a_formatter_is_wrapped default:contracts
  requires is_wrapped(Heap, a_paragraph); // type:pre tag:arg_a_paragraph_is_wrapped default:contracts
  ensures is_wrapped(Heap, a_paragraph); // type:post tag:arg_a_paragraph_is_wrapped default:contracts



function { :inline } variant.FORMATTER_APPLICATION.apply_align_left.1(heap: HeapType, current: ref, a_formatter: ref, a_paragraph: ref) returns (ref) {
  a_formatter
}

function { :inline } variant.FORMATTER_APPLICATION.apply_align_left.2(heap: HeapType, current: ref, a_formatter: ref, a_paragraph: ref) returns (ref) {
  a_paragraph
}

implementation FORMATTER_APPLICATION.apply_align_left(Current: ref, a_formatter: ref, a_paragraph: ref)
{
  var temp_1: ref;
  var local1: ref where detachable(Heap, local1, PROCEDURE);

  init_locals:
  temp_1 := Void;
  local1 := Void;

  entry:
  assume {:captureState "FORMATTER_APPLICATION.apply_align_left"} true;
  // /home/caf/temp/comcom/repo-closures/formatter_application.e:18
  // l_agent := agent a_formatter.align_left
  call temp_1 := allocate(PROCEDURE);
  call create.routine(temp_1);
  assume (forall h: HeapType, oarg_1: ref :: (routine.precondition_1(h, temp_1, oarg_1)) == (pre.fun.FORMATTER.align_left(h, a_formatter, oarg_1)));
  assume (forall h: HeapType, old_h: HeapType, oarg_1: ref :: (routine.postcondition_1(h, old_h, temp_1, oarg_1)) == (post.FORMATTER.align_left(h, old_h, a_formatter, oarg_1)));
  assume (forall h: HeapType, oarg_1: ref :: (routine.modify_1(h, temp_1, oarg_1)) == (modify.FORMATTER.align_left(h, a_formatter, oarg_1)));
  local1 := temp_1;
  // /home/caf/temp/comcom/repo-closures/formatter_application.e:19
  // a_paragraph.format (l_agent)
  assert {:subsumption 0} (a_paragraph) != (Void); // type:attached line:19
  call PARAGRAPH.format(a_paragraph, local1); // line:19 cid:405 rid:5421
}

procedure FORMATTER_APPLICATION.apply_align_right(Current: ref, a_formatter: ref, a_paragraph: ref);
  free requires attached_exact(Heap, Current, FORMATTER_APPLICATION); // info:type property for argument Current
  free requires detachable(Heap, a_formatter, FORMATTER); // info:type property for argument a_formatter
  free requires detachable(Heap, a_paragraph, PARAGRAPH); // info:type property for argument a_paragraph
  modifies Heap;
  requires (a_formatter) != (Void); // type:pre line:29
  requires (a_paragraph) != (Void); // type:pre line:30
  requires Heap[a_paragraph, PARAGRAPH.is_left_aligned]; // type:pre line:31
  ensures (a_paragraph) != (Void); // type:attached line:40
  ensures !(Heap[a_paragraph, PARAGRAPH.is_left_aligned]); // type:post line:40
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.FORMATTER_APPLICATION.apply_align_right(Heap, Current, a_formatter, a_paragraph), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.FORMATTER_APPLICATION.apply_align_right(old(Heap), Current, a_formatter, a_paragraph));
  free ensures HeapSucc(old(Heap), Heap);
  requires is_wrapped(Heap, Current); // type:pre tag:default_is_wrapped default:contracts
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts
  requires is_wrapped(Heap, a_formatter); // type:pre tag:arg_a_formatter_is_wrapped default:contracts
  ensures is_wrapped(Heap, a_formatter); // type:post tag:arg_a_formatter_is_wrapped default:contracts
  requires is_wrapped(Heap, a_paragraph); // type:pre tag:arg_a_paragraph_is_wrapped default:contracts
  ensures is_wrapped(Heap, a_paragraph); // type:post tag:arg_a_paragraph_is_wrapped default:contracts



function { :inline } variant.FORMATTER_APPLICATION.apply_align_right.1(heap: HeapType, current: ref, a_formatter: ref, a_paragraph: ref) returns (ref) {
  a_formatter
}

function { :inline } variant.FORMATTER_APPLICATION.apply_align_right.2(heap: HeapType, current: ref, a_formatter: ref, a_paragraph: ref) returns (ref) {
  a_paragraph
}

implementation FORMATTER_APPLICATION.apply_align_right(Current: ref, a_formatter: ref, a_paragraph: ref)
{
  var temp_2: ref;
  var local1: ref where detachable(Heap, local1, PROCEDURE);

  init_locals:
  temp_2 := Void;
  local1 := Void;

  entry:
  assume {:captureState "FORMATTER_APPLICATION.apply_align_right"} true;
  // /home/caf/temp/comcom/repo-closures/formatter_application.e:37
  // l_agent := agent a_formatter.align_right
  call temp_2 := allocate(PROCEDURE);
  call create.routine(temp_2);
  assume (forall h: HeapType, oarg_1: ref :: (routine.precondition_1(h, temp_2, oarg_1)) == (pre.fun.FORMATTER.align_right(h, a_formatter, oarg_1)));
  assume (forall h: HeapType, old_h: HeapType, oarg_1: ref :: (routine.postcondition_1(h, old_h, temp_2, oarg_1)) == (post.FORMATTER.align_right(h, old_h, a_formatter, oarg_1)));
  assume (forall h: HeapType, oarg_1: ref :: (routine.modify_1(h, temp_2, oarg_1)) == (modify.FORMATTER.align_right(h, a_formatter, oarg_1)));
  local1 := temp_2;
  // /home/caf/temp/comcom/repo-closures/formatter_application.e:38
  // a_paragraph.format (l_agent)
  assert {:subsumption 0} (a_paragraph) != (Void); // type:attached line:38
  call PARAGRAPH.format(a_paragraph, local1); // line:38 cid:405 rid:5421
}

const unique TAPE: Type;

axiom ((TAPE) <: (ANY));

axiom ((forall t: Type :: { (TAPE) <: (t) } ((TAPE) <: (t)) <==> (((t) == (TAPE)) || ((ANY) <: (t)))));

axiom ((FieldId(allocated, TAPE)) == (-1));

axiom ((FieldId(closed, TAPE)) == (-2));

axiom ((FieldId(owner, TAPE)) == (-3));

axiom ((FieldId(owns, TAPE)) == (-4));

axiom ((FieldId(observers, TAPE)) == (-5));

axiom ((FieldId(subjects, TAPE)) == (-6));

axiom ((forall <T5> $f: Field T5 :: { IsModelField($f, TAPE) } (IsModelField($f, TAPE)) <==> ((($f) == (subjects)) || (($f) == (observers)))));

function { :inline } TAPE.user_inv(heap: HeapType, current: ref) returns (bool) {
  (Set#IsEmpty(heap[current, observers])) && (Set#IsEmpty(heap[current, subjects])) && (Set#IsEmpty(heap[current, owns])) && (admissibility2(heap, current))
}

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached_exact(heap, current, TAPE)) ==> ((user_inv(heap, current)) <==> (TAPE.user_inv(heap, current)))));

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached(heap, current, TAPE)) ==> ((user_inv(heap, current)) ==> (TAPE.user_inv(heap, current)))));

procedure TAPE.invariant_admissibility_check(Current: ref);
  requires attached_exact(Heap, Current, TAPE);



implementation TAPE.invariant_admissibility_check(Current: ref)
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

procedure create.TAPE.default_create(Current: ref);
  free requires attached_exact(Heap, Current, TAPE); // info:type property for argument Current
  modifies Heap;
  requires (forall <T6> $f: Field T6 :: (($f) != (allocated)) ==> ((Heap[Current, $f]) == (Default($f))));
  ensures (forall <T7> $f: Field T7 :: ((($f) != (allocated)) && (($f) != (closed))) ==> ((Heap[Current, $f]) == (Default($f))));
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.TAPE.default_create(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.TAPE.default_create(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts



implementation create.TAPE.default_create(Current: ref)
{
  entry:
  assume {:captureState "create.TAPE.default_create"} true;
  if (*) {
    assert Set#IsEmpty(Heap[Current, observers]); // type:inv tag:default_observers line:11 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, subjects]); // type:inv tag:default_subjects line:11 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, owns]); // type:inv tag:default_owns line:11 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert admissibility2(Heap, Current); // type:inv tag:A2 line:11 cid:1 rid:55
    assume false;
  }
  call wrap(Current); // default:wrapping cid:1 rid:55 line:364
}

procedure TAPE.save(Current: ref, o: ref);
  free requires attached_exact(Heap, Current, TAPE); // info:type property for argument Current
  free requires Heap[o, allocated]; // info:type property for argument o
  modifies Heap;
  requires (o) != (Void); // type:pre tag:o_not_void line:8
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.TAPE.save(Heap, Current, o), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.TAPE.save(old(Heap), Current, o));
  free ensures HeapSucc(old(Heap), Heap);
  requires is_wrapped(Heap, Current); // type:pre tag:default_is_wrapped default:contracts
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts
  requires is_wrapped(Heap, o); // type:pre tag:arg_o_is_wrapped default:contracts
  ensures is_wrapped(Heap, o); // type:post tag:arg_o_is_wrapped default:contracts



function { :inline } variant.TAPE.save.1(heap: HeapType, current: ref, o: ref) returns (ref) {
  o
}

implementation TAPE.save(Current: ref, o: ref)
{
  entry:
  assume {:captureState "TAPE.save"} true;
  call unwrap(Current); // default:wrapping cid:1 rid:57 line:5
  assume TAPE.user_inv(Heap, Current);
  if (*) {
    assert Set#IsEmpty(Heap[Current, observers]); // type:inv tag:default_observers line:11 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, subjects]); // type:inv tag:default_subjects line:11 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, owns]); // type:inv tag:default_owns line:11 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert admissibility2(Heap, Current); // type:inv tag:A2 line:11 cid:1 rid:55
    assume false;
  }
  call wrap(Current); // default:wrapping cid:1 rid:55 line:11
}

const unique ACCOUNT_CLIENT: Type;

axiom ((ACCOUNT_CLIENT) <: (ANY));

axiom ((forall t: Type :: { (ACCOUNT_CLIENT) <: (t) } ((ACCOUNT_CLIENT) <: (t)) <==> (((t) == (ACCOUNT_CLIENT)) || ((ANY) <: (t)))));

axiom ((FieldId(allocated, ACCOUNT_CLIENT)) == (-1));

axiom ((FieldId(closed, ACCOUNT_CLIENT)) == (-2));

axiom ((FieldId(owner, ACCOUNT_CLIENT)) == (-3));

axiom ((FieldId(owns, ACCOUNT_CLIENT)) == (-4));

axiom ((FieldId(observers, ACCOUNT_CLIENT)) == (-5));

axiom ((FieldId(subjects, ACCOUNT_CLIENT)) == (-6));

axiom ((forall <T8> $f: Field T8 :: { IsModelField($f, ACCOUNT_CLIENT) } (IsModelField($f, ACCOUNT_CLIENT)) <==> ((($f) == (subjects)) || (($f) == (observers)))));

function { :inline } ACCOUNT_CLIENT.user_inv(heap: HeapType, current: ref) returns (bool) {
  (Set#IsEmpty(heap[current, observers])) && (Set#IsEmpty(heap[current, subjects])) && (Set#IsEmpty(heap[current, owns])) && (admissibility2(heap, current))
}

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached_exact(heap, current, ACCOUNT_CLIENT)) ==> ((user_inv(heap, current)) <==> (ACCOUNT_CLIENT.user_inv(heap, current)))));

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached(heap, current, ACCOUNT_CLIENT)) ==> ((user_inv(heap, current)) ==> (ACCOUNT_CLIENT.user_inv(heap, current)))));

procedure ACCOUNT_CLIENT.invariant_admissibility_check(Current: ref);
  requires attached_exact(Heap, Current, ACCOUNT_CLIENT);



implementation ACCOUNT_CLIENT.invariant_admissibility_check(Current: ref)
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

procedure create.ACCOUNT_CLIENT.default_create(Current: ref);
  free requires attached_exact(Heap, Current, ACCOUNT_CLIENT); // info:type property for argument Current
  modifies Heap;
  requires (forall <T9> $f: Field T9 :: (($f) != (allocated)) ==> ((Heap[Current, $f]) == (Default($f))));
  ensures (forall <T10> $f: Field T10 :: ((($f) != (allocated)) && (($f) != (closed))) ==> ((Heap[Current, $f]) == (Default($f))));
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.ACCOUNT_CLIENT.default_create(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.ACCOUNT_CLIENT.default_create(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts



implementation create.ACCOUNT_CLIENT.default_create(Current: ref)
{
  entry:
  assume {:captureState "create.ACCOUNT_CLIENT.default_create"} true;
  if (*) {
    assert Set#IsEmpty(Heap[Current, observers]); // type:inv tag:default_observers line:26 cid:1 rid:55
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
  call wrap(Current); // default:wrapping cid:1 rid:55 line:364
}

procedure ACCOUNT_CLIENT.test_agents(Current: ref);
  free requires attached_exact(Heap, Current, ACCOUNT_CLIENT); // info:type property for argument Current
  modifies Heap;
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.ACCOUNT_CLIENT.test_agents(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.ACCOUNT_CLIENT.test_agents(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);
  requires is_wrapped(Heap, Current); // type:pre tag:default_is_wrapped default:contracts
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts



function { :inline } variant.ACCOUNT_CLIENT.test_agents.1(heap: HeapType, current: ref) returns (int) {
  0
}

implementation ACCOUNT_CLIENT.test_agents(Current: ref)
{
  var temp_3: ref;
  var temp_4: ref;
  var temp_5: ref;
  var temp_6: ref;
  var temp_7: ref;
  var local1: ref where detachable(Heap, local1, ACCOUNT);
  var local2: ref where detachable(Heap, local2, ACCOUNT);
  var local3: ref where detachable(Heap, local3, PROCEDURE);
  var local4: ref where detachable(Heap, local4, PROCEDURE);
  var local5: ref where detachable(Heap, local5, PROCEDURE);

  init_locals:
  temp_3 := Void;
  temp_4 := Void;
  temp_5 := Void;
  temp_6 := Void;
  temp_7 := Void;
  local1 := Void;
  local2 := Void;
  local3 := Void;
  local4 := Void;
  local5 := Void;

  entry:
  assume {:captureState "ACCOUNT_CLIENT.test_agents"} true;
  call unwrap(Current); // default:wrapping cid:1 rid:57 line:5
  assume ACCOUNT_CLIENT.user_inv(Heap, Current);
  // /home/caf/temp/comcom/repo-closures/account_client.e:10
  // create a1.make
  call temp_3 := allocate(ACCOUNT); // line:-1
  call create.ACCOUNT.make(temp_3); // line:10 cid:410 rid:5405
  local1 := temp_3;
  // /home/caf/temp/comcom/repo-closures/account_client.e:11
  // create a2.make
  call temp_4 := allocate(ACCOUNT); // line:-1
  call create.ACCOUNT.make(temp_4); // line:11 cid:410 rid:5405
  local2 := temp_4;
  // /home/caf/temp/comcom/repo-closures/account_client.e:13
  // p1 := agent a1.deposit (100)
  call temp_5 := allocate(PROCEDURE);
  call create.routine(temp_5);
  assume (forall h: HeapType :: (routine.precondition_0(h, temp_5)) == (pre.fun.ACCOUNT.deposit(h, local1, 100)));
  assume (forall h: HeapType, old_h: HeapType :: (routine.postcondition_0(h, old_h, temp_5)) == (post.ACCOUNT.deposit(h, old_h, local1, 100)));
  assume (forall h: HeapType :: (routine.modify_0(h, temp_5)) == (modify.ACCOUNT.deposit(h, local1, 100)));
  local3 := temp_5;
  // /home/caf/temp/comcom/repo-closures/account_client.e:14
  // p2 := agent a1.withdraw (40)
  call temp_6 := allocate(PROCEDURE);
  call create.routine(temp_6);
  assume (forall h: HeapType :: (routine.precondition_0(h, temp_6)) == (pre.fun.ACCOUNT.withdraw(h, local1, 40)));
  assume (forall h: HeapType, old_h: HeapType :: (routine.postcondition_0(h, old_h, temp_6)) == (post.ACCOUNT.withdraw(h, old_h, local1, 40)));
  assume (forall h: HeapType :: (routine.modify_0(h, temp_6)) == (modify.ACCOUNT.withdraw(h, local1, 40)));
  local4 := temp_6;
  // /home/caf/temp/comcom/repo-closures/account_client.e:15
  // p3 := agent a1.transfer (20, a2)
  call temp_7 := allocate(PROCEDURE);
  call create.routine(temp_7);
  assume (forall h: HeapType :: (routine.precondition_0(h, temp_7)) == (pre.fun.ACCOUNT.transfer(h, local1, 20, local2)));
  assume (forall h: HeapType, old_h: HeapType :: (routine.postcondition_0(h, old_h, temp_7)) == (post.ACCOUNT.transfer(h, old_h, local1, 20, local2)));
  assume (forall h: HeapType :: (routine.modify_0(h, temp_7)) == (modify.ACCOUNT.transfer(h, local1, 20, local2)));
  local5 := temp_7;
  // /home/caf/temp/comcom/repo-closures/account_client.e:17
  // p1.call ([])
  assert {:subsumption 0} (local3) != (Void); // type:attached line:17
  call routine.call_0(local3); // line:17 cid:7 rid:4813
  // /home/caf/temp/comcom/repo-closures/account_client.e:18
  // p3.call ([])
  assert {:subsumption 0} (local5) != (Void); // type:attached line:18
  call routine.call_0(local5); // line:18 cid:7 rid:4813
  // /home/caf/temp/comcom/repo-closures/account_client.e:19
  // p2.call ([])
  assert {:subsumption 0} (local4) != (Void); // type:attached line:19
  call routine.call_0(local4); // line:19 cid:7 rid:4813
  // /home/caf/temp/comcom/repo-closures/account_client.e:20
  // p3.call ([])
  assert {:subsumption 0} (local5) != (Void); // type:attached line:20
  call routine.call_0(local5); // line:20 cid:7 rid:4813
  // /home/caf/temp/comcom/repo-closures/account_client.e:22
  // check a1.balance = 20 end
  assert {:subsumption 0} (local1) != (Void); // type:attached line:22
  assert (Heap[local1, ACCOUNT.balance]) == (20); // type:check line:22
  // /home/caf/temp/comcom/repo-closures/account_client.e:23
  // check a2.balance = 40 end
  assert {:subsumption 0} (local2) != (Void); // type:attached line:23
  assert (Heap[local2, ACCOUNT.balance]) == (40); // type:check line:23
  if (*) {
    assert Set#IsEmpty(Heap[Current, observers]); // type:inv tag:default_observers line:26 cid:1 rid:55
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

const unique CLIENT: Type;

axiom ((CLIENT) <: (ANY));

axiom ((forall t: Type :: { (CLIENT) <: (t) } ((CLIENT) <: (t)) <==> (((t) == (CLIENT)) || ((ANY) <: (t)))));

axiom ((FieldId(allocated, CLIENT)) == (-1));

axiom ((FieldId(closed, CLIENT)) == (-2));

axiom ((FieldId(owner, CLIENT)) == (-3));

axiom ((FieldId(owns, CLIENT)) == (-4));

axiom ((FieldId(observers, CLIENT)) == (-5));

axiom ((FieldId(subjects, CLIENT)) == (-6));

axiom ((forall <T11> $f: Field T11 :: { IsModelField($f, CLIENT) } (IsModelField($f, CLIENT)) <==> ((($f) == (subjects)) || (($f) == (observers)))));

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
  requires (forall <T12> $f: Field T12 :: (($f) != (allocated)) ==> ((Heap[Current, $f]) == (Default($f))));
  ensures (forall <T13> $f: Field T13 :: ((($f) != (allocated)) && (($f) != (closed))) ==> ((Heap[Current, $f]) == (Default($f))));
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
    assert Set#IsEmpty(Heap[Current, observers]); // type:inv tag:default_observers line:364 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, subjects]); // type:inv tag:default_subjects line:364 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, owns]); // type:inv tag:default_owns line:364 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert admissibility2(Heap, Current); // type:inv tag:A2 line:364 cid:1 rid:55
    assume false;
  }
  call wrap(Current); // default:wrapping cid:1 rid:55 line:364
}

procedure CLIENT.log(Current: ref, log_file: ref, data: ref);
  free requires attached_exact(Heap, Current, CLIENT); // info:type property for argument Current
  free requires detachable(Heap, log_file, PROCEDURE); // info:type property for argument log_file
  free requires Heap[data, allocated]; // info:type property for argument data
  modifies Heap;
  requires (log_file) != (Void); // type:pre tag:log_file_not_void line:9
  requires (data) != (Void); // type:pre tag:data_not_void line:10
  requires (data) != (Current); // type:pre tag:data_not_current line:11
  requires routine.precondition_1(Heap, log_file, data); // type:pre tag:log_file_valid line:12
  ensures (log_file) != (Void); // type:attached tag:log_file_called line:18
  ensures routine.postcondition_1(Heap, old(Heap), log_file, data); // type:post tag:log_file_called line:18
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.CLIENT.log(Heap, Current, log_file, data), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.CLIENT.log(old(Heap), Current, log_file, data));
  free ensures HeapSucc(old(Heap), Heap);
  requires Frame#Subset(routine.modify_1(Heap, log_file, data), writable); // type:pre tag:agent_modifies_writable



function { :inline } variant.CLIENT.log.1(heap: HeapType, current: ref, log_file: ref, data: ref) returns (ref) {
  log_file
}

function { :inline } variant.CLIENT.log.2(heap: HeapType, current: ref, log_file: ref, data: ref) returns (ref) {
  data
}

implementation CLIENT.log(Current: ref, log_file: ref, data: ref)
{
  entry:
  assume {:captureState "CLIENT.log"} true;
  // /home/caf/temp/comcom/repo-closures/client.e:16
  // log_file.call ([data])
  assert {:subsumption 0} (log_file) != (Void); // type:attached line:16
  call routine.call_1(log_file, data); // line:16 cid:7 rid:4813
}

const unique PARAGRAPH: Type;

axiom ((PARAGRAPH) <: (ANY));

axiom ((forall t: Type :: { (PARAGRAPH) <: (t) } ((PARAGRAPH) <: (t)) <==> (((t) == (PARAGRAPH)) || ((ANY) <: (t)))));

axiom ((FieldId(allocated, PARAGRAPH)) == (-1));

axiom ((FieldId(closed, PARAGRAPH)) == (-2));

axiom ((FieldId(owner, PARAGRAPH)) == (-3));

axiom ((FieldId(owns, PARAGRAPH)) == (-4));

axiom ((FieldId(observers, PARAGRAPH)) == (-5));

axiom ((FieldId(subjects, PARAGRAPH)) == (-6));

axiom ((forall <T14> $f: Field T14 :: { IsModelField($f, PARAGRAPH) } (IsModelField($f, PARAGRAPH)) <==> ((($f) == (subjects)) || (($f) == (observers)))));

function { :inline } PARAGRAPH.user_inv(heap: HeapType, current: ref) returns (bool) {
  (Set#IsEmpty(heap[current, observers])) && (Set#IsEmpty(heap[current, subjects])) && (Set#IsEmpty(heap[current, owns])) && (admissibility2(heap, current))
}

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached_exact(heap, current, PARAGRAPH)) ==> ((user_inv(heap, current)) <==> (PARAGRAPH.user_inv(heap, current)))));

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached(heap, current, PARAGRAPH)) ==> ((user_inv(heap, current)) ==> (PARAGRAPH.user_inv(heap, current)))));

procedure PARAGRAPH.invariant_admissibility_check(Current: ref);
  requires attached_exact(Heap, Current, PARAGRAPH);



implementation PARAGRAPH.invariant_admissibility_check(Current: ref)
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

procedure create.PARAGRAPH.default_create(Current: ref);
  free requires attached_exact(Heap, Current, PARAGRAPH); // info:type property for argument Current
  modifies Heap;
  requires (forall <T15> $f: Field T15 :: (($f) != (allocated)) ==> ((Heap[Current, $f]) == (Default($f))));
  ensures (forall <T16> $f: Field T16 :: ((($f) != (allocated)) && (($f) != (closed))) ==> ((Heap[Current, $f]) == (Default($f))));
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.PARAGRAPH.default_create(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.PARAGRAPH.default_create(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts



implementation create.PARAGRAPH.default_create(Current: ref)
{
  entry:
  assume {:captureState "create.PARAGRAPH.default_create"} true;
  if (*) {
    assert Set#IsEmpty(Heap[Current, observers]); // type:inv tag:default_observers line:25 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, subjects]); // type:inv tag:default_subjects line:25 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, owns]); // type:inv tag:default_owns line:25 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert admissibility2(Heap, Current); // type:inv tag:A2 line:25 cid:1 rid:55
    assume false;
  }
  call wrap(Current); // default:wrapping cid:1 rid:55 line:364
}

procedure PARAGRAPH.align_left(Current: ref);
  free requires attached_exact(Heap, Current, PARAGRAPH); // info:type property for argument Current
  modifies Heap;
  ensures Heap[Current, PARAGRAPH.is_left_aligned]; // type:post line:16
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.PARAGRAPH.align_left(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.PARAGRAPH.align_left(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);
  requires is_wrapped(Heap, Current); // type:pre tag:default_is_wrapped default:contracts
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts



function { :inline } variant.PARAGRAPH.align_left.1(heap: HeapType, current: ref) returns (int) {
  0
}

implementation PARAGRAPH.align_left(Current: ref)
{
  entry:
  assume {:captureState "PARAGRAPH.align_left"} true;
  call unwrap(Current); // default:wrapping cid:1 rid:57 line:11
  assume PARAGRAPH.user_inv(Heap, Current);
  // /home/caf/temp/comcom/repo-closures/paragraph.e:14
  // is_left_aligned := True
  call update_heap(Current, PARAGRAPH.is_left_aligned, true); // line:14
  if (*) {
    assert Set#IsEmpty(Heap[Current, observers]); // type:inv tag:default_observers line:25 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, subjects]); // type:inv tag:default_subjects line:25 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, owns]); // type:inv tag:default_owns line:25 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert admissibility2(Heap, Current); // type:inv tag:A2 line:25 cid:1 rid:55
    assume false;
  }
  call wrap(Current); // default:wrapping cid:1 rid:55 line:17
}

procedure PARAGRAPH.align_right(Current: ref);
  free requires attached_exact(Heap, Current, PARAGRAPH); // info:type property for argument Current
  modifies Heap;
  ensures !(Heap[Current, PARAGRAPH.is_left_aligned]); // type:post line:24
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.PARAGRAPH.align_right(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.PARAGRAPH.align_right(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);
  requires is_wrapped(Heap, Current); // type:pre tag:default_is_wrapped default:contracts
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts



function { :inline } variant.PARAGRAPH.align_right.1(heap: HeapType, current: ref) returns (int) {
  0
}

implementation PARAGRAPH.align_right(Current: ref)
{
  entry:
  assume {:captureState "PARAGRAPH.align_right"} true;
  call unwrap(Current); // default:wrapping cid:1 rid:57 line:19
  assume PARAGRAPH.user_inv(Heap, Current);
  // /home/caf/temp/comcom/repo-closures/paragraph.e:22
  // is_left_aligned := False
  call update_heap(Current, PARAGRAPH.is_left_aligned, false); // line:22
  if (*) {
    assert Set#IsEmpty(Heap[Current, observers]); // type:inv tag:default_observers line:25 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, subjects]); // type:inv tag:default_subjects line:25 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, owns]); // type:inv tag:default_owns line:25 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert admissibility2(Heap, Current); // type:inv tag:A2 line:25 cid:1 rid:55
    assume false;
  }
  call wrap(Current); // default:wrapping cid:1 rid:55 line:25
}

procedure PARAGRAPH.format(Current: ref, proc: ref);
  free requires attached_exact(Heap, Current, PARAGRAPH); // info:type property for argument Current
  free requires detachable(Heap, proc, PROCEDURE); // info:type property for argument proc
  modifies Heap;
  requires (proc) != (Void); // type:attached tag:pre line:32
  requires routine.precondition_1(Heap, proc, Current); // type:pre tag:pre line:32
  ensures (proc) != (Void); // type:attached line:38
  ensures routine.postcondition_1(Heap, old(Heap), proc, Current); // type:post line:38
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.PARAGRAPH.format(Heap, Current, proc), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.PARAGRAPH.format(old(Heap), Current, proc));
  free ensures HeapSucc(old(Heap), Heap);
  requires Frame#Subset(routine.modify_1(Heap, proc, Current), writable); // type:pre tag:agent_modifies_writable



function { :inline } variant.PARAGRAPH.format.1(heap: HeapType, current: ref, proc: ref) returns (ref) {
  proc
}

implementation PARAGRAPH.format(Current: ref, proc: ref)
{
  entry:
  assume {:captureState "PARAGRAPH.format"} true;
  // /home/caf/temp/comcom/repo-closures/paragraph.e:36
  // proc.call ([Current])
  assert {:subsumption 0} (proc) != (Void); // type:attached line:36
  call routine.call_1(proc, Current); // line:36 cid:7 rid:4813
}

const unique ARCHIVER_APPLICATION: Type;

axiom ((ARCHIVER_APPLICATION) <: (ANY));

axiom ((forall t: Type :: { (ARCHIVER_APPLICATION) <: (t) } ((ARCHIVER_APPLICATION) <: (t)) <==> (((t) == (ARCHIVER_APPLICATION)) || ((ANY) <: (t)))));

axiom ((FieldId(allocated, ARCHIVER_APPLICATION)) == (-1));

axiom ((FieldId(closed, ARCHIVER_APPLICATION)) == (-2));

axiom ((FieldId(owner, ARCHIVER_APPLICATION)) == (-3));

axiom ((FieldId(owns, ARCHIVER_APPLICATION)) == (-4));

axiom ((FieldId(observers, ARCHIVER_APPLICATION)) == (-5));

axiom ((FieldId(subjects, ARCHIVER_APPLICATION)) == (-6));

axiom ((forall <T17> $f: Field T17 :: { IsModelField($f, ARCHIVER_APPLICATION) } (IsModelField($f, ARCHIVER_APPLICATION)) <==> ((($f) == (subjects)) || (($f) == (observers)))));

function { :inline } ARCHIVER_APPLICATION.user_inv(heap: HeapType, current: ref) returns (bool) {
  (Set#IsEmpty(heap[current, observers])) && (Set#IsEmpty(heap[current, subjects])) && (Set#IsEmpty(heap[current, owns])) && (admissibility2(heap, current))
}

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached_exact(heap, current, ARCHIVER_APPLICATION)) ==> ((user_inv(heap, current)) <==> (ARCHIVER_APPLICATION.user_inv(heap, current)))));

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached(heap, current, ARCHIVER_APPLICATION)) ==> ((user_inv(heap, current)) ==> (ARCHIVER_APPLICATION.user_inv(heap, current)))));

procedure ARCHIVER_APPLICATION.invariant_admissibility_check(Current: ref);
  requires attached_exact(Heap, Current, ARCHIVER_APPLICATION);



implementation ARCHIVER_APPLICATION.invariant_admissibility_check(Current: ref)
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

procedure create.ARCHIVER_APPLICATION.default_create(Current: ref);
  free requires attached_exact(Heap, Current, ARCHIVER_APPLICATION); // info:type property for argument Current
  modifies Heap;
  requires (forall <T18> $f: Field T18 :: (($f) != (allocated)) ==> ((Heap[Current, $f]) == (Default($f))));
  ensures (forall <T19> $f: Field T19 :: ((($f) != (allocated)) && (($f) != (closed))) ==> ((Heap[Current, $f]) == (Default($f))));
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.ARCHIVER_APPLICATION.default_create(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.ARCHIVER_APPLICATION.default_create(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts



implementation create.ARCHIVER_APPLICATION.default_create(Current: ref)
{
  entry:
  assume {:captureState "create.ARCHIVER_APPLICATION.default_create"} true;
  if (*) {
    assert Set#IsEmpty(Heap[Current, observers]); // type:inv tag:default_observers line:364 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, subjects]); // type:inv tag:default_subjects line:364 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, owns]); // type:inv tag:default_owns line:364 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert admissibility2(Heap, Current); // type:inv tag:A2 line:364 cid:1 rid:55
    assume false;
  }
  call wrap(Current); // default:wrapping cid:1 rid:55 line:364
}

procedure ARCHIVER_APPLICATION.run(Current: ref, c: ref, data: ref);
  free requires attached_exact(Heap, Current, ARCHIVER_APPLICATION); // info:type property for argument Current
  free requires detachable(Heap, c, CLIENT); // info:type property for argument c
  free requires Heap[data, allocated]; // info:type property for argument data
  modifies Heap;
  requires (c) != (Void); // type:attached line:10
  requires is_wrapped(Heap, c); // type:pre line:10
  requires (data) != (Void); // type:attached line:11
  requires is_wrapped(Heap, data); // type:pre line:11
  requires (c) != (data); // type:pre line:12
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.ARCHIVER_APPLICATION.run(Heap, Current, c, data), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.ARCHIVER_APPLICATION.run(old(Heap), Current, c, data));
  free ensures HeapSucc(old(Heap), Heap);



function { :inline } variant.ARCHIVER_APPLICATION.run.1(heap: HeapType, current: ref, c: ref, data: ref) returns (ref) {
  c
}

function { :inline } variant.ARCHIVER_APPLICATION.run.2(heap: HeapType, current: ref, c: ref, data: ref) returns (ref) {
  data
}

implementation ARCHIVER_APPLICATION.run(Current: ref, c: ref, data: ref)
{
  var temp_8: ref;
  var temp_9: ref;
  var local1: ref where detachable(Heap, local1, TAPE_ARCHIVE);

  init_locals:
  temp_8 := Void;
  temp_9 := Void;
  local1 := Void;

  entry:
  assume {:captureState "ARCHIVER_APPLICATION.run"} true;
  // /home/caf/temp/comcom/repo-closures/archiver_application.e:18
  // create archive.make
  call temp_8 := allocate(TAPE_ARCHIVE); // line:-1
  call create.TAPE_ARCHIVE.make(temp_8); // line:18 cid:407 rid:5412
  local1 := temp_8;
  // /home/caf/temp/comcom/repo-closures/archiver_application.e:20
  // c.log (agent archive.store, data)
  assert {:subsumption 0} (c) != (Void); // type:attached line:20
  call temp_9 := allocate(PROCEDURE);
  call create.routine(temp_9);
  assume (forall h: HeapType, oarg_1: ref :: (routine.precondition_1(h, temp_9, oarg_1)) == (pre.fun.TAPE_ARCHIVE.store(h, local1, oarg_1)));
  assume (forall h: HeapType, old_h: HeapType, oarg_1: ref :: (routine.postcondition_1(h, old_h, temp_9, oarg_1)) == (post.TAPE_ARCHIVE.store(h, old_h, local1, oarg_1)));
  assume (forall h: HeapType, oarg_1: ref :: (routine.modify_1(h, temp_9, oarg_1)) == (modify.TAPE_ARCHIVE.store(h, local1, oarg_1)));
  call CLIENT.log(c, temp_9, data); // line:20 cid:409 rid:5410
}

const unique FORMATTER: Type;

axiom ((FORMATTER) <: (ANY));

axiom ((forall t: Type :: { (FORMATTER) <: (t) } ((FORMATTER) <: (t)) <==> (((t) == (FORMATTER)) || ((ANY) <: (t)))));

axiom ((FieldId(allocated, FORMATTER)) == (-1));

axiom ((FieldId(closed, FORMATTER)) == (-2));

axiom ((FieldId(owner, FORMATTER)) == (-3));

axiom ((FieldId(owns, FORMATTER)) == (-4));

axiom ((FieldId(observers, FORMATTER)) == (-5));

axiom ((FieldId(subjects, FORMATTER)) == (-6));

axiom ((forall <T20> $f: Field T20 :: { IsModelField($f, FORMATTER) } (IsModelField($f, FORMATTER)) <==> ((($f) == (subjects)) || (($f) == (observers)))));

function { :inline } FORMATTER.user_inv(heap: HeapType, current: ref) returns (bool) {
  (Set#IsEmpty(heap[current, observers])) && (Set#IsEmpty(heap[current, subjects])) && (Set#IsEmpty(heap[current, owns])) && (admissibility2(heap, current))
}

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached_exact(heap, current, FORMATTER)) ==> ((user_inv(heap, current)) <==> (FORMATTER.user_inv(heap, current)))));

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached(heap, current, FORMATTER)) ==> ((user_inv(heap, current)) ==> (FORMATTER.user_inv(heap, current)))));

procedure FORMATTER.invariant_admissibility_check(Current: ref);
  requires attached_exact(Heap, Current, FORMATTER);



implementation FORMATTER.invariant_admissibility_check(Current: ref)
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

procedure create.FORMATTER.default_create(Current: ref);
  free requires attached_exact(Heap, Current, FORMATTER); // info:type property for argument Current
  modifies Heap;
  requires (forall <T21> $f: Field T21 :: (($f) != (allocated)) ==> ((Heap[Current, $f]) == (Default($f))));
  ensures (forall <T22> $f: Field T22 :: ((($f) != (allocated)) && (($f) != (closed))) ==> ((Heap[Current, $f]) == (Default($f))));
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.FORMATTER.default_create(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.FORMATTER.default_create(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts



implementation create.FORMATTER.default_create(Current: ref)
{
  entry:
  assume {:captureState "create.FORMATTER.default_create"} true;
  if (*) {
    assert Set#IsEmpty(Heap[Current, observers]); // type:inv tag:default_observers line:364 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, subjects]); // type:inv tag:default_subjects line:364 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, owns]); // type:inv tag:default_owns line:364 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert admissibility2(Heap, Current); // type:inv tag:A2 line:364 cid:1 rid:55
    assume false;
  }
  call wrap(Current); // default:wrapping cid:1 rid:55 line:364
}

procedure FORMATTER.align_left(Current: ref, a_paragraph: ref);
  free requires attached_exact(Heap, Current, FORMATTER); // info:type property for argument Current
  free requires detachable(Heap, a_paragraph, PARAGRAPH); // info:type property for argument a_paragraph
  modifies Heap;
  requires (a_paragraph) != (Void); // type:pre line:10
  requires !(Heap[a_paragraph, PARAGRAPH.is_left_aligned]); // type:pre tag:not_left_aligned line:11
  ensures (a_paragraph) != (Void); // type:attached tag:is_left_aligned line:17
  ensures Heap[a_paragraph, PARAGRAPH.is_left_aligned]; // type:post tag:is_left_aligned line:17
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.FORMATTER.align_left(Heap, Current, a_paragraph), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.FORMATTER.align_left(old(Heap), Current, a_paragraph));
  free ensures HeapSucc(old(Heap), Heap);
  requires is_wrapped(Heap, Current); // type:pre tag:default_is_wrapped default:contracts
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts
  requires is_wrapped(Heap, a_paragraph); // type:pre tag:arg_a_paragraph_is_wrapped default:contracts
  ensures is_wrapped(Heap, a_paragraph); // type:post tag:arg_a_paragraph_is_wrapped default:contracts



function { :inline } variant.FORMATTER.align_left.1(heap: HeapType, current: ref, a_paragraph: ref) returns (ref) {
  a_paragraph
}

implementation FORMATTER.align_left(Current: ref, a_paragraph: ref)
{
  entry:
  assume {:captureState "FORMATTER.align_left"} true;
  // /home/caf/temp/comcom/repo-closures/formatter.e:15
  // a_paragraph.align_left
  assert {:subsumption 0} (a_paragraph) != (Void); // type:attached line:15
  call PARAGRAPH.align_left(a_paragraph); // line:15 cid:405 rid:5419
}

procedure FORMATTER.align_right(Current: ref, a_paragraph: ref);
  free requires attached_exact(Heap, Current, FORMATTER); // info:type property for argument Current
  free requires detachable(Heap, a_paragraph, PARAGRAPH); // info:type property for argument a_paragraph
  modifies Heap;
  requires (a_paragraph) != (Void); // type:pre line:25
  requires Heap[a_paragraph, PARAGRAPH.is_left_aligned]; // type:pre tag:left_aligned line:26
  ensures (a_paragraph) != (Void); // type:attached tag:not_is_left_aligned line:32
  ensures !(Heap[a_paragraph, PARAGRAPH.is_left_aligned]); // type:post tag:not_is_left_aligned line:32
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.FORMATTER.align_right(Heap, Current, a_paragraph), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.FORMATTER.align_right(old(Heap), Current, a_paragraph));
  free ensures HeapSucc(old(Heap), Heap);
  requires is_wrapped(Heap, Current); // type:pre tag:default_is_wrapped default:contracts
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts
  requires is_wrapped(Heap, a_paragraph); // type:pre tag:arg_a_paragraph_is_wrapped default:contracts
  ensures is_wrapped(Heap, a_paragraph); // type:post tag:arg_a_paragraph_is_wrapped default:contracts



function { :inline } variant.FORMATTER.align_right.1(heap: HeapType, current: ref, a_paragraph: ref) returns (ref) {
  a_paragraph
}

implementation FORMATTER.align_right(Current: ref, a_paragraph: ref)
{
  entry:
  assume {:captureState "FORMATTER.align_right"} true;
  // /home/caf/temp/comcom/repo-closures/formatter.e:30
  // a_paragraph.align_right
  assert {:subsumption 0} (a_paragraph) != (Void); // type:attached line:30
  call PARAGRAPH.align_right(a_paragraph); // line:30 cid:405 rid:5420
}

const unique ACCOUNT: Type;

axiom ((ACCOUNT) <: (ANY));

axiom ((forall t: Type :: { (ACCOUNT) <: (t) } ((ACCOUNT) <: (t)) <==> (((t) == (ACCOUNT)) || ((ANY) <: (t)))));

axiom ((FieldId(allocated, ACCOUNT)) == (-1));

axiom ((FieldId(closed, ACCOUNT)) == (-2));

axiom ((FieldId(owner, ACCOUNT)) == (-3));

axiom ((FieldId(owns, ACCOUNT)) == (-4));

axiom ((FieldId(observers, ACCOUNT)) == (-5));

axiom ((FieldId(subjects, ACCOUNT)) == (-6));

axiom ((forall <T23> $f: Field T23 :: { IsModelField($f, ACCOUNT) } (IsModelField($f, ACCOUNT)) <==> ((($f) == (subjects)) || (($f) == (observers)))));

function { :inline } ACCOUNT.user_inv(heap: HeapType, current: ref) returns (bool) {
  ((heap[current, ACCOUNT.balance]) >= (0)) && (Set#IsEmpty(heap[current, observers])) && (Set#IsEmpty(heap[current, subjects])) && (Set#IsEmpty(heap[current, owns])) && (admissibility2(heap, current))
}

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached_exact(heap, current, ACCOUNT)) ==> ((user_inv(heap, current)) <==> (ACCOUNT.user_inv(heap, current)))));

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached(heap, current, ACCOUNT)) ==> ((user_inv(heap, current)) ==> (ACCOUNT.user_inv(heap, current)))));

procedure ACCOUNT.invariant_admissibility_check(Current: ref);
  requires attached_exact(Heap, Current, ACCOUNT);



implementation ACCOUNT.invariant_admissibility_check(Current: ref)
{
  entry:
  goto pre, a2, a3;
  pre:
  assert user_inv_readable(Heap, Current)[Current, ACCOUNT.balance]; // type:access tag:attribute_readable line:63 cid:410 fid:81
  assume (Heap[Current, ACCOUNT.balance]) >= (0);
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

procedure create.ACCOUNT.make(Current: ref);
  free requires attached_exact(Heap, Current, ACCOUNT); // info:type property for argument Current
  modifies Heap;
  ensures (Heap[Current, ACCOUNT.balance]) == (0); // type:post tag:balance_set line:13
  requires (forall <T24> $f: Field T24 :: (($f) != (allocated)) ==> ((Heap[Current, $f]) == (Default($f))));
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.ACCOUNT.make(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.ACCOUNT.make(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts



implementation create.ACCOUNT.make(Current: ref)
{
  entry:
  assume {:captureState "create.ACCOUNT.make"} true;
  // /home/caf/temp/comcom/repo-closures/account.e:11
  // balance := 0
  call update_heap(Current, ACCOUNT.balance, 0); // line:11
  if (*) {
    assert (Heap[Current, ACCOUNT.balance]) >= (0); // type:inv line:41 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, observers]); // type:inv tag:default_observers line:41 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, subjects]); // type:inv tag:default_subjects line:41 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, owns]); // type:inv tag:default_owns line:41 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert admissibility2(Heap, Current); // type:inv tag:A2 line:41 cid:1 rid:55
    assume false;
  }
  call wrap(Current); // default:wrapping cid:1 rid:55 line:14
}

procedure ACCOUNT.make(Current: ref);
  free requires attached_exact(Heap, Current, ACCOUNT); // info:type property for argument Current
  modifies Heap;
  ensures (Heap[Current, ACCOUNT.balance]) == (0); // type:post tag:balance_set line:13
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.ACCOUNT.make(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.ACCOUNT.make(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);
  requires is_wrapped(Heap, Current); // type:pre tag:default_is_wrapped default:contracts
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts



function { :inline } variant.ACCOUNT.make.1(heap: HeapType, current: ref) returns (int) {
  0
}

implementation ACCOUNT.make(Current: ref)
{
  entry:
  assume {:captureState "ACCOUNT.make"} true;
  call unwrap(Current); // default:wrapping cid:1 rid:57 line:8
  assume ACCOUNT.user_inv(Heap, Current);
  // /home/caf/temp/comcom/repo-closures/account.e:11
  // balance := 0
  call update_heap(Current, ACCOUNT.balance, 0); // line:11
  if (*) {
    assert (Heap[Current, ACCOUNT.balance]) >= (0); // type:inv line:41 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, observers]); // type:inv tag:default_observers line:41 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, subjects]); // type:inv tag:default_subjects line:41 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, owns]); // type:inv tag:default_owns line:41 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert admissibility2(Heap, Current); // type:inv tag:A2 line:41 cid:1 rid:55
    assume false;
  }
  call wrap(Current); // default:wrapping cid:1 rid:55 line:14
}

procedure ACCOUNT.deposit(Current: ref, amount: int);
  free requires attached_exact(Heap, Current, ACCOUNT); // info:type property for argument Current
  free requires is_integer_32(amount); // info:type property for argument amount
  modifies Heap;
  requires (amount) >= (0); // type:pre tag:amount_not_negative line:26
  ensures (Heap[Current, ACCOUNT.balance]) == ((old(Heap)[Current, ACCOUNT.balance]) + (amount)); // type:post tag:balance_increased line:30
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.ACCOUNT.deposit(Heap, Current, amount), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.ACCOUNT.deposit(old(Heap), Current, amount));
  free ensures HeapSucc(old(Heap), Heap);
  requires is_wrapped(Heap, Current); // type:pre tag:default_is_wrapped default:contracts
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts



function { :inline } variant.ACCOUNT.deposit.1(heap: HeapType, current: ref, amount: int) returns (int) {
  amount
}

implementation ACCOUNT.deposit(Current: ref, amount: int)
{
  entry:
  assume {:captureState "ACCOUNT.deposit"} true;
  call unwrap(Current); // default:wrapping cid:1 rid:57 line:23
  assume ACCOUNT.user_inv(Heap, Current);
  // /home/caf/temp/comcom/repo-closures/account.e:28
  // balance := balance + amount
  call update_heap(Current, ACCOUNT.balance, (Heap[Current, ACCOUNT.balance]) + (amount)); // line:28
  if (*) {
    assert (Heap[Current, ACCOUNT.balance]) >= (0); // type:inv line:41 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, observers]); // type:inv tag:default_observers line:41 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, subjects]); // type:inv tag:default_subjects line:41 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, owns]); // type:inv tag:default_owns line:41 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert admissibility2(Heap, Current); // type:inv tag:A2 line:41 cid:1 rid:55
    assume false;
  }
  call wrap(Current); // default:wrapping cid:1 rid:55 line:31
}

procedure ACCOUNT.withdraw(Current: ref, amount: int);
  free requires attached_exact(Heap, Current, ACCOUNT); // info:type property for argument Current
  free requires is_integer_32(amount); // info:type property for argument amount
  modifies Heap;
  requires (amount) <= (Heap[Current, ACCOUNT.balance]); // type:pre tag:amount_not_too_large line:36
  ensures (Heap[Current, ACCOUNT.balance]) == ((old(Heap)[Current, ACCOUNT.balance]) - (amount)); // type:post tag:balance_decreased line:40
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.ACCOUNT.withdraw(Heap, Current, amount), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.ACCOUNT.withdraw(old(Heap), Current, amount));
  free ensures HeapSucc(old(Heap), Heap);
  requires is_wrapped(Heap, Current); // type:pre tag:default_is_wrapped default:contracts
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts



function { :inline } variant.ACCOUNT.withdraw.1(heap: HeapType, current: ref, amount: int) returns (int) {
  amount
}

implementation ACCOUNT.withdraw(Current: ref, amount: int)
{
  entry:
  assume {:captureState "ACCOUNT.withdraw"} true;
  call unwrap(Current); // default:wrapping cid:1 rid:57 line:33
  assume ACCOUNT.user_inv(Heap, Current);
  // /home/caf/temp/comcom/repo-closures/account.e:38
  // balance := balance - amount
  call update_heap(Current, ACCOUNT.balance, (Heap[Current, ACCOUNT.balance]) - (amount)); // line:38
  if (*) {
    assert (Heap[Current, ACCOUNT.balance]) >= (0); // type:inv line:41 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, observers]); // type:inv tag:default_observers line:41 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, subjects]); // type:inv tag:default_subjects line:41 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, owns]); // type:inv tag:default_owns line:41 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert admissibility2(Heap, Current); // type:inv tag:A2 line:41 cid:1 rid:55
    assume false;
  }
  call wrap(Current); // default:wrapping cid:1 rid:55 line:41
}

procedure ACCOUNT.transfer(Current: ref, amount: int, other: ref);
  free requires attached_exact(Heap, Current, ACCOUNT); // info:type property for argument Current
  free requires is_integer_32(amount); // info:type property for argument amount
  free requires detachable(Heap, other, ACCOUNT); // info:type property for argument other
  modifies Heap;
  requires (other) != (Void); // type:pre tag:other_not_void line:48
  requires (other) != (Current); // type:pre tag:other_not_current line:49
  requires (amount) >= (0); // type:pre tag:amount_not_negative line:50
  requires (amount) <= (Heap[Current, ACCOUNT.balance]); // type:pre tag:amount_not_too_large line:51
  ensures (Heap[Current, ACCOUNT.balance]) == ((old(Heap)[Current, ACCOUNT.balance]) - (amount)); // type:post tag:balance_decreased line:58
  ensures (other) != (Void); // type:attached tag:other_balance_increased line:59
  ensures (Heap[other, ACCOUNT.balance]) == ((old(Heap)[other, ACCOUNT.balance]) + (amount)); // type:post tag:other_balance_increased line:59
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.ACCOUNT.transfer(Heap, Current, amount, other), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.ACCOUNT.transfer(old(Heap), Current, amount, other));
  free ensures HeapSucc(old(Heap), Heap);
  requires is_wrapped(Heap, Current); // type:pre tag:default_is_wrapped default:contracts
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts
  requires is_wrapped(Heap, other); // type:pre tag:arg_other_is_wrapped default:contracts
  ensures is_wrapped(Heap, other); // type:post tag:arg_other_is_wrapped default:contracts



function { :inline } variant.ACCOUNT.transfer.1(heap: HeapType, current: ref, amount: int, other: ref) returns (int) {
  amount
}

function { :inline } variant.ACCOUNT.transfer.2(heap: HeapType, current: ref, amount: int, other: ref) returns (ref) {
  other
}

implementation ACCOUNT.transfer(Current: ref, amount: int, other: ref)
{
  entry:
  assume {:captureState "ACCOUNT.transfer"} true;
  // /home/caf/temp/comcom/repo-closures/account.e:55
  // withdraw (amount)
  call ACCOUNT.withdraw(Current, amount); // line:55 cid:410 rid:5408
  // /home/caf/temp/comcom/repo-closures/account.e:56
  // other.deposit (amount)
  assert {:subsumption 0} (other) != (Void); // type:attached line:56
  call ACCOUNT.deposit(other, amount); // line:56 cid:410 rid:5407
}

const unique TAPE_ARCHIVE: Type;

axiom ((TAPE_ARCHIVE) <: (ANY));

axiom ((forall t: Type :: { (TAPE_ARCHIVE) <: (t) } ((TAPE_ARCHIVE) <: (t)) <==> (((t) == (TAPE_ARCHIVE)) || ((ANY) <: (t)))));

axiom ((FieldId(allocated, TAPE_ARCHIVE)) == (-1));

axiom ((FieldId(closed, TAPE_ARCHIVE)) == (-2));

axiom ((FieldId(owner, TAPE_ARCHIVE)) == (-3));

axiom ((FieldId(owns, TAPE_ARCHIVE)) == (-4));

axiom ((FieldId(observers, TAPE_ARCHIVE)) == (-5));

axiom ((FieldId(subjects, TAPE_ARCHIVE)) == (-6));

axiom ((forall <T25> $f: Field T25 :: { IsModelField($f, TAPE_ARCHIVE) } (IsModelField($f, TAPE_ARCHIVE)) <==> ((($f) == (subjects)) || (($f) == (observers)))));

function { :inline } TAPE_ARCHIVE.user_inv(heap: HeapType, current: ref) returns (bool) {
  ((heap[current, TAPE_ARCHIVE.is_loaded]) ==> (Set#Equal(heap[current, owns], Set#Singleton(heap[current, TAPE_ARCHIVE.tape])))) && ((heap[current, TAPE_ARCHIVE.is_loaded]) ==> ((heap[current, TAPE_ARCHIVE.tape]) != (Void))) && (Set#IsEmpty(heap[current, observers])) && (Set#IsEmpty(heap[current, subjects])) && (admissibility2(heap, current))
}

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached_exact(heap, current, TAPE_ARCHIVE)) ==> ((user_inv(heap, current)) <==> (TAPE_ARCHIVE.user_inv(heap, current)))));

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached(heap, current, TAPE_ARCHIVE)) ==> ((user_inv(heap, current)) ==> (TAPE_ARCHIVE.user_inv(heap, current)))));

procedure TAPE_ARCHIVE.invariant_admissibility_check(Current: ref);
  requires attached_exact(Heap, Current, TAPE_ARCHIVE);



implementation TAPE_ARCHIVE.invariant_admissibility_check(Current: ref)
{
  entry:
  goto pre, a2, a3;
  pre:
  assert user_inv_readable(Heap, Current)[Current, TAPE_ARCHIVE.is_loaded]; // type:access tag:attribute_readable line:53 cid:407 fid:82
  assert (Heap[Current, TAPE_ARCHIVE.is_loaded]) ==> (user_inv_readable(Heap, Current)[Current, TAPE_ARCHIVE.tape]); // type:access tag:attribute_readable line:53 cid:407 fid:81
  assume (Heap[Current, TAPE_ARCHIVE.is_loaded]) ==> (Set#Equal(Heap[Current, owns], Set#Singleton(Heap[Current, TAPE_ARCHIVE.tape])));
  assert user_inv_readable(Heap, Current)[Current, TAPE_ARCHIVE.is_loaded]; // type:access tag:attribute_readable line:54 cid:407 fid:82
  assert (Heap[Current, TAPE_ARCHIVE.is_loaded]) ==> (user_inv_readable(Heap, Current)[Current, TAPE_ARCHIVE.tape]); // type:access tag:attribute_readable line:54 cid:407 fid:81
  assume (Heap[Current, TAPE_ARCHIVE.is_loaded]) ==> ((Heap[Current, TAPE_ARCHIVE.tape]) != (Void));
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

procedure create.TAPE_ARCHIVE.make(Current: ref);
  free requires attached_exact(Heap, Current, TAPE_ARCHIVE); // info:type property for argument Current
  modifies Heap;
  ensures (Heap[Current, TAPE_ARCHIVE.tape]) != (Void); // type:post tag:tape_created line:17
  ensures Heap[Current, TAPE_ARCHIVE.is_loaded]; // type:post tag:loaded line:18
  requires (forall <T26> $f: Field T26 :: (($f) != (allocated)) ==> ((Heap[Current, $f]) == (Default($f))));
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.TAPE_ARCHIVE.make(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.TAPE_ARCHIVE.make(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts



implementation create.TAPE_ARCHIVE.make(Current: ref)
{
  var temp_10: ref;

  init_locals:
  temp_10 := Void;

  entry:
  assume {:captureState "create.TAPE_ARCHIVE.make"} true;
  // /home/caf/temp/comcom/repo-closures/tape_archive.e:13
  // create tape
  call temp_10 := allocate(TAPE); // line:-1
  call create.TAPE.default_create(temp_10); // line:13 cid:408 rid:35
  call update_heap(Current, TAPE_ARCHIVE.tape, temp_10); // line:13
  // /home/caf/temp/comcom/repo-closures/tape_archive.e:14
  // is_loaded := True
  call update_heap(Current, TAPE_ARCHIVE.is_loaded, true); // line:14
  // /home/caf/temp/comcom/repo-closures/tape_archive.e:15
  // set_owns ([tape])
  call update_heap(Current, owns, Set#Singleton(Heap[Current, TAPE_ARCHIVE.tape])); // line:15
  if (*) {
    assert (Heap[Current, TAPE_ARCHIVE.is_loaded]) ==> (Set#Equal(Heap[Current, owns], Set#Singleton(Heap[Current, TAPE_ARCHIVE.tape]))); // type:inv tag:owns_def line:50 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert (Heap[Current, TAPE_ARCHIVE.is_loaded]) ==> ((Heap[Current, TAPE_ARCHIVE.tape]) != (Void)); // type:inv tag:loaded line:50 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, observers]); // type:inv tag:default_observers line:50 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, subjects]); // type:inv tag:default_subjects line:50 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert admissibility2(Heap, Current); // type:inv tag:A2 line:50 cid:1 rid:55
    assume false;
  }
  call wrap(Current); // default:wrapping cid:1 rid:55 line:19
}

procedure TAPE_ARCHIVE.eject(Current: ref);
  free requires attached_exact(Heap, Current, TAPE_ARCHIVE); // info:type property for argument Current
  modifies Heap;
  ensures (Heap[Current, TAPE_ARCHIVE.tape]) == (Void); // type:post tag:tape_ejected line:38
  ensures !(Heap[Current, TAPE_ARCHIVE.is_loaded]); // type:post tag:not_loaded line:39
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.TAPE_ARCHIVE.eject(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.TAPE_ARCHIVE.eject(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);
  requires is_wrapped(Heap, Current); // type:pre tag:default_is_wrapped default:contracts
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts



function { :inline } variant.TAPE_ARCHIVE.eject.1(heap: HeapType, current: ref) returns (int) {
  0
}

implementation TAPE_ARCHIVE.eject(Current: ref)
{
  entry:
  assume {:captureState "TAPE_ARCHIVE.eject"} true;
  call unwrap(Current); // default:wrapping cid:1 rid:57 line:31
  assume TAPE_ARCHIVE.user_inv(Heap, Current);
  // /home/caf/temp/comcom/repo-closures/tape_archive.e:34
  // tape := Void
  call update_heap(Current, TAPE_ARCHIVE.tape, Void); // line:34
  // /home/caf/temp/comcom/repo-closures/tape_archive.e:35
  // is_loaded := False
  call update_heap(Current, TAPE_ARCHIVE.is_loaded, false); // line:35
  // /home/caf/temp/comcom/repo-closures/tape_archive.e:36
  // set_owns ([])
  call update_heap(Current, owns, Set#Empty()); // line:36
  if (*) {
    assert (Heap[Current, TAPE_ARCHIVE.is_loaded]) ==> (Set#Equal(Heap[Current, owns], Set#Singleton(Heap[Current, TAPE_ARCHIVE.tape]))); // type:inv tag:owns_def line:50 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert (Heap[Current, TAPE_ARCHIVE.is_loaded]) ==> ((Heap[Current, TAPE_ARCHIVE.tape]) != (Void)); // type:inv tag:loaded line:50 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, observers]); // type:inv tag:default_observers line:50 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, subjects]); // type:inv tag:default_subjects line:50 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert admissibility2(Heap, Current); // type:inv tag:A2 line:50 cid:1 rid:55
    assume false;
  }
  call wrap(Current); // default:wrapping cid:1 rid:55 line:40
}

procedure TAPE_ARCHIVE.store(Current: ref, o: ref);
  free requires attached_exact(Heap, Current, TAPE_ARCHIVE); // info:type property for argument Current
  free requires Heap[o, allocated]; // info:type property for argument o
  modifies Heap;
  requires (o) != (Void); // type:pre tag:o_not_void line:45
  requires (o) != (Current); // type:pre tag:o_not_current line:46
  requires Heap[Current, TAPE_ARCHIVE.is_loaded]; // type:pre tag:loaded line:47
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.TAPE_ARCHIVE.store(Heap, Current, o), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.TAPE_ARCHIVE.store(old(Heap), Current, o));
  free ensures HeapSucc(old(Heap), Heap);
  requires is_wrapped(Heap, Current); // type:pre tag:default_is_wrapped default:contracts
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts
  requires is_wrapped(Heap, o); // type:pre tag:arg_o_is_wrapped default:contracts
  ensures is_wrapped(Heap, o); // type:post tag:arg_o_is_wrapped default:contracts



function { :inline } variant.TAPE_ARCHIVE.store.1(heap: HeapType, current: ref, o: ref) returns (ref) {
  o
}

implementation TAPE_ARCHIVE.store(Current: ref, o: ref)
{
  entry:
  assume {:captureState "TAPE_ARCHIVE.store"} true;
  call unwrap(Current); // default:wrapping cid:1 rid:57 line:42
  assume TAPE_ARCHIVE.user_inv(Heap, Current);
  // /home/caf/temp/comcom/repo-closures/tape_archive.e:49
  // tape.save (o)
  assert {:subsumption 0} (Heap[Current, TAPE_ARCHIVE.tape]) != (Void); // type:attached line:49
  call TAPE.save(Heap[Current, TAPE_ARCHIVE.tape], o); // line:49 cid:408 rid:5411
  if (*) {
    assert (Heap[Current, TAPE_ARCHIVE.is_loaded]) ==> (Set#Equal(Heap[Current, owns], Set#Singleton(Heap[Current, TAPE_ARCHIVE.tape]))); // type:inv tag:owns_def line:50 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert (Heap[Current, TAPE_ARCHIVE.is_loaded]) ==> ((Heap[Current, TAPE_ARCHIVE.tape]) != (Void)); // type:inv tag:loaded line:50 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, observers]); // type:inv tag:default_observers line:50 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, subjects]); // type:inv tag:default_subjects line:50 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert admissibility2(Heap, Current); // type:inv tag:A2 line:50 cid:1 rid:55
    assume false;
  }
  call wrap(Current); // default:wrapping cid:1 rid:55 line:50
}

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, owns, v, o) } (attached_exact(heap, current, ANY)) ==> ((guard(heap, current, owns, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, subjects, v, o) } (attached_exact(heap, current, ANY)) ==> ((guard(heap, current, subjects, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached_exact(heap, current, ANY)) ==> ((guard(heap, current, observers, v, o)) <==> (fun.ANY.in_observers(heap, current, v, o)))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached(heap, current, ANY)) ==> ((guard(heap, current, observers, v, o)) ==> (fun.ANY.in_observers(heap, current, v, o)))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, owns, v, o) } (attached_exact(heap, current, FORMATTER_APPLICATION)) ==> ((guard(heap, current, owns, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, subjects, v, o) } (attached_exact(heap, current, FORMATTER_APPLICATION)) ==> ((guard(heap, current, subjects, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached_exact(heap, current, FORMATTER_APPLICATION)) ==> ((guard(heap, current, observers, v, o)) <==> (fun.FORMATTER_APPLICATION.in_observers(heap, current, v, o)))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached(heap, current, FORMATTER_APPLICATION)) ==> ((guard(heap, current, observers, v, o)) ==> (fun.FORMATTER_APPLICATION.in_observers(heap, current, v, o)))));

function modify.FORMATTER_APPLICATION.default_create(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T27> $o: ref, $f: Field T27 :: { modify.FORMATTER_APPLICATION.default_create(heap, current)[$o, $f] } (modify.FORMATTER_APPLICATION.default_create(heap, current)[$o, $f]) <==> (($o) == (current))))));

const PARAGRAPH.is_left_aligned: Field bool;

axiom ((FieldId(PARAGRAPH.is_left_aligned, PARAGRAPH)) == (80));

axiom ((forall heap: HeapType, current: ref, v: bool, o: ref :: { guard(heap, current, PARAGRAPH.is_left_aligned, v, o) } (attached_exact(heap, current, PARAGRAPH)) ==> ((guard(heap, current, PARAGRAPH.is_left_aligned, v, o)) <==> ((user_inv(heap, o)) ==> (user_inv(heap[current, PARAGRAPH.is_left_aligned := v], o))))));

axiom ((forall heap: HeapType, current: ref, v: bool, o: ref :: { guard(heap, current, PARAGRAPH.is_left_aligned, v, o) } (attached(heap, current, PARAGRAPH)) ==> ((guard(heap, current, PARAGRAPH.is_left_aligned, v, o)) ==> ((user_inv(heap, o)) ==> (user_inv(heap[current, PARAGRAPH.is_left_aligned := v], o))))));

function modify.FORMATTER_APPLICATION.apply_align_left(heap: HeapType, current: ref, a_formatter: ref, a_paragraph: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, a_formatter: ref, a_paragraph: ref :: (IsHeap(heap)) ==> ((forall <T28> $o: ref, $f: Field T28 :: { modify.FORMATTER_APPLICATION.apply_align_left(heap, current, a_formatter, a_paragraph)[$o, $f] } (modify.FORMATTER_APPLICATION.apply_align_left(heap, current, a_formatter, a_paragraph)[$o, $f]) <==> (($o) == (a_paragraph))))));

function pre.fun.FORMATTER.align_left(heap: HeapType, current: ref, a_paragraph: ref) returns (bool) {
  ((a_paragraph) != (Void)) && (!(heap[a_paragraph, PARAGRAPH.is_left_aligned])) && (is_wrapped(heap, current)) && (is_wrapped(heap, current)) && (is_wrapped(heap, a_paragraph)) && (is_wrapped(heap, a_paragraph))
}

function trigger.fun.FORMATTER.align_left(heap: HeapType, current: ref, a_paragraph: ref) returns (bool);

function post.FORMATTER.align_left(heap: HeapType, old_heap: HeapType, Current: ref, a_paragraph: ref) returns (bool);

axiom ((forall heap: HeapType, old_heap: HeapType, current: ref, a_paragraph: ref :: ((type_of(current)) <: (FORMATTER)) ==> ((post.FORMATTER.align_left(heap, old_heap, current, a_paragraph)) ==> ((heap[a_paragraph, PARAGRAPH.is_left_aligned]) && (is_wrapped(heap, current)) && (is_wrapped(heap, current)) && (is_wrapped(heap, a_paragraph)) && (is_wrapped(heap, a_paragraph))))));

function modify.FORMATTER_APPLICATION.apply_align_right(heap: HeapType, current: ref, a_formatter: ref, a_paragraph: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, a_formatter: ref, a_paragraph: ref :: (IsHeap(heap)) ==> ((forall <T29> $o: ref, $f: Field T29 :: { modify.FORMATTER_APPLICATION.apply_align_right(heap, current, a_formatter, a_paragraph)[$o, $f] } (modify.FORMATTER_APPLICATION.apply_align_right(heap, current, a_formatter, a_paragraph)[$o, $f]) <==> (($o) == (a_paragraph))))));

function pre.fun.FORMATTER.align_right(heap: HeapType, current: ref, a_paragraph: ref) returns (bool) {
  ((a_paragraph) != (Void)) && (heap[a_paragraph, PARAGRAPH.is_left_aligned]) && (is_wrapped(heap, current)) && (is_wrapped(heap, current)) && (is_wrapped(heap, a_paragraph)) && (is_wrapped(heap, a_paragraph))
}

function trigger.fun.FORMATTER.align_right(heap: HeapType, current: ref, a_paragraph: ref) returns (bool);

function post.FORMATTER.align_right(heap: HeapType, old_heap: HeapType, Current: ref, a_paragraph: ref) returns (bool);

axiom ((forall heap: HeapType, old_heap: HeapType, current: ref, a_paragraph: ref :: ((type_of(current)) <: (FORMATTER)) ==> ((post.FORMATTER.align_right(heap, old_heap, current, a_paragraph)) ==> ((!(heap[a_paragraph, PARAGRAPH.is_left_aligned])) && (is_wrapped(heap, current)) && (is_wrapped(heap, current)) && (is_wrapped(heap, a_paragraph)) && (is_wrapped(heap, a_paragraph))))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, owns, v, o) } (attached_exact(heap, current, TAPE)) ==> ((guard(heap, current, owns, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, subjects, v, o) } (attached_exact(heap, current, TAPE)) ==> ((guard(heap, current, subjects, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached_exact(heap, current, TAPE)) ==> ((guard(heap, current, observers, v, o)) <==> (fun.TAPE.in_observers(heap, current, v, o)))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached(heap, current, TAPE)) ==> ((guard(heap, current, observers, v, o)) ==> (fun.TAPE.in_observers(heap, current, v, o)))));

function modify.TAPE.default_create(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T30> $o: ref, $f: Field T30 :: { modify.TAPE.default_create(heap, current)[$o, $f] } (modify.TAPE.default_create(heap, current)[$o, $f]) <==> (($o) == (current))))));

function modify.TAPE.save(heap: HeapType, current: ref, o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, o: ref :: (IsHeap(heap)) ==> ((forall <T31> $o: ref, $f: Field T31 :: { modify.TAPE.save(heap, current, o)[$o, $f] } (modify.TAPE.save(heap, current, o)[$o, $f]) <==> (($o) == (current))))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, owns, v, o) } (attached_exact(heap, current, ACCOUNT_CLIENT)) ==> ((guard(heap, current, owns, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, subjects, v, o) } (attached_exact(heap, current, ACCOUNT_CLIENT)) ==> ((guard(heap, current, subjects, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached_exact(heap, current, ACCOUNT_CLIENT)) ==> ((guard(heap, current, observers, v, o)) <==> (fun.ACCOUNT_CLIENT.in_observers(heap, current, v, o)))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached(heap, current, ACCOUNT_CLIENT)) ==> ((guard(heap, current, observers, v, o)) ==> (fun.ACCOUNT_CLIENT.in_observers(heap, current, v, o)))));

function modify.ACCOUNT_CLIENT.default_create(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T32> $o: ref, $f: Field T32 :: { modify.ACCOUNT_CLIENT.default_create(heap, current)[$o, $f] } (modify.ACCOUNT_CLIENT.default_create(heap, current)[$o, $f]) <==> (($o) == (current))))));

function modify.ACCOUNT_CLIENT.test_agents(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T33> $o: ref, $f: Field T33 :: { modify.ACCOUNT_CLIENT.test_agents(heap, current)[$o, $f] } (modify.ACCOUNT_CLIENT.test_agents(heap, current)[$o, $f]) <==> (($o) == (current))))));

function pre.fun.ACCOUNT.deposit(heap: HeapType, current: ref, amount: int) returns (bool) {
  ((amount) >= (0)) && (is_wrapped(heap, current)) && (is_wrapped(heap, current))
}

function trigger.fun.ACCOUNT.deposit(heap: HeapType, current: ref, amount: int) returns (bool);

function post.ACCOUNT.deposit(heap: HeapType, old_heap: HeapType, Current: ref, amount: int) returns (bool);

axiom ((forall heap: HeapType, old_heap: HeapType, current: ref, amount: int :: ((type_of(current)) <: (ACCOUNT)) ==> ((post.ACCOUNT.deposit(heap, old_heap, current, amount)) ==> (((heap[current, ACCOUNT.balance]) == ((old_heap[current, ACCOUNT.balance]) + (amount))) && (is_wrapped(heap, current)) && (is_wrapped(heap, current))))));

function pre.fun.ACCOUNT.withdraw(heap: HeapType, current: ref, amount: int) returns (bool) {
  ((amount) <= (heap[current, ACCOUNT.balance])) && (is_wrapped(heap, current)) && (is_wrapped(heap, current))
}

function trigger.fun.ACCOUNT.withdraw(heap: HeapType, current: ref, amount: int) returns (bool);

function post.ACCOUNT.withdraw(heap: HeapType, old_heap: HeapType, Current: ref, amount: int) returns (bool);

axiom ((forall heap: HeapType, old_heap: HeapType, current: ref, amount: int :: ((type_of(current)) <: (ACCOUNT)) ==> ((post.ACCOUNT.withdraw(heap, old_heap, current, amount)) ==> (((heap[current, ACCOUNT.balance]) == ((old_heap[current, ACCOUNT.balance]) - (amount))) && (is_wrapped(heap, current)) && (is_wrapped(heap, current))))));

function pre.fun.ACCOUNT.transfer(heap: HeapType, current: ref, amount: int, other: ref) returns (bool) {
  ((other) != (Void)) && ((other) != (current)) && ((amount) >= (0)) && ((amount) <= (heap[current, ACCOUNT.balance])) && (is_wrapped(heap, current)) && (is_wrapped(heap, current)) && (is_wrapped(heap, other)) && (is_wrapped(heap, other))
}

function trigger.fun.ACCOUNT.transfer(heap: HeapType, current: ref, amount: int, other: ref) returns (bool);

function post.ACCOUNT.transfer(heap: HeapType, old_heap: HeapType, Current: ref, amount: int, other: ref) returns (bool);

axiom ((forall heap: HeapType, old_heap: HeapType, current: ref, amount: int, other: ref :: ((type_of(current)) <: (ACCOUNT)) ==> ((post.ACCOUNT.transfer(heap, old_heap, current, amount, other)) ==> (((heap[current, ACCOUNT.balance]) == ((old_heap[current, ACCOUNT.balance]) - (amount))) && ((heap[other, ACCOUNT.balance]) == ((old_heap[other, ACCOUNT.balance]) + (amount))) && (is_wrapped(heap, current)) && (is_wrapped(heap, current)) && (is_wrapped(heap, other)) && (is_wrapped(heap, other))))));

const ACCOUNT.balance: Field int;

axiom ((FieldId(ACCOUNT.balance, ACCOUNT)) == (81));

axiom ((forall heap: HeapType, o: ref :: { heap[o, ACCOUNT.balance] } ((IsHeap(heap)) && (attached(heap, o, ACCOUNT))) ==> (is_integer_32(heap[o, ACCOUNT.balance]))));

axiom ((forall heap: HeapType, current: ref, v: int, o: ref :: { guard(heap, current, ACCOUNT.balance, v, o) } (attached_exact(heap, current, ACCOUNT)) ==> ((guard(heap, current, ACCOUNT.balance, v, o)) <==> ((user_inv(heap, o)) ==> (user_inv(heap[current, ACCOUNT.balance := v], o))))));

axiom ((forall heap: HeapType, current: ref, v: int, o: ref :: { guard(heap, current, ACCOUNT.balance, v, o) } (attached(heap, current, ACCOUNT)) ==> ((guard(heap, current, ACCOUNT.balance, v, o)) ==> ((user_inv(heap, o)) ==> (user_inv(heap[current, ACCOUNT.balance := v], o))))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, owns, v, o) } (attached_exact(heap, current, CLIENT)) ==> ((guard(heap, current, owns, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, subjects, v, o) } (attached_exact(heap, current, CLIENT)) ==> ((guard(heap, current, subjects, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached_exact(heap, current, CLIENT)) ==> ((guard(heap, current, observers, v, o)) <==> (fun.CLIENT.in_observers(heap, current, v, o)))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached(heap, current, CLIENT)) ==> ((guard(heap, current, observers, v, o)) ==> (fun.CLIENT.in_observers(heap, current, v, o)))));

function modify.CLIENT.default_create(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T34> $o: ref, $f: Field T34 :: { modify.CLIENT.default_create(heap, current)[$o, $f] } (modify.CLIENT.default_create(heap, current)[$o, $f]) <==> (($o) == (current))))));

function modify.CLIENT.log(heap: HeapType, current: ref, log_file: ref, data: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, log_file: ref, data: ref :: (IsHeap(heap)) ==> ((forall <T35> $o: ref, $f: Field T35 :: { modify.CLIENT.log(heap, current, log_file, data)[$o, $f] } (modify.CLIENT.log(heap, current, log_file, data)[$o, $f]) <==> (($o) == (current))))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, owns, v, o) } (attached_exact(heap, current, PARAGRAPH)) ==> ((guard(heap, current, owns, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, subjects, v, o) } (attached_exact(heap, current, PARAGRAPH)) ==> ((guard(heap, current, subjects, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached_exact(heap, current, PARAGRAPH)) ==> ((guard(heap, current, observers, v, o)) <==> (fun.PARAGRAPH.in_observers(heap, current, v, o)))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached(heap, current, PARAGRAPH)) ==> ((guard(heap, current, observers, v, o)) ==> (fun.PARAGRAPH.in_observers(heap, current, v, o)))));

function modify.PARAGRAPH.default_create(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T36> $o: ref, $f: Field T36 :: { modify.PARAGRAPH.default_create(heap, current)[$o, $f] } (modify.PARAGRAPH.default_create(heap, current)[$o, $f]) <==> (($o) == (current))))));

function modify.PARAGRAPH.align_left(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T37> $o: ref, $f: Field T37 :: { modify.PARAGRAPH.align_left(heap, current)[$o, $f] } (modify.PARAGRAPH.align_left(heap, current)[$o, $f]) <==> (($o) == (current))))));

function modify.PARAGRAPH.align_right(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T38> $o: ref, $f: Field T38 :: { modify.PARAGRAPH.align_right(heap, current)[$o, $f] } (modify.PARAGRAPH.align_right(heap, current)[$o, $f]) <==> (($o) == (current))))));

function modify.PARAGRAPH.format(heap: HeapType, current: ref, proc: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, proc: ref :: (IsHeap(heap)) ==> ((forall <T39> $o: ref, $f: Field T39 :: { modify.PARAGRAPH.format(heap, current, proc)[$o, $f] } (modify.PARAGRAPH.format(heap, current, proc)[$o, $f]) <==> (($o) == (current))))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, owns, v, o) } (attached_exact(heap, current, ARCHIVER_APPLICATION)) ==> ((guard(heap, current, owns, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, subjects, v, o) } (attached_exact(heap, current, ARCHIVER_APPLICATION)) ==> ((guard(heap, current, subjects, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached_exact(heap, current, ARCHIVER_APPLICATION)) ==> ((guard(heap, current, observers, v, o)) <==> (fun.ARCHIVER_APPLICATION.in_observers(heap, current, v, o)))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached(heap, current, ARCHIVER_APPLICATION)) ==> ((guard(heap, current, observers, v, o)) ==> (fun.ARCHIVER_APPLICATION.in_observers(heap, current, v, o)))));

function modify.ARCHIVER_APPLICATION.default_create(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T40> $o: ref, $f: Field T40 :: { modify.ARCHIVER_APPLICATION.default_create(heap, current)[$o, $f] } (modify.ARCHIVER_APPLICATION.default_create(heap, current)[$o, $f]) <==> (($o) == (current))))));

function modify.ARCHIVER_APPLICATION.run(heap: HeapType, current: ref, c: ref, data: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, c: ref, data: ref :: (IsHeap(heap)) ==> ((forall <T41> $o: ref, $f: Field T41 :: { modify.ARCHIVER_APPLICATION.run(heap, current, c, data)[$o, $f] } (modify.ARCHIVER_APPLICATION.run(heap, current, c, data)[$o, $f]) <==> (($o) == (c))))));

function pre.fun.TAPE_ARCHIVE.store(heap: HeapType, current: ref, o: ref) returns (bool) {
  ((o) != (Void)) && ((o) != (current)) && (heap[current, TAPE_ARCHIVE.is_loaded]) && (is_wrapped(heap, current)) && (is_wrapped(heap, current)) && (is_wrapped(heap, o)) && (is_wrapped(heap, o))
}

function trigger.fun.TAPE_ARCHIVE.store(heap: HeapType, current: ref, o: ref) returns (bool);

function post.TAPE_ARCHIVE.store(heap: HeapType, old_heap: HeapType, Current: ref, o: ref) returns (bool);

axiom ((forall heap: HeapType, old_heap: HeapType, current: ref, o: ref :: ((type_of(current)) <: (TAPE_ARCHIVE)) ==> ((post.TAPE_ARCHIVE.store(heap, old_heap, current, o)) ==> ((is_wrapped(heap, current)) && (is_wrapped(heap, current)) && (is_wrapped(heap, o)) && (is_wrapped(heap, o))))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, owns, v, o) } (attached_exact(heap, current, FORMATTER)) ==> ((guard(heap, current, owns, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, subjects, v, o) } (attached_exact(heap, current, FORMATTER)) ==> ((guard(heap, current, subjects, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached_exact(heap, current, FORMATTER)) ==> ((guard(heap, current, observers, v, o)) <==> (fun.FORMATTER.in_observers(heap, current, v, o)))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached(heap, current, FORMATTER)) ==> ((guard(heap, current, observers, v, o)) ==> (fun.FORMATTER.in_observers(heap, current, v, o)))));

function modify.FORMATTER.default_create(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T42> $o: ref, $f: Field T42 :: { modify.FORMATTER.default_create(heap, current)[$o, $f] } (modify.FORMATTER.default_create(heap, current)[$o, $f]) <==> (($o) == (current))))));

function modify.FORMATTER.align_left(heap: HeapType, current: ref, a_paragraph: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, a_paragraph: ref :: (IsHeap(heap)) ==> ((forall <T43> $o: ref, $f: Field T43 :: { modify.FORMATTER.align_left(heap, current, a_paragraph)[$o, $f] } (modify.FORMATTER.align_left(heap, current, a_paragraph)[$o, $f]) <==> (($o) == (a_paragraph))))));

function modify.FORMATTER.align_right(heap: HeapType, current: ref, a_paragraph: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, a_paragraph: ref :: (IsHeap(heap)) ==> ((forall <T44> $o: ref, $f: Field T44 :: { modify.FORMATTER.align_right(heap, current, a_paragraph)[$o, $f] } (modify.FORMATTER.align_right(heap, current, a_paragraph)[$o, $f]) <==> (($o) == (a_paragraph))))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, owns, v, o) } (attached_exact(heap, current, ACCOUNT)) ==> ((guard(heap, current, owns, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, subjects, v, o) } (attached_exact(heap, current, ACCOUNT)) ==> ((guard(heap, current, subjects, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached_exact(heap, current, ACCOUNT)) ==> ((guard(heap, current, observers, v, o)) <==> (fun.ACCOUNT.in_observers(heap, current, v, o)))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached(heap, current, ACCOUNT)) ==> ((guard(heap, current, observers, v, o)) ==> (fun.ACCOUNT.in_observers(heap, current, v, o)))));

function modify.ACCOUNT.make(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T45> $o: ref, $f: Field T45 :: { modify.ACCOUNT.make(heap, current)[$o, $f] } (modify.ACCOUNT.make(heap, current)[$o, $f]) <==> (($o) == (current))))));

function modify.ACCOUNT.deposit(heap: HeapType, current: ref, amount: int) returns (Frame);

axiom ((forall heap: HeapType, current: ref, amount: int :: (IsHeap(heap)) ==> ((forall <T46> $o: ref, $f: Field T46 :: { modify.ACCOUNT.deposit(heap, current, amount)[$o, $f] } (modify.ACCOUNT.deposit(heap, current, amount)[$o, $f]) <==> (($o) == (current))))));

function modify.ACCOUNT.withdraw(heap: HeapType, current: ref, amount: int) returns (Frame);

axiom ((forall heap: HeapType, current: ref, amount: int :: (IsHeap(heap)) ==> ((forall <T47> $o: ref, $f: Field T47 :: { modify.ACCOUNT.withdraw(heap, current, amount)[$o, $f] } (modify.ACCOUNT.withdraw(heap, current, amount)[$o, $f]) <==> (($o) == (current))))));

function modify.ACCOUNT.transfer(heap: HeapType, current: ref, amount: int, other: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, amount: int, other: ref :: (IsHeap(heap)) ==> ((forall <T48> $o: ref, $f: Field T48 :: { modify.ACCOUNT.transfer(heap, current, amount, other)[$o, $f] } (modify.ACCOUNT.transfer(heap, current, amount, other)[$o, $f]) <==> ((($o) == (current)) || (($o) == (other)))))));

const TAPE_ARCHIVE.is_loaded: Field bool;

axiom ((FieldId(TAPE_ARCHIVE.is_loaded, TAPE_ARCHIVE)) == (82));

axiom ((forall heap: HeapType, current: ref, v: bool, o: ref :: { guard(heap, current, TAPE_ARCHIVE.is_loaded, v, o) } (attached_exact(heap, current, TAPE_ARCHIVE)) ==> ((guard(heap, current, TAPE_ARCHIVE.is_loaded, v, o)) <==> ((user_inv(heap, o)) ==> (user_inv(heap[current, TAPE_ARCHIVE.is_loaded := v], o))))));

axiom ((forall heap: HeapType, current: ref, v: bool, o: ref :: { guard(heap, current, TAPE_ARCHIVE.is_loaded, v, o) } (attached(heap, current, TAPE_ARCHIVE)) ==> ((guard(heap, current, TAPE_ARCHIVE.is_loaded, v, o)) ==> ((user_inv(heap, o)) ==> (user_inv(heap[current, TAPE_ARCHIVE.is_loaded := v], o))))));

const TAPE_ARCHIVE.tape: Field (ref);

axiom ((FieldId(TAPE_ARCHIVE.tape, TAPE_ARCHIVE)) == (81));

axiom ((forall heap: HeapType, o: ref :: { heap[o, TAPE_ARCHIVE.tape] } ((IsHeap(heap)) && (attached(heap, o, TAPE_ARCHIVE))) ==> (detachable(heap, heap[o, TAPE_ARCHIVE.tape], TAPE))));

axiom ((forall heap: HeapType, current: ref, v: ref, o: ref :: { guard(heap, current, TAPE_ARCHIVE.tape, v, o) } (attached_exact(heap, current, TAPE_ARCHIVE)) ==> ((guard(heap, current, TAPE_ARCHIVE.tape, v, o)) <==> ((user_inv(heap, o)) ==> (user_inv(heap[current, TAPE_ARCHIVE.tape := v], o))))));

axiom ((forall heap: HeapType, current: ref, v: ref, o: ref :: { guard(heap, current, TAPE_ARCHIVE.tape, v, o) } (attached(heap, current, TAPE_ARCHIVE)) ==> ((guard(heap, current, TAPE_ARCHIVE.tape, v, o)) ==> ((user_inv(heap, o)) ==> (user_inv(heap[current, TAPE_ARCHIVE.tape := v], o))))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, owns, v, o) } (attached_exact(heap, current, TAPE_ARCHIVE)) ==> ((guard(heap, current, owns, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, subjects, v, o) } (attached_exact(heap, current, TAPE_ARCHIVE)) ==> ((guard(heap, current, subjects, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached_exact(heap, current, TAPE_ARCHIVE)) ==> ((guard(heap, current, observers, v, o)) <==> (fun.TAPE_ARCHIVE.in_observers(heap, current, v, o)))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached(heap, current, TAPE_ARCHIVE)) ==> ((guard(heap, current, observers, v, o)) ==> (fun.TAPE_ARCHIVE.in_observers(heap, current, v, o)))));

function modify.TAPE_ARCHIVE.make(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T49> $o: ref, $f: Field T49 :: { modify.TAPE_ARCHIVE.make(heap, current)[$o, $f] } (modify.TAPE_ARCHIVE.make(heap, current)[$o, $f]) <==> (($o) == (current))))));

function modify.TAPE_ARCHIVE.eject(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T50> $o: ref, $f: Field T50 :: { modify.TAPE_ARCHIVE.eject(heap, current)[$o, $f] } (modify.TAPE_ARCHIVE.eject(heap, current)[$o, $f]) <==> (($o) == (current))))));

function modify.TAPE_ARCHIVE.store(heap: HeapType, current: ref, o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, o: ref :: (IsHeap(heap)) ==> ((forall <T51> $o: ref, $f: Field T51 :: { modify.TAPE_ARCHIVE.store(heap, current, o)[$o, $f] } (modify.TAPE_ARCHIVE.store(heap, current, o)[$o, $f]) <==> (($o) == (current))))));

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

procedure FORMATTER_APPLICATION.in_observers(Current: ref, new_observers: Set (ref), o: ref) returns (Result: bool where true);
  free requires attached_exact(Heap, Current, FORMATTER_APPLICATION); // info:type property for argument Current
  free requires Set#ItemsType(Heap, new_observers, ANY); // info:type property for argument new_observers
  free requires Heap[o, allocated]; // info:type property for argument o
  modifies Heap;
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.FORMATTER_APPLICATION.in_observers(Heap, Current, new_observers, o), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.FORMATTER_APPLICATION.in_observers(old(Heap), Current, new_observers, o));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.FORMATTER_APPLICATION.in_observers(Heap, Current, new_observers, o), readable);



function fun.FORMATTER_APPLICATION.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function fun0.FORMATTER_APPLICATION.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.FORMATTER_APPLICATION.in_observers(heap, current, new_observers, o) } { trigger.fun.FORMATTER_APPLICATION.in_observers(heap, current, new_observers, o) } (pre.fun.FORMATTER_APPLICATION.in_observers(heap, current, new_observers, o)) ==> ((fun.FORMATTER_APPLICATION.in_observers(heap, current, new_observers, o)) == (new_observers[o]))));

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.FORMATTER_APPLICATION.in_observers(heap, current, new_observers, o) } (fun.FORMATTER_APPLICATION.in_observers(heap, current, new_observers, o)) == (fun0.FORMATTER_APPLICATION.in_observers(heap, current, new_observers, o))));

axiom ((forall h: HeapType, h': HeapType, current: ref, new_observers: Set (ref), o: ref :: { HeapSucc(h, h'), fun0.FORMATTER_APPLICATION.in_observers(h, current, new_observers, o), fun0.FORMATTER_APPLICATION.in_observers(h', current, new_observers, o) } ((HeapSucc(h, h')) && (pre.fun.FORMATTER_APPLICATION.in_observers(h, current, new_observers, o)) && (pre.fun.FORMATTER_APPLICATION.in_observers(h', current, new_observers, o)) && (same_inside(h, h', read.fun.FORMATTER_APPLICATION.in_observers(h, current, new_observers, o)))) ==> ((fun0.FORMATTER_APPLICATION.in_observers(h, current, new_observers, o)) == (fun0.FORMATTER_APPLICATION.in_observers(h', current, new_observers, o)))));

procedure TAPE.in_observers(Current: ref, new_observers: Set (ref), o: ref) returns (Result: bool where true);
  free requires attached_exact(Heap, Current, TAPE); // info:type property for argument Current
  free requires Set#ItemsType(Heap, new_observers, ANY); // info:type property for argument new_observers
  free requires Heap[o, allocated]; // info:type property for argument o
  modifies Heap;
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.TAPE.in_observers(Heap, Current, new_observers, o), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.TAPE.in_observers(old(Heap), Current, new_observers, o));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.TAPE.in_observers(Heap, Current, new_observers, o), readable);



function fun.TAPE.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function fun0.TAPE.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.TAPE.in_observers(heap, current, new_observers, o) } { trigger.fun.TAPE.in_observers(heap, current, new_observers, o) } (pre.fun.TAPE.in_observers(heap, current, new_observers, o)) ==> ((fun.TAPE.in_observers(heap, current, new_observers, o)) == (new_observers[o]))));

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.TAPE.in_observers(heap, current, new_observers, o) } (fun.TAPE.in_observers(heap, current, new_observers, o)) == (fun0.TAPE.in_observers(heap, current, new_observers, o))));

axiom ((forall h: HeapType, h': HeapType, current: ref, new_observers: Set (ref), o: ref :: { HeapSucc(h, h'), fun0.TAPE.in_observers(h, current, new_observers, o), fun0.TAPE.in_observers(h', current, new_observers, o) } ((HeapSucc(h, h')) && (pre.fun.TAPE.in_observers(h, current, new_observers, o)) && (pre.fun.TAPE.in_observers(h', current, new_observers, o)) && (same_inside(h, h', read.fun.TAPE.in_observers(h, current, new_observers, o)))) ==> ((fun0.TAPE.in_observers(h, current, new_observers, o)) == (fun0.TAPE.in_observers(h', current, new_observers, o)))));

procedure ACCOUNT_CLIENT.in_observers(Current: ref, new_observers: Set (ref), o: ref) returns (Result: bool where true);
  free requires attached_exact(Heap, Current, ACCOUNT_CLIENT); // info:type property for argument Current
  free requires Set#ItemsType(Heap, new_observers, ANY); // info:type property for argument new_observers
  free requires Heap[o, allocated]; // info:type property for argument o
  modifies Heap;
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.ACCOUNT_CLIENT.in_observers(Heap, Current, new_observers, o), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.ACCOUNT_CLIENT.in_observers(old(Heap), Current, new_observers, o));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.ACCOUNT_CLIENT.in_observers(Heap, Current, new_observers, o), readable);



function fun.ACCOUNT_CLIENT.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function fun0.ACCOUNT_CLIENT.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.ACCOUNT_CLIENT.in_observers(heap, current, new_observers, o) } { trigger.fun.ACCOUNT_CLIENT.in_observers(heap, current, new_observers, o) } (pre.fun.ACCOUNT_CLIENT.in_observers(heap, current, new_observers, o)) ==> ((fun.ACCOUNT_CLIENT.in_observers(heap, current, new_observers, o)) == (new_observers[o]))));

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.ACCOUNT_CLIENT.in_observers(heap, current, new_observers, o) } (fun.ACCOUNT_CLIENT.in_observers(heap, current, new_observers, o)) == (fun0.ACCOUNT_CLIENT.in_observers(heap, current, new_observers, o))));

axiom ((forall h: HeapType, h': HeapType, current: ref, new_observers: Set (ref), o: ref :: { HeapSucc(h, h'), fun0.ACCOUNT_CLIENT.in_observers(h, current, new_observers, o), fun0.ACCOUNT_CLIENT.in_observers(h', current, new_observers, o) } ((HeapSucc(h, h')) && (pre.fun.ACCOUNT_CLIENT.in_observers(h, current, new_observers, o)) && (pre.fun.ACCOUNT_CLIENT.in_observers(h', current, new_observers, o)) && (same_inside(h, h', read.fun.ACCOUNT_CLIENT.in_observers(h, current, new_observers, o)))) ==> ((fun0.ACCOUNT_CLIENT.in_observers(h, current, new_observers, o)) == (fun0.ACCOUNT_CLIENT.in_observers(h', current, new_observers, o)))));

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

procedure PARAGRAPH.in_observers(Current: ref, new_observers: Set (ref), o: ref) returns (Result: bool where true);
  free requires attached_exact(Heap, Current, PARAGRAPH); // info:type property for argument Current
  free requires Set#ItemsType(Heap, new_observers, ANY); // info:type property for argument new_observers
  free requires Heap[o, allocated]; // info:type property for argument o
  modifies Heap;
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.PARAGRAPH.in_observers(Heap, Current, new_observers, o), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.PARAGRAPH.in_observers(old(Heap), Current, new_observers, o));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.PARAGRAPH.in_observers(Heap, Current, new_observers, o), readable);



function fun.PARAGRAPH.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function fun0.PARAGRAPH.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.PARAGRAPH.in_observers(heap, current, new_observers, o) } { trigger.fun.PARAGRAPH.in_observers(heap, current, new_observers, o) } (pre.fun.PARAGRAPH.in_observers(heap, current, new_observers, o)) ==> ((fun.PARAGRAPH.in_observers(heap, current, new_observers, o)) == (new_observers[o]))));

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.PARAGRAPH.in_observers(heap, current, new_observers, o) } (fun.PARAGRAPH.in_observers(heap, current, new_observers, o)) == (fun0.PARAGRAPH.in_observers(heap, current, new_observers, o))));

axiom ((forall h: HeapType, h': HeapType, current: ref, new_observers: Set (ref), o: ref :: { HeapSucc(h, h'), fun0.PARAGRAPH.in_observers(h, current, new_observers, o), fun0.PARAGRAPH.in_observers(h', current, new_observers, o) } ((HeapSucc(h, h')) && (pre.fun.PARAGRAPH.in_observers(h, current, new_observers, o)) && (pre.fun.PARAGRAPH.in_observers(h', current, new_observers, o)) && (same_inside(h, h', read.fun.PARAGRAPH.in_observers(h, current, new_observers, o)))) ==> ((fun0.PARAGRAPH.in_observers(h, current, new_observers, o)) == (fun0.PARAGRAPH.in_observers(h', current, new_observers, o)))));

procedure ARCHIVER_APPLICATION.in_observers(Current: ref, new_observers: Set (ref), o: ref) returns (Result: bool where true);
  free requires attached_exact(Heap, Current, ARCHIVER_APPLICATION); // info:type property for argument Current
  free requires Set#ItemsType(Heap, new_observers, ANY); // info:type property for argument new_observers
  free requires Heap[o, allocated]; // info:type property for argument o
  modifies Heap;
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.ARCHIVER_APPLICATION.in_observers(Heap, Current, new_observers, o), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.ARCHIVER_APPLICATION.in_observers(old(Heap), Current, new_observers, o));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.ARCHIVER_APPLICATION.in_observers(Heap, Current, new_observers, o), readable);



function fun.ARCHIVER_APPLICATION.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function fun0.ARCHIVER_APPLICATION.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.ARCHIVER_APPLICATION.in_observers(heap, current, new_observers, o) } { trigger.fun.ARCHIVER_APPLICATION.in_observers(heap, current, new_observers, o) } (pre.fun.ARCHIVER_APPLICATION.in_observers(heap, current, new_observers, o)) ==> ((fun.ARCHIVER_APPLICATION.in_observers(heap, current, new_observers, o)) == (new_observers[o]))));

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.ARCHIVER_APPLICATION.in_observers(heap, current, new_observers, o) } (fun.ARCHIVER_APPLICATION.in_observers(heap, current, new_observers, o)) == (fun0.ARCHIVER_APPLICATION.in_observers(heap, current, new_observers, o))));

axiom ((forall h: HeapType, h': HeapType, current: ref, new_observers: Set (ref), o: ref :: { HeapSucc(h, h'), fun0.ARCHIVER_APPLICATION.in_observers(h, current, new_observers, o), fun0.ARCHIVER_APPLICATION.in_observers(h', current, new_observers, o) } ((HeapSucc(h, h')) && (pre.fun.ARCHIVER_APPLICATION.in_observers(h, current, new_observers, o)) && (pre.fun.ARCHIVER_APPLICATION.in_observers(h', current, new_observers, o)) && (same_inside(h, h', read.fun.ARCHIVER_APPLICATION.in_observers(h, current, new_observers, o)))) ==> ((fun0.ARCHIVER_APPLICATION.in_observers(h, current, new_observers, o)) == (fun0.ARCHIVER_APPLICATION.in_observers(h', current, new_observers, o)))));

procedure FORMATTER.in_observers(Current: ref, new_observers: Set (ref), o: ref) returns (Result: bool where true);
  free requires attached_exact(Heap, Current, FORMATTER); // info:type property for argument Current
  free requires Set#ItemsType(Heap, new_observers, ANY); // info:type property for argument new_observers
  free requires Heap[o, allocated]; // info:type property for argument o
  modifies Heap;
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.FORMATTER.in_observers(Heap, Current, new_observers, o), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.FORMATTER.in_observers(old(Heap), Current, new_observers, o));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.FORMATTER.in_observers(Heap, Current, new_observers, o), readable);



function fun.FORMATTER.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function fun0.FORMATTER.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.FORMATTER.in_observers(heap, current, new_observers, o) } { trigger.fun.FORMATTER.in_observers(heap, current, new_observers, o) } (pre.fun.FORMATTER.in_observers(heap, current, new_observers, o)) ==> ((fun.FORMATTER.in_observers(heap, current, new_observers, o)) == (new_observers[o]))));

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.FORMATTER.in_observers(heap, current, new_observers, o) } (fun.FORMATTER.in_observers(heap, current, new_observers, o)) == (fun0.FORMATTER.in_observers(heap, current, new_observers, o))));

axiom ((forall h: HeapType, h': HeapType, current: ref, new_observers: Set (ref), o: ref :: { HeapSucc(h, h'), fun0.FORMATTER.in_observers(h, current, new_observers, o), fun0.FORMATTER.in_observers(h', current, new_observers, o) } ((HeapSucc(h, h')) && (pre.fun.FORMATTER.in_observers(h, current, new_observers, o)) && (pre.fun.FORMATTER.in_observers(h', current, new_observers, o)) && (same_inside(h, h', read.fun.FORMATTER.in_observers(h, current, new_observers, o)))) ==> ((fun0.FORMATTER.in_observers(h, current, new_observers, o)) == (fun0.FORMATTER.in_observers(h', current, new_observers, o)))));

procedure ACCOUNT.in_observers(Current: ref, new_observers: Set (ref), o: ref) returns (Result: bool where true);
  free requires attached_exact(Heap, Current, ACCOUNT); // info:type property for argument Current
  free requires Set#ItemsType(Heap, new_observers, ANY); // info:type property for argument new_observers
  free requires Heap[o, allocated]; // info:type property for argument o
  modifies Heap;
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.ACCOUNT.in_observers(Heap, Current, new_observers, o), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.ACCOUNT.in_observers(old(Heap), Current, new_observers, o));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.ACCOUNT.in_observers(Heap, Current, new_observers, o), readable);



function fun.ACCOUNT.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function fun0.ACCOUNT.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.ACCOUNT.in_observers(heap, current, new_observers, o) } { trigger.fun.ACCOUNT.in_observers(heap, current, new_observers, o) } (pre.fun.ACCOUNT.in_observers(heap, current, new_observers, o)) ==> ((fun.ACCOUNT.in_observers(heap, current, new_observers, o)) == (new_observers[o]))));

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.ACCOUNT.in_observers(heap, current, new_observers, o) } (fun.ACCOUNT.in_observers(heap, current, new_observers, o)) == (fun0.ACCOUNT.in_observers(heap, current, new_observers, o))));

axiom ((forall h: HeapType, h': HeapType, current: ref, new_observers: Set (ref), o: ref :: { HeapSucc(h, h'), fun0.ACCOUNT.in_observers(h, current, new_observers, o), fun0.ACCOUNT.in_observers(h', current, new_observers, o) } ((HeapSucc(h, h')) && (pre.fun.ACCOUNT.in_observers(h, current, new_observers, o)) && (pre.fun.ACCOUNT.in_observers(h', current, new_observers, o)) && (same_inside(h, h', read.fun.ACCOUNT.in_observers(h, current, new_observers, o)))) ==> ((fun0.ACCOUNT.in_observers(h, current, new_observers, o)) == (fun0.ACCOUNT.in_observers(h', current, new_observers, o)))));

procedure TAPE_ARCHIVE.in_observers(Current: ref, new_observers: Set (ref), o: ref) returns (Result: bool where true);
  free requires attached_exact(Heap, Current, TAPE_ARCHIVE); // info:type property for argument Current
  free requires Set#ItemsType(Heap, new_observers, ANY); // info:type property for argument new_observers
  free requires Heap[o, allocated]; // info:type property for argument o
  modifies Heap;
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.TAPE_ARCHIVE.in_observers(Heap, Current, new_observers, o), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.TAPE_ARCHIVE.in_observers(old(Heap), Current, new_observers, o));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.TAPE_ARCHIVE.in_observers(Heap, Current, new_observers, o), readable);



function fun.TAPE_ARCHIVE.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function fun0.TAPE_ARCHIVE.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.TAPE_ARCHIVE.in_observers(heap, current, new_observers, o) } { trigger.fun.TAPE_ARCHIVE.in_observers(heap, current, new_observers, o) } (pre.fun.TAPE_ARCHIVE.in_observers(heap, current, new_observers, o)) ==> ((fun.TAPE_ARCHIVE.in_observers(heap, current, new_observers, o)) == (new_observers[o]))));

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.TAPE_ARCHIVE.in_observers(heap, current, new_observers, o) } (fun.TAPE_ARCHIVE.in_observers(heap, current, new_observers, o)) == (fun0.TAPE_ARCHIVE.in_observers(heap, current, new_observers, o))));

axiom ((forall h: HeapType, h': HeapType, current: ref, new_observers: Set (ref), o: ref :: { HeapSucc(h, h'), fun0.TAPE_ARCHIVE.in_observers(h, current, new_observers, o), fun0.TAPE_ARCHIVE.in_observers(h', current, new_observers, o) } ((HeapSucc(h, h')) && (pre.fun.TAPE_ARCHIVE.in_observers(h, current, new_observers, o)) && (pre.fun.TAPE_ARCHIVE.in_observers(h', current, new_observers, o)) && (same_inside(h, h', read.fun.TAPE_ARCHIVE.in_observers(h, current, new_observers, o)))) ==> ((fun0.TAPE_ARCHIVE.in_observers(h, current, new_observers, o)) == (fun0.TAPE_ARCHIVE.in_observers(h', current, new_observers, o)))));

function modify.ANY.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T52> $o: ref, $f: Field T52 :: { modify.ANY.in_observers(heap, current, new_observers, o)[$o, $f] } (modify.ANY.in_observers(heap, current, new_observers, o)[$o, $f]) <==> (false)))));

function read.fun.ANY.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T53> $o: ref, $f: Field T53 :: { read.fun.ANY.in_observers(heap, current, new_observers, o)[$o, $f] } (read.fun.ANY.in_observers(heap, current, new_observers, o)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.ANY.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool) {
  true
}

function trigger.fun.ANY.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function modify.FORMATTER_APPLICATION.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T54> $o: ref, $f: Field T54 :: { modify.FORMATTER_APPLICATION.in_observers(heap, current, new_observers, o)[$o, $f] } (modify.FORMATTER_APPLICATION.in_observers(heap, current, new_observers, o)[$o, $f]) <==> (false)))));

function read.fun.FORMATTER_APPLICATION.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T55> $o: ref, $f: Field T55 :: { read.fun.FORMATTER_APPLICATION.in_observers(heap, current, new_observers, o)[$o, $f] } (read.fun.FORMATTER_APPLICATION.in_observers(heap, current, new_observers, o)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.FORMATTER_APPLICATION.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool) {
  true
}

function trigger.fun.FORMATTER_APPLICATION.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function modify.TAPE.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T56> $o: ref, $f: Field T56 :: { modify.TAPE.in_observers(heap, current, new_observers, o)[$o, $f] } (modify.TAPE.in_observers(heap, current, new_observers, o)[$o, $f]) <==> (false)))));

function read.fun.TAPE.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T57> $o: ref, $f: Field T57 :: { read.fun.TAPE.in_observers(heap, current, new_observers, o)[$o, $f] } (read.fun.TAPE.in_observers(heap, current, new_observers, o)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.TAPE.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool) {
  true
}

function trigger.fun.TAPE.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function modify.ACCOUNT_CLIENT.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T58> $o: ref, $f: Field T58 :: { modify.ACCOUNT_CLIENT.in_observers(heap, current, new_observers, o)[$o, $f] } (modify.ACCOUNT_CLIENT.in_observers(heap, current, new_observers, o)[$o, $f]) <==> (false)))));

function read.fun.ACCOUNT_CLIENT.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T59> $o: ref, $f: Field T59 :: { read.fun.ACCOUNT_CLIENT.in_observers(heap, current, new_observers, o)[$o, $f] } (read.fun.ACCOUNT_CLIENT.in_observers(heap, current, new_observers, o)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.ACCOUNT_CLIENT.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool) {
  true
}

function trigger.fun.ACCOUNT_CLIENT.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function modify.CLIENT.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T60> $o: ref, $f: Field T60 :: { modify.CLIENT.in_observers(heap, current, new_observers, o)[$o, $f] } (modify.CLIENT.in_observers(heap, current, new_observers, o)[$o, $f]) <==> (false)))));

function read.fun.CLIENT.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T61> $o: ref, $f: Field T61 :: { read.fun.CLIENT.in_observers(heap, current, new_observers, o)[$o, $f] } (read.fun.CLIENT.in_observers(heap, current, new_observers, o)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.CLIENT.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool) {
  true
}

function trigger.fun.CLIENT.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function modify.PARAGRAPH.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T62> $o: ref, $f: Field T62 :: { modify.PARAGRAPH.in_observers(heap, current, new_observers, o)[$o, $f] } (modify.PARAGRAPH.in_observers(heap, current, new_observers, o)[$o, $f]) <==> (false)))));

function read.fun.PARAGRAPH.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T63> $o: ref, $f: Field T63 :: { read.fun.PARAGRAPH.in_observers(heap, current, new_observers, o)[$o, $f] } (read.fun.PARAGRAPH.in_observers(heap, current, new_observers, o)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.PARAGRAPH.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool) {
  true
}

function trigger.fun.PARAGRAPH.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function modify.ARCHIVER_APPLICATION.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T64> $o: ref, $f: Field T64 :: { modify.ARCHIVER_APPLICATION.in_observers(heap, current, new_observers, o)[$o, $f] } (modify.ARCHIVER_APPLICATION.in_observers(heap, current, new_observers, o)[$o, $f]) <==> (false)))));

function read.fun.ARCHIVER_APPLICATION.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T65> $o: ref, $f: Field T65 :: { read.fun.ARCHIVER_APPLICATION.in_observers(heap, current, new_observers, o)[$o, $f] } (read.fun.ARCHIVER_APPLICATION.in_observers(heap, current, new_observers, o)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.ARCHIVER_APPLICATION.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool) {
  true
}

function trigger.fun.ARCHIVER_APPLICATION.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function modify.FORMATTER.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T66> $o: ref, $f: Field T66 :: { modify.FORMATTER.in_observers(heap, current, new_observers, o)[$o, $f] } (modify.FORMATTER.in_observers(heap, current, new_observers, o)[$o, $f]) <==> (false)))));

function read.fun.FORMATTER.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T67> $o: ref, $f: Field T67 :: { read.fun.FORMATTER.in_observers(heap, current, new_observers, o)[$o, $f] } (read.fun.FORMATTER.in_observers(heap, current, new_observers, o)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.FORMATTER.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool) {
  true
}

function trigger.fun.FORMATTER.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function modify.ACCOUNT.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T68> $o: ref, $f: Field T68 :: { modify.ACCOUNT.in_observers(heap, current, new_observers, o)[$o, $f] } (modify.ACCOUNT.in_observers(heap, current, new_observers, o)[$o, $f]) <==> (false)))));

function read.fun.ACCOUNT.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T69> $o: ref, $f: Field T69 :: { read.fun.ACCOUNT.in_observers(heap, current, new_observers, o)[$o, $f] } (read.fun.ACCOUNT.in_observers(heap, current, new_observers, o)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.ACCOUNT.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool) {
  true
}

function trigger.fun.ACCOUNT.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function modify.TAPE_ARCHIVE.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T70> $o: ref, $f: Field T70 :: { modify.TAPE_ARCHIVE.in_observers(heap, current, new_observers, o)[$o, $f] } (modify.TAPE_ARCHIVE.in_observers(heap, current, new_observers, o)[$o, $f]) <==> (false)))));

function read.fun.TAPE_ARCHIVE.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T71> $o: ref, $f: Field T71 :: { read.fun.TAPE_ARCHIVE.in_observers(heap, current, new_observers, o)[$o, $f] } (read.fun.TAPE_ARCHIVE.in_observers(heap, current, new_observers, o)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.TAPE_ARCHIVE.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool) {
  true
}

function trigger.fun.TAPE_ARCHIVE.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);
