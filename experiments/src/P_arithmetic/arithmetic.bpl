// Automatically generated (12/12/2017 1:54:13.128 PM)

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
//// axiom (forall r: real :: { real_to_integer_32(r) } is_integer_32(int(r)) ==> real_to_integer_32(r) == int(r));
// axiom (forall r: real :: { real_to_integer_32(r) } (!is_integer_32(int(r)) && r < 0.0) ==> real_to_integer_32(r) == -2147483648); // 'real' unsupported
// axiom (forall r: real :: { real_to_integer_32(r) } (!is_integer_32(int(r)) && r > 0.0) ==> real_to_integer_32(r) ==  2147483647); // 'real' unsupported

// function real_to_integer_64(r: real) returns (int); // 'real' unsupported
//// axiom (forall r: real :: { real_to_integer_64(r) } is_integer_64(int(r)) ==> real_to_integer_64(r) == int(r));
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

const unique ARITHMETIC: Type;

axiom ((ARITHMETIC) <: (ANY));

axiom ((forall t: Type :: { (ARITHMETIC) <: (t) } ((ARITHMETIC) <: (t)) <==> (((t) == (ARITHMETIC)) || ((ANY) <: (t)))));

axiom ((FieldId(allocated, ARITHMETIC)) == (-1));

axiom ((FieldId(closed, ARITHMETIC)) == (-2));

axiom ((FieldId(owner, ARITHMETIC)) == (-3));

axiom ((FieldId(owns, ARITHMETIC)) == (-4));

axiom ((FieldId(observers, ARITHMETIC)) == (-5));

axiom ((FieldId(subjects, ARITHMETIC)) == (-6));

axiom ((forall <T0> $f: Field T0 :: { IsModelField($f, ARITHMETIC) } (IsModelField($f, ARITHMETIC)) <==> ((($f) == (subjects)) || (($f) == (observers)))));

function { :inline } ARITHMETIC.user_inv(heap: HeapType, current: ref) returns (bool) {
  (Set#IsEmpty(heap[current, observers])) && (Set#IsEmpty(heap[current, subjects])) && (Set#IsEmpty(heap[current, owns])) && (admissibility2(heap, current))
}

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached_exact(heap, current, ARITHMETIC)) ==> ((user_inv(heap, current)) <==> (ARITHMETIC.user_inv(heap, current)))));

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached(heap, current, ARITHMETIC)) ==> ((user_inv(heap, current)) ==> (ARITHMETIC.user_inv(heap, current)))));

procedure ARITHMETIC.invariant_admissibility_check(Current: ref);
  requires attached_exact(Heap, Current, ARITHMETIC);



implementation ARITHMETIC.invariant_admissibility_check(Current: ref)
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

procedure create.ARITHMETIC.default_create(Current: ref);
  free requires attached_exact(Heap, Current, ARITHMETIC); // info:type property for argument Current
  modifies Heap;
  requires (forall <T2> $f: Field T2 :: (($f) != (allocated)) ==> ((Heap[Current, $f]) == (Default($f))));
  ensures (forall <T3> $f: Field T3 :: ((($f) != (allocated)) && (($f) != (closed))) ==> ((Heap[Current, $f]) == (Default($f))));
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.ARITHMETIC.default_create(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.ARITHMETIC.default_create(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts



implementation create.ARITHMETIC.default_create(Current: ref)
{
  entry:
  assume {:captureState "create.ARITHMETIC.default_create"} true;
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

procedure ARITHMETIC.add(Current: ref, a: int, b: int) returns (Result: int where is_integer_32(Result));
  free requires attached_exact(Heap, Current, ARITHMETIC); // info:type property for argument Current
  free requires is_integer_32(a); // info:type property for argument a
  free requires is_integer_32(b); // info:type property for argument b
  modifies Heap;
  ensures (Result) == ((a) + (b)); // type:post tag:result_correct line:47
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.ARITHMETIC.add(Heap, Current, a, b), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.ARITHMETIC.add(old(Heap), Current, a, b));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.ARITHMETIC.add(Heap, Current, a, b), readable);
  requires is_closed(Heap, Current); // type:pre tag:default_is_closed default:contracts
  free ensures (Result) == (fun.ARITHMETIC.add(old(Heap), Current, a, b));



function fun.ARITHMETIC.add(heap: HeapType, current: ref, a: int, b: int) returns (int);

axiom ((forall heap: HeapType, current: ref, a: int, b: int :: { fun.ARITHMETIC.add(heap, current, a, b) } (pre.fun.ARITHMETIC.add(heap, current, a, b)) ==> (((fun.ARITHMETIC.add(heap, current, a, b)) == ((a) + (b))) && (is_integer_32(fun.ARITHMETIC.add(heap, current, a, b))))));

axiom ((forall h: HeapType, h': HeapType, current: ref, a: int, b: int :: { HeapSucc(h, h'), fun.ARITHMETIC.add(h, current, a, b), fun.ARITHMETIC.add(h', current, a, b) } ((HeapSucc(h, h')) && (pre.fun.ARITHMETIC.add(h, current, a, b)) && (pre.fun.ARITHMETIC.add(h', current, a, b)) && (same_inside(h, h', read.fun.ARITHMETIC.add(h, current, a, b)))) ==> ((fun.ARITHMETIC.add(h, current, a, b)) == (fun.ARITHMETIC.add(h', current, a, b)))));

function { :inline } variant.ARITHMETIC.add.1(heap: HeapType, current: ref, a: int, b: int) returns (int) {
  a
}

function { :inline } variant.ARITHMETIC.add.2(heap: HeapType, current: ref, a: int, b: int) returns (int) {
  b
}

implementation ARITHMETIC.add(Current: ref, a: int, b: int) returns (Result: int)
{
  var PreLoopHeap_4: HeapType;
  var variant_5: int;
  var PreLoopHeap_9: HeapType;
  var variant_10: int;
  var local1: int where is_integer_32(local1);

  init_locals:
  variant_5 := 0;
  variant_10 := 0;
  local1 := 0;
  Result := 0;

  entry:
  assume {:captureState "ARITHMETIC.add"} true;
  // /home/caf/temp/comcom/repo-arithmetic/arithmetic.e:15
  // if b >= 0 then
  if ((b) >= (0)) {
    // /home/caf/temp/comcom/repo-arithmetic/arithmetic.e:17
    // Result := a
    Result := a;
    // /home/caf/temp/comcom/repo-arithmetic/arithmetic.e:18
    // i := b
    local1 := b;
    PreLoopHeap_4 := Heap;
    goto loop_head_1;
    loop_head_1:
    // /home/caf/temp/comcom/repo-arithmetic/arithmetic.e:20
    // Result = a + (b - i)
    assert (Result) == ((a) + ((b) - (local1))); // type:loop_inv line:20
    // /home/caf/temp/comcom/repo-arithmetic/arithmetic.e:21
    // 0 <= i and i <= b
    assert ((0) <= (local1)) && ((local1) <= (b)); // type:loop_inv line:21
    assume HeapSucc(PreLoopHeap_4, Heap);
    assume same_outside(old(Heap), Heap, modify.ARITHMETIC.add(old(Heap), Current, a, b));
    assume global(Heap);
    // /home/caf/temp/comcom/repo-arithmetic/arithmetic.e:-1
    goto loop_body_2, loop_end_3;
    loop_body_2:
    assume !((local1) == (0));
    // /home/caf/temp/comcom/repo-arithmetic/arithmetic.e:28
    // i
    variant_5 := local1;
    // /home/caf/temp/comcom/repo-arithmetic/arithmetic.e:25
    // Result := Result + 1
    Result := (Result) + (1);
    // /home/caf/temp/comcom/repo-arithmetic/arithmetic.e:26
    // i := i - 1
    local1 := (local1) - (1);
    // /home/caf/temp/comcom/repo-arithmetic/arithmetic.e:28
    // i
    assert {:subsumption 0} (((local1) <= (variant_5)) && ((variant_5) <= (local1))) || ((0) <= (variant_5)); // type:termination tag:bounded line:28 varid:1
    assert {:subsumption 0} ((local1) <= (variant_5)) && (!((variant_5) <= (local1))); // type:termination tag:variant_decreases line:28
    goto loop_head_1;
    loop_end_3:
    assume (local1) == (0);
  } else {
    // /home/caf/temp/comcom/repo-arithmetic/arithmetic.e:32
    // Result := a
    Result := a;
    // /home/caf/temp/comcom/repo-arithmetic/arithmetic.e:33
    // i := b
    local1 := b;
    PreLoopHeap_9 := Heap;
    goto loop_head_6;
    loop_head_6:
    // /home/caf/temp/comcom/repo-arithmetic/arithmetic.e:35
    // Result = a + (b - i)
    assert (Result) == ((a) + ((b) - (local1))); // type:loop_inv line:35
    // /home/caf/temp/comcom/repo-arithmetic/arithmetic.e:36
    // b <= i and i <= 0
    assert ((b) <= (local1)) && ((local1) <= (0)); // type:loop_inv line:36
    assume HeapSucc(PreLoopHeap_9, Heap);
    assume same_outside(old(Heap), Heap, modify.ARITHMETIC.add(old(Heap), Current, a, b));
    assume global(Heap);
    // /home/caf/temp/comcom/repo-arithmetic/arithmetic.e:-1
    goto loop_body_7, loop_end_8;
    loop_body_7:
    assume !((local1) == (0));
    // /home/caf/temp/comcom/repo-arithmetic/arithmetic.e:43
    // -i
    variant_10 := -(local1);
    // /home/caf/temp/comcom/repo-arithmetic/arithmetic.e:40
    // Result := Result - 1
    Result := (Result) - (1);
    // /home/caf/temp/comcom/repo-arithmetic/arithmetic.e:41
    // i := i + 1
    local1 := (local1) + (1);
    // /home/caf/temp/comcom/repo-arithmetic/arithmetic.e:43
    // -i
    assert {:subsumption 0} (((-(local1)) <= (variant_10)) && ((variant_10) <= (-(local1)))) || ((0) <= (variant_10)); // type:termination tag:bounded line:43 varid:1
    assert {:subsumption 0} ((-(local1)) <= (variant_10)) && (!((variant_10) <= (-(local1)))); // type:termination tag:variant_decreases line:43
    goto loop_head_6;
    loop_end_8:
    assume (local1) == (0);
  }
}

procedure ARITHMETIC.add_recursive(Current: ref, a: int, b: int) returns (Result: int where is_integer_32(Result));
  free requires attached_exact(Heap, Current, ARITHMETIC); // info:type property for argument Current
  free requires is_integer_32(a); // info:type property for argument a
  free requires is_integer_32(b); // info:type property for argument b
  modifies Heap;
  ensures (Result) == ((a) + (b)); // type:post tag:result_correct line:64
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.ARITHMETIC.add_recursive(Heap, Current, a, b), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.ARITHMETIC.add_recursive(old(Heap), Current, a, b));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.ARITHMETIC.add_recursive(Heap, Current, a, b), readable);
  requires is_closed(Heap, Current); // type:pre tag:default_is_closed default:contracts
  free ensures (Result) == (fun.ARITHMETIC.add_recursive(old(Heap), Current, a, b));



function fun.ARITHMETIC.add_recursive(heap: HeapType, current: ref, a: int, b: int) returns (int);

axiom ((forall heap: HeapType, current: ref, a: int, b: int :: { fun.ARITHMETIC.add_recursive(heap, current, a, b) } (pre.fun.ARITHMETIC.add_recursive(heap, current, a, b)) ==> (((fun.ARITHMETIC.add_recursive(heap, current, a, b)) == ((a) + (b))) && (is_integer_32(fun.ARITHMETIC.add_recursive(heap, current, a, b))))));

axiom ((forall h: HeapType, h': HeapType, current: ref, a: int, b: int :: { HeapSucc(h, h'), fun.ARITHMETIC.add_recursive(h, current, a, b), fun.ARITHMETIC.add_recursive(h', current, a, b) } ((HeapSucc(h, h')) && (pre.fun.ARITHMETIC.add_recursive(h, current, a, b)) && (pre.fun.ARITHMETIC.add_recursive(h', current, a, b)) && (same_inside(h, h', read.fun.ARITHMETIC.add_recursive(h, current, a, b)))) ==> ((fun.ARITHMETIC.add_recursive(h, current, a, b)) == (fun.ARITHMETIC.add_recursive(h', current, a, b)))));

function { :inline } variant.ARITHMETIC.add_recursive.1(heap: HeapType, current: ref, a: int, b: int) returns (int) {
  (if (b) < (0) then -(b) else b)
}

implementation ARITHMETIC.add_recursive(Current: ref, a: int, b: int) returns (Result: int)
{
  var temp_11: int;
  var temp_12: int;

  init_locals:
  temp_11 := 0;
  temp_12 := 0;
  Result := 0;

  entry:
  assume {:captureState "ARITHMETIC.add_recursive"} true;
  // /home/caf/temp/comcom/repo-arithmetic/arithmetic.e:56
  // if b = 0 then
  if ((b) == (0)) {
    // /home/caf/temp/comcom/repo-arithmetic/arithmetic.e:57
    // Result := a
    Result := a;
  } else {
    // /home/caf/temp/comcom/repo-arithmetic/arithmetic.e:58
    // elseif b > 0 then
    if ((b) > (0)) {
      // /home/caf/temp/comcom/repo-arithmetic/arithmetic.e:59
      // Result := add_recursive (a, b - 1) + 1
      assert Frame#Subset(read.fun.ARITHMETIC.add_recursive(Heap, Current, a, (b) - (1)), readable); // type:access tag:frame_readable line:59 cid:404 rid:5402
      assert {:subsumption 0} (((variant.ARITHMETIC.add_recursive.1(Heap, Current, a, (b) - (1))) <= (variant.ARITHMETIC.add_recursive.1(old(Heap), Current, a, b))) && ((variant.ARITHMETIC.add_recursive.1(old(Heap), Current, a, b)) <= (variant.ARITHMETIC.add_recursive.1(Heap, Current, a, (b) - (1))))) || ((0) <= (variant.ARITHMETIC.add_recursive.1(old(Heap), Current, a, b))); // type:termination tag:bounded line:59 varid:1
      assert {:subsumption 0} ((variant.ARITHMETIC.add_recursive.1(Heap, Current, a, (b) - (1))) <= (variant.ARITHMETIC.add_recursive.1(old(Heap), Current, a, b))) && (!((variant.ARITHMETIC.add_recursive.1(old(Heap), Current, a, b)) <= (variant.ARITHMETIC.add_recursive.1(Heap, Current, a, (b) - (1))))); // type:termination tag:variant_decreases line:59
      call temp_11 := ARITHMETIC.add_recursive(Current, a, (b) - (1)); // line:59 cid:404 rid:5402
      Result := (temp_11) + (1);
    } else {
      // /home/caf/temp/comcom/repo-arithmetic/arithmetic.e:61
      // Result := add_recursive (a, b + 1) - 1
      assert Frame#Subset(read.fun.ARITHMETIC.add_recursive(Heap, Current, a, (b) + (1)), readable); // type:access tag:frame_readable line:61 cid:404 rid:5402
      assert {:subsumption 0} (((variant.ARITHMETIC.add_recursive.1(Heap, Current, a, (b) + (1))) <= (variant.ARITHMETIC.add_recursive.1(old(Heap), Current, a, b))) && ((variant.ARITHMETIC.add_recursive.1(old(Heap), Current, a, b)) <= (variant.ARITHMETIC.add_recursive.1(Heap, Current, a, (b) + (1))))) || ((0) <= (variant.ARITHMETIC.add_recursive.1(old(Heap), Current, a, b))); // type:termination tag:bounded line:61 varid:1
      assert {:subsumption 0} ((variant.ARITHMETIC.add_recursive.1(Heap, Current, a, (b) + (1))) <= (variant.ARITHMETIC.add_recursive.1(old(Heap), Current, a, b))) && (!((variant.ARITHMETIC.add_recursive.1(old(Heap), Current, a, b)) <= (variant.ARITHMETIC.add_recursive.1(Heap, Current, a, (b) + (1))))); // type:termination tag:variant_decreases line:61
      call temp_12 := ARITHMETIC.add_recursive(Current, a, (b) + (1)); // line:61 cid:404 rid:5402
      Result := (temp_12) - (1);
    }
  }
}

procedure ARITHMETIC.multiply(Current: ref, a: int, b: int) returns (Result: int where is_integer_32(Result));
  free requires attached_exact(Heap, Current, ARITHMETIC); // info:type property for argument Current
  free requires is_integer_32(a); // info:type property for argument a
  free requires is_integer_32(b); // info:type property for argument b
  modifies Heap;
  requires (b) >= (0); // type:pre tag:b_not_negative line:73
  ensures (Result) == ((a) * (b)); // type:post tag:result_correct line:96
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.ARITHMETIC.multiply(Heap, Current, a, b), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.ARITHMETIC.multiply(old(Heap), Current, a, b));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.ARITHMETIC.multiply(Heap, Current, a, b), readable);
  requires is_closed(Heap, Current); // type:pre tag:default_is_closed default:contracts
  free ensures (Result) == (fun.ARITHMETIC.multiply(old(Heap), Current, a, b));



function fun.ARITHMETIC.multiply(heap: HeapType, current: ref, a: int, b: int) returns (int);

axiom ((forall heap: HeapType, current: ref, a: int, b: int :: { fun.ARITHMETIC.multiply(heap, current, a, b) } (pre.fun.ARITHMETIC.multiply(heap, current, a, b)) ==> (((fun.ARITHMETIC.multiply(heap, current, a, b)) == ((a) * (b))) && (is_integer_32(fun.ARITHMETIC.multiply(heap, current, a, b))))));

axiom ((forall h: HeapType, h': HeapType, current: ref, a: int, b: int :: { HeapSucc(h, h'), fun.ARITHMETIC.multiply(h, current, a, b), fun.ARITHMETIC.multiply(h', current, a, b) } ((HeapSucc(h, h')) && (pre.fun.ARITHMETIC.multiply(h, current, a, b)) && (pre.fun.ARITHMETIC.multiply(h', current, a, b)) && (same_inside(h, h', read.fun.ARITHMETIC.multiply(h, current, a, b)))) ==> ((fun.ARITHMETIC.multiply(h, current, a, b)) == (fun.ARITHMETIC.multiply(h', current, a, b)))));

function { :inline } variant.ARITHMETIC.multiply.1(heap: HeapType, current: ref, a: int, b: int) returns (int) {
  a
}

function { :inline } variant.ARITHMETIC.multiply.2(heap: HeapType, current: ref, a: int, b: int) returns (int) {
  b
}

implementation ARITHMETIC.multiply(Current: ref, a: int, b: int) returns (Result: int)
{
  var PreLoopHeap_16: HeapType;
  var variant_17: int;
  var temp_18: int;
  var local1: int where is_integer_32(local1);

  init_locals:
  variant_17 := 0;
  temp_18 := 0;
  local1 := 0;
  Result := 0;

  entry:
  assume {:captureState "ARITHMETIC.multiply"} true;
  // /home/caf/temp/comcom/repo-arithmetic/arithmetic.e:77
  // if a = 0 or b = 0 then
  if (((a) == (0)) || ((b) == (0))) {
    // /home/caf/temp/comcom/repo-arithmetic/arithmetic.e:78
    // Result := 0
    Result := 0;
  } else {
    // /home/caf/temp/comcom/repo-arithmetic/arithmetic.e:81
    // Result := a
    Result := a;
    // /home/caf/temp/comcom/repo-arithmetic/arithmetic.e:82
    // i := b
    local1 := b;
    PreLoopHeap_16 := Heap;
    goto loop_head_13;
    loop_head_13:
    // /home/caf/temp/comcom/repo-arithmetic/arithmetic.e:84
    // Result = a * (b - i + 1)
    assert (Result) == ((a) * (((b) - (local1)) + (1))); // type:loop_inv line:84
    // /home/caf/temp/comcom/repo-arithmetic/arithmetic.e:85
    // 1 <= i and i <= b
    assert ((1) <= (local1)) && ((local1) <= (b)); // type:loop_inv line:85
    assume HeapSucc(PreLoopHeap_16, Heap);
    assume same_outside(old(Heap), Heap, modify.ARITHMETIC.multiply(old(Heap), Current, a, b));
    assume global(Heap);
    // /home/caf/temp/comcom/repo-arithmetic/arithmetic.e:-1
    goto loop_body_14, loop_end_15;
    loop_body_14:
    assume !((local1) == (1));
    // /home/caf/temp/comcom/repo-arithmetic/arithmetic.e:92
    // i
    variant_17 := local1;
    // /home/caf/temp/comcom/repo-arithmetic/arithmetic.e:89
    // Result := add (Result, a)
    assert Frame#Subset(read.fun.ARITHMETIC.add(Heap, Current, Result, a), readable); // type:access tag:frame_readable line:89 cid:404 rid:5401
    call temp_18 := ARITHMETIC.add(Current, Result, a); // line:89 cid:404 rid:5401
    Result := temp_18;
    // /home/caf/temp/comcom/repo-arithmetic/arithmetic.e:90
    // i := i - 1
    local1 := (local1) - (1);
    // /home/caf/temp/comcom/repo-arithmetic/arithmetic.e:92
    // i
    assert {:subsumption 0} (((local1) <= (variant_17)) && ((variant_17) <= (local1))) || ((0) <= (variant_17)); // type:termination tag:bounded line:92 varid:1
    assert {:subsumption 0} ((local1) <= (variant_17)) && (!((variant_17) <= (local1))); // type:termination tag:variant_decreases line:92
    goto loop_head_13;
    loop_end_15:
    assume (local1) == (1);
  }
}

procedure ARITHMETIC.multiply_recursive(Current: ref, a: int, b: int) returns (Result: int where is_integer_32(Result));
  free requires attached_exact(Heap, Current, ARITHMETIC); // info:type property for argument Current
  free requires is_integer_32(a); // info:type property for argument a
  free requires is_integer_32(b); // info:type property for argument b
  modifies Heap;
  requires (b) >= (0); // type:pre tag:b_not_negative line:103
  ensures (Result) == ((a) * (b)); // type:post tag:result_correct line:115
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.ARITHMETIC.multiply_recursive(Heap, Current, a, b), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.ARITHMETIC.multiply_recursive(old(Heap), Current, a, b));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.ARITHMETIC.multiply_recursive(Heap, Current, a, b), readable);
  requires is_closed(Heap, Current); // type:pre tag:default_is_closed default:contracts
  free ensures (Result) == (fun.ARITHMETIC.multiply_recursive(old(Heap), Current, a, b));



function fun.ARITHMETIC.multiply_recursive(heap: HeapType, current: ref, a: int, b: int) returns (int);

axiom ((forall heap: HeapType, current: ref, a: int, b: int :: { fun.ARITHMETIC.multiply_recursive(heap, current, a, b) } (pre.fun.ARITHMETIC.multiply_recursive(heap, current, a, b)) ==> (((fun.ARITHMETIC.multiply_recursive(heap, current, a, b)) == ((a) * (b))) && (is_integer_32(fun.ARITHMETIC.multiply_recursive(heap, current, a, b))))));

axiom ((forall h: HeapType, h': HeapType, current: ref, a: int, b: int :: { HeapSucc(h, h'), fun.ARITHMETIC.multiply_recursive(h, current, a, b), fun.ARITHMETIC.multiply_recursive(h', current, a, b) } ((HeapSucc(h, h')) && (pre.fun.ARITHMETIC.multiply_recursive(h, current, a, b)) && (pre.fun.ARITHMETIC.multiply_recursive(h', current, a, b)) && (same_inside(h, h', read.fun.ARITHMETIC.multiply_recursive(h, current, a, b)))) ==> ((fun.ARITHMETIC.multiply_recursive(h, current, a, b)) == (fun.ARITHMETIC.multiply_recursive(h', current, a, b)))));

function { :inline } variant.ARITHMETIC.multiply_recursive.1(heap: HeapType, current: ref, a: int, b: int) returns (int) {
  a
}

function { :inline } variant.ARITHMETIC.multiply_recursive.2(heap: HeapType, current: ref, a: int, b: int) returns (int) {
  b
}

implementation ARITHMETIC.multiply_recursive(Current: ref, a: int, b: int) returns (Result: int)
{
  var temp_19: int;
  var temp_20: int;

  init_locals:
  temp_19 := 0;
  temp_20 := 0;
  Result := 0;

  entry:
  assume {:captureState "ARITHMETIC.multiply_recursive"} true;
  // /home/caf/temp/comcom/repo-arithmetic/arithmetic.e:105
  // if a = 0 or b = 0 then
  if (((a) == (0)) || ((b) == (0))) {
    // /home/caf/temp/comcom/repo-arithmetic/arithmetic.e:106
    // Result := 0
    Result := 0;
  } else {
    // /home/caf/temp/comcom/repo-arithmetic/arithmetic.e:108
    // if b = 1 then
    if ((b) == (1)) {
      // /home/caf/temp/comcom/repo-arithmetic/arithmetic.e:109
      // Result := a
      Result := a;
    } else {
      // /home/caf/temp/comcom/repo-arithmetic/arithmetic.e:111
      // Result := add_recursive (a, multiply (a, b-1))
      assert Frame#Subset(read.fun.ARITHMETIC.multiply(Heap, Current, a, (b) - (1)), readable); // type:access tag:frame_readable line:111 cid:404 rid:5403
      call temp_19 := ARITHMETIC.multiply(Current, a, (b) - (1)); // line:111 cid:404 rid:5403
      assert Frame#Subset(read.fun.ARITHMETIC.add_recursive(Heap, Current, a, temp_19), readable); // type:access tag:frame_readable line:111 cid:404 rid:5402
      call temp_20 := ARITHMETIC.add_recursive(Current, a, temp_19); // line:111 cid:404 rid:5402
      Result := temp_20;
    }
  }
}

procedure ARITHMETIC.divide(Current: ref, n: int, m: int) returns (Result: ref where detachable(Heap, Result, TUPLE^INTEGER_32#INTEGER_32^));
  free requires attached_exact(Heap, Current, ARITHMETIC); // info:type property for argument Current
  free requires is_integer_32(n); // info:type property for argument n
  free requires is_integer_32(m); // info:type property for argument m
  modifies Heap;
  requires (n) >= (0); // type:pre tag:n_not_negative line:124
  requires (m) > (0); // type:pre tag:m_positive line:125
  ensures (Result) != (Void); // type:attached line:145
  ensures (n) == (((m) * (Heap[Result, TUPLE^INTEGER_32#INTEGER_32^.field_1])) + (Heap[Result, TUPLE^INTEGER_32#INTEGER_32^.field_2])); // type:post line:145
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.ARITHMETIC.divide(Heap, Current, n, m), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.ARITHMETIC.divide(old(Heap), Current, n, m));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.ARITHMETIC.divide(Heap, Current, n, m), readable);
  requires is_closed(Heap, Current); // type:pre tag:default_is_closed default:contracts
  free ensures (Result) == (fun.ARITHMETIC.divide(old(Heap), Current, n, m));



function fun.ARITHMETIC.divide(heap: HeapType, current: ref, n: int, m: int) returns (ref);

axiom ((forall heap: HeapType, current: ref, n: int, m: int :: { fun.ARITHMETIC.divide(heap, current, n, m) } (pre.fun.ARITHMETIC.divide(heap, current, n, m)) ==> (((n) == (((m) * (heap[fun.ARITHMETIC.divide(heap, current, n, m), TUPLE^INTEGER_32#INTEGER_32^.field_1])) + (heap[fun.ARITHMETIC.divide(heap, current, n, m), TUPLE^INTEGER_32#INTEGER_32^.field_2]))) && (detachable(heap, fun.ARITHMETIC.divide(heap, current, n, m), TUPLE^INTEGER_32#INTEGER_32^)))));

axiom ((forall h: HeapType, h': HeapType, current: ref, n: int, m: int :: { HeapSucc(h, h'), fun.ARITHMETIC.divide(h, current, n, m), fun.ARITHMETIC.divide(h', current, n, m) } ((HeapSucc(h, h')) && (pre.fun.ARITHMETIC.divide(h, current, n, m)) && (pre.fun.ARITHMETIC.divide(h', current, n, m)) && (same_inside(h, h', read.fun.ARITHMETIC.divide(h, current, n, m)))) ==> ((fun.ARITHMETIC.divide(h, current, n, m)) == (fun.ARITHMETIC.divide(h', current, n, m)))));

function { :inline } variant.ARITHMETIC.divide.1(heap: HeapType, current: ref, n: int, m: int) returns (int) {
  n
}

function { :inline } variant.ARITHMETIC.divide.2(heap: HeapType, current: ref, n: int, m: int) returns (int) {
  m
}

implementation ARITHMETIC.divide(Current: ref, n: int, m: int) returns (Result: ref)
{
  var PreLoopHeap_24: HeapType;
  var variant_25: int;
  var temp_26: int;
  var temp_27: ref;
  var local1: int where is_integer_32(local1);
  var local2: int where is_integer_32(local2);

  init_locals:
  variant_25 := 0;
  temp_26 := 0;
  temp_27 := Void;
  local1 := 0;
  local2 := 0;
  Result := Void;

  entry:
  assume {:captureState "ARITHMETIC.divide"} true;
  // /home/caf/temp/comcom/repo-arithmetic/arithmetic.e:130
  // r := n
  local2 := n;
  // /home/caf/temp/comcom/repo-arithmetic/arithmetic.e:131
  // q := 0
  local1 := 0;
  PreLoopHeap_24 := Heap;
  goto loop_head_21;
  loop_head_21:
  // /home/caf/temp/comcom/repo-arithmetic/arithmetic.e:133
  // 0 <= r
  assert (0) <= (local2); // type:loop_inv line:133
  // /home/caf/temp/comcom/repo-arithmetic/arithmetic.e:134
  // n = m * q + r
  assert (n) == (((m) * (local1)) + (local2)); // type:loop_inv line:134
  assume HeapSucc(PreLoopHeap_24, Heap);
  assume same_outside(old(Heap), Heap, modify.ARITHMETIC.divide(old(Heap), Current, n, m));
  assume global(Heap);
  // /home/caf/temp/comcom/repo-arithmetic/arithmetic.e:-1
  goto loop_body_22, loop_end_23;
  loop_body_22:
  assume !((local2) < (m));
  // /home/caf/temp/comcom/repo-arithmetic/arithmetic.e:141
  // r
  variant_25 := local2;
  // /home/caf/temp/comcom/repo-arithmetic/arithmetic.e:138
  // r := add (r, -m)
  assert Frame#Subset(read.fun.ARITHMETIC.add(Heap, Current, local2, -(m)), readable); // type:access tag:frame_readable line:138 cid:404 rid:5401
  call temp_26 := ARITHMETIC.add(Current, local2, -(m)); // line:138 cid:404 rid:5401
  local2 := temp_26;
  // /home/caf/temp/comcom/repo-arithmetic/arithmetic.e:139
  // q := q + 1
  local1 := (local1) + (1);
  // /home/caf/temp/comcom/repo-arithmetic/arithmetic.e:141
  // r
  assert {:subsumption 0} (((local2) <= (variant_25)) && ((variant_25) <= (local2))) || ((0) <= (variant_25)); // type:termination tag:bounded line:141 varid:1
  assert {:subsumption 0} ((local2) <= (variant_25)) && (!((variant_25) <= (local2))); // type:termination tag:variant_decreases line:141
  goto loop_head_21;
  loop_end_23:
  assume (local2) < (m);
  // /home/caf/temp/comcom/repo-arithmetic/arithmetic.e:143
  // Result := [q ,r]
  call temp_27 := allocate(TUPLE^INTEGER_32#INTEGER_32^); // line:-1
  call create.TUPLE^INTEGER_32#INTEGER_32^.make(temp_27, local1, local2);
  Result := temp_27;
}

procedure ARITHMETIC.divide_recursive(Current: ref, n: int, m: int) returns (Result: ref where detachable(Heap, Result, TUPLE^INTEGER_32#INTEGER_32^));
  free requires attached_exact(Heap, Current, ARITHMETIC); // info:type property for argument Current
  free requires is_integer_32(n); // info:type property for argument n
  free requires is_integer_32(m); // info:type property for argument m
  modifies Heap;
  requires (n) >= (0); // type:pre tag:n_not_negative line:152
  requires (m) > (0); // type:pre tag:m_positive line:153
  ensures (Result) != (Void); // type:attached line:165
  ensures (n) == (((m) * (Heap[Result, TUPLE^INTEGER_32#INTEGER_32^.field_1])) + (Heap[Result, TUPLE^INTEGER_32#INTEGER_32^.field_2])); // type:post line:165
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.ARITHMETIC.divide_recursive(Heap, Current, n, m), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.ARITHMETIC.divide_recursive(old(Heap), Current, n, m));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.ARITHMETIC.divide_recursive(Heap, Current, n, m), readable);
  requires is_closed(Heap, Current); // type:pre tag:default_is_closed default:contracts
  free ensures (Result) == (fun.ARITHMETIC.divide_recursive(old(Heap), Current, n, m));



function fun.ARITHMETIC.divide_recursive(heap: HeapType, current: ref, n: int, m: int) returns (ref);

axiom ((forall heap: HeapType, current: ref, n: int, m: int :: { fun.ARITHMETIC.divide_recursive(heap, current, n, m) } (pre.fun.ARITHMETIC.divide_recursive(heap, current, n, m)) ==> (((n) == (((m) * (heap[fun.ARITHMETIC.divide_recursive(heap, current, n, m), TUPLE^INTEGER_32#INTEGER_32^.field_1])) + (heap[fun.ARITHMETIC.divide_recursive(heap, current, n, m), TUPLE^INTEGER_32#INTEGER_32^.field_2]))) && (detachable(heap, fun.ARITHMETIC.divide_recursive(heap, current, n, m), TUPLE^INTEGER_32#INTEGER_32^)))));

axiom ((forall h: HeapType, h': HeapType, current: ref, n: int, m: int :: { HeapSucc(h, h'), fun.ARITHMETIC.divide_recursive(h, current, n, m), fun.ARITHMETIC.divide_recursive(h', current, n, m) } ((HeapSucc(h, h')) && (pre.fun.ARITHMETIC.divide_recursive(h, current, n, m)) && (pre.fun.ARITHMETIC.divide_recursive(h', current, n, m)) && (same_inside(h, h', read.fun.ARITHMETIC.divide_recursive(h, current, n, m)))) ==> ((fun.ARITHMETIC.divide_recursive(h, current, n, m)) == (fun.ARITHMETIC.divide_recursive(h', current, n, m)))));

function { :inline } variant.ARITHMETIC.divide_recursive.1(heap: HeapType, current: ref, n: int, m: int) returns (int) {
  n
}

function { :inline } variant.ARITHMETIC.divide_recursive.2(heap: HeapType, current: ref, n: int, m: int) returns (int) {
  m
}

implementation ARITHMETIC.divide_recursive(Current: ref, n: int, m: int) returns (Result: ref)
{
  var temp_28: ref;
  var temp_29: int;
  var temp_30: ref;
  var temp_31: ref;
  var local3: ref where detachable(Heap, local3, TUPLE^INTEGER_32#INTEGER_32^);

  init_locals:
  temp_28 := Void;
  temp_29 := 0;
  temp_30 := Void;
  temp_31 := Void;
  local3 := Void;
  Result := Void;

  entry:
  assume {:captureState "ARITHMETIC.divide_recursive"} true;
  // /home/caf/temp/comcom/repo-arithmetic/arithmetic.e:158
  // if n < m then
  if ((n) < (m)) {
    // /home/caf/temp/comcom/repo-arithmetic/arithmetic.e:159
    // Result := [0, n]
    call temp_28 := allocate(TUPLE^INTEGER_32#INTEGER_32^); // line:-1
    call create.TUPLE^INTEGER_32#INTEGER_32^.make(temp_28, 0, n);
    Result := temp_28;
  } else {
    // /home/caf/temp/comcom/repo-arithmetic/arithmetic.e:161
    // res := divide_recursive (add_recursive (n, -m), m)
    assert Frame#Subset(read.fun.ARITHMETIC.add_recursive(Heap, Current, n, -(m)), readable); // type:access tag:frame_readable line:161 cid:404 rid:5402
    call temp_29 := ARITHMETIC.add_recursive(Current, n, -(m)); // line:161 cid:404 rid:5402
    assert Frame#Subset(read.fun.ARITHMETIC.divide_recursive(Heap, Current, temp_29, m), readable); // type:access tag:frame_readable line:161 cid:404 rid:5406
    assert {:subsumption 0} (((variant.ARITHMETIC.divide_recursive.1(Heap, Current, temp_29, m)) <= (variant.ARITHMETIC.divide_recursive.1(old(Heap), Current, n, m))) && ((variant.ARITHMETIC.divide_recursive.1(old(Heap), Current, n, m)) <= (variant.ARITHMETIC.divide_recursive.1(Heap, Current, temp_29, m)))) || ((0) <= (variant.ARITHMETIC.divide_recursive.1(old(Heap), Current, n, m))); // type:termination tag:bounded line:161 varid:1
    assert {:subsumption 0} (((variant.ARITHMETIC.divide_recursive.1(Heap, Current, temp_29, m)) <= (variant.ARITHMETIC.divide_recursive.1(old(Heap), Current, n, m))) && (!((variant.ARITHMETIC.divide_recursive.1(old(Heap), Current, n, m)) <= (variant.ARITHMETIC.divide_recursive.1(Heap, Current, temp_29, m))))) || (((variant.ARITHMETIC.divide_recursive.2(Heap, Current, temp_29, m)) <= (variant.ARITHMETIC.divide_recursive.2(old(Heap), Current, n, m))) && ((variant.ARITHMETIC.divide_recursive.2(old(Heap), Current, n, m)) <= (variant.ARITHMETIC.divide_recursive.2(Heap, Current, temp_29, m)))) || ((0) <= (variant.ARITHMETIC.divide_recursive.2(old(Heap), Current, n, m))); // type:termination tag:bounded line:161 varid:2
    assert {:subsumption 0} (((variant.ARITHMETIC.divide_recursive.1(Heap, Current, temp_29, m)) <= (variant.ARITHMETIC.divide_recursive.1(old(Heap), Current, n, m))) && (!((variant.ARITHMETIC.divide_recursive.1(old(Heap), Current, n, m)) <= (variant.ARITHMETIC.divide_recursive.1(Heap, Current, temp_29, m))))) || (((variant.ARITHMETIC.divide_recursive.1(Heap, Current, temp_29, m)) <= (variant.ARITHMETIC.divide_recursive.1(old(Heap), Current, n, m))) && ((variant.ARITHMETIC.divide_recursive.1(old(Heap), Current, n, m)) <= (variant.ARITHMETIC.divide_recursive.1(Heap, Current, temp_29, m))) && ((variant.ARITHMETIC.divide_recursive.2(Heap, Current, temp_29, m)) <= (variant.ARITHMETIC.divide_recursive.2(old(Heap), Current, n, m))) && (!((variant.ARITHMETIC.divide_recursive.2(old(Heap), Current, n, m)) <= (variant.ARITHMETIC.divide_recursive.2(Heap, Current, temp_29, m))))); // type:termination tag:variant_decreases line:161
    call temp_30 := ARITHMETIC.divide_recursive(Current, temp_29, m); // line:161 cid:404 rid:5406
    local3 := temp_30;
    // /home/caf/temp/comcom/repo-arithmetic/arithmetic.e:162
    // Result := [res.quotient + 1, res.remainder]
    assert {:subsumption 0} (local3) != (Void); // type:attached line:162
    assert {:subsumption 0} (local3) != (Void); // type:attached line:162
    call temp_31 := allocate(TUPLE^INTEGER_32#INTEGER_32^); // line:-1
    call create.TUPLE^INTEGER_32#INTEGER_32^.make(temp_31, (Heap[local3, TUPLE^INTEGER_32#INTEGER_32^.field_1]) + (1), Heap[local3, TUPLE^INTEGER_32#INTEGER_32^.field_2]);
    Result := temp_31;
  }
}

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, owns, v, o) } (attached_exact(heap, current, ANY)) ==> ((guard(heap, current, owns, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, subjects, v, o) } (attached_exact(heap, current, ANY)) ==> ((guard(heap, current, subjects, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached_exact(heap, current, ANY)) ==> ((guard(heap, current, observers, v, o)) <==> (fun.ANY.in_observers(heap, current, v, o)))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached(heap, current, ANY)) ==> ((guard(heap, current, observers, v, o)) ==> (fun.ANY.in_observers(heap, current, v, o)))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, owns, v, o) } (attached_exact(heap, current, ARITHMETIC)) ==> ((guard(heap, current, owns, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, subjects, v, o) } (attached_exact(heap, current, ARITHMETIC)) ==> ((guard(heap, current, subjects, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached_exact(heap, current, ARITHMETIC)) ==> ((guard(heap, current, observers, v, o)) <==> (fun.ARITHMETIC.in_observers(heap, current, v, o)))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached(heap, current, ARITHMETIC)) ==> ((guard(heap, current, observers, v, o)) ==> (fun.ARITHMETIC.in_observers(heap, current, v, o)))));

function modify.ARITHMETIC.default_create(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T5> $o: ref, $f: Field T5 :: { modify.ARITHMETIC.default_create(heap, current)[$o, $f] } (modify.ARITHMETIC.default_create(heap, current)[$o, $f]) <==> (($o) == (current))))));

function modify.ARITHMETIC.add(heap: HeapType, current: ref, a: int, b: int) returns (Frame);

axiom ((forall heap: HeapType, current: ref, a: int, b: int :: (IsHeap(heap)) ==> ((forall <T6> $o: ref, $f: Field T6 :: { modify.ARITHMETIC.add(heap, current, a, b)[$o, $f] } (modify.ARITHMETIC.add(heap, current, a, b)[$o, $f]) <==> (false)))));

function read.fun.ARITHMETIC.add(heap: HeapType, current: ref, a: int, b: int) returns (Frame);

axiom ((forall heap: HeapType, current: ref, a: int, b: int :: (IsHeap(heap)) ==> ((forall <T7> $o: ref, $f: Field T7 :: { read.fun.ARITHMETIC.add(heap, current, a, b)[$o, $f] } (read.fun.ARITHMETIC.add(heap, current, a, b)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.ARITHMETIC.add(heap: HeapType, current: ref, a: int, b: int) returns (bool) {
  is_closed(heap, current)
}

function trigger.fun.ARITHMETIC.add(heap: HeapType, current: ref, a: int, b: int) returns (bool);

function modify.ARITHMETIC.add_recursive(heap: HeapType, current: ref, a: int, b: int) returns (Frame);

axiom ((forall heap: HeapType, current: ref, a: int, b: int :: (IsHeap(heap)) ==> ((forall <T8> $o: ref, $f: Field T8 :: { modify.ARITHMETIC.add_recursive(heap, current, a, b)[$o, $f] } (modify.ARITHMETIC.add_recursive(heap, current, a, b)[$o, $f]) <==> (false)))));

function read.fun.ARITHMETIC.add_recursive(heap: HeapType, current: ref, a: int, b: int) returns (Frame);

axiom ((forall heap: HeapType, current: ref, a: int, b: int :: (IsHeap(heap)) ==> ((forall <T9> $o: ref, $f: Field T9 :: { read.fun.ARITHMETIC.add_recursive(heap, current, a, b)[$o, $f] } (read.fun.ARITHMETIC.add_recursive(heap, current, a, b)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.ARITHMETIC.add_recursive(heap: HeapType, current: ref, a: int, b: int) returns (bool) {
  is_closed(heap, current)
}

function trigger.fun.ARITHMETIC.add_recursive(heap: HeapType, current: ref, a: int, b: int) returns (bool);

function modify.ARITHMETIC.multiply(heap: HeapType, current: ref, a: int, b: int) returns (Frame);

axiom ((forall heap: HeapType, current: ref, a: int, b: int :: (IsHeap(heap)) ==> ((forall <T10> $o: ref, $f: Field T10 :: { modify.ARITHMETIC.multiply(heap, current, a, b)[$o, $f] } (modify.ARITHMETIC.multiply(heap, current, a, b)[$o, $f]) <==> (false)))));

function read.fun.ARITHMETIC.multiply(heap: HeapType, current: ref, a: int, b: int) returns (Frame);

axiom ((forall heap: HeapType, current: ref, a: int, b: int :: (IsHeap(heap)) ==> ((forall <T11> $o: ref, $f: Field T11 :: { read.fun.ARITHMETIC.multiply(heap, current, a, b)[$o, $f] } (read.fun.ARITHMETIC.multiply(heap, current, a, b)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.ARITHMETIC.multiply(heap: HeapType, current: ref, a: int, b: int) returns (bool) {
  ((b) >= (0)) && (is_closed(heap, current))
}

function trigger.fun.ARITHMETIC.multiply(heap: HeapType, current: ref, a: int, b: int) returns (bool);

function modify.ARITHMETIC.multiply_recursive(heap: HeapType, current: ref, a: int, b: int) returns (Frame);

axiom ((forall heap: HeapType, current: ref, a: int, b: int :: (IsHeap(heap)) ==> ((forall <T12> $o: ref, $f: Field T12 :: { modify.ARITHMETIC.multiply_recursive(heap, current, a, b)[$o, $f] } (modify.ARITHMETIC.multiply_recursive(heap, current, a, b)[$o, $f]) <==> (false)))));

function read.fun.ARITHMETIC.multiply_recursive(heap: HeapType, current: ref, a: int, b: int) returns (Frame);

axiom ((forall heap: HeapType, current: ref, a: int, b: int :: (IsHeap(heap)) ==> ((forall <T13> $o: ref, $f: Field T13 :: { read.fun.ARITHMETIC.multiply_recursive(heap, current, a, b)[$o, $f] } (read.fun.ARITHMETIC.multiply_recursive(heap, current, a, b)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.ARITHMETIC.multiply_recursive(heap: HeapType, current: ref, a: int, b: int) returns (bool) {
  ((b) >= (0)) && (is_closed(heap, current))
}

function trigger.fun.ARITHMETIC.multiply_recursive(heap: HeapType, current: ref, a: int, b: int) returns (bool);

const unique TUPLE^INTEGER_32#INTEGER_32^: Type;

const TUPLE^INTEGER_32#INTEGER_32^.field_1: Field int;

axiom ((FieldId(TUPLE^INTEGER_32#INTEGER_32^.field_1, TUPLE^INTEGER_32#INTEGER_32^)) == (1));

axiom ((forall heap: HeapType, o: ref :: { heap[o, TUPLE^INTEGER_32#INTEGER_32^.field_1] } ((IsHeap(heap)) && (attached(heap, o, TUPLE^INTEGER_32#INTEGER_32^))) ==> (is_integer_32(heap[o, TUPLE^INTEGER_32#INTEGER_32^.field_1]))));

const TUPLE^INTEGER_32#INTEGER_32^.field_2: Field int;

axiom ((FieldId(TUPLE^INTEGER_32#INTEGER_32^.field_2, TUPLE^INTEGER_32#INTEGER_32^)) == (2));

axiom ((forall heap: HeapType, o: ref :: { heap[o, TUPLE^INTEGER_32#INTEGER_32^.field_2] } ((IsHeap(heap)) && (attached(heap, o, TUPLE^INTEGER_32#INTEGER_32^))) ==> (is_integer_32(heap[o, TUPLE^INTEGER_32#INTEGER_32^.field_2]))));

procedure create.TUPLE^INTEGER_32#INTEGER_32^.make(Current: ref, f_1: int, f_2: int);
  free requires attached_exact(Heap, Current, TUPLE^INTEGER_32#INTEGER_32^); // info:type property for argument Current
  free requires is_integer_32(f_1); // info:type property for argument f_1
  ensures (Heap[Current, TUPLE^INTEGER_32#INTEGER_32^.field_1]) == (f_1);
  free requires is_integer_32(f_2); // info:type property for argument f_2
  ensures (Heap[Current, TUPLE^INTEGER_32#INTEGER_32^.field_2]) == (f_2);
  modifies Heap;
  requires (forall <T14> $f: Field T14 :: (($f) != (allocated)) ==> ((Heap[Current, $f]) == (Default($f))));
  ensures is_wrapped(Heap, Current);
  ensures global(Heap);
  ensures same_outside(old(Heap), Heap, Frame#Singleton(Current));
  ensures HeapSucc(old(Heap), Heap);



axiom ((FieldId(allocated, TUPLE^INTEGER_32#INTEGER_32^)) == (-1));

axiom ((FieldId(closed, TUPLE^INTEGER_32#INTEGER_32^)) == (-2));

axiom ((FieldId(owner, TUPLE^INTEGER_32#INTEGER_32^)) == (-3));

axiom ((FieldId(owns, TUPLE^INTEGER_32#INTEGER_32^)) == (-4));

axiom ((FieldId(observers, TUPLE^INTEGER_32#INTEGER_32^)) == (-5));

axiom ((FieldId(subjects, TUPLE^INTEGER_32#INTEGER_32^)) == (-6));

function { :inline } TUPLE^INTEGER_32#INTEGER_32^.user_inv(heap: HeapType, current: ref) returns (bool) {
  (Set#IsEmpty(heap[current, observers])) && (Set#IsEmpty(heap[current, subjects])) && (Set#IsEmpty(heap[current, owns]))
}

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached_exact(heap, current, TUPLE^INTEGER_32#INTEGER_32^)) ==> ((user_inv(heap, current)) <==> (TUPLE^INTEGER_32#INTEGER_32^.user_inv(heap, current)))));

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached(heap, current, TUPLE^INTEGER_32#INTEGER_32^)) ==> ((user_inv(heap, current)) ==> (TUPLE^INTEGER_32#INTEGER_32^.user_inv(heap, current)))));

function modify.ARITHMETIC.divide(heap: HeapType, current: ref, n: int, m: int) returns (Frame);

axiom ((forall heap: HeapType, current: ref, n: int, m: int :: (IsHeap(heap)) ==> ((forall <T15> $o: ref, $f: Field T15 :: { modify.ARITHMETIC.divide(heap, current, n, m)[$o, $f] } (modify.ARITHMETIC.divide(heap, current, n, m)[$o, $f]) <==> (false)))));

function read.fun.ARITHMETIC.divide(heap: HeapType, current: ref, n: int, m: int) returns (Frame);

axiom ((forall heap: HeapType, current: ref, n: int, m: int :: (IsHeap(heap)) ==> ((forall <T16> $o: ref, $f: Field T16 :: { read.fun.ARITHMETIC.divide(heap, current, n, m)[$o, $f] } (read.fun.ARITHMETIC.divide(heap, current, n, m)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.ARITHMETIC.divide(heap: HeapType, current: ref, n: int, m: int) returns (bool) {
  ((n) >= (0)) && ((m) > (0)) && (is_closed(heap, current))
}

function trigger.fun.ARITHMETIC.divide(heap: HeapType, current: ref, n: int, m: int) returns (bool);

function modify.ARITHMETIC.divide_recursive(heap: HeapType, current: ref, n: int, m: int) returns (Frame);

axiom ((forall heap: HeapType, current: ref, n: int, m: int :: (IsHeap(heap)) ==> ((forall <T17> $o: ref, $f: Field T17 :: { modify.ARITHMETIC.divide_recursive(heap, current, n, m)[$o, $f] } (modify.ARITHMETIC.divide_recursive(heap, current, n, m)[$o, $f]) <==> (false)))));

function read.fun.ARITHMETIC.divide_recursive(heap: HeapType, current: ref, n: int, m: int) returns (Frame);

axiom ((forall heap: HeapType, current: ref, n: int, m: int :: (IsHeap(heap)) ==> ((forall <T18> $o: ref, $f: Field T18 :: { read.fun.ARITHMETIC.divide_recursive(heap, current, n, m)[$o, $f] } (read.fun.ARITHMETIC.divide_recursive(heap, current, n, m)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.ARITHMETIC.divide_recursive(heap: HeapType, current: ref, n: int, m: int) returns (bool) {
  ((n) >= (0)) && ((m) > (0)) && (is_closed(heap, current))
}

function trigger.fun.ARITHMETIC.divide_recursive(heap: HeapType, current: ref, n: int, m: int) returns (bool);

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

procedure ARITHMETIC.in_observers(Current: ref, new_observers: Set (ref), o: ref) returns (Result: bool where true);
  free requires attached_exact(Heap, Current, ARITHMETIC); // info:type property for argument Current
  free requires Set#ItemsType(Heap, new_observers, ANY); // info:type property for argument new_observers
  free requires Heap[o, allocated]; // info:type property for argument o
  modifies Heap;
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.ARITHMETIC.in_observers(Heap, Current, new_observers, o), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.ARITHMETIC.in_observers(old(Heap), Current, new_observers, o));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.ARITHMETIC.in_observers(Heap, Current, new_observers, o), readable);



function fun.ARITHMETIC.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function fun0.ARITHMETIC.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.ARITHMETIC.in_observers(heap, current, new_observers, o) } { trigger.fun.ARITHMETIC.in_observers(heap, current, new_observers, o) } (pre.fun.ARITHMETIC.in_observers(heap, current, new_observers, o)) ==> ((fun.ARITHMETIC.in_observers(heap, current, new_observers, o)) == (new_observers[o]))));

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.ARITHMETIC.in_observers(heap, current, new_observers, o) } (fun.ARITHMETIC.in_observers(heap, current, new_observers, o)) == (fun0.ARITHMETIC.in_observers(heap, current, new_observers, o))));

axiom ((forall h: HeapType, h': HeapType, current: ref, new_observers: Set (ref), o: ref :: { HeapSucc(h, h'), fun0.ARITHMETIC.in_observers(h, current, new_observers, o), fun0.ARITHMETIC.in_observers(h', current, new_observers, o) } ((HeapSucc(h, h')) && (pre.fun.ARITHMETIC.in_observers(h, current, new_observers, o)) && (pre.fun.ARITHMETIC.in_observers(h', current, new_observers, o)) && (same_inside(h, h', read.fun.ARITHMETIC.in_observers(h, current, new_observers, o)))) ==> ((fun0.ARITHMETIC.in_observers(h, current, new_observers, o)) == (fun0.ARITHMETIC.in_observers(h', current, new_observers, o)))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, owns, v, o) } (attached_exact(heap, current, TUPLE^INTEGER_32#INTEGER_32^)) ==> ((guard(heap, current, owns, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, subjects, v, o) } (attached_exact(heap, current, TUPLE^INTEGER_32#INTEGER_32^)) ==> ((guard(heap, current, subjects, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached_exact(heap, current, TUPLE^INTEGER_32#INTEGER_32^)) ==> ((guard(heap, current, observers, v, o)) <==> (fun.TUPLE^INTEGER_32#INTEGER_32^.in_observers(heap, current, v, o)))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached(heap, current, TUPLE^INTEGER_32#INTEGER_32^)) ==> ((guard(heap, current, observers, v, o)) ==> (fun.TUPLE^INTEGER_32#INTEGER_32^.in_observers(heap, current, v, o)))));

function modify.ANY.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T19> $o: ref, $f: Field T19 :: { modify.ANY.in_observers(heap, current, new_observers, o)[$o, $f] } (modify.ANY.in_observers(heap, current, new_observers, o)[$o, $f]) <==> (false)))));

function read.fun.ANY.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T20> $o: ref, $f: Field T20 :: { read.fun.ANY.in_observers(heap, current, new_observers, o)[$o, $f] } (read.fun.ANY.in_observers(heap, current, new_observers, o)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.ANY.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool) {
  true
}

function trigger.fun.ANY.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function modify.ARITHMETIC.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T21> $o: ref, $f: Field T21 :: { modify.ARITHMETIC.in_observers(heap, current, new_observers, o)[$o, $f] } (modify.ARITHMETIC.in_observers(heap, current, new_observers, o)[$o, $f]) <==> (false)))));

function read.fun.ARITHMETIC.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T22> $o: ref, $f: Field T22 :: { read.fun.ARITHMETIC.in_observers(heap, current, new_observers, o)[$o, $f] } (read.fun.ARITHMETIC.in_observers(heap, current, new_observers, o)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.ARITHMETIC.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool) {
  true
}

function trigger.fun.ARITHMETIC.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

procedure TUPLE^INTEGER_32#INTEGER_32^.in_observers(Current: ref, new_observers: Set (ref), o: ref) returns (Result: bool where true);
  free requires attached_exact(Heap, Current, TUPLE^INTEGER_32#INTEGER_32^); // info:type property for argument Current
  free requires Set#ItemsType(Heap, new_observers, ANY); // info:type property for argument new_observers
  free requires Heap[o, allocated]; // info:type property for argument o
  modifies Heap;
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.TUPLE^INTEGER_32#INTEGER_32^.in_observers(Heap, Current, new_observers, o), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.TUPLE^INTEGER_32#INTEGER_32^.in_observers(old(Heap), Current, new_observers, o));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.TUPLE^INTEGER_32#INTEGER_32^.in_observers(Heap, Current, new_observers, o), readable);



function fun.TUPLE^INTEGER_32#INTEGER_32^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function fun0.TUPLE^INTEGER_32#INTEGER_32^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.TUPLE^INTEGER_32#INTEGER_32^.in_observers(heap, current, new_observers, o) } { trigger.fun.TUPLE^INTEGER_32#INTEGER_32^.in_observers(heap, current, new_observers, o) } (pre.fun.TUPLE^INTEGER_32#INTEGER_32^.in_observers(heap, current, new_observers, o)) ==> ((fun.TUPLE^INTEGER_32#INTEGER_32^.in_observers(heap, current, new_observers, o)) == (new_observers[o]))));

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.TUPLE^INTEGER_32#INTEGER_32^.in_observers(heap, current, new_observers, o) } (fun.TUPLE^INTEGER_32#INTEGER_32^.in_observers(heap, current, new_observers, o)) == (fun0.TUPLE^INTEGER_32#INTEGER_32^.in_observers(heap, current, new_observers, o))));

axiom ((forall h: HeapType, h': HeapType, current: ref, new_observers: Set (ref), o: ref :: { HeapSucc(h, h'), fun0.TUPLE^INTEGER_32#INTEGER_32^.in_observers(h, current, new_observers, o), fun0.TUPLE^INTEGER_32#INTEGER_32^.in_observers(h', current, new_observers, o) } ((HeapSucc(h, h')) && (pre.fun.TUPLE^INTEGER_32#INTEGER_32^.in_observers(h, current, new_observers, o)) && (pre.fun.TUPLE^INTEGER_32#INTEGER_32^.in_observers(h', current, new_observers, o)) && (same_inside(h, h', read.fun.TUPLE^INTEGER_32#INTEGER_32^.in_observers(h, current, new_observers, o)))) ==> ((fun0.TUPLE^INTEGER_32#INTEGER_32^.in_observers(h, current, new_observers, o)) == (fun0.TUPLE^INTEGER_32#INTEGER_32^.in_observers(h', current, new_observers, o)))));

function modify.TUPLE^INTEGER_32#INTEGER_32^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T23> $o: ref, $f: Field T23 :: { modify.TUPLE^INTEGER_32#INTEGER_32^.in_observers(heap, current, new_observers, o)[$o, $f] } (modify.TUPLE^INTEGER_32#INTEGER_32^.in_observers(heap, current, new_observers, o)[$o, $f]) <==> (false)))));

function read.fun.TUPLE^INTEGER_32#INTEGER_32^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T24> $o: ref, $f: Field T24 :: { read.fun.TUPLE^INTEGER_32#INTEGER_32^.in_observers(heap, current, new_observers, o)[$o, $f] } (read.fun.TUPLE^INTEGER_32#INTEGER_32^.in_observers(heap, current, new_observers, o)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.TUPLE^INTEGER_32#INTEGER_32^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool) {
  true
}

function trigger.fun.TUPLE^INTEGER_32#INTEGER_32^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);
