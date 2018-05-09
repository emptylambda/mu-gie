// Automatically generated (12/12/2017 1:55:26.674 PM)

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

const unique FLIP_UP_COMMAND: Type;

axiom ((FLIP_UP_COMMAND) <: (LIGHT_COMMAND));

axiom ((forall t: Type :: { (FLIP_UP_COMMAND) <: (t) } ((FLIP_UP_COMMAND) <: (t)) <==> (((t) == (FLIP_UP_COMMAND)) || ((LIGHT_COMMAND) <: (t)))));

axiom ((FieldId(allocated, FLIP_UP_COMMAND)) == (-1));

axiom ((FieldId(closed, FLIP_UP_COMMAND)) == (-2));

axiom ((FieldId(owner, FLIP_UP_COMMAND)) == (-3));

axiom ((FieldId(owns, FLIP_UP_COMMAND)) == (-4));

axiom ((FieldId(observers, FLIP_UP_COMMAND)) == (-5));

axiom ((FieldId(subjects, FLIP_UP_COMMAND)) == (-6));

axiom ((forall <T0> $f: Field T0 :: { IsModelField($f, FLIP_UP_COMMAND) } (IsModelField($f, FLIP_UP_COMMAND)) <==> ((($f) == (subjects)) || (($f) == (observers)))));

function { :inline } FLIP_UP_COMMAND.user_inv(heap: HeapType, current: ref) returns (bool) {
  ((heap[current, FLIP_UP_COMMAND.light]) != (Void)) && (Set#IsEmpty(heap[current, observers])) && (Set#IsEmpty(heap[current, subjects])) && (Set#IsEmpty(heap[current, owns])) && (admissibility2(heap, current))
}

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached_exact(heap, current, FLIP_UP_COMMAND)) ==> ((user_inv(heap, current)) <==> (FLIP_UP_COMMAND.user_inv(heap, current)))));

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached(heap, current, FLIP_UP_COMMAND)) ==> ((user_inv(heap, current)) ==> (FLIP_UP_COMMAND.user_inv(heap, current)))));

procedure FLIP_UP_COMMAND.invariant_admissibility_check(Current: ref);
  requires attached_exact(Heap, Current, FLIP_UP_COMMAND);



implementation FLIP_UP_COMMAND.invariant_admissibility_check(Current: ref)
{
  entry:
  goto pre, a2, a3;
  pre:
  assert user_inv_readable(Heap, Current)[Current, FLIP_UP_COMMAND.light]; // type:access tag:attribute_readable line:30 cid:406 fid:81
  assume (Heap[Current, FLIP_UP_COMMAND.light]) != (Void);
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

procedure create.FLIP_UP_COMMAND.make(Current: ref, a_light: ref);
  free requires attached_exact(Heap, Current, FLIP_UP_COMMAND); // info:type property for argument Current
  free requires detachable(Heap, a_light, LIGHT); // info:type property for argument a_light
  modifies Heap;
  ensures (Heap[Current, FLIP_UP_COMMAND.light]) == (a_light); // type:post line:13
  requires (forall <T3> $f: Field T3 :: (($f) != (allocated)) ==> ((Heap[Current, $f]) == (Default($f))));
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.FLIP_UP_COMMAND.make(Heap, Current, a_light), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.FLIP_UP_COMMAND.make(old(Heap), Current, a_light));
  free ensures HeapSucc(old(Heap), Heap);
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts
  requires is_wrapped(Heap, a_light); // type:pre tag:arg_a_light_is_wrapped default:contracts
  ensures is_wrapped(Heap, a_light); // type:post tag:arg_a_light_is_wrapped default:contracts



implementation create.FLIP_UP_COMMAND.make(Current: ref, a_light: ref)
{
  entry:
  assume {:captureState "create.FLIP_UP_COMMAND.make"} true;
  // /home/caf/temp/comcom/repo-command/light_command.e:11
  // light := a_light
  call update_heap(Current, FLIP_UP_COMMAND.light, a_light); // line:11
  if (*) {
    assert (Heap[Current, FLIP_UP_COMMAND.light]) != (Void); // type:inv line:14 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, observers]); // type:inv tag:default_observers line:14 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, subjects]); // type:inv tag:default_subjects line:14 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, owns]); // type:inv tag:default_owns line:14 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert admissibility2(Heap, Current); // type:inv tag:A2 line:14 cid:1 rid:55
    assume false;
  }
  call wrap(Current); // default:wrapping cid:1 rid:55 line:14
}

procedure FLIP_UP_COMMAND.execute(Current: ref);
  free requires attached_exact(Heap, Current, FLIP_UP_COMMAND); // info:type property for argument Current
  modifies Heap;
  requires (Heap[Current, FLIP_UP_COMMAND.light]) != (Void); // type:attached line:22
  requires is_wrapped(Heap, Heap[Current, FLIP_UP_COMMAND.light]); // type:pre line:22
  ensures (Heap[Current, FLIP_UP_COMMAND.light]) != (Void); // type:attached tag:on line:19
  ensures Heap[Heap[Current, FLIP_UP_COMMAND.light], LIGHT.is_on]; // type:post tag:on line:19
  ensures is_wrapped(Heap, Heap[Current, FLIP_UP_COMMAND.light]); // type:post line:26
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.FLIP_UP_COMMAND.execute(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.FLIP_UP_COMMAND.execute(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);
  requires is_wrapped(Heap, Current); // type:pre tag:default_is_wrapped default:contracts
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts



function { :inline } variant.FLIP_UP_COMMAND.execute.1(heap: HeapType, current: ref) returns (int) {
  0
}

implementation FLIP_UP_COMMAND.execute(Current: ref)
{
  entry:
  assume {:captureState "FLIP_UP_COMMAND.execute"} true;
  // /home/caf/temp/comcom/repo-command/flip_up_command.e:17
  // light.turn_on
  assert {:subsumption 0} (Heap[Current, FLIP_UP_COMMAND.light]) != (Void); // type:attached line:17
  call LIGHT.turn_on(Heap[Current, FLIP_UP_COMMAND.light]); // line:17 cid:405 rid:5404
}

const unique LIGHT: Type;

axiom ((LIGHT) <: (ANY));

axiom ((forall t: Type :: { (LIGHT) <: (t) } ((LIGHT) <: (t)) <==> (((t) == (LIGHT)) || ((ANY) <: (t)))));

axiom ((FieldId(allocated, LIGHT)) == (-1));

axiom ((FieldId(closed, LIGHT)) == (-2));

axiom ((FieldId(owner, LIGHT)) == (-3));

axiom ((FieldId(owns, LIGHT)) == (-4));

axiom ((FieldId(observers, LIGHT)) == (-5));

axiom ((FieldId(subjects, LIGHT)) == (-6));

axiom ((forall <T4> $f: Field T4 :: { IsModelField($f, LIGHT) } (IsModelField($f, LIGHT)) <==> ((($f) == (subjects)) || (($f) == (observers)))));

function { :inline } LIGHT.user_inv(heap: HeapType, current: ref) returns (bool) {
  (Set#IsEmpty(heap[current, observers])) && (Set#IsEmpty(heap[current, subjects])) && (Set#IsEmpty(heap[current, owns])) && (admissibility2(heap, current))
}

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached_exact(heap, current, LIGHT)) ==> ((user_inv(heap, current)) <==> (LIGHT.user_inv(heap, current)))));

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached(heap, current, LIGHT)) ==> ((user_inv(heap, current)) ==> (LIGHT.user_inv(heap, current)))));

procedure LIGHT.invariant_admissibility_check(Current: ref);
  requires attached_exact(Heap, Current, LIGHT);



implementation LIGHT.invariant_admissibility_check(Current: ref)
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

procedure create.LIGHT.default_create(Current: ref);
  free requires attached_exact(Heap, Current, LIGHT); // info:type property for argument Current
  modifies Heap;
  requires (forall <T5> $f: Field T5 :: (($f) != (allocated)) ==> ((Heap[Current, $f]) == (Default($f))));
  ensures (forall <T6> $f: Field T6 :: ((($f) != (allocated)) && (($f) != (closed))) ==> ((Heap[Current, $f]) == (Default($f))));
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.LIGHT.default_create(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.LIGHT.default_create(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts



implementation create.LIGHT.default_create(Current: ref)
{
  entry:
  assume {:captureState "create.LIGHT.default_create"} true;
  if (*) {
    assert Set#IsEmpty(Heap[Current, observers]); // type:inv tag:default_observers line:23 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, subjects]); // type:inv tag:default_subjects line:23 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, owns]); // type:inv tag:default_owns line:23 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert admissibility2(Heap, Current); // type:inv tag:A2 line:23 cid:1 rid:55
    assume false;
  }
  call wrap(Current); // default:wrapping cid:1 rid:55 line:364
}

procedure LIGHT.turn_on(Current: ref);
  free requires attached_exact(Heap, Current, LIGHT); // info:type property for argument Current
  modifies Heap;
  ensures Heap[Current, LIGHT.is_on]; // type:post tag:on line:14
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.LIGHT.turn_on(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.LIGHT.turn_on(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);
  requires is_wrapped(Heap, Current); // type:pre tag:default_is_wrapped default:contracts
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts



function { :inline } variant.LIGHT.turn_on.1(heap: HeapType, current: ref) returns (int) {
  0
}

implementation LIGHT.turn_on(Current: ref)
{
  entry:
  assume {:captureState "LIGHT.turn_on"} true;
  call unwrap(Current); // default:wrapping cid:1 rid:57 line:9
  assume LIGHT.user_inv(Heap, Current);
  // /home/caf/temp/comcom/repo-command/light.e:12
  // is_on := True
  call update_heap(Current, LIGHT.is_on, true); // line:12
  if (*) {
    assert Set#IsEmpty(Heap[Current, observers]); // type:inv tag:default_observers line:23 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, subjects]); // type:inv tag:default_subjects line:23 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, owns]); // type:inv tag:default_owns line:23 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert admissibility2(Heap, Current); // type:inv tag:A2 line:23 cid:1 rid:55
    assume false;
  }
  call wrap(Current); // default:wrapping cid:1 rid:55 line:15
}

procedure LIGHT.turn_off(Current: ref);
  free requires attached_exact(Heap, Current, LIGHT); // info:type property for argument Current
  modifies Heap;
  ensures !(Heap[Current, LIGHT.is_on]); // type:post tag:off line:22
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.LIGHT.turn_off(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.LIGHT.turn_off(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);
  requires is_wrapped(Heap, Current); // type:pre tag:default_is_wrapped default:contracts
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts



function { :inline } variant.LIGHT.turn_off.1(heap: HeapType, current: ref) returns (int) {
  0
}

implementation LIGHT.turn_off(Current: ref)
{
  entry:
  assume {:captureState "LIGHT.turn_off"} true;
  call unwrap(Current); // default:wrapping cid:1 rid:57 line:17
  assume LIGHT.user_inv(Heap, Current);
  // /home/caf/temp/comcom/repo-command/light.e:20
  // is_on := False
  call update_heap(Current, LIGHT.is_on, false); // line:20
  if (*) {
    assert Set#IsEmpty(Heap[Current, observers]); // type:inv tag:default_observers line:23 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, subjects]); // type:inv tag:default_subjects line:23 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, owns]); // type:inv tag:default_owns line:23 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert admissibility2(Heap, Current); // type:inv tag:A2 line:23 cid:1 rid:55
    assume false;
  }
  call wrap(Current); // default:wrapping cid:1 rid:55 line:23
}

const unique FLIP_DOWN_COMMAND: Type;

axiom ((FLIP_DOWN_COMMAND) <: (LIGHT_COMMAND));

axiom ((forall t: Type :: { (FLIP_DOWN_COMMAND) <: (t) } ((FLIP_DOWN_COMMAND) <: (t)) <==> (((t) == (FLIP_DOWN_COMMAND)) || ((LIGHT_COMMAND) <: (t)))));

axiom ((FieldId(allocated, FLIP_DOWN_COMMAND)) == (-1));

axiom ((FieldId(closed, FLIP_DOWN_COMMAND)) == (-2));

axiom ((FieldId(owner, FLIP_DOWN_COMMAND)) == (-3));

axiom ((FieldId(owns, FLIP_DOWN_COMMAND)) == (-4));

axiom ((FieldId(observers, FLIP_DOWN_COMMAND)) == (-5));

axiom ((FieldId(subjects, FLIP_DOWN_COMMAND)) == (-6));

axiom ((forall <T7> $f: Field T7 :: { IsModelField($f, FLIP_DOWN_COMMAND) } (IsModelField($f, FLIP_DOWN_COMMAND)) <==> ((($f) == (subjects)) || (($f) == (observers)))));

function { :inline } FLIP_DOWN_COMMAND.user_inv(heap: HeapType, current: ref) returns (bool) {
  ((heap[current, FLIP_DOWN_COMMAND.light]) != (Void)) && (Set#IsEmpty(heap[current, observers])) && (Set#IsEmpty(heap[current, subjects])) && (Set#IsEmpty(heap[current, owns])) && (admissibility2(heap, current))
}

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached_exact(heap, current, FLIP_DOWN_COMMAND)) ==> ((user_inv(heap, current)) <==> (FLIP_DOWN_COMMAND.user_inv(heap, current)))));

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached(heap, current, FLIP_DOWN_COMMAND)) ==> ((user_inv(heap, current)) ==> (FLIP_DOWN_COMMAND.user_inv(heap, current)))));

procedure FLIP_DOWN_COMMAND.invariant_admissibility_check(Current: ref);
  requires attached_exact(Heap, Current, FLIP_DOWN_COMMAND);



implementation FLIP_DOWN_COMMAND.invariant_admissibility_check(Current: ref)
{
  entry:
  goto pre, a2, a3;
  pre:
  assert user_inv_readable(Heap, Current)[Current, FLIP_DOWN_COMMAND.light]; // type:access tag:attribute_readable line:30 cid:404 fid:81
  assume (Heap[Current, FLIP_DOWN_COMMAND.light]) != (Void);
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

procedure create.FLIP_DOWN_COMMAND.make(Current: ref, a_light: ref);
  free requires attached_exact(Heap, Current, FLIP_DOWN_COMMAND); // info:type property for argument Current
  free requires detachable(Heap, a_light, LIGHT); // info:type property for argument a_light
  modifies Heap;
  ensures (Heap[Current, FLIP_DOWN_COMMAND.light]) == (a_light); // type:post line:13
  requires (forall <T8> $f: Field T8 :: (($f) != (allocated)) ==> ((Heap[Current, $f]) == (Default($f))));
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.FLIP_DOWN_COMMAND.make(Heap, Current, a_light), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.FLIP_DOWN_COMMAND.make(old(Heap), Current, a_light));
  free ensures HeapSucc(old(Heap), Heap);
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts
  requires is_wrapped(Heap, a_light); // type:pre tag:arg_a_light_is_wrapped default:contracts
  ensures is_wrapped(Heap, a_light); // type:post tag:arg_a_light_is_wrapped default:contracts



implementation create.FLIP_DOWN_COMMAND.make(Current: ref, a_light: ref)
{
  entry:
  assume {:captureState "create.FLIP_DOWN_COMMAND.make"} true;
  // /home/caf/temp/comcom/repo-command/light_command.e:11
  // light := a_light
  call update_heap(Current, FLIP_DOWN_COMMAND.light, a_light); // line:11
  if (*) {
    assert (Heap[Current, FLIP_DOWN_COMMAND.light]) != (Void); // type:inv line:14 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, observers]); // type:inv tag:default_observers line:14 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, subjects]); // type:inv tag:default_subjects line:14 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, owns]); // type:inv tag:default_owns line:14 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert admissibility2(Heap, Current); // type:inv tag:A2 line:14 cid:1 rid:55
    assume false;
  }
  call wrap(Current); // default:wrapping cid:1 rid:55 line:14
}

procedure FLIP_DOWN_COMMAND.execute(Current: ref);
  free requires attached_exact(Heap, Current, FLIP_DOWN_COMMAND); // info:type property for argument Current
  modifies Heap;
  requires (Heap[Current, FLIP_DOWN_COMMAND.light]) != (Void); // type:attached line:22
  requires is_wrapped(Heap, Heap[Current, FLIP_DOWN_COMMAND.light]); // type:pre line:22
  ensures (Heap[Current, FLIP_DOWN_COMMAND.light]) != (Void); // type:attached tag:off line:19
  ensures !(Heap[Heap[Current, FLIP_DOWN_COMMAND.light], LIGHT.is_on]); // type:post tag:off line:19
  ensures is_wrapped(Heap, Heap[Current, FLIP_DOWN_COMMAND.light]); // type:post line:26
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.FLIP_DOWN_COMMAND.execute(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.FLIP_DOWN_COMMAND.execute(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);
  requires is_wrapped(Heap, Current); // type:pre tag:default_is_wrapped default:contracts
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts



function { :inline } variant.FLIP_DOWN_COMMAND.execute.1(heap: HeapType, current: ref) returns (int) {
  0
}

implementation FLIP_DOWN_COMMAND.execute(Current: ref)
{
  entry:
  assume {:captureState "FLIP_DOWN_COMMAND.execute"} true;
  // /home/caf/temp/comcom/repo-command/flip_down_command.e:17
  // light.turn_off
  assert {:subsumption 0} (Heap[Current, FLIP_DOWN_COMMAND.light]) != (Void); // type:attached line:17
  call LIGHT.turn_off(Heap[Current, FLIP_DOWN_COMMAND.light]); // line:17 cid:405 rid:5405
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

axiom ((forall <T9> $f: Field T9 :: { IsModelField($f, CLIENT) } (IsModelField($f, CLIENT)) <==> ((($f) == (subjects)) || (($f) == (observers)))));

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
  requires (forall <T10> $f: Field T10 :: (($f) != (allocated)) ==> ((Heap[Current, $f]) == (Default($f))));
  ensures (forall <T11> $f: Field T11 :: ((($f) != (allocated)) && (($f) != (closed))) ==> ((Heap[Current, $f]) == (Default($f))));
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
    assert Set#IsEmpty(Heap[Current, observers]); // type:inv tag:default_observers line:21 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, subjects]); // type:inv tag:default_subjects line:21 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, owns]); // type:inv tag:default_owns line:21 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert admissibility2(Heap, Current); // type:inv tag:A2 line:21 cid:1 rid:55
    assume false;
  }
  call wrap(Current); // default:wrapping cid:1 rid:55 line:364
}

procedure CLIENT.switch_light(Current: ref);
  free requires attached_exact(Heap, Current, CLIENT); // info:type property for argument Current
  modifies Heap;
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.CLIENT.switch_light(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.CLIENT.switch_light(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);
  requires is_wrapped(Heap, Current); // type:pre tag:default_is_wrapped default:contracts
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts



function { :inline } variant.CLIENT.switch_light.1(heap: HeapType, current: ref) returns (int) {
  0
}

implementation CLIENT.switch_light(Current: ref)
{
  var temp_1: ref;
  var temp_2: ref;
  var temp_3: ref;
  var temp_4: ref;
  var local1: ref where detachable(Heap, local1, LIGHT);
  var local2: ref where detachable(Heap, local2, SWITCH);
  var local3: ref where detachable(Heap, local3, LIGHT_COMMAND);
  var local4: ref where detachable(Heap, local4, LIGHT_COMMAND);

  init_locals:
  temp_1 := Void;
  temp_2 := Void;
  temp_3 := Void;
  temp_4 := Void;
  local1 := Void;
  local2 := Void;
  local3 := Void;
  local4 := Void;

  entry:
  assume {:captureState "CLIENT.switch_light"} true;
  call unwrap(Current); // default:wrapping cid:1 rid:57 line:5
  assume CLIENT.user_inv(Heap, Current);
  // /home/caf/temp/comcom/repo-command/client.e:11
  // create light
  call temp_1 := allocate(LIGHT); // line:-1
  call create.LIGHT.default_create(temp_1); // line:11 cid:405 rid:35
  local1 := temp_1;
  // /home/caf/temp/comcom/repo-command/client.e:12
  // create {FLIP_UP_COMMAND} cup.make (light)
  call temp_2 := allocate(FLIP_UP_COMMAND); // line:-1
  call create.FLIP_UP_COMMAND.make(temp_2, local1); // line:12 cid:406 rid:5406
  local3 := temp_2;
  // /home/caf/temp/comcom/repo-command/client.e:13
  // create {FLIP_DOWN_COMMAND} cdown.make (light)
  call temp_3 := allocate(FLIP_DOWN_COMMAND); // line:-1
  call create.FLIP_DOWN_COMMAND.make(temp_3, local1); // line:13 cid:404 rid:5406
  local4 := temp_3;
  // /home/caf/temp/comcom/repo-command/client.e:14
  // create switch
  call temp_4 := allocate(SWITCH); // line:-1
  call create.SWITCH.default_create(temp_4); // line:14 cid:408 rid:35
  local2 := temp_4;
  // /home/caf/temp/comcom/repo-command/client.e:16
  // switch.execute_command (cup)
  assert {:subsumption 0} (local2) != (Void); // type:attached line:16
  call SWITCH.execute_command(local2, local3); // line:16 cid:408 rid:5401
  // /home/caf/temp/comcom/repo-command/client.e:17
  // check light.is_on end
  assert {:subsumption 0} (local1) != (Void); // type:attached line:17
  assert Heap[local1, LIGHT.is_on]; // type:check line:17
  // /home/caf/temp/comcom/repo-command/client.e:19
  // switch.execute_command (cdown)
  assert {:subsumption 0} (local2) != (Void); // type:attached line:19
  call SWITCH.execute_command(local2, local4); // line:19 cid:408 rid:5401
  // /home/caf/temp/comcom/repo-command/client.e:20
  // check not light.is_on end
  assert {:subsumption 0} (local1) != (Void); // type:attached line:20
  assert !(Heap[local1, LIGHT.is_on]); // type:check line:20
  if (*) {
    assert Set#IsEmpty(Heap[Current, observers]); // type:inv tag:default_observers line:21 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, subjects]); // type:inv tag:default_subjects line:21 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, owns]); // type:inv tag:default_owns line:21 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert admissibility2(Heap, Current); // type:inv tag:A2 line:21 cid:1 rid:55
    assume false;
  }
  call wrap(Current); // default:wrapping cid:1 rid:55 line:21
}

const unique LIGHT_COMMAND: Type;

axiom ((LIGHT_COMMAND) <: (ANY));

axiom ((forall t: Type :: { (LIGHT_COMMAND) <: (t) } ((LIGHT_COMMAND) <: (t)) <==> (((t) == (LIGHT_COMMAND)) || ((ANY) <: (t)))));

axiom ((FieldId(allocated, LIGHT_COMMAND)) == (-1));

axiom ((FieldId(closed, LIGHT_COMMAND)) == (-2));

axiom ((FieldId(owner, LIGHT_COMMAND)) == (-3));

axiom ((FieldId(owns, LIGHT_COMMAND)) == (-4));

axiom ((FieldId(observers, LIGHT_COMMAND)) == (-5));

axiom ((FieldId(subjects, LIGHT_COMMAND)) == (-6));

axiom ((forall <T12> $f: Field T12 :: { IsModelField($f, LIGHT_COMMAND) } (IsModelField($f, LIGHT_COMMAND)) <==> ((($f) == (subjects)) || (($f) == (observers)))));

function { :inline } LIGHT_COMMAND.user_inv(heap: HeapType, current: ref) returns (bool) {
  ((heap[current, LIGHT_COMMAND.light]) != (Void)) && (admissibility2(heap, current))
}

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached_exact(heap, current, LIGHT_COMMAND)) ==> ((user_inv(heap, current)) <==> (LIGHT_COMMAND.user_inv(heap, current)))));

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached(heap, current, LIGHT_COMMAND)) ==> ((user_inv(heap, current)) ==> (LIGHT_COMMAND.user_inv(heap, current)))));

procedure LIGHT_COMMAND.invariant_admissibility_check(Current: ref);
  requires attached_exact(Heap, Current, LIGHT_COMMAND);



implementation LIGHT_COMMAND.invariant_admissibility_check(Current: ref)
{
  entry:
  goto pre, a2, a3;
  pre:
  assert user_inv_readable(Heap, Current)[Current, LIGHT_COMMAND.light]; // type:access tag:attribute_readable line:30 cid:409 fid:81
  assume (Heap[Current, LIGHT_COMMAND.light]) != (Void);
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

procedure LIGHT_COMMAND.execute(Current: ref);
  free requires attached_exact(Heap, Current, LIGHT_COMMAND); // info:type property for argument Current
  modifies Heap;
  requires (Heap[Current, LIGHT_COMMAND.light]) != (Void); // type:attached line:22
  requires is_wrapped(Heap, Heap[Current, LIGHT_COMMAND.light]); // type:pre line:22
  ensures (Heap[Current, LIGHT_COMMAND.light]) != (Void); // type:attached line:26
  ensures is_wrapped(Heap, Heap[Current, LIGHT_COMMAND.light]); // type:post line:26
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.LIGHT_COMMAND.execute(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.LIGHT_COMMAND.execute(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);
  requires is_wrapped(Heap, Current); // type:pre tag:default_is_wrapped default:contracts
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts



const unique SWITCH: Type;

axiom ((SWITCH) <: (ANY));

axiom ((forall t: Type :: { (SWITCH) <: (t) } ((SWITCH) <: (t)) <==> (((t) == (SWITCH)) || ((ANY) <: (t)))));

axiom ((FieldId(allocated, SWITCH)) == (-1));

axiom ((FieldId(closed, SWITCH)) == (-2));

axiom ((FieldId(owner, SWITCH)) == (-3));

axiom ((FieldId(owns, SWITCH)) == (-4));

axiom ((FieldId(observers, SWITCH)) == (-5));

axiom ((FieldId(subjects, SWITCH)) == (-6));

axiom ((forall <T13> $f: Field T13 :: { IsModelField($f, SWITCH) } (IsModelField($f, SWITCH)) <==> ((($f) == (subjects)) || (($f) == (observers)))));

function { :inline } SWITCH.user_inv(heap: HeapType, current: ref) returns (bool) {
  (Set#IsEmpty(heap[current, observers])) && (Set#IsEmpty(heap[current, subjects])) && (Set#IsEmpty(heap[current, owns])) && (admissibility2(heap, current))
}

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached_exact(heap, current, SWITCH)) ==> ((user_inv(heap, current)) <==> (SWITCH.user_inv(heap, current)))));

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached(heap, current, SWITCH)) ==> ((user_inv(heap, current)) ==> (SWITCH.user_inv(heap, current)))));

procedure SWITCH.invariant_admissibility_check(Current: ref);
  requires attached_exact(Heap, Current, SWITCH);



implementation SWITCH.invariant_admissibility_check(Current: ref)
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

procedure create.SWITCH.default_create(Current: ref);
  free requires attached_exact(Heap, Current, SWITCH); // info:type property for argument Current
  modifies Heap;
  requires (forall <T14> $f: Field T14 :: (($f) != (allocated)) ==> ((Heap[Current, $f]) == (Default($f))));
  ensures (forall <T15> $f: Field T15 :: ((($f) != (allocated)) && (($f) != (closed))) ==> ((Heap[Current, $f]) == (Default($f))));
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.SWITCH.default_create(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.SWITCH.default_create(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts



implementation create.SWITCH.default_create(Current: ref)
{
  entry:
  assume {:captureState "create.SWITCH.default_create"} true;
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

procedure SWITCH.execute_command(Current: ref, cmd: ref);
  free requires attached_exact(Heap, Current, SWITCH); // info:type property for argument Current
  free requires detachable(Heap, cmd, LIGHT_COMMAND); // info:type property for argument cmd
  modifies Heap;
  requires (cmd) != (Void); // type:attached tag:can_execute line:10
  requires (Heap[cmd, LIGHT_COMMAND.light]) != (Void); // type:attached tag:can_execute line:10
  requires is_wrapped(Heap, Heap[cmd, LIGHT_COMMAND.light]); // type:pre tag:can_execute line:10
  ensures post.LIGHT_COMMAND.execute(Heap, old(Heap), cmd); // type:post line:16
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.SWITCH.execute_command(Heap, Current, cmd), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.SWITCH.execute_command(old(Heap), Current, cmd));
  free ensures HeapSucc(old(Heap), Heap);
  requires is_wrapped(Heap, Current); // type:pre tag:default_is_wrapped default:contracts
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts
  requires is_wrapped(Heap, cmd); // type:pre tag:arg_cmd_is_wrapped default:contracts
  ensures is_wrapped(Heap, cmd); // type:post tag:arg_cmd_is_wrapped default:contracts



function { :inline } variant.SWITCH.execute_command.1(heap: HeapType, current: ref, cmd: ref) returns (ref) {
  cmd
}

implementation SWITCH.execute_command(Current: ref, cmd: ref)
{
  entry:
  assume {:captureState "SWITCH.execute_command"} true;
  // /home/caf/temp/comcom/repo-command/switch.e:14
  // cmd.execute
  assert {:subsumption 0} (cmd) != (Void); // type:attached line:14
  call LIGHT_COMMAND.execute(cmd); // line:14 cid:409 rid:5408
}

const FLIP_UP_COMMAND.light: Field (ref);

axiom ((FieldId(FLIP_UP_COMMAND.light, FLIP_UP_COMMAND)) == (81));

const LIGHT_COMMAND.light: Field (ref);

axiom ((FLIP_UP_COMMAND.light) == (LIGHT_COMMAND.light));

axiom ((forall heap: HeapType, o: ref :: { heap[o, FLIP_UP_COMMAND.light] } ((IsHeap(heap)) && (attached(heap, o, FLIP_UP_COMMAND))) ==> (detachable(heap, heap[o, FLIP_UP_COMMAND.light], LIGHT))));

axiom ((forall heap: HeapType, current: ref, v: ref, o: ref :: { guard(heap, current, FLIP_UP_COMMAND.light, v, o) } (attached_exact(heap, current, FLIP_UP_COMMAND)) ==> ((guard(heap, current, FLIP_UP_COMMAND.light, v, o)) <==> ((user_inv(heap, o)) ==> (user_inv(heap[current, FLIP_UP_COMMAND.light := v], o))))));

axiom ((forall heap: HeapType, current: ref, v: ref, o: ref :: { guard(heap, current, FLIP_UP_COMMAND.light, v, o) } (attached(heap, current, FLIP_UP_COMMAND)) ==> ((guard(heap, current, FLIP_UP_COMMAND.light, v, o)) ==> ((user_inv(heap, o)) ==> (user_inv(heap[current, FLIP_UP_COMMAND.light := v], o))))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, owns, v, o) } (attached_exact(heap, current, ANY)) ==> ((guard(heap, current, owns, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, subjects, v, o) } (attached_exact(heap, current, ANY)) ==> ((guard(heap, current, subjects, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached_exact(heap, current, ANY)) ==> ((guard(heap, current, observers, v, o)) <==> (fun.ANY.in_observers(heap, current, v, o)))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached(heap, current, ANY)) ==> ((guard(heap, current, observers, v, o)) ==> (fun.ANY.in_observers(heap, current, v, o)))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, owns, v, o) } (attached_exact(heap, current, FLIP_UP_COMMAND)) ==> ((guard(heap, current, owns, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, subjects, v, o) } (attached_exact(heap, current, FLIP_UP_COMMAND)) ==> ((guard(heap, current, subjects, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached_exact(heap, current, FLIP_UP_COMMAND)) ==> ((guard(heap, current, observers, v, o)) <==> (fun.FLIP_UP_COMMAND.in_observers(heap, current, v, o)))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached(heap, current, FLIP_UP_COMMAND)) ==> ((guard(heap, current, observers, v, o)) ==> (fun.FLIP_UP_COMMAND.in_observers(heap, current, v, o)))));

function modify.FLIP_UP_COMMAND.make(heap: HeapType, current: ref, a_light: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, a_light: ref :: (IsHeap(heap)) ==> ((forall <T16> $o: ref, $f: Field T16 :: { modify.FLIP_UP_COMMAND.make(heap, current, a_light)[$o, $f] } (modify.FLIP_UP_COMMAND.make(heap, current, a_light)[$o, $f]) <==> (($o) == (current))))));

const LIGHT.is_on: Field bool;

axiom ((FieldId(LIGHT.is_on, LIGHT)) == (80));

axiom ((forall heap: HeapType, current: ref, v: bool, o: ref :: { guard(heap, current, LIGHT.is_on, v, o) } (attached_exact(heap, current, LIGHT)) ==> ((guard(heap, current, LIGHT.is_on, v, o)) <==> ((user_inv(heap, o)) ==> (user_inv(heap[current, LIGHT.is_on := v], o))))));

axiom ((forall heap: HeapType, current: ref, v: bool, o: ref :: { guard(heap, current, LIGHT.is_on, v, o) } (attached(heap, current, LIGHT)) ==> ((guard(heap, current, LIGHT.is_on, v, o)) ==> ((user_inv(heap, o)) ==> (user_inv(heap[current, LIGHT.is_on := v], o))))));

function modify.FLIP_UP_COMMAND.execute(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T17> $o: ref, $f: Field T17 :: { modify.FLIP_UP_COMMAND.execute(heap, current)[$o, $f] } (modify.FLIP_UP_COMMAND.execute(heap, current)[$o, $f]) <==> (($o) == (heap[current, FLIP_UP_COMMAND.light]))))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, owns, v, o) } (attached_exact(heap, current, LIGHT)) ==> ((guard(heap, current, owns, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, subjects, v, o) } (attached_exact(heap, current, LIGHT)) ==> ((guard(heap, current, subjects, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached_exact(heap, current, LIGHT)) ==> ((guard(heap, current, observers, v, o)) <==> (fun.LIGHT.in_observers(heap, current, v, o)))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached(heap, current, LIGHT)) ==> ((guard(heap, current, observers, v, o)) ==> (fun.LIGHT.in_observers(heap, current, v, o)))));

function modify.LIGHT.default_create(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T18> $o: ref, $f: Field T18 :: { modify.LIGHT.default_create(heap, current)[$o, $f] } (modify.LIGHT.default_create(heap, current)[$o, $f]) <==> (($o) == (current))))));

function modify.LIGHT.turn_on(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T19> $o: ref, $f: Field T19 :: { modify.LIGHT.turn_on(heap, current)[$o, $f] } (modify.LIGHT.turn_on(heap, current)[$o, $f]) <==> (($o) == (current))))));

function modify.LIGHT.turn_off(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T20> $o: ref, $f: Field T20 :: { modify.LIGHT.turn_off(heap, current)[$o, $f] } (modify.LIGHT.turn_off(heap, current)[$o, $f]) <==> (($o) == (current))))));

const FLIP_DOWN_COMMAND.light: Field (ref);

axiom ((FieldId(FLIP_DOWN_COMMAND.light, FLIP_DOWN_COMMAND)) == (81));

axiom ((FLIP_DOWN_COMMAND.light) == (LIGHT_COMMAND.light));

axiom ((forall heap: HeapType, o: ref :: { heap[o, FLIP_DOWN_COMMAND.light] } ((IsHeap(heap)) && (attached(heap, o, FLIP_DOWN_COMMAND))) ==> (detachable(heap, heap[o, FLIP_DOWN_COMMAND.light], LIGHT))));

axiom ((forall heap: HeapType, current: ref, v: ref, o: ref :: { guard(heap, current, FLIP_DOWN_COMMAND.light, v, o) } (attached_exact(heap, current, FLIP_DOWN_COMMAND)) ==> ((guard(heap, current, FLIP_DOWN_COMMAND.light, v, o)) <==> ((user_inv(heap, o)) ==> (user_inv(heap[current, FLIP_DOWN_COMMAND.light := v], o))))));

axiom ((forall heap: HeapType, current: ref, v: ref, o: ref :: { guard(heap, current, FLIP_DOWN_COMMAND.light, v, o) } (attached(heap, current, FLIP_DOWN_COMMAND)) ==> ((guard(heap, current, FLIP_DOWN_COMMAND.light, v, o)) ==> ((user_inv(heap, o)) ==> (user_inv(heap[current, FLIP_DOWN_COMMAND.light := v], o))))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, owns, v, o) } (attached_exact(heap, current, FLIP_DOWN_COMMAND)) ==> ((guard(heap, current, owns, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, subjects, v, o) } (attached_exact(heap, current, FLIP_DOWN_COMMAND)) ==> ((guard(heap, current, subjects, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached_exact(heap, current, FLIP_DOWN_COMMAND)) ==> ((guard(heap, current, observers, v, o)) <==> (fun.FLIP_DOWN_COMMAND.in_observers(heap, current, v, o)))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached(heap, current, FLIP_DOWN_COMMAND)) ==> ((guard(heap, current, observers, v, o)) ==> (fun.FLIP_DOWN_COMMAND.in_observers(heap, current, v, o)))));

function modify.FLIP_DOWN_COMMAND.make(heap: HeapType, current: ref, a_light: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, a_light: ref :: (IsHeap(heap)) ==> ((forall <T21> $o: ref, $f: Field T21 :: { modify.FLIP_DOWN_COMMAND.make(heap, current, a_light)[$o, $f] } (modify.FLIP_DOWN_COMMAND.make(heap, current, a_light)[$o, $f]) <==> (($o) == (current))))));

function modify.FLIP_DOWN_COMMAND.execute(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T22> $o: ref, $f: Field T22 :: { modify.FLIP_DOWN_COMMAND.execute(heap, current)[$o, $f] } (modify.FLIP_DOWN_COMMAND.execute(heap, current)[$o, $f]) <==> (($o) == (heap[current, FLIP_DOWN_COMMAND.light]))))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, owns, v, o) } (attached_exact(heap, current, CLIENT)) ==> ((guard(heap, current, owns, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, subjects, v, o) } (attached_exact(heap, current, CLIENT)) ==> ((guard(heap, current, subjects, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached_exact(heap, current, CLIENT)) ==> ((guard(heap, current, observers, v, o)) <==> (fun.CLIENT.in_observers(heap, current, v, o)))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached(heap, current, CLIENT)) ==> ((guard(heap, current, observers, v, o)) ==> (fun.CLIENT.in_observers(heap, current, v, o)))));

function modify.CLIENT.default_create(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T23> $o: ref, $f: Field T23 :: { modify.CLIENT.default_create(heap, current)[$o, $f] } (modify.CLIENT.default_create(heap, current)[$o, $f]) <==> (($o) == (current))))));

function modify.CLIENT.switch_light(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T24> $o: ref, $f: Field T24 :: { modify.CLIENT.switch_light(heap, current)[$o, $f] } (modify.CLIENT.switch_light(heap, current)[$o, $f]) <==> (($o) == (current))))));

axiom ((FieldId(LIGHT_COMMAND.light, LIGHT_COMMAND)) == (81));

axiom ((forall heap: HeapType, o: ref :: { heap[o, LIGHT_COMMAND.light] } ((IsHeap(heap)) && (attached(heap, o, LIGHT_COMMAND))) ==> (detachable(heap, heap[o, LIGHT_COMMAND.light], LIGHT))));

axiom ((forall heap: HeapType, current: ref, v: ref, o: ref :: { guard(heap, current, LIGHT_COMMAND.light, v, o) } (attached_exact(heap, current, LIGHT_COMMAND)) ==> ((guard(heap, current, LIGHT_COMMAND.light, v, o)) <==> ((user_inv(heap, o)) ==> (user_inv(heap[current, LIGHT_COMMAND.light := v], o))))));

axiom ((forall heap: HeapType, current: ref, v: ref, o: ref :: { guard(heap, current, LIGHT_COMMAND.light, v, o) } (attached(heap, current, LIGHT_COMMAND)) ==> ((guard(heap, current, LIGHT_COMMAND.light, v, o)) ==> ((user_inv(heap, o)) ==> (user_inv(heap[current, LIGHT_COMMAND.light := v], o))))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, owns, v, o) } (attached_exact(heap, current, LIGHT_COMMAND)) ==> ((guard(heap, current, owns, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, subjects, v, o) } (attached_exact(heap, current, LIGHT_COMMAND)) ==> ((guard(heap, current, subjects, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached_exact(heap, current, LIGHT_COMMAND)) ==> ((guard(heap, current, observers, v, o)) <==> (fun.LIGHT_COMMAND.in_observers(heap, current, v, o)))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached(heap, current, LIGHT_COMMAND)) ==> ((guard(heap, current, observers, v, o)) ==> (fun.LIGHT_COMMAND.in_observers(heap, current, v, o)))));

function modify.LIGHT_COMMAND.execute(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T25> $o: ref, $f: Field T25 :: { modify.LIGHT_COMMAND.execute(heap, current)[$o, $f] } (modify.LIGHT_COMMAND.execute(heap, current)[$o, $f]) <==> (($o) == (heap[current, LIGHT_COMMAND.light]))))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, owns, v, o) } (attached_exact(heap, current, SWITCH)) ==> ((guard(heap, current, owns, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, subjects, v, o) } (attached_exact(heap, current, SWITCH)) ==> ((guard(heap, current, subjects, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached_exact(heap, current, SWITCH)) ==> ((guard(heap, current, observers, v, o)) <==> (fun.SWITCH.in_observers(heap, current, v, o)))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached(heap, current, SWITCH)) ==> ((guard(heap, current, observers, v, o)) ==> (fun.SWITCH.in_observers(heap, current, v, o)))));

function modify.SWITCH.default_create(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T26> $o: ref, $f: Field T26 :: { modify.SWITCH.default_create(heap, current)[$o, $f] } (modify.SWITCH.default_create(heap, current)[$o, $f]) <==> (($o) == (current))))));

function post.LIGHT_COMMAND.execute(heap: HeapType, old_heap: HeapType, Current: ref) returns (bool);

axiom ((forall heap: HeapType, old_heap: HeapType, current: ref :: ((type_of(current)) <: (LIGHT_COMMAND)) ==> ((post.LIGHT_COMMAND.execute(heap, old_heap, current)) ==> ((is_wrapped(heap, heap[current, LIGHT_COMMAND.light])) && (is_wrapped(heap, current)) && (is_wrapped(heap, current))))));

axiom ((forall heap: HeapType, old_heap: HeapType, current: ref :: ((type_of(current)) <: (FLIP_DOWN_COMMAND)) ==> ((post.LIGHT_COMMAND.execute(heap, old_heap, current)) ==> ((!(heap[heap[current, FLIP_DOWN_COMMAND.light], LIGHT.is_on])) && (is_wrapped(heap, heap[current, FLIP_DOWN_COMMAND.light])) && (is_wrapped(heap, current)) && (is_wrapped(heap, current))))));

axiom ((forall heap: HeapType, old_heap: HeapType, current: ref :: ((type_of(current)) <: (FLIP_UP_COMMAND)) ==> ((post.LIGHT_COMMAND.execute(heap, old_heap, current)) ==> ((heap[heap[current, FLIP_UP_COMMAND.light], LIGHT.is_on]) && (is_wrapped(heap, heap[current, FLIP_UP_COMMAND.light])) && (is_wrapped(heap, current)) && (is_wrapped(heap, current))))));

function modify.SWITCH.execute_command(heap: HeapType, current: ref, cmd: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, cmd: ref :: (IsHeap(heap)) ==> ((forall <T27> $o: ref, $f: Field T27 :: { modify.SWITCH.execute_command(heap, current, cmd)[$o, $f] } (modify.SWITCH.execute_command(heap, current, cmd)[$o, $f]) <==> ((($o) == (current)) || (($o) == (heap[cmd, LIGHT_COMMAND.light])))))));

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

procedure FLIP_UP_COMMAND.in_observers(Current: ref, new_observers: Set (ref), o: ref) returns (Result: bool where true);
  free requires attached_exact(Heap, Current, FLIP_UP_COMMAND); // info:type property for argument Current
  free requires Set#ItemsType(Heap, new_observers, ANY); // info:type property for argument new_observers
  free requires Heap[o, allocated]; // info:type property for argument o
  modifies Heap;
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.FLIP_UP_COMMAND.in_observers(Heap, Current, new_observers, o), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.FLIP_UP_COMMAND.in_observers(old(Heap), Current, new_observers, o));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.FLIP_UP_COMMAND.in_observers(Heap, Current, new_observers, o), readable);



function fun.FLIP_UP_COMMAND.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function fun0.FLIP_UP_COMMAND.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.FLIP_UP_COMMAND.in_observers(heap, current, new_observers, o) } { trigger.fun.FLIP_UP_COMMAND.in_observers(heap, current, new_observers, o) } (pre.fun.FLIP_UP_COMMAND.in_observers(heap, current, new_observers, o)) ==> ((fun.FLIP_UP_COMMAND.in_observers(heap, current, new_observers, o)) == (new_observers[o]))));

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.FLIP_UP_COMMAND.in_observers(heap, current, new_observers, o) } (fun.FLIP_UP_COMMAND.in_observers(heap, current, new_observers, o)) == (fun0.FLIP_UP_COMMAND.in_observers(heap, current, new_observers, o))));

axiom ((forall h: HeapType, h': HeapType, current: ref, new_observers: Set (ref), o: ref :: { HeapSucc(h, h'), fun0.FLIP_UP_COMMAND.in_observers(h, current, new_observers, o), fun0.FLIP_UP_COMMAND.in_observers(h', current, new_observers, o) } ((HeapSucc(h, h')) && (pre.fun.FLIP_UP_COMMAND.in_observers(h, current, new_observers, o)) && (pre.fun.FLIP_UP_COMMAND.in_observers(h', current, new_observers, o)) && (same_inside(h, h', read.fun.FLIP_UP_COMMAND.in_observers(h, current, new_observers, o)))) ==> ((fun0.FLIP_UP_COMMAND.in_observers(h, current, new_observers, o)) == (fun0.FLIP_UP_COMMAND.in_observers(h', current, new_observers, o)))));

procedure LIGHT.in_observers(Current: ref, new_observers: Set (ref), o: ref) returns (Result: bool where true);
  free requires attached_exact(Heap, Current, LIGHT); // info:type property for argument Current
  free requires Set#ItemsType(Heap, new_observers, ANY); // info:type property for argument new_observers
  free requires Heap[o, allocated]; // info:type property for argument o
  modifies Heap;
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.LIGHT.in_observers(Heap, Current, new_observers, o), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.LIGHT.in_observers(old(Heap), Current, new_observers, o));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.LIGHT.in_observers(Heap, Current, new_observers, o), readable);



function fun.LIGHT.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function fun0.LIGHT.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.LIGHT.in_observers(heap, current, new_observers, o) } { trigger.fun.LIGHT.in_observers(heap, current, new_observers, o) } (pre.fun.LIGHT.in_observers(heap, current, new_observers, o)) ==> ((fun.LIGHT.in_observers(heap, current, new_observers, o)) == (new_observers[o]))));

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.LIGHT.in_observers(heap, current, new_observers, o) } (fun.LIGHT.in_observers(heap, current, new_observers, o)) == (fun0.LIGHT.in_observers(heap, current, new_observers, o))));

axiom ((forall h: HeapType, h': HeapType, current: ref, new_observers: Set (ref), o: ref :: { HeapSucc(h, h'), fun0.LIGHT.in_observers(h, current, new_observers, o), fun0.LIGHT.in_observers(h', current, new_observers, o) } ((HeapSucc(h, h')) && (pre.fun.LIGHT.in_observers(h, current, new_observers, o)) && (pre.fun.LIGHT.in_observers(h', current, new_observers, o)) && (same_inside(h, h', read.fun.LIGHT.in_observers(h, current, new_observers, o)))) ==> ((fun0.LIGHT.in_observers(h, current, new_observers, o)) == (fun0.LIGHT.in_observers(h', current, new_observers, o)))));

procedure FLIP_DOWN_COMMAND.in_observers(Current: ref, new_observers: Set (ref), o: ref) returns (Result: bool where true);
  free requires attached_exact(Heap, Current, FLIP_DOWN_COMMAND); // info:type property for argument Current
  free requires Set#ItemsType(Heap, new_observers, ANY); // info:type property for argument new_observers
  free requires Heap[o, allocated]; // info:type property for argument o
  modifies Heap;
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.FLIP_DOWN_COMMAND.in_observers(Heap, Current, new_observers, o), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.FLIP_DOWN_COMMAND.in_observers(old(Heap), Current, new_observers, o));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.FLIP_DOWN_COMMAND.in_observers(Heap, Current, new_observers, o), readable);



function fun.FLIP_DOWN_COMMAND.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function fun0.FLIP_DOWN_COMMAND.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.FLIP_DOWN_COMMAND.in_observers(heap, current, new_observers, o) } { trigger.fun.FLIP_DOWN_COMMAND.in_observers(heap, current, new_observers, o) } (pre.fun.FLIP_DOWN_COMMAND.in_observers(heap, current, new_observers, o)) ==> ((fun.FLIP_DOWN_COMMAND.in_observers(heap, current, new_observers, o)) == (new_observers[o]))));

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.FLIP_DOWN_COMMAND.in_observers(heap, current, new_observers, o) } (fun.FLIP_DOWN_COMMAND.in_observers(heap, current, new_observers, o)) == (fun0.FLIP_DOWN_COMMAND.in_observers(heap, current, new_observers, o))));

axiom ((forall h: HeapType, h': HeapType, current: ref, new_observers: Set (ref), o: ref :: { HeapSucc(h, h'), fun0.FLIP_DOWN_COMMAND.in_observers(h, current, new_observers, o), fun0.FLIP_DOWN_COMMAND.in_observers(h', current, new_observers, o) } ((HeapSucc(h, h')) && (pre.fun.FLIP_DOWN_COMMAND.in_observers(h, current, new_observers, o)) && (pre.fun.FLIP_DOWN_COMMAND.in_observers(h', current, new_observers, o)) && (same_inside(h, h', read.fun.FLIP_DOWN_COMMAND.in_observers(h, current, new_observers, o)))) ==> ((fun0.FLIP_DOWN_COMMAND.in_observers(h, current, new_observers, o)) == (fun0.FLIP_DOWN_COMMAND.in_observers(h', current, new_observers, o)))));

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

procedure LIGHT_COMMAND.in_observers(Current: ref, new_observers: Set (ref), o: ref) returns (Result: bool where true);
  free requires attached_exact(Heap, Current, LIGHT_COMMAND); // info:type property for argument Current
  free requires Set#ItemsType(Heap, new_observers, ANY); // info:type property for argument new_observers
  free requires Heap[o, allocated]; // info:type property for argument o
  modifies Heap;
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.LIGHT_COMMAND.in_observers(Heap, Current, new_observers, o), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.LIGHT_COMMAND.in_observers(old(Heap), Current, new_observers, o));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.LIGHT_COMMAND.in_observers(Heap, Current, new_observers, o), readable);



function fun.LIGHT_COMMAND.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function fun0.LIGHT_COMMAND.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.LIGHT_COMMAND.in_observers(heap, current, new_observers, o) } { trigger.fun.LIGHT_COMMAND.in_observers(heap, current, new_observers, o) } (pre.fun.LIGHT_COMMAND.in_observers(heap, current, new_observers, o)) ==> ((fun.LIGHT_COMMAND.in_observers(heap, current, new_observers, o)) == (new_observers[o]))));

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.LIGHT_COMMAND.in_observers(heap, current, new_observers, o) } (fun.LIGHT_COMMAND.in_observers(heap, current, new_observers, o)) == (fun0.LIGHT_COMMAND.in_observers(heap, current, new_observers, o))));

axiom ((forall h: HeapType, h': HeapType, current: ref, new_observers: Set (ref), o: ref :: { HeapSucc(h, h'), fun0.LIGHT_COMMAND.in_observers(h, current, new_observers, o), fun0.LIGHT_COMMAND.in_observers(h', current, new_observers, o) } ((HeapSucc(h, h')) && (pre.fun.LIGHT_COMMAND.in_observers(h, current, new_observers, o)) && (pre.fun.LIGHT_COMMAND.in_observers(h', current, new_observers, o)) && (same_inside(h, h', read.fun.LIGHT_COMMAND.in_observers(h, current, new_observers, o)))) ==> ((fun0.LIGHT_COMMAND.in_observers(h, current, new_observers, o)) == (fun0.LIGHT_COMMAND.in_observers(h', current, new_observers, o)))));

procedure SWITCH.in_observers(Current: ref, new_observers: Set (ref), o: ref) returns (Result: bool where true);
  free requires attached_exact(Heap, Current, SWITCH); // info:type property for argument Current
  free requires Set#ItemsType(Heap, new_observers, ANY); // info:type property for argument new_observers
  free requires Heap[o, allocated]; // info:type property for argument o
  modifies Heap;
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.SWITCH.in_observers(Heap, Current, new_observers, o), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.SWITCH.in_observers(old(Heap), Current, new_observers, o));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.SWITCH.in_observers(Heap, Current, new_observers, o), readable);



function fun.SWITCH.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function fun0.SWITCH.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.SWITCH.in_observers(heap, current, new_observers, o) } { trigger.fun.SWITCH.in_observers(heap, current, new_observers, o) } (pre.fun.SWITCH.in_observers(heap, current, new_observers, o)) ==> ((fun.SWITCH.in_observers(heap, current, new_observers, o)) == (new_observers[o]))));

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.SWITCH.in_observers(heap, current, new_observers, o) } (fun.SWITCH.in_observers(heap, current, new_observers, o)) == (fun0.SWITCH.in_observers(heap, current, new_observers, o))));

axiom ((forall h: HeapType, h': HeapType, current: ref, new_observers: Set (ref), o: ref :: { HeapSucc(h, h'), fun0.SWITCH.in_observers(h, current, new_observers, o), fun0.SWITCH.in_observers(h', current, new_observers, o) } ((HeapSucc(h, h')) && (pre.fun.SWITCH.in_observers(h, current, new_observers, o)) && (pre.fun.SWITCH.in_observers(h', current, new_observers, o)) && (same_inside(h, h', read.fun.SWITCH.in_observers(h, current, new_observers, o)))) ==> ((fun0.SWITCH.in_observers(h, current, new_observers, o)) == (fun0.SWITCH.in_observers(h', current, new_observers, o)))));

function modify.ANY.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T28> $o: ref, $f: Field T28 :: { modify.ANY.in_observers(heap, current, new_observers, o)[$o, $f] } (modify.ANY.in_observers(heap, current, new_observers, o)[$o, $f]) <==> (false)))));

function read.fun.ANY.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T29> $o: ref, $f: Field T29 :: { read.fun.ANY.in_observers(heap, current, new_observers, o)[$o, $f] } (read.fun.ANY.in_observers(heap, current, new_observers, o)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.ANY.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool) {
  true
}

function trigger.fun.ANY.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function modify.FLIP_UP_COMMAND.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T30> $o: ref, $f: Field T30 :: { modify.FLIP_UP_COMMAND.in_observers(heap, current, new_observers, o)[$o, $f] } (modify.FLIP_UP_COMMAND.in_observers(heap, current, new_observers, o)[$o, $f]) <==> (false)))));

function read.fun.FLIP_UP_COMMAND.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T31> $o: ref, $f: Field T31 :: { read.fun.FLIP_UP_COMMAND.in_observers(heap, current, new_observers, o)[$o, $f] } (read.fun.FLIP_UP_COMMAND.in_observers(heap, current, new_observers, o)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.FLIP_UP_COMMAND.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool) {
  true
}

function trigger.fun.FLIP_UP_COMMAND.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function modify.LIGHT.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T32> $o: ref, $f: Field T32 :: { modify.LIGHT.in_observers(heap, current, new_observers, o)[$o, $f] } (modify.LIGHT.in_observers(heap, current, new_observers, o)[$o, $f]) <==> (false)))));

function read.fun.LIGHT.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T33> $o: ref, $f: Field T33 :: { read.fun.LIGHT.in_observers(heap, current, new_observers, o)[$o, $f] } (read.fun.LIGHT.in_observers(heap, current, new_observers, o)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.LIGHT.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool) {
  true
}

function trigger.fun.LIGHT.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function modify.FLIP_DOWN_COMMAND.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T34> $o: ref, $f: Field T34 :: { modify.FLIP_DOWN_COMMAND.in_observers(heap, current, new_observers, o)[$o, $f] } (modify.FLIP_DOWN_COMMAND.in_observers(heap, current, new_observers, o)[$o, $f]) <==> (false)))));

function read.fun.FLIP_DOWN_COMMAND.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T35> $o: ref, $f: Field T35 :: { read.fun.FLIP_DOWN_COMMAND.in_observers(heap, current, new_observers, o)[$o, $f] } (read.fun.FLIP_DOWN_COMMAND.in_observers(heap, current, new_observers, o)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.FLIP_DOWN_COMMAND.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool) {
  true
}

function trigger.fun.FLIP_DOWN_COMMAND.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function modify.CLIENT.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T36> $o: ref, $f: Field T36 :: { modify.CLIENT.in_observers(heap, current, new_observers, o)[$o, $f] } (modify.CLIENT.in_observers(heap, current, new_observers, o)[$o, $f]) <==> (false)))));

function read.fun.CLIENT.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T37> $o: ref, $f: Field T37 :: { read.fun.CLIENT.in_observers(heap, current, new_observers, o)[$o, $f] } (read.fun.CLIENT.in_observers(heap, current, new_observers, o)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.CLIENT.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool) {
  true
}

function trigger.fun.CLIENT.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function modify.LIGHT_COMMAND.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T38> $o: ref, $f: Field T38 :: { modify.LIGHT_COMMAND.in_observers(heap, current, new_observers, o)[$o, $f] } (modify.LIGHT_COMMAND.in_observers(heap, current, new_observers, o)[$o, $f]) <==> (false)))));

function read.fun.LIGHT_COMMAND.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T39> $o: ref, $f: Field T39 :: { read.fun.LIGHT_COMMAND.in_observers(heap, current, new_observers, o)[$o, $f] } (read.fun.LIGHT_COMMAND.in_observers(heap, current, new_observers, o)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.LIGHT_COMMAND.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool) {
  true
}

function trigger.fun.LIGHT_COMMAND.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function modify.SWITCH.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T40> $o: ref, $f: Field T40 :: { modify.SWITCH.in_observers(heap, current, new_observers, o)[$o, $f] } (modify.SWITCH.in_observers(heap, current, new_observers, o)[$o, $f]) <==> (false)))));

function read.fun.SWITCH.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T41> $o: ref, $f: Field T41 :: { read.fun.SWITCH.in_observers(heap, current, new_observers, o)[$o, $f] } (read.fun.SWITCH.in_observers(heap, current, new_observers, o)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.SWITCH.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool) {
  true
}

function trigger.fun.SWITCH.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);
