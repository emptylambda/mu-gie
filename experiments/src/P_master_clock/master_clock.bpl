// Automatically generated (12/12/2017 1:54:52.881 PM)

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

const unique MASTER: Type;

axiom (is_frozen(MASTER));

axiom ((MASTER) <: (ANY));

axiom ((forall t: Type :: { (MASTER) <: (t) } ((MASTER) <: (t)) <==> (((t) == (MASTER)) || ((ANY) <: (t)))));

axiom ((FieldId(allocated, MASTER)) == (-1));

axiom ((FieldId(closed, MASTER)) == (-2));

axiom ((FieldId(owner, MASTER)) == (-3));

axiom ((FieldId(owns, MASTER)) == (-4));

axiom ((FieldId(observers, MASTER)) == (-5));

axiom ((FieldId(subjects, MASTER)) == (-6));

axiom ((forall <T0> $f: Field T0 :: { IsModelField($f, MASTER) } (IsModelField($f, MASTER)) <==> ((($f) == (subjects)) || (($f) == (observers)))));

function { :inline } MASTER.user_inv(heap: HeapType, current: ref) returns (bool) {
  ((0) <= (heap[current, MASTER.time])) && (Set#IsEmpty(heap[current, subjects])) && (Set#IsEmpty(heap[current, owns])) && (admissibility2(heap, current))
}

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached_exact(heap, current, MASTER)) ==> ((user_inv(heap, current)) <==> (MASTER.user_inv(heap, current)))));

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached(heap, current, MASTER)) ==> ((user_inv(heap, current)) ==> (MASTER.user_inv(heap, current)))));

procedure MASTER.invariant_admissibility_check(Current: ref);
  requires attached_exact(Heap, Current, MASTER);



implementation MASTER.invariant_admissibility_check(Current: ref)
{
  entry:
  goto pre, a2, a3;
  pre:
  assert user_inv_readable(Heap, Current)[Current, MASTER.time]; // type:access tag:attribute_readable line:68 cid:404 fid:81
  assume (0) <= (Heap[Current, MASTER.time]);
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

procedure create.MASTER.make(Current: ref);
  free requires attached_exact(Heap, Current, MASTER); // info:type property for argument Current
  modifies Heap;
  ensures (Heap[Current, MASTER.time]) == (0); // type:post tag:time_reset line:18
  ensures Set#IsEmpty(Heap[Current, observers]); // type:post tag:no_observers line:19
  requires (forall <T3> $f: Field T3 :: (($f) != (allocated)) ==> ((Heap[Current, $f]) == (Default($f))));
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.MASTER.make(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.MASTER.make(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts



implementation create.MASTER.make(Current: ref)
{
  entry:
  assume {:captureState "create.MASTER.make"} true;
  if (*) {
    assert (0) <= (Heap[Current, MASTER.time]); // type:inv tag:time_non_negative line:55 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, subjects]); // type:inv tag:default_subjects line:55 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, owns]); // type:inv tag:default_owns line:55 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert admissibility2(Heap, Current); // type:inv tag:A2 line:55 cid:1 rid:55
    assume false;
  }
  call wrap(Current); // default:wrapping cid:1 rid:55 line:20
}

procedure MASTER.tick(Current: ref);
  free requires attached_exact(Heap, Current, MASTER); // info:type property for argument Current
  modifies Heap;
  ensures (Heap[Current, MASTER.time]) > (old(Heap)[Current, MASTER.time]); // type:post tag:time_increased line:41
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.MASTER.tick(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.MASTER.tick(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);
  requires is_wrapped(Heap, Current); // type:pre tag:default_is_wrapped default:contracts
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts



function { :inline } variant.MASTER.tick.1(heap: HeapType, current: ref) returns (int) {
  0
}

implementation MASTER.tick(Current: ref)
{
  entry:
  assume {:captureState "MASTER.tick"} true;
  call unwrap(Current); // default:wrapping cid:1 rid:57 line:33
  assume MASTER.user_inv(Heap, Current);
  // /home/caf/temp/comcom/repo-master_clock/master.e:39
  // time := time + 1
  call update_heap(Current, MASTER.time, (Heap[Current, MASTER.time]) + (1)); // line:39
  if (*) {
    assert (0) <= (Heap[Current, MASTER.time]); // type:inv tag:time_non_negative line:55 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, subjects]); // type:inv tag:default_subjects line:55 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, owns]); // type:inv tag:default_owns line:55 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert admissibility2(Heap, Current); // type:inv tag:A2 line:55 cid:1 rid:55
    assume false;
  }
  call wrap(Current); // default:wrapping cid:1 rid:55 line:42
}

procedure MASTER.reset(Current: ref);
  free requires attached_exact(Heap, Current, MASTER); // info:type property for argument Current
  modifies Heap;
  requires (forall i_1: ref :: (Heap[Current, observers][i_1]) ==> (is_open(Heap, i_1))); // type:pre tag:observers_open line:47
  ensures (Heap[Current, MASTER.time]) == (0); // type:post tag:time_reset line:54
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.MASTER.reset(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.MASTER.reset(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);
  requires is_wrapped(Heap, Current); // type:pre tag:default_is_wrapped default:contracts
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts



function { :inline } variant.MASTER.reset.1(heap: HeapType, current: ref) returns (int) {
  0
}

implementation MASTER.reset(Current: ref)
{
  entry:
  assume {:captureState "MASTER.reset"} true;
  call unwrap(Current); // default:wrapping cid:1 rid:57 line:44
  assume MASTER.user_inv(Heap, Current);
  // /home/caf/temp/comcom/repo-master_clock/master.e:52
  // time := 0
  call update_heap(Current, MASTER.time, 0); // line:52
  if (*) {
    assert (0) <= (Heap[Current, MASTER.time]); // type:inv tag:time_non_negative line:55 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, subjects]); // type:inv tag:default_subjects line:55 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, owns]); // type:inv tag:default_owns line:55 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert admissibility2(Heap, Current); // type:inv tag:A2 line:55 cid:1 rid:55
    assume false;
  }
  call wrap(Current); // default:wrapping cid:1 rid:55 line:55
}

procedure MASTER.time_increased(Current: ref, new_time: int, o: ref) returns (Result: bool where true);
  free requires attached_exact(Heap, Current, MASTER); // info:type property for argument Current
  free requires is_integer_32(new_time); // info:type property for argument new_time
  free requires Heap[o, allocated]; // info:type property for argument o
  modifies Heap;
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.MASTER.time_increased(Heap, Current, new_time, o), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.MASTER.time_increased(old(Heap), Current, new_time, o));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.MASTER.time_increased(Heap, Current, new_time, o), readable);



function fun.MASTER.time_increased(heap: HeapType, current: ref, new_time: int, o: ref) returns (bool);

function fun0.MASTER.time_increased(heap: HeapType, current: ref, new_time: int, o: ref) returns (bool);

axiom ((forall heap: HeapType, current: ref, new_time: int, o: ref :: { fun.MASTER.time_increased(heap, current, new_time, o) } { trigger.fun.MASTER.time_increased(heap, current, new_time, o) } (pre.fun.MASTER.time_increased(heap, current, new_time, o)) ==> ((fun.MASTER.time_increased(heap, current, new_time, o)) == ((new_time) >= (heap[current, MASTER.time])))));

axiom ((forall heap: HeapType, current: ref, new_time: int, o: ref :: { fun.MASTER.time_increased(heap, current, new_time, o) } (fun.MASTER.time_increased(heap, current, new_time, o)) == (fun0.MASTER.time_increased(heap, current, new_time, o))));

axiom ((forall h: HeapType, h': HeapType, current: ref, new_time: int, o: ref :: { HeapSucc(h, h'), fun0.MASTER.time_increased(h, current, new_time, o), fun0.MASTER.time_increased(h', current, new_time, o) } ((HeapSucc(h, h')) && (pre.fun.MASTER.time_increased(h, current, new_time, o)) && (pre.fun.MASTER.time_increased(h', current, new_time, o)) && (same_inside(h, h', read.fun.MASTER.time_increased(h, current, new_time, o)))) ==> ((fun0.MASTER.time_increased(h, current, new_time, o)) == (fun0.MASTER.time_increased(h', current, new_time, o)))));

function { :inline } variant.MASTER.time_increased.1(heap: HeapType, current: ref, new_time: int, o: ref) returns (int) {
  new_time
}

function { :inline } variant.MASTER.time_increased.2(heap: HeapType, current: ref, new_time: int, o: ref) returns (ref) {
  o
}

implementation MASTER.time_increased(Current: ref, new_time: int, o: ref) returns (Result: bool)
{

  init_locals:
  Result := false;

  entry:
  assume {:captureState "MASTER.time_increased"} true;
  // /home/caf/temp/comcom/repo-master_clock/master.e:64
  // Result := new_time >= time
  assert readable[Current, MASTER.time]; // type:access tag:attribute_readable line:64 cid:404 fid:81
  Result := (new_time) >= (Heap[Current, MASTER.time]);
}

const unique CLOCK: Type;

axiom ((CLOCK) <: (ANY));

axiom ((forall t: Type :: { (CLOCK) <: (t) } ((CLOCK) <: (t)) <==> (((t) == (CLOCK)) || ((ANY) <: (t)))));

axiom ((FieldId(allocated, CLOCK)) == (-1));

axiom ((FieldId(closed, CLOCK)) == (-2));

axiom ((FieldId(owner, CLOCK)) == (-3));

axiom ((FieldId(owns, CLOCK)) == (-4));

axiom ((FieldId(observers, CLOCK)) == (-5));

axiom ((FieldId(subjects, CLOCK)) == (-6));

axiom ((forall <T4> $f: Field T4 :: { IsModelField($f, CLOCK) } (IsModelField($f, CLOCK)) <==> ((($f) == (subjects)) || (($f) == (observers)))));

function { :inline } CLOCK.user_inv(heap: HeapType, current: ref) returns (bool) {
  ((heap[current, CLOCK.master]) != (Void)) && (Set#Equal(heap[current, subjects], Set#Singleton(heap[current, CLOCK.master]))) && ((0) <= (heap[current, CLOCK.local_time])) && ((heap[current, CLOCK.local_time]) <= (heap[heap[current, CLOCK.master], MASTER.time])) && (Set#IsEmpty(heap[current, observers])) && (Set#IsEmpty(heap[current, owns])) && (admissibility2(heap, current))
}

function CLOCK.subjects.static(heap: HeapType, current: ref) returns (Set (ref)) {
  Set#Singleton(heap[current, CLOCK.master])
}

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached_exact(heap, current, CLOCK)) ==> ((user_inv(heap, current)) <==> (CLOCK.user_inv(heap, current)))));

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached(heap, current, CLOCK)) ==> ((user_inv(heap, current)) ==> (CLOCK.user_inv(heap, current)))));

procedure CLOCK.invariant_admissibility_check(Current: ref);
  requires attached_exact(Heap, Current, CLOCK);



implementation CLOCK.invariant_admissibility_check(Current: ref)
{
  entry:
  goto pre, a2, a3;
  pre:
  assert user_inv_readable(Heap, Current)[Current, CLOCK.master]; // type:access tag:attribute_readable line:64 cid:406 fid:81
  assume (Heap[Current, CLOCK.master]) != (Void);
  assert user_inv_readable(Heap, Current)[Current, CLOCK.master]; // type:access tag:attribute_readable line:65 cid:406 fid:81
  assume Set#Equal(Heap[Current, subjects], Set#Singleton(Heap[Current, CLOCK.master]));
  assert user_inv_readable(Heap, Current)[Current, CLOCK.local_time]; // type:access tag:attribute_readable line:66 cid:406 fid:82
  assume (0) <= (Heap[Current, CLOCK.local_time]);
  assert user_inv_readable(Heap, Current)[Current, CLOCK.local_time]; // type:access tag:attribute_readable line:67 cid:406 fid:82
  assert user_inv_readable(Heap, Current)[Current, CLOCK.master]; // type:access tag:attribute_readable line:67 cid:406 fid:81
  assert {:subsumption 0} (Heap[Current, CLOCK.master]) != (Void); // type:attached tag:time_weakly_synchronized line:67
  assert user_inv_readable(Heap, Current)[Heap[Current, CLOCK.master], MASTER.time]; // type:access tag:attribute_readable line:67 cid:404 fid:81
  assume (Heap[Current, CLOCK.local_time]) <= (Heap[Heap[Current, CLOCK.master], MASTER.time]);
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

procedure create.CLOCK.make(Current: ref, m: ref);
  free requires attached_exact(Heap, Current, CLOCK); // info:type property for argument Current
  free requires detachable_exact(Heap, m, MASTER); // info:type property for argument m
  modifies Heap;
  requires (m) != (Void); // type:pre tag:m_exists line:17
  ensures (Heap[Current, CLOCK.master]) == (m); // type:post tag:master_set line:28
  ensures (m) != (Void); // type:attached tag:time_synchronized line:29
  ensures (Heap[Current, CLOCK.local_time]) == (Heap[m, MASTER.time]); // type:post tag:time_synchronized line:29
  ensures Set#Equal(Heap[m, observers], Set#Union(old(Heap)[m, observers], Set#Singleton(Current))); // type:post tag:observing_master line:30
  requires (forall <T5> $f: Field T5 :: (($f) != (allocated)) ==> ((Heap[Current, $f]) == (Default($f))));
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.CLOCK.make(Heap, Current, m), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.CLOCK.make(old(Heap), Current, m));
  free ensures HeapSucc(old(Heap), Heap);
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts
  requires is_wrapped(Heap, m); // type:pre tag:arg_m_is_wrapped default:contracts
  ensures is_wrapped(Heap, m); // type:post tag:arg_m_is_wrapped default:contracts



implementation create.CLOCK.make(Current: ref, m: ref)
{
  entry:
  assume {:captureState "create.CLOCK.make"} true;
  // /home/caf/temp/comcom/repo-master_clock/clock.e:21
  // master := m
  call update_heap(Current, CLOCK.master, m); // line:21
  // /home/caf/temp/comcom/repo-master_clock/clock.e:22
  // local_time := master.time
  assert {:subsumption 0} (Heap[Current, CLOCK.master]) != (Void); // type:attached line:22
  call update_heap(Current, CLOCK.local_time, Heap[Heap[Current, CLOCK.master], MASTER.time]); // line:22
  // /home/caf/temp/comcom/repo-master_clock/clock.e:24
  // m.unwrap
  assert {:subsumption 0} (m) != (Void); // type:attached line:24
  call unwrap(m); // line:24 cid:1 rid:57
  assume MASTER.user_inv(Heap, m);
  // /home/caf/temp/comcom/repo-master_clock/clock.e:25
  // m.set_observers (m.observers + [Current])
  assert {:subsumption 0} (m) != (Void); // type:attached line:25
  assert {:subsumption 0} (m) != (Void); // type:attached line:25
  call update_heap(m, observers, Set#Union(Heap[m, observers], Set#Singleton(Current))); // line:25
  // /home/caf/temp/comcom/repo-master_clock/clock.e:26
  // m.wrap
  assert {:subsumption 0} (m) != (Void); // type:attached line:26
  if (*) {
    assert (0) <= (Heap[m, MASTER.time]); // type:inv tag:time_non_negative line:26 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[m, subjects]); // type:inv tag:default_subjects line:26 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[m, owns]); // type:inv tag:default_owns line:26 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert admissibility2(Heap, m); // type:inv tag:A2 line:26 cid:1 rid:55
    assume false;
  }
  call wrap(m); // line:26 cid:1 rid:55
  if (modify.CLOCK.make(Heap, Current, m)[Current, subjects]) {
    call update_heap(Current, subjects, CLOCK.subjects.static(Heap, Current)); // default:subjects line:31
  }
  if (*) {
    assert (Heap[Current, CLOCK.master]) != (Void); // type:inv tag:master_exists line:31 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#Equal(Heap[Current, subjects], Set#Singleton(Heap[Current, CLOCK.master])); // type:inv tag:subjects_structure line:31 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert (0) <= (Heap[Current, CLOCK.local_time]); // type:inv tag:time_non_negative line:31 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert (Heap[Current, CLOCK.local_time]) <= (Heap[Heap[Current, CLOCK.master], MASTER.time]); // type:inv tag:time_weakly_synchronized line:31 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, observers]); // type:inv tag:default_observers line:31 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, owns]); // type:inv tag:default_owns line:31 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert admissibility2(Heap, Current); // type:inv tag:A2 line:31 cid:1 rid:55
    assume false;
  }
  call wrap(Current); // default:wrapping cid:1 rid:55 line:31
}

procedure CLOCK.sync(Current: ref);
  free requires attached_exact(Heap, Current, CLOCK); // info:type property for argument Current
  modifies Heap;
  requires is_free(Heap, Current); // type:pre tag:free line:48
  requires CLOCK#E#time_weakly_synchronized.filtered_inv(Heap, Current); // type:pre tag:partially_holds line:49
  requires (Heap[Current, CLOCK.master]) != (Void); // type:attached tag:master_wrapped line:50
  requires is_wrapped(Heap, Heap[Current, CLOCK.master]); // type:pre tag:master_wrapped line:50
  ensures (Heap[Current, CLOCK.master]) != (Void); // type:attached tag:time_synchronized line:59
  ensures (Heap[Current, CLOCK.local_time]) == (Heap[Heap[Current, CLOCK.master], MASTER.time]); // type:post tag:time_synchronized line:59
  ensures is_wrapped(Heap, Current); // type:post tag:wrapped line:60
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.CLOCK.sync(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.CLOCK.sync(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);



function { :inline } variant.CLOCK.sync.1(heap: HeapType, current: ref) returns (int) {
  0
}

implementation CLOCK.sync(Current: ref)
{
  entry:
  assume {:captureState "CLOCK.sync"} true;
  // /home/caf/temp/comcom/repo-master_clock/clock.e:53
  // if closed then
  if (is_closed(Heap, Current)) {
    // /home/caf/temp/comcom/repo-master_clock/clock.e:54
    // unwrap
    call unwrap(Current); // line:54 cid:1 rid:57
    assume CLOCK.user_inv(Heap, Current);
  }
  // /home/caf/temp/comcom/repo-master_clock/clock.e:56
  // local_time := master.time
  assert {:subsumption 0} (Heap[Current, CLOCK.master]) != (Void); // type:attached line:56
  call update_heap(Current, CLOCK.local_time, Heap[Heap[Current, CLOCK.master], MASTER.time]); // line:56
  // /home/caf/temp/comcom/repo-master_clock/clock.e:57
  // wrap
  if (modify.CLOCK.sync(Heap, Current)[Current, subjects]) {
    call update_heap(Current, subjects, CLOCK.subjects.static(Heap, Current)); // default:subjects line:57
  }
  if (*) {
    assert (Heap[Current, CLOCK.master]) != (Void); // type:inv tag:master_exists line:57 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#Equal(Heap[Current, subjects], Set#Singleton(Heap[Current, CLOCK.master])); // type:inv tag:subjects_structure line:57 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert (0) <= (Heap[Current, CLOCK.local_time]); // type:inv tag:time_non_negative line:57 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert (Heap[Current, CLOCK.local_time]) <= (Heap[Heap[Current, CLOCK.master], MASTER.time]); // type:inv tag:time_weakly_synchronized line:57 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, observers]); // type:inv tag:default_observers line:57 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, owns]); // type:inv tag:default_owns line:57 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert admissibility2(Heap, Current); // type:inv tag:A2 line:57 cid:1 rid:55
    assume false;
  }
  call wrap(Current); // line:57 cid:1 rid:55
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
    assert Set#IsEmpty(Heap[Current, observers]); // type:inv tag:default_observers line:36 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, subjects]); // type:inv tag:default_subjects line:36 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, owns]); // type:inv tag:default_owns line:36 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert admissibility2(Heap, Current); // type:inv tag:A2 line:36 cid:1 rid:55
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
  var temp_2: ref;
  var temp_3: ref;
  var temp_4: ref;
  var local1: ref where detachable_exact(Heap, local1, MASTER);
  var local2: ref where detachable(Heap, local2, CLOCK);
  var local3: ref where detachable(Heap, local3, CLOCK);

  init_locals:
  temp_2 := Void;
  temp_3 := Void;
  temp_4 := Void;
  local1 := Void;
  local2 := Void;
  local3 := Void;

  entry:
  assume {:captureState "CLIENT.test"} true;
  call unwrap(Current); // default:wrapping cid:1 rid:57 line:9
  assume CLIENT.user_inv(Heap, Current);
  // /home/caf/temp/comcom/repo-master_clock/client.e:15
  // create m.make
  call temp_2 := allocate(MASTER); // line:-1
  call create.MASTER.make(temp_2); // line:15 cid:404 rid:5406
  local1 := temp_2;
  // /home/caf/temp/comcom/repo-master_clock/client.e:16
  // create c1.make (m)
  call temp_3 := allocate(CLOCK); // line:-1
  call create.CLOCK.make(temp_3, local1); // line:16 cid:406 rid:5401
  local2 := temp_3;
  // /home/caf/temp/comcom/repo-master_clock/client.e:17
  // create c2.make (m)
  call temp_4 := allocate(CLOCK); // line:-1
  call create.CLOCK.make(temp_4, local1); // line:17 cid:406 rid:5401
  local3 := temp_4;
  // /home/caf/temp/comcom/repo-master_clock/client.e:19
  // m.tick
  assert {:subsumption 0} (local1) != (Void); // type:attached line:19
  call MASTER.tick(local1); // line:19 cid:404 rid:5408
  // /home/caf/temp/comcom/repo-master_clock/client.e:21
  // check c1_in_synch: c1.local_time <= m.time end
  assert {:subsumption 0} (local2) != (Void); // type:attached line:21
  assert {:subsumption 0} (local1) != (Void); // type:attached line:21
  assert (Heap[local2, CLOCK.local_time]) <= (Heap[local1, MASTER.time]); // type:check tag:c1_in_synch line:21
  // /home/caf/temp/comcom/repo-master_clock/client.e:22
  // check c2_in_synch: c2.local_time <= m.time end
  assert {:subsumption 0} (local3) != (Void); // type:attached line:22
  assert {:subsumption 0} (local1) != (Void); // type:attached line:22
  assert (Heap[local3, CLOCK.local_time]) <= (Heap[local1, MASTER.time]); // type:check tag:c2_in_synch line:22
  // /home/caf/temp/comcom/repo-master_clock/client.e:24
  // c1.sync
  assert {:subsumption 0} (local2) != (Void); // type:attached line:24
  call CLOCK.sync(local2); // line:24 cid:406 rid:5404
  // /home/caf/temp/comcom/repo-master_clock/client.e:25
  // c2.sync
  assert {:subsumption 0} (local3) != (Void); // type:attached line:25
  call CLOCK.sync(local3); // line:25 cid:406 rid:5404
  // /home/caf/temp/comcom/repo-master_clock/client.e:27
  // unwrap_all ([c1, c2])
  call unwrap_all(Current, Set#Extended(Set#Singleton(local2), local3)); // line:27 cid:1 rid:59
  // /home/caf/temp/comcom/repo-master_clock/client.e:28
  // m.reset
  assert {:subsumption 0} (local1) != (Void); // type:attached line:28
  call MASTER.reset(local1); // line:28 cid:404 rid:5409
  // /home/caf/temp/comcom/repo-master_clock/client.e:30
  // c1.sync
  assert {:subsumption 0} (local2) != (Void); // type:attached line:30
  call CLOCK.sync(local2); // line:30 cid:406 rid:5404
  // /home/caf/temp/comcom/repo-master_clock/client.e:31
  // c2.sync
  assert {:subsumption 0} (local3) != (Void); // type:attached line:31
  call CLOCK.sync(local3); // line:31 cid:406 rid:5404
  // /home/caf/temp/comcom/repo-master_clock/client.e:34
  // check c1_in_synch: c1.local_time <= m.time end
  assert {:subsumption 0} (local2) != (Void); // type:attached line:34
  assert {:subsumption 0} (local1) != (Void); // type:attached line:34
  assert (Heap[local2, CLOCK.local_time]) <= (Heap[local1, MASTER.time]); // type:check tag:c1_in_synch line:34
  // /home/caf/temp/comcom/repo-master_clock/client.e:35
  // check c2_in_synch: c2.local_time <= m.time end
  assert {:subsumption 0} (local3) != (Void); // type:attached line:35
  assert {:subsumption 0} (local1) != (Void); // type:attached line:35
  assert (Heap[local3, CLOCK.local_time]) <= (Heap[local1, MASTER.time]); // type:check tag:c2_in_synch line:35
  if (*) {
    assert Set#IsEmpty(Heap[Current, observers]); // type:inv tag:default_observers line:36 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, subjects]); // type:inv tag:default_subjects line:36 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, owns]); // type:inv tag:default_owns line:36 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert admissibility2(Heap, Current); // type:inv tag:A2 line:36 cid:1 rid:55
    assume false;
  }
  call wrap(Current); // default:wrapping cid:1 rid:55 line:36
}

const MASTER.time: Field int;

axiom ((FieldId(MASTER.time, MASTER)) == (81));

axiom ((forall heap: HeapType, o: ref :: { heap[o, MASTER.time] } ((IsHeap(heap)) && (attached(heap, o, MASTER))) ==> (is_integer_32(heap[o, MASTER.time]))));

axiom ((forall heap: HeapType, current: ref, v: int, o: ref :: { guard(heap, current, MASTER.time, v, o) } (attached_exact(heap, current, MASTER)) ==> ((guard(heap, current, MASTER.time, v, o)) <==> (fun.MASTER.time_increased(heap, current, v, o)))));

axiom ((forall heap: HeapType, current: ref, v: int, o: ref :: { guard(heap, current, MASTER.time, v, o) } (attached(heap, current, MASTER)) ==> ((guard(heap, current, MASTER.time, v, o)) ==> (fun.MASTER.time_increased(heap, current, v, o)))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, owns, v, o) } (attached_exact(heap, current, ANY)) ==> ((guard(heap, current, owns, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, subjects, v, o) } (attached_exact(heap, current, ANY)) ==> ((guard(heap, current, subjects, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached_exact(heap, current, ANY)) ==> ((guard(heap, current, observers, v, o)) <==> (fun.ANY.in_observers(heap, current, v, o)))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached(heap, current, ANY)) ==> ((guard(heap, current, observers, v, o)) ==> (fun.ANY.in_observers(heap, current, v, o)))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, owns, v, o) } (attached_exact(heap, current, MASTER)) ==> ((guard(heap, current, owns, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, subjects, v, o) } (attached_exact(heap, current, MASTER)) ==> ((guard(heap, current, subjects, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached_exact(heap, current, MASTER)) ==> ((guard(heap, current, observers, v, o)) <==> (fun.MASTER.in_observers(heap, current, v, o)))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached(heap, current, MASTER)) ==> ((guard(heap, current, observers, v, o)) ==> (fun.MASTER.in_observers(heap, current, v, o)))));

function modify.MASTER.make(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T9> $o: ref, $f: Field T9 :: { modify.MASTER.make(heap, current)[$o, $f] } (modify.MASTER.make(heap, current)[$o, $f]) <==> (($o) == (current))))));

function modify.MASTER.tick(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T10> $o: ref, $f: Field T10 :: { modify.MASTER.tick(heap, current)[$o, $f] } (modify.MASTER.tick(heap, current)[$o, $f]) <==> ((($o) == (current)) && ((($f) == (MASTER.time)) || (($f) == (closed))))))));

function modify.MASTER.reset(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T11> $o: ref, $f: Field T11 :: { modify.MASTER.reset(heap, current)[$o, $f] } (modify.MASTER.reset(heap, current)[$o, $f]) <==> ((($o) == (current)) && ((($f) == (MASTER.time)) || (($f) == (closed))))))));

function modify.MASTER.time_increased(heap: HeapType, current: ref, new_time: int, o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_time: int, o: ref :: (IsHeap(heap)) ==> ((forall <T12> $o: ref, $f: Field T12 :: { modify.MASTER.time_increased(heap, current, new_time, o)[$o, $f] } (modify.MASTER.time_increased(heap, current, new_time, o)[$o, $f]) <==> (false)))));

function read.fun.MASTER.time_increased(heap: HeapType, current: ref, new_time: int, o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_time: int, o: ref :: (IsHeap(heap)) ==> ((forall <T13> $o: ref, $f: Field T13 :: { read.fun.MASTER.time_increased(heap, current, new_time, o)[$o, $f] } (read.fun.MASTER.time_increased(heap, current, new_time, o)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.MASTER.time_increased(heap: HeapType, current: ref, new_time: int, o: ref) returns (bool) {
  true
}

function trigger.fun.MASTER.time_increased(heap: HeapType, current: ref, new_time: int, o: ref) returns (bool);

const CLOCK.master: Field (ref);

axiom ((FieldId(CLOCK.master, CLOCK)) == (81));

axiom ((forall heap: HeapType, o: ref :: { heap[o, CLOCK.master] } ((IsHeap(heap)) && (attached(heap, o, CLOCK))) ==> (detachable_exact(heap, heap[o, CLOCK.master], MASTER))));

axiom ((forall heap: HeapType, current: ref, v: ref, o: ref :: { guard(heap, current, CLOCK.master, v, o) } (attached_exact(heap, current, CLOCK)) ==> ((guard(heap, current, CLOCK.master, v, o)) <==> ((user_inv(heap, o)) ==> (user_inv(heap[current, CLOCK.master := v], o))))));

axiom ((forall heap: HeapType, current: ref, v: ref, o: ref :: { guard(heap, current, CLOCK.master, v, o) } (attached(heap, current, CLOCK)) ==> ((guard(heap, current, CLOCK.master, v, o)) ==> ((user_inv(heap, o)) ==> (user_inv(heap[current, CLOCK.master := v], o))))));

const CLOCK.local_time: Field int;

axiom ((FieldId(CLOCK.local_time, CLOCK)) == (82));

axiom ((forall heap: HeapType, o: ref :: { heap[o, CLOCK.local_time] } ((IsHeap(heap)) && (attached(heap, o, CLOCK))) ==> (is_integer_32(heap[o, CLOCK.local_time]))));

axiom ((forall heap: HeapType, current: ref, v: int, o: ref :: { guard(heap, current, CLOCK.local_time, v, o) } (attached_exact(heap, current, CLOCK)) ==> ((guard(heap, current, CLOCK.local_time, v, o)) <==> ((user_inv(heap, o)) ==> (user_inv(heap[current, CLOCK.local_time := v], o))))));

axiom ((forall heap: HeapType, current: ref, v: int, o: ref :: { guard(heap, current, CLOCK.local_time, v, o) } (attached(heap, current, CLOCK)) ==> ((guard(heap, current, CLOCK.local_time, v, o)) ==> ((user_inv(heap, o)) ==> (user_inv(heap[current, CLOCK.local_time := v], o))))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, owns, v, o) } (attached_exact(heap, current, CLOCK)) ==> ((guard(heap, current, owns, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, subjects, v, o) } (attached_exact(heap, current, CLOCK)) ==> ((guard(heap, current, subjects, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached_exact(heap, current, CLOCK)) ==> ((guard(heap, current, observers, v, o)) <==> (fun.CLOCK.in_observers(heap, current, v, o)))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached(heap, current, CLOCK)) ==> ((guard(heap, current, observers, v, o)) ==> (fun.CLOCK.in_observers(heap, current, v, o)))));

function modify.CLOCK.make(heap: HeapType, current: ref, m: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, m: ref :: (IsHeap(heap)) ==> ((forall <T14> $o: ref, $f: Field T14 :: { modify.CLOCK.make(heap, current, m)[$o, $f] } (modify.CLOCK.make(heap, current, m)[$o, $f]) <==> (((($o) == (m)) && ((($f) == (observers)) || (($f) == (closed)))) || (($o) == (current)))))));

function CLOCK#E#time_weakly_synchronized.filtered_inv(heap: HeapType, current: ref) returns (bool) {
  ((heap[current, CLOCK.master]) != (Void)) && (Set#Equal(heap[current, subjects], Set#Singleton(heap[current, CLOCK.master]))) && ((0) <= (heap[current, CLOCK.local_time])) && (Set#IsEmpty(heap[current, observers])) && (Set#IsEmpty(heap[current, owns])) && (admissibility2(heap, current))
}

axiom ((forall h: HeapType, o: ref :: { CLOCK#E#time_weakly_synchronized.filtered_inv(h, o) } ((IsHeap(h)) && (attached(h, o, CLOCK)) && (h[o, closed])) ==> (CLOCK#E#time_weakly_synchronized.filtered_inv(h, o))));

function modify.CLOCK.sync(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T15> $o: ref, $f: Field T15 :: { modify.CLOCK.sync(heap, current)[$o, $f] } (modify.CLOCK.sync(heap, current)[$o, $f]) <==> ((($o) == (current)) && ((($f) == (CLOCK.local_time)) || (($f) == (closed))))))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, owns, v, o) } (attached_exact(heap, current, CLIENT)) ==> ((guard(heap, current, owns, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, subjects, v, o) } (attached_exact(heap, current, CLIENT)) ==> ((guard(heap, current, subjects, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached_exact(heap, current, CLIENT)) ==> ((guard(heap, current, observers, v, o)) <==> (fun.CLIENT.in_observers(heap, current, v, o)))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached(heap, current, CLIENT)) ==> ((guard(heap, current, observers, v, o)) ==> (fun.CLIENT.in_observers(heap, current, v, o)))));

function modify.CLIENT.default_create(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T16> $o: ref, $f: Field T16 :: { modify.CLIENT.default_create(heap, current)[$o, $f] } (modify.CLIENT.default_create(heap, current)[$o, $f]) <==> (($o) == (current))))));

function modify.CLIENT.test(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T17> $o: ref, $f: Field T17 :: { modify.CLIENT.test(heap, current)[$o, $f] } (modify.CLIENT.test(heap, current)[$o, $f]) <==> (($o) == (current))))));

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

procedure MASTER.in_observers(Current: ref, new_observers: Set (ref), o: ref) returns (Result: bool where true);
  free requires attached_exact(Heap, Current, MASTER); // info:type property for argument Current
  free requires Set#ItemsType(Heap, new_observers, ANY); // info:type property for argument new_observers
  free requires Heap[o, allocated]; // info:type property for argument o
  modifies Heap;
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.MASTER.in_observers(Heap, Current, new_observers, o), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.MASTER.in_observers(old(Heap), Current, new_observers, o));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.MASTER.in_observers(Heap, Current, new_observers, o), readable);



function fun.MASTER.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function fun0.MASTER.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.MASTER.in_observers(heap, current, new_observers, o) } { trigger.fun.MASTER.in_observers(heap, current, new_observers, o) } (pre.fun.MASTER.in_observers(heap, current, new_observers, o)) ==> ((fun.MASTER.in_observers(heap, current, new_observers, o)) == (new_observers[o]))));

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.MASTER.in_observers(heap, current, new_observers, o) } (fun.MASTER.in_observers(heap, current, new_observers, o)) == (fun0.MASTER.in_observers(heap, current, new_observers, o))));

axiom ((forall h: HeapType, h': HeapType, current: ref, new_observers: Set (ref), o: ref :: { HeapSucc(h, h'), fun0.MASTER.in_observers(h, current, new_observers, o), fun0.MASTER.in_observers(h', current, new_observers, o) } ((HeapSucc(h, h')) && (pre.fun.MASTER.in_observers(h, current, new_observers, o)) && (pre.fun.MASTER.in_observers(h', current, new_observers, o)) && (same_inside(h, h', read.fun.MASTER.in_observers(h, current, new_observers, o)))) ==> ((fun0.MASTER.in_observers(h, current, new_observers, o)) == (fun0.MASTER.in_observers(h', current, new_observers, o)))));

procedure CLOCK.in_observers(Current: ref, new_observers: Set (ref), o: ref) returns (Result: bool where true);
  free requires attached_exact(Heap, Current, CLOCK); // info:type property for argument Current
  free requires Set#ItemsType(Heap, new_observers, ANY); // info:type property for argument new_observers
  free requires Heap[o, allocated]; // info:type property for argument o
  modifies Heap;
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.CLOCK.in_observers(Heap, Current, new_observers, o), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.CLOCK.in_observers(old(Heap), Current, new_observers, o));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.CLOCK.in_observers(Heap, Current, new_observers, o), readable);



function fun.CLOCK.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function fun0.CLOCK.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.CLOCK.in_observers(heap, current, new_observers, o) } { trigger.fun.CLOCK.in_observers(heap, current, new_observers, o) } (pre.fun.CLOCK.in_observers(heap, current, new_observers, o)) ==> ((fun.CLOCK.in_observers(heap, current, new_observers, o)) == (new_observers[o]))));

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.CLOCK.in_observers(heap, current, new_observers, o) } (fun.CLOCK.in_observers(heap, current, new_observers, o)) == (fun0.CLOCK.in_observers(heap, current, new_observers, o))));

axiom ((forall h: HeapType, h': HeapType, current: ref, new_observers: Set (ref), o: ref :: { HeapSucc(h, h'), fun0.CLOCK.in_observers(h, current, new_observers, o), fun0.CLOCK.in_observers(h', current, new_observers, o) } ((HeapSucc(h, h')) && (pre.fun.CLOCK.in_observers(h, current, new_observers, o)) && (pre.fun.CLOCK.in_observers(h', current, new_observers, o)) && (same_inside(h, h', read.fun.CLOCK.in_observers(h, current, new_observers, o)))) ==> ((fun0.CLOCK.in_observers(h, current, new_observers, o)) == (fun0.CLOCK.in_observers(h', current, new_observers, o)))));

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

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T18> $o: ref, $f: Field T18 :: { modify.ANY.in_observers(heap, current, new_observers, o)[$o, $f] } (modify.ANY.in_observers(heap, current, new_observers, o)[$o, $f]) <==> (false)))));

function read.fun.ANY.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T19> $o: ref, $f: Field T19 :: { read.fun.ANY.in_observers(heap, current, new_observers, o)[$o, $f] } (read.fun.ANY.in_observers(heap, current, new_observers, o)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.ANY.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool) {
  true
}

function trigger.fun.ANY.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function modify.MASTER.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T20> $o: ref, $f: Field T20 :: { modify.MASTER.in_observers(heap, current, new_observers, o)[$o, $f] } (modify.MASTER.in_observers(heap, current, new_observers, o)[$o, $f]) <==> (false)))));

function read.fun.MASTER.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T21> $o: ref, $f: Field T21 :: { read.fun.MASTER.in_observers(heap, current, new_observers, o)[$o, $f] } (read.fun.MASTER.in_observers(heap, current, new_observers, o)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.MASTER.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool) {
  true
}

function trigger.fun.MASTER.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function modify.CLOCK.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T22> $o: ref, $f: Field T22 :: { modify.CLOCK.in_observers(heap, current, new_observers, o)[$o, $f] } (modify.CLOCK.in_observers(heap, current, new_observers, o)[$o, $f]) <==> (false)))));

function read.fun.CLOCK.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T23> $o: ref, $f: Field T23 :: { read.fun.CLOCK.in_observers(heap, current, new_observers, o)[$o, $f] } (read.fun.CLOCK.in_observers(heap, current, new_observers, o)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.CLOCK.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool) {
  true
}

function trigger.fun.CLOCK.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function modify.CLIENT.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T24> $o: ref, $f: Field T24 :: { modify.CLIENT.in_observers(heap, current, new_observers, o)[$o, $f] } (modify.CLIENT.in_observers(heap, current, new_observers, o)[$o, $f]) <==> (false)))));

function read.fun.CLIENT.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T25> $o: ref, $f: Field T25 :: { read.fun.CLIENT.in_observers(heap, current, new_observers, o)[$o, $f] } (read.fun.CLIENT.in_observers(heap, current, new_observers, o)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.CLIENT.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool) {
  true
}

function trigger.fun.CLIENT.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);
