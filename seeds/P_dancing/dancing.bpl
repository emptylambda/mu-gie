// Automatically generated (12/12/2017 1:54:27.302 PM)

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

const unique DANCING: Type;

axiom (is_frozen(DANCING));

axiom ((DANCING) <: (ANY));

axiom ((forall t: Type :: { (DANCING) <: (t) } ((DANCING) <: (t)) <==> (((t) == (DANCING)) || ((ANY) <: (t)))));

axiom ((FieldId(allocated, DANCING)) == (-1));

axiom ((FieldId(closed, DANCING)) == (-2));

axiom ((FieldId(owner, DANCING)) == (-3));

axiom ((FieldId(owns, DANCING)) == (-4));

axiom ((FieldId(observers, DANCING)) == (-5));

axiom ((FieldId(subjects, DANCING)) == (-6));

axiom ((forall <T0> $f: Field T0 :: { IsModelField($f, DANCING) } (IsModelField($f, DANCING)) <==> ((($f) == (subjects)) || (($f) == (observers)))));

function { :inline } DANCING.user_inv(heap: HeapType, current: ref) returns (bool) {
  ((heap[current, DANCING.left]) != (Void)) && ((heap[current, DANCING.right]) != (Void)) && (Set#Equal(heap[current, subjects], Set#Extended(Set#Singleton(heap[current, DANCING.left]), heap[current, DANCING.right]))) && (Set#Equal(heap[current, observers], Set#Extended(Set#Singleton(heap[current, DANCING.left]), heap[current, DANCING.right]))) && ((heap[heap[current, DANCING.left], DANCING.right]) == (current)) && ((heap[heap[current, DANCING.right], DANCING.left]) == (current)) && (Set#IsEmpty(heap[current, owns])) && (admissibility2(heap, current))
}

function DANCING.subjects.static(heap: HeapType, current: ref) returns (Set (ref)) {
  Set#Extended(Set#Singleton(heap[current, DANCING.left]), heap[current, DANCING.right])
}

function DANCING.observers.static(heap: HeapType, current: ref) returns (Set (ref)) {
  Set#Extended(Set#Singleton(heap[current, DANCING.left]), heap[current, DANCING.right])
}

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached_exact(heap, current, DANCING)) ==> ((user_inv(heap, current)) <==> (DANCING.user_inv(heap, current)))));

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached(heap, current, DANCING)) ==> ((user_inv(heap, current)) ==> (DANCING.user_inv(heap, current)))));

procedure DANCING.invariant_admissibility_check(Current: ref);
  requires attached_exact(Heap, Current, DANCING);



implementation DANCING.invariant_admissibility_check(Current: ref)
{
  entry:
  goto pre, a2, a3;
  pre:
  assert user_inv_readable(Heap, Current)[Current, DANCING.left]; // type:access tag:attribute_readable line:192 cid:404 fid:81
  assume (Heap[Current, DANCING.left]) != (Void);
  assert user_inv_readable(Heap, Current)[Current, DANCING.right]; // type:access tag:attribute_readable line:193 cid:404 fid:82
  assume (Heap[Current, DANCING.right]) != (Void);
  assert user_inv_readable(Heap, Current)[Current, DANCING.left]; // type:access tag:attribute_readable line:194 cid:404 fid:81
  assert user_inv_readable(Heap, Current)[Current, DANCING.right]; // type:access tag:attribute_readable line:194 cid:404 fid:82
  assume Set#Equal(Heap[Current, subjects], Set#Extended(Set#Singleton(Heap[Current, DANCING.left]), Heap[Current, DANCING.right]));
  assert user_inv_readable(Heap, Current)[Current, DANCING.left]; // type:access tag:attribute_readable line:195 cid:404 fid:81
  assert user_inv_readable(Heap, Current)[Current, DANCING.right]; // type:access tag:attribute_readable line:195 cid:404 fid:82
  assume Set#Equal(Heap[Current, observers], Set#Extended(Set#Singleton(Heap[Current, DANCING.left]), Heap[Current, DANCING.right]));
  assert user_inv_readable(Heap, Current)[Current, DANCING.left]; // type:access tag:attribute_readable line:196 cid:404 fid:81
  assert {:subsumption 0} (Heap[Current, DANCING.left]) != (Void); // type:attached tag:left_consistent line:196
  assert user_inv_readable(Heap, Current)[Heap[Current, DANCING.left], DANCING.right]; // type:access tag:attribute_readable line:196 cid:404 fid:82
  assume (Heap[Heap[Current, DANCING.left], DANCING.right]) == (Current);
  assert user_inv_readable(Heap, Current)[Current, DANCING.right]; // type:access tag:attribute_readable line:197 cid:404 fid:82
  assert {:subsumption 0} (Heap[Current, DANCING.right]) != (Void); // type:attached tag:right_consistent line:197
  assert user_inv_readable(Heap, Current)[Heap[Current, DANCING.right], DANCING.left]; // type:access tag:attribute_readable line:197 cid:404 fid:81
  assume (Heap[Heap[Current, DANCING.right], DANCING.left]) == (Current);
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

procedure create.DANCING.make(Current: ref);
  free requires attached_exact(Heap, Current, DANCING); // info:type property for argument Current
  modifies Heap;
  ensures (Heap[Current, DANCING.left]) == (Current); // type:post tag:singleton line:19
  requires (forall <T3> $f: Field T3 :: (($f) != (allocated)) ==> ((Heap[Current, $f]) == (Default($f))));
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.DANCING.make(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.DANCING.make(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts



implementation create.DANCING.make(Current: ref)
{
  entry:
  assume {:captureState "create.DANCING.make"} true;
  // /home/caf/temp/comcom/repo-dancing/dancing.e:16
  // left := Current
  call update_heap(Current, DANCING.left, Current); // line:16
  // /home/caf/temp/comcom/repo-dancing/dancing.e:17
  // right := Current
  call update_heap(Current, DANCING.right, Current); // line:17
  if (modify.DANCING.make(Heap, Current)[Current, observers]) {
    call update_heap(Current, observers, DANCING.observers.static(Heap, Current)); // default:observers line:20
  }
  if (modify.DANCING.make(Heap, Current)[Current, subjects]) {
    call update_heap(Current, subjects, DANCING.subjects.static(Heap, Current)); // default:subjects line:20
  }
  if (*) {
    assert (Heap[Current, DANCING.left]) != (Void); // type:inv tag:left_exists line:20 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert (Heap[Current, DANCING.right]) != (Void); // type:inv tag:right_exists line:20 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#Equal(Heap[Current, subjects], Set#Extended(Set#Singleton(Heap[Current, DANCING.left]), Heap[Current, DANCING.right])); // type:inv tag:subjects_structure line:20 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#Equal(Heap[Current, observers], Set#Extended(Set#Singleton(Heap[Current, DANCING.left]), Heap[Current, DANCING.right])); // type:inv tag:observers_structure line:20 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert (Heap[Heap[Current, DANCING.left], DANCING.right]) == (Current); // type:inv tag:left_consistent line:20 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert (Heap[Heap[Current, DANCING.right], DANCING.left]) == (Current); // type:inv tag:right_consistent line:20 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, owns]); // type:inv tag:default_owns line:20 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert admissibility2(Heap, Current); // type:inv tag:A2 line:20 cid:1 rid:55
    assume false;
  }
  call wrap(Current); // default:wrapping cid:1 rid:55 line:20
}

procedure DANCING.insert_right(Current: ref, n: ref);
  free requires attached_exact(Heap, Current, DANCING); // info:type property for argument Current
  free requires detachable_exact(Heap, n, DANCING); // info:type property for argument n
  modifies Heap;
  requires (n) != (Void); // type:attached tag:n_singleton line:45
  requires (Heap[n, DANCING.left]) == (n); // type:pre tag:n_singleton line:45
  requires (Heap[Current, DANCING.right]) != (Void); // type:attached tag:right_wrapped line:46
  requires is_wrapped(Heap, Heap[Current, DANCING.right]); // type:pre tag:right_wrapped line:46
  ensures (Heap[Current, DANCING.right]) == (n); // type:post tag:n_left_set line:70
  ensures (n) != (Void); // type:attached tag:n_right_set line:71
  ensures (Heap[n, DANCING.right]) == (old(Heap)[Current, DANCING.right]); // type:post tag:n_right_set line:71
  ensures (old(Heap)[Current, DANCING.right]) != (Void); // type:attached tag:old_right_wrapped line:72
  ensures is_wrapped(Heap, old(Heap)[Current, DANCING.right]); // type:post tag:old_right_wrapped line:72
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.DANCING.insert_right(Heap, Current, n), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.DANCING.insert_right(old(Heap), Current, n));
  free ensures HeapSucc(old(Heap), Heap);
  requires is_wrapped(Heap, Current); // type:pre tag:default_is_wrapped default:contracts
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts
  requires is_wrapped(Heap, n); // type:pre tag:arg_n_is_wrapped default:contracts
  ensures is_wrapped(Heap, n); // type:post tag:arg_n_is_wrapped default:contracts



function { :inline } variant.DANCING.insert_right.1(heap: HeapType, current: ref, n: ref) returns (ref) {
  n
}

implementation DANCING.insert_right(Current: ref, n: ref)
{
  var local1: ref where detachable_exact(Heap, local1, DANCING);

  init_locals:
  local1 := Void;

  entry:
  assume {:captureState "DANCING.insert_right"} true;
  // /home/caf/temp/comcom/repo-dancing/dancing.e:53
  // r := right
  local1 := Heap[Current, DANCING.right];
  // /home/caf/temp/comcom/repo-dancing/dancing.e:54
  // unwrap_all ([Current, r, n])
  call unwrap_all(Current, Set#Extended(Set#Extended(Set#Singleton(Current), local1), n)); // line:54 cid:1 rid:59
  // /home/caf/temp/comcom/repo-dancing/dancing.e:56
  // n.set_right (r)
  assert {:subsumption 0} (n) != (Void); // type:attached line:56
  call DANCING.set_right(n, local1); // line:56 cid:404 rid:5411
  // /home/caf/temp/comcom/repo-dancing/dancing.e:57
  // n.set_left (Current)
  assert {:subsumption 0} (n) != (Void); // type:attached line:57
  call DANCING.set_left(n, Current); // line:57 cid:404 rid:5410
  // /home/caf/temp/comcom/repo-dancing/dancing.e:59
  // r.set_left (n)
  assert {:subsumption 0} (local1) != (Void); // type:attached line:59
  call DANCING.set_left(local1, n); // line:59 cid:404 rid:5410
  // /home/caf/temp/comcom/repo-dancing/dancing.e:60
  // set_right (n)
  call DANCING.set_right(Current, n); // line:60 cid:404 rid:5411
  // /home/caf/temp/comcom/repo-dancing/dancing.e:62
  // n.set_subjects ([r, Current])
  assert {:subsumption 0} (n) != (Void); // type:attached line:62
  call update_heap(n, subjects, Set#Extended(Set#Singleton(local1), Current)); // line:62
  // /home/caf/temp/comcom/repo-dancing/dancing.e:63
  // n.set_observers ([r, Current])
  assert {:subsumption 0} (n) != (Void); // type:attached line:63
  call update_heap(n, observers, Set#Extended(Set#Singleton(local1), Current)); // line:63
  // /home/caf/temp/comcom/repo-dancing/dancing.e:64
  // set_subjects ([left, n])
  call update_heap(Current, subjects, Set#Extended(Set#Singleton(Heap[Current, DANCING.left]), n)); // line:64
  // /home/caf/temp/comcom/repo-dancing/dancing.e:65
  // set_observers ([left, n])
  call update_heap(Current, observers, Set#Extended(Set#Singleton(Heap[Current, DANCING.left]), n)); // line:65
  // /home/caf/temp/comcom/repo-dancing/dancing.e:66
  // r.set_subjects ([n, r.right])
  assert {:subsumption 0} (local1) != (Void); // type:attached line:66
  assert {:subsumption 0} (local1) != (Void); // type:attached line:66
  call update_heap(local1, subjects, Set#Extended(Set#Singleton(n), Heap[local1, DANCING.right])); // line:66
  // /home/caf/temp/comcom/repo-dancing/dancing.e:67
  // r.set_observers ([n, r.right])
  assert {:subsumption 0} (local1) != (Void); // type:attached line:67
  assert {:subsumption 0} (local1) != (Void); // type:attached line:67
  call update_heap(local1, observers, Set#Extended(Set#Singleton(n), Heap[local1, DANCING.right])); // line:67
  // /home/caf/temp/comcom/repo-dancing/dancing.e:68
  // wrap_all ([Current, r, n])
  call wrap_all(Current, Set#Extended(Set#Extended(Set#Singleton(Current), local1), n)); // line:68 cid:1 rid:56
}

procedure DANCING.remove(Current: ref);
  free requires attached_exact(Heap, Current, DANCING); // info:type property for argument Current
  modifies Heap;
  requires is_wrapped(Heap, Current); // type:pre tag:wrapped line:80
  requires (Heap[Current, DANCING.left]) != (Void); // type:attached tag:left_wrapped line:81
  requires is_wrapped(Heap, Heap[Current, DANCING.left]); // type:pre tag:left_wrapped line:81
  requires (Heap[Current, DANCING.right]) != (Void); // type:attached tag:right_wrapped line:82
  requires is_wrapped(Heap, Heap[Current, DANCING.right]); // type:pre tag:right_wrapped line:82
  ensures is_open(Heap, Current); // type:post tag:open line:101
  ensures DANCING#E#left_consistent#right_consistent#A2.filtered_inv(Heap, Current); // type:post line:102
  ensures (Heap[Current, DANCING.left]) == (old(Heap)[Current, DANCING.left]); // type:post tag:left_unchanged line:103
  ensures (Heap[Current, DANCING.right]) == (old(Heap)[Current, DANCING.right]); // type:post tag:right_unchanged line:104
  ensures ((Heap[Current, DANCING.left]) != (Current)) ==> ((Heap[Current, DANCING.left]) != (Void)); // type:attached tag:left_wrapped line:105
  ensures ((Heap[Current, DANCING.left]) != (Current)) ==> (is_wrapped(Heap, Heap[Current, DANCING.left])); // type:post tag:left_wrapped line:105
  ensures ((Heap[Current, DANCING.right]) != (Current)) ==> ((Heap[Current, DANCING.right]) != (Void)); // type:attached tag:right_wrapped line:106
  ensures ((Heap[Current, DANCING.right]) != (Current)) ==> (is_wrapped(Heap, Heap[Current, DANCING.right])); // type:post tag:right_wrapped line:106
  ensures (Heap[Current, DANCING.left]) != (Void); // type:attached tag:neighbors_connected line:107
  ensures (Heap[Heap[Current, DANCING.left], DANCING.right]) == (Heap[Current, DANCING.right]); // type:post tag:neighbors_connected line:107
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.DANCING.remove(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.DANCING.remove(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);



function { :inline } variant.DANCING.remove.1(heap: HeapType, current: ref) returns (int) {
  0
}

implementation DANCING.remove(Current: ref)
{
  entry:
  assume {:captureState "DANCING.remove"} true;
  // /home/caf/temp/comcom/repo-dancing/dancing.e:87
  // unwrap_all ([Current, left, right])	-- Ghost: open objects for modification
  call unwrap_all(Current, Set#Extended(Set#Extended(Set#Singleton(Current), Heap[Current, DANCING.left]), Heap[Current, DANCING.right])); // line:87 cid:1 rid:59
  // /home/caf/temp/comcom/repo-dancing/dancing.e:89
  // left.set_right (right)	-- R[L[x]] := R[x]
  assert {:subsumption 0} (Heap[Current, DANCING.left]) != (Void); // type:attached line:89
  call DANCING.set_right(Heap[Current, DANCING.left], Heap[Current, DANCING.right]); // line:89 cid:404 rid:5411
  // /home/caf/temp/comcom/repo-dancing/dancing.e:90
  // right.set_left (left)	-- L[R[x]] := L[x]
  assert {:subsumption 0} (Heap[Current, DANCING.right]) != (Void); // type:attached line:90
  call DANCING.set_left(Heap[Current, DANCING.right], Heap[Current, DANCING.left]); // line:90 cid:404 rid:5410
  // /home/caf/temp/comcom/repo-dancing/dancing.e:92
  // left.set_subjects ([left.left, right])	-- Ghost: update subjects set
  assert {:subsumption 0} (Heap[Current, DANCING.left]) != (Void); // type:attached line:92
  assert {:subsumption 0} (Heap[Current, DANCING.left]) != (Void); // type:attached line:92
  call update_heap(Heap[Current, DANCING.left], subjects, Set#Extended(Set#Singleton(Heap[Heap[Current, DANCING.left], DANCING.left]), Heap[Current, DANCING.right])); // line:92
  // /home/caf/temp/comcom/repo-dancing/dancing.e:93
  // left.set_observers ([left.left, right])	-- Ghost: update observers set
  assert {:subsumption 0} (Heap[Current, DANCING.left]) != (Void); // type:attached line:93
  assert {:subsumption 0} (Heap[Current, DANCING.left]) != (Void); // type:attached line:93
  call update_heap(Heap[Current, DANCING.left], observers, Set#Extended(Set#Singleton(Heap[Heap[Current, DANCING.left], DANCING.left]), Heap[Current, DANCING.right])); // line:93
  // /home/caf/temp/comcom/repo-dancing/dancing.e:94
  // right.set_subjects ([left, right.right])	-- Ghost: update subjects set
  assert {:subsumption 0} (Heap[Current, DANCING.right]) != (Void); // type:attached line:94
  assert {:subsumption 0} (Heap[Current, DANCING.right]) != (Void); // type:attached line:94
  call update_heap(Heap[Current, DANCING.right], subjects, Set#Extended(Set#Singleton(Heap[Current, DANCING.left]), Heap[Heap[Current, DANCING.right], DANCING.right])); // line:94
  // /home/caf/temp/comcom/repo-dancing/dancing.e:95
  // right.set_observers ([left, right.right])	-- Ghost: update observers set
  assert {:subsumption 0} (Heap[Current, DANCING.right]) != (Void); // type:attached line:95
  assert {:subsumption 0} (Heap[Current, DANCING.right]) != (Void); // type:attached line:95
  call update_heap(Heap[Current, DANCING.right], observers, Set#Extended(Set#Singleton(Heap[Current, DANCING.left]), Heap[Heap[Current, DANCING.right], DANCING.right])); // line:95
  // /home/caf/temp/comcom/repo-dancing/dancing.e:96
  // if left /= Current then
  if ((Heap[Current, DANCING.left]) != (Current)) {
    // /home/caf/temp/comcom/repo-dancing/dancing.e:97
    // check right /= Current end	-- Follows from the invariant
    assert (Heap[Current, DANCING.right]) != (Current); // type:check line:97
    // /home/caf/temp/comcom/repo-dancing/dancing.e:98
    // wrap_all ([left, right])	-- Ghost: close objects after checking their invariant
    call wrap_all(Current, Set#Extended(Set#Singleton(Heap[Current, DANCING.left]), Heap[Current, DANCING.right])); // line:98 cid:1 rid:56
  }
}

procedure DANCING.unremove(Current: ref);
  free requires attached_exact(Heap, Current, DANCING); // info:type property for argument Current
  modifies Heap;
  requires is_open(Heap, Current); // type:pre tag:open line:115
  requires DANCING#E#left_consistent#right_consistent#A2.filtered_inv(Heap, Current); // type:pre line:116
  requires ((Heap[Current, DANCING.left]) != (Current)) ==> ((Heap[Current, DANCING.left]) != (Void)); // type:attached tag:left_wrapped line:117
  requires ((Heap[Current, DANCING.left]) != (Current)) ==> (is_wrapped(Heap, Heap[Current, DANCING.left])); // type:pre tag:left_wrapped line:117
  requires ((Heap[Current, DANCING.right]) != (Current)) ==> ((Heap[Current, DANCING.right]) != (Void)); // type:attached tag:right_wrapped line:118
  requires ((Heap[Current, DANCING.right]) != (Current)) ==> (is_wrapped(Heap, Heap[Current, DANCING.right])); // type:pre tag:right_wrapped line:118
  requires ((Heap[Current, DANCING.left]) == (Current)) == ((Heap[Current, DANCING.right]) == (Current)); // type:pre tag:both_or_neither line:119
  requires (Heap[Current, DANCING.left]) != (Void); // type:attached tag:neighbors_connected line:120
  requires (Heap[Heap[Current, DANCING.left], DANCING.right]) == (Heap[Current, DANCING.right]); // type:pre tag:neighbors_connected line:120
  requires (Heap[Current, DANCING.right]) != (Void); // type:pre tag:right_exists line:122
  ensures is_wrapped(Heap, Current); // type:post tag:wrapped line:140
  ensures (Heap[Current, DANCING.left]) != (Void); // type:attached tag:left_wrapped line:141
  ensures is_wrapped(Heap, Heap[Current, DANCING.left]); // type:post tag:left_wrapped line:141
  ensures (Heap[Current, DANCING.right]) != (Void); // type:attached tag:right_wrapped line:142
  ensures is_wrapped(Heap, Heap[Current, DANCING.right]); // type:post tag:right_wrapped line:142
  ensures (Heap[Current, DANCING.left]) == (old(Heap)[Current, DANCING.left]); // type:post tag:left_unchanged line:143
  ensures (Heap[Current, DANCING.right]) == (old(Heap)[Current, DANCING.right]); // type:post tag:right_unchanged line:144
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.DANCING.unremove(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.DANCING.unremove(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);



function { :inline } variant.DANCING.unremove.1(heap: HeapType, current: ref) returns (int) {
  0
}

implementation DANCING.unremove(Current: ref)
{
  entry:
  assume {:captureState "DANCING.unremove"} true;
  // /home/caf/temp/comcom/repo-dancing/dancing.e:127
  // if left /= Current then
  if ((Heap[Current, DANCING.left]) != (Current)) {
    // /home/caf/temp/comcom/repo-dancing/dancing.e:128
    // unwrap_all ([left, right])
    call unwrap_all(Current, Set#Extended(Set#Singleton(Heap[Current, DANCING.left]), Heap[Current, DANCING.right])); // line:128 cid:1 rid:59
  }
  // /home/caf/temp/comcom/repo-dancing/dancing.e:131
  // left.set_right (Current)	-- R[L[x]] := x
  assert {:subsumption 0} (Heap[Current, DANCING.left]) != (Void); // type:attached line:131
  call DANCING.set_right(Heap[Current, DANCING.left], Current); // line:131 cid:404 rid:5411
  // /home/caf/temp/comcom/repo-dancing/dancing.e:132
  // right.set_left (Current)	-- L[R[x]] := x
  assert {:subsumption 0} (Heap[Current, DANCING.right]) != (Void); // type:attached line:132
  call DANCING.set_left(Heap[Current, DANCING.right], Current); // line:132 cid:404 rid:5410
  // /home/caf/temp/comcom/repo-dancing/dancing.e:134
  // left.set_subjects ([left.left, Current])
  assert {:subsumption 0} (Heap[Current, DANCING.left]) != (Void); // type:attached line:134
  assert {:subsumption 0} (Heap[Current, DANCING.left]) != (Void); // type:attached line:134
  call update_heap(Heap[Current, DANCING.left], subjects, Set#Extended(Set#Singleton(Heap[Heap[Current, DANCING.left], DANCING.left]), Current)); // line:134
  // /home/caf/temp/comcom/repo-dancing/dancing.e:135
  // left.set_observers ([left.left, Current])
  assert {:subsumption 0} (Heap[Current, DANCING.left]) != (Void); // type:attached line:135
  assert {:subsumption 0} (Heap[Current, DANCING.left]) != (Void); // type:attached line:135
  call update_heap(Heap[Current, DANCING.left], observers, Set#Extended(Set#Singleton(Heap[Heap[Current, DANCING.left], DANCING.left]), Current)); // line:135
  // /home/caf/temp/comcom/repo-dancing/dancing.e:136
  // right.set_subjects ([Current, right.right])
  assert {:subsumption 0} (Heap[Current, DANCING.right]) != (Void); // type:attached line:136
  assert {:subsumption 0} (Heap[Current, DANCING.right]) != (Void); // type:attached line:136
  call update_heap(Heap[Current, DANCING.right], subjects, Set#Extended(Set#Singleton(Current), Heap[Heap[Current, DANCING.right], DANCING.right])); // line:136
  // /home/caf/temp/comcom/repo-dancing/dancing.e:137
  // right.set_observers ([Current, right.right])
  assert {:subsumption 0} (Heap[Current, DANCING.right]) != (Void); // type:attached line:137
  assert {:subsumption 0} (Heap[Current, DANCING.right]) != (Void); // type:attached line:137
  call update_heap(Heap[Current, DANCING.right], observers, Set#Extended(Set#Singleton(Current), Heap[Heap[Current, DANCING.right], DANCING.right])); // line:137
  // /home/caf/temp/comcom/repo-dancing/dancing.e:138
  // wrap_all ([Current, left, right])
  call wrap_all(Current, Set#Extended(Set#Extended(Set#Singleton(Current), Heap[Current, DANCING.left]), Heap[Current, DANCING.right])); // line:138 cid:1 rid:56
}

procedure DANCING.set_left(Current: ref, n: ref);
  free requires attached_exact(Heap, Current, DANCING); // info:type property for argument Current
  free requires detachable_exact(Heap, n, DANCING); // info:type property for argument n
  modifies Heap;
  requires is_open(Heap, Current); // type:pre tag:open line:152
  requires (Heap[Current, DANCING.left]) != (Void); // type:attached tag:left_open line:153
  requires is_open(Heap, Heap[Current, DANCING.left]); // type:pre tag:left_open line:153
  ensures (Heap[Current, DANCING.left]) == (n); // type:post line:158
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.DANCING.set_left(Heap, Current, n), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.DANCING.set_left(old(Heap), Current, n));
  free ensures HeapSucc(old(Heap), Heap);



function { :inline } variant.DANCING.set_left.1(heap: HeapType, current: ref, n: ref) returns (ref) {
  n
}

implementation DANCING.set_left(Current: ref, n: ref)
{
  entry:
  assume {:captureState "DANCING.set_left"} true;
  // /home/caf/temp/comcom/repo-dancing/dancing.e:156
  // left := n -- preserves `right'
  call update_heap(Current, DANCING.left, n); // line:156
}

procedure DANCING.set_right(Current: ref, n: ref);
  free requires attached_exact(Heap, Current, DANCING); // info:type property for argument Current
  free requires detachable_exact(Heap, n, DANCING); // info:type property for argument n
  modifies Heap;
  requires is_open(Heap, Current); // type:pre tag:open line:164
  requires (Heap[Current, DANCING.right]) != (Void); // type:attached tag:right_open line:165
  requires is_open(Heap, Heap[Current, DANCING.right]); // type:pre tag:right_open line:165
  ensures (Heap[Current, DANCING.right]) == (n); // type:post line:170
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.DANCING.set_right(Heap, Current, n), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.DANCING.set_right(old(Heap), Current, n));
  free ensures HeapSucc(old(Heap), Heap);



function { :inline } variant.DANCING.set_right.1(heap: HeapType, current: ref, n: ref) returns (ref) {
  n
}

implementation DANCING.set_right(Current: ref, n: ref)
{
  entry:
  assume {:captureState "DANCING.set_right"} true;
  // /home/caf/temp/comcom/repo-dancing/dancing.e:168
  // right := n -- preserves `left'
  call update_heap(Current, DANCING.right, n); // line:168
}

procedure DANCING.not_left(Current: ref, new_left: ref, o: ref) returns (Result: bool where true);
  free requires attached_exact(Heap, Current, DANCING); // info:type property for argument Current
  free requires detachable_exact(Heap, new_left, DANCING); // info:type property for argument new_left
  free requires Heap[o, allocated]; // info:type property for argument o
  modifies Heap;
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.DANCING.not_left(Heap, Current, new_left, o), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.DANCING.not_left(old(Heap), Current, new_left, o));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.DANCING.not_left(Heap, Current, new_left, o), readable);



function fun.DANCING.not_left(heap: HeapType, current: ref, new_left: ref, o: ref) returns (bool);

function fun0.DANCING.not_left(heap: HeapType, current: ref, new_left: ref, o: ref) returns (bool);

axiom ((forall heap: HeapType, current: ref, new_left: ref, o: ref :: { fun.DANCING.not_left(heap, current, new_left, o) } { trigger.fun.DANCING.not_left(heap, current, new_left, o) } (pre.fun.DANCING.not_left(heap, current, new_left, o)) ==> ((fun.DANCING.not_left(heap, current, new_left, o)) == ((o) != (heap[current, DANCING.left])))));

axiom ((forall heap: HeapType, current: ref, new_left: ref, o: ref :: { fun.DANCING.not_left(heap, current, new_left, o) } (fun.DANCING.not_left(heap, current, new_left, o)) == (fun0.DANCING.not_left(heap, current, new_left, o))));

axiom ((forall h: HeapType, h': HeapType, current: ref, new_left: ref, o: ref :: { HeapSucc(h, h'), fun0.DANCING.not_left(h, current, new_left, o), fun0.DANCING.not_left(h', current, new_left, o) } ((HeapSucc(h, h')) && (pre.fun.DANCING.not_left(h, current, new_left, o)) && (pre.fun.DANCING.not_left(h', current, new_left, o)) && (same_inside(h, h', read.fun.DANCING.not_left(h, current, new_left, o)))) ==> ((fun0.DANCING.not_left(h, current, new_left, o)) == (fun0.DANCING.not_left(h', current, new_left, o)))));

function { :inline } variant.DANCING.not_left.1(heap: HeapType, current: ref, new_left: ref, o: ref) returns (ref) {
  new_left
}

function { :inline } variant.DANCING.not_left.2(heap: HeapType, current: ref, new_left: ref, o: ref) returns (ref) {
  o
}

implementation DANCING.not_left(Current: ref, new_left: ref, o: ref) returns (Result: bool)
{

  init_locals:
  Result := false;

  entry:
  assume {:captureState "DANCING.not_left"} true;
  // /home/caf/temp/comcom/repo-dancing/dancing.e:180
  // Result := o /= left
  assert readable[Current, DANCING.left]; // type:access tag:attribute_readable line:180 cid:404 fid:81
  Result := (o) != (Heap[Current, DANCING.left]);
}

procedure DANCING.not_right(Current: ref, new_right: ref, o: ref) returns (Result: bool where true);
  free requires attached_exact(Heap, Current, DANCING); // info:type property for argument Current
  free requires detachable_exact(Heap, new_right, DANCING); // info:type property for argument new_right
  free requires Heap[o, allocated]; // info:type property for argument o
  modifies Heap;
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.DANCING.not_right(Heap, Current, new_right, o), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.DANCING.not_right(old(Heap), Current, new_right, o));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.DANCING.not_right(Heap, Current, new_right, o), readable);



function fun.DANCING.not_right(heap: HeapType, current: ref, new_right: ref, o: ref) returns (bool);

function fun0.DANCING.not_right(heap: HeapType, current: ref, new_right: ref, o: ref) returns (bool);

axiom ((forall heap: HeapType, current: ref, new_right: ref, o: ref :: { fun.DANCING.not_right(heap, current, new_right, o) } { trigger.fun.DANCING.not_right(heap, current, new_right, o) } (pre.fun.DANCING.not_right(heap, current, new_right, o)) ==> ((fun.DANCING.not_right(heap, current, new_right, o)) == ((o) != (heap[current, DANCING.right])))));

axiom ((forall heap: HeapType, current: ref, new_right: ref, o: ref :: { fun.DANCING.not_right(heap, current, new_right, o) } (fun.DANCING.not_right(heap, current, new_right, o)) == (fun0.DANCING.not_right(heap, current, new_right, o))));

axiom ((forall h: HeapType, h': HeapType, current: ref, new_right: ref, o: ref :: { HeapSucc(h, h'), fun0.DANCING.not_right(h, current, new_right, o), fun0.DANCING.not_right(h', current, new_right, o) } ((HeapSucc(h, h')) && (pre.fun.DANCING.not_right(h, current, new_right, o)) && (pre.fun.DANCING.not_right(h', current, new_right, o)) && (same_inside(h, h', read.fun.DANCING.not_right(h, current, new_right, o)))) ==> ((fun0.DANCING.not_right(h, current, new_right, o)) == (fun0.DANCING.not_right(h', current, new_right, o)))));

function { :inline } variant.DANCING.not_right.1(heap: HeapType, current: ref, new_right: ref, o: ref) returns (ref) {
  new_right
}

function { :inline } variant.DANCING.not_right.2(heap: HeapType, current: ref, new_right: ref, o: ref) returns (ref) {
  o
}

implementation DANCING.not_right(Current: ref, new_right: ref, o: ref) returns (Result: bool)
{

  init_locals:
  Result := false;

  entry:
  assume {:captureState "DANCING.not_right"} true;
  // /home/caf/temp/comcom/repo-dancing/dancing.e:188
  // Result := o /= right
  assert readable[Current, DANCING.right]; // type:access tag:attribute_readable line:188 cid:404 fid:82
  Result := (o) != (Heap[Current, DANCING.right]);
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

axiom ((forall <T4> $f: Field T4 :: { IsModelField($f, CLIENT) } (IsModelField($f, CLIENT)) <==> ((($f) == (subjects)) || (($f) == (observers)))));

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
  requires (forall <T5> $f: Field T5 :: (($f) != (allocated)) ==> ((Heap[Current, $f]) == (Default($f))));
  ensures (forall <T6> $f: Field T6 :: ((($f) != (allocated)) && (($f) != (closed))) ==> ((Heap[Current, $f]) == (Default($f))));
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
    assert Set#IsEmpty(Heap[Current, observers]); // type:inv tag:default_observers line:96 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, subjects]); // type:inv tag:default_subjects line:96 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, owns]); // type:inv tag:default_owns line:96 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert admissibility2(Heap, Current); // type:inv tag:A2 line:96 cid:1 rid:55
    assume false;
  }
  call wrap(Current); // default:wrapping cid:1 rid:55 line:364
}

procedure CLIENT.test_singleton(Current: ref);
  free requires attached_exact(Heap, Current, CLIENT); // info:type property for argument Current
  modifies Heap;
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.CLIENT.test_singleton(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.CLIENT.test_singleton(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);
  requires is_wrapped(Heap, Current); // type:pre tag:default_is_wrapped default:contracts
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts



function { :inline } variant.CLIENT.test_singleton.1(heap: HeapType, current: ref) returns (int) {
  0
}

implementation CLIENT.test_singleton(Current: ref)
{
  var temp_1: ref;
  var local1: ref where detachable_exact(Heap, local1, DANCING);

  init_locals:
  temp_1 := Void;
  local1 := Void;

  entry:
  assume {:captureState "CLIENT.test_singleton"} true;
  call unwrap(Current); // default:wrapping cid:1 rid:57 line:9
  assume CLIENT.user_inv(Heap, Current);
  // /home/caf/temp/comcom/repo-dancing/client.e:14
  // create n1.make
  call temp_1 := allocate(DANCING); // line:-1
  call create.DANCING.make(temp_1); // line:14 cid:404 rid:5404
  local1 := temp_1;
  // /home/caf/temp/comcom/repo-dancing/client.e:15
  // check n1.right = n1 end
  assert {:subsumption 0} (local1) != (Void); // type:attached line:15
  assert (Heap[local1, DANCING.right]) == (local1); // type:check line:15
  // /home/caf/temp/comcom/repo-dancing/client.e:16
  // check n1.left = n1 end
  assert {:subsumption 0} (local1) != (Void); // type:attached line:16
  assert (Heap[local1, DANCING.left]) == (local1); // type:check line:16
  // /home/caf/temp/comcom/repo-dancing/client.e:18
  // n1.remove
  assert {:subsumption 0} (local1) != (Void); // type:attached line:18
  call DANCING.remove(local1); // line:18 cid:404 rid:5408
  // /home/caf/temp/comcom/repo-dancing/client.e:20
  // n1.unremove
  assert {:subsumption 0} (local1) != (Void); // type:attached line:20
  call DANCING.unremove(local1); // line:20 cid:404 rid:5409
  // /home/caf/temp/comcom/repo-dancing/client.e:21
  // check n1.right = n1 end
  assert {:subsumption 0} (local1) != (Void); // type:attached line:21
  assert (Heap[local1, DANCING.right]) == (local1); // type:check line:21
  // /home/caf/temp/comcom/repo-dancing/client.e:22
  // check n1.left = n1 end
  assert {:subsumption 0} (local1) != (Void); // type:attached line:22
  assert (Heap[local1, DANCING.left]) == (local1); // type:check line:22
  if (*) {
    assert Set#IsEmpty(Heap[Current, observers]); // type:inv tag:default_observers line:96 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, subjects]); // type:inv tag:default_subjects line:96 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, owns]); // type:inv tag:default_owns line:96 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert admissibility2(Heap, Current); // type:inv tag:A2 line:96 cid:1 rid:55
    assume false;
  }
  call wrap(Current); // default:wrapping cid:1 rid:55 line:23
}

procedure CLIENT.test_remove_once(Current: ref);
  free requires attached_exact(Heap, Current, CLIENT); // info:type property for argument Current
  modifies Heap;
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.CLIENT.test_remove_once(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.CLIENT.test_remove_once(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);
  requires is_wrapped(Heap, Current); // type:pre tag:default_is_wrapped default:contracts
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts



function { :inline } variant.CLIENT.test_remove_once.1(heap: HeapType, current: ref) returns (int) {
  0
}

implementation CLIENT.test_remove_once(Current: ref)
{
  var temp_2: ref;
  var temp_3: ref;
  var temp_4: ref;
  var local1: ref where detachable_exact(Heap, local1, DANCING);
  var local2: ref where detachable_exact(Heap, local2, DANCING);
  var local3: ref where detachable_exact(Heap, local3, DANCING);

  init_locals:
  temp_2 := Void;
  temp_3 := Void;
  temp_4 := Void;
  local1 := Void;
  local2 := Void;
  local3 := Void;

  entry:
  assume {:captureState "CLIENT.test_remove_once"} true;
  call unwrap(Current); // default:wrapping cid:1 rid:57 line:25
  assume CLIENT.user_inv(Heap, Current);
  // /home/caf/temp/comcom/repo-dancing/client.e:30
  // create n1.make
  call temp_2 := allocate(DANCING); // line:-1
  call create.DANCING.make(temp_2); // line:30 cid:404 rid:5404
  local1 := temp_2;
  // /home/caf/temp/comcom/repo-dancing/client.e:31
  // create n2.make
  call temp_3 := allocate(DANCING); // line:-1
  call create.DANCING.make(temp_3); // line:31 cid:404 rid:5404
  local2 := temp_3;
  // /home/caf/temp/comcom/repo-dancing/client.e:32
  // create n3.make
  call temp_4 := allocate(DANCING); // line:-1
  call create.DANCING.make(temp_4); // line:32 cid:404 rid:5404
  local3 := temp_4;
  // /home/caf/temp/comcom/repo-dancing/client.e:34
  // n1.insert_right (n2)
  assert {:subsumption 0} (local1) != (Void); // type:attached line:34
  call DANCING.insert_right(local1, local2); // line:34 cid:404 rid:5407
  // /home/caf/temp/comcom/repo-dancing/client.e:35
  // n2.insert_right (n3)
  assert {:subsumption 0} (local2) != (Void); // type:attached line:35
  call DANCING.insert_right(local2, local3); // line:35 cid:404 rid:5407
  // /home/caf/temp/comcom/repo-dancing/client.e:37
  // check n1.right = n2 end
  assert {:subsumption 0} (local1) != (Void); // type:attached line:37
  assert (Heap[local1, DANCING.right]) == (local2); // type:check line:37
  // /home/caf/temp/comcom/repo-dancing/client.e:38
  // check n1.left = n3 end
  assert {:subsumption 0} (local1) != (Void); // type:attached line:38
  assert (Heap[local1, DANCING.left]) == (local3); // type:check line:38
  // /home/caf/temp/comcom/repo-dancing/client.e:39
  // check n2.right = n3 end
  assert {:subsumption 0} (local2) != (Void); // type:attached line:39
  assert (Heap[local2, DANCING.right]) == (local3); // type:check line:39
  // /home/caf/temp/comcom/repo-dancing/client.e:40
  // check n2.left = n1 end
  assert {:subsumption 0} (local2) != (Void); // type:attached line:40
  assert (Heap[local2, DANCING.left]) == (local1); // type:check line:40
  // /home/caf/temp/comcom/repo-dancing/client.e:41
  // check n3.right = n1 end
  assert {:subsumption 0} (local3) != (Void); // type:attached line:41
  assert (Heap[local3, DANCING.right]) == (local1); // type:check line:41
  // /home/caf/temp/comcom/repo-dancing/client.e:42
  // check n3.left = n2 end
  assert {:subsumption 0} (local3) != (Void); // type:attached line:42
  assert (Heap[local3, DANCING.left]) == (local2); // type:check line:42
  // /home/caf/temp/comcom/repo-dancing/client.e:44
  // n2.remove
  assert {:subsumption 0} (local2) != (Void); // type:attached line:44
  call DANCING.remove(local2); // line:44 cid:404 rid:5408
  // /home/caf/temp/comcom/repo-dancing/client.e:46
  // check n1.right = n3 end
  assert {:subsumption 0} (local1) != (Void); // type:attached line:46
  assert (Heap[local1, DANCING.right]) == (local3); // type:check line:46
  // /home/caf/temp/comcom/repo-dancing/client.e:47
  // check n1.left = n3 end
  assert {:subsumption 0} (local1) != (Void); // type:attached line:47
  assert (Heap[local1, DANCING.left]) == (local3); // type:check line:47
  // /home/caf/temp/comcom/repo-dancing/client.e:48
  // check n2.right = n3 end
  assert {:subsumption 0} (local2) != (Void); // type:attached line:48
  assert (Heap[local2, DANCING.right]) == (local3); // type:check line:48
  // /home/caf/temp/comcom/repo-dancing/client.e:49
  // check n2.left = n1 end
  assert {:subsumption 0} (local2) != (Void); // type:attached line:49
  assert (Heap[local2, DANCING.left]) == (local1); // type:check line:49
  // /home/caf/temp/comcom/repo-dancing/client.e:50
  // check n3.right = n1 end
  assert {:subsumption 0} (local3) != (Void); // type:attached line:50
  assert (Heap[local3, DANCING.right]) == (local1); // type:check line:50
  // /home/caf/temp/comcom/repo-dancing/client.e:51
  // check n3.left = n1 end
  assert {:subsumption 0} (local3) != (Void); // type:attached line:51
  assert (Heap[local3, DANCING.left]) == (local1); // type:check line:51
  // /home/caf/temp/comcom/repo-dancing/client.e:53
  // n2.unremove
  assert {:subsumption 0} (local2) != (Void); // type:attached line:53
  call DANCING.unremove(local2); // line:53 cid:404 rid:5409
  // /home/caf/temp/comcom/repo-dancing/client.e:55
  // check n1.right = n2 end
  assert {:subsumption 0} (local1) != (Void); // type:attached line:55
  assert (Heap[local1, DANCING.right]) == (local2); // type:check line:55
  // /home/caf/temp/comcom/repo-dancing/client.e:56
  // check n1.left = n3 end
  assert {:subsumption 0} (local1) != (Void); // type:attached line:56
  assert (Heap[local1, DANCING.left]) == (local3); // type:check line:56
  // /home/caf/temp/comcom/repo-dancing/client.e:57
  // check n2.right = n3 end
  assert {:subsumption 0} (local2) != (Void); // type:attached line:57
  assert (Heap[local2, DANCING.right]) == (local3); // type:check line:57
  // /home/caf/temp/comcom/repo-dancing/client.e:58
  // check n2.left = n1 end
  assert {:subsumption 0} (local2) != (Void); // type:attached line:58
  assert (Heap[local2, DANCING.left]) == (local1); // type:check line:58
  // /home/caf/temp/comcom/repo-dancing/client.e:59
  // check n3.right = n1 end
  assert {:subsumption 0} (local3) != (Void); // type:attached line:59
  assert (Heap[local3, DANCING.right]) == (local1); // type:check line:59
  // /home/caf/temp/comcom/repo-dancing/client.e:60
  // check n3.left = n2 end
  assert {:subsumption 0} (local3) != (Void); // type:attached line:60
  assert (Heap[local3, DANCING.left]) == (local2); // type:check line:60
  if (*) {
    assert Set#IsEmpty(Heap[Current, observers]); // type:inv tag:default_observers line:96 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, subjects]); // type:inv tag:default_subjects line:96 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, owns]); // type:inv tag:default_owns line:96 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert admissibility2(Heap, Current); // type:inv tag:A2 line:96 cid:1 rid:55
    assume false;
  }
  call wrap(Current); // default:wrapping cid:1 rid:55 line:61
}

procedure CLIENT.test_remove_multiple(Current: ref);
  free requires attached_exact(Heap, Current, CLIENT); // info:type property for argument Current
  modifies Heap;
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.CLIENT.test_remove_multiple(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.CLIENT.test_remove_multiple(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);
  requires is_wrapped(Heap, Current); // type:pre tag:default_is_wrapped default:contracts
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts



function { :inline } variant.CLIENT.test_remove_multiple.1(heap: HeapType, current: ref) returns (int) {
  0
}

implementation CLIENT.test_remove_multiple(Current: ref)
{
  var temp_5: ref;
  var temp_6: ref;
  var temp_7: ref;
  var local1: ref where detachable_exact(Heap, local1, DANCING);
  var local2: ref where detachable_exact(Heap, local2, DANCING);
  var local3: ref where detachable_exact(Heap, local3, DANCING);

  init_locals:
  temp_5 := Void;
  temp_6 := Void;
  temp_7 := Void;
  local1 := Void;
  local2 := Void;
  local3 := Void;

  entry:
  assume {:captureState "CLIENT.test_remove_multiple"} true;
  call unwrap(Current); // default:wrapping cid:1 rid:57 line:63
  assume CLIENT.user_inv(Heap, Current);
  // /home/caf/temp/comcom/repo-dancing/client.e:68
  // create n1.make
  call temp_5 := allocate(DANCING); // line:-1
  call create.DANCING.make(temp_5); // line:68 cid:404 rid:5404
  local1 := temp_5;
  // /home/caf/temp/comcom/repo-dancing/client.e:69
  // create n2.make
  call temp_6 := allocate(DANCING); // line:-1
  call create.DANCING.make(temp_6); // line:69 cid:404 rid:5404
  local2 := temp_6;
  // /home/caf/temp/comcom/repo-dancing/client.e:70
  // create n3.make
  call temp_7 := allocate(DANCING); // line:-1
  call create.DANCING.make(temp_7); // line:70 cid:404 rid:5404
  local3 := temp_7;
  // /home/caf/temp/comcom/repo-dancing/client.e:72
  // n1.insert_right (n2)
  assert {:subsumption 0} (local1) != (Void); // type:attached line:72
  call DANCING.insert_right(local1, local2); // line:72 cid:404 rid:5407
  // /home/caf/temp/comcom/repo-dancing/client.e:73
  // n2.insert_right (n3)
  assert {:subsumption 0} (local2) != (Void); // type:attached line:73
  call DANCING.insert_right(local2, local3); // line:73 cid:404 rid:5407
  // /home/caf/temp/comcom/repo-dancing/client.e:75
  // check n1.right = n2 end
  assert {:subsumption 0} (local1) != (Void); // type:attached line:75
  assert (Heap[local1, DANCING.right]) == (local2); // type:check line:75
  // /home/caf/temp/comcom/repo-dancing/client.e:76
  // check n1.left = n3 end
  assert {:subsumption 0} (local1) != (Void); // type:attached line:76
  assert (Heap[local1, DANCING.left]) == (local3); // type:check line:76
  // /home/caf/temp/comcom/repo-dancing/client.e:77
  // check n2.right = n3 end
  assert {:subsumption 0} (local2) != (Void); // type:attached line:77
  assert (Heap[local2, DANCING.right]) == (local3); // type:check line:77
  // /home/caf/temp/comcom/repo-dancing/client.e:78
  // check n2.left = n1 end
  assert {:subsumption 0} (local2) != (Void); // type:attached line:78
  assert (Heap[local2, DANCING.left]) == (local1); // type:check line:78
  // /home/caf/temp/comcom/repo-dancing/client.e:79
  // check n3.right = n1 end
  assert {:subsumption 0} (local3) != (Void); // type:attached line:79
  assert (Heap[local3, DANCING.right]) == (local1); // type:check line:79
  // /home/caf/temp/comcom/repo-dancing/client.e:80
  // check n3.left = n2 end
  assert {:subsumption 0} (local3) != (Void); // type:attached line:80
  assert (Heap[local3, DANCING.left]) == (local2); // type:check line:80
  // /home/caf/temp/comcom/repo-dancing/client.e:82
  // n1.remove
  assert {:subsumption 0} (local1) != (Void); // type:attached line:82
  call DANCING.remove(local1); // line:82 cid:404 rid:5408
  // /home/caf/temp/comcom/repo-dancing/client.e:83
  // n2.remove
  assert {:subsumption 0} (local2) != (Void); // type:attached line:83
  call DANCING.remove(local2); // line:83 cid:404 rid:5408
  // /home/caf/temp/comcom/repo-dancing/client.e:84
  // n3.remove
  assert {:subsumption 0} (local3) != (Void); // type:attached line:84
  call DANCING.remove(local3); // line:84 cid:404 rid:5408
  // /home/caf/temp/comcom/repo-dancing/client.e:86
  // n3.unremove
  assert {:subsumption 0} (local3) != (Void); // type:attached line:86
  call DANCING.unremove(local3); // line:86 cid:404 rid:5409
  // /home/caf/temp/comcom/repo-dancing/client.e:87
  // n2.unremove
  assert {:subsumption 0} (local2) != (Void); // type:attached line:87
  call DANCING.unremove(local2); // line:87 cid:404 rid:5409
  // /home/caf/temp/comcom/repo-dancing/client.e:88
  // n1.unremove
  assert {:subsumption 0} (local1) != (Void); // type:attached line:88
  call DANCING.unremove(local1); // line:88 cid:404 rid:5409
  // /home/caf/temp/comcom/repo-dancing/client.e:90
  // check n1.right = n2 end
  assert {:subsumption 0} (local1) != (Void); // type:attached line:90
  assert (Heap[local1, DANCING.right]) == (local2); // type:check line:90
  // /home/caf/temp/comcom/repo-dancing/client.e:91
  // check n1.left = n3 end
  assert {:subsumption 0} (local1) != (Void); // type:attached line:91
  assert (Heap[local1, DANCING.left]) == (local3); // type:check line:91
  // /home/caf/temp/comcom/repo-dancing/client.e:92
  // check n2.right = n3 end
  assert {:subsumption 0} (local2) != (Void); // type:attached line:92
  assert (Heap[local2, DANCING.right]) == (local3); // type:check line:92
  // /home/caf/temp/comcom/repo-dancing/client.e:93
  // check n2.left = n1 end
  assert {:subsumption 0} (local2) != (Void); // type:attached line:93
  assert (Heap[local2, DANCING.left]) == (local1); // type:check line:93
  // /home/caf/temp/comcom/repo-dancing/client.e:94
  // check n3.right = n1 end
  assert {:subsumption 0} (local3) != (Void); // type:attached line:94
  assert (Heap[local3, DANCING.right]) == (local1); // type:check line:94
  // /home/caf/temp/comcom/repo-dancing/client.e:95
  // check n3.left = n2 end
  assert {:subsumption 0} (local3) != (Void); // type:attached line:95
  assert (Heap[local3, DANCING.left]) == (local2); // type:check line:95
  if (*) {
    assert Set#IsEmpty(Heap[Current, observers]); // type:inv tag:default_observers line:96 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, subjects]); // type:inv tag:default_subjects line:96 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, owns]); // type:inv tag:default_owns line:96 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert admissibility2(Heap, Current); // type:inv tag:A2 line:96 cid:1 rid:55
    assume false;
  }
  call wrap(Current); // default:wrapping cid:1 rid:55 line:96
}

const DANCING.left: Field (ref);

axiom ((FieldId(DANCING.left, DANCING)) == (81));

axiom ((forall heap: HeapType, o: ref :: { heap[o, DANCING.left] } ((IsHeap(heap)) && (attached(heap, o, DANCING))) ==> (detachable_exact(heap, heap[o, DANCING.left], DANCING))));

axiom ((forall heap: HeapType, current: ref, v: ref, o: ref :: { guard(heap, current, DANCING.left, v, o) } (attached_exact(heap, current, DANCING)) ==> ((guard(heap, current, DANCING.left, v, o)) <==> (fun.DANCING.not_left(heap, current, v, o)))));

axiom ((forall heap: HeapType, current: ref, v: ref, o: ref :: { guard(heap, current, DANCING.left, v, o) } (attached(heap, current, DANCING)) ==> ((guard(heap, current, DANCING.left, v, o)) ==> (fun.DANCING.not_left(heap, current, v, o)))));

const DANCING.right: Field (ref);

axiom ((FieldId(DANCING.right, DANCING)) == (82));

axiom ((forall heap: HeapType, o: ref :: { heap[o, DANCING.right] } ((IsHeap(heap)) && (attached(heap, o, DANCING))) ==> (detachable_exact(heap, heap[o, DANCING.right], DANCING))));

axiom ((forall heap: HeapType, current: ref, v: ref, o: ref :: { guard(heap, current, DANCING.right, v, o) } (attached_exact(heap, current, DANCING)) ==> ((guard(heap, current, DANCING.right, v, o)) <==> (fun.DANCING.not_right(heap, current, v, o)))));

axiom ((forall heap: HeapType, current: ref, v: ref, o: ref :: { guard(heap, current, DANCING.right, v, o) } (attached(heap, current, DANCING)) ==> ((guard(heap, current, DANCING.right, v, o)) ==> (fun.DANCING.not_right(heap, current, v, o)))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, owns, v, o) } (attached_exact(heap, current, ANY)) ==> ((guard(heap, current, owns, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, subjects, v, o) } (attached_exact(heap, current, ANY)) ==> ((guard(heap, current, subjects, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached_exact(heap, current, ANY)) ==> ((guard(heap, current, observers, v, o)) <==> (fun.ANY.in_observers(heap, current, v, o)))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached(heap, current, ANY)) ==> ((guard(heap, current, observers, v, o)) ==> (fun.ANY.in_observers(heap, current, v, o)))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, owns, v, o) } (attached_exact(heap, current, DANCING)) ==> ((guard(heap, current, owns, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, subjects, v, o) } (attached_exact(heap, current, DANCING)) ==> ((guard(heap, current, subjects, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached_exact(heap, current, DANCING)) ==> ((guard(heap, current, observers, v, o)) <==> (fun.DANCING.in_observers(heap, current, v, o)))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached(heap, current, DANCING)) ==> ((guard(heap, current, observers, v, o)) ==> (fun.DANCING.in_observers(heap, current, v, o)))));

function modify.DANCING.make(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T7> $o: ref, $f: Field T7 :: { modify.DANCING.make(heap, current)[$o, $f] } (modify.DANCING.make(heap, current)[$o, $f]) <==> (($o) == (current))))));

function modify.DANCING.insert_right(heap: HeapType, current: ref, n: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, n: ref :: (IsHeap(heap)) ==> ((forall <T8> $o: ref, $f: Field T8 :: { modify.DANCING.insert_right(heap, current, n)[$o, $f] } (modify.DANCING.insert_right(heap, current, n)[$o, $f]) <==> (((($o) == (current)) && ((($f) == (DANCING.right)) || (($f) == (closed)) || (($f) == (subjects)) || (($f) == (observers)))) || ((($o) == (heap[current, DANCING.right])) && ((($f) == (DANCING.left)) || (($f) == (closed)) || (($f) == (subjects)) || (($f) == (observers)))) || (($o) == (n)))))));

function DANCING#E#left_consistent#right_consistent#A2.filtered_inv(heap: HeapType, current: ref) returns (bool) {
  ((heap[current, DANCING.left]) != (Void)) && ((heap[current, DANCING.right]) != (Void)) && (Set#Equal(heap[current, subjects], Set#Extended(Set#Singleton(heap[current, DANCING.left]), heap[current, DANCING.right]))) && (Set#Equal(heap[current, observers], Set#Extended(Set#Singleton(heap[current, DANCING.left]), heap[current, DANCING.right]))) && (Set#IsEmpty(heap[current, owns]))
}

axiom ((forall h: HeapType, o: ref :: { DANCING#E#left_consistent#right_consistent#A2.filtered_inv(h, o) } ((IsHeap(h)) && (attached(h, o, DANCING)) && (h[o, closed])) ==> (DANCING#E#left_consistent#right_consistent#A2.filtered_inv(h, o))));

function modify.DANCING.remove(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T9> $o: ref, $f: Field T9 :: { modify.DANCING.remove(heap, current)[$o, $f] } (modify.DANCING.remove(heap, current)[$o, $f]) <==> (((($o) == (current)) && (($f) == (closed))) || ((($o) == (heap[current, DANCING.right])) && ((($f) == (DANCING.left)) || (($f) == (closed)) || (($f) == (subjects)) || (($f) == (observers)))) || ((($o) == (heap[current, DANCING.left])) && ((($f) == (DANCING.right)) || (($f) == (closed)) || (($f) == (subjects)) || (($f) == (observers)))))))));

function modify.DANCING.unremove(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T10> $o: ref, $f: Field T10 :: { modify.DANCING.unremove(heap, current)[$o, $f] } (modify.DANCING.unremove(heap, current)[$o, $f]) <==> (((($o) == (current)) && (($f) == (closed))) || ((($o) == (heap[current, DANCING.right])) && ((($f) == (DANCING.left)) || (($f) == (closed)) || (($f) == (subjects)) || (($f) == (observers)))) || ((($o) == (heap[current, DANCING.left])) && ((($f) == (DANCING.right)) || (($f) == (closed)) || (($f) == (subjects)) || (($f) == (observers)))))))));

function modify.DANCING.set_left(heap: HeapType, current: ref, n: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, n: ref :: (IsHeap(heap)) ==> ((forall <T11> $o: ref, $f: Field T11 :: { modify.DANCING.set_left(heap, current, n)[$o, $f] } (modify.DANCING.set_left(heap, current, n)[$o, $f]) <==> ((($o) == (current)) && (($f) == (DANCING.left)))))));

function modify.DANCING.set_right(heap: HeapType, current: ref, n: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, n: ref :: (IsHeap(heap)) ==> ((forall <T12> $o: ref, $f: Field T12 :: { modify.DANCING.set_right(heap, current, n)[$o, $f] } (modify.DANCING.set_right(heap, current, n)[$o, $f]) <==> ((($o) == (current)) && (($f) == (DANCING.right)))))));

function modify.DANCING.not_left(heap: HeapType, current: ref, new_left: ref, o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_left: ref, o: ref :: (IsHeap(heap)) ==> ((forall <T13> $o: ref, $f: Field T13 :: { modify.DANCING.not_left(heap, current, new_left, o)[$o, $f] } (modify.DANCING.not_left(heap, current, new_left, o)[$o, $f]) <==> (false)))));

function read.fun.DANCING.not_left(heap: HeapType, current: ref, new_left: ref, o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_left: ref, o: ref :: (IsHeap(heap)) ==> ((forall <T14> $o: ref, $f: Field T14 :: { read.fun.DANCING.not_left(heap, current, new_left, o)[$o, $f] } (read.fun.DANCING.not_left(heap, current, new_left, o)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.DANCING.not_left(heap: HeapType, current: ref, new_left: ref, o: ref) returns (bool) {
  true
}

function trigger.fun.DANCING.not_left(heap: HeapType, current: ref, new_left: ref, o: ref) returns (bool);

function modify.DANCING.not_right(heap: HeapType, current: ref, new_right: ref, o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_right: ref, o: ref :: (IsHeap(heap)) ==> ((forall <T15> $o: ref, $f: Field T15 :: { modify.DANCING.not_right(heap, current, new_right, o)[$o, $f] } (modify.DANCING.not_right(heap, current, new_right, o)[$o, $f]) <==> (false)))));

function read.fun.DANCING.not_right(heap: HeapType, current: ref, new_right: ref, o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_right: ref, o: ref :: (IsHeap(heap)) ==> ((forall <T16> $o: ref, $f: Field T16 :: { read.fun.DANCING.not_right(heap, current, new_right, o)[$o, $f] } (read.fun.DANCING.not_right(heap, current, new_right, o)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.DANCING.not_right(heap: HeapType, current: ref, new_right: ref, o: ref) returns (bool) {
  true
}

function trigger.fun.DANCING.not_right(heap: HeapType, current: ref, new_right: ref, o: ref) returns (bool);

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, owns, v, o) } (attached_exact(heap, current, CLIENT)) ==> ((guard(heap, current, owns, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, subjects, v, o) } (attached_exact(heap, current, CLIENT)) ==> ((guard(heap, current, subjects, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached_exact(heap, current, CLIENT)) ==> ((guard(heap, current, observers, v, o)) <==> (fun.CLIENT.in_observers(heap, current, v, o)))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached(heap, current, CLIENT)) ==> ((guard(heap, current, observers, v, o)) ==> (fun.CLIENT.in_observers(heap, current, v, o)))));

function modify.CLIENT.default_create(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T17> $o: ref, $f: Field T17 :: { modify.CLIENT.default_create(heap, current)[$o, $f] } (modify.CLIENT.default_create(heap, current)[$o, $f]) <==> (($o) == (current))))));

function modify.CLIENT.test_singleton(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T18> $o: ref, $f: Field T18 :: { modify.CLIENT.test_singleton(heap, current)[$o, $f] } (modify.CLIENT.test_singleton(heap, current)[$o, $f]) <==> (($o) == (current))))));

function modify.CLIENT.test_remove_once(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T19> $o: ref, $f: Field T19 :: { modify.CLIENT.test_remove_once(heap, current)[$o, $f] } (modify.CLIENT.test_remove_once(heap, current)[$o, $f]) <==> (($o) == (current))))));

function modify.CLIENT.test_remove_multiple(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T20> $o: ref, $f: Field T20 :: { modify.CLIENT.test_remove_multiple(heap, current)[$o, $f] } (modify.CLIENT.test_remove_multiple(heap, current)[$o, $f]) <==> (($o) == (current))))));

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

procedure DANCING.in_observers(Current: ref, new_observers: Set (ref), o: ref) returns (Result: bool where true);
  free requires attached_exact(Heap, Current, DANCING); // info:type property for argument Current
  free requires Set#ItemsType(Heap, new_observers, ANY); // info:type property for argument new_observers
  free requires Heap[o, allocated]; // info:type property for argument o
  modifies Heap;
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.DANCING.in_observers(Heap, Current, new_observers, o), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.DANCING.in_observers(old(Heap), Current, new_observers, o));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.DANCING.in_observers(Heap, Current, new_observers, o), readable);



function fun.DANCING.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function fun0.DANCING.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.DANCING.in_observers(heap, current, new_observers, o) } { trigger.fun.DANCING.in_observers(heap, current, new_observers, o) } (pre.fun.DANCING.in_observers(heap, current, new_observers, o)) ==> ((fun.DANCING.in_observers(heap, current, new_observers, o)) == (new_observers[o]))));

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.DANCING.in_observers(heap, current, new_observers, o) } (fun.DANCING.in_observers(heap, current, new_observers, o)) == (fun0.DANCING.in_observers(heap, current, new_observers, o))));

axiom ((forall h: HeapType, h': HeapType, current: ref, new_observers: Set (ref), o: ref :: { HeapSucc(h, h'), fun0.DANCING.in_observers(h, current, new_observers, o), fun0.DANCING.in_observers(h', current, new_observers, o) } ((HeapSucc(h, h')) && (pre.fun.DANCING.in_observers(h, current, new_observers, o)) && (pre.fun.DANCING.in_observers(h', current, new_observers, o)) && (same_inside(h, h', read.fun.DANCING.in_observers(h, current, new_observers, o)))) ==> ((fun0.DANCING.in_observers(h, current, new_observers, o)) == (fun0.DANCING.in_observers(h', current, new_observers, o)))));

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

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T21> $o: ref, $f: Field T21 :: { modify.ANY.in_observers(heap, current, new_observers, o)[$o, $f] } (modify.ANY.in_observers(heap, current, new_observers, o)[$o, $f]) <==> (false)))));

function read.fun.ANY.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T22> $o: ref, $f: Field T22 :: { read.fun.ANY.in_observers(heap, current, new_observers, o)[$o, $f] } (read.fun.ANY.in_observers(heap, current, new_observers, o)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.ANY.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool) {
  true
}

function trigger.fun.ANY.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function modify.DANCING.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T23> $o: ref, $f: Field T23 :: { modify.DANCING.in_observers(heap, current, new_observers, o)[$o, $f] } (modify.DANCING.in_observers(heap, current, new_observers, o)[$o, $f]) <==> (false)))));

function read.fun.DANCING.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T24> $o: ref, $f: Field T24 :: { read.fun.DANCING.in_observers(heap, current, new_observers, o)[$o, $f] } (read.fun.DANCING.in_observers(heap, current, new_observers, o)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.DANCING.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool) {
  true
}

function trigger.fun.DANCING.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function modify.CLIENT.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T25> $o: ref, $f: Field T25 :: { modify.CLIENT.in_observers(heap, current, new_observers, o)[$o, $f] } (modify.CLIENT.in_observers(heap, current, new_observers, o)[$o, $f]) <==> (false)))));

function read.fun.CLIENT.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T26> $o: ref, $f: Field T26 :: { read.fun.CLIENT.in_observers(heap, current, new_observers, o)[$o, $f] } (read.fun.CLIENT.in_observers(heap, current, new_observers, o)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.CLIENT.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool) {
  true
}

function trigger.fun.CLIENT.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);
