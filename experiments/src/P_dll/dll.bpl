// Automatically generated (12/12/2017 1:54:22.075 PM)

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

const unique CLIENT: Type;

axiom ((CLIENT) <: (ANY));

axiom ((forall t: Type :: { (CLIENT) <: (t) } ((CLIENT) <: (t)) <==> (((t) == (CLIENT)) || ((ANY) <: (t)))));

axiom ((FieldId(allocated, CLIENT)) == (-1));

axiom ((FieldId(closed, CLIENT)) == (-2));

axiom ((FieldId(owner, CLIENT)) == (-3));

axiom ((FieldId(owns, CLIENT)) == (-4));

axiom ((FieldId(observers, CLIENT)) == (-5));

axiom ((FieldId(subjects, CLIENT)) == (-6));

axiom ((forall <T0> $f: Field T0 :: { IsModelField($f, CLIENT) } (IsModelField($f, CLIENT)) <==> ((($f) == (subjects)) || (($f) == (observers)))));

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
  requires (forall <T2> $f: Field T2 :: (($f) != (allocated)) ==> ((Heap[Current, $f]) == (Default($f))));
  ensures (forall <T3> $f: Field T3 :: ((($f) != (allocated)) && (($f) != (closed))) ==> ((Heap[Current, $f]) == (Default($f))));
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
    assert Set#IsEmpty(Heap[Current, observers]); // type:inv tag:default_observers line:27 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, subjects]); // type:inv tag:default_subjects line:27 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, owns]); // type:inv tag:default_owns line:27 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert admissibility2(Heap, Current); // type:inv tag:A2 line:27 cid:1 rid:55
    assume false;
  }
  call wrap(Current); // default:wrapping cid:1 rid:55 line:364
}

procedure CLIENT.test_dll(Current: ref);
  free requires attached_exact(Heap, Current, CLIENT); // info:type property for argument Current
  modifies Heap;
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.CLIENT.test_dll(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.CLIENT.test_dll(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);
  requires is_wrapped(Heap, Current); // type:pre tag:default_is_wrapped default:contracts
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts



function { :inline } variant.CLIENT.test_dll.1(heap: HeapType, current: ref) returns (int) {
  0
}

implementation CLIENT.test_dll(Current: ref)
{
  var temp_1: ref;
  var temp_2: ref;
  var local1: ref where detachable_exact(Heap, local1, NODE);
  var local2: ref where detachable_exact(Heap, local2, NODE);

  init_locals:
  temp_1 := Void;
  temp_2 := Void;
  local1 := Void;
  local2 := Void;

  entry:
  assume {:captureState "CLIENT.test_dll"} true;
  call unwrap(Current); // default:wrapping cid:1 rid:57 line:9
  assume CLIENT.user_inv(Heap, Current);
  // /home/caf/temp/comcom/repo-dll/client.e:14
  // create n1.make
  call temp_1 := allocate(NODE); // line:-1
  call create.NODE.make(temp_1); // line:14 cid:404 rid:5402
  local1 := temp_1;
  // /home/caf/temp/comcom/repo-dll/client.e:15
  // check n1_singleton: n1.left = n1 end
  assert {:subsumption 0} (local1) != (Void); // type:attached line:15
  assert (Heap[local1, NODE.left]) == (local1); // type:check tag:n1_singleton line:15
  // /home/caf/temp/comcom/repo-dll/client.e:17
  // n1.insert_right (n1)
  assert {:subsumption 0} (local1) != (Void); // type:attached line:17
  call NODE.insert_right(local1, local1); // line:17 cid:404 rid:5405
  // /home/caf/temp/comcom/repo-dll/client.e:18
  // check n1_singleton: n1.left = n1 end
  assert {:subsumption 0} (local1) != (Void); // type:attached line:18
  assert (Heap[local1, NODE.left]) == (local1); // type:check tag:n1_singleton line:18
  // /home/caf/temp/comcom/repo-dll/client.e:20
  // create n2.make
  call temp_2 := allocate(NODE); // line:-1
  call create.NODE.make(temp_2); // line:20 cid:404 rid:5402
  local2 := temp_2;
  // /home/caf/temp/comcom/repo-dll/client.e:21
  // n1.insert_right (n2)
  assert {:subsumption 0} (local1) != (Void); // type:attached line:21
  call NODE.insert_right(local1, local2); // line:21 cid:404 rid:5405
  // /home/caf/temp/comcom/repo-dll/client.e:22
  // check connected: n1.left = n2 and n2.left = n1 end
  assert {:subsumption 0} (local1) != (Void); // type:attached line:22
  assert {:subsumption 0} (local2) != (Void); // type:attached line:22
  assert ((Heap[local1, NODE.left]) == (local2)) && ((Heap[local2, NODE.left]) == (local1)); // type:check tag:connected line:22
  // /home/caf/temp/comcom/repo-dll/client.e:24
  // n2.remove
  assert {:subsumption 0} (local2) != (Void); // type:attached line:24
  call NODE.remove(local2); // line:24 cid:404 rid:5406
  // /home/caf/temp/comcom/repo-dll/client.e:25
  // check n2_singleton: n2.left = n2 end
  assert {:subsumption 0} (local2) != (Void); // type:attached line:25
  assert (Heap[local2, NODE.left]) == (local2); // type:check tag:n2_singleton line:25
  // /home/caf/temp/comcom/repo-dll/client.e:26
  // check n1_singleton: n1.left = n1 end
  assert {:subsumption 0} (local1) != (Void); // type:attached line:26
  assert (Heap[local1, NODE.left]) == (local1); // type:check tag:n1_singleton line:26
  if (*) {
    assert Set#IsEmpty(Heap[Current, observers]); // type:inv tag:default_observers line:27 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, subjects]); // type:inv tag:default_subjects line:27 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, owns]); // type:inv tag:default_owns line:27 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert admissibility2(Heap, Current); // type:inv tag:A2 line:27 cid:1 rid:55
    assume false;
  }
  call wrap(Current); // default:wrapping cid:1 rid:55 line:27
}

const unique NODE: Type;

axiom (is_frozen(NODE));

axiom ((NODE) <: (ANY));

axiom ((forall t: Type :: { (NODE) <: (t) } ((NODE) <: (t)) <==> (((t) == (NODE)) || ((ANY) <: (t)))));

axiom ((FieldId(allocated, NODE)) == (-1));

axiom ((FieldId(closed, NODE)) == (-2));

axiom ((FieldId(owner, NODE)) == (-3));

axiom ((FieldId(owns, NODE)) == (-4));

axiom ((FieldId(observers, NODE)) == (-5));

axiom ((FieldId(subjects, NODE)) == (-6));

axiom ((forall <T5> $f: Field T5 :: { IsModelField($f, NODE) } (IsModelField($f, NODE)) <==> ((($f) == (subjects)) || (($f) == (observers)))));

function { :inline } NODE.user_inv(heap: HeapType, current: ref) returns (bool) {
  ((heap[current, NODE.left]) != (Void)) && ((heap[current, NODE.right]) != (Void)) && (Set#Equal(heap[current, subjects], Set#Extended(Set#Singleton(heap[current, NODE.left]), heap[current, NODE.right]))) && (Set#Equal(heap[current, observers], Set#Extended(Set#Singleton(heap[current, NODE.left]), heap[current, NODE.right]))) && ((heap[heap[current, NODE.left], NODE.right]) == (current)) && ((heap[heap[current, NODE.right], NODE.left]) == (current)) && (Set#IsEmpty(heap[current, owns])) && (admissibility2(heap, current))
}

function NODE.subjects.static(heap: HeapType, current: ref) returns (Set (ref)) {
  Set#Extended(Set#Singleton(heap[current, NODE.left]), heap[current, NODE.right])
}

function NODE.observers.static(heap: HeapType, current: ref) returns (Set (ref)) {
  Set#Extended(Set#Singleton(heap[current, NODE.left]), heap[current, NODE.right])
}

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached_exact(heap, current, NODE)) ==> ((user_inv(heap, current)) <==> (NODE.user_inv(heap, current)))));

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached(heap, current, NODE)) ==> ((user_inv(heap, current)) ==> (NODE.user_inv(heap, current)))));

procedure NODE.invariant_admissibility_check(Current: ref);
  requires attached_exact(Heap, Current, NODE);



implementation NODE.invariant_admissibility_check(Current: ref)
{
  entry:
  goto pre, a2, a3;
  pre:
  assert user_inv_readable(Heap, Current)[Current, NODE.left]; // type:access tag:attribute_readable line:153 cid:404 fid:81
  assume (Heap[Current, NODE.left]) != (Void);
  assert user_inv_readable(Heap, Current)[Current, NODE.right]; // type:access tag:attribute_readable line:154 cid:404 fid:82
  assume (Heap[Current, NODE.right]) != (Void);
  assert user_inv_readable(Heap, Current)[Current, NODE.left]; // type:access tag:attribute_readable line:155 cid:404 fid:81
  assert user_inv_readable(Heap, Current)[Current, NODE.right]; // type:access tag:attribute_readable line:155 cid:404 fid:82
  assume Set#Equal(Heap[Current, subjects], Set#Extended(Set#Singleton(Heap[Current, NODE.left]), Heap[Current, NODE.right]));
  assert user_inv_readable(Heap, Current)[Current, NODE.left]; // type:access tag:attribute_readable line:156 cid:404 fid:81
  assert user_inv_readable(Heap, Current)[Current, NODE.right]; // type:access tag:attribute_readable line:156 cid:404 fid:82
  assume Set#Equal(Heap[Current, observers], Set#Extended(Set#Singleton(Heap[Current, NODE.left]), Heap[Current, NODE.right]));
  assert user_inv_readable(Heap, Current)[Current, NODE.left]; // type:access tag:attribute_readable line:157 cid:404 fid:81
  assert {:subsumption 0} (Heap[Current, NODE.left]) != (Void); // type:attached tag:left_consistent line:157
  assert user_inv_readable(Heap, Current)[Heap[Current, NODE.left], NODE.right]; // type:access tag:attribute_readable line:157 cid:404 fid:82
  assume (Heap[Heap[Current, NODE.left], NODE.right]) == (Current);
  assert user_inv_readable(Heap, Current)[Current, NODE.right]; // type:access tag:attribute_readable line:158 cid:404 fid:82
  assert {:subsumption 0} (Heap[Current, NODE.right]) != (Void); // type:attached tag:right_consistent line:158
  assert user_inv_readable(Heap, Current)[Heap[Current, NODE.right], NODE.left]; // type:access tag:attribute_readable line:158 cid:404 fid:81
  assume (Heap[Heap[Current, NODE.right], NODE.left]) == (Current);
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

procedure create.NODE.make(Current: ref);
  free requires attached_exact(Heap, Current, NODE); // info:type property for argument Current
  modifies Heap;
  ensures (Heap[Current, NODE.left]) == (Current); // type:post tag:singleton line:20
  requires (forall <T6> $f: Field T6 :: (($f) != (allocated)) ==> ((Heap[Current, $f]) == (Default($f))));
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.NODE.make(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.NODE.make(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts



implementation create.NODE.make(Current: ref)
{
  entry:
  assume {:captureState "create.NODE.make"} true;
  // /home/caf/temp/comcom/repo-dll/node.e:17
  // left := Current
  call update_heap(Current, NODE.left, Current); // line:17
  // /home/caf/temp/comcom/repo-dll/node.e:18
  // right := Current
  call update_heap(Current, NODE.right, Current); // line:18
  if (modify.NODE.make(Heap, Current)[Current, observers]) {
    call update_heap(Current, observers, NODE.observers.static(Heap, Current)); // default:observers line:21
  }
  if (modify.NODE.make(Heap, Current)[Current, subjects]) {
    call update_heap(Current, subjects, NODE.subjects.static(Heap, Current)); // default:subjects line:21
  }
  if (*) {
    assert (Heap[Current, NODE.left]) != (Void); // type:inv tag:left_exists line:21 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert (Heap[Current, NODE.right]) != (Void); // type:inv tag:right_exists line:21 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#Equal(Heap[Current, subjects], Set#Extended(Set#Singleton(Heap[Current, NODE.left]), Heap[Current, NODE.right])); // type:inv tag:subjects_structure line:21 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert Set#Equal(Heap[Current, observers], Set#Extended(Set#Singleton(Heap[Current, NODE.left]), Heap[Current, NODE.right])); // type:inv tag:observers_structure line:21 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert (Heap[Heap[Current, NODE.left], NODE.right]) == (Current); // type:inv tag:left_consistent line:21 cid:1 rid:55
    assume false;
  }
  if (*) {
    assert (Heap[Heap[Current, NODE.right], NODE.left]) == (Current); // type:inv tag:right_consistent line:21 cid:1 rid:55
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

procedure NODE.insert_right(Current: ref, n: ref);
  free requires attached_exact(Heap, Current, NODE); // info:type property for argument Current
  free requires detachable_exact(Heap, n, NODE); // info:type property for argument n
  modifies Heap;
  requires (n) != (Void); // type:attached tag:n_singleton line:46
  requires (Heap[n, NODE.left]) == (n); // type:pre tag:n_singleton line:46
  requires (Heap[Current, NODE.right]) != (Void); // type:attached tag:right_wrapped line:47
  requires is_wrapped(Heap, Heap[Current, NODE.right]); // type:pre tag:right_wrapped line:47
  ensures (Heap[Current, NODE.right]) == (n); // type:post tag:n_left_set line:69
  ensures (n) != (Void); // type:attached tag:n_right_set line:70
  ensures (Heap[n, NODE.right]) == (old(Heap)[Current, NODE.right]); // type:post tag:n_right_set line:70
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.NODE.insert_right(Heap, Current, n), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.NODE.insert_right(old(Heap), Current, n));
  free ensures HeapSucc(old(Heap), Heap);
  requires is_wrapped(Heap, Current); // type:pre tag:default_is_wrapped default:contracts
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts
  requires is_wrapped(Heap, n); // type:pre tag:arg_n_is_wrapped default:contracts
  ensures is_wrapped(Heap, n); // type:post tag:arg_n_is_wrapped default:contracts



function { :inline } variant.NODE.insert_right.1(heap: HeapType, current: ref, n: ref) returns (ref) {
  n
}

implementation NODE.insert_right(Current: ref, n: ref)
{
  var local1: ref where detachable_exact(Heap, local1, NODE);

  init_locals:
  local1 := Void;

  entry:
  assume {:captureState "NODE.insert_right"} true;
  // /home/caf/temp/comcom/repo-dll/node.e:52
  // r := right
  local1 := Heap[Current, NODE.right];
  // /home/caf/temp/comcom/repo-dll/node.e:53
  // unwrap_all ([Current, r, n])
  call unwrap_all(Current, Set#Extended(Set#Extended(Set#Singleton(Current), local1), n)); // line:53 cid:1 rid:59
  // /home/caf/temp/comcom/repo-dll/node.e:55
  // n.set_right (r)
  assert {:subsumption 0} (n) != (Void); // type:attached line:55
  call NODE.set_right(n, local1); // line:55 cid:404 rid:5408
  // /home/caf/temp/comcom/repo-dll/node.e:56
  // n.set_left (Current)
  assert {:subsumption 0} (n) != (Void); // type:attached line:56
  call NODE.set_left(n, Current); // line:56 cid:404 rid:5407
  // /home/caf/temp/comcom/repo-dll/node.e:58
  // r.set_left (n)
  assert {:subsumption 0} (local1) != (Void); // type:attached line:58
  call NODE.set_left(local1, n); // line:58 cid:404 rid:5407
  // /home/caf/temp/comcom/repo-dll/node.e:59
  // set_right (n)
  call NODE.set_right(Current, n); // line:59 cid:404 rid:5408
  // /home/caf/temp/comcom/repo-dll/node.e:61
  // n.set_subjects ([r, Current])
  assert {:subsumption 0} (n) != (Void); // type:attached line:61
  call update_heap(n, subjects, Set#Extended(Set#Singleton(local1), Current)); // line:61
  // /home/caf/temp/comcom/repo-dll/node.e:62
  // n.set_observers ([r, Current])
  assert {:subsumption 0} (n) != (Void); // type:attached line:62
  call update_heap(n, observers, Set#Extended(Set#Singleton(local1), Current)); // line:62
  // /home/caf/temp/comcom/repo-dll/node.e:63
  // set_subjects ([left, n])
  call update_heap(Current, subjects, Set#Extended(Set#Singleton(Heap[Current, NODE.left]), n)); // line:63
  // /home/caf/temp/comcom/repo-dll/node.e:64
  // set_observers ([left, n])
  call update_heap(Current, observers, Set#Extended(Set#Singleton(Heap[Current, NODE.left]), n)); // line:64
  // /home/caf/temp/comcom/repo-dll/node.e:65
  // r.set_subjects ([n, r.right])
  assert {:subsumption 0} (local1) != (Void); // type:attached line:65
  assert {:subsumption 0} (local1) != (Void); // type:attached line:65
  call update_heap(local1, subjects, Set#Extended(Set#Singleton(n), Heap[local1, NODE.right])); // line:65
  // /home/caf/temp/comcom/repo-dll/node.e:66
  // r.set_observers ([n, r.right])
  assert {:subsumption 0} (local1) != (Void); // type:attached line:66
  assert {:subsumption 0} (local1) != (Void); // type:attached line:66
  call update_heap(local1, observers, Set#Extended(Set#Singleton(n), Heap[local1, NODE.right])); // line:66
  // /home/caf/temp/comcom/repo-dll/node.e:67
  // wrap_all ([Current, r, n])
  call wrap_all(Current, Set#Extended(Set#Extended(Set#Singleton(Current), local1), n)); // line:67 cid:1 rid:56
}

procedure NODE.remove(Current: ref);
  free requires attached_exact(Heap, Current, NODE); // info:type property for argument Current
  modifies Heap;
  requires (Heap[Current, NODE.left]) != (Void); // type:attached tag:left_wrapped line:78
  requires is_wrapped(Heap, Heap[Current, NODE.left]); // type:pre tag:left_wrapped line:78
  requires (Heap[Current, NODE.right]) != (Void); // type:attached tag:right_wrapped line:79
  requires is_wrapped(Heap, Heap[Current, NODE.right]); // type:pre tag:right_wrapped line:79
  ensures (Heap[Current, NODE.right]) == (Current); // type:post tag:singleton line:102
  ensures (old(Heap)[Current, NODE.left]) != (Void); // type:attached tag:old_left_wrapped line:103
  ensures is_wrapped(Heap, old(Heap)[Current, NODE.left]); // type:post tag:old_left_wrapped line:103
  ensures (old(Heap)[Current, NODE.right]) != (Void); // type:attached tag:old_right_wrapped line:104
  ensures is_wrapped(Heap, old(Heap)[Current, NODE.right]); // type:post tag:old_right_wrapped line:104
  ensures (Heap[old(Heap)[Current, NODE.left], NODE.right]) == (old(Heap)[Current, NODE.right]); // type:post tag:neighbors_connected line:105
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.NODE.remove(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.NODE.remove(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);
  requires is_wrapped(Heap, Current); // type:pre tag:default_is_wrapped default:contracts
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts



function { :inline } variant.NODE.remove.1(heap: HeapType, current: ref) returns (int) {
  0
}

implementation NODE.remove(Current: ref)
{
  var local1: ref where detachable_exact(Heap, local1, NODE);
  var local2: ref where detachable_exact(Heap, local2, NODE);

  init_locals:
  local1 := Void;
  local2 := Void;

  entry:
  assume {:captureState "NODE.remove"} true;
  // /home/caf/temp/comcom/repo-dll/node.e:84
  // l := left
  local1 := Heap[Current, NODE.left];
  // /home/caf/temp/comcom/repo-dll/node.e:85
  // r := right
  local2 := Heap[Current, NODE.right];
  // /home/caf/temp/comcom/repo-dll/node.e:86
  // unwrap_all ([Current, l, r])
  call unwrap_all(Current, Set#Extended(Set#Extended(Set#Singleton(Current), local1), local2)); // line:86 cid:1 rid:59
  // /home/caf/temp/comcom/repo-dll/node.e:88
  // set_left (Current)
  call NODE.set_left(Current, Current); // line:88 cid:404 rid:5407
  // /home/caf/temp/comcom/repo-dll/node.e:89
  // set_right (Current)
  call NODE.set_right(Current, Current); // line:89 cid:404 rid:5408
  // /home/caf/temp/comcom/repo-dll/node.e:91
  // l.set_right (r)
  assert {:subsumption 0} (local1) != (Void); // type:attached line:91
  call NODE.set_right(local1, local2); // line:91 cid:404 rid:5408
  // /home/caf/temp/comcom/repo-dll/node.e:92
  // r.set_left (l)
  assert {:subsumption 0} (local2) != (Void); // type:attached line:92
  call NODE.set_left(local2, local1); // line:92 cid:404 rid:5407
  // /home/caf/temp/comcom/repo-dll/node.e:94
  // set_subjects ([Current])
  call update_heap(Current, subjects, Set#Singleton(Current)); // line:94
  // /home/caf/temp/comcom/repo-dll/node.e:95
  // set_observers ([Current])
  call update_heap(Current, observers, Set#Singleton(Current)); // line:95
  // /home/caf/temp/comcom/repo-dll/node.e:96
  // l.set_subjects ([l.left, r])
  assert {:subsumption 0} (local1) != (Void); // type:attached line:96
  assert {:subsumption 0} (local1) != (Void); // type:attached line:96
  call update_heap(local1, subjects, Set#Extended(Set#Singleton(Heap[local1, NODE.left]), local2)); // line:96
  // /home/caf/temp/comcom/repo-dll/node.e:97
  // l.set_observers ([l.left, r])
  assert {:subsumption 0} (local1) != (Void); // type:attached line:97
  assert {:subsumption 0} (local1) != (Void); // type:attached line:97
  call update_heap(local1, observers, Set#Extended(Set#Singleton(Heap[local1, NODE.left]), local2)); // line:97
  // /home/caf/temp/comcom/repo-dll/node.e:98
  // r.set_subjects ([l, r.right])
  assert {:subsumption 0} (local2) != (Void); // type:attached line:98
  assert {:subsumption 0} (local2) != (Void); // type:attached line:98
  call update_heap(local2, subjects, Set#Extended(Set#Singleton(local1), Heap[local2, NODE.right])); // line:98
  // /home/caf/temp/comcom/repo-dll/node.e:99
  // r.set_observers ([l, r.right])
  assert {:subsumption 0} (local2) != (Void); // type:attached line:99
  assert {:subsumption 0} (local2) != (Void); // type:attached line:99
  call update_heap(local2, observers, Set#Extended(Set#Singleton(local1), Heap[local2, NODE.right])); // line:99
  // /home/caf/temp/comcom/repo-dll/node.e:100
  // wrap_all ([Current, l, r])
  call wrap_all(Current, Set#Extended(Set#Extended(Set#Singleton(Current), local1), local2)); // line:100 cid:1 rid:56
}

procedure NODE.set_left(Current: ref, n: ref);
  free requires attached_exact(Heap, Current, NODE); // info:type property for argument Current
  free requires detachable_exact(Heap, n, NODE); // info:type property for argument n
  modifies Heap;
  requires is_open(Heap, Current); // type:pre tag:open line:113
  requires (Heap[Current, NODE.left]) != (Void); // type:attached tag:left_open line:114
  requires is_open(Heap, Heap[Current, NODE.left]); // type:pre tag:left_open line:114
  ensures (Heap[Current, NODE.left]) == (n); // type:post line:119
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.NODE.set_left(Heap, Current, n), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.NODE.set_left(old(Heap), Current, n));
  free ensures HeapSucc(old(Heap), Heap);



function { :inline } variant.NODE.set_left.1(heap: HeapType, current: ref, n: ref) returns (ref) {
  n
}

implementation NODE.set_left(Current: ref, n: ref)
{
  entry:
  assume {:captureState "NODE.set_left"} true;
  // /home/caf/temp/comcom/repo-dll/node.e:117
  // left := n -- preserves `right'
  call update_heap(Current, NODE.left, n); // line:117
}

procedure NODE.set_right(Current: ref, n: ref);
  free requires attached_exact(Heap, Current, NODE); // info:type property for argument Current
  free requires detachable_exact(Heap, n, NODE); // info:type property for argument n
  modifies Heap;
  requires is_open(Heap, Current); // type:pre tag:open line:125
  requires (Heap[Current, NODE.right]) != (Void); // type:attached tag:right_open line:126
  requires is_open(Heap, Heap[Current, NODE.right]); // type:pre tag:right_open line:126
  ensures (Heap[Current, NODE.right]) == (n); // type:post line:131
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.NODE.set_right(Heap, Current, n), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.NODE.set_right(old(Heap), Current, n));
  free ensures HeapSucc(old(Heap), Heap);



function { :inline } variant.NODE.set_right.1(heap: HeapType, current: ref, n: ref) returns (ref) {
  n
}

implementation NODE.set_right(Current: ref, n: ref)
{
  entry:
  assume {:captureState "NODE.set_right"} true;
  // /home/caf/temp/comcom/repo-dll/node.e:129
  // right := n -- preserves `left'
  call update_heap(Current, NODE.right, n); // line:129
}

procedure NODE.not_left(Current: ref, new_left: ref, o: ref) returns (Result: bool where true);
  free requires attached_exact(Heap, Current, NODE); // info:type property for argument Current
  free requires detachable_exact(Heap, new_left, NODE); // info:type property for argument new_left
  free requires Heap[o, allocated]; // info:type property for argument o
  modifies Heap;
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.NODE.not_left(Heap, Current, new_left, o), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.NODE.not_left(old(Heap), Current, new_left, o));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.NODE.not_left(Heap, Current, new_left, o), readable);



function fun.NODE.not_left(heap: HeapType, current: ref, new_left: ref, o: ref) returns (bool);

function fun0.NODE.not_left(heap: HeapType, current: ref, new_left: ref, o: ref) returns (bool);

axiom ((forall heap: HeapType, current: ref, new_left: ref, o: ref :: { fun.NODE.not_left(heap, current, new_left, o) } { trigger.fun.NODE.not_left(heap, current, new_left, o) } (pre.fun.NODE.not_left(heap, current, new_left, o)) ==> ((fun.NODE.not_left(heap, current, new_left, o)) == ((o) != (heap[current, NODE.left])))));

axiom ((forall heap: HeapType, current: ref, new_left: ref, o: ref :: { fun.NODE.not_left(heap, current, new_left, o) } (fun.NODE.not_left(heap, current, new_left, o)) == (fun0.NODE.not_left(heap, current, new_left, o))));

axiom ((forall h: HeapType, h': HeapType, current: ref, new_left: ref, o: ref :: { HeapSucc(h, h'), fun0.NODE.not_left(h, current, new_left, o), fun0.NODE.not_left(h', current, new_left, o) } ((HeapSucc(h, h')) && (pre.fun.NODE.not_left(h, current, new_left, o)) && (pre.fun.NODE.not_left(h', current, new_left, o)) && (same_inside(h, h', read.fun.NODE.not_left(h, current, new_left, o)))) ==> ((fun0.NODE.not_left(h, current, new_left, o)) == (fun0.NODE.not_left(h', current, new_left, o)))));

function { :inline } variant.NODE.not_left.1(heap: HeapType, current: ref, new_left: ref, o: ref) returns (ref) {
  new_left
}

function { :inline } variant.NODE.not_left.2(heap: HeapType, current: ref, new_left: ref, o: ref) returns (ref) {
  o
}

implementation NODE.not_left(Current: ref, new_left: ref, o: ref) returns (Result: bool)
{

  init_locals:
  Result := false;

  entry:
  assume {:captureState "NODE.not_left"} true;
  // /home/caf/temp/comcom/repo-dll/node.e:141
  // Result := o /= left
  assert readable[Current, NODE.left]; // type:access tag:attribute_readable line:141 cid:404 fid:81
  Result := (o) != (Heap[Current, NODE.left]);
}

procedure NODE.not_right(Current: ref, new_right: ref, o: ref) returns (Result: bool where true);
  free requires attached_exact(Heap, Current, NODE); // info:type property for argument Current
  free requires detachable_exact(Heap, new_right, NODE); // info:type property for argument new_right
  free requires Heap[o, allocated]; // info:type property for argument o
  modifies Heap;
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.NODE.not_right(Heap, Current, new_right, o), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.NODE.not_right(old(Heap), Current, new_right, o));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.NODE.not_right(Heap, Current, new_right, o), readable);



function fun.NODE.not_right(heap: HeapType, current: ref, new_right: ref, o: ref) returns (bool);

function fun0.NODE.not_right(heap: HeapType, current: ref, new_right: ref, o: ref) returns (bool);

axiom ((forall heap: HeapType, current: ref, new_right: ref, o: ref :: { fun.NODE.not_right(heap, current, new_right, o) } { trigger.fun.NODE.not_right(heap, current, new_right, o) } (pre.fun.NODE.not_right(heap, current, new_right, o)) ==> ((fun.NODE.not_right(heap, current, new_right, o)) == ((o) != (heap[current, NODE.right])))));

axiom ((forall heap: HeapType, current: ref, new_right: ref, o: ref :: { fun.NODE.not_right(heap, current, new_right, o) } (fun.NODE.not_right(heap, current, new_right, o)) == (fun0.NODE.not_right(heap, current, new_right, o))));

axiom ((forall h: HeapType, h': HeapType, current: ref, new_right: ref, o: ref :: { HeapSucc(h, h'), fun0.NODE.not_right(h, current, new_right, o), fun0.NODE.not_right(h', current, new_right, o) } ((HeapSucc(h, h')) && (pre.fun.NODE.not_right(h, current, new_right, o)) && (pre.fun.NODE.not_right(h', current, new_right, o)) && (same_inside(h, h', read.fun.NODE.not_right(h, current, new_right, o)))) ==> ((fun0.NODE.not_right(h, current, new_right, o)) == (fun0.NODE.not_right(h', current, new_right, o)))));

function { :inline } variant.NODE.not_right.1(heap: HeapType, current: ref, new_right: ref, o: ref) returns (ref) {
  new_right
}

function { :inline } variant.NODE.not_right.2(heap: HeapType, current: ref, new_right: ref, o: ref) returns (ref) {
  o
}

implementation NODE.not_right(Current: ref, new_right: ref, o: ref) returns (Result: bool)
{

  init_locals:
  Result := false;

  entry:
  assume {:captureState "NODE.not_right"} true;
  // /home/caf/temp/comcom/repo-dll/node.e:149
  // Result := o /= right
  assert readable[Current, NODE.right]; // type:access tag:attribute_readable line:149 cid:404 fid:82
  Result := (o) != (Heap[Current, NODE.right]);
}

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, owns, v, o) } (attached_exact(heap, current, ANY)) ==> ((guard(heap, current, owns, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, subjects, v, o) } (attached_exact(heap, current, ANY)) ==> ((guard(heap, current, subjects, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached_exact(heap, current, ANY)) ==> ((guard(heap, current, observers, v, o)) <==> (fun.ANY.in_observers(heap, current, v, o)))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached(heap, current, ANY)) ==> ((guard(heap, current, observers, v, o)) ==> (fun.ANY.in_observers(heap, current, v, o)))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, owns, v, o) } (attached_exact(heap, current, CLIENT)) ==> ((guard(heap, current, owns, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, subjects, v, o) } (attached_exact(heap, current, CLIENT)) ==> ((guard(heap, current, subjects, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached_exact(heap, current, CLIENT)) ==> ((guard(heap, current, observers, v, o)) <==> (fun.CLIENT.in_observers(heap, current, v, o)))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached(heap, current, CLIENT)) ==> ((guard(heap, current, observers, v, o)) ==> (fun.CLIENT.in_observers(heap, current, v, o)))));

function modify.CLIENT.default_create(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T7> $o: ref, $f: Field T7 :: { modify.CLIENT.default_create(heap, current)[$o, $f] } (modify.CLIENT.default_create(heap, current)[$o, $f]) <==> (($o) == (current))))));

function modify.CLIENT.test_dll(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T8> $o: ref, $f: Field T8 :: { modify.CLIENT.test_dll(heap, current)[$o, $f] } (modify.CLIENT.test_dll(heap, current)[$o, $f]) <==> (($o) == (current))))));

const NODE.left: Field (ref);

axiom ((FieldId(NODE.left, NODE)) == (81));

axiom ((forall heap: HeapType, o: ref :: { heap[o, NODE.left] } ((IsHeap(heap)) && (attached(heap, o, NODE))) ==> (detachable_exact(heap, heap[o, NODE.left], NODE))));

axiom ((forall heap: HeapType, current: ref, v: ref, o: ref :: { guard(heap, current, NODE.left, v, o) } (attached_exact(heap, current, NODE)) ==> ((guard(heap, current, NODE.left, v, o)) <==> (fun.NODE.not_left(heap, current, v, o)))));

axiom ((forall heap: HeapType, current: ref, v: ref, o: ref :: { guard(heap, current, NODE.left, v, o) } (attached(heap, current, NODE)) ==> ((guard(heap, current, NODE.left, v, o)) ==> (fun.NODE.not_left(heap, current, v, o)))));

const NODE.right: Field (ref);

axiom ((FieldId(NODE.right, NODE)) == (82));

axiom ((forall heap: HeapType, o: ref :: { heap[o, NODE.right] } ((IsHeap(heap)) && (attached(heap, o, NODE))) ==> (detachable_exact(heap, heap[o, NODE.right], NODE))));

axiom ((forall heap: HeapType, current: ref, v: ref, o: ref :: { guard(heap, current, NODE.right, v, o) } (attached_exact(heap, current, NODE)) ==> ((guard(heap, current, NODE.right, v, o)) <==> (fun.NODE.not_right(heap, current, v, o)))));

axiom ((forall heap: HeapType, current: ref, v: ref, o: ref :: { guard(heap, current, NODE.right, v, o) } (attached(heap, current, NODE)) ==> ((guard(heap, current, NODE.right, v, o)) ==> (fun.NODE.not_right(heap, current, v, o)))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, owns, v, o) } (attached_exact(heap, current, NODE)) ==> ((guard(heap, current, owns, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, subjects, v, o) } (attached_exact(heap, current, NODE)) ==> ((guard(heap, current, subjects, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached_exact(heap, current, NODE)) ==> ((guard(heap, current, observers, v, o)) <==> (fun.NODE.in_observers(heap, current, v, o)))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached(heap, current, NODE)) ==> ((guard(heap, current, observers, v, o)) ==> (fun.NODE.in_observers(heap, current, v, o)))));

function modify.NODE.make(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T9> $o: ref, $f: Field T9 :: { modify.NODE.make(heap, current)[$o, $f] } (modify.NODE.make(heap, current)[$o, $f]) <==> (($o) == (current))))));

function modify.NODE.insert_right(heap: HeapType, current: ref, n: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, n: ref :: (IsHeap(heap)) ==> ((forall <T10> $o: ref, $f: Field T10 :: { modify.NODE.insert_right(heap, current, n)[$o, $f] } (modify.NODE.insert_right(heap, current, n)[$o, $f]) <==> ((($o) == (current)) || (($o) == (heap[current, NODE.right])) || (($o) == (n)))))));

function modify.NODE.remove(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T11> $o: ref, $f: Field T11 :: { modify.NODE.remove(heap, current)[$o, $f] } (modify.NODE.remove(heap, current)[$o, $f]) <==> ((($o) == (current)) || (($o) == (heap[current, NODE.left])) || (($o) == (heap[current, NODE.right])))))));

function modify.NODE.set_left(heap: HeapType, current: ref, n: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, n: ref :: (IsHeap(heap)) ==> ((forall <T12> $o: ref, $f: Field T12 :: { modify.NODE.set_left(heap, current, n)[$o, $f] } (modify.NODE.set_left(heap, current, n)[$o, $f]) <==> ((($o) == (current)) && (($f) == (NODE.left)))))));

function modify.NODE.set_right(heap: HeapType, current: ref, n: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, n: ref :: (IsHeap(heap)) ==> ((forall <T13> $o: ref, $f: Field T13 :: { modify.NODE.set_right(heap, current, n)[$o, $f] } (modify.NODE.set_right(heap, current, n)[$o, $f]) <==> ((($o) == (current)) && (($f) == (NODE.right)))))));

function modify.NODE.not_left(heap: HeapType, current: ref, new_left: ref, o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_left: ref, o: ref :: (IsHeap(heap)) ==> ((forall <T14> $o: ref, $f: Field T14 :: { modify.NODE.not_left(heap, current, new_left, o)[$o, $f] } (modify.NODE.not_left(heap, current, new_left, o)[$o, $f]) <==> (false)))));

function read.fun.NODE.not_left(heap: HeapType, current: ref, new_left: ref, o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_left: ref, o: ref :: (IsHeap(heap)) ==> ((forall <T15> $o: ref, $f: Field T15 :: { read.fun.NODE.not_left(heap, current, new_left, o)[$o, $f] } (read.fun.NODE.not_left(heap, current, new_left, o)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.NODE.not_left(heap: HeapType, current: ref, new_left: ref, o: ref) returns (bool) {
  true
}

function trigger.fun.NODE.not_left(heap: HeapType, current: ref, new_left: ref, o: ref) returns (bool);

function modify.NODE.not_right(heap: HeapType, current: ref, new_right: ref, o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_right: ref, o: ref :: (IsHeap(heap)) ==> ((forall <T16> $o: ref, $f: Field T16 :: { modify.NODE.not_right(heap, current, new_right, o)[$o, $f] } (modify.NODE.not_right(heap, current, new_right, o)[$o, $f]) <==> (false)))));

function read.fun.NODE.not_right(heap: HeapType, current: ref, new_right: ref, o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_right: ref, o: ref :: (IsHeap(heap)) ==> ((forall <T17> $o: ref, $f: Field T17 :: { read.fun.NODE.not_right(heap, current, new_right, o)[$o, $f] } (read.fun.NODE.not_right(heap, current, new_right, o)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.NODE.not_right(heap: HeapType, current: ref, new_right: ref, o: ref) returns (bool) {
  true
}

function trigger.fun.NODE.not_right(heap: HeapType, current: ref, new_right: ref, o: ref) returns (bool);

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

procedure NODE.in_observers(Current: ref, new_observers: Set (ref), o: ref) returns (Result: bool where true);
  free requires attached_exact(Heap, Current, NODE); // info:type property for argument Current
  free requires Set#ItemsType(Heap, new_observers, ANY); // info:type property for argument new_observers
  free requires Heap[o, allocated]; // info:type property for argument o
  modifies Heap;
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.NODE.in_observers(Heap, Current, new_observers, o), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.NODE.in_observers(old(Heap), Current, new_observers, o));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.NODE.in_observers(Heap, Current, new_observers, o), readable);



function fun.NODE.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function fun0.NODE.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.NODE.in_observers(heap, current, new_observers, o) } { trigger.fun.NODE.in_observers(heap, current, new_observers, o) } (pre.fun.NODE.in_observers(heap, current, new_observers, o)) ==> ((fun.NODE.in_observers(heap, current, new_observers, o)) == (new_observers[o]))));

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.NODE.in_observers(heap, current, new_observers, o) } (fun.NODE.in_observers(heap, current, new_observers, o)) == (fun0.NODE.in_observers(heap, current, new_observers, o))));

axiom ((forall h: HeapType, h': HeapType, current: ref, new_observers: Set (ref), o: ref :: { HeapSucc(h, h'), fun0.NODE.in_observers(h, current, new_observers, o), fun0.NODE.in_observers(h', current, new_observers, o) } ((HeapSucc(h, h')) && (pre.fun.NODE.in_observers(h, current, new_observers, o)) && (pre.fun.NODE.in_observers(h', current, new_observers, o)) && (same_inside(h, h', read.fun.NODE.in_observers(h, current, new_observers, o)))) ==> ((fun0.NODE.in_observers(h, current, new_observers, o)) == (fun0.NODE.in_observers(h', current, new_observers, o)))));

function modify.ANY.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T18> $o: ref, $f: Field T18 :: { modify.ANY.in_observers(heap, current, new_observers, o)[$o, $f] } (modify.ANY.in_observers(heap, current, new_observers, o)[$o, $f]) <==> (false)))));

function read.fun.ANY.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T19> $o: ref, $f: Field T19 :: { read.fun.ANY.in_observers(heap, current, new_observers, o)[$o, $f] } (read.fun.ANY.in_observers(heap, current, new_observers, o)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.ANY.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool) {
  true
}

function trigger.fun.ANY.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function modify.CLIENT.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T20> $o: ref, $f: Field T20 :: { modify.CLIENT.in_observers(heap, current, new_observers, o)[$o, $f] } (modify.CLIENT.in_observers(heap, current, new_observers, o)[$o, $f]) <==> (false)))));

function read.fun.CLIENT.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T21> $o: ref, $f: Field T21 :: { read.fun.CLIENT.in_observers(heap, current, new_observers, o)[$o, $f] } (read.fun.CLIENT.in_observers(heap, current, new_observers, o)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.CLIENT.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool) {
  true
}

function trigger.fun.CLIENT.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function modify.NODE.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T22> $o: ref, $f: Field T22 :: { modify.NODE.in_observers(heap, current, new_observers, o)[$o, $f] } (modify.NODE.in_observers(heap, current, new_observers, o)[$o, $f]) <==> (false)))));

function read.fun.NODE.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T23> $o: ref, $f: Field T23 :: { read.fun.NODE.in_observers(heap, current, new_observers, o)[$o, $f] } (read.fun.NODE.in_observers(heap, current, new_observers, o)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.NODE.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool) {
  true
}

function trigger.fun.NODE.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);
