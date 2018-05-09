// Dafny 2.0.0.00922 technical preview 0
// Command Line Options: /compile:0 /noVerify /print:BreadthFirstSearch.bpl BreadthFirstSearch.dfy

const $$Language$Dafny: bool;

axiom $$Language$Dafny;

type Ty;

type Bv0 = int;

const unique TBool: Ty;

const unique TChar: Ty;

const unique TInt: Ty;

const unique TReal: Ty;

const unique TORDINAL: Ty;

function TBitvector(int) : Ty;

function TSet(Ty) : Ty;

function TISet(Ty) : Ty;

function TMultiSet(Ty) : Ty;

function TSeq(Ty) : Ty;

function TMap(Ty, Ty) : Ty;

function TIMap(Ty, Ty) : Ty;

function Inv0_TBitvector(Ty) : int;

axiom (forall w: int :: { TBitvector(w) } Inv0_TBitvector(TBitvector(w)) == w);

function Inv0_TSet(Ty) : Ty;

axiom (forall t: Ty :: { TSet(t) } Inv0_TSet(TSet(t)) == t);

function Inv0_TISet(Ty) : Ty;

axiom (forall t: Ty :: { TISet(t) } Inv0_TISet(TISet(t)) == t);

function Inv0_TSeq(Ty) : Ty;

axiom (forall t: Ty :: { TSeq(t) } Inv0_TSeq(TSeq(t)) == t);

function Inv0_TMultiSet(Ty) : Ty;

axiom (forall t: Ty :: { TMultiSet(t) } Inv0_TMultiSet(TMultiSet(t)) == t);

function Inv0_TMap(Ty) : Ty;

function Inv1_TMap(Ty) : Ty;

axiom (forall t: Ty, u: Ty :: { TMap(t, u) } Inv0_TMap(TMap(t, u)) == t);

axiom (forall t: Ty, u: Ty :: { TMap(t, u) } Inv1_TMap(TMap(t, u)) == u);

function Inv0_TIMap(Ty) : Ty;

function Inv1_TIMap(Ty) : Ty;

axiom (forall t: Ty, u: Ty :: { TIMap(t, u) } Inv0_TIMap(TIMap(t, u)) == t);

axiom (forall t: Ty, u: Ty :: { TIMap(t, u) } Inv1_TIMap(TIMap(t, u)) == u);

type TyTag;

function Tag(Ty) : TyTag;

const unique TagBool: TyTag;

const unique TagChar: TyTag;

const unique TagInt: TyTag;

const unique TagReal: TyTag;

const unique TagORDINAL: TyTag;

const unique TagSet: TyTag;

const unique TagISet: TyTag;

const unique TagMultiSet: TyTag;

const unique TagSeq: TyTag;

const unique TagMap: TyTag;

const unique TagIMap: TyTag;

const unique TagClass: TyTag;

axiom Tag(TBool) == TagBool;

axiom Tag(TChar) == TagChar;

axiom Tag(TInt) == TagInt;

axiom Tag(TReal) == TagReal;

axiom Tag(TORDINAL) == TagORDINAL;

axiom (forall t: Ty :: { TSet(t) } Tag(TSet(t)) == TagSet);

axiom (forall t: Ty :: { TISet(t) } Tag(TISet(t)) == TagISet);

axiom (forall t: Ty :: { TMultiSet(t) } Tag(TMultiSet(t)) == TagMultiSet);

axiom (forall t: Ty :: { TSeq(t) } Tag(TSeq(t)) == TagSeq);

axiom (forall t: Ty, u: Ty :: { TMap(t, u) } Tag(TMap(t, u)) == TagMap);

axiom (forall t: Ty, u: Ty :: { TIMap(t, u) } Tag(TIMap(t, u)) == TagIMap);

function {:identity} LitInt(x: int) : int;

axiom (forall x: int :: {:identity} { LitInt(x): int } LitInt(x): int == x);

axiom (forall x: int :: { $Box(LitInt(x)) } $Box(LitInt(x)) == Lit($Box(x)));

// function {:identity} LitReal(x: real) : real; // 'real' unsupported

// axiom (forall x: real :: {:identity} { LitReal(x): real } LitReal(x): real == x); // 'real' unsupported

// axiom (forall x: real :: { $Box(LitReal(x)) } $Box(LitReal(x)) == Lit($Box(x))); // 'real' unsupported

function {:identity} Lit<T>(x: T) : T;

axiom (forall<T> x: T :: {:identity} { Lit(x): T } Lit(x): T == x);

axiom (forall<T> x: T :: { $Box(Lit(x)) } $Box(Lit(x)) == Lit($Box(x)));

type char;

function char#FromInt(int) : char;

function char#ToInt(char) : int;

axiom (forall ch: char :: { char#ToInt(ch) } char#FromInt(char#ToInt(ch)) == ch);

axiom (forall n: int ::
  { char#FromInt(n) }
  0 <= n && n < 65536 ==> char#ToInt(char#FromInt(n)) == n);

type ref;

const null: ref;

const unique NoTraitAtAll: ClassName;

function TraitParent(ClassName) : ClassName;

type Box;

const $ArbitraryBoxValue: Box;

function $Box<T>(T) : Box;

function $Unbox<T>(Box) : T;

axiom (forall<T> x: T :: { $Box(x) } $Unbox($Box(x)) == x);

axiom (forall bx: Box ::
  { $IsBox(bx, TInt) }
  $IsBox(bx, TInt) ==> $Box($Unbox(bx): int) == bx && $Is($Unbox(bx): int, TInt));

// axiom (forall bx: Box :: // 'real' unsupported
//   { $IsBox(bx, TReal) } // 'real' unsupported
//   $IsBox(bx, TReal) // 'real' unsupported
//      ==> $Box($Unbox(bx): real) == bx && $Is($Unbox(bx): real, TReal)); // 'real' unsupported

axiom (forall bx: Box ::
  { $IsBox(bx, TBool) }
  $IsBox(bx, TBool)
     ==> $Box($Unbox(bx): bool) == bx && $Is($Unbox(bx): bool, TBool));

axiom (forall bx: Box ::
  { $IsBox(bx, TChar) }
  $IsBox(bx, TChar)
     ==> $Box($Unbox(bx): char) == bx && $Is($Unbox(bx): char, TChar));

axiom (forall bx: Box, t: Ty ::
  { $IsBox(bx, TSet(t)) }
  $IsBox(bx, TSet(t))
     ==> $Box($Unbox(bx): Set Box) == bx && $Is($Unbox(bx): Set Box, TSet(t)));

axiom (forall bx: Box, t: Ty ::
  { $IsBox(bx, TISet(t)) }
  $IsBox(bx, TISet(t))
     ==> $Box($Unbox(bx): ISet Box) == bx && $Is($Unbox(bx): ISet Box, TISet(t)));

axiom (forall bx: Box, t: Ty ::
  { $IsBox(bx, TMultiSet(t)) }
  $IsBox(bx, TMultiSet(t))
     ==> $Box($Unbox(bx): MultiSet Box) == bx
       && $Is($Unbox(bx): MultiSet Box, TMultiSet(t)));

axiom (forall bx: Box, t: Ty ::
  { $IsBox(bx, TSeq(t)) }
  $IsBox(bx, TSeq(t))
     ==> $Box($Unbox(bx): Seq Box) == bx && $Is($Unbox(bx): Seq Box, TSeq(t)));

axiom (forall bx: Box, s: Ty, t: Ty ::
  { $IsBox(bx, TMap(s, t)) }
  $IsBox(bx, TMap(s, t))
     ==> $Box($Unbox(bx): Map Box Box) == bx && $Is($Unbox(bx): Map Box Box, TMap(s, t)));

axiom (forall bx: Box, s: Ty, t: Ty ::
  { $IsBox(bx, TIMap(s, t)) }
  $IsBox(bx, TIMap(s, t))
     ==> $Box($Unbox(bx): IMap Box Box) == bx
       && $Is($Unbox(bx): IMap Box Box, TIMap(s, t)));

axiom (forall<T> v: T, t: Ty ::
  { $IsBox($Box(v), t) }
  $IsBox($Box(v), t) <==> $Is(v, t));

axiom (forall<T> v: T, t: Ty, h: Heap ::
  { $IsAllocBox($Box(v), t, h) }
  $IsAllocBox($Box(v), t, h) <==> $IsAlloc(v, t, h));

function $Is<T>(T, Ty) : bool;

function $IsAlloc<T>(T, Ty, Heap) : bool;

function $IsBox<T>(T, Ty) : bool;

function $IsAllocBox<T>(T, Ty, Heap) : bool;

axiom (forall v: int :: { $Is(v, TInt) } $Is(v, TInt));

// axiom (forall v: real :: { $Is(v, TReal) } $Is(v, TReal)); // 'real' unsupported

axiom (forall v: bool :: { $Is(v, TBool) } $Is(v, TBool));

axiom (forall v: char :: { $Is(v, TChar) } $Is(v, TChar));

axiom (forall v: ORDINAL :: { $Is(v, TORDINAL) } $Is(v, TORDINAL));

axiom (forall h: Heap, v: int :: { $IsAlloc(v, TInt, h) } $IsAlloc(v, TInt, h));

// axiom (forall h: Heap, v: real :: { $IsAlloc(v, TReal, h) } $IsAlloc(v, TReal, h)); // 'real' unsupported

axiom (forall h: Heap, v: bool :: { $IsAlloc(v, TBool, h) } $IsAlloc(v, TBool, h));

axiom (forall h: Heap, v: char :: { $IsAlloc(v, TChar, h) } $IsAlloc(v, TChar, h));

axiom (forall h: Heap, v: ORDINAL ::
  { $IsAlloc(v, TORDINAL, h) }
  $IsAlloc(v, TORDINAL, h));

axiom (forall v: Set Box, t0: Ty ::
  { $Is(v, TSet(t0)) }
  $Is(v, TSet(t0)) <==> (forall bx: Box :: { v[bx] } v[bx] ==> $IsBox(bx, t0)));

axiom (forall v: ISet Box, t0: Ty ::
  { $Is(v, TISet(t0)) }
  $Is(v, TISet(t0)) <==> (forall bx: Box :: { v[bx] } v[bx] ==> $IsBox(bx, t0)));

axiom (forall v: MultiSet Box, t0: Ty ::
  { $Is(v, TMultiSet(t0)) }
  $Is(v, TMultiSet(t0))
     <==> (forall bx: Box :: { v[bx] } 0 < v[bx] ==> $IsBox(bx, t0)));

axiom (forall v: MultiSet Box, t0: Ty ::
  { $Is(v, TMultiSet(t0)) }
  $Is(v, TMultiSet(t0)) ==> $IsGoodMultiSet(v));

axiom (forall v: Seq Box, t0: Ty ::
  { $Is(v, TSeq(t0)) }
  $Is(v, TSeq(t0))
     <==> (forall i: int ::
      { Seq#Index(v, i) }
      0 <= i && i < Seq#Length(v) ==> $IsBox(Seq#Index(v, i), t0)));

axiom (forall v: Set Box, t0: Ty, h: Heap ::
  { $IsAlloc(v, TSet(t0), h) }
  $IsAlloc(v, TSet(t0), h)
     <==> (forall bx: Box :: { v[bx] } v[bx] ==> $IsAllocBox(bx, t0, h)));

axiom (forall v: ISet Box, t0: Ty, h: Heap ::
  { $IsAlloc(v, TISet(t0), h) }
  $IsAlloc(v, TISet(t0), h)
     <==> (forall bx: Box :: { v[bx] } v[bx] ==> $IsAllocBox(bx, t0, h)));

axiom (forall v: MultiSet Box, t0: Ty, h: Heap ::
  { $IsAlloc(v, TMultiSet(t0), h) }
  $IsAlloc(v, TMultiSet(t0), h)
     <==> (forall bx: Box :: { v[bx] } 0 < v[bx] ==> $IsAllocBox(bx, t0, h)));

axiom (forall v: Seq Box, t0: Ty, h: Heap ::
  { $IsAlloc(v, TSeq(t0), h) }
  $IsAlloc(v, TSeq(t0), h)
     <==> (forall i: int ::
      { Seq#Index(v, i) }
      0 <= i && i < Seq#Length(v) ==> $IsAllocBox(Seq#Index(v, i), t0, h)));

axiom (forall v: Map Box Box, t0: Ty, t1: Ty ::
  { $Is(v, TMap(t0, t1)) }
  $Is(v, TMap(t0, t1))
     <==> (forall bx: Box ::
      { Map#Elements(v)[bx] } { Map#Domain(v)[bx] }
      Map#Domain(v)[bx] ==> $IsBox(Map#Elements(v)[bx], t1) && $IsBox(bx, t0)));

axiom (forall v: Map Box Box, t0: Ty, t1: Ty, h: Heap ::
  { $IsAlloc(v, TMap(t0, t1), h) }
  $IsAlloc(v, TMap(t0, t1), h)
     <==> (forall bx: Box ::
      { Map#Elements(v)[bx] } { Map#Domain(v)[bx] }
      Map#Domain(v)[bx]
         ==> $IsAllocBox(Map#Elements(v)[bx], t1, h) && $IsAllocBox(bx, t0, h)));

axiom (forall v: IMap Box Box, t0: Ty, t1: Ty ::
  { $Is(v, TIMap(t0, t1)) }
  $Is(v, TIMap(t0, t1))
     <==> (forall bx: Box ::
      { IMap#Elements(v)[bx] } { IMap#Domain(v)[bx] }
      IMap#Domain(v)[bx] ==> $IsBox(IMap#Elements(v)[bx], t1) && $IsBox(bx, t0)));

axiom (forall v: IMap Box Box, t0: Ty, t1: Ty, h: Heap ::
  { $IsAlloc(v, TIMap(t0, t1), h) }
  $IsAlloc(v, TIMap(t0, t1), h)
     <==> (forall bx: Box ::
      { IMap#Elements(v)[bx] } { IMap#Domain(v)[bx] }
      IMap#Domain(v)[bx]
         ==> $IsAllocBox(IMap#Elements(v)[bx], t1, h) && $IsAllocBox(bx, t0, h)));

type ClassName;

const unique class._System.int: ClassName;

const unique class._System.bool: ClassName;

const unique class._System.set: ClassName;

const unique class._System.seq: ClassName;

const unique class._System.multiset: ClassName;

function Tclass._System.object() : Ty;

function dtype(ref) : Ty;

function TypeTuple(a: ClassName, b: ClassName) : ClassName;

function TypeTupleCar(ClassName) : ClassName;

function TypeTupleCdr(ClassName) : ClassName;

axiom (forall a: ClassName, b: ClassName ::
  { TypeTuple(a, b) }
  TypeTupleCar(TypeTuple(a, b)) == a && TypeTupleCdr(TypeTuple(a, b)) == b);

type HandleType;

function SetRef_to_SetBox(s: [ref]bool) : Set Box;

axiom (forall s: [ref]bool, bx: Box ::
  { SetRef_to_SetBox(s)[bx] }
  SetRef_to_SetBox(s)[bx] == s[$Unbox(bx): ref]);

axiom (forall s: [ref]bool ::
  { SetRef_to_SetBox(s) }
  $Is(SetRef_to_SetBox(s), TSet(Tclass._System.object())));

type DatatypeType;

type DtCtorId;

function DatatypeCtorId(DatatypeType) : DtCtorId;

function DtRank(DatatypeType) : int;

function BoxRank(Box) : int;

axiom (forall d: DatatypeType :: { BoxRank($Box(d)) } BoxRank($Box(d)) == DtRank(d));

type ORDINAL = Box;

function ORD#IsNat(ORDINAL) : bool;

function ORD#Offset(ORDINAL) : int;

axiom (forall o: ORDINAL :: { ORD#Offset(o) } 0 <= ORD#Offset(o));

function {:inline} ORD#IsLimit(o: ORDINAL) : bool
{
  ORD#Offset(o) == 0
}

function {:inline} ORD#IsSucc(o: ORDINAL) : bool
{
  0 < ORD#Offset(o)
}

function ORD#FromNat(int) : ORDINAL;

axiom (forall n: int ::
  { ORD#FromNat(n) }
  0 <= n ==> ORD#IsNat(ORD#FromNat(n)) && ORD#Offset(ORD#FromNat(n)) == n);

axiom (forall o: ORDINAL ::
  { ORD#Offset(o) } { ORD#IsNat(o) }
  ORD#IsNat(o) ==> o == ORD#FromNat(ORD#Offset(o)));

function ORD#Less(ORDINAL, ORDINAL) : bool;

axiom (forall o: ORDINAL, p: ORDINAL ::
  { ORD#Less(o, p) }
  (ORD#Less(o, p) ==> o != p)
     && (ORD#IsNat(o) && !ORD#IsNat(p) ==> ORD#Less(o, p))
     && (ORD#IsNat(o) && ORD#IsNat(p)
       ==> ORD#Less(o, p) == (ORD#Offset(o) < ORD#Offset(p))));

axiom (forall o: ORDINAL, p: ORDINAL :: { ORD#Less(o, p) } ORD#Less(o, p) ==> o != p);

axiom (forall o: ORDINAL, p: ORDINAL ::
  { ORD#Less(o, p), ORD#Less(p, o) }
  ORD#Less(o, p) || o == p || ORD#Less(p, o));

axiom (forall o: ORDINAL, p: ORDINAL, r: ORDINAL ::
  { ORD#Less(o, p), ORD#Less(p, r) } { ORD#Less(o, p), ORD#Less(o, r) }
  ORD#Less(o, p) && ORD#Less(p, r) ==> ORD#Less(o, r));

function ORD#LessThanLimit(ORDINAL, ORDINAL) : bool;

axiom (forall o: ORDINAL, p: ORDINAL ::
  { ORD#LessThanLimit(o, p) }
  ORD#LessThanLimit(o, p) == ORD#Less(o, p));

function ORD#Plus(ORDINAL, ORDINAL) : ORDINAL;

axiom (forall o: ORDINAL, p: ORDINAL ::
  { ORD#Plus(o, p) }
  (ORD#IsNat(ORD#Plus(o, p)) ==> ORD#IsNat(o) && ORD#IsNat(p))
     && (ORD#IsNat(p)
       ==> ORD#IsNat(ORD#Plus(o, p)) == ORD#IsNat(o)
         && ORD#Offset(ORD#Plus(o, p)) == ORD#Offset(o) + ORD#Offset(p)));

axiom (forall o: ORDINAL, p: ORDINAL ::
  { ORD#Plus(o, p) }
  (o == ORD#Plus(o, p) || ORD#Less(o, ORD#Plus(o, p)))
     && (p == ORD#Plus(o, p) || ORD#Less(p, ORD#Plus(o, p))));

axiom (forall o: ORDINAL, p: ORDINAL ::
  { ORD#Plus(o, p) }
  (o == ORD#FromNat(0) ==> ORD#Plus(o, p) == p)
     && (p == ORD#FromNat(0) ==> ORD#Plus(o, p) == o));

function ORD#Minus(ORDINAL, ORDINAL) : ORDINAL;

axiom (forall o: ORDINAL, p: ORDINAL ::
  { ORD#Minus(o, p) }
  ORD#IsNat(p) && ORD#Offset(p) <= ORD#Offset(o)
     ==> ORD#IsNat(ORD#Minus(o, p)) == ORD#IsNat(o)
       && ORD#Offset(ORD#Minus(o, p)) == ORD#Offset(o) - ORD#Offset(p));

axiom (forall o: ORDINAL, p: ORDINAL ::
  { ORD#Minus(o, p) }
  ORD#IsNat(p) && ORD#Offset(p) <= ORD#Offset(o)
     ==> (p == ORD#FromNat(0) && ORD#Minus(o, p) == o)
       || (p != ORD#FromNat(0) && ORD#Less(ORD#Minus(o, p), o)));

axiom (forall o: ORDINAL, m: int, n: int ::
  { ORD#Plus(ORD#Plus(o, ORD#FromNat(m)), ORD#FromNat(n)) }
  0 <= m && 0 <= n
     ==> ORD#Plus(ORD#Plus(o, ORD#FromNat(m)), ORD#FromNat(n))
       == ORD#Plus(o, ORD#FromNat(m + n)));

axiom (forall o: ORDINAL, m: int, n: int ::
  { ORD#Minus(ORD#Minus(o, ORD#FromNat(m)), ORD#FromNat(n)) }
  0 <= m && 0 <= n && m + n <= ORD#Offset(o)
     ==> ORD#Minus(ORD#Minus(o, ORD#FromNat(m)), ORD#FromNat(n))
       == ORD#Minus(o, ORD#FromNat(m + n)));

axiom (forall o: ORDINAL, m: int, n: int ::
  { ORD#Minus(ORD#Plus(o, ORD#FromNat(m)), ORD#FromNat(n)) }
  0 <= m && 0 <= n && n <= ORD#Offset(o) + m
     ==> (0 <= m - n
         ==> ORD#Minus(ORD#Plus(o, ORD#FromNat(m)), ORD#FromNat(n))
           == ORD#Plus(o, ORD#FromNat(m - n)))
       && (m - n <= 0
         ==> ORD#Minus(ORD#Plus(o, ORD#FromNat(m)), ORD#FromNat(n))
           == ORD#Minus(o, ORD#FromNat(n - m))));

axiom (forall o: ORDINAL, m: int, n: int ::
  { ORD#Plus(ORD#Minus(o, ORD#FromNat(m)), ORD#FromNat(n)) }
  0 <= m && 0 <= n && n <= ORD#Offset(o) + m
     ==> (0 <= m - n
         ==> ORD#Plus(ORD#Minus(o, ORD#FromNat(m)), ORD#FromNat(n))
           == ORD#Minus(o, ORD#FromNat(m - n)))
       && (m - n <= 0
         ==> ORD#Plus(ORD#Minus(o, ORD#FromNat(m)), ORD#FromNat(n))
           == ORD#Plus(o, ORD#FromNat(n - m))));

const $ModuleContextHeight: int;

const $FunctionContextHeight: int;

type LayerType;

const $LZ: LayerType;

function $LS(LayerType) : LayerType;

function AsFuelBottom(LayerType) : LayerType;

function AtLayer<A>([LayerType]A, LayerType) : A;

axiom (forall<A> f: [LayerType]A, ly: LayerType ::
  { AtLayer(f, ly) }
  AtLayer(f, ly) == f[ly]);

axiom (forall<A> f: [LayerType]A, ly: LayerType ::
  { AtLayer(f, $LS(ly)) }
  AtLayer(f, $LS(ly)) == AtLayer(f, ly));

type Field _;

function FDim<T>(Field T) : int;

function IndexField(int) : Field Box;

axiom (forall i: int :: { IndexField(i) } FDim(IndexField(i)) == 1);

function IndexField_Inverse<T>(Field T) : int;

axiom (forall i: int :: { IndexField(i) } IndexField_Inverse(IndexField(i)) == i);

function MultiIndexField(Field Box, int) : Field Box;

axiom (forall f: Field Box, i: int ::
  { MultiIndexField(f, i) }
  FDim(MultiIndexField(f, i)) == FDim(f) + 1);

function MultiIndexField_Inverse0<T>(Field T) : Field T;

function MultiIndexField_Inverse1<T>(Field T) : int;

axiom (forall f: Field Box, i: int ::
  { MultiIndexField(f, i) }
  MultiIndexField_Inverse0(MultiIndexField(f, i)) == f
     && MultiIndexField_Inverse1(MultiIndexField(f, i)) == i);

function DeclType<T>(Field T) : ClassName;

type NameFamily;

function DeclName<T>(Field T) : NameFamily;

function FieldOfDecl<alpha>(ClassName, NameFamily) : Field alpha;

axiom (forall<T> cl: ClassName, nm: NameFamily ::
  { FieldOfDecl(cl, nm): Field T }
  DeclType(FieldOfDecl(cl, nm): Field T) == cl
     && DeclName(FieldOfDecl(cl, nm): Field T) == nm);

function $IsGhostField<T>(Field T) : bool;

axiom (forall<T> h: Heap, k: Heap, v: T, t: Ty ::
  { $HeapSucc(h, k), $IsAlloc(v, t, h) }
  $HeapSucc(h, k) ==> $IsAlloc(v, t, h) ==> $IsAlloc(v, t, k));

axiom (forall h: Heap, k: Heap, bx: Box, t: Ty ::
  { $HeapSucc(h, k), $IsAllocBox(bx, t, h) }
  $HeapSucc(h, k) ==> $IsAllocBox(bx, t, h) ==> $IsAllocBox(bx, t, k));

const unique alloc: Field bool;

axiom FDim(alloc) == 0 && !$IsGhostField(alloc);

function _System.array.Length(a: ref) : int;

axiom (forall o: ref :: 0 <= _System.array.Length(o));

// function Int(x: real) : int; // 'real' unsupported

// axiom (forall x: real :: { Int(x): int } Int(x): int == int(x));

// function Real(x: int) : real; // 'real' unsupported

// axiom (forall x: int :: { Real(x): real } Real(x): real == real(x));

// axiom (forall i: int :: { Int(Real(i)) } Int(Real(i)) == i); // 'real' unsupported

// function {:inline} _System.real.Floor(x: real) : int // 'real' unsupported
// { // 'real' unsupported
//   Int(x) // 'real' unsupported
// } // 'real' unsupported

type Heap = <alpha>[ref,Field alpha]alpha;

function {:inline} read<alpha>(H: Heap, r: ref, f: Field alpha) : alpha
{
  H[r, f]
}

function {:inline} update<alpha>(H: Heap, r: ref, f: Field alpha, v: alpha) : Heap
{
  H[r, f := v]
}

function $IsGoodHeap(Heap) : bool;

function $IsHeapAnchor(Heap) : bool;

var $Heap: Heap where $IsGoodHeap($Heap) && $IsHeapAnchor($Heap);

const $OneHeap: Heap;

axiom $IsGoodHeap($OneHeap);

function $HeapSucc(Heap, Heap) : bool;

axiom (forall<alpha> h: Heap, r: ref, f: Field alpha, x: alpha ::
  { update(h, r, f, x) }
  $IsGoodHeap(update(h, r, f, x)) ==> $HeapSucc(h, update(h, r, f, x)));

axiom (forall a: Heap, b: Heap, c: Heap ::
  { $HeapSucc(a, b), $HeapSucc(b, c) }
  $HeapSucc(a, b) && $HeapSucc(b, c) ==> $HeapSucc(a, c));

axiom (forall h: Heap, k: Heap ::
  { $HeapSucc(h, k) }
  $HeapSucc(h, k)
     ==> (forall o: ref :: { read(k, o, alloc) } read(h, o, alloc) ==> read(k, o, alloc)));

function $HeapSuccGhost(Heap, Heap) : bool;

axiom (forall h: Heap, k: Heap ::
  { $HeapSuccGhost(h, k) }
  $HeapSuccGhost(h, k)
     ==> $HeapSucc(h, k)
       && (forall<alpha> o: ref, f: Field alpha ::
        { read(k, o, f) }
        !$IsGhostField(f) ==> read(h, o, f) == read(k, o, f)));

type TickType;

var $Tick: TickType;

procedure $YieldHavoc(this: ref, rds: Set Box, nw: Set Box);
  modifies $Heap;
  ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==>
      $o == this || rds[$Box($o)] || nw[$Box($o)]
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
  ensures $HeapSucc(old($Heap), $Heap);



procedure $IterHavoc0(this: ref, rds: Set Box, modi: Set Box);
  modifies $Heap;
  ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==>
      rds[$Box($o)] && !modi[$Box($o)] && $o != this
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
  ensures $HeapSucc(old($Heap), $Heap);



procedure $IterHavoc1(this: ref, modi: Set Box, nw: Set Box);
  modifies $Heap;
  ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f)
         || $o == this
         || modi[$Box($o)]
         || nw[$Box($o)]);
  ensures $HeapSucc(old($Heap), $Heap);



procedure $IterCollectNewObjects(prevHeap: Heap, newHeap: Heap, this: ref, NW: Field (Set Box))
   returns (s: Set Box);
  ensures (forall bx: Box ::
    { s[bx] }
    s[bx]
       <==> read(newHeap, this, NW)[bx]
         || (
          $Unbox(bx) != null
           && !read(prevHeap, $Unbox(bx): ref, alloc)
           && read(newHeap, $Unbox(bx): ref, alloc)));



type Set T = [T]bool;

function Set#Card<T>(Set T) : int;

axiom (forall<T> s: Set T :: { Set#Card(s) } 0 <= Set#Card(s));

function Set#Empty<T>() : Set T;

axiom (forall<T> o: T :: { Set#Empty()[o] } !Set#Empty()[o]);

axiom (forall<T> s: Set T ::
  { Set#Card(s) }
  (Set#Card(s) == 0 <==> s == Set#Empty())
     && (Set#Card(s) != 0 ==> (exists x: T :: s[x])));

function Set#Singleton<T>(T) : Set T;

axiom (forall<T> r: T :: { Set#Singleton(r) } Set#Singleton(r)[r]);

axiom (forall<T> r: T, o: T ::
  { Set#Singleton(r)[o] }
  Set#Singleton(r)[o] <==> r == o);

axiom (forall<T> r: T ::
  { Set#Card(Set#Singleton(r)) }
  Set#Card(Set#Singleton(r)) == 1);

function Set#UnionOne<T>(Set T, T) : Set T;

axiom (forall<T> a: Set T, x: T, o: T ::
  { Set#UnionOne(a, x)[o] }
  Set#UnionOne(a, x)[o] <==> o == x || a[o]);

axiom (forall<T> a: Set T, x: T :: { Set#UnionOne(a, x) } Set#UnionOne(a, x)[x]);

axiom (forall<T> a: Set T, x: T, y: T ::
  { Set#UnionOne(a, x), a[y] }
  a[y] ==> Set#UnionOne(a, x)[y]);

axiom (forall<T> a: Set T, x: T ::
  { Set#Card(Set#UnionOne(a, x)) }
  a[x] ==> Set#Card(Set#UnionOne(a, x)) == Set#Card(a));

axiom (forall<T> a: Set T, x: T ::
  { Set#Card(Set#UnionOne(a, x)) }
  !a[x] ==> Set#Card(Set#UnionOne(a, x)) == Set#Card(a) + 1);

function Set#Union<T>(Set T, Set T) : Set T;

axiom (forall<T> a: Set T, b: Set T, o: T ::
  { Set#Union(a, b)[o] }
  Set#Union(a, b)[o] <==> a[o] || b[o]);

axiom (forall<T> a: Set T, b: Set T, y: T ::
  { Set#Union(a, b), a[y] }
  a[y] ==> Set#Union(a, b)[y]);

axiom (forall<T> a: Set T, b: Set T, y: T ::
  { Set#Union(a, b), b[y] }
  b[y] ==> Set#Union(a, b)[y]);

axiom (forall<T> a: Set T, b: Set T ::
  { Set#Union(a, b) }
  Set#Disjoint(a, b)
     ==> Set#Difference(Set#Union(a, b), a) == b
       && Set#Difference(Set#Union(a, b), b) == a);

function Set#Intersection<T>(Set T, Set T) : Set T;

axiom (forall<T> a: Set T, b: Set T, o: T ::
  { Set#Intersection(a, b)[o] }
  Set#Intersection(a, b)[o] <==> a[o] && b[o]);

axiom (forall<T> a: Set T, b: Set T ::
  { Set#Union(Set#Union(a, b), b) }
  Set#Union(Set#Union(a, b), b) == Set#Union(a, b));

axiom (forall<T> a: Set T, b: Set T ::
  { Set#Union(a, Set#Union(a, b)) }
  Set#Union(a, Set#Union(a, b)) == Set#Union(a, b));

axiom (forall<T> a: Set T, b: Set T ::
  { Set#Intersection(Set#Intersection(a, b), b) }
  Set#Intersection(Set#Intersection(a, b), b) == Set#Intersection(a, b));

axiom (forall<T> a: Set T, b: Set T ::
  { Set#Intersection(a, Set#Intersection(a, b)) }
  Set#Intersection(a, Set#Intersection(a, b)) == Set#Intersection(a, b));

axiom (forall<T> a: Set T, b: Set T ::
  { Set#Card(Set#Union(a, b)) } { Set#Card(Set#Intersection(a, b)) }
  Set#Card(Set#Union(a, b)) + Set#Card(Set#Intersection(a, b))
     == Set#Card(a) + Set#Card(b));

function Set#Difference<T>(Set T, Set T) : Set T;

axiom (forall<T> a: Set T, b: Set T, o: T ::
  { Set#Difference(a, b)[o] }
  Set#Difference(a, b)[o] <==> a[o] && !b[o]);

axiom (forall<T> a: Set T, b: Set T, y: T ::
  { Set#Difference(a, b), b[y] }
  b[y] ==> !Set#Difference(a, b)[y]);

axiom (forall<T> a: Set T, b: Set T ::
  { Set#Card(Set#Difference(a, b)) }
  Set#Card(Set#Difference(a, b))
         + Set#Card(Set#Difference(b, a))
         + Set#Card(Set#Intersection(a, b))
       == Set#Card(Set#Union(a, b))
     && Set#Card(Set#Difference(a, b)) == Set#Card(a) - Set#Card(Set#Intersection(a, b)));

function Set#Subset<T>(Set T, Set T) : bool;

axiom (forall<T> a: Set T, b: Set T ::
  { Set#Subset(a, b) }
  Set#Subset(a, b) <==> (forall o: T :: { a[o] } { b[o] } a[o] ==> b[o]));

function Set#Equal<T>(Set T, Set T) : bool;

axiom (forall<T> a: Set T, b: Set T ::
  { Set#Equal(a, b) }
  Set#Equal(a, b) <==> (forall o: T :: { a[o] } { b[o] } a[o] <==> b[o]));

axiom (forall<T> a: Set T, b: Set T :: { Set#Equal(a, b) } Set#Equal(a, b) ==> a == b);

function Set#Disjoint<T>(Set T, Set T) : bool;

axiom (forall<T> a: Set T, b: Set T ::
  { Set#Disjoint(a, b) }
  Set#Disjoint(a, b) <==> (forall o: T :: { a[o] } { b[o] } !a[o] || !b[o]));

type ISet T = [T]bool;

function ISet#Empty<T>() : Set T;

axiom (forall<T> o: T :: { ISet#Empty()[o] } !ISet#Empty()[o]);

function ISet#UnionOne<T>(ISet T, T) : ISet T;

axiom (forall<T> a: ISet T, x: T, o: T ::
  { ISet#UnionOne(a, x)[o] }
  ISet#UnionOne(a, x)[o] <==> o == x || a[o]);

axiom (forall<T> a: ISet T, x: T :: { ISet#UnionOne(a, x) } ISet#UnionOne(a, x)[x]);

axiom (forall<T> a: ISet T, x: T, y: T ::
  { ISet#UnionOne(a, x), a[y] }
  a[y] ==> ISet#UnionOne(a, x)[y]);

function ISet#Union<T>(ISet T, ISet T) : ISet T;

axiom (forall<T> a: ISet T, b: ISet T, o: T ::
  { ISet#Union(a, b)[o] }
  ISet#Union(a, b)[o] <==> a[o] || b[o]);

axiom (forall<T> a: ISet T, b: ISet T, y: T ::
  { ISet#Union(a, b), a[y] }
  a[y] ==> ISet#Union(a, b)[y]);

axiom (forall<T> a: Set T, b: Set T, y: T ::
  { ISet#Union(a, b), b[y] }
  b[y] ==> ISet#Union(a, b)[y]);

axiom (forall<T> a: ISet T, b: ISet T ::
  { ISet#Union(a, b) }
  ISet#Disjoint(a, b)
     ==> ISet#Difference(ISet#Union(a, b), a) == b
       && ISet#Difference(ISet#Union(a, b), b) == a);

function ISet#Intersection<T>(ISet T, ISet T) : ISet T;

axiom (forall<T> a: ISet T, b: ISet T, o: T ::
  { ISet#Intersection(a, b)[o] }
  ISet#Intersection(a, b)[o] <==> a[o] && b[o]);

axiom (forall<T> a: ISet T, b: ISet T ::
  { ISet#Union(ISet#Union(a, b), b) }
  ISet#Union(ISet#Union(a, b), b) == ISet#Union(a, b));

axiom (forall<T> a: Set T, b: Set T ::
  { ISet#Union(a, ISet#Union(a, b)) }
  ISet#Union(a, ISet#Union(a, b)) == ISet#Union(a, b));

axiom (forall<T> a: ISet T, b: ISet T ::
  { ISet#Intersection(ISet#Intersection(a, b), b) }
  ISet#Intersection(ISet#Intersection(a, b), b) == ISet#Intersection(a, b));

axiom (forall<T> a: ISet T, b: ISet T ::
  { ISet#Intersection(a, ISet#Intersection(a, b)) }
  ISet#Intersection(a, ISet#Intersection(a, b)) == ISet#Intersection(a, b));

function ISet#Difference<T>(ISet T, ISet T) : ISet T;

axiom (forall<T> a: ISet T, b: ISet T, o: T ::
  { ISet#Difference(a, b)[o] }
  ISet#Difference(a, b)[o] <==> a[o] && !b[o]);

axiom (forall<T> a: ISet T, b: ISet T, y: T ::
  { ISet#Difference(a, b), b[y] }
  b[y] ==> !ISet#Difference(a, b)[y]);

function ISet#Subset<T>(ISet T, ISet T) : bool;

axiom (forall<T> a: ISet T, b: ISet T ::
  { ISet#Subset(a, b) }
  ISet#Subset(a, b) <==> (forall o: T :: { a[o] } { b[o] } a[o] ==> b[o]));

function ISet#Equal<T>(ISet T, ISet T) : bool;

axiom (forall<T> a: ISet T, b: ISet T ::
  { ISet#Equal(a, b) }
  ISet#Equal(a, b) <==> (forall o: T :: { a[o] } { b[o] } a[o] <==> b[o]));

axiom (forall<T> a: ISet T, b: ISet T ::
  { ISet#Equal(a, b) }
  ISet#Equal(a, b) ==> a == b);

function ISet#Disjoint<T>(ISet T, ISet T) : bool;

axiom (forall<T> a: ISet T, b: ISet T ::
  { ISet#Disjoint(a, b) }
  ISet#Disjoint(a, b) <==> (forall o: T :: { a[o] } { b[o] } !a[o] || !b[o]));

function Math#min(a: int, b: int) : int;

axiom (forall a: int, b: int :: { Math#min(a, b) } a <= b <==> Math#min(a, b) == a);

axiom (forall a: int, b: int :: { Math#min(a, b) } b <= a <==> Math#min(a, b) == b);

axiom (forall a: int, b: int ::
  { Math#min(a, b) }
  Math#min(a, b) == a || Math#min(a, b) == b);

function Math#clip(a: int) : int;

axiom (forall a: int :: { Math#clip(a) } 0 <= a ==> Math#clip(a) == a);

axiom (forall a: int :: { Math#clip(a) } a < 0 ==> Math#clip(a) == 0);

type MultiSet T = [T]int;

function $IsGoodMultiSet<T>(ms: MultiSet T) : bool;

axiom (forall<T> ms: MultiSet T ::
  { $IsGoodMultiSet(ms) }
  $IsGoodMultiSet(ms)
     <==> (forall bx: T :: { ms[bx] } 0 <= ms[bx] && ms[bx] <= MultiSet#Card(ms)));

function MultiSet#Card<T>(MultiSet T) : int;

axiom (forall<T> s: MultiSet T :: { MultiSet#Card(s) } 0 <= MultiSet#Card(s));

axiom (forall<T> s: MultiSet T, x: T, n: int ::
  { MultiSet#Card(s[x := n]) }
  0 <= n ==> MultiSet#Card(s[x := n]) == MultiSet#Card(s) - s[x] + n);

function MultiSet#Empty<T>() : MultiSet T;

axiom (forall<T> o: T :: { MultiSet#Empty()[o] } MultiSet#Empty()[o] == 0);

axiom (forall<T> s: MultiSet T ::
  { MultiSet#Card(s) }
  (MultiSet#Card(s) == 0 <==> s == MultiSet#Empty())
     && (MultiSet#Card(s) != 0 ==> (exists x: T :: 0 < s[x])));

function MultiSet#Singleton<T>(T) : MultiSet T;

axiom (forall<T> r: T, o: T ::
  { MultiSet#Singleton(r)[o] }
  (MultiSet#Singleton(r)[o] == 1 <==> r == o)
     && (MultiSet#Singleton(r)[o] == 0 <==> r != o));

axiom (forall<T> r: T ::
  { MultiSet#Singleton(r) }
  MultiSet#Singleton(r) == MultiSet#UnionOne(MultiSet#Empty(), r));

function MultiSet#UnionOne<T>(MultiSet T, T) : MultiSet T;

axiom (forall<T> a: MultiSet T, x: T, o: T ::
  { MultiSet#UnionOne(a, x)[o] }
  0 < MultiSet#UnionOne(a, x)[o] <==> o == x || 0 < a[o]);

axiom (forall<T> a: MultiSet T, x: T ::
  { MultiSet#UnionOne(a, x) }
  MultiSet#UnionOne(a, x)[x] == a[x] + 1);

axiom (forall<T> a: MultiSet T, x: T, y: T ::
  { MultiSet#UnionOne(a, x), a[y] }
  0 < a[y] ==> 0 < MultiSet#UnionOne(a, x)[y]);

axiom (forall<T> a: MultiSet T, x: T, y: T ::
  { MultiSet#UnionOne(a, x), a[y] }
  x != y ==> a[y] == MultiSet#UnionOne(a, x)[y]);

axiom (forall<T> a: MultiSet T, x: T ::
  { MultiSet#Card(MultiSet#UnionOne(a, x)) }
  MultiSet#Card(MultiSet#UnionOne(a, x)) == MultiSet#Card(a) + 1);

function MultiSet#Union<T>(MultiSet T, MultiSet T) : MultiSet T;

axiom (forall<T> a: MultiSet T, b: MultiSet T, o: T ::
  { MultiSet#Union(a, b)[o] }
  MultiSet#Union(a, b)[o] == a[o] + b[o]);

axiom (forall<T> a: MultiSet T, b: MultiSet T ::
  { MultiSet#Card(MultiSet#Union(a, b)) }
  MultiSet#Card(MultiSet#Union(a, b)) == MultiSet#Card(a) + MultiSet#Card(b));

function MultiSet#Intersection<T>(MultiSet T, MultiSet T) : MultiSet T;

axiom (forall<T> a: MultiSet T, b: MultiSet T, o: T ::
  { MultiSet#Intersection(a, b)[o] }
  MultiSet#Intersection(a, b)[o] == Math#min(a[o], b[o]));

axiom (forall<T> a: MultiSet T, b: MultiSet T ::
  { MultiSet#Intersection(MultiSet#Intersection(a, b), b) }
  MultiSet#Intersection(MultiSet#Intersection(a, b), b)
     == MultiSet#Intersection(a, b));

axiom (forall<T> a: MultiSet T, b: MultiSet T ::
  { MultiSet#Intersection(a, MultiSet#Intersection(a, b)) }
  MultiSet#Intersection(a, MultiSet#Intersection(a, b))
     == MultiSet#Intersection(a, b));

function MultiSet#Difference<T>(MultiSet T, MultiSet T) : MultiSet T;

axiom (forall<T> a: MultiSet T, b: MultiSet T, o: T ::
  { MultiSet#Difference(a, b)[o] }
  MultiSet#Difference(a, b)[o] == Math#clip(a[o] - b[o]));

axiom (forall<T> a: MultiSet T, b: MultiSet T, y: T ::
  { MultiSet#Difference(a, b), b[y], a[y] }
  a[y] <= b[y] ==> MultiSet#Difference(a, b)[y] == 0);

axiom (forall<T> a: MultiSet T, b: MultiSet T ::
  { MultiSet#Card(MultiSet#Difference(a, b)) }
  MultiSet#Card(MultiSet#Difference(a, b))
         + MultiSet#Card(MultiSet#Difference(b, a))
         + 2 * MultiSet#Card(MultiSet#Intersection(a, b))
       == MultiSet#Card(MultiSet#Union(a, b))
     && MultiSet#Card(MultiSet#Difference(a, b))
       == MultiSet#Card(a) - MultiSet#Card(MultiSet#Intersection(a, b)));

function MultiSet#Subset<T>(MultiSet T, MultiSet T) : bool;

axiom (forall<T> a: MultiSet T, b: MultiSet T ::
  { MultiSet#Subset(a, b) }
  MultiSet#Subset(a, b) <==> (forall o: T :: { a[o] } { b[o] } a[o] <= b[o]));

function MultiSet#Equal<T>(MultiSet T, MultiSet T) : bool;

axiom (forall<T> a: MultiSet T, b: MultiSet T ::
  { MultiSet#Equal(a, b) }
  MultiSet#Equal(a, b) <==> (forall o: T :: { a[o] } { b[o] } a[o] == b[o]));

axiom (forall<T> a: MultiSet T, b: MultiSet T ::
  { MultiSet#Equal(a, b) }
  MultiSet#Equal(a, b) ==> a == b);

function MultiSet#Disjoint<T>(MultiSet T, MultiSet T) : bool;

axiom (forall<T> a: MultiSet T, b: MultiSet T ::
  { MultiSet#Disjoint(a, b) }
  MultiSet#Disjoint(a, b)
     <==> (forall o: T :: { a[o] } { b[o] } a[o] == 0 || b[o] == 0));

function MultiSet#FromSet<T>(Set T) : MultiSet T;

axiom (forall<T> s: Set T, a: T ::
  { MultiSet#FromSet(s)[a] }
  (MultiSet#FromSet(s)[a] == 0 <==> !s[a])
     && (MultiSet#FromSet(s)[a] == 1 <==> s[a]));

axiom (forall<T> s: Set T ::
  { MultiSet#Card(MultiSet#FromSet(s)) }
  MultiSet#Card(MultiSet#FromSet(s)) == Set#Card(s));

function MultiSet#FromSeq<T>(Seq T) : MultiSet T;

axiom (forall<T> s: Seq T ::
  { MultiSet#FromSeq(s) }
  $IsGoodMultiSet(MultiSet#FromSeq(s)));

axiom (forall<T> s: Seq T ::
  { MultiSet#Card(MultiSet#FromSeq(s)) }
  MultiSet#Card(MultiSet#FromSeq(s)) == Seq#Length(s));

axiom (forall<T> s: Seq T, v: T ::
  { MultiSet#FromSeq(Seq#Build(s, v)) }
  MultiSet#FromSeq(Seq#Build(s, v)) == MultiSet#UnionOne(MultiSet#FromSeq(s), v));

axiom (forall<T>  ::
  MultiSet#FromSeq(Seq#Empty(): Seq T) == MultiSet#Empty(): MultiSet T);

axiom (forall<T> a: Seq T, b: Seq T ::
  { MultiSet#FromSeq(Seq#Append(a, b)) }
  MultiSet#FromSeq(Seq#Append(a, b))
     == MultiSet#Union(MultiSet#FromSeq(a), MultiSet#FromSeq(b)));

axiom (forall<T> s: Seq T, i: int, v: T, x: T ::
  { MultiSet#FromSeq(Seq#Update(s, i, v))[x] }
  0 <= i && i < Seq#Length(s)
     ==> MultiSet#FromSeq(Seq#Update(s, i, v))[x]
       == MultiSet#Union(MultiSet#Difference(MultiSet#FromSeq(s), MultiSet#Singleton(Seq#Index(s, i))),
        MultiSet#Singleton(v))[x]);

axiom (forall<T> s: Seq T, x: T ::
  { MultiSet#FromSeq(s)[x] }
  (exists i: int ::
      { Seq#Index(s, i) }
      0 <= i && i < Seq#Length(s) && x == Seq#Index(s, i))
     <==> 0 < MultiSet#FromSeq(s)[x]);

type Seq _;

function Seq#Length<T>(Seq T) : int;

axiom (forall<T> s: Seq T :: { Seq#Length(s) } 0 <= Seq#Length(s));

function Seq#Empty<T>() : Seq T;

axiom (forall<T>  :: Seq#Length(Seq#Empty(): Seq T) == 0);

axiom (forall<T> s: Seq T ::
  { Seq#Length(s) }
  Seq#Length(s) == 0 ==> s == Seq#Empty());

axiom (forall<T> t: Ty :: { $Is(Seq#Empty(): Seq T, t) } $Is(Seq#Empty(): Seq T, t));

function Seq#Singleton<T>(T) : Seq T;

axiom (forall<T> t: T ::
  { Seq#Length(Seq#Singleton(t)) }
  Seq#Length(Seq#Singleton(t)) == 1);

function Seq#Build<T>(s: Seq T, val: T) : Seq T;

function Seq#Build_inv0<T>(s: Seq T) : Seq T;

function Seq#Build_inv1<T>(s: Seq T) : T;

axiom (forall<T> s: Seq T, val: T ::
  { Seq#Build(s, val) }
  Seq#Build_inv0(Seq#Build(s, val)) == s
     && Seq#Build_inv1(Seq#Build(s, val)) == val);

axiom (forall<T> s: Seq T, v: T ::
  { Seq#Length(Seq#Build(s, v)) }
  Seq#Length(Seq#Build(s, v)) == 1 + Seq#Length(s));

axiom (forall<T> s: Seq T, i: int, v: T ::
  { Seq#Index(Seq#Build(s, v), i) }
  (i == Seq#Length(s) ==> Seq#Index(Seq#Build(s, v), i) == v)
     && (i != Seq#Length(s) ==> Seq#Index(Seq#Build(s, v), i) == Seq#Index(s, i)));

axiom (forall s: Seq Box, bx: Box, t: Ty ::
  { $Is(Seq#Build(s, bx), TSeq(t)) }
  $Is(s, TSeq(t)) && $IsBox(bx, t) ==> $Is(Seq#Build(s, bx), TSeq(t)));

function Seq#Append<T>(Seq T, Seq T) : Seq T;

axiom (forall<T> s0: Seq T, s1: Seq T ::
  { Seq#Length(Seq#Append(s0, s1)) }
  Seq#Length(Seq#Append(s0, s1)) == Seq#Length(s0) + Seq#Length(s1));

axiom (forall s0: Seq Box, s1: Seq Box, t: Ty ::
  { $Is(Seq#Append(s0, s1), t) }
  $Is(s0, t) && $Is(s1, t) ==> $Is(Seq#Append(s0, s1), t));

function Seq#Index<T>(Seq T, int) : T;

axiom (forall<T> t: T ::
  { Seq#Index(Seq#Singleton(t), 0) }
  Seq#Index(Seq#Singleton(t), 0) == t);

axiom (forall<T> s0: Seq T, s1: Seq T, n: int ::
  { Seq#Index(Seq#Append(s0, s1), n) }
  (n < Seq#Length(s0) ==> Seq#Index(Seq#Append(s0, s1), n) == Seq#Index(s0, n))
     && (Seq#Length(s0) <= n
       ==> Seq#Index(Seq#Append(s0, s1), n) == Seq#Index(s1, n - Seq#Length(s0))));

function Seq#Update<T>(Seq T, int, T) : Seq T;

axiom (forall<T> s: Seq T, i: int, v: T ::
  { Seq#Length(Seq#Update(s, i, v)) }
  0 <= i && i < Seq#Length(s) ==> Seq#Length(Seq#Update(s, i, v)) == Seq#Length(s));

axiom (forall<T> s: Seq T, i: int, v: T, n: int ::
  { Seq#Index(Seq#Update(s, i, v), n) }
  0 <= n && n < Seq#Length(s)
     ==> (i == n ==> Seq#Index(Seq#Update(s, i, v), n) == v)
       && (i != n ==> Seq#Index(Seq#Update(s, i, v), n) == Seq#Index(s, n)));

function Seq#Contains<T>(Seq T, T) : bool;

axiom (forall<T> s: Seq T, x: T ::
  { Seq#Contains(s, x) }
  Seq#Contains(s, x)
     <==> (exists i: int ::
      { Seq#Index(s, i) }
      0 <= i && i < Seq#Length(s) && Seq#Index(s, i) == x));

axiom (forall<T> x: T ::
  { Seq#Contains(Seq#Empty(), x) }
  !Seq#Contains(Seq#Empty(), x));

axiom (forall<T> s0: Seq T, s1: Seq T, x: T ::
  { Seq#Contains(Seq#Append(s0, s1), x) }
  Seq#Contains(Seq#Append(s0, s1), x)
     <==> Seq#Contains(s0, x) || Seq#Contains(s1, x));

axiom (forall<T> s: Seq T, v: T, x: T ::
  { Seq#Contains(Seq#Build(s, v), x) }
  Seq#Contains(Seq#Build(s, v), x) <==> v == x || Seq#Contains(s, x));

axiom (forall<T> s: Seq T, n: int, x: T ::
  { Seq#Contains(Seq#Take(s, n), x) }
  Seq#Contains(Seq#Take(s, n), x)
     <==> (exists i: int ::
      { Seq#Index(s, i) }
      0 <= i && i < n && i < Seq#Length(s) && Seq#Index(s, i) == x));

axiom (forall<T> s: Seq T, n: int, x: T ::
  { Seq#Contains(Seq#Drop(s, n), x) }
  Seq#Contains(Seq#Drop(s, n), x)
     <==> (exists i: int ::
      { Seq#Index(s, i) }
      0 <= n && n <= i && i < Seq#Length(s) && Seq#Index(s, i) == x));

function Seq#Equal<T>(Seq T, Seq T) : bool;

axiom (forall<T> s0: Seq T, s1: Seq T ::
  { Seq#Equal(s0, s1) }
  Seq#Equal(s0, s1)
     <==> Seq#Length(s0) == Seq#Length(s1)
       && (forall j: int ::
        { Seq#Index(s0, j) } { Seq#Index(s1, j) }
        0 <= j && j < Seq#Length(s0) ==> Seq#Index(s0, j) == Seq#Index(s1, j)));

axiom (forall<T> a: Seq T, b: Seq T :: { Seq#Equal(a, b) } Seq#Equal(a, b) ==> a == b);

function Seq#SameUntil<T>(Seq T, Seq T, int) : bool;

axiom (forall<T> s0: Seq T, s1: Seq T, n: int ::
  { Seq#SameUntil(s0, s1, n) }
  Seq#SameUntil(s0, s1, n)
     <==> (forall j: int ::
      { Seq#Index(s0, j) } { Seq#Index(s1, j) }
      0 <= j && j < n ==> Seq#Index(s0, j) == Seq#Index(s1, j)));

function Seq#Take<T>(s: Seq T, howMany: int) : Seq T;

axiom (forall<T> s: Seq T, n: int ::
  { Seq#Length(Seq#Take(s, n)) }
  0 <= n && n <= Seq#Length(s) ==> Seq#Length(Seq#Take(s, n)) == n);

axiom (forall<T> s: Seq T, n: int, j: int ::
  {:weight 25} { Seq#Index(Seq#Take(s, n), j) } { Seq#Index(s, j), Seq#Take(s, n) }
  0 <= j && j < n && j < Seq#Length(s)
     ==> Seq#Index(Seq#Take(s, n), j) == Seq#Index(s, j));

function Seq#Drop<T>(s: Seq T, howMany: int) : Seq T;

axiom (forall<T> s: Seq T, n: int ::
  { Seq#Length(Seq#Drop(s, n)) }
  0 <= n && n <= Seq#Length(s) ==> Seq#Length(Seq#Drop(s, n)) == Seq#Length(s) - n);

axiom (forall<T> s: Seq T, n: int, j: int ::
  {:weight 25} { Seq#Index(Seq#Drop(s, n), j) }
  0 <= n && 0 <= j && j < Seq#Length(s) - n
     ==> Seq#Index(Seq#Drop(s, n), j) == Seq#Index(s, j + n));

axiom (forall<T> s: Seq T, n: int, k: int ::
  {:weight 25} { Seq#Index(s, k), Seq#Drop(s, n) }
  0 <= n && n <= k && k < Seq#Length(s)
     ==> Seq#Index(Seq#Drop(s, n), k - n) == Seq#Index(s, k));

axiom (forall<T> s: Seq T, t: Seq T ::
  { Seq#Append(s, t) }
  Seq#Take(Seq#Append(s, t), Seq#Length(s)) == s
     && Seq#Drop(Seq#Append(s, t), Seq#Length(s)) == t);

function Seq#FromArray(h: Heap, a: ref) : Seq Box;

axiom (forall h: Heap, a: ref ::
  { Seq#Length(Seq#FromArray(h, a)) }
  Seq#Length(Seq#FromArray(h, a)) == _System.array.Length(a));

axiom (forall h: Heap, a: ref ::
  { Seq#FromArray(h, a) }
  (forall i: int ::
    { read(h, a, IndexField(i)) } { Seq#Index(Seq#FromArray(h, a): Seq Box, i) }
    0 <= i && i < Seq#Length(Seq#FromArray(h, a))
       ==> Seq#Index(Seq#FromArray(h, a), i) == read(h, a, IndexField(i))));

axiom (forall h0: Heap, h1: Heap, a: ref ::
  { Seq#FromArray(h1, a), $HeapSucc(h0, h1) }
  $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && $HeapSucc(h0, h1)
       && (forall i: int ::
        0 <= i && i < _System.array.Length(a)
           ==> read(h0, a, IndexField(i)) == read(h1, a, IndexField(i)))
     ==> Seq#FromArray(h0, a) == Seq#FromArray(h1, a));

axiom (forall h: Heap, i: int, v: Box, a: ref ::
  { Seq#FromArray(update(h, a, IndexField(i), v), a) }
  0 <= i && i < _System.array.Length(a)
     ==> Seq#FromArray(update(h, a, IndexField(i), v), a)
       == Seq#Update(Seq#FromArray(h, a), i, v));

axiom (forall<T> s: Seq T, i: int, v: T, n: int ::
  { Seq#Take(Seq#Update(s, i, v), n) }
  0 <= i && i < n && n <= Seq#Length(s)
     ==> Seq#Take(Seq#Update(s, i, v), n) == Seq#Update(Seq#Take(s, n), i, v));

axiom (forall<T> s: Seq T, i: int, v: T, n: int ::
  { Seq#Take(Seq#Update(s, i, v), n) }
  n <= i && i < Seq#Length(s)
     ==> Seq#Take(Seq#Update(s, i, v), n) == Seq#Take(s, n));

axiom (forall<T> s: Seq T, i: int, v: T, n: int ::
  { Seq#Drop(Seq#Update(s, i, v), n) }
  0 <= n && n <= i && i < Seq#Length(s)
     ==> Seq#Drop(Seq#Update(s, i, v), n) == Seq#Update(Seq#Drop(s, n), i - n, v));

axiom (forall<T> s: Seq T, i: int, v: T, n: int ::
  { Seq#Drop(Seq#Update(s, i, v), n) }
  0 <= i && i < n && n < Seq#Length(s)
     ==> Seq#Drop(Seq#Update(s, i, v), n) == Seq#Drop(s, n));

axiom (forall h: Heap, a: ref, n0: int, n1: int ::
  { Seq#Take(Seq#FromArray(h, a), n0), Seq#Take(Seq#FromArray(h, a), n1) }
  n0 + 1 == n1 && 0 <= n0 && n1 <= _System.array.Length(a)
     ==> Seq#Take(Seq#FromArray(h, a), n1)
       == Seq#Build(Seq#Take(Seq#FromArray(h, a), n0), read(h, a, IndexField(n0): Field Box)));

axiom (forall<T> s: Seq T, v: T, n: int ::
  { Seq#Drop(Seq#Build(s, v), n) }
  0 <= n && n <= Seq#Length(s)
     ==> Seq#Drop(Seq#Build(s, v), n) == Seq#Build(Seq#Drop(s, n), v));

function Seq#Rank<T>(Seq T) : int;

axiom (forall s: Seq Box, i: int ::
  { DtRank($Unbox(Seq#Index(s, i)): DatatypeType) }
  0 <= i && i < Seq#Length(s)
     ==> DtRank($Unbox(Seq#Index(s, i)): DatatypeType) < Seq#Rank(s));

axiom (forall<T> s: Seq T, i: int ::
  { Seq#Rank(Seq#Drop(s, i)) }
  0 < i && i <= Seq#Length(s) ==> Seq#Rank(Seq#Drop(s, i)) < Seq#Rank(s));

axiom (forall<T> s: Seq T, i: int ::
  { Seq#Rank(Seq#Take(s, i)) }
  0 <= i && i < Seq#Length(s) ==> Seq#Rank(Seq#Take(s, i)) < Seq#Rank(s));

axiom (forall<T> s: Seq T, i: int, j: int ::
  { Seq#Rank(Seq#Append(Seq#Take(s, i), Seq#Drop(s, j))) }
  0 <= i && i < j && j <= Seq#Length(s)
     ==> Seq#Rank(Seq#Append(Seq#Take(s, i), Seq#Drop(s, j))) < Seq#Rank(s));

axiom (forall<T> s: Seq T, n: int ::
  { Seq#Drop(s, n) }
  n == 0 ==> Seq#Drop(s, n) == s);

axiom (forall<T> s: Seq T, n: int ::
  { Seq#Take(s, n) }
  n == 0 ==> Seq#Take(s, n) == Seq#Empty());

axiom (forall<T> s: Seq T, m: int, n: int ::
  { Seq#Drop(Seq#Drop(s, m), n) }
  0 <= m && 0 <= n && m + n <= Seq#Length(s)
     ==> Seq#Drop(Seq#Drop(s, m), n) == Seq#Drop(s, m + n));

type Map _ _;

function Map#Domain<U,V>(Map U V) : Set U;

function Map#Elements<U,V>(Map U V) : [U]V;

function Map#Card<U,V>(Map U V) : int;

axiom (forall<U,V> m: Map U V :: { Map#Card(m) } 0 <= Map#Card(m));

axiom (forall<U,V> m: Map U V ::
  { Set#Card(Map#Domain(m)) }
  Set#Card(Map#Domain(m)) == Map#Card(m));

function Map#Values<U,V>(Map U V) : Set V;

axiom (forall<U,V> m: Map U V, v: V ::
  { Map#Values(m)[v] }
  Map#Values(m)[v]
     == (exists u: U ::
      { Map#Domain(m)[u] } { Map#Elements(m)[u] }
      Map#Domain(m)[u] && v == Map#Elements(m)[u]));

function Map#Items<U,V>(Map U V) : Set Box;

function _System.__tuple_h2._0(DatatypeType) : Box;

function _System.__tuple_h2._1(DatatypeType) : Box;

axiom (forall<U,V> m: Map U V ::
  { Set#Card(Map#Items(m)) }
  Set#Card(Map#Items(m)) == Map#Card(m));

axiom (forall m: Map Box Box, item: Box ::
  { Map#Items(m)[item] }
  Map#Items(m)[item]
     <==> Map#Domain(m)[_System.__tuple_h2._0($Unbox(item))]
       && Map#Elements(m)[_System.__tuple_h2._0($Unbox(item))]
         == _System.__tuple_h2._1($Unbox(item)));

function Map#Empty<U,V>() : Map U V;

axiom (forall<U,V> u: U ::
  { Map#Domain(Map#Empty(): Map U V)[u] }
  !Map#Domain(Map#Empty(): Map U V)[u]);

axiom (forall<U,V> m: Map U V ::
  { Map#Card(m) }
  (Map#Card(m) == 0 <==> m == Map#Empty())
     && (Map#Card(m) != 0 ==> (exists x: U :: Map#Domain(m)[x])));

function Map#Glue<U,V>([U]bool, [U]V, Ty) : Map U V;

axiom (forall<U,V> a: [U]bool, b: [U]V, t: Ty ::
  { Map#Domain(Map#Glue(a, b, t)) }
  Map#Domain(Map#Glue(a, b, t)) == a);

axiom (forall<U,V> a: [U]bool, b: [U]V, t: Ty ::
  { Map#Elements(Map#Glue(a, b, t)) }
  Map#Elements(Map#Glue(a, b, t)) == b);

axiom (forall<U,V> a: [U]bool, b: [U]V, t: Ty ::
  { $Is(Map#Glue(a, b, t), t) }
  $Is(Map#Glue(a, b, t), t));

function Map#Build<U,V>(Map U V, U, V) : Map U V;

axiom (forall<U,V> m: Map U V, u: U, u': U, v: V ::
  { Map#Domain(Map#Build(m, u, v))[u'] } { Map#Elements(Map#Build(m, u, v))[u'] }
  (u' == u
       ==> Map#Domain(Map#Build(m, u, v))[u'] && Map#Elements(Map#Build(m, u, v))[u'] == v)
     && (u' != u
       ==> Map#Domain(Map#Build(m, u, v))[u'] == Map#Domain(m)[u']
         && Map#Elements(Map#Build(m, u, v))[u'] == Map#Elements(m)[u']));

axiom (forall<U,V> m: Map U V, u: U, v: V ::
  { Map#Card(Map#Build(m, u, v)) }
  Map#Domain(m)[u] ==> Map#Card(Map#Build(m, u, v)) == Map#Card(m));

axiom (forall<U,V> m: Map U V, u: U, v: V ::
  { Map#Card(Map#Build(m, u, v)) }
  !Map#Domain(m)[u] ==> Map#Card(Map#Build(m, u, v)) == Map#Card(m) + 1);

function Map#Equal<U,V>(Map U V, Map U V) : bool;

axiom (forall<U,V> m: Map U V, m': Map U V ::
  { Map#Equal(m, m') }
  Map#Equal(m, m')
     <==> (forall u: U :: Map#Domain(m)[u] == Map#Domain(m')[u])
       && (forall u: U :: Map#Domain(m)[u] ==> Map#Elements(m)[u] == Map#Elements(m')[u]));

axiom (forall<U,V> m: Map U V, m': Map U V ::
  { Map#Equal(m, m') }
  Map#Equal(m, m') ==> m == m');

function Map#Disjoint<U,V>(Map U V, Map U V) : bool;

axiom (forall<U,V> m: Map U V, m': Map U V ::
  { Map#Disjoint(m, m') }
  Map#Disjoint(m, m')
     <==> (forall o: U ::
      { Map#Domain(m)[o] } { Map#Domain(m')[o] }
      !Map#Domain(m)[o] || !Map#Domain(m')[o]));

type IMap _ _;

function IMap#Domain<U,V>(IMap U V) : Set U;

function IMap#Elements<U,V>(IMap U V) : [U]V;

function IMap#Values<U,V>(IMap U V) : Set V;

axiom (forall<U,V> m: IMap U V, v: V ::
  { IMap#Values(m)[v] }
  IMap#Values(m)[v]
     == (exists u: U ::
      { IMap#Domain(m)[u] } { IMap#Elements(m)[u] }
      IMap#Domain(m)[u] && v == IMap#Elements(m)[u]));

function IMap#Items<U,V>(IMap U V) : Set Box;

axiom (forall m: IMap Box Box, item: Box ::
  { IMap#Items(m)[item] }
  IMap#Items(m)[item]
     <==> IMap#Domain(m)[_System.__tuple_h2._0($Unbox(item))]
       && IMap#Elements(m)[_System.__tuple_h2._0($Unbox(item))]
         == _System.__tuple_h2._1($Unbox(item)));

function IMap#Empty<U,V>() : IMap U V;

axiom (forall<U,V> u: U ::
  { IMap#Domain(IMap#Empty(): IMap U V)[u] }
  !IMap#Domain(IMap#Empty(): IMap U V)[u]);

function IMap#Glue<U,V>([U]bool, [U]V, Ty) : IMap U V;

axiom (forall<U,V> a: [U]bool, b: [U]V, t: Ty ::
  { IMap#Domain(IMap#Glue(a, b, t)) }
  IMap#Domain(IMap#Glue(a, b, t)) == a);

axiom (forall<U,V> a: [U]bool, b: [U]V, t: Ty ::
  { IMap#Elements(IMap#Glue(a, b, t)) }
  IMap#Elements(IMap#Glue(a, b, t)) == b);

axiom (forall<U,V> a: [U]bool, b: [U]V, t: Ty ::
  { $Is(IMap#Glue(a, b, t), t) }
  $Is(IMap#Glue(a, b, t), t));

function IMap#Build<U,V>(IMap U V, U, V) : IMap U V;

axiom (forall<U,V> m: IMap U V, u: U, u': U, v: V ::
  { IMap#Domain(IMap#Build(m, u, v))[u'] }
    { IMap#Elements(IMap#Build(m, u, v))[u'] }
  (u' == u
       ==> IMap#Domain(IMap#Build(m, u, v))[u']
         && IMap#Elements(IMap#Build(m, u, v))[u'] == v)
     && (u' != u
       ==> IMap#Domain(IMap#Build(m, u, v))[u'] == IMap#Domain(m)[u']
         && IMap#Elements(IMap#Build(m, u, v))[u'] == IMap#Elements(m)[u']));

function IMap#Equal<U,V>(IMap U V, IMap U V) : bool;

axiom (forall<U,V> m: IMap U V, m': IMap U V ::
  { IMap#Equal(m, m') }
  IMap#Equal(m, m')
     <==> (forall u: U :: IMap#Domain(m)[u] == IMap#Domain(m')[u])
       && (forall u: U ::
        IMap#Domain(m)[u] ==> IMap#Elements(m)[u] == IMap#Elements(m')[u]));

axiom (forall<U,V> m: IMap U V, m': IMap U V ::
  { IMap#Equal(m, m') }
  IMap#Equal(m, m') ==> m == m');

function INTERNAL_add_boogie(x: int, y: int) : int;

axiom (forall x: int, y: int ::
  { INTERNAL_add_boogie(x, y): int }
  INTERNAL_add_boogie(x, y): int == x + y);

function INTERNAL_sub_boogie(x: int, y: int) : int;

axiom (forall x: int, y: int ::
  { INTERNAL_sub_boogie(x, y): int }
  INTERNAL_sub_boogie(x, y): int == x - y);

function INTERNAL_mul_boogie(x: int, y: int) : int;

axiom (forall x: int, y: int ::
  { INTERNAL_mul_boogie(x, y): int }
  INTERNAL_mul_boogie(x, y): int == x * y);

function INTERNAL_div_boogie(x: int, y: int) : int;

axiom (forall x: int, y: int ::
  { INTERNAL_div_boogie(x, y): int }
  INTERNAL_div_boogie(x, y): int == x div y);

function INTERNAL_mod_boogie(x: int, y: int) : int;

axiom (forall x: int, y: int ::
  { INTERNAL_mod_boogie(x, y): int }
  INTERNAL_mod_boogie(x, y): int == x mod y);

function {:never_pattern true} INTERNAL_lt_boogie(x: int, y: int) : bool;

axiom (forall x: int, y: int ::
  {:never_pattern true} { INTERNAL_lt_boogie(x, y): bool }
  INTERNAL_lt_boogie(x, y): bool == (x < y));

function {:never_pattern true} INTERNAL_le_boogie(x: int, y: int) : bool;

axiom (forall x: int, y: int ::
  {:never_pattern true} { INTERNAL_le_boogie(x, y): bool }
  INTERNAL_le_boogie(x, y): bool == (x <= y));

function {:never_pattern true} INTERNAL_gt_boogie(x: int, y: int) : bool;

axiom (forall x: int, y: int ::
  {:never_pattern true} { INTERNAL_gt_boogie(x, y): bool }
  INTERNAL_gt_boogie(x, y): bool == (x > y));

function {:never_pattern true} INTERNAL_ge_boogie(x: int, y: int) : bool;

axiom (forall x: int, y: int ::
  {:never_pattern true} { INTERNAL_ge_boogie(x, y): bool }
  INTERNAL_ge_boogie(x, y): bool == (x >= y));

function Tclass._System.nat() : Ty;

// Tclass._System.nat Tag
axiom Tag(Tclass._System.nat()) == Tagclass._System.nat;

const unique Tagclass._System.nat: TyTag;

// Box/unbox axiom for Tclass._System.nat
axiom (forall bx: Box ::
  { $IsBox(bx, Tclass._System.nat()) }
  $IsBox(bx, Tclass._System.nat())
     ==> $Box($Unbox(bx): int) == bx && $Is($Unbox(bx): int, Tclass._System.nat()));

// _System.nat: subset type $Is
axiom (forall x#0: int ::
  { $Is(x#0, Tclass._System.nat()) }
  $Is(x#0, Tclass._System.nat()) <==> LitInt(0) <= x#0);

// _System.nat: subset type $IsAlloc
axiom (forall x#0: int, $h: Heap ::
  { $IsAlloc(x#0, Tclass._System.nat(), $h) }
  $IsAlloc(x#0, Tclass._System.nat(), $h));

const unique class._System.object: ClassName;

// Tclass._System.object Tag
axiom Tag(Tclass._System.object()) == Tagclass._System.object;

const unique Tagclass._System.object: TyTag;

// Box/unbox axiom for Tclass._System.object
axiom (forall bx: Box ::
  { $IsBox(bx, Tclass._System.object()) }
  $IsBox(bx, Tclass._System.object())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._System.object()));

// object: Class $Is
axiom (forall $o: ref ::
  { $Is($o, Tclass._System.object()) }
  $Is($o, Tclass._System.object()));

// object: Class $IsAlloc
axiom (forall $o: ref, $h: Heap ::
  { $IsAlloc($o, Tclass._System.object(), $h) }
  $IsAlloc($o, Tclass._System.object(), $h) <==> $o == null || read($h, $o, alloc));

function implements$_System.object(Ty) : bool;

const unique class._System.array: ClassName;

function Tclass._System.array(Ty) : Ty;

// Tclass._System.array Tag
axiom (forall #$arg: Ty ::
  { Tclass._System.array(#$arg) }
  Tag(Tclass._System.array(#$arg)) == Tagclass._System.array);

const unique Tagclass._System.array: TyTag;

// Tclass._System.array injectivity 0
axiom (forall #$arg: Ty ::
  { Tclass._System.array(#$arg) }
  Tclass._System.array_0(Tclass._System.array(#$arg)) == #$arg);

function Tclass._System.array_0(Ty) : Ty;

// Box/unbox axiom for Tclass._System.array
axiom (forall #$arg: Ty, bx: Box ::
  { $IsBox(bx, Tclass._System.array(#$arg)) }
  $IsBox(bx, Tclass._System.array(#$arg))
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._System.array(#$arg)));

// array.: Allocation axiom
axiom (forall #$arg: Ty, $i0: int, $h: Heap, $o: ref ::
  { read($h, $o, IndexField($i0)), Tclass._System.array(#$arg) }
  $IsGoodHeap($h)
       && $o != null
       && dtype($o) == Tclass._System.array(#$arg)
       &&
      0 <= $i0
       && $i0 < _System.array.Length($o)
     ==> $IsBox(read($h, $o, IndexField($i0)), #$arg)
       && (read($h, $o, alloc) ==> $IsAllocBox(read($h, $o, IndexField($i0)), #$arg, $h)));

// array: Class $Is
axiom (forall #$arg: Ty, $o: ref ::
  { $Is($o, Tclass._System.array(#$arg)) }
  $Is($o, Tclass._System.array(#$arg))
     <==> $o == null || dtype($o) == Tclass._System.array(#$arg));

// array: Class $IsAlloc
axiom (forall #$arg: Ty, $o: ref, $h: Heap ::
  { $IsAlloc($o, Tclass._System.array(#$arg), $h) }
  $IsAlloc($o, Tclass._System.array(#$arg), $h)
     <==> $o == null || read($h, $o, alloc));

// array.Length: Allocation axiom
axiom (forall #$arg: Ty, $h: Heap, $o: ref ::
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._System.array(#$arg)
     ==> $Is(_System.array.Length($o), TInt)
       && (read($h, $o, alloc) ==> $IsAlloc(_System.array.Length($o), TInt, $h)));

function Tclass._System.___hFunc0(Ty) : Ty;

// Tclass._System.___hFunc0 Tag
axiom (forall #$R: Ty ::
  { Tclass._System.___hFunc0(#$R) }
  Tag(Tclass._System.___hFunc0(#$R)) == Tagclass._System.___hFunc0);

const unique Tagclass._System.___hFunc0: TyTag;

// Tclass._System.___hFunc0 injectivity 0
axiom (forall #$R: Ty ::
  { Tclass._System.___hFunc0(#$R) }
  Tclass._System.___hFunc0_0(Tclass._System.___hFunc0(#$R)) == #$R);

function Tclass._System.___hFunc0_0(Ty) : Ty;

// Box/unbox axiom for Tclass._System.___hFunc0
axiom (forall #$R: Ty, bx: Box ::
  { $IsBox(bx, Tclass._System.___hFunc0(#$R)) }
  $IsBox(bx, Tclass._System.___hFunc0(#$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, Tclass._System.___hFunc0(#$R)));

function Handle0([Heap]Box, [Heap]bool, [Heap]Set Box) : HandleType;

function Apply0(Ty, Heap, HandleType) : Box;

function Requires0(Ty, Heap, HandleType) : bool;

function Reads0(Ty, Heap, HandleType) : Set Box;

axiom (forall t0: Ty, heap: Heap, h: [Heap]Box, r: [Heap]bool, rd: [Heap]Set Box ::
  { Apply0(t0, heap, Handle0(h, r, rd)) }
  Apply0(t0, heap, Handle0(h, r, rd)) == h[heap]);

axiom (forall t0: Ty, heap: Heap, h: [Heap]Box, r: [Heap]bool, rd: [Heap]Set Box ::
  { Requires0(t0, heap, Handle0(h, r, rd)) }
  r[heap] ==> Requires0(t0, heap, Handle0(h, r, rd)));

axiom (forall t0: Ty, heap: Heap, h: [Heap]Box, r: [Heap]bool, rd: [Heap]Set Box, bx: Box ::
  { Reads0(t0, heap, Handle0(h, r, rd))[bx] }
  Reads0(t0, heap, Handle0(h, r, rd))[bx] == rd[heap][bx]);

function {:inline} Requires0#canCall(t0: Ty, heap: Heap, f: HandleType) : bool
{
  true
}

function {:inline} Reads0#canCall(t0: Ty, heap: Heap, f: HandleType) : bool
{
  true
}

// frame axiom for Reads0
axiom (forall t0: Ty, h0: Heap, h1: Heap, f: HandleType ::
  { $HeapSucc(h0, h1), Reads0(t0, h1, f) }
  $HeapSucc(h0, h1)
       &&
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && $Is(f, Tclass._System.___hFunc0(t0))
       && (forall<a> o: ref, fld: Field a ::
        o != null && Reads0(t0, h0, f)[$Box(o)] ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Reads0(t0, h0, f) == Reads0(t0, h1, f));

// frame axiom for Reads0
axiom (forall t0: Ty, h0: Heap, h1: Heap, f: HandleType ::
  { $HeapSucc(h0, h1), Reads0(t0, h1, f) }
  $HeapSucc(h0, h1)
       &&
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && $Is(f, Tclass._System.___hFunc0(t0))
       && (forall<a> o: ref, fld: Field a ::
        o != null && Reads0(t0, h1, f)[$Box(o)] ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Reads0(t0, h0, f) == Reads0(t0, h1, f));

// frame axiom for Requires0
axiom (forall t0: Ty, h0: Heap, h1: Heap, f: HandleType ::
  { $HeapSucc(h0, h1), Requires0(t0, h1, f) }
  $HeapSucc(h0, h1)
       &&
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && $Is(f, Tclass._System.___hFunc0(t0))
       && (forall<a> o: ref, fld: Field a ::
        o != null && Reads0(t0, h0, f)[$Box(o)] ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Requires0(t0, h0, f) == Requires0(t0, h1, f));

// frame axiom for Requires0
axiom (forall t0: Ty, h0: Heap, h1: Heap, f: HandleType ::
  { $HeapSucc(h0, h1), Requires0(t0, h1, f) }
  $HeapSucc(h0, h1)
       &&
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && $Is(f, Tclass._System.___hFunc0(t0))
       && (forall<a> o: ref, fld: Field a ::
        o != null && Reads0(t0, h1, f)[$Box(o)] ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Requires0(t0, h0, f) == Requires0(t0, h1, f));

// frame axiom for Apply0
axiom (forall t0: Ty, h0: Heap, h1: Heap, f: HandleType ::
  { $HeapSucc(h0, h1), Apply0(t0, h1, f) }
  $HeapSucc(h0, h1)
       &&
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && $Is(f, Tclass._System.___hFunc0(t0))
       && (forall<a> o: ref, fld: Field a ::
        o != null && Reads0(t0, h0, f)[$Box(o)] ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Apply0(t0, h0, f) == Apply0(t0, h1, f));

// frame axiom for Apply0
axiom (forall t0: Ty, h0: Heap, h1: Heap, f: HandleType ::
  { $HeapSucc(h0, h1), Apply0(t0, h1, f) }
  $HeapSucc(h0, h1)
       &&
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && $Is(f, Tclass._System.___hFunc0(t0))
       && (forall<a> o: ref, fld: Field a ::
        o != null && Reads0(t0, h1, f)[$Box(o)] ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Apply0(t0, h0, f) == Apply0(t0, h1, f));

// empty-reads property for Reads0
axiom (forall t0: Ty, heap: Heap, f: HandleType ::
  { Reads0(t0, $OneHeap, f), $IsGoodHeap(heap) } { Reads0(t0, heap, f) }
  $IsGoodHeap(heap) && $Is(f, Tclass._System.___hFunc0(t0))
     ==> (Set#Equal(Reads0(t0, $OneHeap, f), Set#Empty(): Set Box)
       <==> Set#Equal(Reads0(t0, heap, f), Set#Empty(): Set Box)));

// empty-reads property for Requires0
axiom (forall t0: Ty, heap: Heap, f: HandleType ::
  { Requires0(t0, $OneHeap, f), $IsGoodHeap(heap) } { Requires0(t0, heap, f) }
  $IsGoodHeap(heap)
       && $Is(f, Tclass._System.___hFunc0(t0))
       && Set#Equal(Reads0(t0, $OneHeap, f), Set#Empty(): Set Box)
     ==> Requires0(t0, $OneHeap, f) == Requires0(t0, heap, f));

axiom (forall f: HandleType, t0: Ty ::
  { $Is(f, Tclass._System.___hFunc0(t0)) }
  $Is(f, Tclass._System.___hFunc0(t0))
     <==> (forall h: Heap ::
      { Apply0(t0, h, f) }
      $IsGoodHeap(h) && Requires0(t0, h, f) ==> $IsBox(Apply0(t0, h, f), t0)));

axiom (forall f: HandleType, t0: Ty, u0: Ty ::
  { $Is(f, Tclass._System.___hFunc0(t0)), $Is(f, Tclass._System.___hFunc0(u0)) }
  $Is(f, Tclass._System.___hFunc0(t0))
       && (forall bx: Box ::
        { $IsBox(bx, t0) } { $IsBox(bx, u0) }
        $IsBox(bx, t0) ==> $IsBox(bx, u0))
     ==> $Is(f, Tclass._System.___hFunc0(u0)));

axiom (forall f: HandleType, t0: Ty, h: Heap ::
  { $IsAlloc(f, Tclass._System.___hFunc0(t0), h) }
  $IsGoodHeap(h)
     ==> ($IsAlloc(f, Tclass._System.___hFunc0(t0), h)
       <==> Requires0(t0, h, f)
         ==> (forall r: ref ::
          { Reads0(t0, h, f)[$Box(r)] }
          r != null && Reads0(t0, h, f)[$Box(r)] ==> read(h, r, alloc))));

axiom (forall f: HandleType, t0: Ty, h: Heap ::
  { $IsAlloc(f, Tclass._System.___hFunc0(t0), h) }
  $IsGoodHeap(h) && $IsAlloc(f, Tclass._System.___hFunc0(t0), h)
     ==>
    Requires0(t0, h, f)
     ==> $IsAllocBox(Apply0(t0, h, f), t0, h));

function Tclass._System.___hPartialFunc0(Ty) : Ty;

// Tclass._System.___hPartialFunc0 Tag
axiom (forall #$R: Ty ::
  { Tclass._System.___hPartialFunc0(#$R) }
  Tag(Tclass._System.___hPartialFunc0(#$R)) == Tagclass._System.___hPartialFunc0);

const unique Tagclass._System.___hPartialFunc0: TyTag;

// Tclass._System.___hPartialFunc0 injectivity 0
axiom (forall #$R: Ty ::
  { Tclass._System.___hPartialFunc0(#$R) }
  Tclass._System.___hPartialFunc0_0(Tclass._System.___hPartialFunc0(#$R)) == #$R);

function Tclass._System.___hPartialFunc0_0(Ty) : Ty;

// Box/unbox axiom for Tclass._System.___hPartialFunc0
axiom (forall #$R: Ty, bx: Box ::
  { $IsBox(bx, Tclass._System.___hPartialFunc0(#$R)) }
  $IsBox(bx, Tclass._System.___hPartialFunc0(#$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, Tclass._System.___hPartialFunc0(#$R)));

// _System._#PartialFunc0: subset type $Is
axiom (forall #$R: Ty, f#0: HandleType ::
  { $Is(f#0, Tclass._System.___hPartialFunc0(#$R)) }
  $Is(f#0, Tclass._System.___hPartialFunc0(#$R))
     <==> $Is(f#0, Tclass._System.___hFunc0(#$R))
       && Set#Equal(Reads0(#$R, $OneHeap, f#0), Set#Empty(): Set Box));

// _System._#PartialFunc0: subset type $IsAlloc
axiom (forall #$R: Ty, f#0: HandleType, $h: Heap ::
  { $IsAlloc(f#0, Tclass._System.___hPartialFunc0(#$R), $h) }
  $IsAlloc(f#0, Tclass._System.___hPartialFunc0(#$R), $h)
     <==> $IsAlloc(f#0, Tclass._System.___hFunc0(#$R), $h));

function Tclass._System.___hTotalFunc0(Ty) : Ty;

// Tclass._System.___hTotalFunc0 Tag
axiom (forall #$R: Ty ::
  { Tclass._System.___hTotalFunc0(#$R) }
  Tag(Tclass._System.___hTotalFunc0(#$R)) == Tagclass._System.___hTotalFunc0);

const unique Tagclass._System.___hTotalFunc0: TyTag;

// Tclass._System.___hTotalFunc0 injectivity 0
axiom (forall #$R: Ty ::
  { Tclass._System.___hTotalFunc0(#$R) }
  Tclass._System.___hTotalFunc0_0(Tclass._System.___hTotalFunc0(#$R)) == #$R);

function Tclass._System.___hTotalFunc0_0(Ty) : Ty;

// Box/unbox axiom for Tclass._System.___hTotalFunc0
axiom (forall #$R: Ty, bx: Box ::
  { $IsBox(bx, Tclass._System.___hTotalFunc0(#$R)) }
  $IsBox(bx, Tclass._System.___hTotalFunc0(#$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, Tclass._System.___hTotalFunc0(#$R)));

// _System._#TotalFunc0: subset type $Is
axiom (forall #$R: Ty, f#0: HandleType ::
  { $Is(f#0, Tclass._System.___hTotalFunc0(#$R)) }
  $Is(f#0, Tclass._System.___hTotalFunc0(#$R))
     <==> $Is(f#0, Tclass._System.___hPartialFunc0(#$R)) && Requires0(#$R, $OneHeap, f#0));

// _System._#TotalFunc0: subset type $IsAlloc
axiom (forall #$R: Ty, f#0: HandleType, $h: Heap ::
  { $IsAlloc(f#0, Tclass._System.___hTotalFunc0(#$R), $h) }
  $IsAlloc(f#0, Tclass._System.___hTotalFunc0(#$R), $h)
     <==> $IsAlloc(f#0, Tclass._System.___hPartialFunc0(#$R), $h));

function Tclass._System.___hFunc1(Ty, Ty) : Ty;

// Tclass._System.___hFunc1 Tag
axiom (forall #$T0: Ty, #$R: Ty ::
  { Tclass._System.___hFunc1(#$T0, #$R) }
  Tag(Tclass._System.___hFunc1(#$T0, #$R)) == Tagclass._System.___hFunc1);

const unique Tagclass._System.___hFunc1: TyTag;

// Tclass._System.___hFunc1 injectivity 0
axiom (forall #$T0: Ty, #$R: Ty ::
  { Tclass._System.___hFunc1(#$T0, #$R) }
  Tclass._System.___hFunc1_0(Tclass._System.___hFunc1(#$T0, #$R)) == #$T0);

function Tclass._System.___hFunc1_0(Ty) : Ty;

// Tclass._System.___hFunc1 injectivity 1
axiom (forall #$T0: Ty, #$R: Ty ::
  { Tclass._System.___hFunc1(#$T0, #$R) }
  Tclass._System.___hFunc1_1(Tclass._System.___hFunc1(#$T0, #$R)) == #$R);

function Tclass._System.___hFunc1_1(Ty) : Ty;

// Box/unbox axiom for Tclass._System.___hFunc1
axiom (forall #$T0: Ty, #$R: Ty, bx: Box ::
  { $IsBox(bx, Tclass._System.___hFunc1(#$T0, #$R)) }
  $IsBox(bx, Tclass._System.___hFunc1(#$T0, #$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, Tclass._System.___hFunc1(#$T0, #$R)));

function Handle1([Heap,Box]Box, [Heap,Box]bool, [Heap,Box]Set Box) : HandleType;

function Apply1(Ty, Ty, Heap, HandleType, Box) : Box;

function Requires1(Ty, Ty, Heap, HandleType, Box) : bool;

function Reads1(Ty, Ty, Heap, HandleType, Box) : Set Box;

axiom (forall t0: Ty,
    t1: Ty,
    heap: Heap,
    h: [Heap,Box]Box,
    r: [Heap,Box]bool,
    rd: [Heap,Box]Set Box,
    bx0: Box ::
  { Apply1(t0, t1, heap, Handle1(h, r, rd), bx0) }
  Apply1(t0, t1, heap, Handle1(h, r, rd), bx0) == h[heap, bx0]);

axiom (forall t0: Ty,
    t1: Ty,
    heap: Heap,
    h: [Heap,Box]Box,
    r: [Heap,Box]bool,
    rd: [Heap,Box]Set Box,
    bx0: Box ::
  { Requires1(t0, t1, heap, Handle1(h, r, rd), bx0) }
  r[heap, bx0] ==> Requires1(t0, t1, heap, Handle1(h, r, rd), bx0));

axiom (forall t0: Ty,
    t1: Ty,
    heap: Heap,
    h: [Heap,Box]Box,
    r: [Heap,Box]bool,
    rd: [Heap,Box]Set Box,
    bx0: Box,
    bx: Box ::
  { Reads1(t0, t1, heap, Handle1(h, r, rd), bx0)[bx] }
  Reads1(t0, t1, heap, Handle1(h, r, rd), bx0)[bx] == rd[heap, bx0][bx]);

function {:inline} Requires1#canCall(t0: Ty, t1: Ty, heap: Heap, f: HandleType, bx0: Box) : bool
{
  true
}

function {:inline} Reads1#canCall(t0: Ty, t1: Ty, heap: Heap, f: HandleType, bx0: Box) : bool
{
  true
}

// frame axiom for Reads1
axiom (forall t0: Ty, t1: Ty, h0: Heap, h1: Heap, f: HandleType, bx0: Box ::
  { $HeapSucc(h0, h1), Reads1(t0, t1, h1, f, bx0) }
  $HeapSucc(h0, h1)
       &&
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       &&
      $IsBox(bx0, t0)
       && $Is(f, Tclass._System.___hFunc1(t0, t1))
       && (forall<a> o: ref, fld: Field a ::
        o != null && Reads1(t0, t1, h0, f, bx0)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Reads1(t0, t1, h0, f, bx0) == Reads1(t0, t1, h1, f, bx0));

// frame axiom for Reads1
axiom (forall t0: Ty, t1: Ty, h0: Heap, h1: Heap, f: HandleType, bx0: Box ::
  { $HeapSucc(h0, h1), Reads1(t0, t1, h1, f, bx0) }
  $HeapSucc(h0, h1)
       &&
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       &&
      $IsBox(bx0, t0)
       && $Is(f, Tclass._System.___hFunc1(t0, t1))
       && (forall<a> o: ref, fld: Field a ::
        o != null && Reads1(t0, t1, h1, f, bx0)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Reads1(t0, t1, h0, f, bx0) == Reads1(t0, t1, h1, f, bx0));

// frame axiom for Requires1
axiom (forall t0: Ty, t1: Ty, h0: Heap, h1: Heap, f: HandleType, bx0: Box ::
  { $HeapSucc(h0, h1), Requires1(t0, t1, h1, f, bx0) }
  $HeapSucc(h0, h1)
       &&
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       &&
      $IsBox(bx0, t0)
       && $Is(f, Tclass._System.___hFunc1(t0, t1))
       && (forall<a> o: ref, fld: Field a ::
        o != null && Reads1(t0, t1, h0, f, bx0)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Requires1(t0, t1, h0, f, bx0) == Requires1(t0, t1, h1, f, bx0));

// frame axiom for Requires1
axiom (forall t0: Ty, t1: Ty, h0: Heap, h1: Heap, f: HandleType, bx0: Box ::
  { $HeapSucc(h0, h1), Requires1(t0, t1, h1, f, bx0) }
  $HeapSucc(h0, h1)
       &&
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       &&
      $IsBox(bx0, t0)
       && $Is(f, Tclass._System.___hFunc1(t0, t1))
       && (forall<a> o: ref, fld: Field a ::
        o != null && Reads1(t0, t1, h1, f, bx0)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Requires1(t0, t1, h0, f, bx0) == Requires1(t0, t1, h1, f, bx0));

// frame axiom for Apply1
axiom (forall t0: Ty, t1: Ty, h0: Heap, h1: Heap, f: HandleType, bx0: Box ::
  { $HeapSucc(h0, h1), Apply1(t0, t1, h1, f, bx0) }
  $HeapSucc(h0, h1)
       &&
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       &&
      $IsBox(bx0, t0)
       && $Is(f, Tclass._System.___hFunc1(t0, t1))
       && (forall<a> o: ref, fld: Field a ::
        o != null && Reads1(t0, t1, h0, f, bx0)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Apply1(t0, t1, h0, f, bx0) == Apply1(t0, t1, h1, f, bx0));

// frame axiom for Apply1
axiom (forall t0: Ty, t1: Ty, h0: Heap, h1: Heap, f: HandleType, bx0: Box ::
  { $HeapSucc(h0, h1), Apply1(t0, t1, h1, f, bx0) }
  $HeapSucc(h0, h1)
       &&
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       &&
      $IsBox(bx0, t0)
       && $Is(f, Tclass._System.___hFunc1(t0, t1))
       && (forall<a> o: ref, fld: Field a ::
        o != null && Reads1(t0, t1, h1, f, bx0)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Apply1(t0, t1, h0, f, bx0) == Apply1(t0, t1, h1, f, bx0));

// empty-reads property for Reads1
axiom (forall t0: Ty, t1: Ty, heap: Heap, f: HandleType, bx0: Box ::
  { Reads1(t0, t1, $OneHeap, f, bx0), $IsGoodHeap(heap) }
    { Reads1(t0, t1, heap, f, bx0) }
  $IsGoodHeap(heap) && $IsBox(bx0, t0) && $Is(f, Tclass._System.___hFunc1(t0, t1))
     ==> (Set#Equal(Reads1(t0, t1, $OneHeap, f, bx0), Set#Empty(): Set Box)
       <==> Set#Equal(Reads1(t0, t1, heap, f, bx0), Set#Empty(): Set Box)));

// empty-reads property for Requires1
axiom (forall t0: Ty, t1: Ty, heap: Heap, f: HandleType, bx0: Box ::
  { Requires1(t0, t1, $OneHeap, f, bx0), $IsGoodHeap(heap) }
    { Requires1(t0, t1, heap, f, bx0) }
  $IsGoodHeap(heap)
       &&
      $IsBox(bx0, t0)
       && $Is(f, Tclass._System.___hFunc1(t0, t1))
       && Set#Equal(Reads1(t0, t1, $OneHeap, f, bx0), Set#Empty(): Set Box)
     ==> Requires1(t0, t1, $OneHeap, f, bx0) == Requires1(t0, t1, heap, f, bx0));

axiom (forall f: HandleType, t0: Ty, t1: Ty ::
  { $Is(f, Tclass._System.___hFunc1(t0, t1)) }
  $Is(f, Tclass._System.___hFunc1(t0, t1))
     <==> (forall h: Heap, bx0: Box ::
      { Apply1(t0, t1, h, f, bx0) }
      $IsGoodHeap(h) && $IsBox(bx0, t0) && Requires1(t0, t1, h, f, bx0)
         ==> $IsBox(Apply1(t0, t1, h, f, bx0), t1)));

axiom (forall f: HandleType, t0: Ty, t1: Ty, u0: Ty, u1: Ty ::
  { $Is(f, Tclass._System.___hFunc1(t0, t1)), $Is(f, Tclass._System.___hFunc1(u0, u1)) }
  $Is(f, Tclass._System.___hFunc1(t0, t1))
       && (forall bx: Box ::
        { $IsBox(bx, u0) } { $IsBox(bx, t0) }
        $IsBox(bx, u0) ==> $IsBox(bx, t0))
       && (forall bx: Box ::
        { $IsBox(bx, t1) } { $IsBox(bx, u1) }
        $IsBox(bx, t1) ==> $IsBox(bx, u1))
     ==> $Is(f, Tclass._System.___hFunc1(u0, u1)));

axiom (forall f: HandleType, t0: Ty, t1: Ty, h: Heap ::
  { $IsAlloc(f, Tclass._System.___hFunc1(t0, t1), h) }
  $IsGoodHeap(h)
     ==> ($IsAlloc(f, Tclass._System.___hFunc1(t0, t1), h)
       <==> (forall bx0: Box ::
        { Apply1(t0, t1, h, f, bx0) } { Reads1(t0, t1, h, f, bx0) }
        $IsBox(bx0, t0) && $IsAllocBox(bx0, t0, h) && Requires1(t0, t1, h, f, bx0)
           ==> (forall r: ref ::
            { Reads1(t0, t1, h, f, bx0)[$Box(r)] }
            r != null && Reads1(t0, t1, h, f, bx0)[$Box(r)] ==> read(h, r, alloc)))));

axiom (forall f: HandleType, t0: Ty, t1: Ty, h: Heap ::
  { $IsAlloc(f, Tclass._System.___hFunc1(t0, t1), h) }
  $IsGoodHeap(h) && $IsAlloc(f, Tclass._System.___hFunc1(t0, t1), h)
     ==> (forall bx0: Box ::
      { Apply1(t0, t1, h, f, bx0) }
      $IsAllocBox(bx0, t0, h) && Requires1(t0, t1, h, f, bx0)
         ==> $IsAllocBox(Apply1(t0, t1, h, f, bx0), t1, h)));

function Tclass._System.___hPartialFunc1(Ty, Ty) : Ty;

// Tclass._System.___hPartialFunc1 Tag
axiom (forall #$T0: Ty, #$R: Ty ::
  { Tclass._System.___hPartialFunc1(#$T0, #$R) }
  Tag(Tclass._System.___hPartialFunc1(#$T0, #$R))
     == Tagclass._System.___hPartialFunc1);

const unique Tagclass._System.___hPartialFunc1: TyTag;

// Tclass._System.___hPartialFunc1 injectivity 0
axiom (forall #$T0: Ty, #$R: Ty ::
  { Tclass._System.___hPartialFunc1(#$T0, #$R) }
  Tclass._System.___hPartialFunc1_0(Tclass._System.___hPartialFunc1(#$T0, #$R))
     == #$T0);

function Tclass._System.___hPartialFunc1_0(Ty) : Ty;

// Tclass._System.___hPartialFunc1 injectivity 1
axiom (forall #$T0: Ty, #$R: Ty ::
  { Tclass._System.___hPartialFunc1(#$T0, #$R) }
  Tclass._System.___hPartialFunc1_1(Tclass._System.___hPartialFunc1(#$T0, #$R))
     == #$R);

function Tclass._System.___hPartialFunc1_1(Ty) : Ty;

// Box/unbox axiom for Tclass._System.___hPartialFunc1
axiom (forall #$T0: Ty, #$R: Ty, bx: Box ::
  { $IsBox(bx, Tclass._System.___hPartialFunc1(#$T0, #$R)) }
  $IsBox(bx, Tclass._System.___hPartialFunc1(#$T0, #$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, Tclass._System.___hPartialFunc1(#$T0, #$R)));

// _System._#PartialFunc1: subset type $Is
axiom (forall #$T0: Ty, #$R: Ty, f#0: HandleType ::
  { $Is(f#0, Tclass._System.___hPartialFunc1(#$T0, #$R)) }
  $Is(f#0, Tclass._System.___hPartialFunc1(#$T0, #$R))
     <==> $Is(f#0, Tclass._System.___hFunc1(#$T0, #$R))
       && (forall x0#0: Box ::
        $IsBox(x0#0, #$T0)
           ==> Set#Equal(Reads1(#$T0, #$R, $OneHeap, f#0, x0#0), Set#Empty(): Set Box)));

// _System._#PartialFunc1: subset type $IsAlloc
axiom (forall #$T0: Ty, #$R: Ty, f#0: HandleType, $h: Heap ::
  { $IsAlloc(f#0, Tclass._System.___hPartialFunc1(#$T0, #$R), $h) }
  $IsAlloc(f#0, Tclass._System.___hPartialFunc1(#$T0, #$R), $h)
     <==> $IsAlloc(f#0, Tclass._System.___hFunc1(#$T0, #$R), $h));

function Tclass._System.___hTotalFunc1(Ty, Ty) : Ty;

// Tclass._System.___hTotalFunc1 Tag
axiom (forall #$T0: Ty, #$R: Ty ::
  { Tclass._System.___hTotalFunc1(#$T0, #$R) }
  Tag(Tclass._System.___hTotalFunc1(#$T0, #$R)) == Tagclass._System.___hTotalFunc1);

const unique Tagclass._System.___hTotalFunc1: TyTag;

// Tclass._System.___hTotalFunc1 injectivity 0
axiom (forall #$T0: Ty, #$R: Ty ::
  { Tclass._System.___hTotalFunc1(#$T0, #$R) }
  Tclass._System.___hTotalFunc1_0(Tclass._System.___hTotalFunc1(#$T0, #$R))
     == #$T0);

function Tclass._System.___hTotalFunc1_0(Ty) : Ty;

// Tclass._System.___hTotalFunc1 injectivity 1
axiom (forall #$T0: Ty, #$R: Ty ::
  { Tclass._System.___hTotalFunc1(#$T0, #$R) }
  Tclass._System.___hTotalFunc1_1(Tclass._System.___hTotalFunc1(#$T0, #$R)) == #$R);

function Tclass._System.___hTotalFunc1_1(Ty) : Ty;

// Box/unbox axiom for Tclass._System.___hTotalFunc1
axiom (forall #$T0: Ty, #$R: Ty, bx: Box ::
  { $IsBox(bx, Tclass._System.___hTotalFunc1(#$T0, #$R)) }
  $IsBox(bx, Tclass._System.___hTotalFunc1(#$T0, #$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, Tclass._System.___hTotalFunc1(#$T0, #$R)));

// _System._#TotalFunc1: subset type $Is
axiom (forall #$T0: Ty, #$R: Ty, f#0: HandleType ::
  { $Is(f#0, Tclass._System.___hTotalFunc1(#$T0, #$R)) }
  $Is(f#0, Tclass._System.___hTotalFunc1(#$T0, #$R))
     <==> $Is(f#0, Tclass._System.___hPartialFunc1(#$T0, #$R))
       && (forall x0#0: Box ::
        $IsBox(x0#0, #$T0) ==> Requires1(#$T0, #$R, $OneHeap, f#0, x0#0)));

// _System._#TotalFunc1: subset type $IsAlloc
axiom (forall #$T0: Ty, #$R: Ty, f#0: HandleType, $h: Heap ::
  { $IsAlloc(f#0, Tclass._System.___hTotalFunc1(#$T0, #$R), $h) }
  $IsAlloc(f#0, Tclass._System.___hTotalFunc1(#$T0, #$R), $h)
     <==> $IsAlloc(f#0, Tclass._System.___hPartialFunc1(#$T0, #$R), $h));

function Tclass._System.___hFunc3(Ty, Ty, Ty, Ty) : Ty;

// Tclass._System.___hFunc3 Tag
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty ::
  { Tclass._System.___hFunc3(#$T0, #$T1, #$T2, #$R) }
  Tag(Tclass._System.___hFunc3(#$T0, #$T1, #$T2, #$R))
     == Tagclass._System.___hFunc3);

const unique Tagclass._System.___hFunc3: TyTag;

// Tclass._System.___hFunc3 injectivity 0
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty ::
  { Tclass._System.___hFunc3(#$T0, #$T1, #$T2, #$R) }
  Tclass._System.___hFunc3_0(Tclass._System.___hFunc3(#$T0, #$T1, #$T2, #$R))
     == #$T0);

function Tclass._System.___hFunc3_0(Ty) : Ty;

// Tclass._System.___hFunc3 injectivity 1
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty ::
  { Tclass._System.___hFunc3(#$T0, #$T1, #$T2, #$R) }
  Tclass._System.___hFunc3_1(Tclass._System.___hFunc3(#$T0, #$T1, #$T2, #$R))
     == #$T1);

function Tclass._System.___hFunc3_1(Ty) : Ty;

// Tclass._System.___hFunc3 injectivity 2
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty ::
  { Tclass._System.___hFunc3(#$T0, #$T1, #$T2, #$R) }
  Tclass._System.___hFunc3_2(Tclass._System.___hFunc3(#$T0, #$T1, #$T2, #$R))
     == #$T2);

function Tclass._System.___hFunc3_2(Ty) : Ty;

// Tclass._System.___hFunc3 injectivity 3
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty ::
  { Tclass._System.___hFunc3(#$T0, #$T1, #$T2, #$R) }
  Tclass._System.___hFunc3_3(Tclass._System.___hFunc3(#$T0, #$T1, #$T2, #$R))
     == #$R);

function Tclass._System.___hFunc3_3(Ty) : Ty;

// Box/unbox axiom for Tclass._System.___hFunc3
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty, bx: Box ::
  { $IsBox(bx, Tclass._System.___hFunc3(#$T0, #$T1, #$T2, #$R)) }
  $IsBox(bx, Tclass._System.___hFunc3(#$T0, #$T1, #$T2, #$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, Tclass._System.___hFunc3(#$T0, #$T1, #$T2, #$R)));

function Handle3([Heap,Box,Box,Box]Box, [Heap,Box,Box,Box]bool, [Heap,Box,Box,Box]Set Box)
   : HandleType;

function Apply3(Ty, Ty, Ty, Ty, Heap, HandleType, Box, Box, Box) : Box;

function Requires3(Ty, Ty, Ty, Ty, Heap, HandleType, Box, Box, Box) : bool;

function Reads3(Ty, Ty, Ty, Ty, Heap, HandleType, Box, Box, Box) : Set Box;

axiom (forall t0: Ty,
    t1: Ty,
    t2: Ty,
    t3: Ty,
    heap: Heap,
    h: [Heap,Box,Box,Box]Box,
    r: [Heap,Box,Box,Box]bool,
    rd: [Heap,Box,Box,Box]Set Box,
    bx0: Box,
    bx1: Box,
    bx2: Box ::
  { Apply3(t0, t1, t2, t3, heap, Handle3(h, r, rd), bx0, bx1, bx2) }
  Apply3(t0, t1, t2, t3, heap, Handle3(h, r, rd), bx0, bx1, bx2)
     == h[heap, bx0, bx1, bx2]);

axiom (forall t0: Ty,
    t1: Ty,
    t2: Ty,
    t3: Ty,
    heap: Heap,
    h: [Heap,Box,Box,Box]Box,
    r: [Heap,Box,Box,Box]bool,
    rd: [Heap,Box,Box,Box]Set Box,
    bx0: Box,
    bx1: Box,
    bx2: Box ::
  { Requires3(t0, t1, t2, t3, heap, Handle3(h, r, rd), bx0, bx1, bx2) }
  r[heap, bx0, bx1, bx2]
     ==> Requires3(t0, t1, t2, t3, heap, Handle3(h, r, rd), bx0, bx1, bx2));

axiom (forall t0: Ty,
    t1: Ty,
    t2: Ty,
    t3: Ty,
    heap: Heap,
    h: [Heap,Box,Box,Box]Box,
    r: [Heap,Box,Box,Box]bool,
    rd: [Heap,Box,Box,Box]Set Box,
    bx0: Box,
    bx1: Box,
    bx2: Box,
    bx: Box ::
  { Reads3(t0, t1, t2, t3, heap, Handle3(h, r, rd), bx0, bx1, bx2)[bx] }
  Reads3(t0, t1, t2, t3, heap, Handle3(h, r, rd), bx0, bx1, bx2)[bx]
     == rd[heap, bx0, bx1, bx2][bx]);

function {:inline} Requires3#canCall(t0: Ty,
    t1: Ty,
    t2: Ty,
    t3: Ty,
    heap: Heap,
    f: HandleType,
    bx0: Box,
    bx1: Box,
    bx2: Box)
   : bool
{
  true
}

function {:inline} Reads3#canCall(t0: Ty,
    t1: Ty,
    t2: Ty,
    t3: Ty,
    heap: Heap,
    f: HandleType,
    bx0: Box,
    bx1: Box,
    bx2: Box)
   : bool
{
  true
}

// frame axiom for Reads3
axiom (forall t0: Ty,
    t1: Ty,
    t2: Ty,
    t3: Ty,
    h0: Heap,
    h1: Heap,
    f: HandleType,
    bx0: Box,
    bx1: Box,
    bx2: Box ::
  { $HeapSucc(h0, h1), Reads3(t0, t1, t2, t3, h1, f, bx0, bx1, bx2) }
  $HeapSucc(h0, h1)
       &&
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       &&
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $Is(f, Tclass._System.___hFunc3(t0, t1, t2, t3))
       && (forall<a> o: ref, fld: Field a ::
        o != null && Reads3(t0, t1, t2, t3, h0, f, bx0, bx1, bx2)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Reads3(t0, t1, t2, t3, h0, f, bx0, bx1, bx2)
       == Reads3(t0, t1, t2, t3, h1, f, bx0, bx1, bx2));

// frame axiom for Reads3
axiom (forall t0: Ty,
    t1: Ty,
    t2: Ty,
    t3: Ty,
    h0: Heap,
    h1: Heap,
    f: HandleType,
    bx0: Box,
    bx1: Box,
    bx2: Box ::
  { $HeapSucc(h0, h1), Reads3(t0, t1, t2, t3, h1, f, bx0, bx1, bx2) }
  $HeapSucc(h0, h1)
       &&
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       &&
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $Is(f, Tclass._System.___hFunc3(t0, t1, t2, t3))
       && (forall<a> o: ref, fld: Field a ::
        o != null && Reads3(t0, t1, t2, t3, h1, f, bx0, bx1, bx2)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Reads3(t0, t1, t2, t3, h0, f, bx0, bx1, bx2)
       == Reads3(t0, t1, t2, t3, h1, f, bx0, bx1, bx2));

// frame axiom for Requires3
axiom (forall t0: Ty,
    t1: Ty,
    t2: Ty,
    t3: Ty,
    h0: Heap,
    h1: Heap,
    f: HandleType,
    bx0: Box,
    bx1: Box,
    bx2: Box ::
  { $HeapSucc(h0, h1), Requires3(t0, t1, t2, t3, h1, f, bx0, bx1, bx2) }
  $HeapSucc(h0, h1)
       &&
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       &&
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $Is(f, Tclass._System.___hFunc3(t0, t1, t2, t3))
       && (forall<a> o: ref, fld: Field a ::
        o != null && Reads3(t0, t1, t2, t3, h0, f, bx0, bx1, bx2)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Requires3(t0, t1, t2, t3, h0, f, bx0, bx1, bx2)
       == Requires3(t0, t1, t2, t3, h1, f, bx0, bx1, bx2));

// frame axiom for Requires3
axiom (forall t0: Ty,
    t1: Ty,
    t2: Ty,
    t3: Ty,
    h0: Heap,
    h1: Heap,
    f: HandleType,
    bx0: Box,
    bx1: Box,
    bx2: Box ::
  { $HeapSucc(h0, h1), Requires3(t0, t1, t2, t3, h1, f, bx0, bx1, bx2) }
  $HeapSucc(h0, h1)
       &&
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       &&
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $Is(f, Tclass._System.___hFunc3(t0, t1, t2, t3))
       && (forall<a> o: ref, fld: Field a ::
        o != null && Reads3(t0, t1, t2, t3, h1, f, bx0, bx1, bx2)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Requires3(t0, t1, t2, t3, h0, f, bx0, bx1, bx2)
       == Requires3(t0, t1, t2, t3, h1, f, bx0, bx1, bx2));

// frame axiom for Apply3
axiom (forall t0: Ty,
    t1: Ty,
    t2: Ty,
    t3: Ty,
    h0: Heap,
    h1: Heap,
    f: HandleType,
    bx0: Box,
    bx1: Box,
    bx2: Box ::
  { $HeapSucc(h0, h1), Apply3(t0, t1, t2, t3, h1, f, bx0, bx1, bx2) }
  $HeapSucc(h0, h1)
       &&
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       &&
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $Is(f, Tclass._System.___hFunc3(t0, t1, t2, t3))
       && (forall<a> o: ref, fld: Field a ::
        o != null && Reads3(t0, t1, t2, t3, h0, f, bx0, bx1, bx2)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Apply3(t0, t1, t2, t3, h0, f, bx0, bx1, bx2)
       == Apply3(t0, t1, t2, t3, h1, f, bx0, bx1, bx2));

// frame axiom for Apply3
axiom (forall t0: Ty,
    t1: Ty,
    t2: Ty,
    t3: Ty,
    h0: Heap,
    h1: Heap,
    f: HandleType,
    bx0: Box,
    bx1: Box,
    bx2: Box ::
  { $HeapSucc(h0, h1), Apply3(t0, t1, t2, t3, h1, f, bx0, bx1, bx2) }
  $HeapSucc(h0, h1)
       &&
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       &&
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $Is(f, Tclass._System.___hFunc3(t0, t1, t2, t3))
       && (forall<a> o: ref, fld: Field a ::
        o != null && Reads3(t0, t1, t2, t3, h1, f, bx0, bx1, bx2)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Apply3(t0, t1, t2, t3, h0, f, bx0, bx1, bx2)
       == Apply3(t0, t1, t2, t3, h1, f, bx0, bx1, bx2));

// empty-reads property for Reads3
axiom (forall t0: Ty,
    t1: Ty,
    t2: Ty,
    t3: Ty,
    heap: Heap,
    f: HandleType,
    bx0: Box,
    bx1: Box,
    bx2: Box ::
  { Reads3(t0, t1, t2, t3, $OneHeap, f, bx0, bx1, bx2), $IsGoodHeap(heap) }
    { Reads3(t0, t1, t2, t3, heap, f, bx0, bx1, bx2) }
  $IsGoodHeap(heap)
       &&
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $Is(f, Tclass._System.___hFunc3(t0, t1, t2, t3))
     ==> (Set#Equal(Reads3(t0, t1, t2, t3, $OneHeap, f, bx0, bx1, bx2), Set#Empty(): Set Box)
       <==> Set#Equal(Reads3(t0, t1, t2, t3, heap, f, bx0, bx1, bx2), Set#Empty(): Set Box)));

// empty-reads property for Requires3
axiom (forall t0: Ty,
    t1: Ty,
    t2: Ty,
    t3: Ty,
    heap: Heap,
    f: HandleType,
    bx0: Box,
    bx1: Box,
    bx2: Box ::
  { Requires3(t0, t1, t2, t3, $OneHeap, f, bx0, bx1, bx2), $IsGoodHeap(heap) }
    { Requires3(t0, t1, t2, t3, heap, f, bx0, bx1, bx2) }
  $IsGoodHeap(heap)
       &&
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $Is(f, Tclass._System.___hFunc3(t0, t1, t2, t3))
       && Set#Equal(Reads3(t0, t1, t2, t3, $OneHeap, f, bx0, bx1, bx2), Set#Empty(): Set Box)
     ==> Requires3(t0, t1, t2, t3, $OneHeap, f, bx0, bx1, bx2)
       == Requires3(t0, t1, t2, t3, heap, f, bx0, bx1, bx2));

axiom (forall f: HandleType, t0: Ty, t1: Ty, t2: Ty, t3: Ty ::
  { $Is(f, Tclass._System.___hFunc3(t0, t1, t2, t3)) }
  $Is(f, Tclass._System.___hFunc3(t0, t1, t2, t3))
     <==> (forall h: Heap, bx0: Box, bx1: Box, bx2: Box ::
      { Apply3(t0, t1, t2, t3, h, f, bx0, bx1, bx2) }
      $IsGoodHeap(h)
           &&
          $IsBox(bx0, t0)
           && $IsBox(bx1, t1)
           && $IsBox(bx2, t2)
           && Requires3(t0, t1, t2, t3, h, f, bx0, bx1, bx2)
         ==> $IsBox(Apply3(t0, t1, t2, t3, h, f, bx0, bx1, bx2), t3)));

axiom (forall f: HandleType, t0: Ty, t1: Ty, t2: Ty, t3: Ty, u0: Ty, u1: Ty, u2: Ty, u3: Ty ::
  { $Is(f, Tclass._System.___hFunc3(t0, t1, t2, t3)), $Is(f, Tclass._System.___hFunc3(u0, u1, u2, u3)) }
  $Is(f, Tclass._System.___hFunc3(t0, t1, t2, t3))
       && (forall bx: Box ::
        { $IsBox(bx, u0) } { $IsBox(bx, t0) }
        $IsBox(bx, u0) ==> $IsBox(bx, t0))
       && (forall bx: Box ::
        { $IsBox(bx, u1) } { $IsBox(bx, t1) }
        $IsBox(bx, u1) ==> $IsBox(bx, t1))
       && (forall bx: Box ::
        { $IsBox(bx, u2) } { $IsBox(bx, t2) }
        $IsBox(bx, u2) ==> $IsBox(bx, t2))
       && (forall bx: Box ::
        { $IsBox(bx, t3) } { $IsBox(bx, u3) }
        $IsBox(bx, t3) ==> $IsBox(bx, u3))
     ==> $Is(f, Tclass._System.___hFunc3(u0, u1, u2, u3)));

axiom (forall f: HandleType, t0: Ty, t1: Ty, t2: Ty, t3: Ty, h: Heap ::
  { $IsAlloc(f, Tclass._System.___hFunc3(t0, t1, t2, t3), h) }
  $IsGoodHeap(h)
     ==> ($IsAlloc(f, Tclass._System.___hFunc3(t0, t1, t2, t3), h)
       <==> (forall bx0: Box, bx1: Box, bx2: Box ::
        { Apply3(t0, t1, t2, t3, h, f, bx0, bx1, bx2) }
          { Reads3(t0, t1, t2, t3, h, f, bx0, bx1, bx2) }
        $IsBox(bx0, t0)
             && $IsAllocBox(bx0, t0, h)
             &&
            $IsBox(bx1, t1)
             && $IsAllocBox(bx1, t1, h)
             &&
            $IsBox(bx2, t2)
             && $IsAllocBox(bx2, t2, h)
             && Requires3(t0, t1, t2, t3, h, f, bx0, bx1, bx2)
           ==> (forall r: ref ::
            { Reads3(t0, t1, t2, t3, h, f, bx0, bx1, bx2)[$Box(r)] }
            r != null && Reads3(t0, t1, t2, t3, h, f, bx0, bx1, bx2)[$Box(r)]
               ==> read(h, r, alloc)))));

axiom (forall f: HandleType, t0: Ty, t1: Ty, t2: Ty, t3: Ty, h: Heap ::
  { $IsAlloc(f, Tclass._System.___hFunc3(t0, t1, t2, t3), h) }
  $IsGoodHeap(h) && $IsAlloc(f, Tclass._System.___hFunc3(t0, t1, t2, t3), h)
     ==> (forall bx0: Box, bx1: Box, bx2: Box ::
      { Apply3(t0, t1, t2, t3, h, f, bx0, bx1, bx2) }
      $IsAllocBox(bx0, t0, h)
           && $IsAllocBox(bx1, t1, h)
           && $IsAllocBox(bx2, t2, h)
           && Requires3(t0, t1, t2, t3, h, f, bx0, bx1, bx2)
         ==> $IsAllocBox(Apply3(t0, t1, t2, t3, h, f, bx0, bx1, bx2), t3, h)));

function Tclass._System.___hPartialFunc3(Ty, Ty, Ty, Ty) : Ty;

// Tclass._System.___hPartialFunc3 Tag
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty ::
  { Tclass._System.___hPartialFunc3(#$T0, #$T1, #$T2, #$R) }
  Tag(Tclass._System.___hPartialFunc3(#$T0, #$T1, #$T2, #$R))
     == Tagclass._System.___hPartialFunc3);

const unique Tagclass._System.___hPartialFunc3: TyTag;

// Tclass._System.___hPartialFunc3 injectivity 0
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty ::
  { Tclass._System.___hPartialFunc3(#$T0, #$T1, #$T2, #$R) }
  Tclass._System.___hPartialFunc3_0(Tclass._System.___hPartialFunc3(#$T0, #$T1, #$T2, #$R))
     == #$T0);

function Tclass._System.___hPartialFunc3_0(Ty) : Ty;

// Tclass._System.___hPartialFunc3 injectivity 1
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty ::
  { Tclass._System.___hPartialFunc3(#$T0, #$T1, #$T2, #$R) }
  Tclass._System.___hPartialFunc3_1(Tclass._System.___hPartialFunc3(#$T0, #$T1, #$T2, #$R))
     == #$T1);

function Tclass._System.___hPartialFunc3_1(Ty) : Ty;

// Tclass._System.___hPartialFunc3 injectivity 2
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty ::
  { Tclass._System.___hPartialFunc3(#$T0, #$T1, #$T2, #$R) }
  Tclass._System.___hPartialFunc3_2(Tclass._System.___hPartialFunc3(#$T0, #$T1, #$T2, #$R))
     == #$T2);

function Tclass._System.___hPartialFunc3_2(Ty) : Ty;

// Tclass._System.___hPartialFunc3 injectivity 3
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty ::
  { Tclass._System.___hPartialFunc3(#$T0, #$T1, #$T2, #$R) }
  Tclass._System.___hPartialFunc3_3(Tclass._System.___hPartialFunc3(#$T0, #$T1, #$T2, #$R))
     == #$R);

function Tclass._System.___hPartialFunc3_3(Ty) : Ty;

// Box/unbox axiom for Tclass._System.___hPartialFunc3
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty, bx: Box ::
  { $IsBox(bx, Tclass._System.___hPartialFunc3(#$T0, #$T1, #$T2, #$R)) }
  $IsBox(bx, Tclass._System.___hPartialFunc3(#$T0, #$T1, #$T2, #$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, Tclass._System.___hPartialFunc3(#$T0, #$T1, #$T2, #$R)));

// _System._#PartialFunc3: subset type $Is
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty, f#0: HandleType ::
  { $Is(f#0, Tclass._System.___hPartialFunc3(#$T0, #$T1, #$T2, #$R)) }
  $Is(f#0, Tclass._System.___hPartialFunc3(#$T0, #$T1, #$T2, #$R))
     <==> $Is(f#0, Tclass._System.___hFunc3(#$T0, #$T1, #$T2, #$R))
       && (forall x0#0: Box, x1#0: Box, x2#0: Box ::
        $IsBox(x0#0, #$T0) && $IsBox(x1#0, #$T1) && $IsBox(x2#0, #$T2)
           ==> Set#Equal(Reads3(#$T0, #$T1, #$T2, #$R, $OneHeap, f#0, x0#0, x1#0, x2#0),
            Set#Empty(): Set Box)));

// _System._#PartialFunc3: subset type $IsAlloc
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty, f#0: HandleType, $h: Heap ::
  { $IsAlloc(f#0, Tclass._System.___hPartialFunc3(#$T0, #$T1, #$T2, #$R), $h) }
  $IsAlloc(f#0, Tclass._System.___hPartialFunc3(#$T0, #$T1, #$T2, #$R), $h)
     <==> $IsAlloc(f#0, Tclass._System.___hFunc3(#$T0, #$T1, #$T2, #$R), $h));

function Tclass._System.___hTotalFunc3(Ty, Ty, Ty, Ty) : Ty;

// Tclass._System.___hTotalFunc3 Tag
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty ::
  { Tclass._System.___hTotalFunc3(#$T0, #$T1, #$T2, #$R) }
  Tag(Tclass._System.___hTotalFunc3(#$T0, #$T1, #$T2, #$R))
     == Tagclass._System.___hTotalFunc3);

const unique Tagclass._System.___hTotalFunc3: TyTag;

// Tclass._System.___hTotalFunc3 injectivity 0
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty ::
  { Tclass._System.___hTotalFunc3(#$T0, #$T1, #$T2, #$R) }
  Tclass._System.___hTotalFunc3_0(Tclass._System.___hTotalFunc3(#$T0, #$T1, #$T2, #$R))
     == #$T0);

function Tclass._System.___hTotalFunc3_0(Ty) : Ty;

// Tclass._System.___hTotalFunc3 injectivity 1
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty ::
  { Tclass._System.___hTotalFunc3(#$T0, #$T1, #$T2, #$R) }
  Tclass._System.___hTotalFunc3_1(Tclass._System.___hTotalFunc3(#$T0, #$T1, #$T2, #$R))
     == #$T1);

function Tclass._System.___hTotalFunc3_1(Ty) : Ty;

// Tclass._System.___hTotalFunc3 injectivity 2
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty ::
  { Tclass._System.___hTotalFunc3(#$T0, #$T1, #$T2, #$R) }
  Tclass._System.___hTotalFunc3_2(Tclass._System.___hTotalFunc3(#$T0, #$T1, #$T2, #$R))
     == #$T2);

function Tclass._System.___hTotalFunc3_2(Ty) : Ty;

// Tclass._System.___hTotalFunc3 injectivity 3
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty ::
  { Tclass._System.___hTotalFunc3(#$T0, #$T1, #$T2, #$R) }
  Tclass._System.___hTotalFunc3_3(Tclass._System.___hTotalFunc3(#$T0, #$T1, #$T2, #$R))
     == #$R);

function Tclass._System.___hTotalFunc3_3(Ty) : Ty;

// Box/unbox axiom for Tclass._System.___hTotalFunc3
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty, bx: Box ::
  { $IsBox(bx, Tclass._System.___hTotalFunc3(#$T0, #$T1, #$T2, #$R)) }
  $IsBox(bx, Tclass._System.___hTotalFunc3(#$T0, #$T1, #$T2, #$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, Tclass._System.___hTotalFunc3(#$T0, #$T1, #$T2, #$R)));

// _System._#TotalFunc3: subset type $Is
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty, f#0: HandleType ::
  { $Is(f#0, Tclass._System.___hTotalFunc3(#$T0, #$T1, #$T2, #$R)) }
  $Is(f#0, Tclass._System.___hTotalFunc3(#$T0, #$T1, #$T2, #$R))
     <==> $Is(f#0, Tclass._System.___hPartialFunc3(#$T0, #$T1, #$T2, #$R))
       && (forall x0#0: Box, x1#0: Box, x2#0: Box ::
        $IsBox(x0#0, #$T0) && $IsBox(x1#0, #$T1) && $IsBox(x2#0, #$T2)
           ==> Requires3(#$T0, #$T1, #$T2, #$R, $OneHeap, f#0, x0#0, x1#0, x2#0)));

// _System._#TotalFunc3: subset type $IsAlloc
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty, f#0: HandleType, $h: Heap ::
  { $IsAlloc(f#0, Tclass._System.___hTotalFunc3(#$T0, #$T1, #$T2, #$R), $h) }
  $IsAlloc(f#0, Tclass._System.___hTotalFunc3(#$T0, #$T1, #$T2, #$R), $h)
     <==> $IsAlloc(f#0, Tclass._System.___hPartialFunc3(#$T0, #$T1, #$T2, #$R), $h));

function Tclass._System.___hFunc2(Ty, Ty, Ty) : Ty;

// Tclass._System.___hFunc2 Tag
axiom (forall #$T0: Ty, #$T1: Ty, #$R: Ty ::
  { Tclass._System.___hFunc2(#$T0, #$T1, #$R) }
  Tag(Tclass._System.___hFunc2(#$T0, #$T1, #$R)) == Tagclass._System.___hFunc2);

const unique Tagclass._System.___hFunc2: TyTag;

// Tclass._System.___hFunc2 injectivity 0
axiom (forall #$T0: Ty, #$T1: Ty, #$R: Ty ::
  { Tclass._System.___hFunc2(#$T0, #$T1, #$R) }
  Tclass._System.___hFunc2_0(Tclass._System.___hFunc2(#$T0, #$T1, #$R)) == #$T0);

function Tclass._System.___hFunc2_0(Ty) : Ty;

// Tclass._System.___hFunc2 injectivity 1
axiom (forall #$T0: Ty, #$T1: Ty, #$R: Ty ::
  { Tclass._System.___hFunc2(#$T0, #$T1, #$R) }
  Tclass._System.___hFunc2_1(Tclass._System.___hFunc2(#$T0, #$T1, #$R)) == #$T1);

function Tclass._System.___hFunc2_1(Ty) : Ty;

// Tclass._System.___hFunc2 injectivity 2
axiom (forall #$T0: Ty, #$T1: Ty, #$R: Ty ::
  { Tclass._System.___hFunc2(#$T0, #$T1, #$R) }
  Tclass._System.___hFunc2_2(Tclass._System.___hFunc2(#$T0, #$T1, #$R)) == #$R);

function Tclass._System.___hFunc2_2(Ty) : Ty;

// Box/unbox axiom for Tclass._System.___hFunc2
axiom (forall #$T0: Ty, #$T1: Ty, #$R: Ty, bx: Box ::
  { $IsBox(bx, Tclass._System.___hFunc2(#$T0, #$T1, #$R)) }
  $IsBox(bx, Tclass._System.___hFunc2(#$T0, #$T1, #$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, Tclass._System.___hFunc2(#$T0, #$T1, #$R)));

function Handle2([Heap,Box,Box]Box, [Heap,Box,Box]bool, [Heap,Box,Box]Set Box) : HandleType;

function Apply2(Ty, Ty, Ty, Heap, HandleType, Box, Box) : Box;

function Requires2(Ty, Ty, Ty, Heap, HandleType, Box, Box) : bool;

function Reads2(Ty, Ty, Ty, Heap, HandleType, Box, Box) : Set Box;

axiom (forall t0: Ty,
    t1: Ty,
    t2: Ty,
    heap: Heap,
    h: [Heap,Box,Box]Box,
    r: [Heap,Box,Box]bool,
    rd: [Heap,Box,Box]Set Box,
    bx0: Box,
    bx1: Box ::
  { Apply2(t0, t1, t2, heap, Handle2(h, r, rd), bx0, bx1) }
  Apply2(t0, t1, t2, heap, Handle2(h, r, rd), bx0, bx1) == h[heap, bx0, bx1]);

axiom (forall t0: Ty,
    t1: Ty,
    t2: Ty,
    heap: Heap,
    h: [Heap,Box,Box]Box,
    r: [Heap,Box,Box]bool,
    rd: [Heap,Box,Box]Set Box,
    bx0: Box,
    bx1: Box ::
  { Requires2(t0, t1, t2, heap, Handle2(h, r, rd), bx0, bx1) }
  r[heap, bx0, bx1] ==> Requires2(t0, t1, t2, heap, Handle2(h, r, rd), bx0, bx1));

axiom (forall t0: Ty,
    t1: Ty,
    t2: Ty,
    heap: Heap,
    h: [Heap,Box,Box]Box,
    r: [Heap,Box,Box]bool,
    rd: [Heap,Box,Box]Set Box,
    bx0: Box,
    bx1: Box,
    bx: Box ::
  { Reads2(t0, t1, t2, heap, Handle2(h, r, rd), bx0, bx1)[bx] }
  Reads2(t0, t1, t2, heap, Handle2(h, r, rd), bx0, bx1)[bx]
     == rd[heap, bx0, bx1][bx]);

function {:inline} Requires2#canCall(t0: Ty, t1: Ty, t2: Ty, heap: Heap, f: HandleType, bx0: Box, bx1: Box) : bool
{
  true
}

function {:inline} Reads2#canCall(t0: Ty, t1: Ty, t2: Ty, heap: Heap, f: HandleType, bx0: Box, bx1: Box) : bool
{
  true
}

// frame axiom for Reads2
axiom (forall t0: Ty, t1: Ty, t2: Ty, h0: Heap, h1: Heap, f: HandleType, bx0: Box, bx1: Box ::
  { $HeapSucc(h0, h1), Reads2(t0, t1, t2, h1, f, bx0, bx1) }
  $HeapSucc(h0, h1)
       &&
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       &&
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $Is(f, Tclass._System.___hFunc2(t0, t1, t2))
       && (forall<a> o: ref, fld: Field a ::
        o != null && Reads2(t0, t1, t2, h0, f, bx0, bx1)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Reads2(t0, t1, t2, h0, f, bx0, bx1) == Reads2(t0, t1, t2, h1, f, bx0, bx1));

// frame axiom for Reads2
axiom (forall t0: Ty, t1: Ty, t2: Ty, h0: Heap, h1: Heap, f: HandleType, bx0: Box, bx1: Box ::
  { $HeapSucc(h0, h1), Reads2(t0, t1, t2, h1, f, bx0, bx1) }
  $HeapSucc(h0, h1)
       &&
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       &&
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $Is(f, Tclass._System.___hFunc2(t0, t1, t2))
       && (forall<a> o: ref, fld: Field a ::
        o != null && Reads2(t0, t1, t2, h1, f, bx0, bx1)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Reads2(t0, t1, t2, h0, f, bx0, bx1) == Reads2(t0, t1, t2, h1, f, bx0, bx1));

// frame axiom for Requires2
axiom (forall t0: Ty, t1: Ty, t2: Ty, h0: Heap, h1: Heap, f: HandleType, bx0: Box, bx1: Box ::
  { $HeapSucc(h0, h1), Requires2(t0, t1, t2, h1, f, bx0, bx1) }
  $HeapSucc(h0, h1)
       &&
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       &&
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $Is(f, Tclass._System.___hFunc2(t0, t1, t2))
       && (forall<a> o: ref, fld: Field a ::
        o != null && Reads2(t0, t1, t2, h0, f, bx0, bx1)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Requires2(t0, t1, t2, h0, f, bx0, bx1) == Requires2(t0, t1, t2, h1, f, bx0, bx1));

// frame axiom for Requires2
axiom (forall t0: Ty, t1: Ty, t2: Ty, h0: Heap, h1: Heap, f: HandleType, bx0: Box, bx1: Box ::
  { $HeapSucc(h0, h1), Requires2(t0, t1, t2, h1, f, bx0, bx1) }
  $HeapSucc(h0, h1)
       &&
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       &&
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $Is(f, Tclass._System.___hFunc2(t0, t1, t2))
       && (forall<a> o: ref, fld: Field a ::
        o != null && Reads2(t0, t1, t2, h1, f, bx0, bx1)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Requires2(t0, t1, t2, h0, f, bx0, bx1) == Requires2(t0, t1, t2, h1, f, bx0, bx1));

// frame axiom for Apply2
axiom (forall t0: Ty, t1: Ty, t2: Ty, h0: Heap, h1: Heap, f: HandleType, bx0: Box, bx1: Box ::
  { $HeapSucc(h0, h1), Apply2(t0, t1, t2, h1, f, bx0, bx1) }
  $HeapSucc(h0, h1)
       &&
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       &&
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $Is(f, Tclass._System.___hFunc2(t0, t1, t2))
       && (forall<a> o: ref, fld: Field a ::
        o != null && Reads2(t0, t1, t2, h0, f, bx0, bx1)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Apply2(t0, t1, t2, h0, f, bx0, bx1) == Apply2(t0, t1, t2, h1, f, bx0, bx1));

// frame axiom for Apply2
axiom (forall t0: Ty, t1: Ty, t2: Ty, h0: Heap, h1: Heap, f: HandleType, bx0: Box, bx1: Box ::
  { $HeapSucc(h0, h1), Apply2(t0, t1, t2, h1, f, bx0, bx1) }
  $HeapSucc(h0, h1)
       &&
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       &&
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $Is(f, Tclass._System.___hFunc2(t0, t1, t2))
       && (forall<a> o: ref, fld: Field a ::
        o != null && Reads2(t0, t1, t2, h1, f, bx0, bx1)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Apply2(t0, t1, t2, h0, f, bx0, bx1) == Apply2(t0, t1, t2, h1, f, bx0, bx1));

// empty-reads property for Reads2
axiom (forall t0: Ty, t1: Ty, t2: Ty, heap: Heap, f: HandleType, bx0: Box, bx1: Box ::
  { Reads2(t0, t1, t2, $OneHeap, f, bx0, bx1), $IsGoodHeap(heap) }
    { Reads2(t0, t1, t2, heap, f, bx0, bx1) }
  $IsGoodHeap(heap)
       &&
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $Is(f, Tclass._System.___hFunc2(t0, t1, t2))
     ==> (Set#Equal(Reads2(t0, t1, t2, $OneHeap, f, bx0, bx1), Set#Empty(): Set Box)
       <==> Set#Equal(Reads2(t0, t1, t2, heap, f, bx0, bx1), Set#Empty(): Set Box)));

// empty-reads property for Requires2
axiom (forall t0: Ty, t1: Ty, t2: Ty, heap: Heap, f: HandleType, bx0: Box, bx1: Box ::
  { Requires2(t0, t1, t2, $OneHeap, f, bx0, bx1), $IsGoodHeap(heap) }
    { Requires2(t0, t1, t2, heap, f, bx0, bx1) }
  $IsGoodHeap(heap)
       &&
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $Is(f, Tclass._System.___hFunc2(t0, t1, t2))
       && Set#Equal(Reads2(t0, t1, t2, $OneHeap, f, bx0, bx1), Set#Empty(): Set Box)
     ==> Requires2(t0, t1, t2, $OneHeap, f, bx0, bx1)
       == Requires2(t0, t1, t2, heap, f, bx0, bx1));

axiom (forall f: HandleType, t0: Ty, t1: Ty, t2: Ty ::
  { $Is(f, Tclass._System.___hFunc2(t0, t1, t2)) }
  $Is(f, Tclass._System.___hFunc2(t0, t1, t2))
     <==> (forall h: Heap, bx0: Box, bx1: Box ::
      { Apply2(t0, t1, t2, h, f, bx0, bx1) }
      $IsGoodHeap(h)
           &&
          $IsBox(bx0, t0)
           && $IsBox(bx1, t1)
           && Requires2(t0, t1, t2, h, f, bx0, bx1)
         ==> $IsBox(Apply2(t0, t1, t2, h, f, bx0, bx1), t2)));

axiom (forall f: HandleType, t0: Ty, t1: Ty, t2: Ty, u0: Ty, u1: Ty, u2: Ty ::
  { $Is(f, Tclass._System.___hFunc2(t0, t1, t2)), $Is(f, Tclass._System.___hFunc2(u0, u1, u2)) }
  $Is(f, Tclass._System.___hFunc2(t0, t1, t2))
       && (forall bx: Box ::
        { $IsBox(bx, u0) } { $IsBox(bx, t0) }
        $IsBox(bx, u0) ==> $IsBox(bx, t0))
       && (forall bx: Box ::
        { $IsBox(bx, u1) } { $IsBox(bx, t1) }
        $IsBox(bx, u1) ==> $IsBox(bx, t1))
       && (forall bx: Box ::
        { $IsBox(bx, t2) } { $IsBox(bx, u2) }
        $IsBox(bx, t2) ==> $IsBox(bx, u2))
     ==> $Is(f, Tclass._System.___hFunc2(u0, u1, u2)));

axiom (forall f: HandleType, t0: Ty, t1: Ty, t2: Ty, h: Heap ::
  { $IsAlloc(f, Tclass._System.___hFunc2(t0, t1, t2), h) }
  $IsGoodHeap(h)
     ==> ($IsAlloc(f, Tclass._System.___hFunc2(t0, t1, t2), h)
       <==> (forall bx0: Box, bx1: Box ::
        { Apply2(t0, t1, t2, h, f, bx0, bx1) } { Reads2(t0, t1, t2, h, f, bx0, bx1) }
        $IsBox(bx0, t0)
             && $IsAllocBox(bx0, t0, h)
             &&
            $IsBox(bx1, t1)
             && $IsAllocBox(bx1, t1, h)
             && Requires2(t0, t1, t2, h, f, bx0, bx1)
           ==> (forall r: ref ::
            { Reads2(t0, t1, t2, h, f, bx0, bx1)[$Box(r)] }
            r != null && Reads2(t0, t1, t2, h, f, bx0, bx1)[$Box(r)] ==> read(h, r, alloc)))));

axiom (forall f: HandleType, t0: Ty, t1: Ty, t2: Ty, h: Heap ::
  { $IsAlloc(f, Tclass._System.___hFunc2(t0, t1, t2), h) }
  $IsGoodHeap(h) && $IsAlloc(f, Tclass._System.___hFunc2(t0, t1, t2), h)
     ==> (forall bx0: Box, bx1: Box ::
      { Apply2(t0, t1, t2, h, f, bx0, bx1) }
      $IsAllocBox(bx0, t0, h)
           && $IsAllocBox(bx1, t1, h)
           && Requires2(t0, t1, t2, h, f, bx0, bx1)
         ==> $IsAllocBox(Apply2(t0, t1, t2, h, f, bx0, bx1), t2, h)));

function Tclass._System.___hPartialFunc2(Ty, Ty, Ty) : Ty;

// Tclass._System.___hPartialFunc2 Tag
axiom (forall #$T0: Ty, #$T1: Ty, #$R: Ty ::
  { Tclass._System.___hPartialFunc2(#$T0, #$T1, #$R) }
  Tag(Tclass._System.___hPartialFunc2(#$T0, #$T1, #$R))
     == Tagclass._System.___hPartialFunc2);

const unique Tagclass._System.___hPartialFunc2: TyTag;

// Tclass._System.___hPartialFunc2 injectivity 0
axiom (forall #$T0: Ty, #$T1: Ty, #$R: Ty ::
  { Tclass._System.___hPartialFunc2(#$T0, #$T1, #$R) }
  Tclass._System.___hPartialFunc2_0(Tclass._System.___hPartialFunc2(#$T0, #$T1, #$R))
     == #$T0);

function Tclass._System.___hPartialFunc2_0(Ty) : Ty;

// Tclass._System.___hPartialFunc2 injectivity 1
axiom (forall #$T0: Ty, #$T1: Ty, #$R: Ty ::
  { Tclass._System.___hPartialFunc2(#$T0, #$T1, #$R) }
  Tclass._System.___hPartialFunc2_1(Tclass._System.___hPartialFunc2(#$T0, #$T1, #$R))
     == #$T1);

function Tclass._System.___hPartialFunc2_1(Ty) : Ty;

// Tclass._System.___hPartialFunc2 injectivity 2
axiom (forall #$T0: Ty, #$T1: Ty, #$R: Ty ::
  { Tclass._System.___hPartialFunc2(#$T0, #$T1, #$R) }
  Tclass._System.___hPartialFunc2_2(Tclass._System.___hPartialFunc2(#$T0, #$T1, #$R))
     == #$R);

function Tclass._System.___hPartialFunc2_2(Ty) : Ty;

// Box/unbox axiom for Tclass._System.___hPartialFunc2
axiom (forall #$T0: Ty, #$T1: Ty, #$R: Ty, bx: Box ::
  { $IsBox(bx, Tclass._System.___hPartialFunc2(#$T0, #$T1, #$R)) }
  $IsBox(bx, Tclass._System.___hPartialFunc2(#$T0, #$T1, #$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, Tclass._System.___hPartialFunc2(#$T0, #$T1, #$R)));

// _System._#PartialFunc2: subset type $Is
axiom (forall #$T0: Ty, #$T1: Ty, #$R: Ty, f#0: HandleType ::
  { $Is(f#0, Tclass._System.___hPartialFunc2(#$T0, #$T1, #$R)) }
  $Is(f#0, Tclass._System.___hPartialFunc2(#$T0, #$T1, #$R))
     <==> $Is(f#0, Tclass._System.___hFunc2(#$T0, #$T1, #$R))
       && (forall x0#0: Box, x1#0: Box ::
        $IsBox(x0#0, #$T0) && $IsBox(x1#0, #$T1)
           ==> Set#Equal(Reads2(#$T0, #$T1, #$R, $OneHeap, f#0, x0#0, x1#0), Set#Empty(): Set Box)));

// _System._#PartialFunc2: subset type $IsAlloc
axiom (forall #$T0: Ty, #$T1: Ty, #$R: Ty, f#0: HandleType, $h: Heap ::
  { $IsAlloc(f#0, Tclass._System.___hPartialFunc2(#$T0, #$T1, #$R), $h) }
  $IsAlloc(f#0, Tclass._System.___hPartialFunc2(#$T0, #$T1, #$R), $h)
     <==> $IsAlloc(f#0, Tclass._System.___hFunc2(#$T0, #$T1, #$R), $h));

function Tclass._System.___hTotalFunc2(Ty, Ty, Ty) : Ty;

// Tclass._System.___hTotalFunc2 Tag
axiom (forall #$T0: Ty, #$T1: Ty, #$R: Ty ::
  { Tclass._System.___hTotalFunc2(#$T0, #$T1, #$R) }
  Tag(Tclass._System.___hTotalFunc2(#$T0, #$T1, #$R))
     == Tagclass._System.___hTotalFunc2);

const unique Tagclass._System.___hTotalFunc2: TyTag;

// Tclass._System.___hTotalFunc2 injectivity 0
axiom (forall #$T0: Ty, #$T1: Ty, #$R: Ty ::
  { Tclass._System.___hTotalFunc2(#$T0, #$T1, #$R) }
  Tclass._System.___hTotalFunc2_0(Tclass._System.___hTotalFunc2(#$T0, #$T1, #$R))
     == #$T0);

function Tclass._System.___hTotalFunc2_0(Ty) : Ty;

// Tclass._System.___hTotalFunc2 injectivity 1
axiom (forall #$T0: Ty, #$T1: Ty, #$R: Ty ::
  { Tclass._System.___hTotalFunc2(#$T0, #$T1, #$R) }
  Tclass._System.___hTotalFunc2_1(Tclass._System.___hTotalFunc2(#$T0, #$T1, #$R))
     == #$T1);

function Tclass._System.___hTotalFunc2_1(Ty) : Ty;

// Tclass._System.___hTotalFunc2 injectivity 2
axiom (forall #$T0: Ty, #$T1: Ty, #$R: Ty ::
  { Tclass._System.___hTotalFunc2(#$T0, #$T1, #$R) }
  Tclass._System.___hTotalFunc2_2(Tclass._System.___hTotalFunc2(#$T0, #$T1, #$R))
     == #$R);

function Tclass._System.___hTotalFunc2_2(Ty) : Ty;

// Box/unbox axiom for Tclass._System.___hTotalFunc2
axiom (forall #$T0: Ty, #$T1: Ty, #$R: Ty, bx: Box ::
  { $IsBox(bx, Tclass._System.___hTotalFunc2(#$T0, #$T1, #$R)) }
  $IsBox(bx, Tclass._System.___hTotalFunc2(#$T0, #$T1, #$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, Tclass._System.___hTotalFunc2(#$T0, #$T1, #$R)));

// _System._#TotalFunc2: subset type $Is
axiom (forall #$T0: Ty, #$T1: Ty, #$R: Ty, f#0: HandleType ::
  { $Is(f#0, Tclass._System.___hTotalFunc2(#$T0, #$T1, #$R)) }
  $Is(f#0, Tclass._System.___hTotalFunc2(#$T0, #$T1, #$R))
     <==> $Is(f#0, Tclass._System.___hPartialFunc2(#$T0, #$T1, #$R))
       && (forall x0#0: Box, x1#0: Box ::
        $IsBox(x0#0, #$T0) && $IsBox(x1#0, #$T1)
           ==> Requires2(#$T0, #$T1, #$R, $OneHeap, f#0, x0#0, x1#0)));

// _System._#TotalFunc2: subset type $IsAlloc
axiom (forall #$T0: Ty, #$T1: Ty, #$R: Ty, f#0: HandleType, $h: Heap ::
  { $IsAlloc(f#0, Tclass._System.___hTotalFunc2(#$T0, #$T1, #$R), $h) }
  $IsAlloc(f#0, Tclass._System.___hTotalFunc2(#$T0, #$T1, #$R), $h)
     <==> $IsAlloc(f#0, Tclass._System.___hPartialFunc2(#$T0, #$T1, #$R), $h));

const unique class._System.__tuple_h0: ClassName;

// Constructor function declaration
function #_System._tuple#0._#Make0() : DatatypeType;

const unique ##_System._tuple#0._#Make0: DtCtorId;

// Constructor identifier
axiom DatatypeCtorId(#_System._tuple#0._#Make0()) == ##_System._tuple#0._#Make0;

function _System.__tuple_h0.___hMake0_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType ::
  { _System.__tuple_h0.___hMake0_q(d) }
  _System.__tuple_h0.___hMake0_q(d)
     <==> DatatypeCtorId(d) == ##_System._tuple#0._#Make0);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType ::
  { _System.__tuple_h0.___hMake0_q(d) }
  _System.__tuple_h0.___hMake0_q(d) ==> d == #_System._tuple#0._#Make0());

function Tclass._System.__tuple_h0() : Ty;

// Tclass._System.__tuple_h0 Tag
axiom Tag(Tclass._System.__tuple_h0()) == Tagclass._System.__tuple_h0;

const unique Tagclass._System.__tuple_h0: TyTag;

// Box/unbox axiom for Tclass._System.__tuple_h0
axiom (forall bx: Box ::
  { $IsBox(bx, Tclass._System.__tuple_h0()) }
  $IsBox(bx, Tclass._System.__tuple_h0())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._System.__tuple_h0()));

// Constructor $Is
axiom $Is(#_System._tuple#0._#Make0(), Tclass._System.__tuple_h0());

// Constructor $IsAlloc
axiom (forall $h: Heap ::
  { $IsAlloc(#_System._tuple#0._#Make0(), Tclass._System.__tuple_h0(), $h) }
  $IsGoodHeap($h)
     ==> $IsAlloc(#_System._tuple#0._#Make0(), Tclass._System.__tuple_h0(), $h));

// Constructor literal
axiom #_System._tuple#0._#Make0() == Lit(#_System._tuple#0._#Make0());

// One-depth case-split function
function $IsA#_System.__tuple_h0(DatatypeType) : bool;

// One-depth case-split axiom
axiom (forall d: DatatypeType ::
  { $IsA#_System.__tuple_h0(d) }
  $IsA#_System.__tuple_h0(d) ==> _System.__tuple_h0.___hMake0_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType ::
  { _System.__tuple_h0.___hMake0_q(d), $Is(d, Tclass._System.__tuple_h0()) }
  $Is(d, Tclass._System.__tuple_h0()) ==> _System.__tuple_h0.___hMake0_q(d));

const unique class._System.__tuple_h2: ClassName;

// Constructor function declaration
function #_System._tuple#2._#Make2(Box, Box) : DatatypeType;

const unique ##_System._tuple#2._#Make2: DtCtorId;

// Constructor identifier
axiom (forall a#5#0#0: Box, a#5#1#0: Box ::
  { #_System._tuple#2._#Make2(a#5#0#0, a#5#1#0) }
  DatatypeCtorId(#_System._tuple#2._#Make2(a#5#0#0, a#5#1#0))
     == ##_System._tuple#2._#Make2);

function _System.__tuple_h2.___hMake2_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType ::
  { _System.__tuple_h2.___hMake2_q(d) }
  _System.__tuple_h2.___hMake2_q(d)
     <==> DatatypeCtorId(d) == ##_System._tuple#2._#Make2);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType ::
  { _System.__tuple_h2.___hMake2_q(d) }
  _System.__tuple_h2.___hMake2_q(d)
     ==> (exists a#6#0#0: Box, a#6#1#0: Box ::
      d == #_System._tuple#2._#Make2(a#6#0#0, a#6#1#0)));

function Tclass._System.__tuple_h2(Ty, Ty) : Ty;

// Tclass._System.__tuple_h2 Tag
axiom (forall #$T0: Ty, #$T1: Ty ::
  { Tclass._System.__tuple_h2(#$T0, #$T1) }
  Tag(Tclass._System.__tuple_h2(#$T0, #$T1)) == Tagclass._System.__tuple_h2);

const unique Tagclass._System.__tuple_h2: TyTag;

// Tclass._System.__tuple_h2 injectivity 0
axiom (forall #$T0: Ty, #$T1: Ty ::
  { Tclass._System.__tuple_h2(#$T0, #$T1) }
  Tclass._System.__tuple_h2_0(Tclass._System.__tuple_h2(#$T0, #$T1)) == #$T0);

function Tclass._System.__tuple_h2_0(Ty) : Ty;

// Tclass._System.__tuple_h2 injectivity 1
axiom (forall #$T0: Ty, #$T1: Ty ::
  { Tclass._System.__tuple_h2(#$T0, #$T1) }
  Tclass._System.__tuple_h2_1(Tclass._System.__tuple_h2(#$T0, #$T1)) == #$T1);

function Tclass._System.__tuple_h2_1(Ty) : Ty;

// Box/unbox axiom for Tclass._System.__tuple_h2
axiom (forall #$T0: Ty, #$T1: Ty, bx: Box ::
  { $IsBox(bx, Tclass._System.__tuple_h2(#$T0, #$T1)) }
  $IsBox(bx, Tclass._System.__tuple_h2(#$T0, #$T1))
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._System.__tuple_h2(#$T0, #$T1)));

// Constructor $Is
axiom (forall #$T0: Ty, #$T1: Ty, a#7#0#0: Box, a#7#1#0: Box ::
  { $Is(#_System._tuple#2._#Make2(a#7#0#0, a#7#1#0),
      Tclass._System.__tuple_h2(#$T0, #$T1)) }
  $Is(#_System._tuple#2._#Make2(a#7#0#0, a#7#1#0),
      Tclass._System.__tuple_h2(#$T0, #$T1))
     <==> $IsBox(a#7#0#0, #$T0) && $IsBox(a#7#1#0, #$T1));

// Constructor $IsAlloc
axiom (forall #$T0: Ty, #$T1: Ty, a#8#0#0: Box, a#8#1#0: Box, $h: Heap ::
  { $IsAlloc(#_System._tuple#2._#Make2(a#8#0#0, a#8#1#0),
      Tclass._System.__tuple_h2(#$T0, #$T1),
      $h) }
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_System._tuple#2._#Make2(a#8#0#0, a#8#1#0),
        Tclass._System.__tuple_h2(#$T0, #$T1),
        $h)
       <==> $IsAllocBox(a#8#0#0, #$T0, $h) && $IsAllocBox(a#8#1#0, #$T1, $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, #$T0: Ty, $h: Heap ::
  { $IsAllocBox(_System.__tuple_h2._0(d), #$T0, $h) }
  $IsGoodHeap($h)
       &&
      _System.__tuple_h2.___hMake2_q(d)
       && (exists #$T1: Ty ::
        { $IsAlloc(d, Tclass._System.__tuple_h2(#$T0, #$T1), $h) }
        $IsAlloc(d, Tclass._System.__tuple_h2(#$T0, #$T1), $h))
     ==> $IsAllocBox(_System.__tuple_h2._0(d), #$T0, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, #$T1: Ty, $h: Heap ::
  { $IsAllocBox(_System.__tuple_h2._1(d), #$T1, $h) }
  $IsGoodHeap($h)
       &&
      _System.__tuple_h2.___hMake2_q(d)
       && (exists #$T0: Ty ::
        { $IsAlloc(d, Tclass._System.__tuple_h2(#$T0, #$T1), $h) }
        $IsAlloc(d, Tclass._System.__tuple_h2(#$T0, #$T1), $h))
     ==> $IsAllocBox(_System.__tuple_h2._1(d), #$T1, $h));

// Constructor literal
axiom (forall a#9#0#0: Box, a#9#1#0: Box ::
  { #_System._tuple#2._#Make2(Lit(a#9#0#0), Lit(a#9#1#0)) }
  #_System._tuple#2._#Make2(Lit(a#9#0#0), Lit(a#9#1#0))
     == Lit(#_System._tuple#2._#Make2(a#9#0#0, a#9#1#0)));

// Constructor injectivity
axiom (forall a#10#0#0: Box, a#10#1#0: Box ::
  { #_System._tuple#2._#Make2(a#10#0#0, a#10#1#0) }
  _System.__tuple_h2._0(#_System._tuple#2._#Make2(a#10#0#0, a#10#1#0)) == a#10#0#0);

// Inductive rank
axiom (forall a#11#0#0: Box, a#11#1#0: Box ::
  { #_System._tuple#2._#Make2(a#11#0#0, a#11#1#0) }
  BoxRank(a#11#0#0) < DtRank(#_System._tuple#2._#Make2(a#11#0#0, a#11#1#0)));

// Constructor injectivity
axiom (forall a#12#0#0: Box, a#12#1#0: Box ::
  { #_System._tuple#2._#Make2(a#12#0#0, a#12#1#0) }
  _System.__tuple_h2._1(#_System._tuple#2._#Make2(a#12#0#0, a#12#1#0)) == a#12#1#0);

// Inductive rank
axiom (forall a#13#0#0: Box, a#13#1#0: Box ::
  { #_System._tuple#2._#Make2(a#13#0#0, a#13#1#0) }
  BoxRank(a#13#1#0) < DtRank(#_System._tuple#2._#Make2(a#13#0#0, a#13#1#0)));

// One-depth case-split function
function $IsA#_System.__tuple_h2(DatatypeType) : bool;

// One-depth case-split axiom
axiom (forall d: DatatypeType ::
  { $IsA#_System.__tuple_h2(d) }
  $IsA#_System.__tuple_h2(d) ==> _System.__tuple_h2.___hMake2_q(d));

// Questionmark data type disjunctivity
axiom (forall #$T0: Ty, #$T1: Ty, d: DatatypeType ::
  { _System.__tuple_h2.___hMake2_q(d), $Is(d, Tclass._System.__tuple_h2(#$T0, #$T1)) }
  $Is(d, Tclass._System.__tuple_h2(#$T0, #$T1))
     ==> _System.__tuple_h2.___hMake2_q(d));

const unique class._module.BreadthFirstSearch: ClassName;

function Tclass._module.BreadthFirstSearch(Ty) : Ty;

// Tclass._module.BreadthFirstSearch Tag
axiom (forall _module.BreadthFirstSearch$Vertex: Ty ::
  { Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex) }
  Tag(Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex))
     == Tagclass._module.BreadthFirstSearch);

const unique Tagclass._module.BreadthFirstSearch: TyTag;

// Tclass._module.BreadthFirstSearch injectivity 0
axiom (forall _module.BreadthFirstSearch$Vertex: Ty ::
  { Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex) }
  Tclass._module.BreadthFirstSearch_0(Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex))
     == _module.BreadthFirstSearch$Vertex);

function Tclass._module.BreadthFirstSearch_0(Ty) : Ty;

// Box/unbox axiom for Tclass._module.BreadthFirstSearch
axiom (forall _module.BreadthFirstSearch$Vertex: Ty, bx: Box ::
  { $IsBox(bx, Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex)) }
  $IsBox(bx, Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex))
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref,
        Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex)));

// BreadthFirstSearch: Class $Is
axiom (forall _module.BreadthFirstSearch$Vertex: Ty, $o: ref ::
  { $Is($o, Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex)) }
  $Is($o, Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex))
     <==> $o == null
       || dtype($o)
         == Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex));

// BreadthFirstSearch: Class $IsAlloc
axiom (forall _module.BreadthFirstSearch$Vertex: Ty, $o: ref, $h: Heap ::
  { $IsAlloc($o, Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex), $h) }
  $IsAlloc($o, Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex), $h)
     <==> $o == null || read($h, $o, alloc));

// function declaration for _module.BreadthFirstSearch.Succ
function _module.BreadthFirstSearch.Succ(_module.BreadthFirstSearch$Vertex: Ty, this: ref, x#0: Box) : Set Box;

function _module.BreadthFirstSearch.Succ#canCall(_module.BreadthFirstSearch$Vertex: Ty, this: ref, x#0: Box) : bool;

// consequence axiom for _module.BreadthFirstSearch.Succ
axiom 1 <= $FunctionContextHeight
   ==> (forall _module.BreadthFirstSearch$Vertex: Ty, this: ref, x#0: Box ::
    { _module.BreadthFirstSearch.Succ(_module.BreadthFirstSearch$Vertex, this, x#0) }
    _module.BreadthFirstSearch.Succ#canCall(_module.BreadthFirstSearch$Vertex, this, x#0)
         || (1 != $FunctionContextHeight
           &&
          this != null
           && $Is(this, Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex))
           && $IsBox(x#0, _module.BreadthFirstSearch$Vertex))
       ==> $Is(_module.BreadthFirstSearch.Succ(_module.BreadthFirstSearch$Vertex, this, x#0),
        TSet(_module.BreadthFirstSearch$Vertex)));

function _module.BreadthFirstSearch.Succ#requires(Ty, ref, Box) : bool;

// #requires axiom for _module.BreadthFirstSearch.Succ
axiom (forall _module.BreadthFirstSearch$Vertex: Ty, this: ref, x#0: Box ::
  { _module.BreadthFirstSearch.Succ#requires(_module.BreadthFirstSearch$Vertex, this, x#0) }
  this != null
       && $Is(this, Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex))
       && $IsBox(x#0, _module.BreadthFirstSearch$Vertex)
     ==> _module.BreadthFirstSearch.Succ#requires(_module.BreadthFirstSearch$Vertex, this, x#0)
       == true);

procedure CheckWellformed$$_module.BreadthFirstSearch.Succ(_module.BreadthFirstSearch$Vertex: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex))
         && $IsAlloc(this,
          Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex),
          $Heap),
    x#0: Box where $IsBox(x#0, _module.BreadthFirstSearch$Vertex));
  free requires 1 == $FunctionContextHeight;
  modifies $Heap, $Tick;



// function declaration for _module.BreadthFirstSearch.IsPath
function _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex: Ty,
    $ly: LayerType,
    this: ref,
    source#0: Box,
    dest#0: Box,
    p#0: DatatypeType)
   : bool;

function _module.BreadthFirstSearch.IsPath#canCall(_module.BreadthFirstSearch$Vertex: Ty,
    this: ref,
    source#0: Box,
    dest#0: Box,
    p#0: DatatypeType)
   : bool;

// layer synonym axiom
axiom (forall _module.BreadthFirstSearch$Vertex: Ty,
    $ly: LayerType,
    this: ref,
    source#0: Box,
    dest#0: Box,
    p#0: DatatypeType ::
  { _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex, $LS($ly), this, source#0, dest#0, p#0) }
  _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex, $LS($ly), this, source#0, dest#0, p#0)
     == _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex, $ly, this, source#0, dest#0, p#0));

// fuel synonym axiom
axiom (forall _module.BreadthFirstSearch$Vertex: Ty,
    $ly: LayerType,
    this: ref,
    source#0: Box,
    dest#0: Box,
    p#0: DatatypeType ::
  { _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex,
      AsFuelBottom($ly),
      this,
      source#0,
      dest#0,
      p#0) }
  _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex, $ly, this, source#0, dest#0, p#0)
     == _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex, $LZ, this, source#0, dest#0, p#0));

function Tclass._module.List(Ty) : Ty;

// Tclass._module.List Tag
axiom (forall _module.List$T: Ty ::
  { Tclass._module.List(_module.List$T) }
  Tag(Tclass._module.List(_module.List$T)) == Tagclass._module.List);

const unique Tagclass._module.List: TyTag;

// Tclass._module.List injectivity 0
axiom (forall _module.List$T: Ty ::
  { Tclass._module.List(_module.List$T) }
  Tclass._module.List_0(Tclass._module.List(_module.List$T)) == _module.List$T);

function Tclass._module.List_0(Ty) : Ty;

// Box/unbox axiom for Tclass._module.List
axiom (forall _module.List$T: Ty, bx: Box ::
  { $IsBox(bx, Tclass._module.List(_module.List$T)) }
  $IsBox(bx, Tclass._module.List(_module.List$T))
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.List(_module.List$T)));

// consequence axiom for _module.BreadthFirstSearch.IsPath
axiom 7 <= $FunctionContextHeight
   ==> (forall _module.BreadthFirstSearch$Vertex: Ty,
      $ly: LayerType,
      this: ref,
      source#0: Box,
      dest#0: Box,
      p#0: DatatypeType ::
    { _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex, $ly, this, source#0, dest#0, p#0) }
    _module.BreadthFirstSearch.IsPath#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, dest#0, p#0)
         || (7 != $FunctionContextHeight
           &&
          this != null
           && $Is(this, Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex))
           && $IsBox(source#0, _module.BreadthFirstSearch$Vertex)
           && $IsBox(dest#0, _module.BreadthFirstSearch$Vertex)
           && $Is(p#0, Tclass._module.List(_module.BreadthFirstSearch$Vertex)))
       ==> true);

function _module.BreadthFirstSearch.IsPath#requires(Ty, LayerType, ref, Box, Box, DatatypeType) : bool;

// #requires axiom for _module.BreadthFirstSearch.IsPath
axiom (forall _module.BreadthFirstSearch$Vertex: Ty,
    $ly: LayerType,
    $Heap: Heap,
    this: ref,
    source#0: Box,
    dest#0: Box,
    p#0: DatatypeType ::
  { _module.BreadthFirstSearch.IsPath#requires(_module.BreadthFirstSearch$Vertex, $ly, this, source#0, dest#0, p#0), $IsGoodHeap($Heap) }
  $IsGoodHeap($Heap)
       &&
      this != null
       &&
      $Is(this, Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex))
       && $IsAlloc(this,
        Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex),
        $Heap)
       && $IsBox(source#0, _module.BreadthFirstSearch$Vertex)
       && $IsBox(dest#0, _module.BreadthFirstSearch$Vertex)
       && $Is(p#0, Tclass._module.List(_module.BreadthFirstSearch$Vertex))
     ==> _module.BreadthFirstSearch.IsPath#requires(_module.BreadthFirstSearch$Vertex, $ly, this, source#0, dest#0, p#0)
       == true);

// definition axiom for _module.BreadthFirstSearch.IsPath(revealed)
axiom 7 <= $FunctionContextHeight
   ==> (forall _module.BreadthFirstSearch$Vertex: Ty,
      $ly: LayerType,
      $Heap: Heap,
      this: ref,
      source#0: Box,
      dest#0: Box,
      p#0: DatatypeType ::
    { _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex, $LS($ly), this, source#0, dest#0, p#0), $IsGoodHeap($Heap) }
    _module.BreadthFirstSearch.IsPath#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, dest#0, p#0)
         || (7 != $FunctionContextHeight
           &&
          $IsGoodHeap($Heap)
           &&
          this != null
           &&
          $Is(this, Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex))
           && $IsAlloc(this,
            Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex),
            $Heap)
           && $IsBox(source#0, _module.BreadthFirstSearch$Vertex)
           && $IsBox(dest#0, _module.BreadthFirstSearch$Vertex)
           && $Is(p#0, Tclass._module.List(_module.BreadthFirstSearch$Vertex)))
       ==> (!_module.List.Nil_q(p#0)
           ==> _module.BreadthFirstSearch.Succ#canCall(_module.BreadthFirstSearch$Vertex, this, _module.List.head(p#0))
             && (_module.BreadthFirstSearch.Succ(_module.BreadthFirstSearch$Vertex, this, _module.List.head(p#0))[dest#0]
               ==> _module.BreadthFirstSearch.IsPath#canCall(_module.BreadthFirstSearch$Vertex,
                this,
                source#0,
                _module.List.head(p#0),
                _module.List.tail(p#0))))
         && _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex, $LS($ly), this, source#0, dest#0, p#0)
           == (if _module.List.Nil_q(p#0)
             then source#0 == dest#0
             else _module.BreadthFirstSearch.Succ(_module.BreadthFirstSearch$Vertex, this, _module.List.head(p#0))[dest#0]
               && _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex,
                $ly,
                this,
                source#0,
                _module.List.head(p#0),
                _module.List.tail(p#0))));

// definition axiom for _module.BreadthFirstSearch.IsPath for decreasing-related literals(revealed)
axiom 7 <= $FunctionContextHeight
   ==> (forall _module.BreadthFirstSearch$Vertex: Ty,
      $ly: LayerType,
      $Heap: Heap,
      this: ref,
      source#0: Box,
      dest#0: Box,
      p#0: DatatypeType ::
    {:weight 3} { _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex, $LS($ly), this, source#0, dest#0, Lit(p#0)), $IsGoodHeap($Heap) }
    _module.BreadthFirstSearch.IsPath#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, dest#0, Lit(p#0))
         || (7 != $FunctionContextHeight
           &&
          $IsGoodHeap($Heap)
           &&
          this != null
           &&
          $Is(this, Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex))
           && $IsAlloc(this,
            Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex),
            $Heap)
           && $IsBox(source#0, _module.BreadthFirstSearch$Vertex)
           && $IsBox(dest#0, _module.BreadthFirstSearch$Vertex)
           && $Is(p#0, Tclass._module.List(_module.BreadthFirstSearch$Vertex)))
       ==> (!Lit(_module.List.Nil_q(Lit(p#0)))
           ==> _module.BreadthFirstSearch.Succ#canCall(_module.BreadthFirstSearch$Vertex, this, Lit(_module.List.head(Lit(p#0))))
             && (_module.BreadthFirstSearch.Succ(_module.BreadthFirstSearch$Vertex, this, Lit(_module.List.head(Lit(p#0))))[dest#0]
               ==> _module.BreadthFirstSearch.IsPath#canCall(_module.BreadthFirstSearch$Vertex,
                this,
                source#0,
                Lit(_module.List.head(Lit(p#0))),
                Lit(_module.List.tail(Lit(p#0))))))
         && _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex, $LS($ly), this, source#0, dest#0, Lit(p#0))
           == (if _module.List.Nil_q(Lit(p#0))
             then source#0 == dest#0
             else _module.BreadthFirstSearch.Succ(_module.BreadthFirstSearch$Vertex, this, Lit(_module.List.head(Lit(p#0))))[dest#0]
               && _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex,
                $LS($ly),
                this,
                source#0,
                Lit(_module.List.head(Lit(p#0))),
                Lit(_module.List.tail(Lit(p#0))))));

// definition axiom for _module.BreadthFirstSearch.IsPath for all literals(revealed)
axiom 7 <= $FunctionContextHeight
   ==> (forall _module.BreadthFirstSearch$Vertex: Ty,
      $ly: LayerType,
      $Heap: Heap,
      this: ref,
      source#0: Box,
      dest#0: Box,
      p#0: DatatypeType ::
    {:weight 3} { _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex,
        $LS($ly),
        this,
        Lit(source#0),
        Lit(dest#0),
        Lit(p#0)), $IsGoodHeap($Heap) }
    _module.BreadthFirstSearch.IsPath#canCall(_module.BreadthFirstSearch$Vertex, this, Lit(source#0), Lit(dest#0), Lit(p#0))
         || (7 != $FunctionContextHeight
           &&
          $IsGoodHeap($Heap)
           &&
          this != null
           &&
          $Is(this, Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex))
           && $IsAlloc(this,
            Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex),
            $Heap)
           && $IsBox(source#0, _module.BreadthFirstSearch$Vertex)
           && $IsBox(dest#0, _module.BreadthFirstSearch$Vertex)
           && $Is(p#0, Tclass._module.List(_module.BreadthFirstSearch$Vertex)))
       ==> (!Lit(_module.List.Nil_q(Lit(p#0)))
           ==> _module.BreadthFirstSearch.Succ#canCall(_module.BreadthFirstSearch$Vertex, this, Lit(_module.List.head(Lit(p#0))))
             && (_module.BreadthFirstSearch.Succ(_module.BreadthFirstSearch$Vertex, this, Lit(_module.List.head(Lit(p#0))))[Lit(dest#0)]
               ==> _module.BreadthFirstSearch.IsPath#canCall(_module.BreadthFirstSearch$Vertex,
                this,
                Lit(source#0),
                Lit(_module.List.head(Lit(p#0))),
                Lit(_module.List.tail(Lit(p#0))))))
         && _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex,
            $LS($ly),
            this,
            Lit(source#0),
            Lit(dest#0),
            Lit(p#0))
           == (if _module.List.Nil_q(Lit(p#0))
             then Lit(source#0) == Lit(dest#0)
             else _module.BreadthFirstSearch.Succ(_module.BreadthFirstSearch$Vertex, this, Lit(_module.List.head(Lit(p#0))))[Lit(dest#0)]
               && _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex,
                $LS($ly),
                this,
                Lit(source#0),
                Lit(_module.List.head(Lit(p#0))),
                Lit(_module.List.tail(Lit(p#0))))));

procedure CheckWellformed$$_module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex))
         && $IsAlloc(this,
          Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex),
          $Heap),
    source#0: Box where $IsBox(source#0, _module.BreadthFirstSearch$Vertex),
    dest#0: Box where $IsBox(dest#0, _module.BreadthFirstSearch$Vertex),
    p#0: DatatypeType
       where $Is(p#0, Tclass._module.List(_module.BreadthFirstSearch$Vertex)));
  free requires 7 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex: Ty,
    this: ref,
    source#0: Box,
    dest#0: Box,
    p#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var v#0: Box;
  var tail#0: DatatypeType;
  var ##x#0: Box;
  var ##source#0: Box;
  var ##dest#0: Box;
  var ##p#0: DatatypeType;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function IsPath
    assume {:captureState "BreadthFirstSearch.dfy(13,12): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
          $o != null && read($Heap, $o, alloc) ==> false);
        if (p#0 == #_module.List.Nil())
        {
            assume _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex, $LS($LZ), this, source#0, dest#0, p#0)
               ==
              (source#0
               == dest#0);
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex, $LS($LZ), this, source#0, dest#0, p#0),
              TBool);
        }
        else if (p#0 == #_module.List.Cons(v#0, tail#0))
        {
            assume $IsBox(v#0, _module.BreadthFirstSearch$Vertex);
            assume $Is(tail#0, Tclass._module.List(_module.BreadthFirstSearch$Vertex));
            ##x#0 := v#0;
            // assume allocatedness for argument to function
            assume $IsAllocBox(##x#0, _module.BreadthFirstSearch$Vertex, $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume _module.BreadthFirstSearch.Succ#canCall(_module.BreadthFirstSearch$Vertex, this, v#0);
            if (_module.BreadthFirstSearch.Succ(_module.BreadthFirstSearch$Vertex, this, v#0)[dest#0])
            {
                ##source#0 := source#0;
                // assume allocatedness for argument to function
                assume $IsAllocBox(##source#0, _module.BreadthFirstSearch$Vertex, $Heap);
                ##dest#0 := v#0;
                // assume allocatedness for argument to function
                assume $IsAllocBox(##dest#0, _module.BreadthFirstSearch$Vertex, $Heap);
                ##p#0 := tail#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##p#0, Tclass._module.List(_module.BreadthFirstSearch$Vertex), $Heap);
                b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                assert DtRank(##p#0) < DtRank(p#0);
                assume _module.BreadthFirstSearch.IsPath#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, v#0, tail#0);
            }

            assume _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex, $LS($LZ), this, source#0, dest#0, p#0)
               == (_module.BreadthFirstSearch.Succ(_module.BreadthFirstSearch$Vertex, this, v#0)[dest#0]
                 && _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex, $LS($LZ), this, source#0, v#0, tail#0));
            assume _module.BreadthFirstSearch.Succ#canCall(_module.BreadthFirstSearch$Vertex, this, v#0)
               && (_module.BreadthFirstSearch.Succ(_module.BreadthFirstSearch$Vertex, this, v#0)[dest#0]
                 ==> _module.BreadthFirstSearch.IsPath#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, v#0, tail#0));
            // CheckWellformedWithResult: any expression
            assume $Is(_module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex, $LS($LZ), this, source#0, dest#0, p#0),
              TBool);
        }
        else
        {
            assume false;
        }

        assert b$reqreads#0;
        assert b$reqreads#1;
    }
}



// function declaration for _module.BreadthFirstSearch.IsClosed
function _module.BreadthFirstSearch.IsClosed(_module.BreadthFirstSearch$Vertex: Ty, this: ref, S#0: Set Box) : bool;

function _module.BreadthFirstSearch.IsClosed#canCall(_module.BreadthFirstSearch$Vertex: Ty, this: ref, S#0: Set Box) : bool;

// consequence axiom for _module.BreadthFirstSearch.IsClosed
axiom 8 <= $FunctionContextHeight
   ==> (forall _module.BreadthFirstSearch$Vertex: Ty, this: ref, S#0: Set Box ::
    { _module.BreadthFirstSearch.IsClosed(_module.BreadthFirstSearch$Vertex, this, S#0) }
    _module.BreadthFirstSearch.IsClosed#canCall(_module.BreadthFirstSearch$Vertex, this, S#0)
         || (8 != $FunctionContextHeight
           &&
          this != null
           && $Is(this, Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex))
           && $Is(S#0, TSet(_module.BreadthFirstSearch$Vertex)))
       ==> true);

function _module.BreadthFirstSearch.IsClosed#requires(Ty, ref, Set Box) : bool;

// #requires axiom for _module.BreadthFirstSearch.IsClosed
axiom (forall _module.BreadthFirstSearch$Vertex: Ty, $Heap: Heap, this: ref, S#0: Set Box ::
  { _module.BreadthFirstSearch.IsClosed#requires(_module.BreadthFirstSearch$Vertex, this, S#0), $IsGoodHeap($Heap) }
  $IsGoodHeap($Heap)
       &&
      this != null
       &&
      $Is(this, Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex))
       && $IsAlloc(this,
        Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex),
        $Heap)
       && $Is(S#0, TSet(_module.BreadthFirstSearch$Vertex))
     ==> _module.BreadthFirstSearch.IsClosed#requires(_module.BreadthFirstSearch$Vertex, this, S#0)
       == true);

// definition axiom for _module.BreadthFirstSearch.IsClosed(revealed)
axiom 8 <= $FunctionContextHeight
   ==> (forall _module.BreadthFirstSearch$Vertex: Ty, $Heap: Heap, this: ref, S#0: Set Box ::
    { _module.BreadthFirstSearch.IsClosed(_module.BreadthFirstSearch$Vertex, this, S#0), $IsGoodHeap($Heap) }
    _module.BreadthFirstSearch.IsClosed#canCall(_module.BreadthFirstSearch$Vertex, this, S#0)
         || (8 != $FunctionContextHeight
           &&
          $IsGoodHeap($Heap)
           &&
          this != null
           &&
          $Is(this, Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex))
           && $IsAlloc(this,
            Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex),
            $Heap)
           && $Is(S#0, TSet(_module.BreadthFirstSearch$Vertex)))
       ==> (forall v#0: Box ::
          { _module.BreadthFirstSearch.Succ(_module.BreadthFirstSearch$Vertex, this, v#0) }
            { S#0[v#0] }
          $IsBox(v#0, _module.BreadthFirstSearch$Vertex)
             ==>
            S#0[v#0]
             ==> _module.BreadthFirstSearch.Succ#canCall(_module.BreadthFirstSearch$Vertex, this, v#0))
         && _module.BreadthFirstSearch.IsClosed(_module.BreadthFirstSearch$Vertex, this, S#0)
           == (forall v#0: Box ::
            { _module.BreadthFirstSearch.Succ(_module.BreadthFirstSearch$Vertex, this, v#0) }
              { S#0[v#0] }
            $IsBox(v#0, _module.BreadthFirstSearch$Vertex)
               ==>
              S#0[v#0]
               ==> Set#Subset(_module.BreadthFirstSearch.Succ(_module.BreadthFirstSearch$Vertex, this, v#0),
                S#0)));

// definition axiom for _module.BreadthFirstSearch.IsClosed for all literals(revealed)
axiom 8 <= $FunctionContextHeight
   ==> (forall _module.BreadthFirstSearch$Vertex: Ty, $Heap: Heap, this: ref, S#0: Set Box ::
    {:weight 3} { _module.BreadthFirstSearch.IsClosed(_module.BreadthFirstSearch$Vertex, this, Lit(S#0)), $IsGoodHeap($Heap) }
    _module.BreadthFirstSearch.IsClosed#canCall(_module.BreadthFirstSearch$Vertex, this, Lit(S#0))
         || (8 != $FunctionContextHeight
           &&
          $IsGoodHeap($Heap)
           &&
          this != null
           &&
          $Is(this, Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex))
           && $IsAlloc(this,
            Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex),
            $Heap)
           && $Is(S#0, TSet(_module.BreadthFirstSearch$Vertex)))
       ==> (forall v#1: Box ::
          { _module.BreadthFirstSearch.Succ(_module.BreadthFirstSearch$Vertex, this, v#1) }
            { S#0[v#1] }
          $IsBox(v#1, _module.BreadthFirstSearch$Vertex)
             ==>
            Lit(S#0)[v#1]
             ==> _module.BreadthFirstSearch.Succ#canCall(_module.BreadthFirstSearch$Vertex, this, v#1))
         && _module.BreadthFirstSearch.IsClosed(_module.BreadthFirstSearch$Vertex, this, Lit(S#0))
           == (forall v#1: Box ::
            { _module.BreadthFirstSearch.Succ(_module.BreadthFirstSearch$Vertex, this, v#1) }
              { S#0[v#1] }
            $IsBox(v#1, _module.BreadthFirstSearch$Vertex)
               ==>
              Lit(S#0)[v#1]
               ==> Set#Subset(_module.BreadthFirstSearch.Succ(_module.BreadthFirstSearch$Vertex, this, v#1),
                S#0)));

procedure CheckWellformed$$_module.BreadthFirstSearch.IsClosed(_module.BreadthFirstSearch$Vertex: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex))
         && $IsAlloc(this,
          Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex),
          $Heap),
    S#0: Set Box where $Is(S#0, TSet(_module.BreadthFirstSearch$Vertex)));
  free requires 8 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.BreadthFirstSearch.IsClosed(_module.BreadthFirstSearch$Vertex: Ty, this: ref, S#0: Set Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var v#2: Box;
  var ##x#0: Box;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function IsClosed
    assume {:captureState "BreadthFirstSearch.dfy(20,12): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
          $o != null && read($Heap, $o, alloc) ==> false);
        havoc v#2;
        assume $IsBox(v#2, _module.BreadthFirstSearch$Vertex);
        // Begin Comprehension WF check
        if (S#0[v#2])
        {
            ##x#0 := v#2;
            // assume allocatedness for argument to function
            assume $IsAllocBox(##x#0, _module.BreadthFirstSearch$Vertex, $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume _module.BreadthFirstSearch.Succ#canCall(_module.BreadthFirstSearch$Vertex, this, v#2);
        }

        // End Comprehension WF check
        assume _module.BreadthFirstSearch.IsClosed(_module.BreadthFirstSearch$Vertex, this, S#0)
           == (forall v#3: Box ::
            { _module.BreadthFirstSearch.Succ(_module.BreadthFirstSearch$Vertex, this, v#3) }
              { S#0[v#3] }
            $IsBox(v#3, _module.BreadthFirstSearch$Vertex)
               ==>
              S#0[v#3]
               ==> Set#Subset(_module.BreadthFirstSearch.Succ(_module.BreadthFirstSearch$Vertex, this, v#3),
                S#0));
        assume (forall v#3: Box ::
          { _module.BreadthFirstSearch.Succ(_module.BreadthFirstSearch$Vertex, this, v#3) }
            { S#0[v#3] }
          $IsBox(v#3, _module.BreadthFirstSearch$Vertex)
             ==>
            S#0[v#3]
             ==> _module.BreadthFirstSearch.Succ#canCall(_module.BreadthFirstSearch$Vertex, this, v#3));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.BreadthFirstSearch.IsClosed(_module.BreadthFirstSearch$Vertex, this, S#0),
          TBool);
        assert b$reqreads#0;
    }
}



procedure CheckWellformed$$_module.BreadthFirstSearch.BFS(_module.BreadthFirstSearch$Vertex: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex))
         && $IsAlloc(this,
          Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex),
          $Heap),
    source#0: Box
       where $IsBox(source#0, _module.BreadthFirstSearch$Vertex)
         && $IsAllocBox(source#0, _module.BreadthFirstSearch$Vertex, $Heap),
    dest#0: Box
       where $IsBox(dest#0, _module.BreadthFirstSearch$Vertex)
         && $IsAllocBox(dest#0, _module.BreadthFirstSearch$Vertex, $Heap),
    AllVertices#0: Set Box
       where $Is(AllVertices#0, TSet(_module.BreadthFirstSearch$Vertex))
         && $IsAlloc(AllVertices#0, TSet(_module.BreadthFirstSearch$Vertex), $Heap))
   returns (d#0: int,
    path#0: DatatypeType
       where $Is(path#0, Tclass._module.List(_module.BreadthFirstSearch$Vertex))
         && $IsAlloc(path#0, Tclass._module.List(_module.BreadthFirstSearch$Vertex), $Heap));
  free requires 16 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.BreadthFirstSearch.BFS(_module.BreadthFirstSearch$Vertex: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex))
         && $IsAlloc(this,
          Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex),
          $Heap),
    source#0: Box
       where $IsBox(source#0, _module.BreadthFirstSearch$Vertex)
         && $IsAllocBox(source#0, _module.BreadthFirstSearch$Vertex, $Heap),
    dest#0: Box
       where $IsBox(dest#0, _module.BreadthFirstSearch$Vertex)
         && $IsAllocBox(dest#0, _module.BreadthFirstSearch$Vertex, $Heap),
    AllVertices#0: Set Box
       where $Is(AllVertices#0, TSet(_module.BreadthFirstSearch$Vertex))
         && $IsAlloc(AllVertices#0, TSet(_module.BreadthFirstSearch$Vertex), $Heap))
   returns (d#0: int,
    path#0: DatatypeType
       where $Is(path#0, Tclass._module.List(_module.BreadthFirstSearch$Vertex))
         && $IsAlloc(path#0, Tclass._module.List(_module.BreadthFirstSearch$Vertex), $Heap));
  // user-defined preconditions
  requires AllVertices#0[source#0];
  requires AllVertices#0[dest#0];
  requires _module.BreadthFirstSearch.IsClosed#canCall(_module.BreadthFirstSearch$Vertex, this, AllVertices#0)
     ==> _module.BreadthFirstSearch.IsClosed(_module.BreadthFirstSearch$Vertex, this, AllVertices#0)
       || (forall v#0: Box ::
        { _module.BreadthFirstSearch.Succ(_module.BreadthFirstSearch$Vertex, this, v#0) }
          { AllVertices#0[v#0] }
        $IsBox(v#0, _module.BreadthFirstSearch$Vertex)
           ==>
          AllVertices#0[v#0]
           ==> Set#Subset(_module.BreadthFirstSearch.Succ(_module.BreadthFirstSearch$Vertex, this, v#0),
            AllVertices#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures LitInt(0) <= d#0
     ==> _module.BreadthFirstSearch.IsPath#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, dest#0, path#0)
       && (_module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex, $LS($LZ), this, source#0, dest#0, path#0)
         ==> _module.__default.length#canCall(_module.BreadthFirstSearch$Vertex, path#0));
  ensures LitInt(0) <= d#0
     ==> _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex, $LS($LS($LZ)), this, source#0, dest#0, path#0);
  ensures LitInt(0) <= d#0
     ==> _module.__default.length(_module.BreadthFirstSearch$Vertex, $LS($LS($LZ)), path#0)
       == d#0;
  free ensures LitInt(0) <= d#0
     ==> (forall p#1: DatatypeType ::
      { _module.__default.length(_module.BreadthFirstSearch$Vertex, $LS($LZ), p#1) }
        { _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex, $LS($LZ), this, source#0, dest#0, p#1) }
      $Is(p#1, Tclass._module.List(_module.BreadthFirstSearch$Vertex))
         ==> _module.BreadthFirstSearch.IsPath#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, dest#0, p#1)
           && (_module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex, $LS($LZ), this, source#0, dest#0, p#1)
             ==> _module.__default.length#canCall(_module.BreadthFirstSearch$Vertex, path#0)
               && _module.__default.length#canCall(_module.BreadthFirstSearch$Vertex, p#1)));
  free ensures LitInt(0) <= d#0
     ==> (forall p#1: DatatypeType ::
      {:_induction p#1} { _module.__default.length(_module.BreadthFirstSearch$Vertex, $LS($LZ), p#1) }
        { _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex, $LS($LZ), this, source#0, dest#0, p#1) }
      $Is(p#1, Tclass._module.List(_module.BreadthFirstSearch$Vertex))
         ==>
        _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex, $LS($LZ), this, source#0, dest#0, p#1)
         ==> _module.__default.length(_module.BreadthFirstSearch$Vertex, $LS($LZ), path#0)
           <= _module.__default.length(_module.BreadthFirstSearch$Vertex, $LS($LZ), p#1));
  free ensures d#0 < 0
     ==> (forall p#3: DatatypeType ::
      { _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex, $LS($LZ), this, source#0, dest#0, p#3) }
      $Is(p#3, Tclass._module.List(_module.BreadthFirstSearch$Vertex))
         ==> _module.BreadthFirstSearch.IsPath#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, dest#0, p#3));
  free ensures d#0 < 0
     ==> !(exists p#3: DatatypeType ::
      {:_induction p#3} { _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex, $LS($LZ), this, source#0, dest#0, p#3) }
      $Is(p#3, Tclass._module.List(_module.BreadthFirstSearch$Vertex))
         && _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex, $LS($LZ), this, source#0, dest#0, p#3));
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.BreadthFirstSearch.BFS(_module.BreadthFirstSearch$Vertex: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex))
         && $IsAlloc(this,
          Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex),
          $Heap),
    source#0: Box
       where $IsBox(source#0, _module.BreadthFirstSearch$Vertex)
         && $IsAllocBox(source#0, _module.BreadthFirstSearch$Vertex, $Heap),
    dest#0: Box
       where $IsBox(dest#0, _module.BreadthFirstSearch$Vertex)
         && $IsAllocBox(dest#0, _module.BreadthFirstSearch$Vertex, $Heap),
    AllVertices#0: Set Box
       where $Is(AllVertices#0, TSet(_module.BreadthFirstSearch$Vertex))
         && $IsAlloc(AllVertices#0, TSet(_module.BreadthFirstSearch$Vertex), $Heap))
   returns (d#0: int,
    path#0: DatatypeType
       where $Is(path#0, Tclass._module.List(_module.BreadthFirstSearch$Vertex))
         && $IsAlloc(path#0, Tclass._module.List(_module.BreadthFirstSearch$Vertex), $Heap),
    $_reverifyPost: bool);
  free requires 16 == $FunctionContextHeight;
  // user-defined preconditions
  requires AllVertices#0[source#0];
  requires AllVertices#0[dest#0];
  free requires _module.BreadthFirstSearch.IsClosed#canCall(_module.BreadthFirstSearch$Vertex, this, AllVertices#0)
     &&
    _module.BreadthFirstSearch.IsClosed(_module.BreadthFirstSearch$Vertex, this, AllVertices#0)
     && (forall v#1: Box ::
      { _module.BreadthFirstSearch.Succ(_module.BreadthFirstSearch$Vertex, this, v#1) }
        { AllVertices#0[v#1] }
      $IsBox(v#1, _module.BreadthFirstSearch$Vertex)
         ==>
        AllVertices#0[v#1]
         ==> Set#Subset(_module.BreadthFirstSearch.Succ(_module.BreadthFirstSearch$Vertex, this, v#1),
          AllVertices#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures LitInt(0) <= d#0
     ==> _module.BreadthFirstSearch.IsPath#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, dest#0, path#0)
       && (_module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex, $LS($LZ), this, source#0, dest#0, path#0)
         ==> _module.__default.length#canCall(_module.BreadthFirstSearch$Vertex, path#0));
  ensures LitInt(0) <= d#0
     ==> _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex, $LS($LS($LZ)), this, source#0, dest#0, path#0);
  ensures LitInt(0) <= d#0
     ==> _module.__default.length(_module.BreadthFirstSearch$Vertex, $LS($LS($LZ)), path#0)
       == d#0;
  free ensures LitInt(0) <= d#0
     ==> (forall p#1: DatatypeType ::
      { _module.__default.length(_module.BreadthFirstSearch$Vertex, $LS($LZ), p#1) }
        { _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex, $LS($LZ), this, source#0, dest#0, p#1) }
      $Is(p#1, Tclass._module.List(_module.BreadthFirstSearch$Vertex))
         ==> _module.BreadthFirstSearch.IsPath#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, dest#0, p#1)
           && (_module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex, $LS($LZ), this, source#0, dest#0, p#1)
             ==> _module.__default.length#canCall(_module.BreadthFirstSearch$Vertex, path#0)
               && _module.__default.length#canCall(_module.BreadthFirstSearch$Vertex, p#1)));
  ensures LitInt(0) <= d#0
     ==> (forall p#1: DatatypeType ::
      { _module.__default.length(_module.BreadthFirstSearch$Vertex, $LS($LS($LZ)), p#1) }
        { _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex, $LS($LS($LZ)), this, source#0, dest#0, p#1) }
      $Is(p#1, Tclass._module.List(_module.BreadthFirstSearch$Vertex))
           && (forall p$ih#2#0: DatatypeType ::
            { _module.__default.length(_module.BreadthFirstSearch$Vertex, $LS($LZ), p$ih#2#0) }
              { _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex, $LS($LZ), this, source#0, dest#0, p$ih#2#0) }
            $Is(p$ih#2#0, Tclass._module.List(_module.BreadthFirstSearch$Vertex))
               ==>
              DtRank(p$ih#2#0) < DtRank(p#1)
               ==>
              _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex, $LS($LZ), this, source#0, dest#0, p$ih#2#0)
               ==> _module.__default.length(_module.BreadthFirstSearch$Vertex, $LS($LZ), path#0)
                 <= _module.__default.length(_module.BreadthFirstSearch$Vertex, $LS($LZ), p$ih#2#0))
           &&
          true
           && #_module.List.Nil() == p#1
         ==>
        _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex, $LS($LS($LZ)), this, source#0, dest#0, p#1)
         ==> _module.__default.length(_module.BreadthFirstSearch$Vertex, $LS($LS($LZ)), path#0)
           <= _module.__default.length(_module.BreadthFirstSearch$Vertex, $LS($LS($LZ)), p#1));
  ensures LitInt(0) <= d#0
     ==> (forall p#1: DatatypeType ::
      { _module.__default.length(_module.BreadthFirstSearch$Vertex, $LS($LS($LZ)), p#1) }
        { _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex, $LS($LS($LZ)), this, source#0, dest#0, p#1) }
      $Is(p#1, Tclass._module.List(_module.BreadthFirstSearch$Vertex))
           && (forall p$ih#2#0: DatatypeType ::
            { _module.__default.length(_module.BreadthFirstSearch$Vertex, $LS($LZ), p$ih#2#0) }
              { _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex, $LS($LZ), this, source#0, dest#0, p$ih#2#0) }
            $Is(p$ih#2#0, Tclass._module.List(_module.BreadthFirstSearch$Vertex))
               ==>
              DtRank(p$ih#2#0) < DtRank(p#1)
               ==>
              _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex, $LS($LZ), this, source#0, dest#0, p$ih#2#0)
               ==> _module.__default.length(_module.BreadthFirstSearch$Vertex, $LS($LZ), path#0)
                 <= _module.__default.length(_module.BreadthFirstSearch$Vertex, $LS($LZ), p$ih#2#0))
           &&
          true
           && (exists a#5#0#0: Box, a#5#1#0: DatatypeType ::
            { #_module.List.Cons(a#5#0#0, a#5#1#0) }
            $IsBox(a#5#0#0, _module.BreadthFirstSearch$Vertex)
               && $Is(a#5#1#0, Tclass._module.List(_module.BreadthFirstSearch$Vertex))
               && #_module.List.Cons(a#5#0#0, a#5#1#0) == p#1)
         ==>
        _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex, $LS($LS($LZ)), this, source#0, dest#0, p#1)
         ==> _module.__default.length(_module.BreadthFirstSearch$Vertex, $LS($LS($LZ)), path#0)
           <= _module.__default.length(_module.BreadthFirstSearch$Vertex, $LS($LS($LZ)), p#1));
  free ensures d#0 < 0
     ==> (forall p#3: DatatypeType ::
      { _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex, $LS($LZ), this, source#0, dest#0, p#3) }
      $Is(p#3, Tclass._module.List(_module.BreadthFirstSearch$Vertex))
         ==> _module.BreadthFirstSearch.IsPath#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, dest#0, p#3));
  ensures d#0 < 0
     ==> !(exists p#3: DatatypeType ::
      { _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex, $LS($LS($LZ)), this, source#0, dest#0, p#3) }
      $Is(p#3, Tclass._module.List(_module.BreadthFirstSearch$Vertex))
         && (forall p$ih#3#0: DatatypeType ::
          { _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex, $LS($LZ), this, source#0, dest#0, p$ih#3#0) }
          $Is(p$ih#3#0, Tclass._module.List(_module.BreadthFirstSearch$Vertex))
             ==>
            DtRank(p$ih#3#0) < DtRank(p#3)
             ==> !_module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex, $LS($LZ), this, source#0, dest#0, p$ih#3#0))
         &&
        true
         && #_module.List.Nil() == p#3
         && _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex, $LS($LS($LZ)), this, source#0, dest#0, p#3));
  ensures d#0 < 0
     ==> !(exists p#3: DatatypeType ::
      { _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex, $LS($LS($LZ)), this, source#0, dest#0, p#3) }
      $Is(p#3, Tclass._module.List(_module.BreadthFirstSearch$Vertex))
         && (forall p$ih#3#0: DatatypeType ::
          { _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex, $LS($LZ), this, source#0, dest#0, p$ih#3#0) }
          $Is(p$ih#3#0, Tclass._module.List(_module.BreadthFirstSearch$Vertex))
             ==>
            DtRank(p$ih#3#0) < DtRank(p#3)
             ==> !_module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex, $LS($LZ), this, source#0, dest#0, p$ih#3#0))
         &&
        true
         && (exists a#7#0#0: Box, a#7#1#0: DatatypeType ::
          { #_module.List.Cons(a#7#0#0, a#7#1#0) }
          $IsBox(a#7#0#0, _module.BreadthFirstSearch$Vertex)
             && $Is(a#7#1#0, Tclass._module.List(_module.BreadthFirstSearch$Vertex))
             && #_module.List.Cons(a#7#0#0, a#7#1#0) == p#3)
         && _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex, $LS($LS($LZ)), this, source#0, dest#0, p#3));
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.BreadthFirstSearch.BFS(_module.BreadthFirstSearch$Vertex: Ty,
    this: ref,
    source#0: Box,
    dest#0: Box,
    AllVertices#0: Set Box)
   returns (d#0: int, path#0: DatatypeType, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var V#0: Set Box
     where $Is(V#0, TSet(_module.BreadthFirstSearch$Vertex))
       && $IsAlloc(V#0, TSet(_module.BreadthFirstSearch$Vertex), $Heap);
  var C#0: Set Box
     where $Is(C#0, TSet(_module.BreadthFirstSearch$Vertex))
       && $IsAlloc(C#0, TSet(_module.BreadthFirstSearch$Vertex), $Heap);
  var N#0: Set Box
     where $Is(N#0, TSet(_module.BreadthFirstSearch$Vertex))
       && $IsAlloc(N#0, TSet(_module.BreadthFirstSearch$Vertex), $Heap);
  var $rhs#0: Set Box where $Is($rhs#0, TSet(_module.BreadthFirstSearch$Vertex));
  var $rhs#1: Set Box where $Is($rhs#1, TSet(_module.BreadthFirstSearch$Vertex));
  var $rhs#2: Set Box where $Is($rhs#2, TSet(_module.BreadthFirstSearch$Vertex));
  var Processed#0: Set Box
     where $Is(Processed#0, TSet(_module.BreadthFirstSearch$Vertex))
       && $IsAlloc(Processed#0, TSet(_module.BreadthFirstSearch$Vertex), $Heap);
  var paths#0: Map Box Box
     where $Is(paths#0,
        TMap(_module.BreadthFirstSearch$Vertex,
          Tclass._module.List(_module.BreadthFirstSearch$Vertex)))
       && $IsAlloc(paths#0,
        TMap(_module.BreadthFirstSearch$Vertex,
          Tclass._module.List(_module.BreadthFirstSearch$Vertex)),
        $Heap);
  var $rhs#3: Set Box where $Is($rhs#3, TSet(_module.BreadthFirstSearch$Vertex));
  var $rhs#4: Map Box Box
     where $Is($rhs#4,
      TMap(_module.BreadthFirstSearch$Vertex,
        Tclass._module.List(_module.BreadthFirstSearch$Vertex)));
  var ##m#0: Map Box Box;
  var $PreLoopHeap$loop#0: Heap;
  var $decr_init$loop#00: Set Box;
  var $w$loop#0: bool;
  var ##source#3: Box;
  var ##m#1: Map Box Box;
  var ##m#2: Map Box Box;
  var x#0: Box;
  var ##source#4: Box;
  var ##x#0: Box;
  var ##m#3: Map Box Box;
  var ##list#3: DatatypeType;
  var x#2: Box;
  var ##source#5: Box;
  var ##x#1: Box;
  var ##m#4: Map Box Box;
  var ##list#4: DatatypeType;
  var ##source#6: Box;
  var ##n#0: int;
  var ##AllVertices#0: Set Box;
  var ##source#7: Box;
  var ##n#1: int;
  var ##AllVertices#1: Set Box;
  var ##source#8: Box;
  var ##n#2: int;
  var ##AllVertices#2: Set Box;
  var ##S#1: Set Box;
  var ##AllVertices#3: Set Box;
  var ##source#9: Box;
  var ##n#3: int;
  var ##AllVertices#4: Set Box;
  var $decr$loop#00: Set Box;
  var v#0_0: Box
     where $IsBox(v#0_0, _module.BreadthFirstSearch$Vertex)
       && $IsAllocBox(v#0_0, _module.BreadthFirstSearch$Vertex, $Heap);
  var $rhs#0_0: Set Box where $Is($rhs#0_0, TSet(_module.BreadthFirstSearch$Vertex));
  var $rhs#0_1: Set Box where $Is($rhs#0_1, TSet(_module.BreadthFirstSearch$Vertex));
  var pathToV#0_0: DatatypeType
     where $Is(pathToV#0_0, Tclass._module.List(_module.BreadthFirstSearch$Vertex))
       && $IsAlloc(pathToV#0_0, Tclass._module.List(_module.BreadthFirstSearch$Vertex), $Heap);
  var ##source#0_0: Box;
  var ##x#0_0: Box;
  var ##m#0_0: Map Box Box;
  var p#0_0_0: DatatypeType;
  var ##source#0_0_0: Box;
  var ##dest#0_0_0: Box;
  var ##p#0_0_0: DatatypeType;
  var source##0_0_0: Box;
  var x##0_0_0: Box;
  var p##0_0_0: DatatypeType;
  var AllVertices##0_0_0: Set Box;
  var ##list#0_0_0: DatatypeType;
  var ##list#0_0_1: DatatypeType;
  var source##0_0_0_0: Box;
  var m##0_0_0_0: int;
  var ##list#0_0_0_0: DatatypeType;
  var n##0_0_0_0: int;
  var AllVertices##0_0_0_0: Set Box;
  var $rhs#0_0_0: int;
  var $rhs#0_0_1: DatatypeType
     where $Is($rhs#0_0_1, Tclass._module.List(_module.BreadthFirstSearch$Vertex));
  var newlyEncountered#0_0: Set Box
     where $Is(newlyEncountered#0_0, TSet(_module.BreadthFirstSearch$Vertex))
       && $IsAlloc(newlyEncountered#0_0, TSet(_module.BreadthFirstSearch$Vertex), $Heap);
  var w#0_0: Box;
  var ##x#0_1: Box;
  var $rhs#0_2: Set Box where $Is($rhs#0_2, TSet(_module.BreadthFirstSearch$Vertex));
  var $rhs#0_3: Set Box where $Is($rhs#0_3, TSet(_module.BreadthFirstSearch$Vertex));
  var $rhs##0_0: Map Box Box
     where $Is($rhs##0_0,
        TMap(_module.BreadthFirstSearch$Vertex,
          Tclass._module.List(_module.BreadthFirstSearch$Vertex)))
       && $IsAlloc($rhs##0_0,
        TMap(_module.BreadthFirstSearch$Vertex,
          Tclass._module.List(_module.BreadthFirstSearch$Vertex)),
        $Heap);
  var vSuccs##0_0: Set Box;
  var source##0_0: Box;
  var paths##0_0: Map Box Box;
  var v##0_0: Box;
  var pathToV##0_0: DatatypeType;
  var $rhs#0_1_0: Set Box
     where $Is($rhs#0_1_0, TSet(_module.BreadthFirstSearch$Vertex));
  var $rhs#0_1_1: Set Box
     where $Is($rhs#0_1_1, TSet(_module.BreadthFirstSearch$Vertex));
  var $rhs#0_1_2: int;
  var n#0: int;
  var source##1_0: Box;
  var m##1_0: int;
  var n##1_0: int;
  var AllVertices##1_0: Set Box;
  var source##0: Box;
  var m##0: int;
  var n##0: int;
  var AllVertices##0: Set Box;
  var p#4: DatatypeType;
  var ##source#10: Box;
  var ##dest#3: Box;
  var ##p#3: DatatypeType;
  var source##1: Box;
  var x##0: Box;
  var p##0: DatatypeType;
  var AllVertices##1: Set Box;

    // AddMethodImpl: BFS, Impl$$_module.BreadthFirstSearch.BFS
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "BreadthFirstSearch.dfy(45,2): initial state"} true;
    $_reverifyPost := false;
    // ----- update statement ----- BreadthFirstSearch.dfy(46,17)
    assume true;
    assume true;
    assume true;
    assume true;
    $rhs#0 := Set#UnionOne(Set#Empty(): Set Box, source#0);
    assume true;
    $rhs#1 := Set#UnionOne(Set#Empty(): Set Box, source#0);
    assume true;
    $rhs#2 := Lit(Set#Empty(): Set Box);
    V#0 := $rhs#0;
    C#0 := $rhs#1;
    N#0 := $rhs#2;
    assume {:captureState "BreadthFirstSearch.dfy(46,41)"} true;
    // ----- update statement ----- BreadthFirstSearch.dfy(47,32)
    assume true;
    assume true;
    assume true;
    $rhs#3 := Lit(Set#Empty(): Set Box);
    assume true;
    $rhs#4 := Map#Build(Map#Empty(): Map Box Box, source#0, $Box(Lit(#_module.List.Nil())));
    Processed#0 := $rhs#3;
    paths#0 := $rhs#4;
    assume {:captureState "BreadthFirstSearch.dfy(47,56)"} true;
    // ----- assert statement ----- BreadthFirstSearch.dfy(48,5)
    ##m#0 := paths#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##m#0,
      TMap(_module.BreadthFirstSearch$Vertex,
        Tclass._module.List(_module.BreadthFirstSearch$Vertex)),
      $Heap);
    assume _module.__default.domain#canCall(_module.BreadthFirstSearch$Vertex,
      Tclass._module.List(_module.BreadthFirstSearch$Vertex),
      paths#0);
    assume _module.__default.domain#canCall(_module.BreadthFirstSearch$Vertex,
      Tclass._module.List(_module.BreadthFirstSearch$Vertex),
      paths#0);
    assert Set#Equal(_module.__default.domain(_module.BreadthFirstSearch$Vertex,
        Tclass._module.List(_module.BreadthFirstSearch$Vertex),
        paths#0),
      Set#UnionOne(Set#Empty(): Set Box, source#0));
    // ----- assignment statement ----- BreadthFirstSearch.dfy(55,7)
    assume true;
    assume true;
    d#0 := LitInt(0);
    assume {:captureState "BreadthFirstSearch.dfy(55,10)"} true;
    // ----- while statement ----- BreadthFirstSearch.dfy(56,5)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    $decr_init$loop#00 := Set#Difference(AllVertices#0, Processed#0);
    havoc $w$loop#0;
    while (true)
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0 ==> Set#Subset(V#0, AllVertices#0);
      invariant $w$loop#0 ==> Set#Subset(Processed#0, AllVertices#0);
      invariant $w$loop#0 ==> Set#Subset(C#0, AllVertices#0);
      invariant $w$loop#0 ==> Set#Subset(N#0, AllVertices#0);
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0 ==> V#0[source#0];
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0 ==> Set#Equal(V#0, Set#Union(Set#Union(Processed#0, C#0), N#0));
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0 ==> Set#Disjoint(Processed#0, C#0);
      invariant $w$loop#0 ==> Set#Disjoint(Processed#0, C#0);
      invariant $w$loop#0 ==> Set#Disjoint(Set#Union(Processed#0, C#0), N#0);
      free invariant $w$loop#0
         ==> _module.BreadthFirstSearch.ValidMap#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, paths#0);
      invariant $w$loop#0
         ==>
        _module.BreadthFirstSearch.ValidMap#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, paths#0)
         ==> _module.BreadthFirstSearch.ValidMap(_module.BreadthFirstSearch$Vertex, this, source#0, paths#0)
           || (forall v#2: Box ::
            { $Unbox(Map#Elements(paths#0)[v#2]): DatatypeType }
              { Map#Domain(paths#0)[v#2] }
            $IsBox(v#2, _module.BreadthFirstSearch$Vertex)
               ==>
              Map#Domain(paths#0)[v#2]
               ==> _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex,
                $LS($LS($LZ)),
                this,
                source#0,
                v#2,
                $Unbox(Map#Elements(paths#0)[v#2]): DatatypeType));
      free invariant $w$loop#0
         ==> _module.BreadthFirstSearch.ValidMap#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, paths#0)
           &&
          _module.BreadthFirstSearch.ValidMap(_module.BreadthFirstSearch$Vertex, this, source#0, paths#0)
           && (forall v#2: Box ::
            { $Unbox(Map#Elements(paths#0)[v#2]): DatatypeType }
              { Map#Domain(paths#0)[v#2] }
            $IsBox(v#2, _module.BreadthFirstSearch$Vertex)
               ==>
              Map#Domain(paths#0)[v#2]
               ==> _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex,
                $LS($LZ),
                this,
                source#0,
                v#2,
                $Unbox(Map#Elements(paths#0)[v#2]): DatatypeType));
      free invariant $w$loop#0
         ==> _module.__default.domain#canCall(_module.BreadthFirstSearch$Vertex,
          Tclass._module.List(_module.BreadthFirstSearch$Vertex),
          paths#0);
      invariant $w$loop#0
         ==> Set#Equal(V#0,
          _module.__default.domain(_module.BreadthFirstSearch$Vertex,
            Tclass._module.List(_module.BreadthFirstSearch$Vertex),
            paths#0));
      free invariant $w$loop#0
         ==> (forall x#1: Box ::
          { _module.BreadthFirstSearch.Find(_module.BreadthFirstSearch$Vertex, this, source#0, x#1, paths#0) }
            { C#0[x#1] }
          $IsBox(x#1, _module.BreadthFirstSearch$Vertex)
             ==>
            C#0[x#1]
             ==> _module.BreadthFirstSearch.Find#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, x#1, paths#0)
               && _module.__default.length#canCall(_module.BreadthFirstSearch$Vertex,
                _module.BreadthFirstSearch.Find(_module.BreadthFirstSearch$Vertex, this, source#0, x#1, paths#0)));
      invariant $w$loop#0
         ==> (forall x#1: Box ::
          { _module.BreadthFirstSearch.Find(_module.BreadthFirstSearch$Vertex, this, source#0, x#1, paths#0) }
            { C#0[x#1] }
          $IsBox(x#1, _module.BreadthFirstSearch$Vertex)
             ==>
            C#0[x#1]
             ==> _module.__default.length(_module.BreadthFirstSearch$Vertex,
                $LS($LS($LZ)),
                _module.BreadthFirstSearch.Find(_module.BreadthFirstSearch$Vertex, this, source#0, x#1, paths#0))
               == d#0);
      free invariant $w$loop#0
         ==> (forall x#1: Box ::
          { _module.BreadthFirstSearch.Find(_module.BreadthFirstSearch$Vertex, this, source#0, x#1, paths#0) }
            { C#0[x#1] }
          $IsBox(x#1, _module.BreadthFirstSearch$Vertex)
             ==>
            C#0[x#1]
             ==> _module.__default.length(_module.BreadthFirstSearch$Vertex,
                $LS($LZ),
                _module.BreadthFirstSearch.Find(_module.BreadthFirstSearch$Vertex, this, source#0, x#1, paths#0))
               == d#0);
      free invariant $w$loop#0
         ==> (forall x#3: Box ::
          { _module.BreadthFirstSearch.Find(_module.BreadthFirstSearch$Vertex, this, source#0, x#3, paths#0) }
            { N#0[x#3] }
          $IsBox(x#3, _module.BreadthFirstSearch$Vertex)
             ==>
            N#0[x#3]
             ==> _module.BreadthFirstSearch.Find#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, x#3, paths#0)
               && _module.__default.length#canCall(_module.BreadthFirstSearch$Vertex,
                _module.BreadthFirstSearch.Find(_module.BreadthFirstSearch$Vertex, this, source#0, x#3, paths#0)));
      invariant $w$loop#0
         ==> (forall x#3: Box ::
          { _module.BreadthFirstSearch.Find(_module.BreadthFirstSearch$Vertex, this, source#0, x#3, paths#0) }
            { N#0[x#3] }
          $IsBox(x#3, _module.BreadthFirstSearch$Vertex)
             ==>
            N#0[x#3]
             ==> _module.__default.length(_module.BreadthFirstSearch$Vertex,
                $LS($LS($LZ)),
                _module.BreadthFirstSearch.Find(_module.BreadthFirstSearch$Vertex, this, source#0, x#3, paths#0))
               == d#0 + 1);
      free invariant $w$loop#0
         ==> (forall x#3: Box ::
          { _module.BreadthFirstSearch.Find(_module.BreadthFirstSearch$Vertex, this, source#0, x#3, paths#0) }
            { N#0[x#3] }
          $IsBox(x#3, _module.BreadthFirstSearch$Vertex)
             ==>
            N#0[x#3]
             ==> _module.__default.length(_module.BreadthFirstSearch$Vertex,
                $LS($LZ),
                _module.BreadthFirstSearch.Find(_module.BreadthFirstSearch$Vertex, this, source#0, x#3, paths#0))
               == d#0 + 1);
      free invariant $w$loop#0
         ==> _module.BreadthFirstSearch.R#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, d#0, AllVertices#0);
      invariant $w$loop#0
         ==>
        _module.BreadthFirstSearch.R(_module.BreadthFirstSearch$Vertex, $LS($LZ), this, source#0, d#0, AllVertices#0)[dest#0]
         ==> C#0[dest#0];
      free invariant $w$loop#0
         ==>
        d#0 != 0
         ==> _module.BreadthFirstSearch.R#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, d#0 - 1, AllVertices#0);
      invariant $w$loop#0
         ==>
        d#0 != 0
         ==> !_module.BreadthFirstSearch.R(_module.BreadthFirstSearch$Vertex,
          $LS($LS($LZ)),
          this,
          source#0,
          d#0 - 1,
          AllVertices#0)[dest#0];
      free invariant $w$loop#0
         ==> _module.BreadthFirstSearch.R#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, d#0, AllVertices#0);
      invariant $w$loop#0
         ==> Set#Equal(Set#Union(Processed#0, C#0),
          _module.BreadthFirstSearch.R(_module.BreadthFirstSearch$Vertex,
            $LS($LS($LZ)),
            this,
            source#0,
            d#0,
            AllVertices#0));
      free invariant $w$loop#0
         ==> _module.BreadthFirstSearch.Successors#canCall(_module.BreadthFirstSearch$Vertex, this, Processed#0, AllVertices#0)
           && _module.BreadthFirstSearch.R#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, d#0, AllVertices#0);
      invariant $w$loop#0
         ==> Set#Equal(N#0,
          Set#Difference(_module.BreadthFirstSearch.Successors(_module.BreadthFirstSearch$Vertex, this, Processed#0, AllVertices#0),
            _module.BreadthFirstSearch.R(_module.BreadthFirstSearch$Vertex,
              $LS($LS($LZ)),
              this,
              source#0,
              d#0,
              AllVertices#0)));
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0
         ==>
        Set#Equal(C#0, Set#Empty(): Set Box)
         ==> Set#Equal(N#0, Set#Empty(): Set Box);
      free invariant (forall<alpha> $o: ref, $f: Field alpha ::
        { read($Heap, $o, $f) }
        $o != null && read(old($Heap), $o, alloc)
           ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0, $o, $f));
      free invariant $HeapSucc($PreLoopHeap$loop#0, $Heap);
      free invariant (forall<alpha> $o: ref, $f: Field alpha ::
        { read($Heap, $o, $f) }
        $o != null && read($PreLoopHeap$loop#0, $o, alloc)
           ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0, $o, $f) || $_Frame[$o, $f]);
      free invariant Set#Subset(Set#Difference(AllVertices#0, Processed#0), $decr_init$loop#00)
         && (Set#Equal(Set#Difference(AllVertices#0, Processed#0), $decr_init$loop#00)
           ==> true);
    {
        assume {:captureState "BreadthFirstSearch.dfy(56,4): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            if (Set#Subset(V#0, AllVertices#0))
            {
            }

            if (Set#Subset(V#0, AllVertices#0) && Set#Subset(Processed#0, AllVertices#0))
            {
            }

            if (Set#Subset(V#0, AllVertices#0)
               && Set#Subset(Processed#0, AllVertices#0)
               && Set#Subset(C#0, AllVertices#0))
            {
            }

            assume true;
            assume Set#Subset(V#0, AllVertices#0)
               && Set#Subset(Processed#0, AllVertices#0)
               && Set#Subset(C#0, AllVertices#0)
               && Set#Subset(N#0, AllVertices#0);
            assume true;
            assume V#0[source#0];
            assume true;
            assume Set#Equal(V#0, Set#Union(Set#Union(Processed#0, C#0), N#0));
            if (Set#Disjoint(Processed#0, C#0))
            {
            }

            if (Set#Disjoint(Processed#0, C#0) && Set#Disjoint(Processed#0, C#0))
            {
            }

            assume true;
            assume Set#Disjoint(Processed#0, C#0)
               && Set#Disjoint(Processed#0, C#0)
               && Set#Disjoint(Set#Union(Processed#0, C#0), N#0);
            ##source#3 := source#0;
            // assume allocatedness for argument to function
            assume $IsAllocBox(##source#3, _module.BreadthFirstSearch$Vertex, $Heap);
            ##m#1 := paths#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##m#1,
              TMap(_module.BreadthFirstSearch$Vertex,
                Tclass._module.List(_module.BreadthFirstSearch$Vertex)),
              $Heap);
            assume _module.BreadthFirstSearch.ValidMap#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, paths#0);
            assume _module.BreadthFirstSearch.ValidMap#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, paths#0);
            assume _module.BreadthFirstSearch.ValidMap(_module.BreadthFirstSearch$Vertex, this, source#0, paths#0);
            ##m#2 := paths#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##m#2,
              TMap(_module.BreadthFirstSearch$Vertex,
                Tclass._module.List(_module.BreadthFirstSearch$Vertex)),
              $Heap);
            assume _module.__default.domain#canCall(_module.BreadthFirstSearch$Vertex,
              Tclass._module.List(_module.BreadthFirstSearch$Vertex),
              paths#0);
            assume _module.__default.domain#canCall(_module.BreadthFirstSearch$Vertex,
              Tclass._module.List(_module.BreadthFirstSearch$Vertex),
              paths#0);
            assume Set#Equal(V#0,
              _module.__default.domain(_module.BreadthFirstSearch$Vertex,
                Tclass._module.List(_module.BreadthFirstSearch$Vertex),
                paths#0));
            havoc x#0;
            assume $IsBox(x#0, _module.BreadthFirstSearch$Vertex);
            // Begin Comprehension WF check
            if (C#0[x#0])
            {
                ##source#4 := source#0;
                // assume allocatedness for argument to function
                assume $IsAllocBox(##source#4, _module.BreadthFirstSearch$Vertex, $Heap);
                ##x#0 := x#0;
                // assume allocatedness for argument to function
                assume $IsAllocBox(##x#0, _module.BreadthFirstSearch$Vertex, $Heap);
                ##m#3 := paths#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##m#3,
                  TMap(_module.BreadthFirstSearch$Vertex,
                    Tclass._module.List(_module.BreadthFirstSearch$Vertex)),
                  $Heap);
                assert {:subsumption 0} _module.BreadthFirstSearch.ValidMap#canCall(_module.BreadthFirstSearch$Vertex, this, ##source#4, ##m#3)
                   ==> _module.BreadthFirstSearch.ValidMap(_module.BreadthFirstSearch$Vertex, this, ##source#4, ##m#3)
                     || (forall v#3: Box ::
                      { $Unbox(Map#Elements(##m#3)[v#3]): DatatypeType } { Map#Domain(##m#3)[v#3] }
                      $IsBox(v#3, _module.BreadthFirstSearch$Vertex)
                         ==>
                        Map#Domain(##m#3)[v#3]
                         ==> _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex,
                          $LS($LS($LZ)),
                          this,
                          ##source#4,
                          v#3,
                          $Unbox(Map#Elements(##m#3)[v#3]): DatatypeType));
                assert {:subsumption 0} Map#Domain(##m#3)[##x#0];
                assume _module.BreadthFirstSearch.Find#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, x#0, paths#0);
                ##list#3 := _module.BreadthFirstSearch.Find(_module.BreadthFirstSearch$Vertex, this, source#0, x#0, paths#0);
                // assume allocatedness for argument to function
                assume $IsAlloc(##list#3, Tclass._module.List(_module.BreadthFirstSearch$Vertex), $Heap);
                assume _module.__default.length#canCall(_module.BreadthFirstSearch$Vertex,
                  _module.BreadthFirstSearch.Find(_module.BreadthFirstSearch$Vertex, this, source#0, x#0, paths#0));
            }

            // End Comprehension WF check
            assume (forall x#1: Box ::
              { _module.BreadthFirstSearch.Find(_module.BreadthFirstSearch$Vertex, this, source#0, x#1, paths#0) }
                { C#0[x#1] }
              $IsBox(x#1, _module.BreadthFirstSearch$Vertex)
                 ==>
                C#0[x#1]
                 ==> _module.BreadthFirstSearch.Find#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, x#1, paths#0)
                   && _module.__default.length#canCall(_module.BreadthFirstSearch$Vertex,
                    _module.BreadthFirstSearch.Find(_module.BreadthFirstSearch$Vertex, this, source#0, x#1, paths#0)));
            assume (forall x#1: Box ::
              { _module.BreadthFirstSearch.Find(_module.BreadthFirstSearch$Vertex, this, source#0, x#1, paths#0) }
                { C#0[x#1] }
              $IsBox(x#1, _module.BreadthFirstSearch$Vertex)
                 ==>
                C#0[x#1]
                 ==> _module.__default.length(_module.BreadthFirstSearch$Vertex,
                    $LS($LZ),
                    _module.BreadthFirstSearch.Find(_module.BreadthFirstSearch$Vertex, this, source#0, x#1, paths#0))
                   == d#0);
            havoc x#2;
            assume $IsBox(x#2, _module.BreadthFirstSearch$Vertex);
            // Begin Comprehension WF check
            if (N#0[x#2])
            {
                ##source#5 := source#0;
                // assume allocatedness for argument to function
                assume $IsAllocBox(##source#5, _module.BreadthFirstSearch$Vertex, $Heap);
                ##x#1 := x#2;
                // assume allocatedness for argument to function
                assume $IsAllocBox(##x#1, _module.BreadthFirstSearch$Vertex, $Heap);
                ##m#4 := paths#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##m#4,
                  TMap(_module.BreadthFirstSearch$Vertex,
                    Tclass._module.List(_module.BreadthFirstSearch$Vertex)),
                  $Heap);
                assert {:subsumption 0} _module.BreadthFirstSearch.ValidMap#canCall(_module.BreadthFirstSearch$Vertex, this, ##source#5, ##m#4)
                   ==> _module.BreadthFirstSearch.ValidMap(_module.BreadthFirstSearch$Vertex, this, ##source#5, ##m#4)
                     || (forall v#4: Box ::
                      { $Unbox(Map#Elements(##m#4)[v#4]): DatatypeType } { Map#Domain(##m#4)[v#4] }
                      $IsBox(v#4, _module.BreadthFirstSearch$Vertex)
                         ==>
                        Map#Domain(##m#4)[v#4]
                         ==> _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex,
                          $LS($LS($LZ)),
                          this,
                          ##source#5,
                          v#4,
                          $Unbox(Map#Elements(##m#4)[v#4]): DatatypeType));
                assert {:subsumption 0} Map#Domain(##m#4)[##x#1];
                assume _module.BreadthFirstSearch.Find#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, x#2, paths#0);
                ##list#4 := _module.BreadthFirstSearch.Find(_module.BreadthFirstSearch$Vertex, this, source#0, x#2, paths#0);
                // assume allocatedness for argument to function
                assume $IsAlloc(##list#4, Tclass._module.List(_module.BreadthFirstSearch$Vertex), $Heap);
                assume _module.__default.length#canCall(_module.BreadthFirstSearch$Vertex,
                  _module.BreadthFirstSearch.Find(_module.BreadthFirstSearch$Vertex, this, source#0, x#2, paths#0));
            }

            // End Comprehension WF check
            assume (forall x#3: Box ::
              { _module.BreadthFirstSearch.Find(_module.BreadthFirstSearch$Vertex, this, source#0, x#3, paths#0) }
                { N#0[x#3] }
              $IsBox(x#3, _module.BreadthFirstSearch$Vertex)
                 ==>
                N#0[x#3]
                 ==> _module.BreadthFirstSearch.Find#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, x#3, paths#0)
                   && _module.__default.length#canCall(_module.BreadthFirstSearch$Vertex,
                    _module.BreadthFirstSearch.Find(_module.BreadthFirstSearch$Vertex, this, source#0, x#3, paths#0)));
            assume (forall x#3: Box ::
              { _module.BreadthFirstSearch.Find(_module.BreadthFirstSearch$Vertex, this, source#0, x#3, paths#0) }
                { N#0[x#3] }
              $IsBox(x#3, _module.BreadthFirstSearch$Vertex)
                 ==>
                N#0[x#3]
                 ==> _module.__default.length(_module.BreadthFirstSearch$Vertex,
                    $LS($LZ),
                    _module.BreadthFirstSearch.Find(_module.BreadthFirstSearch$Vertex, this, source#0, x#3, paths#0))
                   == d#0 + 1);
            ##source#6 := source#0;
            // assume allocatedness for argument to function
            assume $IsAllocBox(##source#6, _module.BreadthFirstSearch$Vertex, $Heap);
            assert $Is(d#0, Tclass._System.nat());
            ##n#0 := d#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#0, Tclass._System.nat(), $Heap);
            ##AllVertices#0 := AllVertices#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##AllVertices#0, TSet(_module.BreadthFirstSearch$Vertex), $Heap);
            assume _module.BreadthFirstSearch.R#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, d#0, AllVertices#0);
            if (_module.BreadthFirstSearch.R(_module.BreadthFirstSearch$Vertex, $LS($LZ), this, source#0, d#0, AllVertices#0)[dest#0])
            {
            }

            assume _module.BreadthFirstSearch.R#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, d#0, AllVertices#0);
            assume _module.BreadthFirstSearch.R(_module.BreadthFirstSearch$Vertex, $LS($LZ), this, source#0, d#0, AllVertices#0)[dest#0]
               ==> C#0[dest#0];
            if (d#0 != 0)
            {
                ##source#7 := source#0;
                // assume allocatedness for argument to function
                assume $IsAllocBox(##source#7, _module.BreadthFirstSearch$Vertex, $Heap);
                assert $Is(d#0 - 1, Tclass._System.nat());
                ##n#1 := d#0 - 1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##n#1, Tclass._System.nat(), $Heap);
                ##AllVertices#1 := AllVertices#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##AllVertices#1, TSet(_module.BreadthFirstSearch$Vertex), $Heap);
                assume _module.BreadthFirstSearch.R#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, d#0 - 1, AllVertices#0);
            }

            assume d#0 != 0
               ==> _module.BreadthFirstSearch.R#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, d#0 - 1, AllVertices#0);
            assume d#0 != 0
               ==> !_module.BreadthFirstSearch.R(_module.BreadthFirstSearch$Vertex,
                $LS($LZ),
                this,
                source#0,
                d#0 - 1,
                AllVertices#0)[dest#0];
            ##source#8 := source#0;
            // assume allocatedness for argument to function
            assume $IsAllocBox(##source#8, _module.BreadthFirstSearch$Vertex, $Heap);
            assert $Is(d#0, Tclass._System.nat());
            ##n#2 := d#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#2, Tclass._System.nat(), $Heap);
            ##AllVertices#2 := AllVertices#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##AllVertices#2, TSet(_module.BreadthFirstSearch$Vertex), $Heap);
            assume _module.BreadthFirstSearch.R#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, d#0, AllVertices#0);
            assume _module.BreadthFirstSearch.R#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, d#0, AllVertices#0);
            assume Set#Equal(Set#Union(Processed#0, C#0),
              _module.BreadthFirstSearch.R(_module.BreadthFirstSearch$Vertex, $LS($LZ), this, source#0, d#0, AllVertices#0));
            ##S#1 := Processed#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##S#1, TSet(_module.BreadthFirstSearch$Vertex), $Heap);
            ##AllVertices#3 := AllVertices#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##AllVertices#3, TSet(_module.BreadthFirstSearch$Vertex), $Heap);
            assume _module.BreadthFirstSearch.Successors#canCall(_module.BreadthFirstSearch$Vertex, this, Processed#0, AllVertices#0);
            ##source#9 := source#0;
            // assume allocatedness for argument to function
            assume $IsAllocBox(##source#9, _module.BreadthFirstSearch$Vertex, $Heap);
            assert $Is(d#0, Tclass._System.nat());
            ##n#3 := d#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#3, Tclass._System.nat(), $Heap);
            ##AllVertices#4 := AllVertices#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##AllVertices#4, TSet(_module.BreadthFirstSearch$Vertex), $Heap);
            assume _module.BreadthFirstSearch.R#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, d#0, AllVertices#0);
            assume _module.BreadthFirstSearch.Successors#canCall(_module.BreadthFirstSearch$Vertex, this, Processed#0, AllVertices#0)
               && _module.BreadthFirstSearch.R#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, d#0, AllVertices#0);
            assume Set#Equal(N#0,
              Set#Difference(_module.BreadthFirstSearch.Successors(_module.BreadthFirstSearch$Vertex, this, Processed#0, AllVertices#0),
                _module.BreadthFirstSearch.R(_module.BreadthFirstSearch$Vertex, $LS($LZ), this, source#0, d#0, AllVertices#0)));
            if (Set#Equal(C#0, Set#Empty(): Set Box))
            {
            }

            assume true;
            assume Set#Equal(C#0, Set#Empty(): Set Box) ==> Set#Equal(N#0, Set#Empty(): Set Box);
            assume true;
            assume false;
        }

        assume true;
        if (Set#Equal(C#0, Set#Empty(): Set Box))
        {
            break;
        }

        $decr$loop#00 := Set#Difference(AllVertices#0, Processed#0);
        // ----- assign-such-that statement ----- BreadthFirstSearch.dfy(84,13)
        assume true;
        havoc v#0_0;
        assume true;
        assert (exists $as#v0_0#0_0: Box ::
          $IsBox($as#v0_0#0_0, _module.BreadthFirstSearch$Vertex) && C#0[$as#v0_0#0_0]);
        assume C#0[v#0_0];
        assume {:captureState "BreadthFirstSearch.dfy(84,21)"} true;
        // ----- update statement ----- BreadthFirstSearch.dfy(85,20)
        assume true;
        assume true;
        assume true;
        $rhs#0_0 := Set#Difference(C#0, Set#UnionOne(Set#Empty(): Set Box, v#0_0));
        assume true;
        $rhs#0_1 := Set#Union(Processed#0, Set#UnionOne(Set#Empty(): Set Box, v#0_0));
        C#0 := $rhs#0_0;
        Processed#0 := $rhs#0_1;
        assume {:captureState "BreadthFirstSearch.dfy(85,46)"} true;
        // ----- assignment statement ----- BreadthFirstSearch.dfy(86,25)
        assume true;
        ##source#0_0 := source#0;
        // assume allocatedness for argument to function
        assume $IsAllocBox(##source#0_0, _module.BreadthFirstSearch$Vertex, $Heap);
        ##x#0_0 := v#0_0;
        // assume allocatedness for argument to function
        assume $IsAllocBox(##x#0_0, _module.BreadthFirstSearch$Vertex, $Heap);
        ##m#0_0 := paths#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##m#0_0,
          TMap(_module.BreadthFirstSearch$Vertex,
            Tclass._module.List(_module.BreadthFirstSearch$Vertex)),
          $Heap);
        assert {:subsumption 0} _module.BreadthFirstSearch.ValidMap#canCall(_module.BreadthFirstSearch$Vertex, this, ##source#0_0, ##m#0_0)
           ==> _module.BreadthFirstSearch.ValidMap(_module.BreadthFirstSearch$Vertex, this, ##source#0_0, ##m#0_0)
             || (forall v#0_1: Box ::
              { $Unbox(Map#Elements(##m#0_0)[v#0_1]): DatatypeType }
                { Map#Domain(##m#0_0)[v#0_1] }
              $IsBox(v#0_1, _module.BreadthFirstSearch$Vertex)
                 ==>
                Map#Domain(##m#0_0)[v#0_1]
                 ==> _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex,
                  $LS($LS($LZ)),
                  this,
                  ##source#0_0,
                  v#0_1,
                  $Unbox(Map#Elements(##m#0_0)[v#0_1]): DatatypeType));
        assert {:subsumption 0} Map#Domain(##m#0_0)[##x#0_0];
        assume _module.BreadthFirstSearch.ValidMap(_module.BreadthFirstSearch$Vertex, this, ##source#0_0, ##m#0_0)
           && Map#Domain(##m#0_0)[##x#0_0];
        assume _module.BreadthFirstSearch.Find#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, v#0_0, paths#0);
        assume _module.BreadthFirstSearch.Find#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, v#0_0, paths#0);
        pathToV#0_0 := _module.BreadthFirstSearch.Find(_module.BreadthFirstSearch$Vertex, this, source#0, v#0_0, paths#0);
        assume {:captureState "BreadthFirstSearch.dfy(86,49)"} true;
        // ----- if statement ----- BreadthFirstSearch.dfy(88,7)
        assume true;
        if (v#0_0 == dest#0)
        {
            // ----- forall statement (proof) ----- BreadthFirstSearch.dfy(89,9)
            if (*)
            {
                // Assume Fuel Constant
                havoc p#0_0_0;
                assume $Is(p#0_0_0, Tclass._module.List(_module.BreadthFirstSearch$Vertex));
                ##source#0_0_0 := source#0;
                // assume allocatedness for argument to function
                assume $IsAllocBox(##source#0_0_0, _module.BreadthFirstSearch$Vertex, $Heap);
                ##dest#0_0_0 := dest#0;
                // assume allocatedness for argument to function
                assume $IsAllocBox(##dest#0_0_0, _module.BreadthFirstSearch$Vertex, $Heap);
                ##p#0_0_0 := p#0_0_0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##p#0_0_0, Tclass._module.List(_module.BreadthFirstSearch$Vertex), $Heap);
                assume _module.BreadthFirstSearch.IsPath#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, dest#0, p#0_0_0);
                assume _module.BreadthFirstSearch.IsPath#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, dest#0, p#0_0_0);
                assume _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex, $LS($LZ), this, source#0, dest#0, p#0_0_0);
                // ----- call statement ----- BreadthFirstSearch.dfy(92,25)
                // TrCallStmt: Before ProcessCallStmt
                assume true;
                // ProcessCallStmt: CheckSubrange
                source##0_0_0 := source#0;
                assume true;
                // ProcessCallStmt: CheckSubrange
                x##0_0_0 := dest#0;
                assume true;
                // ProcessCallStmt: CheckSubrange
                p##0_0_0 := p#0_0_0;
                assume true;
                // ProcessCallStmt: CheckSubrange
                AllVertices##0_0_0 := AllVertices#0;
                assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                // ProcessCallStmt: Make the call
                call Call$$_module.BreadthFirstSearch.Lemma__IsPath__R(_module.BreadthFirstSearch$Vertex, this, source##0_0_0, x##0_0_0, p##0_0_0, AllVertices##0_0_0);
                // TrCallStmt: After ProcessCallStmt
                assume {:captureState "BreadthFirstSearch.dfy(92,54)"} true;
                // ----- if statement ----- BreadthFirstSearch.dfy(93,11)
                ##list#0_0_0 := p#0_0_0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##list#0_0_0, Tclass._module.List(_module.BreadthFirstSearch$Vertex), $Heap);
                assume _module.__default.length#canCall(_module.BreadthFirstSearch$Vertex, p#0_0_0);
                ##list#0_0_1 := pathToV#0_0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##list#0_0_1, Tclass._module.List(_module.BreadthFirstSearch$Vertex), $Heap);
                assume _module.__default.length#canCall(_module.BreadthFirstSearch$Vertex, pathToV#0_0);
                assume _module.__default.length#canCall(_module.BreadthFirstSearch$Vertex, p#0_0_0)
                   && _module.__default.length#canCall(_module.BreadthFirstSearch$Vertex, pathToV#0_0);
                if (_module.__default.length(_module.BreadthFirstSearch$Vertex, $LS($LZ), p#0_0_0)
                   < _module.__default.length(_module.BreadthFirstSearch$Vertex, $LS($LZ), pathToV#0_0))
                {
                    // ----- call statement ----- BreadthFirstSearch.dfy(95,26)
                    // TrCallStmt: Before ProcessCallStmt
                    assume true;
                    // ProcessCallStmt: CheckSubrange
                    source##0_0_0_0 := source#0;
                    ##list#0_0_0_0 := p#0_0_0;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##list#0_0_0_0, Tclass._module.List(_module.BreadthFirstSearch$Vertex), $Heap);
                    assume _module.__default.length#canCall(_module.BreadthFirstSearch$Vertex, p#0_0_0);
                    assume _module.__default.length#canCall(_module.BreadthFirstSearch$Vertex, p#0_0_0);
                    // ProcessCallStmt: CheckSubrange
                    m##0_0_0_0 := _module.__default.length(_module.BreadthFirstSearch$Vertex, $LS($LZ), p#0_0_0);
                    assume true;
                    // ProcessCallStmt: CheckSubrange
                    assert $Is(d#0 - 1, Tclass._System.nat());
                    n##0_0_0_0 := d#0 - 1;
                    assume true;
                    // ProcessCallStmt: CheckSubrange
                    AllVertices##0_0_0_0 := AllVertices#0;
                    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                    // ProcessCallStmt: Make the call
                    call Call$$_module.BreadthFirstSearch.RMonotonicity(_module.BreadthFirstSearch$Vertex, this, source##0_0_0_0, m##0_0_0_0, n##0_0_0_0, AllVertices##0_0_0_0);
                    // TrCallStmt: After ProcessCallStmt
                    assume {:captureState "BreadthFirstSearch.dfy(95,62)"} true;
                }
                else
                {
                }

                assert _module.__default.length(_module.BreadthFirstSearch$Vertex, $LS($LS($LZ)), pathToV#0_0)
                   <= _module.__default.length(_module.BreadthFirstSearch$Vertex, $LS($LS($LZ)), p#0_0_0);
                assume false;
            }
            else
            {
                assume (forall p#0_0_1: DatatypeType ::
                  { _module.__default.length(_module.BreadthFirstSearch$Vertex, $LS($LZ), p#0_0_1) }
                    { _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex, $LS($LZ), this, source#0, dest#0, p#0_0_1) }
                  $Is(p#0_0_1, Tclass._module.List(_module.BreadthFirstSearch$Vertex))
                       && _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex, $LS($LZ), this, source#0, dest#0, p#0_0_1)
                     ==> _module.__default.length(_module.BreadthFirstSearch$Vertex, $LS($LZ), pathToV#0_0)
                       <= _module.__default.length(_module.BreadthFirstSearch$Vertex, $LS($LZ), p#0_0_1));
            }

            assume {:captureState "BreadthFirstSearch.dfy(97,8)"} true;
            // ----- return statement ----- BreadthFirstSearch.dfy(98,9)
            // ----- update statement ----- BreadthFirstSearch.dfy(98,9)
            assume true;
            assume true;
            assume true;
            $rhs#0_0_0 := d#0;
            assume true;
            $rhs#0_0_1 := pathToV#0_0;
            d#0 := $rhs#0_0_0;
            path#0 := $rhs#0_0_1;
            assume {:captureState "BreadthFirstSearch.dfy(98,25)"} true;
            return;
        }
        else
        {
        }

        // ----- assignment statement ----- BreadthFirstSearch.dfy(102,28)
        assume true;
        havoc w#0_0;
        assume $IsBox(w#0_0, _module.BreadthFirstSearch$Vertex);
        // Begin Comprehension WF check
        ##x#0_1 := v#0_0;
        // assume allocatedness for argument to function
        assume $IsAllocBox(##x#0_1, _module.BreadthFirstSearch$Vertex, $Heap);
        assume _module.BreadthFirstSearch.Succ#canCall(_module.BreadthFirstSearch$Vertex, this, v#0_0);
        if (_module.BreadthFirstSearch.Succ(_module.BreadthFirstSearch$Vertex, this, v#0_0)[w#0_0])
        {
        }

        if (_module.BreadthFirstSearch.Succ(_module.BreadthFirstSearch$Vertex, this, v#0_0)[w#0_0]
           && !V#0[w#0_0])
        {
        }

        // End Comprehension WF check
        assume (forall w#0_1: Box ::
          { V#0[w#0_1] }
            { _module.BreadthFirstSearch.Succ(_module.BreadthFirstSearch$Vertex, this, v#0_0)[w#0_1] }
          $IsBox(w#0_1, _module.BreadthFirstSearch$Vertex)
             ==> _module.BreadthFirstSearch.Succ#canCall(_module.BreadthFirstSearch$Vertex, this, v#0_0));
        newlyEncountered#0_0 := (lambda $y#0_0: Box ::
          $IsBox($y#0_0, _module.BreadthFirstSearch$Vertex)
             &&
            _module.BreadthFirstSearch.Succ(_module.BreadthFirstSearch$Vertex, this, v#0_0)[$y#0_0]
             && !V#0[$y#0_0]);
        assume {:captureState "BreadthFirstSearch.dfy(102,61)"} true;
        // ----- update statement ----- BreadthFirstSearch.dfy(103,12)
        assume true;
        assume true;
        assume true;
        $rhs#0_2 := Set#Union(V#0, newlyEncountered#0_0);
        assume true;
        $rhs#0_3 := Set#Union(N#0, newlyEncountered#0_0);
        V#0 := $rhs#0_2;
        N#0 := $rhs#0_3;
        assume {:captureState "BreadthFirstSearch.dfy(103,56)"} true;
        // ----- call statement ----- BreadthFirstSearch.dfy(104,27)
        assume true;
        // TrCallStmt: Adding lhs Microsoft.Dafny.IdentifierExpr with type map<Vertex, List<Vertex>>
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        vSuccs##0_0 := newlyEncountered#0_0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        source##0_0 := source#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        paths##0_0 := paths#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        v##0_0 := v#0_0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        pathToV##0_0 := pathToV#0_0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call $rhs##0_0 := Call$$_module.BreadthFirstSearch.UpdatePaths(_module.BreadthFirstSearch$Vertex, this, vSuccs##0_0, source##0_0, paths##0_0, v##0_0, pathToV##0_0);
        // TrCallStmt: After ProcessCallStmt
        paths#0 := $rhs##0_0;
        assume {:captureState "BreadthFirstSearch.dfy(104,71)"} true;
        // ----- if statement ----- BreadthFirstSearch.dfy(106,7)
        assume true;
        if (Set#Equal(C#0, Set#Empty(): Set Box))
        {
            // ----- update statement ----- BreadthFirstSearch.dfy(107,17)
            assume true;
            assume true;
            assume true;
            assume true;
            $rhs#0_1_0 := N#0;
            assume true;
            $rhs#0_1_1 := Lit(Set#Empty(): Set Box);
            assume true;
            $rhs#0_1_2 := d#0 + 1;
            C#0 := $rhs#0_1_0;
            N#0 := $rhs#0_1_1;
            d#0 := $rhs#0_1_2;
            assume {:captureState "BreadthFirstSearch.dfy(107,29)"} true;
        }
        else
        {
        }

        // ----- loop termination check ----- BreadthFirstSearch.dfy(56,5)
        assert Set#Subset(Set#Difference(AllVertices#0, Processed#0), $decr$loop#00)
           && !Set#Subset($decr$loop#00, Set#Difference(AllVertices#0, Processed#0));
        assume true;
        assume true;
        assume true;
        assume true;
        assume _module.BreadthFirstSearch.ValidMap#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, paths#0);
        assume _module.__default.domain#canCall(_module.BreadthFirstSearch$Vertex,
          Tclass._module.List(_module.BreadthFirstSearch$Vertex),
          paths#0);
        assume (forall x#1: Box ::
          { _module.BreadthFirstSearch.Find(_module.BreadthFirstSearch$Vertex, this, source#0, x#1, paths#0) }
            { C#0[x#1] }
          $IsBox(x#1, _module.BreadthFirstSearch$Vertex)
             ==>
            C#0[x#1]
             ==> _module.BreadthFirstSearch.Find#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, x#1, paths#0)
               && _module.__default.length#canCall(_module.BreadthFirstSearch$Vertex,
                _module.BreadthFirstSearch.Find(_module.BreadthFirstSearch$Vertex, this, source#0, x#1, paths#0)));
        assume (forall x#3: Box ::
          { _module.BreadthFirstSearch.Find(_module.BreadthFirstSearch$Vertex, this, source#0, x#3, paths#0) }
            { N#0[x#3] }
          $IsBox(x#3, _module.BreadthFirstSearch$Vertex)
             ==>
            N#0[x#3]
             ==> _module.BreadthFirstSearch.Find#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, x#3, paths#0)
               && _module.__default.length#canCall(_module.BreadthFirstSearch$Vertex,
                _module.BreadthFirstSearch.Find(_module.BreadthFirstSearch$Vertex, this, source#0, x#3, paths#0)));
        assume _module.BreadthFirstSearch.R#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, d#0, AllVertices#0);
        assume d#0 != 0
           ==> _module.BreadthFirstSearch.R#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, d#0 - 1, AllVertices#0);
        assume _module.BreadthFirstSearch.R#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, d#0, AllVertices#0);
        assume _module.BreadthFirstSearch.Successors#canCall(_module.BreadthFirstSearch$Vertex, this, Processed#0, AllVertices#0)
           && _module.BreadthFirstSearch.R#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, d#0, AllVertices#0);
        assume true;
    }

    // ----- forall statement (proof) ----- BreadthFirstSearch.dfy(113,5)
    if (*)
    {
        // Assume Fuel Constant
        havoc n#0;
        assume LitInt(0) <= n#0;
        assume true;
        assume true;
        // ----- if statement ----- BreadthFirstSearch.dfy(116,7)
        assume true;
        if (n#0 < d#0)
        {
            // ----- call statement ----- BreadthFirstSearch.dfy(117,22)
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            // ProcessCallStmt: CheckSubrange
            source##1_0 := source#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            assert $Is(n#0, Tclass._System.nat());
            m##1_0 := n#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            assert $Is(d#0, Tclass._System.nat());
            n##1_0 := d#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            AllVertices##1_0 := AllVertices#0;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call Call$$_module.BreadthFirstSearch.RMonotonicity(_module.BreadthFirstSearch$Vertex, this, source##1_0, m##1_0, n##1_0, AllVertices##1_0);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "BreadthFirstSearch.dfy(117,48)"} true;
        }
        else
        {
            // ----- call statement ----- BreadthFirstSearch.dfy(119,24)
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            // ProcessCallStmt: CheckSubrange
            source##0 := source#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            assert $Is(d#0, Tclass._System.nat());
            m##0 := d#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            assert $Is(n#0, Tclass._System.nat());
            n##0 := n#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            AllVertices##0 := AllVertices#0;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call Call$$_module.BreadthFirstSearch.IsReachFixpoint(_module.BreadthFirstSearch$Vertex, this, source##0, m##0, n##0, AllVertices##0);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "BreadthFirstSearch.dfy(119,50)"} true;
        }

        assert !_module.BreadthFirstSearch.R(_module.BreadthFirstSearch$Vertex,
          $LS($LS($LZ)),
          this,
          source#0,
          n#0,
          AllVertices#0)[dest#0];
        assume false;
    }
    else
    {
        assume (forall n#1: int ::
          { _module.BreadthFirstSearch.R(_module.BreadthFirstSearch$Vertex, $LS($LZ), this, source#0, n#1, AllVertices#0) }
          LitInt(0) <= n#1 && Lit(true)
             ==> !_module.BreadthFirstSearch.R(_module.BreadthFirstSearch$Vertex, $LS($LZ), this, source#0, n#1, AllVertices#0)[dest#0]);
    }

    assume {:captureState "BreadthFirstSearch.dfy(121,4)"} true;
    // ----- forall statement (proof) ----- BreadthFirstSearch.dfy(125,5)
    if (*)
    {
        // Assume Fuel Constant
        havoc p#4;
        assume $Is(p#4, Tclass._module.List(_module.BreadthFirstSearch$Vertex));
        ##source#10 := source#0;
        // assume allocatedness for argument to function
        assume $IsAllocBox(##source#10, _module.BreadthFirstSearch$Vertex, $Heap);
        ##dest#3 := dest#0;
        // assume allocatedness for argument to function
        assume $IsAllocBox(##dest#3, _module.BreadthFirstSearch$Vertex, $Heap);
        ##p#3 := p#4;
        // assume allocatedness for argument to function
        assume $IsAlloc(##p#3, Tclass._module.List(_module.BreadthFirstSearch$Vertex), $Heap);
        assume _module.BreadthFirstSearch.IsPath#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, dest#0, p#4);
        assume _module.BreadthFirstSearch.IsPath#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, dest#0, p#4);
        assume _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex, $LS($LZ), this, source#0, dest#0, p#4);
        // ----- call statement ----- BreadthFirstSearch.dfy(130,21)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        source##1 := source#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        x##0 := dest#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        p##0 := p#4;
        assume true;
        // ProcessCallStmt: CheckSubrange
        AllVertices##1 := AllVertices#0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$_module.BreadthFirstSearch.Lemma__IsPath__R(_module.BreadthFirstSearch$Vertex, this, source##1, x##0, p##0, AllVertices##1);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "BreadthFirstSearch.dfy(130,50)"} true;
        assert false;
        assume false;
    }
    else
    {
        assume (forall p#5: DatatypeType ::
          { _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex, $LS($LZ), this, source#0, dest#0, p#5) }
          $Is(p#5, Tclass._module.List(_module.BreadthFirstSearch$Vertex))
               && _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex, $LS($LZ), this, source#0, dest#0, p#5)
             ==> Lit(false));
    }

    assume {:captureState "BreadthFirstSearch.dfy(134,4)"} true;
    // ----- assignment statement ----- BreadthFirstSearch.dfy(136,7)
    assume true;
    assume true;
    d#0 := LitInt(0 - 1);
    assume {:captureState "BreadthFirstSearch.dfy(136,11)"} true;
}



procedure {:_induction p#0} CheckWellformed$$_module.BreadthFirstSearch.Lemma__IsPath__Closure(_module.BreadthFirstSearch$Vertex: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex))
         && $IsAlloc(this,
          Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex),
          $Heap),
    source#0: Box
       where $IsBox(source#0, _module.BreadthFirstSearch$Vertex)
         && $IsAllocBox(source#0, _module.BreadthFirstSearch$Vertex, $Heap),
    dest#0: Box
       where $IsBox(dest#0, _module.BreadthFirstSearch$Vertex)
         && $IsAllocBox(dest#0, _module.BreadthFirstSearch$Vertex, $Heap),
    p#0: DatatypeType
       where $Is(p#0, Tclass._module.List(_module.BreadthFirstSearch$Vertex))
         && $IsAlloc(p#0, Tclass._module.List(_module.BreadthFirstSearch$Vertex), $Heap)
         && $IsA#_module.List(p#0),
    AllVertices#0: Set Box
       where $Is(AllVertices#0, TSet(_module.BreadthFirstSearch$Vertex))
         && $IsAlloc(AllVertices#0, TSet(_module.BreadthFirstSearch$Vertex), $Heap));
  free requires 13 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:_induction p#0} Call$$_module.BreadthFirstSearch.Lemma__IsPath__Closure(_module.BreadthFirstSearch$Vertex: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex))
         && $IsAlloc(this,
          Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex),
          $Heap),
    source#0: Box
       where $IsBox(source#0, _module.BreadthFirstSearch$Vertex)
         && $IsAllocBox(source#0, _module.BreadthFirstSearch$Vertex, $Heap),
    dest#0: Box
       where $IsBox(dest#0, _module.BreadthFirstSearch$Vertex)
         && $IsAllocBox(dest#0, _module.BreadthFirstSearch$Vertex, $Heap),
    p#0: DatatypeType
       where $Is(p#0, Tclass._module.List(_module.BreadthFirstSearch$Vertex))
         && $IsAlloc(p#0, Tclass._module.List(_module.BreadthFirstSearch$Vertex), $Heap)
         && $IsA#_module.List(p#0),
    AllVertices#0: Set Box
       where $Is(AllVertices#0, TSet(_module.BreadthFirstSearch$Vertex))
         && $IsAlloc(AllVertices#0, TSet(_module.BreadthFirstSearch$Vertex), $Heap));
  // user-defined preconditions
  requires _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex, $LS($LS($LZ)), this, source#0, dest#0, p#0);
  requires AllVertices#0[source#0];
  requires _module.BreadthFirstSearch.IsClosed#canCall(_module.BreadthFirstSearch$Vertex, this, AllVertices#0)
     ==> _module.BreadthFirstSearch.IsClosed(_module.BreadthFirstSearch$Vertex, this, AllVertices#0)
       || (forall v#2: Box ::
        { _module.BreadthFirstSearch.Succ(_module.BreadthFirstSearch$Vertex, this, v#2) }
          { AllVertices#0[v#2] }
        $IsBox(v#2, _module.BreadthFirstSearch$Vertex)
           ==>
          AllVertices#0[v#2]
           ==> Set#Subset(_module.BreadthFirstSearch.Succ(_module.BreadthFirstSearch$Vertex, this, v#2),
            AllVertices#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures AllVertices#0[dest#0]
     ==> (forall v#1: Box ::
      { AllVertices#0[v#1] }
        { _module.__default.elements(_module.BreadthFirstSearch$Vertex, $LS($LZ), p#0)[v#1] }
      $IsBox(v#1, _module.BreadthFirstSearch$Vertex)
         ==> _module.__default.elements#canCall(_module.BreadthFirstSearch$Vertex, p#0));
  ensures AllVertices#0[dest#0];
  free ensures (forall v#1: Box ::
    { AllVertices#0[v#1] }
      { _module.__default.elements(_module.BreadthFirstSearch$Vertex, $LS($LZ), p#0)[v#1] }
    $IsBox(v#1, _module.BreadthFirstSearch$Vertex)
       ==>
      _module.__default.elements(_module.BreadthFirstSearch$Vertex, $LS($LZ), p#0)[v#1]
       ==> AllVertices#0[v#1]);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction p#0} Impl$$_module.BreadthFirstSearch.Lemma__IsPath__Closure(_module.BreadthFirstSearch$Vertex: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex))
         && $IsAlloc(this,
          Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex),
          $Heap),
    source#0: Box
       where $IsBox(source#0, _module.BreadthFirstSearch$Vertex)
         && $IsAllocBox(source#0, _module.BreadthFirstSearch$Vertex, $Heap),
    dest#0: Box
       where $IsBox(dest#0, _module.BreadthFirstSearch$Vertex)
         && $IsAllocBox(dest#0, _module.BreadthFirstSearch$Vertex, $Heap),
    p#0: DatatypeType
       where $Is(p#0, Tclass._module.List(_module.BreadthFirstSearch$Vertex))
         && $IsAlloc(p#0, Tclass._module.List(_module.BreadthFirstSearch$Vertex), $Heap)
         && $IsA#_module.List(p#0),
    AllVertices#0: Set Box
       where $Is(AllVertices#0, TSet(_module.BreadthFirstSearch$Vertex))
         && $IsAlloc(AllVertices#0, TSet(_module.BreadthFirstSearch$Vertex), $Heap))
   returns ($_reverifyPost: bool);
  free requires 13 == $FunctionContextHeight;
  // user-defined preconditions
  requires _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex, $LS($LS($LZ)), this, source#0, dest#0, p#0);
  requires AllVertices#0[source#0];
  free requires _module.BreadthFirstSearch.IsClosed#canCall(_module.BreadthFirstSearch$Vertex, this, AllVertices#0)
     &&
    _module.BreadthFirstSearch.IsClosed(_module.BreadthFirstSearch$Vertex, this, AllVertices#0)
     && (forall v#3: Box ::
      { _module.BreadthFirstSearch.Succ(_module.BreadthFirstSearch$Vertex, this, v#3) }
        { AllVertices#0[v#3] }
      $IsBox(v#3, _module.BreadthFirstSearch$Vertex)
         ==>
        AllVertices#0[v#3]
         ==> Set#Subset(_module.BreadthFirstSearch.Succ(_module.BreadthFirstSearch$Vertex, this, v#3),
          AllVertices#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures AllVertices#0[dest#0]
     ==> (forall v#1: Box ::
      { AllVertices#0[v#1] }
        { _module.__default.elements(_module.BreadthFirstSearch$Vertex, $LS($LZ), p#0)[v#1] }
      $IsBox(v#1, _module.BreadthFirstSearch$Vertex)
         ==> _module.__default.elements#canCall(_module.BreadthFirstSearch$Vertex, p#0));
  ensures AllVertices#0[dest#0];
  ensures (forall v#1: Box ::
    { AllVertices#0[v#1] }
      { _module.__default.elements(_module.BreadthFirstSearch$Vertex, $LS($LS($LZ)), p#0)[v#1] }
    $IsBox(v#1, _module.BreadthFirstSearch$Vertex)
       ==>
      _module.__default.elements(_module.BreadthFirstSearch$Vertex, $LS($LS($LZ)), p#0)[v#1]
       ==> AllVertices#0[v#1]);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction p#0} Impl$$_module.BreadthFirstSearch.Lemma__IsPath__Closure(_module.BreadthFirstSearch$Vertex: Ty,
    this: ref,
    source#0: Box,
    dest#0: Box,
    p#0: DatatypeType,
    AllVertices#0: Set Box)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var v#0_0: Box;
  var tail#0_0: DatatypeType;
  var source##0_0: Box;
  var dest##0_0: Box;
  var p##0_0: DatatypeType;
  var AllVertices##0_0: Set Box;

    // AddMethodImpl: Lemma_IsPath_Closure, Impl$$_module.BreadthFirstSearch.Lemma__IsPath__Closure
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "BreadthFirstSearch.dfy(145,2): initial state"} true;
    assume $IsA#_module.List(p#0);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#p0#0: DatatypeType ::
      $Is($ih#p0#0, Tclass._module.List(_module.BreadthFirstSearch$Vertex))
           &&
          _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex, $LS($LZ), this, source#0, dest#0, $ih#p0#0)
           && AllVertices#0[source#0]
           && _module.BreadthFirstSearch.IsClosed(_module.BreadthFirstSearch$Vertex, this, AllVertices#0)
           && (DtRank($ih#p0#0) < DtRank(p#0)
             || (DtRank($ih#p0#0) == DtRank(p#0)
               &&
              Set#Subset(AllVertices#0, AllVertices#0)
               && !Set#Subset(AllVertices#0, AllVertices#0)))
         ==> AllVertices#0[dest#0]
           && (forall v#4: Box ::
            { AllVertices#0[v#4] }
              { _module.__default.elements(_module.BreadthFirstSearch$Vertex, $LS($LZ), $ih#p0#0)[v#4] }
            $IsBox(v#4, _module.BreadthFirstSearch$Vertex)
               ==>
              _module.__default.elements(_module.BreadthFirstSearch$Vertex, $LS($LZ), $ih#p0#0)[v#4]
               ==> AllVertices#0[v#4]));
    $_reverifyPost := false;
    assume true;
    havoc v#0_0, tail#0_0;
    if (p#0 == #_module.List.Nil())
    {
    }
    else if (p#0 == #_module.List.Cons(v#0_0, tail#0_0))
    {
        assume $IsBox(v#0_0, _module.BreadthFirstSearch$Vertex);
        assume $Is(tail#0_0, Tclass._module.List(_module.BreadthFirstSearch$Vertex));
        // ----- call statement ----- BreadthFirstSearch.dfy(149,29)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        source##0_0 := source#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        dest##0_0 := v#0_0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        p##0_0 := tail#0_0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        AllVertices##0_0 := AllVertices#0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assert DtRank(p##0_0) < DtRank(p#0)
           || (DtRank(p##0_0) == DtRank(p#0)
             &&
            Set#Subset(AllVertices##0_0, AllVertices#0)
             && !Set#Subset(AllVertices#0, AllVertices##0_0));
        // ProcessCallStmt: Make the call
        call Call$$_module.BreadthFirstSearch.Lemma__IsPath__Closure(_module.BreadthFirstSearch$Vertex, this, source##0_0, dest##0_0, p##0_0, AllVertices##0_0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "BreadthFirstSearch.dfy(149,58)"} true;
    }
    else
    {
        assume false;
    }
}



// function declaration for _module.BreadthFirstSearch.R
function _module.BreadthFirstSearch.R(_module.BreadthFirstSearch$Vertex: Ty,
    $ly: LayerType,
    this: ref,
    source#0: Box,
    n#0: int,
    AllVertices#0: Set Box)
   : Set Box;

function _module.BreadthFirstSearch.R#canCall(_module.BreadthFirstSearch$Vertex: Ty,
    this: ref,
    source#0: Box,
    n#0: int,
    AllVertices#0: Set Box)
   : bool;

// layer synonym axiom
axiom (forall _module.BreadthFirstSearch$Vertex: Ty,
    $ly: LayerType,
    this: ref,
    source#0: Box,
    n#0: int,
    AllVertices#0: Set Box ::
  { _module.BreadthFirstSearch.R(_module.BreadthFirstSearch$Vertex, $LS($ly), this, source#0, n#0, AllVertices#0) }
  _module.BreadthFirstSearch.R(_module.BreadthFirstSearch$Vertex, $LS($ly), this, source#0, n#0, AllVertices#0)
     == _module.BreadthFirstSearch.R(_module.BreadthFirstSearch$Vertex, $ly, this, source#0, n#0, AllVertices#0));

// fuel synonym axiom
axiom (forall _module.BreadthFirstSearch$Vertex: Ty,
    $ly: LayerType,
    this: ref,
    source#0: Box,
    n#0: int,
    AllVertices#0: Set Box ::
  { _module.BreadthFirstSearch.R(_module.BreadthFirstSearch$Vertex,
      AsFuelBottom($ly),
      this,
      source#0,
      n#0,
      AllVertices#0) }
  _module.BreadthFirstSearch.R(_module.BreadthFirstSearch$Vertex, $ly, this, source#0, n#0, AllVertices#0)
     == _module.BreadthFirstSearch.R(_module.BreadthFirstSearch$Vertex, $LZ, this, source#0, n#0, AllVertices#0));

// consequence axiom for _module.BreadthFirstSearch.R
axiom 3 <= $FunctionContextHeight
   ==> (forall _module.BreadthFirstSearch$Vertex: Ty,
      $ly: LayerType,
      this: ref,
      source#0: Box,
      n#0: int,
      AllVertices#0: Set Box ::
    { _module.BreadthFirstSearch.R(_module.BreadthFirstSearch$Vertex, $ly, this, source#0, n#0, AllVertices#0) }
    _module.BreadthFirstSearch.R#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, n#0, AllVertices#0)
         || (3 != $FunctionContextHeight
           &&
          this != null
           && $Is(this, Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex))
           && $IsBox(source#0, _module.BreadthFirstSearch$Vertex)
           && LitInt(0) <= n#0
           && $Is(AllVertices#0, TSet(_module.BreadthFirstSearch$Vertex)))
       ==> $Is(_module.BreadthFirstSearch.R(_module.BreadthFirstSearch$Vertex, $ly, this, source#0, n#0, AllVertices#0),
        TSet(_module.BreadthFirstSearch$Vertex)));

function _module.BreadthFirstSearch.R#requires(Ty, LayerType, ref, Box, int, Set Box) : bool;

// #requires axiom for _module.BreadthFirstSearch.R
axiom (forall _module.BreadthFirstSearch$Vertex: Ty,
    $ly: LayerType,
    $Heap: Heap,
    this: ref,
    source#0: Box,
    n#0: int,
    AllVertices#0: Set Box ::
  { _module.BreadthFirstSearch.R#requires(_module.BreadthFirstSearch$Vertex, $ly, this, source#0, n#0, AllVertices#0), $IsGoodHeap($Heap) }
  $IsGoodHeap($Heap)
       &&
      this != null
       &&
      $Is(this, Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex))
       && $IsAlloc(this,
        Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex),
        $Heap)
       && $IsBox(source#0, _module.BreadthFirstSearch$Vertex)
       && LitInt(0) <= n#0
       && $Is(AllVertices#0, TSet(_module.BreadthFirstSearch$Vertex))
     ==> _module.BreadthFirstSearch.R#requires(_module.BreadthFirstSearch$Vertex, $ly, this, source#0, n#0, AllVertices#0)
       == true);

// definition axiom for _module.BreadthFirstSearch.R(revealed)
axiom 3 <= $FunctionContextHeight
   ==> (forall _module.BreadthFirstSearch$Vertex: Ty,
      $ly: LayerType,
      $Heap: Heap,
      this: ref,
      source#0: Box,
      n#0: int,
      AllVertices#0: Set Box ::
    { _module.BreadthFirstSearch.R(_module.BreadthFirstSearch$Vertex, $LS($ly), this, source#0, n#0, AllVertices#0), $IsGoodHeap($Heap) }
    _module.BreadthFirstSearch.R#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, n#0, AllVertices#0)
         || (3 != $FunctionContextHeight
           &&
          $IsGoodHeap($Heap)
           &&
          this != null
           &&
          $Is(this, Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex))
           && $IsAlloc(this,
            Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex),
            $Heap)
           && $IsBox(source#0, _module.BreadthFirstSearch$Vertex)
           && LitInt(0) <= n#0
           && $Is(AllVertices#0, TSet(_module.BreadthFirstSearch$Vertex)))
       ==> (n#0 != LitInt(0)
           ==> _module.BreadthFirstSearch.R#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, n#0 - 1, AllVertices#0)
             &&
            _module.BreadthFirstSearch.R#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, n#0 - 1, AllVertices#0)
             && _module.BreadthFirstSearch.Successors#canCall(_module.BreadthFirstSearch$Vertex,
              this,
              _module.BreadthFirstSearch.R(_module.BreadthFirstSearch$Vertex, $ly, this, source#0, n#0 - 1, AllVertices#0),
              AllVertices#0))
         && _module.BreadthFirstSearch.R(_module.BreadthFirstSearch$Vertex, $LS($ly), this, source#0, n#0, AllVertices#0)
           == (if n#0 == LitInt(0)
             then Set#UnionOne(Set#Empty(): Set Box, source#0)
             else Set#Union(_module.BreadthFirstSearch.R(_module.BreadthFirstSearch$Vertex, $ly, this, source#0, n#0 - 1, AllVertices#0),
              _module.BreadthFirstSearch.Successors(_module.BreadthFirstSearch$Vertex,
                this,
                _module.BreadthFirstSearch.R(_module.BreadthFirstSearch$Vertex, $ly, this, source#0, n#0 - 1, AllVertices#0),
                AllVertices#0))));

// definition axiom for _module.BreadthFirstSearch.R for decreasing-related literals(revealed)
axiom 3 <= $FunctionContextHeight
   ==> (forall _module.BreadthFirstSearch$Vertex: Ty,
      $ly: LayerType,
      $Heap: Heap,
      this: ref,
      source#0: Box,
      n#0: int,
      AllVertices#0: Set Box ::
    {:weight 3} { _module.BreadthFirstSearch.R(_module.BreadthFirstSearch$Vertex,
        $LS($ly),
        this,
        source#0,
        LitInt(n#0),
        Lit(AllVertices#0)), $IsGoodHeap($Heap) }
    _module.BreadthFirstSearch.R#canCall(_module.BreadthFirstSearch$Vertex,
          this,
          source#0,
          LitInt(n#0),
          Lit(AllVertices#0))
         || (3 != $FunctionContextHeight
           &&
          $IsGoodHeap($Heap)
           &&
          this != null
           &&
          $Is(this, Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex))
           && $IsAlloc(this,
            Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex),
            $Heap)
           && $IsBox(source#0, _module.BreadthFirstSearch$Vertex)
           && LitInt(0) <= n#0
           && $Is(AllVertices#0, TSet(_module.BreadthFirstSearch$Vertex)))
       ==> (LitInt(n#0) != LitInt(0)
           ==> _module.BreadthFirstSearch.R#canCall(_module.BreadthFirstSearch$Vertex,
              this,
              source#0,
              LitInt(n#0 - 1),
              Lit(AllVertices#0))
             &&
            _module.BreadthFirstSearch.R#canCall(_module.BreadthFirstSearch$Vertex,
              this,
              source#0,
              LitInt(n#0 - 1),
              Lit(AllVertices#0))
             && _module.BreadthFirstSearch.Successors#canCall(_module.BreadthFirstSearch$Vertex,
              this,
              _module.BreadthFirstSearch.R(_module.BreadthFirstSearch$Vertex,
                $LS($ly),
                this,
                source#0,
                LitInt(n#0 - 1),
                Lit(AllVertices#0)),
              Lit(AllVertices#0)))
         && _module.BreadthFirstSearch.R(_module.BreadthFirstSearch$Vertex,
            $LS($ly),
            this,
            source#0,
            LitInt(n#0),
            Lit(AllVertices#0))
           == (if LitInt(n#0) == LitInt(0)
             then Set#UnionOne(Set#Empty(): Set Box, source#0)
             else Set#Union(_module.BreadthFirstSearch.R(_module.BreadthFirstSearch$Vertex,
                $LS($ly),
                this,
                source#0,
                LitInt(n#0 - 1),
                Lit(AllVertices#0)),
              _module.BreadthFirstSearch.Successors(_module.BreadthFirstSearch$Vertex,
                this,
                _module.BreadthFirstSearch.R(_module.BreadthFirstSearch$Vertex,
                  $LS($ly),
                  this,
                  source#0,
                  LitInt(n#0 - 1),
                  Lit(AllVertices#0)),
                Lit(AllVertices#0)))));

// definition axiom for _module.BreadthFirstSearch.R for all literals(revealed)
axiom 3 <= $FunctionContextHeight
   ==> (forall _module.BreadthFirstSearch$Vertex: Ty,
      $ly: LayerType,
      $Heap: Heap,
      this: ref,
      source#0: Box,
      n#0: int,
      AllVertices#0: Set Box ::
    {:weight 3} { _module.BreadthFirstSearch.R(_module.BreadthFirstSearch$Vertex,
        $LS($ly),
        this,
        Lit(source#0),
        LitInt(n#0),
        Lit(AllVertices#0)), $IsGoodHeap($Heap) }
    _module.BreadthFirstSearch.R#canCall(_module.BreadthFirstSearch$Vertex,
          this,
          Lit(source#0),
          LitInt(n#0),
          Lit(AllVertices#0))
         || (3 != $FunctionContextHeight
           &&
          $IsGoodHeap($Heap)
           &&
          this != null
           &&
          $Is(this, Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex))
           && $IsAlloc(this,
            Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex),
            $Heap)
           && $IsBox(source#0, _module.BreadthFirstSearch$Vertex)
           && LitInt(0) <= n#0
           && $Is(AllVertices#0, TSet(_module.BreadthFirstSearch$Vertex)))
       ==> (LitInt(n#0) != LitInt(0)
           ==> _module.BreadthFirstSearch.R#canCall(_module.BreadthFirstSearch$Vertex,
              this,
              Lit(source#0),
              LitInt(n#0 - 1),
              Lit(AllVertices#0))
             &&
            _module.BreadthFirstSearch.R#canCall(_module.BreadthFirstSearch$Vertex,
              this,
              Lit(source#0),
              LitInt(n#0 - 1),
              Lit(AllVertices#0))
             && _module.BreadthFirstSearch.Successors#canCall(_module.BreadthFirstSearch$Vertex,
              this,
              Lit(_module.BreadthFirstSearch.R(_module.BreadthFirstSearch$Vertex,
                  $LS($ly),
                  this,
                  Lit(source#0),
                  LitInt(n#0 - 1),
                  Lit(AllVertices#0))),
              Lit(AllVertices#0)))
         && _module.BreadthFirstSearch.R(_module.BreadthFirstSearch$Vertex,
            $LS($ly),
            this,
            Lit(source#0),
            LitInt(n#0),
            Lit(AllVertices#0))
           == (if LitInt(n#0) == LitInt(0)
             then Set#UnionOne(Set#Empty(): Set Box, Lit(source#0))
             else Set#Union(_module.BreadthFirstSearch.R(_module.BreadthFirstSearch$Vertex,
                $LS($ly),
                this,
                Lit(source#0),
                LitInt(n#0 - 1),
                Lit(AllVertices#0)),
              _module.BreadthFirstSearch.Successors(_module.BreadthFirstSearch$Vertex,
                this,
                Lit(_module.BreadthFirstSearch.R(_module.BreadthFirstSearch$Vertex,
                    $LS($ly),
                    this,
                    Lit(source#0),
                    LitInt(n#0 - 1),
                    Lit(AllVertices#0))),
                Lit(AllVertices#0)))));

procedure CheckWellformed$$_module.BreadthFirstSearch.R(_module.BreadthFirstSearch$Vertex: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex))
         && $IsAlloc(this,
          Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex),
          $Heap),
    source#0: Box where $IsBox(source#0, _module.BreadthFirstSearch$Vertex),
    n#0: int where LitInt(0) <= n#0,
    AllVertices#0: Set Box
       where $Is(AllVertices#0, TSet(_module.BreadthFirstSearch$Vertex)));
  free requires 3 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.BreadthFirstSearch.R(_module.BreadthFirstSearch$Vertex: Ty,
    this: ref,
    source#0: Box,
    n#0: int,
    AllVertices#0: Set Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##source#0: Box;
  var ##n#0: int;
  var ##AllVertices#0: Set Box;
  var ##source#1: Box;
  var ##n#1: int;
  var ##AllVertices#1: Set Box;
  var ##S#0: Set Box;
  var ##AllVertices#2: Set Box;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;
  var b$reqreads#2: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;
    b$reqreads#2 := true;

    // AddWellformednessCheck for function R
    assume {:captureState "BreadthFirstSearch.dfy(155,11): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.BreadthFirstSearch.R(_module.BreadthFirstSearch$Vertex, $LS($LZ), this, source#0, n#0, AllVertices#0),
          TSet(_module.BreadthFirstSearch$Vertex));
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
          $o != null && read($Heap, $o, alloc) ==> false);
        if (n#0 == LitInt(0))
        {
            assume _module.BreadthFirstSearch.R(_module.BreadthFirstSearch$Vertex, $LS($LZ), this, source#0, n#0, AllVertices#0)
               == Set#UnionOne(Set#Empty(): Set Box, source#0);
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.BreadthFirstSearch.R(_module.BreadthFirstSearch$Vertex, $LS($LZ), this, source#0, n#0, AllVertices#0),
              TSet(_module.BreadthFirstSearch$Vertex));
        }
        else
        {
            ##source#0 := source#0;
            // assume allocatedness for argument to function
            assume $IsAllocBox(##source#0, _module.BreadthFirstSearch$Vertex, $Heap);
            assert $Is(n#0 - 1, Tclass._System.nat());
            ##n#0 := n#0 - 1;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#0, Tclass._System.nat(), $Heap);
            ##AllVertices#0 := AllVertices#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##AllVertices#0, TSet(_module.BreadthFirstSearch$Vertex), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert 0 <= n#0 || ##n#0 == n#0;
            assert ##n#0 < n#0
               || (##n#0 == n#0
                 &&
                Set#Subset(##AllVertices#0, AllVertices#0)
                 && !Set#Subset(AllVertices#0, ##AllVertices#0));
            assume _module.BreadthFirstSearch.R#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, n#0 - 1, AllVertices#0);
            ##source#1 := source#0;
            // assume allocatedness for argument to function
            assume $IsAllocBox(##source#1, _module.BreadthFirstSearch$Vertex, $Heap);
            assert $Is(n#0 - 1, Tclass._System.nat());
            ##n#1 := n#0 - 1;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#1, Tclass._System.nat(), $Heap);
            ##AllVertices#1 := AllVertices#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##AllVertices#1, TSet(_module.BreadthFirstSearch$Vertex), $Heap);
            b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert 0 <= n#0 || ##n#1 == n#0;
            assert ##n#1 < n#0
               || (##n#1 == n#0
                 &&
                Set#Subset(##AllVertices#1, AllVertices#0)
                 && !Set#Subset(AllVertices#0, ##AllVertices#1));
            assume _module.BreadthFirstSearch.R#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, n#0 - 1, AllVertices#0);
            ##S#0 := _module.BreadthFirstSearch.R(_module.BreadthFirstSearch$Vertex,
              $LS($LZ),
              this,
              source#0,
              n#0 - 1,
              AllVertices#0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##S#0, TSet(_module.BreadthFirstSearch$Vertex), $Heap);
            ##AllVertices#2 := AllVertices#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##AllVertices#2, TSet(_module.BreadthFirstSearch$Vertex), $Heap);
            b$reqreads#2 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume _module.BreadthFirstSearch.Successors#canCall(_module.BreadthFirstSearch$Vertex,
              this,
              _module.BreadthFirstSearch.R(_module.BreadthFirstSearch$Vertex,
                $LS($LZ),
                this,
                source#0,
                n#0 - 1,
                AllVertices#0),
              AllVertices#0);
            assume _module.BreadthFirstSearch.R(_module.BreadthFirstSearch$Vertex, $LS($LZ), this, source#0, n#0, AllVertices#0)
               == Set#Union(_module.BreadthFirstSearch.R(_module.BreadthFirstSearch$Vertex,
                  $LS($LZ),
                  this,
                  source#0,
                  n#0 - 1,
                  AllVertices#0),
                _module.BreadthFirstSearch.Successors(_module.BreadthFirstSearch$Vertex,
                  this,
                  _module.BreadthFirstSearch.R(_module.BreadthFirstSearch$Vertex,
                    $LS($LZ),
                    this,
                    source#0,
                    n#0 - 1,
                    AllVertices#0),
                  AllVertices#0));
            assume _module.BreadthFirstSearch.R#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, n#0 - 1, AllVertices#0)
               &&
              _module.BreadthFirstSearch.R#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, n#0 - 1, AllVertices#0)
               && _module.BreadthFirstSearch.Successors#canCall(_module.BreadthFirstSearch$Vertex,
                this,
                _module.BreadthFirstSearch.R(_module.BreadthFirstSearch$Vertex,
                  $LS($LZ),
                  this,
                  source#0,
                  n#0 - 1,
                  AllVertices#0),
                AllVertices#0);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.BreadthFirstSearch.R(_module.BreadthFirstSearch$Vertex, $LS($LZ), this, source#0, n#0, AllVertices#0),
              TSet(_module.BreadthFirstSearch$Vertex));
        }

        assert b$reqreads#0;
        assert b$reqreads#1;
        assert b$reqreads#2;
    }
}



// function declaration for _module.BreadthFirstSearch.Successors
function _module.BreadthFirstSearch.Successors(_module.BreadthFirstSearch$Vertex: Ty,
    this: ref,
    S#0: Set Box,
    AllVertices#0: Set Box)
   : Set Box;

function _module.BreadthFirstSearch.Successors#canCall(_module.BreadthFirstSearch$Vertex: Ty,
    this: ref,
    S#0: Set Box,
    AllVertices#0: Set Box)
   : bool;

// consequence axiom for _module.BreadthFirstSearch.Successors
axiom 2 <= $FunctionContextHeight
   ==> (forall _module.BreadthFirstSearch$Vertex: Ty,
      this: ref,
      S#0: Set Box,
      AllVertices#0: Set Box ::
    { _module.BreadthFirstSearch.Successors(_module.BreadthFirstSearch$Vertex, this, S#0, AllVertices#0) }
    _module.BreadthFirstSearch.Successors#canCall(_module.BreadthFirstSearch$Vertex, this, S#0, AllVertices#0)
         || (2 != $FunctionContextHeight
           &&
          this != null
           && $Is(this, Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex))
           && $Is(S#0, TSet(_module.BreadthFirstSearch$Vertex))
           && $Is(AllVertices#0, TSet(_module.BreadthFirstSearch$Vertex)))
       ==> $Is(_module.BreadthFirstSearch.Successors(_module.BreadthFirstSearch$Vertex, this, S#0, AllVertices#0),
        TSet(_module.BreadthFirstSearch$Vertex)));

function _module.BreadthFirstSearch.Successors#requires(Ty, ref, Set Box, Set Box) : bool;

// #requires axiom for _module.BreadthFirstSearch.Successors
axiom (forall _module.BreadthFirstSearch$Vertex: Ty,
    $Heap: Heap,
    this: ref,
    S#0: Set Box,
    AllVertices#0: Set Box ::
  { _module.BreadthFirstSearch.Successors#requires(_module.BreadthFirstSearch$Vertex, this, S#0, AllVertices#0), $IsGoodHeap($Heap) }
  $IsGoodHeap($Heap)
       &&
      this != null
       &&
      $Is(this, Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex))
       && $IsAlloc(this,
        Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex),
        $Heap)
       && $Is(S#0, TSet(_module.BreadthFirstSearch$Vertex))
       && $Is(AllVertices#0, TSet(_module.BreadthFirstSearch$Vertex))
     ==> _module.BreadthFirstSearch.Successors#requires(_module.BreadthFirstSearch$Vertex, this, S#0, AllVertices#0)
       == true);

// definition axiom for _module.BreadthFirstSearch.Successors(revealed)
axiom 2 <= $FunctionContextHeight
   ==> (forall _module.BreadthFirstSearch$Vertex: Ty,
      $Heap: Heap,
      this: ref,
      S#0: Set Box,
      AllVertices#0: Set Box ::
    { _module.BreadthFirstSearch.Successors(_module.BreadthFirstSearch$Vertex, this, S#0, AllVertices#0), $IsGoodHeap($Heap) }
    _module.BreadthFirstSearch.Successors#canCall(_module.BreadthFirstSearch$Vertex, this, S#0, AllVertices#0)
         || (2 != $FunctionContextHeight
           &&
          $IsGoodHeap($Heap)
           &&
          this != null
           &&
          $Is(this, Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex))
           && $IsAlloc(this,
            Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex),
            $Heap)
           && $Is(S#0, TSet(_module.BreadthFirstSearch$Vertex))
           && $Is(AllVertices#0, TSet(_module.BreadthFirstSearch$Vertex)))
       ==> (forall w#0: Box ::
          { AllVertices#0[w#0] }
          $IsBox(w#0, _module.BreadthFirstSearch$Vertex)
             ==>
            AllVertices#0[w#0]
             ==> (forall x#0: Box ::
              { _module.BreadthFirstSearch.Succ(_module.BreadthFirstSearch$Vertex, this, x#0) }
                { S#0[x#0] }
              $IsBox(x#0, _module.BreadthFirstSearch$Vertex)
                 ==>
                S#0[x#0]
                 ==> _module.BreadthFirstSearch.Succ#canCall(_module.BreadthFirstSearch$Vertex, this, x#0)))
         && _module.BreadthFirstSearch.Successors(_module.BreadthFirstSearch$Vertex, this, S#0, AllVertices#0)
           == (lambda $y#0: Box ::
            $IsBox($y#0, _module.BreadthFirstSearch$Vertex)
               &&
              AllVertices#0[$y#0]
               && (exists x#1: Box ::
                { _module.BreadthFirstSearch.Succ(_module.BreadthFirstSearch$Vertex, this, x#1) }
                  { S#0[x#1] }
                $IsBox(x#1, _module.BreadthFirstSearch$Vertex)
                   &&
                  S#0[x#1]
                   && _module.BreadthFirstSearch.Succ(_module.BreadthFirstSearch$Vertex, this, x#1)[$y#0])));

// definition axiom for _module.BreadthFirstSearch.Successors for all literals(revealed)
axiom 2 <= $FunctionContextHeight
   ==> (forall _module.BreadthFirstSearch$Vertex: Ty,
      $Heap: Heap,
      this: ref,
      S#0: Set Box,
      AllVertices#0: Set Box ::
    {:weight 3} { _module.BreadthFirstSearch.Successors(_module.BreadthFirstSearch$Vertex, this, Lit(S#0), Lit(AllVertices#0)), $IsGoodHeap($Heap) }
    _module.BreadthFirstSearch.Successors#canCall(_module.BreadthFirstSearch$Vertex, this, Lit(S#0), Lit(AllVertices#0))
         || (2 != $FunctionContextHeight
           &&
          $IsGoodHeap($Heap)
           &&
          this != null
           &&
          $Is(this, Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex))
           && $IsAlloc(this,
            Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex),
            $Heap)
           && $Is(S#0, TSet(_module.BreadthFirstSearch$Vertex))
           && $Is(AllVertices#0, TSet(_module.BreadthFirstSearch$Vertex)))
       ==> (forall w#1: Box ::
          { AllVertices#0[w#1] }
          $IsBox(w#1, _module.BreadthFirstSearch$Vertex)
             ==>
            Lit(AllVertices#0)[w#1]
             ==> (forall x#2: Box ::
              { _module.BreadthFirstSearch.Succ(_module.BreadthFirstSearch$Vertex, this, x#2) }
                { S#0[x#2] }
              $IsBox(x#2, _module.BreadthFirstSearch$Vertex)
                 ==>
                Lit(S#0)[x#2]
                 ==> _module.BreadthFirstSearch.Succ#canCall(_module.BreadthFirstSearch$Vertex, this, x#2)))
         && _module.BreadthFirstSearch.Successors(_module.BreadthFirstSearch$Vertex, this, Lit(S#0), Lit(AllVertices#0))
           == (lambda $y#1: Box ::
            $IsBox($y#1, _module.BreadthFirstSearch$Vertex)
               &&
              Lit(AllVertices#0)[$y#1]
               && (exists x#3: Box ::
                { _module.BreadthFirstSearch.Succ(_module.BreadthFirstSearch$Vertex, this, x#3) }
                  { S#0[x#3] }
                $IsBox(x#3, _module.BreadthFirstSearch$Vertex)
                   &&
                  Lit(S#0)[x#3]
                   && _module.BreadthFirstSearch.Succ(_module.BreadthFirstSearch$Vertex, this, x#3)[$y#1])));

procedure CheckWellformed$$_module.BreadthFirstSearch.Successors(_module.BreadthFirstSearch$Vertex: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex))
         && $IsAlloc(this,
          Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex),
          $Heap),
    S#0: Set Box where $Is(S#0, TSet(_module.BreadthFirstSearch$Vertex)),
    AllVertices#0: Set Box
       where $Is(AllVertices#0, TSet(_module.BreadthFirstSearch$Vertex)));
  free requires 2 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.BreadthFirstSearch.Successors(_module.BreadthFirstSearch$Vertex: Ty,
    this: ref,
    S#0: Set Box,
    AllVertices#0: Set Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var w#2: Box;
  var x#4: Box;
  var ##x#0: Box;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function Successors
    assume {:captureState "BreadthFirstSearch.dfy(161,11): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.BreadthFirstSearch.Successors(_module.BreadthFirstSearch$Vertex, this, S#0, AllVertices#0),
          TSet(_module.BreadthFirstSearch$Vertex));
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
          $o != null && read($Heap, $o, alloc) ==> false);
        havoc w#2;
        assume $IsBox(w#2, _module.BreadthFirstSearch$Vertex);
        // Begin Comprehension WF check
        if (AllVertices#0[w#2])
        {
            havoc x#4;
            assume $IsBox(x#4, _module.BreadthFirstSearch$Vertex);
            // Begin Comprehension WF check
            if (S#0[x#4])
            {
                ##x#0 := x#4;
                // assume allocatedness for argument to function
                assume $IsAllocBox(##x#0, _module.BreadthFirstSearch$Vertex, $Heap);
                b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                assume _module.BreadthFirstSearch.Succ#canCall(_module.BreadthFirstSearch$Vertex, this, x#4);
            }

            // End Comprehension WF check
        }

        if (AllVertices#0[w#2]
           && (exists x#5: Box ::
            { _module.BreadthFirstSearch.Succ(_module.BreadthFirstSearch$Vertex, this, x#5) }
              { S#0[x#5] }
            $IsBox(x#5, _module.BreadthFirstSearch$Vertex)
               &&
              S#0[x#5]
               && _module.BreadthFirstSearch.Succ(_module.BreadthFirstSearch$Vertex, this, x#5)[w#2]))
        {
        }

        // End Comprehension WF check
        assume _module.BreadthFirstSearch.Successors(_module.BreadthFirstSearch$Vertex, this, S#0, AllVertices#0)
           == (lambda $y#2: Box ::
            $IsBox($y#2, _module.BreadthFirstSearch$Vertex)
               &&
              AllVertices#0[$y#2]
               && (exists x#6: Box ::
                { _module.BreadthFirstSearch.Succ(_module.BreadthFirstSearch$Vertex, this, x#6) }
                  { S#0[x#6] }
                $IsBox(x#6, _module.BreadthFirstSearch$Vertex)
                   &&
                  S#0[x#6]
                   && _module.BreadthFirstSearch.Succ(_module.BreadthFirstSearch$Vertex, this, x#6)[$y#2]));
        assume (forall w#3: Box ::
          { AllVertices#0[w#3] }
          $IsBox(w#3, _module.BreadthFirstSearch$Vertex)
             ==>
            AllVertices#0[w#3]
             ==> (forall x#7: Box ::
              { _module.BreadthFirstSearch.Succ(_module.BreadthFirstSearch$Vertex, this, x#7) }
                { S#0[x#7] }
              $IsBox(x#7, _module.BreadthFirstSearch$Vertex)
                 ==>
                S#0[x#7]
                 ==> _module.BreadthFirstSearch.Succ#canCall(_module.BreadthFirstSearch$Vertex, this, x#7)));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.BreadthFirstSearch.Successors(_module.BreadthFirstSearch$Vertex, this, S#0, AllVertices#0),
          TSet(_module.BreadthFirstSearch$Vertex));
        assert b$reqreads#0;
    }
}



procedure {:_induction m#0, n#0, AllVertices#0} CheckWellformed$$_module.BreadthFirstSearch.RMonotonicity(_module.BreadthFirstSearch$Vertex: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex))
         && $IsAlloc(this,
          Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex),
          $Heap),
    source#0: Box
       where $IsBox(source#0, _module.BreadthFirstSearch$Vertex)
         && $IsAllocBox(source#0, _module.BreadthFirstSearch$Vertex, $Heap),
    m#0: int where LitInt(0) <= m#0,
    n#0: int where LitInt(0) <= n#0,
    AllVertices#0: Set Box
       where $Is(AllVertices#0, TSet(_module.BreadthFirstSearch$Vertex))
         && $IsAlloc(AllVertices#0, TSet(_module.BreadthFirstSearch$Vertex), $Heap));
  free requires 4 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:_induction m#0, n#0, AllVertices#0} CheckWellformed$$_module.BreadthFirstSearch.RMonotonicity(_module.BreadthFirstSearch$Vertex: Ty,
    this: ref,
    source#0: Box,
    m#0: int,
    n#0: int,
    AllVertices#0: Set Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##source#0: Box;
  var ##n#0: int;
  var ##AllVertices#0: Set Box;
  var ##source#1: Box;
  var ##n#1: int;
  var ##AllVertices#1: Set Box;

    // AddMethodImpl: RMonotonicity, CheckWellformed$$_module.BreadthFirstSearch.RMonotonicity
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "BreadthFirstSearch.dfy(166,8): initial state"} true;
    assume m#0 <= n#0;
    havoc $Heap;
    assume old($Heap) == $Heap;
    assume {:captureState "BreadthFirstSearch.dfy(168,38): post-state"} true;
    ##source#0 := source#0;
    // assume allocatedness for argument to function
    assume $IsAllocBox(##source#0, _module.BreadthFirstSearch$Vertex, $Heap);
    assert $Is(m#0, Tclass._System.nat());
    ##n#0 := m#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#0, Tclass._System.nat(), $Heap);
    ##AllVertices#0 := AllVertices#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##AllVertices#0, TSet(_module.BreadthFirstSearch$Vertex), $Heap);
    assume _module.BreadthFirstSearch.R#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, m#0, AllVertices#0);
    ##source#1 := source#0;
    // assume allocatedness for argument to function
    assume $IsAllocBox(##source#1, _module.BreadthFirstSearch$Vertex, $Heap);
    assert $Is(n#0, Tclass._System.nat());
    ##n#1 := n#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#1, Tclass._System.nat(), $Heap);
    ##AllVertices#1 := AllVertices#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##AllVertices#1, TSet(_module.BreadthFirstSearch$Vertex), $Heap);
    assume _module.BreadthFirstSearch.R#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, n#0, AllVertices#0);
    assume Set#Subset(_module.BreadthFirstSearch.R(_module.BreadthFirstSearch$Vertex, $LS($LZ), this, source#0, m#0, AllVertices#0),
      _module.BreadthFirstSearch.R(_module.BreadthFirstSearch$Vertex, $LS($LZ), this, source#0, n#0, AllVertices#0));
}



procedure {:_induction m#0, n#0, AllVertices#0} Call$$_module.BreadthFirstSearch.RMonotonicity(_module.BreadthFirstSearch$Vertex: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex))
         && $IsAlloc(this,
          Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex),
          $Heap),
    source#0: Box
       where $IsBox(source#0, _module.BreadthFirstSearch$Vertex)
         && $IsAllocBox(source#0, _module.BreadthFirstSearch$Vertex, $Heap),
    m#0: int where LitInt(0) <= m#0,
    n#0: int where LitInt(0) <= n#0,
    AllVertices#0: Set Box
       where $Is(AllVertices#0, TSet(_module.BreadthFirstSearch$Vertex))
         && $IsAlloc(AllVertices#0, TSet(_module.BreadthFirstSearch$Vertex), $Heap));
  // user-defined preconditions
  requires m#0 <= n#0;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.BreadthFirstSearch.R#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, m#0, AllVertices#0)
     && _module.BreadthFirstSearch.R#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, n#0, AllVertices#0);
  ensures Set#Subset(_module.BreadthFirstSearch.R(_module.BreadthFirstSearch$Vertex,
      $LS($LS($LZ)),
      this,
      source#0,
      m#0,
      AllVertices#0),
    _module.BreadthFirstSearch.R(_module.BreadthFirstSearch$Vertex,
      $LS($LS($LZ)),
      this,
      source#0,
      n#0,
      AllVertices#0));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction m#0, n#0, AllVertices#0} Impl$$_module.BreadthFirstSearch.RMonotonicity(_module.BreadthFirstSearch$Vertex: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex))
         && $IsAlloc(this,
          Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex),
          $Heap),
    source#0: Box
       where $IsBox(source#0, _module.BreadthFirstSearch$Vertex)
         && $IsAllocBox(source#0, _module.BreadthFirstSearch$Vertex, $Heap),
    m#0: int where LitInt(0) <= m#0,
    n#0: int where LitInt(0) <= n#0,
    AllVertices#0: Set Box
       where $Is(AllVertices#0, TSet(_module.BreadthFirstSearch$Vertex))
         && $IsAlloc(AllVertices#0, TSet(_module.BreadthFirstSearch$Vertex), $Heap))
   returns ($_reverifyPost: bool);
  free requires 4 == $FunctionContextHeight;
  // user-defined preconditions
  requires m#0 <= n#0;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.BreadthFirstSearch.R#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, m#0, AllVertices#0)
     && _module.BreadthFirstSearch.R#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, n#0, AllVertices#0);
  ensures Set#Subset(_module.BreadthFirstSearch.R(_module.BreadthFirstSearch$Vertex,
      $LS($LS($LZ)),
      this,
      source#0,
      m#0,
      AllVertices#0),
    _module.BreadthFirstSearch.R(_module.BreadthFirstSearch$Vertex,
      $LS($LS($LZ)),
      this,
      source#0,
      n#0,
      AllVertices#0));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction m#0, n#0, AllVertices#0} Impl$$_module.BreadthFirstSearch.RMonotonicity(_module.BreadthFirstSearch$Vertex: Ty,
    this: ref,
    source#0: Box,
    m#0: int,
    n#0: int,
    AllVertices#0: Set Box)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var source##0_0: Box;
  var m##0_0: int;
  var n##0_0: int;
  var AllVertices##0_0: Set Box;

    // AddMethodImpl: RMonotonicity, Impl$$_module.BreadthFirstSearch.RMonotonicity
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "BreadthFirstSearch.dfy(170,2): initial state"} true;
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#m0#0: int, $ih#n0#0: int, $ih#AllVertices0#0: Set Box ::
      LitInt(0) <= $ih#m0#0
           && LitInt(0) <= $ih#n0#0
           && $Is($ih#AllVertices0#0, TSet(_module.BreadthFirstSearch$Vertex))
           && $ih#m0#0 <= $ih#n0#0
           &&
          0 <= $ih#n0#0 - $ih#m0#0
           && $ih#n0#0 - $ih#m0#0 < n#0 - m#0
         ==> Set#Subset(_module.BreadthFirstSearch.R(_module.BreadthFirstSearch$Vertex,
            $LS($LZ),
            this,
            source#0,
            $ih#m0#0,
            $ih#AllVertices0#0),
          _module.BreadthFirstSearch.R(_module.BreadthFirstSearch$Vertex,
            $LS($LZ),
            this,
            source#0,
            $ih#n0#0,
            $ih#AllVertices0#0)));
    $_reverifyPost := false;
    // ----- if statement ----- BreadthFirstSearch.dfy(171,5)
    assume true;
    if (m#0 < n#0)
    {
        // ----- call statement ----- BreadthFirstSearch.dfy(172,20)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        source##0_0 := source#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        assert $Is(m#0 + 1, Tclass._System.nat());
        m##0_0 := m#0 + 1;
        assume true;
        // ProcessCallStmt: CheckSubrange
        assert $Is(n#0, Tclass._System.nat());
        n##0_0 := n#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        AllVertices##0_0 := AllVertices#0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assert 0 <= n#0 - m#0 || n##0_0 - m##0_0 == n#0 - m#0;
        assert n##0_0 - m##0_0 < n#0 - m#0;
        // ProcessCallStmt: Make the call
        call Call$$_module.BreadthFirstSearch.RMonotonicity(_module.BreadthFirstSearch$Vertex, this, source##0_0, m##0_0, n##0_0, AllVertices##0_0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "BreadthFirstSearch.dfy(172,50)"} true;
    }
    else
    {
    }
}



procedure {:_induction m#0, n#0, AllVertices#0} CheckWellformed$$_module.BreadthFirstSearch.IsReachFixpoint(_module.BreadthFirstSearch$Vertex: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex))
         && $IsAlloc(this,
          Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex),
          $Heap),
    source#0: Box
       where $IsBox(source#0, _module.BreadthFirstSearch$Vertex)
         && $IsAllocBox(source#0, _module.BreadthFirstSearch$Vertex, $Heap),
    m#0: int where LitInt(0) <= m#0,
    n#0: int where LitInt(0) <= n#0,
    AllVertices#0: Set Box
       where $Is(AllVertices#0, TSet(_module.BreadthFirstSearch$Vertex))
         && $IsAlloc(AllVertices#0, TSet(_module.BreadthFirstSearch$Vertex), $Heap));
  free requires 5 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:_induction m#0, n#0, AllVertices#0} CheckWellformed$$_module.BreadthFirstSearch.IsReachFixpoint(_module.BreadthFirstSearch$Vertex: Ty,
    this: ref,
    source#0: Box,
    m#0: int,
    n#0: int,
    AllVertices#0: Set Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##source#0: Box;
  var ##n#0: int;
  var ##AllVertices#0: Set Box;
  var ##source#1: Box;
  var ##n#1: int;
  var ##AllVertices#1: Set Box;
  var ##source#2: Box;
  var ##n#2: int;
  var ##AllVertices#2: Set Box;
  var ##source#3: Box;
  var ##n#3: int;
  var ##AllVertices#3: Set Box;

    // AddMethodImpl: IsReachFixpoint, CheckWellformed$$_module.BreadthFirstSearch.IsReachFixpoint
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "BreadthFirstSearch.dfy(176,8): initial state"} true;
    ##source#0 := source#0;
    // assume allocatedness for argument to function
    assume $IsAllocBox(##source#0, _module.BreadthFirstSearch$Vertex, $Heap);
    assert $Is(m#0, Tclass._System.nat());
    ##n#0 := m#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#0, Tclass._System.nat(), $Heap);
    ##AllVertices#0 := AllVertices#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##AllVertices#0, TSet(_module.BreadthFirstSearch$Vertex), $Heap);
    assume _module.BreadthFirstSearch.R#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, m#0, AllVertices#0);
    ##source#1 := source#0;
    // assume allocatedness for argument to function
    assume $IsAllocBox(##source#1, _module.BreadthFirstSearch$Vertex, $Heap);
    assert $Is(m#0 + 1, Tclass._System.nat());
    ##n#1 := m#0 + 1;
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#1, Tclass._System.nat(), $Heap);
    ##AllVertices#1 := AllVertices#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##AllVertices#1, TSet(_module.BreadthFirstSearch$Vertex), $Heap);
    assume _module.BreadthFirstSearch.R#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, m#0 + 1, AllVertices#0);
    assume Set#Equal(_module.BreadthFirstSearch.R(_module.BreadthFirstSearch$Vertex, $LS($LZ), this, source#0, m#0, AllVertices#0),
      _module.BreadthFirstSearch.R(_module.BreadthFirstSearch$Vertex,
        $LS($LZ),
        this,
        source#0,
        m#0 + 1,
        AllVertices#0));
    assume m#0 <= n#0;
    havoc $Heap;
    assume old($Heap) == $Heap;
    assume {:captureState "BreadthFirstSearch.dfy(179,38): post-state"} true;
    ##source#2 := source#0;
    // assume allocatedness for argument to function
    assume $IsAllocBox(##source#2, _module.BreadthFirstSearch$Vertex, $Heap);
    assert $Is(m#0, Tclass._System.nat());
    ##n#2 := m#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#2, Tclass._System.nat(), $Heap);
    ##AllVertices#2 := AllVertices#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##AllVertices#2, TSet(_module.BreadthFirstSearch$Vertex), $Heap);
    assume _module.BreadthFirstSearch.R#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, m#0, AllVertices#0);
    ##source#3 := source#0;
    // assume allocatedness for argument to function
    assume $IsAllocBox(##source#3, _module.BreadthFirstSearch$Vertex, $Heap);
    assert $Is(n#0, Tclass._System.nat());
    ##n#3 := n#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#3, Tclass._System.nat(), $Heap);
    ##AllVertices#3 := AllVertices#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##AllVertices#3, TSet(_module.BreadthFirstSearch$Vertex), $Heap);
    assume _module.BreadthFirstSearch.R#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, n#0, AllVertices#0);
    assume Set#Equal(_module.BreadthFirstSearch.R(_module.BreadthFirstSearch$Vertex, $LS($LZ), this, source#0, m#0, AllVertices#0),
      _module.BreadthFirstSearch.R(_module.BreadthFirstSearch$Vertex, $LS($LZ), this, source#0, n#0, AllVertices#0));
}



procedure {:_induction m#0, n#0, AllVertices#0} Call$$_module.BreadthFirstSearch.IsReachFixpoint(_module.BreadthFirstSearch$Vertex: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex))
         && $IsAlloc(this,
          Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex),
          $Heap),
    source#0: Box
       where $IsBox(source#0, _module.BreadthFirstSearch$Vertex)
         && $IsAllocBox(source#0, _module.BreadthFirstSearch$Vertex, $Heap),
    m#0: int where LitInt(0) <= m#0,
    n#0: int where LitInt(0) <= n#0,
    AllVertices#0: Set Box
       where $Is(AllVertices#0, TSet(_module.BreadthFirstSearch$Vertex))
         && $IsAlloc(AllVertices#0, TSet(_module.BreadthFirstSearch$Vertex), $Heap));
  // user-defined preconditions
  requires Set#Equal(_module.BreadthFirstSearch.R(_module.BreadthFirstSearch$Vertex,
      $LS($LS($LZ)),
      this,
      source#0,
      m#0,
      AllVertices#0),
    _module.BreadthFirstSearch.R(_module.BreadthFirstSearch$Vertex,
      $LS($LS($LZ)),
      this,
      source#0,
      m#0 + 1,
      AllVertices#0));
  requires m#0 <= n#0;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.BreadthFirstSearch.R#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, m#0, AllVertices#0)
     && _module.BreadthFirstSearch.R#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, n#0, AllVertices#0);
  ensures Set#Equal(_module.BreadthFirstSearch.R(_module.BreadthFirstSearch$Vertex,
      $LS($LS($LZ)),
      this,
      source#0,
      m#0,
      AllVertices#0),
    _module.BreadthFirstSearch.R(_module.BreadthFirstSearch$Vertex,
      $LS($LS($LZ)),
      this,
      source#0,
      n#0,
      AllVertices#0));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction m#0, n#0, AllVertices#0} Impl$$_module.BreadthFirstSearch.IsReachFixpoint(_module.BreadthFirstSearch$Vertex: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex))
         && $IsAlloc(this,
          Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex),
          $Heap),
    source#0: Box
       where $IsBox(source#0, _module.BreadthFirstSearch$Vertex)
         && $IsAllocBox(source#0, _module.BreadthFirstSearch$Vertex, $Heap),
    m#0: int where LitInt(0) <= m#0,
    n#0: int where LitInt(0) <= n#0,
    AllVertices#0: Set Box
       where $Is(AllVertices#0, TSet(_module.BreadthFirstSearch$Vertex))
         && $IsAlloc(AllVertices#0, TSet(_module.BreadthFirstSearch$Vertex), $Heap))
   returns ($_reverifyPost: bool);
  free requires 5 == $FunctionContextHeight;
  // user-defined preconditions
  requires Set#Equal(_module.BreadthFirstSearch.R(_module.BreadthFirstSearch$Vertex,
      $LS($LS($LZ)),
      this,
      source#0,
      m#0,
      AllVertices#0),
    _module.BreadthFirstSearch.R(_module.BreadthFirstSearch$Vertex,
      $LS($LS($LZ)),
      this,
      source#0,
      m#0 + 1,
      AllVertices#0));
  requires m#0 <= n#0;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.BreadthFirstSearch.R#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, m#0, AllVertices#0)
     && _module.BreadthFirstSearch.R#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, n#0, AllVertices#0);
  ensures Set#Equal(_module.BreadthFirstSearch.R(_module.BreadthFirstSearch$Vertex,
      $LS($LS($LZ)),
      this,
      source#0,
      m#0,
      AllVertices#0),
    _module.BreadthFirstSearch.R(_module.BreadthFirstSearch$Vertex,
      $LS($LS($LZ)),
      this,
      source#0,
      n#0,
      AllVertices#0));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction m#0, n#0, AllVertices#0} Impl$$_module.BreadthFirstSearch.IsReachFixpoint(_module.BreadthFirstSearch$Vertex: Ty,
    this: ref,
    source#0: Box,
    m#0: int,
    n#0: int,
    AllVertices#0: Set Box)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var source##0_0: Box;
  var m##0_0: int;
  var n##0_0: int;
  var AllVertices##0_0: Set Box;

    // AddMethodImpl: IsReachFixpoint, Impl$$_module.BreadthFirstSearch.IsReachFixpoint
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "BreadthFirstSearch.dfy(181,2): initial state"} true;
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#m0#0: int, $ih#n0#0: int, $ih#AllVertices0#0: Set Box ::
      LitInt(0) <= $ih#m0#0
           && LitInt(0) <= $ih#n0#0
           && $Is($ih#AllVertices0#0, TSet(_module.BreadthFirstSearch$Vertex))
           &&
          Set#Equal(_module.BreadthFirstSearch.R(_module.BreadthFirstSearch$Vertex,
              $LS($LZ),
              this,
              source#0,
              $ih#m0#0,
              $ih#AllVertices0#0),
            _module.BreadthFirstSearch.R(_module.BreadthFirstSearch$Vertex,
              $LS($LZ),
              this,
              source#0,
              $ih#m0#0 + 1,
              $ih#AllVertices0#0))
           && $ih#m0#0 <= $ih#n0#0
           &&
          0 <= $ih#n0#0 - $ih#m0#0
           && $ih#n0#0 - $ih#m0#0 < n#0 - m#0
         ==> Set#Equal(_module.BreadthFirstSearch.R(_module.BreadthFirstSearch$Vertex,
            $LS($LZ),
            this,
            source#0,
            $ih#m0#0,
            $ih#AllVertices0#0),
          _module.BreadthFirstSearch.R(_module.BreadthFirstSearch$Vertex,
            $LS($LZ),
            this,
            source#0,
            $ih#n0#0,
            $ih#AllVertices0#0)));
    $_reverifyPost := false;
    // ----- if statement ----- BreadthFirstSearch.dfy(182,5)
    assume true;
    if (m#0 < n#0)
    {
        // ----- call statement ----- BreadthFirstSearch.dfy(183,22)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        source##0_0 := source#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        assert $Is(m#0 + 1, Tclass._System.nat());
        m##0_0 := m#0 + 1;
        assume true;
        // ProcessCallStmt: CheckSubrange
        assert $Is(n#0, Tclass._System.nat());
        n##0_0 := n#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        AllVertices##0_0 := AllVertices#0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assert 0 <= n#0 - m#0 || n##0_0 - m##0_0 == n#0 - m#0;
        assert n##0_0 - m##0_0 < n#0 - m#0;
        // ProcessCallStmt: Make the call
        call Call$$_module.BreadthFirstSearch.IsReachFixpoint(_module.BreadthFirstSearch$Vertex, this, source##0_0, m##0_0, n##0_0, AllVertices##0_0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "BreadthFirstSearch.dfy(183,52)"} true;
    }
    else
    {
    }
}



procedure {:_induction p#0, AllVertices#0} CheckWellformed$$_module.BreadthFirstSearch.Lemma__IsPath__R(_module.BreadthFirstSearch$Vertex: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex))
         && $IsAlloc(this,
          Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex),
          $Heap),
    source#0: Box
       where $IsBox(source#0, _module.BreadthFirstSearch$Vertex)
         && $IsAllocBox(source#0, _module.BreadthFirstSearch$Vertex, $Heap),
    x#0: Box
       where $IsBox(x#0, _module.BreadthFirstSearch$Vertex)
         && $IsAllocBox(x#0, _module.BreadthFirstSearch$Vertex, $Heap),
    p#0: DatatypeType
       where $Is(p#0, Tclass._module.List(_module.BreadthFirstSearch$Vertex))
         && $IsAlloc(p#0, Tclass._module.List(_module.BreadthFirstSearch$Vertex), $Heap)
         && $IsA#_module.List(p#0),
    AllVertices#0: Set Box
       where $Is(AllVertices#0, TSet(_module.BreadthFirstSearch$Vertex))
         && $IsAlloc(AllVertices#0, TSet(_module.BreadthFirstSearch$Vertex), $Heap));
  free requires 14 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:_induction p#0, AllVertices#0} Call$$_module.BreadthFirstSearch.Lemma__IsPath__R(_module.BreadthFirstSearch$Vertex: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex))
         && $IsAlloc(this,
          Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex),
          $Heap),
    source#0: Box
       where $IsBox(source#0, _module.BreadthFirstSearch$Vertex)
         && $IsAllocBox(source#0, _module.BreadthFirstSearch$Vertex, $Heap),
    x#0: Box
       where $IsBox(x#0, _module.BreadthFirstSearch$Vertex)
         && $IsAllocBox(x#0, _module.BreadthFirstSearch$Vertex, $Heap),
    p#0: DatatypeType
       where $Is(p#0, Tclass._module.List(_module.BreadthFirstSearch$Vertex))
         && $IsAlloc(p#0, Tclass._module.List(_module.BreadthFirstSearch$Vertex), $Heap)
         && $IsA#_module.List(p#0),
    AllVertices#0: Set Box
       where $Is(AllVertices#0, TSet(_module.BreadthFirstSearch$Vertex))
         && $IsAlloc(AllVertices#0, TSet(_module.BreadthFirstSearch$Vertex), $Heap));
  // user-defined preconditions
  requires _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex, $LS($LS($LZ)), this, source#0, x#0, p#0);
  requires AllVertices#0[source#0];
  requires _module.BreadthFirstSearch.IsClosed#canCall(_module.BreadthFirstSearch$Vertex, this, AllVertices#0)
     ==> _module.BreadthFirstSearch.IsClosed(_module.BreadthFirstSearch$Vertex, this, AllVertices#0)
       || (forall v#0: Box ::
        { _module.BreadthFirstSearch.Succ(_module.BreadthFirstSearch$Vertex, this, v#0) }
          { AllVertices#0[v#0] }
        $IsBox(v#0, _module.BreadthFirstSearch$Vertex)
           ==>
          AllVertices#0[v#0]
           ==> Set#Subset(_module.BreadthFirstSearch.Succ(_module.BreadthFirstSearch$Vertex, this, v#0),
            AllVertices#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.length#canCall(_module.BreadthFirstSearch$Vertex, p#0)
     && _module.BreadthFirstSearch.R#canCall(_module.BreadthFirstSearch$Vertex,
      this,
      source#0,
      _module.__default.length(_module.BreadthFirstSearch$Vertex, $LS($LZ), p#0),
      AllVertices#0);
  ensures _module.BreadthFirstSearch.R(_module.BreadthFirstSearch$Vertex,
    $LS($LS($LZ)),
    this,
    source#0,
    _module.__default.length(_module.BreadthFirstSearch$Vertex, $LS($LS($LZ)), p#0),
    AllVertices#0)[x#0];
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction p#0, AllVertices#0} Impl$$_module.BreadthFirstSearch.Lemma__IsPath__R(_module.BreadthFirstSearch$Vertex: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex))
         && $IsAlloc(this,
          Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex),
          $Heap),
    source#0: Box
       where $IsBox(source#0, _module.BreadthFirstSearch$Vertex)
         && $IsAllocBox(source#0, _module.BreadthFirstSearch$Vertex, $Heap),
    x#0: Box
       where $IsBox(x#0, _module.BreadthFirstSearch$Vertex)
         && $IsAllocBox(x#0, _module.BreadthFirstSearch$Vertex, $Heap),
    p#0: DatatypeType
       where $Is(p#0, Tclass._module.List(_module.BreadthFirstSearch$Vertex))
         && $IsAlloc(p#0, Tclass._module.List(_module.BreadthFirstSearch$Vertex), $Heap)
         && $IsA#_module.List(p#0),
    AllVertices#0: Set Box
       where $Is(AllVertices#0, TSet(_module.BreadthFirstSearch$Vertex))
         && $IsAlloc(AllVertices#0, TSet(_module.BreadthFirstSearch$Vertex), $Heap))
   returns ($_reverifyPost: bool);
  free requires 14 == $FunctionContextHeight;
  // user-defined preconditions
  requires _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex, $LS($LS($LZ)), this, source#0, x#0, p#0);
  requires AllVertices#0[source#0];
  free requires _module.BreadthFirstSearch.IsClosed#canCall(_module.BreadthFirstSearch$Vertex, this, AllVertices#0)
     &&
    _module.BreadthFirstSearch.IsClosed(_module.BreadthFirstSearch$Vertex, this, AllVertices#0)
     && (forall v#1: Box ::
      { _module.BreadthFirstSearch.Succ(_module.BreadthFirstSearch$Vertex, this, v#1) }
        { AllVertices#0[v#1] }
      $IsBox(v#1, _module.BreadthFirstSearch$Vertex)
         ==>
        AllVertices#0[v#1]
         ==> Set#Subset(_module.BreadthFirstSearch.Succ(_module.BreadthFirstSearch$Vertex, this, v#1),
          AllVertices#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.length#canCall(_module.BreadthFirstSearch$Vertex, p#0)
     && _module.BreadthFirstSearch.R#canCall(_module.BreadthFirstSearch$Vertex,
      this,
      source#0,
      _module.__default.length(_module.BreadthFirstSearch$Vertex, $LS($LZ), p#0),
      AllVertices#0);
  ensures _module.BreadthFirstSearch.R(_module.BreadthFirstSearch$Vertex,
    $LS($LS($LZ)),
    this,
    source#0,
    _module.__default.length(_module.BreadthFirstSearch$Vertex, $LS($LS($LZ)), p#0),
    AllVertices#0)[x#0];
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction p#0, AllVertices#0} Impl$$_module.BreadthFirstSearch.Lemma__IsPath__R(_module.BreadthFirstSearch$Vertex: Ty,
    this: ref,
    source#0: Box,
    x#0: Box,
    p#0: DatatypeType,
    AllVertices#0: Set Box)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var v#0_0: Box;
  var tail#0_0: DatatypeType;
  var source##0_0: Box;
  var dest##0_0: Box;
  var p##0_0: DatatypeType;
  var AllVertices##0_0: Set Box;
  var source##0_1: Box;
  var x##0_0: Box;
  var p##0_1: DatatypeType;
  var AllVertices##0_1: Set Box;

    // AddMethodImpl: Lemma_IsPath_R, Impl$$_module.BreadthFirstSearch.Lemma__IsPath__R
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "BreadthFirstSearch.dfy(190,2): initial state"} true;
    assume $IsA#_module.List(p#0);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#p0#0: DatatypeType, $ih#AllVertices0#0: Set Box ::
      $Is($ih#p0#0, Tclass._module.List(_module.BreadthFirstSearch$Vertex))
           && $Is($ih#AllVertices0#0, TSet(_module.BreadthFirstSearch$Vertex))
           &&
          _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex, $LS($LZ), this, source#0, x#0, $ih#p0#0)
           && $ih#AllVertices0#0[source#0]
           && _module.BreadthFirstSearch.IsClosed(_module.BreadthFirstSearch$Vertex, this, $ih#AllVertices0#0)
           && (DtRank($ih#p0#0) < DtRank(p#0)
             || (DtRank($ih#p0#0) == DtRank(p#0)
               &&
              Set#Subset($ih#AllVertices0#0, AllVertices#0)
               && !Set#Subset(AllVertices#0, $ih#AllVertices0#0)))
         ==> _module.BreadthFirstSearch.R(_module.BreadthFirstSearch$Vertex,
          $LS($LZ),
          this,
          source#0,
          _module.__default.length(_module.BreadthFirstSearch$Vertex, $LS($LZ), $ih#p0#0),
          $ih#AllVertices0#0)[x#0]);
    $_reverifyPost := false;
    assume true;
    havoc v#0_0, tail#0_0;
    if (p#0 == #_module.List.Nil())
    {
    }
    else if (p#0 == #_module.List.Cons(v#0_0, tail#0_0))
    {
        assume $IsBox(v#0_0, _module.BreadthFirstSearch$Vertex);
        assume $Is(tail#0_0, Tclass._module.List(_module.BreadthFirstSearch$Vertex));
        // ----- call statement ----- BreadthFirstSearch.dfy(194,29)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        source##0_0 := source#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        dest##0_0 := x#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        p##0_0 := p#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        AllVertices##0_0 := AllVertices#0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$_module.BreadthFirstSearch.Lemma__IsPath__Closure(_module.BreadthFirstSearch$Vertex, this, source##0_0, dest##0_0, p##0_0, AllVertices##0_0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "BreadthFirstSearch.dfy(194,55)"} true;
        // ----- call statement ----- BreadthFirstSearch.dfy(195,23)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        source##0_1 := source#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        x##0_0 := v#0_0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        p##0_1 := tail#0_0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        AllVertices##0_1 := AllVertices#0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assert DtRank(p##0_1) < DtRank(p#0)
           || (DtRank(p##0_1) == DtRank(p#0)
             &&
            Set#Subset(AllVertices##0_1, AllVertices#0)
             && !Set#Subset(AllVertices#0, AllVertices##0_1));
        // ProcessCallStmt: Make the call
        call Call$$_module.BreadthFirstSearch.Lemma__IsPath__R(_module.BreadthFirstSearch$Vertex, this, source##0_1, x##0_0, p##0_1, AllVertices##0_1);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "BreadthFirstSearch.dfy(195,52)"} true;
    }
    else
    {
        assume false;
    }
}



// function declaration for _module.BreadthFirstSearch.ValidMap
function _module.BreadthFirstSearch.ValidMap(_module.BreadthFirstSearch$Vertex: Ty,
    this: ref,
    source#0: Box,
    m#0: Map Box Box)
   : bool;

function _module.BreadthFirstSearch.ValidMap#canCall(_module.BreadthFirstSearch$Vertex: Ty,
    this: ref,
    source#0: Box,
    m#0: Map Box Box)
   : bool;

// consequence axiom for _module.BreadthFirstSearch.ValidMap
axiom 10 <= $FunctionContextHeight
   ==> (forall _module.BreadthFirstSearch$Vertex: Ty,
      this: ref,
      source#0: Box,
      m#0: Map Box Box ::
    { _module.BreadthFirstSearch.ValidMap(_module.BreadthFirstSearch$Vertex, this, source#0, m#0) }
    _module.BreadthFirstSearch.ValidMap#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, m#0)
         || (10 != $FunctionContextHeight
           &&
          this != null
           && $Is(this, Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex))
           && $IsBox(source#0, _module.BreadthFirstSearch$Vertex)
           && $Is(m#0,
            TMap(_module.BreadthFirstSearch$Vertex,
              Tclass._module.List(_module.BreadthFirstSearch$Vertex))))
       ==> true);

function _module.BreadthFirstSearch.ValidMap#requires(Ty, ref, Box, Map Box Box) : bool;

// #requires axiom for _module.BreadthFirstSearch.ValidMap
axiom (forall _module.BreadthFirstSearch$Vertex: Ty,
    $Heap: Heap,
    this: ref,
    source#0: Box,
    m#0: Map Box Box ::
  { _module.BreadthFirstSearch.ValidMap#requires(_module.BreadthFirstSearch$Vertex, this, source#0, m#0), $IsGoodHeap($Heap) }
  $IsGoodHeap($Heap)
       &&
      this != null
       &&
      $Is(this, Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex))
       && $IsAlloc(this,
        Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex),
        $Heap)
       && $IsBox(source#0, _module.BreadthFirstSearch$Vertex)
       && $Is(m#0,
        TMap(_module.BreadthFirstSearch$Vertex,
          Tclass._module.List(_module.BreadthFirstSearch$Vertex)))
     ==> _module.BreadthFirstSearch.ValidMap#requires(_module.BreadthFirstSearch$Vertex, this, source#0, m#0)
       == true);

// definition axiom for _module.BreadthFirstSearch.ValidMap(revealed)
axiom 10 <= $FunctionContextHeight
   ==> (forall _module.BreadthFirstSearch$Vertex: Ty,
      $Heap: Heap,
      this: ref,
      source#0: Box,
      m#0: Map Box Box ::
    { _module.BreadthFirstSearch.ValidMap(_module.BreadthFirstSearch$Vertex, this, source#0, m#0), $IsGoodHeap($Heap) }
    _module.BreadthFirstSearch.ValidMap#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, m#0)
         || (10 != $FunctionContextHeight
           &&
          $IsGoodHeap($Heap)
           &&
          this != null
           &&
          $Is(this, Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex))
           && $IsAlloc(this,
            Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex),
            $Heap)
           && $IsBox(source#0, _module.BreadthFirstSearch$Vertex)
           && $Is(m#0,
            TMap(_module.BreadthFirstSearch$Vertex,
              Tclass._module.List(_module.BreadthFirstSearch$Vertex))))
       ==> (forall v#0: Box ::
          { $Unbox(Map#Elements(m#0)[v#0]): DatatypeType } { Map#Domain(m#0)[v#0] }
          $IsBox(v#0, _module.BreadthFirstSearch$Vertex)
             ==>
            Map#Domain(m#0)[v#0]
             ==> _module.BreadthFirstSearch.IsPath#canCall(_module.BreadthFirstSearch$Vertex,
              this,
              source#0,
              v#0,
              $Unbox(Map#Elements(m#0)[v#0]): DatatypeType))
         && _module.BreadthFirstSearch.ValidMap(_module.BreadthFirstSearch$Vertex, this, source#0, m#0)
           == (forall v#0: Box ::
            { $Unbox(Map#Elements(m#0)[v#0]): DatatypeType } { Map#Domain(m#0)[v#0] }
            $IsBox(v#0, _module.BreadthFirstSearch$Vertex)
               ==>
              Map#Domain(m#0)[v#0]
               ==> _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex,
                $LS($LZ),
                this,
                source#0,
                v#0,
                $Unbox(Map#Elements(m#0)[v#0]): DatatypeType)));

// definition axiom for _module.BreadthFirstSearch.ValidMap for decreasing-related literals(revealed)
axiom 10 <= $FunctionContextHeight
   ==> (forall _module.BreadthFirstSearch$Vertex: Ty,
      $Heap: Heap,
      this: ref,
      source#0: Box,
      m#0: Map Box Box ::
    {:weight 3} { _module.BreadthFirstSearch.ValidMap(_module.BreadthFirstSearch$Vertex, this, source#0, Lit(m#0)), $IsGoodHeap($Heap) }
    _module.BreadthFirstSearch.ValidMap#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, Lit(m#0))
         || (10 != $FunctionContextHeight
           &&
          $IsGoodHeap($Heap)
           &&
          this != null
           &&
          $Is(this, Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex))
           && $IsAlloc(this,
            Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex),
            $Heap)
           && $IsBox(source#0, _module.BreadthFirstSearch$Vertex)
           && $Is(m#0,
            TMap(_module.BreadthFirstSearch$Vertex,
              Tclass._module.List(_module.BreadthFirstSearch$Vertex))))
       ==> (forall v#1: Box ::
          { $Unbox(Map#Elements(m#0)[v#1]): DatatypeType } { Map#Domain(m#0)[v#1] }
          $IsBox(v#1, _module.BreadthFirstSearch$Vertex)
             ==>
            Map#Domain(m#0)[v#1]
             ==> _module.BreadthFirstSearch.IsPath#canCall(_module.BreadthFirstSearch$Vertex,
              this,
              source#0,
              v#1,
              $Unbox(Map#Elements(Lit(m#0))[v#1]): DatatypeType))
         && _module.BreadthFirstSearch.ValidMap(_module.BreadthFirstSearch$Vertex, this, source#0, Lit(m#0))
           == (forall v#1: Box ::
            { $Unbox(Map#Elements(m#0)[v#1]): DatatypeType } { Map#Domain(m#0)[v#1] }
            $IsBox(v#1, _module.BreadthFirstSearch$Vertex)
               ==>
              Map#Domain(m#0)[v#1]
               ==> _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex,
                $LS($LZ),
                this,
                source#0,
                v#1,
                $Unbox(Map#Elements(Lit(m#0))[v#1]): DatatypeType)));

// definition axiom for _module.BreadthFirstSearch.ValidMap for all literals(revealed)
axiom 10 <= $FunctionContextHeight
   ==> (forall _module.BreadthFirstSearch$Vertex: Ty,
      $Heap: Heap,
      this: ref,
      source#0: Box,
      m#0: Map Box Box ::
    {:weight 3} { _module.BreadthFirstSearch.ValidMap(_module.BreadthFirstSearch$Vertex, this, Lit(source#0), Lit(m#0)), $IsGoodHeap($Heap) }
    _module.BreadthFirstSearch.ValidMap#canCall(_module.BreadthFirstSearch$Vertex, this, Lit(source#0), Lit(m#0))
         || (10 != $FunctionContextHeight
           &&
          $IsGoodHeap($Heap)
           &&
          this != null
           &&
          $Is(this, Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex))
           && $IsAlloc(this,
            Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex),
            $Heap)
           && $IsBox(source#0, _module.BreadthFirstSearch$Vertex)
           && $Is(m#0,
            TMap(_module.BreadthFirstSearch$Vertex,
              Tclass._module.List(_module.BreadthFirstSearch$Vertex))))
       ==> (forall v#2: Box ::
          { $Unbox(Map#Elements(m#0)[v#2]): DatatypeType } { Map#Domain(m#0)[v#2] }
          $IsBox(v#2, _module.BreadthFirstSearch$Vertex)
             ==>
            Map#Domain(m#0)[v#2]
             ==> _module.BreadthFirstSearch.IsPath#canCall(_module.BreadthFirstSearch$Vertex,
              this,
              Lit(source#0),
              v#2,
              $Unbox(Map#Elements(Lit(m#0))[v#2]): DatatypeType))
         && _module.BreadthFirstSearch.ValidMap(_module.BreadthFirstSearch$Vertex, this, Lit(source#0), Lit(m#0))
           == (forall v#2: Box ::
            { $Unbox(Map#Elements(m#0)[v#2]): DatatypeType } { Map#Domain(m#0)[v#2] }
            $IsBox(v#2, _module.BreadthFirstSearch$Vertex)
               ==>
              Map#Domain(m#0)[v#2]
               ==> _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex,
                $LS($LZ),
                this,
                Lit(source#0),
                v#2,
                $Unbox(Map#Elements(Lit(m#0))[v#2]): DatatypeType)));

procedure CheckWellformed$$_module.BreadthFirstSearch.ValidMap(_module.BreadthFirstSearch$Vertex: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex))
         && $IsAlloc(this,
          Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex),
          $Heap),
    source#0: Box where $IsBox(source#0, _module.BreadthFirstSearch$Vertex),
    m#0: Map Box Box
       where $Is(m#0,
        TMap(_module.BreadthFirstSearch$Vertex,
          Tclass._module.List(_module.BreadthFirstSearch$Vertex))));
  free requires 10 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.BreadthFirstSearch.ValidMap(_module.BreadthFirstSearch$Vertex: Ty,
    this: ref,
    source#0: Box,
    m#0: Map Box Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var v#3: Box;
  var ##source#0: Box;
  var ##dest#0: Box;
  var ##p#0: DatatypeType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function ValidMap
    assume {:captureState "BreadthFirstSearch.dfy(201,12): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
          $o != null && read($Heap, $o, alloc) ==> false);
        havoc v#3;
        assume $IsBox(v#3, _module.BreadthFirstSearch$Vertex);
        // Begin Comprehension WF check
        if (Map#Domain(m#0)[v#3])
        {
            assert Map#Domain(m#0)[v#3];
            ##source#0 := source#0;
            // assume allocatedness for argument to function
            assume $IsAllocBox(##source#0, _module.BreadthFirstSearch$Vertex, $Heap);
            ##dest#0 := v#3;
            // assume allocatedness for argument to function
            assume $IsAllocBox(##dest#0, _module.BreadthFirstSearch$Vertex, $Heap);
            ##p#0 := $Unbox(Map#Elements(m#0)[v#3]): DatatypeType;
            // assume allocatedness for argument to function
            assume $IsAlloc(##p#0, Tclass._module.List(_module.BreadthFirstSearch$Vertex), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume _module.BreadthFirstSearch.IsPath#canCall(_module.BreadthFirstSearch$Vertex,
              this,
              source#0,
              v#3,
              $Unbox(Map#Elements(m#0)[v#3]): DatatypeType);
        }

        // End Comprehension WF check
        assume _module.BreadthFirstSearch.ValidMap(_module.BreadthFirstSearch$Vertex, this, source#0, m#0)
           == (forall v#4: Box ::
            { $Unbox(Map#Elements(m#0)[v#4]): DatatypeType } { Map#Domain(m#0)[v#4] }
            $IsBox(v#4, _module.BreadthFirstSearch$Vertex)
               ==>
              Map#Domain(m#0)[v#4]
               ==> _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex,
                $LS($LZ),
                this,
                source#0,
                v#4,
                $Unbox(Map#Elements(m#0)[v#4]): DatatypeType));
        assume (forall v#4: Box ::
          { $Unbox(Map#Elements(m#0)[v#4]): DatatypeType } { Map#Domain(m#0)[v#4] }
          $IsBox(v#4, _module.BreadthFirstSearch$Vertex)
             ==>
            Map#Domain(m#0)[v#4]
             ==> _module.BreadthFirstSearch.IsPath#canCall(_module.BreadthFirstSearch$Vertex,
              this,
              source#0,
              v#4,
              $Unbox(Map#Elements(m#0)[v#4]): DatatypeType));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.BreadthFirstSearch.ValidMap(_module.BreadthFirstSearch$Vertex, this, source#0, m#0),
          TBool);
        assert b$reqreads#0;
    }
}



// function declaration for _module.BreadthFirstSearch.Find
function _module.BreadthFirstSearch.Find(_module.BreadthFirstSearch$Vertex: Ty,
    this: ref,
    source#0: Box,
    x#0: Box,
    m#0: Map Box Box)
   : DatatypeType;

function _module.BreadthFirstSearch.Find#canCall(_module.BreadthFirstSearch$Vertex: Ty,
    this: ref,
    source#0: Box,
    x#0: Box,
    m#0: Map Box Box)
   : bool;

// consequence axiom for _module.BreadthFirstSearch.Find
axiom 11 <= $FunctionContextHeight
   ==> (forall _module.BreadthFirstSearch$Vertex: Ty,
      $Heap: Heap,
      this: ref,
      source#0: Box,
      x#0: Box,
      m#0: Map Box Box ::
    { _module.BreadthFirstSearch.Find(_module.BreadthFirstSearch$Vertex, this, source#0, x#0, m#0), $IsGoodHeap($Heap) }
    _module.BreadthFirstSearch.Find#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, x#0, m#0)
         || (11 != $FunctionContextHeight
           &&
          $IsGoodHeap($Heap)
           &&
          this != null
           &&
          $Is(this, Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex))
           && $IsAlloc(this,
            Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex),
            $Heap)
           && $IsBox(source#0, _module.BreadthFirstSearch$Vertex)
           && $IsBox(x#0, _module.BreadthFirstSearch$Vertex)
           && $Is(m#0,
            TMap(_module.BreadthFirstSearch$Vertex,
              Tclass._module.List(_module.BreadthFirstSearch$Vertex)))
           &&
          _module.BreadthFirstSearch.ValidMap(_module.BreadthFirstSearch$Vertex, this, source#0, m#0)
           && Map#Domain(m#0)[x#0])
       ==> _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex,
          $LS($LZ),
          this,
          source#0,
          x#0,
          _module.BreadthFirstSearch.Find(_module.BreadthFirstSearch$Vertex, this, source#0, x#0, m#0))
         && $Is(_module.BreadthFirstSearch.Find(_module.BreadthFirstSearch$Vertex, this, source#0, x#0, m#0),
          Tclass._module.List(_module.BreadthFirstSearch$Vertex)));

function _module.BreadthFirstSearch.Find#requires(Ty, ref, Box, Box, Map Box Box) : bool;

// #requires axiom for _module.BreadthFirstSearch.Find
axiom (forall _module.BreadthFirstSearch$Vertex: Ty,
    $Heap: Heap,
    this: ref,
    source#0: Box,
    x#0: Box,
    m#0: Map Box Box ::
  { _module.BreadthFirstSearch.Find#requires(_module.BreadthFirstSearch$Vertex, this, source#0, x#0, m#0), $IsGoodHeap($Heap) }
  $IsGoodHeap($Heap)
       &&
      this != null
       &&
      $Is(this, Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex))
       && $IsAlloc(this,
        Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex),
        $Heap)
       && $IsBox(source#0, _module.BreadthFirstSearch$Vertex)
       && $IsBox(x#0, _module.BreadthFirstSearch$Vertex)
       && $Is(m#0,
        TMap(_module.BreadthFirstSearch$Vertex,
          Tclass._module.List(_module.BreadthFirstSearch$Vertex)))
     ==> _module.BreadthFirstSearch.Find#requires(_module.BreadthFirstSearch$Vertex, this, source#0, x#0, m#0)
       == (_module.BreadthFirstSearch.ValidMap(_module.BreadthFirstSearch$Vertex, this, source#0, m#0)
         && Map#Domain(m#0)[x#0]));

// definition axiom for _module.BreadthFirstSearch.Find(revealed)
axiom 11 <= $FunctionContextHeight
   ==> (forall _module.BreadthFirstSearch$Vertex: Ty,
      $Heap: Heap,
      this: ref,
      source#0: Box,
      x#0: Box,
      m#0: Map Box Box ::
    { _module.BreadthFirstSearch.Find(_module.BreadthFirstSearch$Vertex, this, source#0, x#0, m#0), $IsGoodHeap($Heap) }
    _module.BreadthFirstSearch.Find#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, x#0, m#0)
         || (11 != $FunctionContextHeight
           &&
          $IsGoodHeap($Heap)
           &&
          this != null
           &&
          $Is(this, Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex))
           && $IsAlloc(this,
            Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex),
            $Heap)
           && $IsBox(source#0, _module.BreadthFirstSearch$Vertex)
           && $IsBox(x#0, _module.BreadthFirstSearch$Vertex)
           && $Is(m#0,
            TMap(_module.BreadthFirstSearch$Vertex,
              Tclass._module.List(_module.BreadthFirstSearch$Vertex)))
           &&
          _module.BreadthFirstSearch.ValidMap(_module.BreadthFirstSearch$Vertex, this, source#0, m#0)
           && Map#Domain(m#0)[x#0])
       ==> _module.BreadthFirstSearch.Find(_module.BreadthFirstSearch$Vertex, this, source#0, x#0, m#0)
         == $Unbox(Map#Elements(m#0)[x#0]): DatatypeType);

// definition axiom for _module.BreadthFirstSearch.Find for decreasing-related literals(revealed)
axiom 11 <= $FunctionContextHeight
   ==> (forall _module.BreadthFirstSearch$Vertex: Ty,
      $Heap: Heap,
      this: ref,
      source#0: Box,
      x#0: Box,
      m#0: Map Box Box ::
    {:weight 3} { _module.BreadthFirstSearch.Find(_module.BreadthFirstSearch$Vertex, this, source#0, x#0, Lit(m#0)), $IsGoodHeap($Heap) }
    _module.BreadthFirstSearch.Find#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, x#0, Lit(m#0))
         || (11 != $FunctionContextHeight
           &&
          $IsGoodHeap($Heap)
           &&
          this != null
           &&
          $Is(this, Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex))
           && $IsAlloc(this,
            Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex),
            $Heap)
           && $IsBox(source#0, _module.BreadthFirstSearch$Vertex)
           && $IsBox(x#0, _module.BreadthFirstSearch$Vertex)
           && $Is(m#0,
            TMap(_module.BreadthFirstSearch$Vertex,
              Tclass._module.List(_module.BreadthFirstSearch$Vertex)))
           &&
          _module.BreadthFirstSearch.ValidMap(_module.BreadthFirstSearch$Vertex, this, source#0, Lit(m#0))
           && Map#Domain(m#0)[x#0])
       ==> _module.BreadthFirstSearch.Find(_module.BreadthFirstSearch$Vertex, this, source#0, x#0, Lit(m#0))
         == $Unbox(Map#Elements(Lit(m#0))[x#0]): DatatypeType);

// definition axiom for _module.BreadthFirstSearch.Find for all literals(revealed)
axiom 11 <= $FunctionContextHeight
   ==> (forall _module.BreadthFirstSearch$Vertex: Ty,
      $Heap: Heap,
      this: ref,
      source#0: Box,
      x#0: Box,
      m#0: Map Box Box ::
    {:weight 3} { _module.BreadthFirstSearch.Find(_module.BreadthFirstSearch$Vertex, this, Lit(source#0), Lit(x#0), Lit(m#0)), $IsGoodHeap($Heap) }
    _module.BreadthFirstSearch.Find#canCall(_module.BreadthFirstSearch$Vertex, this, Lit(source#0), Lit(x#0), Lit(m#0))
         || (11 != $FunctionContextHeight
           &&
          $IsGoodHeap($Heap)
           &&
          this != null
           &&
          $Is(this, Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex))
           && $IsAlloc(this,
            Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex),
            $Heap)
           && $IsBox(source#0, _module.BreadthFirstSearch$Vertex)
           && $IsBox(x#0, _module.BreadthFirstSearch$Vertex)
           && $Is(m#0,
            TMap(_module.BreadthFirstSearch$Vertex,
              Tclass._module.List(_module.BreadthFirstSearch$Vertex)))
           &&
          _module.BreadthFirstSearch.ValidMap(_module.BreadthFirstSearch$Vertex, this, Lit(source#0), Lit(m#0))
           && Map#Domain(m#0)[x#0])
       ==> _module.BreadthFirstSearch.Find(_module.BreadthFirstSearch$Vertex, this, Lit(source#0), Lit(x#0), Lit(m#0))
         == $Unbox(Map#Elements(Lit(m#0))[Lit(x#0)]): DatatypeType);

procedure CheckWellformed$$_module.BreadthFirstSearch.Find(_module.BreadthFirstSearch$Vertex: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex))
         && $IsAlloc(this,
          Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex),
          $Heap),
    source#0: Box where $IsBox(source#0, _module.BreadthFirstSearch$Vertex),
    x#0: Box where $IsBox(x#0, _module.BreadthFirstSearch$Vertex),
    m#0: Map Box Box
       where $Is(m#0,
        TMap(_module.BreadthFirstSearch$Vertex,
          Tclass._module.List(_module.BreadthFirstSearch$Vertex))));
  free requires 11 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  ensures _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex,
    $LS($LS($LZ)),
    this,
    source#0,
    x#0,
    _module.BreadthFirstSearch.Find(_module.BreadthFirstSearch$Vertex, this, source#0, x#0, m#0));



implementation CheckWellformed$$_module.BreadthFirstSearch.Find(_module.BreadthFirstSearch$Vertex: Ty,
    this: ref,
    source#0: Box,
    x#0: Box,
    m#0: Map Box Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##source#0: Box;
  var ##m#0: Map Box Box;
  var b$reqreads#0: bool;
  var ##source#1: Box;
  var ##x#0: Box;
  var ##m#1: Map Box Box;
  var ##source#2: Box;
  var ##dest#0: Box;
  var ##p#0: DatatypeType;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function Find
    assume {:captureState "BreadthFirstSearch.dfy(206,11): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    ##source#0 := source#0;
    // assume allocatedness for argument to function
    assume $IsAllocBox(##source#0, _module.BreadthFirstSearch$Vertex, $Heap);
    ##m#0 := m#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##m#0,
      TMap(_module.BreadthFirstSearch$Vertex,
        Tclass._module.List(_module.BreadthFirstSearch$Vertex)),
      $Heap);
    b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    assume _module.BreadthFirstSearch.ValidMap#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, m#0);
    assume _module.BreadthFirstSearch.ValidMap(_module.BreadthFirstSearch$Vertex, this, source#0, m#0);
    assume Map#Domain(m#0)[x#0];
    assert b$reqreads#0;
    if (*)
    {
        assume $Is(_module.BreadthFirstSearch.Find(_module.BreadthFirstSearch$Vertex, this, source#0, x#0, m#0),
          Tclass._module.List(_module.BreadthFirstSearch$Vertex));
        ##source#1 := source#0;
        // assume allocatedness for argument to function
        assume $IsAllocBox(##source#1, _module.BreadthFirstSearch$Vertex, $Heap);
        ##x#0 := x#0;
        // assume allocatedness for argument to function
        assume $IsAllocBox(##x#0, _module.BreadthFirstSearch$Vertex, $Heap);
        ##m#1 := m#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##m#1,
          TMap(_module.BreadthFirstSearch$Vertex,
            Tclass._module.List(_module.BreadthFirstSearch$Vertex)),
          $Heap);
        assert {:subsumption 0} _module.BreadthFirstSearch.ValidMap#canCall(_module.BreadthFirstSearch$Vertex, this, ##source#1, ##m#1)
           ==> _module.BreadthFirstSearch.ValidMap(_module.BreadthFirstSearch$Vertex, this, ##source#1, ##m#1)
             || (forall v#0: Box ::
              { $Unbox(Map#Elements(##m#1)[v#0]): DatatypeType } { Map#Domain(##m#1)[v#0] }
              $IsBox(v#0, _module.BreadthFirstSearch$Vertex)
                 ==>
                Map#Domain(##m#1)[v#0]
                 ==> _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex,
                  $LS($LS($LZ)),
                  this,
                  ##source#1,
                  v#0,
                  $Unbox(Map#Elements(##m#1)[v#0]): DatatypeType));
        assert {:subsumption 0} Map#Domain(##m#1)[##x#0];
        assume _module.BreadthFirstSearch.ValidMap(_module.BreadthFirstSearch$Vertex, this, ##source#1, ##m#1)
           && Map#Domain(##m#1)[##x#0];
        assert (this == this && source#0 == source#0 && x#0 == x#0 && m#0 == m#0)
           || (Set#Subset(Map#Domain(##m#1), Map#Domain(m#0))
             && !Set#Subset(Map#Domain(m#0), Map#Domain(##m#1)));
        assume (this == this && source#0 == source#0 && x#0 == x#0 && m#0 == m#0)
           || _module.BreadthFirstSearch.Find#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, x#0, m#0);
        ##source#2 := source#0;
        // assume allocatedness for argument to function
        assume $IsAllocBox(##source#2, _module.BreadthFirstSearch$Vertex, $Heap);
        ##dest#0 := x#0;
        // assume allocatedness for argument to function
        assume $IsAllocBox(##dest#0, _module.BreadthFirstSearch$Vertex, $Heap);
        ##p#0 := _module.BreadthFirstSearch.Find(_module.BreadthFirstSearch$Vertex, this, source#0, x#0, m#0);
        // assume allocatedness for argument to function
        assume $IsAlloc(##p#0, Tclass._module.List(_module.BreadthFirstSearch$Vertex), $Heap);
        assume _module.BreadthFirstSearch.IsPath#canCall(_module.BreadthFirstSearch$Vertex,
          this,
          source#0,
          x#0,
          _module.BreadthFirstSearch.Find(_module.BreadthFirstSearch$Vertex, this, source#0, x#0, m#0));
        assume _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex,
          $LS($LZ),
          this,
          source#0,
          x#0,
          _module.BreadthFirstSearch.Find(_module.BreadthFirstSearch$Vertex, this, source#0, x#0, m#0));
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
          $o != null && read($Heap, $o, alloc) ==> false);
        assert Map#Domain(m#0)[x#0];
        assume _module.BreadthFirstSearch.Find(_module.BreadthFirstSearch$Vertex, this, source#0, x#0, m#0)
           == $Unbox(Map#Elements(m#0)[x#0]): DatatypeType;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(_module.BreadthFirstSearch.Find(_module.BreadthFirstSearch$Vertex, this, source#0, x#0, m#0),
          Tclass._module.List(_module.BreadthFirstSearch$Vertex));
    }
}



procedure CheckWellformed$$_module.BreadthFirstSearch.UpdatePaths(_module.BreadthFirstSearch$Vertex: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex))
         && $IsAlloc(this,
          Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex),
          $Heap),
    vSuccs#0: Set Box
       where $Is(vSuccs#0, TSet(_module.BreadthFirstSearch$Vertex))
         && $IsAlloc(vSuccs#0, TSet(_module.BreadthFirstSearch$Vertex), $Heap),
    source#0: Box
       where $IsBox(source#0, _module.BreadthFirstSearch$Vertex)
         && $IsAllocBox(source#0, _module.BreadthFirstSearch$Vertex, $Heap),
    paths#0: Map Box Box
       where $Is(paths#0,
          TMap(_module.BreadthFirstSearch$Vertex,
            Tclass._module.List(_module.BreadthFirstSearch$Vertex)))
         && $IsAlloc(paths#0,
          TMap(_module.BreadthFirstSearch$Vertex,
            Tclass._module.List(_module.BreadthFirstSearch$Vertex)),
          $Heap),
    v#0: Box
       where $IsBox(v#0, _module.BreadthFirstSearch$Vertex)
         && $IsAllocBox(v#0, _module.BreadthFirstSearch$Vertex, $Heap),
    pathToV#0: DatatypeType
       where $Is(pathToV#0, Tclass._module.List(_module.BreadthFirstSearch$Vertex))
         && $IsAlloc(pathToV#0, Tclass._module.List(_module.BreadthFirstSearch$Vertex), $Heap)
         && $IsA#_module.List(pathToV#0))
   returns (newPaths#0: Map Box Box
       where $Is(newPaths#0,
          TMap(_module.BreadthFirstSearch$Vertex,
            Tclass._module.List(_module.BreadthFirstSearch$Vertex)))
         && $IsAlloc(newPaths#0,
          TMap(_module.BreadthFirstSearch$Vertex,
            Tclass._module.List(_module.BreadthFirstSearch$Vertex)),
          $Heap));
  free requires 15 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.BreadthFirstSearch.UpdatePaths(_module.BreadthFirstSearch$Vertex: Ty,
    this: ref,
    vSuccs#0: Set Box,
    source#0: Box,
    paths#0: Map Box Box,
    v#0: Box,
    pathToV#0: DatatypeType)
   returns (newPaths#0: Map Box Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##source#0: Box;
  var ##m#0: Map Box Box;
  var ##m#1: Map Box Box;
  var succ#0: Box;
  var ##source#1: Box;
  var ##dest#0: Box;
  var ##p#0: DatatypeType;
  var ##source#2: Box;
  var ##m#2: Map Box Box;
  var ##m#3: Map Box Box;
  var ##m#4: Map Box Box;
  var x#0: Box;
  var ##source#3: Box;
  var ##x#0: Box;
  var ##m#5: Map Box Box;
  var ##source#4: Box;
  var ##x#1: Box;
  var ##m#6: Map Box Box;
  var x#2: Box;
  var ##source#5: Box;
  var ##x#2: Box;
  var ##m#7: Map Box Box;

    // AddMethodImpl: UpdatePaths, CheckWellformed$$_module.BreadthFirstSearch.UpdatePaths
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "BreadthFirstSearch.dfy(213,15): initial state"} true;
    ##source#0 := source#0;
    // assume allocatedness for argument to function
    assume $IsAllocBox(##source#0, _module.BreadthFirstSearch$Vertex, $Heap);
    ##m#0 := paths#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##m#0,
      TMap(_module.BreadthFirstSearch$Vertex,
        Tclass._module.List(_module.BreadthFirstSearch$Vertex)),
      $Heap);
    assume _module.BreadthFirstSearch.ValidMap#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, paths#0);
    assume _module.BreadthFirstSearch.ValidMap(_module.BreadthFirstSearch$Vertex, this, source#0, paths#0);
    ##m#1 := paths#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##m#1,
      TMap(_module.BreadthFirstSearch$Vertex,
        Tclass._module.List(_module.BreadthFirstSearch$Vertex)),
      $Heap);
    assume _module.__default.domain#canCall(_module.BreadthFirstSearch$Vertex,
      Tclass._module.List(_module.BreadthFirstSearch$Vertex),
      paths#0);
    assume Set#Disjoint(vSuccs#0,
      _module.__default.domain(_module.BreadthFirstSearch$Vertex,
        Tclass._module.List(_module.BreadthFirstSearch$Vertex),
        paths#0));
    havoc succ#0;
    assume $IsBox(succ#0, _module.BreadthFirstSearch$Vertex);
    if (*)
    {
        assume vSuccs#0[succ#0];
        ##source#1 := source#0;
        // assume allocatedness for argument to function
        assume $IsAllocBox(##source#1, _module.BreadthFirstSearch$Vertex, $Heap);
        ##dest#0 := succ#0;
        // assume allocatedness for argument to function
        assume $IsAllocBox(##dest#0, _module.BreadthFirstSearch$Vertex, $Heap);
        ##p#0 := #_module.List.Cons(v#0, pathToV#0);
        // assume allocatedness for argument to function
        assume $IsAlloc(##p#0, Tclass._module.List(_module.BreadthFirstSearch$Vertex), $Heap);
        assume _module.BreadthFirstSearch.IsPath#canCall(_module.BreadthFirstSearch$Vertex,
          this,
          source#0,
          succ#0,
          #_module.List.Cons(v#0, pathToV#0));
        assume _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex,
          $LS($LZ),
          this,
          source#0,
          succ#0,
          #_module.List.Cons(v#0, pathToV#0));
    }
    else
    {
        assume vSuccs#0[succ#0]
           ==> _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex,
            $LS($LZ),
            this,
            source#0,
            succ#0,
            #_module.List.Cons(v#0, pathToV#0));
    }

    assume (forall succ#1: Box ::
      { _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex,
          $LS($LZ),
          this,
          source#0,
          succ#1,
          #_module.List.Cons(v#0, pathToV#0)) }
        { vSuccs#0[succ#1] }
      $IsBox(succ#1, _module.BreadthFirstSearch$Vertex)
         ==>
        vSuccs#0[succ#1]
         ==> _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex,
          $LS($LZ),
          this,
          source#0,
          succ#1,
          #_module.List.Cons(v#0, pathToV#0)));
    havoc $Heap;
    assume old($Heap) == $Heap;
    havoc newPaths#0;
    assume {:captureState "BreadthFirstSearch.dfy(219,39): post-state"} true;
    ##source#2 := source#0;
    // assume allocatedness for argument to function
    assume $IsAllocBox(##source#2, _module.BreadthFirstSearch$Vertex, $Heap);
    ##m#2 := newPaths#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##m#2,
      TMap(_module.BreadthFirstSearch$Vertex,
        Tclass._module.List(_module.BreadthFirstSearch$Vertex)),
      $Heap);
    assume _module.BreadthFirstSearch.ValidMap#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, newPaths#0);
    assume _module.BreadthFirstSearch.ValidMap(_module.BreadthFirstSearch$Vertex, this, source#0, newPaths#0);
    ##m#3 := newPaths#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##m#3,
      TMap(_module.BreadthFirstSearch$Vertex,
        Tclass._module.List(_module.BreadthFirstSearch$Vertex)),
      $Heap);
    assume _module.__default.domain#canCall(_module.BreadthFirstSearch$Vertex,
      Tclass._module.List(_module.BreadthFirstSearch$Vertex),
      newPaths#0);
    ##m#4 := paths#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##m#4,
      TMap(_module.BreadthFirstSearch$Vertex,
        Tclass._module.List(_module.BreadthFirstSearch$Vertex)),
      $Heap);
    assume _module.__default.domain#canCall(_module.BreadthFirstSearch$Vertex,
      Tclass._module.List(_module.BreadthFirstSearch$Vertex),
      paths#0);
    assume Set#Equal(_module.__default.domain(_module.BreadthFirstSearch$Vertex,
        Tclass._module.List(_module.BreadthFirstSearch$Vertex),
        newPaths#0),
      Set#Union(_module.__default.domain(_module.BreadthFirstSearch$Vertex,
          Tclass._module.List(_module.BreadthFirstSearch$Vertex),
          paths#0),
        vSuccs#0));
    havoc x#0;
    assume $IsBox(x#0, _module.BreadthFirstSearch$Vertex);
    if (*)
    {
        assume Map#Domain(paths#0)[x#0];
        ##source#3 := source#0;
        // assume allocatedness for argument to function
        assume $IsAllocBox(##source#3, _module.BreadthFirstSearch$Vertex, $Heap);
        ##x#0 := x#0;
        // assume allocatedness for argument to function
        assume $IsAllocBox(##x#0, _module.BreadthFirstSearch$Vertex, $Heap);
        ##m#5 := paths#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##m#5,
          TMap(_module.BreadthFirstSearch$Vertex,
            Tclass._module.List(_module.BreadthFirstSearch$Vertex)),
          $Heap);
        assert {:subsumption 0} _module.BreadthFirstSearch.ValidMap#canCall(_module.BreadthFirstSearch$Vertex, this, ##source#3, ##m#5)
           ==> _module.BreadthFirstSearch.ValidMap(_module.BreadthFirstSearch$Vertex, this, ##source#3, ##m#5)
             || (forall v#1: Box ::
              { $Unbox(Map#Elements(##m#5)[v#1]): DatatypeType } { Map#Domain(##m#5)[v#1] }
              $IsBox(v#1, _module.BreadthFirstSearch$Vertex)
                 ==>
                Map#Domain(##m#5)[v#1]
                 ==> _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex,
                  $LS($LS($LZ)),
                  this,
                  ##source#3,
                  v#1,
                  $Unbox(Map#Elements(##m#5)[v#1]): DatatypeType));
        assert {:subsumption 0} Map#Domain(##m#5)[##x#0];
        assume _module.BreadthFirstSearch.ValidMap(_module.BreadthFirstSearch$Vertex, this, ##source#3, ##m#5)
           && Map#Domain(##m#5)[##x#0];
        assume _module.BreadthFirstSearch.Find#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, x#0, paths#0);
        ##source#4 := source#0;
        // assume allocatedness for argument to function
        assume $IsAllocBox(##source#4, _module.BreadthFirstSearch$Vertex, $Heap);
        ##x#1 := x#0;
        // assume allocatedness for argument to function
        assume $IsAllocBox(##x#1, _module.BreadthFirstSearch$Vertex, $Heap);
        ##m#6 := newPaths#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##m#6,
          TMap(_module.BreadthFirstSearch$Vertex,
            Tclass._module.List(_module.BreadthFirstSearch$Vertex)),
          $Heap);
        assert {:subsumption 0} _module.BreadthFirstSearch.ValidMap#canCall(_module.BreadthFirstSearch$Vertex, this, ##source#4, ##m#6)
           ==> _module.BreadthFirstSearch.ValidMap(_module.BreadthFirstSearch$Vertex, this, ##source#4, ##m#6)
             || (forall v#2: Box ::
              { $Unbox(Map#Elements(##m#6)[v#2]): DatatypeType } { Map#Domain(##m#6)[v#2] }
              $IsBox(v#2, _module.BreadthFirstSearch$Vertex)
                 ==>
                Map#Domain(##m#6)[v#2]
                 ==> _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex,
                  $LS($LS($LZ)),
                  this,
                  ##source#4,
                  v#2,
                  $Unbox(Map#Elements(##m#6)[v#2]): DatatypeType));
        assert {:subsumption 0} Map#Domain(##m#6)[##x#1];
        assume _module.BreadthFirstSearch.ValidMap(_module.BreadthFirstSearch$Vertex, this, ##source#4, ##m#6)
           && Map#Domain(##m#6)[##x#1];
        assume _module.BreadthFirstSearch.Find#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, x#0, newPaths#0);
        assume _module.BreadthFirstSearch.Find(_module.BreadthFirstSearch$Vertex, this, source#0, x#0, paths#0)
           == _module.BreadthFirstSearch.Find(_module.BreadthFirstSearch$Vertex, this, source#0, x#0, newPaths#0);
    }
    else
    {
        assume Map#Domain(paths#0)[x#0]
           ==> _module.BreadthFirstSearch.Find(_module.BreadthFirstSearch$Vertex, this, source#0, x#0, paths#0)
             == _module.BreadthFirstSearch.Find(_module.BreadthFirstSearch$Vertex, this, source#0, x#0, newPaths#0);
    }

    assume (forall x#1: Box ::
      { _module.BreadthFirstSearch.Find(_module.BreadthFirstSearch$Vertex, this, source#0, x#1, newPaths#0) }
        { _module.BreadthFirstSearch.Find(_module.BreadthFirstSearch$Vertex, this, source#0, x#1, paths#0) }
        { Map#Domain(paths#0)[x#1] }
      $IsBox(x#1, _module.BreadthFirstSearch$Vertex)
         ==>
        Map#Domain(paths#0)[x#1]
         ==> _module.BreadthFirstSearch.Find(_module.BreadthFirstSearch$Vertex, this, source#0, x#1, paths#0)
           == _module.BreadthFirstSearch.Find(_module.BreadthFirstSearch$Vertex, this, source#0, x#1, newPaths#0));
    havoc x#2;
    assume $IsBox(x#2, _module.BreadthFirstSearch$Vertex);
    if (*)
    {
        assume vSuccs#0[x#2];
        ##source#5 := source#0;
        // assume allocatedness for argument to function
        assume $IsAllocBox(##source#5, _module.BreadthFirstSearch$Vertex, $Heap);
        ##x#2 := x#2;
        // assume allocatedness for argument to function
        assume $IsAllocBox(##x#2, _module.BreadthFirstSearch$Vertex, $Heap);
        ##m#7 := newPaths#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##m#7,
          TMap(_module.BreadthFirstSearch$Vertex,
            Tclass._module.List(_module.BreadthFirstSearch$Vertex)),
          $Heap);
        assert {:subsumption 0} _module.BreadthFirstSearch.ValidMap#canCall(_module.BreadthFirstSearch$Vertex, this, ##source#5, ##m#7)
           ==> _module.BreadthFirstSearch.ValidMap(_module.BreadthFirstSearch$Vertex, this, ##source#5, ##m#7)
             || (forall v#3: Box ::
              { $Unbox(Map#Elements(##m#7)[v#3]): DatatypeType } { Map#Domain(##m#7)[v#3] }
              $IsBox(v#3, _module.BreadthFirstSearch$Vertex)
                 ==>
                Map#Domain(##m#7)[v#3]
                 ==> _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex,
                  $LS($LS($LZ)),
                  this,
                  ##source#5,
                  v#3,
                  $Unbox(Map#Elements(##m#7)[v#3]): DatatypeType));
        assert {:subsumption 0} Map#Domain(##m#7)[##x#2];
        assume _module.BreadthFirstSearch.ValidMap(_module.BreadthFirstSearch$Vertex, this, ##source#5, ##m#7)
           && Map#Domain(##m#7)[##x#2];
        assume _module.BreadthFirstSearch.Find#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, x#2, newPaths#0);
        assume _module.BreadthFirstSearch.Find(_module.BreadthFirstSearch$Vertex, this, source#0, x#2, newPaths#0)
           == #_module.List.Cons(v#0, pathToV#0);
    }
    else
    {
        assume vSuccs#0[x#2]
           ==> _module.BreadthFirstSearch.Find(_module.BreadthFirstSearch$Vertex, this, source#0, x#2, newPaths#0)
             == #_module.List.Cons(v#0, pathToV#0);
    }

    assume (forall x#3: Box ::
      { _module.BreadthFirstSearch.Find(_module.BreadthFirstSearch$Vertex, this, source#0, x#3, newPaths#0) }
        { vSuccs#0[x#3] }
      $IsBox(x#3, _module.BreadthFirstSearch$Vertex)
         ==>
        vSuccs#0[x#3]
         ==> _module.BreadthFirstSearch.Find(_module.BreadthFirstSearch$Vertex, this, source#0, x#3, newPaths#0)
           == #_module.List.Cons(v#0, pathToV#0));
}



procedure Call$$_module.BreadthFirstSearch.UpdatePaths(_module.BreadthFirstSearch$Vertex: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex))
         && $IsAlloc(this,
          Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex),
          $Heap),
    vSuccs#0: Set Box
       where $Is(vSuccs#0, TSet(_module.BreadthFirstSearch$Vertex))
         && $IsAlloc(vSuccs#0, TSet(_module.BreadthFirstSearch$Vertex), $Heap),
    source#0: Box
       where $IsBox(source#0, _module.BreadthFirstSearch$Vertex)
         && $IsAllocBox(source#0, _module.BreadthFirstSearch$Vertex, $Heap),
    paths#0: Map Box Box
       where $Is(paths#0,
          TMap(_module.BreadthFirstSearch$Vertex,
            Tclass._module.List(_module.BreadthFirstSearch$Vertex)))
         && $IsAlloc(paths#0,
          TMap(_module.BreadthFirstSearch$Vertex,
            Tclass._module.List(_module.BreadthFirstSearch$Vertex)),
          $Heap),
    v#0: Box
       where $IsBox(v#0, _module.BreadthFirstSearch$Vertex)
         && $IsAllocBox(v#0, _module.BreadthFirstSearch$Vertex, $Heap),
    pathToV#0: DatatypeType
       where $Is(pathToV#0, Tclass._module.List(_module.BreadthFirstSearch$Vertex))
         && $IsAlloc(pathToV#0, Tclass._module.List(_module.BreadthFirstSearch$Vertex), $Heap)
         && $IsA#_module.List(pathToV#0))
   returns (newPaths#0: Map Box Box
       where $Is(newPaths#0,
          TMap(_module.BreadthFirstSearch$Vertex,
            Tclass._module.List(_module.BreadthFirstSearch$Vertex)))
         && $IsAlloc(newPaths#0,
          TMap(_module.BreadthFirstSearch$Vertex,
            Tclass._module.List(_module.BreadthFirstSearch$Vertex)),
          $Heap));
  // user-defined preconditions
  requires _module.BreadthFirstSearch.ValidMap#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, paths#0)
     ==> _module.BreadthFirstSearch.ValidMap(_module.BreadthFirstSearch$Vertex, this, source#0, paths#0)
       || (forall v#4: Box ::
        { $Unbox(Map#Elements(paths#0)[v#4]): DatatypeType }
          { Map#Domain(paths#0)[v#4] }
        $IsBox(v#4, _module.BreadthFirstSearch$Vertex)
           ==>
          Map#Domain(paths#0)[v#4]
           ==> _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex,
            $LS($LS($LZ)),
            this,
            source#0,
            v#4,
            $Unbox(Map#Elements(paths#0)[v#4]): DatatypeType));
  requires Set#Disjoint(vSuccs#0,
    _module.__default.domain(_module.BreadthFirstSearch$Vertex,
      Tclass._module.List(_module.BreadthFirstSearch$Vertex),
      paths#0));
  requires (forall succ#1: Box ::
    { _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex,
        $LS($LS($LZ)),
        this,
        source#0,
        succ#1,
        #_module.List.Cons(v#0, pathToV#0)) }
      { vSuccs#0[succ#1] }
    $IsBox(succ#1, _module.BreadthFirstSearch$Vertex)
       ==>
      vSuccs#0[succ#1]
       ==> _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex,
        $LS($LS($LZ)),
        this,
        source#0,
        succ#1,
        #_module.List.Cons(v#0, pathToV#0)));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.BreadthFirstSearch.ValidMap#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, newPaths#0)
     && (_module.BreadthFirstSearch.ValidMap(_module.BreadthFirstSearch$Vertex, this, source#0, newPaths#0)
       ==> _module.__default.domain#canCall(_module.BreadthFirstSearch$Vertex,
          Tclass._module.List(_module.BreadthFirstSearch$Vertex),
          newPaths#0)
         && _module.__default.domain#canCall(_module.BreadthFirstSearch$Vertex,
          Tclass._module.List(_module.BreadthFirstSearch$Vertex),
          paths#0));
  free ensures _module.BreadthFirstSearch.ValidMap#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, newPaths#0)
     &&
    _module.BreadthFirstSearch.ValidMap(_module.BreadthFirstSearch$Vertex, this, source#0, newPaths#0)
     && (forall v#5: Box ::
      { $Unbox(Map#Elements(newPaths#0)[v#5]): DatatypeType }
        { Map#Domain(newPaths#0)[v#5] }
      $IsBox(v#5, _module.BreadthFirstSearch$Vertex)
         ==>
        Map#Domain(newPaths#0)[v#5]
         ==> _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex,
          $LS($LZ),
          this,
          source#0,
          v#5,
          $Unbox(Map#Elements(newPaths#0)[v#5]): DatatypeType));
  ensures Set#Equal(_module.__default.domain(_module.BreadthFirstSearch$Vertex,
      Tclass._module.List(_module.BreadthFirstSearch$Vertex),
      newPaths#0),
    Set#Union(_module.__default.domain(_module.BreadthFirstSearch$Vertex,
        Tclass._module.List(_module.BreadthFirstSearch$Vertex),
        paths#0),
      vSuccs#0));
  free ensures (forall x#1: Box ::
    { _module.BreadthFirstSearch.Find(_module.BreadthFirstSearch$Vertex, this, source#0, x#1, newPaths#0) }
      { _module.BreadthFirstSearch.Find(_module.BreadthFirstSearch$Vertex, this, source#0, x#1, paths#0) }
      { Map#Domain(paths#0)[x#1] }
    $IsBox(x#1, _module.BreadthFirstSearch$Vertex)
       ==>
      Map#Domain(paths#0)[x#1]
       ==> _module.BreadthFirstSearch.Find#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, x#1, paths#0)
         && _module.BreadthFirstSearch.Find#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, x#1, newPaths#0));
  ensures (forall x#1: Box ::
    { _module.BreadthFirstSearch.Find(_module.BreadthFirstSearch$Vertex, this, source#0, x#1, newPaths#0) }
      { _module.BreadthFirstSearch.Find(_module.BreadthFirstSearch$Vertex, this, source#0, x#1, paths#0) }
      { Map#Domain(paths#0)[x#1] }
    $IsBox(x#1, _module.BreadthFirstSearch$Vertex)
       ==>
      Map#Domain(paths#0)[x#1]
       ==> _module.BreadthFirstSearch.Find(_module.BreadthFirstSearch$Vertex, this, source#0, x#1, paths#0)
         == _module.BreadthFirstSearch.Find(_module.BreadthFirstSearch$Vertex, this, source#0, x#1, newPaths#0));
  free ensures (forall x#3: Box ::
    { _module.BreadthFirstSearch.Find(_module.BreadthFirstSearch$Vertex, this, source#0, x#3, newPaths#0) }
      { vSuccs#0[x#3] }
    $IsBox(x#3, _module.BreadthFirstSearch$Vertex)
       ==>
      vSuccs#0[x#3]
       ==> _module.BreadthFirstSearch.Find#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, x#3, newPaths#0));
  ensures (forall x#3: Box ::
    { _module.BreadthFirstSearch.Find(_module.BreadthFirstSearch$Vertex, this, source#0, x#3, newPaths#0) }
      { vSuccs#0[x#3] }
    $IsBox(x#3, _module.BreadthFirstSearch$Vertex)
       ==>
      vSuccs#0[x#3]
       ==> _module.BreadthFirstSearch.Find(_module.BreadthFirstSearch$Vertex, this, source#0, x#3, newPaths#0)
         == #_module.List.Cons(v#0, pathToV#0));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.BreadthFirstSearch.UpdatePaths(_module.BreadthFirstSearch$Vertex: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex))
         && $IsAlloc(this,
          Tclass._module.BreadthFirstSearch(_module.BreadthFirstSearch$Vertex),
          $Heap),
    vSuccs#0: Set Box
       where $Is(vSuccs#0, TSet(_module.BreadthFirstSearch$Vertex))
         && $IsAlloc(vSuccs#0, TSet(_module.BreadthFirstSearch$Vertex), $Heap),
    source#0: Box
       where $IsBox(source#0, _module.BreadthFirstSearch$Vertex)
         && $IsAllocBox(source#0, _module.BreadthFirstSearch$Vertex, $Heap),
    paths#0: Map Box Box
       where $Is(paths#0,
          TMap(_module.BreadthFirstSearch$Vertex,
            Tclass._module.List(_module.BreadthFirstSearch$Vertex)))
         && $IsAlloc(paths#0,
          TMap(_module.BreadthFirstSearch$Vertex,
            Tclass._module.List(_module.BreadthFirstSearch$Vertex)),
          $Heap),
    v#0: Box
       where $IsBox(v#0, _module.BreadthFirstSearch$Vertex)
         && $IsAllocBox(v#0, _module.BreadthFirstSearch$Vertex, $Heap),
    pathToV#0: DatatypeType
       where $Is(pathToV#0, Tclass._module.List(_module.BreadthFirstSearch$Vertex))
         && $IsAlloc(pathToV#0, Tclass._module.List(_module.BreadthFirstSearch$Vertex), $Heap)
         && $IsA#_module.List(pathToV#0))
   returns (newPaths#0: Map Box Box
       where $Is(newPaths#0,
          TMap(_module.BreadthFirstSearch$Vertex,
            Tclass._module.List(_module.BreadthFirstSearch$Vertex)))
         && $IsAlloc(newPaths#0,
          TMap(_module.BreadthFirstSearch$Vertex,
            Tclass._module.List(_module.BreadthFirstSearch$Vertex)),
          $Heap),
    $_reverifyPost: bool);
  free requires 15 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.BreadthFirstSearch.ValidMap#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, paths#0)
     &&
    _module.BreadthFirstSearch.ValidMap(_module.BreadthFirstSearch$Vertex, this, source#0, paths#0)
     && (forall v#6: Box ::
      { $Unbox(Map#Elements(paths#0)[v#6]): DatatypeType }
        { Map#Domain(paths#0)[v#6] }
      $IsBox(v#6, _module.BreadthFirstSearch$Vertex)
         ==>
        Map#Domain(paths#0)[v#6]
         ==> _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex,
          $LS($LZ),
          this,
          source#0,
          v#6,
          $Unbox(Map#Elements(paths#0)[v#6]): DatatypeType));
  requires Set#Disjoint(vSuccs#0,
    _module.__default.domain(_module.BreadthFirstSearch$Vertex,
      Tclass._module.List(_module.BreadthFirstSearch$Vertex),
      paths#0));
  free requires (forall succ#1: Box ::
    { _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex,
        $LS($LZ),
        this,
        source#0,
        succ#1,
        #_module.List.Cons(v#0, pathToV#0)) }
      { vSuccs#0[succ#1] }
    $IsBox(succ#1, _module.BreadthFirstSearch$Vertex)
       ==>
      vSuccs#0[succ#1]
       ==> _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex,
        $LS($LZ),
        this,
        source#0,
        succ#1,
        #_module.List.Cons(v#0, pathToV#0)));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.BreadthFirstSearch.ValidMap#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, newPaths#0)
     && (_module.BreadthFirstSearch.ValidMap(_module.BreadthFirstSearch$Vertex, this, source#0, newPaths#0)
       ==> _module.__default.domain#canCall(_module.BreadthFirstSearch$Vertex,
          Tclass._module.List(_module.BreadthFirstSearch$Vertex),
          newPaths#0)
         && _module.__default.domain#canCall(_module.BreadthFirstSearch$Vertex,
          Tclass._module.List(_module.BreadthFirstSearch$Vertex),
          paths#0));
  ensures _module.BreadthFirstSearch.ValidMap#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, newPaths#0)
     ==> _module.BreadthFirstSearch.ValidMap(_module.BreadthFirstSearch$Vertex, this, source#0, newPaths#0)
       || (forall v#7: Box ::
        { $Unbox(Map#Elements(newPaths#0)[v#7]): DatatypeType }
          { Map#Domain(newPaths#0)[v#7] }
        $IsBox(v#7, _module.BreadthFirstSearch$Vertex)
           ==>
          Map#Domain(newPaths#0)[v#7]
           ==> _module.BreadthFirstSearch.IsPath(_module.BreadthFirstSearch$Vertex,
            $LS($LS($LZ)),
            this,
            source#0,
            v#7,
            $Unbox(Map#Elements(newPaths#0)[v#7]): DatatypeType));
  ensures Set#Equal(_module.__default.domain(_module.BreadthFirstSearch$Vertex,
      Tclass._module.List(_module.BreadthFirstSearch$Vertex),
      newPaths#0),
    Set#Union(_module.__default.domain(_module.BreadthFirstSearch$Vertex,
        Tclass._module.List(_module.BreadthFirstSearch$Vertex),
        paths#0),
      vSuccs#0));
  free ensures (forall x#1: Box ::
    { _module.BreadthFirstSearch.Find(_module.BreadthFirstSearch$Vertex, this, source#0, x#1, newPaths#0) }
      { _module.BreadthFirstSearch.Find(_module.BreadthFirstSearch$Vertex, this, source#0, x#1, paths#0) }
      { Map#Domain(paths#0)[x#1] }
    $IsBox(x#1, _module.BreadthFirstSearch$Vertex)
       ==>
      Map#Domain(paths#0)[x#1]
       ==> _module.BreadthFirstSearch.Find#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, x#1, paths#0)
         && _module.BreadthFirstSearch.Find#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, x#1, newPaths#0));
  ensures (forall x#1: Box ::
    { _module.BreadthFirstSearch.Find(_module.BreadthFirstSearch$Vertex, this, source#0, x#1, newPaths#0) }
      { _module.BreadthFirstSearch.Find(_module.BreadthFirstSearch$Vertex, this, source#0, x#1, paths#0) }
      { Map#Domain(paths#0)[x#1] }
    $IsBox(x#1, _module.BreadthFirstSearch$Vertex)
       ==>
      Map#Domain(paths#0)[x#1]
       ==> _module.BreadthFirstSearch.Find(_module.BreadthFirstSearch$Vertex, this, source#0, x#1, paths#0)
         == _module.BreadthFirstSearch.Find(_module.BreadthFirstSearch$Vertex, this, source#0, x#1, newPaths#0));
  free ensures (forall x#3: Box ::
    { _module.BreadthFirstSearch.Find(_module.BreadthFirstSearch$Vertex, this, source#0, x#3, newPaths#0) }
      { vSuccs#0[x#3] }
    $IsBox(x#3, _module.BreadthFirstSearch$Vertex)
       ==>
      vSuccs#0[x#3]
       ==> _module.BreadthFirstSearch.Find#canCall(_module.BreadthFirstSearch$Vertex, this, source#0, x#3, newPaths#0));
  ensures (forall x#3: Box ::
    { _module.BreadthFirstSearch.Find(_module.BreadthFirstSearch$Vertex, this, source#0, x#3, newPaths#0) }
      { vSuccs#0[x#3] }
    $IsBox(x#3, _module.BreadthFirstSearch$Vertex)
       ==>
      vSuccs#0[x#3]
       ==> _module.BreadthFirstSearch.Find(_module.BreadthFirstSearch$Vertex, this, source#0, x#3, newPaths#0)
         == #_module.List.Cons(v#0, pathToV#0));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.BreadthFirstSearch.UpdatePaths(_module.BreadthFirstSearch$Vertex: Ty,
    this: ref,
    vSuccs#0: Set Box,
    source#0: Box,
    paths#0: Map Box Box,
    v#0: Box,
    pathToV#0: DatatypeType)
   returns (newPaths#0: Map Box Box, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var succ#2: Box
     where $IsBox(succ#2, _module.BreadthFirstSearch$Vertex)
       && $IsAllocBox(succ#2, _module.BreadthFirstSearch$Vertex, $Heap);
  var ##m#8: Map Box Box;
  var ##m#9: Map Box Box;
  var $rhs##0: Map Box Box
     where $Is($rhs##0,
        TMap(_module.BreadthFirstSearch$Vertex,
          Tclass._module.List(_module.BreadthFirstSearch$Vertex)))
       && $IsAlloc($rhs##0,
        TMap(_module.BreadthFirstSearch$Vertex,
          Tclass._module.List(_module.BreadthFirstSearch$Vertex)),
        $Heap);
  var vSuccs##0: Set Box;
  var source##0: Box;
  var paths##0: Map Box Box;
  var v##0: Box;
  var pathToV##0: DatatypeType;

    // AddMethodImpl: UpdatePaths, Impl$$_module.BreadthFirstSearch.UpdatePaths
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "BreadthFirstSearch.dfy(223,2): initial state"} true;
    $_reverifyPost := false;
    // ----- if statement ----- BreadthFirstSearch.dfy(224,5)
    assume true;
    if (Set#Equal(vSuccs#0, Set#Empty(): Set Box))
    {
        // ----- assignment statement ----- BreadthFirstSearch.dfy(225,16)
        assume true;
        assume true;
        newPaths#0 := paths#0;
        assume {:captureState "BreadthFirstSearch.dfy(225,23)"} true;
    }
    else
    {
        // ----- assign-such-that statement ----- BreadthFirstSearch.dfy(227,16)
        assume true;
        havoc succ#2;
        assume true;
        assert (exists $as#succ0#0: Box ::
          $IsBox($as#succ0#0, _module.BreadthFirstSearch$Vertex) && vSuccs#0[$as#succ0#0]);
        assume vSuccs#0[succ#2];
        assume {:captureState "BreadthFirstSearch.dfy(227,32)"} true;
        // ----- assignment statement ----- BreadthFirstSearch.dfy(228,16)
        assume true;
        assume true;
        newPaths#0 := Map#Build(paths#0, succ#2, $Box(#_module.List.Cons(v#0, pathToV#0)));
        assume {:captureState "BreadthFirstSearch.dfy(228,49)"} true;
        // ----- assert statement ----- BreadthFirstSearch.dfy(229,7)
        ##m#8 := newPaths#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##m#8,
          TMap(_module.BreadthFirstSearch$Vertex,
            Tclass._module.List(_module.BreadthFirstSearch$Vertex)),
          $Heap);
        assume _module.__default.domain#canCall(_module.BreadthFirstSearch$Vertex,
          Tclass._module.List(_module.BreadthFirstSearch$Vertex),
          newPaths#0);
        ##m#9 := paths#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##m#9,
          TMap(_module.BreadthFirstSearch$Vertex,
            Tclass._module.List(_module.BreadthFirstSearch$Vertex)),
          $Heap);
        assume _module.__default.domain#canCall(_module.BreadthFirstSearch$Vertex,
          Tclass._module.List(_module.BreadthFirstSearch$Vertex),
          paths#0);
        assume _module.__default.domain#canCall(_module.BreadthFirstSearch$Vertex,
            Tclass._module.List(_module.BreadthFirstSearch$Vertex),
            newPaths#0)
           && _module.__default.domain#canCall(_module.BreadthFirstSearch$Vertex,
            Tclass._module.List(_module.BreadthFirstSearch$Vertex),
            paths#0);
        assert Set#Equal(_module.__default.domain(_module.BreadthFirstSearch$Vertex,
            Tclass._module.List(_module.BreadthFirstSearch$Vertex),
            newPaths#0),
          Set#Union(_module.__default.domain(_module.BreadthFirstSearch$Vertex,
              Tclass._module.List(_module.BreadthFirstSearch$Vertex),
              paths#0),
            Set#UnionOne(Set#Empty(): Set Box, succ#2)));
        // ----- call statement ----- BreadthFirstSearch.dfy(230,30)
        assume true;
        // TrCallStmt: Adding lhs Microsoft.Dafny.IdentifierExpr with type map<Vertex, List<Vertex>>
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        vSuccs##0 := Set#Difference(vSuccs#0, Set#UnionOne(Set#Empty(): Set Box, succ#2));
        assume true;
        // ProcessCallStmt: CheckSubrange
        source##0 := source#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        paths##0 := newPaths#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        v##0 := v#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        pathToV##0 := pathToV#0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assert (Set#Subset(vSuccs##0, vSuccs#0) && !Set#Subset(vSuccs#0, vSuccs##0))
           || (Set#Equal(vSuccs##0, vSuccs#0)
             && ((Set#Subset(Map#Domain(paths##0), Map#Domain(paths#0))
                 && !Set#Subset(Map#Domain(paths#0), Map#Domain(paths##0)))
               || (Set#Equal(Map#Domain(paths##0), Map#Domain(paths#0))
                 && DtRank(pathToV##0) < DtRank(pathToV#0))));
        // ProcessCallStmt: Make the call
        call $rhs##0 := Call$$_module.BreadthFirstSearch.UpdatePaths(_module.BreadthFirstSearch$Vertex, this, vSuccs##0, source##0, paths##0, v##0, pathToV##0);
        // TrCallStmt: After ProcessCallStmt
        newPaths#0 := $rhs##0;
        assume {:captureState "BreadthFirstSearch.dfy(230,76)"} true;
    }
}



const unique class._module.List: ClassName;

// Constructor function declaration
function #_module.List.Nil() : DatatypeType;

const unique ##_module.List.Nil: DtCtorId;

// Constructor identifier
axiom DatatypeCtorId(#_module.List.Nil()) == ##_module.List.Nil;

function _module.List.Nil_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType ::
  { _module.List.Nil_q(d) }
  _module.List.Nil_q(d) <==> DatatypeCtorId(d) == ##_module.List.Nil);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType ::
  { _module.List.Nil_q(d) }
  _module.List.Nil_q(d) ==> d == #_module.List.Nil());

// Constructor $Is
axiom (forall _module.List$T: Ty ::
  { $Is(#_module.List.Nil(), Tclass._module.List(_module.List$T)) }
  $Is(#_module.List.Nil(), Tclass._module.List(_module.List$T)));

// Constructor $IsAlloc
axiom (forall _module.List$T: Ty, $h: Heap ::
  { $IsAlloc(#_module.List.Nil(), Tclass._module.List(_module.List$T), $h) }
  $IsGoodHeap($h)
     ==> $IsAlloc(#_module.List.Nil(), Tclass._module.List(_module.List$T), $h));

// Constructor literal
axiom #_module.List.Nil() == Lit(#_module.List.Nil());

// Constructor function declaration
function #_module.List.Cons(Box, DatatypeType) : DatatypeType;

const unique ##_module.List.Cons: DtCtorId;

// Constructor identifier
axiom (forall a#5#0#0: Box, a#5#1#0: DatatypeType ::
  { #_module.List.Cons(a#5#0#0, a#5#1#0) }
  DatatypeCtorId(#_module.List.Cons(a#5#0#0, a#5#1#0)) == ##_module.List.Cons);

function _module.List.Cons_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType ::
  { _module.List.Cons_q(d) }
  _module.List.Cons_q(d) <==> DatatypeCtorId(d) == ##_module.List.Cons);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType ::
  { _module.List.Cons_q(d) }
  _module.List.Cons_q(d)
     ==> (exists a#6#0#0: Box, a#6#1#0: DatatypeType ::
      d == #_module.List.Cons(a#6#0#0, a#6#1#0)));

// Constructor $Is
axiom (forall _module.List$T: Ty, a#7#0#0: Box, a#7#1#0: DatatypeType ::
  { $Is(#_module.List.Cons(a#7#0#0, a#7#1#0), Tclass._module.List(_module.List$T)) }
  $Is(#_module.List.Cons(a#7#0#0, a#7#1#0), Tclass._module.List(_module.List$T))
     <==> $IsBox(a#7#0#0, _module.List$T)
       && $Is(a#7#1#0, Tclass._module.List(_module.List$T)));

// Constructor $IsAlloc
axiom (forall _module.List$T: Ty, a#8#0#0: Box, a#8#1#0: DatatypeType, $h: Heap ::
  { $IsAlloc(#_module.List.Cons(a#8#0#0, a#8#1#0), Tclass._module.List(_module.List$T), $h) }
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.List.Cons(a#8#0#0, a#8#1#0), Tclass._module.List(_module.List$T), $h)
       <==> $IsAllocBox(a#8#0#0, _module.List$T, $h)
         && $IsAlloc(a#8#1#0, Tclass._module.List(_module.List$T), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, _module.List$T: Ty, $h: Heap ::
  { $IsAllocBox(_module.List.head(d), _module.List$T, $h) }
  $IsGoodHeap($h)
       &&
      _module.List.Cons_q(d)
       && $IsAlloc(d, Tclass._module.List(_module.List$T), $h)
     ==> $IsAllocBox(_module.List.head(d), _module.List$T, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, _module.List$T: Ty, $h: Heap ::
  { $IsAlloc(_module.List.tail(d), Tclass._module.List(_module.List$T), $h) }
  $IsGoodHeap($h)
       &&
      _module.List.Cons_q(d)
       && $IsAlloc(d, Tclass._module.List(_module.List$T), $h)
     ==> $IsAlloc(_module.List.tail(d), Tclass._module.List(_module.List$T), $h));

// Constructor literal
axiom (forall a#9#0#0: Box, a#9#1#0: DatatypeType ::
  { #_module.List.Cons(Lit(a#9#0#0), Lit(a#9#1#0)) }
  #_module.List.Cons(Lit(a#9#0#0), Lit(a#9#1#0))
     == Lit(#_module.List.Cons(a#9#0#0, a#9#1#0)));

function _module.List.head(DatatypeType) : Box;

// Constructor injectivity
axiom (forall a#10#0#0: Box, a#10#1#0: DatatypeType ::
  { #_module.List.Cons(a#10#0#0, a#10#1#0) }
  _module.List.head(#_module.List.Cons(a#10#0#0, a#10#1#0)) == a#10#0#0);

// Inductive rank
axiom (forall a#11#0#0: Box, a#11#1#0: DatatypeType ::
  { #_module.List.Cons(a#11#0#0, a#11#1#0) }
  BoxRank(a#11#0#0) < DtRank(#_module.List.Cons(a#11#0#0, a#11#1#0)));

function _module.List.tail(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#12#0#0: Box, a#12#1#0: DatatypeType ::
  { #_module.List.Cons(a#12#0#0, a#12#1#0) }
  _module.List.tail(#_module.List.Cons(a#12#0#0, a#12#1#0)) == a#12#1#0);

// Inductive rank
axiom (forall a#13#0#0: Box, a#13#1#0: DatatypeType ::
  { #_module.List.Cons(a#13#0#0, a#13#1#0) }
  DtRank(a#13#1#0) < DtRank(#_module.List.Cons(a#13#0#0, a#13#1#0)));

// One-depth case-split function
function $IsA#_module.List(DatatypeType) : bool;

// One-depth case-split axiom
axiom (forall d: DatatypeType ::
  { $IsA#_module.List(d) }
  $IsA#_module.List(d) ==> _module.List.Nil_q(d) || _module.List.Cons_q(d));

// Questionmark data type disjunctivity
axiom (forall _module.List$T: Ty, d: DatatypeType ::
  { _module.List.Cons_q(d), $Is(d, Tclass._module.List(_module.List$T)) }
    { _module.List.Nil_q(d), $Is(d, Tclass._module.List(_module.List$T)) }
  $Is(d, Tclass._module.List(_module.List$T))
     ==> _module.List.Nil_q(d) || _module.List.Cons_q(d));

const unique class._module.__default: ClassName;

function Tclass._module.__default() : Ty;

// Tclass._module.__default Tag
axiom Tag(Tclass._module.__default()) == Tagclass._module.__default;

const unique Tagclass._module.__default: TyTag;

// Box/unbox axiom for Tclass._module.__default
axiom (forall bx: Box ::
  { $IsBox(bx, Tclass._module.__default()) }
  $IsBox(bx, Tclass._module.__default())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.__default()));

// _default: Class $Is
axiom (forall $o: ref ::
  { $Is($o, Tclass._module.__default()) }
  $Is($o, Tclass._module.__default())
     <==> $o == null || dtype($o) == Tclass._module.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap ::
  { $IsAlloc($o, Tclass._module.__default(), $h) }
  $IsAlloc($o, Tclass._module.__default(), $h)
     <==> $o == null || read($h, $o, alloc));

// function declaration for _module._default.domain
function _module.__default.domain(_module._default.domain$T: Ty, _module._default.domain$U: Ty, m#0: Map Box Box)
   : Set Box;

function _module.__default.domain#canCall(_module._default.domain$T: Ty, _module._default.domain$U: Ty, m#0: Map Box Box)
   : bool;

// consequence axiom for _module.__default.domain
axiom 9 <= $FunctionContextHeight
   ==> (forall _module._default.domain$T: Ty, _module._default.domain$U: Ty, m#0: Map Box Box ::
    { _module.__default.domain(_module._default.domain$T, _module._default.domain$U, m#0) }
    _module.__default.domain#canCall(_module._default.domain$T, _module._default.domain$U, m#0)
         || (9 != $FunctionContextHeight
           && $Is(m#0, TMap(_module._default.domain$T, _module._default.domain$U)))
       ==> $Is(_module.__default.domain(_module._default.domain$T, _module._default.domain$U, m#0),
        TSet(_module._default.domain$T)));

function _module.__default.domain#requires(Ty, Ty, Map Box Box) : bool;

// #requires axiom for _module.__default.domain
axiom (forall _module._default.domain$T: Ty, _module._default.domain$U: Ty, m#0: Map Box Box ::
  { _module.__default.domain#requires(_module._default.domain$T, _module._default.domain$U, m#0) }
  $Is(m#0, TMap(_module._default.domain$T, _module._default.domain$U))
     ==> _module.__default.domain#requires(_module._default.domain$T, _module._default.domain$U, m#0)
       == true);

// definition axiom for _module.__default.domain(revealed)
axiom 9 <= $FunctionContextHeight
   ==> (forall _module._default.domain$T: Ty, _module._default.domain$U: Ty, m#0: Map Box Box ::
    { _module.__default.domain(_module._default.domain$T, _module._default.domain$U, m#0) }
    _module.__default.domain#canCall(_module._default.domain$T, _module._default.domain$U, m#0)
         || (9 != $FunctionContextHeight
           && $Is(m#0, TMap(_module._default.domain$T, _module._default.domain$U)))
       ==> (forall t#0: Box :: { Map#Domain(m#0)[t#0] } true)
         && _module.__default.domain(_module._default.domain$T, _module._default.domain$U, m#0)
           == (lambda $y#0: Box ::
            $IsBox($y#0, _module._default.domain$T) && Map#Domain(m#0)[$y#0]));

// definition axiom for _module.__default.domain for all literals(revealed)
axiom 9 <= $FunctionContextHeight
   ==> (forall _module._default.domain$T: Ty, _module._default.domain$U: Ty, m#0: Map Box Box ::
    {:weight 3} { _module.__default.domain(_module._default.domain$T, _module._default.domain$U, Lit(m#0)) }
    _module.__default.domain#canCall(_module._default.domain$T, _module._default.domain$U, Lit(m#0))
         || (9 != $FunctionContextHeight
           && $Is(m#0, TMap(_module._default.domain$T, _module._default.domain$U)))
       ==> (forall t#1: Box :: { Map#Domain(m#0)[t#1] } true)
         && _module.__default.domain(_module._default.domain$T, _module._default.domain$U, Lit(m#0))
           == (lambda $y#1: Box ::
            $IsBox($y#1, _module._default.domain$T) && Map#Domain(m#0)[$y#1]));

procedure CheckWellformed$$_module.__default.domain(_module._default.domain$T: Ty,
    _module._default.domain$U: Ty,
    m#0: Map Box Box
       where $Is(m#0, TMap(_module._default.domain$T, _module._default.domain$U)));
  free requires 9 == $FunctionContextHeight;
  modifies $Heap, $Tick;



// function declaration for _module._default.length
function _module.__default.length(_module._default.length$_T0: Ty, $ly: LayerType, list#0: DatatypeType) : int;

function _module.__default.length#canCall(_module._default.length$_T0: Ty, list#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall _module._default.length$_T0: Ty, $ly: LayerType, list#0: DatatypeType ::
  { _module.__default.length(_module._default.length$_T0, $LS($ly), list#0) }
  _module.__default.length(_module._default.length$_T0, $LS($ly), list#0)
     == _module.__default.length(_module._default.length$_T0, $ly, list#0));

// fuel synonym axiom
axiom (forall _module._default.length$_T0: Ty, $ly: LayerType, list#0: DatatypeType ::
  { _module.__default.length(_module._default.length$_T0, AsFuelBottom($ly), list#0) }
  _module.__default.length(_module._default.length$_T0, $ly, list#0)
     == _module.__default.length(_module._default.length$_T0, $LZ, list#0));

// consequence axiom for _module.__default.length
axiom 6 <= $FunctionContextHeight
   ==> (forall _module._default.length$_T0: Ty, $ly: LayerType, list#0: DatatypeType ::
    { _module.__default.length(_module._default.length$_T0, $ly, list#0) }
    _module.__default.length#canCall(_module._default.length$_T0, list#0)
         || (6 != $FunctionContextHeight
           && $Is(list#0, Tclass._module.List(_module._default.length$_T0)))
       ==> LitInt(0) <= _module.__default.length(_module._default.length$_T0, $ly, list#0));

function _module.__default.length#requires(Ty, LayerType, DatatypeType) : bool;

// #requires axiom for _module.__default.length
axiom (forall _module._default.length$_T0: Ty, $ly: LayerType, list#0: DatatypeType ::
  { _module.__default.length#requires(_module._default.length$_T0, $ly, list#0) }
  $Is(list#0, Tclass._module.List(_module._default.length$_T0))
     ==> _module.__default.length#requires(_module._default.length$_T0, $ly, list#0)
       == true);

// definition axiom for _module.__default.length(revealed)
axiom 6 <= $FunctionContextHeight
   ==> (forall _module._default.length$_T0: Ty, $ly: LayerType, list#0: DatatypeType ::
    { _module.__default.length(_module._default.length$_T0, $LS($ly), list#0) }
    _module.__default.length#canCall(_module._default.length$_T0, list#0)
         || (6 != $FunctionContextHeight
           && $Is(list#0, Tclass._module.List(_module._default.length$_T0)))
       ==> (!_module.List.Nil_q(list#0)
           ==> _module.__default.length#canCall(_module._default.length$_T0, _module.List.tail(list#0)))
         && _module.__default.length(_module._default.length$_T0, $LS($ly), list#0)
           == (if _module.List.Nil_q(list#0)
             then 0
             else 1
               + _module.__default.length(_module._default.length$_T0, $ly, _module.List.tail(list#0))));

// definition axiom for _module.__default.length for all literals(revealed)
axiom 6 <= $FunctionContextHeight
   ==> (forall _module._default.length$_T0: Ty, $ly: LayerType, list#0: DatatypeType ::
    {:weight 3} { _module.__default.length(_module._default.length$_T0, $LS($ly), Lit(list#0)) }
    _module.__default.length#canCall(_module._default.length$_T0, Lit(list#0))
         || (6 != $FunctionContextHeight
           && $Is(list#0, Tclass._module.List(_module._default.length$_T0)))
       ==> (!Lit(_module.List.Nil_q(Lit(list#0)))
           ==> _module.__default.length#canCall(_module._default.length$_T0, Lit(_module.List.tail(Lit(list#0)))))
         && _module.__default.length(_module._default.length$_T0, $LS($ly), Lit(list#0))
           == (if _module.List.Nil_q(Lit(list#0))
             then 0
             else 1
               + _module.__default.length(_module._default.length$_T0, $LS($ly), Lit(_module.List.tail(Lit(list#0))))));

procedure CheckWellformed$$_module.__default.length(_module._default.length$_T0: Ty,
    list#0: DatatypeType
       where $Is(list#0, Tclass._module.List(_module._default.length$_T0)));
  free requires 6 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.length(_module._default.length$_T0: Ty, list#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _v0#0: Box;
  var tail#0: DatatypeType;
  var ##list#0: DatatypeType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function length
    assume {:captureState "BreadthFirstSearch.dfy(242,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume LitInt(0)
           <= _module.__default.length(_module._default.length$_T0, $LS($LZ), list#0);
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
          $o != null && read($Heap, $o, alloc) ==> false);
        if (list#0 == #_module.List.Nil())
        {
            assert $Is(LitInt(0), Tclass._System.nat());
            assume _module.__default.length(_module._default.length$_T0, $LS($LZ), list#0)
               == LitInt(0);
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.length(_module._default.length$_T0, $LS($LZ), list#0),
              Tclass._System.nat());
        }
        else if (list#0 == #_module.List.Cons(_v0#0, tail#0))
        {
            assume $IsBox(_v0#0, _module._default.length$_T0);
            assume $Is(tail#0, Tclass._module.List(_module._default.length$_T0));
            ##list#0 := tail#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##list#0, Tclass._module.List(_module._default.length$_T0), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert DtRank(##list#0) < DtRank(list#0);
            assume _module.__default.length#canCall(_module._default.length$_T0, tail#0);
            assert $Is(1 + _module.__default.length(_module._default.length$_T0, $LS($LZ), tail#0),
              Tclass._System.nat());
            assume _module.__default.length(_module._default.length$_T0, $LS($LZ), list#0)
               == 1 + _module.__default.length(_module._default.length$_T0, $LS($LZ), tail#0);
            assume _module.__default.length#canCall(_module._default.length$_T0, tail#0);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.length(_module._default.length$_T0, $LS($LZ), list#0),
              Tclass._System.nat());
        }
        else
        {
            assume false;
        }

        assert b$reqreads#0;
    }
}



// function declaration for _module._default.elements
function _module.__default.elements(_module._default.elements$T: Ty, $ly: LayerType, list#0: DatatypeType) : Set Box;

function _module.__default.elements#canCall(_module._default.elements$T: Ty, list#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall _module._default.elements$T: Ty, $ly: LayerType, list#0: DatatypeType ::
  { _module.__default.elements(_module._default.elements$T, $LS($ly), list#0) }
  _module.__default.elements(_module._default.elements$T, $LS($ly), list#0)
     == _module.__default.elements(_module._default.elements$T, $ly, list#0));

// fuel synonym axiom
axiom (forall _module._default.elements$T: Ty, $ly: LayerType, list#0: DatatypeType ::
  { _module.__default.elements(_module._default.elements$T, AsFuelBottom($ly), list#0) }
  _module.__default.elements(_module._default.elements$T, $ly, list#0)
     == _module.__default.elements(_module._default.elements$T, $LZ, list#0));

// consequence axiom for _module.__default.elements
axiom 12 <= $FunctionContextHeight
   ==> (forall _module._default.elements$T: Ty, $ly: LayerType, list#0: DatatypeType ::
    { _module.__default.elements(_module._default.elements$T, $ly, list#0) }
    _module.__default.elements#canCall(_module._default.elements$T, list#0)
         || (12 != $FunctionContextHeight
           && $Is(list#0, Tclass._module.List(_module._default.elements$T)))
       ==> $Is(_module.__default.elements(_module._default.elements$T, $ly, list#0),
        TSet(_module._default.elements$T)));

function _module.__default.elements#requires(Ty, LayerType, DatatypeType) : bool;

// #requires axiom for _module.__default.elements
axiom (forall _module._default.elements$T: Ty, $ly: LayerType, list#0: DatatypeType ::
  { _module.__default.elements#requires(_module._default.elements$T, $ly, list#0) }
  $Is(list#0, Tclass._module.List(_module._default.elements$T))
     ==> _module.__default.elements#requires(_module._default.elements$T, $ly, list#0)
       == true);

// definition axiom for _module.__default.elements(revealed)
axiom 12 <= $FunctionContextHeight
   ==> (forall _module._default.elements$T: Ty, $ly: LayerType, list#0: DatatypeType ::
    { _module.__default.elements(_module._default.elements$T, $LS($ly), list#0) }
    _module.__default.elements#canCall(_module._default.elements$T, list#0)
         || (12 != $FunctionContextHeight
           && $Is(list#0, Tclass._module.List(_module._default.elements$T)))
       ==> (!_module.List.Nil_q(list#0)
           ==> _module.__default.elements#canCall(_module._default.elements$T, _module.List.tail(list#0)))
         && _module.__default.elements(_module._default.elements$T, $LS($ly), list#0)
           == (if _module.List.Nil_q(list#0)
             then Set#Empty(): Set Box
             else Set#Union(Set#UnionOne(Set#Empty(): Set Box, _module.List.head(list#0)),
              _module.__default.elements(_module._default.elements$T, $ly, _module.List.tail(list#0)))));

// definition axiom for _module.__default.elements for all literals(revealed)
axiom 12 <= $FunctionContextHeight
   ==> (forall _module._default.elements$T: Ty, $ly: LayerType, list#0: DatatypeType ::
    {:weight 3} { _module.__default.elements(_module._default.elements$T, $LS($ly), Lit(list#0)) }
    _module.__default.elements#canCall(_module._default.elements$T, Lit(list#0))
         || (12 != $FunctionContextHeight
           && $Is(list#0, Tclass._module.List(_module._default.elements$T)))
       ==> (!Lit(_module.List.Nil_q(Lit(list#0)))
           ==> _module.__default.elements#canCall(_module._default.elements$T, Lit(_module.List.tail(Lit(list#0)))))
         && _module.__default.elements(_module._default.elements$T, $LS($ly), Lit(list#0))
           == (if _module.List.Nil_q(Lit(list#0))
             then Set#Empty(): Set Box
             else Set#Union(Set#UnionOne(Set#Empty(): Set Box, Lit(_module.List.head(Lit(list#0)))),
              _module.__default.elements(_module._default.elements$T, $LS($ly), Lit(_module.List.tail(Lit(list#0)))))));

procedure CheckWellformed$$_module.__default.elements(_module._default.elements$T: Ty,
    list#0: DatatypeType
       where $Is(list#0, Tclass._module.List(_module._default.elements$T)));
  free requires 12 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.elements(_module._default.elements$T: Ty, list#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var x#0: Box;
  var tail#0: DatatypeType;
  var ##list#0: DatatypeType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function elements
    assume {:captureState "BreadthFirstSearch.dfy(249,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.elements(_module._default.elements$T, $LS($LZ), list#0),
          TSet(_module._default.elements$T));
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
          $o != null && read($Heap, $o, alloc) ==> false);
        if (list#0 == #_module.List.Nil())
        {
            assume _module.__default.elements(_module._default.elements$T, $LS($LZ), list#0)
               == Lit(Set#Empty(): Set Box);
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.elements(_module._default.elements$T, $LS($LZ), list#0),
              TSet(_module._default.elements$T));
        }
        else if (list#0 == #_module.List.Cons(x#0, tail#0))
        {
            assume $IsBox(x#0, _module._default.elements$T);
            assume $Is(tail#0, Tclass._module.List(_module._default.elements$T));
            ##list#0 := tail#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##list#0, Tclass._module.List(_module._default.elements$T), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert DtRank(##list#0) < DtRank(list#0);
            assume _module.__default.elements#canCall(_module._default.elements$T, tail#0);
            assume _module.__default.elements(_module._default.elements$T, $LS($LZ), list#0)
               == Set#Union(Set#UnionOne(Set#Empty(): Set Box, x#0),
                _module.__default.elements(_module._default.elements$T, $LS($LZ), tail#0));
            assume _module.__default.elements#canCall(_module._default.elements$T, tail#0);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.elements(_module._default.elements$T, $LS($LZ), list#0),
              TSet(_module._default.elements$T));
        }
        else
        {
            assume false;
        }

        assert b$reqreads#0;
    }
}

