// Dafny 2.0.0.00922 technical preview 0
// Command Line Options: /compile:0 /noVerify /print:Problem5-DoubleEndedQueue.bpl Problem5-DoubleEndedQueue.dfy

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

const unique class._module.AmortizedQueue: ClassName;

function Tclass._module.AmortizedQueue(Ty) : Ty;

// Tclass._module.AmortizedQueue Tag
axiom (forall _module.AmortizedQueue$T: Ty ::
  { Tclass._module.AmortizedQueue(_module.AmortizedQueue$T) }
  Tag(Tclass._module.AmortizedQueue(_module.AmortizedQueue$T))
     == Tagclass._module.AmortizedQueue);

const unique Tagclass._module.AmortizedQueue: TyTag;

// Tclass._module.AmortizedQueue injectivity 0
axiom (forall _module.AmortizedQueue$T: Ty ::
  { Tclass._module.AmortizedQueue(_module.AmortizedQueue$T) }
  Tclass._module.AmortizedQueue_0(Tclass._module.AmortizedQueue(_module.AmortizedQueue$T))
     == _module.AmortizedQueue$T);

function Tclass._module.AmortizedQueue_0(Ty) : Ty;

// Box/unbox axiom for Tclass._module.AmortizedQueue
axiom (forall _module.AmortizedQueue$T: Ty, bx: Box ::
  { $IsBox(bx, Tclass._module.AmortizedQueue(_module.AmortizedQueue$T)) }
  $IsBox(bx, Tclass._module.AmortizedQueue(_module.AmortizedQueue$T))
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.AmortizedQueue(_module.AmortizedQueue$T)));

// AmortizedQueue: Class $Is
axiom (forall _module.AmortizedQueue$T: Ty, $o: ref ::
  { $Is($o, Tclass._module.AmortizedQueue(_module.AmortizedQueue$T)) }
  $Is($o, Tclass._module.AmortizedQueue(_module.AmortizedQueue$T))
     <==> $o == null
       || dtype($o) == Tclass._module.AmortizedQueue(_module.AmortizedQueue$T));

// AmortizedQueue: Class $IsAlloc
axiom (forall _module.AmortizedQueue$T: Ty, $o: ref, $h: Heap ::
  { $IsAlloc($o, Tclass._module.AmortizedQueue(_module.AmortizedQueue$T), $h) }
  $IsAlloc($o, Tclass._module.AmortizedQueue(_module.AmortizedQueue$T), $h)
     <==> $o == null || read($h, $o, alloc));

axiom FDim(_module.AmortizedQueue.front) == 0
   && FieldOfDecl(class._module.AmortizedQueue, field$front)
     == _module.AmortizedQueue.front
   && !$IsGhostField(_module.AmortizedQueue.front);

const _module.AmortizedQueue.front: Field ref;

function Tclass._module.LinkedList(Ty) : Ty;

// Tclass._module.LinkedList Tag
axiom (forall _module.LinkedList$T: Ty ::
  { Tclass._module.LinkedList(_module.LinkedList$T) }
  Tag(Tclass._module.LinkedList(_module.LinkedList$T))
     == Tagclass._module.LinkedList);

const unique Tagclass._module.LinkedList: TyTag;

// Tclass._module.LinkedList injectivity 0
axiom (forall _module.LinkedList$T: Ty ::
  { Tclass._module.LinkedList(_module.LinkedList$T) }
  Tclass._module.LinkedList_0(Tclass._module.LinkedList(_module.LinkedList$T))
     == _module.LinkedList$T);

function Tclass._module.LinkedList_0(Ty) : Ty;

// Box/unbox axiom for Tclass._module.LinkedList
axiom (forall _module.LinkedList$T: Ty, bx: Box ::
  { $IsBox(bx, Tclass._module.LinkedList(_module.LinkedList$T)) }
  $IsBox(bx, Tclass._module.LinkedList(_module.LinkedList$T))
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.LinkedList(_module.LinkedList$T)));

// AmortizedQueue.front: Allocation axiom
axiom (forall _module.AmortizedQueue$T: Ty, $h: Heap, $o: ref ::
  { read($h, $o, _module.AmortizedQueue.front), Tclass._module.AmortizedQueue(_module.AmortizedQueue$T) }
  $IsGoodHeap($h)
       && $o != null
       && dtype($o) == Tclass._module.AmortizedQueue(_module.AmortizedQueue$T)
     ==> $Is(read($h, $o, _module.AmortizedQueue.front),
        Tclass._module.LinkedList(_module.AmortizedQueue$T))
       && (read($h, $o, alloc)
         ==> $IsAlloc(read($h, $o, _module.AmortizedQueue.front),
          Tclass._module.LinkedList(_module.AmortizedQueue$T),
          $h)));

axiom FDim(_module.AmortizedQueue.rear) == 0
   && FieldOfDecl(class._module.AmortizedQueue, field$rear)
     == _module.AmortizedQueue.rear
   && !$IsGhostField(_module.AmortizedQueue.rear);

const _module.AmortizedQueue.rear: Field ref;

// AmortizedQueue.rear: Allocation axiom
axiom (forall _module.AmortizedQueue$T: Ty, $h: Heap, $o: ref ::
  { read($h, $o, _module.AmortizedQueue.rear), Tclass._module.AmortizedQueue(_module.AmortizedQueue$T) }
  $IsGoodHeap($h)
       && $o != null
       && dtype($o) == Tclass._module.AmortizedQueue(_module.AmortizedQueue$T)
     ==> $Is(read($h, $o, _module.AmortizedQueue.rear),
        Tclass._module.LinkedList(_module.AmortizedQueue$T))
       && (read($h, $o, alloc)
         ==> $IsAlloc(read($h, $o, _module.AmortizedQueue.rear),
          Tclass._module.LinkedList(_module.AmortizedQueue$T),
          $h)));

axiom FDim(_module.AmortizedQueue.Repr) == 0
   && FieldOfDecl(class._module.AmortizedQueue, field$Repr)
     == _module.AmortizedQueue.Repr
   && $IsGhostField(_module.AmortizedQueue.Repr);

const _module.AmortizedQueue.Repr: Field (Set Box);

// AmortizedQueue.Repr: Allocation axiom
axiom (forall _module.AmortizedQueue$T: Ty, $h: Heap, $o: ref ::
  { read($h, $o, _module.AmortizedQueue.Repr), Tclass._module.AmortizedQueue(_module.AmortizedQueue$T) }
  $IsGoodHeap($h)
       && $o != null
       && dtype($o) == Tclass._module.AmortizedQueue(_module.AmortizedQueue$T)
     ==> $Is(read($h, $o, _module.AmortizedQueue.Repr), TSet(Tclass._System.object()))
       && (read($h, $o, alloc)
         ==> $IsAlloc(read($h, $o, _module.AmortizedQueue.Repr), TSet(Tclass._System.object()), $h)));

axiom FDim(_module.AmortizedQueue.List) == 0
   && FieldOfDecl(class._module.AmortizedQueue, field$List)
     == _module.AmortizedQueue.List
   && $IsGhostField(_module.AmortizedQueue.List);

const _module.AmortizedQueue.List: Field (Seq Box);

// AmortizedQueue.List: Allocation axiom
axiom (forall _module.AmortizedQueue$T: Ty, $h: Heap, $o: ref ::
  { read($h, $o, _module.AmortizedQueue.List), Tclass._module.AmortizedQueue(_module.AmortizedQueue$T) }
  $IsGoodHeap($h)
       && $o != null
       && dtype($o) == Tclass._module.AmortizedQueue(_module.AmortizedQueue$T)
     ==> $Is(read($h, $o, _module.AmortizedQueue.List), TSeq(_module.AmortizedQueue$T))
       && (read($h, $o, alloc)
         ==> $IsAlloc(read($h, $o, _module.AmortizedQueue.List), TSeq(_module.AmortizedQueue$T), $h)));

// function declaration for _module.AmortizedQueue.Valid
function _module.AmortizedQueue.Valid(_module.AmortizedQueue$T: Ty, $heap: Heap, this: ref) : bool;

function _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T: Ty, $heap: Heap, this: ref) : bool;

// frame axiom for _module.AmortizedQueue.Valid
axiom (forall _module.AmortizedQueue$T: Ty, $h0: Heap, $h1: Heap, this: ref ::
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $h1, this) }
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       &&
      this != null
       && $Is(this, Tclass._module.AmortizedQueue(_module.AmortizedQueue$T))
       &&
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==>
    (forall<alpha> $o: ref, $f: Field alpha ::
      $o != null
           && ($o == this || read($h0, this, _module.AmortizedQueue.Repr)[$Box($o)])
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $h0, this)
       == _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $h1, this));

// consequence axiom for _module.AmortizedQueue.Valid
axiom 2 <= $FunctionContextHeight
   ==> (forall _module.AmortizedQueue$T: Ty, $Heap: Heap, this: ref ::
    { _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this) }
    _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
         || (2 != $FunctionContextHeight
           &&
          $IsGoodHeap($Heap)
           &&
          this != null
           &&
          $Is(this, Tclass._module.AmortizedQueue(_module.AmortizedQueue$T))
           && $IsAlloc(this, Tclass._module.AmortizedQueue(_module.AmortizedQueue$T), $Heap))
       ==> true);

function _module.AmortizedQueue.Valid#requires(Ty, Heap, ref) : bool;

// #requires axiom for _module.AmortizedQueue.Valid
axiom (forall _module.AmortizedQueue$T: Ty, $Heap: Heap, this: ref ::
  { _module.AmortizedQueue.Valid#requires(_module.AmortizedQueue$T, $Heap, this) }
  $IsGoodHeap($Heap)
       &&
      this != null
       &&
      $Is(this, Tclass._module.AmortizedQueue(_module.AmortizedQueue$T))
       && $IsAlloc(this, Tclass._module.AmortizedQueue(_module.AmortizedQueue$T), $Heap)
     ==> _module.AmortizedQueue.Valid#requires(_module.AmortizedQueue$T, $Heap, this)
       == true);

axiom FDim(_module.LinkedList.Repr) == 0
   && FieldOfDecl(class._module.LinkedList, field$Repr) == _module.LinkedList.Repr
   && $IsGhostField(_module.LinkedList.Repr);

axiom FDim(_module.LinkedList.List) == 0
   && FieldOfDecl(class._module.LinkedList, field$List) == _module.LinkedList.List
   && $IsGhostField(_module.LinkedList.List);

// definition axiom for _module.AmortizedQueue.Valid(revealed)
axiom 2 <= $FunctionContextHeight
   ==> (forall _module.AmortizedQueue$T: Ty, $Heap: Heap, this: ref ::
    { _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this) }
    _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
         || (2 != $FunctionContextHeight
           &&
          $IsGoodHeap($Heap)
           &&
          this != null
           &&
          $Is(this, Tclass._module.AmortizedQueue(_module.AmortizedQueue$T))
           && $IsAlloc(this, Tclass._module.AmortizedQueue(_module.AmortizedQueue$T), $Heap))
       ==> (Set#Subset(read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.Repr),
            read($Heap, this, _module.AmortizedQueue.Repr))
           ==> _module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.front)))
         && (Set#Subset(read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.Repr),
            read($Heap, this, _module.AmortizedQueue.Repr))
           ==> _module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.rear)))
         && (Seq#Length(read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.List))
             <= Seq#Length(read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.List))
           ==> _module.LinkedList.ReverseSeq#canCall(_module.AmortizedQueue$T,
            read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.List)))
         && _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
           == (
            read($Heap, this, _module.AmortizedQueue.Repr)[$Box(this)]
             && read($Heap, this, _module.AmortizedQueue.front) != null
             && read($Heap, this, _module.AmortizedQueue.Repr)[$Box(read($Heap, this, _module.AmortizedQueue.front))]
             && Set#Subset(read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.Repr),
              read($Heap, this, _module.AmortizedQueue.Repr))
             && _module.LinkedList.Valid(_module.AmortizedQueue$T,
              $LS($LZ),
              $Heap,
              read($Heap, this, _module.AmortizedQueue.front))
             && read($Heap, this, _module.AmortizedQueue.rear) != null
             && read($Heap, this, _module.AmortizedQueue.Repr)[$Box(read($Heap, this, _module.AmortizedQueue.rear))]
             && Set#Subset(read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.Repr),
              read($Heap, this, _module.AmortizedQueue.Repr))
             && _module.LinkedList.Valid(_module.AmortizedQueue$T,
              $LS($LZ),
              $Heap,
              read($Heap, this, _module.AmortizedQueue.rear))
             && Seq#Length(read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.List))
               <= Seq#Length(read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.List))
             && Seq#Equal(read($Heap, this, _module.AmortizedQueue.List),
              Seq#Append(read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.List),
                _module.LinkedList.ReverseSeq(_module.AmortizedQueue$T,
                  $LS($LZ),
                  read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.List))))));

procedure CheckWellformed$$_module.AmortizedQueue.Valid(_module.AmortizedQueue$T: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.AmortizedQueue(_module.AmortizedQueue$T))
         && $IsAlloc(this, Tclass._module.AmortizedQueue(_module.AmortizedQueue$T), $Heap));
  free requires 2 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.AmortizedQueue.Valid(_module.AmortizedQueue$T: Ty, this: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;
  var ##s#0: Seq Box;
  var b$reqreads#1: bool;
  var b$reqreads#2: bool;
  var b$reqreads#3: bool;
  var b$reqreads#4: bool;
  var b$reqreads#5: bool;
  var b$reqreads#6: bool;
  var b$reqreads#7: bool;
  var b$reqreads#8: bool;
  var b$reqreads#9: bool;
  var b$reqreads#10: bool;
  var b$reqreads#11: bool;
  var b$reqreads#12: bool;
  var b$reqreads#13: bool;
  var b$reqreads#14: bool;
  var b$reqreads#15: bool;
  var b$reqreads#16: bool;
  var b$reqreads#17: bool;
  var b$reqreads#18: bool;
  var b$reqreads#19: bool;
  var b$reqreads#20: bool;
  var b$reqreads#21: bool;
  var b$reqreads#22: bool;
  var b$reqreads#23: bool;
  var b$reqreads#24: bool;
  var b$reqreads#25: bool;
  var b$reqreads#26: bool;
  var b$reqreads#27: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;
    b$reqreads#2 := true;
    b$reqreads#3 := true;
    b$reqreads#4 := true;
    b$reqreads#5 := true;
    b$reqreads#6 := true;
    b$reqreads#7 := true;
    b$reqreads#8 := true;
    b$reqreads#9 := true;
    b$reqreads#10 := true;
    b$reqreads#11 := true;
    b$reqreads#12 := true;
    b$reqreads#13 := true;
    b$reqreads#14 := true;
    b$reqreads#15 := true;
    b$reqreads#16 := true;
    b$reqreads#17 := true;
    b$reqreads#18 := true;
    b$reqreads#19 := true;
    b$reqreads#20 := true;
    b$reqreads#21 := true;
    b$reqreads#22 := true;
    b$reqreads#23 := true;
    b$reqreads#24 := true;
    b$reqreads#25 := true;
    b$reqreads#26 := true;
    b$reqreads#27 := true;

    // AddWellformednessCheck for function Valid
    assume {:captureState "Problem5-DoubleEndedQueue.dfy(22,12): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc)
         ==> $o == this || read($Heap, this, _module.AmortizedQueue.Repr)[$Box($o)]);
    b$reqreads#0 := $_Frame[this, _module.AmortizedQueue.Repr];
    assert b$reqreads#0;
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
          $o != null && read($Heap, $o, alloc)
             ==> $o == this || read($Heap, this, _module.AmortizedQueue.Repr)[$Box($o)]);
        b$reqreads#1 := $_Frame[this, _module.AmortizedQueue.Repr];
        if (read($Heap, this, _module.AmortizedQueue.Repr)[$Box(this)])
        {
            b$reqreads#2 := $_Frame[this, _module.AmortizedQueue.front];
        }

        if (read($Heap, this, _module.AmortizedQueue.Repr)[$Box(this)]
           && read($Heap, this, _module.AmortizedQueue.front) != null)
        {
            b$reqreads#3 := $_Frame[this, _module.AmortizedQueue.front];
            b$reqreads#4 := $_Frame[this, _module.AmortizedQueue.Repr];
        }

        if (read($Heap, this, _module.AmortizedQueue.Repr)[$Box(this)]
           && read($Heap, this, _module.AmortizedQueue.front) != null
           && read($Heap, this, _module.AmortizedQueue.Repr)[$Box(read($Heap, this, _module.AmortizedQueue.front))])
        {
            b$reqreads#5 := $_Frame[this, _module.AmortizedQueue.front];
            assert read($Heap, this, _module.AmortizedQueue.front) != null;
            b$reqreads#6 := $_Frame[read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.Repr];
            b$reqreads#7 := $_Frame[this, _module.AmortizedQueue.Repr];
        }

        if (read($Heap, this, _module.AmortizedQueue.Repr)[$Box(this)]
           && read($Heap, this, _module.AmortizedQueue.front) != null
           && read($Heap, this, _module.AmortizedQueue.Repr)[$Box(read($Heap, this, _module.AmortizedQueue.front))]
           && Set#Subset(read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.Repr),
            read($Heap, this, _module.AmortizedQueue.Repr)))
        {
            b$reqreads#8 := $_Frame[this, _module.AmortizedQueue.front];
            assert read($Heap, this, _module.AmortizedQueue.front) != null;
            b$reqreads#9 := (forall<alpha> $o: ref, $f: Field alpha ::
              $o != null
                   && read($Heap, $o, alloc)
                   && ($o == read($Heap, this, _module.AmortizedQueue.front)
                     || read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.Repr)[$Box($o)])
                 ==> $_Frame[$o, $f]);
            assume _module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.front));
        }

        if (read($Heap, this, _module.AmortizedQueue.Repr)[$Box(this)]
           && read($Heap, this, _module.AmortizedQueue.front) != null
           && read($Heap, this, _module.AmortizedQueue.Repr)[$Box(read($Heap, this, _module.AmortizedQueue.front))]
           && Set#Subset(read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.Repr),
            read($Heap, this, _module.AmortizedQueue.Repr))
           && _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.front)))
        {
            b$reqreads#10 := $_Frame[this, _module.AmortizedQueue.rear];
        }

        if (read($Heap, this, _module.AmortizedQueue.Repr)[$Box(this)]
           && read($Heap, this, _module.AmortizedQueue.front) != null
           && read($Heap, this, _module.AmortizedQueue.Repr)[$Box(read($Heap, this, _module.AmortizedQueue.front))]
           && Set#Subset(read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.Repr),
            read($Heap, this, _module.AmortizedQueue.Repr))
           && _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.front))
           && read($Heap, this, _module.AmortizedQueue.rear) != null)
        {
            b$reqreads#11 := $_Frame[this, _module.AmortizedQueue.rear];
            b$reqreads#12 := $_Frame[this, _module.AmortizedQueue.Repr];
        }

        if (read($Heap, this, _module.AmortizedQueue.Repr)[$Box(this)]
           && read($Heap, this, _module.AmortizedQueue.front) != null
           && read($Heap, this, _module.AmortizedQueue.Repr)[$Box(read($Heap, this, _module.AmortizedQueue.front))]
           && Set#Subset(read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.Repr),
            read($Heap, this, _module.AmortizedQueue.Repr))
           && _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.front))
           && read($Heap, this, _module.AmortizedQueue.rear) != null
           && read($Heap, this, _module.AmortizedQueue.Repr)[$Box(read($Heap, this, _module.AmortizedQueue.rear))])
        {
            b$reqreads#13 := $_Frame[this, _module.AmortizedQueue.rear];
            assert read($Heap, this, _module.AmortizedQueue.rear) != null;
            b$reqreads#14 := $_Frame[read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.Repr];
            b$reqreads#15 := $_Frame[this, _module.AmortizedQueue.Repr];
        }

        if (read($Heap, this, _module.AmortizedQueue.Repr)[$Box(this)]
           && read($Heap, this, _module.AmortizedQueue.front) != null
           && read($Heap, this, _module.AmortizedQueue.Repr)[$Box(read($Heap, this, _module.AmortizedQueue.front))]
           && Set#Subset(read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.Repr),
            read($Heap, this, _module.AmortizedQueue.Repr))
           && _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.front))
           && read($Heap, this, _module.AmortizedQueue.rear) != null
           && read($Heap, this, _module.AmortizedQueue.Repr)[$Box(read($Heap, this, _module.AmortizedQueue.rear))]
           && Set#Subset(read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.Repr),
            read($Heap, this, _module.AmortizedQueue.Repr)))
        {
            b$reqreads#16 := $_Frame[this, _module.AmortizedQueue.rear];
            assert read($Heap, this, _module.AmortizedQueue.rear) != null;
            b$reqreads#17 := (forall<alpha> $o: ref, $f: Field alpha ::
              $o != null
                   && read($Heap, $o, alloc)
                   && ($o == read($Heap, this, _module.AmortizedQueue.rear)
                     || read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.Repr)[$Box($o)])
                 ==> $_Frame[$o, $f]);
            assume _module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.rear));
        }

        if (read($Heap, this, _module.AmortizedQueue.Repr)[$Box(this)]
           && read($Heap, this, _module.AmortizedQueue.front) != null
           && read($Heap, this, _module.AmortizedQueue.Repr)[$Box(read($Heap, this, _module.AmortizedQueue.front))]
           && Set#Subset(read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.Repr),
            read($Heap, this, _module.AmortizedQueue.Repr))
           && _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.front))
           && read($Heap, this, _module.AmortizedQueue.rear) != null
           && read($Heap, this, _module.AmortizedQueue.Repr)[$Box(read($Heap, this, _module.AmortizedQueue.rear))]
           && Set#Subset(read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.Repr),
            read($Heap, this, _module.AmortizedQueue.Repr))
           && _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.rear)))
        {
            b$reqreads#18 := $_Frame[this, _module.AmortizedQueue.rear];
            assert read($Heap, this, _module.AmortizedQueue.rear) != null;
            b$reqreads#19 := $_Frame[read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.List];
            b$reqreads#20 := $_Frame[this, _module.AmortizedQueue.front];
            assert read($Heap, this, _module.AmortizedQueue.front) != null;
            b$reqreads#21 := $_Frame[read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.List];
        }

        if (read($Heap, this, _module.AmortizedQueue.Repr)[$Box(this)]
           && read($Heap, this, _module.AmortizedQueue.front) != null
           && read($Heap, this, _module.AmortizedQueue.Repr)[$Box(read($Heap, this, _module.AmortizedQueue.front))]
           && Set#Subset(read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.Repr),
            read($Heap, this, _module.AmortizedQueue.Repr))
           && _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.front))
           && read($Heap, this, _module.AmortizedQueue.rear) != null
           && read($Heap, this, _module.AmortizedQueue.Repr)[$Box(read($Heap, this, _module.AmortizedQueue.rear))]
           && Set#Subset(read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.Repr),
            read($Heap, this, _module.AmortizedQueue.Repr))
           && _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.rear))
           && Seq#Length(read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.List))
             <= Seq#Length(read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.List)))
        {
            b$reqreads#22 := $_Frame[this, _module.AmortizedQueue.List];
            b$reqreads#23 := $_Frame[this, _module.AmortizedQueue.front];
            assert read($Heap, this, _module.AmortizedQueue.front) != null;
            b$reqreads#24 := $_Frame[read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.List];
            b$reqreads#25 := $_Frame[this, _module.AmortizedQueue.rear];
            assert read($Heap, this, _module.AmortizedQueue.rear) != null;
            b$reqreads#26 := $_Frame[read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.List];
            ##s#0 := read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.List);
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#0, TSeq(_module.AmortizedQueue$T), $Heap);
            b$reqreads#27 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume _module.LinkedList.ReverseSeq#canCall(_module.AmortizedQueue$T,
              read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.List));
        }

        assume _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
           == (
            read($Heap, this, _module.AmortizedQueue.Repr)[$Box(this)]
             && read($Heap, this, _module.AmortizedQueue.front) != null
             && read($Heap, this, _module.AmortizedQueue.Repr)[$Box(read($Heap, this, _module.AmortizedQueue.front))]
             && Set#Subset(read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.Repr),
              read($Heap, this, _module.AmortizedQueue.Repr))
             && _module.LinkedList.Valid(_module.AmortizedQueue$T,
              $LS($LZ),
              $Heap,
              read($Heap, this, _module.AmortizedQueue.front))
             && read($Heap, this, _module.AmortizedQueue.rear) != null
             && read($Heap, this, _module.AmortizedQueue.Repr)[$Box(read($Heap, this, _module.AmortizedQueue.rear))]
             && Set#Subset(read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.Repr),
              read($Heap, this, _module.AmortizedQueue.Repr))
             && _module.LinkedList.Valid(_module.AmortizedQueue$T,
              $LS($LZ),
              $Heap,
              read($Heap, this, _module.AmortizedQueue.rear))
             && Seq#Length(read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.List))
               <= Seq#Length(read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.List))
             && Seq#Equal(read($Heap, this, _module.AmortizedQueue.List),
              Seq#Append(read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.List),
                _module.LinkedList.ReverseSeq(_module.AmortizedQueue$T,
                  $LS($LZ),
                  read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.List)))));
        assume (Set#Subset(read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.Repr),
              read($Heap, this, _module.AmortizedQueue.Repr))
             ==> _module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.front)))
           && (Set#Subset(read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.Repr),
              read($Heap, this, _module.AmortizedQueue.Repr))
             ==> _module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.rear)))
           && (Seq#Length(read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.List))
               <= Seq#Length(read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.List))
             ==> _module.LinkedList.ReverseSeq#canCall(_module.AmortizedQueue$T,
              read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.List)));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this), TBool);
        assert b$reqreads#1;
        assert b$reqreads#2;
        assert b$reqreads#3;
        assert b$reqreads#4;
        assert b$reqreads#5;
        assert b$reqreads#6;
        assert b$reqreads#7;
        assert b$reqreads#8;
        assert b$reqreads#9;
        assert b$reqreads#10;
        assert b$reqreads#11;
        assert b$reqreads#12;
        assert b$reqreads#13;
        assert b$reqreads#14;
        assert b$reqreads#15;
        assert b$reqreads#16;
        assert b$reqreads#17;
        assert b$reqreads#18;
        assert b$reqreads#19;
        assert b$reqreads#20;
        assert b$reqreads#21;
        assert b$reqreads#22;
        assert b$reqreads#23;
        assert b$reqreads#24;
        assert b$reqreads#25;
        assert b$reqreads#26;
        assert b$reqreads#27;
    }
}



procedure CheckWellformed$$_module.AmortizedQueue.Init(_module.AmortizedQueue$T: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.AmortizedQueue(_module.AmortizedQueue$T))
         && $IsAlloc(this, Tclass._module.AmortizedQueue(_module.AmortizedQueue$T), $Heap));
  free requires 4 == $FunctionContextHeight;
  modifies $Heap, $Tick;



axiom FDim(_module.LinkedList.length) == 0
   && FieldOfDecl(class._module.LinkedList, field$length) == _module.LinkedList.length
   && !$IsGhostField(_module.LinkedList.length);

axiom FDim(_module.LinkedList.tail) == 0
   && FieldOfDecl(class._module.LinkedList, field$tail) == _module.LinkedList.tail
   && !$IsGhostField(_module.LinkedList.tail);

axiom FDim(_module.LinkedList.head) == 0
   && FieldOfDecl(class._module.LinkedList, field$head) == _module.LinkedList.head
   && !$IsGhostField(_module.LinkedList.head);

procedure Call$$_module.AmortizedQueue.Init(_module.AmortizedQueue$T: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.AmortizedQueue(_module.AmortizedQueue$T))
         && $IsAlloc(this, Tclass._module.AmortizedQueue(_module.AmortizedQueue$T), $Heap));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this);
  free ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     &&
    _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
     &&
    read($Heap, this, _module.AmortizedQueue.Repr)[$Box(this)]
     && read($Heap, this, _module.AmortizedQueue.front) != null
     && read($Heap, this, _module.AmortizedQueue.Repr)[$Box(read($Heap, this, _module.AmortizedQueue.front))]
     && Set#Subset(read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.Repr),
      read($Heap, this, _module.AmortizedQueue.Repr))
     && _module.LinkedList.Valid(_module.AmortizedQueue$T,
      $LS($LZ),
      $Heap,
      read($Heap, this, _module.AmortizedQueue.front))
     && read($Heap, this, _module.AmortizedQueue.rear) != null
     && read($Heap, this, _module.AmortizedQueue.Repr)[$Box(read($Heap, this, _module.AmortizedQueue.rear))]
     && Set#Subset(read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.Repr),
      read($Heap, this, _module.AmortizedQueue.Repr))
     && _module.LinkedList.Valid(_module.AmortizedQueue$T,
      $LS($LZ),
      $Heap,
      read($Heap, this, _module.AmortizedQueue.rear))
     && Seq#Length(read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.List))
       <= Seq#Length(read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.List))
     && Seq#Equal(read($Heap, this, _module.AmortizedQueue.List),
      Seq#Append(read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.List),
        _module.LinkedList.ReverseSeq(_module.AmortizedQueue$T,
          $LS($LZ),
          read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.List))));
  ensures Seq#Equal(read($Heap, this, _module.AmortizedQueue.List), Seq#Empty(): Seq Box);
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f) || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.AmortizedQueue.Init(_module.AmortizedQueue$T: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.AmortizedQueue(_module.AmortizedQueue$T))
         && $IsAlloc(this, Tclass._module.AmortizedQueue(_module.AmortizedQueue$T), $Heap))
   returns ($_reverifyPost: bool);
  free requires 4 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this);
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || read($Heap, this, _module.AmortizedQueue.Repr)[$Box(this)];
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || read($Heap, this, _module.AmortizedQueue.front) != null;
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || read($Heap, this, _module.AmortizedQueue.Repr)[$Box(read($Heap, this, _module.AmortizedQueue.front))];
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || Set#Subset(read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.Repr),
        read($Heap, this, _module.AmortizedQueue.Repr));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.front))
           || read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.Repr)[$Box(read($Heap, this, _module.AmortizedQueue.front))]);
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.front))
           || LitInt(0)
             <= read($Heap,
              read($Heap, this, _module.AmortizedQueue.front),
              _module.LinkedList.length));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.front))
           || read($Heap,
              read($Heap, this, _module.AmortizedQueue.front),
              _module.LinkedList.length)
             == Seq#Length(read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.List)));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.front))
           || (read($Heap,
                read($Heap, this, _module.AmortizedQueue.front),
                _module.LinkedList.length)
               == LitInt(0)
             ==> Seq#Equal(read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.List),
              Seq#Empty(): Seq Box)));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.front))
           || (read($Heap,
                read($Heap, this, _module.AmortizedQueue.front),
                _module.LinkedList.length)
               == LitInt(0)
             ==> read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.tail)
               == null));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.front))
           || (read($Heap,
                read($Heap, this, _module.AmortizedQueue.front),
                _module.LinkedList.length)
               != 0
             ==> read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.tail)
               != null));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.front))
           || (read($Heap,
                read($Heap, this, _module.AmortizedQueue.front),
                _module.LinkedList.length)
               != 0
             ==> read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.Repr)[$Box(read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.tail))]));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.front))
           || (read($Heap,
                read($Heap, this, _module.AmortizedQueue.front),
                _module.LinkedList.length)
               != 0
             ==> Set#Subset(read($Heap,
                read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.tail),
                _module.LinkedList.Repr),
              read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.Repr))));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.front))
           || (read($Heap,
                read($Heap, this, _module.AmortizedQueue.front),
                _module.LinkedList.length)
               != 0
             ==> !read($Heap,
              read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.tail),
              _module.LinkedList.Repr)[$Box(read($Heap, this, _module.AmortizedQueue.front))]));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.front))
           || (read($Heap,
                read($Heap, this, _module.AmortizedQueue.front),
                _module.LinkedList.length)
               != 0
             ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
              $LS($LS($LZ)),
              $Heap,
              read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.tail))));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.front))
           || (read($Heap,
                read($Heap, this, _module.AmortizedQueue.front),
                _module.LinkedList.length)
               != 0
             ==> Seq#Equal(read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.List),
              Seq#Append(Seq#Build(Seq#Empty(): Seq Box,
                  read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.head)),
                read($Heap,
                  read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.tail),
                  _module.LinkedList.List)))));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.front))
           || (read($Heap,
                read($Heap, this, _module.AmortizedQueue.front),
                _module.LinkedList.length)
               != 0
             ==> read($Heap,
                read($Heap, this, _module.AmortizedQueue.front),
                _module.LinkedList.length)
               == read($Heap,
                  read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.tail),
                  _module.LinkedList.length)
                 + 1));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || read($Heap, this, _module.AmortizedQueue.rear) != null;
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || read($Heap, this, _module.AmortizedQueue.Repr)[$Box(read($Heap, this, _module.AmortizedQueue.rear))];
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || Set#Subset(read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.Repr),
        read($Heap, this, _module.AmortizedQueue.Repr));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.rear))
           || read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.Repr)[$Box(read($Heap, this, _module.AmortizedQueue.rear))]);
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.rear))
           || LitInt(0)
             <= read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.length));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.rear))
           || read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.length)
             == Seq#Length(read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.List)));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.rear))
           || (read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.length)
               == LitInt(0)
             ==> Seq#Equal(read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.List),
              Seq#Empty(): Seq Box)));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.rear))
           || (read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.length)
               == LitInt(0)
             ==> read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.tail)
               == null));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.rear))
           || (read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.length)
               != 0
             ==> read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.tail)
               != null));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.rear))
           || (read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.length)
               != 0
             ==> read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.Repr)[$Box(read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.tail))]));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.rear))
           || (read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.length)
               != 0
             ==> Set#Subset(read($Heap,
                read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.tail),
                _module.LinkedList.Repr),
              read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.Repr))));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.rear))
           || (read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.length)
               != 0
             ==> !read($Heap,
              read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.tail),
              _module.LinkedList.Repr)[$Box(read($Heap, this, _module.AmortizedQueue.rear))]));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.rear))
           || (read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.length)
               != 0
             ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
              $LS($LS($LZ)),
              $Heap,
              read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.tail))));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.rear))
           || (read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.length)
               != 0
             ==> Seq#Equal(read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.List),
              Seq#Append(Seq#Build(Seq#Empty(): Seq Box,
                  read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.head)),
                read($Heap,
                  read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.tail),
                  _module.LinkedList.List)))));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.rear))
           || (read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.length)
               != 0
             ==> read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.length)
               == read($Heap,
                  read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.tail),
                  _module.LinkedList.length)
                 + 1));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || Seq#Length(read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.List))
         <= Seq#Length(read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.List));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || Seq#Equal(read($Heap, this, _module.AmortizedQueue.List),
        Seq#Append(read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.List),
          _module.LinkedList.ReverseSeq(_module.AmortizedQueue$T,
            $LS($LS($LZ)),
            read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.List))));
  ensures Seq#Equal(read($Heap, this, _module.AmortizedQueue.List), Seq#Empty(): Seq Box);
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f) || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.AmortizedQueue.Init(_module.AmortizedQueue$T: Ty, this: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs#0: ref
     where $Is($rhs#0, Tclass._module.LinkedList(_module.AmortizedQueue$T));
  var $nw: ref;
  var $rhs#1: ref
     where $Is($rhs#1, Tclass._module.LinkedList(_module.AmortizedQueue$T));
  var $rhs#2: Set Box where $Is($rhs#2, TSet(Tclass._System.object()));
  var $rhs#3: Set Box where $Is($rhs#3, TSet(Tclass._System.object()));
  var $rhs#4: Seq Box where $Is($rhs#4, TSeq(_module.AmortizedQueue$T));

    // AddMethodImpl: Init, Impl$$_module.AmortizedQueue.Init
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> $o == this);
    assume {:captureState "Problem5-DoubleEndedQueue.dfy(35,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- Problem5-DoubleEndedQueue.dfy(36,11)
    assume true;
    assert $_Frame[this, _module.AmortizedQueue.front];
    havoc $nw;
    assume $nw != null
       &&
      !read($Heap, $nw, alloc)
       && dtype($nw) == Tclass._module.LinkedList(_module.AmortizedQueue$T);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    // ----- init call statement ----- Problem5-DoubleEndedQueue.dfy(36,32)
    // TrCallStmt: Before ProcessCallStmt
    assert (forall<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) && $o == $nw ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.LinkedList.Init(_module.AmortizedQueue$T, $nw);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "Problem5-DoubleEndedQueue.dfy(36,37)"} true;
    $rhs#0 := $nw;
    $Heap := update($Heap, this, _module.AmortizedQueue.front, $rhs#0);
    assume $IsGoodHeap($Heap);
    assume {:captureState "Problem5-DoubleEndedQueue.dfy(36,37)"} true;
    // ----- assignment statement ----- Problem5-DoubleEndedQueue.dfy(37,10)
    assume true;
    assert $_Frame[this, _module.AmortizedQueue.rear];
    havoc $nw;
    assume $nw != null
       &&
      !read($Heap, $nw, alloc)
       && dtype($nw) == Tclass._module.LinkedList(_module.AmortizedQueue$T);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    // ----- init call statement ----- Problem5-DoubleEndedQueue.dfy(37,31)
    // TrCallStmt: Before ProcessCallStmt
    assert (forall<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) && $o == $nw ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.LinkedList.Init(_module.AmortizedQueue$T, $nw);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "Problem5-DoubleEndedQueue.dfy(37,36)"} true;
    $rhs#1 := $nw;
    $Heap := update($Heap, this, _module.AmortizedQueue.rear, $rhs#1);
    assume $IsGoodHeap($Heap);
    assume {:captureState "Problem5-DoubleEndedQueue.dfy(37,36)"} true;
    // ----- assignment statement ----- Problem5-DoubleEndedQueue.dfy(38,10)
    assume true;
    assert $_Frame[this, _module.AmortizedQueue.Repr];
    assume true;
    $rhs#2 := Set#UnionOne(Set#Empty(): Set Box, $Box(this));
    $Heap := update($Heap, this, _module.AmortizedQueue.Repr, $rhs#2);
    assume $IsGoodHeap($Heap);
    assume {:captureState "Problem5-DoubleEndedQueue.dfy(38,18)"} true;
    // ----- assignment statement ----- Problem5-DoubleEndedQueue.dfy(39,10)
    assume true;
    assert $_Frame[this, _module.AmortizedQueue.Repr];
    assert read($Heap, this, _module.AmortizedQueue.front) != null;
    assert read($Heap, this, _module.AmortizedQueue.rear) != null;
    assume true;
    $rhs#3 := Set#Union(Set#Union(read($Heap, this, _module.AmortizedQueue.Repr),
        read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.Repr)),
      read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.Repr));
    $Heap := update($Heap, this, _module.AmortizedQueue.Repr, $rhs#3);
    assume $IsGoodHeap($Heap);
    assume {:captureState "Problem5-DoubleEndedQueue.dfy(39,41)"} true;
    // ----- assignment statement ----- Problem5-DoubleEndedQueue.dfy(40,10)
    assume true;
    assert $_Frame[this, _module.AmortizedQueue.List];
    assume true;
    $rhs#4 := Lit(Seq#Empty(): Seq Box);
    $Heap := update($Heap, this, _module.AmortizedQueue.List, $rhs#4);
    assume $IsGoodHeap($Heap);
    assume {:captureState "Problem5-DoubleEndedQueue.dfy(40,14)"} true;
}



procedure CheckWellformed$$_module.AmortizedQueue.InitFromPieces(_module.AmortizedQueue$T: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.AmortizedQueue(_module.AmortizedQueue$T))
         && $IsAlloc(this, Tclass._module.AmortizedQueue(_module.AmortizedQueue$T), $Heap),
    f#0: ref
       where $Is(f#0, Tclass._module.LinkedList(_module.AmortizedQueue$T))
         && $IsAlloc(f#0, Tclass._module.LinkedList(_module.AmortizedQueue$T), $Heap),
    r#0: ref
       where $Is(r#0, Tclass._module.LinkedList(_module.AmortizedQueue$T))
         && $IsAlloc(r#0, Tclass._module.LinkedList(_module.AmortizedQueue$T), $Heap));
  free requires 8 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.AmortizedQueue.InitFromPieces(_module.AmortizedQueue$T: Ty, this: ref, f#0: ref, r#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##s#0: Seq Box;

    // AddMethodImpl: InitFromPieces, CheckWellformed$$_module.AmortizedQueue.InitFromPieces
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> $o == this);
    assume {:captureState "Problem5-DoubleEndedQueue.dfy(43,9): initial state"} true;
    assume f#0 != null;
    assert f#0 != null;
    assume _module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, f#0);
    assume _module.LinkedList.Valid(_module.AmortizedQueue$T, $LS($LZ), $Heap, f#0);
    assume r#0 != null;
    assert r#0 != null;
    assume _module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0);
    assume _module.LinkedList.Valid(_module.AmortizedQueue$T, $LS($LZ), $Heap, r#0);
    havoc $Heap;
    assume (forall<alpha> $o: ref, $f: Field alpha ::
      { read($Heap, $o, $f) }
      $o != null && read(old($Heap), $o, alloc)
         ==> read($Heap, $o, $f) == read(old($Heap), $o, $f) || $o == this);
    assume $HeapSucc(old($Heap), $Heap);
    assume {:captureState "Problem5-DoubleEndedQueue.dfy(46,20): post-state"} true;
    assume _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this);
    assume _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this);
    assert f#0 != null;
    assert r#0 != null;
    ##s#0 := read($Heap, r#0, _module.LinkedList.List);
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#0, TSeq(_module.AmortizedQueue$T), $Heap);
    assume _module.LinkedList.ReverseSeq#canCall(_module.AmortizedQueue$T, read($Heap, r#0, _module.LinkedList.List));
    assume Seq#Equal(read($Heap, this, _module.AmortizedQueue.List),
      Seq#Append(read($Heap, f#0, _module.LinkedList.List),
        _module.LinkedList.ReverseSeq(_module.AmortizedQueue$T, $LS($LZ), read($Heap, r#0, _module.LinkedList.List))));
}



procedure Call$$_module.AmortizedQueue.InitFromPieces(_module.AmortizedQueue$T: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.AmortizedQueue(_module.AmortizedQueue$T))
         && $IsAlloc(this, Tclass._module.AmortizedQueue(_module.AmortizedQueue$T), $Heap),
    f#0: ref
       where $Is(f#0, Tclass._module.LinkedList(_module.AmortizedQueue$T))
         && $IsAlloc(f#0, Tclass._module.LinkedList(_module.AmortizedQueue$T), $Heap),
    r#0: ref
       where $Is(r#0, Tclass._module.LinkedList(_module.AmortizedQueue$T))
         && $IsAlloc(r#0, Tclass._module.LinkedList(_module.AmortizedQueue$T), $Heap));
  // user-defined preconditions
  requires f#0 != null;
  requires _module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, f#0)
     ==> _module.LinkedList.Valid(_module.AmortizedQueue$T, $LS($LZ), $Heap, f#0)
       || read($Heap, f#0, _module.LinkedList.Repr)[$Box(f#0)];
  requires _module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, f#0)
     ==> _module.LinkedList.Valid(_module.AmortizedQueue$T, $LS($LZ), $Heap, f#0)
       || LitInt(0) <= read($Heap, f#0, _module.LinkedList.length);
  requires _module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, f#0)
     ==> _module.LinkedList.Valid(_module.AmortizedQueue$T, $LS($LZ), $Heap, f#0)
       || read($Heap, f#0, _module.LinkedList.length)
         == Seq#Length(read($Heap, f#0, _module.LinkedList.List));
  requires _module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, f#0)
     ==> _module.LinkedList.Valid(_module.AmortizedQueue$T, $LS($LZ), $Heap, f#0)
       || (read($Heap, f#0, _module.LinkedList.length) == LitInt(0)
         ==> Seq#Equal(read($Heap, f#0, _module.LinkedList.List), Seq#Empty(): Seq Box));
  requires _module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, f#0)
     ==> _module.LinkedList.Valid(_module.AmortizedQueue$T, $LS($LZ), $Heap, f#0)
       || (read($Heap, f#0, _module.LinkedList.length) == LitInt(0)
         ==> read($Heap, f#0, _module.LinkedList.tail) == null);
  requires _module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, f#0)
     ==> _module.LinkedList.Valid(_module.AmortizedQueue$T, $LS($LZ), $Heap, f#0)
       || (read($Heap, f#0, _module.LinkedList.length) != 0
         ==> read($Heap, f#0, _module.LinkedList.tail) != null);
  requires _module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, f#0)
     ==> _module.LinkedList.Valid(_module.AmortizedQueue$T, $LS($LZ), $Heap, f#0)
       || (read($Heap, f#0, _module.LinkedList.length) != 0
         ==> read($Heap, f#0, _module.LinkedList.Repr)[$Box(read($Heap, f#0, _module.LinkedList.tail))]);
  requires _module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, f#0)
     ==> _module.LinkedList.Valid(_module.AmortizedQueue$T, $LS($LZ), $Heap, f#0)
       || (read($Heap, f#0, _module.LinkedList.length) != 0
         ==> Set#Subset(read($Heap, read($Heap, f#0, _module.LinkedList.tail), _module.LinkedList.Repr),
          read($Heap, f#0, _module.LinkedList.Repr)));
  requires _module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, f#0)
     ==> _module.LinkedList.Valid(_module.AmortizedQueue$T, $LS($LZ), $Heap, f#0)
       || (read($Heap, f#0, _module.LinkedList.length) != 0
         ==> !read($Heap, read($Heap, f#0, _module.LinkedList.tail), _module.LinkedList.Repr)[$Box(f#0)]);
  requires _module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, f#0)
     ==> _module.LinkedList.Valid(_module.AmortizedQueue$T, $LS($LZ), $Heap, f#0)
       || (read($Heap, f#0, _module.LinkedList.length) != 0
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
          $LS($LS($LZ)),
          $Heap,
          read($Heap, f#0, _module.LinkedList.tail)));
  requires _module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, f#0)
     ==> _module.LinkedList.Valid(_module.AmortizedQueue$T, $LS($LZ), $Heap, f#0)
       || (read($Heap, f#0, _module.LinkedList.length) != 0
         ==> Seq#Equal(read($Heap, f#0, _module.LinkedList.List),
          Seq#Append(Seq#Build(Seq#Empty(): Seq Box, read($Heap, f#0, _module.LinkedList.head)),
            read($Heap, read($Heap, f#0, _module.LinkedList.tail), _module.LinkedList.List))));
  requires _module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, f#0)
     ==> _module.LinkedList.Valid(_module.AmortizedQueue$T, $LS($LZ), $Heap, f#0)
       || (read($Heap, f#0, _module.LinkedList.length) != 0
         ==> read($Heap, f#0, _module.LinkedList.length)
           == read($Heap, read($Heap, f#0, _module.LinkedList.tail), _module.LinkedList.length)
             + 1);
  requires r#0 != null;
  requires _module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0)
     ==> _module.LinkedList.Valid(_module.AmortizedQueue$T, $LS($LZ), $Heap, r#0)
       || read($Heap, r#0, _module.LinkedList.Repr)[$Box(r#0)];
  requires _module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0)
     ==> _module.LinkedList.Valid(_module.AmortizedQueue$T, $LS($LZ), $Heap, r#0)
       || LitInt(0) <= read($Heap, r#0, _module.LinkedList.length);
  requires _module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0)
     ==> _module.LinkedList.Valid(_module.AmortizedQueue$T, $LS($LZ), $Heap, r#0)
       || read($Heap, r#0, _module.LinkedList.length)
         == Seq#Length(read($Heap, r#0, _module.LinkedList.List));
  requires _module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0)
     ==> _module.LinkedList.Valid(_module.AmortizedQueue$T, $LS($LZ), $Heap, r#0)
       || (read($Heap, r#0, _module.LinkedList.length) == LitInt(0)
         ==> Seq#Equal(read($Heap, r#0, _module.LinkedList.List), Seq#Empty(): Seq Box));
  requires _module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0)
     ==> _module.LinkedList.Valid(_module.AmortizedQueue$T, $LS($LZ), $Heap, r#0)
       || (read($Heap, r#0, _module.LinkedList.length) == LitInt(0)
         ==> read($Heap, r#0, _module.LinkedList.tail) == null);
  requires _module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0)
     ==> _module.LinkedList.Valid(_module.AmortizedQueue$T, $LS($LZ), $Heap, r#0)
       || (read($Heap, r#0, _module.LinkedList.length) != 0
         ==> read($Heap, r#0, _module.LinkedList.tail) != null);
  requires _module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0)
     ==> _module.LinkedList.Valid(_module.AmortizedQueue$T, $LS($LZ), $Heap, r#0)
       || (read($Heap, r#0, _module.LinkedList.length) != 0
         ==> read($Heap, r#0, _module.LinkedList.Repr)[$Box(read($Heap, r#0, _module.LinkedList.tail))]);
  requires _module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0)
     ==> _module.LinkedList.Valid(_module.AmortizedQueue$T, $LS($LZ), $Heap, r#0)
       || (read($Heap, r#0, _module.LinkedList.length) != 0
         ==> Set#Subset(read($Heap, read($Heap, r#0, _module.LinkedList.tail), _module.LinkedList.Repr),
          read($Heap, r#0, _module.LinkedList.Repr)));
  requires _module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0)
     ==> _module.LinkedList.Valid(_module.AmortizedQueue$T, $LS($LZ), $Heap, r#0)
       || (read($Heap, r#0, _module.LinkedList.length) != 0
         ==> !read($Heap, read($Heap, r#0, _module.LinkedList.tail), _module.LinkedList.Repr)[$Box(r#0)]);
  requires _module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0)
     ==> _module.LinkedList.Valid(_module.AmortizedQueue$T, $LS($LZ), $Heap, r#0)
       || (read($Heap, r#0, _module.LinkedList.length) != 0
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
          $LS($LS($LZ)),
          $Heap,
          read($Heap, r#0, _module.LinkedList.tail)));
  requires _module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0)
     ==> _module.LinkedList.Valid(_module.AmortizedQueue$T, $LS($LZ), $Heap, r#0)
       || (read($Heap, r#0, _module.LinkedList.length) != 0
         ==> Seq#Equal(read($Heap, r#0, _module.LinkedList.List),
          Seq#Append(Seq#Build(Seq#Empty(): Seq Box, read($Heap, r#0, _module.LinkedList.head)),
            read($Heap, read($Heap, r#0, _module.LinkedList.tail), _module.LinkedList.List))));
  requires _module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0)
     ==> _module.LinkedList.Valid(_module.AmortizedQueue$T, $LS($LZ), $Heap, r#0)
       || (read($Heap, r#0, _module.LinkedList.length) != 0
         ==> read($Heap, r#0, _module.LinkedList.length)
           == read($Heap, read($Heap, r#0, _module.LinkedList.tail), _module.LinkedList.length)
             + 1);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     && (_module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       ==> _module.LinkedList.ReverseSeq#canCall(_module.AmortizedQueue$T, read($Heap, r#0, _module.LinkedList.List)));
  free ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     &&
    _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
     &&
    read($Heap, this, _module.AmortizedQueue.Repr)[$Box(this)]
     && read($Heap, this, _module.AmortizedQueue.front) != null
     && read($Heap, this, _module.AmortizedQueue.Repr)[$Box(read($Heap, this, _module.AmortizedQueue.front))]
     && Set#Subset(read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.Repr),
      read($Heap, this, _module.AmortizedQueue.Repr))
     && _module.LinkedList.Valid(_module.AmortizedQueue$T,
      $LS($LZ),
      $Heap,
      read($Heap, this, _module.AmortizedQueue.front))
     && read($Heap, this, _module.AmortizedQueue.rear) != null
     && read($Heap, this, _module.AmortizedQueue.Repr)[$Box(read($Heap, this, _module.AmortizedQueue.rear))]
     && Set#Subset(read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.Repr),
      read($Heap, this, _module.AmortizedQueue.Repr))
     && _module.LinkedList.Valid(_module.AmortizedQueue$T,
      $LS($LZ),
      $Heap,
      read($Heap, this, _module.AmortizedQueue.rear))
     && Seq#Length(read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.List))
       <= Seq#Length(read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.List))
     && Seq#Equal(read($Heap, this, _module.AmortizedQueue.List),
      Seq#Append(read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.List),
        _module.LinkedList.ReverseSeq(_module.AmortizedQueue$T,
          $LS($LZ),
          read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.List))));
  ensures Seq#Equal(read($Heap, this, _module.AmortizedQueue.List),
    Seq#Append(read($Heap, f#0, _module.LinkedList.List),
      _module.LinkedList.ReverseSeq(_module.AmortizedQueue$T,
        $LS($LS($LZ)),
        read($Heap, r#0, _module.LinkedList.List))));
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f) || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.AmortizedQueue.InitFromPieces(_module.AmortizedQueue$T: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.AmortizedQueue(_module.AmortizedQueue$T))
         && $IsAlloc(this, Tclass._module.AmortizedQueue(_module.AmortizedQueue$T), $Heap),
    f#0: ref
       where $Is(f#0, Tclass._module.LinkedList(_module.AmortizedQueue$T))
         && $IsAlloc(f#0, Tclass._module.LinkedList(_module.AmortizedQueue$T), $Heap),
    r#0: ref
       where $Is(r#0, Tclass._module.LinkedList(_module.AmortizedQueue$T))
         && $IsAlloc(r#0, Tclass._module.LinkedList(_module.AmortizedQueue$T), $Heap))
   returns ($_reverifyPost: bool);
  free requires 8 == $FunctionContextHeight;
  // user-defined preconditions
  requires f#0 != null;
  free requires _module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, f#0)
     &&
    _module.LinkedList.Valid(_module.AmortizedQueue$T, $LS($LZ), $Heap, f#0)
     &&
    read($Heap, f#0, _module.LinkedList.Repr)[$Box(f#0)]
     && LitInt(0) <= read($Heap, f#0, _module.LinkedList.length)
     && read($Heap, f#0, _module.LinkedList.length)
       == Seq#Length(read($Heap, f#0, _module.LinkedList.List))
     && (read($Heap, f#0, _module.LinkedList.length) == LitInt(0)
       ==> Seq#Equal(read($Heap, f#0, _module.LinkedList.List), Seq#Empty(): Seq Box)
         && read($Heap, f#0, _module.LinkedList.tail) == null)
     && (read($Heap, f#0, _module.LinkedList.length) != 0
       ==> read($Heap, f#0, _module.LinkedList.tail) != null
         && read($Heap, f#0, _module.LinkedList.Repr)[$Box(read($Heap, f#0, _module.LinkedList.tail))]
         && Set#Subset(read($Heap, read($Heap, f#0, _module.LinkedList.tail), _module.LinkedList.Repr),
          read($Heap, f#0, _module.LinkedList.Repr))
         && !read($Heap, read($Heap, f#0, _module.LinkedList.tail), _module.LinkedList.Repr)[$Box(f#0)]
         && _module.LinkedList.Valid(_module.AmortizedQueue$T,
          $LS($LZ),
          $Heap,
          read($Heap, f#0, _module.LinkedList.tail))
         && Seq#Equal(read($Heap, f#0, _module.LinkedList.List),
          Seq#Append(Seq#Build(Seq#Empty(): Seq Box, read($Heap, f#0, _module.LinkedList.head)),
            read($Heap, read($Heap, f#0, _module.LinkedList.tail), _module.LinkedList.List)))
         && read($Heap, f#0, _module.LinkedList.length)
           == read($Heap, read($Heap, f#0, _module.LinkedList.tail), _module.LinkedList.length)
             + 1);
  requires r#0 != null;
  free requires _module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0)
     &&
    _module.LinkedList.Valid(_module.AmortizedQueue$T, $LS($LZ), $Heap, r#0)
     &&
    read($Heap, r#0, _module.LinkedList.Repr)[$Box(r#0)]
     && LitInt(0) <= read($Heap, r#0, _module.LinkedList.length)
     && read($Heap, r#0, _module.LinkedList.length)
       == Seq#Length(read($Heap, r#0, _module.LinkedList.List))
     && (read($Heap, r#0, _module.LinkedList.length) == LitInt(0)
       ==> Seq#Equal(read($Heap, r#0, _module.LinkedList.List), Seq#Empty(): Seq Box)
         && read($Heap, r#0, _module.LinkedList.tail) == null)
     && (read($Heap, r#0, _module.LinkedList.length) != 0
       ==> read($Heap, r#0, _module.LinkedList.tail) != null
         && read($Heap, r#0, _module.LinkedList.Repr)[$Box(read($Heap, r#0, _module.LinkedList.tail))]
         && Set#Subset(read($Heap, read($Heap, r#0, _module.LinkedList.tail), _module.LinkedList.Repr),
          read($Heap, r#0, _module.LinkedList.Repr))
         && !read($Heap, read($Heap, r#0, _module.LinkedList.tail), _module.LinkedList.Repr)[$Box(r#0)]
         && _module.LinkedList.Valid(_module.AmortizedQueue$T,
          $LS($LZ),
          $Heap,
          read($Heap, r#0, _module.LinkedList.tail))
         && Seq#Equal(read($Heap, r#0, _module.LinkedList.List),
          Seq#Append(Seq#Build(Seq#Empty(): Seq Box, read($Heap, r#0, _module.LinkedList.head)),
            read($Heap, read($Heap, r#0, _module.LinkedList.tail), _module.LinkedList.List)))
         && read($Heap, r#0, _module.LinkedList.length)
           == read($Heap, read($Heap, r#0, _module.LinkedList.tail), _module.LinkedList.length)
             + 1);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     && (_module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       ==> _module.LinkedList.ReverseSeq#canCall(_module.AmortizedQueue$T, read($Heap, r#0, _module.LinkedList.List)));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || read($Heap, this, _module.AmortizedQueue.Repr)[$Box(this)];
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || read($Heap, this, _module.AmortizedQueue.front) != null;
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || read($Heap, this, _module.AmortizedQueue.Repr)[$Box(read($Heap, this, _module.AmortizedQueue.front))];
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || Set#Subset(read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.Repr),
        read($Heap, this, _module.AmortizedQueue.Repr));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.front))
           || read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.Repr)[$Box(read($Heap, this, _module.AmortizedQueue.front))]);
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.front))
           || LitInt(0)
             <= read($Heap,
              read($Heap, this, _module.AmortizedQueue.front),
              _module.LinkedList.length));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.front))
           || read($Heap,
              read($Heap, this, _module.AmortizedQueue.front),
              _module.LinkedList.length)
             == Seq#Length(read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.List)));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.front))
           || (read($Heap,
                read($Heap, this, _module.AmortizedQueue.front),
                _module.LinkedList.length)
               == LitInt(0)
             ==> Seq#Equal(read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.List),
              Seq#Empty(): Seq Box)));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.front))
           || (read($Heap,
                read($Heap, this, _module.AmortizedQueue.front),
                _module.LinkedList.length)
               == LitInt(0)
             ==> read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.tail)
               == null));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.front))
           || (read($Heap,
                read($Heap, this, _module.AmortizedQueue.front),
                _module.LinkedList.length)
               != 0
             ==> read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.tail)
               != null));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.front))
           || (read($Heap,
                read($Heap, this, _module.AmortizedQueue.front),
                _module.LinkedList.length)
               != 0
             ==> read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.Repr)[$Box(read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.tail))]));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.front))
           || (read($Heap,
                read($Heap, this, _module.AmortizedQueue.front),
                _module.LinkedList.length)
               != 0
             ==> Set#Subset(read($Heap,
                read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.tail),
                _module.LinkedList.Repr),
              read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.Repr))));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.front))
           || (read($Heap,
                read($Heap, this, _module.AmortizedQueue.front),
                _module.LinkedList.length)
               != 0
             ==> !read($Heap,
              read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.tail),
              _module.LinkedList.Repr)[$Box(read($Heap, this, _module.AmortizedQueue.front))]));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.front))
           || (read($Heap,
                read($Heap, this, _module.AmortizedQueue.front),
                _module.LinkedList.length)
               != 0
             ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
              $LS($LS($LZ)),
              $Heap,
              read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.tail))));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.front))
           || (read($Heap,
                read($Heap, this, _module.AmortizedQueue.front),
                _module.LinkedList.length)
               != 0
             ==> Seq#Equal(read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.List),
              Seq#Append(Seq#Build(Seq#Empty(): Seq Box,
                  read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.head)),
                read($Heap,
                  read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.tail),
                  _module.LinkedList.List)))));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.front))
           || (read($Heap,
                read($Heap, this, _module.AmortizedQueue.front),
                _module.LinkedList.length)
               != 0
             ==> read($Heap,
                read($Heap, this, _module.AmortizedQueue.front),
                _module.LinkedList.length)
               == read($Heap,
                  read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.tail),
                  _module.LinkedList.length)
                 + 1));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || read($Heap, this, _module.AmortizedQueue.rear) != null;
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || read($Heap, this, _module.AmortizedQueue.Repr)[$Box(read($Heap, this, _module.AmortizedQueue.rear))];
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || Set#Subset(read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.Repr),
        read($Heap, this, _module.AmortizedQueue.Repr));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.rear))
           || read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.Repr)[$Box(read($Heap, this, _module.AmortizedQueue.rear))]);
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.rear))
           || LitInt(0)
             <= read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.length));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.rear))
           || read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.length)
             == Seq#Length(read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.List)));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.rear))
           || (read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.length)
               == LitInt(0)
             ==> Seq#Equal(read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.List),
              Seq#Empty(): Seq Box)));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.rear))
           || (read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.length)
               == LitInt(0)
             ==> read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.tail)
               == null));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.rear))
           || (read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.length)
               != 0
             ==> read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.tail)
               != null));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.rear))
           || (read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.length)
               != 0
             ==> read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.Repr)[$Box(read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.tail))]));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.rear))
           || (read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.length)
               != 0
             ==> Set#Subset(read($Heap,
                read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.tail),
                _module.LinkedList.Repr),
              read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.Repr))));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.rear))
           || (read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.length)
               != 0
             ==> !read($Heap,
              read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.tail),
              _module.LinkedList.Repr)[$Box(read($Heap, this, _module.AmortizedQueue.rear))]));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.rear))
           || (read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.length)
               != 0
             ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
              $LS($LS($LZ)),
              $Heap,
              read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.tail))));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.rear))
           || (read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.length)
               != 0
             ==> Seq#Equal(read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.List),
              Seq#Append(Seq#Build(Seq#Empty(): Seq Box,
                  read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.head)),
                read($Heap,
                  read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.tail),
                  _module.LinkedList.List)))));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.rear))
           || (read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.length)
               != 0
             ==> read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.length)
               == read($Heap,
                  read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.tail),
                  _module.LinkedList.length)
                 + 1));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || Seq#Length(read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.List))
         <= Seq#Length(read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.List));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || Seq#Equal(read($Heap, this, _module.AmortizedQueue.List),
        Seq#Append(read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.List),
          _module.LinkedList.ReverseSeq(_module.AmortizedQueue$T,
            $LS($LS($LZ)),
            read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.List))));
  ensures Seq#Equal(read($Heap, this, _module.AmortizedQueue.List),
    Seq#Append(read($Heap, f#0, _module.LinkedList.List),
      _module.LinkedList.ReverseSeq(_module.AmortizedQueue$T,
        $LS($LS($LZ)),
        read($Heap, r#0, _module.LinkedList.List))));
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f) || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.AmortizedQueue.InitFromPieces(_module.AmortizedQueue$T: Ty, this: ref, f#0: ref, r#0: ref)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs#0_0: ref
     where $Is($rhs#0_0, Tclass._module.LinkedList(_module.AmortizedQueue$T));
  var $rhs#0_1: ref
     where $Is($rhs#0_1, Tclass._module.LinkedList(_module.AmortizedQueue$T));
  var rr#0: ref
     where $Is(rr#0, Tclass._module.LinkedList(_module.AmortizedQueue$T))
       && $IsAlloc(rr#0, Tclass._module.LinkedList(_module.AmortizedQueue$T), $Heap);
  var $rhs##0: ref
     where $Is($rhs##0, Tclass._module.LinkedList(_module.AmortizedQueue$T))
       && $IsAlloc($rhs##0, Tclass._module.LinkedList(_module.AmortizedQueue$T), $Heap);
  var ff#0: ref
     where $Is(ff#0, Tclass._module.LinkedList(_module.AmortizedQueue$T))
       && $IsAlloc(ff#0, Tclass._module.LinkedList(_module.AmortizedQueue$T), $Heap);
  var $rhs##1: ref
     where $Is($rhs##1, Tclass._module.LinkedList(_module.AmortizedQueue$T))
       && $IsAlloc($rhs##1, Tclass._module.LinkedList(_module.AmortizedQueue$T), $Heap);
  var end##0: ref;
  var $rhs#0: ref
     where $Is($rhs#0, Tclass._module.LinkedList(_module.AmortizedQueue$T));
  var $rhs#1: ref
     where $Is($rhs#1, Tclass._module.LinkedList(_module.AmortizedQueue$T));
  var $nw: ref;
  var $rhs#2: Set Box where $Is($rhs#2, TSet(Tclass._System.object()));
  var $rhs#3: Set Box where $Is($rhs#3, TSet(Tclass._System.object()));
  var $rhs#4: Seq Box where $Is($rhs#4, TSeq(_module.AmortizedQueue$T));
  var ##s#1: Seq Box;

    // AddMethodImpl: InitFromPieces, Impl$$_module.AmortizedQueue.InitFromPieces
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> $o == this);
    assume {:captureState "Problem5-DoubleEndedQueue.dfy(47,2): initial state"} true;
    $_reverifyPost := false;
    // ----- if statement ----- Problem5-DoubleEndedQueue.dfy(48,5)
    assert r#0 != null;
    assert f#0 != null;
    assume true;
    if (read($Heap, r#0, _module.LinkedList.length)
       <= read($Heap, f#0, _module.LinkedList.length))
    {
        // ----- assignment statement ----- Problem5-DoubleEndedQueue.dfy(49,13)
        assume true;
        assert $_Frame[this, _module.AmortizedQueue.front];
        assume true;
        $rhs#0_0 := f#0;
        $Heap := update($Heap, this, _module.AmortizedQueue.front, $rhs#0_0);
        assume $IsGoodHeap($Heap);
        assume {:captureState "Problem5-DoubleEndedQueue.dfy(49,16)"} true;
        // ----- assignment statement ----- Problem5-DoubleEndedQueue.dfy(50,12)
        assume true;
        assert $_Frame[this, _module.AmortizedQueue.rear];
        assume true;
        $rhs#0_1 := r#0;
        $Heap := update($Heap, this, _module.AmortizedQueue.rear, $rhs#0_1);
        assume $IsGoodHeap($Heap);
        assume {:captureState "Problem5-DoubleEndedQueue.dfy(50,15)"} true;
    }
    else
    {
        // ----- call statement ----- Problem5-DoubleEndedQueue.dfy(52,26)
        assume true;
        // TrCallStmt: Adding lhs Microsoft.Dafny.AutoGhostIdentifierExpr with type LinkedList<T>
        // TrCallStmt: Before ProcessCallStmt
        assert r#0 != null;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call $rhs##0 := Call$$_module.LinkedList.Reverse(_module.AmortizedQueue$T, r#0);
        // TrCallStmt: After ProcessCallStmt
        rr#0 := $rhs##0;
        assume {:captureState "Problem5-DoubleEndedQueue.dfy(52,27)"} true;
        // ----- call statement ----- Problem5-DoubleEndedQueue.dfy(53,25)
        assume true;
        // TrCallStmt: Adding lhs Microsoft.Dafny.AutoGhostIdentifierExpr with type LinkedList<T>
        // TrCallStmt: Before ProcessCallStmt
        assert f#0 != null;
        assume true;
        // ProcessCallStmt: CheckSubrange
        end##0 := rr#0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call $rhs##1 := Call$$_module.LinkedList.Concat(_module.AmortizedQueue$T, f#0, end##0);
        // TrCallStmt: After ProcessCallStmt
        ff#0 := $rhs##1;
        assume {:captureState "Problem5-DoubleEndedQueue.dfy(53,28)"} true;
        // ----- assignment statement ----- Problem5-DoubleEndedQueue.dfy(54,13)
        assume true;
        assert $_Frame[this, _module.AmortizedQueue.front];
        assume true;
        $rhs#0 := ff#0;
        $Heap := update($Heap, this, _module.AmortizedQueue.front, $rhs#0);
        assume $IsGoodHeap($Heap);
        assume {:captureState "Problem5-DoubleEndedQueue.dfy(54,17)"} true;
        // ----- assignment statement ----- Problem5-DoubleEndedQueue.dfy(56,12)
        assume true;
        assert $_Frame[this, _module.AmortizedQueue.rear];
        havoc $nw;
        assume $nw != null
           &&
          !read($Heap, $nw, alloc)
           && dtype($nw) == Tclass._module.LinkedList(_module.AmortizedQueue$T);
        $Heap := update($Heap, $nw, alloc, true);
        assume $IsGoodHeap($Heap);
        assume $IsHeapAnchor($Heap);
        // ----- init call statement ----- Problem5-DoubleEndedQueue.dfy(56,33)
        // TrCallStmt: Before ProcessCallStmt
        assert (forall<alpha> $o: ref, $f: Field alpha ::
          $o != null && read($Heap, $o, alloc) && $o == $nw ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$_module.LinkedList.Init(_module.AmortizedQueue$T, $nw);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "Problem5-DoubleEndedQueue.dfy(56,38)"} true;
        $rhs#1 := $nw;
        $Heap := update($Heap, this, _module.AmortizedQueue.rear, $rhs#1);
        assume $IsGoodHeap($Heap);
        assume {:captureState "Problem5-DoubleEndedQueue.dfy(56,38)"} true;
    }

    // ----- assignment statement ----- Problem5-DoubleEndedQueue.dfy(58,10)
    assume true;
    assert $_Frame[this, _module.AmortizedQueue.Repr];
    assume true;
    $rhs#2 := Set#UnionOne(Set#Empty(): Set Box, $Box(this));
    $Heap := update($Heap, this, _module.AmortizedQueue.Repr, $rhs#2);
    assume $IsGoodHeap($Heap);
    assume {:captureState "Problem5-DoubleEndedQueue.dfy(58,18)"} true;
    // ----- assignment statement ----- Problem5-DoubleEndedQueue.dfy(59,10)
    assume true;
    assert $_Frame[this, _module.AmortizedQueue.Repr];
    assert read($Heap, this, _module.AmortizedQueue.front) != null;
    assert read($Heap, this, _module.AmortizedQueue.rear) != null;
    assume true;
    $rhs#3 := Set#Union(Set#Union(read($Heap, this, _module.AmortizedQueue.Repr),
        read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.Repr)),
      read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.Repr));
    $Heap := update($Heap, this, _module.AmortizedQueue.Repr, $rhs#3);
    assume $IsGoodHeap($Heap);
    assume {:captureState "Problem5-DoubleEndedQueue.dfy(59,41)"} true;
    // ----- assignment statement ----- Problem5-DoubleEndedQueue.dfy(60,10)
    assume true;
    assert $_Frame[this, _module.AmortizedQueue.List];
    assert read($Heap, this, _module.AmortizedQueue.front) != null;
    assert read($Heap, this, _module.AmortizedQueue.rear) != null;
    ##s#1 := read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.List);
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#1, TSeq(_module.AmortizedQueue$T), $Heap);
    assume _module.LinkedList.ReverseSeq#canCall(_module.AmortizedQueue$T,
      read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.List));
    assume _module.LinkedList.ReverseSeq#canCall(_module.AmortizedQueue$T,
      read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.List));
    $rhs#4 := Seq#Append(read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.List),
      _module.LinkedList.ReverseSeq(_module.AmortizedQueue$T,
        $LS($LZ),
        read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.List)));
    $Heap := update($Heap, this, _module.AmortizedQueue.List, $rhs#4);
    assume $IsGoodHeap($Heap);
    assume {:captureState "Problem5-DoubleEndedQueue.dfy(60,51)"} true;
}



procedure CheckWellformed$$_module.AmortizedQueue.Front(_module.AmortizedQueue$T: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.AmortizedQueue(_module.AmortizedQueue$T))
         && $IsAlloc(this, Tclass._module.AmortizedQueue(_module.AmortizedQueue$T), $Heap))
   returns (t#0: Box
       where $IsBox(t#0, _module.AmortizedQueue$T)
         && $IsAllocBox(t#0, _module.AmortizedQueue$T, $Heap));
  free requires 9 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.AmortizedQueue.Front(_module.AmortizedQueue$T: Ty, this: ref) returns (t#0: Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: Front, CheckWellformed$$_module.AmortizedQueue.Front
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "Problem5-DoubleEndedQueue.dfy(63,9): initial state"} true;
    assume _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this);
    assume _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this);
    assume !Seq#Equal(read($Heap, this, _module.AmortizedQueue.List), Seq#Empty(): Seq Box);
    havoc $Heap;
    assume (forall<alpha> $o: ref, $f: Field alpha ::
      { read($Heap, $o, $f) }
      $o != null && read(old($Heap), $o, alloc)
         ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
    assume $HeapSucc(old($Heap), $Heap);
    havoc t#0;
    assume {:captureState "Problem5-DoubleEndedQueue.dfy(65,14): post-state"} true;
    assert 0 <= LitInt(0)
       && LitInt(0) < Seq#Length(read($Heap, this, _module.AmortizedQueue.List));
    assume t#0 == Seq#Index(read($Heap, this, _module.AmortizedQueue.List), LitInt(0));
}



procedure Call$$_module.AmortizedQueue.Front(_module.AmortizedQueue$T: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.AmortizedQueue(_module.AmortizedQueue$T))
         && $IsAlloc(this, Tclass._module.AmortizedQueue(_module.AmortizedQueue$T), $Heap))
   returns (t#0: Box
       where $IsBox(t#0, _module.AmortizedQueue$T)
         && $IsAllocBox(t#0, _module.AmortizedQueue$T, $Heap));
  // user-defined preconditions
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || read($Heap, this, _module.AmortizedQueue.Repr)[$Box(this)];
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || read($Heap, this, _module.AmortizedQueue.front) != null;
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || read($Heap, this, _module.AmortizedQueue.Repr)[$Box(read($Heap, this, _module.AmortizedQueue.front))];
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || Set#Subset(read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.Repr),
        read($Heap, this, _module.AmortizedQueue.Repr));
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.front))
           || read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.Repr)[$Box(read($Heap, this, _module.AmortizedQueue.front))]);
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.front))
           || LitInt(0)
             <= read($Heap,
              read($Heap, this, _module.AmortizedQueue.front),
              _module.LinkedList.length));
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.front))
           || read($Heap,
              read($Heap, this, _module.AmortizedQueue.front),
              _module.LinkedList.length)
             == Seq#Length(read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.List)));
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.front))
           || (read($Heap,
                read($Heap, this, _module.AmortizedQueue.front),
                _module.LinkedList.length)
               == LitInt(0)
             ==> Seq#Equal(read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.List),
              Seq#Empty(): Seq Box)));
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.front))
           || (read($Heap,
                read($Heap, this, _module.AmortizedQueue.front),
                _module.LinkedList.length)
               == LitInt(0)
             ==> read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.tail)
               == null));
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.front))
           || (read($Heap,
                read($Heap, this, _module.AmortizedQueue.front),
                _module.LinkedList.length)
               != 0
             ==> read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.tail)
               != null));
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.front))
           || (read($Heap,
                read($Heap, this, _module.AmortizedQueue.front),
                _module.LinkedList.length)
               != 0
             ==> read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.Repr)[$Box(read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.tail))]));
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.front))
           || (read($Heap,
                read($Heap, this, _module.AmortizedQueue.front),
                _module.LinkedList.length)
               != 0
             ==> Set#Subset(read($Heap,
                read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.tail),
                _module.LinkedList.Repr),
              read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.Repr))));
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.front))
           || (read($Heap,
                read($Heap, this, _module.AmortizedQueue.front),
                _module.LinkedList.length)
               != 0
             ==> !read($Heap,
              read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.tail),
              _module.LinkedList.Repr)[$Box(read($Heap, this, _module.AmortizedQueue.front))]));
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.front))
           || (read($Heap,
                read($Heap, this, _module.AmortizedQueue.front),
                _module.LinkedList.length)
               != 0
             ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
              $LS($LS($LZ)),
              $Heap,
              read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.tail))));
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.front))
           || (read($Heap,
                read($Heap, this, _module.AmortizedQueue.front),
                _module.LinkedList.length)
               != 0
             ==> Seq#Equal(read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.List),
              Seq#Append(Seq#Build(Seq#Empty(): Seq Box,
                  read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.head)),
                read($Heap,
                  read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.tail),
                  _module.LinkedList.List)))));
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.front))
           || (read($Heap,
                read($Heap, this, _module.AmortizedQueue.front),
                _module.LinkedList.length)
               != 0
             ==> read($Heap,
                read($Heap, this, _module.AmortizedQueue.front),
                _module.LinkedList.length)
               == read($Heap,
                  read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.tail),
                  _module.LinkedList.length)
                 + 1));
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || read($Heap, this, _module.AmortizedQueue.rear) != null;
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || read($Heap, this, _module.AmortizedQueue.Repr)[$Box(read($Heap, this, _module.AmortizedQueue.rear))];
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || Set#Subset(read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.Repr),
        read($Heap, this, _module.AmortizedQueue.Repr));
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.rear))
           || read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.Repr)[$Box(read($Heap, this, _module.AmortizedQueue.rear))]);
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.rear))
           || LitInt(0)
             <= read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.length));
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.rear))
           || read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.length)
             == Seq#Length(read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.List)));
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.rear))
           || (read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.length)
               == LitInt(0)
             ==> Seq#Equal(read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.List),
              Seq#Empty(): Seq Box)));
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.rear))
           || (read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.length)
               == LitInt(0)
             ==> read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.tail)
               == null));
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.rear))
           || (read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.length)
               != 0
             ==> read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.tail)
               != null));
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.rear))
           || (read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.length)
               != 0
             ==> read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.Repr)[$Box(read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.tail))]));
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.rear))
           || (read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.length)
               != 0
             ==> Set#Subset(read($Heap,
                read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.tail),
                _module.LinkedList.Repr),
              read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.Repr))));
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.rear))
           || (read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.length)
               != 0
             ==> !read($Heap,
              read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.tail),
              _module.LinkedList.Repr)[$Box(read($Heap, this, _module.AmortizedQueue.rear))]));
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.rear))
           || (read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.length)
               != 0
             ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
              $LS($LS($LZ)),
              $Heap,
              read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.tail))));
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.rear))
           || (read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.length)
               != 0
             ==> Seq#Equal(read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.List),
              Seq#Append(Seq#Build(Seq#Empty(): Seq Box,
                  read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.head)),
                read($Heap,
                  read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.tail),
                  _module.LinkedList.List)))));
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.rear))
           || (read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.length)
               != 0
             ==> read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.length)
               == read($Heap,
                  read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.tail),
                  _module.LinkedList.length)
                 + 1));
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || Seq#Length(read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.List))
         <= Seq#Length(read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.List));
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || Seq#Equal(read($Heap, this, _module.AmortizedQueue.List),
        Seq#Append(read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.List),
          _module.LinkedList.ReverseSeq(_module.AmortizedQueue$T,
            $LS($LS($LZ)),
            read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.List))));
  requires !Seq#Equal(read($Heap, this, _module.AmortizedQueue.List), Seq#Empty(): Seq Box);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures t#0 == Seq#Index(read($Heap, this, _module.AmortizedQueue.List), LitInt(0));
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.AmortizedQueue.Front(_module.AmortizedQueue$T: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.AmortizedQueue(_module.AmortizedQueue$T))
         && $IsAlloc(this, Tclass._module.AmortizedQueue(_module.AmortizedQueue$T), $Heap))
   returns (t#0: Box
       where $IsBox(t#0, _module.AmortizedQueue$T)
         && $IsAllocBox(t#0, _module.AmortizedQueue$T, $Heap),
    $_reverifyPost: bool);
  free requires 9 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     &&
    _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
     &&
    read($Heap, this, _module.AmortizedQueue.Repr)[$Box(this)]
     && read($Heap, this, _module.AmortizedQueue.front) != null
     && read($Heap, this, _module.AmortizedQueue.Repr)[$Box(read($Heap, this, _module.AmortizedQueue.front))]
     && Set#Subset(read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.Repr),
      read($Heap, this, _module.AmortizedQueue.Repr))
     && _module.LinkedList.Valid(_module.AmortizedQueue$T,
      $LS($LZ),
      $Heap,
      read($Heap, this, _module.AmortizedQueue.front))
     && read($Heap, this, _module.AmortizedQueue.rear) != null
     && read($Heap, this, _module.AmortizedQueue.Repr)[$Box(read($Heap, this, _module.AmortizedQueue.rear))]
     && Set#Subset(read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.Repr),
      read($Heap, this, _module.AmortizedQueue.Repr))
     && _module.LinkedList.Valid(_module.AmortizedQueue$T,
      $LS($LZ),
      $Heap,
      read($Heap, this, _module.AmortizedQueue.rear))
     && Seq#Length(read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.List))
       <= Seq#Length(read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.List))
     && Seq#Equal(read($Heap, this, _module.AmortizedQueue.List),
      Seq#Append(read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.List),
        _module.LinkedList.ReverseSeq(_module.AmortizedQueue$T,
          $LS($LZ),
          read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.List))));
  requires !Seq#Equal(read($Heap, this, _module.AmortizedQueue.List), Seq#Empty(): Seq Box);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures t#0 == Seq#Index(read($Heap, this, _module.AmortizedQueue.List), LitInt(0));
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.AmortizedQueue.Front(_module.AmortizedQueue$T: Ty, this: ref)
   returns (t#0: Box, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: Front, Impl$$_module.AmortizedQueue.Front
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "Problem5-DoubleEndedQueue.dfy(66,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- Problem5-DoubleEndedQueue.dfy(67,7)
    assume true;
    assert read($Heap, this, _module.AmortizedQueue.front) != null;
    assume true;
    t#0 := read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.head);
    assume {:captureState "Problem5-DoubleEndedQueue.dfy(67,19)"} true;
}



procedure CheckWellformed$$_module.AmortizedQueue.Tail(_module.AmortizedQueue$T: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.AmortizedQueue(_module.AmortizedQueue$T))
         && $IsAlloc(this, Tclass._module.AmortizedQueue(_module.AmortizedQueue$T), $Heap))
   returns (r#0: ref
       where $Is(r#0, Tclass._module.AmortizedQueue(_module.AmortizedQueue$T))
         && $IsAlloc(r#0, Tclass._module.AmortizedQueue(_module.AmortizedQueue$T), $Heap));
  free requires 10 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.AmortizedQueue.Tail(_module.AmortizedQueue$T: Ty, this: ref) returns (r#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: Tail, CheckWellformed$$_module.AmortizedQueue.Tail
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "Problem5-DoubleEndedQueue.dfy(70,9): initial state"} true;
    assume _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this);
    assume _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this);
    assume !Seq#Equal(read($Heap, this, _module.AmortizedQueue.List), Seq#Empty(): Seq Box);
    havoc $Heap;
    assume (forall<alpha> $o: ref, $f: Field alpha ::
      { read($Heap, $o, $f) }
      $o != null && read(old($Heap), $o, alloc)
         ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
    assume $HeapSucc(old($Heap), $Heap);
    havoc r#0;
    assume {:captureState "Problem5-DoubleEndedQueue.dfy(72,35): post-state"} true;
    assume r#0 != null;
    assert r#0 != null;
    assume _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0);
    assume _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, r#0);
    assert r#0 != null;
    assert 0 <= LitInt(1)
       && LitInt(1) <= Seq#Length(read($Heap, this, _module.AmortizedQueue.List));
    assume Seq#Equal(read($Heap, r#0, _module.AmortizedQueue.List),
      Seq#Drop(read($Heap, this, _module.AmortizedQueue.List), LitInt(1)));
}



procedure Call$$_module.AmortizedQueue.Tail(_module.AmortizedQueue$T: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.AmortizedQueue(_module.AmortizedQueue$T))
         && $IsAlloc(this, Tclass._module.AmortizedQueue(_module.AmortizedQueue$T), $Heap))
   returns (r#0: ref
       where $Is(r#0, Tclass._module.AmortizedQueue(_module.AmortizedQueue$T))
         && $IsAlloc(r#0, Tclass._module.AmortizedQueue(_module.AmortizedQueue$T), $Heap));
  // user-defined preconditions
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || read($Heap, this, _module.AmortizedQueue.Repr)[$Box(this)];
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || read($Heap, this, _module.AmortizedQueue.front) != null;
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || read($Heap, this, _module.AmortizedQueue.Repr)[$Box(read($Heap, this, _module.AmortizedQueue.front))];
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || Set#Subset(read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.Repr),
        read($Heap, this, _module.AmortizedQueue.Repr));
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.front))
           || read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.Repr)[$Box(read($Heap, this, _module.AmortizedQueue.front))]);
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.front))
           || LitInt(0)
             <= read($Heap,
              read($Heap, this, _module.AmortizedQueue.front),
              _module.LinkedList.length));
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.front))
           || read($Heap,
              read($Heap, this, _module.AmortizedQueue.front),
              _module.LinkedList.length)
             == Seq#Length(read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.List)));
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.front))
           || (read($Heap,
                read($Heap, this, _module.AmortizedQueue.front),
                _module.LinkedList.length)
               == LitInt(0)
             ==> Seq#Equal(read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.List),
              Seq#Empty(): Seq Box)));
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.front))
           || (read($Heap,
                read($Heap, this, _module.AmortizedQueue.front),
                _module.LinkedList.length)
               == LitInt(0)
             ==> read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.tail)
               == null));
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.front))
           || (read($Heap,
                read($Heap, this, _module.AmortizedQueue.front),
                _module.LinkedList.length)
               != 0
             ==> read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.tail)
               != null));
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.front))
           || (read($Heap,
                read($Heap, this, _module.AmortizedQueue.front),
                _module.LinkedList.length)
               != 0
             ==> read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.Repr)[$Box(read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.tail))]));
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.front))
           || (read($Heap,
                read($Heap, this, _module.AmortizedQueue.front),
                _module.LinkedList.length)
               != 0
             ==> Set#Subset(read($Heap,
                read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.tail),
                _module.LinkedList.Repr),
              read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.Repr))));
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.front))
           || (read($Heap,
                read($Heap, this, _module.AmortizedQueue.front),
                _module.LinkedList.length)
               != 0
             ==> !read($Heap,
              read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.tail),
              _module.LinkedList.Repr)[$Box(read($Heap, this, _module.AmortizedQueue.front))]));
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.front))
           || (read($Heap,
                read($Heap, this, _module.AmortizedQueue.front),
                _module.LinkedList.length)
               != 0
             ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
              $LS($LS($LZ)),
              $Heap,
              read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.tail))));
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.front))
           || (read($Heap,
                read($Heap, this, _module.AmortizedQueue.front),
                _module.LinkedList.length)
               != 0
             ==> Seq#Equal(read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.List),
              Seq#Append(Seq#Build(Seq#Empty(): Seq Box,
                  read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.head)),
                read($Heap,
                  read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.tail),
                  _module.LinkedList.List)))));
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.front))
           || (read($Heap,
                read($Heap, this, _module.AmortizedQueue.front),
                _module.LinkedList.length)
               != 0
             ==> read($Heap,
                read($Heap, this, _module.AmortizedQueue.front),
                _module.LinkedList.length)
               == read($Heap,
                  read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.tail),
                  _module.LinkedList.length)
                 + 1));
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || read($Heap, this, _module.AmortizedQueue.rear) != null;
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || read($Heap, this, _module.AmortizedQueue.Repr)[$Box(read($Heap, this, _module.AmortizedQueue.rear))];
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || Set#Subset(read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.Repr),
        read($Heap, this, _module.AmortizedQueue.Repr));
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.rear))
           || read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.Repr)[$Box(read($Heap, this, _module.AmortizedQueue.rear))]);
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.rear))
           || LitInt(0)
             <= read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.length));
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.rear))
           || read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.length)
             == Seq#Length(read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.List)));
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.rear))
           || (read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.length)
               == LitInt(0)
             ==> Seq#Equal(read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.List),
              Seq#Empty(): Seq Box)));
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.rear))
           || (read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.length)
               == LitInt(0)
             ==> read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.tail)
               == null));
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.rear))
           || (read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.length)
               != 0
             ==> read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.tail)
               != null));
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.rear))
           || (read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.length)
               != 0
             ==> read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.Repr)[$Box(read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.tail))]));
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.rear))
           || (read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.length)
               != 0
             ==> Set#Subset(read($Heap,
                read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.tail),
                _module.LinkedList.Repr),
              read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.Repr))));
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.rear))
           || (read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.length)
               != 0
             ==> !read($Heap,
              read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.tail),
              _module.LinkedList.Repr)[$Box(read($Heap, this, _module.AmortizedQueue.rear))]));
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.rear))
           || (read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.length)
               != 0
             ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
              $LS($LS($LZ)),
              $Heap,
              read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.tail))));
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.rear))
           || (read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.length)
               != 0
             ==> Seq#Equal(read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.List),
              Seq#Append(Seq#Build(Seq#Empty(): Seq Box,
                  read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.head)),
                read($Heap,
                  read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.tail),
                  _module.LinkedList.List)))));
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.rear))
           || (read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.length)
               != 0
             ==> read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.length)
               == read($Heap,
                  read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.tail),
                  _module.LinkedList.length)
                 + 1));
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || Seq#Length(read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.List))
         <= Seq#Length(read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.List));
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || Seq#Equal(read($Heap, this, _module.AmortizedQueue.List),
        Seq#Append(read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.List),
          _module.LinkedList.ReverseSeq(_module.AmortizedQueue$T,
            $LS($LS($LZ)),
            read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.List))));
  requires !Seq#Equal(read($Heap, this, _module.AmortizedQueue.List), Seq#Empty(): Seq Box);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures r#0 != null
     ==> _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0);
  ensures r#0 != null;
  free ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0)
     &&
    _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, r#0)
     &&
    read($Heap, r#0, _module.AmortizedQueue.Repr)[$Box(r#0)]
     && read($Heap, r#0, _module.AmortizedQueue.front) != null
     && read($Heap, r#0, _module.AmortizedQueue.Repr)[$Box(read($Heap, r#0, _module.AmortizedQueue.front))]
     && Set#Subset(read($Heap, read($Heap, r#0, _module.AmortizedQueue.front), _module.LinkedList.Repr),
      read($Heap, r#0, _module.AmortizedQueue.Repr))
     && _module.LinkedList.Valid(_module.AmortizedQueue$T,
      $LS($LZ),
      $Heap,
      read($Heap, r#0, _module.AmortizedQueue.front))
     && read($Heap, r#0, _module.AmortizedQueue.rear) != null
     && read($Heap, r#0, _module.AmortizedQueue.Repr)[$Box(read($Heap, r#0, _module.AmortizedQueue.rear))]
     && Set#Subset(read($Heap, read($Heap, r#0, _module.AmortizedQueue.rear), _module.LinkedList.Repr),
      read($Heap, r#0, _module.AmortizedQueue.Repr))
     && _module.LinkedList.Valid(_module.AmortizedQueue$T,
      $LS($LZ),
      $Heap,
      read($Heap, r#0, _module.AmortizedQueue.rear))
     && Seq#Length(read($Heap, read($Heap, r#0, _module.AmortizedQueue.rear), _module.LinkedList.List))
       <= Seq#Length(read($Heap, read($Heap, r#0, _module.AmortizedQueue.front), _module.LinkedList.List))
     && Seq#Equal(read($Heap, r#0, _module.AmortizedQueue.List),
      Seq#Append(read($Heap, read($Heap, r#0, _module.AmortizedQueue.front), _module.LinkedList.List),
        _module.LinkedList.ReverseSeq(_module.AmortizedQueue$T,
          $LS($LZ),
          read($Heap, read($Heap, r#0, _module.AmortizedQueue.rear), _module.LinkedList.List))));
  ensures Seq#Equal(read($Heap, r#0, _module.AmortizedQueue.List),
    Seq#Drop(read($Heap, this, _module.AmortizedQueue.List), LitInt(1)));
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.AmortizedQueue.Tail(_module.AmortizedQueue$T: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.AmortizedQueue(_module.AmortizedQueue$T))
         && $IsAlloc(this, Tclass._module.AmortizedQueue(_module.AmortizedQueue$T), $Heap))
   returns (r#0: ref
       where $Is(r#0, Tclass._module.AmortizedQueue(_module.AmortizedQueue$T))
         && $IsAlloc(r#0, Tclass._module.AmortizedQueue(_module.AmortizedQueue$T), $Heap),
    $_reverifyPost: bool);
  free requires 10 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     &&
    _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
     &&
    read($Heap, this, _module.AmortizedQueue.Repr)[$Box(this)]
     && read($Heap, this, _module.AmortizedQueue.front) != null
     && read($Heap, this, _module.AmortizedQueue.Repr)[$Box(read($Heap, this, _module.AmortizedQueue.front))]
     && Set#Subset(read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.Repr),
      read($Heap, this, _module.AmortizedQueue.Repr))
     && _module.LinkedList.Valid(_module.AmortizedQueue$T,
      $LS($LZ),
      $Heap,
      read($Heap, this, _module.AmortizedQueue.front))
     && read($Heap, this, _module.AmortizedQueue.rear) != null
     && read($Heap, this, _module.AmortizedQueue.Repr)[$Box(read($Heap, this, _module.AmortizedQueue.rear))]
     && Set#Subset(read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.Repr),
      read($Heap, this, _module.AmortizedQueue.Repr))
     && _module.LinkedList.Valid(_module.AmortizedQueue$T,
      $LS($LZ),
      $Heap,
      read($Heap, this, _module.AmortizedQueue.rear))
     && Seq#Length(read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.List))
       <= Seq#Length(read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.List))
     && Seq#Equal(read($Heap, this, _module.AmortizedQueue.List),
      Seq#Append(read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.List),
        _module.LinkedList.ReverseSeq(_module.AmortizedQueue$T,
          $LS($LZ),
          read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.List))));
  requires !Seq#Equal(read($Heap, this, _module.AmortizedQueue.List), Seq#Empty(): Seq Box);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures r#0 != null
     ==> _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0);
  ensures r#0 != null;
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, r#0)
       || read($Heap, r#0, _module.AmortizedQueue.Repr)[$Box(r#0)];
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, r#0)
       || read($Heap, r#0, _module.AmortizedQueue.front) != null;
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, r#0)
       || read($Heap, r#0, _module.AmortizedQueue.Repr)[$Box(read($Heap, r#0, _module.AmortizedQueue.front))];
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, r#0)
       || Set#Subset(read($Heap, read($Heap, r#0, _module.AmortizedQueue.front), _module.LinkedList.Repr),
        read($Heap, r#0, _module.AmortizedQueue.Repr));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, r#0)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, r#0, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, r#0, _module.AmortizedQueue.front))
           || read($Heap, read($Heap, r#0, _module.AmortizedQueue.front), _module.LinkedList.Repr)[$Box(read($Heap, r#0, _module.AmortizedQueue.front))]);
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, r#0)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, r#0, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, r#0, _module.AmortizedQueue.front))
           || LitInt(0)
             <= read($Heap, read($Heap, r#0, _module.AmortizedQueue.front), _module.LinkedList.length));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, r#0)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, r#0, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, r#0, _module.AmortizedQueue.front))
           || read($Heap, read($Heap, r#0, _module.AmortizedQueue.front), _module.LinkedList.length)
             == Seq#Length(read($Heap, read($Heap, r#0, _module.AmortizedQueue.front), _module.LinkedList.List)));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, r#0)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, r#0, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, r#0, _module.AmortizedQueue.front))
           || (read($Heap, read($Heap, r#0, _module.AmortizedQueue.front), _module.LinkedList.length)
               == LitInt(0)
             ==> Seq#Equal(read($Heap, read($Heap, r#0, _module.AmortizedQueue.front), _module.LinkedList.List),
              Seq#Empty(): Seq Box)));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, r#0)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, r#0, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, r#0, _module.AmortizedQueue.front))
           || (read($Heap, read($Heap, r#0, _module.AmortizedQueue.front), _module.LinkedList.length)
               == LitInt(0)
             ==> read($Heap, read($Heap, r#0, _module.AmortizedQueue.front), _module.LinkedList.tail)
               == null));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, r#0)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, r#0, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, r#0, _module.AmortizedQueue.front))
           || (read($Heap, read($Heap, r#0, _module.AmortizedQueue.front), _module.LinkedList.length)
               != 0
             ==> read($Heap, read($Heap, r#0, _module.AmortizedQueue.front), _module.LinkedList.tail)
               != null));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, r#0)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, r#0, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, r#0, _module.AmortizedQueue.front))
           || (read($Heap, read($Heap, r#0, _module.AmortizedQueue.front), _module.LinkedList.length)
               != 0
             ==> read($Heap, read($Heap, r#0, _module.AmortizedQueue.front), _module.LinkedList.Repr)[$Box(read($Heap, read($Heap, r#0, _module.AmortizedQueue.front), _module.LinkedList.tail))]));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, r#0)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, r#0, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, r#0, _module.AmortizedQueue.front))
           || (read($Heap, read($Heap, r#0, _module.AmortizedQueue.front), _module.LinkedList.length)
               != 0
             ==> Set#Subset(read($Heap,
                read($Heap, read($Heap, r#0, _module.AmortizedQueue.front), _module.LinkedList.tail),
                _module.LinkedList.Repr),
              read($Heap, read($Heap, r#0, _module.AmortizedQueue.front), _module.LinkedList.Repr))));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, r#0)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, r#0, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, r#0, _module.AmortizedQueue.front))
           || (read($Heap, read($Heap, r#0, _module.AmortizedQueue.front), _module.LinkedList.length)
               != 0
             ==> !read($Heap,
              read($Heap, read($Heap, r#0, _module.AmortizedQueue.front), _module.LinkedList.tail),
              _module.LinkedList.Repr)[$Box(read($Heap, r#0, _module.AmortizedQueue.front))]));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, r#0)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, r#0, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, r#0, _module.AmortizedQueue.front))
           || (read($Heap, read($Heap, r#0, _module.AmortizedQueue.front), _module.LinkedList.length)
               != 0
             ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
              $LS($LS($LZ)),
              $Heap,
              read($Heap, read($Heap, r#0, _module.AmortizedQueue.front), _module.LinkedList.tail))));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, r#0)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, r#0, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, r#0, _module.AmortizedQueue.front))
           || (read($Heap, read($Heap, r#0, _module.AmortizedQueue.front), _module.LinkedList.length)
               != 0
             ==> Seq#Equal(read($Heap, read($Heap, r#0, _module.AmortizedQueue.front), _module.LinkedList.List),
              Seq#Append(Seq#Build(Seq#Empty(): Seq Box,
                  read($Heap, read($Heap, r#0, _module.AmortizedQueue.front), _module.LinkedList.head)),
                read($Heap,
                  read($Heap, read($Heap, r#0, _module.AmortizedQueue.front), _module.LinkedList.tail),
                  _module.LinkedList.List)))));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, r#0)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, r#0, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, r#0, _module.AmortizedQueue.front))
           || (read($Heap, read($Heap, r#0, _module.AmortizedQueue.front), _module.LinkedList.length)
               != 0
             ==> read($Heap, read($Heap, r#0, _module.AmortizedQueue.front), _module.LinkedList.length)
               == read($Heap,
                  read($Heap, read($Heap, r#0, _module.AmortizedQueue.front), _module.LinkedList.tail),
                  _module.LinkedList.length)
                 + 1));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, r#0)
       || read($Heap, r#0, _module.AmortizedQueue.rear) != null;
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, r#0)
       || read($Heap, r#0, _module.AmortizedQueue.Repr)[$Box(read($Heap, r#0, _module.AmortizedQueue.rear))];
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, r#0)
       || Set#Subset(read($Heap, read($Heap, r#0, _module.AmortizedQueue.rear), _module.LinkedList.Repr),
        read($Heap, r#0, _module.AmortizedQueue.Repr));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, r#0)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, r#0, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, r#0, _module.AmortizedQueue.rear))
           || read($Heap, read($Heap, r#0, _module.AmortizedQueue.rear), _module.LinkedList.Repr)[$Box(read($Heap, r#0, _module.AmortizedQueue.rear))]);
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, r#0)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, r#0, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, r#0, _module.AmortizedQueue.rear))
           || LitInt(0)
             <= read($Heap, read($Heap, r#0, _module.AmortizedQueue.rear), _module.LinkedList.length));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, r#0)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, r#0, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, r#0, _module.AmortizedQueue.rear))
           || read($Heap, read($Heap, r#0, _module.AmortizedQueue.rear), _module.LinkedList.length)
             == Seq#Length(read($Heap, read($Heap, r#0, _module.AmortizedQueue.rear), _module.LinkedList.List)));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, r#0)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, r#0, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, r#0, _module.AmortizedQueue.rear))
           || (read($Heap, read($Heap, r#0, _module.AmortizedQueue.rear), _module.LinkedList.length)
               == LitInt(0)
             ==> Seq#Equal(read($Heap, read($Heap, r#0, _module.AmortizedQueue.rear), _module.LinkedList.List),
              Seq#Empty(): Seq Box)));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, r#0)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, r#0, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, r#0, _module.AmortizedQueue.rear))
           || (read($Heap, read($Heap, r#0, _module.AmortizedQueue.rear), _module.LinkedList.length)
               == LitInt(0)
             ==> read($Heap, read($Heap, r#0, _module.AmortizedQueue.rear), _module.LinkedList.tail)
               == null));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, r#0)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, r#0, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, r#0, _module.AmortizedQueue.rear))
           || (read($Heap, read($Heap, r#0, _module.AmortizedQueue.rear), _module.LinkedList.length)
               != 0
             ==> read($Heap, read($Heap, r#0, _module.AmortizedQueue.rear), _module.LinkedList.tail)
               != null));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, r#0)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, r#0, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, r#0, _module.AmortizedQueue.rear))
           || (read($Heap, read($Heap, r#0, _module.AmortizedQueue.rear), _module.LinkedList.length)
               != 0
             ==> read($Heap, read($Heap, r#0, _module.AmortizedQueue.rear), _module.LinkedList.Repr)[$Box(read($Heap, read($Heap, r#0, _module.AmortizedQueue.rear), _module.LinkedList.tail))]));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, r#0)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, r#0, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, r#0, _module.AmortizedQueue.rear))
           || (read($Heap, read($Heap, r#0, _module.AmortizedQueue.rear), _module.LinkedList.length)
               != 0
             ==> Set#Subset(read($Heap,
                read($Heap, read($Heap, r#0, _module.AmortizedQueue.rear), _module.LinkedList.tail),
                _module.LinkedList.Repr),
              read($Heap, read($Heap, r#0, _module.AmortizedQueue.rear), _module.LinkedList.Repr))));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, r#0)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, r#0, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, r#0, _module.AmortizedQueue.rear))
           || (read($Heap, read($Heap, r#0, _module.AmortizedQueue.rear), _module.LinkedList.length)
               != 0
             ==> !read($Heap,
              read($Heap, read($Heap, r#0, _module.AmortizedQueue.rear), _module.LinkedList.tail),
              _module.LinkedList.Repr)[$Box(read($Heap, r#0, _module.AmortizedQueue.rear))]));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, r#0)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, r#0, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, r#0, _module.AmortizedQueue.rear))
           || (read($Heap, read($Heap, r#0, _module.AmortizedQueue.rear), _module.LinkedList.length)
               != 0
             ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
              $LS($LS($LZ)),
              $Heap,
              read($Heap, read($Heap, r#0, _module.AmortizedQueue.rear), _module.LinkedList.tail))));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, r#0)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, r#0, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, r#0, _module.AmortizedQueue.rear))
           || (read($Heap, read($Heap, r#0, _module.AmortizedQueue.rear), _module.LinkedList.length)
               != 0
             ==> Seq#Equal(read($Heap, read($Heap, r#0, _module.AmortizedQueue.rear), _module.LinkedList.List),
              Seq#Append(Seq#Build(Seq#Empty(): Seq Box,
                  read($Heap, read($Heap, r#0, _module.AmortizedQueue.rear), _module.LinkedList.head)),
                read($Heap,
                  read($Heap, read($Heap, r#0, _module.AmortizedQueue.rear), _module.LinkedList.tail),
                  _module.LinkedList.List)))));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, r#0)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, r#0, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, r#0, _module.AmortizedQueue.rear))
           || (read($Heap, read($Heap, r#0, _module.AmortizedQueue.rear), _module.LinkedList.length)
               != 0
             ==> read($Heap, read($Heap, r#0, _module.AmortizedQueue.rear), _module.LinkedList.length)
               == read($Heap,
                  read($Heap, read($Heap, r#0, _module.AmortizedQueue.rear), _module.LinkedList.tail),
                  _module.LinkedList.length)
                 + 1));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, r#0)
       || Seq#Length(read($Heap, read($Heap, r#0, _module.AmortizedQueue.rear), _module.LinkedList.List))
         <= Seq#Length(read($Heap, read($Heap, r#0, _module.AmortizedQueue.front), _module.LinkedList.List));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, r#0)
       || Seq#Equal(read($Heap, r#0, _module.AmortizedQueue.List),
        Seq#Append(read($Heap, read($Heap, r#0, _module.AmortizedQueue.front), _module.LinkedList.List),
          _module.LinkedList.ReverseSeq(_module.AmortizedQueue$T,
            $LS($LS($LZ)),
            read($Heap, read($Heap, r#0, _module.AmortizedQueue.rear), _module.LinkedList.List))));
  ensures Seq#Equal(read($Heap, r#0, _module.AmortizedQueue.List),
    Seq#Drop(read($Heap, this, _module.AmortizedQueue.List), LitInt(1)));
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.AmortizedQueue.Tail(_module.AmortizedQueue$T: Ty, this: ref)
   returns (r#0: ref, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $nw: ref;
  var f##0: ref;
  var r##0: ref;

    // AddMethodImpl: Tail, Impl$$_module.AmortizedQueue.Tail
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "Problem5-DoubleEndedQueue.dfy(73,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- Problem5-DoubleEndedQueue.dfy(74,7)
    assume true;
    havoc $nw;
    assume $nw != null
       &&
      !read($Heap, $nw, alloc)
       && dtype($nw) == Tclass._module.AmortizedQueue(_module.AmortizedQueue$T);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    // ----- init call statement ----- Problem5-DoubleEndedQueue.dfy(74,32)
    // TrCallStmt: Before ProcessCallStmt
    assert read($Heap, this, _module.AmortizedQueue.front) != null;
    assume true;
    // ProcessCallStmt: CheckSubrange
    f##0 := read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.tail);
    assume true;
    // ProcessCallStmt: CheckSubrange
    r##0 := read($Heap, this, _module.AmortizedQueue.rear);
    assert (forall<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) && $o == $nw ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.AmortizedQueue.InitFromPieces(_module.AmortizedQueue$T, $nw, f##0, r##0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "Problem5-DoubleEndedQueue.dfy(74,63)"} true;
    r#0 := $nw;
    assume {:captureState "Problem5-DoubleEndedQueue.dfy(74,63)"} true;
}



procedure CheckWellformed$$_module.AmortizedQueue.Enqueue(_module.AmortizedQueue$T: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.AmortizedQueue(_module.AmortizedQueue$T))
         && $IsAlloc(this, Tclass._module.AmortizedQueue(_module.AmortizedQueue$T), $Heap),
    item#0: Box
       where $IsBox(item#0, _module.AmortizedQueue$T)
         && $IsAllocBox(item#0, _module.AmortizedQueue$T, $Heap))
   returns (r#0: ref
       where $Is(r#0, Tclass._module.AmortizedQueue(_module.AmortizedQueue$T))
         && $IsAlloc(r#0, Tclass._module.AmortizedQueue(_module.AmortizedQueue$T), $Heap));
  free requires 11 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.AmortizedQueue.Enqueue(_module.AmortizedQueue$T: Ty, this: ref, item#0: Box) returns (r#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: Enqueue, CheckWellformed$$_module.AmortizedQueue.Enqueue
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "Problem5-DoubleEndedQueue.dfy(77,9): initial state"} true;
    assume _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this);
    assume _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this);
    havoc $Heap;
    assume (forall<alpha> $o: ref, $f: Field alpha ::
      { read($Heap, $o, $f) }
      $o != null && read(old($Heap), $o, alloc)
         ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
    assume $HeapSucc(old($Heap), $Heap);
    havoc r#0;
    assume {:captureState "Problem5-DoubleEndedQueue.dfy(79,35): post-state"} true;
    assume r#0 != null;
    assert r#0 != null;
    assume _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0);
    assume _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, r#0);
    assert r#0 != null;
    assume Seq#Equal(read($Heap, r#0, _module.AmortizedQueue.List),
      Seq#Append(read($Heap, this, _module.AmortizedQueue.List),
        Seq#Build(Seq#Empty(): Seq Box, item#0)));
}



procedure Call$$_module.AmortizedQueue.Enqueue(_module.AmortizedQueue$T: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.AmortizedQueue(_module.AmortizedQueue$T))
         && $IsAlloc(this, Tclass._module.AmortizedQueue(_module.AmortizedQueue$T), $Heap),
    item#0: Box
       where $IsBox(item#0, _module.AmortizedQueue$T)
         && $IsAllocBox(item#0, _module.AmortizedQueue$T, $Heap))
   returns (r#0: ref
       where $Is(r#0, Tclass._module.AmortizedQueue(_module.AmortizedQueue$T))
         && $IsAlloc(r#0, Tclass._module.AmortizedQueue(_module.AmortizedQueue$T), $Heap));
  // user-defined preconditions
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || read($Heap, this, _module.AmortizedQueue.Repr)[$Box(this)];
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || read($Heap, this, _module.AmortizedQueue.front) != null;
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || read($Heap, this, _module.AmortizedQueue.Repr)[$Box(read($Heap, this, _module.AmortizedQueue.front))];
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || Set#Subset(read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.Repr),
        read($Heap, this, _module.AmortizedQueue.Repr));
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.front))
           || read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.Repr)[$Box(read($Heap, this, _module.AmortizedQueue.front))]);
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.front))
           || LitInt(0)
             <= read($Heap,
              read($Heap, this, _module.AmortizedQueue.front),
              _module.LinkedList.length));
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.front))
           || read($Heap,
              read($Heap, this, _module.AmortizedQueue.front),
              _module.LinkedList.length)
             == Seq#Length(read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.List)));
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.front))
           || (read($Heap,
                read($Heap, this, _module.AmortizedQueue.front),
                _module.LinkedList.length)
               == LitInt(0)
             ==> Seq#Equal(read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.List),
              Seq#Empty(): Seq Box)));
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.front))
           || (read($Heap,
                read($Heap, this, _module.AmortizedQueue.front),
                _module.LinkedList.length)
               == LitInt(0)
             ==> read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.tail)
               == null));
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.front))
           || (read($Heap,
                read($Heap, this, _module.AmortizedQueue.front),
                _module.LinkedList.length)
               != 0
             ==> read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.tail)
               != null));
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.front))
           || (read($Heap,
                read($Heap, this, _module.AmortizedQueue.front),
                _module.LinkedList.length)
               != 0
             ==> read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.Repr)[$Box(read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.tail))]));
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.front))
           || (read($Heap,
                read($Heap, this, _module.AmortizedQueue.front),
                _module.LinkedList.length)
               != 0
             ==> Set#Subset(read($Heap,
                read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.tail),
                _module.LinkedList.Repr),
              read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.Repr))));
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.front))
           || (read($Heap,
                read($Heap, this, _module.AmortizedQueue.front),
                _module.LinkedList.length)
               != 0
             ==> !read($Heap,
              read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.tail),
              _module.LinkedList.Repr)[$Box(read($Heap, this, _module.AmortizedQueue.front))]));
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.front))
           || (read($Heap,
                read($Heap, this, _module.AmortizedQueue.front),
                _module.LinkedList.length)
               != 0
             ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
              $LS($LS($LZ)),
              $Heap,
              read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.tail))));
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.front))
           || (read($Heap,
                read($Heap, this, _module.AmortizedQueue.front),
                _module.LinkedList.length)
               != 0
             ==> Seq#Equal(read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.List),
              Seq#Append(Seq#Build(Seq#Empty(): Seq Box,
                  read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.head)),
                read($Heap,
                  read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.tail),
                  _module.LinkedList.List)))));
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.front))
           || (read($Heap,
                read($Heap, this, _module.AmortizedQueue.front),
                _module.LinkedList.length)
               != 0
             ==> read($Heap,
                read($Heap, this, _module.AmortizedQueue.front),
                _module.LinkedList.length)
               == read($Heap,
                  read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.tail),
                  _module.LinkedList.length)
                 + 1));
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || read($Heap, this, _module.AmortizedQueue.rear) != null;
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || read($Heap, this, _module.AmortizedQueue.Repr)[$Box(read($Heap, this, _module.AmortizedQueue.rear))];
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || Set#Subset(read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.Repr),
        read($Heap, this, _module.AmortizedQueue.Repr));
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.rear))
           || read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.Repr)[$Box(read($Heap, this, _module.AmortizedQueue.rear))]);
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.rear))
           || LitInt(0)
             <= read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.length));
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.rear))
           || read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.length)
             == Seq#Length(read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.List)));
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.rear))
           || (read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.length)
               == LitInt(0)
             ==> Seq#Equal(read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.List),
              Seq#Empty(): Seq Box)));
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.rear))
           || (read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.length)
               == LitInt(0)
             ==> read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.tail)
               == null));
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.rear))
           || (read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.length)
               != 0
             ==> read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.tail)
               != null));
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.rear))
           || (read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.length)
               != 0
             ==> read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.Repr)[$Box(read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.tail))]));
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.rear))
           || (read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.length)
               != 0
             ==> Set#Subset(read($Heap,
                read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.tail),
                _module.LinkedList.Repr),
              read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.Repr))));
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.rear))
           || (read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.length)
               != 0
             ==> !read($Heap,
              read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.tail),
              _module.LinkedList.Repr)[$Box(read($Heap, this, _module.AmortizedQueue.rear))]));
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.rear))
           || (read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.length)
               != 0
             ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
              $LS($LS($LZ)),
              $Heap,
              read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.tail))));
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.rear))
           || (read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.length)
               != 0
             ==> Seq#Equal(read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.List),
              Seq#Append(Seq#Build(Seq#Empty(): Seq Box,
                  read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.head)),
                read($Heap,
                  read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.tail),
                  _module.LinkedList.List)))));
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, this, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.AmortizedQueue.rear))
           || (read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.length)
               != 0
             ==> read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.length)
               == read($Heap,
                  read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.tail),
                  _module.LinkedList.length)
                 + 1));
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || Seq#Length(read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.List))
         <= Seq#Length(read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.List));
  requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
       || Seq#Equal(read($Heap, this, _module.AmortizedQueue.List),
        Seq#Append(read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.List),
          _module.LinkedList.ReverseSeq(_module.AmortizedQueue$T,
            $LS($LS($LZ)),
            read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.List))));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures r#0 != null
     ==> _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0);
  ensures r#0 != null;
  free ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0)
     &&
    _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, r#0)
     &&
    read($Heap, r#0, _module.AmortizedQueue.Repr)[$Box(r#0)]
     && read($Heap, r#0, _module.AmortizedQueue.front) != null
     && read($Heap, r#0, _module.AmortizedQueue.Repr)[$Box(read($Heap, r#0, _module.AmortizedQueue.front))]
     && Set#Subset(read($Heap, read($Heap, r#0, _module.AmortizedQueue.front), _module.LinkedList.Repr),
      read($Heap, r#0, _module.AmortizedQueue.Repr))
     && _module.LinkedList.Valid(_module.AmortizedQueue$T,
      $LS($LZ),
      $Heap,
      read($Heap, r#0, _module.AmortizedQueue.front))
     && read($Heap, r#0, _module.AmortizedQueue.rear) != null
     && read($Heap, r#0, _module.AmortizedQueue.Repr)[$Box(read($Heap, r#0, _module.AmortizedQueue.rear))]
     && Set#Subset(read($Heap, read($Heap, r#0, _module.AmortizedQueue.rear), _module.LinkedList.Repr),
      read($Heap, r#0, _module.AmortizedQueue.Repr))
     && _module.LinkedList.Valid(_module.AmortizedQueue$T,
      $LS($LZ),
      $Heap,
      read($Heap, r#0, _module.AmortizedQueue.rear))
     && Seq#Length(read($Heap, read($Heap, r#0, _module.AmortizedQueue.rear), _module.LinkedList.List))
       <= Seq#Length(read($Heap, read($Heap, r#0, _module.AmortizedQueue.front), _module.LinkedList.List))
     && Seq#Equal(read($Heap, r#0, _module.AmortizedQueue.List),
      Seq#Append(read($Heap, read($Heap, r#0, _module.AmortizedQueue.front), _module.LinkedList.List),
        _module.LinkedList.ReverseSeq(_module.AmortizedQueue$T,
          $LS($LZ),
          read($Heap, read($Heap, r#0, _module.AmortizedQueue.rear), _module.LinkedList.List))));
  ensures Seq#Equal(read($Heap, r#0, _module.AmortizedQueue.List),
    Seq#Append(read($Heap, this, _module.AmortizedQueue.List),
      Seq#Build(Seq#Empty(): Seq Box, item#0)));
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.AmortizedQueue.Enqueue(_module.AmortizedQueue$T: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.AmortizedQueue(_module.AmortizedQueue$T))
         && $IsAlloc(this, Tclass._module.AmortizedQueue(_module.AmortizedQueue$T), $Heap),
    item#0: Box
       where $IsBox(item#0, _module.AmortizedQueue$T)
         && $IsAllocBox(item#0, _module.AmortizedQueue$T, $Heap))
   returns (r#0: ref
       where $Is(r#0, Tclass._module.AmortizedQueue(_module.AmortizedQueue$T))
         && $IsAlloc(r#0, Tclass._module.AmortizedQueue(_module.AmortizedQueue$T), $Heap),
    $_reverifyPost: bool);
  free requires 11 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, this)
     &&
    _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, this)
     &&
    read($Heap, this, _module.AmortizedQueue.Repr)[$Box(this)]
     && read($Heap, this, _module.AmortizedQueue.front) != null
     && read($Heap, this, _module.AmortizedQueue.Repr)[$Box(read($Heap, this, _module.AmortizedQueue.front))]
     && Set#Subset(read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.Repr),
      read($Heap, this, _module.AmortizedQueue.Repr))
     && _module.LinkedList.Valid(_module.AmortizedQueue$T,
      $LS($LZ),
      $Heap,
      read($Heap, this, _module.AmortizedQueue.front))
     && read($Heap, this, _module.AmortizedQueue.rear) != null
     && read($Heap, this, _module.AmortizedQueue.Repr)[$Box(read($Heap, this, _module.AmortizedQueue.rear))]
     && Set#Subset(read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.Repr),
      read($Heap, this, _module.AmortizedQueue.Repr))
     && _module.LinkedList.Valid(_module.AmortizedQueue$T,
      $LS($LZ),
      $Heap,
      read($Heap, this, _module.AmortizedQueue.rear))
     && Seq#Length(read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.List))
       <= Seq#Length(read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.List))
     && Seq#Equal(read($Heap, this, _module.AmortizedQueue.List),
      Seq#Append(read($Heap, read($Heap, this, _module.AmortizedQueue.front), _module.LinkedList.List),
        _module.LinkedList.ReverseSeq(_module.AmortizedQueue$T,
          $LS($LZ),
          read($Heap, read($Heap, this, _module.AmortizedQueue.rear), _module.LinkedList.List))));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures r#0 != null
     ==> _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0);
  ensures r#0 != null;
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, r#0)
       || read($Heap, r#0, _module.AmortizedQueue.Repr)[$Box(r#0)];
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, r#0)
       || read($Heap, r#0, _module.AmortizedQueue.front) != null;
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, r#0)
       || read($Heap, r#0, _module.AmortizedQueue.Repr)[$Box(read($Heap, r#0, _module.AmortizedQueue.front))];
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, r#0)
       || Set#Subset(read($Heap, read($Heap, r#0, _module.AmortizedQueue.front), _module.LinkedList.Repr),
        read($Heap, r#0, _module.AmortizedQueue.Repr));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, r#0)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, r#0, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, r#0, _module.AmortizedQueue.front))
           || read($Heap, read($Heap, r#0, _module.AmortizedQueue.front), _module.LinkedList.Repr)[$Box(read($Heap, r#0, _module.AmortizedQueue.front))]);
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, r#0)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, r#0, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, r#0, _module.AmortizedQueue.front))
           || LitInt(0)
             <= read($Heap, read($Heap, r#0, _module.AmortizedQueue.front), _module.LinkedList.length));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, r#0)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, r#0, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, r#0, _module.AmortizedQueue.front))
           || read($Heap, read($Heap, r#0, _module.AmortizedQueue.front), _module.LinkedList.length)
             == Seq#Length(read($Heap, read($Heap, r#0, _module.AmortizedQueue.front), _module.LinkedList.List)));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, r#0)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, r#0, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, r#0, _module.AmortizedQueue.front))
           || (read($Heap, read($Heap, r#0, _module.AmortizedQueue.front), _module.LinkedList.length)
               == LitInt(0)
             ==> Seq#Equal(read($Heap, read($Heap, r#0, _module.AmortizedQueue.front), _module.LinkedList.List),
              Seq#Empty(): Seq Box)));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, r#0)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, r#0, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, r#0, _module.AmortizedQueue.front))
           || (read($Heap, read($Heap, r#0, _module.AmortizedQueue.front), _module.LinkedList.length)
               == LitInt(0)
             ==> read($Heap, read($Heap, r#0, _module.AmortizedQueue.front), _module.LinkedList.tail)
               == null));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, r#0)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, r#0, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, r#0, _module.AmortizedQueue.front))
           || (read($Heap, read($Heap, r#0, _module.AmortizedQueue.front), _module.LinkedList.length)
               != 0
             ==> read($Heap, read($Heap, r#0, _module.AmortizedQueue.front), _module.LinkedList.tail)
               != null));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, r#0)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, r#0, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, r#0, _module.AmortizedQueue.front))
           || (read($Heap, read($Heap, r#0, _module.AmortizedQueue.front), _module.LinkedList.length)
               != 0
             ==> read($Heap, read($Heap, r#0, _module.AmortizedQueue.front), _module.LinkedList.Repr)[$Box(read($Heap, read($Heap, r#0, _module.AmortizedQueue.front), _module.LinkedList.tail))]));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, r#0)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, r#0, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, r#0, _module.AmortizedQueue.front))
           || (read($Heap, read($Heap, r#0, _module.AmortizedQueue.front), _module.LinkedList.length)
               != 0
             ==> Set#Subset(read($Heap,
                read($Heap, read($Heap, r#0, _module.AmortizedQueue.front), _module.LinkedList.tail),
                _module.LinkedList.Repr),
              read($Heap, read($Heap, r#0, _module.AmortizedQueue.front), _module.LinkedList.Repr))));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, r#0)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, r#0, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, r#0, _module.AmortizedQueue.front))
           || (read($Heap, read($Heap, r#0, _module.AmortizedQueue.front), _module.LinkedList.length)
               != 0
             ==> !read($Heap,
              read($Heap, read($Heap, r#0, _module.AmortizedQueue.front), _module.LinkedList.tail),
              _module.LinkedList.Repr)[$Box(read($Heap, r#0, _module.AmortizedQueue.front))]));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, r#0)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, r#0, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, r#0, _module.AmortizedQueue.front))
           || (read($Heap, read($Heap, r#0, _module.AmortizedQueue.front), _module.LinkedList.length)
               != 0
             ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
              $LS($LS($LZ)),
              $Heap,
              read($Heap, read($Heap, r#0, _module.AmortizedQueue.front), _module.LinkedList.tail))));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, r#0)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, r#0, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, r#0, _module.AmortizedQueue.front))
           || (read($Heap, read($Heap, r#0, _module.AmortizedQueue.front), _module.LinkedList.length)
               != 0
             ==> Seq#Equal(read($Heap, read($Heap, r#0, _module.AmortizedQueue.front), _module.LinkedList.List),
              Seq#Append(Seq#Build(Seq#Empty(): Seq Box,
                  read($Heap, read($Heap, r#0, _module.AmortizedQueue.front), _module.LinkedList.head)),
                read($Heap,
                  read($Heap, read($Heap, r#0, _module.AmortizedQueue.front), _module.LinkedList.tail),
                  _module.LinkedList.List)))));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, r#0)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, r#0, _module.AmortizedQueue.front))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, r#0, _module.AmortizedQueue.front))
           || (read($Heap, read($Heap, r#0, _module.AmortizedQueue.front), _module.LinkedList.length)
               != 0
             ==> read($Heap, read($Heap, r#0, _module.AmortizedQueue.front), _module.LinkedList.length)
               == read($Heap,
                  read($Heap, read($Heap, r#0, _module.AmortizedQueue.front), _module.LinkedList.tail),
                  _module.LinkedList.length)
                 + 1));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, r#0)
       || read($Heap, r#0, _module.AmortizedQueue.rear) != null;
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, r#0)
       || read($Heap, r#0, _module.AmortizedQueue.Repr)[$Box(read($Heap, r#0, _module.AmortizedQueue.rear))];
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, r#0)
       || Set#Subset(read($Heap, read($Heap, r#0, _module.AmortizedQueue.rear), _module.LinkedList.Repr),
        read($Heap, r#0, _module.AmortizedQueue.Repr));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, r#0)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, r#0, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, r#0, _module.AmortizedQueue.rear))
           || read($Heap, read($Heap, r#0, _module.AmortizedQueue.rear), _module.LinkedList.Repr)[$Box(read($Heap, r#0, _module.AmortizedQueue.rear))]);
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, r#0)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, r#0, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, r#0, _module.AmortizedQueue.rear))
           || LitInt(0)
             <= read($Heap, read($Heap, r#0, _module.AmortizedQueue.rear), _module.LinkedList.length));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, r#0)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, r#0, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, r#0, _module.AmortizedQueue.rear))
           || read($Heap, read($Heap, r#0, _module.AmortizedQueue.rear), _module.LinkedList.length)
             == Seq#Length(read($Heap, read($Heap, r#0, _module.AmortizedQueue.rear), _module.LinkedList.List)));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, r#0)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, r#0, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, r#0, _module.AmortizedQueue.rear))
           || (read($Heap, read($Heap, r#0, _module.AmortizedQueue.rear), _module.LinkedList.length)
               == LitInt(0)
             ==> Seq#Equal(read($Heap, read($Heap, r#0, _module.AmortizedQueue.rear), _module.LinkedList.List),
              Seq#Empty(): Seq Box)));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, r#0)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, r#0, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, r#0, _module.AmortizedQueue.rear))
           || (read($Heap, read($Heap, r#0, _module.AmortizedQueue.rear), _module.LinkedList.length)
               == LitInt(0)
             ==> read($Heap, read($Heap, r#0, _module.AmortizedQueue.rear), _module.LinkedList.tail)
               == null));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, r#0)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, r#0, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, r#0, _module.AmortizedQueue.rear))
           || (read($Heap, read($Heap, r#0, _module.AmortizedQueue.rear), _module.LinkedList.length)
               != 0
             ==> read($Heap, read($Heap, r#0, _module.AmortizedQueue.rear), _module.LinkedList.tail)
               != null));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, r#0)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, r#0, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, r#0, _module.AmortizedQueue.rear))
           || (read($Heap, read($Heap, r#0, _module.AmortizedQueue.rear), _module.LinkedList.length)
               != 0
             ==> read($Heap, read($Heap, r#0, _module.AmortizedQueue.rear), _module.LinkedList.Repr)[$Box(read($Heap, read($Heap, r#0, _module.AmortizedQueue.rear), _module.LinkedList.tail))]));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, r#0)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, r#0, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, r#0, _module.AmortizedQueue.rear))
           || (read($Heap, read($Heap, r#0, _module.AmortizedQueue.rear), _module.LinkedList.length)
               != 0
             ==> Set#Subset(read($Heap,
                read($Heap, read($Heap, r#0, _module.AmortizedQueue.rear), _module.LinkedList.tail),
                _module.LinkedList.Repr),
              read($Heap, read($Heap, r#0, _module.AmortizedQueue.rear), _module.LinkedList.Repr))));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, r#0)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, r#0, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, r#0, _module.AmortizedQueue.rear))
           || (read($Heap, read($Heap, r#0, _module.AmortizedQueue.rear), _module.LinkedList.length)
               != 0
             ==> !read($Heap,
              read($Heap, read($Heap, r#0, _module.AmortizedQueue.rear), _module.LinkedList.tail),
              _module.LinkedList.Repr)[$Box(read($Heap, r#0, _module.AmortizedQueue.rear))]));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, r#0)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, r#0, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, r#0, _module.AmortizedQueue.rear))
           || (read($Heap, read($Heap, r#0, _module.AmortizedQueue.rear), _module.LinkedList.length)
               != 0
             ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
              $LS($LS($LZ)),
              $Heap,
              read($Heap, read($Heap, r#0, _module.AmortizedQueue.rear), _module.LinkedList.tail))));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, r#0)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, r#0, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, r#0, _module.AmortizedQueue.rear))
           || (read($Heap, read($Heap, r#0, _module.AmortizedQueue.rear), _module.LinkedList.length)
               != 0
             ==> Seq#Equal(read($Heap, read($Heap, r#0, _module.AmortizedQueue.rear), _module.LinkedList.List),
              Seq#Append(Seq#Build(Seq#Empty(): Seq Box,
                  read($Heap, read($Heap, r#0, _module.AmortizedQueue.rear), _module.LinkedList.head)),
                read($Heap,
                  read($Heap, read($Heap, r#0, _module.AmortizedQueue.rear), _module.LinkedList.tail),
                  _module.LinkedList.List)))));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, r#0)
       || (_module.LinkedList.Valid#canCall(_module.AmortizedQueue$T, $Heap, read($Heap, r#0, _module.AmortizedQueue.rear))
         ==> _module.LinkedList.Valid(_module.AmortizedQueue$T,
            $LS($LZ),
            $Heap,
            read($Heap, r#0, _module.AmortizedQueue.rear))
           || (read($Heap, read($Heap, r#0, _module.AmortizedQueue.rear), _module.LinkedList.length)
               != 0
             ==> read($Heap, read($Heap, r#0, _module.AmortizedQueue.rear), _module.LinkedList.length)
               == read($Heap,
                  read($Heap, read($Heap, r#0, _module.AmortizedQueue.rear), _module.LinkedList.tail),
                  _module.LinkedList.length)
                 + 1));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, r#0)
       || Seq#Length(read($Heap, read($Heap, r#0, _module.AmortizedQueue.rear), _module.LinkedList.List))
         <= Seq#Length(read($Heap, read($Heap, r#0, _module.AmortizedQueue.front), _module.LinkedList.List));
  ensures _module.AmortizedQueue.Valid#canCall(_module.AmortizedQueue$T, $Heap, r#0)
     ==> _module.AmortizedQueue.Valid(_module.AmortizedQueue$T, $Heap, r#0)
       || Seq#Equal(read($Heap, r#0, _module.AmortizedQueue.List),
        Seq#Append(read($Heap, read($Heap, r#0, _module.AmortizedQueue.front), _module.LinkedList.List),
          _module.LinkedList.ReverseSeq(_module.AmortizedQueue$T,
            $LS($LS($LZ)),
            read($Heap, read($Heap, r#0, _module.AmortizedQueue.rear), _module.LinkedList.List))));
  ensures Seq#Equal(read($Heap, r#0, _module.AmortizedQueue.List),
    Seq#Append(read($Heap, this, _module.AmortizedQueue.List),
      Seq#Build(Seq#Empty(): Seq Box, item#0)));
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.AmortizedQueue.Enqueue(_module.AmortizedQueue$T: Ty, this: ref, item#0: Box)
   returns (r#0: ref, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var rr#0: ref
     where $Is(rr#0, Tclass._module.LinkedList(_module.AmortizedQueue$T))
       && $IsAlloc(rr#0, Tclass._module.LinkedList(_module.AmortizedQueue$T), $Heap);
  var $rhs##0: ref
     where $Is($rhs##0, Tclass._module.LinkedList(_module.AmortizedQueue$T))
       && $IsAlloc($rhs##0, Tclass._module.LinkedList(_module.AmortizedQueue$T), $Heap);
  var d##0: Box;
  var $nw: ref;
  var f##0: ref;
  var r##0: ref;

    // AddMethodImpl: Enqueue, Impl$$_module.AmortizedQueue.Enqueue
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "Problem5-DoubleEndedQueue.dfy(80,2): initial state"} true;
    $_reverifyPost := false;
    // ----- call statement ----- Problem5-DoubleEndedQueue.dfy(81,24)
    assume true;
    // TrCallStmt: Adding lhs Microsoft.Dafny.AutoGhostIdentifierExpr with type LinkedList<T>
    // TrCallStmt: Before ProcessCallStmt
    assert read($Heap, this, _module.AmortizedQueue.rear) != null;
    assume true;
    // ProcessCallStmt: CheckSubrange
    d##0 := item#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##0 := Call$$_module.LinkedList.Cons(_module.AmortizedQueue$T, read($Heap, this, _module.AmortizedQueue.rear), d##0);
    // TrCallStmt: After ProcessCallStmt
    rr#0 := $rhs##0;
    assume {:captureState "Problem5-DoubleEndedQueue.dfy(81,29)"} true;
    // ----- assignment statement ----- Problem5-DoubleEndedQueue.dfy(82,7)
    assume true;
    havoc $nw;
    assume $nw != null
       &&
      !read($Heap, $nw, alloc)
       && dtype($nw) == Tclass._module.AmortizedQueue(_module.AmortizedQueue$T);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    // ----- init call statement ----- Problem5-DoubleEndedQueue.dfy(82,32)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    f##0 := read($Heap, this, _module.AmortizedQueue.front);
    assume true;
    // ProcessCallStmt: CheckSubrange
    r##0 := rr#0;
    assert (forall<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) && $o == $nw ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.AmortizedQueue.InitFromPieces(_module.AmortizedQueue$T, $nw, f##0, r##0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "Problem5-DoubleEndedQueue.dfy(82,56)"} true;
    r#0 := $nw;
    assume {:captureState "Problem5-DoubleEndedQueue.dfy(82,56)"} true;
}



const unique class._module.LinkedList: ClassName;

// LinkedList: Class $Is
axiom (forall _module.LinkedList$T: Ty, $o: ref ::
  { $Is($o, Tclass._module.LinkedList(_module.LinkedList$T)) }
  $Is($o, Tclass._module.LinkedList(_module.LinkedList$T))
     <==> $o == null || dtype($o) == Tclass._module.LinkedList(_module.LinkedList$T));

// LinkedList: Class $IsAlloc
axiom (forall _module.LinkedList$T: Ty, $o: ref, $h: Heap ::
  { $IsAlloc($o, Tclass._module.LinkedList(_module.LinkedList$T), $h) }
  $IsAlloc($o, Tclass._module.LinkedList(_module.LinkedList$T), $h)
     <==> $o == null || read($h, $o, alloc));

const _module.LinkedList.head: Field Box;

// LinkedList.head: Allocation axiom
axiom (forall _module.LinkedList$T: Ty, $h: Heap, $o: ref ::
  { read($h, $o, _module.LinkedList.head), Tclass._module.LinkedList(_module.LinkedList$T) }
  $IsGoodHeap($h)
       && $o != null
       && dtype($o) == Tclass._module.LinkedList(_module.LinkedList$T)
     ==> $IsBox(read($h, $o, _module.LinkedList.head), _module.LinkedList$T)
       && (read($h, $o, alloc)
         ==> $IsAllocBox(read($h, $o, _module.LinkedList.head), _module.LinkedList$T, $h)));

const _module.LinkedList.tail: Field ref;

// LinkedList.tail: Allocation axiom
axiom (forall _module.LinkedList$T: Ty, $h: Heap, $o: ref ::
  { read($h, $o, _module.LinkedList.tail), Tclass._module.LinkedList(_module.LinkedList$T) }
  $IsGoodHeap($h)
       && $o != null
       && dtype($o) == Tclass._module.LinkedList(_module.LinkedList$T)
     ==> $Is(read($h, $o, _module.LinkedList.tail),
        Tclass._module.LinkedList(_module.LinkedList$T))
       && (read($h, $o, alloc)
         ==> $IsAlloc(read($h, $o, _module.LinkedList.tail),
          Tclass._module.LinkedList(_module.LinkedList$T),
          $h)));

const _module.LinkedList.length: Field int;

// LinkedList.length: Allocation axiom
axiom (forall _module.LinkedList$T: Ty, $h: Heap, $o: ref ::
  { read($h, $o, _module.LinkedList.length), Tclass._module.LinkedList(_module.LinkedList$T) }
  $IsGoodHeap($h)
       && $o != null
       && dtype($o) == Tclass._module.LinkedList(_module.LinkedList$T)
     ==> $Is(read($h, $o, _module.LinkedList.length), TInt)
       && (read($h, $o, alloc)
         ==> $IsAlloc(read($h, $o, _module.LinkedList.length), TInt, $h)));

const _module.LinkedList.List: Field (Seq Box);

// LinkedList.List: Allocation axiom
axiom (forall _module.LinkedList$T: Ty, $h: Heap, $o: ref ::
  { read($h, $o, _module.LinkedList.List), Tclass._module.LinkedList(_module.LinkedList$T) }
  $IsGoodHeap($h)
       && $o != null
       && dtype($o) == Tclass._module.LinkedList(_module.LinkedList$T)
     ==> $Is(read($h, $o, _module.LinkedList.List), TSeq(_module.LinkedList$T))
       && (read($h, $o, alloc)
         ==> $IsAlloc(read($h, $o, _module.LinkedList.List), TSeq(_module.LinkedList$T), $h)));

const _module.LinkedList.Repr: Field (Set Box);

// LinkedList.Repr: Allocation axiom
axiom (forall _module.LinkedList$T: Ty, $h: Heap, $o: ref ::
  { read($h, $o, _module.LinkedList.Repr), Tclass._module.LinkedList(_module.LinkedList$T) }
  $IsGoodHeap($h)
       && $o != null
       && dtype($o) == Tclass._module.LinkedList(_module.LinkedList$T)
     ==> $Is(read($h, $o, _module.LinkedList.Repr),
        TSet(Tclass._module.LinkedList(_module.LinkedList$T)))
       && (read($h, $o, alloc)
         ==> $IsAlloc(read($h, $o, _module.LinkedList.Repr),
          TSet(Tclass._module.LinkedList(_module.LinkedList$T)),
          $h)));

// function declaration for _module.LinkedList.Valid
function _module.LinkedList.Valid(_module.LinkedList$T: Ty, $ly: LayerType, $heap: Heap, this: ref) : bool;

function _module.LinkedList.Valid#canCall(_module.LinkedList$T: Ty, $heap: Heap, this: ref) : bool;

// layer synonym axiom
axiom (forall _module.LinkedList$T: Ty, $ly: LayerType, $Heap: Heap, this: ref ::
  { _module.LinkedList.Valid(_module.LinkedList$T, $LS($ly), $Heap, this) }
  _module.LinkedList.Valid(_module.LinkedList$T, $LS($ly), $Heap, this)
     == _module.LinkedList.Valid(_module.LinkedList$T, $ly, $Heap, this));

// fuel synonym axiom
axiom (forall _module.LinkedList$T: Ty, $ly: LayerType, $Heap: Heap, this: ref ::
  { _module.LinkedList.Valid(_module.LinkedList$T, AsFuelBottom($ly), $Heap, this) }
  _module.LinkedList.Valid(_module.LinkedList$T, $ly, $Heap, this)
     == _module.LinkedList.Valid(_module.LinkedList$T, $LZ, $Heap, this));

// frame axiom for _module.LinkedList.Valid
axiom (forall _module.LinkedList$T: Ty, $ly: LayerType, $h0: Heap, $h1: Heap, this: ref ::
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.LinkedList.Valid(_module.LinkedList$T, $ly, $h1, this) }
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       &&
      this != null
       && $Is(this, Tclass._module.LinkedList(_module.LinkedList$T))
       &&
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==>
    (forall<alpha> $o: ref, $f: Field alpha ::
      $o != null && ($o == this || read($h0, this, _module.LinkedList.Repr)[$Box($o)])
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $ly, $h0, this)
       == _module.LinkedList.Valid(_module.LinkedList$T, $ly, $h1, this));

// consequence axiom for _module.LinkedList.Valid
axiom 0 <= $FunctionContextHeight
   ==> (forall _module.LinkedList$T: Ty, $ly: LayerType, $Heap: Heap, this: ref ::
    { _module.LinkedList.Valid(_module.LinkedList$T, $ly, $Heap, this) }
    _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, this)
         || (0 != $FunctionContextHeight
           &&
          $IsGoodHeap($Heap)
           &&
          this != null
           &&
          $Is(this, Tclass._module.LinkedList(_module.LinkedList$T))
           && $IsAlloc(this, Tclass._module.LinkedList(_module.LinkedList$T), $Heap))
       ==> true);

function _module.LinkedList.Valid#requires(Ty, LayerType, Heap, ref) : bool;

// #requires axiom for _module.LinkedList.Valid
axiom (forall _module.LinkedList$T: Ty, $ly: LayerType, $Heap: Heap, this: ref ::
  { _module.LinkedList.Valid#requires(_module.LinkedList$T, $ly, $Heap, this) }
  $IsGoodHeap($Heap)
       &&
      this != null
       &&
      $Is(this, Tclass._module.LinkedList(_module.LinkedList$T))
       && $IsAlloc(this, Tclass._module.LinkedList(_module.LinkedList$T), $Heap)
     ==> _module.LinkedList.Valid#requires(_module.LinkedList$T, $ly, $Heap, this)
       == true);

// definition axiom for _module.LinkedList.Valid(revealed)
axiom 0 <= $FunctionContextHeight
   ==> (forall _module.LinkedList$T: Ty, $ly: LayerType, $Heap: Heap, this: ref ::
    { _module.LinkedList.Valid(_module.LinkedList$T, $LS($ly), $Heap, this) }
    _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, this)
         || (0 != $FunctionContextHeight
           &&
          $IsGoodHeap($Heap)
           &&
          this != null
           &&
          $Is(this, Tclass._module.LinkedList(_module.LinkedList$T))
           && $IsAlloc(this, Tclass._module.LinkedList(_module.LinkedList$T), $Heap))
       ==> (
          (read($Heap, this, _module.LinkedList.length) == LitInt(0)
           ==> Seq#Equal(read($Heap, this, _module.LinkedList.List), Seq#Empty(): Seq Box)
             && read($Heap, this, _module.LinkedList.tail) == null)
           ==>
          read($Heap, this, _module.LinkedList.length) != 0
           ==>
          !read($Heap, read($Heap, this, _module.LinkedList.tail), _module.LinkedList.Repr)[$Box(this)]
           ==> _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, read($Heap, this, _module.LinkedList.tail)))
         && _module.LinkedList.Valid(_module.LinkedList$T, $LS($ly), $Heap, this)
           == (
            read($Heap, this, _module.LinkedList.Repr)[$Box(this)]
             && LitInt(0) <= read($Heap, this, _module.LinkedList.length)
             && read($Heap, this, _module.LinkedList.length)
               == Seq#Length(read($Heap, this, _module.LinkedList.List))
             && (read($Heap, this, _module.LinkedList.length) == LitInt(0)
               ==> Seq#Equal(read($Heap, this, _module.LinkedList.List), Seq#Empty(): Seq Box)
                 && read($Heap, this, _module.LinkedList.tail) == null)
             && (read($Heap, this, _module.LinkedList.length) != 0
               ==> read($Heap, this, _module.LinkedList.tail) != null
                 && read($Heap, this, _module.LinkedList.Repr)[$Box(read($Heap, this, _module.LinkedList.tail))]
                 && Set#Subset(read($Heap, read($Heap, this, _module.LinkedList.tail), _module.LinkedList.Repr),
                  read($Heap, this, _module.LinkedList.Repr))
                 && !read($Heap, read($Heap, this, _module.LinkedList.tail), _module.LinkedList.Repr)[$Box(this)]
                 && _module.LinkedList.Valid(_module.LinkedList$T, $ly, $Heap, read($Heap, this, _module.LinkedList.tail))
                 && Seq#Equal(read($Heap, this, _module.LinkedList.List),
                  Seq#Append(Seq#Build(Seq#Empty(): Seq Box, read($Heap, this, _module.LinkedList.head)),
                    read($Heap, read($Heap, this, _module.LinkedList.tail), _module.LinkedList.List)))
                 && read($Heap, this, _module.LinkedList.length)
                   == read($Heap, read($Heap, this, _module.LinkedList.tail), _module.LinkedList.length)
                     + 1)));

procedure CheckWellformed$$_module.LinkedList.Valid(_module.LinkedList$T: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.LinkedList(_module.LinkedList$T))
         && $IsAlloc(this, Tclass._module.LinkedList(_module.LinkedList$T), $Heap));
  free requires 0 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.LinkedList.Valid(_module.LinkedList$T: Ty, this: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;
  var b$reqreads#2: bool;
  var b$reqreads#3: bool;
  var b$reqreads#4: bool;
  var b$reqreads#5: bool;
  var b$reqreads#6: bool;
  var b$reqreads#7: bool;
  var b$reqreads#8: bool;
  var b$reqreads#9: bool;
  var b$reqreads#10: bool;
  var b$reqreads#11: bool;
  var b$reqreads#12: bool;
  var b$reqreads#13: bool;
  var b$reqreads#14: bool;
  var b$reqreads#15: bool;
  var b$reqreads#16: bool;
  var b$reqreads#17: bool;
  var b$reqreads#18: bool;
  var b$reqreads#19: bool;
  var b$reqreads#20: bool;
  var b$reqreads#21: bool;
  var b$reqreads#22: bool;
  var b$reqreads#23: bool;
  var b$reqreads#24: bool;
  var b$reqreads#25: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;
    b$reqreads#2 := true;
    b$reqreads#3 := true;
    b$reqreads#4 := true;
    b$reqreads#5 := true;
    b$reqreads#6 := true;
    b$reqreads#7 := true;
    b$reqreads#8 := true;
    b$reqreads#9 := true;
    b$reqreads#10 := true;
    b$reqreads#11 := true;
    b$reqreads#12 := true;
    b$reqreads#13 := true;
    b$reqreads#14 := true;
    b$reqreads#15 := true;
    b$reqreads#16 := true;
    b$reqreads#17 := true;
    b$reqreads#18 := true;
    b$reqreads#19 := true;
    b$reqreads#20 := true;
    b$reqreads#21 := true;
    b$reqreads#22 := true;
    b$reqreads#23 := true;
    b$reqreads#24 := true;
    b$reqreads#25 := true;

    // AddWellformednessCheck for function Valid
    assume {:captureState "Problem5-DoubleEndedQueue.dfy(95,12): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc)
         ==> $o == this || read($Heap, this, _module.LinkedList.Repr)[$Box($o)]);
    b$reqreads#0 := $_Frame[this, _module.LinkedList.Repr];
    assert b$reqreads#0;
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
          $o != null && read($Heap, $o, alloc)
             ==> $o == this || read($Heap, this, _module.LinkedList.Repr)[$Box($o)]);
        b$reqreads#1 := $_Frame[this, _module.LinkedList.Repr];
        if (read($Heap, this, _module.LinkedList.Repr)[$Box(this)])
        {
            b$reqreads#2 := $_Frame[this, _module.LinkedList.length];
        }

        if (read($Heap, this, _module.LinkedList.Repr)[$Box(this)]
           && LitInt(0) <= read($Heap, this, _module.LinkedList.length))
        {
            b$reqreads#3 := $_Frame[this, _module.LinkedList.length];
            b$reqreads#4 := $_Frame[this, _module.LinkedList.List];
        }

        if (read($Heap, this, _module.LinkedList.Repr)[$Box(this)]
           && LitInt(0) <= read($Heap, this, _module.LinkedList.length)
           && read($Heap, this, _module.LinkedList.length)
             == Seq#Length(read($Heap, this, _module.LinkedList.List)))
        {
            b$reqreads#5 := $_Frame[this, _module.LinkedList.length];
            if (read($Heap, this, _module.LinkedList.length) == LitInt(0))
            {
                b$reqreads#6 := $_Frame[this, _module.LinkedList.List];
                if (Seq#Equal(read($Heap, this, _module.LinkedList.List), Seq#Empty(): Seq Box))
                {
                    b$reqreads#7 := $_Frame[this, _module.LinkedList.tail];
                }
            }
        }

        if (read($Heap, this, _module.LinkedList.Repr)[$Box(this)]
           && LitInt(0) <= read($Heap, this, _module.LinkedList.length)
           && read($Heap, this, _module.LinkedList.length)
             == Seq#Length(read($Heap, this, _module.LinkedList.List))
           && (read($Heap, this, _module.LinkedList.length) == LitInt(0)
             ==> Seq#Equal(read($Heap, this, _module.LinkedList.List), Seq#Empty(): Seq Box)
               && read($Heap, this, _module.LinkedList.tail) == null))
        {
            b$reqreads#8 := $_Frame[this, _module.LinkedList.length];
            if (read($Heap, this, _module.LinkedList.length) != 0)
            {
                b$reqreads#9 := $_Frame[this, _module.LinkedList.tail];
                if (read($Heap, this, _module.LinkedList.tail) != null)
                {
                    b$reqreads#10 := $_Frame[this, _module.LinkedList.tail];
                    b$reqreads#11 := $_Frame[this, _module.LinkedList.Repr];
                }

                if (read($Heap, this, _module.LinkedList.tail) != null
                   && read($Heap, this, _module.LinkedList.Repr)[$Box(read($Heap, this, _module.LinkedList.tail))])
                {
                    b$reqreads#12 := $_Frame[this, _module.LinkedList.tail];
                    assert read($Heap, this, _module.LinkedList.tail) != null;
                    b$reqreads#13 := $_Frame[read($Heap, this, _module.LinkedList.tail), _module.LinkedList.Repr];
                    b$reqreads#14 := $_Frame[this, _module.LinkedList.Repr];
                }

                if (read($Heap, this, _module.LinkedList.tail) != null
                   && read($Heap, this, _module.LinkedList.Repr)[$Box(read($Heap, this, _module.LinkedList.tail))]
                   && Set#Subset(read($Heap, read($Heap, this, _module.LinkedList.tail), _module.LinkedList.Repr),
                    read($Heap, this, _module.LinkedList.Repr)))
                {
                    b$reqreads#15 := $_Frame[this, _module.LinkedList.tail];
                    assert read($Heap, this, _module.LinkedList.tail) != null;
                    b$reqreads#16 := $_Frame[read($Heap, this, _module.LinkedList.tail), _module.LinkedList.Repr];
                }

                if (read($Heap, this, _module.LinkedList.tail) != null
                   && read($Heap, this, _module.LinkedList.Repr)[$Box(read($Heap, this, _module.LinkedList.tail))]
                   && Set#Subset(read($Heap, read($Heap, this, _module.LinkedList.tail), _module.LinkedList.Repr),
                    read($Heap, this, _module.LinkedList.Repr))
                   && !read($Heap, read($Heap, this, _module.LinkedList.tail), _module.LinkedList.Repr)[$Box(this)])
                {
                    b$reqreads#17 := $_Frame[this, _module.LinkedList.tail];
                    assert read($Heap, this, _module.LinkedList.tail) != null;
                    b$reqreads#18 := (forall<alpha> $o: ref, $f: Field alpha ::
                      $o != null
                           && read($Heap, $o, alloc)
                           && ($o == read($Heap, this, _module.LinkedList.tail)
                             || read($Heap, read($Heap, this, _module.LinkedList.tail), _module.LinkedList.Repr)[$Box($o)])
                         ==> $_Frame[$o, $f]);
                    assert Set#Subset(Set#Union(read($Heap, read($Heap, this, _module.LinkedList.tail), _module.LinkedList.Repr),
                          Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.LinkedList.tail)))),
                        Set#Union(read($Heap, this, _module.LinkedList.Repr),
                          Set#UnionOne(Set#Empty(): Set Box, $Box(this))))
                       && !Set#Subset(Set#Union(read($Heap, this, _module.LinkedList.Repr),
                          Set#UnionOne(Set#Empty(): Set Box, $Box(this))),
                        Set#Union(read($Heap, read($Heap, this, _module.LinkedList.tail), _module.LinkedList.Repr),
                          Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.LinkedList.tail)))));
                    assume _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, read($Heap, this, _module.LinkedList.tail));
                }

                if (read($Heap, this, _module.LinkedList.tail) != null
                   && read($Heap, this, _module.LinkedList.Repr)[$Box(read($Heap, this, _module.LinkedList.tail))]
                   && Set#Subset(read($Heap, read($Heap, this, _module.LinkedList.tail), _module.LinkedList.Repr),
                    read($Heap, this, _module.LinkedList.Repr))
                   && !read($Heap, read($Heap, this, _module.LinkedList.tail), _module.LinkedList.Repr)[$Box(this)]
                   && _module.LinkedList.Valid(_module.LinkedList$T,
                    $LS($LZ),
                    $Heap,
                    read($Heap, this, _module.LinkedList.tail)))
                {
                    b$reqreads#19 := $_Frame[this, _module.LinkedList.List];
                    b$reqreads#20 := $_Frame[this, _module.LinkedList.head];
                    b$reqreads#21 := $_Frame[this, _module.LinkedList.tail];
                    assert read($Heap, this, _module.LinkedList.tail) != null;
                    b$reqreads#22 := $_Frame[read($Heap, this, _module.LinkedList.tail), _module.LinkedList.List];
                }

                if (read($Heap, this, _module.LinkedList.tail) != null
                   && read($Heap, this, _module.LinkedList.Repr)[$Box(read($Heap, this, _module.LinkedList.tail))]
                   && Set#Subset(read($Heap, read($Heap, this, _module.LinkedList.tail), _module.LinkedList.Repr),
                    read($Heap, this, _module.LinkedList.Repr))
                   && !read($Heap, read($Heap, this, _module.LinkedList.tail), _module.LinkedList.Repr)[$Box(this)]
                   && _module.LinkedList.Valid(_module.LinkedList$T,
                    $LS($LZ),
                    $Heap,
                    read($Heap, this, _module.LinkedList.tail))
                   && Seq#Equal(read($Heap, this, _module.LinkedList.List),
                    Seq#Append(Seq#Build(Seq#Empty(): Seq Box, read($Heap, this, _module.LinkedList.head)),
                      read($Heap, read($Heap, this, _module.LinkedList.tail), _module.LinkedList.List))))
                {
                    b$reqreads#23 := $_Frame[this, _module.LinkedList.length];
                    b$reqreads#24 := $_Frame[this, _module.LinkedList.tail];
                    assert read($Heap, this, _module.LinkedList.tail) != null;
                    b$reqreads#25 := $_Frame[read($Heap, this, _module.LinkedList.tail), _module.LinkedList.length];
                }
            }
        }

        assume _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, this)
           == (
            read($Heap, this, _module.LinkedList.Repr)[$Box(this)]
             && LitInt(0) <= read($Heap, this, _module.LinkedList.length)
             && read($Heap, this, _module.LinkedList.length)
               == Seq#Length(read($Heap, this, _module.LinkedList.List))
             && (read($Heap, this, _module.LinkedList.length) == LitInt(0)
               ==> Seq#Equal(read($Heap, this, _module.LinkedList.List), Seq#Empty(): Seq Box)
                 && read($Heap, this, _module.LinkedList.tail) == null)
             && (read($Heap, this, _module.LinkedList.length) != 0
               ==> read($Heap, this, _module.LinkedList.tail) != null
                 && read($Heap, this, _module.LinkedList.Repr)[$Box(read($Heap, this, _module.LinkedList.tail))]
                 && Set#Subset(read($Heap, read($Heap, this, _module.LinkedList.tail), _module.LinkedList.Repr),
                  read($Heap, this, _module.LinkedList.Repr))
                 && !read($Heap, read($Heap, this, _module.LinkedList.tail), _module.LinkedList.Repr)[$Box(this)]
                 && _module.LinkedList.Valid(_module.LinkedList$T,
                  $LS($LZ),
                  $Heap,
                  read($Heap, this, _module.LinkedList.tail))
                 && Seq#Equal(read($Heap, this, _module.LinkedList.List),
                  Seq#Append(Seq#Build(Seq#Empty(): Seq Box, read($Heap, this, _module.LinkedList.head)),
                    read($Heap, read($Heap, this, _module.LinkedList.tail), _module.LinkedList.List)))
                 && read($Heap, this, _module.LinkedList.length)
                   == read($Heap, read($Heap, this, _module.LinkedList.tail), _module.LinkedList.length)
                     + 1));
        assume (read($Heap, this, _module.LinkedList.length) == LitInt(0)
           ==> Seq#Equal(read($Heap, this, _module.LinkedList.List), Seq#Empty(): Seq Box)
             && read($Heap, this, _module.LinkedList.tail) == null)
           ==>
          read($Heap, this, _module.LinkedList.length) != 0
           ==>
          !read($Heap, read($Heap, this, _module.LinkedList.tail), _module.LinkedList.Repr)[$Box(this)]
           ==> _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, read($Heap, this, _module.LinkedList.tail));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, this), TBool);
        assert b$reqreads#1;
        assert b$reqreads#2;
        assert b$reqreads#3;
        assert b$reqreads#4;
        assert b$reqreads#5;
        assert b$reqreads#6;
        assert b$reqreads#7;
        assert b$reqreads#8;
        assert b$reqreads#9;
        assert b$reqreads#10;
        assert b$reqreads#11;
        assert b$reqreads#12;
        assert b$reqreads#13;
        assert b$reqreads#14;
        assert b$reqreads#15;
        assert b$reqreads#16;
        assert b$reqreads#17;
        assert b$reqreads#18;
        assert b$reqreads#19;
        assert b$reqreads#20;
        assert b$reqreads#21;
        assert b$reqreads#22;
        assert b$reqreads#23;
        assert b$reqreads#24;
        assert b$reqreads#25;
    }
}



procedure CheckWellformed$$_module.LinkedList.Init(_module.LinkedList$T: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.LinkedList(_module.LinkedList$T))
         && $IsAlloc(this, Tclass._module.LinkedList(_module.LinkedList$T), $Heap));
  free requires 3 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.LinkedList.Init(_module.LinkedList$T: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.LinkedList(_module.LinkedList$T))
         && $IsAlloc(this, Tclass._module.LinkedList(_module.LinkedList$T), $Heap));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, this);
  free ensures _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, this)
     &&
    _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, this)
     &&
    read($Heap, this, _module.LinkedList.Repr)[$Box(this)]
     && LitInt(0) <= read($Heap, this, _module.LinkedList.length)
     && read($Heap, this, _module.LinkedList.length)
       == Seq#Length(read($Heap, this, _module.LinkedList.List))
     && (read($Heap, this, _module.LinkedList.length) == LitInt(0)
       ==> Seq#Equal(read($Heap, this, _module.LinkedList.List), Seq#Empty(): Seq Box)
         && read($Heap, this, _module.LinkedList.tail) == null)
     && (read($Heap, this, _module.LinkedList.length) != 0
       ==> read($Heap, this, _module.LinkedList.tail) != null
         && read($Heap, this, _module.LinkedList.Repr)[$Box(read($Heap, this, _module.LinkedList.tail))]
         && Set#Subset(read($Heap, read($Heap, this, _module.LinkedList.tail), _module.LinkedList.Repr),
          read($Heap, this, _module.LinkedList.Repr))
         && !read($Heap, read($Heap, this, _module.LinkedList.tail), _module.LinkedList.Repr)[$Box(this)]
         && _module.LinkedList.Valid(_module.LinkedList$T,
          $LS($LZ),
          $Heap,
          read($Heap, this, _module.LinkedList.tail))
         && Seq#Equal(read($Heap, this, _module.LinkedList.List),
          Seq#Append(Seq#Build(Seq#Empty(): Seq Box, read($Heap, this, _module.LinkedList.head)),
            read($Heap, read($Heap, this, _module.LinkedList.tail), _module.LinkedList.List)))
         && read($Heap, this, _module.LinkedList.length)
           == read($Heap, read($Heap, this, _module.LinkedList.tail), _module.LinkedList.length)
             + 1);
  ensures Seq#Equal(read($Heap, this, _module.LinkedList.List), Seq#Empty(): Seq Box);
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f) || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.LinkedList.Init(_module.LinkedList$T: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.LinkedList(_module.LinkedList$T))
         && $IsAlloc(this, Tclass._module.LinkedList(_module.LinkedList$T), $Heap))
   returns ($_reverifyPost: bool);
  free requires 3 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, this);
  ensures _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, this)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, this)
       || read($Heap, this, _module.LinkedList.Repr)[$Box(this)];
  ensures _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, this)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, this)
       || LitInt(0) <= read($Heap, this, _module.LinkedList.length);
  ensures _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, this)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, this)
       || read($Heap, this, _module.LinkedList.length)
         == Seq#Length(read($Heap, this, _module.LinkedList.List));
  ensures _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, this)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.LinkedList.length) == LitInt(0)
         ==> Seq#Equal(read($Heap, this, _module.LinkedList.List), Seq#Empty(): Seq Box));
  ensures _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, this)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.LinkedList.length) == LitInt(0)
         ==> read($Heap, this, _module.LinkedList.tail) == null);
  ensures _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, this)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.LinkedList.length) != 0
         ==> read($Heap, this, _module.LinkedList.tail) != null);
  ensures _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, this)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.LinkedList.length) != 0
         ==> read($Heap, this, _module.LinkedList.Repr)[$Box(read($Heap, this, _module.LinkedList.tail))]);
  ensures _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, this)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.LinkedList.length) != 0
         ==> Set#Subset(read($Heap, read($Heap, this, _module.LinkedList.tail), _module.LinkedList.Repr),
          read($Heap, this, _module.LinkedList.Repr)));
  ensures _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, this)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.LinkedList.length) != 0
         ==> !read($Heap, read($Heap, this, _module.LinkedList.tail), _module.LinkedList.Repr)[$Box(this)]);
  ensures _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, this)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.LinkedList.length) != 0
         ==> _module.LinkedList.Valid(_module.LinkedList$T,
          $LS($LS($LZ)),
          $Heap,
          read($Heap, this, _module.LinkedList.tail)));
  ensures _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, this)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.LinkedList.length) != 0
         ==> Seq#Equal(read($Heap, this, _module.LinkedList.List),
          Seq#Append(Seq#Build(Seq#Empty(): Seq Box, read($Heap, this, _module.LinkedList.head)),
            read($Heap, read($Heap, this, _module.LinkedList.tail), _module.LinkedList.List))));
  ensures _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, this)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.LinkedList.length) != 0
         ==> read($Heap, this, _module.LinkedList.length)
           == read($Heap, read($Heap, this, _module.LinkedList.tail), _module.LinkedList.length)
             + 1);
  ensures Seq#Equal(read($Heap, this, _module.LinkedList.List), Seq#Empty(): Seq Box);
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f) || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.LinkedList.Init(_module.LinkedList$T: Ty, this: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs#0: ref where $Is($rhs#0, Tclass._module.LinkedList(_module.LinkedList$T));
  var $rhs#1: int;
  var $rhs#2: Seq Box where $Is($rhs#2, TSeq(_module.LinkedList$T));
  var $rhs#3: Set Box
     where $Is($rhs#3, TSet(Tclass._module.LinkedList(_module.LinkedList$T)));

    // AddMethodImpl: Init, Impl$$_module.LinkedList.Init
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> $o == this);
    assume {:captureState "Problem5-DoubleEndedQueue.dfy(112,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- Problem5-DoubleEndedQueue.dfy(113,10)
    assume true;
    assert $_Frame[this, _module.LinkedList.tail];
    assume true;
    $rhs#0 := null;
    $Heap := update($Heap, this, _module.LinkedList.tail, $rhs#0);
    assume $IsGoodHeap($Heap);
    assume {:captureState "Problem5-DoubleEndedQueue.dfy(113,16)"} true;
    // ----- assignment statement ----- Problem5-DoubleEndedQueue.dfy(114,12)
    assume true;
    assert $_Frame[this, _module.LinkedList.length];
    assume true;
    $rhs#1 := LitInt(0);
    $Heap := update($Heap, this, _module.LinkedList.length, $rhs#1);
    assume $IsGoodHeap($Heap);
    assume {:captureState "Problem5-DoubleEndedQueue.dfy(114,15)"} true;
    // ----- assignment statement ----- Problem5-DoubleEndedQueue.dfy(115,10)
    assume true;
    assert $_Frame[this, _module.LinkedList.List];
    assume true;
    $rhs#2 := Lit(Seq#Empty(): Seq Box);
    $Heap := update($Heap, this, _module.LinkedList.List, $rhs#2);
    assume $IsGoodHeap($Heap);
    assume {:captureState "Problem5-DoubleEndedQueue.dfy(115,14)"} true;
    // ----- assignment statement ----- Problem5-DoubleEndedQueue.dfy(116,10)
    assume true;
    assert $_Frame[this, _module.LinkedList.Repr];
    assume true;
    $rhs#3 := Set#UnionOne(Set#Empty(): Set Box, $Box(this));
    $Heap := update($Heap, this, _module.LinkedList.Repr, $rhs#3);
    assume $IsGoodHeap($Heap);
    assume {:captureState "Problem5-DoubleEndedQueue.dfy(116,18)"} true;
}



procedure CheckWellformed$$_module.LinkedList.Cons(_module.LinkedList$T: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.LinkedList(_module.LinkedList$T))
         && $IsAlloc(this, Tclass._module.LinkedList(_module.LinkedList$T), $Heap),
    d#0: Box
       where $IsBox(d#0, _module.LinkedList$T)
         && $IsAllocBox(d#0, _module.LinkedList$T, $Heap))
   returns (r#0: ref
       where $Is(r#0, Tclass._module.LinkedList(_module.LinkedList$T))
         && $IsAlloc(r#0, Tclass._module.LinkedList(_module.LinkedList$T), $Heap));
  free requires 5 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.LinkedList.Cons(_module.LinkedList$T: Ty, this: ref, d#0: Box) returns (r#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: Cons, CheckWellformed$$_module.LinkedList.Cons
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "Problem5-DoubleEndedQueue.dfy(119,9): initial state"} true;
    assume _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, this);
    assume _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, this);
    havoc $Heap;
    assume (forall<alpha> $o: ref, $f: Field alpha ::
      { read($Heap, $o, $f) }
      $o != null && read(old($Heap), $o, alloc)
         ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
    assume $HeapSucc(old($Heap), $Heap);
    havoc r#0;
    assume {:captureState "Problem5-DoubleEndedQueue.dfy(121,35): post-state"} true;
    assume r#0 != null;
    assert r#0 != null;
    assume _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, r#0);
    assume _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, r#0);
    assert r#0 != null;
    assume Seq#Equal(read($Heap, r#0, _module.LinkedList.List),
      Seq#Append(Seq#Build(Seq#Empty(): Seq Box, d#0), read($Heap, this, _module.LinkedList.List)));
}



procedure Call$$_module.LinkedList.Cons(_module.LinkedList$T: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.LinkedList(_module.LinkedList$T))
         && $IsAlloc(this, Tclass._module.LinkedList(_module.LinkedList$T), $Heap),
    d#0: Box
       where $IsBox(d#0, _module.LinkedList$T)
         && $IsAllocBox(d#0, _module.LinkedList$T, $Heap))
   returns (r#0: ref
       where $Is(r#0, Tclass._module.LinkedList(_module.LinkedList$T))
         && $IsAlloc(r#0, Tclass._module.LinkedList(_module.LinkedList$T), $Heap));
  // user-defined preconditions
  requires _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, this)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, this)
       || read($Heap, this, _module.LinkedList.Repr)[$Box(this)];
  requires _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, this)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, this)
       || LitInt(0) <= read($Heap, this, _module.LinkedList.length);
  requires _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, this)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, this)
       || read($Heap, this, _module.LinkedList.length)
         == Seq#Length(read($Heap, this, _module.LinkedList.List));
  requires _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, this)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.LinkedList.length) == LitInt(0)
         ==> Seq#Equal(read($Heap, this, _module.LinkedList.List), Seq#Empty(): Seq Box));
  requires _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, this)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.LinkedList.length) == LitInt(0)
         ==> read($Heap, this, _module.LinkedList.tail) == null);
  requires _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, this)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.LinkedList.length) != 0
         ==> read($Heap, this, _module.LinkedList.tail) != null);
  requires _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, this)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.LinkedList.length) != 0
         ==> read($Heap, this, _module.LinkedList.Repr)[$Box(read($Heap, this, _module.LinkedList.tail))]);
  requires _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, this)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.LinkedList.length) != 0
         ==> Set#Subset(read($Heap, read($Heap, this, _module.LinkedList.tail), _module.LinkedList.Repr),
          read($Heap, this, _module.LinkedList.Repr)));
  requires _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, this)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.LinkedList.length) != 0
         ==> !read($Heap, read($Heap, this, _module.LinkedList.tail), _module.LinkedList.Repr)[$Box(this)]);
  requires _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, this)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.LinkedList.length) != 0
         ==> _module.LinkedList.Valid(_module.LinkedList$T,
          $LS($LS($LZ)),
          $Heap,
          read($Heap, this, _module.LinkedList.tail)));
  requires _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, this)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.LinkedList.length) != 0
         ==> Seq#Equal(read($Heap, this, _module.LinkedList.List),
          Seq#Append(Seq#Build(Seq#Empty(): Seq Box, read($Heap, this, _module.LinkedList.head)),
            read($Heap, read($Heap, this, _module.LinkedList.tail), _module.LinkedList.List))));
  requires _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, this)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.LinkedList.length) != 0
         ==> read($Heap, this, _module.LinkedList.length)
           == read($Heap, read($Heap, this, _module.LinkedList.tail), _module.LinkedList.length)
             + 1);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures r#0 != null
     ==> _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, r#0);
  ensures r#0 != null;
  free ensures _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, r#0)
     &&
    _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, r#0)
     &&
    read($Heap, r#0, _module.LinkedList.Repr)[$Box(r#0)]
     && LitInt(0) <= read($Heap, r#0, _module.LinkedList.length)
     && read($Heap, r#0, _module.LinkedList.length)
       == Seq#Length(read($Heap, r#0, _module.LinkedList.List))
     && (read($Heap, r#0, _module.LinkedList.length) == LitInt(0)
       ==> Seq#Equal(read($Heap, r#0, _module.LinkedList.List), Seq#Empty(): Seq Box)
         && read($Heap, r#0, _module.LinkedList.tail) == null)
     && (read($Heap, r#0, _module.LinkedList.length) != 0
       ==> read($Heap, r#0, _module.LinkedList.tail) != null
         && read($Heap, r#0, _module.LinkedList.Repr)[$Box(read($Heap, r#0, _module.LinkedList.tail))]
         && Set#Subset(read($Heap, read($Heap, r#0, _module.LinkedList.tail), _module.LinkedList.Repr),
          read($Heap, r#0, _module.LinkedList.Repr))
         && !read($Heap, read($Heap, r#0, _module.LinkedList.tail), _module.LinkedList.Repr)[$Box(r#0)]
         && _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, read($Heap, r#0, _module.LinkedList.tail))
         && Seq#Equal(read($Heap, r#0, _module.LinkedList.List),
          Seq#Append(Seq#Build(Seq#Empty(): Seq Box, read($Heap, r#0, _module.LinkedList.head)),
            read($Heap, read($Heap, r#0, _module.LinkedList.tail), _module.LinkedList.List)))
         && read($Heap, r#0, _module.LinkedList.length)
           == read($Heap, read($Heap, r#0, _module.LinkedList.tail), _module.LinkedList.length)
             + 1);
  ensures Seq#Equal(read($Heap, r#0, _module.LinkedList.List),
    Seq#Append(Seq#Build(Seq#Empty(): Seq Box, d#0), read($Heap, this, _module.LinkedList.List)));
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.LinkedList.Cons(_module.LinkedList$T: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.LinkedList(_module.LinkedList$T))
         && $IsAlloc(this, Tclass._module.LinkedList(_module.LinkedList$T), $Heap),
    d#0: Box
       where $IsBox(d#0, _module.LinkedList$T)
         && $IsAllocBox(d#0, _module.LinkedList$T, $Heap))
   returns (r#0: ref
       where $Is(r#0, Tclass._module.LinkedList(_module.LinkedList$T))
         && $IsAlloc(r#0, Tclass._module.LinkedList(_module.LinkedList$T), $Heap),
    $_reverifyPost: bool);
  free requires 5 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, this)
     &&
    _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, this)
     &&
    read($Heap, this, _module.LinkedList.Repr)[$Box(this)]
     && LitInt(0) <= read($Heap, this, _module.LinkedList.length)
     && read($Heap, this, _module.LinkedList.length)
       == Seq#Length(read($Heap, this, _module.LinkedList.List))
     && (read($Heap, this, _module.LinkedList.length) == LitInt(0)
       ==> Seq#Equal(read($Heap, this, _module.LinkedList.List), Seq#Empty(): Seq Box)
         && read($Heap, this, _module.LinkedList.tail) == null)
     && (read($Heap, this, _module.LinkedList.length) != 0
       ==> read($Heap, this, _module.LinkedList.tail) != null
         && read($Heap, this, _module.LinkedList.Repr)[$Box(read($Heap, this, _module.LinkedList.tail))]
         && Set#Subset(read($Heap, read($Heap, this, _module.LinkedList.tail), _module.LinkedList.Repr),
          read($Heap, this, _module.LinkedList.Repr))
         && !read($Heap, read($Heap, this, _module.LinkedList.tail), _module.LinkedList.Repr)[$Box(this)]
         && _module.LinkedList.Valid(_module.LinkedList$T,
          $LS($LZ),
          $Heap,
          read($Heap, this, _module.LinkedList.tail))
         && Seq#Equal(read($Heap, this, _module.LinkedList.List),
          Seq#Append(Seq#Build(Seq#Empty(): Seq Box, read($Heap, this, _module.LinkedList.head)),
            read($Heap, read($Heap, this, _module.LinkedList.tail), _module.LinkedList.List)))
         && read($Heap, this, _module.LinkedList.length)
           == read($Heap, read($Heap, this, _module.LinkedList.tail), _module.LinkedList.length)
             + 1);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures r#0 != null
     ==> _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, r#0);
  ensures r#0 != null;
  ensures _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, r#0)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, r#0)
       || read($Heap, r#0, _module.LinkedList.Repr)[$Box(r#0)];
  ensures _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, r#0)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, r#0)
       || LitInt(0) <= read($Heap, r#0, _module.LinkedList.length);
  ensures _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, r#0)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, r#0)
       || read($Heap, r#0, _module.LinkedList.length)
         == Seq#Length(read($Heap, r#0, _module.LinkedList.List));
  ensures _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, r#0)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, r#0)
       || (read($Heap, r#0, _module.LinkedList.length) == LitInt(0)
         ==> Seq#Equal(read($Heap, r#0, _module.LinkedList.List), Seq#Empty(): Seq Box));
  ensures _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, r#0)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, r#0)
       || (read($Heap, r#0, _module.LinkedList.length) == LitInt(0)
         ==> read($Heap, r#0, _module.LinkedList.tail) == null);
  ensures _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, r#0)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, r#0)
       || (read($Heap, r#0, _module.LinkedList.length) != 0
         ==> read($Heap, r#0, _module.LinkedList.tail) != null);
  ensures _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, r#0)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, r#0)
       || (read($Heap, r#0, _module.LinkedList.length) != 0
         ==> read($Heap, r#0, _module.LinkedList.Repr)[$Box(read($Heap, r#0, _module.LinkedList.tail))]);
  ensures _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, r#0)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, r#0)
       || (read($Heap, r#0, _module.LinkedList.length) != 0
         ==> Set#Subset(read($Heap, read($Heap, r#0, _module.LinkedList.tail), _module.LinkedList.Repr),
          read($Heap, r#0, _module.LinkedList.Repr)));
  ensures _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, r#0)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, r#0)
       || (read($Heap, r#0, _module.LinkedList.length) != 0
         ==> !read($Heap, read($Heap, r#0, _module.LinkedList.tail), _module.LinkedList.Repr)[$Box(r#0)]);
  ensures _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, r#0)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, r#0)
       || (read($Heap, r#0, _module.LinkedList.length) != 0
         ==> _module.LinkedList.Valid(_module.LinkedList$T,
          $LS($LS($LZ)),
          $Heap,
          read($Heap, r#0, _module.LinkedList.tail)));
  ensures _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, r#0)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, r#0)
       || (read($Heap, r#0, _module.LinkedList.length) != 0
         ==> Seq#Equal(read($Heap, r#0, _module.LinkedList.List),
          Seq#Append(Seq#Build(Seq#Empty(): Seq Box, read($Heap, r#0, _module.LinkedList.head)),
            read($Heap, read($Heap, r#0, _module.LinkedList.tail), _module.LinkedList.List))));
  ensures _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, r#0)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, r#0)
       || (read($Heap, r#0, _module.LinkedList.length) != 0
         ==> read($Heap, r#0, _module.LinkedList.length)
           == read($Heap, read($Heap, r#0, _module.LinkedList.tail), _module.LinkedList.length)
             + 1);
  ensures Seq#Equal(read($Heap, r#0, _module.LinkedList.List),
    Seq#Append(Seq#Build(Seq#Empty(): Seq Box, d#0), read($Heap, this, _module.LinkedList.List)));
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.LinkedList.Cons(_module.LinkedList$T: Ty, this: ref, d#0: Box)
   returns (r#0: ref, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $nw: ref;
  var $rhs#0: Box where $IsBox($rhs#0, _module.LinkedList$T);
  var $rhs#1: ref where $Is($rhs#1, Tclass._module.LinkedList(_module.LinkedList$T));
  var $rhs#2: int;
  var $rhs#3: Seq Box where $Is($rhs#3, TSeq(_module.LinkedList$T));
  var $rhs#4: Set Box
     where $Is($rhs#4, TSet(Tclass._module.LinkedList(_module.LinkedList$T)));

    // AddMethodImpl: Cons, Impl$$_module.LinkedList.Cons
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "Problem5-DoubleEndedQueue.dfy(122,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- Problem5-DoubleEndedQueue.dfy(123,7)
    assume true;
    havoc $nw;
    assume $nw != null
       &&
      !read($Heap, $nw, alloc)
       && dtype($nw) == Tclass._module.LinkedList(_module.LinkedList$T);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    r#0 := $nw;
    assume {:captureState "Problem5-DoubleEndedQueue.dfy(123,26)"} true;
    // ----- assignment statement ----- Problem5-DoubleEndedQueue.dfy(124,12)
    assert r#0 != null;
    assume true;
    assert $_Frame[r#0, _module.LinkedList.head];
    assume true;
    $rhs#0 := d#0;
    $Heap := update($Heap, r#0, _module.LinkedList.head, $rhs#0);
    assume $IsGoodHeap($Heap);
    assume {:captureState "Problem5-DoubleEndedQueue.dfy(124,15)"} true;
    // ----- assignment statement ----- Problem5-DoubleEndedQueue.dfy(125,12)
    assert r#0 != null;
    assume true;
    assert $_Frame[r#0, _module.LinkedList.tail];
    assume true;
    $rhs#1 := this;
    $Heap := update($Heap, r#0, _module.LinkedList.tail, $rhs#1);
    assume $IsGoodHeap($Heap);
    assume {:captureState "Problem5-DoubleEndedQueue.dfy(125,18)"} true;
    // ----- assignment statement ----- Problem5-DoubleEndedQueue.dfy(126,14)
    assert r#0 != null;
    assume true;
    assert $_Frame[r#0, _module.LinkedList.length];
    assume true;
    $rhs#2 := read($Heap, this, _module.LinkedList.length) + 1;
    $Heap := update($Heap, r#0, _module.LinkedList.length, $rhs#2);
    assume $IsGoodHeap($Heap);
    assume {:captureState "Problem5-DoubleEndedQueue.dfy(126,26)"} true;
    // ----- assignment statement ----- Problem5-DoubleEndedQueue.dfy(127,12)
    assert r#0 != null;
    assume true;
    assert $_Frame[r#0, _module.LinkedList.List];
    assume true;
    $rhs#3 := Seq#Append(Seq#Build(Seq#Empty(): Seq Box, d#0), read($Heap, this, _module.LinkedList.List));
    $Heap := update($Heap, r#0, _module.LinkedList.List, $rhs#3);
    assume $IsGoodHeap($Heap);
    assume {:captureState "Problem5-DoubleEndedQueue.dfy(127,24)"} true;
    // ----- assignment statement ----- Problem5-DoubleEndedQueue.dfy(128,12)
    assert r#0 != null;
    assume true;
    assert $_Frame[r#0, _module.LinkedList.Repr];
    assume true;
    $rhs#4 := Set#Union(Set#UnionOne(Set#Empty(): Set Box, $Box(r#0)),
      read($Heap, this, _module.LinkedList.Repr));
    $Heap := update($Heap, r#0, _module.LinkedList.Repr, $rhs#4);
    assume $IsGoodHeap($Heap);
    assume {:captureState "Problem5-DoubleEndedQueue.dfy(128,24)"} true;
}



procedure CheckWellformed$$_module.LinkedList.Concat(_module.LinkedList$T: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.LinkedList(_module.LinkedList$T))
         && $IsAlloc(this, Tclass._module.LinkedList(_module.LinkedList$T), $Heap),
    end#0: ref
       where $Is(end#0, Tclass._module.LinkedList(_module.LinkedList$T))
         && $IsAlloc(end#0, Tclass._module.LinkedList(_module.LinkedList$T), $Heap))
   returns (r#0: ref
       where $Is(r#0, Tclass._module.LinkedList(_module.LinkedList$T))
         && $IsAlloc(r#0, Tclass._module.LinkedList(_module.LinkedList$T), $Heap));
  free requires 6 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.LinkedList.Concat(_module.LinkedList$T: Ty, this: ref, end#0: ref) returns (r#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: Concat, CheckWellformed$$_module.LinkedList.Concat
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "Problem5-DoubleEndedQueue.dfy(131,9): initial state"} true;
    assume _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, this);
    assume _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, this);
    assume end#0 != null;
    assert end#0 != null;
    assume _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, end#0);
    assume _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, end#0);
    havoc $Heap;
    assume (forall<alpha> $o: ref, $f: Field alpha ::
      { read($Heap, $o, $f) }
      $o != null && read(old($Heap), $o, alloc)
         ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
    assume $HeapSucc(old($Heap), $Heap);
    havoc r#0;
    assume {:captureState "Problem5-DoubleEndedQueue.dfy(133,35): post-state"} true;
    assume r#0 != null;
    assert r#0 != null;
    assume _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, r#0);
    assume _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, r#0);
    assert r#0 != null;
    assert end#0 != null;
    assume Seq#Equal(read($Heap, r#0, _module.LinkedList.List),
      Seq#Append(read($Heap, this, _module.LinkedList.List),
        read($Heap, end#0, _module.LinkedList.List)));
}



procedure Call$$_module.LinkedList.Concat(_module.LinkedList$T: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.LinkedList(_module.LinkedList$T))
         && $IsAlloc(this, Tclass._module.LinkedList(_module.LinkedList$T), $Heap),
    end#0: ref
       where $Is(end#0, Tclass._module.LinkedList(_module.LinkedList$T))
         && $IsAlloc(end#0, Tclass._module.LinkedList(_module.LinkedList$T), $Heap))
   returns (r#0: ref
       where $Is(r#0, Tclass._module.LinkedList(_module.LinkedList$T))
         && $IsAlloc(r#0, Tclass._module.LinkedList(_module.LinkedList$T), $Heap));
  // user-defined preconditions
  requires _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, this)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, this)
       || read($Heap, this, _module.LinkedList.Repr)[$Box(this)];
  requires _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, this)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, this)
       || LitInt(0) <= read($Heap, this, _module.LinkedList.length);
  requires _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, this)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, this)
       || read($Heap, this, _module.LinkedList.length)
         == Seq#Length(read($Heap, this, _module.LinkedList.List));
  requires _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, this)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.LinkedList.length) == LitInt(0)
         ==> Seq#Equal(read($Heap, this, _module.LinkedList.List), Seq#Empty(): Seq Box));
  requires _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, this)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.LinkedList.length) == LitInt(0)
         ==> read($Heap, this, _module.LinkedList.tail) == null);
  requires _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, this)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.LinkedList.length) != 0
         ==> read($Heap, this, _module.LinkedList.tail) != null);
  requires _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, this)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.LinkedList.length) != 0
         ==> read($Heap, this, _module.LinkedList.Repr)[$Box(read($Heap, this, _module.LinkedList.tail))]);
  requires _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, this)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.LinkedList.length) != 0
         ==> Set#Subset(read($Heap, read($Heap, this, _module.LinkedList.tail), _module.LinkedList.Repr),
          read($Heap, this, _module.LinkedList.Repr)));
  requires _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, this)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.LinkedList.length) != 0
         ==> !read($Heap, read($Heap, this, _module.LinkedList.tail), _module.LinkedList.Repr)[$Box(this)]);
  requires _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, this)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.LinkedList.length) != 0
         ==> _module.LinkedList.Valid(_module.LinkedList$T,
          $LS($LS($LZ)),
          $Heap,
          read($Heap, this, _module.LinkedList.tail)));
  requires _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, this)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.LinkedList.length) != 0
         ==> Seq#Equal(read($Heap, this, _module.LinkedList.List),
          Seq#Append(Seq#Build(Seq#Empty(): Seq Box, read($Heap, this, _module.LinkedList.head)),
            read($Heap, read($Heap, this, _module.LinkedList.tail), _module.LinkedList.List))));
  requires _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, this)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.LinkedList.length) != 0
         ==> read($Heap, this, _module.LinkedList.length)
           == read($Heap, read($Heap, this, _module.LinkedList.tail), _module.LinkedList.length)
             + 1);
  requires end#0 != null;
  requires _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, end#0)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, end#0)
       || read($Heap, end#0, _module.LinkedList.Repr)[$Box(end#0)];
  requires _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, end#0)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, end#0)
       || LitInt(0) <= read($Heap, end#0, _module.LinkedList.length);
  requires _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, end#0)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, end#0)
       || read($Heap, end#0, _module.LinkedList.length)
         == Seq#Length(read($Heap, end#0, _module.LinkedList.List));
  requires _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, end#0)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, end#0)
       || (read($Heap, end#0, _module.LinkedList.length) == LitInt(0)
         ==> Seq#Equal(read($Heap, end#0, _module.LinkedList.List), Seq#Empty(): Seq Box));
  requires _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, end#0)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, end#0)
       || (read($Heap, end#0, _module.LinkedList.length) == LitInt(0)
         ==> read($Heap, end#0, _module.LinkedList.tail) == null);
  requires _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, end#0)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, end#0)
       || (read($Heap, end#0, _module.LinkedList.length) != 0
         ==> read($Heap, end#0, _module.LinkedList.tail) != null);
  requires _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, end#0)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, end#0)
       || (read($Heap, end#0, _module.LinkedList.length) != 0
         ==> read($Heap, end#0, _module.LinkedList.Repr)[$Box(read($Heap, end#0, _module.LinkedList.tail))]);
  requires _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, end#0)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, end#0)
       || (read($Heap, end#0, _module.LinkedList.length) != 0
         ==> Set#Subset(read($Heap, read($Heap, end#0, _module.LinkedList.tail), _module.LinkedList.Repr),
          read($Heap, end#0, _module.LinkedList.Repr)));
  requires _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, end#0)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, end#0)
       || (read($Heap, end#0, _module.LinkedList.length) != 0
         ==> !read($Heap, read($Heap, end#0, _module.LinkedList.tail), _module.LinkedList.Repr)[$Box(end#0)]);
  requires _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, end#0)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, end#0)
       || (read($Heap, end#0, _module.LinkedList.length) != 0
         ==> _module.LinkedList.Valid(_module.LinkedList$T,
          $LS($LS($LZ)),
          $Heap,
          read($Heap, end#0, _module.LinkedList.tail)));
  requires _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, end#0)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, end#0)
       || (read($Heap, end#0, _module.LinkedList.length) != 0
         ==> Seq#Equal(read($Heap, end#0, _module.LinkedList.List),
          Seq#Append(Seq#Build(Seq#Empty(): Seq Box, read($Heap, end#0, _module.LinkedList.head)),
            read($Heap, read($Heap, end#0, _module.LinkedList.tail), _module.LinkedList.List))));
  requires _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, end#0)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, end#0)
       || (read($Heap, end#0, _module.LinkedList.length) != 0
         ==> read($Heap, end#0, _module.LinkedList.length)
           == read($Heap, read($Heap, end#0, _module.LinkedList.tail), _module.LinkedList.length)
             + 1);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures r#0 != null
     ==> _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, r#0);
  ensures r#0 != null;
  free ensures _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, r#0)
     &&
    _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, r#0)
     &&
    read($Heap, r#0, _module.LinkedList.Repr)[$Box(r#0)]
     && LitInt(0) <= read($Heap, r#0, _module.LinkedList.length)
     && read($Heap, r#0, _module.LinkedList.length)
       == Seq#Length(read($Heap, r#0, _module.LinkedList.List))
     && (read($Heap, r#0, _module.LinkedList.length) == LitInt(0)
       ==> Seq#Equal(read($Heap, r#0, _module.LinkedList.List), Seq#Empty(): Seq Box)
         && read($Heap, r#0, _module.LinkedList.tail) == null)
     && (read($Heap, r#0, _module.LinkedList.length) != 0
       ==> read($Heap, r#0, _module.LinkedList.tail) != null
         && read($Heap, r#0, _module.LinkedList.Repr)[$Box(read($Heap, r#0, _module.LinkedList.tail))]
         && Set#Subset(read($Heap, read($Heap, r#0, _module.LinkedList.tail), _module.LinkedList.Repr),
          read($Heap, r#0, _module.LinkedList.Repr))
         && !read($Heap, read($Heap, r#0, _module.LinkedList.tail), _module.LinkedList.Repr)[$Box(r#0)]
         && _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, read($Heap, r#0, _module.LinkedList.tail))
         && Seq#Equal(read($Heap, r#0, _module.LinkedList.List),
          Seq#Append(Seq#Build(Seq#Empty(): Seq Box, read($Heap, r#0, _module.LinkedList.head)),
            read($Heap, read($Heap, r#0, _module.LinkedList.tail), _module.LinkedList.List)))
         && read($Heap, r#0, _module.LinkedList.length)
           == read($Heap, read($Heap, r#0, _module.LinkedList.tail), _module.LinkedList.length)
             + 1);
  ensures Seq#Equal(read($Heap, r#0, _module.LinkedList.List),
    Seq#Append(read($Heap, this, _module.LinkedList.List),
      read($Heap, end#0, _module.LinkedList.List)));
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.LinkedList.Concat(_module.LinkedList$T: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.LinkedList(_module.LinkedList$T))
         && $IsAlloc(this, Tclass._module.LinkedList(_module.LinkedList$T), $Heap),
    end#0: ref
       where $Is(end#0, Tclass._module.LinkedList(_module.LinkedList$T))
         && $IsAlloc(end#0, Tclass._module.LinkedList(_module.LinkedList$T), $Heap))
   returns (r#0: ref
       where $Is(r#0, Tclass._module.LinkedList(_module.LinkedList$T))
         && $IsAlloc(r#0, Tclass._module.LinkedList(_module.LinkedList$T), $Heap),
    $_reverifyPost: bool);
  free requires 6 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, this)
     &&
    _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, this)
     &&
    read($Heap, this, _module.LinkedList.Repr)[$Box(this)]
     && LitInt(0) <= read($Heap, this, _module.LinkedList.length)
     && read($Heap, this, _module.LinkedList.length)
       == Seq#Length(read($Heap, this, _module.LinkedList.List))
     && (read($Heap, this, _module.LinkedList.length) == LitInt(0)
       ==> Seq#Equal(read($Heap, this, _module.LinkedList.List), Seq#Empty(): Seq Box)
         && read($Heap, this, _module.LinkedList.tail) == null)
     && (read($Heap, this, _module.LinkedList.length) != 0
       ==> read($Heap, this, _module.LinkedList.tail) != null
         && read($Heap, this, _module.LinkedList.Repr)[$Box(read($Heap, this, _module.LinkedList.tail))]
         && Set#Subset(read($Heap, read($Heap, this, _module.LinkedList.tail), _module.LinkedList.Repr),
          read($Heap, this, _module.LinkedList.Repr))
         && !read($Heap, read($Heap, this, _module.LinkedList.tail), _module.LinkedList.Repr)[$Box(this)]
         && _module.LinkedList.Valid(_module.LinkedList$T,
          $LS($LZ),
          $Heap,
          read($Heap, this, _module.LinkedList.tail))
         && Seq#Equal(read($Heap, this, _module.LinkedList.List),
          Seq#Append(Seq#Build(Seq#Empty(): Seq Box, read($Heap, this, _module.LinkedList.head)),
            read($Heap, read($Heap, this, _module.LinkedList.tail), _module.LinkedList.List)))
         && read($Heap, this, _module.LinkedList.length)
           == read($Heap, read($Heap, this, _module.LinkedList.tail), _module.LinkedList.length)
             + 1);
  requires end#0 != null;
  free requires _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, end#0)
     &&
    _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, end#0)
     &&
    read($Heap, end#0, _module.LinkedList.Repr)[$Box(end#0)]
     && LitInt(0) <= read($Heap, end#0, _module.LinkedList.length)
     && read($Heap, end#0, _module.LinkedList.length)
       == Seq#Length(read($Heap, end#0, _module.LinkedList.List))
     && (read($Heap, end#0, _module.LinkedList.length) == LitInt(0)
       ==> Seq#Equal(read($Heap, end#0, _module.LinkedList.List), Seq#Empty(): Seq Box)
         && read($Heap, end#0, _module.LinkedList.tail) == null)
     && (read($Heap, end#0, _module.LinkedList.length) != 0
       ==> read($Heap, end#0, _module.LinkedList.tail) != null
         && read($Heap, end#0, _module.LinkedList.Repr)[$Box(read($Heap, end#0, _module.LinkedList.tail))]
         && Set#Subset(read($Heap, read($Heap, end#0, _module.LinkedList.tail), _module.LinkedList.Repr),
          read($Heap, end#0, _module.LinkedList.Repr))
         && !read($Heap, read($Heap, end#0, _module.LinkedList.tail), _module.LinkedList.Repr)[$Box(end#0)]
         && _module.LinkedList.Valid(_module.LinkedList$T,
          $LS($LZ),
          $Heap,
          read($Heap, end#0, _module.LinkedList.tail))
         && Seq#Equal(read($Heap, end#0, _module.LinkedList.List),
          Seq#Append(Seq#Build(Seq#Empty(): Seq Box, read($Heap, end#0, _module.LinkedList.head)),
            read($Heap, read($Heap, end#0, _module.LinkedList.tail), _module.LinkedList.List)))
         && read($Heap, end#0, _module.LinkedList.length)
           == read($Heap, read($Heap, end#0, _module.LinkedList.tail), _module.LinkedList.length)
             + 1);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures r#0 != null
     ==> _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, r#0);
  ensures r#0 != null;
  ensures _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, r#0)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, r#0)
       || read($Heap, r#0, _module.LinkedList.Repr)[$Box(r#0)];
  ensures _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, r#0)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, r#0)
       || LitInt(0) <= read($Heap, r#0, _module.LinkedList.length);
  ensures _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, r#0)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, r#0)
       || read($Heap, r#0, _module.LinkedList.length)
         == Seq#Length(read($Heap, r#0, _module.LinkedList.List));
  ensures _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, r#0)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, r#0)
       || (read($Heap, r#0, _module.LinkedList.length) == LitInt(0)
         ==> Seq#Equal(read($Heap, r#0, _module.LinkedList.List), Seq#Empty(): Seq Box));
  ensures _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, r#0)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, r#0)
       || (read($Heap, r#0, _module.LinkedList.length) == LitInt(0)
         ==> read($Heap, r#0, _module.LinkedList.tail) == null);
  ensures _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, r#0)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, r#0)
       || (read($Heap, r#0, _module.LinkedList.length) != 0
         ==> read($Heap, r#0, _module.LinkedList.tail) != null);
  ensures _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, r#0)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, r#0)
       || (read($Heap, r#0, _module.LinkedList.length) != 0
         ==> read($Heap, r#0, _module.LinkedList.Repr)[$Box(read($Heap, r#0, _module.LinkedList.tail))]);
  ensures _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, r#0)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, r#0)
       || (read($Heap, r#0, _module.LinkedList.length) != 0
         ==> Set#Subset(read($Heap, read($Heap, r#0, _module.LinkedList.tail), _module.LinkedList.Repr),
          read($Heap, r#0, _module.LinkedList.Repr)));
  ensures _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, r#0)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, r#0)
       || (read($Heap, r#0, _module.LinkedList.length) != 0
         ==> !read($Heap, read($Heap, r#0, _module.LinkedList.tail), _module.LinkedList.Repr)[$Box(r#0)]);
  ensures _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, r#0)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, r#0)
       || (read($Heap, r#0, _module.LinkedList.length) != 0
         ==> _module.LinkedList.Valid(_module.LinkedList$T,
          $LS($LS($LZ)),
          $Heap,
          read($Heap, r#0, _module.LinkedList.tail)));
  ensures _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, r#0)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, r#0)
       || (read($Heap, r#0, _module.LinkedList.length) != 0
         ==> Seq#Equal(read($Heap, r#0, _module.LinkedList.List),
          Seq#Append(Seq#Build(Seq#Empty(): Seq Box, read($Heap, r#0, _module.LinkedList.head)),
            read($Heap, read($Heap, r#0, _module.LinkedList.tail), _module.LinkedList.List))));
  ensures _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, r#0)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, r#0)
       || (read($Heap, r#0, _module.LinkedList.length) != 0
         ==> read($Heap, r#0, _module.LinkedList.length)
           == read($Heap, read($Heap, r#0, _module.LinkedList.tail), _module.LinkedList.length)
             + 1);
  ensures Seq#Equal(read($Heap, r#0, _module.LinkedList.List),
    Seq#Append(read($Heap, this, _module.LinkedList.List),
      read($Heap, end#0, _module.LinkedList.List)));
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.LinkedList.Concat(_module.LinkedList$T: Ty, this: ref, end#0: ref)
   returns (r#0: ref, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var c#0: ref
     where $Is(c#0, Tclass._module.LinkedList(_module.LinkedList$T))
       && $IsAlloc(c#0, Tclass._module.LinkedList(_module.LinkedList$T), $Heap);
  var $rhs##0: ref
     where $Is($rhs##0, Tclass._module.LinkedList(_module.LinkedList$T))
       && $IsAlloc($rhs##0, Tclass._module.LinkedList(_module.LinkedList$T), $Heap);
  var end##0: ref;
  var $rhs##1: ref
     where $Is($rhs##1, Tclass._module.LinkedList(_module.LinkedList$T))
       && $IsAlloc($rhs##1, Tclass._module.LinkedList(_module.LinkedList$T), $Heap);
  var d##0: Box;

    // AddMethodImpl: Concat, Impl$$_module.LinkedList.Concat
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "Problem5-DoubleEndedQueue.dfy(135,2): initial state"} true;
    $_reverifyPost := false;
    // ----- if statement ----- Problem5-DoubleEndedQueue.dfy(136,5)
    assume true;
    if (read($Heap, this, _module.LinkedList.length) == LitInt(0))
    {
        // ----- assignment statement ----- Problem5-DoubleEndedQueue.dfy(137,9)
        assume true;
        assume true;
        r#0 := end#0;
        assume {:captureState "Problem5-DoubleEndedQueue.dfy(137,14)"} true;
    }
    else
    {
        // ----- call statement ----- Problem5-DoubleEndedQueue.dfy(139,27)
        assume true;
        // TrCallStmt: Adding lhs Microsoft.Dafny.AutoGhostIdentifierExpr with type LinkedList<T>
        // TrCallStmt: Before ProcessCallStmt
        assert read($Heap, this, _module.LinkedList.tail) != null;
        assume true;
        // ProcessCallStmt: CheckSubrange
        end##0 := end#0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assert Set#Subset(read($Heap, read($Heap, this, _module.LinkedList.tail), _module.LinkedList.Repr),
            read(old($Heap), this, _module.LinkedList.Repr))
           && !Set#Subset(read(old($Heap), this, _module.LinkedList.Repr),
            read($Heap, read($Heap, this, _module.LinkedList.tail), _module.LinkedList.Repr));
        // ProcessCallStmt: Make the call
        call $rhs##0 := Call$$_module.LinkedList.Concat(_module.LinkedList$T, read($Heap, this, _module.LinkedList.tail), end##0);
        // TrCallStmt: After ProcessCallStmt
        c#0 := $rhs##0;
        assume {:captureState "Problem5-DoubleEndedQueue.dfy(139,31)"} true;
        // ----- call statement ----- Problem5-DoubleEndedQueue.dfy(140,18)
        assume true;
        // TrCallStmt: Adding lhs Microsoft.Dafny.IdentifierExpr with type LinkedList<T>
        // TrCallStmt: Before ProcessCallStmt
        assert c#0 != null;
        assume true;
        // ProcessCallStmt: CheckSubrange
        d##0 := read($Heap, this, _module.LinkedList.head);
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call $rhs##1 := Call$$_module.LinkedList.Cons(_module.LinkedList$T, c#0, d##0);
        // TrCallStmt: After ProcessCallStmt
        r#0 := $rhs##1;
        assume {:captureState "Problem5-DoubleEndedQueue.dfy(140,23)"} true;
    }
}



procedure CheckWellformed$$_module.LinkedList.Reverse(_module.LinkedList$T: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.LinkedList(_module.LinkedList$T))
         && $IsAlloc(this, Tclass._module.LinkedList(_module.LinkedList$T), $Heap))
   returns (r#0: ref
       where $Is(r#0, Tclass._module.LinkedList(_module.LinkedList$T))
         && $IsAlloc(r#0, Tclass._module.LinkedList(_module.LinkedList$T), $Heap));
  free requires 7 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.LinkedList.Reverse(_module.LinkedList$T: Ty, this: ref) returns (r#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var k#0: int;
  var ##s#0: Seq Box;

    // AddMethodImpl: Reverse, CheckWellformed$$_module.LinkedList.Reverse
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "Problem5-DoubleEndedQueue.dfy(144,9): initial state"} true;
    assume _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, this);
    assume _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, this);
    havoc $Heap;
    assume (forall<alpha> $o: ref, $f: Field alpha ::
      { read($Heap, $o, $f) }
      $o != null && read(old($Heap), $o, alloc)
         ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
    assume $HeapSucc(old($Heap), $Heap);
    havoc r#0;
    assume {:captureState "Problem5-DoubleEndedQueue.dfy(146,35): post-state"} true;
    assume r#0 != null;
    assert r#0 != null;
    assume _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, r#0);
    assume _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, r#0);
    assert r#0 != null;
    assume Seq#Length(read($Heap, this, _module.LinkedList.List))
       == Seq#Length(read($Heap, r#0, _module.LinkedList.List));
    havoc k#0;
    // Begin Comprehension WF check
    if (LitInt(0) <= k#0)
    {
    }

    if (LitInt(0) <= k#0 && k#0 < Seq#Length(read($Heap, this, _module.LinkedList.List)))
    {
        assert 0 <= k#0 && k#0 < Seq#Length(read($Heap, this, _module.LinkedList.List));
        assert r#0 != null;
        assert 0 <= Seq#Length(read($Heap, this, _module.LinkedList.List)) - 1 - k#0
           && Seq#Length(read($Heap, this, _module.LinkedList.List)) - 1 - k#0
             < Seq#Length(read($Heap, r#0, _module.LinkedList.List));
    }

    // End Comprehension WF check
    assume (forall k#1: int ::
      { Seq#Index(read($Heap, this, _module.LinkedList.List), k#1) }
      true
         ==>
        LitInt(0) <= k#1 && k#1 < Seq#Length(read($Heap, this, _module.LinkedList.List))
         ==> Seq#Index(read($Heap, this, _module.LinkedList.List), k#1)
           == Seq#Index(read($Heap, r#0, _module.LinkedList.List),
            Seq#Length(read($Heap, this, _module.LinkedList.List)) - 1 - k#1));
    assert r#0 != null;
    ##s#0 := read($Heap, this, _module.LinkedList.List);
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#0, TSeq(_module.LinkedList$T), $Heap);
    assume _module.LinkedList.ReverseSeq#canCall(_module.LinkedList$T, read($Heap, this, _module.LinkedList.List));
    assume Seq#Equal(read($Heap, r#0, _module.LinkedList.List),
      _module.LinkedList.ReverseSeq(_module.LinkedList$T, $LS($LZ), read($Heap, this, _module.LinkedList.List)));
}



procedure Call$$_module.LinkedList.Reverse(_module.LinkedList$T: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.LinkedList(_module.LinkedList$T))
         && $IsAlloc(this, Tclass._module.LinkedList(_module.LinkedList$T), $Heap))
   returns (r#0: ref
       where $Is(r#0, Tclass._module.LinkedList(_module.LinkedList$T))
         && $IsAlloc(r#0, Tclass._module.LinkedList(_module.LinkedList$T), $Heap));
  // user-defined preconditions
  requires _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, this)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, this)
       || read($Heap, this, _module.LinkedList.Repr)[$Box(this)];
  requires _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, this)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, this)
       || LitInt(0) <= read($Heap, this, _module.LinkedList.length);
  requires _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, this)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, this)
       || read($Heap, this, _module.LinkedList.length)
         == Seq#Length(read($Heap, this, _module.LinkedList.List));
  requires _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, this)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.LinkedList.length) == LitInt(0)
         ==> Seq#Equal(read($Heap, this, _module.LinkedList.List), Seq#Empty(): Seq Box));
  requires _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, this)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.LinkedList.length) == LitInt(0)
         ==> read($Heap, this, _module.LinkedList.tail) == null);
  requires _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, this)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.LinkedList.length) != 0
         ==> read($Heap, this, _module.LinkedList.tail) != null);
  requires _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, this)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.LinkedList.length) != 0
         ==> read($Heap, this, _module.LinkedList.Repr)[$Box(read($Heap, this, _module.LinkedList.tail))]);
  requires _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, this)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.LinkedList.length) != 0
         ==> Set#Subset(read($Heap, read($Heap, this, _module.LinkedList.tail), _module.LinkedList.Repr),
          read($Heap, this, _module.LinkedList.Repr)));
  requires _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, this)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.LinkedList.length) != 0
         ==> !read($Heap, read($Heap, this, _module.LinkedList.tail), _module.LinkedList.Repr)[$Box(this)]);
  requires _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, this)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.LinkedList.length) != 0
         ==> _module.LinkedList.Valid(_module.LinkedList$T,
          $LS($LS($LZ)),
          $Heap,
          read($Heap, this, _module.LinkedList.tail)));
  requires _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, this)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.LinkedList.length) != 0
         ==> Seq#Equal(read($Heap, this, _module.LinkedList.List),
          Seq#Append(Seq#Build(Seq#Empty(): Seq Box, read($Heap, this, _module.LinkedList.head)),
            read($Heap, read($Heap, this, _module.LinkedList.tail), _module.LinkedList.List))));
  requires _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, this)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, this)
       || (read($Heap, this, _module.LinkedList.length) != 0
         ==> read($Heap, this, _module.LinkedList.length)
           == read($Heap, read($Heap, this, _module.LinkedList.tail), _module.LinkedList.length)
             + 1);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures r#0 != null
     ==> _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, r#0);
  ensures r#0 != null;
  free ensures _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, r#0)
     &&
    _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, r#0)
     &&
    read($Heap, r#0, _module.LinkedList.Repr)[$Box(r#0)]
     && LitInt(0) <= read($Heap, r#0, _module.LinkedList.length)
     && read($Heap, r#0, _module.LinkedList.length)
       == Seq#Length(read($Heap, r#0, _module.LinkedList.List))
     && (read($Heap, r#0, _module.LinkedList.length) == LitInt(0)
       ==> Seq#Equal(read($Heap, r#0, _module.LinkedList.List), Seq#Empty(): Seq Box)
         && read($Heap, r#0, _module.LinkedList.tail) == null)
     && (read($Heap, r#0, _module.LinkedList.length) != 0
       ==> read($Heap, r#0, _module.LinkedList.tail) != null
         && read($Heap, r#0, _module.LinkedList.Repr)[$Box(read($Heap, r#0, _module.LinkedList.tail))]
         && Set#Subset(read($Heap, read($Heap, r#0, _module.LinkedList.tail), _module.LinkedList.Repr),
          read($Heap, r#0, _module.LinkedList.Repr))
         && !read($Heap, read($Heap, r#0, _module.LinkedList.tail), _module.LinkedList.Repr)[$Box(r#0)]
         && _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, read($Heap, r#0, _module.LinkedList.tail))
         && Seq#Equal(read($Heap, r#0, _module.LinkedList.List),
          Seq#Append(Seq#Build(Seq#Empty(): Seq Box, read($Heap, r#0, _module.LinkedList.head)),
            read($Heap, read($Heap, r#0, _module.LinkedList.tail), _module.LinkedList.List)))
         && read($Heap, r#0, _module.LinkedList.length)
           == read($Heap, read($Heap, r#0, _module.LinkedList.tail), _module.LinkedList.length)
             + 1);
  ensures Seq#Length(read($Heap, this, _module.LinkedList.List))
     == Seq#Length(read($Heap, r#0, _module.LinkedList.List));
  free ensures (forall k#1: int ::
    { Seq#Index(read($Heap, this, _module.LinkedList.List), k#1) }
    true);
  ensures (forall k#1: int ::
    { Seq#Index(read($Heap, this, _module.LinkedList.List), k#1) }
    true
       ==>
      LitInt(0) <= k#1 && k#1 < Seq#Length(read($Heap, this, _module.LinkedList.List))
       ==> Seq#Index(read($Heap, this, _module.LinkedList.List), k#1)
         == Seq#Index(read($Heap, r#0, _module.LinkedList.List),
          Seq#Length(read($Heap, this, _module.LinkedList.List)) - 1 - k#1));
  free ensures _module.LinkedList.ReverseSeq#canCall(_module.LinkedList$T, read($Heap, this, _module.LinkedList.List));
  ensures Seq#Equal(read($Heap, r#0, _module.LinkedList.List),
    _module.LinkedList.ReverseSeq(_module.LinkedList$T, $LS($LS($LZ)), read($Heap, this, _module.LinkedList.List)));
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.LinkedList.Reverse(_module.LinkedList$T: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.LinkedList(_module.LinkedList$T))
         && $IsAlloc(this, Tclass._module.LinkedList(_module.LinkedList$T), $Heap))
   returns (r#0: ref
       where $Is(r#0, Tclass._module.LinkedList(_module.LinkedList$T))
         && $IsAlloc(r#0, Tclass._module.LinkedList(_module.LinkedList$T), $Heap),
    $_reverifyPost: bool);
  free requires 7 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, this)
     &&
    _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, this)
     &&
    read($Heap, this, _module.LinkedList.Repr)[$Box(this)]
     && LitInt(0) <= read($Heap, this, _module.LinkedList.length)
     && read($Heap, this, _module.LinkedList.length)
       == Seq#Length(read($Heap, this, _module.LinkedList.List))
     && (read($Heap, this, _module.LinkedList.length) == LitInt(0)
       ==> Seq#Equal(read($Heap, this, _module.LinkedList.List), Seq#Empty(): Seq Box)
         && read($Heap, this, _module.LinkedList.tail) == null)
     && (read($Heap, this, _module.LinkedList.length) != 0
       ==> read($Heap, this, _module.LinkedList.tail) != null
         && read($Heap, this, _module.LinkedList.Repr)[$Box(read($Heap, this, _module.LinkedList.tail))]
         && Set#Subset(read($Heap, read($Heap, this, _module.LinkedList.tail), _module.LinkedList.Repr),
          read($Heap, this, _module.LinkedList.Repr))
         && !read($Heap, read($Heap, this, _module.LinkedList.tail), _module.LinkedList.Repr)[$Box(this)]
         && _module.LinkedList.Valid(_module.LinkedList$T,
          $LS($LZ),
          $Heap,
          read($Heap, this, _module.LinkedList.tail))
         && Seq#Equal(read($Heap, this, _module.LinkedList.List),
          Seq#Append(Seq#Build(Seq#Empty(): Seq Box, read($Heap, this, _module.LinkedList.head)),
            read($Heap, read($Heap, this, _module.LinkedList.tail), _module.LinkedList.List)))
         && read($Heap, this, _module.LinkedList.length)
           == read($Heap, read($Heap, this, _module.LinkedList.tail), _module.LinkedList.length)
             + 1);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures r#0 != null
     ==> _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, r#0);
  ensures r#0 != null;
  ensures _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, r#0)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, r#0)
       || read($Heap, r#0, _module.LinkedList.Repr)[$Box(r#0)];
  ensures _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, r#0)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, r#0)
       || LitInt(0) <= read($Heap, r#0, _module.LinkedList.length);
  ensures _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, r#0)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, r#0)
       || read($Heap, r#0, _module.LinkedList.length)
         == Seq#Length(read($Heap, r#0, _module.LinkedList.List));
  ensures _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, r#0)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, r#0)
       || (read($Heap, r#0, _module.LinkedList.length) == LitInt(0)
         ==> Seq#Equal(read($Heap, r#0, _module.LinkedList.List), Seq#Empty(): Seq Box));
  ensures _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, r#0)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, r#0)
       || (read($Heap, r#0, _module.LinkedList.length) == LitInt(0)
         ==> read($Heap, r#0, _module.LinkedList.tail) == null);
  ensures _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, r#0)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, r#0)
       || (read($Heap, r#0, _module.LinkedList.length) != 0
         ==> read($Heap, r#0, _module.LinkedList.tail) != null);
  ensures _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, r#0)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, r#0)
       || (read($Heap, r#0, _module.LinkedList.length) != 0
         ==> read($Heap, r#0, _module.LinkedList.Repr)[$Box(read($Heap, r#0, _module.LinkedList.tail))]);
  ensures _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, r#0)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, r#0)
       || (read($Heap, r#0, _module.LinkedList.length) != 0
         ==> Set#Subset(read($Heap, read($Heap, r#0, _module.LinkedList.tail), _module.LinkedList.Repr),
          read($Heap, r#0, _module.LinkedList.Repr)));
  ensures _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, r#0)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, r#0)
       || (read($Heap, r#0, _module.LinkedList.length) != 0
         ==> !read($Heap, read($Heap, r#0, _module.LinkedList.tail), _module.LinkedList.Repr)[$Box(r#0)]);
  ensures _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, r#0)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, r#0)
       || (read($Heap, r#0, _module.LinkedList.length) != 0
         ==> _module.LinkedList.Valid(_module.LinkedList$T,
          $LS($LS($LZ)),
          $Heap,
          read($Heap, r#0, _module.LinkedList.tail)));
  ensures _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, r#0)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, r#0)
       || (read($Heap, r#0, _module.LinkedList.length) != 0
         ==> Seq#Equal(read($Heap, r#0, _module.LinkedList.List),
          Seq#Append(Seq#Build(Seq#Empty(): Seq Box, read($Heap, r#0, _module.LinkedList.head)),
            read($Heap, read($Heap, r#0, _module.LinkedList.tail), _module.LinkedList.List))));
  ensures _module.LinkedList.Valid#canCall(_module.LinkedList$T, $Heap, r#0)
     ==> _module.LinkedList.Valid(_module.LinkedList$T, $LS($LZ), $Heap, r#0)
       || (read($Heap, r#0, _module.LinkedList.length) != 0
         ==> read($Heap, r#0, _module.LinkedList.length)
           == read($Heap, read($Heap, r#0, _module.LinkedList.tail), _module.LinkedList.length)
             + 1);
  ensures Seq#Length(read($Heap, this, _module.LinkedList.List))
     == Seq#Length(read($Heap, r#0, _module.LinkedList.List));
  free ensures (forall k#1: int ::
    { Seq#Index(read($Heap, this, _module.LinkedList.List), k#1) }
    true);
  ensures (forall k#1: int ::
    { Seq#Index(read($Heap, this, _module.LinkedList.List), k#1) }
    true
       ==>
      LitInt(0) <= k#1 && k#1 < Seq#Length(read($Heap, this, _module.LinkedList.List))
       ==> Seq#Index(read($Heap, this, _module.LinkedList.List), k#1)
         == Seq#Index(read($Heap, r#0, _module.LinkedList.List),
          Seq#Length(read($Heap, this, _module.LinkedList.List)) - 1 - k#1));
  free ensures _module.LinkedList.ReverseSeq#canCall(_module.LinkedList$T, read($Heap, this, _module.LinkedList.List));
  ensures Seq#Equal(read($Heap, r#0, _module.LinkedList.List),
    _module.LinkedList.ReverseSeq(_module.LinkedList$T, $LS($LS($LZ)), read($Heap, this, _module.LinkedList.List)));
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.LinkedList.Reverse(_module.LinkedList$T: Ty, this: ref) returns (r#0: ref, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs##0: ref
     where $Is($rhs##0, Tclass._module.LinkedList(_module.LinkedList$T))
       && $IsAlloc($rhs##0, Tclass._module.LinkedList(_module.LinkedList$T), $Heap);
  var e#0: ref
     where $Is(e#0, Tclass._module.LinkedList(_module.LinkedList$T))
       && $IsAlloc(e#0, Tclass._module.LinkedList(_module.LinkedList$T), $Heap);
  var $nw: ref;
  var $rhs##1: ref
     where $Is($rhs##1, Tclass._module.LinkedList(_module.LinkedList$T))
       && $IsAlloc($rhs##1, Tclass._module.LinkedList(_module.LinkedList$T), $Heap);
  var d##0: Box;
  var $rhs##2: ref
     where $Is($rhs##2, Tclass._module.LinkedList(_module.LinkedList$T))
       && $IsAlloc($rhs##2, Tclass._module.LinkedList(_module.LinkedList$T), $Heap);
  var end##0: ref;

    // AddMethodImpl: Reverse, Impl$$_module.LinkedList.Reverse
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "Problem5-DoubleEndedQueue.dfy(150,2): initial state"} true;
    $_reverifyPost := false;
    // ----- if statement ----- Problem5-DoubleEndedQueue.dfy(151,5)
    assume true;
    if (read($Heap, this, _module.LinkedList.length) == LitInt(0))
    {
        // ----- assignment statement ----- Problem5-DoubleEndedQueue.dfy(152,9)
        assume true;
        assume true;
        r#0 := this;
        assume {:captureState "Problem5-DoubleEndedQueue.dfy(152,15)"} true;
    }
    else
    {
        // ----- call statement ----- Problem5-DoubleEndedQueue.dfy(154,24)
        assume true;
        // TrCallStmt: Adding lhs Microsoft.Dafny.IdentifierExpr with type LinkedList<T>
        // TrCallStmt: Before ProcessCallStmt
        assert read($Heap, this, _module.LinkedList.tail) != null;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assert Set#Subset(read($Heap, read($Heap, this, _module.LinkedList.tail), _module.LinkedList.Repr),
            read(old($Heap), this, _module.LinkedList.Repr))
           && !Set#Subset(read(old($Heap), this, _module.LinkedList.Repr),
            read($Heap, read($Heap, this, _module.LinkedList.tail), _module.LinkedList.Repr));
        // ProcessCallStmt: Make the call
        call $rhs##0 := Call$$_module.LinkedList.Reverse(_module.LinkedList$T, read($Heap, this, _module.LinkedList.tail));
        // TrCallStmt: After ProcessCallStmt
        r#0 := $rhs##0;
        assume {:captureState "Problem5-DoubleEndedQueue.dfy(154,25)"} true;
        // ----- assignment statement ----- Problem5-DoubleEndedQueue.dfy(155,13)
        assume true;
        havoc $nw;
        assume $nw != null
           &&
          !read($Heap, $nw, alloc)
           && dtype($nw) == Tclass._module.LinkedList(_module.LinkedList$T);
        $Heap := update($Heap, $nw, alloc, true);
        assume $IsGoodHeap($Heap);
        assume $IsHeapAnchor($Heap);
        // ----- init call statement ----- Problem5-DoubleEndedQueue.dfy(155,34)
        // TrCallStmt: Before ProcessCallStmt
        assert (forall<alpha> $o: ref, $f: Field alpha ::
          $o != null && read($Heap, $o, alloc) && $o == $nw ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$_module.LinkedList.Init(_module.LinkedList$T, $nw);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "Problem5-DoubleEndedQueue.dfy(155,39)"} true;
        e#0 := $nw;
        assume {:captureState "Problem5-DoubleEndedQueue.dfy(155,39)"} true;
        // ----- call statement ----- Problem5-DoubleEndedQueue.dfy(156,18)
        assume true;
        // TrCallStmt: Adding lhs Microsoft.Dafny.IdentifierExpr with type LinkedList<T>
        // TrCallStmt: Before ProcessCallStmt
        assert e#0 != null;
        assume true;
        // ProcessCallStmt: CheckSubrange
        d##0 := read($Heap, this, _module.LinkedList.head);
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call $rhs##1 := Call$$_module.LinkedList.Cons(_module.LinkedList$T, e#0, d##0);
        // TrCallStmt: After ProcessCallStmt
        e#0 := $rhs##1;
        assume {:captureState "Problem5-DoubleEndedQueue.dfy(156,23)"} true;
        // ----- call statement ----- Problem5-DoubleEndedQueue.dfy(157,20)
        assume true;
        // TrCallStmt: Adding lhs Microsoft.Dafny.IdentifierExpr with type LinkedList<T>
        // TrCallStmt: Before ProcessCallStmt
        assert r#0 != null;
        assume true;
        // ProcessCallStmt: CheckSubrange
        end##0 := e#0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call $rhs##2 := Call$$_module.LinkedList.Concat(_module.LinkedList$T, r#0, end##0);
        // TrCallStmt: After ProcessCallStmt
        r#0 := $rhs##2;
        assume {:captureState "Problem5-DoubleEndedQueue.dfy(157,22)"} true;
    }
}



// function declaration for _module.LinkedList.ReverseSeq
function _module.LinkedList.ReverseSeq(_module.LinkedList$T: Ty, $ly: LayerType, s#0: Seq Box) : Seq Box;

function _module.LinkedList.ReverseSeq#canCall(_module.LinkedList$T: Ty, s#0: Seq Box) : bool;

// layer synonym axiom
axiom (forall _module.LinkedList$T: Ty, $ly: LayerType, s#0: Seq Box ::
  { _module.LinkedList.ReverseSeq(_module.LinkedList$T, $LS($ly), s#0) }
  _module.LinkedList.ReverseSeq(_module.LinkedList$T, $LS($ly), s#0)
     == _module.LinkedList.ReverseSeq(_module.LinkedList$T, $ly, s#0));

// fuel synonym axiom
axiom (forall _module.LinkedList$T: Ty, $ly: LayerType, s#0: Seq Box ::
  { _module.LinkedList.ReverseSeq(_module.LinkedList$T, AsFuelBottom($ly), s#0) }
  _module.LinkedList.ReverseSeq(_module.LinkedList$T, $ly, s#0)
     == _module.LinkedList.ReverseSeq(_module.LinkedList$T, $LZ, s#0));

// consequence axiom for _module.LinkedList.ReverseSeq
axiom 1 <= $FunctionContextHeight
   ==> (forall _module.LinkedList$T: Ty, $ly: LayerType, s#0: Seq Box ::
    { _module.LinkedList.ReverseSeq(_module.LinkedList$T, $ly, s#0) }
    _module.LinkedList.ReverseSeq#canCall(_module.LinkedList$T, s#0)
         || (1 != $FunctionContextHeight && $Is(s#0, TSeq(_module.LinkedList$T)))
       ==> $Is(_module.LinkedList.ReverseSeq(_module.LinkedList$T, $ly, s#0),
        TSeq(_module.LinkedList$T)));

function _module.LinkedList.ReverseSeq#requires(Ty, LayerType, Seq Box) : bool;

// #requires axiom for _module.LinkedList.ReverseSeq
axiom (forall _module.LinkedList$T: Ty, $ly: LayerType, s#0: Seq Box ::
  { _module.LinkedList.ReverseSeq#requires(_module.LinkedList$T, $ly, s#0) }
  $Is(s#0, TSeq(_module.LinkedList$T))
     ==> _module.LinkedList.ReverseSeq#requires(_module.LinkedList$T, $ly, s#0) == true);

// definition axiom for _module.LinkedList.ReverseSeq(revealed)
axiom 1 <= $FunctionContextHeight
   ==> (forall _module.LinkedList$T: Ty, $ly: LayerType, s#0: Seq Box ::
    { _module.LinkedList.ReverseSeq(_module.LinkedList$T, $LS($ly), s#0) }
    _module.LinkedList.ReverseSeq#canCall(_module.LinkedList$T, s#0)
         || (1 != $FunctionContextHeight && $Is(s#0, TSeq(_module.LinkedList$T)))
       ==> (!Seq#Equal(s#0, Seq#Empty(): Seq Box)
           ==> _module.LinkedList.ReverseSeq#canCall(_module.LinkedList$T, Seq#Drop(s#0, LitInt(1))))
         && _module.LinkedList.ReverseSeq(_module.LinkedList$T, $LS($ly), s#0)
           == (if Seq#Equal(s#0, Seq#Empty(): Seq Box)
             then Seq#Empty(): Seq Box
             else Seq#Append(_module.LinkedList.ReverseSeq(_module.LinkedList$T, $ly, Seq#Drop(s#0, LitInt(1))),
              Seq#Build(Seq#Empty(): Seq Box, Seq#Index(s#0, LitInt(0))))));

// definition axiom for _module.LinkedList.ReverseSeq for all literals(revealed)
axiom 1 <= $FunctionContextHeight
   ==> (forall _module.LinkedList$T: Ty, $ly: LayerType, s#0: Seq Box ::
    {:weight 3} { _module.LinkedList.ReverseSeq(_module.LinkedList$T, $LS($ly), Lit(s#0)) }
    _module.LinkedList.ReverseSeq#canCall(_module.LinkedList$T, Lit(s#0))
         || (1 != $FunctionContextHeight && $Is(s#0, TSeq(_module.LinkedList$T)))
       ==> (!Seq#Equal(s#0, Seq#Empty(): Seq Box)
           ==> _module.LinkedList.ReverseSeq#canCall(_module.LinkedList$T, Lit(Seq#Drop(Lit(s#0), LitInt(1)))))
         && _module.LinkedList.ReverseSeq(_module.LinkedList$T, $LS($ly), Lit(s#0))
           == (if Seq#Equal(s#0, Seq#Empty(): Seq Box)
             then Seq#Empty(): Seq Box
             else Seq#Append(_module.LinkedList.ReverseSeq(_module.LinkedList$T, $LS($ly), Lit(Seq#Drop(Lit(s#0), LitInt(1)))),
              Seq#Build(Seq#Empty(): Seq Box, Seq#Index(Lit(s#0), LitInt(0))))));

procedure CheckWellformed$$_module.LinkedList.ReverseSeq(_module.LinkedList$T: Ty,
    s#0: Seq Box where $Is(s#0, TSeq(_module.LinkedList$T)));
  free requires 1 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.LinkedList.ReverseSeq(_module.LinkedList$T: Ty, s#0: Seq Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##s#0: Seq Box;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function ReverseSeq
    assume {:captureState "Problem5-DoubleEndedQueue.dfy(161,18): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.LinkedList.ReverseSeq(_module.LinkedList$T, $LS($LZ), s#0),
          TSeq(_module.LinkedList$T));
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
          $o != null && read($Heap, $o, alloc) ==> false);
        if (Seq#Equal(s#0, Seq#Empty(): Seq Box))
        {
            assume _module.LinkedList.ReverseSeq(_module.LinkedList$T, $LS($LZ), s#0)
               == Lit(Seq#Empty(): Seq Box);
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.LinkedList.ReverseSeq(_module.LinkedList$T, $LS($LZ), s#0),
              TSeq(_module.LinkedList$T));
        }
        else
        {
            assert 0 <= LitInt(1) && LitInt(1) <= Seq#Length(s#0);
            ##s#0 := Seq#Drop(s#0, LitInt(1));
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#0, TSeq(_module.LinkedList$T), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert Seq#Rank(##s#0) < Seq#Rank(s#0);
            assume _module.LinkedList.ReverseSeq#canCall(_module.LinkedList$T, Seq#Drop(s#0, LitInt(1)));
            assert 0 <= LitInt(0) && LitInt(0) < Seq#Length(s#0);
            assume _module.LinkedList.ReverseSeq(_module.LinkedList$T, $LS($LZ), s#0)
               == Seq#Append(_module.LinkedList.ReverseSeq(_module.LinkedList$T, $LS($LZ), Seq#Drop(s#0, LitInt(1))),
                Seq#Build(Seq#Empty(): Seq Box, Seq#Index(s#0, LitInt(0))));
            assume _module.LinkedList.ReverseSeq#canCall(_module.LinkedList$T, Seq#Drop(s#0, LitInt(1)));
            // CheckWellformedWithResult: any expression
            assume $Is(_module.LinkedList.ReverseSeq(_module.LinkedList$T, $LS($LZ), s#0),
              TSeq(_module.LinkedList$T));
        }

        assert b$reqreads#0;
    }
}



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

const unique field$front: NameFamily;

const unique field$rear: NameFamily;

const unique field$Repr: NameFamily;

const unique field$List: NameFamily;

const unique field$length: NameFamily;

const unique field$tail: NameFamily;

const unique field$head: NameFamily;