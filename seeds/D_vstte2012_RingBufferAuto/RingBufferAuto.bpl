// Dafny 2.0.0.00922 technical preview 0
// Command Line Options: /compile:0 /noVerify /print:RingBufferAuto.bpl RingBufferAuto.dfy

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

const unique class._module.RingBuffer: ClassName;

function Tclass._module.RingBuffer(Ty) : Ty;

// Tclass._module.RingBuffer Tag
axiom (forall _module.RingBuffer$T: Ty ::
  { Tclass._module.RingBuffer(_module.RingBuffer$T) }
  Tag(Tclass._module.RingBuffer(_module.RingBuffer$T))
     == Tagclass._module.RingBuffer);

const unique Tagclass._module.RingBuffer: TyTag;

// Tclass._module.RingBuffer injectivity 0
axiom (forall _module.RingBuffer$T: Ty ::
  { Tclass._module.RingBuffer(_module.RingBuffer$T) }
  Tclass._module.RingBuffer_0(Tclass._module.RingBuffer(_module.RingBuffer$T))
     == _module.RingBuffer$T);

function Tclass._module.RingBuffer_0(Ty) : Ty;

// Box/unbox axiom for Tclass._module.RingBuffer
axiom (forall _module.RingBuffer$T: Ty, bx: Box ::
  { $IsBox(bx, Tclass._module.RingBuffer(_module.RingBuffer$T)) }
  $IsBox(bx, Tclass._module.RingBuffer(_module.RingBuffer$T))
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.RingBuffer(_module.RingBuffer$T)));

// RingBuffer: Class $Is
axiom (forall _module.RingBuffer$T: Ty, $o: ref ::
  { $Is($o, Tclass._module.RingBuffer(_module.RingBuffer$T)) }
  $Is($o, Tclass._module.RingBuffer(_module.RingBuffer$T))
     <==> $o == null || dtype($o) == Tclass._module.RingBuffer(_module.RingBuffer$T));

// RingBuffer: Class $IsAlloc
axiom (forall _module.RingBuffer$T: Ty, $o: ref, $h: Heap ::
  { $IsAlloc($o, Tclass._module.RingBuffer(_module.RingBuffer$T), $h) }
  $IsAlloc($o, Tclass._module.RingBuffer(_module.RingBuffer$T), $h)
     <==> $o == null || read($h, $o, alloc));

axiom FDim(_module.RingBuffer.Contents) == 0
   && FieldOfDecl(class._module.RingBuffer, field$Contents)
     == _module.RingBuffer.Contents
   && $IsGhostField(_module.RingBuffer.Contents);

const _module.RingBuffer.Contents: Field (Seq Box);

// RingBuffer.Contents: Allocation axiom
axiom (forall _module.RingBuffer$T: Ty, $h: Heap, $o: ref ::
  { read($h, $o, _module.RingBuffer.Contents), Tclass._module.RingBuffer(_module.RingBuffer$T) }
  $IsGoodHeap($h)
       && $o != null
       && dtype($o) == Tclass._module.RingBuffer(_module.RingBuffer$T)
     ==> $Is(read($h, $o, _module.RingBuffer.Contents), TSeq(_module.RingBuffer$T))
       && (read($h, $o, alloc)
         ==> $IsAlloc(read($h, $o, _module.RingBuffer.Contents), TSeq(_module.RingBuffer$T), $h)));

axiom FDim(_module.RingBuffer.N) == 0
   && FieldOfDecl(class._module.RingBuffer, field$N) == _module.RingBuffer.N
   && $IsGhostField(_module.RingBuffer.N);

const _module.RingBuffer.N: Field int;

// RingBuffer.N: Allocation axiom
axiom (forall _module.RingBuffer$T: Ty, $h: Heap, $o: ref ::
  { read($h, $o, _module.RingBuffer.N), Tclass._module.RingBuffer(_module.RingBuffer$T) }
  $IsGoodHeap($h)
       && $o != null
       && dtype($o) == Tclass._module.RingBuffer(_module.RingBuffer$T)
     ==> $Is(read($h, $o, _module.RingBuffer.N), Tclass._System.nat())
       && (read($h, $o, alloc)
         ==> $IsAlloc(read($h, $o, _module.RingBuffer.N), Tclass._System.nat(), $h)));

axiom FDim(_module.RingBuffer.data) == 0
   && FieldOfDecl(class._module.RingBuffer, field$data) == _module.RingBuffer.data
   && !$IsGhostField(_module.RingBuffer.data);

const _module.RingBuffer.data: Field ref;

// RingBuffer.data: Allocation axiom
axiom (forall _module.RingBuffer$T: Ty, $h: Heap, $o: ref ::
  { read($h, $o, _module.RingBuffer.data), Tclass._module.RingBuffer(_module.RingBuffer$T) }
  $IsGoodHeap($h)
       && $o != null
       && dtype($o) == Tclass._module.RingBuffer(_module.RingBuffer$T)
     ==> $Is(read($h, $o, _module.RingBuffer.data),
        Tclass._System.array(_module.RingBuffer$T))
       && (read($h, $o, alloc)
         ==> $IsAlloc(read($h, $o, _module.RingBuffer.data),
          Tclass._System.array(_module.RingBuffer$T),
          $h)));

axiom FDim(_module.RingBuffer.start) == 0
   && FieldOfDecl(class._module.RingBuffer, field$start) == _module.RingBuffer.start
   && !$IsGhostField(_module.RingBuffer.start);

const _module.RingBuffer.start: Field int;

// RingBuffer.start: Allocation axiom
axiom (forall _module.RingBuffer$T: Ty, $h: Heap, $o: ref ::
  { read($h, $o, _module.RingBuffer.start), Tclass._module.RingBuffer(_module.RingBuffer$T) }
  $IsGoodHeap($h)
       && $o != null
       && dtype($o) == Tclass._module.RingBuffer(_module.RingBuffer$T)
     ==> $Is(read($h, $o, _module.RingBuffer.start), Tclass._System.nat())
       && (read($h, $o, alloc)
         ==> $IsAlloc(read($h, $o, _module.RingBuffer.start), Tclass._System.nat(), $h)));

axiom FDim(_module.RingBuffer.len) == 0
   && FieldOfDecl(class._module.RingBuffer, field$len) == _module.RingBuffer.len
   && !$IsGhostField(_module.RingBuffer.len);

const _module.RingBuffer.len: Field int;

// RingBuffer.len: Allocation axiom
axiom (forall _module.RingBuffer$T: Ty, $h: Heap, $o: ref ::
  { read($h, $o, _module.RingBuffer.len), Tclass._module.RingBuffer(_module.RingBuffer$T) }
  $IsGoodHeap($h)
       && $o != null
       && dtype($o) == Tclass._module.RingBuffer(_module.RingBuffer$T)
     ==> $Is(read($h, $o, _module.RingBuffer.len), Tclass._System.nat())
       && (read($h, $o, alloc)
         ==> $IsAlloc(read($h, $o, _module.RingBuffer.len), Tclass._System.nat(), $h)));

// function declaration for _module.RingBuffer.Valid
function _module.RingBuffer.Valid(_module.RingBuffer$T: Ty, $heap: Heap, this: ref) : bool;

function _module.RingBuffer.Valid#canCall(_module.RingBuffer$T: Ty, $heap: Heap, this: ref) : bool;

axiom FDim(_module.RingBuffer.Repr) == 0
   && FieldOfDecl(class._module.RingBuffer, field$Repr) == _module.RingBuffer.Repr
   && $IsGhostField(_module.RingBuffer.Repr);

// frame axiom for _module.RingBuffer.Valid
axiom (forall _module.RingBuffer$T: Ty, $h0: Heap, $h1: Heap, this: ref ::
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.RingBuffer.Valid(_module.RingBuffer$T, $h1, this) }
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       &&
      this != null
       && $Is(this, Tclass._module.RingBuffer(_module.RingBuffer$T))
       &&
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==>
    (forall<alpha> $o: ref, $f: Field alpha ::
      $o != null && ($o == this || read($h0, this, _module.RingBuffer.Repr)[$Box($o)])
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $h0, this)
       == _module.RingBuffer.Valid(_module.RingBuffer$T, $h1, this));

// consequence axiom for _module.RingBuffer.Valid
axiom 1 <= $FunctionContextHeight
   ==> (forall _module.RingBuffer$T: Ty, $Heap: Heap, this: ref ::
    { _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this) }
    _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
         || (1 != $FunctionContextHeight
           &&
          $IsGoodHeap($Heap)
           &&
          this != null
           &&
          $Is(this, Tclass._module.RingBuffer(_module.RingBuffer$T))
           && $IsAlloc(this, Tclass._module.RingBuffer(_module.RingBuffer$T), $Heap))
       ==> true);

function _module.RingBuffer.Valid#requires(Ty, Heap, ref) : bool;

// #requires axiom for _module.RingBuffer.Valid
axiom (forall _module.RingBuffer$T: Ty, $Heap: Heap, this: ref ::
  { _module.RingBuffer.Valid#requires(_module.RingBuffer$T, $Heap, this) }
  $IsGoodHeap($Heap)
       &&
      this != null
       &&
      $Is(this, Tclass._module.RingBuffer(_module.RingBuffer$T))
       && $IsAlloc(this, Tclass._module.RingBuffer(_module.RingBuffer$T), $Heap)
     ==> _module.RingBuffer.Valid#requires(_module.RingBuffer$T, $Heap, this) == true);

// definition axiom for _module.RingBuffer.Valid(revealed)
axiom 1 <= $FunctionContextHeight
   ==> (forall _module.RingBuffer$T: Ty, $Heap: Heap, this: ref ::
    { _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this) }
    _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
         || (1 != $FunctionContextHeight
           &&
          $IsGoodHeap($Heap)
           &&
          this != null
           &&
          $Is(this, Tclass._module.RingBuffer(_module.RingBuffer$T))
           && $IsAlloc(this, Tclass._module.RingBuffer(_module.RingBuffer$T), $Heap))
       ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
         == (
          read($Heap, this, _module.RingBuffer.Repr)[$Box(this)]
           && !read($Heap, this, _module.RingBuffer.Repr)[$Box(null)]
           &&
          (read($Heap, this, _module.RingBuffer.data) != null
             ==> read($Heap, this, _module.RingBuffer.Repr)[$Box(read($Heap, this, _module.RingBuffer.data))])
           &&
          read($Heap, this, _module.RingBuffer.data) != null
           && _System.array.Length(read($Heap, this, _module.RingBuffer.data))
             == read($Heap, this, _module.RingBuffer.N)
           && (read($Heap, this, _module.RingBuffer.N) == LitInt(0)
             ==> read($Heap, this, _module.RingBuffer.len)
                 == read($Heap, this, _module.RingBuffer.start)
               && read($Heap, this, _module.RingBuffer.start) == LitInt(0)
               && Seq#Equal(read($Heap, this, _module.RingBuffer.Contents), Seq#Empty(): Seq Box))
           && (read($Heap, this, _module.RingBuffer.N) != 0
             ==> read($Heap, this, _module.RingBuffer.len)
                 <= read($Heap, this, _module.RingBuffer.N)
               && read($Heap, this, _module.RingBuffer.start)
                 < read($Heap, this, _module.RingBuffer.N))
           && Seq#Equal(read($Heap, this, _module.RingBuffer.Contents),
            (if read($Heap, this, _module.RingBuffer.start)
                   + read($Heap, this, _module.RingBuffer.len)
                 <= read($Heap, this, _module.RingBuffer.N)
               then Seq#Drop(Seq#Take(Seq#FromArray($Heap, read($Heap, this, _module.RingBuffer.data)),
                  read($Heap, this, _module.RingBuffer.start)
                     + read($Heap, this, _module.RingBuffer.len)),
                read($Heap, this, _module.RingBuffer.start))
               else Seq#Append(Seq#Drop(Seq#FromArray($Heap, read($Heap, this, _module.RingBuffer.data)),
                  read($Heap, this, _module.RingBuffer.start)),
                Seq#Take(Seq#FromArray($Heap, read($Heap, this, _module.RingBuffer.data)),
                  read($Heap, this, _module.RingBuffer.start)
                       + read($Heap, this, _module.RingBuffer.len)
                     - read($Heap, this, _module.RingBuffer.N)))))));

procedure CheckWellformed$$_module.RingBuffer.Valid(_module.RingBuffer$T: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.RingBuffer(_module.RingBuffer$T))
         && $IsAlloc(this, Tclass._module.RingBuffer(_module.RingBuffer$T), $Heap));
  free requires 1 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.RingBuffer.Valid(_module.RingBuffer$T: Ty, this: ref)
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
  var b$reqreads#26: bool;
  var b$reqreads#27: bool;
  var b$reqreads#28: bool;
  var b$reqreads#29: bool;
  var b$reqreads#30: bool;
  var b$reqreads#31: bool;
  var b$reqreads#32: bool;
  var b$reqreads#33: bool;
  var b$reqreads#34: bool;
  var b$reqreads#35: bool;

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
    b$reqreads#28 := true;
    b$reqreads#29 := true;
    b$reqreads#30 := true;
    b$reqreads#31 := true;
    b$reqreads#32 := true;
    b$reqreads#33 := true;
    b$reqreads#34 := true;
    b$reqreads#35 := true;

    // AddWellformednessCheck for function Valid
    assume {:captureState "RingBufferAuto.dfy(16,12): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc)
         ==> $o == this || read($Heap, this, _module.RingBuffer.Repr)[$Box($o)]);
    b$reqreads#0 := $_Frame[this, _module.RingBuffer.Repr];
    assert b$reqreads#0;
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
          $o != null && read($Heap, $o, alloc)
             ==> $o == this || read($Heap, this, _module.RingBuffer.Repr)[$Box($o)]);
        b$reqreads#1 := $_Frame[this, _module.RingBuffer.Repr];
        if (read($Heap, this, _module.RingBuffer.Repr)[$Box(this)])
        {
            b$reqreads#2 := $_Frame[this, _module.RingBuffer.Repr];
        }

        if (read($Heap, this, _module.RingBuffer.Repr)[$Box(this)]
           && !read($Heap, this, _module.RingBuffer.Repr)[$Box(null)])
        {
            b$reqreads#3 := $_Frame[this, _module.RingBuffer.data];
            if (read($Heap, this, _module.RingBuffer.data) != null)
            {
                b$reqreads#4 := $_Frame[this, _module.RingBuffer.data];
                b$reqreads#5 := $_Frame[this, _module.RingBuffer.Repr];
            }

            if (read($Heap, this, _module.RingBuffer.data) != null
               ==> read($Heap, this, _module.RingBuffer.Repr)[$Box(read($Heap, this, _module.RingBuffer.data))])
            {
                b$reqreads#6 := $_Frame[this, _module.RingBuffer.data];
                if (read($Heap, this, _module.RingBuffer.data) != null)
                {
                    b$reqreads#7 := $_Frame[this, _module.RingBuffer.data];
                    assert read($Heap, this, _module.RingBuffer.data) != null;
                    b$reqreads#8 := $_Frame[this, _module.RingBuffer.N];
                }

                if (read($Heap, this, _module.RingBuffer.data) != null
                   && _System.array.Length(read($Heap, this, _module.RingBuffer.data))
                     == read($Heap, this, _module.RingBuffer.N))
                {
                    b$reqreads#9 := $_Frame[this, _module.RingBuffer.N];
                    if (read($Heap, this, _module.RingBuffer.N) == LitInt(0))
                    {
                        b$reqreads#10 := $_Frame[this, _module.RingBuffer.len];
                        b$reqreads#11 := $_Frame[this, _module.RingBuffer.start];
                        if (read($Heap, this, _module.RingBuffer.len)
                           == read($Heap, this, _module.RingBuffer.start))
                        {
                            b$reqreads#12 := $_Frame[this, _module.RingBuffer.start];
                        }

                        if (read($Heap, this, _module.RingBuffer.len)
                             == read($Heap, this, _module.RingBuffer.start)
                           && read($Heap, this, _module.RingBuffer.start) == LitInt(0))
                        {
                            b$reqreads#13 := $_Frame[this, _module.RingBuffer.Contents];
                        }
                    }
                }

                if (read($Heap, this, _module.RingBuffer.data) != null
                   && _System.array.Length(read($Heap, this, _module.RingBuffer.data))
                     == read($Heap, this, _module.RingBuffer.N)
                   && (read($Heap, this, _module.RingBuffer.N) == LitInt(0)
                     ==> read($Heap, this, _module.RingBuffer.len)
                         == read($Heap, this, _module.RingBuffer.start)
                       && read($Heap, this, _module.RingBuffer.start) == LitInt(0)
                       && Seq#Equal(read($Heap, this, _module.RingBuffer.Contents), Seq#Empty(): Seq Box)))
                {
                    b$reqreads#14 := $_Frame[this, _module.RingBuffer.N];
                    if (read($Heap, this, _module.RingBuffer.N) != 0)
                    {
                        b$reqreads#15 := $_Frame[this, _module.RingBuffer.len];
                        b$reqreads#16 := $_Frame[this, _module.RingBuffer.N];
                        if (read($Heap, this, _module.RingBuffer.len)
                           <= read($Heap, this, _module.RingBuffer.N))
                        {
                            b$reqreads#17 := $_Frame[this, _module.RingBuffer.start];
                            b$reqreads#18 := $_Frame[this, _module.RingBuffer.N];
                        }
                    }
                }

                if (read($Heap, this, _module.RingBuffer.data) != null
                   && _System.array.Length(read($Heap, this, _module.RingBuffer.data))
                     == read($Heap, this, _module.RingBuffer.N)
                   && (read($Heap, this, _module.RingBuffer.N) == LitInt(0)
                     ==> read($Heap, this, _module.RingBuffer.len)
                         == read($Heap, this, _module.RingBuffer.start)
                       && read($Heap, this, _module.RingBuffer.start) == LitInt(0)
                       && Seq#Equal(read($Heap, this, _module.RingBuffer.Contents), Seq#Empty(): Seq Box))
                   && (read($Heap, this, _module.RingBuffer.N) != 0
                     ==> read($Heap, this, _module.RingBuffer.len)
                         <= read($Heap, this, _module.RingBuffer.N)
                       && read($Heap, this, _module.RingBuffer.start)
                         < read($Heap, this, _module.RingBuffer.N)))
                {
                    b$reqreads#19 := $_Frame[this, _module.RingBuffer.Contents];
                    b$reqreads#20 := $_Frame[this, _module.RingBuffer.start];
                    b$reqreads#21 := $_Frame[this, _module.RingBuffer.len];
                    b$reqreads#22 := $_Frame[this, _module.RingBuffer.N];
                    if (read($Heap, this, _module.RingBuffer.start)
                         + read($Heap, this, _module.RingBuffer.len)
                       <= read($Heap, this, _module.RingBuffer.N))
                    {
                        b$reqreads#23 := $_Frame[this, _module.RingBuffer.data];
                        assert read($Heap, this, _module.RingBuffer.data) != null;
                        b$reqreads#24 := $_Frame[this, _module.RingBuffer.start];
                        assert 0 <= read($Heap, this, _module.RingBuffer.start)
                           && read($Heap, this, _module.RingBuffer.start)
                             <= _System.array.Length(read($Heap, this, _module.RingBuffer.data));
                        b$reqreads#25 := $_Frame[this, _module.RingBuffer.start];
                        b$reqreads#26 := $_Frame[this, _module.RingBuffer.len];
                        assert read($Heap, this, _module.RingBuffer.start)
                             <= read($Heap, this, _module.RingBuffer.start)
                               + read($Heap, this, _module.RingBuffer.len)
                           && read($Heap, this, _module.RingBuffer.start)
                               + read($Heap, this, _module.RingBuffer.len)
                             <= _System.array.Length(read($Heap, this, _module.RingBuffer.data));
                        b$reqreads#27 := (forall $i: int ::
                          { $_Frame[read($Heap, this, _module.RingBuffer.data), IndexField($i)] }
                          read($Heap, this, _module.RingBuffer.start) <= $i
                               && $i
                                 < read($Heap, this, _module.RingBuffer.start)
                                   + read($Heap, this, _module.RingBuffer.len)
                             ==> $_Frame[read($Heap, this, _module.RingBuffer.data), IndexField($i)]);
                    }
                    else
                    {
                        b$reqreads#28 := $_Frame[this, _module.RingBuffer.data];
                        assert read($Heap, this, _module.RingBuffer.data) != null;
                        b$reqreads#29 := $_Frame[this, _module.RingBuffer.start];
                        assert 0 <= read($Heap, this, _module.RingBuffer.start)
                           && read($Heap, this, _module.RingBuffer.start)
                             <= _System.array.Length(read($Heap, this, _module.RingBuffer.data));
                        b$reqreads#30 := (forall $i: int ::
                          { $_Frame[read($Heap, this, _module.RingBuffer.data), IndexField($i)] }
                          read($Heap, this, _module.RingBuffer.start) <= $i
                               && $i < _System.array.Length(read($Heap, this, _module.RingBuffer.data))
                             ==> $_Frame[read($Heap, this, _module.RingBuffer.data), IndexField($i)]);
                        b$reqreads#31 := $_Frame[this, _module.RingBuffer.data];
                        assert read($Heap, this, _module.RingBuffer.data) != null;
                        b$reqreads#32 := $_Frame[this, _module.RingBuffer.start];
                        b$reqreads#33 := $_Frame[this, _module.RingBuffer.len];
                        b$reqreads#34 := $_Frame[this, _module.RingBuffer.N];
                        assert 0
                             <= read($Heap, this, _module.RingBuffer.start)
                                 + read($Heap, this, _module.RingBuffer.len)
                               - read($Heap, this, _module.RingBuffer.N)
                           && read($Heap, this, _module.RingBuffer.start)
                                 + read($Heap, this, _module.RingBuffer.len)
                               - read($Heap, this, _module.RingBuffer.N)
                             <= _System.array.Length(read($Heap, this, _module.RingBuffer.data));
                        b$reqreads#35 := (forall $i: int ::
                          { $_Frame[read($Heap, this, _module.RingBuffer.data), IndexField($i)] }
                          0 <= $i
                               && $i
                                 < read($Heap, this, _module.RingBuffer.start)
                                     + read($Heap, this, _module.RingBuffer.len)
                                   - read($Heap, this, _module.RingBuffer.N)
                             ==> $_Frame[read($Heap, this, _module.RingBuffer.data), IndexField($i)]);
                    }
                }
            }
        }

        assume _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
           == (
            read($Heap, this, _module.RingBuffer.Repr)[$Box(this)]
             && !read($Heap, this, _module.RingBuffer.Repr)[$Box(null)]
             &&
            (read($Heap, this, _module.RingBuffer.data) != null
               ==> read($Heap, this, _module.RingBuffer.Repr)[$Box(read($Heap, this, _module.RingBuffer.data))])
             &&
            read($Heap, this, _module.RingBuffer.data) != null
             && _System.array.Length(read($Heap, this, _module.RingBuffer.data))
               == read($Heap, this, _module.RingBuffer.N)
             && (read($Heap, this, _module.RingBuffer.N) == LitInt(0)
               ==> read($Heap, this, _module.RingBuffer.len)
                   == read($Heap, this, _module.RingBuffer.start)
                 && read($Heap, this, _module.RingBuffer.start) == LitInt(0)
                 && Seq#Equal(read($Heap, this, _module.RingBuffer.Contents), Seq#Empty(): Seq Box))
             && (read($Heap, this, _module.RingBuffer.N) != 0
               ==> read($Heap, this, _module.RingBuffer.len)
                   <= read($Heap, this, _module.RingBuffer.N)
                 && read($Heap, this, _module.RingBuffer.start)
                   < read($Heap, this, _module.RingBuffer.N))
             && Seq#Equal(read($Heap, this, _module.RingBuffer.Contents),
              (if read($Heap, this, _module.RingBuffer.start)
                     + read($Heap, this, _module.RingBuffer.len)
                   <= read($Heap, this, _module.RingBuffer.N)
                 then Seq#Drop(Seq#Take(Seq#FromArray($Heap, read($Heap, this, _module.RingBuffer.data)),
                    read($Heap, this, _module.RingBuffer.start)
                       + read($Heap, this, _module.RingBuffer.len)),
                  read($Heap, this, _module.RingBuffer.start))
                 else Seq#Append(Seq#Drop(Seq#FromArray($Heap, read($Heap, this, _module.RingBuffer.data)),
                    read($Heap, this, _module.RingBuffer.start)),
                  Seq#Take(Seq#FromArray($Heap, read($Heap, this, _module.RingBuffer.data)),
                    read($Heap, this, _module.RingBuffer.start)
                         + read($Heap, this, _module.RingBuffer.len)
                       - read($Heap, this, _module.RingBuffer.N))))));
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(_module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this), TBool);
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
        assert b$reqreads#28;
        assert b$reqreads#29;
        assert b$reqreads#30;
        assert b$reqreads#31;
        assert b$reqreads#32;
        assert b$reqreads#33;
        assert b$reqreads#34;
        assert b$reqreads#35;
    }
}



procedure CheckWellformed$$_module.RingBuffer.Create(_module.RingBuffer$T: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.RingBuffer(_module.RingBuffer$T))
         && $IsAlloc(this, Tclass._module.RingBuffer(_module.RingBuffer$T), $Heap),
    n#0: int where LitInt(0) <= n#0);
  free requires 2 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.RingBuffer.Create(_module.RingBuffer$T: Ty, n#0: int where LitInt(0) <= n#0)
   returns (this: ref
       where this != null
         &&
        $Is(this, Tclass._module.RingBuffer(_module.RingBuffer$T))
         && $IsAlloc(this, Tclass._module.RingBuffer(_module.RingBuffer$T), $Heap));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this);
  free ensures _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     &&
    _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
     &&
    read($Heap, this, _module.RingBuffer.Repr)[$Box(this)]
     && !read($Heap, this, _module.RingBuffer.Repr)[$Box(null)]
     &&
    (read($Heap, this, _module.RingBuffer.data) != null
       ==> read($Heap, this, _module.RingBuffer.Repr)[$Box(read($Heap, this, _module.RingBuffer.data))])
     &&
    read($Heap, this, _module.RingBuffer.data) != null
     && _System.array.Length(read($Heap, this, _module.RingBuffer.data))
       == read($Heap, this, _module.RingBuffer.N)
     && (read($Heap, this, _module.RingBuffer.N) == LitInt(0)
       ==> read($Heap, this, _module.RingBuffer.len)
           == read($Heap, this, _module.RingBuffer.start)
         && read($Heap, this, _module.RingBuffer.start) == LitInt(0)
         && Seq#Equal(read($Heap, this, _module.RingBuffer.Contents), Seq#Empty(): Seq Box))
     && (read($Heap, this, _module.RingBuffer.N) != 0
       ==> read($Heap, this, _module.RingBuffer.len)
           <= read($Heap, this, _module.RingBuffer.N)
         && read($Heap, this, _module.RingBuffer.start)
           < read($Heap, this, _module.RingBuffer.N))
     && Seq#Equal(read($Heap, this, _module.RingBuffer.Contents),
      (if read($Heap, this, _module.RingBuffer.start)
             + read($Heap, this, _module.RingBuffer.len)
           <= read($Heap, this, _module.RingBuffer.N)
         then Seq#Drop(Seq#Take(Seq#FromArray($Heap, read($Heap, this, _module.RingBuffer.data)),
            read($Heap, this, _module.RingBuffer.start)
               + read($Heap, this, _module.RingBuffer.len)),
          read($Heap, this, _module.RingBuffer.start))
         else Seq#Append(Seq#Drop(Seq#FromArray($Heap, read($Heap, this, _module.RingBuffer.data)),
            read($Heap, this, _module.RingBuffer.start)),
          Seq#Take(Seq#FromArray($Heap, read($Heap, this, _module.RingBuffer.data)),
            read($Heap, this, _module.RingBuffer.start)
                 + read($Heap, this, _module.RingBuffer.len)
               - read($Heap, this, _module.RingBuffer.N)))));
  free ensures true;
  ensures (forall $o: ref ::
    { read(old($Heap), $o, alloc) }
    read($Heap, this, _module.RingBuffer.Repr)[$Box($o)] && $o != this
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures true;
  ensures Seq#Equal(read($Heap, this, _module.RingBuffer.Contents), Seq#Empty(): Seq Box);
  ensures read($Heap, this, _module.RingBuffer.N) == n#0;
  // constructor allocates the object
  ensures !read(old($Heap), this, alloc);
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.RingBuffer.Create(_module.RingBuffer$T: Ty, n#0: int where LitInt(0) <= n#0)
   returns (this: ref, $_reverifyPost: bool);
  free requires 2 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this);
  ensures _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || read($Heap, this, _module.RingBuffer.Repr)[$Box(this)];
  ensures _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || !read($Heap, this, _module.RingBuffer.Repr)[$Box(null)];
  ensures _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || (read($Heap, this, _module.RingBuffer.data) != null
         ==> read($Heap, this, _module.RingBuffer.Repr)[$Box(read($Heap, this, _module.RingBuffer.data))]);
  ensures _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || read($Heap, this, _module.RingBuffer.data) != null;
  ensures _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || _System.array.Length(read($Heap, this, _module.RingBuffer.data))
         == read($Heap, this, _module.RingBuffer.N);
  ensures _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || (read($Heap, this, _module.RingBuffer.N) == LitInt(0)
         ==> read($Heap, this, _module.RingBuffer.len)
           == read($Heap, this, _module.RingBuffer.start));
  ensures _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || (read($Heap, this, _module.RingBuffer.N) == LitInt(0)
         ==> read($Heap, this, _module.RingBuffer.start) == LitInt(0));
  ensures _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || (read($Heap, this, _module.RingBuffer.N) == LitInt(0)
         ==> Seq#Equal(read($Heap, this, _module.RingBuffer.Contents), Seq#Empty(): Seq Box));
  ensures _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || (read($Heap, this, _module.RingBuffer.N) != 0
         ==> read($Heap, this, _module.RingBuffer.len)
           <= read($Heap, this, _module.RingBuffer.N));
  ensures _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || (read($Heap, this, _module.RingBuffer.N) != 0
         ==> read($Heap, this, _module.RingBuffer.start)
           < read($Heap, this, _module.RingBuffer.N));
  ensures _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || Seq#Equal(read($Heap, this, _module.RingBuffer.Contents),
        (if read($Heap, this, _module.RingBuffer.start)
               + read($Heap, this, _module.RingBuffer.len)
             <= read($Heap, this, _module.RingBuffer.N)
           then Seq#Drop(Seq#Take(Seq#FromArray($Heap, read($Heap, this, _module.RingBuffer.data)),
              read($Heap, this, _module.RingBuffer.start)
                 + read($Heap, this, _module.RingBuffer.len)),
            read($Heap, this, _module.RingBuffer.start))
           else Seq#Append(Seq#Drop(Seq#FromArray($Heap, read($Heap, this, _module.RingBuffer.data)),
              read($Heap, this, _module.RingBuffer.start)),
            Seq#Take(Seq#FromArray($Heap, read($Heap, this, _module.RingBuffer.data)),
              read($Heap, this, _module.RingBuffer.start)
                   + read($Heap, this, _module.RingBuffer.len)
                 - read($Heap, this, _module.RingBuffer.N)))));
  free ensures true;
  ensures (forall $o: ref ::
    { read(old($Heap), $o, alloc) }
    read($Heap, this, _module.RingBuffer.Repr)[$Box($o)] && $o != this
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures true;
  ensures Seq#Equal(read($Heap, this, _module.RingBuffer.Contents), Seq#Empty(): Seq Box);
  ensures read($Heap, this, _module.RingBuffer.N) == n#0;
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.RingBuffer.Create(_module.RingBuffer$T: Ty, n#0: int) returns (this: ref, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var this.Contents: Seq Box;
  var this.N: int;
  var this.data: ref;
  var this.start: int;
  var this.len: int;
  var this.Repr: Set Box;
  var $nw: ref;
  var $obj0: ref;
  var $obj1: ref;
  var $rhs#0: int where LitInt(0) <= $rhs#0;
  var $rhs#1: int where LitInt(0) <= $rhs#1;
  var $rhs#2: Seq Box where $Is($rhs#2, TSeq(_module.RingBuffer$T));
  var $rhs#3: int where LitInt(0) <= $rhs#3;
  var $rhs#4: Set Box where $Is($rhs#4, TSet(Tclass._System.object()));
  var $rhs#0_0: Set Box where $Is($rhs#0_0, TSet(Tclass._System.object()));

    // AddMethodImpl: Create, Impl$$_module.RingBuffer.Create
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "RingBufferAuto.dfy(28,2): initial state"} true;
    $_reverifyPost := false;
    // ----- divided block before new; ----- RingBufferAuto.dfy(28,3)
    // ----- assignment statement ----- RingBufferAuto.dfy(29,10)
    assume true;
    assert 0 <= n#0;
    havoc $nw;
    assume $nw != null
       &&
      !read($Heap, $nw, alloc)
       && dtype($nw) == Tclass._System.array(_module.RingBuffer$T);
    assume _System.array.Length($nw) == n#0;
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    this.data := $nw;
    assume {:captureState "RingBufferAuto.dfy(29,20)"} true;
    // ----- update statement ----- RingBufferAuto.dfy(30,16)
    assume true;
    $obj0 := this;
    assume true;
    $obj1 := this;
    assume true;
    assert $Is(LitInt(0), Tclass._System.nat());
    $rhs#0 := LitInt(0);
    assume true;
    assert $Is(LitInt(0), Tclass._System.nat());
    $rhs#1 := LitInt(0);
    this.start := $rhs#0;
    this.len := $rhs#1;
    assume {:captureState "RingBufferAuto.dfy(30,22)"} true;
    // ----- update statement ----- RingBufferAuto.dfy(31,17)
    assume true;
    $obj0 := this;
    assume true;
    $obj1 := this;
    assume true;
    $rhs#2 := Lit(Seq#Empty(): Seq Box);
    assume true;
    assert $Is(n#0, Tclass._System.nat());
    $rhs#3 := n#0;
    this.Contents := $rhs#2;
    this.N := $rhs#3;
    assume {:captureState "RingBufferAuto.dfy(31,24)"} true;
    // ----- new; ----- RingBufferAuto.dfy(28,3)
    assume this != null
       &&
      !read($Heap, this, alloc)
       && dtype(this) == Tclass._module.RingBuffer(_module.RingBuffer$T);
    assume read($Heap, this, _module.RingBuffer.Contents) == this.Contents;
    assume read($Heap, this, _module.RingBuffer.N) == this.N;
    assume read($Heap, this, _module.RingBuffer.data) == this.data;
    assume read($Heap, this, _module.RingBuffer.start) == this.start;
    assume read($Heap, this, _module.RingBuffer.len) == this.len;
    assume read($Heap, this, _module.RingBuffer.Repr) == this.Repr;
    $Heap := update($Heap, this, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    // ----- divided block after new; ----- RingBufferAuto.dfy(28,3)
    // ----- assignment statement ----- RingBufferAuto.dfy(26,15)
    assume true;
    assert $_Frame[this, _module.RingBuffer.Repr];
    assume true;
    $rhs#4 := Set#UnionOne(Set#Empty(): Set Box, $Box(this));
    $Heap := update($Heap, this, _module.RingBuffer.Repr, $rhs#4);
    assume $IsGoodHeap($Heap);
    assume {:captureState "RingBufferAuto.dfy(26,14)"} true;
    // ----- if statement ----- RingBufferAuto.dfy(26,15)
    if (read($Heap, this, _module.RingBuffer.data) != null)
    {
    }

    assume true;
    if (read($Heap, this, _module.RingBuffer.data) != null
       && !read($Heap, this, _module.RingBuffer.Repr)[$Box(read($Heap, this, _module.RingBuffer.data))])
    {
        // ----- assignment statement ----- RingBufferAuto.dfy(26,15)
        assume true;
        assert $_Frame[this, _module.RingBuffer.Repr];
        assume true;
        $rhs#0_0 := Set#Union(read($Heap, this, _module.RingBuffer.Repr),
          Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.RingBuffer.data))));
        $Heap := update($Heap, this, _module.RingBuffer.Repr, $rhs#0_0);
        assume $IsGoodHeap($Heap);
        assume {:captureState "RingBufferAuto.dfy(26,14)"} true;
    }
    else
    {
    }
}



procedure CheckWellformed$$_module.RingBuffer.Clear(_module.RingBuffer$T: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.RingBuffer(_module.RingBuffer$T))
         && $IsAlloc(this, Tclass._module.RingBuffer(_module.RingBuffer$T), $Heap));
  free requires 6 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.RingBuffer.Clear(_module.RingBuffer$T: Ty, this: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: Clear, CheckWellformed$$_module.RingBuffer.Clear
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc)
         ==> read($Heap, this, _module.RingBuffer.Repr)[$Box($o)]);
    assume {:captureState "RingBufferAuto.dfy(34,9): initial state"} true;
    assume _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this);
    assume _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this);
    havoc $Heap;
    assume (forall<alpha> $o: ref, $f: Field alpha ::
      { read($Heap, $o, $f) }
      $o != null && read(old($Heap), $o, alloc)
         ==> read($Heap, $o, $f) == read(old($Heap), $o, $f)
           || read(old($Heap), this, _module.RingBuffer.Repr)[$Box($o)]);
    assume $HeapSucc(old($Heap), $Heap);
    assume {:captureState "RingBufferAuto.dfy(34,9): post-state"} true;
    assume _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this);
    assume _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this);
    assert $IsAlloc(this, Tclass._module.RingBuffer(_module.RingBuffer$T), old($Heap));
    assume (forall $o: ref ::
      { read(old($Heap), $o, alloc) }
      read($Heap, this, _module.RingBuffer.Repr)[$Box($o)]
           && !read(old($Heap), this, _module.RingBuffer.Repr)[$Box($o)]
         ==> $o != null && !read(old($Heap), $o, alloc));
    assume Seq#Equal(read($Heap, this, _module.RingBuffer.Contents), Seq#Empty(): Seq Box);
    assert $IsAlloc(this, Tclass._module.RingBuffer(_module.RingBuffer$T), old($Heap));
    assume read($Heap, this, _module.RingBuffer.N)
       == read(old($Heap), this, _module.RingBuffer.N);
}



procedure Call$$_module.RingBuffer.Clear(_module.RingBuffer$T: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.RingBuffer(_module.RingBuffer$T))
         && $IsAlloc(this, Tclass._module.RingBuffer(_module.RingBuffer$T), $Heap));
  // user-defined preconditions
  requires _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || read($Heap, this, _module.RingBuffer.Repr)[$Box(this)];
  requires _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || !read($Heap, this, _module.RingBuffer.Repr)[$Box(null)];
  requires _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || (read($Heap, this, _module.RingBuffer.data) != null
         ==> read($Heap, this, _module.RingBuffer.Repr)[$Box(read($Heap, this, _module.RingBuffer.data))]);
  requires _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || read($Heap, this, _module.RingBuffer.data) != null;
  requires _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || _System.array.Length(read($Heap, this, _module.RingBuffer.data))
         == read($Heap, this, _module.RingBuffer.N);
  requires _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || (read($Heap, this, _module.RingBuffer.N) == LitInt(0)
         ==> read($Heap, this, _module.RingBuffer.len)
           == read($Heap, this, _module.RingBuffer.start));
  requires _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || (read($Heap, this, _module.RingBuffer.N) == LitInt(0)
         ==> read($Heap, this, _module.RingBuffer.start) == LitInt(0));
  requires _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || (read($Heap, this, _module.RingBuffer.N) == LitInt(0)
         ==> Seq#Equal(read($Heap, this, _module.RingBuffer.Contents), Seq#Empty(): Seq Box));
  requires _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || (read($Heap, this, _module.RingBuffer.N) != 0
         ==> read($Heap, this, _module.RingBuffer.len)
           <= read($Heap, this, _module.RingBuffer.N));
  requires _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || (read($Heap, this, _module.RingBuffer.N) != 0
         ==> read($Heap, this, _module.RingBuffer.start)
           < read($Heap, this, _module.RingBuffer.N));
  requires _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || Seq#Equal(read($Heap, this, _module.RingBuffer.Contents),
        (if read($Heap, this, _module.RingBuffer.start)
               + read($Heap, this, _module.RingBuffer.len)
             <= read($Heap, this, _module.RingBuffer.N)
           then Seq#Drop(Seq#Take(Seq#FromArray($Heap, read($Heap, this, _module.RingBuffer.data)),
              read($Heap, this, _module.RingBuffer.start)
                 + read($Heap, this, _module.RingBuffer.len)),
            read($Heap, this, _module.RingBuffer.start))
           else Seq#Append(Seq#Drop(Seq#FromArray($Heap, read($Heap, this, _module.RingBuffer.data)),
              read($Heap, this, _module.RingBuffer.start)),
            Seq#Take(Seq#FromArray($Heap, read($Heap, this, _module.RingBuffer.data)),
              read($Heap, this, _module.RingBuffer.start)
                   + read($Heap, this, _module.RingBuffer.len)
                 - read($Heap, this, _module.RingBuffer.N)))));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this);
  free ensures _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     &&
    _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
     &&
    read($Heap, this, _module.RingBuffer.Repr)[$Box(this)]
     && !read($Heap, this, _module.RingBuffer.Repr)[$Box(null)]
     &&
    (read($Heap, this, _module.RingBuffer.data) != null
       ==> read($Heap, this, _module.RingBuffer.Repr)[$Box(read($Heap, this, _module.RingBuffer.data))])
     &&
    read($Heap, this, _module.RingBuffer.data) != null
     && _System.array.Length(read($Heap, this, _module.RingBuffer.data))
       == read($Heap, this, _module.RingBuffer.N)
     && (read($Heap, this, _module.RingBuffer.N) == LitInt(0)
       ==> read($Heap, this, _module.RingBuffer.len)
           == read($Heap, this, _module.RingBuffer.start)
         && read($Heap, this, _module.RingBuffer.start) == LitInt(0)
         && Seq#Equal(read($Heap, this, _module.RingBuffer.Contents), Seq#Empty(): Seq Box))
     && (read($Heap, this, _module.RingBuffer.N) != 0
       ==> read($Heap, this, _module.RingBuffer.len)
           <= read($Heap, this, _module.RingBuffer.N)
         && read($Heap, this, _module.RingBuffer.start)
           < read($Heap, this, _module.RingBuffer.N))
     && Seq#Equal(read($Heap, this, _module.RingBuffer.Contents),
      (if read($Heap, this, _module.RingBuffer.start)
             + read($Heap, this, _module.RingBuffer.len)
           <= read($Heap, this, _module.RingBuffer.N)
         then Seq#Drop(Seq#Take(Seq#FromArray($Heap, read($Heap, this, _module.RingBuffer.data)),
            read($Heap, this, _module.RingBuffer.start)
               + read($Heap, this, _module.RingBuffer.len)),
          read($Heap, this, _module.RingBuffer.start))
         else Seq#Append(Seq#Drop(Seq#FromArray($Heap, read($Heap, this, _module.RingBuffer.data)),
            read($Heap, this, _module.RingBuffer.start)),
          Seq#Take(Seq#FromArray($Heap, read($Heap, this, _module.RingBuffer.data)),
            read($Heap, this, _module.RingBuffer.start)
                 + read($Heap, this, _module.RingBuffer.len)
               - read($Heap, this, _module.RingBuffer.N)))));
  free ensures true;
  ensures (forall $o: ref ::
    { read(old($Heap), $o, alloc) }
    read($Heap, this, _module.RingBuffer.Repr)[$Box($o)]
         && !read(old($Heap), this, _module.RingBuffer.Repr)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures true;
  ensures Seq#Equal(read($Heap, this, _module.RingBuffer.Contents), Seq#Empty(): Seq Box);
  ensures read($Heap, this, _module.RingBuffer.N)
     == read(old($Heap), this, _module.RingBuffer.N);
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f)
         || read(old($Heap), this, _module.RingBuffer.Repr)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.RingBuffer.Clear(_module.RingBuffer$T: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.RingBuffer(_module.RingBuffer$T))
         && $IsAlloc(this, Tclass._module.RingBuffer(_module.RingBuffer$T), $Heap))
   returns ($_reverifyPost: bool);
  free requires 6 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     &&
    _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
     &&
    read($Heap, this, _module.RingBuffer.Repr)[$Box(this)]
     && !read($Heap, this, _module.RingBuffer.Repr)[$Box(null)]
     &&
    (read($Heap, this, _module.RingBuffer.data) != null
       ==> read($Heap, this, _module.RingBuffer.Repr)[$Box(read($Heap, this, _module.RingBuffer.data))])
     &&
    read($Heap, this, _module.RingBuffer.data) != null
     && _System.array.Length(read($Heap, this, _module.RingBuffer.data))
       == read($Heap, this, _module.RingBuffer.N)
     && (read($Heap, this, _module.RingBuffer.N) == LitInt(0)
       ==> read($Heap, this, _module.RingBuffer.len)
           == read($Heap, this, _module.RingBuffer.start)
         && read($Heap, this, _module.RingBuffer.start) == LitInt(0)
         && Seq#Equal(read($Heap, this, _module.RingBuffer.Contents), Seq#Empty(): Seq Box))
     && (read($Heap, this, _module.RingBuffer.N) != 0
       ==> read($Heap, this, _module.RingBuffer.len)
           <= read($Heap, this, _module.RingBuffer.N)
         && read($Heap, this, _module.RingBuffer.start)
           < read($Heap, this, _module.RingBuffer.N))
     && Seq#Equal(read($Heap, this, _module.RingBuffer.Contents),
      (if read($Heap, this, _module.RingBuffer.start)
             + read($Heap, this, _module.RingBuffer.len)
           <= read($Heap, this, _module.RingBuffer.N)
         then Seq#Drop(Seq#Take(Seq#FromArray($Heap, read($Heap, this, _module.RingBuffer.data)),
            read($Heap, this, _module.RingBuffer.start)
               + read($Heap, this, _module.RingBuffer.len)),
          read($Heap, this, _module.RingBuffer.start))
         else Seq#Append(Seq#Drop(Seq#FromArray($Heap, read($Heap, this, _module.RingBuffer.data)),
            read($Heap, this, _module.RingBuffer.start)),
          Seq#Take(Seq#FromArray($Heap, read($Heap, this, _module.RingBuffer.data)),
            read($Heap, this, _module.RingBuffer.start)
                 + read($Heap, this, _module.RingBuffer.len)
               - read($Heap, this, _module.RingBuffer.N)))));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this);
  ensures _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || read($Heap, this, _module.RingBuffer.Repr)[$Box(this)];
  ensures _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || !read($Heap, this, _module.RingBuffer.Repr)[$Box(null)];
  ensures _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || (read($Heap, this, _module.RingBuffer.data) != null
         ==> read($Heap, this, _module.RingBuffer.Repr)[$Box(read($Heap, this, _module.RingBuffer.data))]);
  ensures _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || read($Heap, this, _module.RingBuffer.data) != null;
  ensures _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || _System.array.Length(read($Heap, this, _module.RingBuffer.data))
         == read($Heap, this, _module.RingBuffer.N);
  ensures _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || (read($Heap, this, _module.RingBuffer.N) == LitInt(0)
         ==> read($Heap, this, _module.RingBuffer.len)
           == read($Heap, this, _module.RingBuffer.start));
  ensures _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || (read($Heap, this, _module.RingBuffer.N) == LitInt(0)
         ==> read($Heap, this, _module.RingBuffer.start) == LitInt(0));
  ensures _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || (read($Heap, this, _module.RingBuffer.N) == LitInt(0)
         ==> Seq#Equal(read($Heap, this, _module.RingBuffer.Contents), Seq#Empty(): Seq Box));
  ensures _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || (read($Heap, this, _module.RingBuffer.N) != 0
         ==> read($Heap, this, _module.RingBuffer.len)
           <= read($Heap, this, _module.RingBuffer.N));
  ensures _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || (read($Heap, this, _module.RingBuffer.N) != 0
         ==> read($Heap, this, _module.RingBuffer.start)
           < read($Heap, this, _module.RingBuffer.N));
  ensures _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || Seq#Equal(read($Heap, this, _module.RingBuffer.Contents),
        (if read($Heap, this, _module.RingBuffer.start)
               + read($Heap, this, _module.RingBuffer.len)
             <= read($Heap, this, _module.RingBuffer.N)
           then Seq#Drop(Seq#Take(Seq#FromArray($Heap, read($Heap, this, _module.RingBuffer.data)),
              read($Heap, this, _module.RingBuffer.start)
                 + read($Heap, this, _module.RingBuffer.len)),
            read($Heap, this, _module.RingBuffer.start))
           else Seq#Append(Seq#Drop(Seq#FromArray($Heap, read($Heap, this, _module.RingBuffer.data)),
              read($Heap, this, _module.RingBuffer.start)),
            Seq#Take(Seq#FromArray($Heap, read($Heap, this, _module.RingBuffer.data)),
              read($Heap, this, _module.RingBuffer.start)
                   + read($Heap, this, _module.RingBuffer.len)
                 - read($Heap, this, _module.RingBuffer.N)))));
  free ensures true;
  ensures (forall $o: ref ::
    { read(old($Heap), $o, alloc) }
    read($Heap, this, _module.RingBuffer.Repr)[$Box($o)]
         && !read(old($Heap), this, _module.RingBuffer.Repr)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures true;
  ensures Seq#Equal(read($Heap, this, _module.RingBuffer.Contents), Seq#Empty(): Seq Box);
  ensures read($Heap, this, _module.RingBuffer.N)
     == read(old($Heap), this, _module.RingBuffer.N);
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f)
         || read(old($Heap), this, _module.RingBuffer.Repr)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.RingBuffer.Clear(_module.RingBuffer$T: Ty, this: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs#0: int where LitInt(0) <= $rhs#0;
  var $rhs#1: Seq Box where $Is($rhs#1, TSeq(_module.RingBuffer$T));
  var $rhs#0_0: Set Box where $Is($rhs#0_0, TSet(Tclass._System.object()));

    // AddMethodImpl: Clear, Impl$$_module.RingBuffer.Clear
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc)
         ==> read($Heap, this, _module.RingBuffer.Repr)[$Box($o)]);
    assume {:captureState "RingBufferAuto.dfy(36,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- RingBufferAuto.dfy(37,9)
    assume true;
    assert $_Frame[this, _module.RingBuffer.len];
    assume true;
    assert $Is(LitInt(0), Tclass._System.nat());
    $rhs#0 := LitInt(0);
    $Heap := update($Heap, this, _module.RingBuffer.len, $rhs#0);
    assume $IsGoodHeap($Heap);
    assume {:captureState "RingBufferAuto.dfy(37,12)"} true;
    // ----- assignment statement ----- RingBufferAuto.dfy(38,14)
    assume true;
    assert $_Frame[this, _module.RingBuffer.Contents];
    assume true;
    $rhs#1 := Lit(Seq#Empty(): Seq Box);
    $Heap := update($Heap, this, _module.RingBuffer.Contents, $rhs#1);
    assume $IsGoodHeap($Heap);
    assume {:captureState "RingBufferAuto.dfy(38,18)"} true;
    // ----- if statement ----- RingBufferAuto.dfy(34,10)
    if (read($Heap, this, _module.RingBuffer.data) != null)
    {
    }

    assume true;
    if (read($Heap, this, _module.RingBuffer.data) != null
       && !read($Heap, this, _module.RingBuffer.Repr)[$Box(read($Heap, this, _module.RingBuffer.data))])
    {
        // ----- assignment statement ----- RingBufferAuto.dfy(34,10)
        assume true;
        assert $_Frame[this, _module.RingBuffer.Repr];
        assume true;
        $rhs#0_0 := Set#Union(read($Heap, this, _module.RingBuffer.Repr),
          Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.RingBuffer.data))));
        $Heap := update($Heap, this, _module.RingBuffer.Repr, $rhs#0_0);
        assume $IsGoodHeap($Heap);
        assume {:captureState "RingBufferAuto.dfy(34,9)"} true;
    }
    else
    {
    }
}



procedure CheckWellformed$$_module.RingBuffer.Head(_module.RingBuffer$T: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.RingBuffer(_module.RingBuffer$T))
         && $IsAlloc(this, Tclass._module.RingBuffer(_module.RingBuffer$T), $Heap))
   returns (x#0: Box
       where $IsBox(x#0, _module.RingBuffer$T)
         && $IsAllocBox(x#0, _module.RingBuffer$T, $Heap));
  free requires 7 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.RingBuffer.Head(_module.RingBuffer$T: Ty, this: ref) returns (x#0: Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: Head, CheckWellformed$$_module.RingBuffer.Head
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "RingBufferAuto.dfy(41,9): initial state"} true;
    assume _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this);
    assume _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this);
    assume !Seq#Equal(read($Heap, this, _module.RingBuffer.Contents), Seq#Empty(): Seq Box);
    havoc $Heap;
    assume (forall<alpha> $o: ref, $f: Field alpha ::
      { read($Heap, $o, $f) }
      $o != null && read(old($Heap), $o, alloc)
         ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
    assume $HeapSucc(old($Heap), $Heap);
    havoc x#0;
    assume {:captureState "RingBufferAuto.dfy(43,14): post-state"} true;
    assert 0 <= LitInt(0)
       && LitInt(0) < Seq#Length(read($Heap, this, _module.RingBuffer.Contents));
    assume x#0 == Seq#Index(read($Heap, this, _module.RingBuffer.Contents), LitInt(0));
}



procedure Call$$_module.RingBuffer.Head(_module.RingBuffer$T: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.RingBuffer(_module.RingBuffer$T))
         && $IsAlloc(this, Tclass._module.RingBuffer(_module.RingBuffer$T), $Heap))
   returns (x#0: Box
       where $IsBox(x#0, _module.RingBuffer$T)
         && $IsAllocBox(x#0, _module.RingBuffer$T, $Heap));
  // user-defined preconditions
  requires _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || read($Heap, this, _module.RingBuffer.Repr)[$Box(this)];
  requires _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || !read($Heap, this, _module.RingBuffer.Repr)[$Box(null)];
  requires _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || (read($Heap, this, _module.RingBuffer.data) != null
         ==> read($Heap, this, _module.RingBuffer.Repr)[$Box(read($Heap, this, _module.RingBuffer.data))]);
  requires _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || read($Heap, this, _module.RingBuffer.data) != null;
  requires _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || _System.array.Length(read($Heap, this, _module.RingBuffer.data))
         == read($Heap, this, _module.RingBuffer.N);
  requires _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || (read($Heap, this, _module.RingBuffer.N) == LitInt(0)
         ==> read($Heap, this, _module.RingBuffer.len)
           == read($Heap, this, _module.RingBuffer.start));
  requires _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || (read($Heap, this, _module.RingBuffer.N) == LitInt(0)
         ==> read($Heap, this, _module.RingBuffer.start) == LitInt(0));
  requires _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || (read($Heap, this, _module.RingBuffer.N) == LitInt(0)
         ==> Seq#Equal(read($Heap, this, _module.RingBuffer.Contents), Seq#Empty(): Seq Box));
  requires _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || (read($Heap, this, _module.RingBuffer.N) != 0
         ==> read($Heap, this, _module.RingBuffer.len)
           <= read($Heap, this, _module.RingBuffer.N));
  requires _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || (read($Heap, this, _module.RingBuffer.N) != 0
         ==> read($Heap, this, _module.RingBuffer.start)
           < read($Heap, this, _module.RingBuffer.N));
  requires _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || Seq#Equal(read($Heap, this, _module.RingBuffer.Contents),
        (if read($Heap, this, _module.RingBuffer.start)
               + read($Heap, this, _module.RingBuffer.len)
             <= read($Heap, this, _module.RingBuffer.N)
           then Seq#Drop(Seq#Take(Seq#FromArray($Heap, read($Heap, this, _module.RingBuffer.data)),
              read($Heap, this, _module.RingBuffer.start)
                 + read($Heap, this, _module.RingBuffer.len)),
            read($Heap, this, _module.RingBuffer.start))
           else Seq#Append(Seq#Drop(Seq#FromArray($Heap, read($Heap, this, _module.RingBuffer.data)),
              read($Heap, this, _module.RingBuffer.start)),
            Seq#Take(Seq#FromArray($Heap, read($Heap, this, _module.RingBuffer.data)),
              read($Heap, this, _module.RingBuffer.start)
                   + read($Heap, this, _module.RingBuffer.len)
                 - read($Heap, this, _module.RingBuffer.N)))));
  requires !Seq#Equal(read($Heap, this, _module.RingBuffer.Contents), Seq#Empty(): Seq Box);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures x#0 == Seq#Index(read($Heap, this, _module.RingBuffer.Contents), LitInt(0));
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.RingBuffer.Head(_module.RingBuffer$T: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.RingBuffer(_module.RingBuffer$T))
         && $IsAlloc(this, Tclass._module.RingBuffer(_module.RingBuffer$T), $Heap))
   returns (x#0: Box
       where $IsBox(x#0, _module.RingBuffer$T)
         && $IsAllocBox(x#0, _module.RingBuffer$T, $Heap),
    $_reverifyPost: bool);
  free requires 7 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     &&
    _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
     &&
    read($Heap, this, _module.RingBuffer.Repr)[$Box(this)]
     && !read($Heap, this, _module.RingBuffer.Repr)[$Box(null)]
     &&
    (read($Heap, this, _module.RingBuffer.data) != null
       ==> read($Heap, this, _module.RingBuffer.Repr)[$Box(read($Heap, this, _module.RingBuffer.data))])
     &&
    read($Heap, this, _module.RingBuffer.data) != null
     && _System.array.Length(read($Heap, this, _module.RingBuffer.data))
       == read($Heap, this, _module.RingBuffer.N)
     && (read($Heap, this, _module.RingBuffer.N) == LitInt(0)
       ==> read($Heap, this, _module.RingBuffer.len)
           == read($Heap, this, _module.RingBuffer.start)
         && read($Heap, this, _module.RingBuffer.start) == LitInt(0)
         && Seq#Equal(read($Heap, this, _module.RingBuffer.Contents), Seq#Empty(): Seq Box))
     && (read($Heap, this, _module.RingBuffer.N) != 0
       ==> read($Heap, this, _module.RingBuffer.len)
           <= read($Heap, this, _module.RingBuffer.N)
         && read($Heap, this, _module.RingBuffer.start)
           < read($Heap, this, _module.RingBuffer.N))
     && Seq#Equal(read($Heap, this, _module.RingBuffer.Contents),
      (if read($Heap, this, _module.RingBuffer.start)
             + read($Heap, this, _module.RingBuffer.len)
           <= read($Heap, this, _module.RingBuffer.N)
         then Seq#Drop(Seq#Take(Seq#FromArray($Heap, read($Heap, this, _module.RingBuffer.data)),
            read($Heap, this, _module.RingBuffer.start)
               + read($Heap, this, _module.RingBuffer.len)),
          read($Heap, this, _module.RingBuffer.start))
         else Seq#Append(Seq#Drop(Seq#FromArray($Heap, read($Heap, this, _module.RingBuffer.data)),
            read($Heap, this, _module.RingBuffer.start)),
          Seq#Take(Seq#FromArray($Heap, read($Heap, this, _module.RingBuffer.data)),
            read($Heap, this, _module.RingBuffer.start)
                 + read($Heap, this, _module.RingBuffer.len)
               - read($Heap, this, _module.RingBuffer.N)))));
  requires !Seq#Equal(read($Heap, this, _module.RingBuffer.Contents), Seq#Empty(): Seq Box);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures x#0 == Seq#Index(read($Heap, this, _module.RingBuffer.Contents), LitInt(0));
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.RingBuffer.Head(_module.RingBuffer$T: Ty, this: ref) returns (x#0: Box, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: Head, Impl$$_module.RingBuffer.Head
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "RingBufferAuto.dfy(44,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- RingBufferAuto.dfy(45,7)
    assume true;
    assert read($Heap, this, _module.RingBuffer.data) != null;
    assert 0 <= read($Heap, this, _module.RingBuffer.start)
       && read($Heap, this, _module.RingBuffer.start)
         < _System.array.Length(read($Heap, this, _module.RingBuffer.data));
    assume true;
    x#0 := read($Heap,
      read($Heap, this, _module.RingBuffer.data),
      IndexField(read($Heap, this, _module.RingBuffer.start)));
    assume {:captureState "RingBufferAuto.dfy(45,20)"} true;
}



procedure CheckWellformed$$_module.RingBuffer.Enqueue(_module.RingBuffer$T: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.RingBuffer(_module.RingBuffer$T))
         && $IsAlloc(this, Tclass._module.RingBuffer(_module.RingBuffer$T), $Heap),
    x#0: Box
       where $IsBox(x#0, _module.RingBuffer$T)
         && $IsAllocBox(x#0, _module.RingBuffer$T, $Heap));
  free requires 3 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.RingBuffer.Enqueue(_module.RingBuffer$T: Ty, this: ref, x#0: Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: Enqueue, CheckWellformed$$_module.RingBuffer.Enqueue
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc)
         ==> read($Heap, this, _module.RingBuffer.Repr)[$Box($o)]);
    assume {:captureState "RingBufferAuto.dfy(48,9): initial state"} true;
    assume _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this);
    assume _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this);
    assume Seq#Length(read($Heap, this, _module.RingBuffer.Contents))
       != read($Heap, this, _module.RingBuffer.N);
    havoc $Heap;
    assume (forall<alpha> $o: ref, $f: Field alpha ::
      { read($Heap, $o, $f) }
      $o != null && read(old($Heap), $o, alloc)
         ==> read($Heap, $o, $f) == read(old($Heap), $o, $f)
           || read(old($Heap), this, _module.RingBuffer.Repr)[$Box($o)]);
    assume $HeapSucc(old($Heap), $Heap);
    assume {:captureState "RingBufferAuto.dfy(48,9): post-state"} true;
    assume _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this);
    assume _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this);
    assert $IsAlloc(this, Tclass._module.RingBuffer(_module.RingBuffer$T), old($Heap));
    assume (forall $o: ref ::
      { read(old($Heap), $o, alloc) }
      read($Heap, this, _module.RingBuffer.Repr)[$Box($o)]
           && !read(old($Heap), this, _module.RingBuffer.Repr)[$Box($o)]
         ==> $o != null && !read(old($Heap), $o, alloc));
    assert $IsAlloc(this, Tclass._module.RingBuffer(_module.RingBuffer$T), old($Heap));
    assume Seq#Equal(read($Heap, this, _module.RingBuffer.Contents),
      Seq#Append(read(old($Heap), this, _module.RingBuffer.Contents),
        Seq#Build(Seq#Empty(): Seq Box, x#0)));
    assert $IsAlloc(this, Tclass._module.RingBuffer(_module.RingBuffer$T), old($Heap));
    assume read($Heap, this, _module.RingBuffer.N)
       == read(old($Heap), this, _module.RingBuffer.N);
}



procedure Call$$_module.RingBuffer.Enqueue(_module.RingBuffer$T: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.RingBuffer(_module.RingBuffer$T))
         && $IsAlloc(this, Tclass._module.RingBuffer(_module.RingBuffer$T), $Heap),
    x#0: Box
       where $IsBox(x#0, _module.RingBuffer$T)
         && $IsAllocBox(x#0, _module.RingBuffer$T, $Heap));
  // user-defined preconditions
  requires _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || read($Heap, this, _module.RingBuffer.Repr)[$Box(this)];
  requires _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || !read($Heap, this, _module.RingBuffer.Repr)[$Box(null)];
  requires _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || (read($Heap, this, _module.RingBuffer.data) != null
         ==> read($Heap, this, _module.RingBuffer.Repr)[$Box(read($Heap, this, _module.RingBuffer.data))]);
  requires _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || read($Heap, this, _module.RingBuffer.data) != null;
  requires _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || _System.array.Length(read($Heap, this, _module.RingBuffer.data))
         == read($Heap, this, _module.RingBuffer.N);
  requires _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || (read($Heap, this, _module.RingBuffer.N) == LitInt(0)
         ==> read($Heap, this, _module.RingBuffer.len)
           == read($Heap, this, _module.RingBuffer.start));
  requires _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || (read($Heap, this, _module.RingBuffer.N) == LitInt(0)
         ==> read($Heap, this, _module.RingBuffer.start) == LitInt(0));
  requires _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || (read($Heap, this, _module.RingBuffer.N) == LitInt(0)
         ==> Seq#Equal(read($Heap, this, _module.RingBuffer.Contents), Seq#Empty(): Seq Box));
  requires _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || (read($Heap, this, _module.RingBuffer.N) != 0
         ==> read($Heap, this, _module.RingBuffer.len)
           <= read($Heap, this, _module.RingBuffer.N));
  requires _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || (read($Heap, this, _module.RingBuffer.N) != 0
         ==> read($Heap, this, _module.RingBuffer.start)
           < read($Heap, this, _module.RingBuffer.N));
  requires _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || Seq#Equal(read($Heap, this, _module.RingBuffer.Contents),
        (if read($Heap, this, _module.RingBuffer.start)
               + read($Heap, this, _module.RingBuffer.len)
             <= read($Heap, this, _module.RingBuffer.N)
           then Seq#Drop(Seq#Take(Seq#FromArray($Heap, read($Heap, this, _module.RingBuffer.data)),
              read($Heap, this, _module.RingBuffer.start)
                 + read($Heap, this, _module.RingBuffer.len)),
            read($Heap, this, _module.RingBuffer.start))
           else Seq#Append(Seq#Drop(Seq#FromArray($Heap, read($Heap, this, _module.RingBuffer.data)),
              read($Heap, this, _module.RingBuffer.start)),
            Seq#Take(Seq#FromArray($Heap, read($Heap, this, _module.RingBuffer.data)),
              read($Heap, this, _module.RingBuffer.start)
                   + read($Heap, this, _module.RingBuffer.len)
                 - read($Heap, this, _module.RingBuffer.N)))));
  requires Seq#Length(read($Heap, this, _module.RingBuffer.Contents))
     != read($Heap, this, _module.RingBuffer.N);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this);
  free ensures _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     &&
    _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
     &&
    read($Heap, this, _module.RingBuffer.Repr)[$Box(this)]
     && !read($Heap, this, _module.RingBuffer.Repr)[$Box(null)]
     &&
    (read($Heap, this, _module.RingBuffer.data) != null
       ==> read($Heap, this, _module.RingBuffer.Repr)[$Box(read($Heap, this, _module.RingBuffer.data))])
     &&
    read($Heap, this, _module.RingBuffer.data) != null
     && _System.array.Length(read($Heap, this, _module.RingBuffer.data))
       == read($Heap, this, _module.RingBuffer.N)
     && (read($Heap, this, _module.RingBuffer.N) == LitInt(0)
       ==> read($Heap, this, _module.RingBuffer.len)
           == read($Heap, this, _module.RingBuffer.start)
         && read($Heap, this, _module.RingBuffer.start) == LitInt(0)
         && Seq#Equal(read($Heap, this, _module.RingBuffer.Contents), Seq#Empty(): Seq Box))
     && (read($Heap, this, _module.RingBuffer.N) != 0
       ==> read($Heap, this, _module.RingBuffer.len)
           <= read($Heap, this, _module.RingBuffer.N)
         && read($Heap, this, _module.RingBuffer.start)
           < read($Heap, this, _module.RingBuffer.N))
     && Seq#Equal(read($Heap, this, _module.RingBuffer.Contents),
      (if read($Heap, this, _module.RingBuffer.start)
             + read($Heap, this, _module.RingBuffer.len)
           <= read($Heap, this, _module.RingBuffer.N)
         then Seq#Drop(Seq#Take(Seq#FromArray($Heap, read($Heap, this, _module.RingBuffer.data)),
            read($Heap, this, _module.RingBuffer.start)
               + read($Heap, this, _module.RingBuffer.len)),
          read($Heap, this, _module.RingBuffer.start))
         else Seq#Append(Seq#Drop(Seq#FromArray($Heap, read($Heap, this, _module.RingBuffer.data)),
            read($Heap, this, _module.RingBuffer.start)),
          Seq#Take(Seq#FromArray($Heap, read($Heap, this, _module.RingBuffer.data)),
            read($Heap, this, _module.RingBuffer.start)
                 + read($Heap, this, _module.RingBuffer.len)
               - read($Heap, this, _module.RingBuffer.N)))));
  free ensures true;
  ensures (forall $o: ref ::
    { read(old($Heap), $o, alloc) }
    read($Heap, this, _module.RingBuffer.Repr)[$Box($o)]
         && !read(old($Heap), this, _module.RingBuffer.Repr)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures true;
  ensures Seq#Equal(read($Heap, this, _module.RingBuffer.Contents),
    Seq#Append(read(old($Heap), this, _module.RingBuffer.Contents),
      Seq#Build(Seq#Empty(): Seq Box, x#0)));
  ensures read($Heap, this, _module.RingBuffer.N)
     == read(old($Heap), this, _module.RingBuffer.N);
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f)
         || read(old($Heap), this, _module.RingBuffer.Repr)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.RingBuffer.Enqueue(_module.RingBuffer$T: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.RingBuffer(_module.RingBuffer$T))
         && $IsAlloc(this, Tclass._module.RingBuffer(_module.RingBuffer$T), $Heap),
    x#0: Box
       where $IsBox(x#0, _module.RingBuffer$T)
         && $IsAllocBox(x#0, _module.RingBuffer$T, $Heap))
   returns ($_reverifyPost: bool);
  free requires 3 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     &&
    _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
     &&
    read($Heap, this, _module.RingBuffer.Repr)[$Box(this)]
     && !read($Heap, this, _module.RingBuffer.Repr)[$Box(null)]
     &&
    (read($Heap, this, _module.RingBuffer.data) != null
       ==> read($Heap, this, _module.RingBuffer.Repr)[$Box(read($Heap, this, _module.RingBuffer.data))])
     &&
    read($Heap, this, _module.RingBuffer.data) != null
     && _System.array.Length(read($Heap, this, _module.RingBuffer.data))
       == read($Heap, this, _module.RingBuffer.N)
     && (read($Heap, this, _module.RingBuffer.N) == LitInt(0)
       ==> read($Heap, this, _module.RingBuffer.len)
           == read($Heap, this, _module.RingBuffer.start)
         && read($Heap, this, _module.RingBuffer.start) == LitInt(0)
         && Seq#Equal(read($Heap, this, _module.RingBuffer.Contents), Seq#Empty(): Seq Box))
     && (read($Heap, this, _module.RingBuffer.N) != 0
       ==> read($Heap, this, _module.RingBuffer.len)
           <= read($Heap, this, _module.RingBuffer.N)
         && read($Heap, this, _module.RingBuffer.start)
           < read($Heap, this, _module.RingBuffer.N))
     && Seq#Equal(read($Heap, this, _module.RingBuffer.Contents),
      (if read($Heap, this, _module.RingBuffer.start)
             + read($Heap, this, _module.RingBuffer.len)
           <= read($Heap, this, _module.RingBuffer.N)
         then Seq#Drop(Seq#Take(Seq#FromArray($Heap, read($Heap, this, _module.RingBuffer.data)),
            read($Heap, this, _module.RingBuffer.start)
               + read($Heap, this, _module.RingBuffer.len)),
          read($Heap, this, _module.RingBuffer.start))
         else Seq#Append(Seq#Drop(Seq#FromArray($Heap, read($Heap, this, _module.RingBuffer.data)),
            read($Heap, this, _module.RingBuffer.start)),
          Seq#Take(Seq#FromArray($Heap, read($Heap, this, _module.RingBuffer.data)),
            read($Heap, this, _module.RingBuffer.start)
                 + read($Heap, this, _module.RingBuffer.len)
               - read($Heap, this, _module.RingBuffer.N)))));
  requires Seq#Length(read($Heap, this, _module.RingBuffer.Contents))
     != read($Heap, this, _module.RingBuffer.N);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this);
  ensures _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || read($Heap, this, _module.RingBuffer.Repr)[$Box(this)];
  ensures _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || !read($Heap, this, _module.RingBuffer.Repr)[$Box(null)];
  ensures _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || (read($Heap, this, _module.RingBuffer.data) != null
         ==> read($Heap, this, _module.RingBuffer.Repr)[$Box(read($Heap, this, _module.RingBuffer.data))]);
  ensures _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || read($Heap, this, _module.RingBuffer.data) != null;
  ensures _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || _System.array.Length(read($Heap, this, _module.RingBuffer.data))
         == read($Heap, this, _module.RingBuffer.N);
  ensures _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || (read($Heap, this, _module.RingBuffer.N) == LitInt(0)
         ==> read($Heap, this, _module.RingBuffer.len)
           == read($Heap, this, _module.RingBuffer.start));
  ensures _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || (read($Heap, this, _module.RingBuffer.N) == LitInt(0)
         ==> read($Heap, this, _module.RingBuffer.start) == LitInt(0));
  ensures _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || (read($Heap, this, _module.RingBuffer.N) == LitInt(0)
         ==> Seq#Equal(read($Heap, this, _module.RingBuffer.Contents), Seq#Empty(): Seq Box));
  ensures _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || (read($Heap, this, _module.RingBuffer.N) != 0
         ==> read($Heap, this, _module.RingBuffer.len)
           <= read($Heap, this, _module.RingBuffer.N));
  ensures _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || (read($Heap, this, _module.RingBuffer.N) != 0
         ==> read($Heap, this, _module.RingBuffer.start)
           < read($Heap, this, _module.RingBuffer.N));
  ensures _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || Seq#Equal(read($Heap, this, _module.RingBuffer.Contents),
        (if read($Heap, this, _module.RingBuffer.start)
               + read($Heap, this, _module.RingBuffer.len)
             <= read($Heap, this, _module.RingBuffer.N)
           then Seq#Drop(Seq#Take(Seq#FromArray($Heap, read($Heap, this, _module.RingBuffer.data)),
              read($Heap, this, _module.RingBuffer.start)
                 + read($Heap, this, _module.RingBuffer.len)),
            read($Heap, this, _module.RingBuffer.start))
           else Seq#Append(Seq#Drop(Seq#FromArray($Heap, read($Heap, this, _module.RingBuffer.data)),
              read($Heap, this, _module.RingBuffer.start)),
            Seq#Take(Seq#FromArray($Heap, read($Heap, this, _module.RingBuffer.data)),
              read($Heap, this, _module.RingBuffer.start)
                   + read($Heap, this, _module.RingBuffer.len)
                 - read($Heap, this, _module.RingBuffer.N)))));
  free ensures true;
  ensures (forall $o: ref ::
    { read(old($Heap), $o, alloc) }
    read($Heap, this, _module.RingBuffer.Repr)[$Box($o)]
         && !read(old($Heap), this, _module.RingBuffer.Repr)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures true;
  ensures Seq#Equal(read($Heap, this, _module.RingBuffer.Contents),
    Seq#Append(read(old($Heap), this, _module.RingBuffer.Contents),
      Seq#Build(Seq#Empty(): Seq Box, x#0)));
  ensures read($Heap, this, _module.RingBuffer.N)
     == read(old($Heap), this, _module.RingBuffer.N);
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f)
         || read(old($Heap), this, _module.RingBuffer.Repr)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.RingBuffer.Enqueue(_module.RingBuffer$T: Ty, this: ref, x#0: Box) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var nextEmpty#0: int;
  var $rhs#0: Box where $IsBox($rhs#0, _module.RingBuffer$T);
  var $rhs#1: int where LitInt(0) <= $rhs#1;
  var $rhs#2: Seq Box where $Is($rhs#2, TSeq(_module.RingBuffer$T));
  var $rhs#0_0: Set Box where $Is($rhs#0_0, TSet(Tclass._System.object()));

    // AddMethodImpl: Enqueue, Impl$$_module.RingBuffer.Enqueue
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc)
         ==> read($Heap, this, _module.RingBuffer.Repr)[$Box($o)]);
    assume {:captureState "RingBufferAuto.dfy(51,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- RingBufferAuto.dfy(52,19)
    assume true;
    assert read($Heap, this, _module.RingBuffer.data) != null;
    if (read($Heap, this, _module.RingBuffer.start)
         + read($Heap, this, _module.RingBuffer.len)
       < _System.array.Length(read($Heap, this, _module.RingBuffer.data)))
    {
    }
    else
    {
        assert read($Heap, this, _module.RingBuffer.data) != null;
    }

    assume true;
    nextEmpty#0 := (if read($Heap, this, _module.RingBuffer.start)
           + read($Heap, this, _module.RingBuffer.len)
         < _System.array.Length(read($Heap, this, _module.RingBuffer.data))
       then read($Heap, this, _module.RingBuffer.start)
         + read($Heap, this, _module.RingBuffer.len)
       else read($Heap, this, _module.RingBuffer.start)
           + read($Heap, this, _module.RingBuffer.len)
         - _System.array.Length(read($Heap, this, _module.RingBuffer.data)));
    assume {:captureState "RingBufferAuto.dfy(53,68)"} true;
    // ----- assignment statement ----- RingBufferAuto.dfy(54,21)
    assert read($Heap, this, _module.RingBuffer.data) != null;
    assert 0 <= nextEmpty#0
       && nextEmpty#0 < _System.array.Length(read($Heap, this, _module.RingBuffer.data));
    assume true;
    assert $_Frame[read($Heap, this, _module.RingBuffer.data), IndexField(nextEmpty#0)];
    assume true;
    $rhs#0 := x#0;
    $Heap := update($Heap,
      read($Heap, this, _module.RingBuffer.data),
      IndexField(nextEmpty#0),
      $rhs#0);
    assume $IsGoodHeap($Heap);
    assume {:captureState "RingBufferAuto.dfy(54,24)"} true;
    // ----- assignment statement ----- RingBufferAuto.dfy(55,9)
    assume true;
    assert $_Frame[this, _module.RingBuffer.len];
    assume true;
    assert $Is(read($Heap, this, _module.RingBuffer.len) + 1, Tclass._System.nat());
    $rhs#1 := read($Heap, this, _module.RingBuffer.len) + 1;
    $Heap := update($Heap, this, _module.RingBuffer.len, $rhs#1);
    assume $IsGoodHeap($Heap);
    assume {:captureState "RingBufferAuto.dfy(55,18)"} true;
    // ----- assignment statement ----- RingBufferAuto.dfy(56,14)
    assume true;
    assert $_Frame[this, _module.RingBuffer.Contents];
    assume true;
    $rhs#2 := Seq#Append(read($Heap, this, _module.RingBuffer.Contents),
      Seq#Build(Seq#Empty(): Seq Box, x#0));
    $Heap := update($Heap, this, _module.RingBuffer.Contents, $rhs#2);
    assume $IsGoodHeap($Heap);
    assume {:captureState "RingBufferAuto.dfy(56,30)"} true;
    // ----- if statement ----- RingBufferAuto.dfy(48,10)
    if (read($Heap, this, _module.RingBuffer.data) != null)
    {
    }

    assume true;
    if (read($Heap, this, _module.RingBuffer.data) != null
       && !read($Heap, this, _module.RingBuffer.Repr)[$Box(read($Heap, this, _module.RingBuffer.data))])
    {
        // ----- assignment statement ----- RingBufferAuto.dfy(48,10)
        assume true;
        assert $_Frame[this, _module.RingBuffer.Repr];
        assume true;
        $rhs#0_0 := Set#Union(read($Heap, this, _module.RingBuffer.Repr),
          Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.RingBuffer.data))));
        $Heap := update($Heap, this, _module.RingBuffer.Repr, $rhs#0_0);
        assume $IsGoodHeap($Heap);
        assume {:captureState "RingBufferAuto.dfy(48,9)"} true;
    }
    else
    {
    }
}



procedure CheckWellformed$$_module.RingBuffer.ResizingEnqueue(_module.RingBuffer$T: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.RingBuffer(_module.RingBuffer$T))
         && $IsAlloc(this, Tclass._module.RingBuffer(_module.RingBuffer$T), $Heap),
    x#0: Box
       where $IsBox(x#0, _module.RingBuffer$T)
         && $IsAllocBox(x#0, _module.RingBuffer$T, $Heap));
  free requires 8 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.RingBuffer.ResizingEnqueue(_module.RingBuffer$T: Ty, this: ref, x#0: Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: ResizingEnqueue, CheckWellformed$$_module.RingBuffer.ResizingEnqueue
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc)
         ==> read($Heap, this, _module.RingBuffer.Repr)[$Box($o)]);
    assume {:captureState "RingBufferAuto.dfy(59,9): initial state"} true;
    assume _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this);
    assume _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this);
    havoc $Heap;
    assume (forall<alpha> $o: ref, $f: Field alpha ::
      { read($Heap, $o, $f) }
      $o != null && read(old($Heap), $o, alloc)
         ==> read($Heap, $o, $f) == read(old($Heap), $o, $f)
           || read(old($Heap), this, _module.RingBuffer.Repr)[$Box($o)]);
    assume $HeapSucc(old($Heap), $Heap);
    assume {:captureState "RingBufferAuto.dfy(59,9): post-state"} true;
    assume _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this);
    assume _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this);
    assert $IsAlloc(this, Tclass._module.RingBuffer(_module.RingBuffer$T), old($Heap));
    assume (forall $o: ref ::
      { read(old($Heap), $o, alloc) }
      read($Heap, this, _module.RingBuffer.Repr)[$Box($o)]
           && !read(old($Heap), this, _module.RingBuffer.Repr)[$Box($o)]
         ==> $o != null && !read(old($Heap), $o, alloc));
    assert $IsAlloc(this, Tclass._module.RingBuffer(_module.RingBuffer$T), old($Heap));
    assume Seq#Equal(read($Heap, this, _module.RingBuffer.Contents),
      Seq#Append(read(old($Heap), this, _module.RingBuffer.Contents),
        Seq#Build(Seq#Empty(): Seq Box, x#0)));
    assert $IsAlloc(this, Tclass._module.RingBuffer(_module.RingBuffer$T), old($Heap));
    assume read($Heap, this, _module.RingBuffer.N)
       >= read(old($Heap), this, _module.RingBuffer.N);
}



procedure Call$$_module.RingBuffer.ResizingEnqueue(_module.RingBuffer$T: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.RingBuffer(_module.RingBuffer$T))
         && $IsAlloc(this, Tclass._module.RingBuffer(_module.RingBuffer$T), $Heap),
    x#0: Box
       where $IsBox(x#0, _module.RingBuffer$T)
         && $IsAllocBox(x#0, _module.RingBuffer$T, $Heap));
  // user-defined preconditions
  requires _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || read($Heap, this, _module.RingBuffer.Repr)[$Box(this)];
  requires _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || !read($Heap, this, _module.RingBuffer.Repr)[$Box(null)];
  requires _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || (read($Heap, this, _module.RingBuffer.data) != null
         ==> read($Heap, this, _module.RingBuffer.Repr)[$Box(read($Heap, this, _module.RingBuffer.data))]);
  requires _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || read($Heap, this, _module.RingBuffer.data) != null;
  requires _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || _System.array.Length(read($Heap, this, _module.RingBuffer.data))
         == read($Heap, this, _module.RingBuffer.N);
  requires _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || (read($Heap, this, _module.RingBuffer.N) == LitInt(0)
         ==> read($Heap, this, _module.RingBuffer.len)
           == read($Heap, this, _module.RingBuffer.start));
  requires _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || (read($Heap, this, _module.RingBuffer.N) == LitInt(0)
         ==> read($Heap, this, _module.RingBuffer.start) == LitInt(0));
  requires _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || (read($Heap, this, _module.RingBuffer.N) == LitInt(0)
         ==> Seq#Equal(read($Heap, this, _module.RingBuffer.Contents), Seq#Empty(): Seq Box));
  requires _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || (read($Heap, this, _module.RingBuffer.N) != 0
         ==> read($Heap, this, _module.RingBuffer.len)
           <= read($Heap, this, _module.RingBuffer.N));
  requires _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || (read($Heap, this, _module.RingBuffer.N) != 0
         ==> read($Heap, this, _module.RingBuffer.start)
           < read($Heap, this, _module.RingBuffer.N));
  requires _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || Seq#Equal(read($Heap, this, _module.RingBuffer.Contents),
        (if read($Heap, this, _module.RingBuffer.start)
               + read($Heap, this, _module.RingBuffer.len)
             <= read($Heap, this, _module.RingBuffer.N)
           then Seq#Drop(Seq#Take(Seq#FromArray($Heap, read($Heap, this, _module.RingBuffer.data)),
              read($Heap, this, _module.RingBuffer.start)
                 + read($Heap, this, _module.RingBuffer.len)),
            read($Heap, this, _module.RingBuffer.start))
           else Seq#Append(Seq#Drop(Seq#FromArray($Heap, read($Heap, this, _module.RingBuffer.data)),
              read($Heap, this, _module.RingBuffer.start)),
            Seq#Take(Seq#FromArray($Heap, read($Heap, this, _module.RingBuffer.data)),
              read($Heap, this, _module.RingBuffer.start)
                   + read($Heap, this, _module.RingBuffer.len)
                 - read($Heap, this, _module.RingBuffer.N)))));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this);
  free ensures _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     &&
    _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
     &&
    read($Heap, this, _module.RingBuffer.Repr)[$Box(this)]
     && !read($Heap, this, _module.RingBuffer.Repr)[$Box(null)]
     &&
    (read($Heap, this, _module.RingBuffer.data) != null
       ==> read($Heap, this, _module.RingBuffer.Repr)[$Box(read($Heap, this, _module.RingBuffer.data))])
     &&
    read($Heap, this, _module.RingBuffer.data) != null
     && _System.array.Length(read($Heap, this, _module.RingBuffer.data))
       == read($Heap, this, _module.RingBuffer.N)
     && (read($Heap, this, _module.RingBuffer.N) == LitInt(0)
       ==> read($Heap, this, _module.RingBuffer.len)
           == read($Heap, this, _module.RingBuffer.start)
         && read($Heap, this, _module.RingBuffer.start) == LitInt(0)
         && Seq#Equal(read($Heap, this, _module.RingBuffer.Contents), Seq#Empty(): Seq Box))
     && (read($Heap, this, _module.RingBuffer.N) != 0
       ==> read($Heap, this, _module.RingBuffer.len)
           <= read($Heap, this, _module.RingBuffer.N)
         && read($Heap, this, _module.RingBuffer.start)
           < read($Heap, this, _module.RingBuffer.N))
     && Seq#Equal(read($Heap, this, _module.RingBuffer.Contents),
      (if read($Heap, this, _module.RingBuffer.start)
             + read($Heap, this, _module.RingBuffer.len)
           <= read($Heap, this, _module.RingBuffer.N)
         then Seq#Drop(Seq#Take(Seq#FromArray($Heap, read($Heap, this, _module.RingBuffer.data)),
            read($Heap, this, _module.RingBuffer.start)
               + read($Heap, this, _module.RingBuffer.len)),
          read($Heap, this, _module.RingBuffer.start))
         else Seq#Append(Seq#Drop(Seq#FromArray($Heap, read($Heap, this, _module.RingBuffer.data)),
            read($Heap, this, _module.RingBuffer.start)),
          Seq#Take(Seq#FromArray($Heap, read($Heap, this, _module.RingBuffer.data)),
            read($Heap, this, _module.RingBuffer.start)
                 + read($Heap, this, _module.RingBuffer.len)
               - read($Heap, this, _module.RingBuffer.N)))));
  free ensures true;
  ensures (forall $o: ref ::
    { read(old($Heap), $o, alloc) }
    read($Heap, this, _module.RingBuffer.Repr)[$Box($o)]
         && !read(old($Heap), this, _module.RingBuffer.Repr)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures true;
  ensures Seq#Equal(read($Heap, this, _module.RingBuffer.Contents),
    Seq#Append(read(old($Heap), this, _module.RingBuffer.Contents),
      Seq#Build(Seq#Empty(): Seq Box, x#0)));
  ensures read($Heap, this, _module.RingBuffer.N)
     >= read(old($Heap), this, _module.RingBuffer.N);
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f)
         || read(old($Heap), this, _module.RingBuffer.Repr)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.RingBuffer.ResizingEnqueue(_module.RingBuffer$T: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.RingBuffer(_module.RingBuffer$T))
         && $IsAlloc(this, Tclass._module.RingBuffer(_module.RingBuffer$T), $Heap),
    x#0: Box
       where $IsBox(x#0, _module.RingBuffer$T)
         && $IsAllocBox(x#0, _module.RingBuffer$T, $Heap))
   returns ($_reverifyPost: bool);
  free requires 8 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     &&
    _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
     &&
    read($Heap, this, _module.RingBuffer.Repr)[$Box(this)]
     && !read($Heap, this, _module.RingBuffer.Repr)[$Box(null)]
     &&
    (read($Heap, this, _module.RingBuffer.data) != null
       ==> read($Heap, this, _module.RingBuffer.Repr)[$Box(read($Heap, this, _module.RingBuffer.data))])
     &&
    read($Heap, this, _module.RingBuffer.data) != null
     && _System.array.Length(read($Heap, this, _module.RingBuffer.data))
       == read($Heap, this, _module.RingBuffer.N)
     && (read($Heap, this, _module.RingBuffer.N) == LitInt(0)
       ==> read($Heap, this, _module.RingBuffer.len)
           == read($Heap, this, _module.RingBuffer.start)
         && read($Heap, this, _module.RingBuffer.start) == LitInt(0)
         && Seq#Equal(read($Heap, this, _module.RingBuffer.Contents), Seq#Empty(): Seq Box))
     && (read($Heap, this, _module.RingBuffer.N) != 0
       ==> read($Heap, this, _module.RingBuffer.len)
           <= read($Heap, this, _module.RingBuffer.N)
         && read($Heap, this, _module.RingBuffer.start)
           < read($Heap, this, _module.RingBuffer.N))
     && Seq#Equal(read($Heap, this, _module.RingBuffer.Contents),
      (if read($Heap, this, _module.RingBuffer.start)
             + read($Heap, this, _module.RingBuffer.len)
           <= read($Heap, this, _module.RingBuffer.N)
         then Seq#Drop(Seq#Take(Seq#FromArray($Heap, read($Heap, this, _module.RingBuffer.data)),
            read($Heap, this, _module.RingBuffer.start)
               + read($Heap, this, _module.RingBuffer.len)),
          read($Heap, this, _module.RingBuffer.start))
         else Seq#Append(Seq#Drop(Seq#FromArray($Heap, read($Heap, this, _module.RingBuffer.data)),
            read($Heap, this, _module.RingBuffer.start)),
          Seq#Take(Seq#FromArray($Heap, read($Heap, this, _module.RingBuffer.data)),
            read($Heap, this, _module.RingBuffer.start)
                 + read($Heap, this, _module.RingBuffer.len)
               - read($Heap, this, _module.RingBuffer.N)))));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this);
  ensures _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || read($Heap, this, _module.RingBuffer.Repr)[$Box(this)];
  ensures _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || !read($Heap, this, _module.RingBuffer.Repr)[$Box(null)];
  ensures _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || (read($Heap, this, _module.RingBuffer.data) != null
         ==> read($Heap, this, _module.RingBuffer.Repr)[$Box(read($Heap, this, _module.RingBuffer.data))]);
  ensures _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || read($Heap, this, _module.RingBuffer.data) != null;
  ensures _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || _System.array.Length(read($Heap, this, _module.RingBuffer.data))
         == read($Heap, this, _module.RingBuffer.N);
  ensures _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || (read($Heap, this, _module.RingBuffer.N) == LitInt(0)
         ==> read($Heap, this, _module.RingBuffer.len)
           == read($Heap, this, _module.RingBuffer.start));
  ensures _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || (read($Heap, this, _module.RingBuffer.N) == LitInt(0)
         ==> read($Heap, this, _module.RingBuffer.start) == LitInt(0));
  ensures _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || (read($Heap, this, _module.RingBuffer.N) == LitInt(0)
         ==> Seq#Equal(read($Heap, this, _module.RingBuffer.Contents), Seq#Empty(): Seq Box));
  ensures _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || (read($Heap, this, _module.RingBuffer.N) != 0
         ==> read($Heap, this, _module.RingBuffer.len)
           <= read($Heap, this, _module.RingBuffer.N));
  ensures _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || (read($Heap, this, _module.RingBuffer.N) != 0
         ==> read($Heap, this, _module.RingBuffer.start)
           < read($Heap, this, _module.RingBuffer.N));
  ensures _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || Seq#Equal(read($Heap, this, _module.RingBuffer.Contents),
        (if read($Heap, this, _module.RingBuffer.start)
               + read($Heap, this, _module.RingBuffer.len)
             <= read($Heap, this, _module.RingBuffer.N)
           then Seq#Drop(Seq#Take(Seq#FromArray($Heap, read($Heap, this, _module.RingBuffer.data)),
              read($Heap, this, _module.RingBuffer.start)
                 + read($Heap, this, _module.RingBuffer.len)),
            read($Heap, this, _module.RingBuffer.start))
           else Seq#Append(Seq#Drop(Seq#FromArray($Heap, read($Heap, this, _module.RingBuffer.data)),
              read($Heap, this, _module.RingBuffer.start)),
            Seq#Take(Seq#FromArray($Heap, read($Heap, this, _module.RingBuffer.data)),
              read($Heap, this, _module.RingBuffer.start)
                   + read($Heap, this, _module.RingBuffer.len)
                 - read($Heap, this, _module.RingBuffer.N)))));
  free ensures true;
  ensures (forall $o: ref ::
    { read(old($Heap), $o, alloc) }
    read($Heap, this, _module.RingBuffer.Repr)[$Box($o)]
         && !read(old($Heap), this, _module.RingBuffer.Repr)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures true;
  ensures Seq#Equal(read($Heap, this, _module.RingBuffer.Contents),
    Seq#Append(read(old($Heap), this, _module.RingBuffer.Contents),
      Seq#Build(Seq#Empty(): Seq Box, x#0)));
  ensures read($Heap, this, _module.RingBuffer.N)
     >= read(old($Heap), this, _module.RingBuffer.N);
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f)
         || read(old($Heap), this, _module.RingBuffer.Repr)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.RingBuffer.ResizingEnqueue(_module.RingBuffer$T: Ty, this: ref, x#0: Box) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var more#0_0: int;
  var d#0_0: ref
     where $Is(d#0_0, Tclass._System.array(_module.RingBuffer$T))
       && $IsAlloc(d#0_0, Tclass._System.array(_module.RingBuffer$T), $Heap);
  var $nw: ref;
  var i#0_0: int;
  var i#0_1: int;
  var $prevHeap: Heap;
  var $obj0: ref;
  var $obj1: ref;
  var $obj2: ref;
  var $rhs#0_0: int where LitInt(0) <= $rhs#0_0;
  var $rhs#0_1: ref where $Is($rhs#0_1, Tclass._System.array(_module.RingBuffer$T));
  var $rhs#0_2: int where LitInt(0) <= $rhs#0_2;
  var nextEmpty#0: int;
  var $rhs#0: Box where $IsBox($rhs#0, _module.RingBuffer$T);
  var $rhs#1: int where LitInt(0) <= $rhs#1;
  var $rhs#2: Seq Box where $Is($rhs#2, TSeq(_module.RingBuffer$T));
  var $rhs#1_0: Set Box where $Is($rhs#1_0, TSet(Tclass._System.object()));

    // AddMethodImpl: ResizingEnqueue, Impl$$_module.RingBuffer.ResizingEnqueue
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc)
         ==> read($Heap, this, _module.RingBuffer.Repr)[$Box($o)]);
    assume {:captureState "RingBufferAuto.dfy(61,2): initial state"} true;
    $_reverifyPost := false;
    // ----- if statement ----- RingBufferAuto.dfy(62,5)
    assert read($Heap, this, _module.RingBuffer.data) != null;
    assume true;
    if (_System.array.Length(read($Heap, this, _module.RingBuffer.data))
       == read($Heap, this, _module.RingBuffer.len))
    {
        // ----- assignment statement ----- RingBufferAuto.dfy(63,16)
        assume true;
        assert read($Heap, this, _module.RingBuffer.data) != null;
        assume true;
        more#0_0 := _System.array.Length(read($Heap, this, _module.RingBuffer.data)) + 1;
        assume {:captureState "RingBufferAuto.dfy(63,33)"} true;
        // ----- assignment statement ----- RingBufferAuto.dfy(64,13)
        assume true;
        assert read($Heap, this, _module.RingBuffer.data) != null;
        assert 0 <= _System.array.Length(read($Heap, this, _module.RingBuffer.data)) + more#0_0;
        havoc $nw;
        assume $nw != null
           &&
          !read($Heap, $nw, alloc)
           && dtype($nw) == Tclass._System.array(_module.RingBuffer$T);
        assume _System.array.Length($nw)
           == _System.array.Length(read($Heap, this, _module.RingBuffer.data)) + more#0_0;
        $Heap := update($Heap, $nw, alloc, true);
        assume $IsGoodHeap($Heap);
        assume $IsHeapAnchor($Heap);
        d#0_0 := $nw;
        assume {:captureState "RingBufferAuto.dfy(64,40)"} true;
        // ----- forall statement (assign) ----- RingBufferAuto.dfy(65,7)
        if (*)
        {
            // Assume Fuel Constant
            havoc i#0_0;
            if (LitInt(0) <= i#0_0)
            {
                assert {:subsumption 0} read($Heap, this, _module.RingBuffer.data) != null;
            }

            assume true;
            assume LitInt(0) <= i#0_0
               && i#0_0 < _System.array.Length(read($Heap, this, _module.RingBuffer.data));
            assert d#0_0 != null;
            if (i#0_0 < read($Heap, this, _module.RingBuffer.start))
            {
            }
            else
            {
            }

            assert {:subsumption 0} 0
                 <= (if i#0_0 < read($Heap, this, _module.RingBuffer.start)
                   then i#0_0
                   else i#0_0 + more#0_0)
               && (if i#0_0 < read($Heap, this, _module.RingBuffer.start)
                   then i#0_0
                   else i#0_0 + more#0_0)
                 < _System.array.Length(d#0_0);
            assume true;
            assert $_Frame[d#0_0, IndexField((if i#0_0 < read($Heap, this, _module.RingBuffer.start)
                 then i#0_0
                 else i#0_0 + more#0_0))];
            assert read($Heap, this, _module.RingBuffer.data) != null;
            assert {:subsumption 0} 0 <= i#0_0
               && i#0_0 < _System.array.Length(read($Heap, this, _module.RingBuffer.data));
            assume true;
            havoc i#0_1;
            assume LitInt(0) <= i#0_1
               && i#0_1 < _System.array.Length(read($Heap, this, _module.RingBuffer.data));
            assume i#0_0 != i#0_1;
            assert d#0_0 != d#0_0
               || IndexField((if i#0_0 < read($Heap, this, _module.RingBuffer.start)
                     then i#0_0
                     else i#0_0 + more#0_0))
                 != IndexField((if i#0_1 < read($Heap, this, _module.RingBuffer.start)
                     then i#0_1
                     else i#0_1 + more#0_0))
               || read($Heap, read($Heap, this, _module.RingBuffer.data), IndexField(i#0_0))
                 == read($Heap, read($Heap, this, _module.RingBuffer.data), IndexField(i#0_1));
            assume false;
        }
        else
        {
            $prevHeap := $Heap;
            havoc $Heap;
            assume $HeapSucc($prevHeap, $Heap);
            assume (forall<alpha> $o: ref, $f: Field alpha ::
              { read($Heap, $o, $f) }
              read($Heap, $o, $f) == read($prevHeap, $o, $f)
                 || (exists i#0_2: int ::
                  LitInt(0) <= i#0_2
                     && i#0_2 < _System.array.Length(read($prevHeap, this, _module.RingBuffer.data))
                     && $o == d#0_0
                     && $f
                       == IndexField((if i#0_2 < read($prevHeap, this, _module.RingBuffer.start)
                           then i#0_2
                           else i#0_2 + more#0_0))));
            assume (forall i#inv#0_0: int ::
              { read($Heap, d#0_0, IndexField(i#inv#0_0)) }
              LitInt(0) <= i#inv#0_0
                   && i#inv#0_0 < _System.array.Length(read($prevHeap, this, _module.RingBuffer.data))
                   && i#inv#0_0 < read($prevHeap, this, _module.RingBuffer.start)
                 ==> read($Heap, d#0_0, IndexField(i#inv#0_0))
                   == read($prevHeap, read($prevHeap, this, _module.RingBuffer.data), IndexField(i#inv#0_0)));
            assume (forall i#inv#0_0: int ::
              { read($Heap, d#0_0, IndexField(i#inv#0_0)) }
              LitInt(0) <= i#inv#0_0 - more#0_0
                   && i#inv#0_0 - more#0_0
                     < _System.array.Length(read($prevHeap, this, _module.RingBuffer.data))
                   && !(i#inv#0_0 - more#0_0 < read($prevHeap, this, _module.RingBuffer.start))
                 ==> read($Heap, d#0_0, IndexField(i#inv#0_0))
                   == read($prevHeap,
                    read($prevHeap, this, _module.RingBuffer.data),
                    IndexField(i#inv#0_0 - more#0_0)));
        }

        assume {:captureState "RingBufferAuto.dfy(67,6)"} true;
        // ----- update statement ----- RingBufferAuto.dfy(68,22)
        assume true;
        $obj0 := this;
        assert $_Frame[$obj0, _module.RingBuffer.N];
        assume true;
        $obj1 := this;
        assert $_Frame[$obj1, _module.RingBuffer.data];
        assume true;
        $obj2 := this;
        assert $_Frame[$obj2, _module.RingBuffer.start];
        assume true;
        assert $Is(read($Heap, this, _module.RingBuffer.N) + more#0_0, Tclass._System.nat());
        $rhs#0_0 := read($Heap, this, _module.RingBuffer.N) + more#0_0;
        assume true;
        $rhs#0_1 := d#0_0;
        if (read($Heap, this, _module.RingBuffer.len) == LitInt(0))
        {
        }
        else
        {
        }

        assume true;
        assert $Is((if read($Heap, this, _module.RingBuffer.len) == LitInt(0)
             then 0
             else read($Heap, this, _module.RingBuffer.start) + more#0_0),
          Tclass._System.nat());
        $rhs#0_2 := (if read($Heap, this, _module.RingBuffer.len) == LitInt(0)
           then 0
           else read($Heap, this, _module.RingBuffer.start) + more#0_0);
        $Heap := update($Heap, $obj0, _module.RingBuffer.N, $rhs#0_0);
        assume $IsGoodHeap($Heap);
        $Heap := update($Heap, $obj1, _module.RingBuffer.data, $rhs#0_1);
        assume $IsGoodHeap($Heap);
        $Heap := update($Heap, $obj2, _module.RingBuffer.start, $rhs#0_2);
        assume $IsGoodHeap($Heap);
        assume {:captureState "RingBufferAuto.dfy(68,73)"} true;
    }
    else
    {
    }

    // ----- assignment statement ----- RingBufferAuto.dfy(70,19)
    assume true;
    assert read($Heap, this, _module.RingBuffer.data) != null;
    if (read($Heap, this, _module.RingBuffer.start)
         + read($Heap, this, _module.RingBuffer.len)
       < _System.array.Length(read($Heap, this, _module.RingBuffer.data)))
    {
    }
    else
    {
        assert read($Heap, this, _module.RingBuffer.data) != null;
    }

    assume true;
    nextEmpty#0 := (if read($Heap, this, _module.RingBuffer.start)
           + read($Heap, this, _module.RingBuffer.len)
         < _System.array.Length(read($Heap, this, _module.RingBuffer.data))
       then read($Heap, this, _module.RingBuffer.start)
         + read($Heap, this, _module.RingBuffer.len)
       else read($Heap, this, _module.RingBuffer.start)
           + read($Heap, this, _module.RingBuffer.len)
         - _System.array.Length(read($Heap, this, _module.RingBuffer.data)));
    assume {:captureState "RingBufferAuto.dfy(71,68)"} true;
    // ----- assignment statement ----- RingBufferAuto.dfy(72,21)
    assert read($Heap, this, _module.RingBuffer.data) != null;
    assert 0 <= nextEmpty#0
       && nextEmpty#0 < _System.array.Length(read($Heap, this, _module.RingBuffer.data));
    assume true;
    assert $_Frame[read($Heap, this, _module.RingBuffer.data), IndexField(nextEmpty#0)];
    assume true;
    $rhs#0 := x#0;
    $Heap := update($Heap,
      read($Heap, this, _module.RingBuffer.data),
      IndexField(nextEmpty#0),
      $rhs#0);
    assume $IsGoodHeap($Heap);
    assume {:captureState "RingBufferAuto.dfy(72,24)"} true;
    // ----- assignment statement ----- RingBufferAuto.dfy(73,9)
    assume true;
    assert $_Frame[this, _module.RingBuffer.len];
    assume true;
    assert $Is(read($Heap, this, _module.RingBuffer.len) + 1, Tclass._System.nat());
    $rhs#1 := read($Heap, this, _module.RingBuffer.len) + 1;
    $Heap := update($Heap, this, _module.RingBuffer.len, $rhs#1);
    assume $IsGoodHeap($Heap);
    assume {:captureState "RingBufferAuto.dfy(73,18)"} true;
    // ----- assignment statement ----- RingBufferAuto.dfy(74,14)
    assume true;
    assert $_Frame[this, _module.RingBuffer.Contents];
    assume true;
    $rhs#2 := Seq#Append(read($Heap, this, _module.RingBuffer.Contents),
      Seq#Build(Seq#Empty(): Seq Box, x#0));
    $Heap := update($Heap, this, _module.RingBuffer.Contents, $rhs#2);
    assume $IsGoodHeap($Heap);
    assume {:captureState "RingBufferAuto.dfy(74,30)"} true;
    // ----- if statement ----- RingBufferAuto.dfy(59,10)
    if (read($Heap, this, _module.RingBuffer.data) != null)
    {
    }

    assume true;
    if (read($Heap, this, _module.RingBuffer.data) != null
       && !read($Heap, this, _module.RingBuffer.Repr)[$Box(read($Heap, this, _module.RingBuffer.data))])
    {
        // ----- assignment statement ----- RingBufferAuto.dfy(59,10)
        assume true;
        assert $_Frame[this, _module.RingBuffer.Repr];
        assume true;
        $rhs#1_0 := Set#Union(read($Heap, this, _module.RingBuffer.Repr),
          Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.RingBuffer.data))));
        $Heap := update($Heap, this, _module.RingBuffer.Repr, $rhs#1_0);
        assume $IsGoodHeap($Heap);
        assume {:captureState "RingBufferAuto.dfy(59,9)"} true;
    }
    else
    {
    }
}



procedure CheckWellformed$$_module.RingBuffer.Dequeue(_module.RingBuffer$T: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.RingBuffer(_module.RingBuffer$T))
         && $IsAlloc(this, Tclass._module.RingBuffer(_module.RingBuffer$T), $Heap))
   returns (x#0: Box
       where $IsBox(x#0, _module.RingBuffer$T)
         && $IsAllocBox(x#0, _module.RingBuffer$T, $Heap));
  free requires 4 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.RingBuffer.Dequeue(_module.RingBuffer$T: Ty, this: ref) returns (x#0: Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: Dequeue, CheckWellformed$$_module.RingBuffer.Dequeue
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc)
         ==> read($Heap, this, _module.RingBuffer.Repr)[$Box($o)]);
    assume {:captureState "RingBufferAuto.dfy(77,9): initial state"} true;
    assume _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this);
    assume _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this);
    assume !Seq#Equal(read($Heap, this, _module.RingBuffer.Contents), Seq#Empty(): Seq Box);
    havoc $Heap;
    assume (forall<alpha> $o: ref, $f: Field alpha ::
      { read($Heap, $o, $f) }
      $o != null && read(old($Heap), $o, alloc)
         ==> read($Heap, $o, $f) == read(old($Heap), $o, $f)
           || read(old($Heap), this, _module.RingBuffer.Repr)[$Box($o)]);
    assume $HeapSucc(old($Heap), $Heap);
    havoc x#0;
    assume {:captureState "RingBufferAuto.dfy(77,9): post-state"} true;
    assume _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this);
    assume _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this);
    assert $IsAlloc(this, Tclass._module.RingBuffer(_module.RingBuffer$T), old($Heap));
    assume (forall $o: ref ::
      { read(old($Heap), $o, alloc) }
      read($Heap, this, _module.RingBuffer.Repr)[$Box($o)]
           && !read(old($Heap), this, _module.RingBuffer.Repr)[$Box($o)]
         ==> $o != null && !read(old($Heap), $o, alloc));
    assert $IsAlloc(this, Tclass._module.RingBuffer(_module.RingBuffer$T), old($Heap));
    assert 0 <= LitInt(0)
       && LitInt(0) < Seq#Length(read(old($Heap), this, _module.RingBuffer.Contents));
    assume x#0 == Seq#Index(read(old($Heap), this, _module.RingBuffer.Contents), LitInt(0));
    assert $IsAlloc(this, Tclass._module.RingBuffer(_module.RingBuffer$T), old($Heap));
    assert 0 <= LitInt(1)
       && LitInt(1) <= Seq#Length(read(old($Heap), this, _module.RingBuffer.Contents));
    assume Seq#Equal(read($Heap, this, _module.RingBuffer.Contents),
      Seq#Drop(read(old($Heap), this, _module.RingBuffer.Contents), LitInt(1)));
    assert $IsAlloc(this, Tclass._module.RingBuffer(_module.RingBuffer$T), old($Heap));
    assume read($Heap, this, _module.RingBuffer.N)
       == read(old($Heap), this, _module.RingBuffer.N);
}



procedure Call$$_module.RingBuffer.Dequeue(_module.RingBuffer$T: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.RingBuffer(_module.RingBuffer$T))
         && $IsAlloc(this, Tclass._module.RingBuffer(_module.RingBuffer$T), $Heap))
   returns (x#0: Box
       where $IsBox(x#0, _module.RingBuffer$T)
         && $IsAllocBox(x#0, _module.RingBuffer$T, $Heap));
  // user-defined preconditions
  requires _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || read($Heap, this, _module.RingBuffer.Repr)[$Box(this)];
  requires _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || !read($Heap, this, _module.RingBuffer.Repr)[$Box(null)];
  requires _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || (read($Heap, this, _module.RingBuffer.data) != null
         ==> read($Heap, this, _module.RingBuffer.Repr)[$Box(read($Heap, this, _module.RingBuffer.data))]);
  requires _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || read($Heap, this, _module.RingBuffer.data) != null;
  requires _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || _System.array.Length(read($Heap, this, _module.RingBuffer.data))
         == read($Heap, this, _module.RingBuffer.N);
  requires _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || (read($Heap, this, _module.RingBuffer.N) == LitInt(0)
         ==> read($Heap, this, _module.RingBuffer.len)
           == read($Heap, this, _module.RingBuffer.start));
  requires _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || (read($Heap, this, _module.RingBuffer.N) == LitInt(0)
         ==> read($Heap, this, _module.RingBuffer.start) == LitInt(0));
  requires _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || (read($Heap, this, _module.RingBuffer.N) == LitInt(0)
         ==> Seq#Equal(read($Heap, this, _module.RingBuffer.Contents), Seq#Empty(): Seq Box));
  requires _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || (read($Heap, this, _module.RingBuffer.N) != 0
         ==> read($Heap, this, _module.RingBuffer.len)
           <= read($Heap, this, _module.RingBuffer.N));
  requires _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || (read($Heap, this, _module.RingBuffer.N) != 0
         ==> read($Heap, this, _module.RingBuffer.start)
           < read($Heap, this, _module.RingBuffer.N));
  requires _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || Seq#Equal(read($Heap, this, _module.RingBuffer.Contents),
        (if read($Heap, this, _module.RingBuffer.start)
               + read($Heap, this, _module.RingBuffer.len)
             <= read($Heap, this, _module.RingBuffer.N)
           then Seq#Drop(Seq#Take(Seq#FromArray($Heap, read($Heap, this, _module.RingBuffer.data)),
              read($Heap, this, _module.RingBuffer.start)
                 + read($Heap, this, _module.RingBuffer.len)),
            read($Heap, this, _module.RingBuffer.start))
           else Seq#Append(Seq#Drop(Seq#FromArray($Heap, read($Heap, this, _module.RingBuffer.data)),
              read($Heap, this, _module.RingBuffer.start)),
            Seq#Take(Seq#FromArray($Heap, read($Heap, this, _module.RingBuffer.data)),
              read($Heap, this, _module.RingBuffer.start)
                   + read($Heap, this, _module.RingBuffer.len)
                 - read($Heap, this, _module.RingBuffer.N)))));
  requires !Seq#Equal(read($Heap, this, _module.RingBuffer.Contents), Seq#Empty(): Seq Box);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this);
  free ensures _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     &&
    _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
     &&
    read($Heap, this, _module.RingBuffer.Repr)[$Box(this)]
     && !read($Heap, this, _module.RingBuffer.Repr)[$Box(null)]
     &&
    (read($Heap, this, _module.RingBuffer.data) != null
       ==> read($Heap, this, _module.RingBuffer.Repr)[$Box(read($Heap, this, _module.RingBuffer.data))])
     &&
    read($Heap, this, _module.RingBuffer.data) != null
     && _System.array.Length(read($Heap, this, _module.RingBuffer.data))
       == read($Heap, this, _module.RingBuffer.N)
     && (read($Heap, this, _module.RingBuffer.N) == LitInt(0)
       ==> read($Heap, this, _module.RingBuffer.len)
           == read($Heap, this, _module.RingBuffer.start)
         && read($Heap, this, _module.RingBuffer.start) == LitInt(0)
         && Seq#Equal(read($Heap, this, _module.RingBuffer.Contents), Seq#Empty(): Seq Box))
     && (read($Heap, this, _module.RingBuffer.N) != 0
       ==> read($Heap, this, _module.RingBuffer.len)
           <= read($Heap, this, _module.RingBuffer.N)
         && read($Heap, this, _module.RingBuffer.start)
           < read($Heap, this, _module.RingBuffer.N))
     && Seq#Equal(read($Heap, this, _module.RingBuffer.Contents),
      (if read($Heap, this, _module.RingBuffer.start)
             + read($Heap, this, _module.RingBuffer.len)
           <= read($Heap, this, _module.RingBuffer.N)
         then Seq#Drop(Seq#Take(Seq#FromArray($Heap, read($Heap, this, _module.RingBuffer.data)),
            read($Heap, this, _module.RingBuffer.start)
               + read($Heap, this, _module.RingBuffer.len)),
          read($Heap, this, _module.RingBuffer.start))
         else Seq#Append(Seq#Drop(Seq#FromArray($Heap, read($Heap, this, _module.RingBuffer.data)),
            read($Heap, this, _module.RingBuffer.start)),
          Seq#Take(Seq#FromArray($Heap, read($Heap, this, _module.RingBuffer.data)),
            read($Heap, this, _module.RingBuffer.start)
                 + read($Heap, this, _module.RingBuffer.len)
               - read($Heap, this, _module.RingBuffer.N)))));
  free ensures true;
  ensures (forall $o: ref ::
    { read(old($Heap), $o, alloc) }
    read($Heap, this, _module.RingBuffer.Repr)[$Box($o)]
         && !read(old($Heap), this, _module.RingBuffer.Repr)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures true;
  ensures x#0 == Seq#Index(read(old($Heap), this, _module.RingBuffer.Contents), LitInt(0));
  ensures Seq#Equal(read($Heap, this, _module.RingBuffer.Contents),
    Seq#Drop(read(old($Heap), this, _module.RingBuffer.Contents), LitInt(1)));
  ensures read($Heap, this, _module.RingBuffer.N)
     == read(old($Heap), this, _module.RingBuffer.N);
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f)
         || read(old($Heap), this, _module.RingBuffer.Repr)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.RingBuffer.Dequeue(_module.RingBuffer$T: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.RingBuffer(_module.RingBuffer$T))
         && $IsAlloc(this, Tclass._module.RingBuffer(_module.RingBuffer$T), $Heap))
   returns (x#0: Box
       where $IsBox(x#0, _module.RingBuffer$T)
         && $IsAllocBox(x#0, _module.RingBuffer$T, $Heap),
    $_reverifyPost: bool);
  free requires 4 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     &&
    _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
     &&
    read($Heap, this, _module.RingBuffer.Repr)[$Box(this)]
     && !read($Heap, this, _module.RingBuffer.Repr)[$Box(null)]
     &&
    (read($Heap, this, _module.RingBuffer.data) != null
       ==> read($Heap, this, _module.RingBuffer.Repr)[$Box(read($Heap, this, _module.RingBuffer.data))])
     &&
    read($Heap, this, _module.RingBuffer.data) != null
     && _System.array.Length(read($Heap, this, _module.RingBuffer.data))
       == read($Heap, this, _module.RingBuffer.N)
     && (read($Heap, this, _module.RingBuffer.N) == LitInt(0)
       ==> read($Heap, this, _module.RingBuffer.len)
           == read($Heap, this, _module.RingBuffer.start)
         && read($Heap, this, _module.RingBuffer.start) == LitInt(0)
         && Seq#Equal(read($Heap, this, _module.RingBuffer.Contents), Seq#Empty(): Seq Box))
     && (read($Heap, this, _module.RingBuffer.N) != 0
       ==> read($Heap, this, _module.RingBuffer.len)
           <= read($Heap, this, _module.RingBuffer.N)
         && read($Heap, this, _module.RingBuffer.start)
           < read($Heap, this, _module.RingBuffer.N))
     && Seq#Equal(read($Heap, this, _module.RingBuffer.Contents),
      (if read($Heap, this, _module.RingBuffer.start)
             + read($Heap, this, _module.RingBuffer.len)
           <= read($Heap, this, _module.RingBuffer.N)
         then Seq#Drop(Seq#Take(Seq#FromArray($Heap, read($Heap, this, _module.RingBuffer.data)),
            read($Heap, this, _module.RingBuffer.start)
               + read($Heap, this, _module.RingBuffer.len)),
          read($Heap, this, _module.RingBuffer.start))
         else Seq#Append(Seq#Drop(Seq#FromArray($Heap, read($Heap, this, _module.RingBuffer.data)),
            read($Heap, this, _module.RingBuffer.start)),
          Seq#Take(Seq#FromArray($Heap, read($Heap, this, _module.RingBuffer.data)),
            read($Heap, this, _module.RingBuffer.start)
                 + read($Heap, this, _module.RingBuffer.len)
               - read($Heap, this, _module.RingBuffer.N)))));
  requires !Seq#Equal(read($Heap, this, _module.RingBuffer.Contents), Seq#Empty(): Seq Box);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this);
  ensures _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || read($Heap, this, _module.RingBuffer.Repr)[$Box(this)];
  ensures _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || !read($Heap, this, _module.RingBuffer.Repr)[$Box(null)];
  ensures _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || (read($Heap, this, _module.RingBuffer.data) != null
         ==> read($Heap, this, _module.RingBuffer.Repr)[$Box(read($Heap, this, _module.RingBuffer.data))]);
  ensures _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || read($Heap, this, _module.RingBuffer.data) != null;
  ensures _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || _System.array.Length(read($Heap, this, _module.RingBuffer.data))
         == read($Heap, this, _module.RingBuffer.N);
  ensures _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || (read($Heap, this, _module.RingBuffer.N) == LitInt(0)
         ==> read($Heap, this, _module.RingBuffer.len)
           == read($Heap, this, _module.RingBuffer.start));
  ensures _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || (read($Heap, this, _module.RingBuffer.N) == LitInt(0)
         ==> read($Heap, this, _module.RingBuffer.start) == LitInt(0));
  ensures _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || (read($Heap, this, _module.RingBuffer.N) == LitInt(0)
         ==> Seq#Equal(read($Heap, this, _module.RingBuffer.Contents), Seq#Empty(): Seq Box));
  ensures _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || (read($Heap, this, _module.RingBuffer.N) != 0
         ==> read($Heap, this, _module.RingBuffer.len)
           <= read($Heap, this, _module.RingBuffer.N));
  ensures _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || (read($Heap, this, _module.RingBuffer.N) != 0
         ==> read($Heap, this, _module.RingBuffer.start)
           < read($Heap, this, _module.RingBuffer.N));
  ensures _module.RingBuffer.Valid#canCall(_module.RingBuffer$T, $Heap, this)
     ==> _module.RingBuffer.Valid(_module.RingBuffer$T, $Heap, this)
       || Seq#Equal(read($Heap, this, _module.RingBuffer.Contents),
        (if read($Heap, this, _module.RingBuffer.start)
               + read($Heap, this, _module.RingBuffer.len)
             <= read($Heap, this, _module.RingBuffer.N)
           then Seq#Drop(Seq#Take(Seq#FromArray($Heap, read($Heap, this, _module.RingBuffer.data)),
              read($Heap, this, _module.RingBuffer.start)
                 + read($Heap, this, _module.RingBuffer.len)),
            read($Heap, this, _module.RingBuffer.start))
           else Seq#Append(Seq#Drop(Seq#FromArray($Heap, read($Heap, this, _module.RingBuffer.data)),
              read($Heap, this, _module.RingBuffer.start)),
            Seq#Take(Seq#FromArray($Heap, read($Heap, this, _module.RingBuffer.data)),
              read($Heap, this, _module.RingBuffer.start)
                   + read($Heap, this, _module.RingBuffer.len)
                 - read($Heap, this, _module.RingBuffer.N)))));
  free ensures true;
  ensures (forall $o: ref ::
    { read(old($Heap), $o, alloc) }
    read($Heap, this, _module.RingBuffer.Repr)[$Box($o)]
         && !read(old($Heap), this, _module.RingBuffer.Repr)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures true;
  ensures x#0 == Seq#Index(read(old($Heap), this, _module.RingBuffer.Contents), LitInt(0));
  ensures Seq#Equal(read($Heap, this, _module.RingBuffer.Contents),
    Seq#Drop(read(old($Heap), this, _module.RingBuffer.Contents), LitInt(1)));
  ensures read($Heap, this, _module.RingBuffer.N)
     == read(old($Heap), this, _module.RingBuffer.N);
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f)
         || read(old($Heap), this, _module.RingBuffer.Repr)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.RingBuffer.Dequeue(_module.RingBuffer$T: Ty, this: ref) returns (x#0: Box, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $obj0: ref;
  var $obj1: ref;
  var $rhs#0: int where LitInt(0) <= $rhs#0;
  var $rhs#1: int where LitInt(0) <= $rhs#1;
  var $rhs#2: Seq Box where $Is($rhs#2, TSeq(_module.RingBuffer$T));
  var $rhs#0_0: Set Box where $Is($rhs#0_0, TSet(Tclass._System.object()));

    // AddMethodImpl: Dequeue, Impl$$_module.RingBuffer.Dequeue
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc)
         ==> read($Heap, this, _module.RingBuffer.Repr)[$Box($o)]);
    assume {:captureState "RingBufferAuto.dfy(80,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- RingBufferAuto.dfy(81,7)
    assume true;
    assert read($Heap, this, _module.RingBuffer.data) != null;
    assert 0 <= read($Heap, this, _module.RingBuffer.start)
       && read($Heap, this, _module.RingBuffer.start)
         < _System.array.Length(read($Heap, this, _module.RingBuffer.data));
    assume true;
    x#0 := read($Heap,
      read($Heap, this, _module.RingBuffer.data),
      IndexField(read($Heap, this, _module.RingBuffer.start)));
    assume {:captureState "RingBufferAuto.dfy(81,20)"} true;
    // ----- assert statement ----- RingBufferAuto.dfy(81,24)
    assert {:subsumption 0} 0 <= LitInt(0)
       && LitInt(0) < Seq#Length(read($Heap, this, _module.RingBuffer.Contents));
    assume true;
    assert x#0 == Seq#Index(read($Heap, this, _module.RingBuffer.Contents), LitInt(0));
    // ----- update statement ----- RingBufferAuto.dfy(82,16)
    assume true;
    $obj0 := this;
    assert $_Frame[$obj0, _module.RingBuffer.start];
    assume true;
    $obj1 := this;
    assert $_Frame[$obj1, _module.RingBuffer.len];
    assert read($Heap, this, _module.RingBuffer.data) != null;
    if (read($Heap, this, _module.RingBuffer.start) + 1
       == _System.array.Length(read($Heap, this, _module.RingBuffer.data)))
    {
    }
    else
    {
    }

    assume true;
    assert $Is((if read($Heap, this, _module.RingBuffer.start) + 1
           == _System.array.Length(read($Heap, this, _module.RingBuffer.data))
         then 0
         else read($Heap, this, _module.RingBuffer.start) + 1),
      Tclass._System.nat());
    $rhs#0 := (if read($Heap, this, _module.RingBuffer.start) + 1
         == _System.array.Length(read($Heap, this, _module.RingBuffer.data))
       then 0
       else read($Heap, this, _module.RingBuffer.start) + 1);
    assume true;
    assert $Is(read($Heap, this, _module.RingBuffer.len) - 1, Tclass._System.nat());
    $rhs#1 := read($Heap, this, _module.RingBuffer.len) - 1;
    $Heap := update($Heap, $obj0, _module.RingBuffer.start, $rhs#0);
    assume $IsGoodHeap($Heap);
    $Heap := update($Heap, $obj1, _module.RingBuffer.len, $rhs#1);
    assume $IsGoodHeap($Heap);
    assume {:captureState "RingBufferAuto.dfy(82,76)"} true;
    // ----- assignment statement ----- RingBufferAuto.dfy(83,14)
    assume true;
    assert $_Frame[this, _module.RingBuffer.Contents];
    assert 0 <= LitInt(1)
       && LitInt(1) <= Seq#Length(read($Heap, this, _module.RingBuffer.Contents));
    assume true;
    $rhs#2 := Seq#Drop(read($Heap, this, _module.RingBuffer.Contents), LitInt(1));
    $Heap := update($Heap, this, _module.RingBuffer.Contents, $rhs#2);
    assume $IsGoodHeap($Heap);
    assume {:captureState "RingBufferAuto.dfy(83,29)"} true;
    // ----- if statement ----- RingBufferAuto.dfy(77,10)
    if (read($Heap, this, _module.RingBuffer.data) != null)
    {
    }

    assume true;
    if (read($Heap, this, _module.RingBuffer.data) != null
       && !read($Heap, this, _module.RingBuffer.Repr)[$Box(read($Heap, this, _module.RingBuffer.data))])
    {
        // ----- assignment statement ----- RingBufferAuto.dfy(77,10)
        assume true;
        assert $_Frame[this, _module.RingBuffer.Repr];
        assume true;
        $rhs#0_0 := Set#Union(read($Heap, this, _module.RingBuffer.Repr),
          Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.RingBuffer.data))));
        $Heap := update($Heap, this, _module.RingBuffer.Repr, $rhs#0_0);
        assume $IsGoodHeap($Heap);
        assume {:captureState "RingBufferAuto.dfy(77,9)"} true;
    }
    else
    {
    }
}



const _module.RingBuffer.Repr: Field (Set Box);

// RingBuffer.Repr: Allocation axiom
axiom (forall _module.RingBuffer$T: Ty, $h: Heap, $o: ref ::
  { read($h, $o, _module.RingBuffer.Repr), Tclass._module.RingBuffer(_module.RingBuffer$T) }
  $IsGoodHeap($h)
       && $o != null
       && dtype($o) == Tclass._module.RingBuffer(_module.RingBuffer$T)
     ==> $Is(read($h, $o, _module.RingBuffer.Repr), TSet(Tclass._System.object()))
       && (read($h, $o, alloc)
         ==> $IsAlloc(read($h, $o, _module.RingBuffer.Repr), TSet(Tclass._System.object()), $h)));

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

procedure CheckWellformed$$_module.__default.TestHarness(x#0: int, y#0: int, z#0: int);
  free requires 5 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.TestHarness(x#0: int, y#0: int, z#0: int);
  modifies $Heap, $Tick;
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.TestHarness(x#0: int, y#0: int, z#0: int) returns ($_reverifyPost: bool);
  free requires 5 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.TestHarness(x#0: int, y#0: int, z#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b#0: ref
     where $Is(b#0, Tclass._module.RingBuffer(TInt))
       && $IsAlloc(b#0, Tclass._module.RingBuffer(TInt), $Heap);
  var $nw: ref;
  var n##0: int;
  var x##0: Box;
  var x##1: Box;
  var h#0: int;
  var $rhs##0: int;
  var $tmp##0: Box;
  var x##2: Box;
  var $rhs##1: int;
  var $tmp##1: Box;
  var $rhs##2: int;
  var $tmp##2: Box;

    // AddMethodImpl: TestHarness, Impl$$_module.__default.TestHarness
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "RingBufferAuto.dfy(88,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- RingBufferAuto.dfy(89,9)
    assume true;
    // ----- init call statement ----- RingBufferAuto.dfy(89,27)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    assert $Is(LitInt(2), Tclass._System.nat());
    n##0 := LitInt(2);
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $nw := Call$$_module.RingBuffer.Create(TInt, n##0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "RingBufferAuto.dfy(89,35)"} true;
    b#0 := $nw;
    assume {:captureState "RingBufferAuto.dfy(89,35)"} true;
    // ----- call statement ----- RingBufferAuto.dfy(90,12)
    // TrCallStmt: Before ProcessCallStmt
    assert b#0 != null;
    assume true;
    // ProcessCallStmt: CheckSubrange
    x##0 := $Box(x#0);
    assert (forall<alpha> $o: ref, $f: Field alpha ::
      $o != null
           && read($Heap, $o, alloc)
           && read($Heap, b#0, _module.RingBuffer.Repr)[$Box($o)]
         ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.RingBuffer.Enqueue(TInt, b#0, x##0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "RingBufferAuto.dfy(90,14)"} true;
    // ----- call statement ----- RingBufferAuto.dfy(91,12)
    // TrCallStmt: Before ProcessCallStmt
    assert b#0 != null;
    assume true;
    // ProcessCallStmt: CheckSubrange
    x##1 := $Box(y#0);
    assert (forall<alpha> $o: ref, $f: Field alpha ::
      $o != null
           && read($Heap, $o, alloc)
           && read($Heap, b#0, _module.RingBuffer.Repr)[$Box($o)]
         ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.RingBuffer.Enqueue(TInt, b#0, x##1);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "RingBufferAuto.dfy(91,14)"} true;
    // ----- call statement ----- RingBufferAuto.dfy(92,21)
    assume true;
    // TrCallStmt: Adding lhs Microsoft.Dafny.AutoGhostIdentifierExpr with type int
    // TrCallStmt: Before ProcessCallStmt
    assert b#0 != null;
    assert (forall<alpha> $o: ref, $f: Field alpha ::
      $o != null
           && read($Heap, $o, alloc)
           && read($Heap, b#0, _module.RingBuffer.Repr)[$Box($o)]
         ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $tmp##0 := Call$$_module.RingBuffer.Dequeue(TInt, b#0);
    havoc $rhs##0;
    assume $rhs##0 == $Unbox($tmp##0): int;
    // TrCallStmt: After ProcessCallStmt
    h#0 := $rhs##0;
    assume {:captureState "RingBufferAuto.dfy(92,22)"} true;
    // ----- assert statement ----- RingBufferAuto.dfy(92,26)
    assume true;
    assert h#0 == x#0;
    // ----- call statement ----- RingBufferAuto.dfy(93,12)
    // TrCallStmt: Before ProcessCallStmt
    assert b#0 != null;
    assume true;
    // ProcessCallStmt: CheckSubrange
    x##2 := $Box(z#0);
    assert (forall<alpha> $o: ref, $f: Field alpha ::
      $o != null
           && read($Heap, $o, alloc)
           && read($Heap, b#0, _module.RingBuffer.Repr)[$Box($o)]
         ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.RingBuffer.Enqueue(TInt, b#0, x##2);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "RingBufferAuto.dfy(93,14)"} true;
    // ----- call statement ----- RingBufferAuto.dfy(94,17)
    assume true;
    // TrCallStmt: Adding lhs Microsoft.Dafny.IdentifierExpr with type int
    // TrCallStmt: Before ProcessCallStmt
    assert b#0 != null;
    assert (forall<alpha> $o: ref, $f: Field alpha ::
      $o != null
           && read($Heap, $o, alloc)
           && read($Heap, b#0, _module.RingBuffer.Repr)[$Box($o)]
         ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $tmp##1 := Call$$_module.RingBuffer.Dequeue(TInt, b#0);
    havoc $rhs##1;
    assume $rhs##1 == $Unbox($tmp##1): int;
    // TrCallStmt: After ProcessCallStmt
    h#0 := $rhs##1;
    assume {:captureState "RingBufferAuto.dfy(94,18)"} true;
    // ----- assert statement ----- RingBufferAuto.dfy(94,22)
    assume true;
    assert h#0 == y#0;
    // ----- call statement ----- RingBufferAuto.dfy(95,17)
    assume true;
    // TrCallStmt: Adding lhs Microsoft.Dafny.IdentifierExpr with type int
    // TrCallStmt: Before ProcessCallStmt
    assert b#0 != null;
    assert (forall<alpha> $o: ref, $f: Field alpha ::
      $o != null
           && read($Heap, $o, alloc)
           && read($Heap, b#0, _module.RingBuffer.Repr)[$Box($o)]
         ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $tmp##2 := Call$$_module.RingBuffer.Dequeue(TInt, b#0);
    havoc $rhs##2;
    assume $rhs##2 == $Unbox($tmp##2): int;
    // TrCallStmt: After ProcessCallStmt
    h#0 := $rhs##2;
    assume {:captureState "RingBufferAuto.dfy(95,18)"} true;
    // ----- assert statement ----- RingBufferAuto.dfy(95,22)
    assume true;
    assert h#0 == z#0;
}



const unique field$Contents: NameFamily;

const unique field$N: NameFamily;

const unique field$data: NameFamily;

const unique field$start: NameFamily;

const unique field$len: NameFamily;

const unique field$Repr: NameFamily;