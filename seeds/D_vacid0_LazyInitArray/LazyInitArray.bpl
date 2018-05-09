// Dafny 2.0.0.00922 technical preview 0
// Command Line Options: /compile:0 /noVerify /print:LazyInitArray.bpl LazyInitArray.dfy

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

const unique class._module.LazyInitArray: ClassName;

function Tclass._module.LazyInitArray(Ty) : Ty;

// Tclass._module.LazyInitArray Tag
axiom (forall _module.LazyInitArray$T: Ty ::
  { Tclass._module.LazyInitArray(_module.LazyInitArray$T) }
  Tag(Tclass._module.LazyInitArray(_module.LazyInitArray$T))
     == Tagclass._module.LazyInitArray);

const unique Tagclass._module.LazyInitArray: TyTag;

// Tclass._module.LazyInitArray injectivity 0
axiom (forall _module.LazyInitArray$T: Ty ::
  { Tclass._module.LazyInitArray(_module.LazyInitArray$T) }
  Tclass._module.LazyInitArray_0(Tclass._module.LazyInitArray(_module.LazyInitArray$T))
     == _module.LazyInitArray$T);

function Tclass._module.LazyInitArray_0(Ty) : Ty;

// Box/unbox axiom for Tclass._module.LazyInitArray
axiom (forall _module.LazyInitArray$T: Ty, bx: Box ::
  { $IsBox(bx, Tclass._module.LazyInitArray(_module.LazyInitArray$T)) }
  $IsBox(bx, Tclass._module.LazyInitArray(_module.LazyInitArray$T))
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.LazyInitArray(_module.LazyInitArray$T)));

// LazyInitArray: Class $Is
axiom (forall _module.LazyInitArray$T: Ty, $o: ref ::
  { $Is($o, Tclass._module.LazyInitArray(_module.LazyInitArray$T)) }
  $Is($o, Tclass._module.LazyInitArray(_module.LazyInitArray$T))
     <==> $o == null || dtype($o) == Tclass._module.LazyInitArray(_module.LazyInitArray$T));

// LazyInitArray: Class $IsAlloc
axiom (forall _module.LazyInitArray$T: Ty, $o: ref, $h: Heap ::
  { $IsAlloc($o, Tclass._module.LazyInitArray(_module.LazyInitArray$T), $h) }
  $IsAlloc($o, Tclass._module.LazyInitArray(_module.LazyInitArray$T), $h)
     <==> $o == null || read($h, $o, alloc));

axiom FDim(_module.LazyInitArray.Contents) == 0
   && FieldOfDecl(class._module.LazyInitArray, field$Contents)
     == _module.LazyInitArray.Contents
   && $IsGhostField(_module.LazyInitArray.Contents);

const _module.LazyInitArray.Contents: Field (Seq Box);

// LazyInitArray.Contents: Allocation axiom
axiom (forall _module.LazyInitArray$T: Ty, $h: Heap, $o: ref ::
  { read($h, $o, _module.LazyInitArray.Contents), Tclass._module.LazyInitArray(_module.LazyInitArray$T) }
  $IsGoodHeap($h)
       && $o != null
       && dtype($o) == Tclass._module.LazyInitArray(_module.LazyInitArray$T)
     ==> $Is(read($h, $o, _module.LazyInitArray.Contents), TSeq(_module.LazyInitArray$T))
       && (read($h, $o, alloc)
         ==> $IsAlloc(read($h, $o, _module.LazyInitArray.Contents), TSeq(_module.LazyInitArray$T), $h)));

axiom FDim(_module.LazyInitArray.Zero) == 0
   && FieldOfDecl(class._module.LazyInitArray, field$Zero)
     == _module.LazyInitArray.Zero
   && !$IsGhostField(_module.LazyInitArray.Zero);

const _module.LazyInitArray.Zero: Field Box;

// LazyInitArray.Zero: Allocation axiom
axiom (forall _module.LazyInitArray$T: Ty, $h: Heap, $o: ref ::
  { read($h, $o, _module.LazyInitArray.Zero), Tclass._module.LazyInitArray(_module.LazyInitArray$T) }
  $IsGoodHeap($h)
       && $o != null
       && dtype($o) == Tclass._module.LazyInitArray(_module.LazyInitArray$T)
     ==> $IsBox(read($h, $o, _module.LazyInitArray.Zero), _module.LazyInitArray$T)
       && (read($h, $o, alloc)
         ==> $IsAllocBox(read($h, $o, _module.LazyInitArray.Zero), _module.LazyInitArray$T, $h)));

axiom FDim(_module.LazyInitArray.a) == 0
   && FieldOfDecl(class._module.LazyInitArray, field$a) == _module.LazyInitArray.a
   && !$IsGhostField(_module.LazyInitArray.a);

const _module.LazyInitArray.a: Field ref;

// LazyInitArray.a: Allocation axiom
axiom (forall _module.LazyInitArray$T: Ty, $h: Heap, $o: ref ::
  { read($h, $o, _module.LazyInitArray.a), Tclass._module.LazyInitArray(_module.LazyInitArray$T) }
  $IsGoodHeap($h)
       && $o != null
       && dtype($o) == Tclass._module.LazyInitArray(_module.LazyInitArray$T)
     ==> $Is(read($h, $o, _module.LazyInitArray.a),
        Tclass._System.array(_module.LazyInitArray$T))
       && (read($h, $o, alloc)
         ==> $IsAlloc(read($h, $o, _module.LazyInitArray.a),
          Tclass._System.array(_module.LazyInitArray$T),
          $h)));

axiom FDim(_module.LazyInitArray.b) == 0
   && FieldOfDecl(class._module.LazyInitArray, field$b) == _module.LazyInitArray.b
   && !$IsGhostField(_module.LazyInitArray.b);

const _module.LazyInitArray.b: Field ref;

// LazyInitArray.b: Allocation axiom
axiom (forall _module.LazyInitArray$T: Ty, $h: Heap, $o: ref ::
  { read($h, $o, _module.LazyInitArray.b), Tclass._module.LazyInitArray(_module.LazyInitArray$T) }
  $IsGoodHeap($h)
       && $o != null
       && dtype($o) == Tclass._module.LazyInitArray(_module.LazyInitArray$T)
     ==> $Is(read($h, $o, _module.LazyInitArray.b), Tclass._System.array(TInt))
       && (read($h, $o, alloc)
         ==> $IsAlloc(read($h, $o, _module.LazyInitArray.b), Tclass._System.array(TInt), $h)));

axiom FDim(_module.LazyInitArray.c) == 0
   && FieldOfDecl(class._module.LazyInitArray, field$c) == _module.LazyInitArray.c
   && !$IsGhostField(_module.LazyInitArray.c);

const _module.LazyInitArray.c: Field ref;

// LazyInitArray.c: Allocation axiom
axiom (forall _module.LazyInitArray$T: Ty, $h: Heap, $o: ref ::
  { read($h, $o, _module.LazyInitArray.c), Tclass._module.LazyInitArray(_module.LazyInitArray$T) }
  $IsGoodHeap($h)
       && $o != null
       && dtype($o) == Tclass._module.LazyInitArray(_module.LazyInitArray$T)
     ==> $Is(read($h, $o, _module.LazyInitArray.c), Tclass._System.array(TInt))
       && (read($h, $o, alloc)
         ==> $IsAlloc(read($h, $o, _module.LazyInitArray.c), Tclass._System.array(TInt), $h)));

axiom FDim(_module.LazyInitArray.n) == 0
   && FieldOfDecl(class._module.LazyInitArray, field$n) == _module.LazyInitArray.n
   && !$IsGhostField(_module.LazyInitArray.n);

const _module.LazyInitArray.n: Field int;

// LazyInitArray.n: Allocation axiom
axiom (forall _module.LazyInitArray$T: Ty, $h: Heap, $o: ref ::
  { read($h, $o, _module.LazyInitArray.n), Tclass._module.LazyInitArray(_module.LazyInitArray$T) }
  $IsGoodHeap($h)
       && $o != null
       && dtype($o) == Tclass._module.LazyInitArray(_module.LazyInitArray$T)
     ==> $Is(read($h, $o, _module.LazyInitArray.n), TInt)
       && (read($h, $o, alloc)
         ==> $IsAlloc(read($h, $o, _module.LazyInitArray.n), TInt, $h)));

axiom FDim(_module.LazyInitArray.d) == 0
   && FieldOfDecl(class._module.LazyInitArray, field$d) == _module.LazyInitArray.d
   && $IsGhostField(_module.LazyInitArray.d);

const _module.LazyInitArray.d: Field (Seq Box);

// LazyInitArray.d: Allocation axiom
axiom (forall _module.LazyInitArray$T: Ty, $h: Heap, $o: ref ::
  { read($h, $o, _module.LazyInitArray.d), Tclass._module.LazyInitArray(_module.LazyInitArray$T) }
  $IsGoodHeap($h)
       && $o != null
       && dtype($o) == Tclass._module.LazyInitArray(_module.LazyInitArray$T)
     ==> $Is(read($h, $o, _module.LazyInitArray.d), TSeq(TInt))
       && (read($h, $o, alloc)
         ==> $IsAlloc(read($h, $o, _module.LazyInitArray.d), TSeq(TInt), $h)));

axiom FDim(_module.LazyInitArray.e) == 0
   && FieldOfDecl(class._module.LazyInitArray, field$e) == _module.LazyInitArray.e
   && $IsGhostField(_module.LazyInitArray.e);

const _module.LazyInitArray.e: Field (Seq Box);

// LazyInitArray.e: Allocation axiom
axiom (forall _module.LazyInitArray$T: Ty, $h: Heap, $o: ref ::
  { read($h, $o, _module.LazyInitArray.e), Tclass._module.LazyInitArray(_module.LazyInitArray$T) }
  $IsGoodHeap($h)
       && $o != null
       && dtype($o) == Tclass._module.LazyInitArray(_module.LazyInitArray$T)
     ==> $Is(read($h, $o, _module.LazyInitArray.e), TSeq(TInt))
       && (read($h, $o, alloc)
         ==> $IsAlloc(read($h, $o, _module.LazyInitArray.e), TSeq(TInt), $h)));

// function declaration for _module.LazyInitArray.Valid
function _module.LazyInitArray.Valid(_module.LazyInitArray$T: Ty, $heap: Heap, this: ref) : bool;

function _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T: Ty, $heap: Heap, this: ref) : bool;

// frame axiom for _module.LazyInitArray.Valid
axiom (forall _module.LazyInitArray$T: Ty, $h0: Heap, $h1: Heap, this: ref ::
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.LazyInitArray.Valid(_module.LazyInitArray$T, $h1, this) }
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       &&
      this != null
       && $Is(this, Tclass._module.LazyInitArray(_module.LazyInitArray$T))
       &&
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==>
    (forall<alpha> $o: ref, $f: Field alpha ::
      $o != null
           && (
            $o == this
             || $o == read($h0, this, _module.LazyInitArray.a)
             || $o == read($h0, this, _module.LazyInitArray.b)
             || $o == read($h0, this, _module.LazyInitArray.c))
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.LazyInitArray.Valid(_module.LazyInitArray$T, $h0, this)
       == _module.LazyInitArray.Valid(_module.LazyInitArray$T, $h1, this));

// consequence axiom for _module.LazyInitArray.Valid
axiom 0 <= $FunctionContextHeight
   ==> (forall _module.LazyInitArray$T: Ty, $Heap: Heap, this: ref ::
    { _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this) }
    _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
         || (0 != $FunctionContextHeight
           &&
          $IsGoodHeap($Heap)
           &&
          this != null
           &&
          $Is(this, Tclass._module.LazyInitArray(_module.LazyInitArray$T))
           && $IsAlloc(this, Tclass._module.LazyInitArray(_module.LazyInitArray$T), $Heap))
       ==> true);

function _module.LazyInitArray.Valid#requires(Ty, Heap, ref) : bool;

// #requires axiom for _module.LazyInitArray.Valid
axiom (forall _module.LazyInitArray$T: Ty, $Heap: Heap, this: ref ::
  { _module.LazyInitArray.Valid#requires(_module.LazyInitArray$T, $Heap, this) }
  $IsGoodHeap($Heap)
       &&
      this != null
       &&
      $Is(this, Tclass._module.LazyInitArray(_module.LazyInitArray$T))
       && $IsAlloc(this, Tclass._module.LazyInitArray(_module.LazyInitArray$T), $Heap)
     ==> _module.LazyInitArray.Valid#requires(_module.LazyInitArray$T, $Heap, this)
       == true);

// definition axiom for _module.LazyInitArray.Valid(revealed)
axiom 0 <= $FunctionContextHeight
   ==> (forall _module.LazyInitArray$T: Ty, $Heap: Heap, this: ref ::
    { _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this) }
    _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
         || (0 != $FunctionContextHeight
           &&
          $IsGoodHeap($Heap)
           &&
          this != null
           &&
          $Is(this, Tclass._module.LazyInitArray(_module.LazyInitArray$T))
           && $IsAlloc(this, Tclass._module.LazyInitArray(_module.LazyInitArray$T), $Heap))
       ==> (read($Heap, this, _module.LazyInitArray.n)
             <= _System.array.Length(read($Heap, this, _module.LazyInitArray.c))
           ==> (forall i#0: int ::
            { read($Heap, read($Heap, this, _module.LazyInitArray.a), IndexField(i#0)) }
              { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#0))): int }
              { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#0))): int }
              { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#0))): int }
              { Seq#Index(read($Heap, this, _module.LazyInitArray.Contents), i#0) }
            true))
         && ((forall i#0: int ::
              { read($Heap, read($Heap, this, _module.LazyInitArray.a), IndexField(i#0)) }
                { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#0))): int }
                { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#0))): int }
                { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#0))): int }
                { Seq#Index(read($Heap, this, _module.LazyInitArray.Contents), i#0) }
              true)
             && (forall i#0: int ::
              { read($Heap, read($Heap, this, _module.LazyInitArray.a), IndexField(i#0)) }
                { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#0))): int }
                { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#0))): int }
                { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#0))): int }
                { Seq#Index(read($Heap, this, _module.LazyInitArray.Contents), i#0) }
              true
                 ==>
                LitInt(0) <= i#0
                   && i#0 < Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
                 ==> Seq#Index(read($Heap, this, _module.LazyInitArray.Contents), i#0)
                   == (if LitInt(0)
                         <= $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#0))): int
                       && $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#0))): int
                         < read($Heap, this, _module.LazyInitArray.n)
                       && $Unbox(read($Heap,
                            read($Heap, this, _module.LazyInitArray.c),
                            IndexField($Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#0))): int))): int
                         == i#0
                     then read($Heap, read($Heap, this, _module.LazyInitArray.a), IndexField(i#0))
                     else read($Heap, this, _module.LazyInitArray.Zero)))
           ==> (forall i#1: int ::
            { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#1))): int }
              { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#1))): int }
              { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#1))): int }
            i#1 < Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
               ==> (forall j#0: int ::
                { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.c), IndexField(j#0))): int }
                true)))
         && (Seq#Length(read($Heap, this, _module.LazyInitArray.e))
             == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
           ==> (forall i#2: int ::
            { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#2)): int }
              { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.c), IndexField(i#2))): int }
            true))
         && ((forall i#2: int ::
              { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#2)): int }
                { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.c), IndexField(i#2))): int }
              true)
             && (forall i#2: int ::
              { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#2)): int }
                { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.c), IndexField(i#2))): int }
              true
                 ==>
                LitInt(0) <= i#2 && i#2 < read($Heap, this, _module.LazyInitArray.n)
                 ==> $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.c), IndexField(i#2))): int
                   == $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#2)): int)
           ==> (forall i#3: int ::
            { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#3)): int }
              { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#3)): int }
            true))
         && ((forall i#3: int ::
              { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#3)): int }
                { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#3)): int }
              true)
             && (forall i#3: int ::
              { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#3)): int }
                { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#3)): int }
              true
                 ==> (LitInt(0) <= i#3 && i#3 < Seq#Length(read($Heap, this, _module.LazyInitArray.d))
                     ==> LitInt(0)
                       <= $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#3)): int)
                   && (LitInt(0) <= i#3 && i#3 < Seq#Length(read($Heap, this, _module.LazyInitArray.d))
                     ==> $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#3)): int
                       < Seq#Length(read($Heap, this, _module.LazyInitArray.d))))
           ==> (forall i#4: int ::
            { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#4)): int }
              { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#4)): int }
            true))
         && ((forall i#4: int ::
              { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#4)): int }
                { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#4)): int }
              true)
             && (forall i#4: int ::
              { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#4)): int }
                { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#4)): int }
              true
                 ==> (LitInt(0) <= i#4 && i#4 < Seq#Length(read($Heap, this, _module.LazyInitArray.e))
                     ==> LitInt(0)
                       <= $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#4)): int)
                   && (LitInt(0) <= i#4 && i#4 < Seq#Length(read($Heap, this, _module.LazyInitArray.e))
                     ==> $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#4)): int
                       < Seq#Length(read($Heap, this, _module.LazyInitArray.e))))
           ==> (forall i#5: int ::
            { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#5)): int }
            true))
         && _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
           == (
            read($Heap, this, _module.LazyInitArray.a) != null
             && read($Heap, this, _module.LazyInitArray.b) != null
             && read($Heap, this, _module.LazyInitArray.c) != null
             && _System.array.Length(read($Heap, this, _module.LazyInitArray.a))
               == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
             && _System.array.Length(read($Heap, this, _module.LazyInitArray.b))
               == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
             && _System.array.Length(read($Heap, this, _module.LazyInitArray.c))
               == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
             && read($Heap, this, _module.LazyInitArray.b)
               != read($Heap, this, _module.LazyInitArray.c)
             && read($Heap, this, _module.LazyInitArray.a)
               != read($Heap, this, _module.LazyInitArray.b)
             && read($Heap, this, _module.LazyInitArray.a)
               != read($Heap, this, _module.LazyInitArray.c)
             && LitInt(0) <= read($Heap, this, _module.LazyInitArray.n)
             && read($Heap, this, _module.LazyInitArray.n)
               <= _System.array.Length(read($Heap, this, _module.LazyInitArray.c))
             && (forall i#0: int ::
              { read($Heap, read($Heap, this, _module.LazyInitArray.a), IndexField(i#0)) }
                { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#0))): int }
                { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#0))): int }
                { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#0))): int }
                { Seq#Index(read($Heap, this, _module.LazyInitArray.Contents), i#0) }
              true
                 ==>
                LitInt(0) <= i#0
                   && i#0 < Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
                 ==> Seq#Index(read($Heap, this, _module.LazyInitArray.Contents), i#0)
                   == (if LitInt(0)
                         <= $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#0))): int
                       && $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#0))): int
                         < read($Heap, this, _module.LazyInitArray.n)
                       && $Unbox(read($Heap,
                            read($Heap, this, _module.LazyInitArray.c),
                            IndexField($Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#0))): int))): int
                         == i#0
                     then read($Heap, read($Heap, this, _module.LazyInitArray.a), IndexField(i#0))
                     else read($Heap, this, _module.LazyInitArray.Zero)))
             && (forall i#1: int ::
              { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#1))): int }
                { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#1))): int }
                { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#1))): int }
              true
                 ==>
                LitInt(0) <= i#1
                   && i#1 < Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
                 ==> ((exists j#0: int ::
                    { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.c), IndexField(j#0))): int }
                    LitInt(0) <= j#0
                       && j#0 < read($Heap, this, _module.LazyInitArray.n)
                       && $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.c), IndexField(j#0))): int
                         == i#1)
                   <==> LitInt(0)
                       <= $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#1))): int
                     && $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#1))): int
                       < read($Heap, this, _module.LazyInitArray.n)
                     && $Unbox(read($Heap,
                          read($Heap, this, _module.LazyInitArray.c),
                          IndexField($Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#1))): int))): int
                       == i#1))
             && Seq#Length(read($Heap, this, _module.LazyInitArray.d))
               == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
             && Seq#Length(read($Heap, this, _module.LazyInitArray.e))
               == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
             && (forall i#2: int ::
              { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#2)): int }
                { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.c), IndexField(i#2))): int }
              true
                 ==>
                LitInt(0) <= i#2 && i#2 < read($Heap, this, _module.LazyInitArray.n)
                 ==> $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.c), IndexField(i#2))): int
                   == $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#2)): int)
             && (forall i#3: int ::
              { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#3)): int }
                { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#3)): int }
              true
                 ==> (LitInt(0) <= i#3 && i#3 < Seq#Length(read($Heap, this, _module.LazyInitArray.d))
                     ==> LitInt(0)
                       <= $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#3)): int)
                   && (LitInt(0) <= i#3 && i#3 < Seq#Length(read($Heap, this, _module.LazyInitArray.d))
                     ==> $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#3)): int
                       < Seq#Length(read($Heap, this, _module.LazyInitArray.d))))
             && (forall i#4: int ::
              { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#4)): int }
                { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#4)): int }
              true
                 ==> (LitInt(0) <= i#4 && i#4 < Seq#Length(read($Heap, this, _module.LazyInitArray.e))
                     ==> LitInt(0)
                       <= $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#4)): int)
                   && (LitInt(0) <= i#4 && i#4 < Seq#Length(read($Heap, this, _module.LazyInitArray.e))
                     ==> $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#4)): int
                       < Seq#Length(read($Heap, this, _module.LazyInitArray.e))))
             && (forall i#5: int ::
              { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#5)): int }
              true
                 ==>
                LitInt(0) <= i#5 && i#5 < Seq#Length(read($Heap, this, _module.LazyInitArray.e))
                 ==> $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d),
                      $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#5)): int)): int
                   == i#5)));

procedure CheckWellformed$$_module.LazyInitArray.Valid(_module.LazyInitArray$T: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.LazyInitArray(_module.LazyInitArray$T))
         && $IsAlloc(this, Tclass._module.LazyInitArray(_module.LazyInitArray$T), $Heap));
  free requires 0 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.LazyInitArray.Valid(_module.LazyInitArray$T: Ty, this: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;
  var b$reqreads#2: bool;
  var i#6: int;
  var i#7: int;
  var j#1: int;
  var i#10: int;
  var i#11: int;
  var i#13: int;
  var i#15: int;
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
  var b$reqreads#36: bool;
  var b$reqreads#37: bool;
  var b$reqreads#38: bool;
  var b$reqreads#39: bool;
  var b$reqreads#40: bool;
  var b$reqreads#41: bool;
  var b$reqreads#42: bool;
  var b$reqreads#43: bool;
  var b$reqreads#44: bool;
  var b$reqreads#45: bool;
  var b$reqreads#46: bool;
  var b$reqreads#47: bool;
  var b$reqreads#48: bool;
  var b$reqreads#49: bool;
  var b$reqreads#50: bool;
  var b$reqreads#51: bool;
  var b$reqreads#52: bool;
  var b$reqreads#53: bool;
  var b$reqreads#54: bool;
  var b$reqreads#55: bool;
  var b$reqreads#56: bool;
  var b$reqreads#57: bool;
  var b$reqreads#58: bool;
  var b$reqreads#59: bool;
  var b$reqreads#60: bool;
  var b$reqreads#61: bool;
  var b$reqreads#62: bool;
  var b$reqreads#63: bool;
  var b$reqreads#64: bool;
  var b$reqreads#65: bool;
  var b$reqreads#66: bool;

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
    b$reqreads#36 := true;
    b$reqreads#37 := true;
    b$reqreads#38 := true;
    b$reqreads#39 := true;
    b$reqreads#40 := true;
    b$reqreads#41 := true;
    b$reqreads#42 := true;
    b$reqreads#43 := true;
    b$reqreads#44 := true;
    b$reqreads#45 := true;
    b$reqreads#46 := true;
    b$reqreads#47 := true;
    b$reqreads#48 := true;
    b$reqreads#49 := true;
    b$reqreads#50 := true;
    b$reqreads#51 := true;
    b$reqreads#52 := true;
    b$reqreads#53 := true;
    b$reqreads#54 := true;
    b$reqreads#55 := true;
    b$reqreads#56 := true;
    b$reqreads#57 := true;
    b$reqreads#58 := true;
    b$reqreads#59 := true;
    b$reqreads#60 := true;
    b$reqreads#61 := true;
    b$reqreads#62 := true;
    b$reqreads#63 := true;
    b$reqreads#64 := true;
    b$reqreads#65 := true;
    b$reqreads#66 := true;

    // AddWellformednessCheck for function Valid
    assume {:captureState "LazyInitArray.dfy(13,12): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc)
         ==> $o == this
           || $o == read($Heap, this, _module.LazyInitArray.a)
           || $o == read($Heap, this, _module.LazyInitArray.b)
           || $o == read($Heap, this, _module.LazyInitArray.c));
    b$reqreads#0 := $_Frame[this, _module.LazyInitArray.a];
    b$reqreads#1 := $_Frame[this, _module.LazyInitArray.b];
    b$reqreads#2 := $_Frame[this, _module.LazyInitArray.c];
    assert b$reqreads#0;
    assert b$reqreads#1;
    assert b$reqreads#2;
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
          $o != null && read($Heap, $o, alloc)
             ==> $o == this
               || $o == read($Heap, this, _module.LazyInitArray.a)
               || $o == read($Heap, this, _module.LazyInitArray.b)
               || $o == read($Heap, this, _module.LazyInitArray.c));
        b$reqreads#3 := $_Frame[this, _module.LazyInitArray.a];
        if (read($Heap, this, _module.LazyInitArray.a) != null)
        {
            b$reqreads#4 := $_Frame[this, _module.LazyInitArray.b];
        }

        if (read($Heap, this, _module.LazyInitArray.a) != null
           && read($Heap, this, _module.LazyInitArray.b) != null)
        {
            b$reqreads#5 := $_Frame[this, _module.LazyInitArray.c];
        }

        if (read($Heap, this, _module.LazyInitArray.a) != null
           && read($Heap, this, _module.LazyInitArray.b) != null
           && read($Heap, this, _module.LazyInitArray.c) != null)
        {
            b$reqreads#6 := $_Frame[this, _module.LazyInitArray.a];
            assert read($Heap, this, _module.LazyInitArray.a) != null;
            b$reqreads#7 := $_Frame[this, _module.LazyInitArray.Contents];
        }

        if (read($Heap, this, _module.LazyInitArray.a) != null
           && read($Heap, this, _module.LazyInitArray.b) != null
           && read($Heap, this, _module.LazyInitArray.c) != null
           && _System.array.Length(read($Heap, this, _module.LazyInitArray.a))
             == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents)))
        {
            b$reqreads#8 := $_Frame[this, _module.LazyInitArray.b];
            assert read($Heap, this, _module.LazyInitArray.b) != null;
            b$reqreads#9 := $_Frame[this, _module.LazyInitArray.Contents];
        }

        if (read($Heap, this, _module.LazyInitArray.a) != null
           && read($Heap, this, _module.LazyInitArray.b) != null
           && read($Heap, this, _module.LazyInitArray.c) != null
           && _System.array.Length(read($Heap, this, _module.LazyInitArray.a))
             == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
           && _System.array.Length(read($Heap, this, _module.LazyInitArray.b))
             == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents)))
        {
            b$reqreads#10 := $_Frame[this, _module.LazyInitArray.c];
            assert read($Heap, this, _module.LazyInitArray.c) != null;
            b$reqreads#11 := $_Frame[this, _module.LazyInitArray.Contents];
        }

        if (read($Heap, this, _module.LazyInitArray.a) != null
           && read($Heap, this, _module.LazyInitArray.b) != null
           && read($Heap, this, _module.LazyInitArray.c) != null
           && _System.array.Length(read($Heap, this, _module.LazyInitArray.a))
             == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
           && _System.array.Length(read($Heap, this, _module.LazyInitArray.b))
             == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
           && _System.array.Length(read($Heap, this, _module.LazyInitArray.c))
             == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents)))
        {
            b$reqreads#12 := $_Frame[this, _module.LazyInitArray.b];
            b$reqreads#13 := $_Frame[this, _module.LazyInitArray.c];
        }

        if (read($Heap, this, _module.LazyInitArray.a) != null
           && read($Heap, this, _module.LazyInitArray.b) != null
           && read($Heap, this, _module.LazyInitArray.c) != null
           && _System.array.Length(read($Heap, this, _module.LazyInitArray.a))
             == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
           && _System.array.Length(read($Heap, this, _module.LazyInitArray.b))
             == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
           && _System.array.Length(read($Heap, this, _module.LazyInitArray.c))
             == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
           && read($Heap, this, _module.LazyInitArray.b)
             != read($Heap, this, _module.LazyInitArray.c))
        {
            b$reqreads#14 := $_Frame[this, _module.LazyInitArray.a];
            b$reqreads#15 := $_Frame[this, _module.LazyInitArray.b];
        }

        if (read($Heap, this, _module.LazyInitArray.a) != null
           && read($Heap, this, _module.LazyInitArray.b) != null
           && read($Heap, this, _module.LazyInitArray.c) != null
           && _System.array.Length(read($Heap, this, _module.LazyInitArray.a))
             == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
           && _System.array.Length(read($Heap, this, _module.LazyInitArray.b))
             == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
           && _System.array.Length(read($Heap, this, _module.LazyInitArray.c))
             == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
           && read($Heap, this, _module.LazyInitArray.b)
             != read($Heap, this, _module.LazyInitArray.c)
           && read($Heap, this, _module.LazyInitArray.a)
             != read($Heap, this, _module.LazyInitArray.b))
        {
            b$reqreads#16 := $_Frame[this, _module.LazyInitArray.a];
            b$reqreads#17 := $_Frame[this, _module.LazyInitArray.c];
        }

        if (read($Heap, this, _module.LazyInitArray.a) != null
           && read($Heap, this, _module.LazyInitArray.b) != null
           && read($Heap, this, _module.LazyInitArray.c) != null
           && _System.array.Length(read($Heap, this, _module.LazyInitArray.a))
             == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
           && _System.array.Length(read($Heap, this, _module.LazyInitArray.b))
             == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
           && _System.array.Length(read($Heap, this, _module.LazyInitArray.c))
             == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
           && read($Heap, this, _module.LazyInitArray.b)
             != read($Heap, this, _module.LazyInitArray.c)
           && read($Heap, this, _module.LazyInitArray.a)
             != read($Heap, this, _module.LazyInitArray.b)
           && read($Heap, this, _module.LazyInitArray.a)
             != read($Heap, this, _module.LazyInitArray.c))
        {
            b$reqreads#18 := $_Frame[this, _module.LazyInitArray.n];
        }

        if (read($Heap, this, _module.LazyInitArray.a) != null
           && read($Heap, this, _module.LazyInitArray.b) != null
           && read($Heap, this, _module.LazyInitArray.c) != null
           && _System.array.Length(read($Heap, this, _module.LazyInitArray.a))
             == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
           && _System.array.Length(read($Heap, this, _module.LazyInitArray.b))
             == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
           && _System.array.Length(read($Heap, this, _module.LazyInitArray.c))
             == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
           && read($Heap, this, _module.LazyInitArray.b)
             != read($Heap, this, _module.LazyInitArray.c)
           && read($Heap, this, _module.LazyInitArray.a)
             != read($Heap, this, _module.LazyInitArray.b)
           && read($Heap, this, _module.LazyInitArray.a)
             != read($Heap, this, _module.LazyInitArray.c)
           && LitInt(0) <= read($Heap, this, _module.LazyInitArray.n))
        {
            b$reqreads#19 := $_Frame[this, _module.LazyInitArray.n];
            b$reqreads#20 := $_Frame[this, _module.LazyInitArray.c];
            assert read($Heap, this, _module.LazyInitArray.c) != null;
        }

        if (read($Heap, this, _module.LazyInitArray.a) != null
           && read($Heap, this, _module.LazyInitArray.b) != null
           && read($Heap, this, _module.LazyInitArray.c) != null
           && _System.array.Length(read($Heap, this, _module.LazyInitArray.a))
             == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
           && _System.array.Length(read($Heap, this, _module.LazyInitArray.b))
             == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
           && _System.array.Length(read($Heap, this, _module.LazyInitArray.c))
             == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
           && read($Heap, this, _module.LazyInitArray.b)
             != read($Heap, this, _module.LazyInitArray.c)
           && read($Heap, this, _module.LazyInitArray.a)
             != read($Heap, this, _module.LazyInitArray.b)
           && read($Heap, this, _module.LazyInitArray.a)
             != read($Heap, this, _module.LazyInitArray.c)
           && LitInt(0) <= read($Heap, this, _module.LazyInitArray.n)
           && read($Heap, this, _module.LazyInitArray.n)
             <= _System.array.Length(read($Heap, this, _module.LazyInitArray.c)))
        {
            havoc i#6;
            // Begin Comprehension WF check
            if (LitInt(0) <= i#6)
            {
                b$reqreads#21 := $_Frame[this, _module.LazyInitArray.Contents];
            }

            if (LitInt(0) <= i#6
               && i#6 < Seq#Length(read($Heap, this, _module.LazyInitArray.Contents)))
            {
                b$reqreads#22 := $_Frame[this, _module.LazyInitArray.Contents];
                assert 0 <= i#6 && i#6 < Seq#Length(read($Heap, this, _module.LazyInitArray.Contents));
                b$reqreads#23 := $_Frame[this, _module.LazyInitArray.b];
                assert read($Heap, this, _module.LazyInitArray.b) != null;
                assert 0 <= i#6
                   && i#6 < _System.array.Length(read($Heap, this, _module.LazyInitArray.b));
                b$reqreads#24 := $_Frame[read($Heap, this, _module.LazyInitArray.b), IndexField(i#6)];
                if (LitInt(0)
                   <= $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#6))): int)
                {
                    b$reqreads#25 := $_Frame[this, _module.LazyInitArray.b];
                    assert read($Heap, this, _module.LazyInitArray.b) != null;
                    assert 0 <= i#6
                       && i#6 < _System.array.Length(read($Heap, this, _module.LazyInitArray.b));
                    b$reqreads#26 := $_Frame[read($Heap, this, _module.LazyInitArray.b), IndexField(i#6)];
                    b$reqreads#27 := $_Frame[this, _module.LazyInitArray.n];
                }

                if (LitInt(0)
                     <= $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#6))): int
                   && $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#6))): int
                     < read($Heap, this, _module.LazyInitArray.n))
                {
                    b$reqreads#28 := $_Frame[this, _module.LazyInitArray.c];
                    assert read($Heap, this, _module.LazyInitArray.c) != null;
                    b$reqreads#29 := $_Frame[this, _module.LazyInitArray.b];
                    assert read($Heap, this, _module.LazyInitArray.b) != null;
                    assert 0 <= i#6
                       && i#6 < _System.array.Length(read($Heap, this, _module.LazyInitArray.b));
                    b$reqreads#30 := $_Frame[read($Heap, this, _module.LazyInitArray.b), IndexField(i#6)];
                    assert 0
                         <= $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#6))): int
                       && $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#6))): int
                         < _System.array.Length(read($Heap, this, _module.LazyInitArray.c));
                    b$reqreads#31 := $_Frame[read($Heap, this, _module.LazyInitArray.c), IndexField($Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#6))): int)];
                }

                if (LitInt(0)
                     <= $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#6))): int
                   && $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#6))): int
                     < read($Heap, this, _module.LazyInitArray.n)
                   && $Unbox(read($Heap,
                        read($Heap, this, _module.LazyInitArray.c),
                        IndexField($Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#6))): int))): int
                     == i#6)
                {
                    b$reqreads#32 := $_Frame[this, _module.LazyInitArray.a];
                    assert read($Heap, this, _module.LazyInitArray.a) != null;
                    assert 0 <= i#6
                       && i#6 < _System.array.Length(read($Heap, this, _module.LazyInitArray.a));
                    b$reqreads#33 := $_Frame[read($Heap, this, _module.LazyInitArray.a), IndexField(i#6)];
                }
                else
                {
                    b$reqreads#34 := $_Frame[this, _module.LazyInitArray.Zero];
                }
            }

            // End Comprehension WF check
        }

        if (read($Heap, this, _module.LazyInitArray.a) != null
           && read($Heap, this, _module.LazyInitArray.b) != null
           && read($Heap, this, _module.LazyInitArray.c) != null
           && _System.array.Length(read($Heap, this, _module.LazyInitArray.a))
             == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
           && _System.array.Length(read($Heap, this, _module.LazyInitArray.b))
             == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
           && _System.array.Length(read($Heap, this, _module.LazyInitArray.c))
             == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
           && read($Heap, this, _module.LazyInitArray.b)
             != read($Heap, this, _module.LazyInitArray.c)
           && read($Heap, this, _module.LazyInitArray.a)
             != read($Heap, this, _module.LazyInitArray.b)
           && read($Heap, this, _module.LazyInitArray.a)
             != read($Heap, this, _module.LazyInitArray.c)
           && LitInt(0) <= read($Heap, this, _module.LazyInitArray.n)
           && read($Heap, this, _module.LazyInitArray.n)
             <= _System.array.Length(read($Heap, this, _module.LazyInitArray.c))
           && (forall i#8: int ::
            { read($Heap, read($Heap, this, _module.LazyInitArray.a), IndexField(i#8)) }
              { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#8))): int }
              { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#8))): int }
              { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#8))): int }
              { Seq#Index(read($Heap, this, _module.LazyInitArray.Contents), i#8) }
            true
               ==>
              LitInt(0) <= i#8
                 && i#8 < Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
               ==> Seq#Index(read($Heap, this, _module.LazyInitArray.Contents), i#8)
                 == (if LitInt(0)
                       <= $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#8))): int
                     && $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#8))): int
                       < read($Heap, this, _module.LazyInitArray.n)
                     && $Unbox(read($Heap,
                          read($Heap, this, _module.LazyInitArray.c),
                          IndexField($Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#8))): int))): int
                       == i#8
                   then read($Heap, read($Heap, this, _module.LazyInitArray.a), IndexField(i#8))
                   else read($Heap, this, _module.LazyInitArray.Zero))))
        {
            havoc i#7;
            // Begin Comprehension WF check
            if (LitInt(0) <= i#7)
            {
                b$reqreads#35 := $_Frame[this, _module.LazyInitArray.Contents];
            }

            if (LitInt(0) <= i#7
               && i#7 < Seq#Length(read($Heap, this, _module.LazyInitArray.Contents)))
            {
                havoc j#1;
                // Begin Comprehension WF check
                if (LitInt(0) <= j#1)
                {
                    b$reqreads#36 := $_Frame[this, _module.LazyInitArray.n];
                }

                if (LitInt(0) <= j#1 && j#1 < read($Heap, this, _module.LazyInitArray.n))
                {
                    b$reqreads#37 := $_Frame[this, _module.LazyInitArray.c];
                    assert read($Heap, this, _module.LazyInitArray.c) != null;
                    assert 0 <= j#1
                       && j#1 < _System.array.Length(read($Heap, this, _module.LazyInitArray.c));
                    b$reqreads#38 := $_Frame[read($Heap, this, _module.LazyInitArray.c), IndexField(j#1)];
                }

                // End Comprehension WF check
                b$reqreads#39 := $_Frame[this, _module.LazyInitArray.b];
                assert read($Heap, this, _module.LazyInitArray.b) != null;
                assert 0 <= i#7
                   && i#7 < _System.array.Length(read($Heap, this, _module.LazyInitArray.b));
                b$reqreads#40 := $_Frame[read($Heap, this, _module.LazyInitArray.b), IndexField(i#7)];
                if (LitInt(0)
                   <= $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#7))): int)
                {
                    b$reqreads#41 := $_Frame[this, _module.LazyInitArray.b];
                    assert read($Heap, this, _module.LazyInitArray.b) != null;
                    assert 0 <= i#7
                       && i#7 < _System.array.Length(read($Heap, this, _module.LazyInitArray.b));
                    b$reqreads#42 := $_Frame[read($Heap, this, _module.LazyInitArray.b), IndexField(i#7)];
                    b$reqreads#43 := $_Frame[this, _module.LazyInitArray.n];
                }

                if (LitInt(0)
                     <= $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#7))): int
                   && $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#7))): int
                     < read($Heap, this, _module.LazyInitArray.n))
                {
                    b$reqreads#44 := $_Frame[this, _module.LazyInitArray.c];
                    assert read($Heap, this, _module.LazyInitArray.c) != null;
                    b$reqreads#45 := $_Frame[this, _module.LazyInitArray.b];
                    assert read($Heap, this, _module.LazyInitArray.b) != null;
                    assert 0 <= i#7
                       && i#7 < _System.array.Length(read($Heap, this, _module.LazyInitArray.b));
                    b$reqreads#46 := $_Frame[read($Heap, this, _module.LazyInitArray.b), IndexField(i#7)];
                    assert 0
                         <= $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#7))): int
                       && $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#7))): int
                         < _System.array.Length(read($Heap, this, _module.LazyInitArray.c));
                    b$reqreads#47 := $_Frame[read($Heap, this, _module.LazyInitArray.c), IndexField($Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#7))): int)];
                }
            }

            // End Comprehension WF check
        }

        if (read($Heap, this, _module.LazyInitArray.a) != null
           && read($Heap, this, _module.LazyInitArray.b) != null
           && read($Heap, this, _module.LazyInitArray.c) != null
           && _System.array.Length(read($Heap, this, _module.LazyInitArray.a))
             == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
           && _System.array.Length(read($Heap, this, _module.LazyInitArray.b))
             == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
           && _System.array.Length(read($Heap, this, _module.LazyInitArray.c))
             == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
           && read($Heap, this, _module.LazyInitArray.b)
             != read($Heap, this, _module.LazyInitArray.c)
           && read($Heap, this, _module.LazyInitArray.a)
             != read($Heap, this, _module.LazyInitArray.b)
           && read($Heap, this, _module.LazyInitArray.a)
             != read($Heap, this, _module.LazyInitArray.c)
           && LitInt(0) <= read($Heap, this, _module.LazyInitArray.n)
           && read($Heap, this, _module.LazyInitArray.n)
             <= _System.array.Length(read($Heap, this, _module.LazyInitArray.c))
           && (forall i#8: int ::
            { read($Heap, read($Heap, this, _module.LazyInitArray.a), IndexField(i#8)) }
              { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#8))): int }
              { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#8))): int }
              { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#8))): int }
              { Seq#Index(read($Heap, this, _module.LazyInitArray.Contents), i#8) }
            true
               ==>
              LitInt(0) <= i#8
                 && i#8 < Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
               ==> Seq#Index(read($Heap, this, _module.LazyInitArray.Contents), i#8)
                 == (if LitInt(0)
                       <= $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#8))): int
                     && $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#8))): int
                       < read($Heap, this, _module.LazyInitArray.n)
                     && $Unbox(read($Heap,
                          read($Heap, this, _module.LazyInitArray.c),
                          IndexField($Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#8))): int))): int
                       == i#8
                   then read($Heap, read($Heap, this, _module.LazyInitArray.a), IndexField(i#8))
                   else read($Heap, this, _module.LazyInitArray.Zero)))
           && (forall i#9: int ::
            { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#9))): int }
              { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#9))): int }
              { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#9))): int }
            true
               ==>
              LitInt(0) <= i#9
                 && i#9 < Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
               ==> ((exists j#2: int ::
                  { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.c), IndexField(j#2))): int }
                  LitInt(0) <= j#2
                     && j#2 < read($Heap, this, _module.LazyInitArray.n)
                     && $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.c), IndexField(j#2))): int
                       == i#9)
                 <==> LitInt(0)
                     <= $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#9))): int
                   && $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#9))): int
                     < read($Heap, this, _module.LazyInitArray.n)
                   && $Unbox(read($Heap,
                        read($Heap, this, _module.LazyInitArray.c),
                        IndexField($Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#9))): int))): int
                     == i#9)))
        {
            b$reqreads#48 := $_Frame[this, _module.LazyInitArray.d];
            b$reqreads#49 := $_Frame[this, _module.LazyInitArray.Contents];
        }

        if (read($Heap, this, _module.LazyInitArray.a) != null
           && read($Heap, this, _module.LazyInitArray.b) != null
           && read($Heap, this, _module.LazyInitArray.c) != null
           && _System.array.Length(read($Heap, this, _module.LazyInitArray.a))
             == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
           && _System.array.Length(read($Heap, this, _module.LazyInitArray.b))
             == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
           && _System.array.Length(read($Heap, this, _module.LazyInitArray.c))
             == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
           && read($Heap, this, _module.LazyInitArray.b)
             != read($Heap, this, _module.LazyInitArray.c)
           && read($Heap, this, _module.LazyInitArray.a)
             != read($Heap, this, _module.LazyInitArray.b)
           && read($Heap, this, _module.LazyInitArray.a)
             != read($Heap, this, _module.LazyInitArray.c)
           && LitInt(0) <= read($Heap, this, _module.LazyInitArray.n)
           && read($Heap, this, _module.LazyInitArray.n)
             <= _System.array.Length(read($Heap, this, _module.LazyInitArray.c))
           && (forall i#8: int ::
            { read($Heap, read($Heap, this, _module.LazyInitArray.a), IndexField(i#8)) }
              { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#8))): int }
              { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#8))): int }
              { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#8))): int }
              { Seq#Index(read($Heap, this, _module.LazyInitArray.Contents), i#8) }
            true
               ==>
              LitInt(0) <= i#8
                 && i#8 < Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
               ==> Seq#Index(read($Heap, this, _module.LazyInitArray.Contents), i#8)
                 == (if LitInt(0)
                       <= $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#8))): int
                     && $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#8))): int
                       < read($Heap, this, _module.LazyInitArray.n)
                     && $Unbox(read($Heap,
                          read($Heap, this, _module.LazyInitArray.c),
                          IndexField($Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#8))): int))): int
                       == i#8
                   then read($Heap, read($Heap, this, _module.LazyInitArray.a), IndexField(i#8))
                   else read($Heap, this, _module.LazyInitArray.Zero)))
           && (forall i#9: int ::
            { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#9))): int }
              { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#9))): int }
              { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#9))): int }
            true
               ==>
              LitInt(0) <= i#9
                 && i#9 < Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
               ==> ((exists j#2: int ::
                  { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.c), IndexField(j#2))): int }
                  LitInt(0) <= j#2
                     && j#2 < read($Heap, this, _module.LazyInitArray.n)
                     && $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.c), IndexField(j#2))): int
                       == i#9)
                 <==> LitInt(0)
                     <= $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#9))): int
                   && $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#9))): int
                     < read($Heap, this, _module.LazyInitArray.n)
                   && $Unbox(read($Heap,
                        read($Heap, this, _module.LazyInitArray.c),
                        IndexField($Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#9))): int))): int
                     == i#9))
           && Seq#Length(read($Heap, this, _module.LazyInitArray.d))
             == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents)))
        {
            b$reqreads#50 := $_Frame[this, _module.LazyInitArray.e];
            b$reqreads#51 := $_Frame[this, _module.LazyInitArray.Contents];
        }

        if (read($Heap, this, _module.LazyInitArray.a) != null
           && read($Heap, this, _module.LazyInitArray.b) != null
           && read($Heap, this, _module.LazyInitArray.c) != null
           && _System.array.Length(read($Heap, this, _module.LazyInitArray.a))
             == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
           && _System.array.Length(read($Heap, this, _module.LazyInitArray.b))
             == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
           && _System.array.Length(read($Heap, this, _module.LazyInitArray.c))
             == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
           && read($Heap, this, _module.LazyInitArray.b)
             != read($Heap, this, _module.LazyInitArray.c)
           && read($Heap, this, _module.LazyInitArray.a)
             != read($Heap, this, _module.LazyInitArray.b)
           && read($Heap, this, _module.LazyInitArray.a)
             != read($Heap, this, _module.LazyInitArray.c)
           && LitInt(0) <= read($Heap, this, _module.LazyInitArray.n)
           && read($Heap, this, _module.LazyInitArray.n)
             <= _System.array.Length(read($Heap, this, _module.LazyInitArray.c))
           && (forall i#8: int ::
            { read($Heap, read($Heap, this, _module.LazyInitArray.a), IndexField(i#8)) }
              { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#8))): int }
              { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#8))): int }
              { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#8))): int }
              { Seq#Index(read($Heap, this, _module.LazyInitArray.Contents), i#8) }
            true
               ==>
              LitInt(0) <= i#8
                 && i#8 < Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
               ==> Seq#Index(read($Heap, this, _module.LazyInitArray.Contents), i#8)
                 == (if LitInt(0)
                       <= $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#8))): int
                     && $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#8))): int
                       < read($Heap, this, _module.LazyInitArray.n)
                     && $Unbox(read($Heap,
                          read($Heap, this, _module.LazyInitArray.c),
                          IndexField($Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#8))): int))): int
                       == i#8
                   then read($Heap, read($Heap, this, _module.LazyInitArray.a), IndexField(i#8))
                   else read($Heap, this, _module.LazyInitArray.Zero)))
           && (forall i#9: int ::
            { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#9))): int }
              { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#9))): int }
              { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#9))): int }
            true
               ==>
              LitInt(0) <= i#9
                 && i#9 < Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
               ==> ((exists j#2: int ::
                  { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.c), IndexField(j#2))): int }
                  LitInt(0) <= j#2
                     && j#2 < read($Heap, this, _module.LazyInitArray.n)
                     && $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.c), IndexField(j#2))): int
                       == i#9)
                 <==> LitInt(0)
                     <= $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#9))): int
                   && $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#9))): int
                     < read($Heap, this, _module.LazyInitArray.n)
                   && $Unbox(read($Heap,
                        read($Heap, this, _module.LazyInitArray.c),
                        IndexField($Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#9))): int))): int
                     == i#9))
           && Seq#Length(read($Heap, this, _module.LazyInitArray.d))
             == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
           && Seq#Length(read($Heap, this, _module.LazyInitArray.e))
             == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents)))
        {
            havoc i#10;
            // Begin Comprehension WF check
            if (LitInt(0) <= i#10)
            {
                b$reqreads#52 := $_Frame[this, _module.LazyInitArray.n];
            }

            if (LitInt(0) <= i#10 && i#10 < read($Heap, this, _module.LazyInitArray.n))
            {
                b$reqreads#53 := $_Frame[this, _module.LazyInitArray.c];
                assert read($Heap, this, _module.LazyInitArray.c) != null;
                assert 0 <= i#10
                   && i#10 < _System.array.Length(read($Heap, this, _module.LazyInitArray.c));
                b$reqreads#54 := $_Frame[read($Heap, this, _module.LazyInitArray.c), IndexField(i#10)];
                b$reqreads#55 := $_Frame[this, _module.LazyInitArray.d];
                assert 0 <= i#10 && i#10 < Seq#Length(read($Heap, this, _module.LazyInitArray.d));
            }

            // End Comprehension WF check
        }

        if (read($Heap, this, _module.LazyInitArray.a) != null
           && read($Heap, this, _module.LazyInitArray.b) != null
           && read($Heap, this, _module.LazyInitArray.c) != null
           && _System.array.Length(read($Heap, this, _module.LazyInitArray.a))
             == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
           && _System.array.Length(read($Heap, this, _module.LazyInitArray.b))
             == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
           && _System.array.Length(read($Heap, this, _module.LazyInitArray.c))
             == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
           && read($Heap, this, _module.LazyInitArray.b)
             != read($Heap, this, _module.LazyInitArray.c)
           && read($Heap, this, _module.LazyInitArray.a)
             != read($Heap, this, _module.LazyInitArray.b)
           && read($Heap, this, _module.LazyInitArray.a)
             != read($Heap, this, _module.LazyInitArray.c)
           && LitInt(0) <= read($Heap, this, _module.LazyInitArray.n)
           && read($Heap, this, _module.LazyInitArray.n)
             <= _System.array.Length(read($Heap, this, _module.LazyInitArray.c))
           && (forall i#8: int ::
            { read($Heap, read($Heap, this, _module.LazyInitArray.a), IndexField(i#8)) }
              { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#8))): int }
              { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#8))): int }
              { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#8))): int }
              { Seq#Index(read($Heap, this, _module.LazyInitArray.Contents), i#8) }
            true
               ==>
              LitInt(0) <= i#8
                 && i#8 < Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
               ==> Seq#Index(read($Heap, this, _module.LazyInitArray.Contents), i#8)
                 == (if LitInt(0)
                       <= $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#8))): int
                     && $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#8))): int
                       < read($Heap, this, _module.LazyInitArray.n)
                     && $Unbox(read($Heap,
                          read($Heap, this, _module.LazyInitArray.c),
                          IndexField($Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#8))): int))): int
                       == i#8
                   then read($Heap, read($Heap, this, _module.LazyInitArray.a), IndexField(i#8))
                   else read($Heap, this, _module.LazyInitArray.Zero)))
           && (forall i#9: int ::
            { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#9))): int }
              { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#9))): int }
              { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#9))): int }
            true
               ==>
              LitInt(0) <= i#9
                 && i#9 < Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
               ==> ((exists j#2: int ::
                  { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.c), IndexField(j#2))): int }
                  LitInt(0) <= j#2
                     && j#2 < read($Heap, this, _module.LazyInitArray.n)
                     && $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.c), IndexField(j#2))): int
                       == i#9)
                 <==> LitInt(0)
                     <= $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#9))): int
                   && $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#9))): int
                     < read($Heap, this, _module.LazyInitArray.n)
                   && $Unbox(read($Heap,
                        read($Heap, this, _module.LazyInitArray.c),
                        IndexField($Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#9))): int))): int
                     == i#9))
           && Seq#Length(read($Heap, this, _module.LazyInitArray.d))
             == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
           && Seq#Length(read($Heap, this, _module.LazyInitArray.e))
             == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
           && (forall i#12: int ::
            { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#12)): int }
              { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.c), IndexField(i#12))): int }
            true
               ==>
              LitInt(0) <= i#12 && i#12 < read($Heap, this, _module.LazyInitArray.n)
               ==> $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.c), IndexField(i#12))): int
                 == $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#12)): int))
        {
            havoc i#11;
            // Begin Comprehension WF check
            if (LitInt(0) <= i#11)
            {
                b$reqreads#56 := $_Frame[this, _module.LazyInitArray.d];
            }

            if (LitInt(0) <= i#11
               && i#11 < Seq#Length(read($Heap, this, _module.LazyInitArray.d)))
            {
                b$reqreads#57 := $_Frame[this, _module.LazyInitArray.d];
                assert 0 <= i#11 && i#11 < Seq#Length(read($Heap, this, _module.LazyInitArray.d));
                if (LitInt(0)
                   <= $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#11)): int)
                {
                    b$reqreads#58 := $_Frame[this, _module.LazyInitArray.d];
                    assert 0 <= i#11 && i#11 < Seq#Length(read($Heap, this, _module.LazyInitArray.d));
                    b$reqreads#59 := $_Frame[this, _module.LazyInitArray.d];
                }
            }

            // End Comprehension WF check
        }

        if (read($Heap, this, _module.LazyInitArray.a) != null
           && read($Heap, this, _module.LazyInitArray.b) != null
           && read($Heap, this, _module.LazyInitArray.c) != null
           && _System.array.Length(read($Heap, this, _module.LazyInitArray.a))
             == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
           && _System.array.Length(read($Heap, this, _module.LazyInitArray.b))
             == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
           && _System.array.Length(read($Heap, this, _module.LazyInitArray.c))
             == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
           && read($Heap, this, _module.LazyInitArray.b)
             != read($Heap, this, _module.LazyInitArray.c)
           && read($Heap, this, _module.LazyInitArray.a)
             != read($Heap, this, _module.LazyInitArray.b)
           && read($Heap, this, _module.LazyInitArray.a)
             != read($Heap, this, _module.LazyInitArray.c)
           && LitInt(0) <= read($Heap, this, _module.LazyInitArray.n)
           && read($Heap, this, _module.LazyInitArray.n)
             <= _System.array.Length(read($Heap, this, _module.LazyInitArray.c))
           && (forall i#8: int ::
            { read($Heap, read($Heap, this, _module.LazyInitArray.a), IndexField(i#8)) }
              { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#8))): int }
              { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#8))): int }
              { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#8))): int }
              { Seq#Index(read($Heap, this, _module.LazyInitArray.Contents), i#8) }
            true
               ==>
              LitInt(0) <= i#8
                 && i#8 < Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
               ==> Seq#Index(read($Heap, this, _module.LazyInitArray.Contents), i#8)
                 == (if LitInt(0)
                       <= $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#8))): int
                     && $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#8))): int
                       < read($Heap, this, _module.LazyInitArray.n)
                     && $Unbox(read($Heap,
                          read($Heap, this, _module.LazyInitArray.c),
                          IndexField($Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#8))): int))): int
                       == i#8
                   then read($Heap, read($Heap, this, _module.LazyInitArray.a), IndexField(i#8))
                   else read($Heap, this, _module.LazyInitArray.Zero)))
           && (forall i#9: int ::
            { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#9))): int }
              { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#9))): int }
              { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#9))): int }
            true
               ==>
              LitInt(0) <= i#9
                 && i#9 < Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
               ==> ((exists j#2: int ::
                  { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.c), IndexField(j#2))): int }
                  LitInt(0) <= j#2
                     && j#2 < read($Heap, this, _module.LazyInitArray.n)
                     && $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.c), IndexField(j#2))): int
                       == i#9)
                 <==> LitInt(0)
                     <= $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#9))): int
                   && $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#9))): int
                     < read($Heap, this, _module.LazyInitArray.n)
                   && $Unbox(read($Heap,
                        read($Heap, this, _module.LazyInitArray.c),
                        IndexField($Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#9))): int))): int
                     == i#9))
           && Seq#Length(read($Heap, this, _module.LazyInitArray.d))
             == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
           && Seq#Length(read($Heap, this, _module.LazyInitArray.e))
             == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
           && (forall i#12: int ::
            { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#12)): int }
              { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.c), IndexField(i#12))): int }
            true
               ==>
              LitInt(0) <= i#12 && i#12 < read($Heap, this, _module.LazyInitArray.n)
               ==> $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.c), IndexField(i#12))): int
                 == $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#12)): int)
           && (forall i#14: int ::
            { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#14)): int }
              { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#14)): int }
            true
               ==> (LitInt(0) <= i#14
                     && i#14 < Seq#Length(read($Heap, this, _module.LazyInitArray.d))
                   ==> LitInt(0)
                     <= $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#14)): int)
                 && (LitInt(0) <= i#14
                     && i#14 < Seq#Length(read($Heap, this, _module.LazyInitArray.d))
                   ==> $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#14)): int
                     < Seq#Length(read($Heap, this, _module.LazyInitArray.d)))))
        {
            havoc i#13;
            // Begin Comprehension WF check
            if (LitInt(0) <= i#13)
            {
                b$reqreads#60 := $_Frame[this, _module.LazyInitArray.e];
            }

            if (LitInt(0) <= i#13
               && i#13 < Seq#Length(read($Heap, this, _module.LazyInitArray.e)))
            {
                b$reqreads#61 := $_Frame[this, _module.LazyInitArray.e];
                assert 0 <= i#13 && i#13 < Seq#Length(read($Heap, this, _module.LazyInitArray.e));
                if (LitInt(0)
                   <= $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#13)): int)
                {
                    b$reqreads#62 := $_Frame[this, _module.LazyInitArray.e];
                    assert 0 <= i#13 && i#13 < Seq#Length(read($Heap, this, _module.LazyInitArray.e));
                    b$reqreads#63 := $_Frame[this, _module.LazyInitArray.e];
                }
            }

            // End Comprehension WF check
        }

        if (read($Heap, this, _module.LazyInitArray.a) != null
           && read($Heap, this, _module.LazyInitArray.b) != null
           && read($Heap, this, _module.LazyInitArray.c) != null
           && _System.array.Length(read($Heap, this, _module.LazyInitArray.a))
             == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
           && _System.array.Length(read($Heap, this, _module.LazyInitArray.b))
             == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
           && _System.array.Length(read($Heap, this, _module.LazyInitArray.c))
             == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
           && read($Heap, this, _module.LazyInitArray.b)
             != read($Heap, this, _module.LazyInitArray.c)
           && read($Heap, this, _module.LazyInitArray.a)
             != read($Heap, this, _module.LazyInitArray.b)
           && read($Heap, this, _module.LazyInitArray.a)
             != read($Heap, this, _module.LazyInitArray.c)
           && LitInt(0) <= read($Heap, this, _module.LazyInitArray.n)
           && read($Heap, this, _module.LazyInitArray.n)
             <= _System.array.Length(read($Heap, this, _module.LazyInitArray.c))
           && (forall i#8: int ::
            { read($Heap, read($Heap, this, _module.LazyInitArray.a), IndexField(i#8)) }
              { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#8))): int }
              { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#8))): int }
              { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#8))): int }
              { Seq#Index(read($Heap, this, _module.LazyInitArray.Contents), i#8) }
            true
               ==>
              LitInt(0) <= i#8
                 && i#8 < Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
               ==> Seq#Index(read($Heap, this, _module.LazyInitArray.Contents), i#8)
                 == (if LitInt(0)
                       <= $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#8))): int
                     && $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#8))): int
                       < read($Heap, this, _module.LazyInitArray.n)
                     && $Unbox(read($Heap,
                          read($Heap, this, _module.LazyInitArray.c),
                          IndexField($Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#8))): int))): int
                       == i#8
                   then read($Heap, read($Heap, this, _module.LazyInitArray.a), IndexField(i#8))
                   else read($Heap, this, _module.LazyInitArray.Zero)))
           && (forall i#9: int ::
            { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#9))): int }
              { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#9))): int }
              { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#9))): int }
            true
               ==>
              LitInt(0) <= i#9
                 && i#9 < Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
               ==> ((exists j#2: int ::
                  { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.c), IndexField(j#2))): int }
                  LitInt(0) <= j#2
                     && j#2 < read($Heap, this, _module.LazyInitArray.n)
                     && $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.c), IndexField(j#2))): int
                       == i#9)
                 <==> LitInt(0)
                     <= $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#9))): int
                   && $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#9))): int
                     < read($Heap, this, _module.LazyInitArray.n)
                   && $Unbox(read($Heap,
                        read($Heap, this, _module.LazyInitArray.c),
                        IndexField($Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#9))): int))): int
                     == i#9))
           && Seq#Length(read($Heap, this, _module.LazyInitArray.d))
             == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
           && Seq#Length(read($Heap, this, _module.LazyInitArray.e))
             == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
           && (forall i#12: int ::
            { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#12)): int }
              { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.c), IndexField(i#12))): int }
            true
               ==>
              LitInt(0) <= i#12 && i#12 < read($Heap, this, _module.LazyInitArray.n)
               ==> $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.c), IndexField(i#12))): int
                 == $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#12)): int)
           && (forall i#14: int ::
            { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#14)): int }
              { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#14)): int }
            true
               ==> (LitInt(0) <= i#14
                     && i#14 < Seq#Length(read($Heap, this, _module.LazyInitArray.d))
                   ==> LitInt(0)
                     <= $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#14)): int)
                 && (LitInt(0) <= i#14
                     && i#14 < Seq#Length(read($Heap, this, _module.LazyInitArray.d))
                   ==> $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#14)): int
                     < Seq#Length(read($Heap, this, _module.LazyInitArray.d))))
           && (forall i#16: int ::
            { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#16)): int }
              { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#16)): int }
            true
               ==> (LitInt(0) <= i#16
                     && i#16 < Seq#Length(read($Heap, this, _module.LazyInitArray.e))
                   ==> LitInt(0)
                     <= $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#16)): int)
                 && (LitInt(0) <= i#16
                     && i#16 < Seq#Length(read($Heap, this, _module.LazyInitArray.e))
                   ==> $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#16)): int
                     < Seq#Length(read($Heap, this, _module.LazyInitArray.e)))))
        {
            havoc i#15;
            // Begin Comprehension WF check
            if (LitInt(0) <= i#15)
            {
                b$reqreads#64 := $_Frame[this, _module.LazyInitArray.e];
            }

            if (LitInt(0) <= i#15
               && i#15 < Seq#Length(read($Heap, this, _module.LazyInitArray.e)))
            {
                b$reqreads#65 := $_Frame[this, _module.LazyInitArray.d];
                b$reqreads#66 := $_Frame[this, _module.LazyInitArray.e];
                assert 0 <= i#15 && i#15 < Seq#Length(read($Heap, this, _module.LazyInitArray.e));
                assert 0 <= $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#15)): int
                   && $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#15)): int
                     < Seq#Length(read($Heap, this, _module.LazyInitArray.d));
            }

            // End Comprehension WF check
        }

        assume _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
           == (
            read($Heap, this, _module.LazyInitArray.a) != null
             && read($Heap, this, _module.LazyInitArray.b) != null
             && read($Heap, this, _module.LazyInitArray.c) != null
             && _System.array.Length(read($Heap, this, _module.LazyInitArray.a))
               == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
             && _System.array.Length(read($Heap, this, _module.LazyInitArray.b))
               == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
             && _System.array.Length(read($Heap, this, _module.LazyInitArray.c))
               == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
             && read($Heap, this, _module.LazyInitArray.b)
               != read($Heap, this, _module.LazyInitArray.c)
             && read($Heap, this, _module.LazyInitArray.a)
               != read($Heap, this, _module.LazyInitArray.b)
             && read($Heap, this, _module.LazyInitArray.a)
               != read($Heap, this, _module.LazyInitArray.c)
             && LitInt(0) <= read($Heap, this, _module.LazyInitArray.n)
             && read($Heap, this, _module.LazyInitArray.n)
               <= _System.array.Length(read($Heap, this, _module.LazyInitArray.c))
             && (forall i#8: int ::
              { read($Heap, read($Heap, this, _module.LazyInitArray.a), IndexField(i#8)) }
                { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#8))): int }
                { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#8))): int }
                { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#8))): int }
                { Seq#Index(read($Heap, this, _module.LazyInitArray.Contents), i#8) }
              true
                 ==>
                LitInt(0) <= i#8
                   && i#8 < Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
                 ==> Seq#Index(read($Heap, this, _module.LazyInitArray.Contents), i#8)
                   == (if LitInt(0)
                         <= $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#8))): int
                       && $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#8))): int
                         < read($Heap, this, _module.LazyInitArray.n)
                       && $Unbox(read($Heap,
                            read($Heap, this, _module.LazyInitArray.c),
                            IndexField($Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#8))): int))): int
                         == i#8
                     then read($Heap, read($Heap, this, _module.LazyInitArray.a), IndexField(i#8))
                     else read($Heap, this, _module.LazyInitArray.Zero)))
             && (forall i#9: int ::
              { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#9))): int }
                { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#9))): int }
                { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#9))): int }
              true
                 ==>
                LitInt(0) <= i#9
                   && i#9 < Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
                 ==> ((exists j#2: int ::
                    { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.c), IndexField(j#2))): int }
                    LitInt(0) <= j#2
                       && j#2 < read($Heap, this, _module.LazyInitArray.n)
                       && $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.c), IndexField(j#2))): int
                         == i#9)
                   <==> LitInt(0)
                       <= $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#9))): int
                     && $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#9))): int
                       < read($Heap, this, _module.LazyInitArray.n)
                     && $Unbox(read($Heap,
                          read($Heap, this, _module.LazyInitArray.c),
                          IndexField($Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#9))): int))): int
                       == i#9))
             && Seq#Length(read($Heap, this, _module.LazyInitArray.d))
               == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
             && Seq#Length(read($Heap, this, _module.LazyInitArray.e))
               == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
             && (forall i#12: int ::
              { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#12)): int }
                { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.c), IndexField(i#12))): int }
              true
                 ==>
                LitInt(0) <= i#12 && i#12 < read($Heap, this, _module.LazyInitArray.n)
                 ==> $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.c), IndexField(i#12))): int
                   == $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#12)): int)
             && (forall i#14: int ::
              { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#14)): int }
                { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#14)): int }
              true
                 ==> (LitInt(0) <= i#14
                       && i#14 < Seq#Length(read($Heap, this, _module.LazyInitArray.d))
                     ==> LitInt(0)
                       <= $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#14)): int)
                   && (LitInt(0) <= i#14
                       && i#14 < Seq#Length(read($Heap, this, _module.LazyInitArray.d))
                     ==> $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#14)): int
                       < Seq#Length(read($Heap, this, _module.LazyInitArray.d))))
             && (forall i#16: int ::
              { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#16)): int }
                { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#16)): int }
              true
                 ==> (LitInt(0) <= i#16
                       && i#16 < Seq#Length(read($Heap, this, _module.LazyInitArray.e))
                     ==> LitInt(0)
                       <= $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#16)): int)
                   && (LitInt(0) <= i#16
                       && i#16 < Seq#Length(read($Heap, this, _module.LazyInitArray.e))
                     ==> $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#16)): int
                       < Seq#Length(read($Heap, this, _module.LazyInitArray.e))))
             && (forall i#17: int ::
              { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#17)): int }
              true
                 ==>
                LitInt(0) <= i#17
                   && i#17 < Seq#Length(read($Heap, this, _module.LazyInitArray.e))
                 ==> $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d),
                      $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#17)): int)): int
                   == i#17));
        assume (read($Heap, this, _module.LazyInitArray.n)
               <= _System.array.Length(read($Heap, this, _module.LazyInitArray.c))
             ==> (forall i#8: int ::
              { read($Heap, read($Heap, this, _module.LazyInitArray.a), IndexField(i#8)) }
                { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#8))): int }
                { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#8))): int }
                { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#8))): int }
                { Seq#Index(read($Heap, this, _module.LazyInitArray.Contents), i#8) }
              true))
           && ((forall i#8: int ::
                { read($Heap, read($Heap, this, _module.LazyInitArray.a), IndexField(i#8)) }
                  { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#8))): int }
                  { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#8))): int }
                  { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#8))): int }
                  { Seq#Index(read($Heap, this, _module.LazyInitArray.Contents), i#8) }
                true)
               && (forall i#8: int ::
                { read($Heap, read($Heap, this, _module.LazyInitArray.a), IndexField(i#8)) }
                  { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#8))): int }
                  { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#8))): int }
                  { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#8))): int }
                  { Seq#Index(read($Heap, this, _module.LazyInitArray.Contents), i#8) }
                true
                   ==>
                  LitInt(0) <= i#8
                     && i#8 < Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
                   ==> Seq#Index(read($Heap, this, _module.LazyInitArray.Contents), i#8)
                     == (if LitInt(0)
                           <= $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#8))): int
                         && $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#8))): int
                           < read($Heap, this, _module.LazyInitArray.n)
                         && $Unbox(read($Heap,
                              read($Heap, this, _module.LazyInitArray.c),
                              IndexField($Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#8))): int))): int
                           == i#8
                       then read($Heap, read($Heap, this, _module.LazyInitArray.a), IndexField(i#8))
                       else read($Heap, this, _module.LazyInitArray.Zero)))
             ==> (forall i#9: int ::
              { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#9))): int }
                { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#9))): int }
                { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#9))): int }
              i#9 < Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
                 ==> (forall j#2: int ::
                  { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.c), IndexField(j#2))): int }
                  true)))
           && (Seq#Length(read($Heap, this, _module.LazyInitArray.e))
               == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
             ==> (forall i#12: int ::
              { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#12)): int }
                { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.c), IndexField(i#12))): int }
              true))
           && ((forall i#12: int ::
                { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#12)): int }
                  { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.c), IndexField(i#12))): int }
                true)
               && (forall i#12: int ::
                { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#12)): int }
                  { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.c), IndexField(i#12))): int }
                true
                   ==>
                  LitInt(0) <= i#12 && i#12 < read($Heap, this, _module.LazyInitArray.n)
                   ==> $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.c), IndexField(i#12))): int
                     == $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#12)): int)
             ==> (forall i#14: int ::
              { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#14)): int }
                { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#14)): int }
              true))
           && ((forall i#14: int ::
                { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#14)): int }
                  { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#14)): int }
                true)
               && (forall i#14: int ::
                { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#14)): int }
                  { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#14)): int }
                true
                   ==> (LitInt(0) <= i#14
                         && i#14 < Seq#Length(read($Heap, this, _module.LazyInitArray.d))
                       ==> LitInt(0)
                         <= $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#14)): int)
                     && (LitInt(0) <= i#14
                         && i#14 < Seq#Length(read($Heap, this, _module.LazyInitArray.d))
                       ==> $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#14)): int
                         < Seq#Length(read($Heap, this, _module.LazyInitArray.d))))
             ==> (forall i#16: int ::
              { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#16)): int }
                { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#16)): int }
              true))
           && ((forall i#16: int ::
                { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#16)): int }
                  { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#16)): int }
                true)
               && (forall i#16: int ::
                { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#16)): int }
                  { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#16)): int }
                true
                   ==> (LitInt(0) <= i#16
                         && i#16 < Seq#Length(read($Heap, this, _module.LazyInitArray.e))
                       ==> LitInt(0)
                         <= $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#16)): int)
                     && (LitInt(0) <= i#16
                         && i#16 < Seq#Length(read($Heap, this, _module.LazyInitArray.e))
                       ==> $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#16)): int
                         < Seq#Length(read($Heap, this, _module.LazyInitArray.e))))
             ==> (forall i#17: int ::
              { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#17)): int }
              true));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this), TBool);
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
        assert b$reqreads#36;
        assert b$reqreads#37;
        assert b$reqreads#38;
        assert b$reqreads#39;
        assert b$reqreads#40;
        assert b$reqreads#41;
        assert b$reqreads#42;
        assert b$reqreads#43;
        assert b$reqreads#44;
        assert b$reqreads#45;
        assert b$reqreads#46;
        assert b$reqreads#47;
        assert b$reqreads#48;
        assert b$reqreads#49;
        assert b$reqreads#50;
        assert b$reqreads#51;
        assert b$reqreads#52;
        assert b$reqreads#53;
        assert b$reqreads#54;
        assert b$reqreads#55;
        assert b$reqreads#56;
        assert b$reqreads#57;
        assert b$reqreads#58;
        assert b$reqreads#59;
        assert b$reqreads#60;
        assert b$reqreads#61;
        assert b$reqreads#62;
        assert b$reqreads#63;
        assert b$reqreads#64;
        assert b$reqreads#65;
        assert b$reqreads#66;
    }
}



procedure CheckWellformed$$_module.LazyInitArray.Init(_module.LazyInitArray$T: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.LazyInitArray(_module.LazyInitArray$T))
         && $IsAlloc(this, Tclass._module.LazyInitArray(_module.LazyInitArray$T), $Heap),
    N#0: int,
    zero#0: Box
       where $IsBox(zero#0, _module.LazyInitArray$T)
         && $IsAllocBox(zero#0, _module.LazyInitArray$T, $Heap));
  free requires 1 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.LazyInitArray.Init(_module.LazyInitArray$T: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.LazyInitArray(_module.LazyInitArray$T))
         && $IsAlloc(this, Tclass._module.LazyInitArray(_module.LazyInitArray$T), $Heap),
    N#0: int,
    zero#0: Box
       where $IsBox(zero#0, _module.LazyInitArray$T)
         && $IsAllocBox(zero#0, _module.LazyInitArray$T, $Heap));
  // user-defined preconditions
  requires LitInt(0) <= N#0;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this);
  free ensures _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
     &&
    _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
     &&
    read($Heap, this, _module.LazyInitArray.a) != null
     && read($Heap, this, _module.LazyInitArray.b) != null
     && read($Heap, this, _module.LazyInitArray.c) != null
     && _System.array.Length(read($Heap, this, _module.LazyInitArray.a))
       == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
     && _System.array.Length(read($Heap, this, _module.LazyInitArray.b))
       == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
     && _System.array.Length(read($Heap, this, _module.LazyInitArray.c))
       == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
     && read($Heap, this, _module.LazyInitArray.b)
       != read($Heap, this, _module.LazyInitArray.c)
     && read($Heap, this, _module.LazyInitArray.a)
       != read($Heap, this, _module.LazyInitArray.b)
     && read($Heap, this, _module.LazyInitArray.a)
       != read($Heap, this, _module.LazyInitArray.c)
     && LitInt(0) <= read($Heap, this, _module.LazyInitArray.n)
     && read($Heap, this, _module.LazyInitArray.n)
       <= _System.array.Length(read($Heap, this, _module.LazyInitArray.c))
     && (forall i#0: int ::
      { read($Heap, read($Heap, this, _module.LazyInitArray.a), IndexField(i#0)) }
        { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#0))): int }
        { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#0))): int }
        { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#0))): int }
        { Seq#Index(read($Heap, this, _module.LazyInitArray.Contents), i#0) }
      true
         ==>
        LitInt(0) <= i#0
           && i#0 < Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
         ==> Seq#Index(read($Heap, this, _module.LazyInitArray.Contents), i#0)
           == (if LitInt(0)
                 <= $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#0))): int
               && $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#0))): int
                 < read($Heap, this, _module.LazyInitArray.n)
               && $Unbox(read($Heap,
                    read($Heap, this, _module.LazyInitArray.c),
                    IndexField($Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#0))): int))): int
                 == i#0
             then read($Heap, read($Heap, this, _module.LazyInitArray.a), IndexField(i#0))
             else read($Heap, this, _module.LazyInitArray.Zero)))
     && (forall i#1: int ::
      { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#1))): int }
        { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#1))): int }
        { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#1))): int }
      true
         ==>
        LitInt(0) <= i#1
           && i#1 < Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
         ==> ((exists j#0: int ::
            { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.c), IndexField(j#0))): int }
            LitInt(0) <= j#0
               && j#0 < read($Heap, this, _module.LazyInitArray.n)
               && $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.c), IndexField(j#0))): int
                 == i#1)
           <==> LitInt(0)
               <= $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#1))): int
             && $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#1))): int
               < read($Heap, this, _module.LazyInitArray.n)
             && $Unbox(read($Heap,
                  read($Heap, this, _module.LazyInitArray.c),
                  IndexField($Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#1))): int))): int
               == i#1))
     && Seq#Length(read($Heap, this, _module.LazyInitArray.d))
       == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
     && Seq#Length(read($Heap, this, _module.LazyInitArray.e))
       == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
     && (forall i#2: int ::
      { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#2)): int }
        { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.c), IndexField(i#2))): int }
      true
         ==>
        LitInt(0) <= i#2 && i#2 < read($Heap, this, _module.LazyInitArray.n)
         ==> $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.c), IndexField(i#2))): int
           == $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#2)): int)
     && (forall i#3: int ::
      { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#3)): int }
        { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#3)): int }
      true
         ==> (LitInt(0) <= i#3 && i#3 < Seq#Length(read($Heap, this, _module.LazyInitArray.d))
             ==> LitInt(0)
               <= $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#3)): int)
           && (LitInt(0) <= i#3 && i#3 < Seq#Length(read($Heap, this, _module.LazyInitArray.d))
             ==> $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#3)): int
               < Seq#Length(read($Heap, this, _module.LazyInitArray.d))))
     && (forall i#4: int ::
      { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#4)): int }
        { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#4)): int }
      true
         ==> (LitInt(0) <= i#4 && i#4 < Seq#Length(read($Heap, this, _module.LazyInitArray.e))
             ==> LitInt(0)
               <= $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#4)): int)
           && (LitInt(0) <= i#4 && i#4 < Seq#Length(read($Heap, this, _module.LazyInitArray.e))
             ==> $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#4)): int
               < Seq#Length(read($Heap, this, _module.LazyInitArray.e))))
     && (forall i#5: int ::
      { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#5)): int }
      true
         ==>
        LitInt(0) <= i#5 && i#5 < Seq#Length(read($Heap, this, _module.LazyInitArray.e))
         ==> $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d),
              $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#5)): int)): int
           == i#5);
  free ensures true;
  ensures Seq#Length(read($Heap, this, _module.LazyInitArray.Contents)) == N#0;
  ensures read($Heap, this, _module.LazyInitArray.Zero) == zero#0;
  free ensures (forall x#1: Box ::
    { Seq#Contains(read($Heap, this, _module.LazyInitArray.Contents), x#1) }
    true);
  ensures (forall x#1: Box ::
    { Seq#Contains(read($Heap, this, _module.LazyInitArray.Contents), x#1) }
    $IsBox(x#1, _module.LazyInitArray$T)
       ==>
      Seq#Contains(read($Heap, this, _module.LazyInitArray.Contents), x#1)
       ==> x#1 == zero#0);
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f)
         ||
        $o == this
         || $o == read(old($Heap), this, _module.LazyInitArray.a)
         || $o == read(old($Heap), this, _module.LazyInitArray.b)
         || $o == read(old($Heap), this, _module.LazyInitArray.c));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.LazyInitArray.Init(_module.LazyInitArray$T: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.LazyInitArray(_module.LazyInitArray$T))
         && $IsAlloc(this, Tclass._module.LazyInitArray(_module.LazyInitArray$T), $Heap),
    N#0: int,
    zero#0: Box
       where $IsBox(zero#0, _module.LazyInitArray$T)
         && $IsAllocBox(zero#0, _module.LazyInitArray$T, $Heap))
   returns ($_reverifyPost: bool);
  free requires 1 == $FunctionContextHeight;
  // user-defined preconditions
  requires LitInt(0) <= N#0;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this);
  ensures _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
     ==> _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
       || read($Heap, this, _module.LazyInitArray.a) != null;
  ensures _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
     ==> _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
       || read($Heap, this, _module.LazyInitArray.b) != null;
  ensures _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
     ==> _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
       || read($Heap, this, _module.LazyInitArray.c) != null;
  ensures _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
     ==> _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
       || _System.array.Length(read($Heap, this, _module.LazyInitArray.a))
         == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents));
  ensures _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
     ==> _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
       || _System.array.Length(read($Heap, this, _module.LazyInitArray.b))
         == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents));
  ensures _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
     ==> _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
       || _System.array.Length(read($Heap, this, _module.LazyInitArray.c))
         == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents));
  ensures _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
     ==> _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
       || read($Heap, this, _module.LazyInitArray.b)
         != read($Heap, this, _module.LazyInitArray.c);
  ensures _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
     ==> _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
       || read($Heap, this, _module.LazyInitArray.a)
         != read($Heap, this, _module.LazyInitArray.b);
  ensures _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
     ==> _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
       || read($Heap, this, _module.LazyInitArray.a)
         != read($Heap, this, _module.LazyInitArray.c);
  ensures _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
     ==> _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
       || LitInt(0) <= read($Heap, this, _module.LazyInitArray.n);
  ensures _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
     ==> _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
       || read($Heap, this, _module.LazyInitArray.n)
         <= _System.array.Length(read($Heap, this, _module.LazyInitArray.c));
  ensures _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
     ==> _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
       || (forall i#6: int ::
        { read($Heap, read($Heap, this, _module.LazyInitArray.a), IndexField(i#6)) }
          { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#6))): int }
          { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#6))): int }
          { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#6))): int }
          { Seq#Index(read($Heap, this, _module.LazyInitArray.Contents), i#6) }
        true
           ==>
          LitInt(0) <= i#6
             && i#6 < Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
           ==> Seq#Index(read($Heap, this, _module.LazyInitArray.Contents), i#6)
             == (if LitInt(0)
                   <= $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#6))): int
                 && $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#6))): int
                   < read($Heap, this, _module.LazyInitArray.n)
                 && $Unbox(read($Heap,
                      read($Heap, this, _module.LazyInitArray.c),
                      IndexField($Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#6))): int))): int
                   == i#6
               then read($Heap, read($Heap, this, _module.LazyInitArray.a), IndexField(i#6))
               else read($Heap, this, _module.LazyInitArray.Zero)));
  ensures _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
     ==> _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
       || (forall i#7: int ::
        { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#7))): int }
          { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#7))): int }
          { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#7))): int }
        true
           ==>
          LitInt(0) <= i#7
             && i#7 < Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
           ==> ((exists j#1: int ::
              { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.c), IndexField(j#1))): int }
              LitInt(0) <= j#1
                 && j#1 < read($Heap, this, _module.LazyInitArray.n)
                 && $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.c), IndexField(j#1))): int
                   == i#7)
             <==> LitInt(0)
                 <= $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#7))): int
               && $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#7))): int
                 < read($Heap, this, _module.LazyInitArray.n)
               && $Unbox(read($Heap,
                    read($Heap, this, _module.LazyInitArray.c),
                    IndexField($Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#7))): int))): int
                 == i#7));
  ensures _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
     ==> _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
       || Seq#Length(read($Heap, this, _module.LazyInitArray.d))
         == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents));
  ensures _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
     ==> _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
       || Seq#Length(read($Heap, this, _module.LazyInitArray.e))
         == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents));
  ensures _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
     ==> _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
       || (forall i#8: int ::
        { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#8)): int }
          { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.c), IndexField(i#8))): int }
        true
           ==>
          LitInt(0) <= i#8 && i#8 < read($Heap, this, _module.LazyInitArray.n)
           ==> $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.c), IndexField(i#8))): int
             == $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#8)): int);
  ensures _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
     ==> _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
       || (forall i#9: int ::
        { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#9)): int }
          { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#9)): int }
        true
           ==> (LitInt(0) <= i#9 && i#9 < Seq#Length(read($Heap, this, _module.LazyInitArray.d))
               ==> LitInt(0)
                 <= $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#9)): int)
             && (LitInt(0) <= i#9 && i#9 < Seq#Length(read($Heap, this, _module.LazyInitArray.d))
               ==> $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#9)): int
                 < Seq#Length(read($Heap, this, _module.LazyInitArray.d))));
  ensures _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
     ==> _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
       || (forall i#10: int ::
        { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#10)): int }
          { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#10)): int }
        true
           ==> (LitInt(0) <= i#10
                 && i#10 < Seq#Length(read($Heap, this, _module.LazyInitArray.e))
               ==> LitInt(0)
                 <= $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#10)): int)
             && (LitInt(0) <= i#10
                 && i#10 < Seq#Length(read($Heap, this, _module.LazyInitArray.e))
               ==> $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#10)): int
                 < Seq#Length(read($Heap, this, _module.LazyInitArray.e))));
  ensures _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
     ==> _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
       || (forall i#11: int ::
        { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#11)): int }
        true
           ==>
          LitInt(0) <= i#11
             && i#11 < Seq#Length(read($Heap, this, _module.LazyInitArray.e))
           ==> $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d),
                $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#11)): int)): int
             == i#11);
  free ensures true;
  ensures Seq#Length(read($Heap, this, _module.LazyInitArray.Contents)) == N#0;
  ensures read($Heap, this, _module.LazyInitArray.Zero) == zero#0;
  free ensures (forall x#1: Box ::
    { Seq#Contains(read($Heap, this, _module.LazyInitArray.Contents), x#1) }
    true);
  ensures (forall x#1: Box ::
    { Seq#Contains(read($Heap, this, _module.LazyInitArray.Contents), x#1) }
    $IsBox(x#1, _module.LazyInitArray$T)
       ==>
      Seq#Contains(read($Heap, this, _module.LazyInitArray.Contents), x#1)
       ==> x#1 == zero#0);
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f)
         ||
        $o == this
         || $o == read(old($Heap), this, _module.LazyInitArray.a)
         || $o == read(old($Heap), this, _module.LazyInitArray.b)
         || $o == read(old($Heap), this, _module.LazyInitArray.c));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.LazyInitArray.Init(_module.LazyInitArray$T: Ty, this: ref, N#0: int, zero#0: Box)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs#0: ref where $Is($rhs#0, Tclass._System.array(_module.LazyInitArray$T));
  var $nw: ref;
  var $rhs#1: ref where $Is($rhs#1, Tclass._System.array(TInt));
  var $rhs#2: ref where $Is($rhs#2, Tclass._System.array(TInt));
  var $rhs#3: int;
  var s#0: Seq Box
     where $Is(s#0, TSeq(_module.LazyInitArray$T))
       && $IsAlloc(s#0, TSeq(_module.LazyInitArray$T), $Heap);
  var id#0: Seq Box where $Is(id#0, TSeq(TInt)) && $IsAlloc(id#0, TSeq(TInt), $Heap);
  var k#0: int;
  var $PreLoopHeap$loop#0: Heap;
  var $decr_init$loop#00: int;
  var $w$loop#0: bool;
  var i#12: int;
  var i#14: int;
  var $decr$loop#00: int;
  var $rhs#4: Seq Box where $Is($rhs#4, TSeq(TInt));
  var $rhs#5: Seq Box where $Is($rhs#5, TSeq(TInt));
  var $rhs#6: Box where $IsBox($rhs#6, _module.LazyInitArray$T);
  var $rhs#7: Seq Box where $Is($rhs#7, TSeq(_module.LazyInitArray$T));

    // AddMethodImpl: Init, Impl$$_module.LazyInitArray.Init
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc)
         ==> $o == this
           || $o == read($Heap, this, _module.LazyInitArray.a)
           || $o == read($Heap, this, _module.LazyInitArray.b)
           || $o == read($Heap, this, _module.LazyInitArray.c));
    assume {:captureState "LazyInitArray.dfy(46,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- LazyInitArray.dfy(47,7)
    assume true;
    assert $_Frame[this, _module.LazyInitArray.a];
    assert 0 <= N#0;
    havoc $nw;
    assume $nw != null
       &&
      !read($Heap, $nw, alloc)
       && dtype($nw) == Tclass._System.array(_module.LazyInitArray$T);
    assume _System.array.Length($nw) == N#0;
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    $rhs#0 := $nw;
    $Heap := update($Heap, this, _module.LazyInitArray.a, $rhs#0);
    assume $IsGoodHeap($Heap);
    assume {:captureState "LazyInitArray.dfy(47,17)"} true;
    // ----- assignment statement ----- LazyInitArray.dfy(48,7)
    assume true;
    assert $_Frame[this, _module.LazyInitArray.b];
    assert 0 <= N#0;
    havoc $nw;
    assume $nw != null
       &&
      !read($Heap, $nw, alloc)
       && dtype($nw) == Tclass._System.array(TInt);
    assume _System.array.Length($nw) == N#0;
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    $rhs#1 := $nw;
    $Heap := update($Heap, this, _module.LazyInitArray.b, $rhs#1);
    assume $IsGoodHeap($Heap);
    assume {:captureState "LazyInitArray.dfy(48,19)"} true;
    // ----- assignment statement ----- LazyInitArray.dfy(49,7)
    assume true;
    assert $_Frame[this, _module.LazyInitArray.c];
    assert 0 <= N#0;
    havoc $nw;
    assume $nw != null
       &&
      !read($Heap, $nw, alloc)
       && dtype($nw) == Tclass._System.array(TInt);
    assume _System.array.Length($nw) == N#0;
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    $rhs#2 := $nw;
    $Heap := update($Heap, this, _module.LazyInitArray.c, $rhs#2);
    assume $IsGoodHeap($Heap);
    assume {:captureState "LazyInitArray.dfy(49,19)"} true;
    // ----- assignment statement ----- LazyInitArray.dfy(50,7)
    assume true;
    assert $_Frame[this, _module.LazyInitArray.n];
    assume true;
    $rhs#3 := LitInt(0);
    $Heap := update($Heap, this, _module.LazyInitArray.n, $rhs#3);
    assume $IsGoodHeap($Heap);
    assume {:captureState "LazyInitArray.dfy(50,10)"} true;
    // ----- assignment statement ----- LazyInitArray.dfy(54,17)
    assume true;
    assume true;
    s#0 := Lit(Seq#Empty(): Seq Box);
    assume {:captureState "LazyInitArray.dfy(54,21)"} true;
    // ----- assignment statement ----- LazyInitArray.dfy(55,18)
    assume true;
    assume true;
    id#0 := Lit(Seq#Empty(): Seq Box);
    assume {:captureState "LazyInitArray.dfy(55,22)"} true;
    // ----- assignment statement ----- LazyInitArray.dfy(56,17)
    assume true;
    assume true;
    k#0 := LitInt(0);
    assume {:captureState "LazyInitArray.dfy(56,20)"} true;
    // ----- while statement ----- LazyInitArray.dfy(57,5)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    $decr_init$loop#00 := N#0 - k#0;
    havoc $w$loop#0;
    while (true)
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0 ==> k#0 <= N#0;
      free invariant $w$loop#0
         ==>
        Seq#Length(s#0) == k#0
         ==> (forall i#13: int :: { Seq#Index(s#0, i#13) } true);
      invariant $w$loop#0 ==> Seq#Length(s#0) == k#0;
      invariant $w$loop#0
         ==> (forall i#13: int ::
          { Seq#Index(s#0, i#13) }
          true
             ==>
            LitInt(0) <= i#13 && i#13 < Seq#Length(s#0)
             ==> Seq#Index(s#0, i#13) == zero#0);
      free invariant $w$loop#0
         ==>
        Seq#Length(id#0) == k#0
         ==> (forall i#15: int :: { $Unbox(Seq#Index(id#0, i#15)): int } true);
      invariant $w$loop#0 ==> Seq#Length(id#0) == k#0;
      invariant $w$loop#0
         ==> (forall i#15: int ::
          { $Unbox(Seq#Index(id#0, i#15)): int }
          true
             ==>
            LitInt(0) <= i#15 && i#15 < k#0
             ==> $Unbox(Seq#Index(id#0, i#15)): int == i#15);
      free invariant (forall<alpha> $o: ref, $f: Field alpha ::
        { read($Heap, $o, $f) }
        $o != null
           ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0, $o, $f)
             ||
            $o == this
             || $o == read(old($Heap), this, _module.LazyInitArray.a)
             || $o == read(old($Heap), this, _module.LazyInitArray.b)
             || $o == read(old($Heap), this, _module.LazyInitArray.c));
      free invariant $HeapSuccGhost($PreLoopHeap$loop#0, $Heap);
      free invariant (forall<alpha> $o: ref, $f: Field alpha ::
        { read($Heap, $o, $f) }
        $o != null && read($PreLoopHeap$loop#0, $o, alloc)
           ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0, $o, $f) || $_Frame[$o, $f]);
      free invariant N#0 - k#0 <= $decr_init$loop#00 && (N#0 - k#0 == $decr_init$loop#00 ==> true);
    {
        assume {:captureState "LazyInitArray.dfy(57,4): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            assume true;
            assume k#0 <= N#0;
            if (Seq#Length(s#0) == k#0)
            {
                havoc i#12;
                // Begin Comprehension WF check
                if (LitInt(0) <= i#12)
                {
                }

                if (LitInt(0) <= i#12 && i#12 < Seq#Length(s#0))
                {
                    assert {:subsumption 0} 0 <= i#12 && i#12 < Seq#Length(s#0);
                }

                // End Comprehension WF check
            }

            assume Seq#Length(s#0) == k#0 ==> (forall i#13: int :: { Seq#Index(s#0, i#13) } true);
            assume Seq#Length(s#0) == k#0
               && (forall i#13: int ::
                { Seq#Index(s#0, i#13) }
                true
                   ==>
                  LitInt(0) <= i#13 && i#13 < Seq#Length(s#0)
                   ==> Seq#Index(s#0, i#13) == zero#0);
            if (Seq#Length(id#0) == k#0)
            {
                havoc i#14;
                // Begin Comprehension WF check
                if (LitInt(0) <= i#14)
                {
                }

                if (LitInt(0) <= i#14 && i#14 < k#0)
                {
                    assert {:subsumption 0} 0 <= i#14 && i#14 < Seq#Length(id#0);
                }

                // End Comprehension WF check
            }

            assume Seq#Length(id#0) == k#0
               ==> (forall i#15: int :: { $Unbox(Seq#Index(id#0, i#15)): int } true);
            assume Seq#Length(id#0) == k#0
               && (forall i#15: int ::
                { $Unbox(Seq#Index(id#0, i#15)): int }
                true
                   ==>
                  LitInt(0) <= i#15 && i#15 < k#0
                   ==> $Unbox(Seq#Index(id#0, i#15)): int == i#15);
            assume true;
            assume false;
        }

        assume true;
        if (N#0 <= k#0)
        {
            break;
        }

        $decr$loop#00 := N#0 - k#0;
        // ----- assignment statement ----- LazyInitArray.dfy(62,9)
        assume true;
        assume true;
        s#0 := Seq#Append(s#0, Seq#Build(Seq#Empty(): Seq Box, zero#0));
        assume {:captureState "LazyInitArray.dfy(62,21)"} true;
        // ----- assignment statement ----- LazyInitArray.dfy(63,10)
        assume true;
        assume true;
        id#0 := Seq#Append(id#0, Seq#Build(Seq#Empty(): Seq Box, $Box(k#0)));
        assume {:captureState "LazyInitArray.dfy(63,20)"} true;
        // ----- assignment statement ----- LazyInitArray.dfy(64,9)
        assume true;
        assume true;
        k#0 := k#0 + 1;
        assume {:captureState "LazyInitArray.dfy(64,16)"} true;
        // ----- loop termination check ----- LazyInitArray.dfy(57,5)
        assert 0 <= $decr$loop#00 || N#0 - k#0 == $decr$loop#00;
        assert N#0 - k#0 < $decr$loop#00;
        assume true;
        assume Seq#Length(s#0) == k#0 ==> (forall i#13: int :: { Seq#Index(s#0, i#13) } true);
        assume Seq#Length(id#0) == k#0
           ==> (forall i#15: int :: { $Unbox(Seq#Index(id#0, i#15)): int } true);
    }

    // ----- assignment statement ----- LazyInitArray.dfy(67,7)
    assume true;
    assert $_Frame[this, _module.LazyInitArray.d];
    assume true;
    $rhs#4 := id#0;
    $Heap := update($Heap, this, _module.LazyInitArray.d, $rhs#4);
    assume $IsGoodHeap($Heap);
    assume {:captureState "LazyInitArray.dfy(67,11)"} true;
    // ----- assignment statement ----- LazyInitArray.dfy(68,7)
    assume true;
    assert $_Frame[this, _module.LazyInitArray.e];
    assume true;
    $rhs#5 := id#0;
    $Heap := update($Heap, this, _module.LazyInitArray.e, $rhs#5);
    assume $IsGoodHeap($Heap);
    assume {:captureState "LazyInitArray.dfy(68,11)"} true;
    // ----- assignment statement ----- LazyInitArray.dfy(69,10)
    assume true;
    assert $_Frame[this, _module.LazyInitArray.Zero];
    assume true;
    $rhs#6 := zero#0;
    $Heap := update($Heap, this, _module.LazyInitArray.Zero, $rhs#6);
    assume $IsGoodHeap($Heap);
    assume {:captureState "LazyInitArray.dfy(69,16)"} true;
    // ----- assignment statement ----- LazyInitArray.dfy(70,14)
    assume true;
    assert $_Frame[this, _module.LazyInitArray.Contents];
    assume true;
    $rhs#7 := s#0;
    $Heap := update($Heap, this, _module.LazyInitArray.Contents, $rhs#7);
    assume $IsGoodHeap($Heap);
    assume {:captureState "LazyInitArray.dfy(70,17)"} true;
}



procedure CheckWellformed$$_module.LazyInitArray.Get(_module.LazyInitArray$T: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.LazyInitArray(_module.LazyInitArray$T))
         && $IsAlloc(this, Tclass._module.LazyInitArray(_module.LazyInitArray$T), $Heap),
    i#0: int)
   returns (x#0: Box
       where $IsBox(x#0, _module.LazyInitArray$T)
         && $IsAllocBox(x#0, _module.LazyInitArray$T, $Heap));
  free requires 2 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.LazyInitArray.Get(_module.LazyInitArray$T: Ty, this: ref, i#0: int) returns (x#0: Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: Get, CheckWellformed$$_module.LazyInitArray.Get
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "LazyInitArray.dfy(73,9): initial state"} true;
    assume _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this);
    assume _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this);
    assume LitInt(0) <= i#0;
    assume i#0 < Seq#Length(read($Heap, this, _module.LazyInitArray.Contents));
    havoc $Heap;
    assume (forall<alpha> $o: ref, $f: Field alpha ::
      { read($Heap, $o, $f) }
      $o != null && read(old($Heap), $o, alloc)
         ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
    assume $HeapSucc(old($Heap), $Heap);
    havoc x#0;
    assume {:captureState "LazyInitArray.dfy(76,14): post-state"} true;
    assert 0 <= i#0 && i#0 < Seq#Length(read($Heap, this, _module.LazyInitArray.Contents));
    assume x#0 == Seq#Index(read($Heap, this, _module.LazyInitArray.Contents), i#0);
}



procedure Call$$_module.LazyInitArray.Get(_module.LazyInitArray$T: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.LazyInitArray(_module.LazyInitArray$T))
         && $IsAlloc(this, Tclass._module.LazyInitArray(_module.LazyInitArray$T), $Heap),
    i#0: int)
   returns (x#0: Box
       where $IsBox(x#0, _module.LazyInitArray$T)
         && $IsAllocBox(x#0, _module.LazyInitArray$T, $Heap));
  // user-defined preconditions
  requires _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
     ==> _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
       || read($Heap, this, _module.LazyInitArray.a) != null;
  requires _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
     ==> _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
       || read($Heap, this, _module.LazyInitArray.b) != null;
  requires _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
     ==> _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
       || read($Heap, this, _module.LazyInitArray.c) != null;
  requires _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
     ==> _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
       || _System.array.Length(read($Heap, this, _module.LazyInitArray.a))
         == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents));
  requires _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
     ==> _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
       || _System.array.Length(read($Heap, this, _module.LazyInitArray.b))
         == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents));
  requires _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
     ==> _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
       || _System.array.Length(read($Heap, this, _module.LazyInitArray.c))
         == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents));
  requires _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
     ==> _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
       || read($Heap, this, _module.LazyInitArray.b)
         != read($Heap, this, _module.LazyInitArray.c);
  requires _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
     ==> _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
       || read($Heap, this, _module.LazyInitArray.a)
         != read($Heap, this, _module.LazyInitArray.b);
  requires _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
     ==> _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
       || read($Heap, this, _module.LazyInitArray.a)
         != read($Heap, this, _module.LazyInitArray.c);
  requires _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
     ==> _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
       || LitInt(0) <= read($Heap, this, _module.LazyInitArray.n);
  requires _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
     ==> _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
       || read($Heap, this, _module.LazyInitArray.n)
         <= _System.array.Length(read($Heap, this, _module.LazyInitArray.c));
  requires _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
     ==> _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
       || (forall i#1: int ::
        { read($Heap, read($Heap, this, _module.LazyInitArray.a), IndexField(i#1)) }
          { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#1))): int }
          { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#1))): int }
          { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#1))): int }
          { Seq#Index(read($Heap, this, _module.LazyInitArray.Contents), i#1) }
        true
           ==>
          LitInt(0) <= i#1
             && i#1 < Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
           ==> Seq#Index(read($Heap, this, _module.LazyInitArray.Contents), i#1)
             == (if LitInt(0)
                   <= $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#1))): int
                 && $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#1))): int
                   < read($Heap, this, _module.LazyInitArray.n)
                 && $Unbox(read($Heap,
                      read($Heap, this, _module.LazyInitArray.c),
                      IndexField($Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#1))): int))): int
                   == i#1
               then read($Heap, read($Heap, this, _module.LazyInitArray.a), IndexField(i#1))
               else read($Heap, this, _module.LazyInitArray.Zero)));
  requires _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
     ==> _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
       || (forall i#2: int ::
        { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#2))): int }
          { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#2))): int }
          { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#2))): int }
        true
           ==>
          LitInt(0) <= i#2
             && i#2 < Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
           ==> ((exists j#0: int ::
              { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.c), IndexField(j#0))): int }
              LitInt(0) <= j#0
                 && j#0 < read($Heap, this, _module.LazyInitArray.n)
                 && $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.c), IndexField(j#0))): int
                   == i#2)
             <==> LitInt(0)
                 <= $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#2))): int
               && $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#2))): int
                 < read($Heap, this, _module.LazyInitArray.n)
               && $Unbox(read($Heap,
                    read($Heap, this, _module.LazyInitArray.c),
                    IndexField($Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#2))): int))): int
                 == i#2));
  requires _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
     ==> _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
       || Seq#Length(read($Heap, this, _module.LazyInitArray.d))
         == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents));
  requires _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
     ==> _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
       || Seq#Length(read($Heap, this, _module.LazyInitArray.e))
         == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents));
  requires _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
     ==> _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
       || (forall i#3: int ::
        { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#3)): int }
          { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.c), IndexField(i#3))): int }
        true
           ==>
          LitInt(0) <= i#3 && i#3 < read($Heap, this, _module.LazyInitArray.n)
           ==> $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.c), IndexField(i#3))): int
             == $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#3)): int);
  requires _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
     ==> _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
       || (forall i#4: int ::
        { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#4)): int }
          { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#4)): int }
        true
           ==> (LitInt(0) <= i#4 && i#4 < Seq#Length(read($Heap, this, _module.LazyInitArray.d))
               ==> LitInt(0)
                 <= $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#4)): int)
             && (LitInt(0) <= i#4 && i#4 < Seq#Length(read($Heap, this, _module.LazyInitArray.d))
               ==> $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#4)): int
                 < Seq#Length(read($Heap, this, _module.LazyInitArray.d))));
  requires _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
     ==> _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
       || (forall i#5: int ::
        { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#5)): int }
          { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#5)): int }
        true
           ==> (LitInt(0) <= i#5 && i#5 < Seq#Length(read($Heap, this, _module.LazyInitArray.e))
               ==> LitInt(0)
                 <= $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#5)): int)
             && (LitInt(0) <= i#5 && i#5 < Seq#Length(read($Heap, this, _module.LazyInitArray.e))
               ==> $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#5)): int
                 < Seq#Length(read($Heap, this, _module.LazyInitArray.e))));
  requires _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
     ==> _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
       || (forall i#6: int ::
        { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#6)): int }
        true
           ==>
          LitInt(0) <= i#6 && i#6 < Seq#Length(read($Heap, this, _module.LazyInitArray.e))
           ==> $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d),
                $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#6)): int)): int
             == i#6);
  requires LitInt(0) <= i#0;
  requires i#0 < Seq#Length(read($Heap, this, _module.LazyInitArray.Contents));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures x#0 == Seq#Index(read($Heap, this, _module.LazyInitArray.Contents), i#0);
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.LazyInitArray.Get(_module.LazyInitArray$T: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.LazyInitArray(_module.LazyInitArray$T))
         && $IsAlloc(this, Tclass._module.LazyInitArray(_module.LazyInitArray$T), $Heap),
    i#0: int)
   returns (x#0: Box
       where $IsBox(x#0, _module.LazyInitArray$T)
         && $IsAllocBox(x#0, _module.LazyInitArray$T, $Heap),
    $_reverifyPost: bool);
  free requires 2 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
     &&
    _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
     &&
    read($Heap, this, _module.LazyInitArray.a) != null
     && read($Heap, this, _module.LazyInitArray.b) != null
     && read($Heap, this, _module.LazyInitArray.c) != null
     && _System.array.Length(read($Heap, this, _module.LazyInitArray.a))
       == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
     && _System.array.Length(read($Heap, this, _module.LazyInitArray.b))
       == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
     && _System.array.Length(read($Heap, this, _module.LazyInitArray.c))
       == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
     && read($Heap, this, _module.LazyInitArray.b)
       != read($Heap, this, _module.LazyInitArray.c)
     && read($Heap, this, _module.LazyInitArray.a)
       != read($Heap, this, _module.LazyInitArray.b)
     && read($Heap, this, _module.LazyInitArray.a)
       != read($Heap, this, _module.LazyInitArray.c)
     && LitInt(0) <= read($Heap, this, _module.LazyInitArray.n)
     && read($Heap, this, _module.LazyInitArray.n)
       <= _System.array.Length(read($Heap, this, _module.LazyInitArray.c))
     && (forall i#7: int ::
      { read($Heap, read($Heap, this, _module.LazyInitArray.a), IndexField(i#7)) }
        { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#7))): int }
        { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#7))): int }
        { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#7))): int }
        { Seq#Index(read($Heap, this, _module.LazyInitArray.Contents), i#7) }
      true
         ==>
        LitInt(0) <= i#7
           && i#7 < Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
         ==> Seq#Index(read($Heap, this, _module.LazyInitArray.Contents), i#7)
           == (if LitInt(0)
                 <= $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#7))): int
               && $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#7))): int
                 < read($Heap, this, _module.LazyInitArray.n)
               && $Unbox(read($Heap,
                    read($Heap, this, _module.LazyInitArray.c),
                    IndexField($Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#7))): int))): int
                 == i#7
             then read($Heap, read($Heap, this, _module.LazyInitArray.a), IndexField(i#7))
             else read($Heap, this, _module.LazyInitArray.Zero)))
     && (forall i#8: int ::
      { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#8))): int }
        { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#8))): int }
        { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#8))): int }
      true
         ==>
        LitInt(0) <= i#8
           && i#8 < Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
         ==> ((exists j#1: int ::
            { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.c), IndexField(j#1))): int }
            LitInt(0) <= j#1
               && j#1 < read($Heap, this, _module.LazyInitArray.n)
               && $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.c), IndexField(j#1))): int
                 == i#8)
           <==> LitInt(0)
               <= $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#8))): int
             && $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#8))): int
               < read($Heap, this, _module.LazyInitArray.n)
             && $Unbox(read($Heap,
                  read($Heap, this, _module.LazyInitArray.c),
                  IndexField($Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#8))): int))): int
               == i#8))
     && Seq#Length(read($Heap, this, _module.LazyInitArray.d))
       == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
     && Seq#Length(read($Heap, this, _module.LazyInitArray.e))
       == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
     && (forall i#9: int ::
      { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#9)): int }
        { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.c), IndexField(i#9))): int }
      true
         ==>
        LitInt(0) <= i#9 && i#9 < read($Heap, this, _module.LazyInitArray.n)
         ==> $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.c), IndexField(i#9))): int
           == $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#9)): int)
     && (forall i#10: int ::
      { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#10)): int }
        { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#10)): int }
      true
         ==> (LitInt(0) <= i#10
               && i#10 < Seq#Length(read($Heap, this, _module.LazyInitArray.d))
             ==> LitInt(0)
               <= $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#10)): int)
           && (LitInt(0) <= i#10
               && i#10 < Seq#Length(read($Heap, this, _module.LazyInitArray.d))
             ==> $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#10)): int
               < Seq#Length(read($Heap, this, _module.LazyInitArray.d))))
     && (forall i#11: int ::
      { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#11)): int }
        { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#11)): int }
      true
         ==> (LitInt(0) <= i#11
               && i#11 < Seq#Length(read($Heap, this, _module.LazyInitArray.e))
             ==> LitInt(0)
               <= $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#11)): int)
           && (LitInt(0) <= i#11
               && i#11 < Seq#Length(read($Heap, this, _module.LazyInitArray.e))
             ==> $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#11)): int
               < Seq#Length(read($Heap, this, _module.LazyInitArray.e))))
     && (forall i#12: int ::
      { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#12)): int }
      true
         ==>
        LitInt(0) <= i#12
           && i#12 < Seq#Length(read($Heap, this, _module.LazyInitArray.e))
         ==> $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d),
              $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#12)): int)): int
           == i#12);
  requires LitInt(0) <= i#0;
  requires i#0 < Seq#Length(read($Heap, this, _module.LazyInitArray.Contents));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures x#0 == Seq#Index(read($Heap, this, _module.LazyInitArray.Contents), i#0);
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.LazyInitArray.Get(_module.LazyInitArray$T: Ty, this: ref, i#0: int)
   returns (x#0: Box, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: Get, Impl$$_module.LazyInitArray.Get
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "LazyInitArray.dfy(77,2): initial state"} true;
    $_reverifyPost := false;
    // ----- if statement ----- LazyInitArray.dfy(78,5)
    assert read($Heap, this, _module.LazyInitArray.b) != null;
    assert 0 <= i#0
       && i#0 < _System.array.Length(read($Heap, this, _module.LazyInitArray.b));
    if (LitInt(0)
       <= $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#0))): int)
    {
        assert read($Heap, this, _module.LazyInitArray.b) != null;
        assert 0 <= i#0
           && i#0 < _System.array.Length(read($Heap, this, _module.LazyInitArray.b));
    }

    if (LitInt(0)
         <= $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#0))): int
       && $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#0))): int
         < read($Heap, this, _module.LazyInitArray.n))
    {
        assert read($Heap, this, _module.LazyInitArray.c) != null;
        assert read($Heap, this, _module.LazyInitArray.b) != null;
        assert 0 <= i#0
           && i#0 < _System.array.Length(read($Heap, this, _module.LazyInitArray.b));
        assert 0
             <= $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#0))): int
           && $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#0))): int
             < _System.array.Length(read($Heap, this, _module.LazyInitArray.c));
    }

    assume true;
    if (LitInt(0)
         <= $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#0))): int
       && $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#0))): int
         < read($Heap, this, _module.LazyInitArray.n)
       && $Unbox(read($Heap,
            read($Heap, this, _module.LazyInitArray.c),
            IndexField($Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#0))): int))): int
         == i#0)
    {
        // ----- assignment statement ----- LazyInitArray.dfy(79,9)
        assume true;
        assert read($Heap, this, _module.LazyInitArray.a) != null;
        assert 0 <= i#0
           && i#0 < _System.array.Length(read($Heap, this, _module.LazyInitArray.a));
        assume true;
        x#0 := read($Heap, read($Heap, this, _module.LazyInitArray.a), IndexField(i#0));
        assume {:captureState "LazyInitArray.dfy(79,15)"} true;
    }
    else
    {
        // ----- assignment statement ----- LazyInitArray.dfy(81,9)
        assume true;
        assume true;
        x#0 := read($Heap, this, _module.LazyInitArray.Zero);
        assume {:captureState "LazyInitArray.dfy(81,15)"} true;
    }
}



procedure CheckWellformed$$_module.LazyInitArray.Set(_module.LazyInitArray$T: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.LazyInitArray(_module.LazyInitArray$T))
         && $IsAlloc(this, Tclass._module.LazyInitArray(_module.LazyInitArray$T), $Heap),
    i#0: int,
    x#0: Box
       where $IsBox(x#0, _module.LazyInitArray$T)
         && $IsAllocBox(x#0, _module.LazyInitArray$T, $Heap));
  free requires 3 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.LazyInitArray.Set(_module.LazyInitArray$T: Ty, this: ref, i#0: int, x#0: Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: Set, CheckWellformed$$_module.LazyInitArray.Set
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc)
         ==> $o == this
           || $o == read($Heap, this, _module.LazyInitArray.a)
           || $o == read($Heap, this, _module.LazyInitArray.b)
           || $o == read($Heap, this, _module.LazyInitArray.c));
    assume {:captureState "LazyInitArray.dfy(85,9): initial state"} true;
    assume _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this);
    assume _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this);
    assume LitInt(0) <= i#0;
    assume i#0 < Seq#Length(read($Heap, this, _module.LazyInitArray.Contents));
    havoc $Heap;
    assume (forall<alpha> $o: ref, $f: Field alpha ::
      { read($Heap, $o, $f) }
      $o != null && read(old($Heap), $o, alloc)
         ==> read($Heap, $o, $f) == read(old($Heap), $o, $f)
           ||
          $o == this
           || $o == read(old($Heap), this, _module.LazyInitArray.a)
           || $o == read(old($Heap), this, _module.LazyInitArray.b)
           || $o == read(old($Heap), this, _module.LazyInitArray.c));
    assume $HeapSucc(old($Heap), $Heap);
    assume {:captureState "LazyInitArray.dfy(89,17): post-state"} true;
    assume _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this);
    assume _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this);
    assert $IsAlloc(this, Tclass._module.LazyInitArray(_module.LazyInitArray$T), old($Heap));
    assume Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
       == Seq#Length(read(old($Heap), this, _module.LazyInitArray.Contents));
    assert 0 <= i#0 && i#0 < Seq#Length(read($Heap, this, _module.LazyInitArray.Contents));
    assume Seq#Equal(read($Heap, this, _module.LazyInitArray.Contents),
      Seq#Update(read($Heap, this, _module.LazyInitArray.Contents), i#0, x#0));
    assert $IsAlloc(this, Tclass._module.LazyInitArray(_module.LazyInitArray$T), old($Heap));
    assume read($Heap, this, _module.LazyInitArray.Zero)
       == read(old($Heap), this, _module.LazyInitArray.Zero);
}



procedure Call$$_module.LazyInitArray.Set(_module.LazyInitArray$T: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.LazyInitArray(_module.LazyInitArray$T))
         && $IsAlloc(this, Tclass._module.LazyInitArray(_module.LazyInitArray$T), $Heap),
    i#0: int,
    x#0: Box
       where $IsBox(x#0, _module.LazyInitArray$T)
         && $IsAllocBox(x#0, _module.LazyInitArray$T, $Heap));
  // user-defined preconditions
  requires _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
     ==> _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
       || read($Heap, this, _module.LazyInitArray.a) != null;
  requires _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
     ==> _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
       || read($Heap, this, _module.LazyInitArray.b) != null;
  requires _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
     ==> _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
       || read($Heap, this, _module.LazyInitArray.c) != null;
  requires _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
     ==> _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
       || _System.array.Length(read($Heap, this, _module.LazyInitArray.a))
         == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents));
  requires _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
     ==> _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
       || _System.array.Length(read($Heap, this, _module.LazyInitArray.b))
         == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents));
  requires _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
     ==> _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
       || _System.array.Length(read($Heap, this, _module.LazyInitArray.c))
         == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents));
  requires _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
     ==> _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
       || read($Heap, this, _module.LazyInitArray.b)
         != read($Heap, this, _module.LazyInitArray.c);
  requires _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
     ==> _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
       || read($Heap, this, _module.LazyInitArray.a)
         != read($Heap, this, _module.LazyInitArray.b);
  requires _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
     ==> _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
       || read($Heap, this, _module.LazyInitArray.a)
         != read($Heap, this, _module.LazyInitArray.c);
  requires _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
     ==> _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
       || LitInt(0) <= read($Heap, this, _module.LazyInitArray.n);
  requires _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
     ==> _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
       || read($Heap, this, _module.LazyInitArray.n)
         <= _System.array.Length(read($Heap, this, _module.LazyInitArray.c));
  requires _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
     ==> _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
       || (forall i#1: int ::
        { read($Heap, read($Heap, this, _module.LazyInitArray.a), IndexField(i#1)) }
          { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#1))): int }
          { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#1))): int }
          { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#1))): int }
          { Seq#Index(read($Heap, this, _module.LazyInitArray.Contents), i#1) }
        true
           ==>
          LitInt(0) <= i#1
             && i#1 < Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
           ==> Seq#Index(read($Heap, this, _module.LazyInitArray.Contents), i#1)
             == (if LitInt(0)
                   <= $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#1))): int
                 && $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#1))): int
                   < read($Heap, this, _module.LazyInitArray.n)
                 && $Unbox(read($Heap,
                      read($Heap, this, _module.LazyInitArray.c),
                      IndexField($Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#1))): int))): int
                   == i#1
               then read($Heap, read($Heap, this, _module.LazyInitArray.a), IndexField(i#1))
               else read($Heap, this, _module.LazyInitArray.Zero)));
  requires _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
     ==> _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
       || (forall i#2: int ::
        { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#2))): int }
          { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#2))): int }
          { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#2))): int }
        true
           ==>
          LitInt(0) <= i#2
             && i#2 < Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
           ==> ((exists j#0: int ::
              { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.c), IndexField(j#0))): int }
              LitInt(0) <= j#0
                 && j#0 < read($Heap, this, _module.LazyInitArray.n)
                 && $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.c), IndexField(j#0))): int
                   == i#2)
             <==> LitInt(0)
                 <= $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#2))): int
               && $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#2))): int
                 < read($Heap, this, _module.LazyInitArray.n)
               && $Unbox(read($Heap,
                    read($Heap, this, _module.LazyInitArray.c),
                    IndexField($Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#2))): int))): int
                 == i#2));
  requires _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
     ==> _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
       || Seq#Length(read($Heap, this, _module.LazyInitArray.d))
         == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents));
  requires _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
     ==> _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
       || Seq#Length(read($Heap, this, _module.LazyInitArray.e))
         == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents));
  requires _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
     ==> _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
       || (forall i#3: int ::
        { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#3)): int }
          { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.c), IndexField(i#3))): int }
        true
           ==>
          LitInt(0) <= i#3 && i#3 < read($Heap, this, _module.LazyInitArray.n)
           ==> $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.c), IndexField(i#3))): int
             == $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#3)): int);
  requires _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
     ==> _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
       || (forall i#4: int ::
        { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#4)): int }
          { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#4)): int }
        true
           ==> (LitInt(0) <= i#4 && i#4 < Seq#Length(read($Heap, this, _module.LazyInitArray.d))
               ==> LitInt(0)
                 <= $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#4)): int)
             && (LitInt(0) <= i#4 && i#4 < Seq#Length(read($Heap, this, _module.LazyInitArray.d))
               ==> $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#4)): int
                 < Seq#Length(read($Heap, this, _module.LazyInitArray.d))));
  requires _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
     ==> _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
       || (forall i#5: int ::
        { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#5)): int }
          { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#5)): int }
        true
           ==> (LitInt(0) <= i#5 && i#5 < Seq#Length(read($Heap, this, _module.LazyInitArray.e))
               ==> LitInt(0)
                 <= $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#5)): int)
             && (LitInt(0) <= i#5 && i#5 < Seq#Length(read($Heap, this, _module.LazyInitArray.e))
               ==> $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#5)): int
                 < Seq#Length(read($Heap, this, _module.LazyInitArray.e))));
  requires _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
     ==> _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
       || (forall i#6: int ::
        { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#6)): int }
        true
           ==>
          LitInt(0) <= i#6 && i#6 < Seq#Length(read($Heap, this, _module.LazyInitArray.e))
           ==> $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d),
                $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#6)): int)): int
             == i#6);
  requires LitInt(0) <= i#0;
  requires i#0 < Seq#Length(read($Heap, this, _module.LazyInitArray.Contents));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this);
  free ensures _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
     &&
    _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
     &&
    read($Heap, this, _module.LazyInitArray.a) != null
     && read($Heap, this, _module.LazyInitArray.b) != null
     && read($Heap, this, _module.LazyInitArray.c) != null
     && _System.array.Length(read($Heap, this, _module.LazyInitArray.a))
       == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
     && _System.array.Length(read($Heap, this, _module.LazyInitArray.b))
       == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
     && _System.array.Length(read($Heap, this, _module.LazyInitArray.c))
       == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
     && read($Heap, this, _module.LazyInitArray.b)
       != read($Heap, this, _module.LazyInitArray.c)
     && read($Heap, this, _module.LazyInitArray.a)
       != read($Heap, this, _module.LazyInitArray.b)
     && read($Heap, this, _module.LazyInitArray.a)
       != read($Heap, this, _module.LazyInitArray.c)
     && LitInt(0) <= read($Heap, this, _module.LazyInitArray.n)
     && read($Heap, this, _module.LazyInitArray.n)
       <= _System.array.Length(read($Heap, this, _module.LazyInitArray.c))
     && (forall i#7: int ::
      { read($Heap, read($Heap, this, _module.LazyInitArray.a), IndexField(i#7)) }
        { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#7))): int }
        { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#7))): int }
        { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#7))): int }
        { Seq#Index(read($Heap, this, _module.LazyInitArray.Contents), i#7) }
      true
         ==>
        LitInt(0) <= i#7
           && i#7 < Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
         ==> Seq#Index(read($Heap, this, _module.LazyInitArray.Contents), i#7)
           == (if LitInt(0)
                 <= $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#7))): int
               && $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#7))): int
                 < read($Heap, this, _module.LazyInitArray.n)
               && $Unbox(read($Heap,
                    read($Heap, this, _module.LazyInitArray.c),
                    IndexField($Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#7))): int))): int
                 == i#7
             then read($Heap, read($Heap, this, _module.LazyInitArray.a), IndexField(i#7))
             else read($Heap, this, _module.LazyInitArray.Zero)))
     && (forall i#8: int ::
      { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#8))): int }
        { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#8))): int }
        { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#8))): int }
      true
         ==>
        LitInt(0) <= i#8
           && i#8 < Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
         ==> ((exists j#1: int ::
            { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.c), IndexField(j#1))): int }
            LitInt(0) <= j#1
               && j#1 < read($Heap, this, _module.LazyInitArray.n)
               && $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.c), IndexField(j#1))): int
                 == i#8)
           <==> LitInt(0)
               <= $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#8))): int
             && $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#8))): int
               < read($Heap, this, _module.LazyInitArray.n)
             && $Unbox(read($Heap,
                  read($Heap, this, _module.LazyInitArray.c),
                  IndexField($Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#8))): int))): int
               == i#8))
     && Seq#Length(read($Heap, this, _module.LazyInitArray.d))
       == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
     && Seq#Length(read($Heap, this, _module.LazyInitArray.e))
       == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
     && (forall i#9: int ::
      { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#9)): int }
        { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.c), IndexField(i#9))): int }
      true
         ==>
        LitInt(0) <= i#9 && i#9 < read($Heap, this, _module.LazyInitArray.n)
         ==> $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.c), IndexField(i#9))): int
           == $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#9)): int)
     && (forall i#10: int ::
      { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#10)): int }
        { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#10)): int }
      true
         ==> (LitInt(0) <= i#10
               && i#10 < Seq#Length(read($Heap, this, _module.LazyInitArray.d))
             ==> LitInt(0)
               <= $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#10)): int)
           && (LitInt(0) <= i#10
               && i#10 < Seq#Length(read($Heap, this, _module.LazyInitArray.d))
             ==> $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#10)): int
               < Seq#Length(read($Heap, this, _module.LazyInitArray.d))))
     && (forall i#11: int ::
      { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#11)): int }
        { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#11)): int }
      true
         ==> (LitInt(0) <= i#11
               && i#11 < Seq#Length(read($Heap, this, _module.LazyInitArray.e))
             ==> LitInt(0)
               <= $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#11)): int)
           && (LitInt(0) <= i#11
               && i#11 < Seq#Length(read($Heap, this, _module.LazyInitArray.e))
             ==> $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#11)): int
               < Seq#Length(read($Heap, this, _module.LazyInitArray.e))))
     && (forall i#12: int ::
      { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#12)): int }
      true
         ==>
        LitInt(0) <= i#12
           && i#12 < Seq#Length(read($Heap, this, _module.LazyInitArray.e))
         ==> $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d),
              $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#12)): int)): int
           == i#12);
  free ensures true;
  ensures Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
     == Seq#Length(read(old($Heap), this, _module.LazyInitArray.Contents));
  ensures Seq#Equal(read($Heap, this, _module.LazyInitArray.Contents),
    Seq#Update(read($Heap, this, _module.LazyInitArray.Contents), i#0, x#0));
  free ensures true;
  ensures read($Heap, this, _module.LazyInitArray.Zero)
     == read(old($Heap), this, _module.LazyInitArray.Zero);
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f)
         ||
        $o == this
         || $o == read(old($Heap), this, _module.LazyInitArray.a)
         || $o == read(old($Heap), this, _module.LazyInitArray.b)
         || $o == read(old($Heap), this, _module.LazyInitArray.c));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.LazyInitArray.Set(_module.LazyInitArray$T: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.LazyInitArray(_module.LazyInitArray$T))
         && $IsAlloc(this, Tclass._module.LazyInitArray(_module.LazyInitArray$T), $Heap),
    i#0: int,
    x#0: Box
       where $IsBox(x#0, _module.LazyInitArray$T)
         && $IsAllocBox(x#0, _module.LazyInitArray$T, $Heap))
   returns ($_reverifyPost: bool);
  free requires 3 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
     &&
    _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
     &&
    read($Heap, this, _module.LazyInitArray.a) != null
     && read($Heap, this, _module.LazyInitArray.b) != null
     && read($Heap, this, _module.LazyInitArray.c) != null
     && _System.array.Length(read($Heap, this, _module.LazyInitArray.a))
       == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
     && _System.array.Length(read($Heap, this, _module.LazyInitArray.b))
       == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
     && _System.array.Length(read($Heap, this, _module.LazyInitArray.c))
       == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
     && read($Heap, this, _module.LazyInitArray.b)
       != read($Heap, this, _module.LazyInitArray.c)
     && read($Heap, this, _module.LazyInitArray.a)
       != read($Heap, this, _module.LazyInitArray.b)
     && read($Heap, this, _module.LazyInitArray.a)
       != read($Heap, this, _module.LazyInitArray.c)
     && LitInt(0) <= read($Heap, this, _module.LazyInitArray.n)
     && read($Heap, this, _module.LazyInitArray.n)
       <= _System.array.Length(read($Heap, this, _module.LazyInitArray.c))
     && (forall i#13: int ::
      { read($Heap, read($Heap, this, _module.LazyInitArray.a), IndexField(i#13)) }
        { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#13))): int }
        { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#13))): int }
        { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#13))): int }
        { Seq#Index(read($Heap, this, _module.LazyInitArray.Contents), i#13) }
      true
         ==>
        LitInt(0) <= i#13
           && i#13 < Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
         ==> Seq#Index(read($Heap, this, _module.LazyInitArray.Contents), i#13)
           == (if LitInt(0)
                 <= $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#13))): int
               && $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#13))): int
                 < read($Heap, this, _module.LazyInitArray.n)
               && $Unbox(read($Heap,
                    read($Heap, this, _module.LazyInitArray.c),
                    IndexField($Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#13))): int))): int
                 == i#13
             then read($Heap, read($Heap, this, _module.LazyInitArray.a), IndexField(i#13))
             else read($Heap, this, _module.LazyInitArray.Zero)))
     && (forall i#14: int ::
      { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#14))): int }
        { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#14))): int }
        { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#14))): int }
      true
         ==>
        LitInt(0) <= i#14
           && i#14 < Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
         ==> ((exists j#2: int ::
            { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.c), IndexField(j#2))): int }
            LitInt(0) <= j#2
               && j#2 < read($Heap, this, _module.LazyInitArray.n)
               && $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.c), IndexField(j#2))): int
                 == i#14)
           <==> LitInt(0)
               <= $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#14))): int
             && $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#14))): int
               < read($Heap, this, _module.LazyInitArray.n)
             && $Unbox(read($Heap,
                  read($Heap, this, _module.LazyInitArray.c),
                  IndexField($Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#14))): int))): int
               == i#14))
     && Seq#Length(read($Heap, this, _module.LazyInitArray.d))
       == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
     && Seq#Length(read($Heap, this, _module.LazyInitArray.e))
       == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
     && (forall i#15: int ::
      { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#15)): int }
        { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.c), IndexField(i#15))): int }
      true
         ==>
        LitInt(0) <= i#15 && i#15 < read($Heap, this, _module.LazyInitArray.n)
         ==> $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.c), IndexField(i#15))): int
           == $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#15)): int)
     && (forall i#16: int ::
      { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#16)): int }
        { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#16)): int }
      true
         ==> (LitInt(0) <= i#16
               && i#16 < Seq#Length(read($Heap, this, _module.LazyInitArray.d))
             ==> LitInt(0)
               <= $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#16)): int)
           && (LitInt(0) <= i#16
               && i#16 < Seq#Length(read($Heap, this, _module.LazyInitArray.d))
             ==> $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#16)): int
               < Seq#Length(read($Heap, this, _module.LazyInitArray.d))))
     && (forall i#17: int ::
      { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#17)): int }
        { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#17)): int }
      true
         ==> (LitInt(0) <= i#17
               && i#17 < Seq#Length(read($Heap, this, _module.LazyInitArray.e))
             ==> LitInt(0)
               <= $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#17)): int)
           && (LitInt(0) <= i#17
               && i#17 < Seq#Length(read($Heap, this, _module.LazyInitArray.e))
             ==> $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#17)): int
               < Seq#Length(read($Heap, this, _module.LazyInitArray.e))))
     && (forall i#18: int ::
      { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#18)): int }
      true
         ==>
        LitInt(0) <= i#18
           && i#18 < Seq#Length(read($Heap, this, _module.LazyInitArray.e))
         ==> $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d),
              $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#18)): int)): int
           == i#18);
  requires LitInt(0) <= i#0;
  requires i#0 < Seq#Length(read($Heap, this, _module.LazyInitArray.Contents));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this);
  ensures _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
     ==> _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
       || read($Heap, this, _module.LazyInitArray.a) != null;
  ensures _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
     ==> _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
       || read($Heap, this, _module.LazyInitArray.b) != null;
  ensures _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
     ==> _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
       || read($Heap, this, _module.LazyInitArray.c) != null;
  ensures _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
     ==> _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
       || _System.array.Length(read($Heap, this, _module.LazyInitArray.a))
         == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents));
  ensures _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
     ==> _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
       || _System.array.Length(read($Heap, this, _module.LazyInitArray.b))
         == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents));
  ensures _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
     ==> _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
       || _System.array.Length(read($Heap, this, _module.LazyInitArray.c))
         == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents));
  ensures _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
     ==> _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
       || read($Heap, this, _module.LazyInitArray.b)
         != read($Heap, this, _module.LazyInitArray.c);
  ensures _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
     ==> _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
       || read($Heap, this, _module.LazyInitArray.a)
         != read($Heap, this, _module.LazyInitArray.b);
  ensures _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
     ==> _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
       || read($Heap, this, _module.LazyInitArray.a)
         != read($Heap, this, _module.LazyInitArray.c);
  ensures _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
     ==> _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
       || LitInt(0) <= read($Heap, this, _module.LazyInitArray.n);
  ensures _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
     ==> _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
       || read($Heap, this, _module.LazyInitArray.n)
         <= _System.array.Length(read($Heap, this, _module.LazyInitArray.c));
  ensures _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
     ==> _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
       || (forall i#19: int ::
        { read($Heap, read($Heap, this, _module.LazyInitArray.a), IndexField(i#19)) }
          { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#19))): int }
          { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#19))): int }
          { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#19))): int }
          { Seq#Index(read($Heap, this, _module.LazyInitArray.Contents), i#19) }
        true
           ==>
          LitInt(0) <= i#19
             && i#19 < Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
           ==> Seq#Index(read($Heap, this, _module.LazyInitArray.Contents), i#19)
             == (if LitInt(0)
                   <= $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#19))): int
                 && $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#19))): int
                   < read($Heap, this, _module.LazyInitArray.n)
                 && $Unbox(read($Heap,
                      read($Heap, this, _module.LazyInitArray.c),
                      IndexField($Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#19))): int))): int
                   == i#19
               then read($Heap, read($Heap, this, _module.LazyInitArray.a), IndexField(i#19))
               else read($Heap, this, _module.LazyInitArray.Zero)));
  ensures _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
     ==> _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
       || (forall i#20: int ::
        { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#20))): int }
          { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#20))): int }
          { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#20))): int }
        true
           ==>
          LitInt(0) <= i#20
             && i#20 < Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
           ==> ((exists j#3: int ::
              { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.c), IndexField(j#3))): int }
              LitInt(0) <= j#3
                 && j#3 < read($Heap, this, _module.LazyInitArray.n)
                 && $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.c), IndexField(j#3))): int
                   == i#20)
             <==> LitInt(0)
                 <= $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#20))): int
               && $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#20))): int
                 < read($Heap, this, _module.LazyInitArray.n)
               && $Unbox(read($Heap,
                    read($Heap, this, _module.LazyInitArray.c),
                    IndexField($Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#20))): int))): int
                 == i#20));
  ensures _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
     ==> _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
       || Seq#Length(read($Heap, this, _module.LazyInitArray.d))
         == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents));
  ensures _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
     ==> _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
       || Seq#Length(read($Heap, this, _module.LazyInitArray.e))
         == Seq#Length(read($Heap, this, _module.LazyInitArray.Contents));
  ensures _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
     ==> _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
       || (forall i#21: int ::
        { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#21)): int }
          { $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.c), IndexField(i#21))): int }
        true
           ==>
          LitInt(0) <= i#21 && i#21 < read($Heap, this, _module.LazyInitArray.n)
           ==> $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.c), IndexField(i#21))): int
             == $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#21)): int);
  ensures _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
     ==> _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
       || (forall i#22: int ::
        { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#22)): int }
          { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#22)): int }
        true
           ==> (LitInt(0) <= i#22
                 && i#22 < Seq#Length(read($Heap, this, _module.LazyInitArray.d))
               ==> LitInt(0)
                 <= $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#22)): int)
             && (LitInt(0) <= i#22
                 && i#22 < Seq#Length(read($Heap, this, _module.LazyInitArray.d))
               ==> $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d), i#22)): int
                 < Seq#Length(read($Heap, this, _module.LazyInitArray.d))));
  ensures _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
     ==> _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
       || (forall i#23: int ::
        { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#23)): int }
          { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#23)): int }
        true
           ==> (LitInt(0) <= i#23
                 && i#23 < Seq#Length(read($Heap, this, _module.LazyInitArray.e))
               ==> LitInt(0)
                 <= $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#23)): int)
             && (LitInt(0) <= i#23
                 && i#23 < Seq#Length(read($Heap, this, _module.LazyInitArray.e))
               ==> $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#23)): int
                 < Seq#Length(read($Heap, this, _module.LazyInitArray.e))));
  ensures _module.LazyInitArray.Valid#canCall(_module.LazyInitArray$T, $Heap, this)
     ==> _module.LazyInitArray.Valid(_module.LazyInitArray$T, $Heap, this)
       || (forall i#24: int ::
        { $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#24)): int }
        true
           ==>
          LitInt(0) <= i#24
             && i#24 < Seq#Length(read($Heap, this, _module.LazyInitArray.e))
           ==> $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d),
                $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#24)): int)): int
             == i#24);
  free ensures true;
  ensures Seq#Length(read($Heap, this, _module.LazyInitArray.Contents))
     == Seq#Length(read(old($Heap), this, _module.LazyInitArray.Contents));
  ensures Seq#Equal(read($Heap, this, _module.LazyInitArray.Contents),
    Seq#Update(read($Heap, this, _module.LazyInitArray.Contents), i#0, x#0));
  free ensures true;
  ensures read($Heap, this, _module.LazyInitArray.Zero)
     == read(old($Heap), this, _module.LazyInitArray.Zero);
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f)
         ||
        $o == this
         || $o == read(old($Heap), this, _module.LazyInitArray.a)
         || $o == read(old($Heap), this, _module.LazyInitArray.b)
         || $o == read(old($Heap), this, _module.LazyInitArray.c));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.LazyInitArray.Set(_module.LazyInitArray$T: Ty, this: ref, i#0: int, x#0: Box)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs#0: int;
  var $rhs#1: int;
  var t#0: int;
  var k#0: int;
  var $rhs#2: Seq Box where $Is($rhs#2, TSeq(TInt));
  var $rhs#3: Seq Box where $Is($rhs#3, TSeq(TInt));
  var $rhs#4: int;
  var $rhs#5: Box where $IsBox($rhs#5, _module.LazyInitArray$T);
  var $rhs#6: Seq Box where $Is($rhs#6, TSeq(_module.LazyInitArray$T));

    // AddMethodImpl: Set, Impl$$_module.LazyInitArray.Set
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc)
         ==> $o == this
           || $o == read($Heap, this, _module.LazyInitArray.a)
           || $o == read($Heap, this, _module.LazyInitArray.b)
           || $o == read($Heap, this, _module.LazyInitArray.c));
    assume {:captureState "LazyInitArray.dfy(92,2): initial state"} true;
    $_reverifyPost := false;
    // ----- if statement ----- LazyInitArray.dfy(93,5)
    assert read($Heap, this, _module.LazyInitArray.b) != null;
    assert 0 <= i#0
       && i#0 < _System.array.Length(read($Heap, this, _module.LazyInitArray.b));
    if (LitInt(0)
       <= $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#0))): int)
    {
        assert read($Heap, this, _module.LazyInitArray.b) != null;
        assert 0 <= i#0
           && i#0 < _System.array.Length(read($Heap, this, _module.LazyInitArray.b));
    }

    if (LitInt(0)
         <= $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#0))): int
       && $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#0))): int
         < read($Heap, this, _module.LazyInitArray.n))
    {
        assert read($Heap, this, _module.LazyInitArray.c) != null;
        assert read($Heap, this, _module.LazyInitArray.b) != null;
        assert 0 <= i#0
           && i#0 < _System.array.Length(read($Heap, this, _module.LazyInitArray.b));
        assert 0
             <= $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#0))): int
           && $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#0))): int
             < _System.array.Length(read($Heap, this, _module.LazyInitArray.c));
    }

    assume true;
    if (LitInt(0)
         <= $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#0))): int
       && $Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#0))): int
         < read($Heap, this, _module.LazyInitArray.n)
       && $Unbox(read($Heap,
            read($Heap, this, _module.LazyInitArray.c),
            IndexField($Unbox(read($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#0))): int))): int
         == i#0)
    {
    }
    else
    {
        // ----- assert statement ----- LazyInitArray.dfy(95,7)
        assert {:subsumption 0} 0 <= i#0 && i#0 < Seq#Length(read($Heap, this, _module.LazyInitArray.e));
        assume true;
        assert read($Heap, this, _module.LazyInitArray.n)
           <= $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#0)): int;
        // ----- assignment statement ----- LazyInitArray.dfy(96,12)
        assert read($Heap, this, _module.LazyInitArray.b) != null;
        assert 0 <= i#0
           && i#0 < _System.array.Length(read($Heap, this, _module.LazyInitArray.b));
        assume true;
        assert $_Frame[read($Heap, this, _module.LazyInitArray.b), IndexField(i#0)];
        assume true;
        $rhs#0 := read($Heap, this, _module.LazyInitArray.n);
        $Heap := update($Heap, read($Heap, this, _module.LazyInitArray.b), IndexField(i#0), $Box($rhs#0));
        assume $IsGoodHeap($Heap);
        assume {:captureState "LazyInitArray.dfy(96,15)"} true;
        // ----- assignment statement ----- LazyInitArray.dfy(97,12)
        assert read($Heap, this, _module.LazyInitArray.c) != null;
        assert 0 <= read($Heap, this, _module.LazyInitArray.n)
           && read($Heap, this, _module.LazyInitArray.n)
             < _System.array.Length(read($Heap, this, _module.LazyInitArray.c));
        assume true;
        assert $_Frame[read($Heap, this, _module.LazyInitArray.c), IndexField(read($Heap, this, _module.LazyInitArray.n))];
        assume true;
        $rhs#1 := i#0;
        $Heap := update($Heap,
          read($Heap, this, _module.LazyInitArray.c),
          IndexField(read($Heap, this, _module.LazyInitArray.n)),
          $Box($rhs#1));
        assume $IsGoodHeap($Heap);
        assume {:captureState "LazyInitArray.dfy(97,15)"} true;
        // ----- assignment statement ----- LazyInitArray.dfy(98,19)
        assume true;
        assert 0 <= read($Heap, this, _module.LazyInitArray.n)
           && read($Heap, this, _module.LazyInitArray.n)
             < Seq#Length(read($Heap, this, _module.LazyInitArray.d));
        assume true;
        t#0 := $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.d),
            read($Heap, this, _module.LazyInitArray.n))): int;
        assume {:captureState "LazyInitArray.dfy(98,25)"} true;
        // ----- assignment statement ----- LazyInitArray.dfy(99,19)
        assume true;
        assert 0 <= i#0 && i#0 < Seq#Length(read($Heap, this, _module.LazyInitArray.e));
        assume true;
        k#0 := $Unbox(Seq#Index(read($Heap, this, _module.LazyInitArray.e), i#0)): int;
        assume {:captureState "LazyInitArray.dfy(99,25)"} true;
        // ----- assignment statement ----- LazyInitArray.dfy(100,9)
        assume true;
        assert $_Frame[this, _module.LazyInitArray.d];
        assert 0 <= read($Heap, this, _module.LazyInitArray.n)
           && read($Heap, this, _module.LazyInitArray.n)
             < Seq#Length(read($Heap, this, _module.LazyInitArray.d));
        assert 0 <= k#0
           && k#0
             < Seq#Length(Seq#Update(read($Heap, this, _module.LazyInitArray.d),
                read($Heap, this, _module.LazyInitArray.n),
                $Box(i#0)));
        assume true;
        $rhs#2 := Seq#Update(Seq#Update(read($Heap, this, _module.LazyInitArray.d),
            read($Heap, this, _module.LazyInitArray.n),
            $Box(i#0)),
          k#0,
          $Box(t#0));
        $Heap := update($Heap, this, _module.LazyInitArray.d, $rhs#2);
        assume $IsGoodHeap($Heap);
        assume {:captureState "LazyInitArray.dfy(100,28)"} true;
        // ----- assignment statement ----- LazyInitArray.dfy(101,9)
        assume true;
        assert $_Frame[this, _module.LazyInitArray.e];
        assert 0 <= i#0 && i#0 < Seq#Length(read($Heap, this, _module.LazyInitArray.e));
        assert 0 <= t#0
           && t#0
             < Seq#Length(Seq#Update(read($Heap, this, _module.LazyInitArray.e),
                i#0,
                $Box(read($Heap, this, _module.LazyInitArray.n))));
        assume true;
        $rhs#3 := Seq#Update(Seq#Update(read($Heap, this, _module.LazyInitArray.e),
            i#0,
            $Box(read($Heap, this, _module.LazyInitArray.n))),
          t#0,
          $Box(k#0));
        $Heap := update($Heap, this, _module.LazyInitArray.e, $rhs#3);
        assume $IsGoodHeap($Heap);
        assume {:captureState "LazyInitArray.dfy(101,28)"} true;
        // ----- assignment statement ----- LazyInitArray.dfy(102,9)
        assume true;
        assert $_Frame[this, _module.LazyInitArray.n];
        assume true;
        $rhs#4 := read($Heap, this, _module.LazyInitArray.n) + 1;
        $Heap := update($Heap, this, _module.LazyInitArray.n, $rhs#4);
        assume $IsGoodHeap($Heap);
        assume {:captureState "LazyInitArray.dfy(102,16)"} true;
    }

    // ----- assignment statement ----- LazyInitArray.dfy(105,10)
    assert read($Heap, this, _module.LazyInitArray.a) != null;
    assert 0 <= i#0
       && i#0 < _System.array.Length(read($Heap, this, _module.LazyInitArray.a));
    assume true;
    assert $_Frame[read($Heap, this, _module.LazyInitArray.a), IndexField(i#0)];
    assume true;
    $rhs#5 := x#0;
    $Heap := update($Heap, read($Heap, this, _module.LazyInitArray.a), IndexField(i#0), $rhs#5);
    assume $IsGoodHeap($Heap);
    assume {:captureState "LazyInitArray.dfy(105,13)"} true;
    // ----- assignment statement ----- LazyInitArray.dfy(106,14)
    assume true;
    assert $_Frame[this, _module.LazyInitArray.Contents];
    assert 0 <= i#0 && i#0 < Seq#Length(read($Heap, this, _module.LazyInitArray.Contents));
    assume true;
    $rhs#6 := Seq#Update(read($Heap, this, _module.LazyInitArray.Contents), i#0, x#0);
    $Heap := update($Heap, this, _module.LazyInitArray.Contents, $rhs#6);
    assume $IsGoodHeap($Heap);
    assume {:captureState "LazyInitArray.dfy(106,32)"} true;
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

const unique field$Contents: NameFamily;

const unique field$Zero: NameFamily;

const unique field$a: NameFamily;

const unique field$b: NameFamily;

const unique field$c: NameFamily;

const unique field$n: NameFamily;

const unique field$d: NameFamily;

const unique field$e: NameFamily;