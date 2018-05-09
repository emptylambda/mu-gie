// Dafny 2.0.0.00922 technical preview 0
// Command Line Options: /compile:0 /noVerify /print:b7.bpl b7.dfy

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

const unique class._module.Queue: ClassName;

function Tclass._module.Queue(Ty) : Ty;

// Tclass._module.Queue Tag
axiom (forall _module.Queue$T: Ty ::
  { Tclass._module.Queue(_module.Queue$T) }
  Tag(Tclass._module.Queue(_module.Queue$T)) == Tagclass._module.Queue);

const unique Tagclass._module.Queue: TyTag;

// Tclass._module.Queue injectivity 0
axiom (forall _module.Queue$T: Ty ::
  { Tclass._module.Queue(_module.Queue$T) }
  Tclass._module.Queue_0(Tclass._module.Queue(_module.Queue$T)) == _module.Queue$T);

function Tclass._module.Queue_0(Ty) : Ty;

// Box/unbox axiom for Tclass._module.Queue
axiom (forall _module.Queue$T: Ty, bx: Box ::
  { $IsBox(bx, Tclass._module.Queue(_module.Queue$T)) }
  $IsBox(bx, Tclass._module.Queue(_module.Queue$T))
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.Queue(_module.Queue$T)));

// Queue: Class $Is
axiom (forall _module.Queue$T: Ty, $o: ref ::
  { $Is($o, Tclass._module.Queue(_module.Queue$T)) }
  $Is($o, Tclass._module.Queue(_module.Queue$T))
     <==> $o == null || dtype($o) == Tclass._module.Queue(_module.Queue$T));

// Queue: Class $IsAlloc
axiom (forall _module.Queue$T: Ty, $o: ref, $h: Heap ::
  { $IsAlloc($o, Tclass._module.Queue(_module.Queue$T), $h) }
  $IsAlloc($o, Tclass._module.Queue(_module.Queue$T), $h)
     <==> $o == null || read($h, $o, alloc));

axiom FDim(_module.Queue.contents) == 0
   && FieldOfDecl(class._module.Queue, field$contents) == _module.Queue.contents
   && !$IsGhostField(_module.Queue.contents);

const _module.Queue.contents: Field (Seq Box);

// Queue.contents: Allocation axiom
axiom (forall _module.Queue$T: Ty, $h: Heap, $o: ref ::
  { read($h, $o, _module.Queue.contents), Tclass._module.Queue(_module.Queue$T) }
  $IsGoodHeap($h)
       && $o != null
       && dtype($o) == Tclass._module.Queue(_module.Queue$T)
     ==> $Is(read($h, $o, _module.Queue.contents), TSeq(_module.Queue$T))
       && (read($h, $o, alloc)
         ==> $IsAlloc(read($h, $o, _module.Queue.contents), TSeq(_module.Queue$T), $h)));

procedure CheckWellformed$$_module.Queue.Init(_module.Queue$T: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Queue(_module.Queue$T))
         && $IsAlloc(this, Tclass._module.Queue(_module.Queue$T), $Heap));
  free requires 14 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.Queue.Init(_module.Queue$T: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Queue(_module.Queue$T))
         && $IsAlloc(this, Tclass._module.Queue(_module.Queue$T), $Heap));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures Seq#Length(read($Heap, this, _module.Queue.contents)) == LitInt(0);
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f) || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure CheckWellformed$$_module.Queue.Enqueue(_module.Queue$T: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Queue(_module.Queue$T))
         && $IsAlloc(this, Tclass._module.Queue(_module.Queue$T), $Heap),
    x#0: Box
       where $IsBox(x#0, _module.Queue$T) && $IsAllocBox(x#0, _module.Queue$T, $Heap));
  free requires 10 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.Queue.Enqueue(_module.Queue$T: Ty, this: ref, x#0: Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: Enqueue, CheckWellformed$$_module.Queue.Enqueue
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> $o == this);
    assume {:captureState "b7.dfy(17,9): initial state"} true;
    havoc $Heap;
    assume (forall<alpha> $o: ref, $f: Field alpha ::
      { read($Heap, $o, $f) }
      $o != null && read(old($Heap), $o, alloc)
         ==> read($Heap, $o, $f) == read(old($Heap), $o, $f) || $o == this);
    assume $HeapSucc(old($Heap), $Heap);
    assume {:captureState "b7.dfy(19,21): post-state"} true;
    assert $IsAlloc(this, Tclass._module.Queue(_module.Queue$T), old($Heap));
    assume Seq#Equal(read($Heap, this, _module.Queue.contents),
      Seq#Append(read(old($Heap), this, _module.Queue.contents),
        Seq#Build(Seq#Empty(): Seq Box, x#0)));
}



procedure Call$$_module.Queue.Enqueue(_module.Queue$T: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Queue(_module.Queue$T))
         && $IsAlloc(this, Tclass._module.Queue(_module.Queue$T), $Heap),
    x#0: Box
       where $IsBox(x#0, _module.Queue$T) && $IsAllocBox(x#0, _module.Queue$T, $Heap));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures Seq#Equal(read($Heap, this, _module.Queue.contents),
    Seq#Append(read(old($Heap), this, _module.Queue.contents),
      Seq#Build(Seq#Empty(): Seq Box, x#0)));
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f) || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure CheckWellformed$$_module.Queue.Dequeue(_module.Queue$T: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Queue(_module.Queue$T))
         && $IsAlloc(this, Tclass._module.Queue(_module.Queue$T), $Heap))
   returns (x#0: Box
       where $IsBox(x#0, _module.Queue$T) && $IsAllocBox(x#0, _module.Queue$T, $Heap));
  free requires 11 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.Queue.Dequeue(_module.Queue$T: Ty, this: ref) returns (x#0: Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: Dequeue, CheckWellformed$$_module.Queue.Dequeue
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> $o == this);
    assume {:captureState "b7.dfy(20,9): initial state"} true;
    assume 0 < Seq#Length(read($Heap, this, _module.Queue.contents));
    havoc $Heap;
    assume (forall<alpha> $o: ref, $f: Field alpha ::
      { read($Heap, $o, $f) }
      $o != null && read(old($Heap), $o, alloc)
         ==> read($Heap, $o, $f) == read(old($Heap), $o, $f) || $o == this);
    assume $HeapSucc(old($Heap), $Heap);
    havoc x#0;
    assume {:captureState "b7.dfy(23,43): post-state"} true;
    assert $IsAlloc(this, Tclass._module.Queue(_module.Queue$T), old($Heap));
    assert 0 <= LitInt(1)
       && LitInt(1) <= Seq#Length(read(old($Heap), this, _module.Queue.contents));
    assume Seq#Equal(read($Heap, this, _module.Queue.contents),
      Seq#Drop(read(old($Heap), this, _module.Queue.contents), LitInt(1)));
    assert $IsAlloc(this, Tclass._module.Queue(_module.Queue$T), old($Heap));
    assert 0 <= LitInt(0)
       && LitInt(0) < Seq#Length(read(old($Heap), this, _module.Queue.contents));
    assume x#0 == Seq#Index(read(old($Heap), this, _module.Queue.contents), LitInt(0));
}



procedure Call$$_module.Queue.Dequeue(_module.Queue$T: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Queue(_module.Queue$T))
         && $IsAlloc(this, Tclass._module.Queue(_module.Queue$T), $Heap))
   returns (x#0: Box
       where $IsBox(x#0, _module.Queue$T) && $IsAllocBox(x#0, _module.Queue$T, $Heap));
  // user-defined preconditions
  requires 0 < Seq#Length(read($Heap, this, _module.Queue.contents));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures Seq#Equal(read($Heap, this, _module.Queue.contents),
    Seq#Drop(read(old($Heap), this, _module.Queue.contents), LitInt(1)));
  ensures x#0 == Seq#Index(read(old($Heap), this, _module.Queue.contents), LitInt(0));
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f) || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



// function declaration for _module.Queue.Head
function _module.Queue.Head(_module.Queue$T: Ty, $heap: Heap, this: ref) : Box;

function _module.Queue.Head#canCall(_module.Queue$T: Ty, $heap: Heap, this: ref) : bool;

// frame axiom for _module.Queue.Head
axiom (forall _module.Queue$T: Ty, $h0: Heap, $h1: Heap, this: ref ::
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.Queue.Head(_module.Queue$T, $h1, this) }
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       &&
      this != null
       && $Is(this, Tclass._module.Queue(_module.Queue$T))
       &&
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==>
    (forall<alpha> $o: ref, $f: Field alpha ::
      $o != null && $o == this ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.Queue.Head(_module.Queue$T, $h0, this)
       == _module.Queue.Head(_module.Queue$T, $h1, this));

// consequence axiom for _module.Queue.Head
axiom 13 <= $FunctionContextHeight
   ==> (forall _module.Queue$T: Ty, $Heap: Heap, this: ref ::
    { _module.Queue.Head(_module.Queue$T, $Heap, this) }
    _module.Queue.Head#canCall(_module.Queue$T, $Heap, this)
         || (13 != $FunctionContextHeight
           &&
          $IsGoodHeap($Heap)
           &&
          this != null
           &&
          $Is(this, Tclass._module.Queue(_module.Queue$T))
           && $IsAlloc(this, Tclass._module.Queue(_module.Queue$T), $Heap)
           && 0 < Seq#Length(read($Heap, this, _module.Queue.contents)))
       ==> $IsBox(_module.Queue.Head(_module.Queue$T, $Heap, this), _module.Queue$T));

function _module.Queue.Head#requires(Ty, Heap, ref) : bool;

// #requires axiom for _module.Queue.Head
axiom (forall _module.Queue$T: Ty, $Heap: Heap, this: ref ::
  { _module.Queue.Head#requires(_module.Queue$T, $Heap, this) }
  $IsGoodHeap($Heap)
       &&
      this != null
       &&
      $Is(this, Tclass._module.Queue(_module.Queue$T))
       && $IsAlloc(this, Tclass._module.Queue(_module.Queue$T), $Heap)
     ==> _module.Queue.Head#requires(_module.Queue$T, $Heap, this)
       == (0 < Seq#Length(read($Heap, this, _module.Queue.contents))));

// definition axiom for _module.Queue.Head(revealed)
axiom 13 <= $FunctionContextHeight
   ==> (forall _module.Queue$T: Ty, $Heap: Heap, this: ref ::
    { _module.Queue.Head(_module.Queue$T, $Heap, this) }
    _module.Queue.Head#canCall(_module.Queue$T, $Heap, this)
         || (13 != $FunctionContextHeight
           &&
          $IsGoodHeap($Heap)
           &&
          this != null
           &&
          $Is(this, Tclass._module.Queue(_module.Queue$T))
           && $IsAlloc(this, Tclass._module.Queue(_module.Queue$T), $Heap)
           && 0 < Seq#Length(read($Heap, this, _module.Queue.contents)))
       ==> _module.Queue.Head(_module.Queue$T, $Heap, this)
         == Seq#Index(read($Heap, this, _module.Queue.contents), LitInt(0)));

procedure CheckWellformed$$_module.Queue.Head(_module.Queue$T: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Queue(_module.Queue$T))
         && $IsAlloc(this, Tclass._module.Queue(_module.Queue$T), $Heap));
  free requires 13 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.Queue.Head(_module.Queue$T: Ty, this: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function Head
    assume {:captureState "b7.dfy(24,11): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> $o == this);
    b$reqreads#0 := $_Frame[this, _module.Queue.contents];
    assume 0 < Seq#Length(read($Heap, this, _module.Queue.contents));
    assert b$reqreads#0;
    if (*)
    {
        assume $IsBox(_module.Queue.Head(_module.Queue$T, $Heap, this), _module.Queue$T);
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
          $o != null && read($Heap, $o, alloc) ==> $o == this);
        b$reqreads#1 := $_Frame[this, _module.Queue.contents];
        assert 0 <= LitInt(0)
           && LitInt(0) < Seq#Length(read($Heap, this, _module.Queue.contents));
        assume _module.Queue.Head(_module.Queue$T, $Heap, this)
           == Seq#Index(read($Heap, this, _module.Queue.contents), LitInt(0));
        assume true;
        // CheckWellformedWithResult: any expression
        assume $IsBox(_module.Queue.Head(_module.Queue$T, $Heap, this), _module.Queue$T);
        assert b$reqreads#1;
    }
}



// function declaration for _module.Queue.Get
function _module.Queue.Get(_module.Queue$T: Ty, $heap: Heap, this: ref, i#0: int) : Box;

function _module.Queue.Get#canCall(_module.Queue$T: Ty, $heap: Heap, this: ref, i#0: int) : bool;

// frame axiom for _module.Queue.Get
axiom (forall _module.Queue$T: Ty, $h0: Heap, $h1: Heap, this: ref, i#0: int ::
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.Queue.Get(_module.Queue$T, $h1, this, i#0) }
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       &&
      this != null
       && $Is(this, Tclass._module.Queue(_module.Queue$T))
       &&
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==>
    (forall<alpha> $o: ref, $f: Field alpha ::
      $o != null && $o == this ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.Queue.Get(_module.Queue$T, $h0, this, i#0)
       == _module.Queue.Get(_module.Queue$T, $h1, this, i#0));

// consequence axiom for _module.Queue.Get
axiom 8 <= $FunctionContextHeight
   ==> (forall _module.Queue$T: Ty, $Heap: Heap, this: ref, i#0: int ::
    { _module.Queue.Get(_module.Queue$T, $Heap, this, i#0) }
    _module.Queue.Get#canCall(_module.Queue$T, $Heap, this, i#0)
         || (8 != $FunctionContextHeight
           &&
          $IsGoodHeap($Heap)
           &&
          this != null
           &&
          $Is(this, Tclass._module.Queue(_module.Queue$T))
           && $IsAlloc(this, Tclass._module.Queue(_module.Queue$T), $Heap)
           &&
          LitInt(0) <= i#0
           && i#0 < Seq#Length(read($Heap, this, _module.Queue.contents)))
       ==> $IsBox(_module.Queue.Get(_module.Queue$T, $Heap, this, i#0), _module.Queue$T));

function _module.Queue.Get#requires(Ty, Heap, ref, int) : bool;

// #requires axiom for _module.Queue.Get
axiom (forall _module.Queue$T: Ty, $Heap: Heap, this: ref, i#0: int ::
  { _module.Queue.Get#requires(_module.Queue$T, $Heap, this, i#0) }
  $IsGoodHeap($Heap)
       &&
      this != null
       &&
      $Is(this, Tclass._module.Queue(_module.Queue$T))
       && $IsAlloc(this, Tclass._module.Queue(_module.Queue$T), $Heap)
     ==> _module.Queue.Get#requires(_module.Queue$T, $Heap, this, i#0)
       == (LitInt(0) <= i#0
         && i#0 < Seq#Length(read($Heap, this, _module.Queue.contents))));

// definition axiom for _module.Queue.Get(revealed)
axiom 8 <= $FunctionContextHeight
   ==> (forall _module.Queue$T: Ty, $Heap: Heap, this: ref, i#0: int ::
    { _module.Queue.Get(_module.Queue$T, $Heap, this, i#0) }
    _module.Queue.Get#canCall(_module.Queue$T, $Heap, this, i#0)
         || (8 != $FunctionContextHeight
           &&
          $IsGoodHeap($Heap)
           &&
          this != null
           &&
          $Is(this, Tclass._module.Queue(_module.Queue$T))
           && $IsAlloc(this, Tclass._module.Queue(_module.Queue$T), $Heap)
           &&
          LitInt(0) <= i#0
           && i#0 < Seq#Length(read($Heap, this, _module.Queue.contents)))
       ==> _module.Queue.Get(_module.Queue$T, $Heap, this, i#0)
         == Seq#Index(read($Heap, this, _module.Queue.contents), i#0));

procedure CheckWellformed$$_module.Queue.Get(_module.Queue$T: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Queue(_module.Queue$T))
         && $IsAlloc(this, Tclass._module.Queue(_module.Queue$T), $Heap),
    i#0: int);
  free requires 8 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.Queue.Get(_module.Queue$T: Ty, this: ref, i#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function Get
    assume {:captureState "b7.dfy(28,11): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> $o == this);
    if (LitInt(0) <= i#0)
    {
        b$reqreads#0 := $_Frame[this, _module.Queue.contents];
    }

    assume LitInt(0) <= i#0 && i#0 < Seq#Length(read($Heap, this, _module.Queue.contents));
    assert b$reqreads#0;
    if (*)
    {
        assume $IsBox(_module.Queue.Get(_module.Queue$T, $Heap, this, i#0), _module.Queue$T);
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
          $o != null && read($Heap, $o, alloc) ==> $o == this);
        b$reqreads#1 := $_Frame[this, _module.Queue.contents];
        assert 0 <= i#0 && i#0 < Seq#Length(read($Heap, this, _module.Queue.contents));
        assume _module.Queue.Get(_module.Queue$T, $Heap, this, i#0)
           == Seq#Index(read($Heap, this, _module.Queue.contents), i#0);
        assume true;
        // CheckWellformedWithResult: any expression
        assume $IsBox(_module.Queue.Get(_module.Queue$T, $Heap, this, i#0), _module.Queue$T);
        assert b$reqreads#1;
    }
}



const unique class._module.Stream: ClassName;

function Tclass._module.Stream() : Ty;

// Tclass._module.Stream Tag
axiom Tag(Tclass._module.Stream()) == Tagclass._module.Stream;

const unique Tagclass._module.Stream: TyTag;

// Box/unbox axiom for Tclass._module.Stream
axiom (forall bx: Box ::
  { $IsBox(bx, Tclass._module.Stream()) }
  $IsBox(bx, Tclass._module.Stream())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.Stream()));

// Stream: Class $Is
axiom (forall $o: ref ::
  { $Is($o, Tclass._module.Stream()) }
  $Is($o, Tclass._module.Stream())
     <==> $o == null || dtype($o) == Tclass._module.Stream());

// Stream: Class $IsAlloc
axiom (forall $o: ref, $h: Heap ::
  { $IsAlloc($o, Tclass._module.Stream(), $h) }
  $IsAlloc($o, Tclass._module.Stream(), $h) <==> $o == null || read($h, $o, alloc));

axiom FDim(_module.Stream.footprint) == 0
   && FieldOfDecl(class._module.Stream, field$footprint) == _module.Stream.footprint
   && $IsGhostField(_module.Stream.footprint);

const _module.Stream.footprint: Field (Set Box);

// Stream.footprint: Allocation axiom
axiom (forall $h: Heap, $o: ref ::
  { read($h, $o, _module.Stream.footprint) }
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.Stream()
     ==> $Is(read($h, $o, _module.Stream.footprint), TSet(Tclass._System.object()))
       && (read($h, $o, alloc)
         ==> $IsAlloc(read($h, $o, _module.Stream.footprint), TSet(Tclass._System.object()), $h)));

axiom FDim(_module.Stream.stream) == 0
   && FieldOfDecl(class._module.Stream, field$stream) == _module.Stream.stream
   && !$IsGhostField(_module.Stream.stream);

const _module.Stream.stream: Field (Seq Box);

// Stream.stream: Allocation axiom
axiom (forall $h: Heap, $o: ref ::
  { read($h, $o, _module.Stream.stream) }
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.Stream()
     ==> $Is(read($h, $o, _module.Stream.stream), TSeq(TInt))
       && (read($h, $o, alloc)
         ==> $IsAlloc(read($h, $o, _module.Stream.stream), TSeq(TInt), $h)));

axiom FDim(_module.Stream.isOpen) == 0
   && FieldOfDecl(class._module.Stream, field$isOpen) == _module.Stream.isOpen
   && !$IsGhostField(_module.Stream.isOpen);

const _module.Stream.isOpen: Field bool;

// Stream.isOpen: Allocation axiom
axiom (forall $h: Heap, $o: ref ::
  { read($h, $o, _module.Stream.isOpen) }
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.Stream()
     ==> $Is(read($h, $o, _module.Stream.isOpen), TBool)
       && (read($h, $o, alloc)
         ==> $IsAlloc(read($h, $o, _module.Stream.isOpen), TBool, $h)));

// function declaration for _module.Stream.Valid
function _module.Stream.Valid($heap: Heap, this: ref) : bool;

function _module.Stream.Valid#canCall($heap: Heap, this: ref) : bool;

// frame axiom for _module.Stream.Valid
axiom (forall $h0: Heap, $h1: Heap, this: ref ::
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.Stream.Valid($h1, this) }
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       &&
      this != null
       && $Is(this, Tclass._module.Stream())
       &&
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==>
    (forall<alpha> $o: ref, $f: Field alpha ::
      $o != null
           && ($o == this || read($h0, this, _module.Stream.footprint)[$Box($o)])
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.Stream.Valid($h0, this) == _module.Stream.Valid($h1, this));

// consequence axiom for _module.Stream.Valid
axiom 0 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref ::
    { _module.Stream.Valid($Heap, this) }
    _module.Stream.Valid#canCall($Heap, this)
         || (0 != $FunctionContextHeight
           &&
          $IsGoodHeap($Heap)
           &&
          this != null
           &&
          $Is(this, Tclass._module.Stream())
           && $IsAlloc(this, Tclass._module.Stream(), $Heap))
       ==> true);

function _module.Stream.Valid#requires(Heap, ref) : bool;

// #requires axiom for _module.Stream.Valid
axiom (forall $Heap: Heap, this: ref ::
  { _module.Stream.Valid#requires($Heap, this) }
  $IsGoodHeap($Heap)
       &&
      this != null
       &&
      $Is(this, Tclass._module.Stream())
       && $IsAlloc(this, Tclass._module.Stream(), $Heap)
     ==> _module.Stream.Valid#requires($Heap, this) == true);

// definition axiom for _module.Stream.Valid(revealed)
axiom 0 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref ::
    { _module.Stream.Valid($Heap, this) }
    _module.Stream.Valid#canCall($Heap, this)
         || (0 != $FunctionContextHeight
           &&
          $IsGoodHeap($Heap)
           &&
          this != null
           &&
          $Is(this, Tclass._module.Stream())
           && $IsAlloc(this, Tclass._module.Stream(), $Heap))
       ==> _module.Stream.Valid($Heap, this)
         == (
          !read($Heap, this, _module.Stream.footprint)[$Box(null)]
           && read($Heap, this, _module.Stream.footprint)[$Box(this)]
           && read($Heap, this, _module.Stream.isOpen)));

procedure CheckWellformed$$_module.Stream.Valid(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Stream())
         && $IsAlloc(this, Tclass._module.Stream(), $Heap));
  free requires 0 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.Stream.Valid(this: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;
  var b$reqreads#2: bool;
  var b$reqreads#3: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;
    b$reqreads#2 := true;
    b$reqreads#3 := true;

    // AddWellformednessCheck for function Valid
    assume {:captureState "b7.dfy(39,11): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc)
         ==> $o == this || read($Heap, this, _module.Stream.footprint)[$Box($o)]);
    b$reqreads#0 := $_Frame[this, _module.Stream.footprint];
    assert b$reqreads#0;
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
          $o != null && read($Heap, $o, alloc)
             ==> $o == this || read($Heap, this, _module.Stream.footprint)[$Box($o)]);
        b$reqreads#1 := $_Frame[this, _module.Stream.footprint];
        if (!read($Heap, this, _module.Stream.footprint)[$Box(null)])
        {
            b$reqreads#2 := $_Frame[this, _module.Stream.footprint];
        }

        if (!read($Heap, this, _module.Stream.footprint)[$Box(null)]
           && read($Heap, this, _module.Stream.footprint)[$Box(this)])
        {
            b$reqreads#3 := $_Frame[this, _module.Stream.isOpen];
        }

        assume _module.Stream.Valid($Heap, this)
           == (
            !read($Heap, this, _module.Stream.footprint)[$Box(null)]
             && read($Heap, this, _module.Stream.footprint)[$Box(this)]
             && read($Heap, this, _module.Stream.isOpen));
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(_module.Stream.Valid($Heap, this), TBool);
        assert b$reqreads#1;
        assert b$reqreads#2;
        assert b$reqreads#3;
    }
}



procedure CheckWellformed$$_module.Stream.GetCount(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Stream())
         && $IsAlloc(this, Tclass._module.Stream(), $Heap))
   returns (c#0: int);
  free requires 1 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.Stream.GetCount(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Stream())
         && $IsAlloc(this, Tclass._module.Stream(), $Heap))
   returns (c#0: int);
  // user-defined preconditions
  requires _module.Stream.Valid#canCall($Heap, this)
     ==> _module.Stream.Valid($Heap, this)
       || !read($Heap, this, _module.Stream.footprint)[$Box(null)];
  requires _module.Stream.Valid#canCall($Heap, this)
     ==> _module.Stream.Valid($Heap, this)
       || read($Heap, this, _module.Stream.footprint)[$Box(this)];
  requires _module.Stream.Valid#canCall($Heap, this)
     ==> _module.Stream.Valid($Heap, this) || read($Heap, this, _module.Stream.isOpen);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures LitInt(0) <= c#0;
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Stream.GetCount(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Stream())
         && $IsAlloc(this, Tclass._module.Stream(), $Heap))
   returns (c#0: int, $_reverifyPost: bool);
  free requires 1 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.Stream.Valid#canCall($Heap, this)
     &&
    _module.Stream.Valid($Heap, this)
     &&
    !read($Heap, this, _module.Stream.footprint)[$Box(null)]
     && read($Heap, this, _module.Stream.footprint)[$Box(this)]
     && read($Heap, this, _module.Stream.isOpen);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures LitInt(0) <= c#0;
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Stream.GetCount(this: ref) returns (c#0: int, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: GetCount, Impl$$_module.Stream.GetCount
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "b7.dfy(48,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- b7.dfy(49,7)
    assume true;
    assume true;
    c#0 := Seq#Length(read($Heap, this, _module.Stream.stream));
    assume {:captureState "b7.dfy(49,17)"} true;
}



procedure CheckWellformed$$_module.Stream.Create(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Stream())
         && $IsAlloc(this, Tclass._module.Stream(), $Heap));
  free requires 2 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.Stream.Create(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Stream())
         && $IsAlloc(this, Tclass._module.Stream(), $Heap));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.Stream.Valid#canCall($Heap, this);
  free ensures _module.Stream.Valid#canCall($Heap, this)
     &&
    _module.Stream.Valid($Heap, this)
     &&
    !read($Heap, this, _module.Stream.footprint)[$Box(null)]
     && read($Heap, this, _module.Stream.footprint)[$Box(this)]
     && read($Heap, this, _module.Stream.isOpen);
  ensures (forall $o: ref ::
    { read(old($Heap), $o, alloc) }
    read($Heap, this, _module.Stream.footprint)[$Box($o)] && $o != this
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures true;
  ensures Seq#Equal(read($Heap, this, _module.Stream.stream), Seq#Empty(): Seq Box);
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f) || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Stream.Create(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Stream())
         && $IsAlloc(this, Tclass._module.Stream(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 2 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.Stream.Valid#canCall($Heap, this);
  ensures _module.Stream.Valid#canCall($Heap, this)
     ==> _module.Stream.Valid($Heap, this)
       || !read($Heap, this, _module.Stream.footprint)[$Box(null)];
  ensures _module.Stream.Valid#canCall($Heap, this)
     ==> _module.Stream.Valid($Heap, this)
       || read($Heap, this, _module.Stream.footprint)[$Box(this)];
  ensures _module.Stream.Valid#canCall($Heap, this)
     ==> _module.Stream.Valid($Heap, this) || read($Heap, this, _module.Stream.isOpen);
  ensures (forall $o: ref ::
    { read(old($Heap), $o, alloc) }
    read($Heap, this, _module.Stream.footprint)[$Box($o)] && $o != this
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures true;
  ensures Seq#Equal(read($Heap, this, _module.Stream.stream), Seq#Empty(): Seq Box);
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f) || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Stream.Create(this: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs#0: Seq Box where $Is($rhs#0, TSeq(TInt));
  var $rhs#1: Set Box where $Is($rhs#1, TSet(Tclass._System.object()));
  var $rhs#2: bool;

    // AddMethodImpl: Create, Impl$$_module.Stream.Create
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> $o == this);
    assume {:captureState "b7.dfy(56,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- b7.dfy(57,12)
    assume true;
    assert $_Frame[this, _module.Stream.stream];
    assume true;
    $rhs#0 := Lit(Seq#Empty(): Seq Box);
    $Heap := update($Heap, this, _module.Stream.stream, $rhs#0);
    assume $IsGoodHeap($Heap);
    assume {:captureState "b7.dfy(57,16)"} true;
    // ----- assignment statement ----- b7.dfy(58,15)
    assume true;
    assert $_Frame[this, _module.Stream.footprint];
    assume true;
    $rhs#1 := Set#UnionOne(Set#Empty(): Set Box, $Box(this));
    $Heap := update($Heap, this, _module.Stream.footprint, $rhs#1);
    assume $IsGoodHeap($Heap);
    assume {:captureState "b7.dfy(58,23)"} true;
    // ----- assignment statement ----- b7.dfy(59,12)
    assume true;
    assert $_Frame[this, _module.Stream.isOpen];
    assume true;
    $rhs#2 := Lit(true);
    $Heap := update($Heap, this, _module.Stream.isOpen, $rhs#2);
    assume $IsGoodHeap($Heap);
    assume {:captureState "b7.dfy(59,18)"} true;
}



procedure CheckWellformed$$_module.Stream.Open(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Stream())
         && $IsAlloc(this, Tclass._module.Stream(), $Heap));
  free requires 3 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.Stream.Open(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Stream())
         && $IsAlloc(this, Tclass._module.Stream(), $Heap));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.Stream.Valid#canCall($Heap, this);
  free ensures _module.Stream.Valid#canCall($Heap, this)
     &&
    _module.Stream.Valid($Heap, this)
     &&
    !read($Heap, this, _module.Stream.footprint)[$Box(null)]
     && read($Heap, this, _module.Stream.footprint)[$Box(this)]
     && read($Heap, this, _module.Stream.isOpen);
  ensures (forall $o: ref ::
    { read(old($Heap), $o, alloc) }
    read($Heap, this, _module.Stream.footprint)[$Box($o)] && $o != this
       ==> $o != null && !read(old($Heap), $o, alloc));
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f) || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Stream.Open(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Stream())
         && $IsAlloc(this, Tclass._module.Stream(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 3 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.Stream.Valid#canCall($Heap, this);
  ensures _module.Stream.Valid#canCall($Heap, this)
     ==> _module.Stream.Valid($Heap, this)
       || !read($Heap, this, _module.Stream.footprint)[$Box(null)];
  ensures _module.Stream.Valid#canCall($Heap, this)
     ==> _module.Stream.Valid($Heap, this)
       || read($Heap, this, _module.Stream.footprint)[$Box(this)];
  ensures _module.Stream.Valid#canCall($Heap, this)
     ==> _module.Stream.Valid($Heap, this) || read($Heap, this, _module.Stream.isOpen);
  ensures (forall $o: ref ::
    { read(old($Heap), $o, alloc) }
    read($Heap, this, _module.Stream.footprint)[$Box($o)] && $o != this
       ==> $o != null && !read(old($Heap), $o, alloc));
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f) || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Stream.Open(this: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs#0: Set Box where $Is($rhs#0, TSet(Tclass._System.object()));
  var $rhs#1: bool;

    // AddMethodImpl: Open, Impl$$_module.Stream.Open
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> $o == this);
    assume {:captureState "b7.dfy(65,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- b7.dfy(66,15)
    assume true;
    assert $_Frame[this, _module.Stream.footprint];
    assume true;
    $rhs#0 := Set#UnionOne(Set#Empty(): Set Box, $Box(this));
    $Heap := update($Heap, this, _module.Stream.footprint, $rhs#0);
    assume $IsGoodHeap($Heap);
    assume {:captureState "b7.dfy(66,23)"} true;
    // ----- assignment statement ----- b7.dfy(67,12)
    assume true;
    assert $_Frame[this, _module.Stream.isOpen];
    assume true;
    $rhs#1 := Lit(true);
    $Heap := update($Heap, this, _module.Stream.isOpen, $rhs#1);
    assume $IsGoodHeap($Heap);
    assume {:captureState "b7.dfy(67,18)"} true;
}



procedure CheckWellformed$$_module.Stream.PutChar(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Stream())
         && $IsAlloc(this, Tclass._module.Stream(), $Heap),
    x#0: int);
  free requires 4 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.Stream.PutChar(this: ref, x#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: PutChar, CheckWellformed$$_module.Stream.PutChar
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc)
         ==> read($Heap, this, _module.Stream.footprint)[$Box($o)]);
    assume {:captureState "b7.dfy(70,9): initial state"} true;
    assume _module.Stream.Valid#canCall($Heap, this);
    assume _module.Stream.Valid($Heap, this);
    havoc $Heap;
    assume (forall<alpha> $o: ref, $f: Field alpha ::
      { read($Heap, $o, $f) }
      $o != null && read(old($Heap), $o, alloc)
         ==> read($Heap, $o, $f) == read(old($Heap), $o, $f)
           || read(old($Heap), this, _module.Stream.footprint)[$Box($o)]);
    assume $HeapSucc(old($Heap), $Heap);
    assume {:captureState "b7.dfy(73,20): post-state"} true;
    assume _module.Stream.Valid#canCall($Heap, this);
    assume _module.Stream.Valid($Heap, this);
    assert $IsAlloc(this, Tclass._module.Stream(), old($Heap));
    assume (forall $o: ref ::
      { read(old($Heap), $o, alloc) }
      read($Heap, this, _module.Stream.footprint)[$Box($o)]
           && !read(old($Heap), this, _module.Stream.footprint)[$Box($o)]
         ==> $o != null && !read(old($Heap), $o, alloc));
    assert $IsAlloc(this, Tclass._module.Stream(), old($Heap));
    assume Seq#Equal(read($Heap, this, _module.Stream.stream),
      Seq#Append(read(old($Heap), this, _module.Stream.stream),
        Seq#Build(Seq#Empty(): Seq Box, $Box(x#0))));
}



procedure Call$$_module.Stream.PutChar(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Stream())
         && $IsAlloc(this, Tclass._module.Stream(), $Heap),
    x#0: int);
  // user-defined preconditions
  requires _module.Stream.Valid#canCall($Heap, this)
     ==> _module.Stream.Valid($Heap, this)
       || !read($Heap, this, _module.Stream.footprint)[$Box(null)];
  requires _module.Stream.Valid#canCall($Heap, this)
     ==> _module.Stream.Valid($Heap, this)
       || read($Heap, this, _module.Stream.footprint)[$Box(this)];
  requires _module.Stream.Valid#canCall($Heap, this)
     ==> _module.Stream.Valid($Heap, this) || read($Heap, this, _module.Stream.isOpen);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.Stream.Valid#canCall($Heap, this);
  free ensures _module.Stream.Valid#canCall($Heap, this)
     &&
    _module.Stream.Valid($Heap, this)
     &&
    !read($Heap, this, _module.Stream.footprint)[$Box(null)]
     && read($Heap, this, _module.Stream.footprint)[$Box(this)]
     && read($Heap, this, _module.Stream.isOpen);
  ensures (forall $o: ref ::
    { read(old($Heap), $o, alloc) }
    read($Heap, this, _module.Stream.footprint)[$Box($o)]
         && !read(old($Heap), this, _module.Stream.footprint)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures true;
  ensures Seq#Equal(read($Heap, this, _module.Stream.stream),
    Seq#Append(read(old($Heap), this, _module.Stream.stream),
      Seq#Build(Seq#Empty(): Seq Box, $Box(x#0))));
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f)
         || read(old($Heap), this, _module.Stream.footprint)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Stream.PutChar(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Stream())
         && $IsAlloc(this, Tclass._module.Stream(), $Heap),
    x#0: int)
   returns ($_reverifyPost: bool);
  free requires 4 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.Stream.Valid#canCall($Heap, this)
     &&
    _module.Stream.Valid($Heap, this)
     &&
    !read($Heap, this, _module.Stream.footprint)[$Box(null)]
     && read($Heap, this, _module.Stream.footprint)[$Box(this)]
     && read($Heap, this, _module.Stream.isOpen);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.Stream.Valid#canCall($Heap, this);
  ensures _module.Stream.Valid#canCall($Heap, this)
     ==> _module.Stream.Valid($Heap, this)
       || !read($Heap, this, _module.Stream.footprint)[$Box(null)];
  ensures _module.Stream.Valid#canCall($Heap, this)
     ==> _module.Stream.Valid($Heap, this)
       || read($Heap, this, _module.Stream.footprint)[$Box(this)];
  ensures _module.Stream.Valid#canCall($Heap, this)
     ==> _module.Stream.Valid($Heap, this) || read($Heap, this, _module.Stream.isOpen);
  ensures (forall $o: ref ::
    { read(old($Heap), $o, alloc) }
    read($Heap, this, _module.Stream.footprint)[$Box($o)]
         && !read(old($Heap), this, _module.Stream.footprint)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures true;
  ensures Seq#Equal(read($Heap, this, _module.Stream.stream),
    Seq#Append(read(old($Heap), this, _module.Stream.stream),
      Seq#Build(Seq#Empty(): Seq Box, $Box(x#0))));
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f)
         || read(old($Heap), this, _module.Stream.footprint)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Stream.PutChar(this: ref, x#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs#0: Seq Box where $Is($rhs#0, TSeq(TInt));

    // AddMethodImpl: PutChar, Impl$$_module.Stream.PutChar
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc)
         ==> read($Heap, this, _module.Stream.footprint)[$Box($o)]);
    assume {:captureState "b7.dfy(75,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- b7.dfy(76,11)
    assume true;
    assert $_Frame[this, _module.Stream.stream];
    assume true;
    $rhs#0 := Seq#Append(read($Heap, this, _module.Stream.stream),
      Seq#Build(Seq#Empty(): Seq Box, $Box(x#0)));
    $Heap := update($Heap, this, _module.Stream.stream, $rhs#0);
    assume $IsGoodHeap($Heap);
    assume {:captureState "b7.dfy(76,25)"} true;
}



procedure CheckWellformed$$_module.Stream.GetChar(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Stream())
         && $IsAlloc(this, Tclass._module.Stream(), $Heap))
   returns (x#0: int);
  free requires 5 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.Stream.GetChar(this: ref) returns (x#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: GetChar, CheckWellformed$$_module.Stream.GetChar
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc)
         ==> read($Heap, this, _module.Stream.footprint)[$Box($o)]);
    assume {:captureState "b7.dfy(79,9): initial state"} true;
    assume _module.Stream.Valid#canCall($Heap, this);
    assume _module.Stream.Valid($Heap, this);
    assume 0 < Seq#Length(read($Heap, this, _module.Stream.stream));
    havoc $Heap;
    assume (forall<alpha> $o: ref, $f: Field alpha ::
      { read($Heap, $o, $f) }
      $o != null && read(old($Heap), $o, alloc)
         ==> read($Heap, $o, $f) == read(old($Heap), $o, $f)
           || read(old($Heap), this, _module.Stream.footprint)[$Box($o)]);
    assume $HeapSucc(old($Heap), $Heap);
    havoc x#0;
    assume {:captureState "b7.dfy(82,20): post-state"} true;
    assume _module.Stream.Valid#canCall($Heap, this);
    assume _module.Stream.Valid($Heap, this);
    assert $IsAlloc(this, Tclass._module.Stream(), old($Heap));
    assume (forall $o: ref ::
      { read(old($Heap), $o, alloc) }
      read($Heap, this, _module.Stream.footprint)[$Box($o)]
           && !read(old($Heap), this, _module.Stream.footprint)[$Box($o)]
         ==> $o != null && !read(old($Heap), $o, alloc));
    assert $IsAlloc(this, Tclass._module.Stream(), old($Heap));
    assert 0 <= LitInt(0)
       && LitInt(0) < Seq#Length(read(old($Heap), this, _module.Stream.stream));
    assume x#0
       == $Unbox(Seq#Index(read(old($Heap), this, _module.Stream.stream), LitInt(0))): int;
    assert $IsAlloc(this, Tclass._module.Stream(), old($Heap));
    assert 0 <= LitInt(1)
       && LitInt(1) <= Seq#Length(read(old($Heap), this, _module.Stream.stream));
    assume Seq#Equal(read($Heap, this, _module.Stream.stream),
      Seq#Drop(read(old($Heap), this, _module.Stream.stream), LitInt(1)));
}



procedure Call$$_module.Stream.GetChar(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Stream())
         && $IsAlloc(this, Tclass._module.Stream(), $Heap))
   returns (x#0: int);
  // user-defined preconditions
  requires _module.Stream.Valid#canCall($Heap, this)
     ==> _module.Stream.Valid($Heap, this)
       || !read($Heap, this, _module.Stream.footprint)[$Box(null)];
  requires _module.Stream.Valid#canCall($Heap, this)
     ==> _module.Stream.Valid($Heap, this)
       || read($Heap, this, _module.Stream.footprint)[$Box(this)];
  requires _module.Stream.Valid#canCall($Heap, this)
     ==> _module.Stream.Valid($Heap, this) || read($Heap, this, _module.Stream.isOpen);
  requires 0 < Seq#Length(read($Heap, this, _module.Stream.stream));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.Stream.Valid#canCall($Heap, this);
  free ensures _module.Stream.Valid#canCall($Heap, this)
     &&
    _module.Stream.Valid($Heap, this)
     &&
    !read($Heap, this, _module.Stream.footprint)[$Box(null)]
     && read($Heap, this, _module.Stream.footprint)[$Box(this)]
     && read($Heap, this, _module.Stream.isOpen);
  ensures (forall $o: ref ::
    { read(old($Heap), $o, alloc) }
    read($Heap, this, _module.Stream.footprint)[$Box($o)]
         && !read(old($Heap), this, _module.Stream.footprint)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures true;
  ensures x#0
     == $Unbox(Seq#Index(read(old($Heap), this, _module.Stream.stream), LitInt(0))): int;
  free ensures true;
  ensures Seq#Equal(read($Heap, this, _module.Stream.stream),
    Seq#Drop(read(old($Heap), this, _module.Stream.stream), LitInt(1)));
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f)
         || read(old($Heap), this, _module.Stream.footprint)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Stream.GetChar(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Stream())
         && $IsAlloc(this, Tclass._module.Stream(), $Heap))
   returns (x#0: int, $_reverifyPost: bool);
  free requires 5 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.Stream.Valid#canCall($Heap, this)
     &&
    _module.Stream.Valid($Heap, this)
     &&
    !read($Heap, this, _module.Stream.footprint)[$Box(null)]
     && read($Heap, this, _module.Stream.footprint)[$Box(this)]
     && read($Heap, this, _module.Stream.isOpen);
  requires 0 < Seq#Length(read($Heap, this, _module.Stream.stream));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.Stream.Valid#canCall($Heap, this);
  ensures _module.Stream.Valid#canCall($Heap, this)
     ==> _module.Stream.Valid($Heap, this)
       || !read($Heap, this, _module.Stream.footprint)[$Box(null)];
  ensures _module.Stream.Valid#canCall($Heap, this)
     ==> _module.Stream.Valid($Heap, this)
       || read($Heap, this, _module.Stream.footprint)[$Box(this)];
  ensures _module.Stream.Valid#canCall($Heap, this)
     ==> _module.Stream.Valid($Heap, this) || read($Heap, this, _module.Stream.isOpen);
  ensures (forall $o: ref ::
    { read(old($Heap), $o, alloc) }
    read($Heap, this, _module.Stream.footprint)[$Box($o)]
         && !read(old($Heap), this, _module.Stream.footprint)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures true;
  ensures x#0
     == $Unbox(Seq#Index(read(old($Heap), this, _module.Stream.stream), LitInt(0))): int;
  free ensures true;
  ensures Seq#Equal(read($Heap, this, _module.Stream.stream),
    Seq#Drop(read(old($Heap), this, _module.Stream.stream), LitInt(1)));
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f)
         || read(old($Heap), this, _module.Stream.footprint)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Stream.GetChar(this: ref) returns (x#0: int, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs#0: Seq Box where $Is($rhs#0, TSeq(TInt));

    // AddMethodImpl: GetChar, Impl$$_module.Stream.GetChar
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc)
         ==> read($Heap, this, _module.Stream.footprint)[$Box($o)]);
    assume {:captureState "b7.dfy(85,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- b7.dfy(86,7)
    assume true;
    assert 0 <= LitInt(0)
       && LitInt(0) < Seq#Length(read($Heap, this, _module.Stream.stream));
    assume true;
    x#0 := $Unbox(Seq#Index(read($Heap, this, _module.Stream.stream), LitInt(0))): int;
    assume {:captureState "b7.dfy(86,18)"} true;
    // ----- assignment statement ----- b7.dfy(87,12)
    assume true;
    assert $_Frame[this, _module.Stream.stream];
    assert 0 <= LitInt(1)
       && LitInt(1) <= Seq#Length(read($Heap, this, _module.Stream.stream));
    assume true;
    $rhs#0 := Seq#Drop(read($Heap, this, _module.Stream.stream), LitInt(1));
    $Heap := update($Heap, this, _module.Stream.stream, $rhs#0);
    assume $IsGoodHeap($Heap);
    assume {:captureState "b7.dfy(87,25)"} true;
}



procedure CheckWellformed$$_module.Stream.AtEndOfStream(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Stream())
         && $IsAlloc(this, Tclass._module.Stream(), $Heap))
   returns (eos#0: bool);
  free requires 6 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.Stream.AtEndOfStream(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Stream())
         && $IsAlloc(this, Tclass._module.Stream(), $Heap))
   returns (eos#0: bool);
  // user-defined preconditions
  requires _module.Stream.Valid#canCall($Heap, this)
     ==> _module.Stream.Valid($Heap, this)
       || !read($Heap, this, _module.Stream.footprint)[$Box(null)];
  requires _module.Stream.Valid#canCall($Heap, this)
     ==> _module.Stream.Valid($Heap, this)
       || read($Heap, this, _module.Stream.footprint)[$Box(this)];
  requires _module.Stream.Valid#canCall($Heap, this)
     ==> _module.Stream.Valid($Heap, this) || read($Heap, this, _module.Stream.isOpen);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures eos#0 <==> Seq#Length(read($Heap, this, _module.Stream.stream)) == LitInt(0);
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Stream.AtEndOfStream(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Stream())
         && $IsAlloc(this, Tclass._module.Stream(), $Heap))
   returns (eos#0: bool, $_reverifyPost: bool);
  free requires 6 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.Stream.Valid#canCall($Heap, this)
     &&
    _module.Stream.Valid($Heap, this)
     &&
    !read($Heap, this, _module.Stream.footprint)[$Box(null)]
     && read($Heap, this, _module.Stream.footprint)[$Box(this)]
     && read($Heap, this, _module.Stream.isOpen);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures eos#0 <==> Seq#Length(read($Heap, this, _module.Stream.stream)) == LitInt(0);
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Stream.AtEndOfStream(this: ref) returns (eos#0: bool, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: AtEndOfStream, Impl$$_module.Stream.AtEndOfStream
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "b7.dfy(93,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- b7.dfy(94,9)
    assume true;
    assume true;
    eos#0 := Seq#Length(read($Heap, this, _module.Stream.stream)) == LitInt(0);
    assume {:captureState "b7.dfy(94,24)"} true;
}



procedure CheckWellformed$$_module.Stream.Close(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Stream())
         && $IsAlloc(this, Tclass._module.Stream(), $Heap));
  free requires 7 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.Stream.Close(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Stream())
         && $IsAlloc(this, Tclass._module.Stream(), $Heap));
  // user-defined preconditions
  requires _module.Stream.Valid#canCall($Heap, this)
     ==> _module.Stream.Valid($Heap, this)
       || !read($Heap, this, _module.Stream.footprint)[$Box(null)];
  requires _module.Stream.Valid#canCall($Heap, this)
     ==> _module.Stream.Valid($Heap, this)
       || read($Heap, this, _module.Stream.footprint)[$Box(this)];
  requires _module.Stream.Valid#canCall($Heap, this)
     ==> _module.Stream.Valid($Heap, this) || read($Heap, this, _module.Stream.isOpen);
  modifies $Heap, $Tick;
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f)
         || read(old($Heap), this, _module.Stream.footprint)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Stream.Close(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Stream())
         && $IsAlloc(this, Tclass._module.Stream(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 7 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.Stream.Valid#canCall($Heap, this)
     &&
    _module.Stream.Valid($Heap, this)
     &&
    !read($Heap, this, _module.Stream.footprint)[$Box(null)]
     && read($Heap, this, _module.Stream.footprint)[$Box(this)]
     && read($Heap, this, _module.Stream.isOpen);
  modifies $Heap, $Tick;
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f)
         || read(old($Heap), this, _module.Stream.footprint)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Stream.Close(this: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs#0: bool;

    // AddMethodImpl: Close, Impl$$_module.Stream.Close
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc)
         ==> read($Heap, this, _module.Stream.footprint)[$Box($o)]);
    assume {:captureState "b7.dfy(100,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- b7.dfy(101,12)
    assume true;
    assert $_Frame[this, _module.Stream.isOpen];
    assume true;
    $rhs#0 := Lit(false);
    $Heap := update($Heap, this, _module.Stream.isOpen, $rhs#0);
    assume $IsGoodHeap($Heap);
    assume {:captureState "b7.dfy(101,19)"} true;
}



const unique class._module.Client: ClassName;

function Tclass._module.Client() : Ty;

// Tclass._module.Client Tag
axiom Tag(Tclass._module.Client()) == Tagclass._module.Client;

const unique Tagclass._module.Client: TyTag;

// Box/unbox axiom for Tclass._module.Client
axiom (forall bx: Box ::
  { $IsBox(bx, Tclass._module.Client()) }
  $IsBox(bx, Tclass._module.Client())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.Client()));

// Client: Class $Is
axiom (forall $o: ref ::
  { $Is($o, Tclass._module.Client()) }
  $Is($o, Tclass._module.Client())
     <==> $o == null || dtype($o) == Tclass._module.Client());

// Client: Class $IsAlloc
axiom (forall $o: ref, $h: Heap ::
  { $IsAlloc($o, Tclass._module.Client(), $h) }
  $IsAlloc($o, Tclass._module.Client(), $h) <==> $o == null || read($h, $o, alloc));

procedure CheckWellformed$$_module.Client.Sort(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Client())
         && $IsAlloc(this, Tclass._module.Client(), $Heap),
    q#0: ref
       where $Is(q#0, Tclass._module.Queue(TInt))
         && $IsAlloc(q#0, Tclass._module.Queue(TInt), $Heap))
   returns (r#0: ref
       where $Is(r#0, Tclass._module.Queue(TInt))
         && $IsAlloc(r#0, Tclass._module.Queue(TInt), $Heap));
  free requires 9 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.Client.Sort(this: ref, q#0: ref) returns (r#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var i#0: int;
  var j#0: int;
  var ##i#0: int;
  var ##i#1: int;

    // AddMethodImpl: Sort, CheckWellformed$$_module.Client.Sort
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> $o == q#0);
    assume {:captureState "b7.dfy(107,9): initial state"} true;
    assume q#0 != null;
    havoc $Heap;
    assume (forall<alpha> $o: ref, $f: Field alpha ::
      { read($Heap, $o, $f) }
      $o != null && read(old($Heap), $o, alloc)
         ==> read($Heap, $o, $f) == read(old($Heap), $o, $f) || $o == q#0);
    assume $HeapSucc(old($Heap), $Heap);
    havoc r#0;
    assume {:captureState "b7.dfy(110,22): post-state"} true;
    assume r#0 != null;
    assume r#0 != null && !read(old($Heap), r#0, alloc);
    assert r#0 != null;
    assert q#0 != null;
    assert $IsAlloc(q#0, Tclass._module.Queue(TInt), old($Heap));
    assume Seq#Length(read($Heap, r#0, _module.Queue.contents))
       == Seq#Length(read(old($Heap), q#0, _module.Queue.contents));
    havoc i#0;
    havoc j#0;
    if (*)
    {
        assume LitInt(0) <= i#0;
        assume i#0 < j#0;
        assert r#0 != null;
        assume j#0 < Seq#Length(read($Heap, r#0, _module.Queue.contents));
        assert r#0 != null;
        ##i#0 := i#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##i#0, TInt, $Heap);
        assert {:subsumption 0} LitInt(0) <= ##i#0;
        assert {:subsumption 0} ##i#0 < Seq#Length(read($Heap, r#0, _module.Queue.contents));
        assume LitInt(0) <= ##i#0
           && ##i#0 < Seq#Length(read($Heap, r#0, _module.Queue.contents));
        assume _module.Queue.Get#canCall(TInt, $Heap, r#0, i#0);
        assert r#0 != null;
        ##i#1 := j#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##i#1, TInt, $Heap);
        assert {:subsumption 0} LitInt(0) <= ##i#1;
        assert {:subsumption 0} ##i#1 < Seq#Length(read($Heap, r#0, _module.Queue.contents));
        assume LitInt(0) <= ##i#1
           && ##i#1 < Seq#Length(read($Heap, r#0, _module.Queue.contents));
        assume _module.Queue.Get#canCall(TInt, $Heap, r#0, j#0);
        assume $Unbox(_module.Queue.Get(TInt, $Heap, r#0, i#0)): int
           <= $Unbox(_module.Queue.Get(TInt, $Heap, r#0, j#0)): int;
    }
    else
    {
        assume LitInt(0) <= i#0
             && i#0 < j#0
             && j#0 < Seq#Length(read($Heap, r#0, _module.Queue.contents))
           ==> $Unbox(_module.Queue.Get(TInt, $Heap, r#0, i#0)): int
             <= $Unbox(_module.Queue.Get(TInt, $Heap, r#0, j#0)): int;
    }

    assume (forall i#1: int, j#1: int ::
      { $Unbox(_module.Queue.Get(TInt, $Heap, r#0, j#1)): int, $Unbox(_module.Queue.Get(TInt, $Heap, r#0, i#1)): int }
      true
         ==>
        LitInt(0) <= i#1
           && i#1 < j#1
           && j#1 < Seq#Length(read($Heap, r#0, _module.Queue.contents))
         ==> $Unbox(_module.Queue.Get(TInt, $Heap, r#0, i#1)): int
           <= $Unbox(_module.Queue.Get(TInt, $Heap, r#0, j#1)): int);
    assert r#0 != null;
    assert q#0 != null;
    assert $IsAlloc(q#0, Tclass._module.Queue(TInt), old($Heap));
    assume MultiSet#Equal(MultiSet#FromSeq(read($Heap, r#0, _module.Queue.contents)),
      MultiSet#FromSeq(read(old($Heap), q#0, _module.Queue.contents)));
}



procedure Call$$_module.Client.Sort(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Client())
         && $IsAlloc(this, Tclass._module.Client(), $Heap),
    q#0: ref
       where $Is(q#0, Tclass._module.Queue(TInt))
         && $IsAlloc(q#0, Tclass._module.Queue(TInt), $Heap))
   returns (r#0: ref
       where $Is(r#0, Tclass._module.Queue(TInt))
         && $IsAlloc(r#0, Tclass._module.Queue(TInt), $Heap));
  // user-defined preconditions
  requires q#0 != null;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures r#0 != null;
  ensures r#0 != null && !read(old($Heap), r#0, alloc);
  free ensures true;
  ensures Seq#Length(read($Heap, r#0, _module.Queue.contents))
     == Seq#Length(read(old($Heap), q#0, _module.Queue.contents));
  free ensures (forall i#1: int, j#1: int ::
    { $Unbox(_module.Queue.Get(TInt, $Heap, r#0, j#1)): int, $Unbox(_module.Queue.Get(TInt, $Heap, r#0, i#1)): int }
    LitInt(0) <= i#1
         && i#1 < j#1
         && j#1 < Seq#Length(read($Heap, r#0, _module.Queue.contents))
       ==> _module.Queue.Get#canCall(TInt, $Heap, r#0, i#1)
         && _module.Queue.Get#canCall(TInt, $Heap, r#0, j#1));
  ensures (forall i#1: int, j#1: int ::
    { $Unbox(_module.Queue.Get(TInt, $Heap, r#0, j#1)): int, $Unbox(_module.Queue.Get(TInt, $Heap, r#0, i#1)): int }
    true
       ==>
      LitInt(0) <= i#1
         && i#1 < j#1
         && j#1 < Seq#Length(read($Heap, r#0, _module.Queue.contents))
       ==> $Unbox(_module.Queue.Get(TInt, $Heap, r#0, i#1)): int
         <= $Unbox(_module.Queue.Get(TInt, $Heap, r#0, j#1)): int);
  free ensures true;
  ensures MultiSet#Equal(MultiSet#FromSeq(read($Heap, r#0, _module.Queue.contents)),
    MultiSet#FromSeq(read(old($Heap), q#0, _module.Queue.contents)));
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f) || $o == q#0);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure CheckWellformed$$_module.Client.Main(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Client())
         && $IsAlloc(this, Tclass._module.Client(), $Heap));
  free requires 12 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.Client.Main(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Client())
         && $IsAlloc(this, Tclass._module.Client(), $Heap));
  modifies $Heap, $Tick;
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Client.Main(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Client())
         && $IsAlloc(this, Tclass._module.Client(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 12 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Client.Main(this: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var rd#0: ref
     where $Is(rd#0, Tclass._module.Stream())
       && $IsAlloc(rd#0, Tclass._module.Stream(), $Heap);
  var $nw: ref;
  var q#0: ref
     where $Is(q#0, Tclass._module.Queue(TInt))
       && $IsAlloc(q#0, Tclass._module.Queue(TInt), $Heap);
  var $PreLoopHeap$loop#0: Heap;
  var $decr_init$loop#00: int;
  var $w$loop#0: bool;
  var $decr$loop#00: int;
  var eos#0_0: bool;
  var $rhs##0_0: bool;
  var ch#0_0: int;
  var $rhs##0_1: int;
  var x##0_0: Box;
  var $rhs##0: ref
     where $Is($rhs##0, Tclass._module.Queue(TInt))
       && $IsAlloc($rhs##0, Tclass._module.Queue(TInt), $Heap);
  var q##0: ref;
  var wr#0: ref
     where $Is(wr#0, Tclass._module.Stream())
       && $IsAlloc(wr#0, Tclass._module.Stream(), $Heap);
  var $PreLoopHeap$loop#1: Heap;
  var $decr_init$loop#10: int;
  var $w$loop#1: bool;
  var $decr$loop#10: int;
  var ch#1_0: int;
  var $rhs##1_0: int;
  var $tmp##1_0: Box;
  var x##1_0: int;

    // AddMethodImpl: Main, Impl$$_module.Client.Main
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "b7.dfy(117,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- b7.dfy(118,12)
    assume true;
    havoc $nw;
    assume $nw != null && !read($Heap, $nw, alloc) && dtype($nw) == Tclass._module.Stream();
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    rd#0 := $nw;
    assume {:captureState "b7.dfy(118,24)"} true;
    // ----- call statement ----- b7.dfy(119,12)
    // TrCallStmt: Before ProcessCallStmt
    assert rd#0 != null;
    assert (forall<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) && $o == rd#0 ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.Stream.Open(rd#0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "b7.dfy(119,13)"} true;
    // ----- assignment statement ----- b7.dfy(121,11)
    assume true;
    havoc $nw;
    assume $nw != null
       &&
      !read($Heap, $nw, alloc)
       && dtype($nw) == Tclass._module.Queue(TInt);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    q#0 := $nw;
    assume {:captureState "b7.dfy(121,27)"} true;
    // ----- while statement ----- b7.dfy(122,5)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    $decr_init$loop#00 := Seq#Length(read($Heap, rd#0, _module.Stream.stream));
    havoc $w$loop#0;
    while (true)
      free invariant $w$loop#0 ==> _module.Stream.Valid#canCall($Heap, rd#0);
      invariant $w$loop#0
         ==>
        _module.Stream.Valid#canCall($Heap, rd#0)
         ==> _module.Stream.Valid($Heap, rd#0)
           || !read($Heap, rd#0, _module.Stream.footprint)[$Box(null)];
      invariant $w$loop#0
         ==>
        _module.Stream.Valid#canCall($Heap, rd#0)
         ==> _module.Stream.Valid($Heap, rd#0)
           || read($Heap, rd#0, _module.Stream.footprint)[$Box(rd#0)];
      invariant $w$loop#0
         ==>
        _module.Stream.Valid#canCall($Heap, rd#0)
         ==> _module.Stream.Valid($Heap, rd#0) || read($Heap, rd#0, _module.Stream.isOpen);
      free invariant $w$loop#0
         ==> _module.Stream.Valid#canCall($Heap, rd#0)
           &&
          _module.Stream.Valid($Heap, rd#0)
           &&
          !read($Heap, rd#0, _module.Stream.footprint)[$Box(null)]
           && read($Heap, rd#0, _module.Stream.footprint)[$Box(rd#0)]
           && read($Heap, rd#0, _module.Stream.isOpen);
      invariant $w$loop#0
         ==> (forall $o: ref ::
          { read($Heap, rd#0, _module.Stream.footprint)[$Box($o)] }
          read($Heap, rd#0, _module.Stream.footprint)[$Box($o)]
             ==> $o != null && !read(old($Heap), $o, alloc));
      invariant $w$loop#0 ==> q#0 != null && !read(old($Heap), q#0, alloc);
      free invariant (forall<alpha> $o: ref, $f: Field alpha ::
        { read($Heap, $o, $f) }
        $o != null && read(old($Heap), $o, alloc)
           ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0, $o, $f));
      free invariant $HeapSucc($PreLoopHeap$loop#0, $Heap);
      free invariant (forall<alpha> $o: ref, $f: Field alpha ::
        { read($Heap, $o, $f) }
        $o != null && read($PreLoopHeap$loop#0, $o, alloc)
           ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0, $o, $f) || $_Frame[$o, $f]);
      free invariant Seq#Length(read($Heap, rd#0, _module.Stream.stream)) <= $decr_init$loop#00
         && (Seq#Length(read($Heap, rd#0, _module.Stream.stream)) == $decr_init$loop#00
           ==> true);
    {
        assume {:captureState "b7.dfy(122,4): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            assert {:subsumption 0} rd#0 != null;
            assume _module.Stream.Valid#canCall($Heap, rd#0);
            if (_module.Stream.Valid($Heap, rd#0))
            {
                assert {:subsumption 0} rd#0 != null;
            }

            if (_module.Stream.Valid($Heap, rd#0)
               && (forall $o: ref ::
                { read($Heap, rd#0, _module.Stream.footprint)[$Box($o)] }
                read($Heap, rd#0, _module.Stream.footprint)[$Box($o)]
                   ==> $o != null && !read(old($Heap), $o, alloc)))
            {
            }

            assume _module.Stream.Valid#canCall($Heap, rd#0);
            assume _module.Stream.Valid($Heap, rd#0)
               && (forall $o: ref ::
                { read($Heap, rd#0, _module.Stream.footprint)[$Box($o)] }
                read($Heap, rd#0, _module.Stream.footprint)[$Box($o)]
                   ==> $o != null && !read(old($Heap), $o, alloc))
               &&
              q#0 != null
               && !read(old($Heap), q#0, alloc);
            assert rd#0 != null;
            assume true;
            assume false;
        }

        assume true;
        if (!Lit(true))
        {
            break;
        }

        $decr$loop#00 := Seq#Length(read($Heap, rd#0, _module.Stream.stream));
        // ----- call statement ----- b7.dfy(126,34)
        assume true;
        // TrCallStmt: Adding lhs Microsoft.Dafny.AutoGhostIdentifierExpr with type bool
        // TrCallStmt: Before ProcessCallStmt
        assert rd#0 != null;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call $rhs##0_0 := Call$$_module.Stream.AtEndOfStream(rd#0);
        // TrCallStmt: After ProcessCallStmt
        eos#0_0 := $rhs##0_0;
        assume {:captureState "b7.dfy(126,35)"} true;
        // ----- if statement ----- b7.dfy(127,7)
        assume true;
        if (eos#0_0)
        {
            // ----- break statement ----- b7.dfy(128,9)
            goto after_0_0_0;
        }
        else
        {
        }

        // ----- call statement ----- b7.dfy(131,27)
        assume true;
        // TrCallStmt: Adding lhs Microsoft.Dafny.AutoGhostIdentifierExpr with type int
        // TrCallStmt: Before ProcessCallStmt
        assert rd#0 != null;
        assert (forall<alpha> $o: ref, $f: Field alpha ::
          $o != null
               && read($Heap, $o, alloc)
               && read($Heap, rd#0, _module.Stream.footprint)[$Box($o)]
             ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call $rhs##0_1 := Call$$_module.Stream.GetChar(rd#0);
        // TrCallStmt: After ProcessCallStmt
        ch#0_0 := $rhs##0_1;
        assume {:captureState "b7.dfy(131,28)"} true;
        // ----- call statement ----- b7.dfy(132,16)
        // TrCallStmt: Before ProcessCallStmt
        assert q#0 != null;
        assume true;
        // ProcessCallStmt: CheckSubrange
        x##0_0 := $Box(ch#0_0);
        assert (forall<alpha> $o: ref, $f: Field alpha ::
          $o != null && read($Heap, $o, alloc) && $o == q#0 ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$_module.Queue.Enqueue(TInt, q#0, x##0_0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "b7.dfy(132,19)"} true;
        // ----- loop termination check ----- b7.dfy(122,5)
        assert 0 <= $decr$loop#00
           || Seq#Length(read($Heap, rd#0, _module.Stream.stream)) == $decr$loop#00;
        assert Seq#Length(read($Heap, rd#0, _module.Stream.stream)) < $decr$loop#00;
        assume _module.Stream.Valid#canCall($Heap, rd#0);
    }

  after_0_0_0:
    // ----- call statement ----- b7.dfy(135,13)
    // TrCallStmt: Before ProcessCallStmt
    assert rd#0 != null;
    assert (forall<alpha> $o: ref, $f: Field alpha ::
      $o != null
           && read($Heap, $o, alloc)
           && read($Heap, rd#0, _module.Stream.footprint)[$Box($o)]
         ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.Stream.Close(rd#0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "b7.dfy(135,14)"} true;
    // ----- call statement ----- b7.dfy(136,14)
    assume true;
    // TrCallStmt: Adding lhs Microsoft.Dafny.IdentifierExpr with type Queue<int>
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    q##0 := q#0;
    assert (forall<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) && $o == q##0 ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##0 := Call$$_module.Client.Sort(this, q##0);
    // TrCallStmt: After ProcessCallStmt
    q#0 := $rhs##0;
    assume {:captureState "b7.dfy(136,16)"} true;
    // ----- assignment statement ----- b7.dfy(138,12)
    assume true;
    havoc $nw;
    assume $nw != null && !read($Heap, $nw, alloc) && dtype($nw) == Tclass._module.Stream();
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    wr#0 := $nw;
    assume {:captureState "b7.dfy(138,24)"} true;
    // ----- call statement ----- b7.dfy(139,14)
    // TrCallStmt: Before ProcessCallStmt
    assert wr#0 != null;
    assert (forall<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) && $o == wr#0 ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.Stream.Create(wr#0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "b7.dfy(139,15)"} true;
    // ----- while statement ----- b7.dfy(140,5)
    // Assume Fuel Constant
    $PreLoopHeap$loop#1 := $Heap;
    $decr_init$loop#10 := Seq#Length(read($Heap, q#0, _module.Queue.contents)) - 0;
    havoc $w$loop#1;
    while (true)
      free invariant $w$loop#1 ==> _module.Stream.Valid#canCall($Heap, wr#0);
      invariant $w$loop#1
         ==>
        _module.Stream.Valid#canCall($Heap, wr#0)
         ==> _module.Stream.Valid($Heap, wr#0)
           || !read($Heap, wr#0, _module.Stream.footprint)[$Box(null)];
      invariant $w$loop#1
         ==>
        _module.Stream.Valid#canCall($Heap, wr#0)
         ==> _module.Stream.Valid($Heap, wr#0)
           || read($Heap, wr#0, _module.Stream.footprint)[$Box(wr#0)];
      invariant $w$loop#1
         ==>
        _module.Stream.Valid#canCall($Heap, wr#0)
         ==> _module.Stream.Valid($Heap, wr#0) || read($Heap, wr#0, _module.Stream.isOpen);
      free invariant $w$loop#1
         ==> _module.Stream.Valid#canCall($Heap, wr#0)
           &&
          _module.Stream.Valid($Heap, wr#0)
           &&
          !read($Heap, wr#0, _module.Stream.footprint)[$Box(null)]
           && read($Heap, wr#0, _module.Stream.footprint)[$Box(wr#0)]
           && read($Heap, wr#0, _module.Stream.isOpen);
      invariant $w$loop#1
         ==> (forall $o: ref ::
          { read($Heap, wr#0, _module.Stream.footprint)[$Box($o)] }
          read($Heap, wr#0, _module.Stream.footprint)[$Box($o)]
             ==> $o != null && !read(old($Heap), $o, alloc));
      invariant $w$loop#1 ==> q#0 != null && !read(old($Heap), q#0, alloc);
      invariant $w$loop#1 ==> !read($Heap, wr#0, _module.Stream.footprint)[$Box(q#0)];
      free invariant (forall<alpha> $o: ref, $f: Field alpha ::
        { read($Heap, $o, $f) }
        $o != null && read(old($Heap), $o, alloc)
           ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#1, $o, $f));
      free invariant $HeapSucc($PreLoopHeap$loop#1, $Heap);
      free invariant (forall<alpha> $o: ref, $f: Field alpha ::
        { read($Heap, $o, $f) }
        $o != null && read($PreLoopHeap$loop#1, $o, alloc)
           ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#1, $o, $f) || $_Frame[$o, $f]);
      free invariant Seq#Length(read($Heap, q#0, _module.Queue.contents)) - 0 <= $decr_init$loop#10
         && (Seq#Length(read($Heap, q#0, _module.Queue.contents)) - 0 == $decr_init$loop#10
           ==> true);
    {
        assume {:captureState "b7.dfy(140,4): after some loop iterations"} true;
        if (!$w$loop#1)
        {
            assert {:subsumption 0} wr#0 != null;
            assume _module.Stream.Valid#canCall($Heap, wr#0);
            if (_module.Stream.Valid($Heap, wr#0))
            {
                assert {:subsumption 0} wr#0 != null;
            }

            if (_module.Stream.Valid($Heap, wr#0)
               && (forall $o: ref ::
                { read($Heap, wr#0, _module.Stream.footprint)[$Box($o)] }
                read($Heap, wr#0, _module.Stream.footprint)[$Box($o)]
                   ==> $o != null && !read(old($Heap), $o, alloc)))
            {
            }

            if (_module.Stream.Valid($Heap, wr#0)
               && (forall $o: ref ::
                { read($Heap, wr#0, _module.Stream.footprint)[$Box($o)] }
                read($Heap, wr#0, _module.Stream.footprint)[$Box($o)]
                   ==> $o != null && !read(old($Heap), $o, alloc))
               &&
              q#0 != null
               && !read(old($Heap), q#0, alloc))
            {
                assert {:subsumption 0} wr#0 != null;
            }

            assume _module.Stream.Valid#canCall($Heap, wr#0);
            assume _module.Stream.Valid($Heap, wr#0)
               && (forall $o: ref ::
                { read($Heap, wr#0, _module.Stream.footprint)[$Box($o)] }
                read($Heap, wr#0, _module.Stream.footprint)[$Box($o)]
                   ==> $o != null && !read(old($Heap), $o, alloc))
               &&
              q#0 != null
               && !read(old($Heap), q#0, alloc)
               && !read($Heap, wr#0, _module.Stream.footprint)[$Box(q#0)];
            assert q#0 != null;
            assume true;
            assume false;
        }

        assert q#0 != null;
        assume true;
        if (Seq#Length(read($Heap, q#0, _module.Queue.contents)) <= 0)
        {
            break;
        }

        $decr$loop#10 := Seq#Length(read($Heap, q#0, _module.Queue.contents)) - 0;
        // ----- call statement ----- b7.dfy(143,26)
        assume true;
        // TrCallStmt: Adding lhs Microsoft.Dafny.AutoGhostIdentifierExpr with type int
        // TrCallStmt: Before ProcessCallStmt
        assert q#0 != null;
        assert (forall<alpha> $o: ref, $f: Field alpha ::
          $o != null && read($Heap, $o, alloc) && $o == q#0 ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call $tmp##1_0 := Call$$_module.Queue.Dequeue(TInt, q#0);
        havoc $rhs##1_0;
        assume $rhs##1_0 == $Unbox($tmp##1_0): int;
        // TrCallStmt: After ProcessCallStmt
        ch#1_0 := $rhs##1_0;
        assume {:captureState "b7.dfy(143,27)"} true;
        // ----- call statement ----- b7.dfy(144,17)
        // TrCallStmt: Before ProcessCallStmt
        assert wr#0 != null;
        assume true;
        // ProcessCallStmt: CheckSubrange
        x##1_0 := ch#1_0;
        assert (forall<alpha> $o: ref, $f: Field alpha ::
          $o != null
               && read($Heap, $o, alloc)
               && read($Heap, wr#0, _module.Stream.footprint)[$Box($o)]
             ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$_module.Stream.PutChar(wr#0, x##1_0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "b7.dfy(144,20)"} true;
        // ----- loop termination check ----- b7.dfy(140,5)
        assert 0 <= $decr$loop#10
           || Seq#Length(read($Heap, q#0, _module.Queue.contents)) - 0 == $decr$loop#10;
        assert Seq#Length(read($Heap, q#0, _module.Queue.contents)) - 0 < $decr$loop#10;
        assume _module.Stream.Valid#canCall($Heap, wr#0);
    }

    // ----- call statement ----- b7.dfy(146,13)
    // TrCallStmt: Before ProcessCallStmt
    assert wr#0 != null;
    assert (forall<alpha> $o: ref, $f: Field alpha ::
      $o != null
           && read($Heap, $o, alloc)
           && read($Heap, wr#0, _module.Stream.footprint)[$Box($o)]
         ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.Stream.Close(wr#0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "b7.dfy(146,14)"} true;
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

const unique field$contents: NameFamily;

const unique field$footprint: NameFamily;

const unique field$stream: NameFamily;

const unique field$isOpen: NameFamily;