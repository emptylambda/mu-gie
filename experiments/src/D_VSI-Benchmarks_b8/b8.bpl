// Dafny 2.0.0.00922 technical preview 0
// Command Line Options: /compile:0 /noVerify /print:b8.bpl b8.dfy

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

const unique class._module.Maybe: ClassName;

// Constructor function declaration
function #_module.Maybe.None() : DatatypeType;

const unique ##_module.Maybe.None: DtCtorId;

// Constructor identifier
axiom DatatypeCtorId(#_module.Maybe.None()) == ##_module.Maybe.None;

function _module.Maybe.None_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType ::
  { _module.Maybe.None_q(d) }
  _module.Maybe.None_q(d) <==> DatatypeCtorId(d) == ##_module.Maybe.None);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType ::
  { _module.Maybe.None_q(d) }
  _module.Maybe.None_q(d) ==> d == #_module.Maybe.None());

function Tclass._module.Maybe(Ty) : Ty;

// Tclass._module.Maybe Tag
axiom (forall _module.Maybe$T: Ty ::
  { Tclass._module.Maybe(_module.Maybe$T) }
  Tag(Tclass._module.Maybe(_module.Maybe$T)) == Tagclass._module.Maybe);

const unique Tagclass._module.Maybe: TyTag;

// Tclass._module.Maybe injectivity 0
axiom (forall _module.Maybe$T: Ty ::
  { Tclass._module.Maybe(_module.Maybe$T) }
  Tclass._module.Maybe_0(Tclass._module.Maybe(_module.Maybe$T)) == _module.Maybe$T);

function Tclass._module.Maybe_0(Ty) : Ty;

// Box/unbox axiom for Tclass._module.Maybe
axiom (forall _module.Maybe$T: Ty, bx: Box ::
  { $IsBox(bx, Tclass._module.Maybe(_module.Maybe$T)) }
  $IsBox(bx, Tclass._module.Maybe(_module.Maybe$T))
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.Maybe(_module.Maybe$T)));

// Constructor $Is
axiom (forall _module.Maybe$T: Ty ::
  { $Is(#_module.Maybe.None(), Tclass._module.Maybe(_module.Maybe$T)) }
  $Is(#_module.Maybe.None(), Tclass._module.Maybe(_module.Maybe$T)));

// Constructor $IsAlloc
axiom (forall _module.Maybe$T: Ty, $h: Heap ::
  { $IsAlloc(#_module.Maybe.None(), Tclass._module.Maybe(_module.Maybe$T), $h) }
  $IsGoodHeap($h)
     ==> $IsAlloc(#_module.Maybe.None(), Tclass._module.Maybe(_module.Maybe$T), $h));

// Constructor literal
axiom #_module.Maybe.None() == Lit(#_module.Maybe.None());

// Constructor function declaration
function #_module.Maybe.Some(Box) : DatatypeType;

const unique ##_module.Maybe.Some: DtCtorId;

// Constructor identifier
axiom (forall a#19#0#0: Box ::
  { #_module.Maybe.Some(a#19#0#0) }
  DatatypeCtorId(#_module.Maybe.Some(a#19#0#0)) == ##_module.Maybe.Some);

function _module.Maybe.Some_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType ::
  { _module.Maybe.Some_q(d) }
  _module.Maybe.Some_q(d) <==> DatatypeCtorId(d) == ##_module.Maybe.Some);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType ::
  { _module.Maybe.Some_q(d) }
  _module.Maybe.Some_q(d)
     ==> (exists a#20#0#0: Box :: d == #_module.Maybe.Some(a#20#0#0)));

// Constructor $Is
axiom (forall _module.Maybe$T: Ty, a#21#0#0: Box ::
  { $Is(#_module.Maybe.Some(a#21#0#0), Tclass._module.Maybe(_module.Maybe$T)) }
  $Is(#_module.Maybe.Some(a#21#0#0), Tclass._module.Maybe(_module.Maybe$T))
     <==> $IsBox(a#21#0#0, _module.Maybe$T));

// Constructor $IsAlloc
axiom (forall _module.Maybe$T: Ty, a#22#0#0: Box, $h: Heap ::
  { $IsAlloc(#_module.Maybe.Some(a#22#0#0), Tclass._module.Maybe(_module.Maybe$T), $h) }
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Maybe.Some(a#22#0#0), Tclass._module.Maybe(_module.Maybe$T), $h)
       <==> $IsAllocBox(a#22#0#0, _module.Maybe$T, $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, _module.Maybe$T: Ty, $h: Heap ::
  { $IsAllocBox(_module.Maybe.get(d), _module.Maybe$T, $h) }
  $IsGoodHeap($h)
       &&
      _module.Maybe.Some_q(d)
       && $IsAlloc(d, Tclass._module.Maybe(_module.Maybe$T), $h)
     ==> $IsAllocBox(_module.Maybe.get(d), _module.Maybe$T, $h));

// Constructor literal
axiom (forall a#23#0#0: Box ::
  { #_module.Maybe.Some(Lit(a#23#0#0)) }
  #_module.Maybe.Some(Lit(a#23#0#0)) == Lit(#_module.Maybe.Some(a#23#0#0)));

function _module.Maybe.get(DatatypeType) : Box;

// Constructor injectivity
axiom (forall a#24#0#0: Box ::
  { #_module.Maybe.Some(a#24#0#0) }
  _module.Maybe.get(#_module.Maybe.Some(a#24#0#0)) == a#24#0#0);

// Inductive rank
axiom (forall a#25#0#0: Box ::
  { #_module.Maybe.Some(a#25#0#0) }
  BoxRank(a#25#0#0) < DtRank(#_module.Maybe.Some(a#25#0#0)));

// One-depth case-split function
function $IsA#_module.Maybe(DatatypeType) : bool;

// One-depth case-split axiom
axiom (forall d: DatatypeType ::
  { $IsA#_module.Maybe(d) }
  $IsA#_module.Maybe(d) ==> _module.Maybe.None_q(d) || _module.Maybe.Some_q(d));

// Questionmark data type disjunctivity
axiom (forall _module.Maybe$T: Ty, d: DatatypeType ::
  { _module.Maybe.Some_q(d), $Is(d, Tclass._module.Maybe(_module.Maybe$T)) }
    { _module.Maybe.None_q(d), $Is(d, Tclass._module.Maybe(_module.Maybe$T)) }
  $Is(d, Tclass._module.Maybe(_module.Maybe$T))
     ==> _module.Maybe.None_q(d) || _module.Maybe.Some_q(d));

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
  free requires 7 == $FunctionContextHeight;
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
  free requires 13 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.Queue.Enqueue(_module.Queue$T: Ty, this: ref, x#0: Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: Enqueue, CheckWellformed$$_module.Queue.Enqueue
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> $o == this);
    assume {:captureState "b8.dfy(17,9): initial state"} true;
    havoc $Heap;
    assume (forall<alpha> $o: ref, $f: Field alpha ::
      { read($Heap, $o, $f) }
      $o != null && read(old($Heap), $o, alloc)
         ==> read($Heap, $o, $f) == read(old($Heap), $o, $f) || $o == this);
    assume $HeapSucc(old($Heap), $Heap);
    assume {:captureState "b8.dfy(19,21): post-state"} true;
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
  free requires 17 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.Queue.Dequeue(_module.Queue$T: Ty, this: ref) returns (x#0: Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: Dequeue, CheckWellformed$$_module.Queue.Dequeue
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> $o == this);
    assume {:captureState "b8.dfy(20,9): initial state"} true;
    assume 0 < Seq#Length(read($Heap, this, _module.Queue.contents));
    havoc $Heap;
    assume (forall<alpha> $o: ref, $f: Field alpha ::
      { read($Heap, $o, $f) }
      $o != null && read(old($Heap), $o, alloc)
         ==> read($Heap, $o, $f) == read(old($Heap), $o, $f) || $o == this);
    assume $HeapSucc(old($Heap), $Heap);
    havoc x#0;
    assume {:captureState "b8.dfy(23,43): post-state"} true;
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
axiom 25 <= $FunctionContextHeight
   ==> (forall _module.Queue$T: Ty, $Heap: Heap, this: ref ::
    { _module.Queue.Head(_module.Queue$T, $Heap, this) }
    _module.Queue.Head#canCall(_module.Queue$T, $Heap, this)
         || (25 != $FunctionContextHeight
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
axiom 25 <= $FunctionContextHeight
   ==> (forall _module.Queue$T: Ty, $Heap: Heap, this: ref ::
    { _module.Queue.Head(_module.Queue$T, $Heap, this) }
    _module.Queue.Head#canCall(_module.Queue$T, $Heap, this)
         || (25 != $FunctionContextHeight
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
  free requires 25 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.Queue.Head(_module.Queue$T: Ty, this: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function Head
    assume {:captureState "b8.dfy(24,18): initial state"} true;
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
axiom 0 <= $FunctionContextHeight
   ==> (forall _module.Queue$T: Ty, $Heap: Heap, this: ref, i#0: int ::
    { _module.Queue.Get(_module.Queue$T, $Heap, this, i#0) }
    _module.Queue.Get#canCall(_module.Queue$T, $Heap, this, i#0)
         || (0 != $FunctionContextHeight
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
axiom 0 <= $FunctionContextHeight
   ==> (forall _module.Queue$T: Ty, $Heap: Heap, this: ref, i#0: int ::
    { _module.Queue.Get(_module.Queue$T, $Heap, this, i#0) }
    _module.Queue.Get#canCall(_module.Queue$T, $Heap, this, i#0)
         || (0 != $FunctionContextHeight
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
  free requires 0 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.Queue.Get(_module.Queue$T: Ty, this: ref, i#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function Get
    assume {:captureState "b8.dfy(28,18): initial state"} true;
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



const unique class._module.Glossary: ClassName;

function Tclass._module.Glossary() : Ty;

// Tclass._module.Glossary Tag
axiom Tag(Tclass._module.Glossary()) == Tagclass._module.Glossary;

const unique Tagclass._module.Glossary: TyTag;

// Box/unbox axiom for Tclass._module.Glossary
axiom (forall bx: Box ::
  { $IsBox(bx, Tclass._module.Glossary()) }
  $IsBox(bx, Tclass._module.Glossary())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.Glossary()));

// Glossary: Class $Is
axiom (forall $o: ref ::
  { $Is($o, Tclass._module.Glossary()) }
  $Is($o, Tclass._module.Glossary())
     <==> $o == null || dtype($o) == Tclass._module.Glossary());

// Glossary: Class $IsAlloc
axiom (forall $o: ref, $h: Heap ::
  { $IsAlloc($o, Tclass._module.Glossary(), $h) }
  $IsAlloc($o, Tclass._module.Glossary(), $h)
     <==> $o == null || read($h, $o, alloc));

function Tclass._module.Word() : Ty;

// Tclass._module.Word Tag
axiom Tag(Tclass._module.Word()) == Tagclass._module.Word;

const unique Tagclass._module.Word: TyTag;

// Box/unbox axiom for Tclass._module.Word
axiom (forall bx: Box ::
  { $IsBox(bx, Tclass._module.Word()) }
  $IsBox(bx, Tclass._module.Word())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.Word()));

procedure CheckWellformed$$_module.Glossary.Sort(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Glossary())
         && $IsAlloc(this, Tclass._module.Glossary(), $Heap),
    q#0: ref
       where $Is(q#0, Tclass._module.Queue(Tclass._module.Word()))
         && $IsAlloc(q#0, Tclass._module.Queue(Tclass._module.Word()), $Heap))
   returns (r#0: ref
       where $Is(r#0, Tclass._module.Queue(Tclass._module.Word()))
         && $IsAlloc(r#0, Tclass._module.Queue(Tclass._module.Word()), $Heap));
  free requires 2 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.Glossary.Sort(this: ref, q#0: ref) returns (r#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var i#0: int;
  var j#0: int;
  var ##i#0: int;
  var ##i#1: int;
  var ##i#2: int;
  var ##w#0: ref;

    // AddMethodImpl: Sort, CheckWellformed$$_module.Glossary.Sort
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> $o == q#0);
    assume {:captureState "b8.dfy(36,9): initial state"} true;
    assume q#0 != null;
    havoc $Heap;
    assume (forall<alpha> $o: ref, $f: Field alpha ::
      { read($Heap, $o, $f) }
      $o != null && read(old($Heap), $o, alloc)
         ==> read($Heap, $o, $f) == read(old($Heap), $o, $f) || $o == q#0);
    assume $HeapSucc(old($Heap), $Heap);
    havoc r#0;
    assume {:captureState "b8.dfy(39,22): post-state"} true;
    assume r#0 != null;
    assume r#0 != null && !read(old($Heap), r#0, alloc);
    assert r#0 != null;
    assert q#0 != null;
    assert $IsAlloc(q#0, Tclass._module.Queue(Tclass._module.Word()), old($Heap));
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
        assume _module.Queue.Get#canCall(Tclass._module.Word(), $Heap, r#0, i#0);
        assume $Unbox(_module.Queue.Get(Tclass._module.Word(), $Heap, r#0, i#0)): ref != null;
        assert r#0 != null;
        ##i#1 := i#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##i#1, TInt, $Heap);
        assert {:subsumption 0} LitInt(0) <= ##i#1;
        assert {:subsumption 0} ##i#1 < Seq#Length(read($Heap, r#0, _module.Queue.contents));
        assume LitInt(0) <= ##i#1
           && ##i#1 < Seq#Length(read($Heap, r#0, _module.Queue.contents));
        assume _module.Queue.Get#canCall(Tclass._module.Word(), $Heap, r#0, i#0);
        assert $Unbox(_module.Queue.Get(Tclass._module.Word(), $Heap, r#0, i#0)): ref != null;
        assert r#0 != null;
        ##i#2 := j#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##i#2, TInt, $Heap);
        assert {:subsumption 0} LitInt(0) <= ##i#2;
        assert {:subsumption 0} ##i#2 < Seq#Length(read($Heap, r#0, _module.Queue.contents));
        assume LitInt(0) <= ##i#2
           && ##i#2 < Seq#Length(read($Heap, r#0, _module.Queue.contents));
        assume _module.Queue.Get#canCall(Tclass._module.Word(), $Heap, r#0, j#0);
        ##w#0 := $Unbox(_module.Queue.Get(Tclass._module.Word(), $Heap, r#0, j#0)): ref;
        // assume allocatedness for argument to function
        assume $IsAlloc(##w#0, Tclass._module.Word(), $Heap);
        assume _module.Word.AtMost#canCall($Unbox(_module.Queue.Get(Tclass._module.Word(), $Heap, r#0, i#0)): ref,
          $Unbox(_module.Queue.Get(Tclass._module.Word(), $Heap, r#0, j#0)): ref);
        assume _module.Word.AtMost($Unbox(_module.Queue.Get(Tclass._module.Word(), $Heap, r#0, i#0)): ref,
          $Unbox(_module.Queue.Get(Tclass._module.Word(), $Heap, r#0, j#0)): ref);
    }
    else
    {
        assume LitInt(0) <= i#0
             && i#0 < j#0
             && j#0 < Seq#Length(read($Heap, r#0, _module.Queue.contents))
           ==> $Unbox(_module.Queue.Get(Tclass._module.Word(), $Heap, r#0, i#0)): ref != null
             && _module.Word.AtMost($Unbox(_module.Queue.Get(Tclass._module.Word(), $Heap, r#0, i#0)): ref,
              $Unbox(_module.Queue.Get(Tclass._module.Word(), $Heap, r#0, j#0)): ref);
    }

    assume (forall i#1: int, j#1: int ::
      { $Unbox(_module.Queue.Get(Tclass._module.Word(), $Heap, r#0, j#1)): ref, $Unbox(_module.Queue.Get(Tclass._module.Word(), $Heap, r#0, i#1)): ref }
      true
         ==> (LitInt(0) <= i#1
               && i#1 < j#1
               && j#1 < Seq#Length(read($Heap, r#0, _module.Queue.contents))
             ==> $Unbox(_module.Queue.Get(Tclass._module.Word(), $Heap, r#0, i#1)): ref != null)
           && (LitInt(0) <= i#1
               && i#1 < j#1
               && j#1 < Seq#Length(read($Heap, r#0, _module.Queue.contents))
             ==> _module.Word.AtMost($Unbox(_module.Queue.Get(Tclass._module.Word(), $Heap, r#0, i#1)): ref,
              $Unbox(_module.Queue.Get(Tclass._module.Word(), $Heap, r#0, j#1)): ref)));
    assert r#0 != null;
    assert q#0 != null;
    assert $IsAlloc(q#0, Tclass._module.Queue(Tclass._module.Word()), old($Heap));
    assume MultiSet#Equal(MultiSet#FromSeq(read($Heap, r#0, _module.Queue.contents)),
      MultiSet#FromSeq(read(old($Heap), q#0, _module.Queue.contents)));
}



procedure Call$$_module.Glossary.Sort(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Glossary())
         && $IsAlloc(this, Tclass._module.Glossary(), $Heap),
    q#0: ref
       where $Is(q#0, Tclass._module.Queue(Tclass._module.Word()))
         && $IsAlloc(q#0, Tclass._module.Queue(Tclass._module.Word()), $Heap))
   returns (r#0: ref
       where $Is(r#0, Tclass._module.Queue(Tclass._module.Word()))
         && $IsAlloc(r#0, Tclass._module.Queue(Tclass._module.Word()), $Heap));
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
    { $Unbox(_module.Queue.Get(Tclass._module.Word(), $Heap, r#0, j#1)): ref, $Unbox(_module.Queue.Get(Tclass._module.Word(), $Heap, r#0, i#1)): ref }
    (j#1 < Seq#Length(read($Heap, r#0, _module.Queue.contents))
         ==> _module.Queue.Get#canCall(Tclass._module.Word(), $Heap, r#0, i#1))
       && (_module.Queue.Get#canCall(Tclass._module.Word(), $Heap, r#0, i#1)
           && $Unbox(_module.Queue.Get(Tclass._module.Word(), $Heap, r#0, i#1)): ref != null
         ==>
        j#1 < Seq#Length(read($Heap, r#0, _module.Queue.contents))
         ==> _module.Queue.Get#canCall(Tclass._module.Word(), $Heap, r#0, i#1)
           && _module.Queue.Get#canCall(Tclass._module.Word(), $Heap, r#0, j#1)
           && _module.Word.AtMost#canCall($Unbox(_module.Queue.Get(Tclass._module.Word(), $Heap, r#0, i#1)): ref,
            $Unbox(_module.Queue.Get(Tclass._module.Word(), $Heap, r#0, j#1)): ref)));
  ensures (forall i#1: int, j#1: int ::
    { $Unbox(_module.Queue.Get(Tclass._module.Word(), $Heap, r#0, j#1)): ref, $Unbox(_module.Queue.Get(Tclass._module.Word(), $Heap, r#0, i#1)): ref }
    true
       ==> (LitInt(0) <= i#1
             && i#1 < j#1
             && j#1 < Seq#Length(read($Heap, r#0, _module.Queue.contents))
           ==> $Unbox(_module.Queue.Get(Tclass._module.Word(), $Heap, r#0, i#1)): ref != null)
         && (LitInt(0) <= i#1
             && i#1 < j#1
             && j#1 < Seq#Length(read($Heap, r#0, _module.Queue.contents))
           ==> _module.Word.AtMost($Unbox(_module.Queue.Get(Tclass._module.Word(), $Heap, r#0, i#1)): ref,
            $Unbox(_module.Queue.Get(Tclass._module.Word(), $Heap, r#0, j#1)): ref)));
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



procedure CheckWellformed$$_module.Glossary.Main(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Glossary())
         && $IsAlloc(this, Tclass._module.Glossary(), $Heap));
  free requires 22 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.Glossary.Main(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Glossary())
         && $IsAlloc(this, Tclass._module.Glossary(), $Heap));
  modifies $Heap, $Tick;
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Glossary.Main(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Glossary())
         && $IsAlloc(this, Tclass._module.Glossary(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 22 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



function Tclass._module.ReaderStream() : Ty;

// Tclass._module.ReaderStream Tag
axiom Tag(Tclass._module.ReaderStream()) == Tagclass._module.ReaderStream;

const unique Tagclass._module.ReaderStream: TyTag;

// Box/unbox axiom for Tclass._module.ReaderStream
axiom (forall bx: Box ::
  { $IsBox(bx, Tclass._module.ReaderStream()) }
  $IsBox(bx, Tclass._module.ReaderStream())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.ReaderStream()));

function Tclass._module.Map(Ty, Ty) : Ty;

// Tclass._module.Map Tag
axiom (forall _module.Map$Key: Ty, _module.Map$Value: Ty ::
  { Tclass._module.Map(_module.Map$Key, _module.Map$Value) }
  Tag(Tclass._module.Map(_module.Map$Key, _module.Map$Value))
     == Tagclass._module.Map);

const unique Tagclass._module.Map: TyTag;

// Tclass._module.Map injectivity 0
axiom (forall _module.Map$Key: Ty, _module.Map$Value: Ty ::
  { Tclass._module.Map(_module.Map$Key, _module.Map$Value) }
  Tclass._module.Map_0(Tclass._module.Map(_module.Map$Key, _module.Map$Value))
     == _module.Map$Key);

function Tclass._module.Map_0(Ty) : Ty;

// Tclass._module.Map injectivity 1
axiom (forall _module.Map$Key: Ty, _module.Map$Value: Ty ::
  { Tclass._module.Map(_module.Map$Key, _module.Map$Value) }
  Tclass._module.Map_1(Tclass._module.Map(_module.Map$Key, _module.Map$Value))
     == _module.Map$Value);

function Tclass._module.Map_1(Ty) : Ty;

// Box/unbox axiom for Tclass._module.Map
axiom (forall _module.Map$Key: Ty, _module.Map$Value: Ty, bx: Box ::
  { $IsBox(bx, Tclass._module.Map(_module.Map$Key, _module.Map$Value)) }
  $IsBox(bx, Tclass._module.Map(_module.Map$Key, _module.Map$Value))
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.Map(_module.Map$Key, _module.Map$Value)));

axiom FDim(_module.ReaderStream.footprint) == 0
   && FieldOfDecl(class._module.ReaderStream, field$footprint)
     == _module.ReaderStream.footprint
   && $IsGhostField(_module.ReaderStream.footprint);

axiom FDim(_module.ReaderStream.isOpen) == 0
   && FieldOfDecl(class._module.ReaderStream, field$isOpen)
     == _module.ReaderStream.isOpen
   && !$IsGhostField(_module.ReaderStream.isOpen);

axiom FDim(_module.Map.keys) == 0
   && FieldOfDecl(class._module.Map, field$keys) == _module.Map.keys
   && !$IsGhostField(_module.Map.keys);

axiom FDim(_module.Map.values) == 0
   && FieldOfDecl(class._module.Map, field$values) == _module.Map.values
   && !$IsGhostField(_module.Map.values);

function Tclass._module.WriterStream() : Ty;

// Tclass._module.WriterStream Tag
axiom Tag(Tclass._module.WriterStream()) == Tagclass._module.WriterStream;

const unique Tagclass._module.WriterStream: TyTag;

// Box/unbox axiom for Tclass._module.WriterStream
axiom (forall bx: Box ::
  { $IsBox(bx, Tclass._module.WriterStream()) }
  $IsBox(bx, Tclass._module.WriterStream())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.WriterStream()));

axiom FDim(_module.WriterStream.footprint) == 0
   && FieldOfDecl(class._module.WriterStream, field$footprint)
     == _module.WriterStream.footprint
   && $IsGhostField(_module.WriterStream.footprint);

axiom FDim(_module.WriterStream.isOpen) == 0
   && FieldOfDecl(class._module.WriterStream, field$isOpen)
     == _module.WriterStream.isOpen
   && !$IsGhostField(_module.WriterStream.isOpen);

implementation Impl$$_module.Glossary.Main(this: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var rs#0: ref
     where $Is(rs#0, Tclass._module.ReaderStream())
       && $IsAlloc(rs#0, Tclass._module.ReaderStream(), $Heap);
  var $nw: ref;
  var glossary#0: ref
     where $Is(glossary#0,
        Tclass._module.Map(Tclass._module.Word(), TSeq(Tclass._module.Word())))
       && $IsAlloc(glossary#0,
        Tclass._module.Map(Tclass._module.Word(), TSeq(Tclass._module.Word())),
        $Heap);
  var q#0: ref
     where $Is(q#0, Tclass._module.Queue(Tclass._module.Word()))
       && $IsAlloc(q#0, Tclass._module.Queue(Tclass._module.Word()), $Heap);
  var $PreLoopHeap$loop#0: Heap;
  var $w$loop#0: bool;
  var d#0: Seq Box;
  var term#0_0: ref
     where $Is(term#0_0, Tclass._module.Word())
       && $IsAlloc(term#0_0, Tclass._module.Word(), $Heap);
  var definition#0_0: Seq Box
     where $Is(definition#0_0, TSeq(Tclass._module.Word()))
       && $IsAlloc(definition#0_0, TSeq(Tclass._module.Word()), $Heap);
  var $rhs##0_0: ref
     where $Is($rhs##0_0, Tclass._module.Word())
       && $IsAlloc($rhs##0_0, Tclass._module.Word(), $Heap);
  var $rhs##0_1: Seq Box
     where $Is($rhs##0_1, TSeq(Tclass._module.Word()))
       && $IsAlloc($rhs##0_1, TSeq(Tclass._module.Word()), $Heap);
  var rs##0_0: ref;
  var r#0_0: DatatypeType
     where $Is(r#0_0, Tclass._module.Maybe(TSeq(Tclass._module.Word())))
       && $IsAlloc(r#0_0, Tclass._module.Maybe(TSeq(Tclass._module.Word())), $Heap);
  var $rhs##0_2: DatatypeType
     where $Is($rhs##0_2, Tclass._module.Maybe(TSeq(Tclass._module.Word())))
       && $IsAlloc($rhs##0_2, Tclass._module.Maybe(TSeq(Tclass._module.Word())), $Heap);
  var key##0_0: Box;
  var key##0_1_0: Box;
  var val##0_1_0: Box;
  var x##0_1_0: Box;
  var qc#0: Seq Box
     where $Is(qc#0, TSeq(Tclass._module.Word()))
       && $IsAlloc(qc#0, TSeq(Tclass._module.Word()), $Heap);
  var $rhs##0: ref
     where $Is($rhs##0, Tclass._module.Queue(Tclass._module.Word()))
       && $IsAlloc($rhs##0, Tclass._module.Queue(Tclass._module.Word()), $Heap);
  var q##0: ref;
  var k#0: ref;
  var wr#0: ref
     where $Is(wr#0, Tclass._module.WriterStream())
       && $IsAlloc(wr#0, Tclass._module.WriterStream(), $Heap);
  var $PreLoopHeap$loop#1: Heap;
  var $decr_init$loop#10: int;
  var $w$loop#1: bool;
  var d#2: Seq Box;
  var k#2: ref;
  var $decr$loop#10: int;
  var term#1_0: ref
     where $Is(term#1_0, Tclass._module.Word())
       && $IsAlloc(term#1_0, Tclass._module.Word(), $Heap);
  var $rhs##1_0: ref
     where $Is($rhs##1_0, Tclass._module.Word())
       && $IsAlloc($rhs##1_0, Tclass._module.Word(), $Heap);
  var $tmp##1_0: Box;
  var r#1_0: DatatypeType
     where $Is(r#1_0, Tclass._module.Maybe(TSeq(Tclass._module.Word())))
       && $IsAlloc(r#1_0, Tclass._module.Maybe(TSeq(Tclass._module.Word())), $Heap);
  var $rhs##1_1: DatatypeType
     where $Is($rhs##1_1, Tclass._module.Maybe(TSeq(Tclass._module.Word())))
       && $IsAlloc($rhs##1_1, Tclass._module.Maybe(TSeq(Tclass._module.Word())), $Heap);
  var key##1_0: Box;
  var definition#1_0: Seq Box
     where $Is(definition#1_0, TSeq(Tclass._module.Word()))
       && $IsAlloc(definition#1_0, TSeq(Tclass._module.Word()), $Heap);
  var tag##1_0: ref;
  var w##1_0: ref;
  var i#1_0: int;
  var qcon#1_0: Seq Box
     where $Is(qcon#1_0, TSeq(Tclass._module.Word()))
       && $IsAlloc(qcon#1_0, TSeq(Tclass._module.Word()), $Heap);
  var $PreLoopHeap$loop#1_0: Heap;
  var $decr_init$loop#1_00: int;
  var $w$loop#1_0: bool;
  var d#1_0: Seq Box;
  var k#1_0: ref;
  var $decr$loop#1_00: int;
  var w#1_0_0: ref
     where $Is(w#1_0_0, Tclass._module.Word())
       && $IsAlloc(w#1_0_0, Tclass._module.Word(), $Heap);
  var r#1_0_0: DatatypeType
     where $Is(r#1_0_0, Tclass._module.Maybe(TSeq(Tclass._module.Word())))
       && $IsAlloc(r#1_0_0, Tclass._module.Maybe(TSeq(Tclass._module.Word())), $Heap);
  var $rhs##1_0_0: DatatypeType
     where $Is($rhs##1_0_0, Tclass._module.Maybe(TSeq(Tclass._module.Word())))
       && $IsAlloc($rhs##1_0_0, Tclass._module.Maybe(TSeq(Tclass._module.Word())), $Heap);
  var key##1_0_0: Box;
  var tag##1_0_0_0: ref;
  var w##1_0_0_0: ref;
  var w##1_0_0: ref;

    // AddMethodImpl: Main, Impl$$_module.Glossary.Main
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "b8.dfy(49,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- b8.dfy(50,11)
    assume true;
    havoc $nw;
    assume $nw != null
       &&
      !read($Heap, $nw, alloc)
       && dtype($nw) == Tclass._module.ReaderStream();
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    rs#0 := $nw;
    assume {:captureState "b8.dfy(50,29)"} true;
    // ----- call statement ----- b8.dfy(51,12)
    // TrCallStmt: Before ProcessCallStmt
    assert rs#0 != null;
    assert (forall<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) && $o == rs#0 ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.ReaderStream.Open(rs#0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "b8.dfy(51,13)"} true;
    // ----- assignment statement ----- b8.dfy(52,18)
    assume true;
    havoc $nw;
    assume $nw != null
       &&
      !read($Heap, $nw, alloc)
       && dtype($nw)
         == Tclass._module.Map(Tclass._module.Word(), TSeq(Tclass._module.Word()));
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    // ----- init call statement ----- b8.dfy(52,45)
    // TrCallStmt: Before ProcessCallStmt
    assert (forall<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) && $o == $nw ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.Map.Init(Tclass._module.Word(), TSeq(Tclass._module.Word()), $nw);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "b8.dfy(52,50)"} true;
    glossary#0 := $nw;
    assume {:captureState "b8.dfy(52,50)"} true;
    // ----- assignment statement ----- b8.dfy(53,11)
    assume true;
    havoc $nw;
    assume $nw != null
       &&
      !read($Heap, $nw, alloc)
       && dtype($nw) == Tclass._module.Queue(Tclass._module.Word());
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    // ----- init call statement ----- b8.dfy(53,30)
    // TrCallStmt: Before ProcessCallStmt
    assert (forall<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) && $o == $nw ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.Queue.Init(Tclass._module.Word(), $nw);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "b8.dfy(53,35)"} true;
    q#0 := $nw;
    assume {:captureState "b8.dfy(53,35)"} true;
    // ----- while statement ----- b8.dfy(55,5)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    havoc $w$loop#0;
    while (true)
      free invariant $w$loop#0 ==> _module.ReaderStream.Valid#canCall($Heap, rs#0);
      invariant $w$loop#0
         ==>
        _module.ReaderStream.Valid#canCall($Heap, rs#0)
         ==> _module.ReaderStream.Valid($Heap, rs#0)
           || !read($Heap, rs#0, _module.ReaderStream.footprint)[$Box(null)];
      invariant $w$loop#0
         ==>
        _module.ReaderStream.Valid#canCall($Heap, rs#0)
         ==> _module.ReaderStream.Valid($Heap, rs#0)
           || read($Heap, rs#0, _module.ReaderStream.footprint)[$Box(rs#0)];
      invariant $w$loop#0
         ==>
        _module.ReaderStream.Valid#canCall($Heap, rs#0)
         ==> _module.ReaderStream.Valid($Heap, rs#0)
           || read($Heap, rs#0, _module.ReaderStream.isOpen);
      free invariant $w$loop#0
         ==> _module.ReaderStream.Valid#canCall($Heap, rs#0)
           &&
          _module.ReaderStream.Valid($Heap, rs#0)
           &&
          !read($Heap, rs#0, _module.ReaderStream.footprint)[$Box(null)]
           && read($Heap, rs#0, _module.ReaderStream.footprint)[$Box(rs#0)]
           && read($Heap, rs#0, _module.ReaderStream.isOpen);
      invariant $w$loop#0
         ==> (forall $o: ref ::
          { read($Heap, rs#0, _module.ReaderStream.footprint)[$Box($o)] }
          read($Heap, rs#0, _module.ReaderStream.footprint)[$Box($o)]
             ==> $o != null && !read(old($Heap), $o, alloc));
      free invariant $w$loop#0
         ==> _module.Map.Valid#canCall(Tclass._module.Word(), TSeq(Tclass._module.Word()), $Heap, glossary#0);
      invariant $w$loop#0
         ==>
        _module.Map.Valid#canCall(Tclass._module.Word(), TSeq(Tclass._module.Word()), $Heap, glossary#0)
         ==> _module.Map.Valid(Tclass._module.Word(), TSeq(Tclass._module.Word()), $Heap, glossary#0)
           || Seq#Length(read($Heap, glossary#0, _module.Map.keys))
             == Seq#Length(read($Heap, glossary#0, _module.Map.values));
      invariant $w$loop#0
         ==>
        _module.Map.Valid#canCall(Tclass._module.Word(), TSeq(Tclass._module.Word()), $Heap, glossary#0)
         ==> _module.Map.Valid(Tclass._module.Word(), TSeq(Tclass._module.Word()), $Heap, glossary#0)
           || (forall i#0: int, j#0: int ::
            { $Unbox(Seq#Index(read($Heap, glossary#0, _module.Map.keys), j#0)): ref, $Unbox(Seq#Index(read($Heap, glossary#0, _module.Map.keys), i#0)): ref }
            true
               ==>
              LitInt(0) <= i#0
                 && i#0 < j#0
                 && j#0 < Seq#Length(read($Heap, glossary#0, _module.Map.keys))
               ==> $Unbox(Seq#Index(read($Heap, glossary#0, _module.Map.keys), i#0)): ref
                 != $Unbox(Seq#Index(read($Heap, glossary#0, _module.Map.keys), j#0)): ref);
      free invariant $w$loop#0
         ==> _module.Map.Valid#canCall(Tclass._module.Word(), TSeq(Tclass._module.Word()), $Heap, glossary#0)
           &&
          _module.Map.Valid(Tclass._module.Word(), TSeq(Tclass._module.Word()), $Heap, glossary#0)
           &&
          Seq#Length(read($Heap, glossary#0, _module.Map.keys))
             == Seq#Length(read($Heap, glossary#0, _module.Map.values))
           && (forall i#0: int, j#0: int ::
            { $Unbox(Seq#Index(read($Heap, glossary#0, _module.Map.keys), j#0)): ref, $Unbox(Seq#Index(read($Heap, glossary#0, _module.Map.keys), i#0)): ref }
            true
               ==>
              LitInt(0) <= i#0
                 && i#0 < j#0
                 && j#0 < Seq#Length(read($Heap, glossary#0, _module.Map.keys))
               ==> $Unbox(Seq#Index(read($Heap, glossary#0, _module.Map.keys), i#0)): ref
                 != $Unbox(Seq#Index(read($Heap, glossary#0, _module.Map.keys), j#0)): ref);
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0
         ==> !read($Heap, rs#0, _module.ReaderStream.footprint)[$Box(glossary#0)];
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0
         ==> !Seq#Contains(read($Heap, glossary#0, _module.Map.keys), $Box(null));
      free invariant $w$loop#0
         ==> (forall d#1: Seq Box ::
          { Seq#Contains(d#1, $Box(null)) }
            { Seq#Contains(read($Heap, glossary#0, _module.Map.values), $Box(d#1)) }
          true);
      invariant $w$loop#0
         ==> (forall d#1: Seq Box ::
          { Seq#Contains(d#1, $Box(null)) }
            { Seq#Contains(read($Heap, glossary#0, _module.Map.values), $Box(d#1)) }
          $Is(d#1, TSeq(Tclass._module.Word()))
             ==>
            Seq#Contains(read($Heap, glossary#0, _module.Map.values), $Box(d#1))
             ==> !Seq#Contains(d#1, $Box(null)));
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0 ==> !read($Heap, rs#0, _module.ReaderStream.footprint)[$Box(q#0)];
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0
         ==> Seq#Equal(read($Heap, q#0, _module.Queue.contents),
          read($Heap, glossary#0, _module.Map.keys));
      free invariant (forall<alpha> $o: ref, $f: Field alpha ::
        { read($Heap, $o, $f) }
        $o != null && read(old($Heap), $o, alloc)
           ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0, $o, $f));
      free invariant $HeapSucc($PreLoopHeap$loop#0, $Heap);
      free invariant (forall<alpha> $o: ref, $f: Field alpha ::
        { read($Heap, $o, $f) }
        $o != null && read($PreLoopHeap$loop#0, $o, alloc)
           ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0, $o, $f) || $_Frame[$o, $f]);
    {
        assume {:captureState "b8.dfy(55,4): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            assert {:subsumption 0} rs#0 != null;
            assume _module.ReaderStream.Valid#canCall($Heap, rs#0);
            if (_module.ReaderStream.Valid($Heap, rs#0))
            {
                assert {:subsumption 0} rs#0 != null;
            }

            assume _module.ReaderStream.Valid#canCall($Heap, rs#0);
            assume _module.ReaderStream.Valid($Heap, rs#0)
               && (forall $o: ref ::
                { read($Heap, rs#0, _module.ReaderStream.footprint)[$Box($o)] }
                read($Heap, rs#0, _module.ReaderStream.footprint)[$Box($o)]
                   ==> $o != null && !read(old($Heap), $o, alloc));
            assert {:subsumption 0} glossary#0 != null;
            assume _module.Map.Valid#canCall(Tclass._module.Word(), TSeq(Tclass._module.Word()), $Heap, glossary#0);
            assume _module.Map.Valid#canCall(Tclass._module.Word(), TSeq(Tclass._module.Word()), $Heap, glossary#0);
            assume _module.Map.Valid(Tclass._module.Word(), TSeq(Tclass._module.Word()), $Heap, glossary#0);
            assert {:subsumption 0} rs#0 != null;
            assume true;
            assume !read($Heap, rs#0, _module.ReaderStream.footprint)[$Box(glossary#0)];
            assert {:subsumption 0} glossary#0 != null;
            assume true;
            assume !Seq#Contains(read($Heap, glossary#0, _module.Map.keys), $Box(null));
            havoc d#0;
            assume $Is(d#0, TSeq(Tclass._module.Word()));
            // Begin Comprehension WF check
            assert {:subsumption 0} glossary#0 != null;
            if (Seq#Contains(read($Heap, glossary#0, _module.Map.values), $Box(d#0)))
            {
            }

            // End Comprehension WF check
            assume (forall d#1: Seq Box ::
              { Seq#Contains(d#1, $Box(null)) }
                { Seq#Contains(read($Heap, glossary#0, _module.Map.values), $Box(d#1)) }
              true);
            assume (forall d#1: Seq Box ::
              { Seq#Contains(d#1, $Box(null)) }
                { Seq#Contains(read($Heap, glossary#0, _module.Map.values), $Box(d#1)) }
              $Is(d#1, TSeq(Tclass._module.Word()))
                 ==>
                Seq#Contains(read($Heap, glossary#0, _module.Map.values), $Box(d#1))
                 ==> !Seq#Contains(d#1, $Box(null)));
            assert {:subsumption 0} rs#0 != null;
            assume true;
            assume !read($Heap, rs#0, _module.ReaderStream.footprint)[$Box(q#0)];
            assert {:subsumption 0} q#0 != null;
            assert {:subsumption 0} glossary#0 != null;
            assume true;
            assume Seq#Equal(read($Heap, q#0, _module.Queue.contents),
              read($Heap, glossary#0, _module.Map.keys));
            assume true;
            assume false;
        }

        assume true;
        if (!Lit(true))
        {
            break;
        }

        // ----- call statement ----- b8.dfy(65,45)
        assume true;
        assume true;
        // TrCallStmt: Adding lhs Microsoft.Dafny.AutoGhostIdentifierExpr with type Word
        // TrCallStmt: Adding lhs Microsoft.Dafny.AutoGhostIdentifierExpr with type seq<Word>
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        rs##0_0 := rs#0;
        assert (forall<alpha> $o: ref, $f: Field alpha ::
          $o != null
               && read($Heap, $o, alloc)
               && read($Heap, rs##0_0, _module.ReaderStream.footprint)[$Box($o)]
             ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call $rhs##0_0, $rhs##0_1 := Call$$_module.Glossary.readDefinition(this, rs##0_0);
        // TrCallStmt: After ProcessCallStmt
        term#0_0 := $rhs##0_0;
        definition#0_0 := $rhs##0_1;
        assume {:captureState "b8.dfy(65,48)"} true;
        // ----- if statement ----- b8.dfy(66,7)
        assume true;
        if (term#0_0 == null)
        {
            // ----- break statement ----- b8.dfy(67,9)
            goto after_0_0_0;
        }
        else
        {
        }

        // ----- call statement ----- b8.dfy(69,29)
        assume true;
        // TrCallStmt: Adding lhs Microsoft.Dafny.AutoGhostIdentifierExpr with type Maybe<seq<Word>>
        // TrCallStmt: Before ProcessCallStmt
        assert glossary#0 != null;
        assume true;
        // ProcessCallStmt: CheckSubrange
        key##0_0 := $Box(term#0_0);
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call $rhs##0_2 := Call$$_module.Map.Find(Tclass._module.Word(), TSeq(Tclass._module.Word()), glossary#0, key##0_0);
        // TrCallStmt: After ProcessCallStmt
        r#0_0 := $rhs##0_2;
        assume {:captureState "b8.dfy(69,34)"} true;
        // ----- if statement ----- b8.dfy(70,7)
        assume true;
        if (r#0_0 == Lit(#_module.Maybe.None()))
        {
            // ----- call statement ----- b8.dfy(71,21)
            // TrCallStmt: Before ProcessCallStmt
            assert glossary#0 != null;
            assume true;
            // ProcessCallStmt: CheckSubrange
            key##0_1_0 := $Box(term#0_0);
            assume true;
            // ProcessCallStmt: CheckSubrange
            val##0_1_0 := $Box(definition#0_0);
            assert (forall<alpha> $o: ref, $f: Field alpha ::
              $o != null && read($Heap, $o, alloc) && $o == glossary#0 ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call Call$$_module.Map.Add(Tclass._module.Word(), TSeq(Tclass._module.Word()), glossary#0, key##0_1_0, val##0_1_0);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "b8.dfy(71,38)"} true;
            // ----- call statement ----- b8.dfy(72,18)
            // TrCallStmt: Before ProcessCallStmt
            assert q#0 != null;
            assume true;
            // ProcessCallStmt: CheckSubrange
            x##0_1_0 := $Box(term#0_0);
            assert (forall<alpha> $o: ref, $f: Field alpha ::
              $o != null && read($Heap, $o, alloc) && $o == q#0 ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call Call$$_module.Queue.Enqueue(Tclass._module.Word(), q#0, x##0_1_0);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "b8.dfy(72,23)"} true;
        }
        else
        {
        }

        assume _module.ReaderStream.Valid#canCall($Heap, rs#0);
        assume _module.Map.Valid#canCall(Tclass._module.Word(), TSeq(Tclass._module.Word()), $Heap, glossary#0);
        assume true;
        assume true;
        assume (forall d#1: Seq Box ::
          { Seq#Contains(d#1, $Box(null)) }
            { Seq#Contains(read($Heap, glossary#0, _module.Map.values), $Box(d#1)) }
          true);
        assume true;
        assume true;
    }

  after_0_0_0:
    // ----- call statement ----- b8.dfy(76,13)
    // TrCallStmt: Before ProcessCallStmt
    assert rs#0 != null;
    assert (forall<alpha> $o: ref, $f: Field alpha ::
      $o != null
           && read($Heap, $o, alloc)
           && read($Heap, rs#0, _module.ReaderStream.footprint)[$Box($o)]
         ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.ReaderStream.Close(rs#0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "b8.dfy(76,14)"} true;
    // ----- assignment statement ----- b8.dfy(77,18)
    assume true;
    assert q#0 != null;
    assume true;
    qc#0 := read($Heap, q#0, _module.Queue.contents);
    assume {:captureState "b8.dfy(77,30)"} true;
    // ----- call statement ----- b8.dfy(78,14)
    assume true;
    // TrCallStmt: Adding lhs Microsoft.Dafny.IdentifierExpr with type Queue<Word>
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    q##0 := q#0;
    assert (forall<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) && $o == q##0 ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##0 := Call$$_module.Glossary.Sort(this, q##0);
    // TrCallStmt: After ProcessCallStmt
    q#0 := $rhs##0;
    assume {:captureState "b8.dfy(78,16)"} true;
    // ----- assert statement ----- b8.dfy(79,5)
    havoc k#0;
    assume $Is(k#0, Tclass._module.Word());
    // Begin Comprehension WF check
    assert {:subsumption 0} q#0 != null;
    if (Seq#Contains(read($Heap, q#0, _module.Queue.contents), $Box(k#0)))
    {
        assert {:subsumption 0} q#0 != null;
    }

    // End Comprehension WF check
    assume (forall k#1: ref ::
      { MultiSet#FromSeq(read($Heap, q#0, _module.Queue.contents))[$Box(k#1)] }
        { Seq#Contains(read($Heap, q#0, _module.Queue.contents), $Box(k#1)) }
      true);
    assert (forall k#1: ref ::
      { MultiSet#FromSeq(read($Heap, q#0, _module.Queue.contents))[$Box(k#1)] }
        { Seq#Contains(read($Heap, q#0, _module.Queue.contents), $Box(k#1)) }
      $Is(k#1, Tclass._module.Word())
         ==>
        Seq#Contains(read($Heap, q#0, _module.Queue.contents), $Box(k#1))
         ==> MultiSet#FromSeq(read($Heap, q#0, _module.Queue.contents))[$Box(k#1)] > 0);
    // ----- assignment statement ----- b8.dfy(80,12)
    assume true;
    havoc $nw;
    assume $nw != null
       &&
      !read($Heap, $nw, alloc)
       && dtype($nw) == Tclass._module.WriterStream();
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    wr#0 := $nw;
    assume {:captureState "b8.dfy(80,30)"} true;
    // ----- call statement ----- b8.dfy(81,14)
    // TrCallStmt: Before ProcessCallStmt
    assert wr#0 != null;
    assert (forall<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) && $o == wr#0 ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.WriterStream.Create(wr#0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "b8.dfy(81,15)"} true;
    // ----- while statement ----- b8.dfy(83,5)
    // Assume Fuel Constant
    $PreLoopHeap$loop#1 := $Heap;
    $decr_init$loop#10 := Seq#Length(read($Heap, q#0, _module.Queue.contents)) - 0;
    havoc $w$loop#1;
    while (true)
      free invariant $w$loop#1 ==> _module.WriterStream.Valid#canCall($Heap, wr#0);
      invariant $w$loop#1
         ==>
        _module.WriterStream.Valid#canCall($Heap, wr#0)
         ==> _module.WriterStream.Valid($Heap, wr#0)
           || !read($Heap, wr#0, _module.WriterStream.footprint)[$Box(null)];
      invariant $w$loop#1
         ==>
        _module.WriterStream.Valid#canCall($Heap, wr#0)
         ==> _module.WriterStream.Valid($Heap, wr#0)
           || read($Heap, wr#0, _module.WriterStream.footprint)[$Box(wr#0)];
      invariant $w$loop#1
         ==>
        _module.WriterStream.Valid#canCall($Heap, wr#0)
         ==> _module.WriterStream.Valid($Heap, wr#0)
           || read($Heap, wr#0, _module.WriterStream.isOpen);
      free invariant $w$loop#1
         ==> _module.WriterStream.Valid#canCall($Heap, wr#0)
           &&
          _module.WriterStream.Valid($Heap, wr#0)
           &&
          !read($Heap, wr#0, _module.WriterStream.footprint)[$Box(null)]
           && read($Heap, wr#0, _module.WriterStream.footprint)[$Box(wr#0)]
           && read($Heap, wr#0, _module.WriterStream.isOpen);
      invariant $w$loop#1
         ==> (forall $o: ref ::
          { read($Heap, wr#0, _module.WriterStream.footprint)[$Box($o)] }
          read($Heap, wr#0, _module.WriterStream.footprint)[$Box($o)]
             ==> $o != null && !read(old($Heap), $o, alloc));
      free invariant $w$loop#1
         ==> _module.Map.Valid#canCall(Tclass._module.Word(), TSeq(Tclass._module.Word()), $Heap, glossary#0);
      invariant $w$loop#1
         ==>
        _module.Map.Valid#canCall(Tclass._module.Word(), TSeq(Tclass._module.Word()), $Heap, glossary#0)
         ==> _module.Map.Valid(Tclass._module.Word(), TSeq(Tclass._module.Word()), $Heap, glossary#0)
           || Seq#Length(read($Heap, glossary#0, _module.Map.keys))
             == Seq#Length(read($Heap, glossary#0, _module.Map.values));
      invariant $w$loop#1
         ==>
        _module.Map.Valid#canCall(Tclass._module.Word(), TSeq(Tclass._module.Word()), $Heap, glossary#0)
         ==> _module.Map.Valid(Tclass._module.Word(), TSeq(Tclass._module.Word()), $Heap, glossary#0)
           || (forall i#1: int, j#1: int ::
            { $Unbox(Seq#Index(read($Heap, glossary#0, _module.Map.keys), j#1)): ref, $Unbox(Seq#Index(read($Heap, glossary#0, _module.Map.keys), i#1)): ref }
            true
               ==>
              LitInt(0) <= i#1
                 && i#1 < j#1
                 && j#1 < Seq#Length(read($Heap, glossary#0, _module.Map.keys))
               ==> $Unbox(Seq#Index(read($Heap, glossary#0, _module.Map.keys), i#1)): ref
                 != $Unbox(Seq#Index(read($Heap, glossary#0, _module.Map.keys), j#1)): ref);
      free invariant $w$loop#1
         ==> _module.Map.Valid#canCall(Tclass._module.Word(), TSeq(Tclass._module.Word()), $Heap, glossary#0)
           &&
          _module.Map.Valid(Tclass._module.Word(), TSeq(Tclass._module.Word()), $Heap, glossary#0)
           &&
          Seq#Length(read($Heap, glossary#0, _module.Map.keys))
             == Seq#Length(read($Heap, glossary#0, _module.Map.values))
           && (forall i#1: int, j#1: int ::
            { $Unbox(Seq#Index(read($Heap, glossary#0, _module.Map.keys), j#1)): ref, $Unbox(Seq#Index(read($Heap, glossary#0, _module.Map.keys), i#1)): ref }
            true
               ==>
              LitInt(0) <= i#1
                 && i#1 < j#1
                 && j#1 < Seq#Length(read($Heap, glossary#0, _module.Map.keys))
               ==> $Unbox(Seq#Index(read($Heap, glossary#0, _module.Map.keys), i#1)): ref
                 != $Unbox(Seq#Index(read($Heap, glossary#0, _module.Map.keys), j#1)): ref);
      free invariant $w$loop#1 ==> true;
      invariant $w$loop#1
         ==> !read($Heap, wr#0, _module.WriterStream.footprint)[$Box(glossary#0)];
      invariant $w$loop#1
         ==> !Seq#Contains(read($Heap, glossary#0, _module.Map.keys), $Box(null));
      free invariant $w$loop#1
         ==> (forall d#3: Seq Box ::
          { Seq#Contains(d#3, $Box(null)) }
            { Seq#Contains(read($Heap, glossary#0, _module.Map.values), $Box(d#3)) }
          true);
      invariant $w$loop#1
         ==> (forall d#3: Seq Box ::
          { Seq#Contains(d#3, $Box(null)) }
            { Seq#Contains(read($Heap, glossary#0, _module.Map.values), $Box(d#3)) }
          $Is(d#3, TSeq(Tclass._module.Word()))
             ==>
            Seq#Contains(read($Heap, glossary#0, _module.Map.values), $Box(d#3))
             ==> !Seq#Contains(d#3, $Box(null)));
      free invariant $w$loop#1 ==> true;
      invariant $w$loop#1 ==> !read($Heap, wr#0, _module.WriterStream.footprint)[$Box(q#0)];
      free invariant $w$loop#1
         ==> (forall k#3: ref ::
          { Seq#Contains(read($Heap, glossary#0, _module.Map.keys), $Box(k#3)) }
            { Seq#Contains(read($Heap, q#0, _module.Queue.contents), $Box(k#3)) }
          true);
      invariant $w$loop#1
         ==> (forall k#3: ref ::
          { Seq#Contains(read($Heap, glossary#0, _module.Map.keys), $Box(k#3)) }
            { Seq#Contains(read($Heap, q#0, _module.Queue.contents), $Box(k#3)) }
          $Is(k#3, Tclass._module.Word())
             ==>
            Seq#Contains(read($Heap, q#0, _module.Queue.contents), $Box(k#3))
             ==> Seq#Contains(read($Heap, glossary#0, _module.Map.keys), $Box(k#3)));
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
        assume {:captureState "b8.dfy(83,4): after some loop iterations"} true;
        if (!$w$loop#1)
        {
            assert {:subsumption 0} wr#0 != null;
            assume _module.WriterStream.Valid#canCall($Heap, wr#0);
            if (_module.WriterStream.Valid($Heap, wr#0))
            {
                assert {:subsumption 0} wr#0 != null;
            }

            assume _module.WriterStream.Valid#canCall($Heap, wr#0);
            assume _module.WriterStream.Valid($Heap, wr#0)
               && (forall $o: ref ::
                { read($Heap, wr#0, _module.WriterStream.footprint)[$Box($o)] }
                read($Heap, wr#0, _module.WriterStream.footprint)[$Box($o)]
                   ==> $o != null && !read(old($Heap), $o, alloc));
            assert {:subsumption 0} glossary#0 != null;
            assume _module.Map.Valid#canCall(Tclass._module.Word(), TSeq(Tclass._module.Word()), $Heap, glossary#0);
            assume _module.Map.Valid#canCall(Tclass._module.Word(), TSeq(Tclass._module.Word()), $Heap, glossary#0);
            assume _module.Map.Valid(Tclass._module.Word(), TSeq(Tclass._module.Word()), $Heap, glossary#0);
            assert {:subsumption 0} wr#0 != null;
            if (!read($Heap, wr#0, _module.WriterStream.footprint)[$Box(glossary#0)])
            {
                assert {:subsumption 0} glossary#0 != null;
            }

            assume true;
            assume !read($Heap, wr#0, _module.WriterStream.footprint)[$Box(glossary#0)]
               && !Seq#Contains(read($Heap, glossary#0, _module.Map.keys), $Box(null));
            havoc d#2;
            assume $Is(d#2, TSeq(Tclass._module.Word()));
            // Begin Comprehension WF check
            assert {:subsumption 0} glossary#0 != null;
            if (Seq#Contains(read($Heap, glossary#0, _module.Map.values), $Box(d#2)))
            {
            }

            // End Comprehension WF check
            assume (forall d#3: Seq Box ::
              { Seq#Contains(d#3, $Box(null)) }
                { Seq#Contains(read($Heap, glossary#0, _module.Map.values), $Box(d#3)) }
              true);
            assume (forall d#3: Seq Box ::
              { Seq#Contains(d#3, $Box(null)) }
                { Seq#Contains(read($Heap, glossary#0, _module.Map.values), $Box(d#3)) }
              $Is(d#3, TSeq(Tclass._module.Word()))
                 ==>
                Seq#Contains(read($Heap, glossary#0, _module.Map.values), $Box(d#3))
                 ==> !Seq#Contains(d#3, $Box(null)));
            assert {:subsumption 0} wr#0 != null;
            assume true;
            assume !read($Heap, wr#0, _module.WriterStream.footprint)[$Box(q#0)];
            havoc k#2;
            assume $Is(k#2, Tclass._module.Word());
            // Begin Comprehension WF check
            assert {:subsumption 0} q#0 != null;
            if (Seq#Contains(read($Heap, q#0, _module.Queue.contents), $Box(k#2)))
            {
                assert {:subsumption 0} glossary#0 != null;
            }

            // End Comprehension WF check
            assume (forall k#3: ref ::
              { Seq#Contains(read($Heap, glossary#0, _module.Map.keys), $Box(k#3)) }
                { Seq#Contains(read($Heap, q#0, _module.Queue.contents), $Box(k#3)) }
              true);
            assume (forall k#3: ref ::
              { Seq#Contains(read($Heap, glossary#0, _module.Map.keys), $Box(k#3)) }
                { Seq#Contains(read($Heap, q#0, _module.Queue.contents), $Box(k#3)) }
              $Is(k#3, Tclass._module.Word())
                 ==>
                Seq#Contains(read($Heap, q#0, _module.Queue.contents), $Box(k#3))
                 ==> Seq#Contains(read($Heap, glossary#0, _module.Map.keys), $Box(k#3)));
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
        // ----- call statement ----- b8.dfy(91,28)
        assume true;
        // TrCallStmt: Adding lhs Microsoft.Dafny.AutoGhostIdentifierExpr with type Word
        // TrCallStmt: Before ProcessCallStmt
        assert q#0 != null;
        assert (forall<alpha> $o: ref, $f: Field alpha ::
          $o != null && read($Heap, $o, alloc) && $o == q#0 ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call $tmp##1_0 := Call$$_module.Queue.Dequeue(Tclass._module.Word(), q#0);
        havoc $rhs##1_0;
        assume $rhs##1_0 == $Unbox($tmp##1_0): ref;
        // TrCallStmt: After ProcessCallStmt
        term#1_0 := $rhs##1_0;
        assume {:captureState "b8.dfy(91,29)"} true;
        // ----- call statement ----- b8.dfy(92,29)
        assume true;
        // TrCallStmt: Adding lhs Microsoft.Dafny.AutoGhostIdentifierExpr with type Maybe<seq<Word>>
        // TrCallStmt: Before ProcessCallStmt
        assert glossary#0 != null;
        assume true;
        // ProcessCallStmt: CheckSubrange
        key##1_0 := $Box(term#1_0);
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call $rhs##1_1 := Call$$_module.Map.Find(Tclass._module.Word(), TSeq(Tclass._module.Word()), glossary#0, key##1_0);
        // TrCallStmt: After ProcessCallStmt
        r#1_0 := $rhs##1_1;
        assume {:captureState "b8.dfy(92,34)"} true;
        // ----- assert statement ----- b8.dfy(93,7)
        assume true;
        assert _module.Maybe.Some_q(r#1_0);
        // ----- assignment statement ----- b8.dfy(94,22)
        assume true;
        assert _module.Maybe.Some_q(r#1_0);
        assume true;
        definition#1_0 := $Unbox(_module.Maybe.get(r#1_0)): Seq Box;
        assume {:captureState "b8.dfy(94,29)"} true;
        // ----- assert statement ----- b8.dfy(95,7)
        assume true;
        assert !Seq#Contains(definition#1_0, $Box(null));
        // ----- call statement ----- b8.dfy(98,26)
        // TrCallStmt: Before ProcessCallStmt
        assert wr#0 != null;
        assume true;
        // ProcessCallStmt: CheckSubrange
        tag##1_0 := term#1_0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        w##1_0 := term#1_0;
        assert (forall<alpha> $o: ref, $f: Field alpha ::
          $o != null
               && read($Heap, $o, alloc)
               && read($Heap, wr#0, _module.WriterStream.footprint)[$Box($o)]
             ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$_module.WriterStream.PutWordInsideTag(wr#0, tag##1_0, w##1_0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "b8.dfy(98,37)"} true;
        // ----- assignment statement ----- b8.dfy(99,13)
        assume true;
        assume true;
        i#1_0 := LitInt(0);
        assume {:captureState "b8.dfy(99,16)"} true;
        // ----- assignment statement ----- b8.dfy(101,16)
        assume true;
        assert q#0 != null;
        assume true;
        qcon#1_0 := read($Heap, q#0, _module.Queue.contents);
        assume {:captureState "b8.dfy(101,28)"} true;
        // ----- while statement ----- b8.dfy(102,7)
        // Assume Fuel Constant
        $PreLoopHeap$loop#1_0 := $Heap;
        $decr_init$loop#1_00 := Seq#Length(definition#1_0) - i#1_0;
        havoc $w$loop#1_0;
        while (true)
          free invariant $w$loop#1_0 ==> _module.WriterStream.Valid#canCall($Heap, wr#0);
          invariant $w$loop#1_0
             ==>
            _module.WriterStream.Valid#canCall($Heap, wr#0)
             ==> _module.WriterStream.Valid($Heap, wr#0)
               || !read($Heap, wr#0, _module.WriterStream.footprint)[$Box(null)];
          invariant $w$loop#1_0
             ==>
            _module.WriterStream.Valid#canCall($Heap, wr#0)
             ==> _module.WriterStream.Valid($Heap, wr#0)
               || read($Heap, wr#0, _module.WriterStream.footprint)[$Box(wr#0)];
          invariant $w$loop#1_0
             ==>
            _module.WriterStream.Valid#canCall($Heap, wr#0)
             ==> _module.WriterStream.Valid($Heap, wr#0)
               || read($Heap, wr#0, _module.WriterStream.isOpen);
          free invariant $w$loop#1_0
             ==> _module.WriterStream.Valid#canCall($Heap, wr#0)
               &&
              _module.WriterStream.Valid($Heap, wr#0)
               &&
              !read($Heap, wr#0, _module.WriterStream.footprint)[$Box(null)]
               && read($Heap, wr#0, _module.WriterStream.footprint)[$Box(wr#0)]
               && read($Heap, wr#0, _module.WriterStream.isOpen);
          invariant $w$loop#1_0
             ==> (forall $o: ref ::
              { read($Heap, wr#0, _module.WriterStream.footprint)[$Box($o)] }
              read($Heap, wr#0, _module.WriterStream.footprint)[$Box($o)]
                 ==> $o != null && !read(old($Heap), $o, alloc));
          free invariant $w$loop#1_0
             ==> _module.Map.Valid#canCall(Tclass._module.Word(), TSeq(Tclass._module.Word()), $Heap, glossary#0);
          invariant $w$loop#1_0
             ==>
            _module.Map.Valid#canCall(Tclass._module.Word(), TSeq(Tclass._module.Word()), $Heap, glossary#0)
             ==> _module.Map.Valid(Tclass._module.Word(), TSeq(Tclass._module.Word()), $Heap, glossary#0)
               || Seq#Length(read($Heap, glossary#0, _module.Map.keys))
                 == Seq#Length(read($Heap, glossary#0, _module.Map.values));
          invariant $w$loop#1_0
             ==>
            _module.Map.Valid#canCall(Tclass._module.Word(), TSeq(Tclass._module.Word()), $Heap, glossary#0)
             ==> _module.Map.Valid(Tclass._module.Word(), TSeq(Tclass._module.Word()), $Heap, glossary#0)
               || (forall i#1_1: int, j#1_0: int ::
                { $Unbox(Seq#Index(read($Heap, glossary#0, _module.Map.keys), j#1_0)): ref, $Unbox(Seq#Index(read($Heap, glossary#0, _module.Map.keys), i#1_1)): ref }
                true
                   ==>
                  LitInt(0) <= i#1_1
                     && i#1_1 < j#1_0
                     && j#1_0 < Seq#Length(read($Heap, glossary#0, _module.Map.keys))
                   ==> $Unbox(Seq#Index(read($Heap, glossary#0, _module.Map.keys), i#1_1)): ref
                     != $Unbox(Seq#Index(read($Heap, glossary#0, _module.Map.keys), j#1_0)): ref);
          free invariant $w$loop#1_0
             ==> _module.Map.Valid#canCall(Tclass._module.Word(), TSeq(Tclass._module.Word()), $Heap, glossary#0)
               &&
              _module.Map.Valid(Tclass._module.Word(), TSeq(Tclass._module.Word()), $Heap, glossary#0)
               &&
              Seq#Length(read($Heap, glossary#0, _module.Map.keys))
                 == Seq#Length(read($Heap, glossary#0, _module.Map.values))
               && (forall i#1_1: int, j#1_0: int ::
                { $Unbox(Seq#Index(read($Heap, glossary#0, _module.Map.keys), j#1_0)): ref, $Unbox(Seq#Index(read($Heap, glossary#0, _module.Map.keys), i#1_1)): ref }
                true
                   ==>
                  LitInt(0) <= i#1_1
                     && i#1_1 < j#1_0
                     && j#1_0 < Seq#Length(read($Heap, glossary#0, _module.Map.keys))
                   ==> $Unbox(Seq#Index(read($Heap, glossary#0, _module.Map.keys), i#1_1)): ref
                     != $Unbox(Seq#Index(read($Heap, glossary#0, _module.Map.keys), j#1_0)): ref);
          free invariant $w$loop#1_0 ==> true;
          invariant $w$loop#1_0
             ==> !read($Heap, wr#0, _module.WriterStream.footprint)[$Box(glossary#0)];
          invariant $w$loop#1_0
             ==> !Seq#Contains(read($Heap, glossary#0, _module.Map.keys), $Box(null));
          free invariant $w$loop#1_0
             ==> (forall d#1_1: Seq Box ::
              { Seq#Contains(d#1_1, $Box(null)) }
                { Seq#Contains(read($Heap, glossary#0, _module.Map.values), $Box(d#1_1)) }
              true);
          invariant $w$loop#1_0
             ==> (forall d#1_1: Seq Box ::
              { Seq#Contains(d#1_1, $Box(null)) }
                { Seq#Contains(read($Heap, glossary#0, _module.Map.values), $Box(d#1_1)) }
              $Is(d#1_1, TSeq(Tclass._module.Word()))
                 ==>
                Seq#Contains(read($Heap, glossary#0, _module.Map.values), $Box(d#1_1))
                 ==> !Seq#Contains(d#1_1, $Box(null)));
          free invariant $w$loop#1_0 ==> true;
          invariant $w$loop#1_0 ==> !read($Heap, wr#0, _module.WriterStream.footprint)[$Box(q#0)];
          free invariant $w$loop#1_0 ==> true;
          invariant $w$loop#1_0 ==> Seq#Equal(qcon#1_0, read($Heap, q#0, _module.Queue.contents));
          free invariant $w$loop#1_0
             ==> (forall k#1_1: ref ::
              { Seq#Contains(read($Heap, glossary#0, _module.Map.keys), $Box(k#1_1)) }
                { Seq#Contains(read($Heap, q#0, _module.Queue.contents), $Box(k#1_1)) }
              true);
          invariant $w$loop#1_0
             ==> (forall k#1_1: ref ::
              { Seq#Contains(read($Heap, glossary#0, _module.Map.keys), $Box(k#1_1)) }
                { Seq#Contains(read($Heap, q#0, _module.Queue.contents), $Box(k#1_1)) }
              $Is(k#1_1, Tclass._module.Word())
                 ==>
                Seq#Contains(read($Heap, q#0, _module.Queue.contents), $Box(k#1_1))
                 ==> Seq#Contains(read($Heap, glossary#0, _module.Map.keys), $Box(k#1_1)));
          free invariant (forall<alpha> $o: ref, $f: Field alpha ::
            { read($Heap, $o, $f) }
            $o != null && read(old($Heap), $o, alloc)
               ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#1_0, $o, $f));
          free invariant $HeapSucc($PreLoopHeap$loop#1_0, $Heap);
          free invariant (forall<alpha> $o: ref, $f: Field alpha ::
            { read($Heap, $o, $f) }
            $o != null && read($PreLoopHeap$loop#1_0, $o, alloc)
               ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#1_0, $o, $f) || $_Frame[$o, $f]);
          free invariant Seq#Length(definition#1_0) - i#1_0 <= $decr_init$loop#1_00
             && (Seq#Length(definition#1_0) - i#1_0 == $decr_init$loop#1_00 ==> true);
        {
            assume {:captureState "b8.dfy(102,6): after some loop iterations"} true;
            if (!$w$loop#1_0)
            {
                assert {:subsumption 0} wr#0 != null;
                assume _module.WriterStream.Valid#canCall($Heap, wr#0);
                if (_module.WriterStream.Valid($Heap, wr#0))
                {
                    assert {:subsumption 0} wr#0 != null;
                }

                assume _module.WriterStream.Valid#canCall($Heap, wr#0);
                assume _module.WriterStream.Valid($Heap, wr#0)
                   && (forall $o: ref ::
                    { read($Heap, wr#0, _module.WriterStream.footprint)[$Box($o)] }
                    read($Heap, wr#0, _module.WriterStream.footprint)[$Box($o)]
                       ==> $o != null && !read(old($Heap), $o, alloc));
                assert {:subsumption 0} glossary#0 != null;
                assume _module.Map.Valid#canCall(Tclass._module.Word(), TSeq(Tclass._module.Word()), $Heap, glossary#0);
                assume _module.Map.Valid#canCall(Tclass._module.Word(), TSeq(Tclass._module.Word()), $Heap, glossary#0);
                assume _module.Map.Valid(Tclass._module.Word(), TSeq(Tclass._module.Word()), $Heap, glossary#0);
                assert {:subsumption 0} wr#0 != null;
                if (!read($Heap, wr#0, _module.WriterStream.footprint)[$Box(glossary#0)])
                {
                    assert {:subsumption 0} glossary#0 != null;
                }

                assume true;
                assume !read($Heap, wr#0, _module.WriterStream.footprint)[$Box(glossary#0)]
                   && !Seq#Contains(read($Heap, glossary#0, _module.Map.keys), $Box(null));
                havoc d#1_0;
                assume $Is(d#1_0, TSeq(Tclass._module.Word()));
                // Begin Comprehension WF check
                assert {:subsumption 0} glossary#0 != null;
                if (Seq#Contains(read($Heap, glossary#0, _module.Map.values), $Box(d#1_0)))
                {
                }

                // End Comprehension WF check
                assume (forall d#1_1: Seq Box ::
                  { Seq#Contains(d#1_1, $Box(null)) }
                    { Seq#Contains(read($Heap, glossary#0, _module.Map.values), $Box(d#1_1)) }
                  true);
                assume (forall d#1_1: Seq Box ::
                  { Seq#Contains(d#1_1, $Box(null)) }
                    { Seq#Contains(read($Heap, glossary#0, _module.Map.values), $Box(d#1_1)) }
                  $Is(d#1_1, TSeq(Tclass._module.Word()))
                     ==>
                    Seq#Contains(read($Heap, glossary#0, _module.Map.values), $Box(d#1_1))
                     ==> !Seq#Contains(d#1_1, $Box(null)));
                assert {:subsumption 0} wr#0 != null;
                assume true;
                assume !read($Heap, wr#0, _module.WriterStream.footprint)[$Box(q#0)];
                assert {:subsumption 0} q#0 != null;
                assume true;
                assume Seq#Equal(qcon#1_0, read($Heap, q#0, _module.Queue.contents));
                havoc k#1_0;
                assume $Is(k#1_0, Tclass._module.Word());
                // Begin Comprehension WF check
                assert {:subsumption 0} q#0 != null;
                if (Seq#Contains(read($Heap, q#0, _module.Queue.contents), $Box(k#1_0)))
                {
                    assert {:subsumption 0} glossary#0 != null;
                }

                // End Comprehension WF check
                assume (forall k#1_1: ref ::
                  { Seq#Contains(read($Heap, glossary#0, _module.Map.keys), $Box(k#1_1)) }
                    { Seq#Contains(read($Heap, q#0, _module.Queue.contents), $Box(k#1_1)) }
                  true);
                assume (forall k#1_1: ref ::
                  { Seq#Contains(read($Heap, glossary#0, _module.Map.keys), $Box(k#1_1)) }
                    { Seq#Contains(read($Heap, q#0, _module.Queue.contents), $Box(k#1_1)) }
                  $Is(k#1_1, Tclass._module.Word())
                     ==>
                    Seq#Contains(read($Heap, q#0, _module.Queue.contents), $Box(k#1_1))
                     ==> Seq#Contains(read($Heap, glossary#0, _module.Map.keys), $Box(k#1_1)));
                assume true;
                assume false;
            }

            assume true;
            if (Seq#Length(definition#1_0) <= i#1_0)
            {
                break;
            }

            $decr$loop#1_00 := Seq#Length(definition#1_0) - i#1_0;
            // ----- assignment statement ----- b8.dfy(111,15)
            assume true;
            assert 0 <= i#1_0 && i#1_0 < Seq#Length(definition#1_0);
            assume true;
            w#1_0_0 := $Unbox(Seq#Index(definition#1_0, i#1_0)): ref;
            assume {:captureState "b8.dfy(111,30)"} true;
            // ----- call statement ----- b8.dfy(112,31)
            assume true;
            // TrCallStmt: Adding lhs Microsoft.Dafny.AutoGhostIdentifierExpr with type Maybe<seq<Word>>
            // TrCallStmt: Before ProcessCallStmt
            assert glossary#0 != null;
            assume true;
            // ProcessCallStmt: CheckSubrange
            key##1_0_0 := $Box(w#1_0_0);
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call $rhs##1_0_0 := Call$$_module.Map.Find(Tclass._module.Word(), TSeq(Tclass._module.Word()), glossary#0, key##1_0_0);
            // TrCallStmt: After ProcessCallStmt
            r#1_0_0 := $rhs##1_0_0;
            assume {:captureState "b8.dfy(112,33)"} true;
            // ----- if statement ----- b8.dfy(113,9)
            assume true;
            if (r#1_0_0 == Lit(#_module.Maybe.None()))
            {
                // ----- call statement ----- b8.dfy(114,36)
                // TrCallStmt: Before ProcessCallStmt
                assert wr#0 != null;
                assume true;
                // ProcessCallStmt: CheckSubrange
                tag##1_0_0_0 := w#1_0_0;
                assume true;
                // ProcessCallStmt: CheckSubrange
                w##1_0_0_0 := w#1_0_0;
                assert (forall<alpha> $o: ref, $f: Field alpha ::
                  $o != null
                       && read($Heap, $o, alloc)
                       && read($Heap, wr#0, _module.WriterStream.footprint)[$Box($o)]
                     ==> $_Frame[$o, $f]);
                // ProcessCallStmt: Make the call
                call Call$$_module.WriterStream.PutWordInsideHyperlink(wr#0, tag##1_0_0_0, w##1_0_0_0);
                // TrCallStmt: After ProcessCallStmt
                assume {:captureState "b8.dfy(114,41)"} true;
            }
            else
            {
                // ----- call statement ----- b8.dfy(116,21)
                // TrCallStmt: Before ProcessCallStmt
                assert wr#0 != null;
                assume true;
                // ProcessCallStmt: CheckSubrange
                w##1_0_0 := w#1_0_0;
                assert (forall<alpha> $o: ref, $f: Field alpha ::
                  $o != null
                       && read($Heap, $o, alloc)
                       && read($Heap, wr#0, _module.WriterStream.footprint)[$Box($o)]
                     ==> $_Frame[$o, $f]);
                // ProcessCallStmt: Make the call
                call Call$$_module.WriterStream.PutWord(wr#0, w##1_0_0);
                // TrCallStmt: After ProcessCallStmt
                assume {:captureState "b8.dfy(116,23)"} true;
            }

            // ----- assignment statement ----- b8.dfy(118,10)
            assume true;
            assume true;
            i#1_0 := i#1_0 + 1;
            assume {:captureState "b8.dfy(118,16)"} true;
            // ----- loop termination check ----- b8.dfy(102,7)
            assert 0 <= $decr$loop#1_00 || Seq#Length(definition#1_0) - i#1_0 == $decr$loop#1_00;
            assert Seq#Length(definition#1_0) - i#1_0 < $decr$loop#1_00;
            assume _module.WriterStream.Valid#canCall($Heap, wr#0);
            assume _module.Map.Valid#canCall(Tclass._module.Word(), TSeq(Tclass._module.Word()), $Heap, glossary#0);
            assume true;
            assume (forall d#1_1: Seq Box ::
              { Seq#Contains(d#1_1, $Box(null)) }
                { Seq#Contains(read($Heap, glossary#0, _module.Map.values), $Box(d#1_1)) }
              true);
            assume true;
            assume true;
            assume (forall k#1_1: ref ::
              { Seq#Contains(read($Heap, glossary#0, _module.Map.keys), $Box(k#1_1)) }
                { Seq#Contains(read($Heap, q#0, _module.Queue.contents), $Box(k#1_1)) }
              true);
        }

        // ----- loop termination check ----- b8.dfy(83,5)
        assert 0 <= $decr$loop#10
           || Seq#Length(read($Heap, q#0, _module.Queue.contents)) - 0 == $decr$loop#10;
        assert Seq#Length(read($Heap, q#0, _module.Queue.contents)) - 0 < $decr$loop#10;
        assume _module.WriterStream.Valid#canCall($Heap, wr#0);
        assume _module.Map.Valid#canCall(Tclass._module.Word(), TSeq(Tclass._module.Word()), $Heap, glossary#0);
        assume true;
        assume (forall d#3: Seq Box ::
          { Seq#Contains(d#3, $Box(null)) }
            { Seq#Contains(read($Heap, glossary#0, _module.Map.values), $Box(d#3)) }
          true);
        assume true;
        assume (forall k#3: ref ::
          { Seq#Contains(read($Heap, glossary#0, _module.Map.keys), $Box(k#3)) }
            { Seq#Contains(read($Heap, q#0, _module.Queue.contents), $Box(k#3)) }
          true);
    }

    // ----- call statement ----- b8.dfy(121,13)
    // TrCallStmt: Before ProcessCallStmt
    assert wr#0 != null;
    assert (forall<alpha> $o: ref, $f: Field alpha ::
      $o != null
           && read($Heap, $o, alloc)
           && read($Heap, wr#0, _module.WriterStream.footprint)[$Box($o)]
         ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.WriterStream.Close(wr#0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "b8.dfy(121,14)"} true;
}



procedure CheckWellformed$$_module.Glossary.readDefinition(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Glossary())
         && $IsAlloc(this, Tclass._module.Glossary(), $Heap),
    rs#0: ref
       where $Is(rs#0, Tclass._module.ReaderStream())
         && $IsAlloc(rs#0, Tclass._module.ReaderStream(), $Heap))
   returns (term#0: ref
       where $Is(term#0, Tclass._module.Word())
         && $IsAlloc(term#0, Tclass._module.Word(), $Heap),
    definition#0: Seq Box
       where $Is(definition#0, TSeq(Tclass._module.Word()))
         && $IsAlloc(definition#0, TSeq(Tclass._module.Word()), $Heap));
  free requires 9 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.Glossary.readDefinition(this: ref, rs#0: ref) returns (term#0: ref, definition#0: Seq Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: readDefinition, CheckWellformed$$_module.Glossary.readDefinition
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc)
         ==> read($Heap, rs#0, _module.ReaderStream.footprint)[$Box($o)]);
    assume {:captureState "b8.dfy(125,9): initial state"} true;
    assume rs#0 != null;
    assert rs#0 != null;
    assume _module.ReaderStream.Valid#canCall($Heap, rs#0);
    assume _module.ReaderStream.Valid($Heap, rs#0);
    assert rs#0 != null;
    havoc $Heap;
    assume (forall<alpha> $o: ref, $f: Field alpha ::
      { read($Heap, $o, $f) }
      $o != null && read(old($Heap), $o, alloc)
         ==> read($Heap, $o, $f) == read(old($Heap), $o, $f)
           || read(old($Heap), rs#0, _module.ReaderStream.footprint)[$Box($o)]);
    assume $HeapSucc(old($Heap), $Heap);
    havoc term#0, definition#0;
    assume {:captureState "b8.dfy(128,23): post-state"} true;
    assert rs#0 != null;
    assume _module.ReaderStream.Valid#canCall($Heap, rs#0);
    assume _module.ReaderStream.Valid($Heap, rs#0);
    assert rs#0 != null;
    assert rs#0 != null;
    assert $IsAlloc(rs#0, Tclass._module.ReaderStream(), old($Heap));
    assume (forall $o: ref ::
      { read(old($Heap), $o, alloc) }
      read($Heap, rs#0, _module.ReaderStream.footprint)[$Box($o)]
           && !read(old($Heap), rs#0, _module.ReaderStream.footprint)[$Box($o)]
         ==> $o != null && !read(old($Heap), $o, alloc));
    if (*)
    {
        assume term#0 != null;
        assume !Seq#Contains(definition#0, $Box(null));
    }
    else
    {
        assume term#0 != null ==> !Seq#Contains(definition#0, $Box(null));
    }
}



procedure Call$$_module.Glossary.readDefinition(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Glossary())
         && $IsAlloc(this, Tclass._module.Glossary(), $Heap),
    rs#0: ref
       where $Is(rs#0, Tclass._module.ReaderStream())
         && $IsAlloc(rs#0, Tclass._module.ReaderStream(), $Heap))
   returns (term#0: ref
       where $Is(term#0, Tclass._module.Word())
         && $IsAlloc(term#0, Tclass._module.Word(), $Heap),
    definition#0: Seq Box
       where $Is(definition#0, TSeq(Tclass._module.Word()))
         && $IsAlloc(definition#0, TSeq(Tclass._module.Word()), $Heap));
  // user-defined preconditions
  requires rs#0 != null;
  requires _module.ReaderStream.Valid#canCall($Heap, rs#0)
     ==> _module.ReaderStream.Valid($Heap, rs#0)
       || !read($Heap, rs#0, _module.ReaderStream.footprint)[$Box(null)];
  requires _module.ReaderStream.Valid#canCall($Heap, rs#0)
     ==> _module.ReaderStream.Valid($Heap, rs#0)
       || read($Heap, rs#0, _module.ReaderStream.footprint)[$Box(rs#0)];
  requires _module.ReaderStream.Valid#canCall($Heap, rs#0)
     ==> _module.ReaderStream.Valid($Heap, rs#0)
       || read($Heap, rs#0, _module.ReaderStream.isOpen);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.ReaderStream.Valid#canCall($Heap, rs#0);
  free ensures _module.ReaderStream.Valid#canCall($Heap, rs#0)
     &&
    _module.ReaderStream.Valid($Heap, rs#0)
     &&
    !read($Heap, rs#0, _module.ReaderStream.footprint)[$Box(null)]
     && read($Heap, rs#0, _module.ReaderStream.footprint)[$Box(rs#0)]
     && read($Heap, rs#0, _module.ReaderStream.isOpen);
  ensures (forall $o: ref ::
    { read(old($Heap), $o, alloc) }
    read($Heap, rs#0, _module.ReaderStream.footprint)[$Box($o)]
         && !read(old($Heap), rs#0, _module.ReaderStream.footprint)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures true;
  ensures term#0 != null ==> !Seq#Contains(definition#0, $Box(null));
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f)
         || read(old($Heap), rs#0, _module.ReaderStream.footprint)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Glossary.readDefinition(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Glossary())
         && $IsAlloc(this, Tclass._module.Glossary(), $Heap),
    rs#0: ref
       where $Is(rs#0, Tclass._module.ReaderStream())
         && $IsAlloc(rs#0, Tclass._module.ReaderStream(), $Heap))
   returns (term#0: ref
       where $Is(term#0, Tclass._module.Word())
         && $IsAlloc(term#0, Tclass._module.Word(), $Heap),
    definition#0: Seq Box
       where $Is(definition#0, TSeq(Tclass._module.Word()))
         && $IsAlloc(definition#0, TSeq(Tclass._module.Word()), $Heap),
    $_reverifyPost: bool);
  free requires 9 == $FunctionContextHeight;
  // user-defined preconditions
  requires rs#0 != null;
  free requires _module.ReaderStream.Valid#canCall($Heap, rs#0)
     &&
    _module.ReaderStream.Valid($Heap, rs#0)
     &&
    !read($Heap, rs#0, _module.ReaderStream.footprint)[$Box(null)]
     && read($Heap, rs#0, _module.ReaderStream.footprint)[$Box(rs#0)]
     && read($Heap, rs#0, _module.ReaderStream.isOpen);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.ReaderStream.Valid#canCall($Heap, rs#0);
  ensures _module.ReaderStream.Valid#canCall($Heap, rs#0)
     ==> _module.ReaderStream.Valid($Heap, rs#0)
       || !read($Heap, rs#0, _module.ReaderStream.footprint)[$Box(null)];
  ensures _module.ReaderStream.Valid#canCall($Heap, rs#0)
     ==> _module.ReaderStream.Valid($Heap, rs#0)
       || read($Heap, rs#0, _module.ReaderStream.footprint)[$Box(rs#0)];
  ensures _module.ReaderStream.Valid#canCall($Heap, rs#0)
     ==> _module.ReaderStream.Valid($Heap, rs#0)
       || read($Heap, rs#0, _module.ReaderStream.isOpen);
  ensures (forall $o: ref ::
    { read(old($Heap), $o, alloc) }
    read($Heap, rs#0, _module.ReaderStream.footprint)[$Box($o)]
         && !read(old($Heap), rs#0, _module.ReaderStream.footprint)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures true;
  ensures term#0 != null ==> !Seq#Contains(definition#0, $Box(null));
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f)
         || read(old($Heap), rs#0, _module.ReaderStream.footprint)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Glossary.readDefinition(this: ref, rs#0: ref)
   returns (term#0: ref, definition#0: Seq Box, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs##0: ref
     where $Is($rhs##0, Tclass._module.Word())
       && $IsAlloc($rhs##0, Tclass._module.Word(), $Heap);
  var $PreLoopHeap$loop#0_0: Heap;
  var $w$loop#0_0: bool;
  var w#0_0_0: ref
     where $Is(w#0_0_0, Tclass._module.Word())
       && $IsAlloc(w#0_0_0, Tclass._module.Word(), $Heap);
  var $rhs##0_0_0: ref
     where $Is($rhs##0_0_0, Tclass._module.Word())
       && $IsAlloc($rhs##0_0_0, Tclass._module.Word(), $Heap);

    // AddMethodImpl: readDefinition, Impl$$_module.Glossary.readDefinition
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc)
         ==> read($Heap, rs#0, _module.ReaderStream.footprint)[$Box($o)]);
    assume {:captureState "b8.dfy(131,2): initial state"} true;
    $_reverifyPost := false;
    // ----- call statement ----- b8.dfy(132,23)
    assume true;
    // TrCallStmt: Adding lhs Microsoft.Dafny.IdentifierExpr with type Word
    // TrCallStmt: Before ProcessCallStmt
    assert rs#0 != null;
    assert (forall<alpha> $o: ref, $f: Field alpha ::
      $o != null
           && read($Heap, $o, alloc)
           && read($Heap, rs#0, _module.ReaderStream.footprint)[$Box($o)]
         ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##0 := Call$$_module.ReaderStream.GetWord(rs#0);
    // TrCallStmt: After ProcessCallStmt
    term#0 := $rhs##0;
    assume {:captureState "b8.dfy(132,24)"} true;
    // ----- if statement ----- b8.dfy(133,5)
    assume true;
    if (term#0 != null)
    {
        // ----- assignment statement ----- b8.dfy(134,18)
        assume true;
        assume true;
        definition#0 := Lit(Seq#Empty(): Seq Box);
        assume {:captureState "b8.dfy(134,22)"} true;
        // ----- while statement ----- b8.dfy(135,7)
        // Assume Fuel Constant
        $PreLoopHeap$loop#0_0 := $Heap;
        havoc $w$loop#0_0;
        while (true)
          free invariant $w$loop#0_0 ==> _module.ReaderStream.Valid#canCall($Heap, rs#0);
          invariant $w$loop#0_0
             ==>
            _module.ReaderStream.Valid#canCall($Heap, rs#0)
             ==> _module.ReaderStream.Valid($Heap, rs#0)
               || !read($Heap, rs#0, _module.ReaderStream.footprint)[$Box(null)];
          invariant $w$loop#0_0
             ==>
            _module.ReaderStream.Valid#canCall($Heap, rs#0)
             ==> _module.ReaderStream.Valid($Heap, rs#0)
               || read($Heap, rs#0, _module.ReaderStream.footprint)[$Box(rs#0)];
          invariant $w$loop#0_0
             ==>
            _module.ReaderStream.Valid#canCall($Heap, rs#0)
             ==> _module.ReaderStream.Valid($Heap, rs#0)
               || read($Heap, rs#0, _module.ReaderStream.isOpen);
          free invariant $w$loop#0_0
             ==> _module.ReaderStream.Valid#canCall($Heap, rs#0)
               &&
              _module.ReaderStream.Valid($Heap, rs#0)
               &&
              !read($Heap, rs#0, _module.ReaderStream.footprint)[$Box(null)]
               && read($Heap, rs#0, _module.ReaderStream.footprint)[$Box(rs#0)]
               && read($Heap, rs#0, _module.ReaderStream.isOpen);
          invariant $w$loop#0_0
             ==> (forall $o: ref ::
              { read(old($Heap), $o, alloc) }
              read($Heap, rs#0, _module.ReaderStream.footprint)[$Box($o)]
                   && !read(old($Heap), rs#0, _module.ReaderStream.footprint)[$Box($o)]
                 ==> $o != null && !read(old($Heap), $o, alloc));
          free invariant $w$loop#0_0 ==> true;
          invariant $w$loop#0_0 ==> !Seq#Contains(definition#0, $Box(null));
          free invariant (forall<alpha> $o: ref, $f: Field alpha ::
            { read($Heap, $o, $f) }
            $o != null && read(old($Heap), $o, alloc)
               ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0_0, $o, $f)
                 || read(old($Heap), rs#0, _module.ReaderStream.footprint)[$Box($o)]);
          free invariant $HeapSucc($PreLoopHeap$loop#0_0, $Heap);
          free invariant (forall<alpha> $o: ref, $f: Field alpha ::
            { read($Heap, $o, $f) }
            $o != null && read($PreLoopHeap$loop#0_0, $o, alloc)
               ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0_0, $o, $f) || $_Frame[$o, $f]);
        {
            assume {:captureState "b8.dfy(135,6): after some loop iterations"} true;
            if (!$w$loop#0_0)
            {
                assert {:subsumption 0} rs#0 != null;
                assume _module.ReaderStream.Valid#canCall($Heap, rs#0);
                if (_module.ReaderStream.Valid($Heap, rs#0))
                {
                    assert {:subsumption 0} rs#0 != null;
                    assert {:subsumption 0} rs#0 != null;
                    assert $IsAlloc(rs#0, Tclass._module.ReaderStream(), old($Heap));
                }

                assume _module.ReaderStream.Valid#canCall($Heap, rs#0);
                assume _module.ReaderStream.Valid($Heap, rs#0)
                   && (forall $o: ref ::
                    { read(old($Heap), $o, alloc) }
                    read($Heap, rs#0, _module.ReaderStream.footprint)[$Box($o)]
                         && !read(old($Heap), rs#0, _module.ReaderStream.footprint)[$Box($o)]
                       ==> $o != null && !read(old($Heap), $o, alloc));
                assume true;
                assume !Seq#Contains(definition#0, $Box(null));
                assume true;
                assume false;
            }

            assume true;
            if (!Lit(true))
            {
                break;
            }

            // ----- call statement ----- b8.dfy(140,28)
            assume true;
            // TrCallStmt: Adding lhs Microsoft.Dafny.AutoGhostIdentifierExpr with type Word
            // TrCallStmt: Before ProcessCallStmt
            assert rs#0 != null;
            assert (forall<alpha> $o: ref, $f: Field alpha ::
              $o != null
                   && read($Heap, $o, alloc)
                   && read($Heap, rs#0, _module.ReaderStream.footprint)[$Box($o)]
                 ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call $rhs##0_0_0 := Call$$_module.ReaderStream.GetWord(rs#0);
            // TrCallStmt: After ProcessCallStmt
            w#0_0_0 := $rhs##0_0_0;
            assume {:captureState "b8.dfy(140,29)"} true;
            // ----- if statement ----- b8.dfy(141,9)
            assume true;
            if (w#0_0_0 == null)
            {
                // ----- break statement ----- b8.dfy(142,11)
                goto after_0_0_0_0;
            }
            else
            {
            }

            // ----- assignment statement ----- b8.dfy(144,20)
            assume true;
            assume true;
            definition#0 := Seq#Append(definition#0, Seq#Build(Seq#Empty(): Seq Box, $Box(w#0_0_0)));
            assume {:captureState "b8.dfy(144,38)"} true;
            assume _module.ReaderStream.Valid#canCall($Heap, rs#0);
            assume true;
        }

      after_0_0_0_0:
    }
    else
    {
    }
}



const unique class._module.Word: ClassName;

// Word: Class $Is
axiom (forall $o: ref ::
  { $Is($o, Tclass._module.Word()) }
  $Is($o, Tclass._module.Word())
     <==> $o == null || dtype($o) == Tclass._module.Word());

// Word: Class $IsAlloc
axiom (forall $o: ref, $h: Heap ::
  { $IsAlloc($o, Tclass._module.Word(), $h) }
  $IsAlloc($o, Tclass._module.Word(), $h) <==> $o == null || read($h, $o, alloc));

// function declaration for _module.Word.AtMost
function _module.Word.AtMost(this: ref, w#0: ref) : bool;

function _module.Word.AtMost#canCall(this: ref, w#0: ref) : bool;

// consequence axiom for _module.Word.AtMost
axiom 1 <= $FunctionContextHeight
   ==> (forall this: ref, w#0: ref ::
    { _module.Word.AtMost(this, w#0) }
    _module.Word.AtMost#canCall(this, w#0)
         || (1 != $FunctionContextHeight
           &&
          this != null
           && $Is(this, Tclass._module.Word())
           && $Is(w#0, Tclass._module.Word()))
       ==> true);

function _module.Word.AtMost#requires(ref, ref) : bool;

// #requires axiom for _module.Word.AtMost
axiom (forall this: ref, w#0: ref ::
  { _module.Word.AtMost#requires(this, w#0) }
  this != null
       && $Is(this, Tclass._module.Word())
       && $Is(w#0, Tclass._module.Word())
     ==> _module.Word.AtMost#requires(this, w#0) == true);

procedure CheckWellformed$$_module.Word.AtMost(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Word())
         && $IsAlloc(this, Tclass._module.Word(), $Heap),
    w#0: ref where $Is(w#0, Tclass._module.Word()));
  free requires 1 == $FunctionContextHeight;
  modifies $Heap, $Tick;



const unique class._module.ReaderStream: ClassName;

// ReaderStream: Class $Is
axiom (forall $o: ref ::
  { $Is($o, Tclass._module.ReaderStream()) }
  $Is($o, Tclass._module.ReaderStream())
     <==> $o == null || dtype($o) == Tclass._module.ReaderStream());

// ReaderStream: Class $IsAlloc
axiom (forall $o: ref, $h: Heap ::
  { $IsAlloc($o, Tclass._module.ReaderStream(), $h) }
  $IsAlloc($o, Tclass._module.ReaderStream(), $h)
     <==> $o == null || read($h, $o, alloc));

const _module.ReaderStream.footprint: Field (Set Box);

// ReaderStream.footprint: Allocation axiom
axiom (forall $h: Heap, $o: ref ::
  { read($h, $o, _module.ReaderStream.footprint) }
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.ReaderStream()
     ==> $Is(read($h, $o, _module.ReaderStream.footprint), TSet(Tclass._System.object()))
       && (read($h, $o, alloc)
         ==> $IsAlloc(read($h, $o, _module.ReaderStream.footprint), TSet(Tclass._System.object()), $h)));

const _module.ReaderStream.isOpen: Field bool;

// ReaderStream.isOpen: Allocation axiom
axiom (forall $h: Heap, $o: ref ::
  { read($h, $o, _module.ReaderStream.isOpen) }
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.ReaderStream()
     ==> $Is(read($h, $o, _module.ReaderStream.isOpen), TBool)
       && (read($h, $o, alloc)
         ==> $IsAlloc(read($h, $o, _module.ReaderStream.isOpen), TBool, $h)));

// function declaration for _module.ReaderStream.Valid
function _module.ReaderStream.Valid($heap: Heap, this: ref) : bool;

function _module.ReaderStream.Valid#canCall($heap: Heap, this: ref) : bool;

// frame axiom for _module.ReaderStream.Valid
axiom (forall $h0: Heap, $h1: Heap, this: ref ::
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.ReaderStream.Valid($h1, this) }
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       &&
      this != null
       && $Is(this, Tclass._module.ReaderStream())
       &&
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==>
    (forall<alpha> $o: ref, $f: Field alpha ::
      $o != null
           && ($o == this || read($h0, this, _module.ReaderStream.footprint)[$Box($o)])
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.ReaderStream.Valid($h0, this) == _module.ReaderStream.Valid($h1, this));

// consequence axiom for _module.ReaderStream.Valid
axiom 3 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref ::
    { _module.ReaderStream.Valid($Heap, this) }
    _module.ReaderStream.Valid#canCall($Heap, this)
         || (3 != $FunctionContextHeight
           &&
          $IsGoodHeap($Heap)
           &&
          this != null
           &&
          $Is(this, Tclass._module.ReaderStream())
           && $IsAlloc(this, Tclass._module.ReaderStream(), $Heap))
       ==> true);

function _module.ReaderStream.Valid#requires(Heap, ref) : bool;

// #requires axiom for _module.ReaderStream.Valid
axiom (forall $Heap: Heap, this: ref ::
  { _module.ReaderStream.Valid#requires($Heap, this) }
  $IsGoodHeap($Heap)
       &&
      this != null
       &&
      $Is(this, Tclass._module.ReaderStream())
       && $IsAlloc(this, Tclass._module.ReaderStream(), $Heap)
     ==> _module.ReaderStream.Valid#requires($Heap, this) == true);

// definition axiom for _module.ReaderStream.Valid(revealed)
axiom 3 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref ::
    { _module.ReaderStream.Valid($Heap, this) }
    _module.ReaderStream.Valid#canCall($Heap, this)
         || (3 != $FunctionContextHeight
           &&
          $IsGoodHeap($Heap)
           &&
          this != null
           &&
          $Is(this, Tclass._module.ReaderStream())
           && $IsAlloc(this, Tclass._module.ReaderStream(), $Heap))
       ==> _module.ReaderStream.Valid($Heap, this)
         == (
          !read($Heap, this, _module.ReaderStream.footprint)[$Box(null)]
           && read($Heap, this, _module.ReaderStream.footprint)[$Box(this)]
           && read($Heap, this, _module.ReaderStream.isOpen)));

procedure CheckWellformed$$_module.ReaderStream.Valid(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.ReaderStream())
         && $IsAlloc(this, Tclass._module.ReaderStream(), $Heap));
  free requires 3 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.ReaderStream.Valid(this: ref)
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
    assume {:captureState "b8.dfy(159,12): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc)
         ==> $o == this || read($Heap, this, _module.ReaderStream.footprint)[$Box($o)]);
    b$reqreads#0 := $_Frame[this, _module.ReaderStream.footprint];
    assert b$reqreads#0;
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
          $o != null && read($Heap, $o, alloc)
             ==> $o == this || read($Heap, this, _module.ReaderStream.footprint)[$Box($o)]);
        b$reqreads#1 := $_Frame[this, _module.ReaderStream.footprint];
        if (!read($Heap, this, _module.ReaderStream.footprint)[$Box(null)])
        {
            b$reqreads#2 := $_Frame[this, _module.ReaderStream.footprint];
        }

        if (!read($Heap, this, _module.ReaderStream.footprint)[$Box(null)]
           && read($Heap, this, _module.ReaderStream.footprint)[$Box(this)])
        {
            b$reqreads#3 := $_Frame[this, _module.ReaderStream.isOpen];
        }

        assume _module.ReaderStream.Valid($Heap, this)
           == (
            !read($Heap, this, _module.ReaderStream.footprint)[$Box(null)]
             && read($Heap, this, _module.ReaderStream.footprint)[$Box(this)]
             && read($Heap, this, _module.ReaderStream.isOpen));
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(_module.ReaderStream.Valid($Heap, this), TBool);
        assert b$reqreads#1;
        assert b$reqreads#2;
        assert b$reqreads#3;
    }
}



procedure CheckWellformed$$_module.ReaderStream.Open(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.ReaderStream())
         && $IsAlloc(this, Tclass._module.ReaderStream(), $Heap));
  free requires 4 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.ReaderStream.Open(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.ReaderStream())
         && $IsAlloc(this, Tclass._module.ReaderStream(), $Heap));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.ReaderStream.Valid#canCall($Heap, this);
  free ensures _module.ReaderStream.Valid#canCall($Heap, this)
     &&
    _module.ReaderStream.Valid($Heap, this)
     &&
    !read($Heap, this, _module.ReaderStream.footprint)[$Box(null)]
     && read($Heap, this, _module.ReaderStream.footprint)[$Box(this)]
     && read($Heap, this, _module.ReaderStream.isOpen);
  ensures (forall $o: ref ::
    { read(old($Heap), $o, alloc) }
    read($Heap, this, _module.ReaderStream.footprint)[$Box($o)] && $o != this
       ==> $o != null && !read(old($Heap), $o, alloc));
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f) || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.ReaderStream.Open(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.ReaderStream())
         && $IsAlloc(this, Tclass._module.ReaderStream(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 4 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.ReaderStream.Valid#canCall($Heap, this);
  ensures _module.ReaderStream.Valid#canCall($Heap, this)
     ==> _module.ReaderStream.Valid($Heap, this)
       || !read($Heap, this, _module.ReaderStream.footprint)[$Box(null)];
  ensures _module.ReaderStream.Valid#canCall($Heap, this)
     ==> _module.ReaderStream.Valid($Heap, this)
       || read($Heap, this, _module.ReaderStream.footprint)[$Box(this)];
  ensures _module.ReaderStream.Valid#canCall($Heap, this)
     ==> _module.ReaderStream.Valid($Heap, this)
       || read($Heap, this, _module.ReaderStream.isOpen);
  ensures (forall $o: ref ::
    { read(old($Heap), $o, alloc) }
    read($Heap, this, _module.ReaderStream.footprint)[$Box($o)] && $o != this
       ==> $o != null && !read(old($Heap), $o, alloc));
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f) || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.ReaderStream.Open(this: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs#0: Set Box where $Is($rhs#0, TSet(Tclass._System.object()));
  var $rhs#1: bool;

    // AddMethodImpl: Open, Impl$$_module.ReaderStream.Open
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> $o == this);
    assume {:captureState "b8.dfy(168,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- b8.dfy(169,15)
    assume true;
    assert $_Frame[this, _module.ReaderStream.footprint];
    assume true;
    $rhs#0 := Set#UnionOne(Set#Empty(): Set Box, $Box(this));
    $Heap := update($Heap, this, _module.ReaderStream.footprint, $rhs#0);
    assume $IsGoodHeap($Heap);
    assume {:captureState "b8.dfy(169,23)"} true;
    // ----- assignment statement ----- b8.dfy(170,12)
    assume true;
    assert $_Frame[this, _module.ReaderStream.isOpen];
    assume true;
    $rhs#1 := Lit(true);
    $Heap := update($Heap, this, _module.ReaderStream.isOpen, $rhs#1);
    assume $IsGoodHeap($Heap);
    assume {:captureState "b8.dfy(170,17)"} true;
}



procedure CheckWellformed$$_module.ReaderStream.GetWord(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.ReaderStream())
         && $IsAlloc(this, Tclass._module.ReaderStream(), $Heap))
   returns (x#0: ref
       where $Is(x#0, Tclass._module.Word()) && $IsAlloc(x#0, Tclass._module.Word(), $Heap));
  free requires 8 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.ReaderStream.GetWord(this: ref) returns (x#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: GetWord, CheckWellformed$$_module.ReaderStream.GetWord
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc)
         ==> read($Heap, this, _module.ReaderStream.footprint)[$Box($o)]);
    assume {:captureState "b8.dfy(173,9): initial state"} true;
    assume _module.ReaderStream.Valid#canCall($Heap, this);
    assume _module.ReaderStream.Valid($Heap, this);
    havoc $Heap;
    assume (forall<alpha> $o: ref, $f: Field alpha ::
      { read($Heap, $o, $f) }
      $o != null && read(old($Heap), $o, alloc)
         ==> read($Heap, $o, $f) == read(old($Heap), $o, $f)
           || read(old($Heap), this, _module.ReaderStream.footprint)[$Box($o)]);
    assume $HeapSucc(old($Heap), $Heap);
    havoc x#0;
    assume {:captureState "b8.dfy(176,20): post-state"} true;
    assume _module.ReaderStream.Valid#canCall($Heap, this);
    assume _module.ReaderStream.Valid($Heap, this);
    assert $IsAlloc(this, Tclass._module.ReaderStream(), old($Heap));
    assume (forall $o: ref ::
      { read(old($Heap), $o, alloc) }
      read($Heap, this, _module.ReaderStream.footprint)[$Box($o)]
           && !read(old($Heap), this, _module.ReaderStream.footprint)[$Box($o)]
         ==> $o != null && !read(old($Heap), $o, alloc));
}



procedure Call$$_module.ReaderStream.GetWord(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.ReaderStream())
         && $IsAlloc(this, Tclass._module.ReaderStream(), $Heap))
   returns (x#0: ref
       where $Is(x#0, Tclass._module.Word()) && $IsAlloc(x#0, Tclass._module.Word(), $Heap));
  // user-defined preconditions
  requires _module.ReaderStream.Valid#canCall($Heap, this)
     ==> _module.ReaderStream.Valid($Heap, this)
       || !read($Heap, this, _module.ReaderStream.footprint)[$Box(null)];
  requires _module.ReaderStream.Valid#canCall($Heap, this)
     ==> _module.ReaderStream.Valid($Heap, this)
       || read($Heap, this, _module.ReaderStream.footprint)[$Box(this)];
  requires _module.ReaderStream.Valid#canCall($Heap, this)
     ==> _module.ReaderStream.Valid($Heap, this)
       || read($Heap, this, _module.ReaderStream.isOpen);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.ReaderStream.Valid#canCall($Heap, this);
  free ensures _module.ReaderStream.Valid#canCall($Heap, this)
     &&
    _module.ReaderStream.Valid($Heap, this)
     &&
    !read($Heap, this, _module.ReaderStream.footprint)[$Box(null)]
     && read($Heap, this, _module.ReaderStream.footprint)[$Box(this)]
     && read($Heap, this, _module.ReaderStream.isOpen);
  ensures (forall $o: ref ::
    { read(old($Heap), $o, alloc) }
    read($Heap, this, _module.ReaderStream.footprint)[$Box($o)]
         && !read(old($Heap), this, _module.ReaderStream.footprint)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f)
         || read(old($Heap), this, _module.ReaderStream.footprint)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.ReaderStream.GetWord(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.ReaderStream())
         && $IsAlloc(this, Tclass._module.ReaderStream(), $Heap))
   returns (x#0: ref
       where $Is(x#0, Tclass._module.Word()) && $IsAlloc(x#0, Tclass._module.Word(), $Heap),
    $_reverifyPost: bool);
  free requires 8 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.ReaderStream.Valid#canCall($Heap, this)
     &&
    _module.ReaderStream.Valid($Heap, this)
     &&
    !read($Heap, this, _module.ReaderStream.footprint)[$Box(null)]
     && read($Heap, this, _module.ReaderStream.footprint)[$Box(this)]
     && read($Heap, this, _module.ReaderStream.isOpen);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.ReaderStream.Valid#canCall($Heap, this);
  ensures _module.ReaderStream.Valid#canCall($Heap, this)
     ==> _module.ReaderStream.Valid($Heap, this)
       || !read($Heap, this, _module.ReaderStream.footprint)[$Box(null)];
  ensures _module.ReaderStream.Valid#canCall($Heap, this)
     ==> _module.ReaderStream.Valid($Heap, this)
       || read($Heap, this, _module.ReaderStream.footprint)[$Box(this)];
  ensures _module.ReaderStream.Valid#canCall($Heap, this)
     ==> _module.ReaderStream.Valid($Heap, this)
       || read($Heap, this, _module.ReaderStream.isOpen);
  ensures (forall $o: ref ::
    { read(old($Heap), $o, alloc) }
    read($Heap, this, _module.ReaderStream.footprint)[$Box($o)]
         && !read(old($Heap), this, _module.ReaderStream.footprint)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f)
         || read(old($Heap), this, _module.ReaderStream.footprint)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.ReaderStream.GetWord(this: ref) returns (x#0: ref, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: GetWord, Impl$$_module.ReaderStream.GetWord
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc)
         ==> read($Heap, this, _module.ReaderStream.footprint)[$Box($o)]);
    assume {:captureState "b8.dfy(177,2): initial state"} true;
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.ReaderStream.Close(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.ReaderStream())
         && $IsAlloc(this, Tclass._module.ReaderStream(), $Heap));
  free requires 14 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.ReaderStream.Close(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.ReaderStream())
         && $IsAlloc(this, Tclass._module.ReaderStream(), $Heap));
  // user-defined preconditions
  requires _module.ReaderStream.Valid#canCall($Heap, this)
     ==> _module.ReaderStream.Valid($Heap, this)
       || !read($Heap, this, _module.ReaderStream.footprint)[$Box(null)];
  requires _module.ReaderStream.Valid#canCall($Heap, this)
     ==> _module.ReaderStream.Valid($Heap, this)
       || read($Heap, this, _module.ReaderStream.footprint)[$Box(this)];
  requires _module.ReaderStream.Valid#canCall($Heap, this)
     ==> _module.ReaderStream.Valid($Heap, this)
       || read($Heap, this, _module.ReaderStream.isOpen);
  modifies $Heap, $Tick;
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f)
         || read(old($Heap), this, _module.ReaderStream.footprint)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.ReaderStream.Close(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.ReaderStream())
         && $IsAlloc(this, Tclass._module.ReaderStream(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 14 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.ReaderStream.Valid#canCall($Heap, this)
     &&
    _module.ReaderStream.Valid($Heap, this)
     &&
    !read($Heap, this, _module.ReaderStream.footprint)[$Box(null)]
     && read($Heap, this, _module.ReaderStream.footprint)[$Box(this)]
     && read($Heap, this, _module.ReaderStream.isOpen);
  modifies $Heap, $Tick;
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f)
         || read(old($Heap), this, _module.ReaderStream.footprint)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.ReaderStream.Close(this: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs#0: bool;

    // AddMethodImpl: Close, Impl$$_module.ReaderStream.Close
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc)
         ==> read($Heap, this, _module.ReaderStream.footprint)[$Box($o)]);
    assume {:captureState "b8.dfy(183,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- b8.dfy(184,12)
    assume true;
    assert $_Frame[this, _module.ReaderStream.isOpen];
    assume true;
    $rhs#0 := Lit(false);
    $Heap := update($Heap, this, _module.ReaderStream.isOpen, $rhs#0);
    assume $IsGoodHeap($Heap);
    assume {:captureState "b8.dfy(184,19)"} true;
}



const unique class._module.WriterStream: ClassName;

// WriterStream: Class $Is
axiom (forall $o: ref ::
  { $Is($o, Tclass._module.WriterStream()) }
  $Is($o, Tclass._module.WriterStream())
     <==> $o == null || dtype($o) == Tclass._module.WriterStream());

// WriterStream: Class $IsAlloc
axiom (forall $o: ref, $h: Heap ::
  { $IsAlloc($o, Tclass._module.WriterStream(), $h) }
  $IsAlloc($o, Tclass._module.WriterStream(), $h)
     <==> $o == null || read($h, $o, alloc));

const _module.WriterStream.footprint: Field (Set Box);

// WriterStream.footprint: Allocation axiom
axiom (forall $h: Heap, $o: ref ::
  { read($h, $o, _module.WriterStream.footprint) }
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.WriterStream()
     ==> $Is(read($h, $o, _module.WriterStream.footprint), TSet(Tclass._System.object()))
       && (read($h, $o, alloc)
         ==> $IsAlloc(read($h, $o, _module.WriterStream.footprint), TSet(Tclass._System.object()), $h)));

axiom FDim(_module.WriterStream.stream) == 0
   && FieldOfDecl(class._module.WriterStream, field$stream)
     == _module.WriterStream.stream
   && !$IsGhostField(_module.WriterStream.stream);

const _module.WriterStream.stream: Field (Seq Box);

// WriterStream.stream: Allocation axiom
axiom (forall $h: Heap, $o: ref ::
  { read($h, $o, _module.WriterStream.stream) }
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.WriterStream()
     ==> $Is(read($h, $o, _module.WriterStream.stream), TSeq(TInt))
       && (read($h, $o, alloc)
         ==> $IsAlloc(read($h, $o, _module.WriterStream.stream), TSeq(TInt), $h)));

const _module.WriterStream.isOpen: Field bool;

// WriterStream.isOpen: Allocation axiom
axiom (forall $h: Heap, $o: ref ::
  { read($h, $o, _module.WriterStream.isOpen) }
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.WriterStream()
     ==> $Is(read($h, $o, _module.WriterStream.isOpen), TBool)
       && (read($h, $o, alloc)
         ==> $IsAlloc(read($h, $o, _module.WriterStream.isOpen), TBool, $h)));

// function declaration for _module.WriterStream.Valid
function _module.WriterStream.Valid($heap: Heap, this: ref) : bool;

function _module.WriterStream.Valid#canCall($heap: Heap, this: ref) : bool;

// frame axiom for _module.WriterStream.Valid
axiom (forall $h0: Heap, $h1: Heap, this: ref ::
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.WriterStream.Valid($h1, this) }
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       &&
      this != null
       && $Is(this, Tclass._module.WriterStream())
       &&
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==>
    (forall<alpha> $o: ref, $f: Field alpha ::
      $o != null
           && ($o == this || read($h0, this, _module.WriterStream.footprint)[$Box($o)])
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.WriterStream.Valid($h0, this) == _module.WriterStream.Valid($h1, this));

// consequence axiom for _module.WriterStream.Valid
axiom 15 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref ::
    { _module.WriterStream.Valid($Heap, this) }
    _module.WriterStream.Valid#canCall($Heap, this)
         || (15 != $FunctionContextHeight
           &&
          $IsGoodHeap($Heap)
           &&
          this != null
           &&
          $Is(this, Tclass._module.WriterStream())
           && $IsAlloc(this, Tclass._module.WriterStream(), $Heap))
       ==> true);

function _module.WriterStream.Valid#requires(Heap, ref) : bool;

// #requires axiom for _module.WriterStream.Valid
axiom (forall $Heap: Heap, this: ref ::
  { _module.WriterStream.Valid#requires($Heap, this) }
  $IsGoodHeap($Heap)
       &&
      this != null
       &&
      $Is(this, Tclass._module.WriterStream())
       && $IsAlloc(this, Tclass._module.WriterStream(), $Heap)
     ==> _module.WriterStream.Valid#requires($Heap, this) == true);

// definition axiom for _module.WriterStream.Valid(revealed)
axiom 15 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref ::
    { _module.WriterStream.Valid($Heap, this) }
    _module.WriterStream.Valid#canCall($Heap, this)
         || (15 != $FunctionContextHeight
           &&
          $IsGoodHeap($Heap)
           &&
          this != null
           &&
          $Is(this, Tclass._module.WriterStream())
           && $IsAlloc(this, Tclass._module.WriterStream(), $Heap))
       ==> _module.WriterStream.Valid($Heap, this)
         == (
          !read($Heap, this, _module.WriterStream.footprint)[$Box(null)]
           && read($Heap, this, _module.WriterStream.footprint)[$Box(this)]
           && read($Heap, this, _module.WriterStream.isOpen)));

procedure CheckWellformed$$_module.WriterStream.Valid(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.WriterStream())
         && $IsAlloc(this, Tclass._module.WriterStream(), $Heap));
  free requires 15 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.WriterStream.Valid(this: ref)
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
    assume {:captureState "b8.dfy(193,12): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc)
         ==> $o == this || read($Heap, this, _module.WriterStream.footprint)[$Box($o)]);
    b$reqreads#0 := $_Frame[this, _module.WriterStream.footprint];
    assert b$reqreads#0;
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
          $o != null && read($Heap, $o, alloc)
             ==> $o == this || read($Heap, this, _module.WriterStream.footprint)[$Box($o)]);
        b$reqreads#1 := $_Frame[this, _module.WriterStream.footprint];
        if (!read($Heap, this, _module.WriterStream.footprint)[$Box(null)])
        {
            b$reqreads#2 := $_Frame[this, _module.WriterStream.footprint];
        }

        if (!read($Heap, this, _module.WriterStream.footprint)[$Box(null)]
           && read($Heap, this, _module.WriterStream.footprint)[$Box(this)])
        {
            b$reqreads#3 := $_Frame[this, _module.WriterStream.isOpen];
        }

        assume _module.WriterStream.Valid($Heap, this)
           == (
            !read($Heap, this, _module.WriterStream.footprint)[$Box(null)]
             && read($Heap, this, _module.WriterStream.footprint)[$Box(this)]
             && read($Heap, this, _module.WriterStream.isOpen));
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(_module.WriterStream.Valid($Heap, this), TBool);
        assert b$reqreads#1;
        assert b$reqreads#2;
        assert b$reqreads#3;
    }
}



procedure CheckWellformed$$_module.WriterStream.Create(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.WriterStream())
         && $IsAlloc(this, Tclass._module.WriterStream(), $Heap));
  free requires 16 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.WriterStream.Create(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.WriterStream())
         && $IsAlloc(this, Tclass._module.WriterStream(), $Heap));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.WriterStream.Valid#canCall($Heap, this);
  free ensures _module.WriterStream.Valid#canCall($Heap, this)
     &&
    _module.WriterStream.Valid($Heap, this)
     &&
    !read($Heap, this, _module.WriterStream.footprint)[$Box(null)]
     && read($Heap, this, _module.WriterStream.footprint)[$Box(this)]
     && read($Heap, this, _module.WriterStream.isOpen);
  ensures (forall $o: ref ::
    { read(old($Heap), $o, alloc) }
    read($Heap, this, _module.WriterStream.footprint)[$Box($o)] && $o != this
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures true;
  ensures Seq#Equal(read($Heap, this, _module.WriterStream.stream), Seq#Empty(): Seq Box);
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f) || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.WriterStream.Create(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.WriterStream())
         && $IsAlloc(this, Tclass._module.WriterStream(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 16 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.WriterStream.Valid#canCall($Heap, this);
  ensures _module.WriterStream.Valid#canCall($Heap, this)
     ==> _module.WriterStream.Valid($Heap, this)
       || !read($Heap, this, _module.WriterStream.footprint)[$Box(null)];
  ensures _module.WriterStream.Valid#canCall($Heap, this)
     ==> _module.WriterStream.Valid($Heap, this)
       || read($Heap, this, _module.WriterStream.footprint)[$Box(this)];
  ensures _module.WriterStream.Valid#canCall($Heap, this)
     ==> _module.WriterStream.Valid($Heap, this)
       || read($Heap, this, _module.WriterStream.isOpen);
  ensures (forall $o: ref ::
    { read(old($Heap), $o, alloc) }
    read($Heap, this, _module.WriterStream.footprint)[$Box($o)] && $o != this
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures true;
  ensures Seq#Equal(read($Heap, this, _module.WriterStream.stream), Seq#Empty(): Seq Box);
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f) || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.WriterStream.Create(this: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs#0: Seq Box where $Is($rhs#0, TSeq(TInt));
  var $rhs#1: Set Box where $Is($rhs#1, TSet(Tclass._System.object()));
  var $rhs#2: bool;

    // AddMethodImpl: Create, Impl$$_module.WriterStream.Create
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> $o == this);
    assume {:captureState "b8.dfy(203,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- b8.dfy(204,12)
    assume true;
    assert $_Frame[this, _module.WriterStream.stream];
    assume true;
    $rhs#0 := Lit(Seq#Empty(): Seq Box);
    $Heap := update($Heap, this, _module.WriterStream.stream, $rhs#0);
    assume $IsGoodHeap($Heap);
    assume {:captureState "b8.dfy(204,16)"} true;
    // ----- assignment statement ----- b8.dfy(205,15)
    assume true;
    assert $_Frame[this, _module.WriterStream.footprint];
    assume true;
    $rhs#1 := Set#UnionOne(Set#Empty(): Set Box, $Box(this));
    $Heap := update($Heap, this, _module.WriterStream.footprint, $rhs#1);
    assume $IsGoodHeap($Heap);
    assume {:captureState "b8.dfy(205,23)"} true;
    // ----- assignment statement ----- b8.dfy(206,11)
    assume true;
    assert $_Frame[this, _module.WriterStream.isOpen];
    assume true;
    $rhs#2 := Lit(true);
    $Heap := update($Heap, this, _module.WriterStream.isOpen, $rhs#2);
    assume $IsGoodHeap($Heap);
    assume {:captureState "b8.dfy(206,17)"} true;
}



procedure CheckWellformed$$_module.WriterStream.GetCount(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.WriterStream())
         && $IsAlloc(this, Tclass._module.WriterStream(), $Heap))
   returns (c#0: int);
  free requires 23 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.WriterStream.GetCount(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.WriterStream())
         && $IsAlloc(this, Tclass._module.WriterStream(), $Heap))
   returns (c#0: int);
  // user-defined preconditions
  requires _module.WriterStream.Valid#canCall($Heap, this)
     ==> _module.WriterStream.Valid($Heap, this)
       || !read($Heap, this, _module.WriterStream.footprint)[$Box(null)];
  requires _module.WriterStream.Valid#canCall($Heap, this)
     ==> _module.WriterStream.Valid($Heap, this)
       || read($Heap, this, _module.WriterStream.footprint)[$Box(this)];
  requires _module.WriterStream.Valid#canCall($Heap, this)
     ==> _module.WriterStream.Valid($Heap, this)
       || read($Heap, this, _module.WriterStream.isOpen);
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



procedure Impl$$_module.WriterStream.GetCount(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.WriterStream())
         && $IsAlloc(this, Tclass._module.WriterStream(), $Heap))
   returns (c#0: int, $_reverifyPost: bool);
  free requires 23 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.WriterStream.Valid#canCall($Heap, this)
     &&
    _module.WriterStream.Valid($Heap, this)
     &&
    !read($Heap, this, _module.WriterStream.footprint)[$Box(null)]
     && read($Heap, this, _module.WriterStream.footprint)[$Box(this)]
     && read($Heap, this, _module.WriterStream.isOpen);
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



implementation Impl$$_module.WriterStream.GetCount(this: ref) returns (c#0: int, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: GetCount, Impl$$_module.WriterStream.GetCount
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "b8.dfy(211,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- b8.dfy(212,6)
    assume true;
    assume true;
    c#0 := Seq#Length(read($Heap, this, _module.WriterStream.stream));
    assume {:captureState "b8.dfy(212,15)"} true;
}



procedure CheckWellformed$$_module.WriterStream.PutWord(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.WriterStream())
         && $IsAlloc(this, Tclass._module.WriterStream(), $Heap),
    w#0: ref
       where $Is(w#0, Tclass._module.Word()) && $IsAlloc(w#0, Tclass._module.Word(), $Heap));
  free requires 20 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.WriterStream.PutWord(this: ref, w#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: PutWord, CheckWellformed$$_module.WriterStream.PutWord
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc)
         ==> read($Heap, this, _module.WriterStream.footprint)[$Box($o)]);
    assume {:captureState "b8.dfy(215,9): initial state"} true;
    assume _module.WriterStream.Valid#canCall($Heap, this);
    assume _module.WriterStream.Valid($Heap, this);
    assume w#0 != null;
    havoc $Heap;
    assume (forall<alpha> $o: ref, $f: Field alpha ::
      { read($Heap, $o, $f) }
      $o != null && read(old($Heap), $o, alloc)
         ==> read($Heap, $o, $f) == read(old($Heap), $o, $f)
           || read(old($Heap), this, _module.WriterStream.footprint)[$Box($o)]);
    assume $HeapSucc(old($Heap), $Heap);
    assume {:captureState "b8.dfy(219,20): post-state"} true;
    assume _module.WriterStream.Valid#canCall($Heap, this);
    assume _module.WriterStream.Valid($Heap, this);
    assert $IsAlloc(this, Tclass._module.WriterStream(), old($Heap));
    assume (forall $o: ref ::
      { read(old($Heap), $o, alloc) }
      read($Heap, this, _module.WriterStream.footprint)[$Box($o)]
           && !read(old($Heap), this, _module.WriterStream.footprint)[$Box($o)]
         ==> $o != null && !read(old($Heap), $o, alloc));
    assert $IsAlloc(this, Tclass._module.WriterStream(), old($Heap));
    assume Seq#Length(read(old($Heap), this, _module.WriterStream.stream))
         <= Seq#Length(read($Heap, this, _module.WriterStream.stream))
       && Seq#SameUntil(read(old($Heap), this, _module.WriterStream.stream),
        read($Heap, this, _module.WriterStream.stream),
        Seq#Length(read(old($Heap), this, _module.WriterStream.stream)));
}



procedure Call$$_module.WriterStream.PutWord(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.WriterStream())
         && $IsAlloc(this, Tclass._module.WriterStream(), $Heap),
    w#0: ref
       where $Is(w#0, Tclass._module.Word()) && $IsAlloc(w#0, Tclass._module.Word(), $Heap));
  // user-defined preconditions
  requires _module.WriterStream.Valid#canCall($Heap, this)
     ==> _module.WriterStream.Valid($Heap, this)
       || !read($Heap, this, _module.WriterStream.footprint)[$Box(null)];
  requires _module.WriterStream.Valid#canCall($Heap, this)
     ==> _module.WriterStream.Valid($Heap, this)
       || read($Heap, this, _module.WriterStream.footprint)[$Box(this)];
  requires _module.WriterStream.Valid#canCall($Heap, this)
     ==> _module.WriterStream.Valid($Heap, this)
       || read($Heap, this, _module.WriterStream.isOpen);
  requires w#0 != null;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.WriterStream.Valid#canCall($Heap, this);
  free ensures _module.WriterStream.Valid#canCall($Heap, this)
     &&
    _module.WriterStream.Valid($Heap, this)
     &&
    !read($Heap, this, _module.WriterStream.footprint)[$Box(null)]
     && read($Heap, this, _module.WriterStream.footprint)[$Box(this)]
     && read($Heap, this, _module.WriterStream.isOpen);
  ensures (forall $o: ref ::
    { read(old($Heap), $o, alloc) }
    read($Heap, this, _module.WriterStream.footprint)[$Box($o)]
         && !read(old($Heap), this, _module.WriterStream.footprint)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures true;
  ensures Seq#Length(read(old($Heap), this, _module.WriterStream.stream))
       <= Seq#Length(read($Heap, this, _module.WriterStream.stream))
     && Seq#SameUntil(read(old($Heap), this, _module.WriterStream.stream),
      read($Heap, this, _module.WriterStream.stream),
      Seq#Length(read(old($Heap), this, _module.WriterStream.stream)));
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f)
         || read(old($Heap), this, _module.WriterStream.footprint)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.WriterStream.PutWord(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.WriterStream())
         && $IsAlloc(this, Tclass._module.WriterStream(), $Heap),
    w#0: ref
       where $Is(w#0, Tclass._module.Word()) && $IsAlloc(w#0, Tclass._module.Word(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 20 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.WriterStream.Valid#canCall($Heap, this)
     &&
    _module.WriterStream.Valid($Heap, this)
     &&
    !read($Heap, this, _module.WriterStream.footprint)[$Box(null)]
     && read($Heap, this, _module.WriterStream.footprint)[$Box(this)]
     && read($Heap, this, _module.WriterStream.isOpen);
  requires w#0 != null;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.WriterStream.Valid#canCall($Heap, this);
  ensures _module.WriterStream.Valid#canCall($Heap, this)
     ==> _module.WriterStream.Valid($Heap, this)
       || !read($Heap, this, _module.WriterStream.footprint)[$Box(null)];
  ensures _module.WriterStream.Valid#canCall($Heap, this)
     ==> _module.WriterStream.Valid($Heap, this)
       || read($Heap, this, _module.WriterStream.footprint)[$Box(this)];
  ensures _module.WriterStream.Valid#canCall($Heap, this)
     ==> _module.WriterStream.Valid($Heap, this)
       || read($Heap, this, _module.WriterStream.isOpen);
  ensures (forall $o: ref ::
    { read(old($Heap), $o, alloc) }
    read($Heap, this, _module.WriterStream.footprint)[$Box($o)]
         && !read(old($Heap), this, _module.WriterStream.footprint)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures true;
  ensures Seq#Length(read(old($Heap), this, _module.WriterStream.stream))
       <= Seq#Length(read($Heap, this, _module.WriterStream.stream))
     && Seq#SameUntil(read(old($Heap), this, _module.WriterStream.stream),
      read($Heap, this, _module.WriterStream.stream),
      Seq#Length(read(old($Heap), this, _module.WriterStream.stream)));
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f)
         || read(old($Heap), this, _module.WriterStream.footprint)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.WriterStream.PutWord(this: ref, w#0: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: PutWord, Impl$$_module.WriterStream.PutWord
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc)
         ==> read($Heap, this, _module.WriterStream.footprint)[$Box($o)]);
    assume {:captureState "b8.dfy(221,2): initial state"} true;
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.WriterStream.PutWordInsideTag(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.WriterStream())
         && $IsAlloc(this, Tclass._module.WriterStream(), $Heap),
    tag#0: ref
       where $Is(tag#0, Tclass._module.Word())
         && $IsAlloc(tag#0, Tclass._module.Word(), $Heap),
    w#0: ref
       where $Is(w#0, Tclass._module.Word()) && $IsAlloc(w#0, Tclass._module.Word(), $Heap));
  free requires 18 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.WriterStream.PutWordInsideTag(this: ref, tag#0: ref, w#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: PutWordInsideTag, CheckWellformed$$_module.WriterStream.PutWordInsideTag
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc)
         ==> read($Heap, this, _module.WriterStream.footprint)[$Box($o)]);
    assume {:captureState "b8.dfy(224,9): initial state"} true;
    assume _module.WriterStream.Valid#canCall($Heap, this);
    assume _module.WriterStream.Valid($Heap, this);
    assume tag#0 != null;
    assume w#0 != null;
    havoc $Heap;
    assume (forall<alpha> $o: ref, $f: Field alpha ::
      { read($Heap, $o, $f) }
      $o != null && read(old($Heap), $o, alloc)
         ==> read($Heap, $o, $f) == read(old($Heap), $o, $f)
           || read(old($Heap), this, _module.WriterStream.footprint)[$Box($o)]);
    assume $HeapSucc(old($Heap), $Heap);
    assume {:captureState "b8.dfy(228,20): post-state"} true;
    assume _module.WriterStream.Valid#canCall($Heap, this);
    assume _module.WriterStream.Valid($Heap, this);
    assert $IsAlloc(this, Tclass._module.WriterStream(), old($Heap));
    assume (forall $o: ref ::
      { read(old($Heap), $o, alloc) }
      read($Heap, this, _module.WriterStream.footprint)[$Box($o)]
           && !read(old($Heap), this, _module.WriterStream.footprint)[$Box($o)]
         ==> $o != null && !read(old($Heap), $o, alloc));
    assert $IsAlloc(this, Tclass._module.WriterStream(), old($Heap));
    assume Seq#Length(read(old($Heap), this, _module.WriterStream.stream))
         <= Seq#Length(read($Heap, this, _module.WriterStream.stream))
       && Seq#SameUntil(read(old($Heap), this, _module.WriterStream.stream),
        read($Heap, this, _module.WriterStream.stream),
        Seq#Length(read(old($Heap), this, _module.WriterStream.stream)));
}



procedure Call$$_module.WriterStream.PutWordInsideTag(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.WriterStream())
         && $IsAlloc(this, Tclass._module.WriterStream(), $Heap),
    tag#0: ref
       where $Is(tag#0, Tclass._module.Word())
         && $IsAlloc(tag#0, Tclass._module.Word(), $Heap),
    w#0: ref
       where $Is(w#0, Tclass._module.Word()) && $IsAlloc(w#0, Tclass._module.Word(), $Heap));
  // user-defined preconditions
  requires _module.WriterStream.Valid#canCall($Heap, this)
     ==> _module.WriterStream.Valid($Heap, this)
       || !read($Heap, this, _module.WriterStream.footprint)[$Box(null)];
  requires _module.WriterStream.Valid#canCall($Heap, this)
     ==> _module.WriterStream.Valid($Heap, this)
       || read($Heap, this, _module.WriterStream.footprint)[$Box(this)];
  requires _module.WriterStream.Valid#canCall($Heap, this)
     ==> _module.WriterStream.Valid($Heap, this)
       || read($Heap, this, _module.WriterStream.isOpen);
  requires tag#0 != null;
  requires w#0 != null;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.WriterStream.Valid#canCall($Heap, this);
  free ensures _module.WriterStream.Valid#canCall($Heap, this)
     &&
    _module.WriterStream.Valid($Heap, this)
     &&
    !read($Heap, this, _module.WriterStream.footprint)[$Box(null)]
     && read($Heap, this, _module.WriterStream.footprint)[$Box(this)]
     && read($Heap, this, _module.WriterStream.isOpen);
  ensures (forall $o: ref ::
    { read(old($Heap), $o, alloc) }
    read($Heap, this, _module.WriterStream.footprint)[$Box($o)]
         && !read(old($Heap), this, _module.WriterStream.footprint)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures true;
  ensures Seq#Length(read(old($Heap), this, _module.WriterStream.stream))
       <= Seq#Length(read($Heap, this, _module.WriterStream.stream))
     && Seq#SameUntil(read(old($Heap), this, _module.WriterStream.stream),
      read($Heap, this, _module.WriterStream.stream),
      Seq#Length(read(old($Heap), this, _module.WriterStream.stream)));
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f)
         || read(old($Heap), this, _module.WriterStream.footprint)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.WriterStream.PutWordInsideTag(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.WriterStream())
         && $IsAlloc(this, Tclass._module.WriterStream(), $Heap),
    tag#0: ref
       where $Is(tag#0, Tclass._module.Word())
         && $IsAlloc(tag#0, Tclass._module.Word(), $Heap),
    w#0: ref
       where $Is(w#0, Tclass._module.Word()) && $IsAlloc(w#0, Tclass._module.Word(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 18 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.WriterStream.Valid#canCall($Heap, this)
     &&
    _module.WriterStream.Valid($Heap, this)
     &&
    !read($Heap, this, _module.WriterStream.footprint)[$Box(null)]
     && read($Heap, this, _module.WriterStream.footprint)[$Box(this)]
     && read($Heap, this, _module.WriterStream.isOpen);
  requires tag#0 != null;
  requires w#0 != null;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.WriterStream.Valid#canCall($Heap, this);
  ensures _module.WriterStream.Valid#canCall($Heap, this)
     ==> _module.WriterStream.Valid($Heap, this)
       || !read($Heap, this, _module.WriterStream.footprint)[$Box(null)];
  ensures _module.WriterStream.Valid#canCall($Heap, this)
     ==> _module.WriterStream.Valid($Heap, this)
       || read($Heap, this, _module.WriterStream.footprint)[$Box(this)];
  ensures _module.WriterStream.Valid#canCall($Heap, this)
     ==> _module.WriterStream.Valid($Heap, this)
       || read($Heap, this, _module.WriterStream.isOpen);
  ensures (forall $o: ref ::
    { read(old($Heap), $o, alloc) }
    read($Heap, this, _module.WriterStream.footprint)[$Box($o)]
         && !read(old($Heap), this, _module.WriterStream.footprint)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures true;
  ensures Seq#Length(read(old($Heap), this, _module.WriterStream.stream))
       <= Seq#Length(read($Heap, this, _module.WriterStream.stream))
     && Seq#SameUntil(read(old($Heap), this, _module.WriterStream.stream),
      read($Heap, this, _module.WriterStream.stream),
      Seq#Length(read(old($Heap), this, _module.WriterStream.stream)));
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f)
         || read(old($Heap), this, _module.WriterStream.footprint)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.WriterStream.PutWordInsideTag(this: ref, tag#0: ref, w#0: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: PutWordInsideTag, Impl$$_module.WriterStream.PutWordInsideTag
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc)
         ==> read($Heap, this, _module.WriterStream.footprint)[$Box($o)]);
    assume {:captureState "b8.dfy(230,2): initial state"} true;
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.WriterStream.PutWordInsideHyperlink(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.WriterStream())
         && $IsAlloc(this, Tclass._module.WriterStream(), $Heap),
    tag#0: ref
       where $Is(tag#0, Tclass._module.Word())
         && $IsAlloc(tag#0, Tclass._module.Word(), $Heap),
    w#0: ref
       where $Is(w#0, Tclass._module.Word()) && $IsAlloc(w#0, Tclass._module.Word(), $Heap));
  free requires 19 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.WriterStream.PutWordInsideHyperlink(this: ref, tag#0: ref, w#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: PutWordInsideHyperlink, CheckWellformed$$_module.WriterStream.PutWordInsideHyperlink
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc)
         ==> read($Heap, this, _module.WriterStream.footprint)[$Box($o)]);
    assume {:captureState "b8.dfy(233,9): initial state"} true;
    assume _module.WriterStream.Valid#canCall($Heap, this);
    assume _module.WriterStream.Valid($Heap, this);
    assume tag#0 != null;
    assume w#0 != null;
    havoc $Heap;
    assume (forall<alpha> $o: ref, $f: Field alpha ::
      { read($Heap, $o, $f) }
      $o != null && read(old($Heap), $o, alloc)
         ==> read($Heap, $o, $f) == read(old($Heap), $o, $f)
           || read(old($Heap), this, _module.WriterStream.footprint)[$Box($o)]);
    assume $HeapSucc(old($Heap), $Heap);
    assume {:captureState "b8.dfy(237,20): post-state"} true;
    assume _module.WriterStream.Valid#canCall($Heap, this);
    assume _module.WriterStream.Valid($Heap, this);
    assert $IsAlloc(this, Tclass._module.WriterStream(), old($Heap));
    assume (forall $o: ref ::
      { read(old($Heap), $o, alloc) }
      read($Heap, this, _module.WriterStream.footprint)[$Box($o)]
           && !read(old($Heap), this, _module.WriterStream.footprint)[$Box($o)]
         ==> $o != null && !read(old($Heap), $o, alloc));
    assert $IsAlloc(this, Tclass._module.WriterStream(), old($Heap));
    assume Seq#Length(read(old($Heap), this, _module.WriterStream.stream))
         <= Seq#Length(read($Heap, this, _module.WriterStream.stream))
       && Seq#SameUntil(read(old($Heap), this, _module.WriterStream.stream),
        read($Heap, this, _module.WriterStream.stream),
        Seq#Length(read(old($Heap), this, _module.WriterStream.stream)));
}



procedure Call$$_module.WriterStream.PutWordInsideHyperlink(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.WriterStream())
         && $IsAlloc(this, Tclass._module.WriterStream(), $Heap),
    tag#0: ref
       where $Is(tag#0, Tclass._module.Word())
         && $IsAlloc(tag#0, Tclass._module.Word(), $Heap),
    w#0: ref
       where $Is(w#0, Tclass._module.Word()) && $IsAlloc(w#0, Tclass._module.Word(), $Heap));
  // user-defined preconditions
  requires _module.WriterStream.Valid#canCall($Heap, this)
     ==> _module.WriterStream.Valid($Heap, this)
       || !read($Heap, this, _module.WriterStream.footprint)[$Box(null)];
  requires _module.WriterStream.Valid#canCall($Heap, this)
     ==> _module.WriterStream.Valid($Heap, this)
       || read($Heap, this, _module.WriterStream.footprint)[$Box(this)];
  requires _module.WriterStream.Valid#canCall($Heap, this)
     ==> _module.WriterStream.Valid($Heap, this)
       || read($Heap, this, _module.WriterStream.isOpen);
  requires tag#0 != null;
  requires w#0 != null;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.WriterStream.Valid#canCall($Heap, this);
  free ensures _module.WriterStream.Valid#canCall($Heap, this)
     &&
    _module.WriterStream.Valid($Heap, this)
     &&
    !read($Heap, this, _module.WriterStream.footprint)[$Box(null)]
     && read($Heap, this, _module.WriterStream.footprint)[$Box(this)]
     && read($Heap, this, _module.WriterStream.isOpen);
  ensures (forall $o: ref ::
    { read(old($Heap), $o, alloc) }
    read($Heap, this, _module.WriterStream.footprint)[$Box($o)]
         && !read(old($Heap), this, _module.WriterStream.footprint)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures true;
  ensures Seq#Length(read(old($Heap), this, _module.WriterStream.stream))
       <= Seq#Length(read($Heap, this, _module.WriterStream.stream))
     && Seq#SameUntil(read(old($Heap), this, _module.WriterStream.stream),
      read($Heap, this, _module.WriterStream.stream),
      Seq#Length(read(old($Heap), this, _module.WriterStream.stream)));
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f)
         || read(old($Heap), this, _module.WriterStream.footprint)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.WriterStream.PutWordInsideHyperlink(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.WriterStream())
         && $IsAlloc(this, Tclass._module.WriterStream(), $Heap),
    tag#0: ref
       where $Is(tag#0, Tclass._module.Word())
         && $IsAlloc(tag#0, Tclass._module.Word(), $Heap),
    w#0: ref
       where $Is(w#0, Tclass._module.Word()) && $IsAlloc(w#0, Tclass._module.Word(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 19 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.WriterStream.Valid#canCall($Heap, this)
     &&
    _module.WriterStream.Valid($Heap, this)
     &&
    !read($Heap, this, _module.WriterStream.footprint)[$Box(null)]
     && read($Heap, this, _module.WriterStream.footprint)[$Box(this)]
     && read($Heap, this, _module.WriterStream.isOpen);
  requires tag#0 != null;
  requires w#0 != null;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.WriterStream.Valid#canCall($Heap, this);
  ensures _module.WriterStream.Valid#canCall($Heap, this)
     ==> _module.WriterStream.Valid($Heap, this)
       || !read($Heap, this, _module.WriterStream.footprint)[$Box(null)];
  ensures _module.WriterStream.Valid#canCall($Heap, this)
     ==> _module.WriterStream.Valid($Heap, this)
       || read($Heap, this, _module.WriterStream.footprint)[$Box(this)];
  ensures _module.WriterStream.Valid#canCall($Heap, this)
     ==> _module.WriterStream.Valid($Heap, this)
       || read($Heap, this, _module.WriterStream.isOpen);
  ensures (forall $o: ref ::
    { read(old($Heap), $o, alloc) }
    read($Heap, this, _module.WriterStream.footprint)[$Box($o)]
         && !read(old($Heap), this, _module.WriterStream.footprint)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures true;
  ensures Seq#Length(read(old($Heap), this, _module.WriterStream.stream))
       <= Seq#Length(read($Heap, this, _module.WriterStream.stream))
     && Seq#SameUntil(read(old($Heap), this, _module.WriterStream.stream),
      read($Heap, this, _module.WriterStream.stream),
      Seq#Length(read(old($Heap), this, _module.WriterStream.stream)));
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f)
         || read(old($Heap), this, _module.WriterStream.footprint)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.WriterStream.PutWordInsideHyperlink(this: ref, tag#0: ref, w#0: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: PutWordInsideHyperlink, Impl$$_module.WriterStream.PutWordInsideHyperlink
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc)
         ==> read($Heap, this, _module.WriterStream.footprint)[$Box($o)]);
    assume {:captureState "b8.dfy(239,2): initial state"} true;
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.WriterStream.Close(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.WriterStream())
         && $IsAlloc(this, Tclass._module.WriterStream(), $Heap));
  free requires 21 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.WriterStream.Close(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.WriterStream())
         && $IsAlloc(this, Tclass._module.WriterStream(), $Heap));
  // user-defined preconditions
  requires _module.WriterStream.Valid#canCall($Heap, this)
     ==> _module.WriterStream.Valid($Heap, this)
       || !read($Heap, this, _module.WriterStream.footprint)[$Box(null)];
  requires _module.WriterStream.Valid#canCall($Heap, this)
     ==> _module.WriterStream.Valid($Heap, this)
       || read($Heap, this, _module.WriterStream.footprint)[$Box(this)];
  requires _module.WriterStream.Valid#canCall($Heap, this)
     ==> _module.WriterStream.Valid($Heap, this)
       || read($Heap, this, _module.WriterStream.isOpen);
  modifies $Heap, $Tick;
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f)
         || read(old($Heap), this, _module.WriterStream.footprint)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.WriterStream.Close(this: ref
       where this != null
         &&
        $Is(this, Tclass._module.WriterStream())
         && $IsAlloc(this, Tclass._module.WriterStream(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 21 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.WriterStream.Valid#canCall($Heap, this)
     &&
    _module.WriterStream.Valid($Heap, this)
     &&
    !read($Heap, this, _module.WriterStream.footprint)[$Box(null)]
     && read($Heap, this, _module.WriterStream.footprint)[$Box(this)]
     && read($Heap, this, _module.WriterStream.isOpen);
  modifies $Heap, $Tick;
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f)
         || read(old($Heap), this, _module.WriterStream.footprint)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.WriterStream.Close(this: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs#0: bool;

    // AddMethodImpl: Close, Impl$$_module.WriterStream.Close
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc)
         ==> read($Heap, this, _module.WriterStream.footprint)[$Box($o)]);
    assume {:captureState "b8.dfy(245,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- b8.dfy(246,12)
    assume true;
    assert $_Frame[this, _module.WriterStream.isOpen];
    assume true;
    $rhs#0 := Lit(false);
    $Heap := update($Heap, this, _module.WriterStream.isOpen, $rhs#0);
    assume $IsGoodHeap($Heap);
    assume {:captureState "b8.dfy(246,19)"} true;
}



const unique class._module.Map: ClassName;

// Map: Class $Is
axiom (forall _module.Map$Key: Ty, _module.Map$Value: Ty, $o: ref ::
  { $Is($o, Tclass._module.Map(_module.Map$Key, _module.Map$Value)) }
  $Is($o, Tclass._module.Map(_module.Map$Key, _module.Map$Value))
     <==> $o == null
       || dtype($o) == Tclass._module.Map(_module.Map$Key, _module.Map$Value));

// Map: Class $IsAlloc
axiom (forall _module.Map$Key: Ty, _module.Map$Value: Ty, $o: ref, $h: Heap ::
  { $IsAlloc($o, Tclass._module.Map(_module.Map$Key, _module.Map$Value), $h) }
  $IsAlloc($o, Tclass._module.Map(_module.Map$Key, _module.Map$Value), $h)
     <==> $o == null || read($h, $o, alloc));

const _module.Map.keys: Field (Seq Box);

// Map.keys: Allocation axiom
axiom (forall _module.Map$Key: Ty, _module.Map$Value: Ty, $h: Heap, $o: ref ::
  { read($h, $o, _module.Map.keys), Tclass._module.Map(_module.Map$Key, _module.Map$Value) }
  $IsGoodHeap($h)
       && $o != null
       && dtype($o) == Tclass._module.Map(_module.Map$Key, _module.Map$Value)
     ==> $Is(read($h, $o, _module.Map.keys), TSeq(_module.Map$Key))
       && (read($h, $o, alloc)
         ==> $IsAlloc(read($h, $o, _module.Map.keys), TSeq(_module.Map$Key), $h)));

const _module.Map.values: Field (Seq Box);

// Map.values: Allocation axiom
axiom (forall _module.Map$Key: Ty, _module.Map$Value: Ty, $h: Heap, $o: ref ::
  { read($h, $o, _module.Map.values), Tclass._module.Map(_module.Map$Key, _module.Map$Value) }
  $IsGoodHeap($h)
       && $o != null
       && dtype($o) == Tclass._module.Map(_module.Map$Key, _module.Map$Value)
     ==> $Is(read($h, $o, _module.Map.values), TSeq(_module.Map$Value))
       && (read($h, $o, alloc)
         ==> $IsAlloc(read($h, $o, _module.Map.values), TSeq(_module.Map$Value), $h)));

// function declaration for _module.Map.Valid
function _module.Map.Valid(_module.Map$Key: Ty, _module.Map$Value: Ty, $heap: Heap, this: ref) : bool;

function _module.Map.Valid#canCall(_module.Map$Key: Ty, _module.Map$Value: Ty, $heap: Heap, this: ref) : bool;

// frame axiom for _module.Map.Valid
axiom (forall _module.Map$Key: Ty, _module.Map$Value: Ty, $h0: Heap, $h1: Heap, this: ref ::
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.Map.Valid(_module.Map$Key, _module.Map$Value, $h1, this) }
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       &&
      this != null
       && $Is(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value))
       &&
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==>
    (forall<alpha> $o: ref, $f: Field alpha ::
      $o != null && $o == this ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.Map.Valid(_module.Map$Key, _module.Map$Value, $h0, this)
       == _module.Map.Valid(_module.Map$Key, _module.Map$Value, $h1, this));

// consequence axiom for _module.Map.Valid
axiom 5 <= $FunctionContextHeight
   ==> (forall _module.Map$Key: Ty, _module.Map$Value: Ty, $Heap: Heap, this: ref ::
    { _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this) }
    _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
         || (5 != $FunctionContextHeight
           &&
          $IsGoodHeap($Heap)
           &&
          this != null
           &&
          $Is(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value))
           && $IsAlloc(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value), $Heap))
       ==> true);

function _module.Map.Valid#requires(Ty, Ty, Heap, ref) : bool;

// #requires axiom for _module.Map.Valid
axiom (forall _module.Map$Key: Ty, _module.Map$Value: Ty, $Heap: Heap, this: ref ::
  { _module.Map.Valid#requires(_module.Map$Key, _module.Map$Value, $Heap, this) }
  $IsGoodHeap($Heap)
       &&
      this != null
       &&
      $Is(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value))
       && $IsAlloc(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value), $Heap)
     ==> _module.Map.Valid#requires(_module.Map$Key, _module.Map$Value, $Heap, this)
       == true);

// definition axiom for _module.Map.Valid(revealed)
axiom 5 <= $FunctionContextHeight
   ==> (forall _module.Map$Key: Ty, _module.Map$Value: Ty, $Heap: Heap, this: ref ::
    { _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this) }
    _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
         || (5 != $FunctionContextHeight
           &&
          $IsGoodHeap($Heap)
           &&
          this != null
           &&
          $Is(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value))
           && $IsAlloc(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value), $Heap))
       ==> (Seq#Length(read($Heap, this, _module.Map.keys))
             == Seq#Length(read($Heap, this, _module.Map.values))
           ==> (forall i#0: int, j#0: int ::
            { Seq#Index(read($Heap, this, _module.Map.keys), j#0), Seq#Index(read($Heap, this, _module.Map.keys), i#0) }
            true))
         && _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
           == (Seq#Length(read($Heap, this, _module.Map.keys))
               == Seq#Length(read($Heap, this, _module.Map.values))
             && (forall i#0: int, j#0: int ::
              { Seq#Index(read($Heap, this, _module.Map.keys), j#0), Seq#Index(read($Heap, this, _module.Map.keys), i#0) }
              true
                 ==>
                LitInt(0) <= i#0
                   && i#0 < j#0
                   && j#0 < Seq#Length(read($Heap, this, _module.Map.keys))
                 ==> Seq#Index(read($Heap, this, _module.Map.keys), i#0)
                   != Seq#Index(read($Heap, this, _module.Map.keys), j#0))));

procedure CheckWellformed$$_module.Map.Valid(_module.Map$Key: Ty,
    _module.Map$Value: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value))
         && $IsAlloc(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value), $Heap));
  free requires 5 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.Map.Valid(_module.Map$Key: Ty, _module.Map$Value: Ty, this: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var i#1: int;
  var j#1: int;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;
  var b$reqreads#2: bool;
  var b$reqreads#3: bool;
  var b$reqreads#4: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;
    b$reqreads#2 := true;
    b$reqreads#3 := true;
    b$reqreads#4 := true;

    // AddWellformednessCheck for function Valid
    assume {:captureState "b8.dfy(257,12): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> $o == this);
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
          $o != null && read($Heap, $o, alloc) ==> $o == this);
        b$reqreads#0 := $_Frame[this, _module.Map.keys];
        b$reqreads#1 := $_Frame[this, _module.Map.values];
        if (Seq#Length(read($Heap, this, _module.Map.keys))
           == Seq#Length(read($Heap, this, _module.Map.values)))
        {
            havoc i#1;
            havoc j#1;
            // Begin Comprehension WF check
            if (LitInt(0) <= i#1)
            {
            }

            if (LitInt(0) <= i#1 && i#1 < j#1)
            {
                b$reqreads#2 := $_Frame[this, _module.Map.keys];
            }

            if (LitInt(0) <= i#1
               && i#1 < j#1
               && j#1 < Seq#Length(read($Heap, this, _module.Map.keys)))
            {
                b$reqreads#3 := $_Frame[this, _module.Map.keys];
                assert 0 <= i#1 && i#1 < Seq#Length(read($Heap, this, _module.Map.keys));
                b$reqreads#4 := $_Frame[this, _module.Map.keys];
                assert 0 <= j#1 && j#1 < Seq#Length(read($Heap, this, _module.Map.keys));
            }

            // End Comprehension WF check
        }

        assume _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
           == (Seq#Length(read($Heap, this, _module.Map.keys))
               == Seq#Length(read($Heap, this, _module.Map.values))
             && (forall i#2: int, j#2: int ::
              { Seq#Index(read($Heap, this, _module.Map.keys), j#2), Seq#Index(read($Heap, this, _module.Map.keys), i#2) }
              true
                 ==>
                LitInt(0) <= i#2
                   && i#2 < j#2
                   && j#2 < Seq#Length(read($Heap, this, _module.Map.keys))
                 ==> Seq#Index(read($Heap, this, _module.Map.keys), i#2)
                   != Seq#Index(read($Heap, this, _module.Map.keys), j#2)));
        assume Seq#Length(read($Heap, this, _module.Map.keys))
             == Seq#Length(read($Heap, this, _module.Map.values))
           ==> (forall i#2: int, j#2: int ::
            { Seq#Index(read($Heap, this, _module.Map.keys), j#2), Seq#Index(read($Heap, this, _module.Map.keys), i#2) }
            true);
        // CheckWellformedWithResult: any expression
        assume $Is(_module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this), TBool);
        assert b$reqreads#0;
        assert b$reqreads#1;
        assert b$reqreads#2;
        assert b$reqreads#3;
        assert b$reqreads#4;
    }
}



procedure CheckWellformed$$_module.Map.Init(_module.Map$Key: Ty,
    _module.Map$Value: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value))
         && $IsAlloc(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value), $Heap));
  free requires 6 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.Map.Init(_module.Map$Key: Ty,
    _module.Map$Value: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value))
         && $IsAlloc(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value), $Heap));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this);
  free ensures _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     &&
    _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
     &&
    Seq#Length(read($Heap, this, _module.Map.keys))
       == Seq#Length(read($Heap, this, _module.Map.values))
     && (forall i#0: int, j#0: int ::
      { Seq#Index(read($Heap, this, _module.Map.keys), j#0), Seq#Index(read($Heap, this, _module.Map.keys), i#0) }
      true
         ==>
        LitInt(0) <= i#0
           && i#0 < j#0
           && j#0 < Seq#Length(read($Heap, this, _module.Map.keys))
         ==> Seq#Index(read($Heap, this, _module.Map.keys), i#0)
           != Seq#Index(read($Heap, this, _module.Map.keys), j#0));
  ensures Seq#Length(read($Heap, this, _module.Map.keys)) == LitInt(0);
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f) || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Map.Init(_module.Map$Key: Ty,
    _module.Map$Value: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value))
         && $IsAlloc(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value), $Heap))
   returns ($_reverifyPost: bool);
  free requires 6 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this);
  ensures _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     ==> _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
       || Seq#Length(read($Heap, this, _module.Map.keys))
         == Seq#Length(read($Heap, this, _module.Map.values));
  ensures _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     ==> _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
       || (forall i#1: int, j#1: int ::
        { Seq#Index(read($Heap, this, _module.Map.keys), j#1), Seq#Index(read($Heap, this, _module.Map.keys), i#1) }
        true
           ==>
          LitInt(0) <= i#1
             && i#1 < j#1
             && j#1 < Seq#Length(read($Heap, this, _module.Map.keys))
           ==> Seq#Index(read($Heap, this, _module.Map.keys), i#1)
             != Seq#Index(read($Heap, this, _module.Map.keys), j#1));
  ensures Seq#Length(read($Heap, this, _module.Map.keys)) == LitInt(0);
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f) || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Map.Init(_module.Map$Key: Ty, _module.Map$Value: Ty, this: ref)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs#0: Seq Box where $Is($rhs#0, TSeq(_module.Map$Key));
  var $rhs#1: Seq Box where $Is($rhs#1, TSeq(_module.Map$Value));

    // AddMethodImpl: Init, Impl$$_module.Map.Init
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> $o == this);
    assume {:captureState "b8.dfy(267,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- b8.dfy(268,10)
    assume true;
    assert $_Frame[this, _module.Map.keys];
    assume true;
    $rhs#0 := Lit(Seq#Empty(): Seq Box);
    $Heap := update($Heap, this, _module.Map.keys, $rhs#0);
    assume $IsGoodHeap($Heap);
    assume {:captureState "b8.dfy(268,14)"} true;
    // ----- assignment statement ----- b8.dfy(269,12)
    assume true;
    assert $_Frame[this, _module.Map.values];
    assume true;
    $rhs#1 := Lit(Seq#Empty(): Seq Box);
    $Heap := update($Heap, this, _module.Map.values, $rhs#1);
    assume $IsGoodHeap($Heap);
    assume {:captureState "b8.dfy(269,16)"} true;
}



procedure CheckWellformed$$_module.Map.Find(_module.Map$Key: Ty,
    _module.Map$Value: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value))
         && $IsAlloc(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value), $Heap),
    key#0: Box
       where $IsBox(key#0, _module.Map$Key) && $IsAllocBox(key#0, _module.Map$Key, $Heap))
   returns (result#0: DatatypeType
       where $Is(result#0, Tclass._module.Maybe(_module.Map$Value))
         && $IsAlloc(result#0, Tclass._module.Maybe(_module.Map$Value), $Heap));
  free requires 11 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.Map.Find(_module.Map$Key: Ty, _module.Map$Value: Ty, this: ref, key#0: Box)
   returns (result#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var i#0: int;

    // AddMethodImpl: Find, CheckWellformed$$_module.Map.Find
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "b8.dfy(272,9): initial state"} true;
    assume _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this);
    assume _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this);
    havoc $Heap;
    assume (forall<alpha> $o: ref, $f: Field alpha ::
      { read($Heap, $o, $f) }
      $o != null && read(old($Heap), $o, alloc)
         ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
    assume $HeapSucc(old($Heap), $Heap);
    havoc result#0;
    assume {:captureState "b8.dfy(274,27): post-state"} true;
    if (*)
    {
        assume result#0 == Lit(#_module.Maybe.None());
        assume !Seq#Contains(read($Heap, this, _module.Map.keys), key#0);
    }
    else
    {
        assume result#0 == Lit(#_module.Maybe.None())
           ==> !Seq#Contains(read($Heap, this, _module.Map.keys), key#0);
    }

    if (*)
    {
        assume _module.Maybe.Some_q(result#0);
        havoc i#0;
        assume LitInt(0) <= i#0;
        assume i#0 < Seq#Length(read($Heap, this, _module.Map.keys));
        assert 0 <= i#0 && i#0 < Seq#Length(read($Heap, this, _module.Map.keys));
        assume Seq#Index(read($Heap, this, _module.Map.keys), i#0) == key#0;
        assert 0 <= i#0 && i#0 < Seq#Length(read($Heap, this, _module.Map.values));
        assert _module.Maybe.Some_q(result#0);
        assume Seq#Index(read($Heap, this, _module.Map.values), i#0)
           == _module.Maybe.get(result#0);
    }
    else
    {
        assume _module.Maybe.Some_q(result#0)
           ==> (exists i#1: int ::
            { Seq#Index(read($Heap, this, _module.Map.values), i#1) }
              { Seq#Index(read($Heap, this, _module.Map.keys), i#1) }
            LitInt(0) <= i#1
               && i#1 < Seq#Length(read($Heap, this, _module.Map.keys))
               && Seq#Index(read($Heap, this, _module.Map.keys), i#1) == key#0
               && Seq#Index(read($Heap, this, _module.Map.values), i#1)
                 == _module.Maybe.get(result#0));
    }
}



procedure Call$$_module.Map.Find(_module.Map$Key: Ty,
    _module.Map$Value: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value))
         && $IsAlloc(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value), $Heap),
    key#0: Box
       where $IsBox(key#0, _module.Map$Key) && $IsAllocBox(key#0, _module.Map$Key, $Heap))
   returns (result#0: DatatypeType
       where $Is(result#0, Tclass._module.Maybe(_module.Map$Value))
         && $IsAlloc(result#0, Tclass._module.Maybe(_module.Map$Value), $Heap));
  // user-defined preconditions
  requires _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     ==> _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
       || Seq#Length(read($Heap, this, _module.Map.keys))
         == Seq#Length(read($Heap, this, _module.Map.values));
  requires _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     ==> _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
       || (forall i#2: int, j#0: int ::
        { Seq#Index(read($Heap, this, _module.Map.keys), j#0), Seq#Index(read($Heap, this, _module.Map.keys), i#2) }
        true
           ==>
          LitInt(0) <= i#2
             && i#2 < j#0
             && j#0 < Seq#Length(read($Heap, this, _module.Map.keys))
           ==> Seq#Index(read($Heap, this, _module.Map.keys), i#2)
             != Seq#Index(read($Heap, this, _module.Map.keys), j#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures result#0 == Lit(#_module.Maybe.None())
     ==> !Seq#Contains(read($Heap, this, _module.Map.keys), key#0);
  free ensures _module.Maybe.Some_q(result#0)
     ==> (forall i#1: int ::
      { Seq#Index(read($Heap, this, _module.Map.values), i#1) }
        { Seq#Index(read($Heap, this, _module.Map.keys), i#1) }
      true);
  ensures _module.Maybe.Some_q(result#0)
     ==> (exists i#1: int ::
      { Seq#Index(read($Heap, this, _module.Map.values), i#1) }
        { Seq#Index(read($Heap, this, _module.Map.keys), i#1) }
      LitInt(0) <= i#1
         && i#1 < Seq#Length(read($Heap, this, _module.Map.keys))
         && Seq#Index(read($Heap, this, _module.Map.keys), i#1) == key#0
         && Seq#Index(read($Heap, this, _module.Map.values), i#1)
           == _module.Maybe.get(result#0));
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Map.Find(_module.Map$Key: Ty,
    _module.Map$Value: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value))
         && $IsAlloc(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value), $Heap),
    key#0: Box
       where $IsBox(key#0, _module.Map$Key) && $IsAllocBox(key#0, _module.Map$Key, $Heap))
   returns (result#0: DatatypeType
       where $Is(result#0, Tclass._module.Maybe(_module.Map$Value))
         && $IsAlloc(result#0, Tclass._module.Maybe(_module.Map$Value), $Heap),
    $_reverifyPost: bool);
  free requires 11 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     &&
    _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
     &&
    Seq#Length(read($Heap, this, _module.Map.keys))
       == Seq#Length(read($Heap, this, _module.Map.values))
     && (forall i#3: int, j#1: int ::
      { Seq#Index(read($Heap, this, _module.Map.keys), j#1), Seq#Index(read($Heap, this, _module.Map.keys), i#3) }
      true
         ==>
        LitInt(0) <= i#3
           && i#3 < j#1
           && j#1 < Seq#Length(read($Heap, this, _module.Map.keys))
         ==> Seq#Index(read($Heap, this, _module.Map.keys), i#3)
           != Seq#Index(read($Heap, this, _module.Map.keys), j#1));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures result#0 == Lit(#_module.Maybe.None())
     ==> !Seq#Contains(read($Heap, this, _module.Map.keys), key#0);
  free ensures _module.Maybe.Some_q(result#0)
     ==> (forall i#1: int ::
      { Seq#Index(read($Heap, this, _module.Map.values), i#1) }
        { Seq#Index(read($Heap, this, _module.Map.keys), i#1) }
      true);
  ensures _module.Maybe.Some_q(result#0)
     ==> (exists i#1: int ::
      { Seq#Index(read($Heap, this, _module.Map.values), i#1) }
        { Seq#Index(read($Heap, this, _module.Map.keys), i#1) }
      LitInt(0) <= i#1
         && i#1 < Seq#Length(read($Heap, this, _module.Map.keys))
         && Seq#Index(read($Heap, this, _module.Map.keys), i#1) == key#0
         && Seq#Index(read($Heap, this, _module.Map.values), i#1)
           == _module.Maybe.get(result#0));
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Map.Find(_module.Map$Key: Ty, _module.Map$Value: Ty, this: ref, key#0: Box)
   returns (result#0: DatatypeType, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var j#2: int;
  var $rhs##0: int;
  var key##0: Box;

    // AddMethodImpl: Find, Impl$$_module.Map.Find
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "b8.dfy(276,2): initial state"} true;
    $_reverifyPost := false;
    // ----- call statement ----- b8.dfy(277,23)
    assume true;
    // TrCallStmt: Adding lhs Microsoft.Dafny.AutoGhostIdentifierExpr with type int
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    key##0 := key#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##0 := Call$$_module.Map.FindIndex(_module.Map$Key, _module.Map$Value, this, key##0);
    // TrCallStmt: After ProcessCallStmt
    j#2 := $rhs##0;
    assume {:captureState "b8.dfy(277,27)"} true;
    // ----- if statement ----- b8.dfy(278,5)
    assume true;
    if (j#2 == LitInt(0 - 1))
    {
        // ----- return statement ----- b8.dfy(279,7)
        // ----- assignment statement ----- b8.dfy(279,7)
        assume true;
        assume true;
        result#0 := Lit(#_module.Maybe.None());
        assume {:captureState "b8.dfy(279,17)"} true;
        return;
    }
    else
    {
        // ----- return statement ----- b8.dfy(281,7)
        // ----- assignment statement ----- b8.dfy(281,7)
        assume true;
        assert 0 <= j#2 && j#2 < Seq#Length(read($Heap, this, _module.Map.values));
        assume true;
        result#0 := #_module.Maybe.Some(Seq#Index(read($Heap, this, _module.Map.values), j#2));
        assume {:captureState "b8.dfy(281,28)"} true;
        return;
    }
}



procedure CheckWellformed$$_module.Map.Add(_module.Map$Key: Ty,
    _module.Map$Value: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value))
         && $IsAlloc(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value), $Heap),
    key#0: Box
       where $IsBox(key#0, _module.Map$Key) && $IsAllocBox(key#0, _module.Map$Key, $Heap),
    val#0: Box
       where $IsBox(val#0, _module.Map$Value) && $IsAllocBox(val#0, _module.Map$Value, $Heap));
  free requires 12 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.Map.Add(_module.Map$Key: Ty, _module.Map$Value: Ty, this: ref, key#0: Box, val#0: Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var i#0: int;
  var j#0: int;

    // AddMethodImpl: Add, CheckWellformed$$_module.Map.Add
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> $o == this);
    assume {:captureState "b8.dfy(285,9): initial state"} true;
    assume _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this);
    assume _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this);
    havoc $Heap;
    assume (forall<alpha> $o: ref, $f: Field alpha ::
      { read($Heap, $o, $f) }
      $o != null && read(old($Heap), $o, alloc)
         ==> read($Heap, $o, $f) == read(old($Heap), $o, $f) || $o == this);
    assume $HeapSucc(old($Heap), $Heap);
    assume {:captureState "b8.dfy(288,17): post-state"} true;
    assume _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this);
    assume _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this);
    havoc i#0;
    if (*)
    {
        assume LitInt(0) <= i#0;
        assert $IsAlloc(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value), old($Heap));
        assume i#0 < Seq#Length(read(old($Heap), this, _module.Map.keys));
        assert $IsAlloc(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value), old($Heap));
        assert 0 <= i#0 && i#0 < Seq#Length(read(old($Heap), this, _module.Map.keys));
        assume Seq#Index(read(old($Heap), this, _module.Map.keys), i#0) == key#0;
        assert $IsAlloc(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value), old($Heap));
        assume Seq#Length(read($Heap, this, _module.Map.keys))
           == Seq#Length(read(old($Heap), this, _module.Map.keys));
        assert 0 <= i#0 && i#0 < Seq#Length(read($Heap, this, _module.Map.keys));
        assume Seq#Index(read($Heap, this, _module.Map.keys), i#0) == key#0;
        assert 0 <= i#0 && i#0 < Seq#Length(read($Heap, this, _module.Map.values));
        assume Seq#Index(read($Heap, this, _module.Map.values), i#0) == val#0;
        havoc j#0;
        if (*)
        {
            assume LitInt(0) <= j#0;
            assume j#0 < Seq#Length(read($Heap, this, _module.Map.values));
            assume i#0 != j#0;
            assert 0 <= j#0 && j#0 < Seq#Length(read($Heap, this, _module.Map.keys));
            assert $IsAlloc(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value), old($Heap));
            assert 0 <= j#0 && j#0 < Seq#Length(read(old($Heap), this, _module.Map.keys));
            assume Seq#Index(read($Heap, this, _module.Map.keys), j#0)
               == Seq#Index(read(old($Heap), this, _module.Map.keys), j#0);
        }
        else
        {
            assume LitInt(0) <= j#0
                 && j#0 < Seq#Length(read($Heap, this, _module.Map.values))
                 && i#0 != j#0
               ==> Seq#Index(read($Heap, this, _module.Map.keys), j#0)
                 == Seq#Index(read(old($Heap), this, _module.Map.keys), j#0);
        }

        if (*)
        {
            assume LitInt(0) <= j#0;
            assume j#0 < Seq#Length(read($Heap, this, _module.Map.values));
            assume i#0 != j#0;
            assert 0 <= j#0 && j#0 < Seq#Length(read($Heap, this, _module.Map.values));
            assert $IsAlloc(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value), old($Heap));
            assert 0 <= j#0 && j#0 < Seq#Length(read(old($Heap), this, _module.Map.values));
            assume Seq#Index(read($Heap, this, _module.Map.values), j#0)
               == Seq#Index(read(old($Heap), this, _module.Map.values), j#0);
        }
        else
        {
            assume LitInt(0) <= j#0
                 && j#0 < Seq#Length(read($Heap, this, _module.Map.values))
                 && i#0 != j#0
               ==> Seq#Index(read($Heap, this, _module.Map.values), j#0)
                 == Seq#Index(read(old($Heap), this, _module.Map.values), j#0);
        }

        assume (forall j#1: int ::
          { Seq#Index(read(old($Heap), this, _module.Map.values), j#1) }
            { Seq#Index(read($Heap, this, _module.Map.values), j#1) }
            { Seq#Index(read(old($Heap), this, _module.Map.keys), j#1) }
            { Seq#Index(read($Heap, this, _module.Map.keys), j#1) }
          true
             ==> (LitInt(0) <= j#1
                   && j#1 < Seq#Length(read($Heap, this, _module.Map.values))
                   && i#0 != j#1
                 ==> Seq#Index(read($Heap, this, _module.Map.keys), j#1)
                   == Seq#Index(read(old($Heap), this, _module.Map.keys), j#1))
               && (LitInt(0) <= j#1
                   && j#1 < Seq#Length(read($Heap, this, _module.Map.values))
                   && i#0 != j#1
                 ==> Seq#Index(read($Heap, this, _module.Map.values), j#1)
                   == Seq#Index(read(old($Heap), this, _module.Map.values), j#1)));
    }
    else
    {
        assume LitInt(0) <= i#0
             && i#0 < Seq#Length(read(old($Heap), this, _module.Map.keys))
             && Seq#Index(read(old($Heap), this, _module.Map.keys), i#0) == key#0
           ==> Seq#Length(read($Heap, this, _module.Map.keys))
               == Seq#Length(read(old($Heap), this, _module.Map.keys))
             && Seq#Index(read($Heap, this, _module.Map.keys), i#0) == key#0
             && Seq#Index(read($Heap, this, _module.Map.values), i#0) == val#0
             && (forall j#1: int ::
              { Seq#Index(read(old($Heap), this, _module.Map.values), j#1) }
                { Seq#Index(read($Heap, this, _module.Map.values), j#1) }
                { Seq#Index(read(old($Heap), this, _module.Map.keys), j#1) }
                { Seq#Index(read($Heap, this, _module.Map.keys), j#1) }
              true
                 ==> (LitInt(0) <= j#1
                       && j#1 < Seq#Length(read($Heap, this, _module.Map.values))
                       && i#0 != j#1
                     ==> Seq#Index(read($Heap, this, _module.Map.keys), j#1)
                       == Seq#Index(read(old($Heap), this, _module.Map.keys), j#1))
                   && (LitInt(0) <= j#1
                       && j#1 < Seq#Length(read($Heap, this, _module.Map.values))
                       && i#0 != j#1
                     ==> Seq#Index(read($Heap, this, _module.Map.values), j#1)
                       == Seq#Index(read(old($Heap), this, _module.Map.values), j#1)));
    }

    assume (forall i#1: int ::
      { Seq#Index(read($Heap, this, _module.Map.values), i#1) }
        { Seq#Index(read($Heap, this, _module.Map.keys), i#1) }
        { Seq#Index(read(old($Heap), this, _module.Map.keys), i#1) }
      true
         ==> (LitInt(0) <= i#1
               && i#1 < Seq#Length(read(old($Heap), this, _module.Map.keys))
               && Seq#Index(read(old($Heap), this, _module.Map.keys), i#1) == key#0
             ==> Seq#Length(read($Heap, this, _module.Map.keys))
               == Seq#Length(read(old($Heap), this, _module.Map.keys)))
           && (LitInt(0) <= i#1
               && i#1 < Seq#Length(read(old($Heap), this, _module.Map.keys))
               && Seq#Index(read(old($Heap), this, _module.Map.keys), i#1) == key#0
             ==> Seq#Index(read($Heap, this, _module.Map.keys), i#1) == key#0)
           && (LitInt(0) <= i#1
               && i#1 < Seq#Length(read(old($Heap), this, _module.Map.keys))
               && Seq#Index(read(old($Heap), this, _module.Map.keys), i#1) == key#0
             ==> Seq#Index(read($Heap, this, _module.Map.values), i#1) == val#0)
           && (LitInt(0) <= i#1
               && i#1 < Seq#Length(read(old($Heap), this, _module.Map.keys))
               && Seq#Index(read(old($Heap), this, _module.Map.keys), i#1) == key#0
             ==> (forall j#2: int ::
              { Seq#Index(read(old($Heap), this, _module.Map.values), j#2) }
                { Seq#Index(read($Heap, this, _module.Map.values), j#2) }
                { Seq#Index(read(old($Heap), this, _module.Map.keys), j#2) }
                { Seq#Index(read($Heap, this, _module.Map.keys), j#2) }
              true
                 ==> (LitInt(0) <= j#2
                       && j#2 < Seq#Length(read($Heap, this, _module.Map.values))
                       && i#1 != j#2
                     ==> Seq#Index(read($Heap, this, _module.Map.keys), j#2)
                       == Seq#Index(read(old($Heap), this, _module.Map.keys), j#2))
                   && (LitInt(0) <= j#2
                       && j#2 < Seq#Length(read($Heap, this, _module.Map.values))
                       && i#1 != j#2
                     ==> Seq#Index(read($Heap, this, _module.Map.values), j#2)
                       == Seq#Index(read(old($Heap), this, _module.Map.values), j#2)))));
    if (*)
    {
        assert $IsAlloc(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value), old($Heap));
        assume !Seq#Contains(read(old($Heap), this, _module.Map.keys), key#0);
        assert $IsAlloc(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value), old($Heap));
        assume Seq#Equal(read($Heap, this, _module.Map.keys),
          Seq#Append(read(old($Heap), this, _module.Map.keys), Seq#Build(Seq#Empty(): Seq Box, key#0)));
        assert $IsAlloc(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value), old($Heap));
        assume Seq#Equal(read($Heap, this, _module.Map.values),
          Seq#Append(read(old($Heap), this, _module.Map.values),
            Seq#Build(Seq#Empty(): Seq Box, val#0)));
    }
    else
    {
        assume !Seq#Contains(read(old($Heap), this, _module.Map.keys), key#0)
           ==> Seq#Equal(read($Heap, this, _module.Map.keys),
              Seq#Append(read(old($Heap), this, _module.Map.keys), Seq#Build(Seq#Empty(): Seq Box, key#0)))
             && Seq#Equal(read($Heap, this, _module.Map.values),
              Seq#Append(read(old($Heap), this, _module.Map.values),
                Seq#Build(Seq#Empty(): Seq Box, val#0)));
    }
}



procedure Call$$_module.Map.Add(_module.Map$Key: Ty,
    _module.Map$Value: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value))
         && $IsAlloc(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value), $Heap),
    key#0: Box
       where $IsBox(key#0, _module.Map$Key) && $IsAllocBox(key#0, _module.Map$Key, $Heap),
    val#0: Box
       where $IsBox(val#0, _module.Map$Value) && $IsAllocBox(val#0, _module.Map$Value, $Heap));
  // user-defined preconditions
  requires _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     ==> _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
       || Seq#Length(read($Heap, this, _module.Map.keys))
         == Seq#Length(read($Heap, this, _module.Map.values));
  requires _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     ==> _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
       || (forall i#2: int, j#3: int ::
        { Seq#Index(read($Heap, this, _module.Map.keys), j#3), Seq#Index(read($Heap, this, _module.Map.keys), i#2) }
        true
           ==>
          LitInt(0) <= i#2
             && i#2 < j#3
             && j#3 < Seq#Length(read($Heap, this, _module.Map.keys))
           ==> Seq#Index(read($Heap, this, _module.Map.keys), i#2)
             != Seq#Index(read($Heap, this, _module.Map.keys), j#3));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this);
  free ensures _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     &&
    _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
     &&
    Seq#Length(read($Heap, this, _module.Map.keys))
       == Seq#Length(read($Heap, this, _module.Map.values))
     && (forall i#3: int, j#4: int ::
      { Seq#Index(read($Heap, this, _module.Map.keys), j#4), Seq#Index(read($Heap, this, _module.Map.keys), i#3) }
      true
         ==>
        LitInt(0) <= i#3
           && i#3 < j#4
           && j#4 < Seq#Length(read($Heap, this, _module.Map.keys))
         ==> Seq#Index(read($Heap, this, _module.Map.keys), i#3)
           != Seq#Index(read($Heap, this, _module.Map.keys), j#4));
  free ensures (forall i#1: int ::
    { Seq#Index(read($Heap, this, _module.Map.values), i#1) }
      { Seq#Index(read($Heap, this, _module.Map.keys), i#1) }
      { Seq#Index(read(old($Heap), this, _module.Map.keys), i#1) }
    (LitInt(0) <= i#1
         && i#1 < Seq#Length(read(old($Heap), this, _module.Map.keys))
         && Seq#Index(read(old($Heap), this, _module.Map.keys), i#1) == key#0
       ==> Seq#Index(read($Heap, this, _module.Map.values), i#1) == val#0)
       ==>
      Seq#Index(read(old($Heap), this, _module.Map.keys), i#1) == key#0
       ==> (forall j#2: int ::
        { Seq#Index(read(old($Heap), this, _module.Map.values), j#2) }
          { Seq#Index(read($Heap, this, _module.Map.values), j#2) }
          { Seq#Index(read(old($Heap), this, _module.Map.keys), j#2) }
          { Seq#Index(read($Heap, this, _module.Map.keys), j#2) }
        true));
  ensures (forall i#1: int ::
    { Seq#Index(read($Heap, this, _module.Map.values), i#1) }
      { Seq#Index(read($Heap, this, _module.Map.keys), i#1) }
      { Seq#Index(read(old($Heap), this, _module.Map.keys), i#1) }
    true
       ==> (LitInt(0) <= i#1
             && i#1 < Seq#Length(read(old($Heap), this, _module.Map.keys))
             && Seq#Index(read(old($Heap), this, _module.Map.keys), i#1) == key#0
           ==> Seq#Length(read($Heap, this, _module.Map.keys))
             == Seq#Length(read(old($Heap), this, _module.Map.keys)))
         && (LitInt(0) <= i#1
             && i#1 < Seq#Length(read(old($Heap), this, _module.Map.keys))
             && Seq#Index(read(old($Heap), this, _module.Map.keys), i#1) == key#0
           ==> Seq#Index(read($Heap, this, _module.Map.keys), i#1) == key#0)
         && (LitInt(0) <= i#1
             && i#1 < Seq#Length(read(old($Heap), this, _module.Map.keys))
             && Seq#Index(read(old($Heap), this, _module.Map.keys), i#1) == key#0
           ==> Seq#Index(read($Heap, this, _module.Map.values), i#1) == val#0)
         && (LitInt(0) <= i#1
             && i#1 < Seq#Length(read(old($Heap), this, _module.Map.keys))
             && Seq#Index(read(old($Heap), this, _module.Map.keys), i#1) == key#0
           ==> (forall j#2: int ::
            { Seq#Index(read(old($Heap), this, _module.Map.values), j#2) }
              { Seq#Index(read($Heap, this, _module.Map.values), j#2) }
              { Seq#Index(read(old($Heap), this, _module.Map.keys), j#2) }
              { Seq#Index(read($Heap, this, _module.Map.keys), j#2) }
            true
               ==> (LitInt(0) <= j#2
                     && j#2 < Seq#Length(read($Heap, this, _module.Map.values))
                     && i#1 != j#2
                   ==> Seq#Index(read($Heap, this, _module.Map.keys), j#2)
                     == Seq#Index(read(old($Heap), this, _module.Map.keys), j#2))
                 && (LitInt(0) <= j#2
                     && j#2 < Seq#Length(read($Heap, this, _module.Map.values))
                     && i#1 != j#2
                   ==> Seq#Index(read($Heap, this, _module.Map.values), j#2)
                     == Seq#Index(read(old($Heap), this, _module.Map.values), j#2)))));
  free ensures true;
  ensures !Seq#Contains(read(old($Heap), this, _module.Map.keys), key#0)
     ==> Seq#Equal(read($Heap, this, _module.Map.keys),
      Seq#Append(read(old($Heap), this, _module.Map.keys), Seq#Build(Seq#Empty(): Seq Box, key#0)));
  ensures !Seq#Contains(read(old($Heap), this, _module.Map.keys), key#0)
     ==> Seq#Equal(read($Heap, this, _module.Map.values),
      Seq#Append(read(old($Heap), this, _module.Map.values),
        Seq#Build(Seq#Empty(): Seq Box, val#0)));
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f) || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Map.Add(_module.Map$Key: Ty,
    _module.Map$Value: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value))
         && $IsAlloc(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value), $Heap),
    key#0: Box
       where $IsBox(key#0, _module.Map$Key) && $IsAllocBox(key#0, _module.Map$Key, $Heap),
    val#0: Box
       where $IsBox(val#0, _module.Map$Value) && $IsAllocBox(val#0, _module.Map$Value, $Heap))
   returns ($_reverifyPost: bool);
  free requires 12 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     &&
    _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
     &&
    Seq#Length(read($Heap, this, _module.Map.keys))
       == Seq#Length(read($Heap, this, _module.Map.values))
     && (forall i#4: int, j#5: int ::
      { Seq#Index(read($Heap, this, _module.Map.keys), j#5), Seq#Index(read($Heap, this, _module.Map.keys), i#4) }
      true
         ==>
        LitInt(0) <= i#4
           && i#4 < j#5
           && j#5 < Seq#Length(read($Heap, this, _module.Map.keys))
         ==> Seq#Index(read($Heap, this, _module.Map.keys), i#4)
           != Seq#Index(read($Heap, this, _module.Map.keys), j#5));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this);
  ensures _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     ==> _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
       || Seq#Length(read($Heap, this, _module.Map.keys))
         == Seq#Length(read($Heap, this, _module.Map.values));
  ensures _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     ==> _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
       || (forall i#5: int, j#6: int ::
        { Seq#Index(read($Heap, this, _module.Map.keys), j#6), Seq#Index(read($Heap, this, _module.Map.keys), i#5) }
        true
           ==>
          LitInt(0) <= i#5
             && i#5 < j#6
             && j#6 < Seq#Length(read($Heap, this, _module.Map.keys))
           ==> Seq#Index(read($Heap, this, _module.Map.keys), i#5)
             != Seq#Index(read($Heap, this, _module.Map.keys), j#6));
  free ensures (forall i#1: int ::
    { Seq#Index(read($Heap, this, _module.Map.values), i#1) }
      { Seq#Index(read($Heap, this, _module.Map.keys), i#1) }
      { Seq#Index(read(old($Heap), this, _module.Map.keys), i#1) }
    (LitInt(0) <= i#1
         && i#1 < Seq#Length(read(old($Heap), this, _module.Map.keys))
         && Seq#Index(read(old($Heap), this, _module.Map.keys), i#1) == key#0
       ==> Seq#Index(read($Heap, this, _module.Map.values), i#1) == val#0)
       ==>
      Seq#Index(read(old($Heap), this, _module.Map.keys), i#1) == key#0
       ==> (forall j#2: int ::
        { Seq#Index(read(old($Heap), this, _module.Map.values), j#2) }
          { Seq#Index(read($Heap, this, _module.Map.values), j#2) }
          { Seq#Index(read(old($Heap), this, _module.Map.keys), j#2) }
          { Seq#Index(read($Heap, this, _module.Map.keys), j#2) }
        true));
  ensures (forall i#1: int ::
    { Seq#Index(read($Heap, this, _module.Map.values), i#1) }
      { Seq#Index(read($Heap, this, _module.Map.keys), i#1) }
      { Seq#Index(read(old($Heap), this, _module.Map.keys), i#1) }
    true
       ==> (LitInt(0) <= i#1
             && i#1 < Seq#Length(read(old($Heap), this, _module.Map.keys))
             && Seq#Index(read(old($Heap), this, _module.Map.keys), i#1) == key#0
           ==> Seq#Length(read($Heap, this, _module.Map.keys))
             == Seq#Length(read(old($Heap), this, _module.Map.keys)))
         && (LitInt(0) <= i#1
             && i#1 < Seq#Length(read(old($Heap), this, _module.Map.keys))
             && Seq#Index(read(old($Heap), this, _module.Map.keys), i#1) == key#0
           ==> Seq#Index(read($Heap, this, _module.Map.keys), i#1) == key#0)
         && (LitInt(0) <= i#1
             && i#1 < Seq#Length(read(old($Heap), this, _module.Map.keys))
             && Seq#Index(read(old($Heap), this, _module.Map.keys), i#1) == key#0
           ==> Seq#Index(read($Heap, this, _module.Map.values), i#1) == val#0)
         && (LitInt(0) <= i#1
             && i#1 < Seq#Length(read(old($Heap), this, _module.Map.keys))
             && Seq#Index(read(old($Heap), this, _module.Map.keys), i#1) == key#0
           ==> (forall j#2: int ::
            { Seq#Index(read(old($Heap), this, _module.Map.values), j#2) }
              { Seq#Index(read($Heap, this, _module.Map.values), j#2) }
              { Seq#Index(read(old($Heap), this, _module.Map.keys), j#2) }
              { Seq#Index(read($Heap, this, _module.Map.keys), j#2) }
            true
               ==> (LitInt(0) <= j#2
                     && j#2 < Seq#Length(read($Heap, this, _module.Map.values))
                     && i#1 != j#2
                   ==> Seq#Index(read($Heap, this, _module.Map.keys), j#2)
                     == Seq#Index(read(old($Heap), this, _module.Map.keys), j#2))
                 && (LitInt(0) <= j#2
                     && j#2 < Seq#Length(read($Heap, this, _module.Map.values))
                     && i#1 != j#2
                   ==> Seq#Index(read($Heap, this, _module.Map.values), j#2)
                     == Seq#Index(read(old($Heap), this, _module.Map.values), j#2)))));
  free ensures true;
  ensures !Seq#Contains(read(old($Heap), this, _module.Map.keys), key#0)
     ==> Seq#Equal(read($Heap, this, _module.Map.keys),
      Seq#Append(read(old($Heap), this, _module.Map.keys), Seq#Build(Seq#Empty(): Seq Box, key#0)));
  ensures !Seq#Contains(read(old($Heap), this, _module.Map.keys), key#0)
     ==> Seq#Equal(read($Heap, this, _module.Map.values),
      Seq#Append(read(old($Heap), this, _module.Map.values),
        Seq#Build(Seq#Empty(): Seq Box, val#0)));
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f) || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Map.Add(_module.Map$Key: Ty, _module.Map$Value: Ty, this: ref, key#0: Box, val#0: Box)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var j#7: int;
  var $rhs##0: int;
  var key##0: Box;
  var $rhs#0_0: Seq Box where $Is($rhs#0_0, TSeq(_module.Map$Key));
  var $rhs#0_1: Seq Box where $Is($rhs#0_1, TSeq(_module.Map$Value));
  var $rhs#0: Seq Box where $Is($rhs#0, TSeq(_module.Map$Value));

    // AddMethodImpl: Add, Impl$$_module.Map.Add
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> $o == this);
    assume {:captureState "b8.dfy(294,2): initial state"} true;
    $_reverifyPost := false;
    // ----- call statement ----- b8.dfy(295,23)
    assume true;
    // TrCallStmt: Adding lhs Microsoft.Dafny.AutoGhostIdentifierExpr with type int
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    key##0 := key#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##0 := Call$$_module.Map.FindIndex(_module.Map$Key, _module.Map$Value, this, key##0);
    // TrCallStmt: After ProcessCallStmt
    j#7 := $rhs##0;
    assume {:captureState "b8.dfy(295,27)"} true;
    // ----- if statement ----- b8.dfy(296,5)
    assume true;
    if (j#7 == LitInt(0 - 1))
    {
        // ----- assignment statement ----- b8.dfy(297,12)
        assume true;
        assert $_Frame[this, _module.Map.keys];
        assume true;
        $rhs#0_0 := Seq#Append(read($Heap, this, _module.Map.keys), Seq#Build(Seq#Empty(): Seq Box, key#0));
        $Heap := update($Heap, this, _module.Map.keys, $rhs#0_0);
        assume $IsGoodHeap($Heap);
        assume {:captureState "b8.dfy(297,26)"} true;
        // ----- assignment statement ----- b8.dfy(298,14)
        assume true;
        assert $_Frame[this, _module.Map.values];
        assume true;
        $rhs#0_1 := Seq#Append(read($Heap, this, _module.Map.values), Seq#Build(Seq#Empty(): Seq Box, val#0));
        $Heap := update($Heap, this, _module.Map.values, $rhs#0_1);
        assume $IsGoodHeap($Heap);
        assume {:captureState "b8.dfy(298,30)"} true;
    }
    else
    {
        // ----- assignment statement ----- b8.dfy(300,14)
        assume true;
        assert $_Frame[this, _module.Map.values];
        assert 0 <= j#7 && j#7 < Seq#Length(read($Heap, this, _module.Map.values));
        assume true;
        $rhs#0 := Seq#Update(read($Heap, this, _module.Map.values), j#7, val#0);
        $Heap := update($Heap, this, _module.Map.values, $rhs#0);
        assume $IsGoodHeap($Heap);
        assume {:captureState "b8.dfy(300,32)"} true;
    }
}



procedure CheckWellformed$$_module.Map.Remove(_module.Map$Key: Ty,
    _module.Map$Value: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value))
         && $IsAlloc(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value), $Heap),
    key#0: Box
       where $IsBox(key#0, _module.Map$Key) && $IsAllocBox(key#0, _module.Map$Key, $Heap));
  free requires 24 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.Map.Remove(_module.Map$Key: Ty, _module.Map$Value: Ty, this: ref, key#0: Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var k#0: Box;
  var k#2: Box;
  var h#0: int;

    // AddMethodImpl: Remove, CheckWellformed$$_module.Map.Remove
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> $o == this);
    assume {:captureState "b8.dfy(304,9): initial state"} true;
    assume _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this);
    assume _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this);
    havoc $Heap;
    assume (forall<alpha> $o: ref, $f: Field alpha ::
      { read($Heap, $o, $f) }
      $o != null && read(old($Heap), $o, alloc)
         ==> read($Heap, $o, $f) == read(old($Heap), $o, $f) || $o == this);
    assume $HeapSucc(old($Heap), $Heap);
    assume {:captureState "b8.dfy(307,17): post-state"} true;
    assume _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this);
    assume _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this);
    havoc k#0;
    assume $IsBox(k#0, _module.Map$Key);
    // Begin Comprehension WF check
    if (Seq#Contains(read($Heap, this, _module.Map.keys), k#0))
    {
        assert $IsAlloc(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value), old($Heap));
    }

    // End Comprehension WF check
    assume (forall k#1: Box ::
      { Seq#Contains(read(old($Heap), this, _module.Map.keys), k#1) }
        { Seq#Contains(read($Heap, this, _module.Map.keys), k#1) }
      $IsBox(k#1, _module.Map$Key)
         ==>
        Seq#Contains(read($Heap, this, _module.Map.keys), k#1)
         ==> Seq#Contains(read(old($Heap), this, _module.Map.keys), k#1));
    havoc k#2;
    assume $IsBox(k#2, _module.Map$Key);
    if (*)
    {
        assert $IsAlloc(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value), old($Heap));
        assume Seq#Contains(read(old($Heap), this, _module.Map.keys), k#2);
        if (*)
        {
            assume Seq#Contains(read($Heap, this, _module.Map.keys), k#2);
        }
        else
        {
            assume !Seq#Contains(read($Heap, this, _module.Map.keys), k#2);
            assume k#2 == key#0;
        }
    }
    else
    {
        assume Seq#Contains(read(old($Heap), this, _module.Map.keys), k#2)
           ==> Seq#Contains(read($Heap, this, _module.Map.keys), k#2) || k#2 == key#0;
    }

    assume (forall k#3: Box ::
      { Seq#Contains(read($Heap, this, _module.Map.keys), k#3) }
        { Seq#Contains(read(old($Heap), this, _module.Map.keys), k#3) }
      $IsBox(k#3, _module.Map$Key)
         ==>
        Seq#Contains(read(old($Heap), this, _module.Map.keys), k#3)
         ==> Seq#Contains(read($Heap, this, _module.Map.keys), k#3) || k#3 == key#0);
    if (*)
    {
        assert $IsAlloc(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value), old($Heap));
        assume !Seq#Contains(read(old($Heap), this, _module.Map.keys), key#0);
        assert $IsAlloc(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value), old($Heap));
        assume Seq#Equal(read($Heap, this, _module.Map.keys), read(old($Heap), this, _module.Map.keys));
        assert $IsAlloc(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value), old($Heap));
        assume Seq#Equal(read($Heap, this, _module.Map.values),
          read(old($Heap), this, _module.Map.values));
    }
    else
    {
        assume !Seq#Contains(read(old($Heap), this, _module.Map.keys), key#0)
           ==> Seq#Equal(read($Heap, this, _module.Map.keys), read(old($Heap), this, _module.Map.keys))
             && Seq#Equal(read($Heap, this, _module.Map.values),
              read(old($Heap), this, _module.Map.values));
    }

    if (*)
    {
        assert $IsAlloc(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value), old($Heap));
        assume Seq#Contains(read(old($Heap), this, _module.Map.keys), key#0);
        assert $IsAlloc(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value), old($Heap));
        assume Seq#Length(read($Heap, this, _module.Map.keys))
           == Seq#Length(read(old($Heap), this, _module.Map.keys)) - 1;
        assume !Seq#Contains(read($Heap, this, _module.Map.keys), key#0);
        havoc h#0;
        assume LitInt(0) <= h#0;
        assume h#0 <= Seq#Length(read($Heap, this, _module.Map.keys));
        assert 0 <= h#0 && h#0 <= Seq#Length(read($Heap, this, _module.Map.keys));
        assert $IsAlloc(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value), old($Heap));
        assert 0 <= h#0 && h#0 <= Seq#Length(read(old($Heap), this, _module.Map.keys));
        assume Seq#Equal(Seq#Take(read($Heap, this, _module.Map.keys), h#0),
          Seq#Take(read(old($Heap), this, _module.Map.keys), h#0));
        assert 0 <= h#0 && h#0 <= Seq#Length(read($Heap, this, _module.Map.values));
        assert $IsAlloc(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value), old($Heap));
        assert 0 <= h#0 && h#0 <= Seq#Length(read(old($Heap), this, _module.Map.values));
        assume Seq#Equal(Seq#Take(read($Heap, this, _module.Map.values), h#0),
          Seq#Take(read(old($Heap), this, _module.Map.values), h#0));
        assert 0 <= h#0 && h#0 <= Seq#Length(read($Heap, this, _module.Map.keys));
        assert $IsAlloc(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value), old($Heap));
        assert 0 <= h#0 + 1 && h#0 + 1 <= Seq#Length(read(old($Heap), this, _module.Map.keys));
        assume Seq#Equal(Seq#Drop(read($Heap, this, _module.Map.keys), h#0),
          Seq#Drop(read(old($Heap), this, _module.Map.keys), h#0 + 1));
        assert 0 <= h#0 && h#0 <= Seq#Length(read($Heap, this, _module.Map.values));
        assert $IsAlloc(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value), old($Heap));
        assert 0 <= h#0 + 1
           && h#0 + 1 <= Seq#Length(read(old($Heap), this, _module.Map.values));
        assume Seq#Equal(Seq#Drop(read($Heap, this, _module.Map.values), h#0),
          Seq#Drop(read(old($Heap), this, _module.Map.values), h#0 + 1));
    }
    else
    {
        assume Seq#Contains(read(old($Heap), this, _module.Map.keys), key#0)
           ==> Seq#Length(read($Heap, this, _module.Map.keys))
               == Seq#Length(read(old($Heap), this, _module.Map.keys)) - 1
             && !Seq#Contains(read($Heap, this, _module.Map.keys), key#0)
             && (exists h#1: int ::
              { Seq#Drop(read($Heap, this, _module.Map.values), h#1) }
                { Seq#Drop(read($Heap, this, _module.Map.keys), h#1) }
                { Seq#Take(read(old($Heap), this, _module.Map.values), h#1) }
                { Seq#Take(read($Heap, this, _module.Map.values), h#1) }
                { Seq#Take(read(old($Heap), this, _module.Map.keys), h#1) }
                { Seq#Take(read($Heap, this, _module.Map.keys), h#1) }
              LitInt(0) <= h#1
                 && h#1 <= Seq#Length(read($Heap, this, _module.Map.keys))
                 && Seq#Equal(Seq#Take(read($Heap, this, _module.Map.keys), h#1),
                  Seq#Take(read(old($Heap), this, _module.Map.keys), h#1))
                 && Seq#Equal(Seq#Take(read($Heap, this, _module.Map.values), h#1),
                  Seq#Take(read(old($Heap), this, _module.Map.values), h#1))
                 && Seq#Equal(Seq#Drop(read($Heap, this, _module.Map.keys), h#1),
                  Seq#Drop(read(old($Heap), this, _module.Map.keys), h#1 + 1))
                 && Seq#Equal(Seq#Drop(read($Heap, this, _module.Map.values), h#1),
                  Seq#Drop(read(old($Heap), this, _module.Map.values), h#1 + 1)));
    }
}



procedure Call$$_module.Map.Remove(_module.Map$Key: Ty,
    _module.Map$Value: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value))
         && $IsAlloc(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value), $Heap),
    key#0: Box
       where $IsBox(key#0, _module.Map$Key) && $IsAllocBox(key#0, _module.Map$Key, $Heap));
  // user-defined preconditions
  requires _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     ==> _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
       || Seq#Length(read($Heap, this, _module.Map.keys))
         == Seq#Length(read($Heap, this, _module.Map.values));
  requires _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     ==> _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
       || (forall i#0: int, j#0: int ::
        { Seq#Index(read($Heap, this, _module.Map.keys), j#0), Seq#Index(read($Heap, this, _module.Map.keys), i#0) }
        true
           ==>
          LitInt(0) <= i#0
             && i#0 < j#0
             && j#0 < Seq#Length(read($Heap, this, _module.Map.keys))
           ==> Seq#Index(read($Heap, this, _module.Map.keys), i#0)
             != Seq#Index(read($Heap, this, _module.Map.keys), j#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this);
  free ensures _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     &&
    _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
     &&
    Seq#Length(read($Heap, this, _module.Map.keys))
       == Seq#Length(read($Heap, this, _module.Map.values))
     && (forall i#1: int, j#1: int ::
      { Seq#Index(read($Heap, this, _module.Map.keys), j#1), Seq#Index(read($Heap, this, _module.Map.keys), i#1) }
      true
         ==>
        LitInt(0) <= i#1
           && i#1 < j#1
           && j#1 < Seq#Length(read($Heap, this, _module.Map.keys))
         ==> Seq#Index(read($Heap, this, _module.Map.keys), i#1)
           != Seq#Index(read($Heap, this, _module.Map.keys), j#1));
  free ensures (forall k#1: Box ::
    { Seq#Contains(read(old($Heap), this, _module.Map.keys), k#1) }
      { Seq#Contains(read($Heap, this, _module.Map.keys), k#1) }
    true);
  ensures (forall k#1: Box ::
    { Seq#Contains(read(old($Heap), this, _module.Map.keys), k#1) }
      { Seq#Contains(read($Heap, this, _module.Map.keys), k#1) }
    $IsBox(k#1, _module.Map$Key)
       ==>
      Seq#Contains(read($Heap, this, _module.Map.keys), k#1)
       ==> Seq#Contains(read(old($Heap), this, _module.Map.keys), k#1));
  free ensures (forall k#3: Box ::
    { Seq#Contains(read($Heap, this, _module.Map.keys), k#3) }
      { Seq#Contains(read(old($Heap), this, _module.Map.keys), k#3) }
    true);
  ensures (forall k#3: Box ::
    { Seq#Contains(read($Heap, this, _module.Map.keys), k#3) }
      { Seq#Contains(read(old($Heap), this, _module.Map.keys), k#3) }
    $IsBox(k#3, _module.Map$Key)
       ==>
      Seq#Contains(read(old($Heap), this, _module.Map.keys), k#3)
       ==> Seq#Contains(read($Heap, this, _module.Map.keys), k#3) || k#3 == key#0);
  free ensures true;
  ensures !Seq#Contains(read(old($Heap), this, _module.Map.keys), key#0)
     ==> Seq#Equal(read($Heap, this, _module.Map.keys), read(old($Heap), this, _module.Map.keys));
  ensures !Seq#Contains(read(old($Heap), this, _module.Map.keys), key#0)
     ==> Seq#Equal(read($Heap, this, _module.Map.values),
      read(old($Heap), this, _module.Map.values));
  free ensures Seq#Contains(read(old($Heap), this, _module.Map.keys), key#0)
     ==>
    !Seq#Contains(read($Heap, this, _module.Map.keys), key#0)
     ==> (forall h#1: int ::
      { Seq#Drop(read($Heap, this, _module.Map.values), h#1) }
        { Seq#Drop(read($Heap, this, _module.Map.keys), h#1) }
        { Seq#Take(read(old($Heap), this, _module.Map.values), h#1) }
        { Seq#Take(read($Heap, this, _module.Map.values), h#1) }
        { Seq#Take(read(old($Heap), this, _module.Map.keys), h#1) }
        { Seq#Take(read($Heap, this, _module.Map.keys), h#1) }
      true);
  ensures Seq#Contains(read(old($Heap), this, _module.Map.keys), key#0)
     ==> Seq#Length(read($Heap, this, _module.Map.keys))
       == Seq#Length(read(old($Heap), this, _module.Map.keys)) - 1;
  ensures Seq#Contains(read(old($Heap), this, _module.Map.keys), key#0)
     ==> !Seq#Contains(read($Heap, this, _module.Map.keys), key#0);
  ensures Seq#Contains(read(old($Heap), this, _module.Map.keys), key#0)
     ==> (exists h#1: int ::
      { Seq#Drop(read($Heap, this, _module.Map.values), h#1) }
        { Seq#Drop(read($Heap, this, _module.Map.keys), h#1) }
        { Seq#Take(read(old($Heap), this, _module.Map.values), h#1) }
        { Seq#Take(read($Heap, this, _module.Map.values), h#1) }
        { Seq#Take(read(old($Heap), this, _module.Map.keys), h#1) }
        { Seq#Take(read($Heap, this, _module.Map.keys), h#1) }
      LitInt(0) <= h#1
         && h#1 <= Seq#Length(read($Heap, this, _module.Map.keys))
         && Seq#Equal(Seq#Take(read($Heap, this, _module.Map.keys), h#1),
          Seq#Take(read(old($Heap), this, _module.Map.keys), h#1))
         && Seq#Equal(Seq#Take(read($Heap, this, _module.Map.values), h#1),
          Seq#Take(read(old($Heap), this, _module.Map.values), h#1))
         && Seq#Equal(Seq#Drop(read($Heap, this, _module.Map.keys), h#1),
          Seq#Drop(read(old($Heap), this, _module.Map.keys), h#1 + 1))
         && Seq#Equal(Seq#Drop(read($Heap, this, _module.Map.values), h#1),
          Seq#Drop(read(old($Heap), this, _module.Map.values), h#1 + 1)));
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f) || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Map.Remove(_module.Map$Key: Ty,
    _module.Map$Value: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value))
         && $IsAlloc(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value), $Heap),
    key#0: Box
       where $IsBox(key#0, _module.Map$Key) && $IsAllocBox(key#0, _module.Map$Key, $Heap))
   returns ($_reverifyPost: bool);
  free requires 24 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     &&
    _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
     &&
    Seq#Length(read($Heap, this, _module.Map.keys))
       == Seq#Length(read($Heap, this, _module.Map.values))
     && (forall i#2: int, j#2: int ::
      { Seq#Index(read($Heap, this, _module.Map.keys), j#2), Seq#Index(read($Heap, this, _module.Map.keys), i#2) }
      true
         ==>
        LitInt(0) <= i#2
           && i#2 < j#2
           && j#2 < Seq#Length(read($Heap, this, _module.Map.keys))
         ==> Seq#Index(read($Heap, this, _module.Map.keys), i#2)
           != Seq#Index(read($Heap, this, _module.Map.keys), j#2));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this);
  ensures _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     ==> _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
       || Seq#Length(read($Heap, this, _module.Map.keys))
         == Seq#Length(read($Heap, this, _module.Map.values));
  ensures _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     ==> _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
       || (forall i#3: int, j#3: int ::
        { Seq#Index(read($Heap, this, _module.Map.keys), j#3), Seq#Index(read($Heap, this, _module.Map.keys), i#3) }
        true
           ==>
          LitInt(0) <= i#3
             && i#3 < j#3
             && j#3 < Seq#Length(read($Heap, this, _module.Map.keys))
           ==> Seq#Index(read($Heap, this, _module.Map.keys), i#3)
             != Seq#Index(read($Heap, this, _module.Map.keys), j#3));
  free ensures (forall k#1: Box ::
    { Seq#Contains(read(old($Heap), this, _module.Map.keys), k#1) }
      { Seq#Contains(read($Heap, this, _module.Map.keys), k#1) }
    true);
  ensures (forall k#1: Box ::
    { Seq#Contains(read(old($Heap), this, _module.Map.keys), k#1) }
      { Seq#Contains(read($Heap, this, _module.Map.keys), k#1) }
    $IsBox(k#1, _module.Map$Key)
       ==>
      Seq#Contains(read($Heap, this, _module.Map.keys), k#1)
       ==> Seq#Contains(read(old($Heap), this, _module.Map.keys), k#1));
  free ensures (forall k#3: Box ::
    { Seq#Contains(read($Heap, this, _module.Map.keys), k#3) }
      { Seq#Contains(read(old($Heap), this, _module.Map.keys), k#3) }
    true);
  ensures (forall k#3: Box ::
    { Seq#Contains(read($Heap, this, _module.Map.keys), k#3) }
      { Seq#Contains(read(old($Heap), this, _module.Map.keys), k#3) }
    $IsBox(k#3, _module.Map$Key)
       ==>
      Seq#Contains(read(old($Heap), this, _module.Map.keys), k#3)
       ==> Seq#Contains(read($Heap, this, _module.Map.keys), k#3) || k#3 == key#0);
  free ensures true;
  ensures !Seq#Contains(read(old($Heap), this, _module.Map.keys), key#0)
     ==> Seq#Equal(read($Heap, this, _module.Map.keys), read(old($Heap), this, _module.Map.keys));
  ensures !Seq#Contains(read(old($Heap), this, _module.Map.keys), key#0)
     ==> Seq#Equal(read($Heap, this, _module.Map.values),
      read(old($Heap), this, _module.Map.values));
  free ensures Seq#Contains(read(old($Heap), this, _module.Map.keys), key#0)
     ==>
    !Seq#Contains(read($Heap, this, _module.Map.keys), key#0)
     ==> (forall h#1: int ::
      { Seq#Drop(read($Heap, this, _module.Map.values), h#1) }
        { Seq#Drop(read($Heap, this, _module.Map.keys), h#1) }
        { Seq#Take(read(old($Heap), this, _module.Map.values), h#1) }
        { Seq#Take(read($Heap, this, _module.Map.values), h#1) }
        { Seq#Take(read(old($Heap), this, _module.Map.keys), h#1) }
        { Seq#Take(read($Heap, this, _module.Map.keys), h#1) }
      true);
  ensures Seq#Contains(read(old($Heap), this, _module.Map.keys), key#0)
     ==> Seq#Length(read($Heap, this, _module.Map.keys))
       == Seq#Length(read(old($Heap), this, _module.Map.keys)) - 1;
  ensures Seq#Contains(read(old($Heap), this, _module.Map.keys), key#0)
     ==> !Seq#Contains(read($Heap, this, _module.Map.keys), key#0);
  ensures Seq#Contains(read(old($Heap), this, _module.Map.keys), key#0)
     ==> (exists h#1: int ::
      { Seq#Drop(read($Heap, this, _module.Map.values), h#1) }
        { Seq#Drop(read($Heap, this, _module.Map.keys), h#1) }
        { Seq#Take(read(old($Heap), this, _module.Map.values), h#1) }
        { Seq#Take(read($Heap, this, _module.Map.values), h#1) }
        { Seq#Take(read(old($Heap), this, _module.Map.keys), h#1) }
        { Seq#Take(read($Heap, this, _module.Map.keys), h#1) }
      LitInt(0) <= h#1
         && h#1 <= Seq#Length(read($Heap, this, _module.Map.keys))
         && Seq#Equal(Seq#Take(read($Heap, this, _module.Map.keys), h#1),
          Seq#Take(read(old($Heap), this, _module.Map.keys), h#1))
         && Seq#Equal(Seq#Take(read($Heap, this, _module.Map.values), h#1),
          Seq#Take(read(old($Heap), this, _module.Map.values), h#1))
         && Seq#Equal(Seq#Drop(read($Heap, this, _module.Map.keys), h#1),
          Seq#Drop(read(old($Heap), this, _module.Map.keys), h#1 + 1))
         && Seq#Equal(Seq#Drop(read($Heap, this, _module.Map.values), h#1),
          Seq#Drop(read(old($Heap), this, _module.Map.values), h#1 + 1)));
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f) || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Map.Remove(_module.Map$Key: Ty, _module.Map$Value: Ty, this: ref, key#0: Box)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var j#4: int;
  var $rhs##0: int;
  var key##0: Box;
  var $rhs#0_0: Seq Box where $Is($rhs#0_0, TSeq(_module.Map$Key));
  var $rhs#0_1: Seq Box where $Is($rhs#0_1, TSeq(_module.Map$Value));

    // AddMethodImpl: Remove, Impl$$_module.Map.Remove
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> $o == this);
    assume {:captureState "b8.dfy(323,2): initial state"} true;
    $_reverifyPost := false;
    // ----- call statement ----- b8.dfy(324,23)
    assume true;
    // TrCallStmt: Adding lhs Microsoft.Dafny.AutoGhostIdentifierExpr with type int
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    key##0 := key#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##0 := Call$$_module.Map.FindIndex(_module.Map$Key, _module.Map$Value, this, key##0);
    // TrCallStmt: After ProcessCallStmt
    j#4 := $rhs##0;
    assume {:captureState "b8.dfy(324,27)"} true;
    // ----- if statement ----- b8.dfy(325,5)
    assume true;
    if (LitInt(0) <= j#4)
    {
        // ----- assignment statement ----- b8.dfy(326,12)
        assume true;
        assert $_Frame[this, _module.Map.keys];
        assert 0 <= j#4 && j#4 <= Seq#Length(read($Heap, this, _module.Map.keys));
        assert 0 <= j#4 + 1 && j#4 + 1 <= Seq#Length(read($Heap, this, _module.Map.keys));
        assume true;
        $rhs#0_0 := Seq#Append(Seq#Take(read($Heap, this, _module.Map.keys), j#4),
          Seq#Drop(read($Heap, this, _module.Map.keys), j#4 + 1));
        $Heap := update($Heap, this, _module.Map.keys, $rhs#0_0);
        assume $IsGoodHeap($Heap);
        assume {:captureState "b8.dfy(326,37)"} true;
        // ----- assignment statement ----- b8.dfy(327,14)
        assume true;
        assert $_Frame[this, _module.Map.values];
        assert 0 <= j#4 && j#4 <= Seq#Length(read($Heap, this, _module.Map.values));
        assert 0 <= j#4 + 1 && j#4 + 1 <= Seq#Length(read($Heap, this, _module.Map.values));
        assume true;
        $rhs#0_1 := Seq#Append(Seq#Take(read($Heap, this, _module.Map.values), j#4),
          Seq#Drop(read($Heap, this, _module.Map.values), j#4 + 1));
        $Heap := update($Heap, this, _module.Map.values, $rhs#0_1);
        assume $IsGoodHeap($Heap);
        assume {:captureState "b8.dfy(327,43)"} true;
    }
    else
    {
    }
}



procedure CheckWellformed$$_module.Map.FindIndex(_module.Map$Key: Ty,
    _module.Map$Value: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value))
         && $IsAlloc(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value), $Heap),
    key#0: Box
       where $IsBox(key#0, _module.Map$Key) && $IsAllocBox(key#0, _module.Map$Key, $Heap))
   returns (idx#0: int);
  free requires 10 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.Map.FindIndex(_module.Map$Key: Ty, _module.Map$Value: Ty, this: ref, key#0: Box)
   returns (idx#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: FindIndex, CheckWellformed$$_module.Map.FindIndex
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "b8.dfy(331,9): initial state"} true;
    assume _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this);
    assume _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this);
    havoc $Heap;
    assume (forall<alpha> $o: ref, $f: Field alpha ::
      { read($Heap, $o, $f) }
      $o != null && read(old($Heap), $o, alloc)
         ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
    assume $HeapSucc(old($Heap), $Heap);
    havoc idx#0;
    assume {:captureState "b8.dfy(333,22): post-state"} true;
    assume LitInt(0 - 1) <= idx#0;
    assume idx#0 < Seq#Length(read($Heap, this, _module.Map.keys));
    if (*)
    {
        assume idx#0 == LitInt(0 - 1);
        assume !Seq#Contains(read($Heap, this, _module.Map.keys), key#0);
    }
    else
    {
        assume idx#0 == LitInt(0 - 1)
           ==> !Seq#Contains(read($Heap, this, _module.Map.keys), key#0);
    }

    if (*)
    {
        assume LitInt(0) <= idx#0;
        assert 0 <= idx#0 && idx#0 < Seq#Length(read($Heap, this, _module.Map.keys));
        assume Seq#Index(read($Heap, this, _module.Map.keys), idx#0) == key#0;
    }
    else
    {
        assume LitInt(0) <= idx#0
           ==> Seq#Index(read($Heap, this, _module.Map.keys), idx#0) == key#0;
    }
}



procedure Call$$_module.Map.FindIndex(_module.Map$Key: Ty,
    _module.Map$Value: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value))
         && $IsAlloc(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value), $Heap),
    key#0: Box
       where $IsBox(key#0, _module.Map$Key) && $IsAllocBox(key#0, _module.Map$Key, $Heap))
   returns (idx#0: int);
  // user-defined preconditions
  requires _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     ==> _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
       || Seq#Length(read($Heap, this, _module.Map.keys))
         == Seq#Length(read($Heap, this, _module.Map.values));
  requires _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     ==> _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
       || (forall i#0: int, j#0: int ::
        { Seq#Index(read($Heap, this, _module.Map.keys), j#0), Seq#Index(read($Heap, this, _module.Map.keys), i#0) }
        true
           ==>
          LitInt(0) <= i#0
             && i#0 < j#0
             && j#0 < Seq#Length(read($Heap, this, _module.Map.keys))
           ==> Seq#Index(read($Heap, this, _module.Map.keys), i#0)
             != Seq#Index(read($Heap, this, _module.Map.keys), j#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures LitInt(0 - 1) <= idx#0;
  ensures idx#0 < Seq#Length(read($Heap, this, _module.Map.keys));
  free ensures true;
  ensures idx#0 == LitInt(0 - 1)
     ==> !Seq#Contains(read($Heap, this, _module.Map.keys), key#0);
  free ensures true;
  ensures LitInt(0) <= idx#0
     ==> Seq#Index(read($Heap, this, _module.Map.keys), idx#0) == key#0;
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Map.FindIndex(_module.Map$Key: Ty,
    _module.Map$Value: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value))
         && $IsAlloc(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value), $Heap),
    key#0: Box
       where $IsBox(key#0, _module.Map$Key) && $IsAllocBox(key#0, _module.Map$Key, $Heap))
   returns (idx#0: int, $_reverifyPost: bool);
  free requires 10 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     &&
    _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
     &&
    Seq#Length(read($Heap, this, _module.Map.keys))
       == Seq#Length(read($Heap, this, _module.Map.values))
     && (forall i#1: int, j#1: int ::
      { Seq#Index(read($Heap, this, _module.Map.keys), j#1), Seq#Index(read($Heap, this, _module.Map.keys), i#1) }
      true
         ==>
        LitInt(0) <= i#1
           && i#1 < j#1
           && j#1 < Seq#Length(read($Heap, this, _module.Map.keys))
         ==> Seq#Index(read($Heap, this, _module.Map.keys), i#1)
           != Seq#Index(read($Heap, this, _module.Map.keys), j#1));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures LitInt(0 - 1) <= idx#0;
  ensures idx#0 < Seq#Length(read($Heap, this, _module.Map.keys));
  free ensures true;
  ensures idx#0 == LitInt(0 - 1)
     ==> !Seq#Contains(read($Heap, this, _module.Map.keys), key#0);
  free ensures true;
  ensures LitInt(0) <= idx#0
     ==> Seq#Index(read($Heap, this, _module.Map.keys), idx#0) == key#0;
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Map.FindIndex(_module.Map$Key: Ty, _module.Map$Value: Ty, this: ref, key#0: Box)
   returns (idx#0: int, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var j#2: int;
  var $PreLoopHeap$loop#0: Heap;
  var $decr_init$loop#00: int;
  var $w$loop#0: bool;
  var $decr$loop#00: int;

    // AddMethodImpl: FindIndex, Impl$$_module.Map.FindIndex
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "b8.dfy(336,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- b8.dfy(337,11)
    assume true;
    assume true;
    j#2 := LitInt(0);
    assume {:captureState "b8.dfy(337,14)"} true;
    // ----- while statement ----- b8.dfy(338,5)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    $decr_init$loop#00 := Seq#Length(read($Heap, this, _module.Map.keys)) - j#2;
    havoc $w$loop#0;
    while (true)
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0 ==> j#2 <= Seq#Length(read($Heap, this, _module.Map.keys));
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0
         ==> !Seq#Contains(Seq#Take(read($Heap, this, _module.Map.keys), j#2), key#0);
      free invariant (forall<alpha> $o: ref, $f: Field alpha ::
        { read($Heap, $o, $f) }
        $o != null && read(old($Heap), $o, alloc)
           ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0, $o, $f));
      free invariant $HeapSucc($PreLoopHeap$loop#0, $Heap);
      free invariant (forall<alpha> $o: ref, $f: Field alpha ::
        { read($Heap, $o, $f) }
        $o != null && read($PreLoopHeap$loop#0, $o, alloc)
           ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0, $o, $f) || $_Frame[$o, $f]);
      free invariant Seq#Length(read($Heap, this, _module.Map.keys)) - j#2 <= $decr_init$loop#00
         && (Seq#Length(read($Heap, this, _module.Map.keys)) - j#2 == $decr_init$loop#00
           ==> true);
    {
        assume {:captureState "b8.dfy(338,4): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            assume true;
            assume j#2 <= Seq#Length(read($Heap, this, _module.Map.keys));
            assert {:subsumption 0} 0 <= j#2 && j#2 <= Seq#Length(read($Heap, this, _module.Map.keys));
            assume true;
            assume !Seq#Contains(Seq#Take(read($Heap, this, _module.Map.keys), j#2), key#0);
            assume true;
            assume false;
        }

        assume true;
        if (Seq#Length(read($Heap, this, _module.Map.keys)) <= j#2)
        {
            break;
        }

        $decr$loop#00 := Seq#Length(read($Heap, this, _module.Map.keys)) - j#2;
        // ----- if statement ----- b8.dfy(342,7)
        assert 0 <= j#2 && j#2 < Seq#Length(read($Heap, this, _module.Map.keys));
        assume true;
        if (Seq#Index(read($Heap, this, _module.Map.keys), j#2) == key#0)
        {
            // ----- assignment statement ----- b8.dfy(343,13)
            assume true;
            assume true;
            idx#0 := j#2;
            assume {:captureState "b8.dfy(343,16)"} true;
            // ----- return statement ----- b8.dfy(344,9)
            return;
        }
        else
        {
        }

        // ----- assignment statement ----- b8.dfy(346,9)
        assume true;
        assume true;
        j#2 := j#2 + 1;
        assume {:captureState "b8.dfy(346,16)"} true;
        // ----- loop termination check ----- b8.dfy(338,5)
        assert 0 <= $decr$loop#00
           || Seq#Length(read($Heap, this, _module.Map.keys)) - j#2 == $decr$loop#00;
        assert Seq#Length(read($Heap, this, _module.Map.keys)) - j#2 < $decr$loop#00;
        assume true;
        assume true;
    }

    // ----- assignment statement ----- b8.dfy(348,9)
    assume true;
    assume true;
    idx#0 := LitInt(0 - 1);
    assume {:captureState "b8.dfy(348,13)"} true;
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

const unique field$isOpen: NameFamily;

const unique field$keys: NameFamily;

const unique field$values: NameFamily;

const unique field$stream: NameFamily;