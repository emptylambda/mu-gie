// Dafny 2.0.0.00922 technical preview 0
// Command Line Options: /compile:0 /noVerify /print:b4.bpl b4.dfy

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

const unique class._module.Map: ClassName;

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

axiom FDim(_module.Map.M) == 0
   && FieldOfDecl(class._module.Map, field$M) == _module.Map.M
   && $IsGhostField(_module.Map.M);

const _module.Map.M: Field (Map Box Box);

// Map.M: Allocation axiom
axiom (forall _module.Map$Key: Ty, _module.Map$Value: Ty, $h: Heap, $o: ref ::
  { read($h, $o, _module.Map.M), Tclass._module.Map(_module.Map$Key, _module.Map$Value) }
  $IsGoodHeap($h)
       && $o != null
       && dtype($o) == Tclass._module.Map(_module.Map$Key, _module.Map$Value)
     ==> $Is(read($h, $o, _module.Map.M), TMap(_module.Map$Key, _module.Map$Value))
       && (read($h, $o, alloc)
         ==> $IsAlloc(read($h, $o, _module.Map.M), TMap(_module.Map$Key, _module.Map$Value), $h)));

axiom FDim(_module.Map.Repr) == 0
   && FieldOfDecl(class._module.Map, field$Repr) == _module.Map.Repr
   && $IsGhostField(_module.Map.Repr);

const _module.Map.Repr: Field (Set Box);

// Map.Repr: Allocation axiom
axiom (forall _module.Map$Key: Ty, _module.Map$Value: Ty, $h: Heap, $o: ref ::
  { read($h, $o, _module.Map.Repr), Tclass._module.Map(_module.Map$Key, _module.Map$Value) }
  $IsGoodHeap($h)
       && $o != null
       && dtype($o) == Tclass._module.Map(_module.Map$Key, _module.Map$Value)
     ==> $Is(read($h, $o, _module.Map.Repr), TSet(Tclass._System.object()))
       && (read($h, $o, alloc)
         ==> $IsAlloc(read($h, $o, _module.Map.Repr), TSet(Tclass._System.object()), $h)));

axiom FDim(_module.Map.head) == 0
   && FieldOfDecl(class._module.Map, field$head) == _module.Map.head
   && !$IsGhostField(_module.Map.head);

const _module.Map.head: Field ref;

function Tclass._module.Node(Ty, Ty) : Ty;

// Tclass._module.Node Tag
axiom (forall _module.Node$Key: Ty, _module.Node$Value: Ty ::
  { Tclass._module.Node(_module.Node$Key, _module.Node$Value) }
  Tag(Tclass._module.Node(_module.Node$Key, _module.Node$Value))
     == Tagclass._module.Node);

const unique Tagclass._module.Node: TyTag;

// Tclass._module.Node injectivity 0
axiom (forall _module.Node$Key: Ty, _module.Node$Value: Ty ::
  { Tclass._module.Node(_module.Node$Key, _module.Node$Value) }
  Tclass._module.Node_0(Tclass._module.Node(_module.Node$Key, _module.Node$Value))
     == _module.Node$Key);

function Tclass._module.Node_0(Ty) : Ty;

// Tclass._module.Node injectivity 1
axiom (forall _module.Node$Key: Ty, _module.Node$Value: Ty ::
  { Tclass._module.Node(_module.Node$Key, _module.Node$Value) }
  Tclass._module.Node_1(Tclass._module.Node(_module.Node$Key, _module.Node$Value))
     == _module.Node$Value);

function Tclass._module.Node_1(Ty) : Ty;

// Box/unbox axiom for Tclass._module.Node
axiom (forall _module.Node$Key: Ty, _module.Node$Value: Ty, bx: Box ::
  { $IsBox(bx, Tclass._module.Node(_module.Node$Key, _module.Node$Value)) }
  $IsBox(bx, Tclass._module.Node(_module.Node$Key, _module.Node$Value))
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.Node(_module.Node$Key, _module.Node$Value)));

// Map.head: Allocation axiom
axiom (forall _module.Map$Key: Ty, _module.Map$Value: Ty, $h: Heap, $o: ref ::
  { read($h, $o, _module.Map.head), Tclass._module.Map(_module.Map$Key, _module.Map$Value) }
  $IsGoodHeap($h)
       && $o != null
       && dtype($o) == Tclass._module.Map(_module.Map$Key, _module.Map$Value)
     ==> $Is(read($h, $o, _module.Map.head),
        Tclass._module.Node(_module.Map$Key, _module.Map$Value))
       && (read($h, $o, alloc)
         ==> $IsAlloc(read($h, $o, _module.Map.head),
          Tclass._module.Node(_module.Map$Key, _module.Map$Value),
          $h)));

axiom FDim(_module.Map.Spine) == 0
   && FieldOfDecl(class._module.Map, field$Spine) == _module.Map.Spine
   && $IsGhostField(_module.Map.Spine);

const _module.Map.Spine: Field (Set Box);

// Map.Spine: Allocation axiom
axiom (forall _module.Map$Key: Ty, _module.Map$Value: Ty, $h: Heap, $o: ref ::
  { read($h, $o, _module.Map.Spine), Tclass._module.Map(_module.Map$Key, _module.Map$Value) }
  $IsGoodHeap($h)
       && $o != null
       && dtype($o) == Tclass._module.Map(_module.Map$Key, _module.Map$Value)
     ==> $Is(read($h, $o, _module.Map.Spine),
        TSet(Tclass._module.Node(_module.Map$Key, _module.Map$Value)))
       && (read($h, $o, alloc)
         ==> $IsAlloc(read($h, $o, _module.Map.Spine),
          TSet(Tclass._module.Node(_module.Map$Key, _module.Map$Value)),
          $h)));

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
      $o != null && ($o == this || read($h0, this, _module.Map.Repr)[$Box($o)])
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.Map.Valid(_module.Map$Key, _module.Map$Value, $h0, this)
       == _module.Map.Valid(_module.Map$Key, _module.Map$Value, $h1, this));

// consequence axiom for _module.Map.Valid
axiom 1 <= $FunctionContextHeight
   ==> (forall _module.Map$Key: Ty, _module.Map$Value: Ty, $Heap: Heap, this: ref ::
    { _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this) }
    _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
         || (1 != $FunctionContextHeight
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

axiom FDim(_module.Node.key) == 0
   && FieldOfDecl(class._module.Node, field$key) == _module.Node.key
   && !$IsGhostField(_module.Node.key);

axiom FDim(_module.Node.val) == 0
   && FieldOfDecl(class._module.Node, field$val) == _module.Node.val
   && !$IsGhostField(_module.Node.val);

axiom FDim(_module.Node.next) == 0
   && FieldOfDecl(class._module.Node, field$next) == _module.Node.next
   && !$IsGhostField(_module.Node.next);

// definition axiom for _module.Map.Valid(revealed)
axiom 1 <= $FunctionContextHeight
   ==> (forall _module.Map$Key: Ty, _module.Map$Value: Ty, $Heap: Heap, this: ref ::
    { _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this) }
    _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
         || (1 != $FunctionContextHeight
           &&
          $IsGoodHeap($Heap)
           &&
          this != null
           &&
          $Is(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value))
           && $IsAlloc(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value), $Heap))
       ==> (Set#Subset(read($Heap, this, _module.Map.Spine), read($Heap, this, _module.Map.Repr))
           ==> _module.Map.SpineValid#canCall(_module.Map$Key,
            _module.Map$Value,
            $Heap,
            read($Heap, this, _module.Map.Spine),
            read($Heap, this, _module.Map.head)))
         && (_module.Map.SpineValid#canCall(_module.Map$Key,
              _module.Map$Value,
              $Heap,
              read($Heap, this, _module.Map.Spine),
              read($Heap, this, _module.Map.head))
             && _module.Map.SpineValid(_module.Map$Key,
              _module.Map$Value,
              $LS($LZ),
              $Heap,
              read($Heap, this, _module.Map.Spine),
              read($Heap, this, _module.Map.head))
           ==> (forall k#0: Box ::
            { Map#Domain(read($Heap, this, _module.Map.M))[k#0] }
            $IsBox(k#0, _module.Map$Key)
               ==>
              Map#Domain(read($Heap, this, _module.Map.M))[k#0]
               ==> (forall n#0: ref ::
                { read($Heap, n#0, _module.Node.key) }
                  { read($Heap, this, _module.Map.Spine)[$Box(n#0)] }
                true)))
         && ((forall k#0: Box ::
              { Map#Domain(read($Heap, this, _module.Map.M))[k#0] }
              $IsBox(k#0, _module.Map$Key)
                 ==>
                Map#Domain(read($Heap, this, _module.Map.M))[k#0]
                 ==> (forall n#0: ref ::
                  { read($Heap, n#0, _module.Node.key) }
                    { read($Heap, this, _module.Map.Spine)[$Box(n#0)] }
                  true))
             && (forall k#0: Box ::
              { Map#Domain(read($Heap, this, _module.Map.M))[k#0] }
              $IsBox(k#0, _module.Map$Key)
                 ==>
                Map#Domain(read($Heap, this, _module.Map.M))[k#0]
                 ==> (exists n#0: ref ::
                  { read($Heap, n#0, _module.Node.key) }
                    { read($Heap, this, _module.Map.Spine)[$Box(n#0)] }
                  $Is(n#0, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
                     &&
                    read($Heap, this, _module.Map.Spine)[$Box(n#0)]
                     && read($Heap, n#0, _module.Node.key) == k#0))
           ==> (forall n#1: ref ::
            { read($Heap, n#1, _module.Node.val) }
              { read($Heap, n#1, _module.Node.key) }
              { read($Heap, this, _module.Map.Spine)[$Box(n#1)] }
            true))
         && ((forall n#1: ref ::
              { read($Heap, n#1, _module.Node.val) }
                { read($Heap, n#1, _module.Node.key) }
                { read($Heap, this, _module.Map.Spine)[$Box(n#1)] }
              true)
             && (forall n#1: ref ::
              { read($Heap, n#1, _module.Node.val) }
                { read($Heap, n#1, _module.Node.key) }
                { read($Heap, this, _module.Map.Spine)[$Box(n#1)] }
              $Is(n#1, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
                 ==> (read($Heap, this, _module.Map.Spine)[$Box(n#1)]
                     ==> Map#Domain(read($Heap, this, _module.Map.M))[read($Heap, n#1, _module.Node.key)])
                   && (read($Heap, this, _module.Map.Spine)[$Box(n#1)]
                     ==> read($Heap, n#1, _module.Node.val)
                       == Map#Elements(read($Heap, this, _module.Map.M))[read($Heap, n#1, _module.Node.key)]))
           ==> (forall n#2: ref, n'#0: ref ::
            { read($Heap, n'#0, _module.Node.key), read($Heap, n#2, _module.Node.key) }
              { read($Heap, n'#0, _module.Node.key), read($Heap, this, _module.Map.Spine)[$Box(n#2)] }
              { read($Heap, n#2, _module.Node.key), read($Heap, this, _module.Map.Spine)[$Box(n'#0)] }
              { read($Heap, this, _module.Map.Spine)[$Box(n'#0)], read($Heap, this, _module.Map.Spine)[$Box(n#2)] }
            true))
         && ((forall n#2: ref, n'#0: ref ::
              { read($Heap, n'#0, _module.Node.key), read($Heap, n#2, _module.Node.key) }
                { read($Heap, n'#0, _module.Node.key), read($Heap, this, _module.Map.Spine)[$Box(n#2)] }
                { read($Heap, n#2, _module.Node.key), read($Heap, this, _module.Map.Spine)[$Box(n'#0)] }
                { read($Heap, this, _module.Map.Spine)[$Box(n'#0)], read($Heap, this, _module.Map.Spine)[$Box(n#2)] }
              true)
             && (forall n#2: ref, n'#0: ref ::
              { read($Heap, n'#0, _module.Node.key), read($Heap, n#2, _module.Node.key) }
                { read($Heap, n'#0, _module.Node.key), read($Heap, this, _module.Map.Spine)[$Box(n#2)] }
                { read($Heap, n#2, _module.Node.key), read($Heap, this, _module.Map.Spine)[$Box(n'#0)] }
                { read($Heap, this, _module.Map.Spine)[$Box(n'#0)], read($Heap, this, _module.Map.Spine)[$Box(n#2)] }
              $Is(n#2, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
                   && $Is(n'#0, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
                 ==>
                read($Heap, this, _module.Map.Spine)[$Box(n#2)]
                   && read($Heap, this, _module.Map.Spine)[$Box(n'#0)]
                   && n#2 != n'#0
                 ==> read($Heap, n#2, _module.Node.key) != read($Heap, n'#0, _module.Node.key))
           ==> (forall n#3: ref ::
            { read($Heap, n#3, _module.Node.next) }
              { read($Heap, this, _module.Map.Spine)[$Box(n#3)] }
            true))
         && ((forall n#3: ref ::
              { read($Heap, n#3, _module.Node.next) }
                { read($Heap, this, _module.Map.Spine)[$Box(n#3)] }
              true)
             && (forall n#3: ref ::
              { read($Heap, n#3, _module.Node.next) }
                { read($Heap, this, _module.Map.Spine)[$Box(n#3)] }
              $Is(n#3, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
                 ==>
                read($Heap, this, _module.Map.Spine)[$Box(n#3)]
                 ==> read($Heap, n#3, _module.Node.next) != read($Heap, this, _module.Map.head))
           ==> (forall n#4: ref, n'#1: ref ::
            { read($Heap, n'#1, _module.Node.next), read($Heap, n#4, _module.Node.next) }
              { read($Heap, n'#1, _module.Node.next), read($Heap, this, _module.Map.Spine)[$Box(n#4)] }
              { read($Heap, n#4, _module.Node.next), read($Heap, this, _module.Map.Spine)[$Box(n'#1)] }
              { read($Heap, this, _module.Map.Spine)[$Box(n'#1)], read($Heap, this, _module.Map.Spine)[$Box(n#4)] }
            true))
         && _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
           == (
            read($Heap, this, _module.Map.Repr)[$Box(this)]
             && !read($Heap, this, _module.Map.Repr)[$Box(null)]
             && Set#Subset(read($Heap, this, _module.Map.Spine), read($Heap, this, _module.Map.Repr))
             && _module.Map.SpineValid(_module.Map$Key,
              _module.Map$Value,
              $LS($LZ),
              $Heap,
              read($Heap, this, _module.Map.Spine),
              read($Heap, this, _module.Map.head))
             && (forall k#0: Box ::
              { Map#Domain(read($Heap, this, _module.Map.M))[k#0] }
              $IsBox(k#0, _module.Map$Key)
                 ==>
                Map#Domain(read($Heap, this, _module.Map.M))[k#0]
                 ==> (exists n#0: ref ::
                  { read($Heap, n#0, _module.Node.key) }
                    { read($Heap, this, _module.Map.Spine)[$Box(n#0)] }
                  $Is(n#0, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
                     &&
                    read($Heap, this, _module.Map.Spine)[$Box(n#0)]
                     && read($Heap, n#0, _module.Node.key) == k#0))
             && (forall n#1: ref ::
              { read($Heap, n#1, _module.Node.val) }
                { read($Heap, n#1, _module.Node.key) }
                { read($Heap, this, _module.Map.Spine)[$Box(n#1)] }
              $Is(n#1, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
                 ==> (read($Heap, this, _module.Map.Spine)[$Box(n#1)]
                     ==> Map#Domain(read($Heap, this, _module.Map.M))[read($Heap, n#1, _module.Node.key)])
                   && (read($Heap, this, _module.Map.Spine)[$Box(n#1)]
                     ==> read($Heap, n#1, _module.Node.val)
                       == Map#Elements(read($Heap, this, _module.Map.M))[read($Heap, n#1, _module.Node.key)]))
             && (forall n#2: ref, n'#0: ref ::
              { read($Heap, n'#0, _module.Node.key), read($Heap, n#2, _module.Node.key) }
                { read($Heap, n'#0, _module.Node.key), read($Heap, this, _module.Map.Spine)[$Box(n#2)] }
                { read($Heap, n#2, _module.Node.key), read($Heap, this, _module.Map.Spine)[$Box(n'#0)] }
                { read($Heap, this, _module.Map.Spine)[$Box(n'#0)], read($Heap, this, _module.Map.Spine)[$Box(n#2)] }
              $Is(n#2, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
                   && $Is(n'#0, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
                 ==>
                read($Heap, this, _module.Map.Spine)[$Box(n#2)]
                   && read($Heap, this, _module.Map.Spine)[$Box(n'#0)]
                   && n#2 != n'#0
                 ==> read($Heap, n#2, _module.Node.key) != read($Heap, n'#0, _module.Node.key))
             && (forall n#3: ref ::
              { read($Heap, n#3, _module.Node.next) }
                { read($Heap, this, _module.Map.Spine)[$Box(n#3)] }
              $Is(n#3, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
                 ==>
                read($Heap, this, _module.Map.Spine)[$Box(n#3)]
                 ==> read($Heap, n#3, _module.Node.next) != read($Heap, this, _module.Map.head))
             && (forall n#4: ref, n'#1: ref ::
              { read($Heap, n'#1, _module.Node.next), read($Heap, n#4, _module.Node.next) }
                { read($Heap, n'#1, _module.Node.next), read($Heap, this, _module.Map.Spine)[$Box(n#4)] }
                { read($Heap, n#4, _module.Node.next), read($Heap, this, _module.Map.Spine)[$Box(n'#1)] }
                { read($Heap, this, _module.Map.Spine)[$Box(n'#1)], read($Heap, this, _module.Map.Spine)[$Box(n#4)] }
              $Is(n#4, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
                   && $Is(n'#1, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
                 ==>
                read($Heap, this, _module.Map.Spine)[$Box(n#4)]
                   && read($Heap, this, _module.Map.Spine)[$Box(n'#1)]
                   && read($Heap, n#4, _module.Node.next) == read($Heap, n'#1, _module.Node.next)
                 ==> n#4 == n'#1)));

procedure CheckWellformed$$_module.Map.Valid(_module.Map$Key: Ty,
    _module.Map$Value: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value))
         && $IsAlloc(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value), $Heap));
  free requires 1 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.Map.Valid(_module.Map$Key: Ty, _module.Map$Value: Ty, this: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;
  var ##spine#0: Set Box;
  var ##n#0: ref;
  var k#1: Box;
  var n#5: ref;
  var n#6: ref;
  var n#8: ref;
  var n'#2: ref;
  var n#10: ref;
  var n#12: ref;
  var n'#4: ref;
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
    assume {:captureState "b4.dfy(18,12): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc)
         ==> $o == this || read($Heap, this, _module.Map.Repr)[$Box($o)]);
    b$reqreads#0 := $_Frame[this, _module.Map.Repr];
    assert b$reqreads#0;
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
          $o != null && read($Heap, $o, alloc)
             ==> $o == this || read($Heap, this, _module.Map.Repr)[$Box($o)]);
        b$reqreads#1 := $_Frame[this, _module.Map.Repr];
        if (read($Heap, this, _module.Map.Repr)[$Box(this)])
        {
            b$reqreads#2 := $_Frame[this, _module.Map.Repr];
        }

        if (read($Heap, this, _module.Map.Repr)[$Box(this)]
           && !read($Heap, this, _module.Map.Repr)[$Box(null)])
        {
            b$reqreads#3 := $_Frame[this, _module.Map.Spine];
            b$reqreads#4 := $_Frame[this, _module.Map.Repr];
        }

        if (read($Heap, this, _module.Map.Repr)[$Box(this)]
           && !read($Heap, this, _module.Map.Repr)[$Box(null)]
           && Set#Subset(read($Heap, this, _module.Map.Spine), read($Heap, this, _module.Map.Repr)))
        {
            b$reqreads#5 := $_Frame[this, _module.Map.Spine];
            b$reqreads#6 := $_Frame[this, _module.Map.head];
            ##spine#0 := read($Heap, this, _module.Map.Spine);
            // assume allocatedness for argument to function
            assume $IsAlloc(##spine#0, TSet(Tclass._module.Node(_module.Map$Key, _module.Map$Value)), $Heap);
            ##n#0 := read($Heap, this, _module.Map.head);
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#0, Tclass._module.Node(_module.Map$Key, _module.Map$Value), $Heap);
            b$reqreads#7 := (forall<alpha> $o: ref, $f: Field alpha ::
              $o != null && read($Heap, $o, alloc) && ##spine#0[$Box($o)] ==> $_Frame[$o, $f]);
            assume _module.Map.SpineValid#canCall(_module.Map$Key,
              _module.Map$Value,
              $Heap,
              read($Heap, this, _module.Map.Spine),
              read($Heap, this, _module.Map.head));
        }

        if (read($Heap, this, _module.Map.Repr)[$Box(this)]
           && !read($Heap, this, _module.Map.Repr)[$Box(null)]
           && Set#Subset(read($Heap, this, _module.Map.Spine), read($Heap, this, _module.Map.Repr))
           && _module.Map.SpineValid(_module.Map$Key,
            _module.Map$Value,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.Map.Spine),
            read($Heap, this, _module.Map.head)))
        {
            havoc k#1;
            assume $IsBox(k#1, _module.Map$Key);
            // Begin Comprehension WF check
            b$reqreads#8 := $_Frame[this, _module.Map.M];
            if (Map#Domain(read($Heap, this, _module.Map.M))[k#1])
            {
                havoc n#5;
                assume $Is(n#5, Tclass._module.Node(_module.Map$Key, _module.Map$Value));
                // Begin Comprehension WF check
                b$reqreads#9 := $_Frame[this, _module.Map.Spine];
                if (read($Heap, this, _module.Map.Spine)[$Box(n#5)])
                {
                    assert n#5 != null;
                    b$reqreads#10 := $_Frame[n#5, _module.Node.key];
                }

                // End Comprehension WF check
            }

            // End Comprehension WF check
        }

        if (read($Heap, this, _module.Map.Repr)[$Box(this)]
           && !read($Heap, this, _module.Map.Repr)[$Box(null)]
           && Set#Subset(read($Heap, this, _module.Map.Spine), read($Heap, this, _module.Map.Repr))
           && _module.Map.SpineValid(_module.Map$Key,
            _module.Map$Value,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.Map.Spine),
            read($Heap, this, _module.Map.head))
           && (forall k#2: Box ::
            { Map#Domain(read($Heap, this, _module.Map.M))[k#2] }
            $IsBox(k#2, _module.Map$Key)
               ==>
              Map#Domain(read($Heap, this, _module.Map.M))[k#2]
               ==> (exists n#7: ref ::
                { read($Heap, n#7, _module.Node.key) }
                  { read($Heap, this, _module.Map.Spine)[$Box(n#7)] }
                $Is(n#7, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
                   &&
                  read($Heap, this, _module.Map.Spine)[$Box(n#7)]
                   && read($Heap, n#7, _module.Node.key) == k#2)))
        {
            havoc n#6;
            assume $Is(n#6, Tclass._module.Node(_module.Map$Key, _module.Map$Value));
            // Begin Comprehension WF check
            b$reqreads#11 := $_Frame[this, _module.Map.Spine];
            if (read($Heap, this, _module.Map.Spine)[$Box(n#6)])
            {
                assert n#6 != null;
                b$reqreads#12 := $_Frame[n#6, _module.Node.key];
                b$reqreads#13 := $_Frame[this, _module.Map.M];
                if (Map#Domain(read($Heap, this, _module.Map.M))[read($Heap, n#6, _module.Node.key)])
                {
                    assert n#6 != null;
                    b$reqreads#14 := $_Frame[n#6, _module.Node.val];
                    b$reqreads#15 := $_Frame[this, _module.Map.M];
                    assert n#6 != null;
                    b$reqreads#16 := $_Frame[n#6, _module.Node.key];
                    assert Map#Domain(read($Heap, this, _module.Map.M))[read($Heap, n#6, _module.Node.key)];
                }
            }

            // End Comprehension WF check
        }

        if (read($Heap, this, _module.Map.Repr)[$Box(this)]
           && !read($Heap, this, _module.Map.Repr)[$Box(null)]
           && Set#Subset(read($Heap, this, _module.Map.Spine), read($Heap, this, _module.Map.Repr))
           && _module.Map.SpineValid(_module.Map$Key,
            _module.Map$Value,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.Map.Spine),
            read($Heap, this, _module.Map.head))
           && (forall k#2: Box ::
            { Map#Domain(read($Heap, this, _module.Map.M))[k#2] }
            $IsBox(k#2, _module.Map$Key)
               ==>
              Map#Domain(read($Heap, this, _module.Map.M))[k#2]
               ==> (exists n#7: ref ::
                { read($Heap, n#7, _module.Node.key) }
                  { read($Heap, this, _module.Map.Spine)[$Box(n#7)] }
                $Is(n#7, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
                   &&
                  read($Heap, this, _module.Map.Spine)[$Box(n#7)]
                   && read($Heap, n#7, _module.Node.key) == k#2))
           && (forall n#9: ref ::
            { read($Heap, n#9, _module.Node.val) }
              { read($Heap, n#9, _module.Node.key) }
              { read($Heap, this, _module.Map.Spine)[$Box(n#9)] }
            $Is(n#9, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
               ==> (read($Heap, this, _module.Map.Spine)[$Box(n#9)]
                   ==> Map#Domain(read($Heap, this, _module.Map.M))[read($Heap, n#9, _module.Node.key)])
                 && (read($Heap, this, _module.Map.Spine)[$Box(n#9)]
                   ==> read($Heap, n#9, _module.Node.val)
                     == Map#Elements(read($Heap, this, _module.Map.M))[read($Heap, n#9, _module.Node.key)])))
        {
            havoc n#8;
            assume $Is(n#8, Tclass._module.Node(_module.Map$Key, _module.Map$Value));
            havoc n'#2;
            assume $Is(n'#2, Tclass._module.Node(_module.Map$Key, _module.Map$Value));
            // Begin Comprehension WF check
            b$reqreads#17 := $_Frame[this, _module.Map.Spine];
            if (read($Heap, this, _module.Map.Spine)[$Box(n#8)])
            {
                b$reqreads#18 := $_Frame[this, _module.Map.Spine];
            }

            if (read($Heap, this, _module.Map.Spine)[$Box(n#8)]
               && read($Heap, this, _module.Map.Spine)[$Box(n'#2)])
            {
            }

            if (read($Heap, this, _module.Map.Spine)[$Box(n#8)]
               && read($Heap, this, _module.Map.Spine)[$Box(n'#2)]
               && n#8 != n'#2)
            {
                assert n#8 != null;
                b$reqreads#19 := $_Frame[n#8, _module.Node.key];
                assert n'#2 != null;
                b$reqreads#20 := $_Frame[n'#2, _module.Node.key];
            }

            // End Comprehension WF check
        }

        if (read($Heap, this, _module.Map.Repr)[$Box(this)]
           && !read($Heap, this, _module.Map.Repr)[$Box(null)]
           && Set#Subset(read($Heap, this, _module.Map.Spine), read($Heap, this, _module.Map.Repr))
           && _module.Map.SpineValid(_module.Map$Key,
            _module.Map$Value,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.Map.Spine),
            read($Heap, this, _module.Map.head))
           && (forall k#2: Box ::
            { Map#Domain(read($Heap, this, _module.Map.M))[k#2] }
            $IsBox(k#2, _module.Map$Key)
               ==>
              Map#Domain(read($Heap, this, _module.Map.M))[k#2]
               ==> (exists n#7: ref ::
                { read($Heap, n#7, _module.Node.key) }
                  { read($Heap, this, _module.Map.Spine)[$Box(n#7)] }
                $Is(n#7, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
                   &&
                  read($Heap, this, _module.Map.Spine)[$Box(n#7)]
                   && read($Heap, n#7, _module.Node.key) == k#2))
           && (forall n#9: ref ::
            { read($Heap, n#9, _module.Node.val) }
              { read($Heap, n#9, _module.Node.key) }
              { read($Heap, this, _module.Map.Spine)[$Box(n#9)] }
            $Is(n#9, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
               ==> (read($Heap, this, _module.Map.Spine)[$Box(n#9)]
                   ==> Map#Domain(read($Heap, this, _module.Map.M))[read($Heap, n#9, _module.Node.key)])
                 && (read($Heap, this, _module.Map.Spine)[$Box(n#9)]
                   ==> read($Heap, n#9, _module.Node.val)
                     == Map#Elements(read($Heap, this, _module.Map.M))[read($Heap, n#9, _module.Node.key)]))
           && (forall n#11: ref, n'#3: ref ::
            { read($Heap, n'#3, _module.Node.key), read($Heap, n#11, _module.Node.key) }
              { read($Heap, n'#3, _module.Node.key), read($Heap, this, _module.Map.Spine)[$Box(n#11)] }
              { read($Heap, n#11, _module.Node.key), read($Heap, this, _module.Map.Spine)[$Box(n'#3)] }
              { read($Heap, this, _module.Map.Spine)[$Box(n'#3)], read($Heap, this, _module.Map.Spine)[$Box(n#11)] }
            $Is(n#11, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
                 && $Is(n'#3, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
               ==>
              read($Heap, this, _module.Map.Spine)[$Box(n#11)]
                 && read($Heap, this, _module.Map.Spine)[$Box(n'#3)]
                 && n#11 != n'#3
               ==> read($Heap, n#11, _module.Node.key) != read($Heap, n'#3, _module.Node.key)))
        {
            havoc n#10;
            assume $Is(n#10, Tclass._module.Node(_module.Map$Key, _module.Map$Value));
            // Begin Comprehension WF check
            b$reqreads#21 := $_Frame[this, _module.Map.Spine];
            if (read($Heap, this, _module.Map.Spine)[$Box(n#10)])
            {
                assert n#10 != null;
                b$reqreads#22 := $_Frame[n#10, _module.Node.next];
                b$reqreads#23 := $_Frame[this, _module.Map.head];
            }

            // End Comprehension WF check
        }

        if (read($Heap, this, _module.Map.Repr)[$Box(this)]
           && !read($Heap, this, _module.Map.Repr)[$Box(null)]
           && Set#Subset(read($Heap, this, _module.Map.Spine), read($Heap, this, _module.Map.Repr))
           && _module.Map.SpineValid(_module.Map$Key,
            _module.Map$Value,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.Map.Spine),
            read($Heap, this, _module.Map.head))
           && (forall k#2: Box ::
            { Map#Domain(read($Heap, this, _module.Map.M))[k#2] }
            $IsBox(k#2, _module.Map$Key)
               ==>
              Map#Domain(read($Heap, this, _module.Map.M))[k#2]
               ==> (exists n#7: ref ::
                { read($Heap, n#7, _module.Node.key) }
                  { read($Heap, this, _module.Map.Spine)[$Box(n#7)] }
                $Is(n#7, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
                   &&
                  read($Heap, this, _module.Map.Spine)[$Box(n#7)]
                   && read($Heap, n#7, _module.Node.key) == k#2))
           && (forall n#9: ref ::
            { read($Heap, n#9, _module.Node.val) }
              { read($Heap, n#9, _module.Node.key) }
              { read($Heap, this, _module.Map.Spine)[$Box(n#9)] }
            $Is(n#9, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
               ==> (read($Heap, this, _module.Map.Spine)[$Box(n#9)]
                   ==> Map#Domain(read($Heap, this, _module.Map.M))[read($Heap, n#9, _module.Node.key)])
                 && (read($Heap, this, _module.Map.Spine)[$Box(n#9)]
                   ==> read($Heap, n#9, _module.Node.val)
                     == Map#Elements(read($Heap, this, _module.Map.M))[read($Heap, n#9, _module.Node.key)]))
           && (forall n#11: ref, n'#3: ref ::
            { read($Heap, n'#3, _module.Node.key), read($Heap, n#11, _module.Node.key) }
              { read($Heap, n'#3, _module.Node.key), read($Heap, this, _module.Map.Spine)[$Box(n#11)] }
              { read($Heap, n#11, _module.Node.key), read($Heap, this, _module.Map.Spine)[$Box(n'#3)] }
              { read($Heap, this, _module.Map.Spine)[$Box(n'#3)], read($Heap, this, _module.Map.Spine)[$Box(n#11)] }
            $Is(n#11, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
                 && $Is(n'#3, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
               ==>
              read($Heap, this, _module.Map.Spine)[$Box(n#11)]
                 && read($Heap, this, _module.Map.Spine)[$Box(n'#3)]
                 && n#11 != n'#3
               ==> read($Heap, n#11, _module.Node.key) != read($Heap, n'#3, _module.Node.key))
           && (forall n#13: ref ::
            { read($Heap, n#13, _module.Node.next) }
              { read($Heap, this, _module.Map.Spine)[$Box(n#13)] }
            $Is(n#13, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
               ==>
              read($Heap, this, _module.Map.Spine)[$Box(n#13)]
               ==> read($Heap, n#13, _module.Node.next) != read($Heap, this, _module.Map.head)))
        {
            havoc n#12;
            assume $Is(n#12, Tclass._module.Node(_module.Map$Key, _module.Map$Value));
            havoc n'#4;
            assume $Is(n'#4, Tclass._module.Node(_module.Map$Key, _module.Map$Value));
            // Begin Comprehension WF check
            b$reqreads#24 := $_Frame[this, _module.Map.Spine];
            if (read($Heap, this, _module.Map.Spine)[$Box(n#12)])
            {
                b$reqreads#25 := $_Frame[this, _module.Map.Spine];
            }

            if (read($Heap, this, _module.Map.Spine)[$Box(n#12)]
               && read($Heap, this, _module.Map.Spine)[$Box(n'#4)])
            {
                assert n#12 != null;
                b$reqreads#26 := $_Frame[n#12, _module.Node.next];
                assert n'#4 != null;
                b$reqreads#27 := $_Frame[n'#4, _module.Node.next];
            }

            if (read($Heap, this, _module.Map.Spine)[$Box(n#12)]
               && read($Heap, this, _module.Map.Spine)[$Box(n'#4)]
               && read($Heap, n#12, _module.Node.next) == read($Heap, n'#4, _module.Node.next))
            {
            }

            // End Comprehension WF check
        }

        assume _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
           == (
            read($Heap, this, _module.Map.Repr)[$Box(this)]
             && !read($Heap, this, _module.Map.Repr)[$Box(null)]
             && Set#Subset(read($Heap, this, _module.Map.Spine), read($Heap, this, _module.Map.Repr))
             && _module.Map.SpineValid(_module.Map$Key,
              _module.Map$Value,
              $LS($LZ),
              $Heap,
              read($Heap, this, _module.Map.Spine),
              read($Heap, this, _module.Map.head))
             && (forall k#2: Box ::
              { Map#Domain(read($Heap, this, _module.Map.M))[k#2] }
              $IsBox(k#2, _module.Map$Key)
                 ==>
                Map#Domain(read($Heap, this, _module.Map.M))[k#2]
                 ==> (exists n#7: ref ::
                  { read($Heap, n#7, _module.Node.key) }
                    { read($Heap, this, _module.Map.Spine)[$Box(n#7)] }
                  $Is(n#7, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
                     &&
                    read($Heap, this, _module.Map.Spine)[$Box(n#7)]
                     && read($Heap, n#7, _module.Node.key) == k#2))
             && (forall n#9: ref ::
              { read($Heap, n#9, _module.Node.val) }
                { read($Heap, n#9, _module.Node.key) }
                { read($Heap, this, _module.Map.Spine)[$Box(n#9)] }
              $Is(n#9, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
                 ==> (read($Heap, this, _module.Map.Spine)[$Box(n#9)]
                     ==> Map#Domain(read($Heap, this, _module.Map.M))[read($Heap, n#9, _module.Node.key)])
                   && (read($Heap, this, _module.Map.Spine)[$Box(n#9)]
                     ==> read($Heap, n#9, _module.Node.val)
                       == Map#Elements(read($Heap, this, _module.Map.M))[read($Heap, n#9, _module.Node.key)]))
             && (forall n#11: ref, n'#3: ref ::
              { read($Heap, n'#3, _module.Node.key), read($Heap, n#11, _module.Node.key) }
                { read($Heap, n'#3, _module.Node.key), read($Heap, this, _module.Map.Spine)[$Box(n#11)] }
                { read($Heap, n#11, _module.Node.key), read($Heap, this, _module.Map.Spine)[$Box(n'#3)] }
                { read($Heap, this, _module.Map.Spine)[$Box(n'#3)], read($Heap, this, _module.Map.Spine)[$Box(n#11)] }
              $Is(n#11, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
                   && $Is(n'#3, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
                 ==>
                read($Heap, this, _module.Map.Spine)[$Box(n#11)]
                   && read($Heap, this, _module.Map.Spine)[$Box(n'#3)]
                   && n#11 != n'#3
                 ==> read($Heap, n#11, _module.Node.key) != read($Heap, n'#3, _module.Node.key))
             && (forall n#13: ref ::
              { read($Heap, n#13, _module.Node.next) }
                { read($Heap, this, _module.Map.Spine)[$Box(n#13)] }
              $Is(n#13, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
                 ==>
                read($Heap, this, _module.Map.Spine)[$Box(n#13)]
                 ==> read($Heap, n#13, _module.Node.next) != read($Heap, this, _module.Map.head))
             && (forall n#14: ref, n'#5: ref ::
              { read($Heap, n'#5, _module.Node.next), read($Heap, n#14, _module.Node.next) }
                { read($Heap, n'#5, _module.Node.next), read($Heap, this, _module.Map.Spine)[$Box(n#14)] }
                { read($Heap, n#14, _module.Node.next), read($Heap, this, _module.Map.Spine)[$Box(n'#5)] }
                { read($Heap, this, _module.Map.Spine)[$Box(n'#5)], read($Heap, this, _module.Map.Spine)[$Box(n#14)] }
              $Is(n#14, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
                   && $Is(n'#5, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
                 ==>
                read($Heap, this, _module.Map.Spine)[$Box(n#14)]
                   && read($Heap, this, _module.Map.Spine)[$Box(n'#5)]
                   && read($Heap, n#14, _module.Node.next) == read($Heap, n'#5, _module.Node.next)
                 ==> n#14 == n'#5));
        assume (Set#Subset(read($Heap, this, _module.Map.Spine), read($Heap, this, _module.Map.Repr))
             ==> _module.Map.SpineValid#canCall(_module.Map$Key,
              _module.Map$Value,
              $Heap,
              read($Heap, this, _module.Map.Spine),
              read($Heap, this, _module.Map.head)))
           && (_module.Map.SpineValid#canCall(_module.Map$Key,
                _module.Map$Value,
                $Heap,
                read($Heap, this, _module.Map.Spine),
                read($Heap, this, _module.Map.head))
               && _module.Map.SpineValid(_module.Map$Key,
                _module.Map$Value,
                $LS($LZ),
                $Heap,
                read($Heap, this, _module.Map.Spine),
                read($Heap, this, _module.Map.head))
             ==> (forall k#2: Box ::
              { Map#Domain(read($Heap, this, _module.Map.M))[k#2] }
              $IsBox(k#2, _module.Map$Key)
                 ==>
                Map#Domain(read($Heap, this, _module.Map.M))[k#2]
                 ==> (forall n#7: ref ::
                  { read($Heap, n#7, _module.Node.key) }
                    { read($Heap, this, _module.Map.Spine)[$Box(n#7)] }
                  true)))
           && ((forall k#2: Box ::
                { Map#Domain(read($Heap, this, _module.Map.M))[k#2] }
                $IsBox(k#2, _module.Map$Key)
                   ==>
                  Map#Domain(read($Heap, this, _module.Map.M))[k#2]
                   ==> (forall n#7: ref ::
                    { read($Heap, n#7, _module.Node.key) }
                      { read($Heap, this, _module.Map.Spine)[$Box(n#7)] }
                    true))
               && (forall k#2: Box ::
                { Map#Domain(read($Heap, this, _module.Map.M))[k#2] }
                $IsBox(k#2, _module.Map$Key)
                   ==>
                  Map#Domain(read($Heap, this, _module.Map.M))[k#2]
                   ==> (exists n#7: ref ::
                    { read($Heap, n#7, _module.Node.key) }
                      { read($Heap, this, _module.Map.Spine)[$Box(n#7)] }
                    $Is(n#7, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
                       &&
                      read($Heap, this, _module.Map.Spine)[$Box(n#7)]
                       && read($Heap, n#7, _module.Node.key) == k#2))
             ==> (forall n#9: ref ::
              { read($Heap, n#9, _module.Node.val) }
                { read($Heap, n#9, _module.Node.key) }
                { read($Heap, this, _module.Map.Spine)[$Box(n#9)] }
              true))
           && ((forall n#9: ref ::
                { read($Heap, n#9, _module.Node.val) }
                  { read($Heap, n#9, _module.Node.key) }
                  { read($Heap, this, _module.Map.Spine)[$Box(n#9)] }
                true)
               && (forall n#9: ref ::
                { read($Heap, n#9, _module.Node.val) }
                  { read($Heap, n#9, _module.Node.key) }
                  { read($Heap, this, _module.Map.Spine)[$Box(n#9)] }
                $Is(n#9, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
                   ==> (read($Heap, this, _module.Map.Spine)[$Box(n#9)]
                       ==> Map#Domain(read($Heap, this, _module.Map.M))[read($Heap, n#9, _module.Node.key)])
                     && (read($Heap, this, _module.Map.Spine)[$Box(n#9)]
                       ==> read($Heap, n#9, _module.Node.val)
                         == Map#Elements(read($Heap, this, _module.Map.M))[read($Heap, n#9, _module.Node.key)]))
             ==> (forall n#11: ref, n'#3: ref ::
              { read($Heap, n'#3, _module.Node.key), read($Heap, n#11, _module.Node.key) }
                { read($Heap, n'#3, _module.Node.key), read($Heap, this, _module.Map.Spine)[$Box(n#11)] }
                { read($Heap, n#11, _module.Node.key), read($Heap, this, _module.Map.Spine)[$Box(n'#3)] }
                { read($Heap, this, _module.Map.Spine)[$Box(n'#3)], read($Heap, this, _module.Map.Spine)[$Box(n#11)] }
              true))
           && ((forall n#11: ref, n'#3: ref ::
                { read($Heap, n'#3, _module.Node.key), read($Heap, n#11, _module.Node.key) }
                  { read($Heap, n'#3, _module.Node.key), read($Heap, this, _module.Map.Spine)[$Box(n#11)] }
                  { read($Heap, n#11, _module.Node.key), read($Heap, this, _module.Map.Spine)[$Box(n'#3)] }
                  { read($Heap, this, _module.Map.Spine)[$Box(n'#3)], read($Heap, this, _module.Map.Spine)[$Box(n#11)] }
                true)
               && (forall n#11: ref, n'#3: ref ::
                { read($Heap, n'#3, _module.Node.key), read($Heap, n#11, _module.Node.key) }
                  { read($Heap, n'#3, _module.Node.key), read($Heap, this, _module.Map.Spine)[$Box(n#11)] }
                  { read($Heap, n#11, _module.Node.key), read($Heap, this, _module.Map.Spine)[$Box(n'#3)] }
                  { read($Heap, this, _module.Map.Spine)[$Box(n'#3)], read($Heap, this, _module.Map.Spine)[$Box(n#11)] }
                $Is(n#11, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
                     && $Is(n'#3, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
                   ==>
                  read($Heap, this, _module.Map.Spine)[$Box(n#11)]
                     && read($Heap, this, _module.Map.Spine)[$Box(n'#3)]
                     && n#11 != n'#3
                   ==> read($Heap, n#11, _module.Node.key) != read($Heap, n'#3, _module.Node.key))
             ==> (forall n#13: ref ::
              { read($Heap, n#13, _module.Node.next) }
                { read($Heap, this, _module.Map.Spine)[$Box(n#13)] }
              true))
           && ((forall n#13: ref ::
                { read($Heap, n#13, _module.Node.next) }
                  { read($Heap, this, _module.Map.Spine)[$Box(n#13)] }
                true)
               && (forall n#13: ref ::
                { read($Heap, n#13, _module.Node.next) }
                  { read($Heap, this, _module.Map.Spine)[$Box(n#13)] }
                $Is(n#13, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
                   ==>
                  read($Heap, this, _module.Map.Spine)[$Box(n#13)]
                   ==> read($Heap, n#13, _module.Node.next) != read($Heap, this, _module.Map.head))
             ==> (forall n#14: ref, n'#5: ref ::
              { read($Heap, n'#5, _module.Node.next), read($Heap, n#14, _module.Node.next) }
                { read($Heap, n'#5, _module.Node.next), read($Heap, this, _module.Map.Spine)[$Box(n#14)] }
                { read($Heap, n#14, _module.Node.next), read($Heap, this, _module.Map.Spine)[$Box(n'#5)] }
                { read($Heap, this, _module.Map.Spine)[$Box(n'#5)], read($Heap, this, _module.Map.Spine)[$Box(n#14)] }
              true));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this), TBool);
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



// function declaration for _module.Map.SpineValid
function _module.Map.SpineValid(_module.Map$Key: Ty,
    _module.Map$Value: Ty,
    $ly: LayerType,
    $heap: Heap,
    spine#0: Set Box,
    n#0: ref)
   : bool;

function _module.Map.SpineValid#canCall(_module.Map$Key: Ty,
    _module.Map$Value: Ty,
    $heap: Heap,
    spine#0: Set Box,
    n#0: ref)
   : bool;

// layer synonym axiom
axiom (forall _module.Map$Key: Ty,
    _module.Map$Value: Ty,
    $ly: LayerType,
    $Heap: Heap,
    spine#0: Set Box,
    n#0: ref ::
  { _module.Map.SpineValid(_module.Map$Key, _module.Map$Value, $LS($ly), $Heap, spine#0, n#0) }
  _module.Map.SpineValid(_module.Map$Key, _module.Map$Value, $LS($ly), $Heap, spine#0, n#0)
     == _module.Map.SpineValid(_module.Map$Key, _module.Map$Value, $ly, $Heap, spine#0, n#0));

// fuel synonym axiom
axiom (forall _module.Map$Key: Ty,
    _module.Map$Value: Ty,
    $ly: LayerType,
    $Heap: Heap,
    spine#0: Set Box,
    n#0: ref ::
  { _module.Map.SpineValid(_module.Map$Key, _module.Map$Value, AsFuelBottom($ly), $Heap, spine#0, n#0) }
  _module.Map.SpineValid(_module.Map$Key, _module.Map$Value, $ly, $Heap, spine#0, n#0)
     == _module.Map.SpineValid(_module.Map$Key, _module.Map$Value, $LZ, $Heap, spine#0, n#0));

// frame axiom for _module.Map.SpineValid
axiom (forall _module.Map$Key: Ty,
    _module.Map$Value: Ty,
    $ly: LayerType,
    $h0: Heap,
    $h1: Heap,
    spine#0: Set Box,
    n#0: ref ::
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.Map.SpineValid(_module.Map$Key, _module.Map$Value, $ly, $h1, spine#0, n#0) }
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && (_module.Map.SpineValid#canCall(_module.Map$Key, _module.Map$Value, $h0, spine#0, n#0)
         || ($Is(spine#0, TSet(Tclass._module.Node(_module.Map$Key, _module.Map$Value)))
           && $Is(n#0, Tclass._module.Node(_module.Map$Key, _module.Map$Value))))
       &&
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==>
    (forall<alpha> $o: ref, $f: Field alpha ::
      $o != null && spine#0[$Box($o)] ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.Map.SpineValid(_module.Map$Key, _module.Map$Value, $ly, $h0, spine#0, n#0)
       == _module.Map.SpineValid(_module.Map$Key, _module.Map$Value, $ly, $h1, spine#0, n#0));

// consequence axiom for _module.Map.SpineValid
axiom 0 <= $FunctionContextHeight
   ==> (forall _module.Map$Key: Ty,
      _module.Map$Value: Ty,
      $ly: LayerType,
      $Heap: Heap,
      spine#0: Set Box,
      n#0: ref ::
    { _module.Map.SpineValid(_module.Map$Key, _module.Map$Value, $ly, $Heap, spine#0, n#0) }
    _module.Map.SpineValid#canCall(_module.Map$Key, _module.Map$Value, $Heap, spine#0, n#0)
         || (0 != $FunctionContextHeight
           &&
          $IsGoodHeap($Heap)
           && $Is(spine#0, TSet(Tclass._module.Node(_module.Map$Key, _module.Map$Value)))
           && $Is(n#0, Tclass._module.Node(_module.Map$Key, _module.Map$Value)))
       ==> true);

function _module.Map.SpineValid#requires(Ty, Ty, LayerType, Heap, Set Box, ref) : bool;

// #requires axiom for _module.Map.SpineValid
axiom (forall _module.Map$Key: Ty,
    _module.Map$Value: Ty,
    $ly: LayerType,
    $Heap: Heap,
    spine#0: Set Box,
    n#0: ref ::
  { _module.Map.SpineValid#requires(_module.Map$Key, _module.Map$Value, $ly, $Heap, spine#0, n#0) }
  $IsGoodHeap($Heap)
       && $Is(spine#0, TSet(Tclass._module.Node(_module.Map$Key, _module.Map$Value)))
       && $Is(n#0, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
     ==> _module.Map.SpineValid#requires(_module.Map$Key, _module.Map$Value, $ly, $Heap, spine#0, n#0)
       == true);

axiom FDim(_module.Node.Spine) == 0
   && FieldOfDecl(class._module.Node, field$Spine) == _module.Node.Spine
   && $IsGhostField(_module.Node.Spine);

// definition axiom for _module.Map.SpineValid(revealed)
axiom 0 <= $FunctionContextHeight
   ==> (forall _module.Map$Key: Ty,
      _module.Map$Value: Ty,
      $ly: LayerType,
      $Heap: Heap,
      spine#0: Set Box,
      n#0: ref ::
    { _module.Map.SpineValid(_module.Map$Key, _module.Map$Value, $LS($ly), $Heap, spine#0, n#0) }
    _module.Map.SpineValid#canCall(_module.Map$Key, _module.Map$Value, $Heap, spine#0, n#0)
         || (0 != $FunctionContextHeight
           &&
          $IsGoodHeap($Heap)
           && $Is(spine#0, TSet(Tclass._module.Node(_module.Map$Key, _module.Map$Value)))
           && $Is(n#0, Tclass._module.Node(_module.Map$Key, _module.Map$Value)))
       ==> (!Set#Equal(spine#0, Set#Empty(): Set Box)
           ==>
          Set#Equal(read($Heap, n#0, _module.Node.Spine),
            Set#Difference(spine#0, Set#UnionOne(Set#Empty(): Set Box, $Box(n#0))))
           ==> _module.Map.SpineValid#canCall(_module.Map$Key,
            _module.Map$Value,
            $Heap,
            read($Heap, n#0, _module.Node.Spine),
            read($Heap, n#0, _module.Node.next)))
         && _module.Map.SpineValid(_module.Map$Key, _module.Map$Value, $LS($ly), $Heap, spine#0, n#0)
           == ((n#0 == null && Set#Equal(spine#0, Set#Empty(): Set Box))
             || (
              n#0 != null
               && spine#0[$Box(n#0)]
               && Set#Equal(read($Heap, n#0, _module.Node.Spine),
                Set#Difference(spine#0, Set#UnionOne(Set#Empty(): Set Box, $Box(n#0))))
               && _module.Map.SpineValid(_module.Map$Key,
                _module.Map$Value,
                $ly,
                $Heap,
                read($Heap, n#0, _module.Node.Spine),
                read($Heap, n#0, _module.Node.next)))));

procedure CheckWellformed$$_module.Map.SpineValid(_module.Map$Key: Ty,
    _module.Map$Value: Ty,
    spine#0: Set Box
       where $Is(spine#0, TSet(Tclass._module.Node(_module.Map$Key, _module.Map$Value))),
    n#0: ref where $Is(n#0, Tclass._module.Node(_module.Map$Key, _module.Map$Value)));
  free requires 0 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.Map.SpineValid(_module.Map$Key: Ty, _module.Map$Value: Ty, spine#0: Set Box, n#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##spine#0: Set Box;
  var ##n#0: ref;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;
  var b$reqreads#2: bool;
  var b$reqreads#3: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;
    b$reqreads#2 := true;
    b$reqreads#3 := true;

    // AddWellformednessCheck for function SpineValid
    assume {:captureState "b4.dfy(29,19): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> spine#0[$Box($o)]);
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
          $o != null && read($Heap, $o, alloc) ==> spine#0[$Box($o)]);
        if (n#0 == null)
        {
        }

        if (!(n#0 == null && Set#Equal(spine#0, Set#Empty(): Set Box)))
        {
            if (n#0 != null)
            {
            }

            if (n#0 != null && spine#0[$Box(n#0)])
            {
                assert n#0 != null;
                b$reqreads#0 := $_Frame[n#0, _module.Node.Spine];
            }

            if (n#0 != null
               && spine#0[$Box(n#0)]
               && Set#Equal(read($Heap, n#0, _module.Node.Spine),
                Set#Difference(spine#0, Set#UnionOne(Set#Empty(): Set Box, $Box(n#0)))))
            {
                assert n#0 != null;
                b$reqreads#1 := $_Frame[n#0, _module.Node.Spine];
                assert n#0 != null;
                b$reqreads#2 := $_Frame[n#0, _module.Node.next];
                ##spine#0 := read($Heap, n#0, _module.Node.Spine);
                // assume allocatedness for argument to function
                assume $IsAlloc(##spine#0, TSet(Tclass._module.Node(_module.Map$Key, _module.Map$Value)), $Heap);
                ##n#0 := read($Heap, n#0, _module.Node.next);
                // assume allocatedness for argument to function
                assume $IsAlloc(##n#0, Tclass._module.Node(_module.Map$Key, _module.Map$Value), $Heap);
                b$reqreads#3 := (forall<alpha> $o: ref, $f: Field alpha ::
                  $o != null && read($Heap, $o, alloc) && ##spine#0[$Box($o)] ==> $_Frame[$o, $f]);
                assert (Set#Subset(##spine#0, spine#0) && !Set#Subset(spine#0, ##spine#0))
                   || (Set#Equal(##spine#0, spine#0)
                     && ((Set#Subset(##spine#0, spine#0) && !Set#Subset(spine#0, ##spine#0))
                       || (Set#Equal(##spine#0, spine#0) && ##n#0 == null && n#0 != null)));
                assume _module.Map.SpineValid#canCall(_module.Map$Key,
                  _module.Map$Value,
                  $Heap,
                  read($Heap, n#0, _module.Node.Spine),
                  read($Heap, n#0, _module.Node.next));
            }
        }

        assume _module.Map.SpineValid(_module.Map$Key, _module.Map$Value, $LS($LZ), $Heap, spine#0, n#0)
           == ((n#0 == null && Set#Equal(spine#0, Set#Empty(): Set Box))
             || (
              n#0 != null
               && spine#0[$Box(n#0)]
               && Set#Equal(read($Heap, n#0, _module.Node.Spine),
                Set#Difference(spine#0, Set#UnionOne(Set#Empty(): Set Box, $Box(n#0))))
               && _module.Map.SpineValid(_module.Map$Key,
                _module.Map$Value,
                $LS($LZ),
                $Heap,
                read($Heap, n#0, _module.Node.Spine),
                read($Heap, n#0, _module.Node.next))));
        assume !(n#0 == null && Set#Equal(spine#0, Set#Empty(): Set Box))
           ==>
          Set#Equal(read($Heap, n#0, _module.Node.Spine),
            Set#Difference(spine#0, Set#UnionOne(Set#Empty(): Set Box, $Box(n#0))))
           ==> _module.Map.SpineValid#canCall(_module.Map$Key,
            _module.Map$Value,
            $Heap,
            read($Heap, n#0, _module.Node.Spine),
            read($Heap, n#0, _module.Node.next));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.Map.SpineValid(_module.Map$Key, _module.Map$Value, $LS($LZ), $Heap, spine#0, n#0),
          TBool);
        assert b$reqreads#0;
        assert b$reqreads#1;
        assert b$reqreads#2;
        assert b$reqreads#3;
    }
}



// function declaration for _module.Map.SpineValid_One
function _module.Map.SpineValid__One(_module.Map$Key: Ty,
    _module.Map$Value: Ty,
    $heap: Heap,
    spine#0: Set Box,
    n#0: ref)
   : bool;

function _module.Map.SpineValid__One#canCall(_module.Map$Key: Ty,
    _module.Map$Value: Ty,
    $heap: Heap,
    spine#0: Set Box,
    n#0: ref)
   : bool;

// frame axiom for _module.Map.SpineValid__One
axiom (forall _module.Map$Key: Ty,
    _module.Map$Value: Ty,
    $h0: Heap,
    $h1: Heap,
    spine#0: Set Box,
    n#0: ref ::
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.Map.SpineValid__One(_module.Map$Key, _module.Map$Value, $h1, spine#0, n#0) }
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && (_module.Map.SpineValid__One#canCall(_module.Map$Key, _module.Map$Value, $h0, spine#0, n#0)
         || ($Is(spine#0, TSet(Tclass._module.Node(_module.Map$Key, _module.Map$Value)))
           && $Is(n#0, Tclass._module.Node(_module.Map$Key, _module.Map$Value))))
       &&
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==>
    (forall<alpha> $o: ref, $f: Field alpha ::
      $o != null && spine#0[$Box($o)] ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.Map.SpineValid__One(_module.Map$Key, _module.Map$Value, $h0, spine#0, n#0)
       == _module.Map.SpineValid__One(_module.Map$Key, _module.Map$Value, $h1, spine#0, n#0));

// consequence axiom for _module.Map.SpineValid__One
axiom 2 <= $FunctionContextHeight
   ==> (forall _module.Map$Key: Ty,
      _module.Map$Value: Ty,
      $Heap: Heap,
      spine#0: Set Box,
      n#0: ref ::
    { _module.Map.SpineValid__One(_module.Map$Key, _module.Map$Value, $Heap, spine#0, n#0) }
    _module.Map.SpineValid__One#canCall(_module.Map$Key, _module.Map$Value, $Heap, spine#0, n#0)
         || (2 != $FunctionContextHeight
           &&
          $IsGoodHeap($Heap)
           && $Is(spine#0, TSet(Tclass._module.Node(_module.Map$Key, _module.Map$Value)))
           && $Is(n#0, Tclass._module.Node(_module.Map$Key, _module.Map$Value)))
       ==> true);

function _module.Map.SpineValid__One#requires(Ty, Ty, Heap, Set Box, ref) : bool;

// #requires axiom for _module.Map.SpineValid__One
axiom (forall _module.Map$Key: Ty,
    _module.Map$Value: Ty,
    $Heap: Heap,
    spine#0: Set Box,
    n#0: ref ::
  { _module.Map.SpineValid__One#requires(_module.Map$Key, _module.Map$Value, $Heap, spine#0, n#0) }
  $IsGoodHeap($Heap)
       && $Is(spine#0, TSet(Tclass._module.Node(_module.Map$Key, _module.Map$Value)))
       && $Is(n#0, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
     ==> _module.Map.SpineValid__One#requires(_module.Map$Key, _module.Map$Value, $Heap, spine#0, n#0)
       == true);

// definition axiom for _module.Map.SpineValid__One(revealed)
axiom 2 <= $FunctionContextHeight
   ==> (forall _module.Map$Key: Ty,
      _module.Map$Value: Ty,
      $Heap: Heap,
      spine#0: Set Box,
      n#0: ref ::
    { _module.Map.SpineValid__One(_module.Map$Key, _module.Map$Value, $Heap, spine#0, n#0) }
    _module.Map.SpineValid__One#canCall(_module.Map$Key, _module.Map$Value, $Heap, spine#0, n#0)
         || (2 != $FunctionContextHeight
           &&
          $IsGoodHeap($Heap)
           && $Is(spine#0, TSet(Tclass._module.Node(_module.Map$Key, _module.Map$Value)))
           && $Is(n#0, Tclass._module.Node(_module.Map$Key, _module.Map$Value)))
       ==> _module.Map.SpineValid__One(_module.Map$Key, _module.Map$Value, $Heap, spine#0, n#0)
         == ((n#0 == null && Set#Equal(spine#0, Set#Empty(): Set Box))
           || (
            n#0 != null
             && spine#0[$Box(n#0)]
             && Set#Equal(read($Heap, n#0, _module.Node.Spine),
              Set#Difference(spine#0, Set#UnionOne(Set#Empty(): Set Box, $Box(n#0)))))));

procedure CheckWellformed$$_module.Map.SpineValid__One(_module.Map$Key: Ty,
    _module.Map$Value: Ty,
    spine#0: Set Box
       where $Is(spine#0, TSet(Tclass._module.Node(_module.Map$Key, _module.Map$Value))),
    n#0: ref where $Is(n#0, Tclass._module.Node(_module.Map$Key, _module.Map$Value)));
  free requires 2 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.Map.SpineValid__One(_module.Map$Key: Ty, _module.Map$Value: Ty, spine#0: Set Box, n#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function SpineValid_One
    assume {:captureState "b4.dfy(35,19): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> spine#0[$Box($o)]);
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
          $o != null && read($Heap, $o, alloc) ==> spine#0[$Box($o)]);
        if (n#0 == null)
        {
        }

        if (!(n#0 == null && Set#Equal(spine#0, Set#Empty(): Set Box)))
        {
            if (n#0 != null)
            {
            }

            if (n#0 != null && spine#0[$Box(n#0)])
            {
                assert n#0 != null;
                b$reqreads#0 := $_Frame[n#0, _module.Node.Spine];
            }
        }

        assume _module.Map.SpineValid__One(_module.Map$Key, _module.Map$Value, $Heap, spine#0, n#0)
           == ((n#0 == null && Set#Equal(spine#0, Set#Empty(): Set Box))
             || (
              n#0 != null
               && spine#0[$Box(n#0)]
               && Set#Equal(read($Heap, n#0, _module.Node.Spine),
                Set#Difference(spine#0, Set#UnionOne(Set#Empty(): Set Box, $Box(n#0))))));
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(_module.Map.SpineValid__One(_module.Map$Key, _module.Map$Value, $Heap, spine#0, n#0),
          TBool);
        assert b$reqreads#0;
    }
}



procedure {:_induction spine#0, p#0} CheckWellformed$$_module.Map.SpineValidSplit(_module.Map$Key: Ty,
    _module.Map$Value: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value))
         && $IsAlloc(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value), $Heap),
    spine#0: Set Box
       where $Is(spine#0, TSet(Tclass._module.Node(_module.Map$Key, _module.Map$Value)))
         && $IsAlloc(spine#0, TSet(Tclass._module.Node(_module.Map$Key, _module.Map$Value)), $Heap),
    p#0: ref
       where $Is(p#0, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
         && $IsAlloc(p#0, Tclass._module.Node(_module.Map$Key, _module.Map$Value), $Heap));
  free requires 3 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:_induction spine#0, p#0} CheckWellformed$$_module.Map.SpineValidSplit(_module.Map$Key: Ty,
    _module.Map$Value: Ty,
    this: ref,
    spine#0: Set Box,
    p#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##spine#0: Set Box;
  var ##n#0: ref;
  var ##spine#1: Set Box;
  var ##n#1: ref;
  var n#0: ref;
  var ##spine#2: Set Box;
  var ##n#2: ref;
  var n#2: ref;

    // AddMethodImpl: SpineValidSplit, CheckWellformed$$_module.Map.SpineValidSplit
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "b4.dfy(41,8): initial state"} true;
    assume !spine#0[$Box(null)];
    ##spine#0 := spine#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##spine#0, TSet(Tclass._module.Node(_module.Map$Key, _module.Map$Value)), $Heap);
    ##n#0 := p#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#0, Tclass._module.Node(_module.Map$Key, _module.Map$Value), $Heap);
    assume _module.Map.SpineValid#canCall(_module.Map$Key, _module.Map$Value, $Heap, spine#0, p#0);
    assume _module.Map.SpineValid(_module.Map$Key, _module.Map$Value, $LS($LZ), $Heap, spine#0, p#0);
    havoc $Heap;
    assume old($Heap) == $Heap;
    assume {:captureState "b4.dfy(44,26): post-state"} true;
    ##spine#1 := spine#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##spine#1, TSet(Tclass._module.Node(_module.Map$Key, _module.Map$Value)), $Heap);
    ##n#1 := p#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#1, Tclass._module.Node(_module.Map$Key, _module.Map$Value), $Heap);
    assume _module.Map.SpineValid__One#canCall(_module.Map$Key, _module.Map$Value, $Heap, spine#0, p#0);
    assume _module.Map.SpineValid__One(_module.Map$Key, _module.Map$Value, $Heap, spine#0, p#0);
    havoc n#0;
    assume $Is(n#0, Tclass._module.Node(_module.Map$Key, _module.Map$Value));
    if (*)
    {
        assume spine#0[$Box(n#0)];
        assert n#0 != null;
        assert n#0 != null;
        ##spine#2 := read($Heap, n#0, _module.Node.Spine);
        // assume allocatedness for argument to function
        assume $IsAlloc(##spine#2, TSet(Tclass._module.Node(_module.Map$Key, _module.Map$Value)), $Heap);
        ##n#2 := read($Heap, n#0, _module.Node.next);
        // assume allocatedness for argument to function
        assume $IsAlloc(##n#2, Tclass._module.Node(_module.Map$Key, _module.Map$Value), $Heap);
        assume _module.Map.SpineValid__One#canCall(_module.Map$Key,
          _module.Map$Value,
          $Heap,
          read($Heap, n#0, _module.Node.Spine),
          read($Heap, n#0, _module.Node.next));
        assume _module.Map.SpineValid__One(_module.Map$Key,
          _module.Map$Value,
          $Heap,
          read($Heap, n#0, _module.Node.Spine),
          read($Heap, n#0, _module.Node.next));
    }
    else
    {
        assume spine#0[$Box(n#0)]
           ==> _module.Map.SpineValid__One(_module.Map$Key,
            _module.Map$Value,
            $Heap,
            read($Heap, n#0, _module.Node.Spine),
            read($Heap, n#0, _module.Node.next));
    }

    assume (forall n#1: ref ::
      { read($Heap, n#1, _module.Node.next) }
        { read($Heap, n#1, _module.Node.Spine) }
        { spine#0[$Box(n#1)] }
      $Is(n#1, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
         ==>
        spine#0[$Box(n#1)]
         ==> _module.Map.SpineValid__One(_module.Map$Key,
          _module.Map$Value,
          $Heap,
          read($Heap, n#1, _module.Node.Spine),
          read($Heap, n#1, _module.Node.next)));
    havoc n#2;
    assume $Is(n#2, Tclass._module.Node(_module.Map$Key, _module.Map$Value));
    if (*)
    {
        assume spine#0[$Box(n#2)];
        if (*)
        {
            assert n#2 != null;
            assume read($Heap, n#2, _module.Node.next) == null;
        }
        else
        {
            assume read($Heap, n#2, _module.Node.next) != null;
            assert n#2 != null;
            assume spine#0[$Box(read($Heap, n#2, _module.Node.next))];
        }
    }
    else
    {
        assume spine#0[$Box(n#2)]
           ==> read($Heap, n#2, _module.Node.next) == null
             || spine#0[$Box(read($Heap, n#2, _module.Node.next))];
    }

    assume (forall n#3: ref ::
      { read($Heap, n#3, _module.Node.next) }
      $Is(n#3, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
         ==>
        spine#0[$Box(n#3)]
         ==> read($Heap, n#3, _module.Node.next) == null
           || spine#0[$Box(read($Heap, n#3, _module.Node.next))]);
}



procedure {:_induction spine#0, p#0} Call$$_module.Map.SpineValidSplit(_module.Map$Key: Ty,
    _module.Map$Value: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value))
         && $IsAlloc(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value), $Heap),
    spine#0: Set Box
       where $Is(spine#0, TSet(Tclass._module.Node(_module.Map$Key, _module.Map$Value)))
         && $IsAlloc(spine#0, TSet(Tclass._module.Node(_module.Map$Key, _module.Map$Value)), $Heap),
    p#0: ref
       where $Is(p#0, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
         && $IsAlloc(p#0, Tclass._module.Node(_module.Map$Key, _module.Map$Value), $Heap));
  // user-defined preconditions
  requires !spine#0[$Box(null)];
  requires _module.Map.SpineValid#canCall(_module.Map$Key, _module.Map$Value, $Heap, spine#0, p#0)
     ==> _module.Map.SpineValid(_module.Map$Key, _module.Map$Value, $LS($LZ), $Heap, spine#0, p#0)
       ||
      (p#0 == null && Set#Equal(spine#0, Set#Empty(): Set Box))
       || (
        p#0 != null
         && spine#0[$Box(p#0)]
         && Set#Equal(read($Heap, p#0, _module.Node.Spine),
          Set#Difference(spine#0, Set#UnionOne(Set#Empty(): Set Box, $Box(p#0))))
         && _module.Map.SpineValid(_module.Map$Key,
          _module.Map$Value,
          $LS($LS($LZ)),
          $Heap,
          read($Heap, p#0, _module.Node.Spine),
          read($Heap, p#0, _module.Node.next)));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.Map.SpineValid__One#canCall(_module.Map$Key, _module.Map$Value, $Heap, spine#0, p#0);
  free ensures _module.Map.SpineValid__One#canCall(_module.Map$Key, _module.Map$Value, $Heap, spine#0, p#0)
     &&
    _module.Map.SpineValid__One(_module.Map$Key, _module.Map$Value, $Heap, spine#0, p#0)
     && ((p#0 == null && Set#Equal(spine#0, Set#Empty(): Set Box))
       || (
        p#0 != null
         && spine#0[$Box(p#0)]
         && Set#Equal(read($Heap, p#0, _module.Node.Spine),
          Set#Difference(spine#0, Set#UnionOne(Set#Empty(): Set Box, $Box(p#0))))));
  free ensures (forall n#1: ref ::
    { read($Heap, n#1, _module.Node.next) }
      { read($Heap, n#1, _module.Node.Spine) }
      { spine#0[$Box(n#1)] }
    $Is(n#1, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
       ==>
      spine#0[$Box(n#1)]
       ==> _module.Map.SpineValid__One#canCall(_module.Map$Key,
        _module.Map$Value,
        $Heap,
        read($Heap, n#1, _module.Node.Spine),
        read($Heap, n#1, _module.Node.next)));
  ensures (forall n#1: ref ::
    { read($Heap, n#1, _module.Node.next) }
      { read($Heap, n#1, _module.Node.Spine) }
      { spine#0[$Box(n#1)] }
    $Is(n#1, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
       ==>
      spine#0[$Box(n#1)]
       ==> _module.Map.SpineValid__One(_module.Map$Key,
        _module.Map$Value,
        $Heap,
        read($Heap, n#1, _module.Node.Spine),
        read($Heap, n#1, _module.Node.next)));
  free ensures (forall n#3: ref :: { read($Heap, n#3, _module.Node.next) } true);
  ensures (forall n#3: ref ::
    { read($Heap, n#3, _module.Node.next) }
    $Is(n#3, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
       ==>
      spine#0[$Box(n#3)]
       ==> read($Heap, n#3, _module.Node.next) == null
         || spine#0[$Box(read($Heap, n#3, _module.Node.next))]);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction spine#0, p#0} Impl$$_module.Map.SpineValidSplit(_module.Map$Key: Ty,
    _module.Map$Value: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value))
         && $IsAlloc(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value), $Heap),
    spine#0: Set Box
       where $Is(spine#0, TSet(Tclass._module.Node(_module.Map$Key, _module.Map$Value)))
         && $IsAlloc(spine#0, TSet(Tclass._module.Node(_module.Map$Key, _module.Map$Value)), $Heap),
    p#0: ref
       where $Is(p#0, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
         && $IsAlloc(p#0, Tclass._module.Node(_module.Map$Key, _module.Map$Value), $Heap))
   returns ($_reverifyPost: bool);
  free requires 3 == $FunctionContextHeight;
  // user-defined preconditions
  requires !spine#0[$Box(null)];
  free requires _module.Map.SpineValid#canCall(_module.Map$Key, _module.Map$Value, $Heap, spine#0, p#0)
     &&
    _module.Map.SpineValid(_module.Map$Key, _module.Map$Value, $LS($LZ), $Heap, spine#0, p#0)
     && ((p#0 == null && Set#Equal(spine#0, Set#Empty(): Set Box))
       || (
        p#0 != null
         && spine#0[$Box(p#0)]
         && Set#Equal(read($Heap, p#0, _module.Node.Spine),
          Set#Difference(spine#0, Set#UnionOne(Set#Empty(): Set Box, $Box(p#0))))
         && _module.Map.SpineValid(_module.Map$Key,
          _module.Map$Value,
          $LS($LZ),
          $Heap,
          read($Heap, p#0, _module.Node.Spine),
          read($Heap, p#0, _module.Node.next))));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.Map.SpineValid__One#canCall(_module.Map$Key, _module.Map$Value, $Heap, spine#0, p#0);
  ensures _module.Map.SpineValid__One#canCall(_module.Map$Key, _module.Map$Value, $Heap, spine#0, p#0)
     ==> _module.Map.SpineValid__One(_module.Map$Key, _module.Map$Value, $Heap, spine#0, p#0)
       ||
      (p#0 == null && Set#Equal(spine#0, Set#Empty(): Set Box))
       || (
        p#0 != null
         && spine#0[$Box(p#0)]
         && Set#Equal(read($Heap, p#0, _module.Node.Spine),
          Set#Difference(spine#0, Set#UnionOne(Set#Empty(): Set Box, $Box(p#0)))));
  free ensures (forall n#1: ref ::
    { read($Heap, n#1, _module.Node.next) }
      { read($Heap, n#1, _module.Node.Spine) }
      { spine#0[$Box(n#1)] }
    $Is(n#1, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
       ==>
      spine#0[$Box(n#1)]
       ==> _module.Map.SpineValid__One#canCall(_module.Map$Key,
        _module.Map$Value,
        $Heap,
        read($Heap, n#1, _module.Node.Spine),
        read($Heap, n#1, _module.Node.next)));
  ensures (forall n#1: ref ::
    { read($Heap, n#1, _module.Node.next) }
      { read($Heap, n#1, _module.Node.Spine) }
      { spine#0[$Box(n#1)] }
    $Is(n#1, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
       ==>
      spine#0[$Box(n#1)]
       ==> _module.Map.SpineValid__One(_module.Map$Key,
        _module.Map$Value,
        $Heap,
        read($Heap, n#1, _module.Node.Spine),
        read($Heap, n#1, _module.Node.next)));
  free ensures (forall n#3: ref :: { read($Heap, n#3, _module.Node.next) } true);
  ensures (forall n#3: ref ::
    { read($Heap, n#3, _module.Node.next) }
    $Is(n#3, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
       ==>
      spine#0[$Box(n#3)]
       ==> read($Heap, n#3, _module.Node.next) == null
         || spine#0[$Box(read($Heap, n#3, _module.Node.next))]);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction spine#0, p#0} Impl$$_module.Map.SpineValidSplit(_module.Map$Key: Ty,
    _module.Map$Value: Ty,
    this: ref,
    spine#0: Set Box,
    p#0: ref)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;

    // AddMethodImpl: SpineValidSplit, Impl$$_module.Map.SpineValidSplit
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "b4.dfy(47,2): initial state"} true;
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#spine0#0: Set Box, $ih#p0#0: ref ::
      $Is($ih#spine0#0, TSet(Tclass._module.Node(_module.Map$Key, _module.Map$Value)))
           && $Is($ih#p0#0, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
           &&
          !$ih#spine0#0[$Box(null)]
           && _module.Map.SpineValid(_module.Map$Key,
            _module.Map$Value,
            $LS($LZ),
            $initHeapForallStmt#0,
            $ih#spine0#0,
            $ih#p0#0)
           && ((Set#Subset($ih#spine0#0, spine#0) && !Set#Subset(spine#0, $ih#spine0#0))
             || (Set#Equal($ih#spine0#0, spine#0) && $ih#p0#0 == null && p#0 != null))
         ==> _module.Map.SpineValid__One(_module.Map$Key, _module.Map$Value, $Heap, $ih#spine0#0, $ih#p0#0)
           && (forall n#4: ref ::
            { read($Heap, n#4, _module.Node.next) }
              { read($Heap, n#4, _module.Node.Spine) }
              { $ih#spine0#0[$Box(n#4)] }
            $Is(n#4, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
               ==>
              $ih#spine0#0[$Box(n#4)]
               ==> _module.Map.SpineValid__One(_module.Map$Key,
                _module.Map$Value,
                $Heap,
                read($Heap, n#4, _module.Node.Spine),
                read($Heap, n#4, _module.Node.next)))
           && (forall n#5: ref ::
            { read($Heap, n#5, _module.Node.next) }
            $Is(n#5, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
               ==>
              $ih#spine0#0[$Box(n#5)]
               ==> read($Heap, n#5, _module.Node.next) == null
                 || $ih#spine0#0[$Box(read($Heap, n#5, _module.Node.next))]));
    $_reverifyPost := false;
}



procedure {:_induction spine#0, p#0} CheckWellformed$$_module.Map.SpineValidCombine(_module.Map$Key: Ty,
    _module.Map$Value: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value))
         && $IsAlloc(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value), $Heap),
    spine#0: Set Box
       where $Is(spine#0, TSet(Tclass._module.Node(_module.Map$Key, _module.Map$Value)))
         && $IsAlloc(spine#0, TSet(Tclass._module.Node(_module.Map$Key, _module.Map$Value)), $Heap),
    p#0: ref
       where $Is(p#0, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
         && $IsAlloc(p#0, Tclass._module.Node(_module.Map$Key, _module.Map$Value), $Heap));
  free requires 4 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:_induction spine#0, p#0} CheckWellformed$$_module.Map.SpineValidCombine(_module.Map$Key: Ty,
    _module.Map$Value: Ty,
    this: ref,
    spine#0: Set Box,
    p#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##spine#0: Set Box;
  var ##n#0: ref;
  var n#0: ref;
  var ##spine#1: Set Box;
  var ##n#1: ref;
  var ##spine#2: Set Box;
  var ##n#2: ref;

    // AddMethodImpl: SpineValidCombine, CheckWellformed$$_module.Map.SpineValidCombine
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "b4.dfy(49,8): initial state"} true;
    assume !spine#0[$Box(null)];
    ##spine#0 := spine#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##spine#0, TSet(Tclass._module.Node(_module.Map$Key, _module.Map$Value)), $Heap);
    ##n#0 := p#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#0, Tclass._module.Node(_module.Map$Key, _module.Map$Value), $Heap);
    assume _module.Map.SpineValid__One#canCall(_module.Map$Key, _module.Map$Value, $Heap, spine#0, p#0);
    assume _module.Map.SpineValid__One(_module.Map$Key, _module.Map$Value, $Heap, spine#0, p#0);
    havoc n#0;
    assume $Is(n#0, Tclass._module.Node(_module.Map$Key, _module.Map$Value));
    if (*)
    {
        assume spine#0[$Box(n#0)];
        assert n#0 != null;
        assert n#0 != null;
        ##spine#1 := read($Heap, n#0, _module.Node.Spine);
        // assume allocatedness for argument to function
        assume $IsAlloc(##spine#1, TSet(Tclass._module.Node(_module.Map$Key, _module.Map$Value)), $Heap);
        ##n#1 := read($Heap, n#0, _module.Node.next);
        // assume allocatedness for argument to function
        assume $IsAlloc(##n#1, Tclass._module.Node(_module.Map$Key, _module.Map$Value), $Heap);
        assume _module.Map.SpineValid__One#canCall(_module.Map$Key,
          _module.Map$Value,
          $Heap,
          read($Heap, n#0, _module.Node.Spine),
          read($Heap, n#0, _module.Node.next));
        assume _module.Map.SpineValid__One(_module.Map$Key,
          _module.Map$Value,
          $Heap,
          read($Heap, n#0, _module.Node.Spine),
          read($Heap, n#0, _module.Node.next));
    }
    else
    {
        assume spine#0[$Box(n#0)]
           ==> _module.Map.SpineValid__One(_module.Map$Key,
            _module.Map$Value,
            $Heap,
            read($Heap, n#0, _module.Node.Spine),
            read($Heap, n#0, _module.Node.next));
    }

    assume (forall n#1: ref ::
      { read($Heap, n#1, _module.Node.next) }
        { read($Heap, n#1, _module.Node.Spine) }
        { spine#0[$Box(n#1)] }
      $Is(n#1, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
         ==>
        spine#0[$Box(n#1)]
         ==> _module.Map.SpineValid__One(_module.Map$Key,
          _module.Map$Value,
          $Heap,
          read($Heap, n#1, _module.Node.Spine),
          read($Heap, n#1, _module.Node.next)));
    havoc $Heap;
    assume old($Heap) == $Heap;
    assume {:captureState "b4.dfy(53,22): post-state"} true;
    ##spine#2 := spine#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##spine#2, TSet(Tclass._module.Node(_module.Map$Key, _module.Map$Value)), $Heap);
    ##n#2 := p#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#2, Tclass._module.Node(_module.Map$Key, _module.Map$Value), $Heap);
    assume _module.Map.SpineValid#canCall(_module.Map$Key, _module.Map$Value, $Heap, spine#0, p#0);
    assume _module.Map.SpineValid(_module.Map$Key, _module.Map$Value, $LS($LZ), $Heap, spine#0, p#0);
}



procedure {:_induction spine#0, p#0} Call$$_module.Map.SpineValidCombine(_module.Map$Key: Ty,
    _module.Map$Value: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value))
         && $IsAlloc(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value), $Heap),
    spine#0: Set Box
       where $Is(spine#0, TSet(Tclass._module.Node(_module.Map$Key, _module.Map$Value)))
         && $IsAlloc(spine#0, TSet(Tclass._module.Node(_module.Map$Key, _module.Map$Value)), $Heap),
    p#0: ref
       where $Is(p#0, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
         && $IsAlloc(p#0, Tclass._module.Node(_module.Map$Key, _module.Map$Value), $Heap));
  // user-defined preconditions
  requires !spine#0[$Box(null)];
  requires _module.Map.SpineValid__One#canCall(_module.Map$Key, _module.Map$Value, $Heap, spine#0, p#0)
     ==> _module.Map.SpineValid__One(_module.Map$Key, _module.Map$Value, $Heap, spine#0, p#0)
       ||
      (p#0 == null && Set#Equal(spine#0, Set#Empty(): Set Box))
       || (
        p#0 != null
         && spine#0[$Box(p#0)]
         && Set#Equal(read($Heap, p#0, _module.Node.Spine),
          Set#Difference(spine#0, Set#UnionOne(Set#Empty(): Set Box, $Box(p#0)))));
  requires (forall n#1: ref ::
    { read($Heap, n#1, _module.Node.next) }
      { read($Heap, n#1, _module.Node.Spine) }
      { spine#0[$Box(n#1)] }
    $Is(n#1, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
       ==>
      spine#0[$Box(n#1)]
       ==> _module.Map.SpineValid__One(_module.Map$Key,
        _module.Map$Value,
        $Heap,
        read($Heap, n#1, _module.Node.Spine),
        read($Heap, n#1, _module.Node.next)));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.Map.SpineValid#canCall(_module.Map$Key, _module.Map$Value, $Heap, spine#0, p#0);
  free ensures _module.Map.SpineValid#canCall(_module.Map$Key, _module.Map$Value, $Heap, spine#0, p#0)
     &&
    _module.Map.SpineValid(_module.Map$Key, _module.Map$Value, $LS($LZ), $Heap, spine#0, p#0)
     && ((p#0 == null && Set#Equal(spine#0, Set#Empty(): Set Box))
       || (
        p#0 != null
         && spine#0[$Box(p#0)]
         && Set#Equal(read($Heap, p#0, _module.Node.Spine),
          Set#Difference(spine#0, Set#UnionOne(Set#Empty(): Set Box, $Box(p#0))))
         && _module.Map.SpineValid(_module.Map$Key,
          _module.Map$Value,
          $LS($LZ),
          $Heap,
          read($Heap, p#0, _module.Node.Spine),
          read($Heap, p#0, _module.Node.next))));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction spine#0, p#0} Impl$$_module.Map.SpineValidCombine(_module.Map$Key: Ty,
    _module.Map$Value: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value))
         && $IsAlloc(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value), $Heap),
    spine#0: Set Box
       where $Is(spine#0, TSet(Tclass._module.Node(_module.Map$Key, _module.Map$Value)))
         && $IsAlloc(spine#0, TSet(Tclass._module.Node(_module.Map$Key, _module.Map$Value)), $Heap),
    p#0: ref
       where $Is(p#0, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
         && $IsAlloc(p#0, Tclass._module.Node(_module.Map$Key, _module.Map$Value), $Heap))
   returns ($_reverifyPost: bool);
  free requires 4 == $FunctionContextHeight;
  // user-defined preconditions
  requires !spine#0[$Box(null)];
  free requires _module.Map.SpineValid__One#canCall(_module.Map$Key, _module.Map$Value, $Heap, spine#0, p#0)
     &&
    _module.Map.SpineValid__One(_module.Map$Key, _module.Map$Value, $Heap, spine#0, p#0)
     && ((p#0 == null && Set#Equal(spine#0, Set#Empty(): Set Box))
       || (
        p#0 != null
         && spine#0[$Box(p#0)]
         && Set#Equal(read($Heap, p#0, _module.Node.Spine),
          Set#Difference(spine#0, Set#UnionOne(Set#Empty(): Set Box, $Box(p#0))))));
  requires (forall n#1: ref ::
    { read($Heap, n#1, _module.Node.next) }
      { read($Heap, n#1, _module.Node.Spine) }
      { spine#0[$Box(n#1)] }
    $Is(n#1, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
       ==>
      spine#0[$Box(n#1)]
       ==> _module.Map.SpineValid__One(_module.Map$Key,
        _module.Map$Value,
        $Heap,
        read($Heap, n#1, _module.Node.Spine),
        read($Heap, n#1, _module.Node.next)));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.Map.SpineValid#canCall(_module.Map$Key, _module.Map$Value, $Heap, spine#0, p#0);
  ensures _module.Map.SpineValid#canCall(_module.Map$Key, _module.Map$Value, $Heap, spine#0, p#0)
     ==> _module.Map.SpineValid(_module.Map$Key, _module.Map$Value, $LS($LZ), $Heap, spine#0, p#0)
       ||
      (p#0 == null && Set#Equal(spine#0, Set#Empty(): Set Box))
       || (
        p#0 != null
         && spine#0[$Box(p#0)]
         && Set#Equal(read($Heap, p#0, _module.Node.Spine),
          Set#Difference(spine#0, Set#UnionOne(Set#Empty(): Set Box, $Box(p#0))))
         && _module.Map.SpineValid(_module.Map$Key,
          _module.Map$Value,
          $LS($LS($LZ)),
          $Heap,
          read($Heap, p#0, _module.Node.Spine),
          read($Heap, p#0, _module.Node.next)));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction spine#0, p#0} Impl$$_module.Map.SpineValidCombine(_module.Map$Key: Ty,
    _module.Map$Value: Ty,
    this: ref,
    spine#0: Set Box,
    p#0: ref)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;

    // AddMethodImpl: SpineValidCombine, Impl$$_module.Map.SpineValidCombine
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "b4.dfy(54,2): initial state"} true;
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#spine0#0: Set Box, $ih#p0#0: ref ::
      $Is($ih#spine0#0, TSet(Tclass._module.Node(_module.Map$Key, _module.Map$Value)))
           && $Is($ih#p0#0, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
           &&
          !$ih#spine0#0[$Box(null)]
           && _module.Map.SpineValid__One(_module.Map$Key,
            _module.Map$Value,
            $initHeapForallStmt#0,
            $ih#spine0#0,
            $ih#p0#0)
           && (forall n#2: ref ::
            { read($initHeapForallStmt#0, n#2, _module.Node.next) }
              { read($initHeapForallStmt#0, n#2, _module.Node.Spine) }
              { $ih#spine0#0[$Box(n#2)] }
            $Is(n#2, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
               ==>
              $ih#spine0#0[$Box(n#2)]
               ==> _module.Map.SpineValid__One(_module.Map$Key,
                _module.Map$Value,
                $initHeapForallStmt#0,
                read($initHeapForallStmt#0, n#2, _module.Node.Spine),
                read($initHeapForallStmt#0, n#2, _module.Node.next)))
           && ((Set#Subset($ih#spine0#0, spine#0) && !Set#Subset(spine#0, $ih#spine0#0))
             || (Set#Equal($ih#spine0#0, spine#0) && $ih#p0#0 == null && p#0 != null))
         ==> _module.Map.SpineValid(_module.Map$Key, _module.Map$Value, $LS($LZ), $Heap, $ih#spine0#0, $ih#p0#0));
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.Map.Init(_module.Map$Key: Ty,
    _module.Map$Value: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value))
         && $IsAlloc(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value), $Heap));
  free requires 5 == $FunctionContextHeight;
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
    read($Heap, this, _module.Map.Repr)[$Box(this)]
     && !read($Heap, this, _module.Map.Repr)[$Box(null)]
     && Set#Subset(read($Heap, this, _module.Map.Spine), read($Heap, this, _module.Map.Repr))
     && _module.Map.SpineValid(_module.Map$Key,
      _module.Map$Value,
      $LS($LZ),
      $Heap,
      read($Heap, this, _module.Map.Spine),
      read($Heap, this, _module.Map.head))
     && (forall k#0: Box ::
      { Map#Domain(read($Heap, this, _module.Map.M))[k#0] }
      $IsBox(k#0, _module.Map$Key)
         ==>
        Map#Domain(read($Heap, this, _module.Map.M))[k#0]
         ==> (exists n#0: ref ::
          { read($Heap, n#0, _module.Node.key) }
            { read($Heap, this, _module.Map.Spine)[$Box(n#0)] }
          $Is(n#0, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
             &&
            read($Heap, this, _module.Map.Spine)[$Box(n#0)]
             && read($Heap, n#0, _module.Node.key) == k#0))
     && (forall n#1: ref ::
      { read($Heap, n#1, _module.Node.val) }
        { read($Heap, n#1, _module.Node.key) }
        { read($Heap, this, _module.Map.Spine)[$Box(n#1)] }
      $Is(n#1, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
         ==> (read($Heap, this, _module.Map.Spine)[$Box(n#1)]
             ==> Map#Domain(read($Heap, this, _module.Map.M))[read($Heap, n#1, _module.Node.key)])
           && (read($Heap, this, _module.Map.Spine)[$Box(n#1)]
             ==> read($Heap, n#1, _module.Node.val)
               == Map#Elements(read($Heap, this, _module.Map.M))[read($Heap, n#1, _module.Node.key)]))
     && (forall n#2: ref, n'#0: ref ::
      { read($Heap, n'#0, _module.Node.key), read($Heap, n#2, _module.Node.key) }
        { read($Heap, n'#0, _module.Node.key), read($Heap, this, _module.Map.Spine)[$Box(n#2)] }
        { read($Heap, n#2, _module.Node.key), read($Heap, this, _module.Map.Spine)[$Box(n'#0)] }
        { read($Heap, this, _module.Map.Spine)[$Box(n'#0)], read($Heap, this, _module.Map.Spine)[$Box(n#2)] }
      $Is(n#2, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
           && $Is(n'#0, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
         ==>
        read($Heap, this, _module.Map.Spine)[$Box(n#2)]
           && read($Heap, this, _module.Map.Spine)[$Box(n'#0)]
           && n#2 != n'#0
         ==> read($Heap, n#2, _module.Node.key) != read($Heap, n'#0, _module.Node.key))
     && (forall n#3: ref ::
      { read($Heap, n#3, _module.Node.next) }
        { read($Heap, this, _module.Map.Spine)[$Box(n#3)] }
      $Is(n#3, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
         ==>
        read($Heap, this, _module.Map.Spine)[$Box(n#3)]
         ==> read($Heap, n#3, _module.Node.next) != read($Heap, this, _module.Map.head))
     && (forall n#4: ref, n'#1: ref ::
      { read($Heap, n'#1, _module.Node.next), read($Heap, n#4, _module.Node.next) }
        { read($Heap, n'#1, _module.Node.next), read($Heap, this, _module.Map.Spine)[$Box(n#4)] }
        { read($Heap, n#4, _module.Node.next), read($Heap, this, _module.Map.Spine)[$Box(n'#1)] }
        { read($Heap, this, _module.Map.Spine)[$Box(n'#1)], read($Heap, this, _module.Map.Spine)[$Box(n#4)] }
      $Is(n#4, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
           && $Is(n'#1, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
         ==>
        read($Heap, this, _module.Map.Spine)[$Box(n#4)]
           && read($Heap, this, _module.Map.Spine)[$Box(n'#1)]
           && read($Heap, n#4, _module.Node.next) == read($Heap, n'#1, _module.Node.next)
         ==> n#4 == n'#1);
  ensures (forall $o: ref ::
    { read(old($Heap), $o, alloc) }
    read($Heap, this, _module.Map.Repr)[$Box($o)] && $o != this
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures true;
  ensures Map#Equal(read($Heap, this, _module.Map.M), Map#Empty(): Map Box Box);
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
  free requires 5 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this);
  ensures _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     ==> _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
       || read($Heap, this, _module.Map.Repr)[$Box(this)];
  ensures _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     ==> _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
       || !read($Heap, this, _module.Map.Repr)[$Box(null)];
  ensures _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     ==> _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
       || Set#Subset(read($Heap, this, _module.Map.Spine), read($Heap, this, _module.Map.Repr));
  ensures _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     ==> _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
       || (_module.Map.SpineValid#canCall(_module.Map$Key,
          _module.Map$Value,
          $Heap,
          read($Heap, this, _module.Map.Spine),
          read($Heap, this, _module.Map.head))
         ==> _module.Map.SpineValid(_module.Map$Key,
            _module.Map$Value,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.Map.Spine),
            read($Heap, this, _module.Map.head))
           ||
          (read($Heap, this, _module.Map.head) == null
             && Set#Equal(read($Heap, this, _module.Map.Spine), Set#Empty(): Set Box))
           || (
            read($Heap, this, _module.Map.head) != null
             && read($Heap, this, _module.Map.Spine)[$Box(read($Heap, this, _module.Map.head))]
             && Set#Equal(read($Heap, read($Heap, this, _module.Map.head), _module.Node.Spine),
              Set#Difference(read($Heap, this, _module.Map.Spine),
                Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Map.head)))))
             && _module.Map.SpineValid(_module.Map$Key,
              _module.Map$Value,
              $LS($LS($LZ)),
              $Heap,
              read($Heap, read($Heap, this, _module.Map.head), _module.Node.Spine),
              read($Heap, read($Heap, this, _module.Map.head), _module.Node.next))));
  ensures _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     ==> _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
       || (forall k#1: Box ::
        { Map#Domain(read($Heap, this, _module.Map.M))[k#1] }
        $IsBox(k#1, _module.Map$Key)
           ==>
          Map#Domain(read($Heap, this, _module.Map.M))[k#1]
           ==> (exists n#5: ref ::
            { read($Heap, n#5, _module.Node.key) }
              { read($Heap, this, _module.Map.Spine)[$Box(n#5)] }
            $Is(n#5, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
               &&
              read($Heap, this, _module.Map.Spine)[$Box(n#5)]
               && read($Heap, n#5, _module.Node.key) == k#1));
  ensures _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     ==> _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
       || (forall n#6: ref ::
        { read($Heap, n#6, _module.Node.val) }
          { read($Heap, n#6, _module.Node.key) }
          { read($Heap, this, _module.Map.Spine)[$Box(n#6)] }
        $Is(n#6, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
           ==> (read($Heap, this, _module.Map.Spine)[$Box(n#6)]
               ==> Map#Domain(read($Heap, this, _module.Map.M))[read($Heap, n#6, _module.Node.key)])
             && (read($Heap, this, _module.Map.Spine)[$Box(n#6)]
               ==> read($Heap, n#6, _module.Node.val)
                 == Map#Elements(read($Heap, this, _module.Map.M))[read($Heap, n#6, _module.Node.key)]));
  ensures _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     ==> _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
       || (forall n#7: ref, n'#2: ref ::
        { read($Heap, n'#2, _module.Node.key), read($Heap, n#7, _module.Node.key) }
          { read($Heap, n'#2, _module.Node.key), read($Heap, this, _module.Map.Spine)[$Box(n#7)] }
          { read($Heap, n#7, _module.Node.key), read($Heap, this, _module.Map.Spine)[$Box(n'#2)] }
          { read($Heap, this, _module.Map.Spine)[$Box(n'#2)], read($Heap, this, _module.Map.Spine)[$Box(n#7)] }
        $Is(n#7, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
             && $Is(n'#2, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
           ==>
          read($Heap, this, _module.Map.Spine)[$Box(n#7)]
             && read($Heap, this, _module.Map.Spine)[$Box(n'#2)]
             && n#7 != n'#2
           ==> read($Heap, n#7, _module.Node.key) != read($Heap, n'#2, _module.Node.key));
  ensures _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     ==> _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
       || (forall n#8: ref ::
        { read($Heap, n#8, _module.Node.next) }
          { read($Heap, this, _module.Map.Spine)[$Box(n#8)] }
        $Is(n#8, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
           ==>
          read($Heap, this, _module.Map.Spine)[$Box(n#8)]
           ==> read($Heap, n#8, _module.Node.next) != read($Heap, this, _module.Map.head));
  ensures _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     ==> _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
       || (forall n#9: ref, n'#3: ref ::
        { read($Heap, n'#3, _module.Node.next), read($Heap, n#9, _module.Node.next) }
          { read($Heap, n'#3, _module.Node.next), read($Heap, this, _module.Map.Spine)[$Box(n#9)] }
          { read($Heap, n#9, _module.Node.next), read($Heap, this, _module.Map.Spine)[$Box(n'#3)] }
          { read($Heap, this, _module.Map.Spine)[$Box(n'#3)], read($Heap, this, _module.Map.Spine)[$Box(n#9)] }
        $Is(n#9, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
             && $Is(n'#3, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
           ==>
          read($Heap, this, _module.Map.Spine)[$Box(n#9)]
             && read($Heap, this, _module.Map.Spine)[$Box(n'#3)]
             && read($Heap, n#9, _module.Node.next) == read($Heap, n'#3, _module.Node.next)
           ==> n#9 == n'#3);
  ensures (forall $o: ref ::
    { read(old($Heap), $o, alloc) }
    read($Heap, this, _module.Map.Repr)[$Box($o)] && $o != this
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures true;
  ensures Map#Equal(read($Heap, this, _module.Map.M), Map#Empty(): Map Box Box);
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
  var $obj0: ref;
  var $obj1: ref;
  var $rhs#0: ref
     where $Is($rhs#0, Tclass._module.Node(_module.Map$Key, _module.Map$Value));
  var $rhs#1: Set Box
     where $Is($rhs#1, TSet(Tclass._module.Node(_module.Map$Key, _module.Map$Value)));
  var $rhs#2: Map Box Box where $Is($rhs#2, TMap(_module.Map$Key, _module.Map$Value));
  var $rhs#3: Set Box where $Is($rhs#3, TSet(Tclass._System.object()));

    // AddMethodImpl: Init, Impl$$_module.Map.Init
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> $o == this);
    assume {:captureState "b4.dfy(62,2): initial state"} true;
    $_reverifyPost := false;
    // ----- update statement ----- b4.dfy(63,17)
    assume true;
    $obj0 := this;
    assert $_Frame[$obj0, _module.Map.head];
    assume true;
    $obj1 := this;
    assert $_Frame[$obj1, _module.Map.Spine];
    assume true;
    $rhs#0 := null;
    assume true;
    $rhs#1 := Lit(Set#Empty(): Set Box);
    $Heap := update($Heap, $obj0, _module.Map.head, $rhs#0);
    assume $IsGoodHeap($Heap);
    $Heap := update($Heap, $obj1, _module.Map.Spine, $rhs#1);
    assume $IsGoodHeap($Heap);
    assume {:captureState "b4.dfy(63,27)"} true;
    // ----- update statement ----- b4.dfy(64,13)
    assume true;
    $obj0 := this;
    assert $_Frame[$obj0, _module.Map.M];
    assume true;
    $obj1 := this;
    assert $_Frame[$obj1, _module.Map.Repr];
    assume true;
    $rhs#2 := Lit(Map#Empty(): Map Box Box);
    assume true;
    $rhs#3 := Set#UnionOne(Set#Empty(): Set Box, $Box(this));
    $Heap := update($Heap, $obj0, _module.Map.M, $rhs#2);
    assume $IsGoodHeap($Heap);
    $Heap := update($Heap, $obj1, _module.Map.Repr, $rhs#3);
    assume $IsGoodHeap($Heap);
    assume {:captureState "b4.dfy(64,28)"} true;
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
   returns (prev#0: ref
       where $Is(prev#0, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
         && $IsAlloc(prev#0, Tclass._module.Node(_module.Map$Key, _module.Map$Value), $Heap),
    p#0: ref
       where $Is(p#0, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
         && $IsAlloc(p#0, Tclass._module.Node(_module.Map$Key, _module.Map$Value), $Heap));
  free requires 6 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.Map.FindIndex(_module.Map$Key: Ty, _module.Map$Value: Ty, this: ref, key#0: Box)
   returns (prev#0: ref, p#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: FindIndex, CheckWellformed$$_module.Map.FindIndex
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "b4.dfy(67,21): initial state"} true;
    assume _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this);
    assume _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this);
    havoc $Heap;
    assume (forall<alpha> $o: ref, $f: Field alpha ::
      { read($Heap, $o, $f) }
      $o != null && read(old($Heap), $o, alloc)
         ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
    assume $HeapSucc(old($Heap), $Heap);
    havoc prev#0, p#0;
    assume {:captureState "b4.dfy(69,22): post-state"} true;
    if (*)
    {
        assume p#0 == null;
        assume !Map#Domain(read($Heap, this, _module.Map.M))[key#0];
    }
    else
    {
        assume p#0 == null ==> !Map#Domain(read($Heap, this, _module.Map.M))[key#0];
    }

    if (*)
    {
        assume p#0 != null;
        assume Map#Domain(read($Heap, this, _module.Map.M))[key#0];
        assume read($Heap, this, _module.Map.Spine)[$Box(p#0)];
        assert p#0 != null;
        assume read($Heap, p#0, _module.Node.key) == key#0;
        if (p#0 == read($Heap, this, _module.Map.head))
        {
        }

        assume p#0 == read($Heap, this, _module.Map.head) ==> prev#0 == null;
        if (p#0 != read($Heap, this, _module.Map.head))
        {
            if (read($Heap, this, _module.Map.Spine)[$Box(prev#0)])
            {
                assert prev#0 != null;
            }
        }

        assume p#0 != read($Heap, this, _module.Map.head)
           ==> read($Heap, this, _module.Map.Spine)[$Box(prev#0)]
             && read($Heap, prev#0, _module.Node.next) == p#0;
    }
    else
    {
        assume p#0 != null
           ==> Map#Domain(read($Heap, this, _module.Map.M))[key#0]
             && read($Heap, this, _module.Map.Spine)[$Box(p#0)]
             && read($Heap, p#0, _module.Node.key) == key#0
             && (p#0 == read($Heap, this, _module.Map.head) ==> prev#0 == null)
             && (p#0 != read($Heap, this, _module.Map.head)
               ==> read($Heap, this, _module.Map.Spine)[$Box(prev#0)]
                 && read($Heap, prev#0, _module.Node.next) == p#0);
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
   returns (prev#0: ref
       where $Is(prev#0, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
         && $IsAlloc(prev#0, Tclass._module.Node(_module.Map$Key, _module.Map$Value), $Heap),
    p#0: ref
       where $Is(p#0, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
         && $IsAlloc(p#0, Tclass._module.Node(_module.Map$Key, _module.Map$Value), $Heap));
  // user-defined preconditions
  requires _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     ==> _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
       || read($Heap, this, _module.Map.Repr)[$Box(this)];
  requires _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     ==> _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
       || !read($Heap, this, _module.Map.Repr)[$Box(null)];
  requires _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     ==> _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
       || Set#Subset(read($Heap, this, _module.Map.Spine), read($Heap, this, _module.Map.Repr));
  requires _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     ==> _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
       || (_module.Map.SpineValid#canCall(_module.Map$Key,
          _module.Map$Value,
          $Heap,
          read($Heap, this, _module.Map.Spine),
          read($Heap, this, _module.Map.head))
         ==> _module.Map.SpineValid(_module.Map$Key,
            _module.Map$Value,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.Map.Spine),
            read($Heap, this, _module.Map.head))
           ||
          (read($Heap, this, _module.Map.head) == null
             && Set#Equal(read($Heap, this, _module.Map.Spine), Set#Empty(): Set Box))
           || (
            read($Heap, this, _module.Map.head) != null
             && read($Heap, this, _module.Map.Spine)[$Box(read($Heap, this, _module.Map.head))]
             && Set#Equal(read($Heap, read($Heap, this, _module.Map.head), _module.Node.Spine),
              Set#Difference(read($Heap, this, _module.Map.Spine),
                Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Map.head)))))
             && _module.Map.SpineValid(_module.Map$Key,
              _module.Map$Value,
              $LS($LS($LZ)),
              $Heap,
              read($Heap, read($Heap, this, _module.Map.head), _module.Node.Spine),
              read($Heap, read($Heap, this, _module.Map.head), _module.Node.next))));
  requires _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     ==> _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
       || (forall k#0: Box ::
        { Map#Domain(read($Heap, this, _module.Map.M))[k#0] }
        $IsBox(k#0, _module.Map$Key)
           ==>
          Map#Domain(read($Heap, this, _module.Map.M))[k#0]
           ==> (exists n#0: ref ::
            { read($Heap, n#0, _module.Node.key) }
              { read($Heap, this, _module.Map.Spine)[$Box(n#0)] }
            $Is(n#0, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
               &&
              read($Heap, this, _module.Map.Spine)[$Box(n#0)]
               && read($Heap, n#0, _module.Node.key) == k#0));
  requires _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     ==> _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
       || (forall n#1: ref ::
        { read($Heap, n#1, _module.Node.val) }
          { read($Heap, n#1, _module.Node.key) }
          { read($Heap, this, _module.Map.Spine)[$Box(n#1)] }
        $Is(n#1, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
           ==> (read($Heap, this, _module.Map.Spine)[$Box(n#1)]
               ==> Map#Domain(read($Heap, this, _module.Map.M))[read($Heap, n#1, _module.Node.key)])
             && (read($Heap, this, _module.Map.Spine)[$Box(n#1)]
               ==> read($Heap, n#1, _module.Node.val)
                 == Map#Elements(read($Heap, this, _module.Map.M))[read($Heap, n#1, _module.Node.key)]));
  requires _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     ==> _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
       || (forall n#2: ref, n'#0: ref ::
        { read($Heap, n'#0, _module.Node.key), read($Heap, n#2, _module.Node.key) }
          { read($Heap, n'#0, _module.Node.key), read($Heap, this, _module.Map.Spine)[$Box(n#2)] }
          { read($Heap, n#2, _module.Node.key), read($Heap, this, _module.Map.Spine)[$Box(n'#0)] }
          { read($Heap, this, _module.Map.Spine)[$Box(n'#0)], read($Heap, this, _module.Map.Spine)[$Box(n#2)] }
        $Is(n#2, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
             && $Is(n'#0, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
           ==>
          read($Heap, this, _module.Map.Spine)[$Box(n#2)]
             && read($Heap, this, _module.Map.Spine)[$Box(n'#0)]
             && n#2 != n'#0
           ==> read($Heap, n#2, _module.Node.key) != read($Heap, n'#0, _module.Node.key));
  requires _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     ==> _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
       || (forall n#3: ref ::
        { read($Heap, n#3, _module.Node.next) }
          { read($Heap, this, _module.Map.Spine)[$Box(n#3)] }
        $Is(n#3, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
           ==>
          read($Heap, this, _module.Map.Spine)[$Box(n#3)]
           ==> read($Heap, n#3, _module.Node.next) != read($Heap, this, _module.Map.head));
  requires _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     ==> _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
       || (forall n#4: ref, n'#1: ref ::
        { read($Heap, n'#1, _module.Node.next), read($Heap, n#4, _module.Node.next) }
          { read($Heap, n'#1, _module.Node.next), read($Heap, this, _module.Map.Spine)[$Box(n#4)] }
          { read($Heap, n#4, _module.Node.next), read($Heap, this, _module.Map.Spine)[$Box(n'#1)] }
          { read($Heap, this, _module.Map.Spine)[$Box(n'#1)], read($Heap, this, _module.Map.Spine)[$Box(n#4)] }
        $Is(n#4, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
             && $Is(n'#1, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
           ==>
          read($Heap, this, _module.Map.Spine)[$Box(n#4)]
             && read($Heap, this, _module.Map.Spine)[$Box(n'#1)]
             && read($Heap, n#4, _module.Node.next) == read($Heap, n'#1, _module.Node.next)
           ==> n#4 == n'#1);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures p#0 == null ==> !Map#Domain(read($Heap, this, _module.Map.M))[key#0];
  free ensures true;
  ensures p#0 != null ==> Map#Domain(read($Heap, this, _module.Map.M))[key#0];
  ensures p#0 != null ==> read($Heap, this, _module.Map.Spine)[$Box(p#0)];
  ensures p#0 != null ==> read($Heap, p#0, _module.Node.key) == key#0;
  ensures p#0 != null ==> p#0 == read($Heap, this, _module.Map.head) ==> prev#0 == null;
  ensures p#0 != null
     ==>
    p#0 != read($Heap, this, _module.Map.head)
     ==> read($Heap, this, _module.Map.Spine)[$Box(prev#0)];
  ensures p#0 != null
     ==>
    p#0 != read($Heap, this, _module.Map.head)
     ==> read($Heap, prev#0, _module.Node.next) == p#0;
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
   returns (prev#0: ref
       where $Is(prev#0, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
         && $IsAlloc(prev#0, Tclass._module.Node(_module.Map$Key, _module.Map$Value), $Heap),
    p#0: ref
       where $Is(p#0, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
         && $IsAlloc(p#0, Tclass._module.Node(_module.Map$Key, _module.Map$Value), $Heap),
    $_reverifyPost: bool);
  free requires 6 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     &&
    _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
     &&
    read($Heap, this, _module.Map.Repr)[$Box(this)]
     && !read($Heap, this, _module.Map.Repr)[$Box(null)]
     && Set#Subset(read($Heap, this, _module.Map.Spine), read($Heap, this, _module.Map.Repr))
     && _module.Map.SpineValid(_module.Map$Key,
      _module.Map$Value,
      $LS($LZ),
      $Heap,
      read($Heap, this, _module.Map.Spine),
      read($Heap, this, _module.Map.head))
     && (forall k#1: Box ::
      { Map#Domain(read($Heap, this, _module.Map.M))[k#1] }
      $IsBox(k#1, _module.Map$Key)
         ==>
        Map#Domain(read($Heap, this, _module.Map.M))[k#1]
         ==> (exists n#5: ref ::
          { read($Heap, n#5, _module.Node.key) }
            { read($Heap, this, _module.Map.Spine)[$Box(n#5)] }
          $Is(n#5, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
             &&
            read($Heap, this, _module.Map.Spine)[$Box(n#5)]
             && read($Heap, n#5, _module.Node.key) == k#1))
     && (forall n#6: ref ::
      { read($Heap, n#6, _module.Node.val) }
        { read($Heap, n#6, _module.Node.key) }
        { read($Heap, this, _module.Map.Spine)[$Box(n#6)] }
      $Is(n#6, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
         ==> (read($Heap, this, _module.Map.Spine)[$Box(n#6)]
             ==> Map#Domain(read($Heap, this, _module.Map.M))[read($Heap, n#6, _module.Node.key)])
           && (read($Heap, this, _module.Map.Spine)[$Box(n#6)]
             ==> read($Heap, n#6, _module.Node.val)
               == Map#Elements(read($Heap, this, _module.Map.M))[read($Heap, n#6, _module.Node.key)]))
     && (forall n#7: ref, n'#2: ref ::
      { read($Heap, n'#2, _module.Node.key), read($Heap, n#7, _module.Node.key) }
        { read($Heap, n'#2, _module.Node.key), read($Heap, this, _module.Map.Spine)[$Box(n#7)] }
        { read($Heap, n#7, _module.Node.key), read($Heap, this, _module.Map.Spine)[$Box(n'#2)] }
        { read($Heap, this, _module.Map.Spine)[$Box(n'#2)], read($Heap, this, _module.Map.Spine)[$Box(n#7)] }
      $Is(n#7, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
           && $Is(n'#2, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
         ==>
        read($Heap, this, _module.Map.Spine)[$Box(n#7)]
           && read($Heap, this, _module.Map.Spine)[$Box(n'#2)]
           && n#7 != n'#2
         ==> read($Heap, n#7, _module.Node.key) != read($Heap, n'#2, _module.Node.key))
     && (forall n#8: ref ::
      { read($Heap, n#8, _module.Node.next) }
        { read($Heap, this, _module.Map.Spine)[$Box(n#8)] }
      $Is(n#8, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
         ==>
        read($Heap, this, _module.Map.Spine)[$Box(n#8)]
         ==> read($Heap, n#8, _module.Node.next) != read($Heap, this, _module.Map.head))
     && (forall n#9: ref, n'#3: ref ::
      { read($Heap, n'#3, _module.Node.next), read($Heap, n#9, _module.Node.next) }
        { read($Heap, n'#3, _module.Node.next), read($Heap, this, _module.Map.Spine)[$Box(n#9)] }
        { read($Heap, n#9, _module.Node.next), read($Heap, this, _module.Map.Spine)[$Box(n'#3)] }
        { read($Heap, this, _module.Map.Spine)[$Box(n'#3)], read($Heap, this, _module.Map.Spine)[$Box(n#9)] }
      $Is(n#9, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
           && $Is(n'#3, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
         ==>
        read($Heap, this, _module.Map.Spine)[$Box(n#9)]
           && read($Heap, this, _module.Map.Spine)[$Box(n'#3)]
           && read($Heap, n#9, _module.Node.next) == read($Heap, n'#3, _module.Node.next)
         ==> n#9 == n'#3);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures p#0 == null ==> !Map#Domain(read($Heap, this, _module.Map.M))[key#0];
  free ensures true;
  ensures p#0 != null ==> Map#Domain(read($Heap, this, _module.Map.M))[key#0];
  ensures p#0 != null ==> read($Heap, this, _module.Map.Spine)[$Box(p#0)];
  ensures p#0 != null ==> read($Heap, p#0, _module.Node.key) == key#0;
  ensures p#0 != null ==> p#0 == read($Heap, this, _module.Map.head) ==> prev#0 == null;
  ensures p#0 != null
     ==>
    p#0 != read($Heap, this, _module.Map.head)
     ==> read($Heap, this, _module.Map.Spine)[$Box(prev#0)];
  ensures p#0 != null
     ==>
    p#0 != read($Heap, this, _module.Map.head)
     ==> read($Heap, prev#0, _module.Node.next) == p#0;
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Map.FindIndex(_module.Map$Key: Ty, _module.Map$Value: Ty, this: ref, key#0: Box)
   returns (prev#0: ref, p#0: ref, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs#0: ref
     where $Is($rhs#0, Tclass._module.Node(_module.Map$Key, _module.Map$Value));
  var $rhs#1: ref
     where $Is($rhs#1, Tclass._module.Node(_module.Map$Key, _module.Map$Value));
  var spine#0: Set Box
     where $Is(spine#0, TSet(Tclass._module.Node(_module.Map$Key, _module.Map$Value)))
       && $IsAlloc(spine#0, TSet(Tclass._module.Node(_module.Map$Key, _module.Map$Value)), $Heap);
  var $PreLoopHeap$loop#0: Heap;
  var $decr_init$loop#00: Set Box;
  var $w$loop#0: bool;
  var ##spine#0: Set Box;
  var ##n#0: ref;
  var n#10: ref;
  var $decr$loop#00: Set Box;
  var $rhs#0_0: ref
     where $Is($rhs#0_0, Tclass._module.Node(_module.Map$Key, _module.Map$Value));
  var $rhs#0_1: ref
     where $Is($rhs#0_1, Tclass._module.Node(_module.Map$Key, _module.Map$Value));

    // AddMethodImpl: FindIndex, Impl$$_module.Map.FindIndex
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "b4.dfy(75,2): initial state"} true;
    $_reverifyPost := false;
    // ----- update statement ----- b4.dfy(76,13)
    assume true;
    assume true;
    assume true;
    $rhs#0 := null;
    assume true;
    $rhs#1 := read($Heap, this, _module.Map.head);
    prev#0 := $rhs#0;
    p#0 := $rhs#1;
    assume {:captureState "b4.dfy(76,25)"} true;
    // ----- assignment statement ----- b4.dfy(77,21)
    assume true;
    assume true;
    spine#0 := read($Heap, this, _module.Map.Spine);
    assume {:captureState "b4.dfy(77,28)"} true;
    // ----- while statement ----- b4.dfy(78,5)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    $decr_init$loop#00 := spine#0;
    havoc $w$loop#0;
    while (true)
      free invariant $w$loop#0
         ==> _module.Map.SpineValid#canCall(_module.Map$Key, _module.Map$Value, $Heap, spine#0, p#0);
      invariant $w$loop#0
         ==>
        _module.Map.SpineValid#canCall(_module.Map$Key, _module.Map$Value, $Heap, spine#0, p#0)
         ==> _module.Map.SpineValid(_module.Map$Key, _module.Map$Value, $LS($LZ), $Heap, spine#0, p#0)
           ||
          (p#0 == null && Set#Equal(spine#0, Set#Empty(): Set Box))
           || (
            p#0 != null
             && spine#0[$Box(p#0)]
             && Set#Equal(read($Heap, p#0, _module.Node.Spine),
              Set#Difference(spine#0, Set#UnionOne(Set#Empty(): Set Box, $Box(p#0))))
             && _module.Map.SpineValid(_module.Map$Key,
              _module.Map$Value,
              $LS($LS($LZ)),
              $Heap,
              read($Heap, p#0, _module.Node.Spine),
              read($Heap, p#0, _module.Node.next)));
      free invariant $w$loop#0
         ==> _module.Map.SpineValid#canCall(_module.Map$Key, _module.Map$Value, $Heap, spine#0, p#0)
           &&
          _module.Map.SpineValid(_module.Map$Key, _module.Map$Value, $LS($LZ), $Heap, spine#0, p#0)
           && ((p#0 == null && Set#Equal(spine#0, Set#Empty(): Set Box))
             || (
              p#0 != null
               && spine#0[$Box(p#0)]
               && Set#Equal(read($Heap, p#0, _module.Node.Spine),
                Set#Difference(spine#0, Set#UnionOne(Set#Empty(): Set Box, $Box(p#0))))
               && _module.Map.SpineValid(_module.Map$Key,
                _module.Map$Value,
                $LS($LZ),
                $Heap,
                read($Heap, p#0, _module.Node.Spine),
                read($Heap, p#0, _module.Node.next))));
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0 ==> p#0 != null ==> spine#0[$Box(p#0)];
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0 ==> p#0 == read($Heap, this, _module.Map.head) ==> prev#0 == null;
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0
         ==>
        p#0 != read($Heap, this, _module.Map.head)
         ==> read($Heap, this, _module.Map.Spine)[$Box(prev#0)];
      invariant $w$loop#0
         ==>
        p#0 != read($Heap, this, _module.Map.head)
         ==> read($Heap, prev#0, _module.Node.next) == p#0;
      invariant $w$loop#0
         ==>
        p#0 != read($Heap, this, _module.Map.head)
         ==> !spine#0[$Box(read($Heap, this, _module.Map.head))];
      free invariant $w$loop#0
         ==>
        Map#Domain(read($Heap, this, _module.Map.M))[key#0]
         ==> (forall n#11: ref ::
          { read($Heap, n#11, _module.Node.key) } { spine#0[$Box(n#11)] }
          true);
      invariant $w$loop#0
         ==>
        Map#Domain(read($Heap, this, _module.Map.M))[key#0]
         ==> (exists n#11: ref ::
          { read($Heap, n#11, _module.Node.key) } { spine#0[$Box(n#11)] }
          $Is(n#11, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
             &&
            spine#0[$Box(n#11)]
             && read($Heap, n#11, _module.Node.key) == key#0);
      free invariant $w$loop#0
         ==>
        Map#Domain(read($Heap, this, _module.Map.M))[key#0]
         ==> (exists n#11: ref ::
          { read($Heap, n#11, _module.Node.key) } { spine#0[$Box(n#11)] }
          $Is(n#11, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
             &&
            spine#0[$Box(n#11)]
             && read($Heap, n#11, _module.Node.key) == key#0);
      free invariant (forall<alpha> $o: ref, $f: Field alpha ::
        { read($Heap, $o, $f) }
        $o != null && read(old($Heap), $o, alloc)
           ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0, $o, $f));
      free invariant $HeapSucc($PreLoopHeap$loop#0, $Heap);
      free invariant (forall<alpha> $o: ref, $f: Field alpha ::
        { read($Heap, $o, $f) }
        $o != null && read($PreLoopHeap$loop#0, $o, alloc)
           ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0, $o, $f) || $_Frame[$o, $f]);
      free invariant Set#Subset(spine#0, $decr_init$loop#00)
         && (Set#Equal(spine#0, $decr_init$loop#00) ==> true);
    {
        assume {:captureState "b4.dfy(78,4): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            ##spine#0 := spine#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##spine#0, TSet(Tclass._module.Node(_module.Map$Key, _module.Map$Value)), $Heap);
            ##n#0 := p#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#0, Tclass._module.Node(_module.Map$Key, _module.Map$Value), $Heap);
            assume _module.Map.SpineValid#canCall(_module.Map$Key, _module.Map$Value, $Heap, spine#0, p#0);
            assume _module.Map.SpineValid#canCall(_module.Map$Key, _module.Map$Value, $Heap, spine#0, p#0);
            assume _module.Map.SpineValid(_module.Map$Key, _module.Map$Value, $LS($LZ), $Heap, spine#0, p#0);
            if (p#0 != null)
            {
            }

            assume true;
            assume p#0 != null ==> spine#0[$Box(p#0)];
            if (p#0 == read($Heap, this, _module.Map.head))
            {
            }

            assume true;
            assume p#0 == read($Heap, this, _module.Map.head) ==> prev#0 == null;
            if (p#0 != read($Heap, this, _module.Map.head))
            {
                if (read($Heap, this, _module.Map.Spine)[$Box(prev#0)])
                {
                    assert {:subsumption 0} prev#0 != null;
                }

                if (read($Heap, this, _module.Map.Spine)[$Box(prev#0)]
                   && read($Heap, prev#0, _module.Node.next) == p#0)
                {
                }
            }

            assume true;
            assume p#0 != read($Heap, this, _module.Map.head)
               ==> read($Heap, this, _module.Map.Spine)[$Box(prev#0)]
                 && read($Heap, prev#0, _module.Node.next) == p#0
                 && !spine#0[$Box(read($Heap, this, _module.Map.head))];
            if (Map#Domain(read($Heap, this, _module.Map.M))[key#0])
            {
                havoc n#10;
                assume $Is(n#10, Tclass._module.Node(_module.Map$Key, _module.Map$Value));
                // Begin Comprehension WF check
                if (spine#0[$Box(n#10)])
                {
                    assert {:subsumption 0} n#10 != null;
                }

                // End Comprehension WF check
            }

            assume Map#Domain(read($Heap, this, _module.Map.M))[key#0]
               ==> (forall n#11: ref ::
                { read($Heap, n#11, _module.Node.key) } { spine#0[$Box(n#11)] }
                true);
            assume Map#Domain(read($Heap, this, _module.Map.M))[key#0]
               ==> (exists n#11: ref ::
                { read($Heap, n#11, _module.Node.key) } { spine#0[$Box(n#11)] }
                $Is(n#11, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
                   &&
                  spine#0[$Box(n#11)]
                   && read($Heap, n#11, _module.Node.key) == key#0);
            assume true;
            assume false;
        }

        assume true;
        if (p#0 == null)
        {
            break;
        }

        $decr$loop#00 := spine#0;
        // ----- if statement ----- b4.dfy(86,7)
        assert p#0 != null;
        assume true;
        if (read($Heap, p#0, _module.Node.key) == key#0)
        {
            // ----- return statement ----- b4.dfy(87,9)
            return;
        }
        else
        {
            // ----- assignment statement ----- b4.dfy(89,15)
            assume true;
            assert p#0 != null;
            assume true;
            spine#0 := read($Heap, p#0, _module.Node.Spine);
            assume {:captureState "b4.dfy(89,24)"} true;
            // ----- update statement ----- b4.dfy(90,17)
            assume true;
            assume true;
            assume true;
            $rhs#0_0 := p#0;
            assert p#0 != null;
            assume true;
            $rhs#0_1 := read($Heap, p#0, _module.Node.next);
            prev#0 := $rhs#0_0;
            p#0 := $rhs#0_1;
            assume {:captureState "b4.dfy(90,28)"} true;
        }

        // ----- loop termination check ----- b4.dfy(78,5)
        assert Set#Subset(spine#0, $decr$loop#00) && !Set#Subset($decr$loop#00, spine#0);
        assume _module.Map.SpineValid#canCall(_module.Map$Key, _module.Map$Value, $Heap, spine#0, p#0);
        assume true;
        assume true;
        assume true;
        assume Map#Domain(read($Heap, this, _module.Map.M))[key#0]
           ==> (forall n#11: ref ::
            { read($Heap, n#11, _module.Node.key) } { spine#0[$Box(n#11)] }
            true);
    }
}



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
  free requires 7 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.Map.Find(_module.Map$Key: Ty, _module.Map$Value: Ty, this: ref, key#0: Box)
   returns (result#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: Find, CheckWellformed$$_module.Map.Find
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "b4.dfy(95,9): initial state"} true;
    assume _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this);
    assume _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this);
    havoc $Heap;
    assume (forall<alpha> $o: ref, $f: Field alpha ::
      { read($Heap, $o, $f) }
      $o != null && read(old($Heap), $o, alloc)
         ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
    assume $HeapSucc(old($Heap), $Heap);
    havoc result#0;
    assume {:captureState "b4.dfy(97,27): post-state"} true;
    if (*)
    {
        assume result#0 == Lit(#_module.Maybe.None());
        assume !Map#Domain(read($Heap, this, _module.Map.M))[key#0];
    }
    else
    {
        assume result#0 == Lit(#_module.Maybe.None())
           ==> !Map#Domain(read($Heap, this, _module.Map.M))[key#0];
    }

    if (*)
    {
        assume _module.Maybe.Some_q(result#0);
        assume Map#Domain(read($Heap, this, _module.Map.M))[key#0];
        assert _module.Maybe.Some_q(result#0);
        assert Map#Domain(read($Heap, this, _module.Map.M))[key#0];
        assume _module.Maybe.get(result#0)
           == Map#Elements(read($Heap, this, _module.Map.M))[key#0];
    }
    else
    {
        assume _module.Maybe.Some_q(result#0)
           ==> Map#Domain(read($Heap, this, _module.Map.M))[key#0]
             && _module.Maybe.get(result#0)
               == Map#Elements(read($Heap, this, _module.Map.M))[key#0];
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
       || read($Heap, this, _module.Map.Repr)[$Box(this)];
  requires _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     ==> _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
       || !read($Heap, this, _module.Map.Repr)[$Box(null)];
  requires _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     ==> _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
       || Set#Subset(read($Heap, this, _module.Map.Spine), read($Heap, this, _module.Map.Repr));
  requires _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     ==> _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
       || (_module.Map.SpineValid#canCall(_module.Map$Key,
          _module.Map$Value,
          $Heap,
          read($Heap, this, _module.Map.Spine),
          read($Heap, this, _module.Map.head))
         ==> _module.Map.SpineValid(_module.Map$Key,
            _module.Map$Value,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.Map.Spine),
            read($Heap, this, _module.Map.head))
           ||
          (read($Heap, this, _module.Map.head) == null
             && Set#Equal(read($Heap, this, _module.Map.Spine), Set#Empty(): Set Box))
           || (
            read($Heap, this, _module.Map.head) != null
             && read($Heap, this, _module.Map.Spine)[$Box(read($Heap, this, _module.Map.head))]
             && Set#Equal(read($Heap, read($Heap, this, _module.Map.head), _module.Node.Spine),
              Set#Difference(read($Heap, this, _module.Map.Spine),
                Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Map.head)))))
             && _module.Map.SpineValid(_module.Map$Key,
              _module.Map$Value,
              $LS($LS($LZ)),
              $Heap,
              read($Heap, read($Heap, this, _module.Map.head), _module.Node.Spine),
              read($Heap, read($Heap, this, _module.Map.head), _module.Node.next))));
  requires _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     ==> _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
       || (forall k#0: Box ::
        { Map#Domain(read($Heap, this, _module.Map.M))[k#0] }
        $IsBox(k#0, _module.Map$Key)
           ==>
          Map#Domain(read($Heap, this, _module.Map.M))[k#0]
           ==> (exists n#0: ref ::
            { read($Heap, n#0, _module.Node.key) }
              { read($Heap, this, _module.Map.Spine)[$Box(n#0)] }
            $Is(n#0, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
               &&
              read($Heap, this, _module.Map.Spine)[$Box(n#0)]
               && read($Heap, n#0, _module.Node.key) == k#0));
  requires _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     ==> _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
       || (forall n#1: ref ::
        { read($Heap, n#1, _module.Node.val) }
          { read($Heap, n#1, _module.Node.key) }
          { read($Heap, this, _module.Map.Spine)[$Box(n#1)] }
        $Is(n#1, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
           ==> (read($Heap, this, _module.Map.Spine)[$Box(n#1)]
               ==> Map#Domain(read($Heap, this, _module.Map.M))[read($Heap, n#1, _module.Node.key)])
             && (read($Heap, this, _module.Map.Spine)[$Box(n#1)]
               ==> read($Heap, n#1, _module.Node.val)
                 == Map#Elements(read($Heap, this, _module.Map.M))[read($Heap, n#1, _module.Node.key)]));
  requires _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     ==> _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
       || (forall n#2: ref, n'#0: ref ::
        { read($Heap, n'#0, _module.Node.key), read($Heap, n#2, _module.Node.key) }
          { read($Heap, n'#0, _module.Node.key), read($Heap, this, _module.Map.Spine)[$Box(n#2)] }
          { read($Heap, n#2, _module.Node.key), read($Heap, this, _module.Map.Spine)[$Box(n'#0)] }
          { read($Heap, this, _module.Map.Spine)[$Box(n'#0)], read($Heap, this, _module.Map.Spine)[$Box(n#2)] }
        $Is(n#2, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
             && $Is(n'#0, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
           ==>
          read($Heap, this, _module.Map.Spine)[$Box(n#2)]
             && read($Heap, this, _module.Map.Spine)[$Box(n'#0)]
             && n#2 != n'#0
           ==> read($Heap, n#2, _module.Node.key) != read($Heap, n'#0, _module.Node.key));
  requires _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     ==> _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
       || (forall n#3: ref ::
        { read($Heap, n#3, _module.Node.next) }
          { read($Heap, this, _module.Map.Spine)[$Box(n#3)] }
        $Is(n#3, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
           ==>
          read($Heap, this, _module.Map.Spine)[$Box(n#3)]
           ==> read($Heap, n#3, _module.Node.next) != read($Heap, this, _module.Map.head));
  requires _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     ==> _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
       || (forall n#4: ref, n'#1: ref ::
        { read($Heap, n'#1, _module.Node.next), read($Heap, n#4, _module.Node.next) }
          { read($Heap, n'#1, _module.Node.next), read($Heap, this, _module.Map.Spine)[$Box(n#4)] }
          { read($Heap, n#4, _module.Node.next), read($Heap, this, _module.Map.Spine)[$Box(n'#1)] }
          { read($Heap, this, _module.Map.Spine)[$Box(n'#1)], read($Heap, this, _module.Map.Spine)[$Box(n#4)] }
        $Is(n#4, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
             && $Is(n'#1, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
           ==>
          read($Heap, this, _module.Map.Spine)[$Box(n#4)]
             && read($Heap, this, _module.Map.Spine)[$Box(n'#1)]
             && read($Heap, n#4, _module.Node.next) == read($Heap, n'#1, _module.Node.next)
           ==> n#4 == n'#1);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures result#0 == Lit(#_module.Maybe.None())
     ==> !Map#Domain(read($Heap, this, _module.Map.M))[key#0];
  free ensures true;
  ensures _module.Maybe.Some_q(result#0)
     ==> Map#Domain(read($Heap, this, _module.Map.M))[key#0];
  ensures _module.Maybe.Some_q(result#0)
     ==> _module.Maybe.get(result#0)
       == Map#Elements(read($Heap, this, _module.Map.M))[key#0];
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
  free requires 7 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     &&
    _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
     &&
    read($Heap, this, _module.Map.Repr)[$Box(this)]
     && !read($Heap, this, _module.Map.Repr)[$Box(null)]
     && Set#Subset(read($Heap, this, _module.Map.Spine), read($Heap, this, _module.Map.Repr))
     && _module.Map.SpineValid(_module.Map$Key,
      _module.Map$Value,
      $LS($LZ),
      $Heap,
      read($Heap, this, _module.Map.Spine),
      read($Heap, this, _module.Map.head))
     && (forall k#1: Box ::
      { Map#Domain(read($Heap, this, _module.Map.M))[k#1] }
      $IsBox(k#1, _module.Map$Key)
         ==>
        Map#Domain(read($Heap, this, _module.Map.M))[k#1]
         ==> (exists n#5: ref ::
          { read($Heap, n#5, _module.Node.key) }
            { read($Heap, this, _module.Map.Spine)[$Box(n#5)] }
          $Is(n#5, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
             &&
            read($Heap, this, _module.Map.Spine)[$Box(n#5)]
             && read($Heap, n#5, _module.Node.key) == k#1))
     && (forall n#6: ref ::
      { read($Heap, n#6, _module.Node.val) }
        { read($Heap, n#6, _module.Node.key) }
        { read($Heap, this, _module.Map.Spine)[$Box(n#6)] }
      $Is(n#6, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
         ==> (read($Heap, this, _module.Map.Spine)[$Box(n#6)]
             ==> Map#Domain(read($Heap, this, _module.Map.M))[read($Heap, n#6, _module.Node.key)])
           && (read($Heap, this, _module.Map.Spine)[$Box(n#6)]
             ==> read($Heap, n#6, _module.Node.val)
               == Map#Elements(read($Heap, this, _module.Map.M))[read($Heap, n#6, _module.Node.key)]))
     && (forall n#7: ref, n'#2: ref ::
      { read($Heap, n'#2, _module.Node.key), read($Heap, n#7, _module.Node.key) }
        { read($Heap, n'#2, _module.Node.key), read($Heap, this, _module.Map.Spine)[$Box(n#7)] }
        { read($Heap, n#7, _module.Node.key), read($Heap, this, _module.Map.Spine)[$Box(n'#2)] }
        { read($Heap, this, _module.Map.Spine)[$Box(n'#2)], read($Heap, this, _module.Map.Spine)[$Box(n#7)] }
      $Is(n#7, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
           && $Is(n'#2, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
         ==>
        read($Heap, this, _module.Map.Spine)[$Box(n#7)]
           && read($Heap, this, _module.Map.Spine)[$Box(n'#2)]
           && n#7 != n'#2
         ==> read($Heap, n#7, _module.Node.key) != read($Heap, n'#2, _module.Node.key))
     && (forall n#8: ref ::
      { read($Heap, n#8, _module.Node.next) }
        { read($Heap, this, _module.Map.Spine)[$Box(n#8)] }
      $Is(n#8, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
         ==>
        read($Heap, this, _module.Map.Spine)[$Box(n#8)]
         ==> read($Heap, n#8, _module.Node.next) != read($Heap, this, _module.Map.head))
     && (forall n#9: ref, n'#3: ref ::
      { read($Heap, n'#3, _module.Node.next), read($Heap, n#9, _module.Node.next) }
        { read($Heap, n'#3, _module.Node.next), read($Heap, this, _module.Map.Spine)[$Box(n#9)] }
        { read($Heap, n#9, _module.Node.next), read($Heap, this, _module.Map.Spine)[$Box(n'#3)] }
        { read($Heap, this, _module.Map.Spine)[$Box(n'#3)], read($Heap, this, _module.Map.Spine)[$Box(n#9)] }
      $Is(n#9, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
           && $Is(n'#3, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
         ==>
        read($Heap, this, _module.Map.Spine)[$Box(n#9)]
           && read($Heap, this, _module.Map.Spine)[$Box(n'#3)]
           && read($Heap, n#9, _module.Node.next) == read($Heap, n'#3, _module.Node.next)
         ==> n#9 == n'#3);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures result#0 == Lit(#_module.Maybe.None())
     ==> !Map#Domain(read($Heap, this, _module.Map.M))[key#0];
  free ensures true;
  ensures _module.Maybe.Some_q(result#0)
     ==> Map#Domain(read($Heap, this, _module.Map.M))[key#0];
  ensures _module.Maybe.Some_q(result#0)
     ==> _module.Maybe.get(result#0)
       == Map#Elements(read($Heap, this, _module.Map.M))[key#0];
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
  var prev#0: ref
     where $Is(prev#0, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
       && $IsAlloc(prev#0, Tclass._module.Node(_module.Map$Key, _module.Map$Value), $Heap);
  var p#0: ref
     where $Is(p#0, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
       && $IsAlloc(p#0, Tclass._module.Node(_module.Map$Key, _module.Map$Value), $Heap);
  var $rhs##0: ref
     where $Is($rhs##0, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
       && $IsAlloc($rhs##0, Tclass._module.Node(_module.Map$Key, _module.Map$Value), $Heap);
  var $rhs##1: ref
     where $Is($rhs##1, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
       && $IsAlloc($rhs##1, Tclass._module.Node(_module.Map$Key, _module.Map$Value), $Heap);
  var key##0: Box;

    // AddMethodImpl: Find, Impl$$_module.Map.Find
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "b4.dfy(99,2): initial state"} true;
    $_reverifyPost := false;
    // ----- call statement ----- b4.dfy(100,29)
    assume true;
    assume true;
    // TrCallStmt: Adding lhs Microsoft.Dafny.AutoGhostIdentifierExpr with type Node<Key, Value>
    // TrCallStmt: Adding lhs Microsoft.Dafny.AutoGhostIdentifierExpr with type Node<Key, Value>
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    key##0 := key#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##0, $rhs##1 := Call$$_module.Map.FindIndex(_module.Map$Key, _module.Map$Value, this, key##0);
    // TrCallStmt: After ProcessCallStmt
    prev#0 := $rhs##0;
    p#0 := $rhs##1;
    assume {:captureState "b4.dfy(100,33)"} true;
    // ----- if statement ----- b4.dfy(101,5)
    assume true;
    if (p#0 == null)
    {
        // ----- assignment statement ----- b4.dfy(102,14)
        assume true;
        assume true;
        result#0 := Lit(#_module.Maybe.None());
        assume {:captureState "b4.dfy(102,20)"} true;
    }
    else
    {
        // ----- assignment statement ----- b4.dfy(104,14)
        assume true;
        assert p#0 != null;
        assume true;
        result#0 := #_module.Maybe.Some(read($Heap, p#0, _module.Node.val));
        assume {:captureState "b4.dfy(104,27)"} true;
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
  free requires 9 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.Map.Add(_module.Map$Key: Ty, _module.Map$Value: Ty, this: ref, key#0: Box, val#0: Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: Add, CheckWellformed$$_module.Map.Add
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc)
         ==> read($Heap, this, _module.Map.Repr)[$Box($o)]);
    assume {:captureState "b4.dfy(110,9): initial state"} true;
    assume _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this);
    assume _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this);
    havoc $Heap;
    assume (forall<alpha> $o: ref, $f: Field alpha ::
      { read($Heap, $o, $f) }
      $o != null && read(old($Heap), $o, alloc)
         ==> read($Heap, $o, $f) == read(old($Heap), $o, $f)
           || read(old($Heap), this, _module.Map.Repr)[$Box($o)]);
    assume $HeapSucc(old($Heap), $Heap);
    assume {:captureState "b4.dfy(113,20): post-state"} true;
    assume _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this);
    assume _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this);
    assert $IsAlloc(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value), old($Heap));
    assume (forall $o: ref ::
      { read(old($Heap), $o, alloc) }
      read($Heap, this, _module.Map.Repr)[$Box($o)]
           && !read(old($Heap), this, _module.Map.Repr)[$Box($o)]
         ==> $o != null && !read(old($Heap), $o, alloc));
    assert $IsAlloc(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value), old($Heap));
    assume Map#Equal(read($Heap, this, _module.Map.M),
      Map#Build(read(old($Heap), this, _module.Map.M), key#0, val#0));
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
       || read($Heap, this, _module.Map.Repr)[$Box(this)];
  requires _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     ==> _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
       || !read($Heap, this, _module.Map.Repr)[$Box(null)];
  requires _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     ==> _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
       || Set#Subset(read($Heap, this, _module.Map.Spine), read($Heap, this, _module.Map.Repr));
  requires _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     ==> _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
       || (_module.Map.SpineValid#canCall(_module.Map$Key,
          _module.Map$Value,
          $Heap,
          read($Heap, this, _module.Map.Spine),
          read($Heap, this, _module.Map.head))
         ==> _module.Map.SpineValid(_module.Map$Key,
            _module.Map$Value,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.Map.Spine),
            read($Heap, this, _module.Map.head))
           ||
          (read($Heap, this, _module.Map.head) == null
             && Set#Equal(read($Heap, this, _module.Map.Spine), Set#Empty(): Set Box))
           || (
            read($Heap, this, _module.Map.head) != null
             && read($Heap, this, _module.Map.Spine)[$Box(read($Heap, this, _module.Map.head))]
             && Set#Equal(read($Heap, read($Heap, this, _module.Map.head), _module.Node.Spine),
              Set#Difference(read($Heap, this, _module.Map.Spine),
                Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Map.head)))))
             && _module.Map.SpineValid(_module.Map$Key,
              _module.Map$Value,
              $LS($LS($LZ)),
              $Heap,
              read($Heap, read($Heap, this, _module.Map.head), _module.Node.Spine),
              read($Heap, read($Heap, this, _module.Map.head), _module.Node.next))));
  requires _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     ==> _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
       || (forall k#0: Box ::
        { Map#Domain(read($Heap, this, _module.Map.M))[k#0] }
        $IsBox(k#0, _module.Map$Key)
           ==>
          Map#Domain(read($Heap, this, _module.Map.M))[k#0]
           ==> (exists n#0: ref ::
            { read($Heap, n#0, _module.Node.key) }
              { read($Heap, this, _module.Map.Spine)[$Box(n#0)] }
            $Is(n#0, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
               &&
              read($Heap, this, _module.Map.Spine)[$Box(n#0)]
               && read($Heap, n#0, _module.Node.key) == k#0));
  requires _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     ==> _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
       || (forall n#1: ref ::
        { read($Heap, n#1, _module.Node.val) }
          { read($Heap, n#1, _module.Node.key) }
          { read($Heap, this, _module.Map.Spine)[$Box(n#1)] }
        $Is(n#1, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
           ==> (read($Heap, this, _module.Map.Spine)[$Box(n#1)]
               ==> Map#Domain(read($Heap, this, _module.Map.M))[read($Heap, n#1, _module.Node.key)])
             && (read($Heap, this, _module.Map.Spine)[$Box(n#1)]
               ==> read($Heap, n#1, _module.Node.val)
                 == Map#Elements(read($Heap, this, _module.Map.M))[read($Heap, n#1, _module.Node.key)]));
  requires _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     ==> _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
       || (forall n#2: ref, n'#0: ref ::
        { read($Heap, n'#0, _module.Node.key), read($Heap, n#2, _module.Node.key) }
          { read($Heap, n'#0, _module.Node.key), read($Heap, this, _module.Map.Spine)[$Box(n#2)] }
          { read($Heap, n#2, _module.Node.key), read($Heap, this, _module.Map.Spine)[$Box(n'#0)] }
          { read($Heap, this, _module.Map.Spine)[$Box(n'#0)], read($Heap, this, _module.Map.Spine)[$Box(n#2)] }
        $Is(n#2, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
             && $Is(n'#0, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
           ==>
          read($Heap, this, _module.Map.Spine)[$Box(n#2)]
             && read($Heap, this, _module.Map.Spine)[$Box(n'#0)]
             && n#2 != n'#0
           ==> read($Heap, n#2, _module.Node.key) != read($Heap, n'#0, _module.Node.key));
  requires _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     ==> _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
       || (forall n#3: ref ::
        { read($Heap, n#3, _module.Node.next) }
          { read($Heap, this, _module.Map.Spine)[$Box(n#3)] }
        $Is(n#3, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
           ==>
          read($Heap, this, _module.Map.Spine)[$Box(n#3)]
           ==> read($Heap, n#3, _module.Node.next) != read($Heap, this, _module.Map.head));
  requires _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     ==> _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
       || (forall n#4: ref, n'#1: ref ::
        { read($Heap, n'#1, _module.Node.next), read($Heap, n#4, _module.Node.next) }
          { read($Heap, n'#1, _module.Node.next), read($Heap, this, _module.Map.Spine)[$Box(n#4)] }
          { read($Heap, n#4, _module.Node.next), read($Heap, this, _module.Map.Spine)[$Box(n'#1)] }
          { read($Heap, this, _module.Map.Spine)[$Box(n'#1)], read($Heap, this, _module.Map.Spine)[$Box(n#4)] }
        $Is(n#4, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
             && $Is(n'#1, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
           ==>
          read($Heap, this, _module.Map.Spine)[$Box(n#4)]
             && read($Heap, this, _module.Map.Spine)[$Box(n'#1)]
             && read($Heap, n#4, _module.Node.next) == read($Heap, n'#1, _module.Node.next)
           ==> n#4 == n'#1);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this);
  free ensures _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     &&
    _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
     &&
    read($Heap, this, _module.Map.Repr)[$Box(this)]
     && !read($Heap, this, _module.Map.Repr)[$Box(null)]
     && Set#Subset(read($Heap, this, _module.Map.Spine), read($Heap, this, _module.Map.Repr))
     && _module.Map.SpineValid(_module.Map$Key,
      _module.Map$Value,
      $LS($LZ),
      $Heap,
      read($Heap, this, _module.Map.Spine),
      read($Heap, this, _module.Map.head))
     && (forall k#1: Box ::
      { Map#Domain(read($Heap, this, _module.Map.M))[k#1] }
      $IsBox(k#1, _module.Map$Key)
         ==>
        Map#Domain(read($Heap, this, _module.Map.M))[k#1]
         ==> (exists n#5: ref ::
          { read($Heap, n#5, _module.Node.key) }
            { read($Heap, this, _module.Map.Spine)[$Box(n#5)] }
          $Is(n#5, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
             &&
            read($Heap, this, _module.Map.Spine)[$Box(n#5)]
             && read($Heap, n#5, _module.Node.key) == k#1))
     && (forall n#6: ref ::
      { read($Heap, n#6, _module.Node.val) }
        { read($Heap, n#6, _module.Node.key) }
        { read($Heap, this, _module.Map.Spine)[$Box(n#6)] }
      $Is(n#6, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
         ==> (read($Heap, this, _module.Map.Spine)[$Box(n#6)]
             ==> Map#Domain(read($Heap, this, _module.Map.M))[read($Heap, n#6, _module.Node.key)])
           && (read($Heap, this, _module.Map.Spine)[$Box(n#6)]
             ==> read($Heap, n#6, _module.Node.val)
               == Map#Elements(read($Heap, this, _module.Map.M))[read($Heap, n#6, _module.Node.key)]))
     && (forall n#7: ref, n'#2: ref ::
      { read($Heap, n'#2, _module.Node.key), read($Heap, n#7, _module.Node.key) }
        { read($Heap, n'#2, _module.Node.key), read($Heap, this, _module.Map.Spine)[$Box(n#7)] }
        { read($Heap, n#7, _module.Node.key), read($Heap, this, _module.Map.Spine)[$Box(n'#2)] }
        { read($Heap, this, _module.Map.Spine)[$Box(n'#2)], read($Heap, this, _module.Map.Spine)[$Box(n#7)] }
      $Is(n#7, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
           && $Is(n'#2, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
         ==>
        read($Heap, this, _module.Map.Spine)[$Box(n#7)]
           && read($Heap, this, _module.Map.Spine)[$Box(n'#2)]
           && n#7 != n'#2
         ==> read($Heap, n#7, _module.Node.key) != read($Heap, n'#2, _module.Node.key))
     && (forall n#8: ref ::
      { read($Heap, n#8, _module.Node.next) }
        { read($Heap, this, _module.Map.Spine)[$Box(n#8)] }
      $Is(n#8, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
         ==>
        read($Heap, this, _module.Map.Spine)[$Box(n#8)]
         ==> read($Heap, n#8, _module.Node.next) != read($Heap, this, _module.Map.head))
     && (forall n#9: ref, n'#3: ref ::
      { read($Heap, n'#3, _module.Node.next), read($Heap, n#9, _module.Node.next) }
        { read($Heap, n'#3, _module.Node.next), read($Heap, this, _module.Map.Spine)[$Box(n#9)] }
        { read($Heap, n#9, _module.Node.next), read($Heap, this, _module.Map.Spine)[$Box(n'#3)] }
        { read($Heap, this, _module.Map.Spine)[$Box(n'#3)], read($Heap, this, _module.Map.Spine)[$Box(n#9)] }
      $Is(n#9, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
           && $Is(n'#3, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
         ==>
        read($Heap, this, _module.Map.Spine)[$Box(n#9)]
           && read($Heap, this, _module.Map.Spine)[$Box(n'#3)]
           && read($Heap, n#9, _module.Node.next) == read($Heap, n'#3, _module.Node.next)
         ==> n#9 == n'#3);
  ensures (forall $o: ref ::
    { read(old($Heap), $o, alloc) }
    read($Heap, this, _module.Map.Repr)[$Box($o)]
         && !read(old($Heap), this, _module.Map.Repr)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures true;
  ensures Map#Equal(read($Heap, this, _module.Map.M),
    Map#Build(read(old($Heap), this, _module.Map.M), key#0, val#0));
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f)
         || read(old($Heap), this, _module.Map.Repr)[$Box($o)]);
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
  free requires 9 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     &&
    _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
     &&
    read($Heap, this, _module.Map.Repr)[$Box(this)]
     && !read($Heap, this, _module.Map.Repr)[$Box(null)]
     && Set#Subset(read($Heap, this, _module.Map.Spine), read($Heap, this, _module.Map.Repr))
     && _module.Map.SpineValid(_module.Map$Key,
      _module.Map$Value,
      $LS($LZ),
      $Heap,
      read($Heap, this, _module.Map.Spine),
      read($Heap, this, _module.Map.head))
     && (forall k#2: Box ::
      { Map#Domain(read($Heap, this, _module.Map.M))[k#2] }
      $IsBox(k#2, _module.Map$Key)
         ==>
        Map#Domain(read($Heap, this, _module.Map.M))[k#2]
         ==> (exists n#10: ref ::
          { read($Heap, n#10, _module.Node.key) }
            { read($Heap, this, _module.Map.Spine)[$Box(n#10)] }
          $Is(n#10, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
             &&
            read($Heap, this, _module.Map.Spine)[$Box(n#10)]
             && read($Heap, n#10, _module.Node.key) == k#2))
     && (forall n#11: ref ::
      { read($Heap, n#11, _module.Node.val) }
        { read($Heap, n#11, _module.Node.key) }
        { read($Heap, this, _module.Map.Spine)[$Box(n#11)] }
      $Is(n#11, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
         ==> (read($Heap, this, _module.Map.Spine)[$Box(n#11)]
             ==> Map#Domain(read($Heap, this, _module.Map.M))[read($Heap, n#11, _module.Node.key)])
           && (read($Heap, this, _module.Map.Spine)[$Box(n#11)]
             ==> read($Heap, n#11, _module.Node.val)
               == Map#Elements(read($Heap, this, _module.Map.M))[read($Heap, n#11, _module.Node.key)]))
     && (forall n#12: ref, n'#4: ref ::
      { read($Heap, n'#4, _module.Node.key), read($Heap, n#12, _module.Node.key) }
        { read($Heap, n'#4, _module.Node.key), read($Heap, this, _module.Map.Spine)[$Box(n#12)] }
        { read($Heap, n#12, _module.Node.key), read($Heap, this, _module.Map.Spine)[$Box(n'#4)] }
        { read($Heap, this, _module.Map.Spine)[$Box(n'#4)], read($Heap, this, _module.Map.Spine)[$Box(n#12)] }
      $Is(n#12, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
           && $Is(n'#4, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
         ==>
        read($Heap, this, _module.Map.Spine)[$Box(n#12)]
           && read($Heap, this, _module.Map.Spine)[$Box(n'#4)]
           && n#12 != n'#4
         ==> read($Heap, n#12, _module.Node.key) != read($Heap, n'#4, _module.Node.key))
     && (forall n#13: ref ::
      { read($Heap, n#13, _module.Node.next) }
        { read($Heap, this, _module.Map.Spine)[$Box(n#13)] }
      $Is(n#13, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
         ==>
        read($Heap, this, _module.Map.Spine)[$Box(n#13)]
         ==> read($Heap, n#13, _module.Node.next) != read($Heap, this, _module.Map.head))
     && (forall n#14: ref, n'#5: ref ::
      { read($Heap, n'#5, _module.Node.next), read($Heap, n#14, _module.Node.next) }
        { read($Heap, n'#5, _module.Node.next), read($Heap, this, _module.Map.Spine)[$Box(n#14)] }
        { read($Heap, n#14, _module.Node.next), read($Heap, this, _module.Map.Spine)[$Box(n'#5)] }
        { read($Heap, this, _module.Map.Spine)[$Box(n'#5)], read($Heap, this, _module.Map.Spine)[$Box(n#14)] }
      $Is(n#14, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
           && $Is(n'#5, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
         ==>
        read($Heap, this, _module.Map.Spine)[$Box(n#14)]
           && read($Heap, this, _module.Map.Spine)[$Box(n'#5)]
           && read($Heap, n#14, _module.Node.next) == read($Heap, n'#5, _module.Node.next)
         ==> n#14 == n'#5);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this);
  ensures _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     ==> _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
       || read($Heap, this, _module.Map.Repr)[$Box(this)];
  ensures _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     ==> _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
       || !read($Heap, this, _module.Map.Repr)[$Box(null)];
  ensures _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     ==> _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
       || Set#Subset(read($Heap, this, _module.Map.Spine), read($Heap, this, _module.Map.Repr));
  ensures _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     ==> _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
       || (_module.Map.SpineValid#canCall(_module.Map$Key,
          _module.Map$Value,
          $Heap,
          read($Heap, this, _module.Map.Spine),
          read($Heap, this, _module.Map.head))
         ==> _module.Map.SpineValid(_module.Map$Key,
            _module.Map$Value,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.Map.Spine),
            read($Heap, this, _module.Map.head))
           ||
          (read($Heap, this, _module.Map.head) == null
             && Set#Equal(read($Heap, this, _module.Map.Spine), Set#Empty(): Set Box))
           || (
            read($Heap, this, _module.Map.head) != null
             && read($Heap, this, _module.Map.Spine)[$Box(read($Heap, this, _module.Map.head))]
             && Set#Equal(read($Heap, read($Heap, this, _module.Map.head), _module.Node.Spine),
              Set#Difference(read($Heap, this, _module.Map.Spine),
                Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Map.head)))))
             && _module.Map.SpineValid(_module.Map$Key,
              _module.Map$Value,
              $LS($LS($LZ)),
              $Heap,
              read($Heap, read($Heap, this, _module.Map.head), _module.Node.Spine),
              read($Heap, read($Heap, this, _module.Map.head), _module.Node.next))));
  ensures _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     ==> _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
       || (forall k#3: Box ::
        { Map#Domain(read($Heap, this, _module.Map.M))[k#3] }
        $IsBox(k#3, _module.Map$Key)
           ==>
          Map#Domain(read($Heap, this, _module.Map.M))[k#3]
           ==> (exists n#15: ref ::
            { read($Heap, n#15, _module.Node.key) }
              { read($Heap, this, _module.Map.Spine)[$Box(n#15)] }
            $Is(n#15, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
               &&
              read($Heap, this, _module.Map.Spine)[$Box(n#15)]
               && read($Heap, n#15, _module.Node.key) == k#3));
  ensures _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     ==> _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
       || (forall n#16: ref ::
        { read($Heap, n#16, _module.Node.val) }
          { read($Heap, n#16, _module.Node.key) }
          { read($Heap, this, _module.Map.Spine)[$Box(n#16)] }
        $Is(n#16, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
           ==> (read($Heap, this, _module.Map.Spine)[$Box(n#16)]
               ==> Map#Domain(read($Heap, this, _module.Map.M))[read($Heap, n#16, _module.Node.key)])
             && (read($Heap, this, _module.Map.Spine)[$Box(n#16)]
               ==> read($Heap, n#16, _module.Node.val)
                 == Map#Elements(read($Heap, this, _module.Map.M))[read($Heap, n#16, _module.Node.key)]));
  ensures _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     ==> _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
       || (forall n#17: ref, n'#6: ref ::
        { read($Heap, n'#6, _module.Node.key), read($Heap, n#17, _module.Node.key) }
          { read($Heap, n'#6, _module.Node.key), read($Heap, this, _module.Map.Spine)[$Box(n#17)] }
          { read($Heap, n#17, _module.Node.key), read($Heap, this, _module.Map.Spine)[$Box(n'#6)] }
          { read($Heap, this, _module.Map.Spine)[$Box(n'#6)], read($Heap, this, _module.Map.Spine)[$Box(n#17)] }
        $Is(n#17, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
             && $Is(n'#6, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
           ==>
          read($Heap, this, _module.Map.Spine)[$Box(n#17)]
             && read($Heap, this, _module.Map.Spine)[$Box(n'#6)]
             && n#17 != n'#6
           ==> read($Heap, n#17, _module.Node.key) != read($Heap, n'#6, _module.Node.key));
  ensures _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     ==> _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
       || (forall n#18: ref ::
        { read($Heap, n#18, _module.Node.next) }
          { read($Heap, this, _module.Map.Spine)[$Box(n#18)] }
        $Is(n#18, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
           ==>
          read($Heap, this, _module.Map.Spine)[$Box(n#18)]
           ==> read($Heap, n#18, _module.Node.next) != read($Heap, this, _module.Map.head));
  ensures _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     ==> _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
       || (forall n#19: ref, n'#7: ref ::
        { read($Heap, n'#7, _module.Node.next), read($Heap, n#19, _module.Node.next) }
          { read($Heap, n'#7, _module.Node.next), read($Heap, this, _module.Map.Spine)[$Box(n#19)] }
          { read($Heap, n#19, _module.Node.next), read($Heap, this, _module.Map.Spine)[$Box(n'#7)] }
          { read($Heap, this, _module.Map.Spine)[$Box(n'#7)], read($Heap, this, _module.Map.Spine)[$Box(n#19)] }
        $Is(n#19, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
             && $Is(n'#7, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
           ==>
          read($Heap, this, _module.Map.Spine)[$Box(n#19)]
             && read($Heap, this, _module.Map.Spine)[$Box(n'#7)]
             && read($Heap, n#19, _module.Node.next) == read($Heap, n'#7, _module.Node.next)
           ==> n#19 == n'#7);
  ensures (forall $o: ref ::
    { read(old($Heap), $o, alloc) }
    read($Heap, this, _module.Map.Repr)[$Box($o)]
         && !read(old($Heap), this, _module.Map.Repr)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures true;
  ensures Map#Equal(read($Heap, this, _module.Map.M),
    Map#Build(read(old($Heap), this, _module.Map.M), key#0, val#0));
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f)
         || read(old($Heap), this, _module.Map.Repr)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Map.Add(_module.Map$Key: Ty, _module.Map$Value: Ty, this: ref, key#0: Box, val#0: Box)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var prev#0: ref
     where $Is(prev#0, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
       && $IsAlloc(prev#0, Tclass._module.Node(_module.Map$Key, _module.Map$Value), $Heap);
  var p#0: ref
     where $Is(p#0, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
       && $IsAlloc(p#0, Tclass._module.Node(_module.Map$Key, _module.Map$Value), $Heap);
  var $rhs##0: ref
     where $Is($rhs##0, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
       && $IsAlloc($rhs##0, Tclass._module.Node(_module.Map$Key, _module.Map$Value), $Heap);
  var $rhs##1: ref
     where $Is($rhs##1, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
       && $IsAlloc($rhs##1, Tclass._module.Node(_module.Map$Key, _module.Map$Value), $Heap);
  var key##0: Box;
  var h#0_0: ref
     where $Is(h#0_0, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
       && $IsAlloc(h#0_0, Tclass._module.Node(_module.Map$Key, _module.Map$Value), $Heap);
  var $nw: ref;
  var key##0_0: Box;
  var val##0_0: Box;
  var $obj0: ref;
  var $obj1: ref;
  var $rhs#0_0: ref
     where $Is($rhs#0_0, Tclass._module.Node(_module.Map$Key, _module.Map$Value));
  var $rhs#0_1: Set Box
     where $Is($rhs#0_1, TSet(Tclass._module.Node(_module.Map$Key, _module.Map$Value)));
  var $obj2: ref;
  var $rhs#0_2: ref
     where $Is($rhs#0_2, Tclass._module.Node(_module.Map$Key, _module.Map$Value));
  var $rhs#0_3: Set Box
     where $Is($rhs#0_3, TSet(Tclass._module.Node(_module.Map$Key, _module.Map$Value)));
  var $rhs#0_4: Set Box where $Is($rhs#0_4, TSet(Tclass._System.object()));
  var $rhs#0_5: Map Box Box
     where $Is($rhs#0_5, TMap(_module.Map$Key, _module.Map$Value));
  var $rhs#0: Box where $IsBox($rhs#0, _module.Map$Value);
  var $rhs#1: Map Box Box where $Is($rhs#1, TMap(_module.Map$Key, _module.Map$Value));
  var s'#0: Set Box
     where $Is(s'#0, TSet(Tclass._module.Node(_module.Map$Key, _module.Map$Value)))
       && $IsAlloc(s'#0, TSet(Tclass._module.Node(_module.Map$Key, _module.Map$Value)), $Heap);
  var p'#0: ref
     where $Is(p'#0, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
       && $IsAlloc(p'#0, Tclass._module.Node(_module.Map$Key, _module.Map$Value), $Heap);
  var $rhs#2: Set Box
     where $Is($rhs#2, TSet(Tclass._module.Node(_module.Map$Key, _module.Map$Value)));
  var $rhs#3: ref
     where $Is($rhs#3, Tclass._module.Node(_module.Map$Key, _module.Map$Value));
  var $PreLoopHeap$loop#0: Heap;
  var $decr_init$loop#00: Set Box;
  var $w$loop#0: bool;
  var ##spine#0: Set Box;
  var ##n#0: ref;
  var ##spine#1: Set Box;
  var ##n#1: ref;
  var ##spine#2: Set Box;
  var ##n#2: ref;
  var ##spine#3: Set Box;
  var ##n#3: ref;
  var $decr$loop#00: Set Box;
  var $rhs#1_0: Set Box
     where $Is($rhs#1_0, TSet(Tclass._module.Node(_module.Map$Key, _module.Map$Value)));
  var $rhs#1_1: ref
     where $Is($rhs#1_1, Tclass._module.Node(_module.Map$Key, _module.Map$Value));

    // AddMethodImpl: Add, Impl$$_module.Map.Add
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc)
         ==> read($Heap, this, _module.Map.Repr)[$Box($o)]);
    assume {:captureState "b4.dfy(115,2): initial state"} true;
    $_reverifyPost := false;
    // ----- call statement ----- b4.dfy(116,29)
    assume true;
    assume true;
    // TrCallStmt: Adding lhs Microsoft.Dafny.AutoGhostIdentifierExpr with type Node<Key, Value>
    // TrCallStmt: Adding lhs Microsoft.Dafny.AutoGhostIdentifierExpr with type Node<Key, Value>
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    key##0 := key#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##0, $rhs##1 := Call$$_module.Map.FindIndex(_module.Map$Key, _module.Map$Value, this, key##0);
    // TrCallStmt: After ProcessCallStmt
    prev#0 := $rhs##0;
    p#0 := $rhs##1;
    assume {:captureState "b4.dfy(116,33)"} true;
    // ----- if statement ----- b4.dfy(117,5)
    assume true;
    if (p#0 == null)
    {
        // ----- assignment statement ----- b4.dfy(118,13)
        assume true;
        // ----- init call statement ----- b4.dfy(118,16)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        key##0_0 := key#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        val##0_0 := val#0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call $nw := Call$$_module.Node.__ctor(_module.Map$Key, _module.Map$Value, key##0_0, val##0_0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "b4.dfy(118,33)"} true;
        h#0_0 := $nw;
        assume {:captureState "b4.dfy(118,33)"} true;
        // ----- update statement ----- b4.dfy(119,23)
        assert h#0_0 != null;
        assume true;
        $obj0 := h#0_0;
        assert $_Frame[$obj0, _module.Node.next];
        assert h#0_0 != null;
        assume true;
        $obj1 := h#0_0;
        assert $_Frame[$obj1, _module.Node.Spine];
        assume true;
        $rhs#0_0 := read($Heap, this, _module.Map.head);
        assume true;
        $rhs#0_1 := read($Heap, this, _module.Map.Spine);
        $Heap := update($Heap, $obj0, _module.Node.next, $rhs#0_0);
        assume $IsGoodHeap($Heap);
        $Heap := update($Heap, $obj1, _module.Node.Spine, $rhs#0_1);
        assume $IsGoodHeap($Heap);
        assume {:captureState "b4.dfy(119,36)"} true;
        // ----- update statement ----- b4.dfy(120,25)
        assume true;
        $obj0 := this;
        assert $_Frame[$obj0, _module.Map.head];
        assume true;
        $obj1 := this;
        assert $_Frame[$obj1, _module.Map.Spine];
        assume true;
        $obj2 := this;
        assert $_Frame[$obj2, _module.Map.Repr];
        assume true;
        $rhs#0_2 := h#0_0;
        assume true;
        $rhs#0_3 := Set#Union(read($Heap, this, _module.Map.Spine),
          Set#UnionOne(Set#Empty(): Set Box, $Box(h#0_0)));
        assume true;
        $rhs#0_4 := Set#Union(read($Heap, this, _module.Map.Repr),
          Set#UnionOne(Set#Empty(): Set Box, $Box(h#0_0)));
        $Heap := update($Heap, $obj0, _module.Map.head, $rhs#0_2);
        assume $IsGoodHeap($Heap);
        $Heap := update($Heap, $obj1, _module.Map.Spine, $rhs#0_3);
        assume $IsGoodHeap($Heap);
        $Heap := update($Heap, $obj2, _module.Map.Repr, $rhs#0_4);
        assume $IsGoodHeap($Heap);
        assume {:captureState "b4.dfy(120,53)"} true;
        // ----- assignment statement ----- b4.dfy(121,9)
        assume true;
        assert $_Frame[this, _module.Map.M];
        assume true;
        $rhs#0_5 := Map#Build(read($Heap, this, _module.Map.M), key#0, val#0);
        $Heap := update($Heap, this, _module.Map.M, $rhs#0_5);
        assume $IsGoodHeap($Heap);
        assume {:captureState "b4.dfy(121,24)"} true;
    }
    else
    {
        // ----- assignment statement ----- b4.dfy(123,13)
        assert p#0 != null;
        assume true;
        assert $_Frame[p#0, _module.Node.val];
        assume true;
        $rhs#0 := val#0;
        $Heap := update($Heap, p#0, _module.Node.val, $rhs#0);
        assume $IsGoodHeap($Heap);
        assume {:captureState "b4.dfy(123,18)"} true;
        // ----- assignment statement ----- b4.dfy(124,9)
        assume true;
        assert $_Frame[this, _module.Map.M];
        assume true;
        $rhs#1 := Map#Build(read($Heap, this, _module.Map.M), key#0, val#0);
        $Heap := update($Heap, this, _module.Map.M, $rhs#1);
        assume $IsGoodHeap($Heap);
        assume {:captureState "b4.dfy(124,24)"} true;
        // ----- update statement ----- b4.dfy(128,24)
        assume true;
        assume true;
        assume true;
        $rhs#2 := read($Heap, this, _module.Map.Spine);
        assume true;
        $rhs#3 := read($Heap, this, _module.Map.head);
        s'#0 := $rhs#2;
        p'#0 := $rhs#3;
        assume {:captureState "b4.dfy(128,37)"} true;
        // ----- while statement ----- b4.dfy(129,7)
        // Assume Fuel Constant
        $PreLoopHeap$loop#0 := $Heap;
        $decr_init$loop#00 := s'#0;
        havoc $w$loop#0;
        while (true)
          free invariant $w$loop#0 ==> true;
          invariant $w$loop#0
             ==> $IsAlloc(p'#0, Tclass._module.Node(_module.Map$Key, _module.Map$Value), old($Heap));
          free invariant $w$loop#0
             ==> _module.Map.SpineValid#canCall(_module.Map$Key, _module.Map$Value, old($Heap), s'#0, p'#0);
          invariant $w$loop#0
             ==>
            _module.Map.SpineValid#canCall(_module.Map$Key, _module.Map$Value, old($Heap), s'#0, p'#0)
             ==> _module.Map.SpineValid(_module.Map$Key, _module.Map$Value, $LS($LZ), old($Heap), s'#0, p'#0)
               ||
              (p'#0 == null && Set#Equal(s'#0, Set#Empty(): Set Box))
               || (
                p'#0 != null
                 && s'#0[$Box(p'#0)]
                 && Set#Equal(read(old($Heap), p'#0, _module.Node.Spine),
                  Set#Difference(s'#0, Set#UnionOne(Set#Empty(): Set Box, $Box(p'#0))))
                 && _module.Map.SpineValid(_module.Map$Key,
                  _module.Map$Value,
                  $LS($LS($LZ)),
                  old($Heap),
                  read(old($Heap), p'#0, _module.Node.Spine),
                  read(old($Heap), p'#0, _module.Node.next)));
          free invariant $w$loop#0
             ==> _module.Map.SpineValid#canCall(_module.Map$Key, _module.Map$Value, old($Heap), s'#0, p'#0)
               &&
              _module.Map.SpineValid(_module.Map$Key, _module.Map$Value, $LS($LZ), old($Heap), s'#0, p'#0)
               && ((p'#0 == null && Set#Equal(s'#0, Set#Empty(): Set Box))
                 || (
                  p'#0 != null
                   && s'#0[$Box(p'#0)]
                   && Set#Equal(read(old($Heap), p'#0, _module.Node.Spine),
                    Set#Difference(s'#0, Set#UnionOne(Set#Empty(): Set Box, $Box(p'#0))))
                   && _module.Map.SpineValid(_module.Map$Key,
                    _module.Map$Value,
                    $LS($LZ),
                    old($Heap),
                    read(old($Heap), p'#0, _module.Node.Spine),
                    read(old($Heap), p'#0, _module.Node.next))));
          free invariant $w$loop#0
             ==> _module.Map.SpineValid#canCall(_module.Map$Key,
                _module.Map$Value,
                old($Heap),
                read(old($Heap), this, _module.Map.Spine),
                read(old($Heap), this, _module.Map.head))
               && (_module.Map.SpineValid(_module.Map$Key,
                  _module.Map$Value,
                  $LS($LZ),
                  old($Heap),
                  read(old($Heap), this, _module.Map.Spine),
                  read(old($Heap), this, _module.Map.head))
                 ==> _module.Map.SpineValid#canCall(_module.Map$Key,
                    _module.Map$Value,
                    $Heap,
                    read($Heap, this, _module.Map.Spine),
                    read($Heap, this, _module.Map.head))
                   && (!_module.Map.SpineValid(_module.Map$Key,
                      _module.Map$Value,
                      $LS($LZ),
                      $Heap,
                      read($Heap, this, _module.Map.Spine),
                      read($Heap, this, _module.Map.head))
                     ==> _module.Map.SpineValid#canCall(_module.Map$Key, _module.Map$Value, $Heap, s'#0, p'#0)));
          invariant $w$loop#0
             ==>
            _module.Map.SpineValid(_module.Map$Key,
              _module.Map$Value,
              $LS($LZ),
              old($Heap),
              read(old($Heap), this, _module.Map.Spine),
              read(old($Heap), this, _module.Map.head))
             ==> _module.Map.SpineValid(_module.Map$Key,
                _module.Map$Value,
                $LS($LS($LZ)),
                $Heap,
                read($Heap, this, _module.Map.Spine),
                read($Heap, this, _module.Map.head))
               || !_module.Map.SpineValid(_module.Map$Key, _module.Map$Value, $LS($LS($LZ)), $Heap, s'#0, p'#0);
          free invariant (forall<alpha> $o: ref, $f: Field alpha ::
            { read($Heap, $o, $f) }
            $o != null
               ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0, $o, $f)
                 || read(old($Heap), this, _module.Map.Repr)[$Box($o)]);
          free invariant $HeapSuccGhost($PreLoopHeap$loop#0, $Heap);
          free invariant (forall<alpha> $o: ref, $f: Field alpha ::
            { read($Heap, $o, $f) }
            $o != null && read($PreLoopHeap$loop#0, $o, alloc)
               ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0, $o, $f) || $_Frame[$o, $f]);
          free invariant Set#Subset(s'#0, $decr_init$loop#00)
             && (Set#Equal(s'#0, $decr_init$loop#00) ==> true);
        {
            assume {:captureState "b4.dfy(129,6): after some loop iterations"} true;
            if (!$w$loop#0)
            {
                assume true;
                assume $IsAlloc(p'#0, Tclass._module.Node(_module.Map$Key, _module.Map$Value), old($Heap));
                ##spine#0 := s'#0;
                ##n#0 := p'#0;
                assert $IsAlloc(s'#0, TSet(Tclass._module.Node(_module.Map$Key, _module.Map$Value)), old($Heap));
                assert $IsAlloc(p'#0, Tclass._module.Node(_module.Map$Key, _module.Map$Value), old($Heap));
                assume _module.Map.SpineValid#canCall(_module.Map$Key, _module.Map$Value, old($Heap), s'#0, p'#0);
                assume _module.Map.SpineValid#canCall(_module.Map$Key, _module.Map$Value, old($Heap), s'#0, p'#0);
                assume _module.Map.SpineValid(_module.Map$Key, _module.Map$Value, $LS($LZ), old($Heap), s'#0, p'#0);
                assert $IsAlloc(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value), old($Heap));
                assert $IsAlloc(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value), old($Heap));
                ##spine#1 := read(old($Heap), this, _module.Map.Spine);
                ##n#1 := read(old($Heap), this, _module.Map.head);
                assert $IsAlloc(read(old($Heap), this, _module.Map.Spine),
                  TSet(Tclass._module.Node(_module.Map$Key, _module.Map$Value)),
                  old($Heap));
                assert $IsAlloc(read(old($Heap), this, _module.Map.head),
                  Tclass._module.Node(_module.Map$Key, _module.Map$Value),
                  old($Heap));
                assume _module.Map.SpineValid#canCall(_module.Map$Key,
                  _module.Map$Value,
                  old($Heap),
                  read(old($Heap), this, _module.Map.Spine),
                  read(old($Heap), this, _module.Map.head));
                if (_module.Map.SpineValid(_module.Map$Key,
                  _module.Map$Value,
                  $LS($LZ),
                  old($Heap),
                  read(old($Heap), this, _module.Map.Spine),
                  read(old($Heap), this, _module.Map.head)))
                {
                    ##spine#2 := read($Heap, this, _module.Map.Spine);
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##spine#2, TSet(Tclass._module.Node(_module.Map$Key, _module.Map$Value)), $Heap);
                    ##n#2 := read($Heap, this, _module.Map.head);
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##n#2, Tclass._module.Node(_module.Map$Key, _module.Map$Value), $Heap);
                    assume _module.Map.SpineValid#canCall(_module.Map$Key,
                      _module.Map$Value,
                      $Heap,
                      read($Heap, this, _module.Map.Spine),
                      read($Heap, this, _module.Map.head));
                    if (!_module.Map.SpineValid(_module.Map$Key,
                      _module.Map$Value,
                      $LS($LZ),
                      $Heap,
                      read($Heap, this, _module.Map.Spine),
                      read($Heap, this, _module.Map.head)))
                    {
                        ##spine#3 := s'#0;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##spine#3, TSet(Tclass._module.Node(_module.Map$Key, _module.Map$Value)), $Heap);
                        ##n#3 := p'#0;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##n#3, Tclass._module.Node(_module.Map$Key, _module.Map$Value), $Heap);
                        assume _module.Map.SpineValid#canCall(_module.Map$Key, _module.Map$Value, $Heap, s'#0, p'#0);
                    }
                }

                assume _module.Map.SpineValid#canCall(_module.Map$Key,
                    _module.Map$Value,
                    old($Heap),
                    read(old($Heap), this, _module.Map.Spine),
                    read(old($Heap), this, _module.Map.head))
                   && (_module.Map.SpineValid(_module.Map$Key,
                      _module.Map$Value,
                      $LS($LZ),
                      old($Heap),
                      read(old($Heap), this, _module.Map.Spine),
                      read(old($Heap), this, _module.Map.head))
                     ==> _module.Map.SpineValid#canCall(_module.Map$Key,
                        _module.Map$Value,
                        $Heap,
                        read($Heap, this, _module.Map.Spine),
                        read($Heap, this, _module.Map.head))
                       && (!_module.Map.SpineValid(_module.Map$Key,
                          _module.Map$Value,
                          $LS($LZ),
                          $Heap,
                          read($Heap, this, _module.Map.Spine),
                          read($Heap, this, _module.Map.head))
                         ==> _module.Map.SpineValid#canCall(_module.Map$Key, _module.Map$Value, $Heap, s'#0, p'#0)));
                assume _module.Map.SpineValid(_module.Map$Key,
                    _module.Map$Value,
                    $LS($LZ),
                    old($Heap),
                    read(old($Heap), this, _module.Map.Spine),
                    read(old($Heap), this, _module.Map.head))
                   ==> _module.Map.SpineValid(_module.Map$Key,
                      _module.Map$Value,
                      $LS($LZ),
                      $Heap,
                      read($Heap, this, _module.Map.Spine),
                      read($Heap, this, _module.Map.head))
                     || !_module.Map.SpineValid(_module.Map$Key, _module.Map$Value, $LS($LZ), $Heap, s'#0, p'#0);
                assume true;
                assume false;
            }

            assume true;
            if (p'#0 == null)
            {
                break;
            }

            $decr$loop#00 := s'#0;
            // ----- update statement ----- b4.dfy(135,16)
            assume true;
            assume true;
            assert p'#0 != null;
            assume true;
            $rhs#1_0 := read($Heap, p'#0, _module.Node.Spine);
            assert p'#0 != null;
            assume true;
            $rhs#1_1 := read($Heap, p'#0, _module.Node.next);
            s'#0 := $rhs#1_0;
            p'#0 := $rhs#1_1;
            assume {:captureState "b4.dfy(135,35)"} true;
            // ----- loop termination check ----- b4.dfy(129,7)
            assert Set#Subset(s'#0, $decr$loop#00) && !Set#Subset($decr$loop#00, s'#0);
            assume true;
            assume _module.Map.SpineValid#canCall(_module.Map$Key, _module.Map$Value, old($Heap), s'#0, p'#0);
            assume _module.Map.SpineValid#canCall(_module.Map$Key,
                _module.Map$Value,
                old($Heap),
                read(old($Heap), this, _module.Map.Spine),
                read(old($Heap), this, _module.Map.head))
               && (_module.Map.SpineValid(_module.Map$Key,
                  _module.Map$Value,
                  $LS($LZ),
                  old($Heap),
                  read(old($Heap), this, _module.Map.Spine),
                  read(old($Heap), this, _module.Map.head))
                 ==> _module.Map.SpineValid#canCall(_module.Map$Key,
                    _module.Map$Value,
                    $Heap,
                    read($Heap, this, _module.Map.Spine),
                    read($Heap, this, _module.Map.head))
                   && (!_module.Map.SpineValid(_module.Map$Key,
                      _module.Map$Value,
                      $LS($LZ),
                      $Heap,
                      read($Heap, this, _module.Map.Spine),
                      read($Heap, this, _module.Map.head))
                     ==> _module.Map.SpineValid#canCall(_module.Map$Key, _module.Map$Value, $Heap, s'#0, p'#0)));
        }
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
  free requires 10 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.Map.Remove(_module.Map$Key: Ty, _module.Map$Value: Ty, this: ref, key#0: Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var k#0: Box;

    // AddMethodImpl: Remove, CheckWellformed$$_module.Map.Remove
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc)
         ==> read($Heap, this, _module.Map.Repr)[$Box($o)]);
    assume {:captureState "b4.dfy(141,9): initial state"} true;
    assume _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this);
    assume _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this);
    havoc $Heap;
    assume (forall<alpha> $o: ref, $f: Field alpha ::
      { read($Heap, $o, $f) }
      $o != null && read(old($Heap), $o, alloc)
         ==> read($Heap, $o, $f) == read(old($Heap), $o, $f)
           || read(old($Heap), this, _module.Map.Repr)[$Box($o)]);
    assume $HeapSucc(old($Heap), $Heap);
    assume {:captureState "b4.dfy(144,20): post-state"} true;
    assume _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this);
    assume _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this);
    assert $IsAlloc(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value), old($Heap));
    assume (forall $o: ref ::
      { read(old($Heap), $o, alloc) }
      read($Heap, this, _module.Map.Repr)[$Box($o)]
           && !read(old($Heap), this, _module.Map.Repr)[$Box($o)]
         ==> $o != null && !read(old($Heap), $o, alloc));
    havoc k#0;
    assume $IsBox(k#0, _module.Map$Key);
    // Begin Comprehension WF check
    assert $IsAlloc(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value), old($Heap));
    if (Map#Domain(read(old($Heap), this, _module.Map.M))[k#0])
    {
    }

    if (Map#Domain(read(old($Heap), this, _module.Map.M))[k#0] && k#0 != key#0)
    {
        assert $IsAlloc(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value), old($Heap));
        assert Map#Domain(read(old($Heap), this, _module.Map.M))[k#0];
    }

    // End Comprehension WF check
    assume Map#Equal(read($Heap, this, _module.Map.M),
      Map#Glue((lambda $y#0: Box ::
          $IsBox($y#0, _module.Map$Key)
             &&
            Map#Domain(read(old($Heap), this, _module.Map.M))[$y#0]
             && $y#0 != key#0),
        (lambda $y#0: Box :: Map#Elements(read(old($Heap), this, _module.Map.M))[$y#0]),
        TMap(_module.Map$Key, _module.Map$Value)));
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
       || read($Heap, this, _module.Map.Repr)[$Box(this)];
  requires _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     ==> _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
       || !read($Heap, this, _module.Map.Repr)[$Box(null)];
  requires _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     ==> _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
       || Set#Subset(read($Heap, this, _module.Map.Spine), read($Heap, this, _module.Map.Repr));
  requires _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     ==> _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
       || (_module.Map.SpineValid#canCall(_module.Map$Key,
          _module.Map$Value,
          $Heap,
          read($Heap, this, _module.Map.Spine),
          read($Heap, this, _module.Map.head))
         ==> _module.Map.SpineValid(_module.Map$Key,
            _module.Map$Value,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.Map.Spine),
            read($Heap, this, _module.Map.head))
           ||
          (read($Heap, this, _module.Map.head) == null
             && Set#Equal(read($Heap, this, _module.Map.Spine), Set#Empty(): Set Box))
           || (
            read($Heap, this, _module.Map.head) != null
             && read($Heap, this, _module.Map.Spine)[$Box(read($Heap, this, _module.Map.head))]
             && Set#Equal(read($Heap, read($Heap, this, _module.Map.head), _module.Node.Spine),
              Set#Difference(read($Heap, this, _module.Map.Spine),
                Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Map.head)))))
             && _module.Map.SpineValid(_module.Map$Key,
              _module.Map$Value,
              $LS($LS($LZ)),
              $Heap,
              read($Heap, read($Heap, this, _module.Map.head), _module.Node.Spine),
              read($Heap, read($Heap, this, _module.Map.head), _module.Node.next))));
  requires _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     ==> _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
       || (forall k#2: Box ::
        { Map#Domain(read($Heap, this, _module.Map.M))[k#2] }
        $IsBox(k#2, _module.Map$Key)
           ==>
          Map#Domain(read($Heap, this, _module.Map.M))[k#2]
           ==> (exists n#0: ref ::
            { read($Heap, n#0, _module.Node.key) }
              { read($Heap, this, _module.Map.Spine)[$Box(n#0)] }
            $Is(n#0, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
               &&
              read($Heap, this, _module.Map.Spine)[$Box(n#0)]
               && read($Heap, n#0, _module.Node.key) == k#2));
  requires _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     ==> _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
       || (forall n#1: ref ::
        { read($Heap, n#1, _module.Node.val) }
          { read($Heap, n#1, _module.Node.key) }
          { read($Heap, this, _module.Map.Spine)[$Box(n#1)] }
        $Is(n#1, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
           ==> (read($Heap, this, _module.Map.Spine)[$Box(n#1)]
               ==> Map#Domain(read($Heap, this, _module.Map.M))[read($Heap, n#1, _module.Node.key)])
             && (read($Heap, this, _module.Map.Spine)[$Box(n#1)]
               ==> read($Heap, n#1, _module.Node.val)
                 == Map#Elements(read($Heap, this, _module.Map.M))[read($Heap, n#1, _module.Node.key)]));
  requires _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     ==> _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
       || (forall n#2: ref, n'#0: ref ::
        { read($Heap, n'#0, _module.Node.key), read($Heap, n#2, _module.Node.key) }
          { read($Heap, n'#0, _module.Node.key), read($Heap, this, _module.Map.Spine)[$Box(n#2)] }
          { read($Heap, n#2, _module.Node.key), read($Heap, this, _module.Map.Spine)[$Box(n'#0)] }
          { read($Heap, this, _module.Map.Spine)[$Box(n'#0)], read($Heap, this, _module.Map.Spine)[$Box(n#2)] }
        $Is(n#2, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
             && $Is(n'#0, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
           ==>
          read($Heap, this, _module.Map.Spine)[$Box(n#2)]
             && read($Heap, this, _module.Map.Spine)[$Box(n'#0)]
             && n#2 != n'#0
           ==> read($Heap, n#2, _module.Node.key) != read($Heap, n'#0, _module.Node.key));
  requires _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     ==> _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
       || (forall n#3: ref ::
        { read($Heap, n#3, _module.Node.next) }
          { read($Heap, this, _module.Map.Spine)[$Box(n#3)] }
        $Is(n#3, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
           ==>
          read($Heap, this, _module.Map.Spine)[$Box(n#3)]
           ==> read($Heap, n#3, _module.Node.next) != read($Heap, this, _module.Map.head));
  requires _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     ==> _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
       || (forall n#4: ref, n'#1: ref ::
        { read($Heap, n'#1, _module.Node.next), read($Heap, n#4, _module.Node.next) }
          { read($Heap, n'#1, _module.Node.next), read($Heap, this, _module.Map.Spine)[$Box(n#4)] }
          { read($Heap, n#4, _module.Node.next), read($Heap, this, _module.Map.Spine)[$Box(n'#1)] }
          { read($Heap, this, _module.Map.Spine)[$Box(n'#1)], read($Heap, this, _module.Map.Spine)[$Box(n#4)] }
        $Is(n#4, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
             && $Is(n'#1, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
           ==>
          read($Heap, this, _module.Map.Spine)[$Box(n#4)]
             && read($Heap, this, _module.Map.Spine)[$Box(n'#1)]
             && read($Heap, n#4, _module.Node.next) == read($Heap, n'#1, _module.Node.next)
           ==> n#4 == n'#1);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this);
  free ensures _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     &&
    _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
     &&
    read($Heap, this, _module.Map.Repr)[$Box(this)]
     && !read($Heap, this, _module.Map.Repr)[$Box(null)]
     && Set#Subset(read($Heap, this, _module.Map.Spine), read($Heap, this, _module.Map.Repr))
     && _module.Map.SpineValid(_module.Map$Key,
      _module.Map$Value,
      $LS($LZ),
      $Heap,
      read($Heap, this, _module.Map.Spine),
      read($Heap, this, _module.Map.head))
     && (forall k#3: Box ::
      { Map#Domain(read($Heap, this, _module.Map.M))[k#3] }
      $IsBox(k#3, _module.Map$Key)
         ==>
        Map#Domain(read($Heap, this, _module.Map.M))[k#3]
         ==> (exists n#5: ref ::
          { read($Heap, n#5, _module.Node.key) }
            { read($Heap, this, _module.Map.Spine)[$Box(n#5)] }
          $Is(n#5, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
             &&
            read($Heap, this, _module.Map.Spine)[$Box(n#5)]
             && read($Heap, n#5, _module.Node.key) == k#3))
     && (forall n#6: ref ::
      { read($Heap, n#6, _module.Node.val) }
        { read($Heap, n#6, _module.Node.key) }
        { read($Heap, this, _module.Map.Spine)[$Box(n#6)] }
      $Is(n#6, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
         ==> (read($Heap, this, _module.Map.Spine)[$Box(n#6)]
             ==> Map#Domain(read($Heap, this, _module.Map.M))[read($Heap, n#6, _module.Node.key)])
           && (read($Heap, this, _module.Map.Spine)[$Box(n#6)]
             ==> read($Heap, n#6, _module.Node.val)
               == Map#Elements(read($Heap, this, _module.Map.M))[read($Heap, n#6, _module.Node.key)]))
     && (forall n#7: ref, n'#2: ref ::
      { read($Heap, n'#2, _module.Node.key), read($Heap, n#7, _module.Node.key) }
        { read($Heap, n'#2, _module.Node.key), read($Heap, this, _module.Map.Spine)[$Box(n#7)] }
        { read($Heap, n#7, _module.Node.key), read($Heap, this, _module.Map.Spine)[$Box(n'#2)] }
        { read($Heap, this, _module.Map.Spine)[$Box(n'#2)], read($Heap, this, _module.Map.Spine)[$Box(n#7)] }
      $Is(n#7, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
           && $Is(n'#2, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
         ==>
        read($Heap, this, _module.Map.Spine)[$Box(n#7)]
           && read($Heap, this, _module.Map.Spine)[$Box(n'#2)]
           && n#7 != n'#2
         ==> read($Heap, n#7, _module.Node.key) != read($Heap, n'#2, _module.Node.key))
     && (forall n#8: ref ::
      { read($Heap, n#8, _module.Node.next) }
        { read($Heap, this, _module.Map.Spine)[$Box(n#8)] }
      $Is(n#8, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
         ==>
        read($Heap, this, _module.Map.Spine)[$Box(n#8)]
         ==> read($Heap, n#8, _module.Node.next) != read($Heap, this, _module.Map.head))
     && (forall n#9: ref, n'#3: ref ::
      { read($Heap, n'#3, _module.Node.next), read($Heap, n#9, _module.Node.next) }
        { read($Heap, n'#3, _module.Node.next), read($Heap, this, _module.Map.Spine)[$Box(n#9)] }
        { read($Heap, n#9, _module.Node.next), read($Heap, this, _module.Map.Spine)[$Box(n'#3)] }
        { read($Heap, this, _module.Map.Spine)[$Box(n'#3)], read($Heap, this, _module.Map.Spine)[$Box(n#9)] }
      $Is(n#9, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
           && $Is(n'#3, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
         ==>
        read($Heap, this, _module.Map.Spine)[$Box(n#9)]
           && read($Heap, this, _module.Map.Spine)[$Box(n'#3)]
           && read($Heap, n#9, _module.Node.next) == read($Heap, n'#3, _module.Node.next)
         ==> n#9 == n'#3);
  ensures (forall $o: ref ::
    { read(old($Heap), $o, alloc) }
    read($Heap, this, _module.Map.Repr)[$Box($o)]
         && !read(old($Heap), this, _module.Map.Repr)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures (forall k#1: Box ::
    { Map#Elements(read(old($Heap), this, _module.Map.M))[k#1] }
      { Map#Domain(read(old($Heap), this, _module.Map.M))[k#1] }
    true);
  ensures Map#Equal(read($Heap, this, _module.Map.M),
    Map#Glue((lambda $y#1: Box ::
        $IsBox($y#1, _module.Map$Key)
           &&
          Map#Domain(read(old($Heap), this, _module.Map.M))[$y#1]
           && $y#1 != key#0),
      (lambda $y#1: Box :: Map#Elements(read(old($Heap), this, _module.Map.M))[$y#1]),
      TMap(_module.Map$Key, _module.Map$Value)));
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f)
         || read(old($Heap), this, _module.Map.Repr)[$Box($o)]);
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
  free requires 10 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     &&
    _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
     &&
    read($Heap, this, _module.Map.Repr)[$Box(this)]
     && !read($Heap, this, _module.Map.Repr)[$Box(null)]
     && Set#Subset(read($Heap, this, _module.Map.Spine), read($Heap, this, _module.Map.Repr))
     && _module.Map.SpineValid(_module.Map$Key,
      _module.Map$Value,
      $LS($LZ),
      $Heap,
      read($Heap, this, _module.Map.Spine),
      read($Heap, this, _module.Map.head))
     && (forall k#4: Box ::
      { Map#Domain(read($Heap, this, _module.Map.M))[k#4] }
      $IsBox(k#4, _module.Map$Key)
         ==>
        Map#Domain(read($Heap, this, _module.Map.M))[k#4]
         ==> (exists n#10: ref ::
          { read($Heap, n#10, _module.Node.key) }
            { read($Heap, this, _module.Map.Spine)[$Box(n#10)] }
          $Is(n#10, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
             &&
            read($Heap, this, _module.Map.Spine)[$Box(n#10)]
             && read($Heap, n#10, _module.Node.key) == k#4))
     && (forall n#11: ref ::
      { read($Heap, n#11, _module.Node.val) }
        { read($Heap, n#11, _module.Node.key) }
        { read($Heap, this, _module.Map.Spine)[$Box(n#11)] }
      $Is(n#11, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
         ==> (read($Heap, this, _module.Map.Spine)[$Box(n#11)]
             ==> Map#Domain(read($Heap, this, _module.Map.M))[read($Heap, n#11, _module.Node.key)])
           && (read($Heap, this, _module.Map.Spine)[$Box(n#11)]
             ==> read($Heap, n#11, _module.Node.val)
               == Map#Elements(read($Heap, this, _module.Map.M))[read($Heap, n#11, _module.Node.key)]))
     && (forall n#12: ref, n'#4: ref ::
      { read($Heap, n'#4, _module.Node.key), read($Heap, n#12, _module.Node.key) }
        { read($Heap, n'#4, _module.Node.key), read($Heap, this, _module.Map.Spine)[$Box(n#12)] }
        { read($Heap, n#12, _module.Node.key), read($Heap, this, _module.Map.Spine)[$Box(n'#4)] }
        { read($Heap, this, _module.Map.Spine)[$Box(n'#4)], read($Heap, this, _module.Map.Spine)[$Box(n#12)] }
      $Is(n#12, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
           && $Is(n'#4, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
         ==>
        read($Heap, this, _module.Map.Spine)[$Box(n#12)]
           && read($Heap, this, _module.Map.Spine)[$Box(n'#4)]
           && n#12 != n'#4
         ==> read($Heap, n#12, _module.Node.key) != read($Heap, n'#4, _module.Node.key))
     && (forall n#13: ref ::
      { read($Heap, n#13, _module.Node.next) }
        { read($Heap, this, _module.Map.Spine)[$Box(n#13)] }
      $Is(n#13, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
         ==>
        read($Heap, this, _module.Map.Spine)[$Box(n#13)]
         ==> read($Heap, n#13, _module.Node.next) != read($Heap, this, _module.Map.head))
     && (forall n#14: ref, n'#5: ref ::
      { read($Heap, n'#5, _module.Node.next), read($Heap, n#14, _module.Node.next) }
        { read($Heap, n'#5, _module.Node.next), read($Heap, this, _module.Map.Spine)[$Box(n#14)] }
        { read($Heap, n#14, _module.Node.next), read($Heap, this, _module.Map.Spine)[$Box(n'#5)] }
        { read($Heap, this, _module.Map.Spine)[$Box(n'#5)], read($Heap, this, _module.Map.Spine)[$Box(n#14)] }
      $Is(n#14, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
           && $Is(n'#5, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
         ==>
        read($Heap, this, _module.Map.Spine)[$Box(n#14)]
           && read($Heap, this, _module.Map.Spine)[$Box(n'#5)]
           && read($Heap, n#14, _module.Node.next) == read($Heap, n'#5, _module.Node.next)
         ==> n#14 == n'#5);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this);
  ensures _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     ==> _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
       || read($Heap, this, _module.Map.Repr)[$Box(this)];
  ensures _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     ==> _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
       || !read($Heap, this, _module.Map.Repr)[$Box(null)];
  ensures _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     ==> _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
       || Set#Subset(read($Heap, this, _module.Map.Spine), read($Heap, this, _module.Map.Repr));
  ensures _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     ==> _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
       || (_module.Map.SpineValid#canCall(_module.Map$Key,
          _module.Map$Value,
          $Heap,
          read($Heap, this, _module.Map.Spine),
          read($Heap, this, _module.Map.head))
         ==> _module.Map.SpineValid(_module.Map$Key,
            _module.Map$Value,
            $LS($LZ),
            $Heap,
            read($Heap, this, _module.Map.Spine),
            read($Heap, this, _module.Map.head))
           ||
          (read($Heap, this, _module.Map.head) == null
             && Set#Equal(read($Heap, this, _module.Map.Spine), Set#Empty(): Set Box))
           || (
            read($Heap, this, _module.Map.head) != null
             && read($Heap, this, _module.Map.Spine)[$Box(read($Heap, this, _module.Map.head))]
             && Set#Equal(read($Heap, read($Heap, this, _module.Map.head), _module.Node.Spine),
              Set#Difference(read($Heap, this, _module.Map.Spine),
                Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Map.head)))))
             && _module.Map.SpineValid(_module.Map$Key,
              _module.Map$Value,
              $LS($LS($LZ)),
              $Heap,
              read($Heap, read($Heap, this, _module.Map.head), _module.Node.Spine),
              read($Heap, read($Heap, this, _module.Map.head), _module.Node.next))));
  ensures _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     ==> _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
       || (forall k#5: Box ::
        { Map#Domain(read($Heap, this, _module.Map.M))[k#5] }
        $IsBox(k#5, _module.Map$Key)
           ==>
          Map#Domain(read($Heap, this, _module.Map.M))[k#5]
           ==> (exists n#15: ref ::
            { read($Heap, n#15, _module.Node.key) }
              { read($Heap, this, _module.Map.Spine)[$Box(n#15)] }
            $Is(n#15, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
               &&
              read($Heap, this, _module.Map.Spine)[$Box(n#15)]
               && read($Heap, n#15, _module.Node.key) == k#5));
  ensures _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     ==> _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
       || (forall n#16: ref ::
        { read($Heap, n#16, _module.Node.val) }
          { read($Heap, n#16, _module.Node.key) }
          { read($Heap, this, _module.Map.Spine)[$Box(n#16)] }
        $Is(n#16, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
           ==> (read($Heap, this, _module.Map.Spine)[$Box(n#16)]
               ==> Map#Domain(read($Heap, this, _module.Map.M))[read($Heap, n#16, _module.Node.key)])
             && (read($Heap, this, _module.Map.Spine)[$Box(n#16)]
               ==> read($Heap, n#16, _module.Node.val)
                 == Map#Elements(read($Heap, this, _module.Map.M))[read($Heap, n#16, _module.Node.key)]));
  ensures _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     ==> _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
       || (forall n#17: ref, n'#6: ref ::
        { read($Heap, n'#6, _module.Node.key), read($Heap, n#17, _module.Node.key) }
          { read($Heap, n'#6, _module.Node.key), read($Heap, this, _module.Map.Spine)[$Box(n#17)] }
          { read($Heap, n#17, _module.Node.key), read($Heap, this, _module.Map.Spine)[$Box(n'#6)] }
          { read($Heap, this, _module.Map.Spine)[$Box(n'#6)], read($Heap, this, _module.Map.Spine)[$Box(n#17)] }
        $Is(n#17, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
             && $Is(n'#6, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
           ==>
          read($Heap, this, _module.Map.Spine)[$Box(n#17)]
             && read($Heap, this, _module.Map.Spine)[$Box(n'#6)]
             && n#17 != n'#6
           ==> read($Heap, n#17, _module.Node.key) != read($Heap, n'#6, _module.Node.key));
  ensures _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     ==> _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
       || (forall n#18: ref ::
        { read($Heap, n#18, _module.Node.next) }
          { read($Heap, this, _module.Map.Spine)[$Box(n#18)] }
        $Is(n#18, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
           ==>
          read($Heap, this, _module.Map.Spine)[$Box(n#18)]
           ==> read($Heap, n#18, _module.Node.next) != read($Heap, this, _module.Map.head));
  ensures _module.Map.Valid#canCall(_module.Map$Key, _module.Map$Value, $Heap, this)
     ==> _module.Map.Valid(_module.Map$Key, _module.Map$Value, $Heap, this)
       || (forall n#19: ref, n'#7: ref ::
        { read($Heap, n'#7, _module.Node.next), read($Heap, n#19, _module.Node.next) }
          { read($Heap, n'#7, _module.Node.next), read($Heap, this, _module.Map.Spine)[$Box(n#19)] }
          { read($Heap, n#19, _module.Node.next), read($Heap, this, _module.Map.Spine)[$Box(n'#7)] }
          { read($Heap, this, _module.Map.Spine)[$Box(n'#7)], read($Heap, this, _module.Map.Spine)[$Box(n#19)] }
        $Is(n#19, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
             && $Is(n'#7, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
           ==>
          read($Heap, this, _module.Map.Spine)[$Box(n#19)]
             && read($Heap, this, _module.Map.Spine)[$Box(n'#7)]
             && read($Heap, n#19, _module.Node.next) == read($Heap, n'#7, _module.Node.next)
           ==> n#19 == n'#7);
  ensures (forall $o: ref ::
    { read(old($Heap), $o, alloc) }
    read($Heap, this, _module.Map.Repr)[$Box($o)]
         && !read(old($Heap), this, _module.Map.Repr)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures (forall k#1: Box ::
    { Map#Elements(read(old($Heap), this, _module.Map.M))[k#1] }
      { Map#Domain(read(old($Heap), this, _module.Map.M))[k#1] }
    true);
  ensures Map#Equal(read($Heap, this, _module.Map.M),
    Map#Glue((lambda $y#2: Box ::
        $IsBox($y#2, _module.Map$Key)
           &&
          Map#Domain(read(old($Heap), this, _module.Map.M))[$y#2]
           && $y#2 != key#0),
      (lambda $y#2: Box :: Map#Elements(read(old($Heap), this, _module.Map.M))[$y#2]),
      TMap(_module.Map$Key, _module.Map$Value)));
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f)
         || read(old($Heap), this, _module.Map.Repr)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Map.Remove(_module.Map$Key: Ty, _module.Map$Value: Ty, this: ref, key#0: Box)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var prev#0: ref
     where $Is(prev#0, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
       && $IsAlloc(prev#0, Tclass._module.Node(_module.Map$Key, _module.Map$Value), $Heap);
  var p#0: ref
     where $Is(p#0, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
       && $IsAlloc(p#0, Tclass._module.Node(_module.Map$Key, _module.Map$Value), $Heap);
  var $rhs##0: ref
     where $Is($rhs##0, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
       && $IsAlloc($rhs##0, Tclass._module.Node(_module.Map$Key, _module.Map$Value), $Heap);
  var $rhs##1: ref
     where $Is($rhs##1, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
       && $IsAlloc($rhs##1, Tclass._module.Node(_module.Map$Key, _module.Map$Value), $Heap);
  var key##0: Box;
  var $obj0: ref;
  var $obj1: ref;
  var $rhs#0_0_0: Set Box
     where $Is($rhs#0_0_0, TSet(Tclass._module.Node(_module.Map$Key, _module.Map$Value)));
  var $rhs#0_0_1: ref
     where $Is($rhs#0_0_1, Tclass._module.Node(_module.Map$Key, _module.Map$Value));
  var $rhs#0_0_2: Map Box Box
     where $Is($rhs#0_0_2, TMap(_module.Map$Key, _module.Map$Value));
  var k#0_0_0: Box;
  var k#0_0_2: Box;
  var n#0_0_0_0: ref
     where $Is(n#0_0_0_0, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
       && $IsAlloc(n#0_0_0_0, Tclass._module.Node(_module.Map$Key, _module.Map$Value), $Heap);
  var spine##0_0: Set Box;
  var p##0_0: ref;
  var $rhs#0_0: ref
     where $Is($rhs#0_0, Tclass._module.Node(_module.Map$Key, _module.Map$Value));
  var n#0_0: ref;
  var n#0_1: ref;
  var $prevHeap: Heap;
  var $rhs#0_1: Set Box
     where $Is($rhs#0_1, TSet(Tclass._module.Node(_module.Map$Key, _module.Map$Value)));
  var $rhs#0_2: Map Box Box
     where $Is($rhs#0_2, TMap(_module.Map$Key, _module.Map$Value));
  var k#0_0: Box;
  var k#0_2: Box;
  var n#0_3: ref
     where $Is(n#0_3, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
       && $IsAlloc(n#0_3, Tclass._module.Node(_module.Map$Key, _module.Map$Value), $Heap);
  var n#0_6: ref;
  var spine##0_1: Set Box;
  var p##0_1: ref;

    // AddMethodImpl: Remove, Impl$$_module.Map.Remove
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc)
         ==> read($Heap, this, _module.Map.Repr)[$Box($o)]);
    assume {:captureState "b4.dfy(146,2): initial state"} true;
    $_reverifyPost := false;
    // ----- call statement ----- b4.dfy(147,29)
    assume true;
    assume true;
    // TrCallStmt: Adding lhs Microsoft.Dafny.AutoGhostIdentifierExpr with type Node<Key, Value>
    // TrCallStmt: Adding lhs Microsoft.Dafny.AutoGhostIdentifierExpr with type Node<Key, Value>
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    key##0 := key#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##0, $rhs##1 := Call$$_module.Map.FindIndex(_module.Map$Key, _module.Map$Value, this, key##0);
    // TrCallStmt: After ProcessCallStmt
    prev#0 := $rhs##0;
    p#0 := $rhs##1;
    assume {:captureState "b4.dfy(147,33)"} true;
    // ----- if statement ----- b4.dfy(148,5)
    assume true;
    if (p#0 != null)
    {
        // ----- if statement ----- b4.dfy(149,7)
        assume true;
        if (prev#0 == null)
        {
            // ----- update statement ----- b4.dfy(150,21)
            assume true;
            $obj0 := this;
            assert $_Frame[$obj0, _module.Map.Spine];
            assume true;
            $obj1 := this;
            assert $_Frame[$obj1, _module.Map.head];
            assert read($Heap, this, _module.Map.head) != null;
            assume true;
            $rhs#0_0_0 := read($Heap, read($Heap, this, _module.Map.head), _module.Node.Spine);
            assert read($Heap, this, _module.Map.head) != null;
            assume true;
            $rhs#0_0_1 := read($Heap, read($Heap, this, _module.Map.head), _module.Node.next);
            $Heap := update($Heap, $obj0, _module.Map.Spine, $rhs#0_0_0);
            assume $IsGoodHeap($Heap);
            $Heap := update($Heap, $obj1, _module.Map.head, $rhs#0_0_1);
            assume $IsGoodHeap($Heap);
            assume {:captureState "b4.dfy(150,44)"} true;
            // ----- assignment statement ----- b4.dfy(151,11)
            assume true;
            assert $_Frame[this, _module.Map.M];
            havoc k#0_0_0;
            assume $IsBox(k#0_0_0, _module.Map$Key);
            // Begin Comprehension WF check
            if (Map#Domain(read($Heap, this, _module.Map.M))[k#0_0_0])
            {
            }

            if (Map#Domain(read($Heap, this, _module.Map.M))[k#0_0_0] && k#0_0_0 != key#0)
            {
                assert Map#Domain(read($Heap, this, _module.Map.M))[k#0_0_0];
            }

            // End Comprehension WF check
            assume (forall k#0_0_1: Box ::
              { Map#Elements(read($Heap, this, _module.Map.M))[k#0_0_1] }
                { Map#Domain(read($Heap, this, _module.Map.M))[k#0_0_1] }
              true);
            $rhs#0_0_2 := Map#Glue((lambda $y#0_0_0: Box ::
                $IsBox($y#0_0_0, _module.Map$Key)
                   &&
                  Map#Domain(read($Heap, this, _module.Map.M))[$y#0_0_0]
                   && $y#0_0_0 != key#0),
              (lambda $y#0_0_0: Box ::
                Map#Elements(read($Heap, this, _module.Map.M))[$y#0_0_0]),
              TMap(_module.Map$Key, _module.Map$Value));
            $Heap := update($Heap, this, _module.Map.M, $rhs#0_0_2);
            assume $IsGoodHeap($Heap);
            assume {:captureState "b4.dfy(151,47)"} true;
            // ----- forall statement (proof) ----- b4.dfy(152,9)
            if (*)
            {
                // Assume Fuel Constant
                havoc k#0_0_2;
                assume $IsBox(k#0_0_2, _module.Map$Key);
                assume true;
                assume Map#Domain(read($Heap, this, _module.Map.M))[k#0_0_2];
                // ----- if statement ----- b4.dfy(155,11)
                assume true;
                if (k#0_0_2 != key#0)
                {
                    // ----- assert statement ----- b4.dfy(156,13)
                    assert $IsAlloc(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value), old($Heap));
                    assume true;
                    assert Map#Domain(read(old($Heap), this, _module.Map.M))[k#0_0_2];
                    // ----- assign-such-that statement ----- b4.dfy(157,19)
                    assume true;
                    havoc n#0_0_0_0;
                    assert $IsAlloc(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value), old($Heap));
                    if (read(old($Heap), this, _module.Map.Spine)[$Box(n#0_0_0_0)])
                    {
                        assert {:subsumption 0} n#0_0_0_0 != null;
                        assert $IsAlloc(n#0_0_0_0, Tclass._module.Node(_module.Map$Key, _module.Map$Value), old($Heap));
                    }

                    assume true;
                    assert ($Is(null, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
                         &&
                        read(old($Heap), this, _module.Map.Spine)[$Box(null)]
                         && read(old($Heap), null, _module.Node.key) == k#0_0_2)
                       || (exists $as#n0_0_0_0#0_0_0_0: ref ::
                        $Is($as#n0_0_0_0#0_0_0_0, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
                           &&
                          read(old($Heap), this, _module.Map.Spine)[$Box($as#n0_0_0_0#0_0_0_0)]
                           && read(old($Heap), $as#n0_0_0_0#0_0_0_0, _module.Node.key) == k#0_0_2);
                    assume read(old($Heap), this, _module.Map.Spine)[$Box(n#0_0_0_0)]
                       && read(old($Heap), n#0_0_0_0, _module.Node.key) == k#0_0_2;
                    assume {:captureState "b4.dfy(157,55)"} true;
                    // ----- assert statement ----- b4.dfy(158,13)
                    assert {:subsumption 0} n#0_0_0_0 != null;
                    assert {:subsumption 0} n#0_0_0_0 != null;
                    assert $IsAlloc(n#0_0_0_0, Tclass._module.Node(_module.Map$Key, _module.Map$Value), old($Heap));
                    assume true;
                    assert read($Heap, n#0_0_0_0, _module.Node.key)
                       == read(old($Heap), n#0_0_0_0, _module.Node.key);
                }
                else
                {
                }

                assert (exists n#0_0_0: ref ::
                  { read($Heap, n#0_0_0, _module.Node.key) }
                    { read($Heap, this, _module.Map.Spine)[$Box(n#0_0_0)] }
                  $Is(n#0_0_0, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
                     &&
                    read($Heap, this, _module.Map.Spine)[$Box(n#0_0_0)]
                     && read($Heap, n#0_0_0, _module.Node.key) == k#0_0_2);
                assume false;
            }
            else
            {
                assume (forall k#0_0_3: Box ::
                  { Map#Domain(read($Heap, this, _module.Map.M))[k#0_0_3] }
                  $IsBox(k#0_0_3, _module.Map$Key)
                       && Map#Domain(read($Heap, this, _module.Map.M))[k#0_0_3]
                     ==> (exists n#0_0_1: ref ::
                      { read($Heap, n#0_0_1, _module.Node.key) }
                        { read($Heap, this, _module.Map.Spine)[$Box(n#0_0_1)] }
                      $Is(n#0_0_1, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
                         &&
                        read($Heap, this, _module.Map.Spine)[$Box(n#0_0_1)]
                         && read($Heap, n#0_0_1, _module.Node.key) == k#0_0_3));
            }

            assume {:captureState "b4.dfy(160,8)"} true;
        }
        else
        {
            // ----- call statement ----- b4.dfy(162,24)
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            // ProcessCallStmt: CheckSubrange
            spine##0_0 := read($Heap, this, _module.Map.Spine);
            assume true;
            // ProcessCallStmt: CheckSubrange
            p##0_0 := read($Heap, this, _module.Map.head);
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call Call$$_module.Map.SpineValidSplit(_module.Map$Key, _module.Map$Value, this, spine##0_0, p##0_0);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "b4.dfy(162,36)"} true;
            // ----- assignment statement ----- b4.dfy(164,19)
            assert prev#0 != null;
            assume true;
            assert $_Frame[prev#0, _module.Node.next];
            assert p#0 != null;
            assume true;
            $rhs#0_0 := read($Heap, p#0, _module.Node.next);
            $Heap := update($Heap, prev#0, _module.Node.next, $rhs#0_0);
            assume $IsGoodHeap($Heap);
            assume {:captureState "b4.dfy(164,27)"} true;
            // ----- forall statement (assign) ----- b4.dfy(165,9)
            if (*)
            {
                // Assume Fuel Constant
                havoc n#0_0;
                assume $Is(n#0_0, Tclass._module.Node(_module.Map$Key, _module.Map$Value));
                assume true;
                assume read($Heap, this, _module.Map.Spine)[$Box(n#0_0)];
                assert {:subsumption 0} n#0_0 != null;
                assume true;
                assert $_Frame[n#0_0, _module.Node.Spine];
                assert {:subsumption 0} n#0_0 != null;
                assume true;
                havoc n#0_1;
                assume $Is(n#0_1, Tclass._module.Node(_module.Map$Key, _module.Map$Value));
                assume read($Heap, this, _module.Map.Spine)[$Box(n#0_1)];
                assume n#0_0 != n#0_1;
                assert n#0_0 != n#0_1
                   || _module.Node.Spine != _module.Node.Spine
                   || Set#Difference(read($Heap, n#0_0, _module.Node.Spine),
                      Set#UnionOne(Set#Empty(): Set Box, $Box(p#0)))
                     == Set#Difference(read($Heap, n#0_1, _module.Node.Spine),
                      Set#UnionOne(Set#Empty(): Set Box, $Box(p#0)));
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
                     || (exists n#0_2: ref ::
                      $Is(n#0_2, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
                         && read($prevHeap, this, _module.Map.Spine)[$Box(n#0_2)]
                         && $o == n#0_2
                         && $f == _module.Node.Spine));
                assume (forall n#inv#0_0: ref ::
                  { read($Heap, n#inv#0_0, _module.Node.Spine) }
                  $Is(n#inv#0_0, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
                       && read($prevHeap, this, _module.Map.Spine)[$Box(n#inv#0_0)]
                     ==> read($Heap, n#inv#0_0, _module.Node.Spine)
                       == Set#Difference(read($prevHeap, n#inv#0_0, _module.Node.Spine),
                        Set#UnionOne(Set#Empty(): Set Box, $Box(p#0))));
            }

            assume {:captureState "b4.dfy(167,8)"} true;
            // ----- assignment statement ----- b4.dfy(168,15)
            assume true;
            assert $_Frame[this, _module.Map.Spine];
            assume true;
            $rhs#0_1 := Set#Difference(read($Heap, this, _module.Map.Spine),
              Set#UnionOne(Set#Empty(): Set Box, $Box(p#0)));
            $Heap := update($Heap, this, _module.Map.Spine, $rhs#0_1);
            assume $IsGoodHeap($Heap);
            assume {:captureState "b4.dfy(168,28)"} true;
            // ----- assignment statement ----- b4.dfy(169,11)
            assume true;
            assert $_Frame[this, _module.Map.M];
            havoc k#0_0;
            assume $IsBox(k#0_0, _module.Map$Key);
            // Begin Comprehension WF check
            if (Map#Domain(read($Heap, this, _module.Map.M))[k#0_0])
            {
            }

            if (Map#Domain(read($Heap, this, _module.Map.M))[k#0_0] && k#0_0 != key#0)
            {
                assert Map#Domain(read($Heap, this, _module.Map.M))[k#0_0];
            }

            // End Comprehension WF check
            assume (forall k#0_1: Box ::
              { Map#Elements(read($Heap, this, _module.Map.M))[k#0_1] }
                { Map#Domain(read($Heap, this, _module.Map.M))[k#0_1] }
              true);
            $rhs#0_2 := Map#Glue((lambda $y#0_0: Box ::
                $IsBox($y#0_0, _module.Map$Key)
                   &&
                  Map#Domain(read($Heap, this, _module.Map.M))[$y#0_0]
                   && $y#0_0 != key#0),
              (lambda $y#0_0: Box :: Map#Elements(read($Heap, this, _module.Map.M))[$y#0_0]),
              TMap(_module.Map$Key, _module.Map$Value));
            $Heap := update($Heap, this, _module.Map.M, $rhs#0_2);
            assume $IsGoodHeap($Heap);
            assume {:captureState "b4.dfy(169,47)"} true;
            // ----- forall statement (proof) ----- b4.dfy(171,9)
            if (*)
            {
                // Assume Fuel Constant
                havoc k#0_2;
                assume $IsBox(k#0_2, _module.Map$Key);
                assume true;
                assume Map#Domain(read($Heap, this, _module.Map.M))[k#0_2];
                // ----- assert statement ----- b4.dfy(174,11)
                assert $IsAlloc(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value), old($Heap));
                if (Map#Domain(read(old($Heap), this, _module.Map.M))[k#0_2])
                {
                }

                assume true;
                assert {:subsumption 0} Map#Domain(read(old($Heap), this, _module.Map.M))[k#0_2];
                assert {:subsumption 0} k#0_2 != key#0;
                assume Map#Domain(read(old($Heap), this, _module.Map.M))[k#0_2] && k#0_2 != key#0;
                // ----- assign-such-that statement ----- b4.dfy(175,17)
                assume true;
                havoc n#0_3;
                assert $IsAlloc(this, Tclass._module.Map(_module.Map$Key, _module.Map$Value), old($Heap));
                if (read(old($Heap), this, _module.Map.Spine)[$Box(n#0_3)])
                {
                    assert {:subsumption 0} n#0_3 != null;
                    assert $IsAlloc(n#0_3, Tclass._module.Node(_module.Map$Key, _module.Map$Value), old($Heap));
                }

                assume true;
                assert ($Is(null, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
                     &&
                    read(old($Heap), this, _module.Map.Spine)[$Box(null)]
                     && read(old($Heap), null, _module.Node.key) == k#0_2)
                   || (exists $as#n0_0#0_0: ref ::
                    $Is($as#n0_0#0_0, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
                       &&
                      read(old($Heap), this, _module.Map.Spine)[$Box($as#n0_0#0_0)]
                       && read(old($Heap), $as#n0_0#0_0, _module.Node.key) == k#0_2);
                assume read(old($Heap), this, _module.Map.Spine)[$Box(n#0_3)]
                   && read(old($Heap), n#0_3, _module.Node.key) == k#0_2;
                assume {:captureState "b4.dfy(175,53)"} true;
                // ----- assert statement ----- b4.dfy(176,11)
                assert {:subsumption 0} n#0_3 != null;
                assert {:subsumption 0} n#0_3 != null;
                assert $IsAlloc(n#0_3, Tclass._module.Node(_module.Map$Key, _module.Map$Value), old($Heap));
                assume true;
                assert read($Heap, n#0_3, _module.Node.key)
                   == read(old($Heap), n#0_3, _module.Node.key);
                assert (exists n#0_4: ref ::
                  { read($Heap, n#0_4, _module.Node.key) }
                    { read($Heap, this, _module.Map.Spine)[$Box(n#0_4)] }
                  $Is(n#0_4, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
                     &&
                    read($Heap, this, _module.Map.Spine)[$Box(n#0_4)]
                     && read($Heap, n#0_4, _module.Node.key) == k#0_2);
                assume false;
            }
            else
            {
                assume (forall k#0_3: Box ::
                  { Map#Domain(read($Heap, this, _module.Map.M))[k#0_3] }
                  $IsBox(k#0_3, _module.Map$Key)
                       && Map#Domain(read($Heap, this, _module.Map.M))[k#0_3]
                     ==> (exists n#0_5: ref ::
                      { read($Heap, n#0_5, _module.Node.key) }
                        { read($Heap, this, _module.Map.Spine)[$Box(n#0_5)] }
                      $Is(n#0_5, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
                         &&
                        read($Heap, this, _module.Map.Spine)[$Box(n#0_5)]
                         && read($Heap, n#0_5, _module.Node.key) == k#0_3));
            }

            assume {:captureState "b4.dfy(177,8)"} true;
            // ----- forall statement (proof) ----- b4.dfy(179,9)
            if (*)
            {
                // Assume Fuel Constant
                havoc n#0_6;
                assume $Is(n#0_6, Tclass._module.Node(_module.Map$Key, _module.Map$Value));
                assume true;
                assume read($Heap, this, _module.Map.Spine)[$Box(n#0_6)];
                // ----- if statement ----- b4.dfy(182,11)
                if (n#0_6 != prev#0)
                {
                    assert n#0_6 != null;
                }

                assume true;
                if (n#0_6 != prev#0 && read($Heap, n#0_6, _module.Node.next) != null)
                {
                    // ----- assert statement ----- b4.dfy(183,13)
                    assert {:subsumption 0} n#0_6 != null;
                    assert {:subsumption 0} n#0_6 != null;
                    if (read($Heap, n#0_6, _module.Node.Spine)[$Box(read($Heap, n#0_6, _module.Node.next))])
                    {
                        assert {:subsumption 0} n#0_6 != null;
                        assert {:subsumption 0} read($Heap, n#0_6, _module.Node.next) != null;
                        assert {:subsumption 0} n#0_6 != null;
                        assert {:subsumption 0} n#0_6 != null;
                    }

                    assume true;
                    assert {:subsumption 0} read($Heap, n#0_6, _module.Node.Spine)[$Box(read($Heap, n#0_6, _module.Node.next))];
                    assert {:subsumption 0} Set#Equal(read($Heap, read($Heap, n#0_6, _module.Node.next), _module.Node.Spine),
                      Set#Difference(read($Heap, n#0_6, _module.Node.Spine),
                        Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, n#0_6, _module.Node.next)))));
                    assume read($Heap, n#0_6, _module.Node.Spine)[$Box(read($Heap, n#0_6, _module.Node.next))]
                       && Set#Equal(read($Heap, read($Heap, n#0_6, _module.Node.next), _module.Node.Spine),
                        Set#Difference(read($Heap, n#0_6, _module.Node.Spine),
                          Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, n#0_6, _module.Node.next)))));
                }
                else
                {
                }

                assert _module.Map.SpineValid__One#canCall(_module.Map$Key,
                    _module.Map$Value,
                    $Heap,
                    read($Heap, n#0_6, _module.Node.Spine),
                    read($Heap, n#0_6, _module.Node.next))
                   ==> _module.Map.SpineValid__One(_module.Map$Key,
                      _module.Map$Value,
                      $Heap,
                      read($Heap, n#0_6, _module.Node.Spine),
                      read($Heap, n#0_6, _module.Node.next))
                     ||
                    (read($Heap, n#0_6, _module.Node.next) == null
                       && Set#Equal(read($Heap, n#0_6, _module.Node.Spine), Set#Empty(): Set Box))
                     || (
                      read($Heap, n#0_6, _module.Node.next) != null
                       && read($Heap, n#0_6, _module.Node.Spine)[$Box(read($Heap, n#0_6, _module.Node.next))]
                       && Set#Equal(read($Heap, read($Heap, n#0_6, _module.Node.next), _module.Node.Spine),
                        Set#Difference(read($Heap, n#0_6, _module.Node.Spine),
                          Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, n#0_6, _module.Node.next))))));
                assume false;
            }
            else
            {
                assume (forall n#0_7: ref ::
                  { read($Heap, n#0_7, _module.Node.next) }
                    { read($Heap, n#0_7, _module.Node.Spine) }
                    { read($Heap, this, _module.Map.Spine)[$Box(n#0_7)] }
                  $Is(n#0_7, Tclass._module.Node(_module.Map$Key, _module.Map$Value))
                       && read($Heap, this, _module.Map.Spine)[$Box(n#0_7)]
                     ==> _module.Map.SpineValid__One(_module.Map$Key,
                      _module.Map$Value,
                      $Heap,
                      read($Heap, n#0_7, _module.Node.Spine),
                      read($Heap, n#0_7, _module.Node.next)));
            }

            assume {:captureState "b4.dfy(185,8)"} true;
            // ----- call statement ----- b4.dfy(186,26)
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            // ProcessCallStmt: CheckSubrange
            spine##0_1 := read($Heap, this, _module.Map.Spine);
            assume true;
            // ProcessCallStmt: CheckSubrange
            p##0_1 := read($Heap, this, _module.Map.head);
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call Call$$_module.Map.SpineValidCombine(_module.Map$Key, _module.Map$Value, this, spine##0_1, p##0_1);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "b4.dfy(186,38)"} true;
        }
    }
    else
    {
    }
}



const unique class._module.Node: ClassName;

// Node: Class $Is
axiom (forall _module.Node$Key: Ty, _module.Node$Value: Ty, $o: ref ::
  { $Is($o, Tclass._module.Node(_module.Node$Key, _module.Node$Value)) }
  $Is($o, Tclass._module.Node(_module.Node$Key, _module.Node$Value))
     <==> $o == null
       || dtype($o) == Tclass._module.Node(_module.Node$Key, _module.Node$Value));

// Node: Class $IsAlloc
axiom (forall _module.Node$Key: Ty, _module.Node$Value: Ty, $o: ref, $h: Heap ::
  { $IsAlloc($o, Tclass._module.Node(_module.Node$Key, _module.Node$Value), $h) }
  $IsAlloc($o, Tclass._module.Node(_module.Node$Key, _module.Node$Value), $h)
     <==> $o == null || read($h, $o, alloc));

const _module.Node.key: Field Box;

// Node.key: Allocation axiom
axiom (forall _module.Node$Key: Ty, _module.Node$Value: Ty, $h: Heap, $o: ref ::
  { read($h, $o, _module.Node.key), Tclass._module.Node(_module.Node$Key, _module.Node$Value) }
  $IsGoodHeap($h)
       && $o != null
       && dtype($o) == Tclass._module.Node(_module.Node$Key, _module.Node$Value)
     ==> $IsBox(read($h, $o, _module.Node.key), _module.Node$Key)
       && (read($h, $o, alloc)
         ==> $IsAllocBox(read($h, $o, _module.Node.key), _module.Node$Key, $h)));

const _module.Node.val: Field Box;

// Node.val: Allocation axiom
axiom (forall _module.Node$Key: Ty, _module.Node$Value: Ty, $h: Heap, $o: ref ::
  { read($h, $o, _module.Node.val), Tclass._module.Node(_module.Node$Key, _module.Node$Value) }
  $IsGoodHeap($h)
       && $o != null
       && dtype($o) == Tclass._module.Node(_module.Node$Key, _module.Node$Value)
     ==> $IsBox(read($h, $o, _module.Node.val), _module.Node$Value)
       && (read($h, $o, alloc)
         ==> $IsAllocBox(read($h, $o, _module.Node.val), _module.Node$Value, $h)));

const _module.Node.next: Field ref;

// Node.next: Allocation axiom
axiom (forall _module.Node$Key: Ty, _module.Node$Value: Ty, $h: Heap, $o: ref ::
  { read($h, $o, _module.Node.next), Tclass._module.Node(_module.Node$Key, _module.Node$Value) }
  $IsGoodHeap($h)
       && $o != null
       && dtype($o) == Tclass._module.Node(_module.Node$Key, _module.Node$Value)
     ==> $Is(read($h, $o, _module.Node.next),
        Tclass._module.Node(_module.Node$Key, _module.Node$Value))
       && (read($h, $o, alloc)
         ==> $IsAlloc(read($h, $o, _module.Node.next),
          Tclass._module.Node(_module.Node$Key, _module.Node$Value),
          $h)));

const _module.Node.Spine: Field (Set Box);

// Node.Spine: Allocation axiom
axiom (forall _module.Node$Key: Ty, _module.Node$Value: Ty, $h: Heap, $o: ref ::
  { read($h, $o, _module.Node.Spine), Tclass._module.Node(_module.Node$Key, _module.Node$Value) }
  $IsGoodHeap($h)
       && $o != null
       && dtype($o) == Tclass._module.Node(_module.Node$Key, _module.Node$Value)
     ==> $Is(read($h, $o, _module.Node.Spine),
        TSet(Tclass._module.Node(_module.Node$Key, _module.Node$Value)))
       && (read($h, $o, alloc)
         ==> $IsAlloc(read($h, $o, _module.Node.Spine),
          TSet(Tclass._module.Node(_module.Node$Key, _module.Node$Value)),
          $h)));

procedure CheckWellformed$$_module.Node.__ctor(_module.Node$Key: Ty,
    _module.Node$Value: Ty,
    this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Node(_module.Node$Key, _module.Node$Value))
         && $IsAlloc(this, Tclass._module.Node(_module.Node$Key, _module.Node$Value), $Heap),
    key#0: Box
       where $IsBox(key#0, _module.Node$Key) && $IsAllocBox(key#0, _module.Node$Key, $Heap),
    val#0: Box
       where $IsBox(val#0, _module.Node$Value)
         && $IsAllocBox(val#0, _module.Node$Value, $Heap));
  free requires 8 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.Node.__ctor(_module.Node$Key: Ty,
    _module.Node$Value: Ty,
    key#0: Box
       where $IsBox(key#0, _module.Node$Key) && $IsAllocBox(key#0, _module.Node$Key, $Heap),
    val#0: Box
       where $IsBox(val#0, _module.Node$Value)
         && $IsAllocBox(val#0, _module.Node$Value, $Heap))
   returns (this: ref
       where this != null
         &&
        $Is(this, Tclass._module.Node(_module.Node$Key, _module.Node$Value))
         && $IsAlloc(this, Tclass._module.Node(_module.Node$Key, _module.Node$Value), $Heap));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures read($Heap, this, _module.Node.key) == key#0;
  ensures read($Heap, this, _module.Node.val) == val#0;
  // constructor allocates the object
  ensures !read(old($Heap), this, alloc);
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Node.__ctor(_module.Node$Key: Ty,
    _module.Node$Value: Ty,
    key#0: Box
       where $IsBox(key#0, _module.Node$Key) && $IsAllocBox(key#0, _module.Node$Key, $Heap),
    val#0: Box
       where $IsBox(val#0, _module.Node$Value)
         && $IsAllocBox(val#0, _module.Node$Value, $Heap))
   returns (this: ref, $_reverifyPost: bool);
  free requires 8 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures read($Heap, this, _module.Node.key) == key#0;
  ensures read($Heap, this, _module.Node.val) == val#0;
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Node.__ctor(_module.Node$Key: Ty, _module.Node$Value: Ty, key#0: Box, val#0: Box)
   returns (this: ref, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var this.key: Box;
  var this.val: Box;
  var this.next: ref;
  var this.Spine: Set Box;
  var defass#this.key: bool;
  var defass#this.val: bool;
  var $obj0: ref;
  var $obj1: ref;
  var $rhs#0: Box where $IsBox($rhs#0, _module.Node$Key);
  var $rhs#1: Box where $IsBox($rhs#1, _module.Node$Value);

    // AddMethodImpl: _ctor, Impl$$_module.Node.__ctor
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "b4.dfy(200,2): initial state"} true;
    $_reverifyPost := false;
    // ----- divided block before new; ----- b4.dfy(200,3)
    // ----- update statement ----- b4.dfy(201,24)
    assume true;
    $obj0 := this;
    assume true;
    $obj1 := this;
    assume true;
    $rhs#0 := key#0;
    assume true;
    $rhs#1 := val#0;
    this.key := $rhs#0;
    defass#this.key := true;
    this.val := $rhs#1;
    defass#this.val := true;
    assume {:captureState "b4.dfy(201,34)"} true;
    // ----- new; ----- b4.dfy(200,3)
    assert defass#this.key;
    assert defass#this.val;
    assume this != null
       &&
      !read($Heap, this, alloc)
       && dtype(this) == Tclass._module.Node(_module.Node$Key, _module.Node$Value);
    assume read($Heap, this, _module.Node.key) == this.key;
    assume read($Heap, this, _module.Node.val) == this.val;
    assume read($Heap, this, _module.Node.next) == this.next;
    assume read($Heap, this, _module.Node.Spine) == this.Spine;
    $Heap := update($Heap, this, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    // ----- divided block after new; ----- b4.dfy(200,3)
}



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
axiom (forall a#5#0#0: Box ::
  { #_module.Maybe.Some(a#5#0#0) }
  DatatypeCtorId(#_module.Maybe.Some(a#5#0#0)) == ##_module.Maybe.Some);

function _module.Maybe.Some_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType ::
  { _module.Maybe.Some_q(d) }
  _module.Maybe.Some_q(d) <==> DatatypeCtorId(d) == ##_module.Maybe.Some);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType ::
  { _module.Maybe.Some_q(d) }
  _module.Maybe.Some_q(d)
     ==> (exists a#6#0#0: Box :: d == #_module.Maybe.Some(a#6#0#0)));

// Constructor $Is
axiom (forall _module.Maybe$T: Ty, a#7#0#0: Box ::
  { $Is(#_module.Maybe.Some(a#7#0#0), Tclass._module.Maybe(_module.Maybe$T)) }
  $Is(#_module.Maybe.Some(a#7#0#0), Tclass._module.Maybe(_module.Maybe$T))
     <==> $IsBox(a#7#0#0, _module.Maybe$T));

// Constructor $IsAlloc
axiom (forall _module.Maybe$T: Ty, a#8#0#0: Box, $h: Heap ::
  { $IsAlloc(#_module.Maybe.Some(a#8#0#0), Tclass._module.Maybe(_module.Maybe$T), $h) }
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Maybe.Some(a#8#0#0), Tclass._module.Maybe(_module.Maybe$T), $h)
       <==> $IsAllocBox(a#8#0#0, _module.Maybe$T, $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, _module.Maybe$T: Ty, $h: Heap ::
  { $IsAllocBox(_module.Maybe.get(d), _module.Maybe$T, $h) }
  $IsGoodHeap($h)
       &&
      _module.Maybe.Some_q(d)
       && $IsAlloc(d, Tclass._module.Maybe(_module.Maybe$T), $h)
     ==> $IsAllocBox(_module.Maybe.get(d), _module.Maybe$T, $h));

// Constructor literal
axiom (forall a#9#0#0: Box ::
  { #_module.Maybe.Some(Lit(a#9#0#0)) }
  #_module.Maybe.Some(Lit(a#9#0#0)) == Lit(#_module.Maybe.Some(a#9#0#0)));

function _module.Maybe.get(DatatypeType) : Box;

// Constructor injectivity
axiom (forall a#10#0#0: Box ::
  { #_module.Maybe.Some(a#10#0#0) }
  _module.Maybe.get(#_module.Maybe.Some(a#10#0#0)) == a#10#0#0);

// Inductive rank
axiom (forall a#11#0#0: Box ::
  { #_module.Maybe.Some(a#11#0#0) }
  BoxRank(a#11#0#0) < DtRank(#_module.Maybe.Some(a#11#0#0)));

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

const unique field$M: NameFamily;

const unique field$Repr: NameFamily;

const unique field$head: NameFamily;

const unique field$Spine: NameFamily;

const unique field$key: NameFamily;

const unique field$val: NameFamily;

const unique field$next: NameFamily;