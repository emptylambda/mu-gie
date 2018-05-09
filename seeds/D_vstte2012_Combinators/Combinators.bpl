// Dafny 2.0.0.00922 technical preview 0
// Command Line Options: /compile:0 /noVerify /print:Combinators.bpl Combinators.dfy

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

const unique class._module.Term: ClassName;

// Constructor function declaration
function #_module.Term.S() : DatatypeType;

const unique ##_module.Term.S: DtCtorId;

// Constructor identifier
axiom DatatypeCtorId(#_module.Term.S()) == ##_module.Term.S;

function _module.Term.S_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType ::
  { _module.Term.S_q(d) }
  _module.Term.S_q(d) <==> DatatypeCtorId(d) == ##_module.Term.S);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType ::
  { _module.Term.S_q(d) }
  _module.Term.S_q(d) ==> d == #_module.Term.S());

function Tclass._module.Term() : Ty;

// Tclass._module.Term Tag
axiom Tag(Tclass._module.Term()) == Tagclass._module.Term;

const unique Tagclass._module.Term: TyTag;

// Box/unbox axiom for Tclass._module.Term
axiom (forall bx: Box ::
  { $IsBox(bx, Tclass._module.Term()) }
  $IsBox(bx, Tclass._module.Term())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.Term()));

// Constructor $Is
axiom $Is(#_module.Term.S(), Tclass._module.Term());

// Constructor $IsAlloc
axiom (forall $h: Heap ::
  { $IsAlloc(#_module.Term.S(), Tclass._module.Term(), $h) }
  $IsGoodHeap($h) ==> $IsAlloc(#_module.Term.S(), Tclass._module.Term(), $h));

// Constructor literal
axiom #_module.Term.S() == Lit(#_module.Term.S());

// Constructor function declaration
function #_module.Term.K() : DatatypeType;

const unique ##_module.Term.K: DtCtorId;

// Constructor identifier
axiom DatatypeCtorId(#_module.Term.K()) == ##_module.Term.K;

function _module.Term.K_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType ::
  { _module.Term.K_q(d) }
  _module.Term.K_q(d) <==> DatatypeCtorId(d) == ##_module.Term.K);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType ::
  { _module.Term.K_q(d) }
  _module.Term.K_q(d) ==> d == #_module.Term.K());

// Constructor $Is
axiom $Is(#_module.Term.K(), Tclass._module.Term());

// Constructor $IsAlloc
axiom (forall $h: Heap ::
  { $IsAlloc(#_module.Term.K(), Tclass._module.Term(), $h) }
  $IsGoodHeap($h) ==> $IsAlloc(#_module.Term.K(), Tclass._module.Term(), $h));

// Constructor literal
axiom #_module.Term.K() == Lit(#_module.Term.K());

// Constructor function declaration
function #_module.Term.Apply(DatatypeType, DatatypeType) : DatatypeType;

const unique ##_module.Term.Apply: DtCtorId;

// Constructor identifier
axiom (forall a#24#0#0: DatatypeType, a#24#1#0: DatatypeType ::
  { #_module.Term.Apply(a#24#0#0, a#24#1#0) }
  DatatypeCtorId(#_module.Term.Apply(a#24#0#0, a#24#1#0)) == ##_module.Term.Apply);

function _module.Term.Apply_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType ::
  { _module.Term.Apply_q(d) }
  _module.Term.Apply_q(d) <==> DatatypeCtorId(d) == ##_module.Term.Apply);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType ::
  { _module.Term.Apply_q(d) }
  _module.Term.Apply_q(d)
     ==> (exists a#25#0#0: DatatypeType, a#25#1#0: DatatypeType ::
      d == #_module.Term.Apply(a#25#0#0, a#25#1#0)));

// Constructor $Is
axiom (forall a#26#0#0: DatatypeType, a#26#1#0: DatatypeType ::
  { $Is(#_module.Term.Apply(a#26#0#0, a#26#1#0), Tclass._module.Term()) }
  $Is(#_module.Term.Apply(a#26#0#0, a#26#1#0), Tclass._module.Term())
     <==> $Is(a#26#0#0, Tclass._module.Term()) && $Is(a#26#1#0, Tclass._module.Term()));

// Constructor $IsAlloc
axiom (forall a#27#0#0: DatatypeType, a#27#1#0: DatatypeType, $h: Heap ::
  { $IsAlloc(#_module.Term.Apply(a#27#0#0, a#27#1#0), Tclass._module.Term(), $h) }
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Term.Apply(a#27#0#0, a#27#1#0), Tclass._module.Term(), $h)
       <==> $IsAlloc(a#27#0#0, Tclass._module.Term(), $h)
         && $IsAlloc(a#27#1#0, Tclass._module.Term(), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap ::
  { $IsAlloc(_module.Term.car(d), Tclass._module.Term(), $h) }
  $IsGoodHeap($h)
       &&
      _module.Term.Apply_q(d)
       && $IsAlloc(d, Tclass._module.Term(), $h)
     ==> $IsAlloc(_module.Term.car(d), Tclass._module.Term(), $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap ::
  { $IsAlloc(_module.Term.cdr(d), Tclass._module.Term(), $h) }
  $IsGoodHeap($h)
       &&
      _module.Term.Apply_q(d)
       && $IsAlloc(d, Tclass._module.Term(), $h)
     ==> $IsAlloc(_module.Term.cdr(d), Tclass._module.Term(), $h));

// Constructor literal
axiom (forall a#28#0#0: DatatypeType, a#28#1#0: DatatypeType ::
  { #_module.Term.Apply(Lit(a#28#0#0), Lit(a#28#1#0)) }
  #_module.Term.Apply(Lit(a#28#0#0), Lit(a#28#1#0))
     == Lit(#_module.Term.Apply(a#28#0#0, a#28#1#0)));

function _module.Term.car(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#29#0#0: DatatypeType, a#29#1#0: DatatypeType ::
  { #_module.Term.Apply(a#29#0#0, a#29#1#0) }
  _module.Term.car(#_module.Term.Apply(a#29#0#0, a#29#1#0)) == a#29#0#0);

// Inductive rank
axiom (forall a#30#0#0: DatatypeType, a#30#1#0: DatatypeType ::
  { #_module.Term.Apply(a#30#0#0, a#30#1#0) }
  DtRank(a#30#0#0) < DtRank(#_module.Term.Apply(a#30#0#0, a#30#1#0)));

function _module.Term.cdr(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#31#0#0: DatatypeType, a#31#1#0: DatatypeType ::
  { #_module.Term.Apply(a#31#0#0, a#31#1#0) }
  _module.Term.cdr(#_module.Term.Apply(a#31#0#0, a#31#1#0)) == a#31#1#0);

// Inductive rank
axiom (forall a#32#0#0: DatatypeType, a#32#1#0: DatatypeType ::
  { #_module.Term.Apply(a#32#0#0, a#32#1#0) }
  DtRank(a#32#1#0) < DtRank(#_module.Term.Apply(a#32#0#0, a#32#1#0)));

// One-depth case-split function
function $IsA#_module.Term(DatatypeType) : bool;

// One-depth case-split axiom
axiom (forall d: DatatypeType ::
  { $IsA#_module.Term(d) }
  $IsA#_module.Term(d)
     ==> _module.Term.S_q(d) || _module.Term.K_q(d) || _module.Term.Apply_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType ::
  { _module.Term.Apply_q(d), $Is(d, Tclass._module.Term()) }
    { _module.Term.K_q(d), $Is(d, Tclass._module.Term()) }
    { _module.Term.S_q(d), $Is(d, Tclass._module.Term()) }
  $Is(d, Tclass._module.Term())
     ==> _module.Term.S_q(d) || _module.Term.K_q(d) || _module.Term.Apply_q(d));

const unique class._module.Context: ClassName;

// Constructor function declaration
function #_module.Context.Hole() : DatatypeType;

const unique ##_module.Context.Hole: DtCtorId;

// Constructor identifier
axiom DatatypeCtorId(#_module.Context.Hole()) == ##_module.Context.Hole;

function _module.Context.Hole_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType ::
  { _module.Context.Hole_q(d) }
  _module.Context.Hole_q(d) <==> DatatypeCtorId(d) == ##_module.Context.Hole);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType ::
  { _module.Context.Hole_q(d) }
  _module.Context.Hole_q(d) ==> d == #_module.Context.Hole());

function Tclass._module.Context() : Ty;

// Tclass._module.Context Tag
axiom Tag(Tclass._module.Context()) == Tagclass._module.Context;

const unique Tagclass._module.Context: TyTag;

// Box/unbox axiom for Tclass._module.Context
axiom (forall bx: Box ::
  { $IsBox(bx, Tclass._module.Context()) }
  $IsBox(bx, Tclass._module.Context())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.Context()));

// Constructor $Is
axiom $Is(#_module.Context.Hole(), Tclass._module.Context());

// Constructor $IsAlloc
axiom (forall $h: Heap ::
  { $IsAlloc(#_module.Context.Hole(), Tclass._module.Context(), $h) }
  $IsGoodHeap($h)
     ==> $IsAlloc(#_module.Context.Hole(), Tclass._module.Context(), $h));

// Constructor literal
axiom #_module.Context.Hole() == Lit(#_module.Context.Hole());

// Constructor function declaration
function #_module.Context.C_term(DatatypeType, DatatypeType) : DatatypeType;

const unique ##_module.Context.C_term: DtCtorId;

// Constructor identifier
axiom (forall a#38#0#0: DatatypeType, a#38#1#0: DatatypeType ::
  { #_module.Context.C_term(a#38#0#0, a#38#1#0) }
  DatatypeCtorId(#_module.Context.C_term(a#38#0#0, a#38#1#0))
     == ##_module.Context.C_term);

function _module.Context.C__term_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType ::
  { _module.Context.C__term_q(d) }
  _module.Context.C__term_q(d) <==> DatatypeCtorId(d) == ##_module.Context.C_term);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType ::
  { _module.Context.C__term_q(d) }
  _module.Context.C__term_q(d)
     ==> (exists a#39#0#0: DatatypeType, a#39#1#0: DatatypeType ::
      d == #_module.Context.C_term(a#39#0#0, a#39#1#0)));

// Constructor $Is
axiom (forall a#40#0#0: DatatypeType, a#40#1#0: DatatypeType ::
  { $Is(#_module.Context.C_term(a#40#0#0, a#40#1#0), Tclass._module.Context()) }
  $Is(#_module.Context.C_term(a#40#0#0, a#40#1#0), Tclass._module.Context())
     <==> $Is(a#40#0#0, Tclass._module.Context()) && $Is(a#40#1#0, Tclass._module.Term()));

// Constructor $IsAlloc
axiom (forall a#41#0#0: DatatypeType, a#41#1#0: DatatypeType, $h: Heap ::
  { $IsAlloc(#_module.Context.C_term(a#41#0#0, a#41#1#0), Tclass._module.Context(), $h) }
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Context.C_term(a#41#0#0, a#41#1#0), Tclass._module.Context(), $h)
       <==> $IsAlloc(a#41#0#0, Tclass._module.Context(), $h)
         && $IsAlloc(a#41#1#0, Tclass._module.Term(), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap ::
  { $IsAlloc(_module.Context._h0(d), Tclass._module.Context(), $h) }
  $IsGoodHeap($h)
       &&
      _module.Context.C__term_q(d)
       && $IsAlloc(d, Tclass._module.Context(), $h)
     ==> $IsAlloc(_module.Context._h0(d), Tclass._module.Context(), $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap ::
  { $IsAlloc(_module.Context._h1(d), Tclass._module.Term(), $h) }
  $IsGoodHeap($h)
       &&
      _module.Context.C__term_q(d)
       && $IsAlloc(d, Tclass._module.Context(), $h)
     ==> $IsAlloc(_module.Context._h1(d), Tclass._module.Term(), $h));

// Constructor literal
axiom (forall a#42#0#0: DatatypeType, a#42#1#0: DatatypeType ::
  { #_module.Context.C_term(Lit(a#42#0#0), Lit(a#42#1#0)) }
  #_module.Context.C_term(Lit(a#42#0#0), Lit(a#42#1#0))
     == Lit(#_module.Context.C_term(a#42#0#0, a#42#1#0)));

function _module.Context._h0(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#43#0#0: DatatypeType, a#43#1#0: DatatypeType ::
  { #_module.Context.C_term(a#43#0#0, a#43#1#0) }
  _module.Context._h0(#_module.Context.C_term(a#43#0#0, a#43#1#0)) == a#43#0#0);

// Inductive rank
axiom (forall a#44#0#0: DatatypeType, a#44#1#0: DatatypeType ::
  { #_module.Context.C_term(a#44#0#0, a#44#1#0) }
  DtRank(a#44#0#0) < DtRank(#_module.Context.C_term(a#44#0#0, a#44#1#0)));

function _module.Context._h1(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#45#0#0: DatatypeType, a#45#1#0: DatatypeType ::
  { #_module.Context.C_term(a#45#0#0, a#45#1#0) }
  _module.Context._h1(#_module.Context.C_term(a#45#0#0, a#45#1#0)) == a#45#1#0);

// Inductive rank
axiom (forall a#46#0#0: DatatypeType, a#46#1#0: DatatypeType ::
  { #_module.Context.C_term(a#46#0#0, a#46#1#0) }
  DtRank(a#46#1#0) < DtRank(#_module.Context.C_term(a#46#0#0, a#46#1#0)));

// Constructor function declaration
function #_module.Context.value_C(DatatypeType, DatatypeType) : DatatypeType;

const unique ##_module.Context.value_C: DtCtorId;

// Constructor identifier
axiom (forall a#47#0#0: DatatypeType, a#47#1#0: DatatypeType ::
  { #_module.Context.value_C(a#47#0#0, a#47#1#0) }
  DatatypeCtorId(#_module.Context.value_C(a#47#0#0, a#47#1#0))
     == ##_module.Context.value_C);

function _module.Context.value__C_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType ::
  { _module.Context.value__C_q(d) }
  _module.Context.value__C_q(d)
     <==> DatatypeCtorId(d) == ##_module.Context.value_C);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType ::
  { _module.Context.value__C_q(d) }
  _module.Context.value__C_q(d)
     ==> (exists a#48#0#0: DatatypeType, a#48#1#0: DatatypeType ::
      d == #_module.Context.value_C(a#48#0#0, a#48#1#0)));

// Constructor $Is
axiom (forall a#49#0#0: DatatypeType, a#49#1#0: DatatypeType ::
  { $Is(#_module.Context.value_C(a#49#0#0, a#49#1#0), Tclass._module.Context()) }
  $Is(#_module.Context.value_C(a#49#0#0, a#49#1#0), Tclass._module.Context())
     <==> $Is(a#49#0#0, Tclass._module.Term()) && $Is(a#49#1#0, Tclass._module.Context()));

// Constructor $IsAlloc
axiom (forall a#50#0#0: DatatypeType, a#50#1#0: DatatypeType, $h: Heap ::
  { $IsAlloc(#_module.Context.value_C(a#50#0#0, a#50#1#0), Tclass._module.Context(), $h) }
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Context.value_C(a#50#0#0, a#50#1#0), Tclass._module.Context(), $h)
       <==> $IsAlloc(a#50#0#0, Tclass._module.Term(), $h)
         && $IsAlloc(a#50#1#0, Tclass._module.Context(), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap ::
  { $IsAlloc(_module.Context._h2(d), Tclass._module.Term(), $h) }
  $IsGoodHeap($h)
       &&
      _module.Context.value__C_q(d)
       && $IsAlloc(d, Tclass._module.Context(), $h)
     ==> $IsAlloc(_module.Context._h2(d), Tclass._module.Term(), $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap ::
  { $IsAlloc(_module.Context._h3(d), Tclass._module.Context(), $h) }
  $IsGoodHeap($h)
       &&
      _module.Context.value__C_q(d)
       && $IsAlloc(d, Tclass._module.Context(), $h)
     ==> $IsAlloc(_module.Context._h3(d), Tclass._module.Context(), $h));

// Constructor literal
axiom (forall a#51#0#0: DatatypeType, a#51#1#0: DatatypeType ::
  { #_module.Context.value_C(Lit(a#51#0#0), Lit(a#51#1#0)) }
  #_module.Context.value_C(Lit(a#51#0#0), Lit(a#51#1#0))
     == Lit(#_module.Context.value_C(a#51#0#0, a#51#1#0)));

function _module.Context._h2(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#52#0#0: DatatypeType, a#52#1#0: DatatypeType ::
  { #_module.Context.value_C(a#52#0#0, a#52#1#0) }
  _module.Context._h2(#_module.Context.value_C(a#52#0#0, a#52#1#0)) == a#52#0#0);

// Inductive rank
axiom (forall a#53#0#0: DatatypeType, a#53#1#0: DatatypeType ::
  { #_module.Context.value_C(a#53#0#0, a#53#1#0) }
  DtRank(a#53#0#0) < DtRank(#_module.Context.value_C(a#53#0#0, a#53#1#0)));

function _module.Context._h3(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#54#0#0: DatatypeType, a#54#1#0: DatatypeType ::
  { #_module.Context.value_C(a#54#0#0, a#54#1#0) }
  _module.Context._h3(#_module.Context.value_C(a#54#0#0, a#54#1#0)) == a#54#1#0);

// Inductive rank
axiom (forall a#55#0#0: DatatypeType, a#55#1#0: DatatypeType ::
  { #_module.Context.value_C(a#55#0#0, a#55#1#0) }
  DtRank(a#55#1#0) < DtRank(#_module.Context.value_C(a#55#0#0, a#55#1#0)));

// One-depth case-split function
function $IsA#_module.Context(DatatypeType) : bool;

// One-depth case-split axiom
axiom (forall d: DatatypeType ::
  { $IsA#_module.Context(d) }
  $IsA#_module.Context(d)
     ==> _module.Context.Hole_q(d)
       || _module.Context.C__term_q(d)
       || _module.Context.value__C_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType ::
  { _module.Context.value__C_q(d), $Is(d, Tclass._module.Context()) }
    { _module.Context.C__term_q(d), $Is(d, Tclass._module.Context()) }
    { _module.Context.Hole_q(d), $Is(d, Tclass._module.Context()) }
  $Is(d, Tclass._module.Context())
     ==> _module.Context.Hole_q(d)
       || _module.Context.C__term_q(d)
       || _module.Context.value__C_q(d));

const unique class._module.Trace: ClassName;

// Constructor function declaration
function #_module.Trace.EmptyTrace() : DatatypeType;

const unique ##_module.Trace.EmptyTrace: DtCtorId;

// Constructor identifier
axiom DatatypeCtorId(#_module.Trace.EmptyTrace()) == ##_module.Trace.EmptyTrace;

function _module.Trace.EmptyTrace_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType ::
  { _module.Trace.EmptyTrace_q(d) }
  _module.Trace.EmptyTrace_q(d)
     <==> DatatypeCtorId(d) == ##_module.Trace.EmptyTrace);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType ::
  { _module.Trace.EmptyTrace_q(d) }
  _module.Trace.EmptyTrace_q(d) ==> d == #_module.Trace.EmptyTrace());

function Tclass._module.Trace() : Ty;

// Tclass._module.Trace Tag
axiom Tag(Tclass._module.Trace()) == Tagclass._module.Trace;

const unique Tagclass._module.Trace: TyTag;

// Box/unbox axiom for Tclass._module.Trace
axiom (forall bx: Box ::
  { $IsBox(bx, Tclass._module.Trace()) }
  $IsBox(bx, Tclass._module.Trace())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.Trace()));

// Constructor $Is
axiom $Is(#_module.Trace.EmptyTrace(), Tclass._module.Trace());

// Constructor $IsAlloc
axiom (forall $h: Heap ::
  { $IsAlloc(#_module.Trace.EmptyTrace(), Tclass._module.Trace(), $h) }
  $IsGoodHeap($h)
     ==> $IsAlloc(#_module.Trace.EmptyTrace(), Tclass._module.Trace(), $h));

// Constructor literal
axiom #_module.Trace.EmptyTrace() == Lit(#_module.Trace.EmptyTrace());

// Constructor function declaration
function #_module.Trace.ReductionStep(DatatypeType, DatatypeType) : DatatypeType;

const unique ##_module.Trace.ReductionStep: DtCtorId;

// Constructor identifier
axiom (forall a#61#0#0: DatatypeType, a#61#1#0: DatatypeType ::
  { #_module.Trace.ReductionStep(a#61#0#0, a#61#1#0) }
  DatatypeCtorId(#_module.Trace.ReductionStep(a#61#0#0, a#61#1#0))
     == ##_module.Trace.ReductionStep);

function _module.Trace.ReductionStep_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType ::
  { _module.Trace.ReductionStep_q(d) }
  _module.Trace.ReductionStep_q(d)
     <==> DatatypeCtorId(d) == ##_module.Trace.ReductionStep);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType ::
  { _module.Trace.ReductionStep_q(d) }
  _module.Trace.ReductionStep_q(d)
     ==> (exists a#62#0#0: DatatypeType, a#62#1#0: DatatypeType ::
      d == #_module.Trace.ReductionStep(a#62#0#0, a#62#1#0)));

// Constructor $Is
axiom (forall a#63#0#0: DatatypeType, a#63#1#0: DatatypeType ::
  { $Is(#_module.Trace.ReductionStep(a#63#0#0, a#63#1#0), Tclass._module.Trace()) }
  $Is(#_module.Trace.ReductionStep(a#63#0#0, a#63#1#0), Tclass._module.Trace())
     <==> $Is(a#63#0#0, Tclass._module.Trace()) && $Is(a#63#1#0, Tclass._module.Term()));

// Constructor $IsAlloc
axiom (forall a#64#0#0: DatatypeType, a#64#1#0: DatatypeType, $h: Heap ::
  { $IsAlloc(#_module.Trace.ReductionStep(a#64#0#0, a#64#1#0), Tclass._module.Trace(), $h) }
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Trace.ReductionStep(a#64#0#0, a#64#1#0), Tclass._module.Trace(), $h)
       <==> $IsAlloc(a#64#0#0, Tclass._module.Trace(), $h)
         && $IsAlloc(a#64#1#0, Tclass._module.Term(), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap ::
  { $IsAlloc(_module.Trace._h4(d), Tclass._module.Trace(), $h) }
  $IsGoodHeap($h)
       &&
      _module.Trace.ReductionStep_q(d)
       && $IsAlloc(d, Tclass._module.Trace(), $h)
     ==> $IsAlloc(_module.Trace._h4(d), Tclass._module.Trace(), $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap ::
  { $IsAlloc(_module.Trace._h5(d), Tclass._module.Term(), $h) }
  $IsGoodHeap($h)
       &&
      _module.Trace.ReductionStep_q(d)
       && $IsAlloc(d, Tclass._module.Trace(), $h)
     ==> $IsAlloc(_module.Trace._h5(d), Tclass._module.Term(), $h));

// Constructor literal
axiom (forall a#65#0#0: DatatypeType, a#65#1#0: DatatypeType ::
  { #_module.Trace.ReductionStep(Lit(a#65#0#0), Lit(a#65#1#0)) }
  #_module.Trace.ReductionStep(Lit(a#65#0#0), Lit(a#65#1#0))
     == Lit(#_module.Trace.ReductionStep(a#65#0#0, a#65#1#0)));

function _module.Trace._h4(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#66#0#0: DatatypeType, a#66#1#0: DatatypeType ::
  { #_module.Trace.ReductionStep(a#66#0#0, a#66#1#0) }
  _module.Trace._h4(#_module.Trace.ReductionStep(a#66#0#0, a#66#1#0)) == a#66#0#0);

// Inductive rank
axiom (forall a#67#0#0: DatatypeType, a#67#1#0: DatatypeType ::
  { #_module.Trace.ReductionStep(a#67#0#0, a#67#1#0) }
  DtRank(a#67#0#0) < DtRank(#_module.Trace.ReductionStep(a#67#0#0, a#67#1#0)));

function _module.Trace._h5(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#68#0#0: DatatypeType, a#68#1#0: DatatypeType ::
  { #_module.Trace.ReductionStep(a#68#0#0, a#68#1#0) }
  _module.Trace._h5(#_module.Trace.ReductionStep(a#68#0#0, a#68#1#0)) == a#68#1#0);

// Inductive rank
axiom (forall a#69#0#0: DatatypeType, a#69#1#0: DatatypeType ::
  { #_module.Trace.ReductionStep(a#69#0#0, a#69#1#0) }
  DtRank(a#69#1#0) < DtRank(#_module.Trace.ReductionStep(a#69#0#0, a#69#1#0)));

// One-depth case-split function
function $IsA#_module.Trace(DatatypeType) : bool;

// One-depth case-split axiom
axiom (forall d: DatatypeType ::
  { $IsA#_module.Trace(d) }
  $IsA#_module.Trace(d)
     ==> _module.Trace.EmptyTrace_q(d) || _module.Trace.ReductionStep_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType ::
  { _module.Trace.ReductionStep_q(d), $Is(d, Tclass._module.Trace()) }
    { _module.Trace.EmptyTrace_q(d), $Is(d, Tclass._module.Trace()) }
  $Is(d, Tclass._module.Trace())
     ==> _module.Trace.EmptyTrace_q(d) || _module.Trace.ReductionStep_q(d));

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

// function declaration for _module._default.IsValue
function _module.__default.IsValue($ly: LayerType, t#0: DatatypeType) : bool;

function _module.__default.IsValue#canCall(t#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, t#0: DatatypeType ::
  { _module.__default.IsValue($LS($ly), t#0) }
  _module.__default.IsValue($LS($ly), t#0) == _module.__default.IsValue($ly, t#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, t#0: DatatypeType ::
  { _module.__default.IsValue(AsFuelBottom($ly), t#0) }
  _module.__default.IsValue($ly, t#0) == _module.__default.IsValue($LZ, t#0));

// consequence axiom for _module.__default.IsValue
axiom 4 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, $Heap: Heap, t#0: DatatypeType ::
    { _module.__default.IsValue($ly, t#0), $IsGoodHeap($Heap) }
    _module.__default.IsValue#canCall(t#0)
         || (4 != $FunctionContextHeight
           &&
          $IsGoodHeap($Heap)
           && $Is(t#0, Tclass._module.Term()))
       ==>
      _module.__default.IsValue($ly, t#0) && _module.Term.Apply_q(t#0)
       ==> _module.__default.IsValue($ly, _module.Term.car(t#0))
         && _module.__default.IsValue($ly, _module.Term.cdr(t#0)));

function _module.__default.IsValue#requires(LayerType, DatatypeType) : bool;

// #requires axiom for _module.__default.IsValue
axiom (forall $ly: LayerType, t#0: DatatypeType ::
  { _module.__default.IsValue#requires($ly, t#0) }
  $Is(t#0, Tclass._module.Term())
     ==> _module.__default.IsValue#requires($ly, t#0) == true);

// definition axiom for _module.__default.IsValue(revealed)
axiom 4 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, t#0: DatatypeType ::
    { _module.__default.IsValue($LS($ly), t#0) }
    _module.__default.IsValue#canCall(t#0)
         || (4 != $FunctionContextHeight && $Is(t#0, Tclass._module.Term()))
       ==> (!_module.Term.K_q(t#0)
           ==>
          !_module.Term.S_q(t#0)
           ==> (_module.Term.K_q(_module.Term.car(t#0))
               ==> _module.__default.IsValue#canCall(_module.Term.cdr(t#0)))
             && (!_module.Term.K_q(_module.Term.car(t#0))
               ==> (_module.Term.S_q(_module.Term.car(t#0))
                   ==> _module.__default.IsValue#canCall(_module.Term.cdr(t#0)))
                 && (!_module.Term.S_q(_module.Term.car(t#0))
                   ==> (_module.Term.car(_module.Term.car(t#0)) == Lit(#_module.Term.S())
                       ==> _module.__default.IsValue#canCall(_module.Term.cdr(_module.Term.car(t#0))))
                     && (_module.__default.IsValue#canCall(_module.Term.cdr(_module.Term.car(t#0)))
                         && _module.__default.IsValue($ly, _module.Term.cdr(_module.Term.car(t#0)))
                       ==> _module.__default.IsValue#canCall(_module.Term.cdr(t#0))))))
         && _module.__default.IsValue($LS($ly), t#0)
           == (if _module.Term.K_q(t#0)
             then true
             else (if _module.Term.S_q(t#0)
               then true
               else (if _module.Term.K_q(_module.Term.car(t#0))
                 then _module.__default.IsValue($ly, _module.Term.cdr(t#0))
                 else (if _module.Term.S_q(_module.Term.car(t#0))
                   then _module.__default.IsValue($ly, _module.Term.cdr(t#0))
                   else _module.Term.car(_module.Term.car(t#0)) == Lit(#_module.Term.S())
                     && _module.__default.IsValue($ly, _module.Term.cdr(_module.Term.car(t#0)))
                     && _module.__default.IsValue($ly, _module.Term.cdr(t#0)))))));

// definition axiom for _module.__default.IsValue for all literals(revealed)
axiom 4 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, t#0: DatatypeType ::
    {:weight 3} { _module.__default.IsValue($LS($ly), Lit(t#0)) }
    _module.__default.IsValue#canCall(Lit(t#0))
         || (4 != $FunctionContextHeight && $Is(t#0, Tclass._module.Term()))
       ==> (!Lit(_module.Term.K_q(Lit(t#0)))
           ==>
          !Lit(_module.Term.S_q(Lit(t#0)))
           ==> (Lit(_module.Term.K_q(Lit(_module.Term.car(Lit(t#0)))))
               ==> _module.__default.IsValue#canCall(Lit(_module.Term.cdr(Lit(t#0)))))
             && (!Lit(_module.Term.K_q(Lit(_module.Term.car(Lit(t#0)))))
               ==> (Lit(_module.Term.S_q(Lit(_module.Term.car(Lit(t#0)))))
                   ==> _module.__default.IsValue#canCall(Lit(_module.Term.cdr(Lit(t#0)))))
                 && (!Lit(_module.Term.S_q(Lit(_module.Term.car(Lit(t#0)))))
                   ==> (Lit(_module.Term.car(Lit(_module.Term.car(Lit(t#0))))) == Lit(#_module.Term.S())
                       ==> _module.__default.IsValue#canCall(Lit(_module.Term.cdr(Lit(_module.Term.car(Lit(t#0)))))))
                     && (_module.__default.IsValue#canCall(Lit(_module.Term.cdr(Lit(_module.Term.car(Lit(t#0))))))
                         && Lit(_module.__default.IsValue($LS($ly), Lit(_module.Term.cdr(Lit(_module.Term.car(Lit(t#0)))))))
                       ==> _module.__default.IsValue#canCall(Lit(_module.Term.cdr(Lit(t#0))))))))
         && _module.__default.IsValue($LS($ly), Lit(t#0))
           == (if _module.Term.K_q(Lit(t#0))
             then true
             else (if _module.Term.S_q(Lit(t#0))
               then true
               else (if _module.Term.K_q(Lit(_module.Term.car(Lit(t#0))))
                 then _module.__default.IsValue($LS($ly), Lit(_module.Term.cdr(Lit(t#0))))
                 else (if _module.Term.S_q(Lit(_module.Term.car(Lit(t#0))))
                   then _module.__default.IsValue($LS($ly), Lit(_module.Term.cdr(Lit(t#0))))
                   else Lit(_module.Term.car(Lit(_module.Term.car(Lit(t#0))))) == Lit(#_module.Term.S())
                     && _module.__default.IsValue($LS($ly), Lit(_module.Term.cdr(Lit(_module.Term.car(Lit(t#0))))))
                     && _module.__default.IsValue($LS($ly), Lit(_module.Term.cdr(Lit(t#0)))))))));

procedure CheckWellformed$$_module.__default.IsValue(t#0: DatatypeType where $Is(t#0, Tclass._module.Term()));
  free requires 4 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  ensures _module.__default.IsValue($LS($LZ), t#0) && _module.Term.Apply_q(t#0)
     ==> _module.__default.IsValue($LS($LS($LZ)), _module.Term.car(t#0));
  ensures _module.__default.IsValue($LS($LZ), t#0) && _module.Term.Apply_q(t#0)
     ==> _module.__default.IsValue($LS($LS($LZ)), _module.Term.cdr(t#0));



implementation CheckWellformed$$_module.__default.IsValue(t#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##t#0: DatatypeType;
  var ##t#1: DatatypeType;
  var ##t#2: DatatypeType;
  var a#0: DatatypeType;
  var b#0: DatatypeType;
  var x#0: DatatypeType;
  var y#0: DatatypeType;
  var ##t#3: DatatypeType;
  var ##t#4: DatatypeType;
  var ##t#5: DatatypeType;
  var ##t#6: DatatypeType;
  var ##t#7: DatatypeType;
  var ##t#8: DatatypeType;
  var ##t#9: DatatypeType;
  var ##t#10: DatatypeType;
  var ##t#11: DatatypeType;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;
  var b$reqreads#2: bool;
  var b$reqreads#3: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;
    b$reqreads#2 := true;
    b$reqreads#3 := true;

    // AddWellformednessCheck for function IsValue
    assume {:captureState "Combinators.dfy(21,16): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        if (*)
        {
            ##t#0 := t#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##t#0, Tclass._module.Term(), $Heap);
            assert t#0 == t#0 || DtRank(##t#0) < DtRank(t#0);
            assume t#0 == t#0 || _module.__default.IsValue#canCall(t#0);
            assume _module.__default.IsValue($LS($LZ), t#0);
            assume _module.Term.Apply_q(t#0);
            assert _module.Term.Apply_q(t#0);
            ##t#1 := _module.Term.car(t#0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##t#1, Tclass._module.Term(), $Heap);
            assert _module.Term.car(t#0) == t#0 || DtRank(##t#1) < DtRank(t#0);
            assume _module.Term.car(t#0) == t#0
               || _module.__default.IsValue#canCall(_module.Term.car(t#0));
            assume _module.__default.IsValue($LS($LZ), _module.Term.car(t#0));
            assert _module.Term.Apply_q(t#0);
            ##t#2 := _module.Term.cdr(t#0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##t#2, Tclass._module.Term(), $Heap);
            assert _module.Term.cdr(t#0) == t#0 || DtRank(##t#2) < DtRank(t#0);
            assume _module.Term.cdr(t#0) == t#0
               || _module.__default.IsValue#canCall(_module.Term.cdr(t#0));
            assume _module.__default.IsValue($LS($LZ), _module.Term.cdr(t#0));
        }
        else
        {
            assume _module.__default.IsValue($LS($LZ), t#0) && _module.Term.Apply_q(t#0)
               ==> _module.__default.IsValue($LS($LZ), _module.Term.car(t#0))
                 && _module.__default.IsValue($LS($LZ), _module.Term.cdr(t#0));
        }

        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
          $o != null && read($Heap, $o, alloc) ==> false);
        if (t#0 == #_module.Term.K())
        {
            assume _module.__default.IsValue($LS($LZ), t#0) == Lit(true);
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.IsValue($LS($LZ), t#0), TBool);
        }
        else if (t#0 == #_module.Term.S())
        {
            assume _module.__default.IsValue($LS($LZ), t#0) == Lit(true);
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.IsValue($LS($LZ), t#0), TBool);
        }
        else if (t#0 == #_module.Term.Apply(a#0, b#0))
        {
            assume $Is(a#0, Tclass._module.Term());
            assume $Is(b#0, Tclass._module.Term());
            if (a#0 == #_module.Term.K())
            {
                // ----- assert statement ----- Combinators.dfy(30,7)
                ##t#10 := a#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##t#10, Tclass._module.Term(), $Heap);
                assert DtRank(##t#10) < DtRank(t#0);
                assume _module.__default.IsValue#canCall(a#0);
                assume _module.__default.IsValue#canCall(a#0);
                assert {:subsumption 0} _module.__default.IsValue($LS($LS($LZ)), a#0);
                assume _module.__default.IsValue($LS($LZ), a#0);
                ##t#11 := b#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##t#11, Tclass._module.Term(), $Heap);
                b$reqreads#3 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                assert DtRank(##t#11) < DtRank(t#0);
                assume _module.__default.IsValue#canCall(b#0);
                assume _module.__default.IsValue($LS($LZ), t#0)
                   == _module.__default.IsValue($LS($LZ), b#0);
                assume _module.__default.IsValue#canCall(b#0);
                // CheckWellformedWithResult: any expression
                assume $Is(_module.__default.IsValue($LS($LZ), t#0), TBool);
            }
            else if (a#0 == #_module.Term.S())
            {
                // ----- assert statement ----- Combinators.dfy(33,7)
                ##t#8 := a#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##t#8, Tclass._module.Term(), $Heap);
                assert DtRank(##t#8) < DtRank(t#0);
                assume _module.__default.IsValue#canCall(a#0);
                assume _module.__default.IsValue#canCall(a#0);
                assert {:subsumption 0} _module.__default.IsValue($LS($LS($LZ)), a#0);
                assume _module.__default.IsValue($LS($LZ), a#0);
                ##t#9 := b#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##t#9, Tclass._module.Term(), $Heap);
                b$reqreads#2 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                assert DtRank(##t#9) < DtRank(t#0);
                assume _module.__default.IsValue#canCall(b#0);
                assume _module.__default.IsValue($LS($LZ), t#0)
                   == _module.__default.IsValue($LS($LZ), b#0);
                assume _module.__default.IsValue#canCall(b#0);
                // CheckWellformedWithResult: any expression
                assume $Is(_module.__default.IsValue($LS($LZ), t#0), TBool);
            }
            else if (a#0 == #_module.Term.Apply(x#0, y#0))
            {
                assume $Is(x#0, Tclass._module.Term());
                assume $Is(y#0, Tclass._module.Term());
                // ----- assert statement ----- Combinators.dfy(36,7)
                if (x#0 == Lit(#_module.Term.S()))
                {
                    ##t#3 := y#0;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##t#3, Tclass._module.Term(), $Heap);
                    assert DtRank(##t#3) < DtRank(t#0);
                    assume _module.__default.IsValue#canCall(y#0);
                }

                if (x#0 == Lit(#_module.Term.S()) && _module.__default.IsValue($LS($LZ), y#0))
                {
                    ##t#4 := b#0;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##t#4, Tclass._module.Term(), $Heap);
                    assert DtRank(##t#4) < DtRank(t#0);
                    assume _module.__default.IsValue#canCall(b#0);
                }

                if (x#0 == Lit(#_module.Term.S())
                   && _module.__default.IsValue($LS($LZ), y#0)
                   && _module.__default.IsValue($LS($LZ), b#0))
                {
                    ##t#5 := a#0;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##t#5, Tclass._module.Term(), $Heap);
                    assert DtRank(##t#5) < DtRank(t#0);
                    assume _module.__default.IsValue#canCall(a#0);
                }

                assume (x#0 == Lit(#_module.Term.S()) ==> _module.__default.IsValue#canCall(y#0))
                   && (_module.__default.IsValue#canCall(y#0)
                       && _module.__default.IsValue($LS($LZ), y#0)
                     ==> _module.__default.IsValue#canCall(b#0))
                   && (_module.__default.IsValue#canCall(b#0)
                       && _module.__default.IsValue($LS($LZ), b#0)
                     ==> _module.__default.IsValue#canCall(a#0));
                assert {:subsumption 0} x#0 == Lit(#_module.Term.S())
                     && _module.__default.IsValue($LS($LZ), y#0)
                     && _module.__default.IsValue($LS($LZ), b#0)
                   ==> _module.__default.IsValue($LS($LS($LZ)), a#0);
                assume x#0 == Lit(#_module.Term.S())
                     && _module.__default.IsValue($LS($LZ), y#0)
                     && _module.__default.IsValue($LS($LZ), b#0)
                   ==> _module.__default.IsValue($LS($LZ), a#0);
                if (x#0 == Lit(#_module.Term.S()))
                {
                    ##t#6 := y#0;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##t#6, Tclass._module.Term(), $Heap);
                    b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                    assert DtRank(##t#6) < DtRank(t#0);
                    assume _module.__default.IsValue#canCall(y#0);
                }

                if (x#0 == Lit(#_module.Term.S()) && _module.__default.IsValue($LS($LZ), y#0))
                {
                    ##t#7 := b#0;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##t#7, Tclass._module.Term(), $Heap);
                    b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                    assert DtRank(##t#7) < DtRank(t#0);
                    assume _module.__default.IsValue#canCall(b#0);
                }

                assume _module.__default.IsValue($LS($LZ), t#0)
                   == (
                    x#0 == Lit(#_module.Term.S())
                     && _module.__default.IsValue($LS($LZ), y#0)
                     && _module.__default.IsValue($LS($LZ), b#0));
                assume (x#0 == Lit(#_module.Term.S()) ==> _module.__default.IsValue#canCall(y#0))
                   && (_module.__default.IsValue#canCall(y#0)
                       && _module.__default.IsValue($LS($LZ), y#0)
                     ==> _module.__default.IsValue#canCall(b#0));
                // CheckWellformedWithResult: any expression
                assume $Is(_module.__default.IsValue($LS($LZ), t#0), TBool);
            }
            else
            {
                assume false;
            }
        }
        else
        {
            assume false;
        }

        assert b$reqreads#0;
        assert b$reqreads#1;
        assert b$reqreads#2;
        assert b$reqreads#3;
    }
}



// function declaration for _module._default.IsContext
function _module.__default.IsContext($ly: LayerType, C#0: DatatypeType) : bool;

function _module.__default.IsContext#canCall(C#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, C#0: DatatypeType ::
  { _module.__default.IsContext($LS($ly), C#0) }
  _module.__default.IsContext($LS($ly), C#0)
     == _module.__default.IsContext($ly, C#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, C#0: DatatypeType ::
  { _module.__default.IsContext(AsFuelBottom($ly), C#0) }
  _module.__default.IsContext($ly, C#0) == _module.__default.IsContext($LZ, C#0));

// consequence axiom for _module.__default.IsContext
axiom 9 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, C#0: DatatypeType ::
    { _module.__default.IsContext($ly, C#0) }
    _module.__default.IsContext#canCall(C#0)
         || (9 != $FunctionContextHeight && $Is(C#0, Tclass._module.Context()))
       ==> true);

function _module.__default.IsContext#requires(LayerType, DatatypeType) : bool;

// #requires axiom for _module.__default.IsContext
axiom (forall $ly: LayerType, C#0: DatatypeType ::
  { _module.__default.IsContext#requires($ly, C#0) }
  $Is(C#0, Tclass._module.Context())
     ==> _module.__default.IsContext#requires($ly, C#0) == true);

// definition axiom for _module.__default.IsContext(revealed)
axiom 9 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, C#0: DatatypeType ::
    { _module.__default.IsContext($LS($ly), C#0) }
    _module.__default.IsContext#canCall(C#0)
         || (9 != $FunctionContextHeight && $Is(C#0, Tclass._module.Context()))
       ==> (!_module.Context.Hole_q(C#0)
           ==> (_module.Context.C__term_q(C#0)
               ==> _module.__default.IsContext#canCall(_module.Context._h0(C#0)))
             && (!_module.Context.C__term_q(C#0)
               ==> _module.__default.IsValue#canCall(_module.Context._h2(C#0))
                 && (_module.__default.IsValue($LS($LZ), _module.Context._h2(C#0))
                   ==> _module.__default.IsContext#canCall(_module.Context._h3(C#0)))))
         && _module.__default.IsContext($LS($ly), C#0)
           == (if _module.Context.Hole_q(C#0)
             then true
             else (if _module.Context.C__term_q(C#0)
               then _module.__default.IsContext($ly, _module.Context._h0(C#0))
               else _module.__default.IsValue($LS($LZ), _module.Context._h2(C#0))
                 && _module.__default.IsContext($ly, _module.Context._h3(C#0)))));

// definition axiom for _module.__default.IsContext for all literals(revealed)
axiom 9 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, C#0: DatatypeType ::
    {:weight 3} { _module.__default.IsContext($LS($ly), Lit(C#0)) }
    _module.__default.IsContext#canCall(Lit(C#0))
         || (9 != $FunctionContextHeight && $Is(C#0, Tclass._module.Context()))
       ==> (!Lit(_module.Context.Hole_q(Lit(C#0)))
           ==> (Lit(_module.Context.C__term_q(Lit(C#0)))
               ==> _module.__default.IsContext#canCall(Lit(_module.Context._h0(Lit(C#0)))))
             && (!Lit(_module.Context.C__term_q(Lit(C#0)))
               ==> _module.__default.IsValue#canCall(Lit(_module.Context._h2(Lit(C#0))))
                 && (Lit(_module.__default.IsValue($LS($LZ), Lit(_module.Context._h2(Lit(C#0)))))
                   ==> _module.__default.IsContext#canCall(Lit(_module.Context._h3(Lit(C#0)))))))
         && _module.__default.IsContext($LS($ly), Lit(C#0))
           == (if _module.Context.Hole_q(Lit(C#0))
             then true
             else (if _module.Context.C__term_q(Lit(C#0))
               then _module.__default.IsContext($LS($ly), Lit(_module.Context._h0(Lit(C#0))))
               else _module.__default.IsValue($LS($LZ), Lit(_module.Context._h2(Lit(C#0))))
                 && _module.__default.IsContext($LS($ly), Lit(_module.Context._h3(Lit(C#0)))))));

procedure CheckWellformed$$_module.__default.IsContext(C#0: DatatypeType where $Is(C#0, Tclass._module.Context()));
  free requires 9 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.IsContext(C#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var v#0: DatatypeType;
  var D#0: DatatypeType;
  var ##t#0: DatatypeType;
  var ##C#0: DatatypeType;
  var D#1: DatatypeType;
  var t#0: DatatypeType;
  var ##C#1: DatatypeType;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;
  var b$reqreads#2: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;
    b$reqreads#2 := true;

    // AddWellformednessCheck for function IsContext
    assume {:captureState "Combinators.dfy(49,9): initial state"} true;
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
        if (C#0 == #_module.Context.Hole())
        {
            assume _module.__default.IsContext($LS($LZ), C#0) == Lit(true);
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.IsContext($LS($LZ), C#0), TBool);
        }
        else if (C#0 == #_module.Context.C_term(D#1, t#0))
        {
            assume $Is(D#1, Tclass._module.Context());
            assume $Is(t#0, Tclass._module.Term());
            ##C#1 := D#1;
            // assume allocatedness for argument to function
            assume $IsAlloc(##C#1, Tclass._module.Context(), $Heap);
            b$reqreads#2 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert DtRank(##C#1) < DtRank(C#0);
            assume _module.__default.IsContext#canCall(D#1);
            assume _module.__default.IsContext($LS($LZ), C#0)
               == _module.__default.IsContext($LS($LZ), D#1);
            assume _module.__default.IsContext#canCall(D#1);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.IsContext($LS($LZ), C#0), TBool);
        }
        else if (C#0 == #_module.Context.value_C(v#0, D#0))
        {
            assume $Is(v#0, Tclass._module.Term());
            assume $Is(D#0, Tclass._module.Context());
            ##t#0 := v#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##t#0, Tclass._module.Term(), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume _module.__default.IsValue#canCall(v#0);
            if (_module.__default.IsValue($LS($LZ), v#0))
            {
                ##C#0 := D#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##C#0, Tclass._module.Context(), $Heap);
                b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                assert DtRank(##C#0) < DtRank(C#0);
                assume _module.__default.IsContext#canCall(D#0);
            }

            assume _module.__default.IsContext($LS($LZ), C#0)
               == (_module.__default.IsValue($LS($LZ), v#0)
                 && _module.__default.IsContext($LS($LZ), D#0));
            assume _module.__default.IsValue#canCall(v#0)
               && (_module.__default.IsValue($LS($LZ), v#0)
                 ==> _module.__default.IsContext#canCall(D#0));
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.IsContext($LS($LZ), C#0), TBool);
        }
        else
        {
            assume false;
        }

        assert b$reqreads#0;
        assert b$reqreads#1;
        assert b$reqreads#2;
    }
}



// function declaration for _module._default.EvalExpr
function _module.__default.EvalExpr($ly: LayerType, C#0: DatatypeType, t#0: DatatypeType) : DatatypeType;

function _module.__default.EvalExpr#canCall(C#0: DatatypeType, t#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, C#0: DatatypeType, t#0: DatatypeType ::
  { _module.__default.EvalExpr($LS($ly), C#0, t#0) }
  _module.__default.EvalExpr($LS($ly), C#0, t#0)
     == _module.__default.EvalExpr($ly, C#0, t#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, C#0: DatatypeType, t#0: DatatypeType ::
  { _module.__default.EvalExpr(AsFuelBottom($ly), C#0, t#0) }
  _module.__default.EvalExpr($ly, C#0, t#0)
     == _module.__default.EvalExpr($LZ, C#0, t#0));

// consequence axiom for _module.__default.EvalExpr
axiom 10 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, C#0: DatatypeType, t#0: DatatypeType ::
    { _module.__default.EvalExpr($ly, C#0, t#0) }
    _module.__default.EvalExpr#canCall(C#0, t#0)
         || (10 != $FunctionContextHeight
           &&
          $Is(C#0, Tclass._module.Context())
           && $Is(t#0, Tclass._module.Term())
           && _module.__default.IsContext($LS($LZ), C#0))
       ==> $Is(_module.__default.EvalExpr($ly, C#0, t#0), Tclass._module.Term()));

function _module.__default.EvalExpr#requires(LayerType, DatatypeType, DatatypeType) : bool;

// #requires axiom for _module.__default.EvalExpr
axiom (forall $ly: LayerType, C#0: DatatypeType, t#0: DatatypeType ::
  { _module.__default.EvalExpr#requires($ly, C#0, t#0) }
  $Is(C#0, Tclass._module.Context()) && $Is(t#0, Tclass._module.Term())
     ==> _module.__default.EvalExpr#requires($ly, C#0, t#0)
       == _module.__default.IsContext($LS($LZ), C#0));

// definition axiom for _module.__default.EvalExpr(revealed)
axiom 10 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, C#0: DatatypeType, t#0: DatatypeType ::
    { _module.__default.EvalExpr($LS($ly), C#0, t#0) }
    _module.__default.EvalExpr#canCall(C#0, t#0)
         || (10 != $FunctionContextHeight
           &&
          $Is(C#0, Tclass._module.Context())
           && $Is(t#0, Tclass._module.Term())
           && _module.__default.IsContext($LS($LZ), C#0))
       ==> (!_module.Context.Hole_q(C#0)
           ==> (_module.Context.C__term_q(C#0)
               ==> _module.__default.EvalExpr#canCall(_module.Context._h0(C#0), t#0))
             && (!_module.Context.C__term_q(C#0)
               ==> _module.__default.EvalExpr#canCall(_module.Context._h3(C#0), t#0)))
         && _module.__default.EvalExpr($LS($ly), C#0, t#0)
           == (if _module.Context.Hole_q(C#0)
             then t#0
             else (if _module.Context.C__term_q(C#0)
               then #_module.Term.Apply(_module.__default.EvalExpr($ly, _module.Context._h0(C#0), t#0),
                _module.Context._h1(C#0))
               else #_module.Term.Apply(_module.Context._h2(C#0),
                _module.__default.EvalExpr($ly, _module.Context._h3(C#0), t#0)))));

// definition axiom for _module.__default.EvalExpr for all literals(revealed)
axiom 10 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, C#0: DatatypeType, t#0: DatatypeType ::
    {:weight 3} { _module.__default.EvalExpr($LS($ly), Lit(C#0), Lit(t#0)) }
    _module.__default.EvalExpr#canCall(Lit(C#0), Lit(t#0))
         || (10 != $FunctionContextHeight
           &&
          $Is(C#0, Tclass._module.Context())
           && $Is(t#0, Tclass._module.Term())
           && Lit(_module.__default.IsContext($LS($LZ), Lit(C#0))))
       ==> (!Lit(_module.Context.Hole_q(Lit(C#0)))
           ==> (Lit(_module.Context.C__term_q(Lit(C#0)))
               ==> _module.__default.EvalExpr#canCall(Lit(_module.Context._h0(Lit(C#0))), Lit(t#0)))
             && (!Lit(_module.Context.C__term_q(Lit(C#0)))
               ==> _module.__default.EvalExpr#canCall(Lit(_module.Context._h3(Lit(C#0))), Lit(t#0))))
         && _module.__default.EvalExpr($LS($ly), Lit(C#0), Lit(t#0))
           == (if _module.Context.Hole_q(Lit(C#0))
             then t#0
             else (if _module.Context.C__term_q(Lit(C#0))
               then #_module.Term.Apply(Lit(_module.__default.EvalExpr($LS($ly), Lit(_module.Context._h0(Lit(C#0))), Lit(t#0))),
                Lit(_module.Context._h1(Lit(C#0))))
               else #_module.Term.Apply(Lit(_module.Context._h2(Lit(C#0))),
                Lit(_module.__default.EvalExpr($LS($ly), Lit(_module.Context._h3(Lit(C#0))), Lit(t#0)))))));

procedure CheckWellformed$$_module.__default.EvalExpr(C#0: DatatypeType where $Is(C#0, Tclass._module.Context()),
    t#0: DatatypeType where $Is(t#0, Tclass._module.Term()));
  free requires 10 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.EvalExpr(C#0: DatatypeType, t#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##C#0: DatatypeType;
  var b$reqreads#0: bool;
  var v#0: DatatypeType;
  var D#0: DatatypeType;
  var ##C#1: DatatypeType;
  var ##t#0: DatatypeType;
  var D#1: DatatypeType;
  var u#0: DatatypeType;
  var ##C#2: DatatypeType;
  var ##t#1: DatatypeType;
  var b$reqreads#1: bool;
  var b$reqreads#2: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;
    b$reqreads#2 := true;

    // AddWellformednessCheck for function EvalExpr
    assume {:captureState "Combinators.dfy(59,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    ##C#0 := C#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##C#0, Tclass._module.Context(), $Heap);
    b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    assume _module.__default.IsContext#canCall(C#0);
    assume _module.__default.IsContext($LS($LZ), C#0);
    assert b$reqreads#0;
    if (*)
    {
        assume $Is(_module.__default.EvalExpr($LS($LZ), C#0, t#0), Tclass._module.Term());
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
          $o != null && read($Heap, $o, alloc) ==> false);
        if (C#0 == #_module.Context.Hole())
        {
            assume _module.__default.EvalExpr($LS($LZ), C#0, t#0) == t#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.EvalExpr($LS($LZ), C#0, t#0), Tclass._module.Term());
        }
        else if (C#0 == #_module.Context.C_term(D#1, u#0))
        {
            assume $Is(D#1, Tclass._module.Context());
            assume $Is(u#0, Tclass._module.Term());
            ##C#2 := D#1;
            // assume allocatedness for argument to function
            assume $IsAlloc(##C#2, Tclass._module.Context(), $Heap);
            ##t#1 := t#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##t#1, Tclass._module.Term(), $Heap);
            assert {:subsumption 0} _module.__default.IsContext($LS($LS($LZ)), ##C#2);
            assume _module.__default.IsContext($LS($LZ), ##C#2);
            b$reqreads#2 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert DtRank(##C#2) < DtRank(C#0)
               || (DtRank(##C#2) == DtRank(C#0) && DtRank(##t#1) < DtRank(t#0));
            assume _module.__default.EvalExpr#canCall(D#1, t#0);
            assume _module.__default.EvalExpr($LS($LZ), C#0, t#0)
               == #_module.Term.Apply(_module.__default.EvalExpr($LS($LZ), D#1, t#0), u#0);
            assume _module.__default.EvalExpr#canCall(D#1, t#0);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.EvalExpr($LS($LZ), C#0, t#0), Tclass._module.Term());
        }
        else if (C#0 == #_module.Context.value_C(v#0, D#0))
        {
            assume $Is(v#0, Tclass._module.Term());
            assume $Is(D#0, Tclass._module.Context());
            ##C#1 := D#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##C#1, Tclass._module.Context(), $Heap);
            ##t#0 := t#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##t#0, Tclass._module.Term(), $Heap);
            assert {:subsumption 0} _module.__default.IsContext($LS($LS($LZ)), ##C#1);
            assume _module.__default.IsContext($LS($LZ), ##C#1);
            b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert DtRank(##C#1) < DtRank(C#0)
               || (DtRank(##C#1) == DtRank(C#0) && DtRank(##t#0) < DtRank(t#0));
            assume _module.__default.EvalExpr#canCall(D#0, t#0);
            assume _module.__default.EvalExpr($LS($LZ), C#0, t#0)
               == #_module.Term.Apply(v#0, _module.__default.EvalExpr($LS($LZ), D#0, t#0));
            assume _module.__default.EvalExpr#canCall(D#0, t#0);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.EvalExpr($LS($LZ), C#0, t#0), Tclass._module.Term());
        }
        else
        {
            assume false;
        }

        assert b$reqreads#1;
        assert b$reqreads#2;
    }
}



// function declaration for _module._default.Step
function _module.__default.Step(t#0: DatatypeType) : DatatypeType;

function _module.__default.Step#canCall(t#0: DatatypeType) : bool;

// consequence axiom for _module.__default.Step
axiom 5 <= $FunctionContextHeight
   ==> (forall t#0: DatatypeType ::
    { _module.__default.Step(t#0) }
    _module.__default.Step#canCall(t#0)
         || (5 != $FunctionContextHeight && $Is(t#0, Tclass._module.Term()))
       ==> (!_module.__default.ContainsS($LS($LZ), t#0)
           ==> !_module.__default.ContainsS($LS($LZ), _module.__default.Step(t#0))
             && (_module.__default.Step(t#0) == t#0
               || _module.__default.TermSize($LS($LZ), _module.__default.Step(t#0))
                 < _module.__default.TermSize($LS($LZ), t#0)))
         && $Is(_module.__default.Step(t#0), Tclass._module.Term()));

function _module.__default.Step#requires(DatatypeType) : bool;

// #requires axiom for _module.__default.Step
axiom (forall $Heap: Heap, t#0: DatatypeType ::
  { _module.__default.Step#requires(t#0), $IsGoodHeap($Heap) }
  $IsGoodHeap($Heap) && $Is(t#0, Tclass._module.Term())
     ==> _module.__default.Step#requires(t#0) == true);

// definition axiom for _module.__default.Step(revealed)
axiom 5 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, t#0: DatatypeType ::
    { _module.__default.Step(t#0), $IsGoodHeap($Heap) }
    _module.__default.Step#canCall(t#0)
         || (5 != $FunctionContextHeight
           &&
          $IsGoodHeap($Heap)
           && $Is(t#0, Tclass._module.Term()))
       ==> (!_module.Term.S_q(t#0)
           ==>
          !_module.Term.K_q(t#0)
           ==>
          !_module.Term.S_q(_module.Term.car(t#0))
           ==>
          !_module.Term.K_q(_module.Term.car(t#0))
           ==> (_module.Term.car(_module.Term.car(t#0)) == Lit(#_module.Term.K())
               ==> _module.__default.IsValue#canCall(_module.Term.cdr(_module.Term.car(t#0))))
             && (_module.__default.IsValue#canCall(_module.Term.cdr(_module.Term.car(t#0)))
                 && _module.__default.IsValue($LS($LZ), _module.Term.cdr(_module.Term.car(t#0)))
               ==> _module.__default.IsValue#canCall(_module.Term.cdr(t#0)))
             && (!(
                _module.Term.car(_module.Term.car(t#0)) == Lit(#_module.Term.K())
                 && _module.__default.IsValue($LS($LZ), _module.Term.cdr(_module.Term.car(t#0)))
                 && _module.__default.IsValue($LS($LZ), _module.Term.cdr(t#0)))
               ==> (_module.Term.car(_module.Term.car(_module.Term.car(t#0)))
                     == Lit(#_module.Term.S())
                   ==> _module.__default.IsValue#canCall(_module.Term.cdr(_module.Term.car(_module.Term.car(t#0)))))
                 && (_module.__default.IsValue#canCall(_module.Term.cdr(_module.Term.car(_module.Term.car(t#0))))
                     && _module.__default.IsValue($LS($LZ), _module.Term.cdr(_module.Term.car(_module.Term.car(t#0))))
                   ==> _module.__default.IsValue#canCall(_module.Term.cdr(_module.Term.car(t#0))))
                 && (_module.__default.IsValue#canCall(_module.Term.cdr(_module.Term.car(t#0)))
                     && _module.__default.IsValue($LS($LZ), _module.Term.cdr(_module.Term.car(t#0)))
                   ==> _module.__default.IsValue#canCall(_module.Term.cdr(t#0)))))
         && _module.__default.Step(t#0)
           == (if _module.Term.S_q(t#0)
             then t#0
             else (if _module.Term.K_q(t#0)
               then t#0
               else (if _module.Term.S_q(_module.Term.car(t#0))
                 then t#0
                 else (if _module.Term.K_q(_module.Term.car(t#0))
                   then t#0
                   else (if _module.Term.car(_module.Term.car(t#0)) == Lit(#_module.Term.K())
                       && _module.__default.IsValue($LS($LZ), _module.Term.cdr(_module.Term.car(t#0)))
                       && _module.__default.IsValue($LS($LZ), _module.Term.cdr(t#0))
                     then _module.Term.cdr(_module.Term.car(t#0))
                     else (if _module.Term.Apply_q(_module.Term.car(_module.Term.car(t#0)))
                         && _module.Term.car(_module.Term.car(_module.Term.car(t#0)))
                           == Lit(#_module.Term.S())
                         && _module.__default.IsValue($LS($LZ), _module.Term.cdr(_module.Term.car(_module.Term.car(t#0))))
                         && _module.__default.IsValue($LS($LZ), _module.Term.cdr(_module.Term.car(t#0)))
                         && _module.__default.IsValue($LS($LZ), _module.Term.cdr(t#0))
                       then #_module.Term.Apply(#_module.Term.Apply(_module.Term.cdr(_module.Term.car(_module.Term.car(t#0))), _module.Term.cdr(t#0)),
                        #_module.Term.Apply(_module.Term.cdr(_module.Term.car(t#0)), _module.Term.cdr(t#0)))
                       else t#0)))))));

// definition axiom for _module.__default.Step for all literals(revealed)
axiom 5 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, t#0: DatatypeType ::
    {:weight 3} { _module.__default.Step(Lit(t#0)), $IsGoodHeap($Heap) }
    _module.__default.Step#canCall(Lit(t#0))
         || (5 != $FunctionContextHeight
           &&
          $IsGoodHeap($Heap)
           && $Is(t#0, Tclass._module.Term()))
       ==> (!Lit(_module.Term.S_q(Lit(t#0)))
           ==>
          !Lit(_module.Term.K_q(Lit(t#0)))
           ==>
          !Lit(_module.Term.S_q(Lit(_module.Term.car(Lit(t#0)))))
           ==>
          !Lit(_module.Term.K_q(Lit(_module.Term.car(Lit(t#0)))))
           ==> (Lit(_module.Term.car(Lit(_module.Term.car(Lit(t#0))))) == Lit(#_module.Term.K())
               ==> _module.__default.IsValue#canCall(Lit(_module.Term.cdr(Lit(_module.Term.car(Lit(t#0)))))))
             && (_module.__default.IsValue#canCall(Lit(_module.Term.cdr(Lit(_module.Term.car(Lit(t#0))))))
                 && Lit(_module.__default.IsValue($LS($LZ), Lit(_module.Term.cdr(Lit(_module.Term.car(Lit(t#0)))))))
               ==> _module.__default.IsValue#canCall(Lit(_module.Term.cdr(Lit(t#0)))))
             && (!(
                Lit(_module.Term.car(Lit(_module.Term.car(Lit(t#0))))) == Lit(#_module.Term.K())
                 && _module.__default.IsValue($LS($LZ), Lit(_module.Term.cdr(Lit(_module.Term.car(Lit(t#0))))))
                 && _module.__default.IsValue($LS($LZ), Lit(_module.Term.cdr(Lit(t#0)))))
               ==> (Lit(_module.Term.car(Lit(_module.Term.car(Lit(_module.Term.car(Lit(t#0)))))))
                     == Lit(#_module.Term.S())
                   ==> _module.__default.IsValue#canCall(Lit(_module.Term.cdr(Lit(_module.Term.car(Lit(_module.Term.car(Lit(t#0)))))))))
                 && (_module.__default.IsValue#canCall(Lit(_module.Term.cdr(Lit(_module.Term.car(Lit(_module.Term.car(Lit(t#0))))))))
                     && Lit(_module.__default.IsValue($LS($LZ),
                        Lit(_module.Term.cdr(Lit(_module.Term.car(Lit(_module.Term.car(Lit(t#0)))))))))
                   ==> _module.__default.IsValue#canCall(Lit(_module.Term.cdr(Lit(_module.Term.car(Lit(t#0)))))))
                 && (_module.__default.IsValue#canCall(Lit(_module.Term.cdr(Lit(_module.Term.car(Lit(t#0))))))
                     && Lit(_module.__default.IsValue($LS($LZ), Lit(_module.Term.cdr(Lit(_module.Term.car(Lit(t#0)))))))
                   ==> _module.__default.IsValue#canCall(Lit(_module.Term.cdr(Lit(t#0)))))))
         && _module.__default.Step(Lit(t#0))
           == (if _module.Term.S_q(Lit(t#0))
             then t#0
             else (if _module.Term.K_q(Lit(t#0))
               then t#0
               else (if _module.Term.S_q(Lit(_module.Term.car(Lit(t#0))))
                 then t#0
                 else (if _module.Term.K_q(Lit(_module.Term.car(Lit(t#0))))
                   then t#0
                   else (if Lit(_module.Term.car(Lit(_module.Term.car(Lit(t#0))))) == Lit(#_module.Term.K())
                       && _module.__default.IsValue($LS($LZ), Lit(_module.Term.cdr(Lit(_module.Term.car(Lit(t#0))))))
                       && _module.__default.IsValue($LS($LZ), Lit(_module.Term.cdr(Lit(t#0))))
                     then _module.Term.cdr(Lit(_module.Term.car(Lit(t#0))))
                     else (if _module.Term.Apply_q(Lit(_module.Term.car(Lit(_module.Term.car(Lit(t#0))))))
                         && Lit(_module.Term.car(Lit(_module.Term.car(Lit(_module.Term.car(Lit(t#0)))))))
                           == Lit(#_module.Term.S())
                         && _module.__default.IsValue($LS($LZ),
                          Lit(_module.Term.cdr(Lit(_module.Term.car(Lit(_module.Term.car(Lit(t#0))))))))
                         && _module.__default.IsValue($LS($LZ), Lit(_module.Term.cdr(Lit(_module.Term.car(Lit(t#0))))))
                         && _module.__default.IsValue($LS($LZ), Lit(_module.Term.cdr(Lit(t#0))))
                       then #_module.Term.Apply(Lit(#_module.Term.Apply(Lit(_module.Term.cdr(Lit(_module.Term.car(Lit(_module.Term.car(Lit(t#0))))))),
                            Lit(_module.Term.cdr(Lit(t#0))))),
                        Lit(#_module.Term.Apply(Lit(_module.Term.cdr(Lit(_module.Term.car(Lit(t#0))))),
                            Lit(_module.Term.cdr(Lit(t#0))))))
                       else t#0)))))));

procedure CheckWellformed$$_module.__default.Step(t#0: DatatypeType where $Is(t#0, Tclass._module.Term()));
  free requires 5 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  ensures !_module.__default.ContainsS($LS($LZ), t#0)
     ==> !_module.__default.ContainsS($LS($LS($LZ)), _module.__default.Step(t#0));
  ensures !_module.__default.ContainsS($LS($LZ), t#0)
     ==> _module.__default.Step(t#0) == t#0
       || _module.__default.TermSize($LS($LS($LZ)), _module.__default.Step(t#0))
         < _module.__default.TermSize($LS($LS($LZ)), t#0);



implementation CheckWellformed$$_module.__default.Step(t#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##t#0: DatatypeType;
  var ##t#1: DatatypeType;
  var ##t#2: DatatypeType;
  var ##t#3: DatatypeType;
  var ##t#4: DatatypeType;
  var ##t#5: DatatypeType;
  var ##t#6: DatatypeType;
  var x#0: DatatypeType;
  var y#0: DatatypeType;
  var m#0: DatatypeType;
  var n#0: DatatypeType;
  var ##t#7: DatatypeType;
  var ##t#8: DatatypeType;
  var ##t#9: DatatypeType;
  var ##t#10: DatatypeType;
  var ##t#11: DatatypeType;
  var ##t#12: DatatypeType;
  var ##t#13: DatatypeType;
  var ##t#14: DatatypeType;
  var ##t#15: DatatypeType;
  var ##t#16: DatatypeType;
  var ##t#17: DatatypeType;
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

    // AddWellformednessCheck for function Step
    assume {:captureState "Combinators.dfy(99,16): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.Step(t#0), Tclass._module.Term());
        if (*)
        {
            ##t#0 := t#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##t#0, Tclass._module.Term(), $Heap);
            assume _module.__default.ContainsS#canCall(t#0);
            assume !_module.__default.ContainsS($LS($LZ), t#0);
            ##t#1 := t#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##t#1, Tclass._module.Term(), $Heap);
            assert t#0 == t#0 || DtRank(##t#1) < DtRank(t#0);
            assume t#0 == t#0 || _module.__default.Step#canCall(t#0);
            ##t#2 := _module.__default.Step(t#0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##t#2, Tclass._module.Term(), $Heap);
            assume _module.__default.ContainsS#canCall(_module.__default.Step(t#0));
            assume !_module.__default.ContainsS($LS($LZ), _module.__default.Step(t#0));
            ##t#3 := t#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##t#3, Tclass._module.Term(), $Heap);
            assert t#0 == t#0 || DtRank(##t#3) < DtRank(t#0);
            assume t#0 == t#0 || _module.__default.Step#canCall(t#0);
            if (_module.__default.Step(t#0) != t#0)
            {
                ##t#4 := t#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##t#4, Tclass._module.Term(), $Heap);
                assert t#0 == t#0 || DtRank(##t#4) < DtRank(t#0);
                assume t#0 == t#0 || _module.__default.Step#canCall(t#0);
                ##t#5 := _module.__default.Step(t#0);
                // assume allocatedness for argument to function
                assume $IsAlloc(##t#5, Tclass._module.Term(), $Heap);
                assume _module.__default.TermSize#canCall(_module.__default.Step(t#0));
                ##t#6 := t#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##t#6, Tclass._module.Term(), $Heap);
                assume _module.__default.TermSize#canCall(t#0);
            }

            assume _module.__default.Step(t#0) == t#0
               || _module.__default.TermSize($LS($LZ), _module.__default.Step(t#0))
                 < _module.__default.TermSize($LS($LZ), t#0);
        }
        else
        {
            assume !_module.__default.ContainsS($LS($LZ), t#0)
               ==> !_module.__default.ContainsS($LS($LZ), _module.__default.Step(t#0))
                 && (_module.__default.Step(t#0) == t#0
                   || _module.__default.TermSize($LS($LZ), _module.__default.Step(t#0))
                     < _module.__default.TermSize($LS($LZ), t#0));
        }

        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
          $o != null && read($Heap, $o, alloc) ==> false);
        if (t#0 == #_module.Term.S())
        {
            assume _module.__default.Step(t#0) == t#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.Step(t#0), Tclass._module.Term());
        }
        else if (t#0 == #_module.Term.K())
        {
            assume _module.__default.Step(t#0) == t#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.Step(t#0), Tclass._module.Term());
        }
        else if (t#0 == #_module.Term.Apply(x#0, y#0))
        {
            assume $Is(x#0, Tclass._module.Term());
            assume $Is(y#0, Tclass._module.Term());
            if (x#0 == #_module.Term.S())
            {
                assume _module.__default.Step(t#0) == t#0;
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(_module.__default.Step(t#0), Tclass._module.Term());
            }
            else if (x#0 == #_module.Term.K())
            {
                assume _module.__default.Step(t#0) == t#0;
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(_module.__default.Step(t#0), Tclass._module.Term());
            }
            else if (x#0 == #_module.Term.Apply(m#0, n#0))
            {
                assume $Is(m#0, Tclass._module.Term());
                assume $Is(n#0, Tclass._module.Term());
                if (m#0 == Lit(#_module.Term.K()))
                {
                    ##t#7 := n#0;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##t#7, Tclass._module.Term(), $Heap);
                    b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                    assume _module.__default.IsValue#canCall(n#0);
                }

                if (m#0 == Lit(#_module.Term.K()) && _module.__default.IsValue($LS($LZ), n#0))
                {
                    ##t#8 := y#0;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##t#8, Tclass._module.Term(), $Heap);
                    b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                    assume _module.__default.IsValue#canCall(y#0);
                }

                if (m#0 == Lit(#_module.Term.K())
                   && _module.__default.IsValue($LS($LZ), n#0)
                   && _module.__default.IsValue($LS($LZ), y#0))
                {
                    // ----- assert statement ----- Combinators.dfy(114,9)
                    ##t#9 := t#0;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##t#9, Tclass._module.Term(), $Heap);
                    assume _module.__default.ContainsS#canCall(t#0);
                    if (!_module.__default.ContainsS($LS($LZ), t#0))
                    {
                        ##t#10 := x#0;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##t#10, Tclass._module.Term(), $Heap);
                        assume _module.__default.ContainsS#canCall(x#0);
                    }

                    assume _module.__default.ContainsS#canCall(t#0)
                       && (!_module.__default.ContainsS($LS($LZ), t#0)
                         ==> _module.__default.ContainsS#canCall(x#0));
                    assert {:subsumption 0} !_module.__default.ContainsS($LS($LZ), t#0)
                       ==> !_module.__default.ContainsS($LS($LS($LZ)), x#0);
                    assume !_module.__default.ContainsS($LS($LZ), t#0)
                       ==> !_module.__default.ContainsS($LS($LZ), x#0);
                    // ----- assert statement ----- Combinators.dfy(115,9)
                    ##t#11 := n#0;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##t#11, Tclass._module.Term(), $Heap);
                    assume _module.__default.TermSize#canCall(n#0);
                    ##t#12 := #_module.Term.Apply(m#0, n#0);
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##t#12, Tclass._module.Term(), $Heap);
                    assume _module.__default.TermSize#canCall(#_module.Term.Apply(m#0, n#0));
                    assume _module.__default.TermSize#canCall(n#0)
                       && _module.__default.TermSize#canCall(#_module.Term.Apply(m#0, n#0));
                    assert {:subsumption 0} _module.__default.TermSize($LS($LS($LZ)), n#0)
                       < _module.__default.TermSize($LS($LS($LZ)), #_module.Term.Apply(m#0, n#0));
                    assume _module.__default.TermSize($LS($LZ), n#0)
                       < _module.__default.TermSize($LS($LZ), #_module.Term.Apply(m#0, n#0));
                    assume _module.__default.Step(t#0) == n#0;
                    assume true;
                    // CheckWellformedWithResult: any expression
                    assume $Is(_module.__default.Step(t#0), Tclass._module.Term());
                }
                else
                {
                    if (_module.Term.Apply_q(m#0))
                    {
                        assert _module.Term.Apply_q(m#0);
                    }

                    if (_module.Term.Apply_q(m#0) && _module.Term.car(m#0) == Lit(#_module.Term.S()))
                    {
                        assert _module.Term.Apply_q(m#0);
                        ##t#13 := _module.Term.cdr(m#0);
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##t#13, Tclass._module.Term(), $Heap);
                        b$reqreads#2 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                        assume _module.__default.IsValue#canCall(_module.Term.cdr(m#0));
                    }

                    if (_module.Term.Apply_q(m#0)
                       && _module.Term.car(m#0) == Lit(#_module.Term.S())
                       && _module.__default.IsValue($LS($LZ), _module.Term.cdr(m#0)))
                    {
                        ##t#14 := n#0;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##t#14, Tclass._module.Term(), $Heap);
                        b$reqreads#3 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                        assume _module.__default.IsValue#canCall(n#0);
                    }

                    if (_module.Term.Apply_q(m#0)
                       && _module.Term.car(m#0) == Lit(#_module.Term.S())
                       && _module.__default.IsValue($LS($LZ), _module.Term.cdr(m#0))
                       && _module.__default.IsValue($LS($LZ), n#0))
                    {
                        ##t#15 := y#0;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##t#15, Tclass._module.Term(), $Heap);
                        b$reqreads#4 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                        assume _module.__default.IsValue#canCall(y#0);
                    }

                    if (_module.Term.Apply_q(m#0)
                       && _module.Term.car(m#0) == Lit(#_module.Term.S())
                       && _module.__default.IsValue($LS($LZ), _module.Term.cdr(m#0))
                       && _module.__default.IsValue($LS($LZ), n#0)
                       && _module.__default.IsValue($LS($LZ), y#0))
                    {
                        // ----- assert statement ----- Combinators.dfy(119,9)
                        ##t#16 := m#0;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##t#16, Tclass._module.Term(), $Heap);
                        assume _module.__default.ContainsS#canCall(m#0);
                        if (_module.__default.ContainsS($LS($LZ), m#0))
                        {
                            ##t#17 := t#0;
                            // assume allocatedness for argument to function
                            assume $IsAlloc(##t#17, Tclass._module.Term(), $Heap);
                            assume _module.__default.ContainsS#canCall(t#0);
                        }

                        assume _module.__default.ContainsS#canCall(m#0)
                           && (_module.__default.ContainsS($LS($LZ), m#0)
                             ==> _module.__default.ContainsS#canCall(t#0));
                        assert {:subsumption 0} _module.__default.ContainsS($LS($LS($LZ)), m#0);
                        assert {:subsumption 0} _module.__default.ContainsS($LS($LS($LZ)), t#0);
                        assume _module.__default.ContainsS($LS($LZ), m#0)
                           && _module.__default.ContainsS($LS($LZ), t#0);
                        assert _module.Term.Apply_q(m#0);
                        assume _module.__default.Step(t#0)
                           == #_module.Term.Apply(#_module.Term.Apply(_module.Term.cdr(m#0), y#0), #_module.Term.Apply(n#0, y#0));
                        assume true;
                        // CheckWellformedWithResult: any expression
                        assume $Is(_module.__default.Step(t#0), Tclass._module.Term());
                    }
                    else
                    {
                        assume _module.__default.Step(t#0) == t#0;
                        assume true;
                        // CheckWellformedWithResult: any expression
                        assume $Is(_module.__default.Step(t#0), Tclass._module.Term());
                    }
                }
            }
            else
            {
                assume false;
            }
        }
        else
        {
            assume false;
        }

        assert b$reqreads#0;
        assert b$reqreads#1;
        assert b$reqreads#2;
        assert b$reqreads#3;
        assert b$reqreads#4;
    }
}



// function declaration for _module._default.FindAndStep
function _module.__default.FindAndStep($ly: LayerType, t#0: DatatypeType) : DatatypeType;

function _module.__default.FindAndStep#canCall(t#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, t#0: DatatypeType ::
  { _module.__default.FindAndStep($LS($ly), t#0) }
  _module.__default.FindAndStep($LS($ly), t#0)
     == _module.__default.FindAndStep($ly, t#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, t#0: DatatypeType ::
  { _module.__default.FindAndStep(AsFuelBottom($ly), t#0) }
  _module.__default.FindAndStep($ly, t#0)
     == _module.__default.FindAndStep($LZ, t#0));

// consequence axiom for _module.__default.FindAndStep
axiom 6 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, t#0: DatatypeType ::
    { _module.__default.FindAndStep($ly, t#0) }
    _module.__default.FindAndStep#canCall(t#0)
         || (6 != $FunctionContextHeight && $Is(t#0, Tclass._module.Term()))
       ==> (!_module.__default.ContainsS($LS($LZ), t#0)
           ==> !_module.__default.ContainsS($LS($LZ), _module.__default.FindAndStep($ly, t#0))
             && (_module.__default.FindAndStep($ly, t#0) == t#0
               || _module.__default.TermSize($LS($LZ), _module.__default.FindAndStep($ly, t#0))
                 < _module.__default.TermSize($LS($LZ), t#0)))
         && $Is(_module.__default.FindAndStep($ly, t#0), Tclass._module.Term()));

function _module.__default.FindAndStep#requires(LayerType, DatatypeType) : bool;

// #requires axiom for _module.__default.FindAndStep
axiom (forall $ly: LayerType, $Heap: Heap, t#0: DatatypeType ::
  { _module.__default.FindAndStep#requires($ly, t#0), $IsGoodHeap($Heap) }
  $IsGoodHeap($Heap) && $Is(t#0, Tclass._module.Term())
     ==> _module.__default.FindAndStep#requires($ly, t#0) == true);

// definition axiom for _module.__default.FindAndStep(revealed)
axiom 6 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, $Heap: Heap, t#0: DatatypeType ::
    { _module.__default.FindAndStep($LS($ly), t#0), $IsGoodHeap($Heap) }
    _module.__default.FindAndStep#canCall(t#0)
         || (6 != $FunctionContextHeight
           &&
          $IsGoodHeap($Heap)
           && $Is(t#0, Tclass._module.Term()))
       ==> _module.__default.Step#canCall(t#0)
         && (_module.__default.Step(t#0) != t#0 ==> _module.__default.Step#canCall(t#0))
         && (_module.__default.Step(t#0) == t#0
           ==>
          _module.Term.Apply_q(t#0)
           ==> _module.__default.FindAndStep#canCall(_module.Term.car(t#0))
             && (_module.__default.FindAndStep($ly, _module.Term.car(t#0))
                 != _module.Term.car(t#0)
               ==> _module.__default.FindAndStep#canCall(_module.Term.car(t#0)))
             && (_module.__default.FindAndStep($ly, _module.Term.car(t#0))
                 == _module.Term.car(t#0)
               ==> _module.__default.IsValue#canCall(_module.Term.car(t#0))
                 && (_module.__default.IsValue($LS($LZ), _module.Term.car(t#0))
                   ==> _module.__default.FindAndStep#canCall(_module.Term.cdr(t#0)))
                 && (_module.__default.IsValue($LS($LZ), _module.Term.car(t#0))
                     && _module.__default.FindAndStep($ly, _module.Term.cdr(t#0))
                       != _module.Term.cdr(t#0)
                   ==> _module.__default.FindAndStep#canCall(_module.Term.cdr(t#0)))))
         && _module.__default.FindAndStep($LS($ly), t#0)
           == (if _module.__default.Step(t#0) != t#0
             then _module.__default.Step(t#0)
             else (if !_module.Term.Apply_q(t#0)
               then t#0
               else (if _module.__default.FindAndStep($ly, _module.Term.car(t#0))
                   != _module.Term.car(t#0)
                 then #_module.Term.Apply(_module.__default.FindAndStep($ly, _module.Term.car(t#0)), _module.Term.cdr(t#0))
                 else (if _module.__default.IsValue($LS($LZ), _module.Term.car(t#0))
                     && _module.__default.FindAndStep($ly, _module.Term.cdr(t#0))
                       != _module.Term.cdr(t#0)
                   then #_module.Term.Apply(_module.Term.car(t#0), _module.__default.FindAndStep($ly, _module.Term.cdr(t#0)))
                   else t#0)))));

// definition axiom for _module.__default.FindAndStep for all literals(revealed)
axiom 6 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, $Heap: Heap, t#0: DatatypeType ::
    {:weight 3} { _module.__default.FindAndStep($LS($ly), Lit(t#0)), $IsGoodHeap($Heap) }
    _module.__default.FindAndStep#canCall(Lit(t#0))
         || (6 != $FunctionContextHeight
           &&
          $IsGoodHeap($Heap)
           && $Is(t#0, Tclass._module.Term()))
       ==> _module.__default.Step#canCall(Lit(t#0))
         && (Lit(_module.__default.Step(Lit(t#0)) != t#0)
           ==> _module.__default.Step#canCall(Lit(t#0)))
         && (!Lit(_module.__default.Step(Lit(t#0)) != t#0)
           ==>
          Lit(_module.Term.Apply_q(Lit(t#0)))
           ==> _module.__default.FindAndStep#canCall(Lit(_module.Term.car(Lit(t#0))))
             && (Lit(_module.__default.FindAndStep($LS($ly), Lit(_module.Term.car(Lit(t#0))))
                   != _module.Term.car(Lit(t#0)))
               ==> _module.__default.FindAndStep#canCall(Lit(_module.Term.car(Lit(t#0)))))
             && (!Lit(_module.__default.FindAndStep($LS($ly), Lit(_module.Term.car(Lit(t#0))))
                   != _module.Term.car(Lit(t#0)))
               ==> _module.__default.IsValue#canCall(Lit(_module.Term.car(Lit(t#0))))
                 && (Lit(_module.__default.IsValue($LS($LZ), Lit(_module.Term.car(Lit(t#0)))))
                   ==> _module.__default.FindAndStep#canCall(Lit(_module.Term.cdr(Lit(t#0)))))
                 && (Lit(_module.__default.IsValue($LS($LZ), Lit(_module.Term.car(Lit(t#0))))
                       && _module.__default.FindAndStep($LS($ly), Lit(_module.Term.cdr(Lit(t#0))))
                         != _module.Term.cdr(Lit(t#0)))
                   ==> _module.__default.FindAndStep#canCall(Lit(_module.Term.cdr(Lit(t#0)))))))
         && _module.__default.FindAndStep($LS($ly), Lit(t#0))
           == (if _module.__default.Step(Lit(t#0)) != t#0
             then _module.__default.Step(Lit(t#0))
             else (if !Lit(_module.Term.Apply_q(Lit(t#0)))
               then t#0
               else (if _module.__default.FindAndStep($LS($ly), Lit(_module.Term.car(Lit(t#0))))
                   != _module.Term.car(Lit(t#0))
                 then #_module.Term.Apply(Lit(_module.__default.FindAndStep($LS($ly), Lit(_module.Term.car(Lit(t#0))))),
                  Lit(_module.Term.cdr(Lit(t#0))))
                 else (if _module.__default.IsValue($LS($LZ), Lit(_module.Term.car(Lit(t#0))))
                     && _module.__default.FindAndStep($LS($ly), Lit(_module.Term.cdr(Lit(t#0))))
                       != _module.Term.cdr(Lit(t#0))
                   then #_module.Term.Apply(Lit(_module.Term.car(Lit(t#0))),
                    Lit(_module.__default.FindAndStep($LS($ly), Lit(_module.Term.cdr(Lit(t#0))))))
                   else t#0)))));

procedure CheckWellformed$$_module.__default.FindAndStep(t#0: DatatypeType where $Is(t#0, Tclass._module.Term()));
  free requires 6 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  ensures !_module.__default.ContainsS($LS($LZ), t#0)
     ==> !_module.__default.ContainsS($LS($LS($LZ)), _module.__default.FindAndStep($LS($LS($LZ)), t#0));
  ensures !_module.__default.ContainsS($LS($LZ), t#0)
     ==> _module.__default.FindAndStep($LS($LS($LZ)), t#0) == t#0
       || _module.__default.TermSize($LS($LS($LZ)), _module.__default.FindAndStep($LS($LS($LZ)), t#0))
         < _module.__default.TermSize($LS($LS($LZ)), t#0);



implementation CheckWellformed$$_module.__default.FindAndStep(t#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##t#0: DatatypeType;
  var ##t#1: DatatypeType;
  var ##t#2: DatatypeType;
  var ##t#3: DatatypeType;
  var ##t#4: DatatypeType;
  var ##t#5: DatatypeType;
  var ##t#6: DatatypeType;
  var ##t#7: DatatypeType;
  var ##t#8: DatatypeType;
  var ##t#9: DatatypeType;
  var ##t#10: DatatypeType;
  var ##t#11: DatatypeType;
  var ##t#12: DatatypeType;
  var ##t#13: DatatypeType;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;
  var b$reqreads#2: bool;
  var b$reqreads#3: bool;
  var b$reqreads#4: bool;
  var b$reqreads#5: bool;
  var b$reqreads#6: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;
    b$reqreads#2 := true;
    b$reqreads#3 := true;
    b$reqreads#4 := true;
    b$reqreads#5 := true;
    b$reqreads#6 := true;

    // AddWellformednessCheck for function FindAndStep
    assume {:captureState "Combinators.dfy(145,16): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.FindAndStep($LS($LZ), t#0), Tclass._module.Term());
        if (*)
        {
            ##t#0 := t#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##t#0, Tclass._module.Term(), $Heap);
            assume _module.__default.ContainsS#canCall(t#0);
            assume !_module.__default.ContainsS($LS($LZ), t#0);
            ##t#1 := t#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##t#1, Tclass._module.Term(), $Heap);
            assert t#0 == t#0 || DtRank(##t#1) < DtRank(t#0);
            assume t#0 == t#0 || _module.__default.FindAndStep#canCall(t#0);
            ##t#2 := _module.__default.FindAndStep($LS($LZ), t#0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##t#2, Tclass._module.Term(), $Heap);
            assume _module.__default.ContainsS#canCall(_module.__default.FindAndStep($LS($LZ), t#0));
            assume !_module.__default.ContainsS($LS($LZ), _module.__default.FindAndStep($LS($LZ), t#0));
            ##t#3 := t#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##t#3, Tclass._module.Term(), $Heap);
            assert t#0 == t#0 || DtRank(##t#3) < DtRank(t#0);
            assume t#0 == t#0 || _module.__default.FindAndStep#canCall(t#0);
            if (_module.__default.FindAndStep($LS($LZ), t#0) != t#0)
            {
                ##t#4 := t#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##t#4, Tclass._module.Term(), $Heap);
                assert t#0 == t#0 || DtRank(##t#4) < DtRank(t#0);
                assume t#0 == t#0 || _module.__default.FindAndStep#canCall(t#0);
                ##t#5 := _module.__default.FindAndStep($LS($LZ), t#0);
                // assume allocatedness for argument to function
                assume $IsAlloc(##t#5, Tclass._module.Term(), $Heap);
                assume _module.__default.TermSize#canCall(_module.__default.FindAndStep($LS($LZ), t#0));
                ##t#6 := t#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##t#6, Tclass._module.Term(), $Heap);
                assume _module.__default.TermSize#canCall(t#0);
            }

            assume _module.__default.FindAndStep($LS($LZ), t#0) == t#0
               || _module.__default.TermSize($LS($LZ), _module.__default.FindAndStep($LS($LZ), t#0))
                 < _module.__default.TermSize($LS($LZ), t#0);
        }
        else
        {
            assume !_module.__default.ContainsS($LS($LZ), t#0)
               ==> !_module.__default.ContainsS($LS($LZ), _module.__default.FindAndStep($LS($LZ), t#0))
                 && (_module.__default.FindAndStep($LS($LZ), t#0) == t#0
                   || _module.__default.TermSize($LS($LZ), _module.__default.FindAndStep($LS($LZ), t#0))
                     < _module.__default.TermSize($LS($LZ), t#0));
        }

        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
          $o != null && read($Heap, $o, alloc) ==> false);
        ##t#7 := t#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##t#7, Tclass._module.Term(), $Heap);
        b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume _module.__default.Step#canCall(t#0);
        if (_module.__default.Step(t#0) != t#0)
        {
            ##t#8 := t#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##t#8, Tclass._module.Term(), $Heap);
            b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume _module.__default.Step#canCall(t#0);
            assume _module.__default.FindAndStep($LS($LZ), t#0) == _module.__default.Step(t#0);
            assume _module.__default.Step#canCall(t#0);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.FindAndStep($LS($LZ), t#0), Tclass._module.Term());
        }
        else
        {
            if (!_module.Term.Apply_q(t#0))
            {
                assume _module.__default.FindAndStep($LS($LZ), t#0) == t#0;
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(_module.__default.FindAndStep($LS($LZ), t#0), Tclass._module.Term());
            }
            else
            {
                assert _module.Term.Apply_q(t#0);
                ##t#9 := _module.Term.car(t#0);
                // assume allocatedness for argument to function
                assume $IsAlloc(##t#9, Tclass._module.Term(), $Heap);
                b$reqreads#2 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                assert DtRank(##t#9) < DtRank(t#0);
                assume _module.__default.FindAndStep#canCall(_module.Term.car(t#0));
                assert _module.Term.Apply_q(t#0);
                if (_module.__default.FindAndStep($LS($LZ), _module.Term.car(t#0))
                   != _module.Term.car(t#0))
                {
                    assert _module.Term.Apply_q(t#0);
                    ##t#10 := _module.Term.car(t#0);
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##t#10, Tclass._module.Term(), $Heap);
                    b$reqreads#3 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                    assert DtRank(##t#10) < DtRank(t#0);
                    assume _module.__default.FindAndStep#canCall(_module.Term.car(t#0));
                    assert _module.Term.Apply_q(t#0);
                    assume _module.__default.FindAndStep($LS($LZ), t#0)
                       == #_module.Term.Apply(_module.__default.FindAndStep($LS($LZ), _module.Term.car(t#0)),
                        _module.Term.cdr(t#0));
                    assume _module.__default.FindAndStep#canCall(_module.Term.car(t#0));
                    // CheckWellformedWithResult: any expression
                    assume $Is(_module.__default.FindAndStep($LS($LZ), t#0), Tclass._module.Term());
                }
                else
                {
                    assert _module.Term.Apply_q(t#0);
                    ##t#11 := _module.Term.car(t#0);
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##t#11, Tclass._module.Term(), $Heap);
                    b$reqreads#4 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                    assume _module.__default.IsValue#canCall(_module.Term.car(t#0));
                    if (_module.__default.IsValue($LS($LZ), _module.Term.car(t#0)))
                    {
                        assert _module.Term.Apply_q(t#0);
                        ##t#12 := _module.Term.cdr(t#0);
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##t#12, Tclass._module.Term(), $Heap);
                        b$reqreads#5 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                        assert DtRank(##t#12) < DtRank(t#0);
                        assume _module.__default.FindAndStep#canCall(_module.Term.cdr(t#0));
                        assert _module.Term.Apply_q(t#0);
                    }

                    if (_module.__default.IsValue($LS($LZ), _module.Term.car(t#0))
                       && _module.__default.FindAndStep($LS($LZ), _module.Term.cdr(t#0))
                         != _module.Term.cdr(t#0))
                    {
                        assert _module.Term.Apply_q(t#0);
                        assert _module.Term.Apply_q(t#0);
                        ##t#13 := _module.Term.cdr(t#0);
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##t#13, Tclass._module.Term(), $Heap);
                        b$reqreads#6 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                        assert DtRank(##t#13) < DtRank(t#0);
                        assume _module.__default.FindAndStep#canCall(_module.Term.cdr(t#0));
                        assume _module.__default.FindAndStep($LS($LZ), t#0)
                           == #_module.Term.Apply(_module.Term.car(t#0),
                            _module.__default.FindAndStep($LS($LZ), _module.Term.cdr(t#0)));
                        assume _module.__default.FindAndStep#canCall(_module.Term.cdr(t#0));
                        // CheckWellformedWithResult: any expression
                        assume $Is(_module.__default.FindAndStep($LS($LZ), t#0), Tclass._module.Term());
                    }
                    else
                    {
                        assume _module.__default.FindAndStep($LS($LZ), t#0) == t#0;
                        assume true;
                        // CheckWellformedWithResult: any expression
                        assume $Is(_module.__default.FindAndStep($LS($LZ), t#0), Tclass._module.Term());
                    }
                }
            }
        }

        assert b$reqreads#0;
        assert b$reqreads#1;
        assert b$reqreads#2;
        assert b$reqreads#3;
        assert b$reqreads#4;
        assert b$reqreads#5;
        assert b$reqreads#6;
    }
}



// function declaration for _module._default.IsTerminal
function _module.__default.IsTerminal(t#0: DatatypeType) : bool;

function _module.__default.IsTerminal#canCall(t#0: DatatypeType) : bool;

// consequence axiom for _module.__default.IsTerminal
axiom 11 <= $FunctionContextHeight
   ==> (forall t#0: DatatypeType ::
    { _module.__default.IsTerminal(t#0) }
    _module.__default.IsTerminal#canCall(t#0)
         || (11 != $FunctionContextHeight && $Is(t#0, Tclass._module.Term()))
       ==> true);

function _module.__default.IsTerminal#requires(DatatypeType) : bool;

// #requires axiom for _module.__default.IsTerminal
axiom (forall t#0: DatatypeType ::
  { _module.__default.IsTerminal#requires(t#0) }
  $Is(t#0, Tclass._module.Term())
     ==> _module.__default.IsTerminal#requires(t#0) == true);

// definition axiom for _module.__default.IsTerminal(revealed)
axiom 11 <= $FunctionContextHeight
   ==> (forall t#0: DatatypeType ::
    { _module.__default.IsTerminal(t#0) }
    _module.__default.IsTerminal#canCall(t#0)
         || (11 != $FunctionContextHeight && $Is(t#0, Tclass._module.Term()))
       ==> (forall C#0: DatatypeType, u#0: DatatypeType ::
          { _module.__default.Step(u#0), _module.__default.IsContext($LS($LZ), C#0) }
            { _module.__default.EvalExpr($LS($LZ), C#0, u#0) }
          $Is(C#0, Tclass._module.Context()) && $Is(u#0, Tclass._module.Term())
             ==> _module.__default.IsContext#canCall(C#0)
               && (_module.__default.IsContext($LS($LZ), C#0)
                 ==> _module.__default.EvalExpr#canCall(C#0, u#0))
               && (_module.__default.EvalExpr#canCall(C#0, u#0)
                   && t#0 == _module.__default.EvalExpr($LS($LZ), C#0, u#0)
                 ==> _module.__default.Step#canCall(u#0)))
         && _module.__default.IsTerminal(t#0)
           == !(exists C#0: DatatypeType, u#0: DatatypeType ::
            {:_induction C#0, u#0} { _module.__default.Step(u#0), _module.__default.IsContext($LS($LZ), C#0) }
              { _module.__default.EvalExpr($LS($LZ), C#0, u#0) }
            $Is(C#0, Tclass._module.Context())
               && $Is(u#0, Tclass._module.Term())
               &&
              _module.__default.IsContext($LS($LZ), C#0)
               && t#0 == _module.__default.EvalExpr($LS($LZ), C#0, u#0)
               && _module.__default.Step(u#0) != u#0));

// definition axiom for _module.__default.IsTerminal for all literals(revealed)
axiom 11 <= $FunctionContextHeight
   ==> (forall t#0: DatatypeType ::
    {:weight 3} { _module.__default.IsTerminal(Lit(t#0)) }
    _module.__default.IsTerminal#canCall(Lit(t#0))
         || (11 != $FunctionContextHeight && $Is(t#0, Tclass._module.Term()))
       ==> (forall C#1: DatatypeType, u#1: DatatypeType ::
          { _module.__default.Step(u#1), _module.__default.IsContext($LS($LZ), C#1) }
            { _module.__default.EvalExpr($LS($LZ), C#1, u#1) }
          $Is(C#1, Tclass._module.Context()) && $Is(u#1, Tclass._module.Term())
             ==> _module.__default.IsContext#canCall(C#1)
               && (_module.__default.IsContext($LS($LZ), C#1)
                 ==> _module.__default.EvalExpr#canCall(C#1, u#1))
               && (_module.__default.EvalExpr#canCall(C#1, u#1)
                   && Lit(t#0) == _module.__default.EvalExpr($LS($LZ), C#1, u#1)
                 ==> _module.__default.Step#canCall(u#1)))
         && _module.__default.IsTerminal(Lit(t#0))
           == !(exists C#1: DatatypeType, u#1: DatatypeType ::
            {:_induction C#1, u#1} { _module.__default.Step(u#1), _module.__default.IsContext($LS($LZ), C#1) }
              { _module.__default.EvalExpr($LS($LZ), C#1, u#1) }
            $Is(C#1, Tclass._module.Context())
               && $Is(u#1, Tclass._module.Term())
               &&
              _module.__default.IsContext($LS($LZ), C#1)
               && Lit(t#0) == _module.__default.EvalExpr($LS($LZ), C#1, u#1)
               && _module.__default.Step(u#1) != u#1));

procedure CheckWellformed$$_module.__default.IsTerminal(t#0: DatatypeType where $Is(t#0, Tclass._module.Term()));
  free requires 11 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.IsTerminal(t#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var C#2: DatatypeType;
  var u#2: DatatypeType;
  var ##C#0: DatatypeType;
  var ##C#1: DatatypeType;
  var ##t#0: DatatypeType;
  var ##t#1: DatatypeType;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;
  var b$reqreads#2: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;
    b$reqreads#2 := true;

    // AddWellformednessCheck for function IsTerminal
    assume {:captureState "Combinators.dfy(166,9): initial state"} true;
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
        havoc C#2;
        assume $Is(C#2, Tclass._module.Context());
        havoc u#2;
        assume $Is(u#2, Tclass._module.Term());
        // Begin Comprehension WF check
        ##C#0 := C#2;
        // assume allocatedness for argument to function
        assume $IsAlloc(##C#0, Tclass._module.Context(), $Heap);
        b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume _module.__default.IsContext#canCall(C#2);
        if (_module.__default.IsContext($LS($LZ), C#2))
        {
            ##C#1 := C#2;
            // assume allocatedness for argument to function
            assume $IsAlloc(##C#1, Tclass._module.Context(), $Heap);
            ##t#0 := u#2;
            // assume allocatedness for argument to function
            assume $IsAlloc(##t#0, Tclass._module.Term(), $Heap);
            assert {:subsumption 0} _module.__default.IsContext($LS($LS($LZ)), ##C#1);
            assume _module.__default.IsContext($LS($LZ), ##C#1);
            b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume _module.__default.EvalExpr#canCall(C#2, u#2);
        }

        if (_module.__default.IsContext($LS($LZ), C#2)
           && t#0 == _module.__default.EvalExpr($LS($LZ), C#2, u#2))
        {
            ##t#1 := u#2;
            // assume allocatedness for argument to function
            assume $IsAlloc(##t#1, Tclass._module.Term(), $Heap);
            b$reqreads#2 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume _module.__default.Step#canCall(u#2);
        }

        // End Comprehension WF check
        assume _module.__default.IsTerminal(t#0)
           == !(exists C#3: DatatypeType, u#3: DatatypeType ::
            {:_induction C#3, u#3} { _module.__default.Step(u#3), _module.__default.IsContext($LS($LZ), C#3) }
              { _module.__default.EvalExpr($LS($LZ), C#3, u#3) }
            $Is(C#3, Tclass._module.Context())
               && $Is(u#3, Tclass._module.Term())
               &&
              _module.__default.IsContext($LS($LZ), C#3)
               && t#0 == _module.__default.EvalExpr($LS($LZ), C#3, u#3)
               && _module.__default.Step(u#3) != u#3);
        assume (forall C#3: DatatypeType, u#3: DatatypeType ::
          { _module.__default.Step(u#3), _module.__default.IsContext($LS($LZ), C#3) }
            { _module.__default.EvalExpr($LS($LZ), C#3, u#3) }
          $Is(C#3, Tclass._module.Context()) && $Is(u#3, Tclass._module.Term())
             ==> _module.__default.IsContext#canCall(C#3)
               && (_module.__default.IsContext($LS($LZ), C#3)
                 ==> _module.__default.EvalExpr#canCall(C#3, u#3))
               && (_module.__default.EvalExpr#canCall(C#3, u#3)
                   && t#0 == _module.__default.EvalExpr($LS($LZ), C#3, u#3)
                 ==> _module.__default.Step#canCall(u#3)));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.IsTerminal(t#0), TBool);
        assert b$reqreads#0;
        assert b$reqreads#1;
        assert b$reqreads#2;
    }
}



procedure {:_induction t#0} CheckWellformed$$_module.__default.Theorem__FindAndStep(t#0: DatatypeType
       where $Is(t#0, Tclass._module.Term())
         && $IsAlloc(t#0, Tclass._module.Term(), $Heap)
         && $IsA#_module.Term(t#0));
  free requires 14 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:_induction t#0} CheckWellformed$$_module.__default.Theorem__FindAndStep(t#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##t#0: DatatypeType;
  var ##t#1: DatatypeType;
  var ##t#2: DatatypeType;
  var C#0: DatatypeType;
  var u#0: DatatypeType;
  var ##C#0: DatatypeType;
  var ##C#1: DatatypeType;
  var ##t#3: DatatypeType;
  var ##t#4: DatatypeType;
  var ##t#5: DatatypeType;
  var ##t#6: DatatypeType;
  var ##C#2: DatatypeType;
  var ##t#7: DatatypeType;

    // AddMethodImpl: Theorem_FindAndStep, CheckWellformed$$_module.__default.Theorem__FindAndStep
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "Combinators.dfy(173,6): initial state"} true;
    havoc $Heap;
    assume old($Heap) == $Heap;
    assume {:captureState "Combinators.dfy(177,30): post-state"} true;
    if (*)
    {
        ##t#0 := t#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##t#0, Tclass._module.Term(), $Heap);
        assume _module.__default.FindAndStep#canCall(t#0);
        assume _module.__default.FindAndStep($LS($LZ), t#0) == t#0;
        ##t#1 := t#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##t#1, Tclass._module.Term(), $Heap);
        assume _module.__default.IsTerminal#canCall(t#0);
        assume _module.__default.IsTerminal(t#0);
    }
    else
    {
        assume _module.__default.FindAndStep($LS($LZ), t#0) == t#0
           ==> _module.__default.IsTerminal(t#0);
    }

    if (*)
    {
        ##t#2 := t#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##t#2, Tclass._module.Term(), $Heap);
        assume _module.__default.FindAndStep#canCall(t#0);
        assume _module.__default.FindAndStep($LS($LZ), t#0) != t#0;
        havoc C#0;
        assume $Is(C#0, Tclass._module.Context());
        havoc u#0;
        assume $Is(u#0, Tclass._module.Term());
        ##C#0 := C#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##C#0, Tclass._module.Context(), $Heap);
        assume _module.__default.IsContext#canCall(C#0);
        assume _module.__default.IsContext($LS($LZ), C#0);
        ##C#1 := C#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##C#1, Tclass._module.Context(), $Heap);
        ##t#3 := u#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##t#3, Tclass._module.Term(), $Heap);
        assert {:subsumption 0} _module.__default.IsContext($LS($LS($LZ)), ##C#1);
        assume _module.__default.IsContext($LS($LZ), ##C#1);
        assume _module.__default.EvalExpr#canCall(C#0, u#0);
        assume t#0 == _module.__default.EvalExpr($LS($LZ), C#0, u#0);
        ##t#4 := u#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##t#4, Tclass._module.Term(), $Heap);
        assume _module.__default.Step#canCall(u#0);
        assume _module.__default.Step(u#0) != u#0;
        ##t#5 := t#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##t#5, Tclass._module.Term(), $Heap);
        assume _module.__default.FindAndStep#canCall(t#0);
        ##t#6 := u#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##t#6, Tclass._module.Term(), $Heap);
        assume _module.__default.Step#canCall(u#0);
        ##C#2 := C#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##C#2, Tclass._module.Context(), $Heap);
        ##t#7 := _module.__default.Step(u#0);
        // assume allocatedness for argument to function
        assume $IsAlloc(##t#7, Tclass._module.Term(), $Heap);
        assert {:subsumption 0} _module.__default.IsContext($LS($LS($LZ)), ##C#2);
        assume _module.__default.IsContext($LS($LZ), ##C#2);
        assume _module.__default.EvalExpr#canCall(C#0, _module.__default.Step(u#0));
        assume _module.__default.FindAndStep($LS($LZ), t#0)
           == _module.__default.EvalExpr($LS($LZ), C#0, _module.__default.Step(u#0));
    }
    else
    {
        assume _module.__default.FindAndStep($LS($LZ), t#0) != t#0
           ==> (exists C#1: DatatypeType, u#1: DatatypeType ::
            {:_induction C#1, u#1} { _module.__default.Step(u#1), _module.__default.IsContext($LS($LZ), C#1) }
            $Is(C#1, Tclass._module.Context())
               && $Is(u#1, Tclass._module.Term())
               &&
              _module.__default.IsContext($LS($LZ), C#1)
               && t#0 == _module.__default.EvalExpr($LS($LZ), C#1, u#1)
               && _module.__default.Step(u#1) != u#1
               && _module.__default.FindAndStep($LS($LZ), t#0)
                 == _module.__default.EvalExpr($LS($LZ), C#1, _module.__default.Step(u#1)));
    }
}



procedure {:_induction t#0} Call$$_module.__default.Theorem__FindAndStep(t#0: DatatypeType
       where $Is(t#0, Tclass._module.Term())
         && $IsAlloc(t#0, Tclass._module.Term(), $Heap)
         && $IsA#_module.Term(t#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.FindAndStep#canCall(t#0)
     && (_module.__default.FindAndStep($LS($LZ), t#0) == t#0
       ==> _module.__default.IsTerminal#canCall(t#0));
  free ensures _module.__default.FindAndStep($LS($LZ), t#0) == t#0
     ==> _module.__default.IsTerminal#canCall(t#0)
       &&
      _module.__default.IsTerminal(t#0)
       && !(exists C#2: DatatypeType, u#2: DatatypeType ::
        {:_induction C#2, u#2} { _module.__default.Step(u#2), _module.__default.IsContext($LS($LZ), C#2) }
          { _module.__default.EvalExpr($LS($LZ), C#2, u#2) }
        $Is(C#2, Tclass._module.Context())
           && $Is(u#2, Tclass._module.Term())
           &&
          _module.__default.IsContext($LS($LZ), C#2)
           && t#0 == _module.__default.EvalExpr($LS($LZ), C#2, u#2)
           && _module.__default.Step(u#2) != u#2);
  free ensures _module.__default.FindAndStep#canCall(t#0)
     && (_module.__default.FindAndStep($LS($LZ), t#0) != t#0
       ==> (forall C#1: DatatypeType, u#1: DatatypeType ::
        { _module.__default.Step(u#1), _module.__default.IsContext($LS($LZ), C#1) }
        $Is(C#1, Tclass._module.Context()) && $Is(u#1, Tclass._module.Term())
           ==> _module.__default.IsContext#canCall(C#1)
             && (_module.__default.IsContext($LS($LZ), C#1)
               ==> _module.__default.EvalExpr#canCall(C#1, u#1))
             && (_module.__default.EvalExpr#canCall(C#1, u#1)
                 && t#0 == _module.__default.EvalExpr($LS($LZ), C#1, u#1)
               ==> _module.__default.Step#canCall(u#1))
             && (_module.__default.Step#canCall(u#1) && _module.__default.Step(u#1) != u#1
               ==> _module.__default.FindAndStep#canCall(t#0)
                 &&
                _module.__default.Step#canCall(u#1)
                 && _module.__default.EvalExpr#canCall(C#1, _module.__default.Step(u#1)))));
  free ensures _module.__default.FindAndStep($LS($LZ), t#0) != t#0
     ==> (exists C#1: DatatypeType, u#1: DatatypeType ::
      {:_induction C#1, u#1} { _module.__default.Step(u#1), _module.__default.IsContext($LS($LS($LZ)), C#1) }
      $Is(C#1, Tclass._module.Context())
         && $Is(u#1, Tclass._module.Term())
         &&
        _module.__default.IsContext($LS($LS($LZ)), C#1)
         && t#0 == _module.__default.EvalExpr($LS($LS($LZ)), C#1, u#1)
         && _module.__default.Step(u#1) != u#1
         && _module.__default.FindAndStep($LS($LS($LZ)), t#0)
           == _module.__default.EvalExpr($LS($LS($LZ)), C#1, _module.__default.Step(u#1)));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction t#0} Impl$$_module.__default.Theorem__FindAndStep(t#0: DatatypeType
       where $Is(t#0, Tclass._module.Term())
         && $IsAlloc(t#0, Tclass._module.Term(), $Heap)
         && $IsA#_module.Term(t#0))
   returns ($_reverifyPost: bool);
  free requires 14 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.FindAndStep#canCall(t#0)
     && (_module.__default.FindAndStep($LS($LZ), t#0) == t#0
       ==> _module.__default.IsTerminal#canCall(t#0));
  ensures _module.__default.FindAndStep($LS($LZ), t#0) == t#0
     ==>
    _module.__default.IsTerminal#canCall(t#0)
     ==> _module.__default.IsTerminal(t#0)
       || !(exists C#3: DatatypeType, u#3: DatatypeType ::
        { _module.__default.Step(u#3), _module.__default.IsContext($LS($LS($LZ)), C#3) }
          { _module.__default.EvalExpr($LS($LS($LZ)), C#3, u#3) }
        $Is(C#3, Tclass._module.Context())
           && $Is(u#3, Tclass._module.Term())
           && (forall C$ih#1#0: DatatypeType, u$ih#1#0: DatatypeType ::
            { _module.__default.Step(u$ih#1#0), _module.__default.IsContext($LS($LZ), C$ih#1#0) }
              { _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0) }
            $Is(C$ih#1#0, Tclass._module.Context()) && $Is(u$ih#1#0, Tclass._module.Term())
               ==>
              DtRank(C$ih#1#0) < DtRank(C#3)
                 || (DtRank(C$ih#1#0) == DtRank(C#3) && DtRank(u$ih#1#0) < DtRank(u#3))
               ==> !(
                _module.__default.IsContext($LS($LZ), C$ih#1#0)
                 && t#0 == _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0)
                 && _module.__default.Step(u$ih#1#0) != u$ih#1#0))
           &&
          true
           && #_module.Context.Hole() == C#3
           && #_module.Term.S() == u#3
           &&
          _module.__default.IsContext($LS($LS($LZ)), C#3)
           && t#0 == _module.__default.EvalExpr($LS($LS($LZ)), C#3, u#3)
           && _module.__default.Step(u#3) != u#3);
  ensures _module.__default.FindAndStep($LS($LZ), t#0) == t#0
     ==>
    _module.__default.IsTerminal#canCall(t#0)
     ==> _module.__default.IsTerminal(t#0)
       || !(exists C#3: DatatypeType, u#3: DatatypeType ::
        { _module.__default.Step(u#3), _module.__default.IsContext($LS($LS($LZ)), C#3) }
          { _module.__default.EvalExpr($LS($LS($LZ)), C#3, u#3) }
        $Is(C#3, Tclass._module.Context())
           && $Is(u#3, Tclass._module.Term())
           && (forall C$ih#1#0: DatatypeType, u$ih#1#0: DatatypeType ::
            { _module.__default.Step(u$ih#1#0), _module.__default.IsContext($LS($LZ), C$ih#1#0) }
              { _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0) }
            $Is(C$ih#1#0, Tclass._module.Context()) && $Is(u$ih#1#0, Tclass._module.Term())
               ==>
              DtRank(C$ih#1#0) < DtRank(C#3)
                 || (DtRank(C$ih#1#0) == DtRank(C#3) && DtRank(u$ih#1#0) < DtRank(u#3))
               ==> !(
                _module.__default.IsContext($LS($LZ), C$ih#1#0)
                 && t#0 == _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0)
                 && _module.__default.Step(u$ih#1#0) != u$ih#1#0))
           &&
          true
           && (exists a#7#0#0: DatatypeType, a#7#1#0: DatatypeType ::
            { #_module.Context.C_term(a#7#0#0, a#7#1#0) }
            $Is(a#7#0#0, Tclass._module.Context())
               && $Is(a#7#1#0, Tclass._module.Term())
               && #_module.Context.C_term(a#7#0#0, a#7#1#0) == C#3)
           && #_module.Term.S() == u#3
           &&
          _module.__default.IsContext($LS($LS($LZ)), C#3)
           && t#0 == _module.__default.EvalExpr($LS($LS($LZ)), C#3, u#3)
           && _module.__default.Step(u#3) != u#3);
  ensures _module.__default.FindAndStep($LS($LZ), t#0) == t#0
     ==>
    _module.__default.IsTerminal#canCall(t#0)
     ==> _module.__default.IsTerminal(t#0)
       || !(exists C#3: DatatypeType, u#3: DatatypeType ::
        { _module.__default.Step(u#3), _module.__default.IsContext($LS($LS($LZ)), C#3) }
          { _module.__default.EvalExpr($LS($LS($LZ)), C#3, u#3) }
        $Is(C#3, Tclass._module.Context())
           && $Is(u#3, Tclass._module.Term())
           && (forall C$ih#1#0: DatatypeType, u$ih#1#0: DatatypeType ::
            { _module.__default.Step(u$ih#1#0), _module.__default.IsContext($LS($LZ), C$ih#1#0) }
              { _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0) }
            $Is(C$ih#1#0, Tclass._module.Context()) && $Is(u$ih#1#0, Tclass._module.Term())
               ==>
              DtRank(C$ih#1#0) < DtRank(C#3)
                 || (DtRank(C$ih#1#0) == DtRank(C#3) && DtRank(u$ih#1#0) < DtRank(u#3))
               ==> !(
                _module.__default.IsContext($LS($LZ), C$ih#1#0)
                 && t#0 == _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0)
                 && _module.__default.Step(u$ih#1#0) != u$ih#1#0))
           &&
          true
           && (exists a#8#0#0: DatatypeType, a#8#1#0: DatatypeType ::
            { #_module.Context.value_C(a#8#0#0, a#8#1#0) }
            $Is(a#8#0#0, Tclass._module.Term())
               && $Is(a#8#1#0, Tclass._module.Context())
               && #_module.Context.value_C(a#8#0#0, a#8#1#0) == C#3)
           && #_module.Term.S() == u#3
           &&
          _module.__default.IsContext($LS($LS($LZ)), C#3)
           && t#0 == _module.__default.EvalExpr($LS($LS($LZ)), C#3, u#3)
           && _module.__default.Step(u#3) != u#3);
  ensures _module.__default.FindAndStep($LS($LZ), t#0) == t#0
     ==>
    _module.__default.IsTerminal#canCall(t#0)
     ==> _module.__default.IsTerminal(t#0)
       || !(exists C#3: DatatypeType, u#3: DatatypeType ::
        { _module.__default.Step(u#3), _module.__default.IsContext($LS($LS($LZ)), C#3) }
          { _module.__default.EvalExpr($LS($LS($LZ)), C#3, u#3) }
        $Is(C#3, Tclass._module.Context())
           && $Is(u#3, Tclass._module.Term())
           && (forall C$ih#1#0: DatatypeType, u$ih#1#0: DatatypeType ::
            { _module.__default.Step(u$ih#1#0), _module.__default.IsContext($LS($LZ), C$ih#1#0) }
              { _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0) }
            $Is(C$ih#1#0, Tclass._module.Context()) && $Is(u$ih#1#0, Tclass._module.Term())
               ==>
              DtRank(C$ih#1#0) < DtRank(C#3)
                 || (DtRank(C$ih#1#0) == DtRank(C#3) && DtRank(u$ih#1#0) < DtRank(u#3))
               ==> !(
                _module.__default.IsContext($LS($LZ), C$ih#1#0)
                 && t#0 == _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0)
                 && _module.__default.Step(u$ih#1#0) != u$ih#1#0))
           &&
          true
           && #_module.Context.Hole() == C#3
           && #_module.Term.K() == u#3
           &&
          _module.__default.IsContext($LS($LS($LZ)), C#3)
           && t#0 == _module.__default.EvalExpr($LS($LS($LZ)), C#3, u#3)
           && _module.__default.Step(u#3) != u#3);
  ensures _module.__default.FindAndStep($LS($LZ), t#0) == t#0
     ==>
    _module.__default.IsTerminal#canCall(t#0)
     ==> _module.__default.IsTerminal(t#0)
       || !(exists C#3: DatatypeType, u#3: DatatypeType ::
        { _module.__default.Step(u#3), _module.__default.IsContext($LS($LS($LZ)), C#3) }
          { _module.__default.EvalExpr($LS($LS($LZ)), C#3, u#3) }
        $Is(C#3, Tclass._module.Context())
           && $Is(u#3, Tclass._module.Term())
           && (forall C$ih#1#0: DatatypeType, u$ih#1#0: DatatypeType ::
            { _module.__default.Step(u$ih#1#0), _module.__default.IsContext($LS($LZ), C$ih#1#0) }
              { _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0) }
            $Is(C$ih#1#0, Tclass._module.Context()) && $Is(u$ih#1#0, Tclass._module.Term())
               ==>
              DtRank(C$ih#1#0) < DtRank(C#3)
                 || (DtRank(C$ih#1#0) == DtRank(C#3) && DtRank(u$ih#1#0) < DtRank(u#3))
               ==> !(
                _module.__default.IsContext($LS($LZ), C$ih#1#0)
                 && t#0 == _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0)
                 && _module.__default.Step(u$ih#1#0) != u$ih#1#0))
           &&
          true
           && (exists a#7#0#0: DatatypeType, a#7#1#0: DatatypeType ::
            { #_module.Context.C_term(a#7#0#0, a#7#1#0) }
            $Is(a#7#0#0, Tclass._module.Context())
               && $Is(a#7#1#0, Tclass._module.Term())
               && #_module.Context.C_term(a#7#0#0, a#7#1#0) == C#3)
           && #_module.Term.K() == u#3
           &&
          _module.__default.IsContext($LS($LS($LZ)), C#3)
           && t#0 == _module.__default.EvalExpr($LS($LS($LZ)), C#3, u#3)
           && _module.__default.Step(u#3) != u#3);
  ensures _module.__default.FindAndStep($LS($LZ), t#0) == t#0
     ==>
    _module.__default.IsTerminal#canCall(t#0)
     ==> _module.__default.IsTerminal(t#0)
       || !(exists C#3: DatatypeType, u#3: DatatypeType ::
        { _module.__default.Step(u#3), _module.__default.IsContext($LS($LS($LZ)), C#3) }
          { _module.__default.EvalExpr($LS($LS($LZ)), C#3, u#3) }
        $Is(C#3, Tclass._module.Context())
           && $Is(u#3, Tclass._module.Term())
           && (forall C$ih#1#0: DatatypeType, u$ih#1#0: DatatypeType ::
            { _module.__default.Step(u$ih#1#0), _module.__default.IsContext($LS($LZ), C$ih#1#0) }
              { _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0) }
            $Is(C$ih#1#0, Tclass._module.Context()) && $Is(u$ih#1#0, Tclass._module.Term())
               ==>
              DtRank(C$ih#1#0) < DtRank(C#3)
                 || (DtRank(C$ih#1#0) == DtRank(C#3) && DtRank(u$ih#1#0) < DtRank(u#3))
               ==> !(
                _module.__default.IsContext($LS($LZ), C$ih#1#0)
                 && t#0 == _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0)
                 && _module.__default.Step(u$ih#1#0) != u$ih#1#0))
           &&
          true
           && (exists a#8#0#0: DatatypeType, a#8#1#0: DatatypeType ::
            { #_module.Context.value_C(a#8#0#0, a#8#1#0) }
            $Is(a#8#0#0, Tclass._module.Term())
               && $Is(a#8#1#0, Tclass._module.Context())
               && #_module.Context.value_C(a#8#0#0, a#8#1#0) == C#3)
           && #_module.Term.K() == u#3
           &&
          _module.__default.IsContext($LS($LS($LZ)), C#3)
           && t#0 == _module.__default.EvalExpr($LS($LS($LZ)), C#3, u#3)
           && _module.__default.Step(u#3) != u#3);
  ensures _module.__default.FindAndStep($LS($LZ), t#0) == t#0
     ==>
    _module.__default.IsTerminal#canCall(t#0)
     ==> _module.__default.IsTerminal(t#0)
       || !(exists C#3: DatatypeType, u#3: DatatypeType ::
        { _module.__default.Step(u#3), _module.__default.IsContext($LS($LS($LZ)), C#3) }
          { _module.__default.EvalExpr($LS($LS($LZ)), C#3, u#3) }
        $Is(C#3, Tclass._module.Context())
           && $Is(u#3, Tclass._module.Term())
           && (forall C$ih#1#0: DatatypeType, u$ih#1#0: DatatypeType ::
            { _module.__default.Step(u$ih#1#0), _module.__default.IsContext($LS($LZ), C$ih#1#0) }
              { _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0) }
            $Is(C$ih#1#0, Tclass._module.Context()) && $Is(u$ih#1#0, Tclass._module.Term())
               ==>
              DtRank(C$ih#1#0) < DtRank(C#3)
                 || (DtRank(C$ih#1#0) == DtRank(C#3) && DtRank(u$ih#1#0) < DtRank(u#3))
               ==> !(
                _module.__default.IsContext($LS($LZ), C$ih#1#0)
                 && t#0 == _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0)
                 && _module.__default.Step(u$ih#1#0) != u$ih#1#0))
           &&
          true
           && #_module.Context.Hole() == C#3
           && (exists a#11#0#0: DatatypeType, a#11#1#0: DatatypeType ::
            { #_module.Term.Apply(a#11#0#0, a#11#1#0) }
            $Is(a#11#0#0, Tclass._module.Term())
               && $Is(a#11#1#0, Tclass._module.Term())
               && #_module.Term.Apply(a#11#0#0, a#11#1#0) == u#3)
           &&
          _module.__default.IsContext($LS($LS($LZ)), C#3)
           && t#0 == _module.__default.EvalExpr($LS($LS($LZ)), C#3, u#3)
           && _module.__default.Step(u#3) != u#3);
  ensures _module.__default.FindAndStep($LS($LZ), t#0) == t#0
     ==>
    _module.__default.IsTerminal#canCall(t#0)
     ==> _module.__default.IsTerminal(t#0)
       || !(exists C#3: DatatypeType, u#3: DatatypeType ::
        { _module.__default.Step(u#3), _module.__default.IsContext($LS($LS($LZ)), C#3) }
          { _module.__default.EvalExpr($LS($LS($LZ)), C#3, u#3) }
        $Is(C#3, Tclass._module.Context())
           && $Is(u#3, Tclass._module.Term())
           && (forall C$ih#1#0: DatatypeType, u$ih#1#0: DatatypeType ::
            { _module.__default.Step(u$ih#1#0), _module.__default.IsContext($LS($LZ), C$ih#1#0) }
              { _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0) }
            $Is(C$ih#1#0, Tclass._module.Context()) && $Is(u$ih#1#0, Tclass._module.Term())
               ==>
              DtRank(C$ih#1#0) < DtRank(C#3)
                 || (DtRank(C$ih#1#0) == DtRank(C#3) && DtRank(u$ih#1#0) < DtRank(u#3))
               ==> !(
                _module.__default.IsContext($LS($LZ), C$ih#1#0)
                 && t#0 == _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0)
                 && _module.__default.Step(u$ih#1#0) != u$ih#1#0))
           &&
          true
           && (exists a#7#0#0: DatatypeType, a#7#1#0: DatatypeType ::
            { #_module.Context.C_term(a#7#0#0, a#7#1#0) }
            $Is(a#7#0#0, Tclass._module.Context())
               && $Is(a#7#1#0, Tclass._module.Term())
               && #_module.Context.C_term(a#7#0#0, a#7#1#0) == C#3)
           && (exists a#11#0#0: DatatypeType, a#11#1#0: DatatypeType ::
            { #_module.Term.Apply(a#11#0#0, a#11#1#0) }
            $Is(a#11#0#0, Tclass._module.Term())
               && $Is(a#11#1#0, Tclass._module.Term())
               && #_module.Term.Apply(a#11#0#0, a#11#1#0) == u#3)
           &&
          _module.__default.IsContext($LS($LS($LZ)), C#3)
           && t#0 == _module.__default.EvalExpr($LS($LS($LZ)), C#3, u#3)
           && _module.__default.Step(u#3) != u#3);
  ensures _module.__default.FindAndStep($LS($LZ), t#0) == t#0
     ==>
    _module.__default.IsTerminal#canCall(t#0)
     ==> _module.__default.IsTerminal(t#0)
       || !(exists C#3: DatatypeType, u#3: DatatypeType ::
        { _module.__default.Step(u#3), _module.__default.IsContext($LS($LS($LZ)), C#3) }
          { _module.__default.EvalExpr($LS($LS($LZ)), C#3, u#3) }
        $Is(C#3, Tclass._module.Context())
           && $Is(u#3, Tclass._module.Term())
           && (forall C$ih#1#0: DatatypeType, u$ih#1#0: DatatypeType ::
            { _module.__default.Step(u$ih#1#0), _module.__default.IsContext($LS($LZ), C$ih#1#0) }
              { _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0) }
            $Is(C$ih#1#0, Tclass._module.Context()) && $Is(u$ih#1#0, Tclass._module.Term())
               ==>
              DtRank(C$ih#1#0) < DtRank(C#3)
                 || (DtRank(C$ih#1#0) == DtRank(C#3) && DtRank(u$ih#1#0) < DtRank(u#3))
               ==> !(
                _module.__default.IsContext($LS($LZ), C$ih#1#0)
                 && t#0 == _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0)
                 && _module.__default.Step(u$ih#1#0) != u$ih#1#0))
           &&
          true
           && (exists a#8#0#0: DatatypeType, a#8#1#0: DatatypeType ::
            { #_module.Context.value_C(a#8#0#0, a#8#1#0) }
            $Is(a#8#0#0, Tclass._module.Term())
               && $Is(a#8#1#0, Tclass._module.Context())
               && #_module.Context.value_C(a#8#0#0, a#8#1#0) == C#3)
           && (exists a#11#0#0: DatatypeType, a#11#1#0: DatatypeType ::
            { #_module.Term.Apply(a#11#0#0, a#11#1#0) }
            $Is(a#11#0#0, Tclass._module.Term())
               && $Is(a#11#1#0, Tclass._module.Term())
               && #_module.Term.Apply(a#11#0#0, a#11#1#0) == u#3)
           &&
          _module.__default.IsContext($LS($LS($LZ)), C#3)
           && t#0 == _module.__default.EvalExpr($LS($LS($LZ)), C#3, u#3)
           && _module.__default.Step(u#3) != u#3);
  free ensures _module.__default.FindAndStep#canCall(t#0)
     && (_module.__default.FindAndStep($LS($LZ), t#0) != t#0
       ==> (forall C#1: DatatypeType, u#1: DatatypeType ::
        { _module.__default.Step(u#1), _module.__default.IsContext($LS($LZ), C#1) }
        $Is(C#1, Tclass._module.Context()) && $Is(u#1, Tclass._module.Term())
           ==> _module.__default.IsContext#canCall(C#1)
             && (_module.__default.IsContext($LS($LZ), C#1)
               ==> _module.__default.EvalExpr#canCall(C#1, u#1))
             && (_module.__default.EvalExpr#canCall(C#1, u#1)
                 && t#0 == _module.__default.EvalExpr($LS($LZ), C#1, u#1)
               ==> _module.__default.Step#canCall(u#1))
             && (_module.__default.Step#canCall(u#1) && _module.__default.Step(u#1) != u#1
               ==> _module.__default.FindAndStep#canCall(t#0)
                 &&
                _module.__default.Step#canCall(u#1)
                 && _module.__default.EvalExpr#canCall(C#1, _module.__default.Step(u#1)))));
  ensures _module.__default.FindAndStep($LS($LZ), t#0) != t#0
     ==> (exists C#1: DatatypeType, u#1: DatatypeType ::
      {:_induction C#1, u#1} { _module.__default.Step(u#1), _module.__default.IsContext($LS($LZ), C#1) }
      $Is(C#1, Tclass._module.Context())
         && $Is(u#1, Tclass._module.Term())
         &&
        _module.__default.IsContext($LS($LZ), C#1)
         && t#0 == _module.__default.EvalExpr($LS($LZ), C#1, u#1)
         && _module.__default.Step(u#1) != u#1
         && _module.__default.FindAndStep($LS($LZ), t#0)
           == _module.__default.EvalExpr($LS($LZ), C#1, _module.__default.Step(u#1)));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction t#0} Impl$$_module.__default.Theorem__FindAndStep(t#0: DatatypeType) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var r#0: DatatypeType
     where $Is(r#0, Tclass._module.Term()) && $IsAlloc(r#0, Tclass._module.Term(), $Heap);
  var C#5: DatatypeType
     where $Is(C#5, Tclass._module.Context())
       && $IsAlloc(C#5, Tclass._module.Context(), $Heap);
  var u#5: DatatypeType
     where $Is(u#5, Tclass._module.Term()) && $IsAlloc(u#5, Tclass._module.Term(), $Heap);
  var $rhs##0: DatatypeType
     where $Is($rhs##0, Tclass._module.Term())
       && $IsAlloc($rhs##0, Tclass._module.Term(), $Heap);
  var $rhs##1: DatatypeType
     where $Is($rhs##1, Tclass._module.Context())
       && $IsAlloc($rhs##1, Tclass._module.Context(), $Heap);
  var $rhs##2: DatatypeType
     where $Is($rhs##2, Tclass._module.Term())
       && $IsAlloc($rhs##2, Tclass._module.Term(), $Heap);
  var t##0: DatatypeType;

    // AddMethodImpl: Theorem_FindAndStep, Impl$$_module.__default.Theorem__FindAndStep
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "Combinators.dfy(184,0): initial state"} true;
    assume $IsA#_module.Term(t#0);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#t0#0: DatatypeType ::
      $Is($ih#t0#0, Tclass._module.Term())
           && Lit(true)
           && DtRank($ih#t0#0) < DtRank(t#0)
         ==> (_module.__default.FindAndStep($LS($LZ), $ih#t0#0) == $ih#t0#0
             ==> _module.__default.IsTerminal($ih#t0#0))
           && (_module.__default.FindAndStep($LS($LZ), $ih#t0#0) != $ih#t0#0
             ==> (exists C#4: DatatypeType, u#4: DatatypeType ::
              {:_induction C#4, u#4} { _module.__default.Step(u#4), _module.__default.IsContext($LS($LZ), C#4) }
              $Is(C#4, Tclass._module.Context())
                 && $Is(u#4, Tclass._module.Term())
                 &&
                _module.__default.IsContext($LS($LZ), C#4)
                 && $ih#t0#0 == _module.__default.EvalExpr($LS($LZ), C#4, u#4)
                 && _module.__default.Step(u#4) != u#4
                 && _module.__default.FindAndStep($LS($LZ), $ih#t0#0)
                   == _module.__default.EvalExpr($LS($LZ), C#4, _module.__default.Step(u#4)))));
    $_reverifyPost := false;
    // ----- call statement ----- Combinators.dfy(187,35)
    assume true;
    assume true;
    assume true;
    // TrCallStmt: Adding lhs Microsoft.Dafny.AutoGhostIdentifierExpr with type Term
    // TrCallStmt: Adding lhs Microsoft.Dafny.AutoGhostIdentifierExpr with type Context
    // TrCallStmt: Adding lhs Microsoft.Dafny.AutoGhostIdentifierExpr with type Term
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    t##0 := t#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##0, $rhs##1, $rhs##2 := Call$$_module.__default.Lemma__FindAndStep(t##0);
    // TrCallStmt: After ProcessCallStmt
    r#0 := $rhs##0;
    C#5 := $rhs##1;
    u#5 := $rhs##2;
    assume {:captureState "Combinators.dfy(187,37)"} true;
}



procedure CheckWellformed$$_module.__default.Lemma__FindAndStep(t#0: DatatypeType
       where $Is(t#0, Tclass._module.Term())
         && $IsAlloc(t#0, Tclass._module.Term(), $Heap)
         && $IsA#_module.Term(t#0))
   returns (r#0: DatatypeType
       where $Is(r#0, Tclass._module.Term()) && $IsAlloc(r#0, Tclass._module.Term(), $Heap),
    C#0: DatatypeType
       where $Is(C#0, Tclass._module.Context())
         && $IsAlloc(C#0, Tclass._module.Context(), $Heap),
    u#0: DatatypeType
       where $Is(u#0, Tclass._module.Term()) && $IsAlloc(u#0, Tclass._module.Term(), $Heap));
  free requires 13 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.Lemma__FindAndStep(t#0: DatatypeType)
   returns (r#0: DatatypeType, C#0: DatatypeType, u#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##t#0: DatatypeType;
  var ##t#1: DatatypeType;
  var ##C#0: DatatypeType;
  var ##C#1: DatatypeType;
  var ##t#2: DatatypeType;
  var ##t#3: DatatypeType;
  var ##t#4: DatatypeType;
  var ##C#2: DatatypeType;
  var ##t#5: DatatypeType;

    // AddMethodImpl: Lemma_FindAndStep, CheckWellformed$$_module.__default.Lemma__FindAndStep
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "Combinators.dfy(197,6): initial state"} true;
    havoc $Heap;
    assume old($Heap) == $Heap;
    havoc r#0, C#0, u#0;
    assume {:captureState "Combinators.dfy(198,12): post-state"} true;
    ##t#0 := t#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##t#0, Tclass._module.Term(), $Heap);
    assume _module.__default.FindAndStep#canCall(t#0);
    assume r#0 == _module.__default.FindAndStep($LS($LZ), t#0);
    if (*)
    {
        assume r#0 == t#0;
        ##t#1 := t#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##t#1, Tclass._module.Term(), $Heap);
        assume _module.__default.IsTerminal#canCall(t#0);
        assume _module.__default.IsTerminal(t#0);
    }
    else
    {
        assume r#0 == t#0 ==> _module.__default.IsTerminal(t#0);
    }

    if (*)
    {
        assume r#0 != t#0;
        ##C#0 := C#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##C#0, Tclass._module.Context(), $Heap);
        assume _module.__default.IsContext#canCall(C#0);
        assume _module.__default.IsContext($LS($LZ), C#0);
        ##C#1 := C#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##C#1, Tclass._module.Context(), $Heap);
        ##t#2 := u#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##t#2, Tclass._module.Term(), $Heap);
        assert {:subsumption 0} _module.__default.IsContext($LS($LS($LZ)), ##C#1);
        assume _module.__default.IsContext($LS($LZ), ##C#1);
        assume _module.__default.EvalExpr#canCall(C#0, u#0);
        assume t#0 == _module.__default.EvalExpr($LS($LZ), C#0, u#0);
        ##t#3 := u#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##t#3, Tclass._module.Term(), $Heap);
        assume _module.__default.Step#canCall(u#0);
        assume _module.__default.Step(u#0) != u#0;
        ##t#4 := u#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##t#4, Tclass._module.Term(), $Heap);
        assume _module.__default.Step#canCall(u#0);
        ##C#2 := C#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##C#2, Tclass._module.Context(), $Heap);
        ##t#5 := _module.__default.Step(u#0);
        // assume allocatedness for argument to function
        assume $IsAlloc(##t#5, Tclass._module.Term(), $Heap);
        assert {:subsumption 0} _module.__default.IsContext($LS($LS($LZ)), ##C#2);
        assume _module.__default.IsContext($LS($LZ), ##C#2);
        assume _module.__default.EvalExpr#canCall(C#0, _module.__default.Step(u#0));
        assume r#0 == _module.__default.EvalExpr($LS($LZ), C#0, _module.__default.Step(u#0));
    }
    else
    {
        assume r#0 != t#0
           ==> _module.__default.IsContext($LS($LZ), C#0)
             && t#0 == _module.__default.EvalExpr($LS($LZ), C#0, u#0)
             && _module.__default.Step(u#0) != u#0
             && r#0 == _module.__default.EvalExpr($LS($LZ), C#0, _module.__default.Step(u#0));
    }
}



procedure Call$$_module.__default.Lemma__FindAndStep(t#0: DatatypeType
       where $Is(t#0, Tclass._module.Term())
         && $IsAlloc(t#0, Tclass._module.Term(), $Heap)
         && $IsA#_module.Term(t#0))
   returns (r#0: DatatypeType
       where $Is(r#0, Tclass._module.Term()) && $IsAlloc(r#0, Tclass._module.Term(), $Heap),
    C#0: DatatypeType
       where $Is(C#0, Tclass._module.Context())
         && $IsAlloc(C#0, Tclass._module.Context(), $Heap),
    u#0: DatatypeType
       where $Is(u#0, Tclass._module.Term()) && $IsAlloc(u#0, Tclass._module.Term(), $Heap));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.FindAndStep#canCall(t#0);
  ensures r#0 == _module.__default.FindAndStep($LS($LS($LZ)), t#0);
  free ensures r#0 == t#0 ==> _module.__default.IsTerminal#canCall(t#0);
  free ensures r#0 == t#0
     ==> _module.__default.IsTerminal#canCall(t#0)
       &&
      _module.__default.IsTerminal(t#0)
       && !(exists C#1: DatatypeType, u#1: DatatypeType ::
        {:_induction C#1, u#1} { _module.__default.Step(u#1), _module.__default.IsContext($LS($LZ), C#1) }
          { _module.__default.EvalExpr($LS($LZ), C#1, u#1) }
        $Is(C#1, Tclass._module.Context())
           && $Is(u#1, Tclass._module.Term())
           &&
          _module.__default.IsContext($LS($LZ), C#1)
           && t#0 == _module.__default.EvalExpr($LS($LZ), C#1, u#1)
           && _module.__default.Step(u#1) != u#1);
  free ensures r#0 != t#0
     ==> _module.__default.IsContext#canCall(C#0)
       && (_module.__default.IsContext($LS($LZ), C#0)
         ==> _module.__default.EvalExpr#canCall(C#0, u#0))
       && (_module.__default.EvalExpr#canCall(C#0, u#0)
           && t#0 == _module.__default.EvalExpr($LS($LZ), C#0, u#0)
         ==> _module.__default.Step#canCall(u#0))
       && (_module.__default.Step#canCall(u#0) && _module.__default.Step(u#0) != u#0
         ==> _module.__default.Step#canCall(u#0)
           && _module.__default.EvalExpr#canCall(C#0, _module.__default.Step(u#0)));
  ensures r#0 != t#0 ==> _module.__default.IsContext($LS($LS($LZ)), C#0);
  ensures r#0 != t#0 ==> t#0 == _module.__default.EvalExpr($LS($LS($LZ)), C#0, u#0);
  ensures r#0 != t#0 ==> _module.__default.Step(u#0) != u#0;
  ensures r#0 != t#0
     ==> r#0
       == _module.__default.EvalExpr($LS($LS($LZ)), C#0, _module.__default.Step(u#0));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.Lemma__FindAndStep(t#0: DatatypeType
       where $Is(t#0, Tclass._module.Term())
         && $IsAlloc(t#0, Tclass._module.Term(), $Heap)
         && $IsA#_module.Term(t#0))
   returns (r#0: DatatypeType
       where $Is(r#0, Tclass._module.Term()) && $IsAlloc(r#0, Tclass._module.Term(), $Heap),
    C#0: DatatypeType
       where $Is(C#0, Tclass._module.Context())
         && $IsAlloc(C#0, Tclass._module.Context(), $Heap),
    u#0: DatatypeType
       where $Is(u#0, Tclass._module.Term()) && $IsAlloc(u#0, Tclass._module.Term(), $Heap),
    $_reverifyPost: bool);
  free requires 13 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.FindAndStep#canCall(t#0);
  ensures r#0 == _module.__default.FindAndStep($LS($LS($LZ)), t#0);
  free ensures r#0 == t#0 ==> _module.__default.IsTerminal#canCall(t#0);
  ensures r#0 == t#0
     ==>
    _module.__default.IsTerminal#canCall(t#0)
     ==> _module.__default.IsTerminal(t#0)
       || !(exists C#2: DatatypeType, u#2: DatatypeType ::
        { _module.__default.Step(u#2), _module.__default.IsContext($LS($LS($LZ)), C#2) }
          { _module.__default.EvalExpr($LS($LS($LZ)), C#2, u#2) }
        $Is(C#2, Tclass._module.Context())
           && $Is(u#2, Tclass._module.Term())
           && (forall C$ih#1#0: DatatypeType, u$ih#1#0: DatatypeType ::
            { _module.__default.Step(u$ih#1#0), _module.__default.IsContext($LS($LZ), C$ih#1#0) }
              { _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0) }
            $Is(C$ih#1#0, Tclass._module.Context()) && $Is(u$ih#1#0, Tclass._module.Term())
               ==>
              DtRank(C$ih#1#0) < DtRank(C#2)
                 || (DtRank(C$ih#1#0) == DtRank(C#2) && DtRank(u$ih#1#0) < DtRank(u#2))
               ==> !(
                _module.__default.IsContext($LS($LZ), C$ih#1#0)
                 && t#0 == _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0)
                 && _module.__default.Step(u$ih#1#0) != u$ih#1#0))
           &&
          true
           && #_module.Context.Hole() == C#2
           && #_module.Term.S() == u#2
           &&
          _module.__default.IsContext($LS($LS($LZ)), C#2)
           && t#0 == _module.__default.EvalExpr($LS($LS($LZ)), C#2, u#2)
           && _module.__default.Step(u#2) != u#2);
  ensures r#0 == t#0
     ==>
    _module.__default.IsTerminal#canCall(t#0)
     ==> _module.__default.IsTerminal(t#0)
       || !(exists C#2: DatatypeType, u#2: DatatypeType ::
        { _module.__default.Step(u#2), _module.__default.IsContext($LS($LS($LZ)), C#2) }
          { _module.__default.EvalExpr($LS($LS($LZ)), C#2, u#2) }
        $Is(C#2, Tclass._module.Context())
           && $Is(u#2, Tclass._module.Term())
           && (forall C$ih#1#0: DatatypeType, u$ih#1#0: DatatypeType ::
            { _module.__default.Step(u$ih#1#0), _module.__default.IsContext($LS($LZ), C$ih#1#0) }
              { _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0) }
            $Is(C$ih#1#0, Tclass._module.Context()) && $Is(u$ih#1#0, Tclass._module.Term())
               ==>
              DtRank(C$ih#1#0) < DtRank(C#2)
                 || (DtRank(C$ih#1#0) == DtRank(C#2) && DtRank(u$ih#1#0) < DtRank(u#2))
               ==> !(
                _module.__default.IsContext($LS($LZ), C$ih#1#0)
                 && t#0 == _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0)
                 && _module.__default.Step(u$ih#1#0) != u$ih#1#0))
           &&
          true
           && (exists a#7#0#0: DatatypeType, a#7#1#0: DatatypeType ::
            { #_module.Context.C_term(a#7#0#0, a#7#1#0) }
            $Is(a#7#0#0, Tclass._module.Context())
               && $Is(a#7#1#0, Tclass._module.Term())
               && #_module.Context.C_term(a#7#0#0, a#7#1#0) == C#2)
           && #_module.Term.S() == u#2
           &&
          _module.__default.IsContext($LS($LS($LZ)), C#2)
           && t#0 == _module.__default.EvalExpr($LS($LS($LZ)), C#2, u#2)
           && _module.__default.Step(u#2) != u#2);
  ensures r#0 == t#0
     ==>
    _module.__default.IsTerminal#canCall(t#0)
     ==> _module.__default.IsTerminal(t#0)
       || !(exists C#2: DatatypeType, u#2: DatatypeType ::
        { _module.__default.Step(u#2), _module.__default.IsContext($LS($LS($LZ)), C#2) }
          { _module.__default.EvalExpr($LS($LS($LZ)), C#2, u#2) }
        $Is(C#2, Tclass._module.Context())
           && $Is(u#2, Tclass._module.Term())
           && (forall C$ih#1#0: DatatypeType, u$ih#1#0: DatatypeType ::
            { _module.__default.Step(u$ih#1#0), _module.__default.IsContext($LS($LZ), C$ih#1#0) }
              { _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0) }
            $Is(C$ih#1#0, Tclass._module.Context()) && $Is(u$ih#1#0, Tclass._module.Term())
               ==>
              DtRank(C$ih#1#0) < DtRank(C#2)
                 || (DtRank(C$ih#1#0) == DtRank(C#2) && DtRank(u$ih#1#0) < DtRank(u#2))
               ==> !(
                _module.__default.IsContext($LS($LZ), C$ih#1#0)
                 && t#0 == _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0)
                 && _module.__default.Step(u$ih#1#0) != u$ih#1#0))
           &&
          true
           && (exists a#8#0#0: DatatypeType, a#8#1#0: DatatypeType ::
            { #_module.Context.value_C(a#8#0#0, a#8#1#0) }
            $Is(a#8#0#0, Tclass._module.Term())
               && $Is(a#8#1#0, Tclass._module.Context())
               && #_module.Context.value_C(a#8#0#0, a#8#1#0) == C#2)
           && #_module.Term.S() == u#2
           &&
          _module.__default.IsContext($LS($LS($LZ)), C#2)
           && t#0 == _module.__default.EvalExpr($LS($LS($LZ)), C#2, u#2)
           && _module.__default.Step(u#2) != u#2);
  ensures r#0 == t#0
     ==>
    _module.__default.IsTerminal#canCall(t#0)
     ==> _module.__default.IsTerminal(t#0)
       || !(exists C#2: DatatypeType, u#2: DatatypeType ::
        { _module.__default.Step(u#2), _module.__default.IsContext($LS($LS($LZ)), C#2) }
          { _module.__default.EvalExpr($LS($LS($LZ)), C#2, u#2) }
        $Is(C#2, Tclass._module.Context())
           && $Is(u#2, Tclass._module.Term())
           && (forall C$ih#1#0: DatatypeType, u$ih#1#0: DatatypeType ::
            { _module.__default.Step(u$ih#1#0), _module.__default.IsContext($LS($LZ), C$ih#1#0) }
              { _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0) }
            $Is(C$ih#1#0, Tclass._module.Context()) && $Is(u$ih#1#0, Tclass._module.Term())
               ==>
              DtRank(C$ih#1#0) < DtRank(C#2)
                 || (DtRank(C$ih#1#0) == DtRank(C#2) && DtRank(u$ih#1#0) < DtRank(u#2))
               ==> !(
                _module.__default.IsContext($LS($LZ), C$ih#1#0)
                 && t#0 == _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0)
                 && _module.__default.Step(u$ih#1#0) != u$ih#1#0))
           &&
          true
           && #_module.Context.Hole() == C#2
           && #_module.Term.K() == u#2
           &&
          _module.__default.IsContext($LS($LS($LZ)), C#2)
           && t#0 == _module.__default.EvalExpr($LS($LS($LZ)), C#2, u#2)
           && _module.__default.Step(u#2) != u#2);
  ensures r#0 == t#0
     ==>
    _module.__default.IsTerminal#canCall(t#0)
     ==> _module.__default.IsTerminal(t#0)
       || !(exists C#2: DatatypeType, u#2: DatatypeType ::
        { _module.__default.Step(u#2), _module.__default.IsContext($LS($LS($LZ)), C#2) }
          { _module.__default.EvalExpr($LS($LS($LZ)), C#2, u#2) }
        $Is(C#2, Tclass._module.Context())
           && $Is(u#2, Tclass._module.Term())
           && (forall C$ih#1#0: DatatypeType, u$ih#1#0: DatatypeType ::
            { _module.__default.Step(u$ih#1#0), _module.__default.IsContext($LS($LZ), C$ih#1#0) }
              { _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0) }
            $Is(C$ih#1#0, Tclass._module.Context()) && $Is(u$ih#1#0, Tclass._module.Term())
               ==>
              DtRank(C$ih#1#0) < DtRank(C#2)
                 || (DtRank(C$ih#1#0) == DtRank(C#2) && DtRank(u$ih#1#0) < DtRank(u#2))
               ==> !(
                _module.__default.IsContext($LS($LZ), C$ih#1#0)
                 && t#0 == _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0)
                 && _module.__default.Step(u$ih#1#0) != u$ih#1#0))
           &&
          true
           && (exists a#7#0#0: DatatypeType, a#7#1#0: DatatypeType ::
            { #_module.Context.C_term(a#7#0#0, a#7#1#0) }
            $Is(a#7#0#0, Tclass._module.Context())
               && $Is(a#7#1#0, Tclass._module.Term())
               && #_module.Context.C_term(a#7#0#0, a#7#1#0) == C#2)
           && #_module.Term.K() == u#2
           &&
          _module.__default.IsContext($LS($LS($LZ)), C#2)
           && t#0 == _module.__default.EvalExpr($LS($LS($LZ)), C#2, u#2)
           && _module.__default.Step(u#2) != u#2);
  ensures r#0 == t#0
     ==>
    _module.__default.IsTerminal#canCall(t#0)
     ==> _module.__default.IsTerminal(t#0)
       || !(exists C#2: DatatypeType, u#2: DatatypeType ::
        { _module.__default.Step(u#2), _module.__default.IsContext($LS($LS($LZ)), C#2) }
          { _module.__default.EvalExpr($LS($LS($LZ)), C#2, u#2) }
        $Is(C#2, Tclass._module.Context())
           && $Is(u#2, Tclass._module.Term())
           && (forall C$ih#1#0: DatatypeType, u$ih#1#0: DatatypeType ::
            { _module.__default.Step(u$ih#1#0), _module.__default.IsContext($LS($LZ), C$ih#1#0) }
              { _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0) }
            $Is(C$ih#1#0, Tclass._module.Context()) && $Is(u$ih#1#0, Tclass._module.Term())
               ==>
              DtRank(C$ih#1#0) < DtRank(C#2)
                 || (DtRank(C$ih#1#0) == DtRank(C#2) && DtRank(u$ih#1#0) < DtRank(u#2))
               ==> !(
                _module.__default.IsContext($LS($LZ), C$ih#1#0)
                 && t#0 == _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0)
                 && _module.__default.Step(u$ih#1#0) != u$ih#1#0))
           &&
          true
           && (exists a#8#0#0: DatatypeType, a#8#1#0: DatatypeType ::
            { #_module.Context.value_C(a#8#0#0, a#8#1#0) }
            $Is(a#8#0#0, Tclass._module.Term())
               && $Is(a#8#1#0, Tclass._module.Context())
               && #_module.Context.value_C(a#8#0#0, a#8#1#0) == C#2)
           && #_module.Term.K() == u#2
           &&
          _module.__default.IsContext($LS($LS($LZ)), C#2)
           && t#0 == _module.__default.EvalExpr($LS($LS($LZ)), C#2, u#2)
           && _module.__default.Step(u#2) != u#2);
  ensures r#0 == t#0
     ==>
    _module.__default.IsTerminal#canCall(t#0)
     ==> _module.__default.IsTerminal(t#0)
       || !(exists C#2: DatatypeType, u#2: DatatypeType ::
        { _module.__default.Step(u#2), _module.__default.IsContext($LS($LS($LZ)), C#2) }
          { _module.__default.EvalExpr($LS($LS($LZ)), C#2, u#2) }
        $Is(C#2, Tclass._module.Context())
           && $Is(u#2, Tclass._module.Term())
           && (forall C$ih#1#0: DatatypeType, u$ih#1#0: DatatypeType ::
            { _module.__default.Step(u$ih#1#0), _module.__default.IsContext($LS($LZ), C$ih#1#0) }
              { _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0) }
            $Is(C$ih#1#0, Tclass._module.Context()) && $Is(u$ih#1#0, Tclass._module.Term())
               ==>
              DtRank(C$ih#1#0) < DtRank(C#2)
                 || (DtRank(C$ih#1#0) == DtRank(C#2) && DtRank(u$ih#1#0) < DtRank(u#2))
               ==> !(
                _module.__default.IsContext($LS($LZ), C$ih#1#0)
                 && t#0 == _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0)
                 && _module.__default.Step(u$ih#1#0) != u$ih#1#0))
           &&
          true
           && #_module.Context.Hole() == C#2
           && (exists a#11#0#0: DatatypeType, a#11#1#0: DatatypeType ::
            { #_module.Term.Apply(a#11#0#0, a#11#1#0) }
            $Is(a#11#0#0, Tclass._module.Term())
               && $Is(a#11#1#0, Tclass._module.Term())
               && #_module.Term.Apply(a#11#0#0, a#11#1#0) == u#2)
           &&
          _module.__default.IsContext($LS($LS($LZ)), C#2)
           && t#0 == _module.__default.EvalExpr($LS($LS($LZ)), C#2, u#2)
           && _module.__default.Step(u#2) != u#2);
  ensures r#0 == t#0
     ==>
    _module.__default.IsTerminal#canCall(t#0)
     ==> _module.__default.IsTerminal(t#0)
       || !(exists C#2: DatatypeType, u#2: DatatypeType ::
        { _module.__default.Step(u#2), _module.__default.IsContext($LS($LS($LZ)), C#2) }
          { _module.__default.EvalExpr($LS($LS($LZ)), C#2, u#2) }
        $Is(C#2, Tclass._module.Context())
           && $Is(u#2, Tclass._module.Term())
           && (forall C$ih#1#0: DatatypeType, u$ih#1#0: DatatypeType ::
            { _module.__default.Step(u$ih#1#0), _module.__default.IsContext($LS($LZ), C$ih#1#0) }
              { _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0) }
            $Is(C$ih#1#0, Tclass._module.Context()) && $Is(u$ih#1#0, Tclass._module.Term())
               ==>
              DtRank(C$ih#1#0) < DtRank(C#2)
                 || (DtRank(C$ih#1#0) == DtRank(C#2) && DtRank(u$ih#1#0) < DtRank(u#2))
               ==> !(
                _module.__default.IsContext($LS($LZ), C$ih#1#0)
                 && t#0 == _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0)
                 && _module.__default.Step(u$ih#1#0) != u$ih#1#0))
           &&
          true
           && (exists a#7#0#0: DatatypeType, a#7#1#0: DatatypeType ::
            { #_module.Context.C_term(a#7#0#0, a#7#1#0) }
            $Is(a#7#0#0, Tclass._module.Context())
               && $Is(a#7#1#0, Tclass._module.Term())
               && #_module.Context.C_term(a#7#0#0, a#7#1#0) == C#2)
           && (exists a#11#0#0: DatatypeType, a#11#1#0: DatatypeType ::
            { #_module.Term.Apply(a#11#0#0, a#11#1#0) }
            $Is(a#11#0#0, Tclass._module.Term())
               && $Is(a#11#1#0, Tclass._module.Term())
               && #_module.Term.Apply(a#11#0#0, a#11#1#0) == u#2)
           &&
          _module.__default.IsContext($LS($LS($LZ)), C#2)
           && t#0 == _module.__default.EvalExpr($LS($LS($LZ)), C#2, u#2)
           && _module.__default.Step(u#2) != u#2);
  ensures r#0 == t#0
     ==>
    _module.__default.IsTerminal#canCall(t#0)
     ==> _module.__default.IsTerminal(t#0)
       || !(exists C#2: DatatypeType, u#2: DatatypeType ::
        { _module.__default.Step(u#2), _module.__default.IsContext($LS($LS($LZ)), C#2) }
          { _module.__default.EvalExpr($LS($LS($LZ)), C#2, u#2) }
        $Is(C#2, Tclass._module.Context())
           && $Is(u#2, Tclass._module.Term())
           && (forall C$ih#1#0: DatatypeType, u$ih#1#0: DatatypeType ::
            { _module.__default.Step(u$ih#1#0), _module.__default.IsContext($LS($LZ), C$ih#1#0) }
              { _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0) }
            $Is(C$ih#1#0, Tclass._module.Context()) && $Is(u$ih#1#0, Tclass._module.Term())
               ==>
              DtRank(C$ih#1#0) < DtRank(C#2)
                 || (DtRank(C$ih#1#0) == DtRank(C#2) && DtRank(u$ih#1#0) < DtRank(u#2))
               ==> !(
                _module.__default.IsContext($LS($LZ), C$ih#1#0)
                 && t#0 == _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0)
                 && _module.__default.Step(u$ih#1#0) != u$ih#1#0))
           &&
          true
           && (exists a#8#0#0: DatatypeType, a#8#1#0: DatatypeType ::
            { #_module.Context.value_C(a#8#0#0, a#8#1#0) }
            $Is(a#8#0#0, Tclass._module.Term())
               && $Is(a#8#1#0, Tclass._module.Context())
               && #_module.Context.value_C(a#8#0#0, a#8#1#0) == C#2)
           && (exists a#11#0#0: DatatypeType, a#11#1#0: DatatypeType ::
            { #_module.Term.Apply(a#11#0#0, a#11#1#0) }
            $Is(a#11#0#0, Tclass._module.Term())
               && $Is(a#11#1#0, Tclass._module.Term())
               && #_module.Term.Apply(a#11#0#0, a#11#1#0) == u#2)
           &&
          _module.__default.IsContext($LS($LS($LZ)), C#2)
           && t#0 == _module.__default.EvalExpr($LS($LS($LZ)), C#2, u#2)
           && _module.__default.Step(u#2) != u#2);
  free ensures r#0 != t#0
     ==> _module.__default.IsContext#canCall(C#0)
       && (_module.__default.IsContext($LS($LZ), C#0)
         ==> _module.__default.EvalExpr#canCall(C#0, u#0))
       && (_module.__default.EvalExpr#canCall(C#0, u#0)
           && t#0 == _module.__default.EvalExpr($LS($LZ), C#0, u#0)
         ==> _module.__default.Step#canCall(u#0))
       && (_module.__default.Step#canCall(u#0) && _module.__default.Step(u#0) != u#0
         ==> _module.__default.Step#canCall(u#0)
           && _module.__default.EvalExpr#canCall(C#0, _module.__default.Step(u#0)));
  ensures r#0 != t#0 ==> _module.__default.IsContext($LS($LS($LZ)), C#0);
  ensures r#0 != t#0 ==> t#0 == _module.__default.EvalExpr($LS($LS($LZ)), C#0, u#0);
  ensures r#0 != t#0 ==> _module.__default.Step(u#0) != u#0;
  ensures r#0 != t#0
     ==> r#0
       == _module.__default.EvalExpr($LS($LS($LZ)), C#0, _module.__default.Step(u#0));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.Lemma__FindAndStep(t#0: DatatypeType)
   returns (r#0: DatatypeType, C#0: DatatypeType, u#0: DatatypeType, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var t##0: DatatypeType;
  var ##t#6: DatatypeType;
  var $rhs#0_0: DatatypeType where $Is($rhs#0_0, Tclass._module.Term());
  var ##t#0_0: DatatypeType;
  var $rhs#0_1: DatatypeType where $Is($rhs#0_1, Tclass._module.Context());
  var $rhs#0_2: DatatypeType where $Is($rhs#0_2, Tclass._module.Term());
  var $rhs##0: DatatypeType
     where $Is($rhs##0, Tclass._module.Term())
       && $IsAlloc($rhs##0, Tclass._module.Term(), $Heap);
  var $rhs##1: DatatypeType
     where $Is($rhs##1, Tclass._module.Context())
       && $IsAlloc($rhs##1, Tclass._module.Context(), $Heap);
  var $rhs##2: DatatypeType
     where $Is($rhs##2, Tclass._module.Term())
       && $IsAlloc($rhs##2, Tclass._module.Term(), $Heap);
  var t##1: DatatypeType;
  var $rhs#2_0: DatatypeType where $Is($rhs#2_0, Tclass._module.Term());
  var $rhs#2_1: DatatypeType where $Is($rhs#2_1, Tclass._module.Context());
  var $rhs#2_2: DatatypeType where $Is($rhs#2_2, Tclass._module.Term());
  var ##t#7: DatatypeType;
  var $rhs##3_0: DatatypeType
     where $Is($rhs##3_0, Tclass._module.Term())
       && $IsAlloc($rhs##3_0, Tclass._module.Term(), $Heap);
  var $rhs##3_1: DatatypeType
     where $Is($rhs##3_1, Tclass._module.Context())
       && $IsAlloc($rhs##3_1, Tclass._module.Context(), $Heap);
  var $rhs##3_2: DatatypeType
     where $Is($rhs##3_2, Tclass._module.Term())
       && $IsAlloc($rhs##3_2, Tclass._module.Term(), $Heap);
  var t##3_0: DatatypeType;
  var ##t#3_0: DatatypeType;
  var $rhs#3_0_0: DatatypeType where $Is($rhs#3_0_0, Tclass._module.Term());
  var $rhs#3_0_1: DatatypeType where $Is($rhs#3_0_1, Tclass._module.Context());
  var $rhs#3_0_2: DatatypeType where $Is($rhs#3_0_2, Tclass._module.Term());
  var C#3_1: DatatypeType;
  var u#3_1: DatatypeType;
  var ##C#3_0: DatatypeType;
  var ##C#3_1: DatatypeType;
  var ##t#3_1: DatatypeType;
  var ##t#3_2: DatatypeType;
  var at#3_1_0: DatatypeType;
  var D#3_1_0: DatatypeType;
  var ##C#3_1_0: DatatypeType;
  var ##t#3_1_0: DatatypeType;
  var D#3_2_0: DatatypeType;
  var bt#3_2_0: DatatypeType;
  var ##C#3_2_0: DatatypeType;
  var ##t#3_2_0: DatatypeType;

    // AddMethodImpl: Lemma_FindAndStep, Impl$$_module.__default.Lemma__FindAndStep
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "Combinators.dfy(203,0): initial state"} true;
    $_reverifyPost := false;
    // ----- call statement ----- Combinators.dfy(204,29)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    t##0 := t#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.Lemma__ContextPossibilities(t##0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "Combinators.dfy(204,31)"} true;
    // ----- if statement ----- Combinators.dfy(205,3)
    ##t#6 := t#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##t#6, Tclass._module.Term(), $Heap);
    assume _module.__default.Step#canCall(t#0);
    assume _module.__default.Step#canCall(t#0);
    if (_module.__default.Step(t#0) != t#0)
    {
        // ----- return statement ----- Combinators.dfy(207,5)
        // ----- update statement ----- Combinators.dfy(207,5)
        assume true;
        assume true;
        assume true;
        ##t#0_0 := t#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##t#0_0, Tclass._module.Term(), $Heap);
        assume _module.__default.Step#canCall(t#0);
        assume _module.__default.Step#canCall(t#0);
        $rhs#0_0 := _module.__default.Step(t#0);
        assume true;
        $rhs#0_1 := Lit(#_module.Context.Hole());
        assume true;
        $rhs#0_2 := t#0;
        r#0 := $rhs#0_0;
        C#0 := $rhs#0_1;
        u#0 := $rhs#0_2;
        assume {:captureState "Combinators.dfy(207,27)"} true;
        return;
    }
    else
    {
        // ----- if statement ----- Combinators.dfy(208,10)
        assume true;
        if (!_module.Term.Apply_q(t#0))
        {
            // ----- assignment statement ----- Combinators.dfy(209,7)
            assume true;
            assume true;
            r#0 := t#0;
            assume {:captureState "Combinators.dfy(209,10)"} true;
        }
        else
        {
            // ----- call statement ----- Combinators.dfy(211,33)
            assume true;
            assume true;
            assume true;
            // TrCallStmt: Adding lhs Microsoft.Dafny.IdentifierExpr with type Term
            // TrCallStmt: Adding lhs Microsoft.Dafny.IdentifierExpr with type Context
            // TrCallStmt: Adding lhs Microsoft.Dafny.IdentifierExpr with type Term
            // TrCallStmt: Before ProcessCallStmt
            assert _module.Term.Apply_q(t#0);
            assume true;
            // ProcessCallStmt: CheckSubrange
            t##1 := _module.Term.car(t#0);
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert DtRank(t##1) < DtRank(t#0);
            // ProcessCallStmt: Make the call
            call $rhs##0, $rhs##1, $rhs##2 := Call$$_module.__default.Lemma__FindAndStep(t##1);
            // TrCallStmt: After ProcessCallStmt
            r#0 := $rhs##0;
            C#0 := $rhs##1;
            u#0 := $rhs##2;
            assume {:captureState "Combinators.dfy(211,39)"} true;
            // ----- if statement ----- Combinators.dfy(212,5)
            assert _module.Term.Apply_q(t#0);
            assume true;
            if (r#0 != _module.Term.car(t#0))
            {
                // ----- return statement ----- Combinators.dfy(218,7)
                // ----- update statement ----- Combinators.dfy(218,7)
                assume true;
                assume true;
                assume true;
                assert _module.Term.Apply_q(t#0);
                assume true;
                $rhs#2_0 := #_module.Term.Apply(r#0, _module.Term.cdr(t#0));
                assert _module.Term.Apply_q(t#0);
                assume true;
                $rhs#2_1 := #_module.Context.C_term(C#0, _module.Term.cdr(t#0));
                assume true;
                $rhs#2_2 := u#0;
                r#0 := $rhs#2_0;
                C#0 := $rhs#2_1;
                u#0 := $rhs#2_2;
                assume {:captureState "Combinators.dfy(218,49)"} true;
                return;
            }
            else
            {
                // ----- if statement ----- Combinators.dfy(219,12)
                assert _module.Term.Apply_q(t#0);
                ##t#7 := _module.Term.car(t#0);
                // assume allocatedness for argument to function
                assume $IsAlloc(##t#7, Tclass._module.Term(), $Heap);
                assume _module.__default.IsValue#canCall(_module.Term.car(t#0));
                assume _module.__default.IsValue#canCall(_module.Term.car(t#0));
                if (_module.__default.IsValue($LS($LZ), _module.Term.car(t#0)))
                {
                    // ----- call statement ----- Combinators.dfy(220,35)
                    assume true;
                    assume true;
                    assume true;
                    // TrCallStmt: Adding lhs Microsoft.Dafny.IdentifierExpr with type Term
                    // TrCallStmt: Adding lhs Microsoft.Dafny.IdentifierExpr with type Context
                    // TrCallStmt: Adding lhs Microsoft.Dafny.IdentifierExpr with type Term
                    // TrCallStmt: Before ProcessCallStmt
                    assert _module.Term.Apply_q(t#0);
                    assume true;
                    // ProcessCallStmt: CheckSubrange
                    t##3_0 := _module.Term.cdr(t#0);
                    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                    assert DtRank(t##3_0) < DtRank(t#0);
                    // ProcessCallStmt: Make the call
                    call $rhs##3_0, $rhs##3_1, $rhs##3_2 := Call$$_module.__default.Lemma__FindAndStep(t##3_0);
                    // TrCallStmt: After ProcessCallStmt
                    r#0 := $rhs##3_0;
                    C#0 := $rhs##3_1;
                    u#0 := $rhs##3_2;
                    assume {:captureState "Combinators.dfy(220,41)"} true;
                    // ----- assert statement ----- Combinators.dfy(221,7)
                    assert _module.Term.Apply_q(t#0);
                    ##t#3_0 := _module.Term.car(t#0);
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##t#3_0, Tclass._module.Term(), $Heap);
                    assume _module.__default.IsTerminal#canCall(_module.Term.car(t#0));
                    assume _module.__default.IsTerminal#canCall(_module.Term.car(t#0));
                    assert {:subsumption 0} _module.__default.IsTerminal#canCall(_module.Term.car(t#0))
                       ==> _module.__default.IsTerminal(_module.Term.car(t#0))
                         || !(exists C#3_0: DatatypeType, u#3_0: DatatypeType ::
                          { _module.__default.Step(u#3_0), _module.__default.IsContext($LS($LS($LZ)), C#3_0) }
                            { _module.__default.EvalExpr($LS($LS($LZ)), C#3_0, u#3_0) }
                          $Is(C#3_0, Tclass._module.Context())
                             && $Is(u#3_0, Tclass._module.Term())
                             && (forall C$ih#3_0#3_0: DatatypeType, u$ih#3_0#3_0: DatatypeType ::
                              { _module.__default.Step(u$ih#3_0#3_0), _module.__default.IsContext($LS($LZ), C$ih#3_0#3_0) }
                                { _module.__default.EvalExpr($LS($LZ), C$ih#3_0#3_0, u$ih#3_0#3_0) }
                              $Is(C$ih#3_0#3_0, Tclass._module.Context())
                                   && $Is(u$ih#3_0#3_0, Tclass._module.Term())
                                 ==>
                                DtRank(C$ih#3_0#3_0) < DtRank(C#3_0)
                                   || (DtRank(C$ih#3_0#3_0) == DtRank(C#3_0) && DtRank(u$ih#3_0#3_0) < DtRank(u#3_0))
                                 ==> !(
                                  _module.__default.IsContext($LS($LZ), C$ih#3_0#3_0)
                                   && _module.Term.car(t#0)
                                     == _module.__default.EvalExpr($LS($LZ), C$ih#3_0#3_0, u$ih#3_0#3_0)
                                   && _module.__default.Step(u$ih#3_0#3_0) != u$ih#3_0#3_0))
                             &&
                            true
                             && #_module.Context.Hole() == C#3_0
                             && #_module.Term.S() == u#3_0
                             &&
                            _module.__default.IsContext($LS($LS($LZ)), C#3_0)
                             && _module.Term.car(t#0) == _module.__default.EvalExpr($LS($LS($LZ)), C#3_0, u#3_0)
                             && _module.__default.Step(u#3_0) != u#3_0);
                    assert {:subsumption 0} _module.__default.IsTerminal#canCall(_module.Term.car(t#0))
                       ==> _module.__default.IsTerminal(_module.Term.car(t#0))
                         || !(exists C#3_0: DatatypeType, u#3_0: DatatypeType ::
                          { _module.__default.Step(u#3_0), _module.__default.IsContext($LS($LS($LZ)), C#3_0) }
                            { _module.__default.EvalExpr($LS($LS($LZ)), C#3_0, u#3_0) }
                          $Is(C#3_0, Tclass._module.Context())
                             && $Is(u#3_0, Tclass._module.Term())
                             && (forall C$ih#3_0#3_0: DatatypeType, u$ih#3_0#3_0: DatatypeType ::
                              { _module.__default.Step(u$ih#3_0#3_0), _module.__default.IsContext($LS($LZ), C$ih#3_0#3_0) }
                                { _module.__default.EvalExpr($LS($LZ), C$ih#3_0#3_0, u$ih#3_0#3_0) }
                              $Is(C$ih#3_0#3_0, Tclass._module.Context())
                                   && $Is(u$ih#3_0#3_0, Tclass._module.Term())
                                 ==>
                                DtRank(C$ih#3_0#3_0) < DtRank(C#3_0)
                                   || (DtRank(C$ih#3_0#3_0) == DtRank(C#3_0) && DtRank(u$ih#3_0#3_0) < DtRank(u#3_0))
                                 ==> !(
                                  _module.__default.IsContext($LS($LZ), C$ih#3_0#3_0)
                                   && _module.Term.car(t#0)
                                     == _module.__default.EvalExpr($LS($LZ), C$ih#3_0#3_0, u$ih#3_0#3_0)
                                   && _module.__default.Step(u$ih#3_0#3_0) != u$ih#3_0#3_0))
                             &&
                            true
                             && (exists a#3_1#0#0: DatatypeType, a#3_1#1#0: DatatypeType ::
                              { #_module.Context.C_term(a#3_1#0#0, a#3_1#1#0) }
                              $Is(a#3_1#0#0, Tclass._module.Context())
                                 && $Is(a#3_1#1#0, Tclass._module.Term())
                                 && #_module.Context.C_term(a#3_1#0#0, a#3_1#1#0) == C#3_0)
                             && #_module.Term.S() == u#3_0
                             &&
                            _module.__default.IsContext($LS($LS($LZ)), C#3_0)
                             && _module.Term.car(t#0) == _module.__default.EvalExpr($LS($LS($LZ)), C#3_0, u#3_0)
                             && _module.__default.Step(u#3_0) != u#3_0);
                    assert {:subsumption 0} _module.__default.IsTerminal#canCall(_module.Term.car(t#0))
                       ==> _module.__default.IsTerminal(_module.Term.car(t#0))
                         || !(exists C#3_0: DatatypeType, u#3_0: DatatypeType ::
                          { _module.__default.Step(u#3_0), _module.__default.IsContext($LS($LS($LZ)), C#3_0) }
                            { _module.__default.EvalExpr($LS($LS($LZ)), C#3_0, u#3_0) }
                          $Is(C#3_0, Tclass._module.Context())
                             && $Is(u#3_0, Tclass._module.Term())
                             && (forall C$ih#3_0#3_0: DatatypeType, u$ih#3_0#3_0: DatatypeType ::
                              { _module.__default.Step(u$ih#3_0#3_0), _module.__default.IsContext($LS($LZ), C$ih#3_0#3_0) }
                                { _module.__default.EvalExpr($LS($LZ), C$ih#3_0#3_0, u$ih#3_0#3_0) }
                              $Is(C$ih#3_0#3_0, Tclass._module.Context())
                                   && $Is(u$ih#3_0#3_0, Tclass._module.Term())
                                 ==>
                                DtRank(C$ih#3_0#3_0) < DtRank(C#3_0)
                                   || (DtRank(C$ih#3_0#3_0) == DtRank(C#3_0) && DtRank(u$ih#3_0#3_0) < DtRank(u#3_0))
                                 ==> !(
                                  _module.__default.IsContext($LS($LZ), C$ih#3_0#3_0)
                                   && _module.Term.car(t#0)
                                     == _module.__default.EvalExpr($LS($LZ), C$ih#3_0#3_0, u$ih#3_0#3_0)
                                   && _module.__default.Step(u$ih#3_0#3_0) != u$ih#3_0#3_0))
                             &&
                            true
                             && (exists a#3_2#0#0: DatatypeType, a#3_2#1#0: DatatypeType ::
                              { #_module.Context.value_C(a#3_2#0#0, a#3_2#1#0) }
                              $Is(a#3_2#0#0, Tclass._module.Term())
                                 && $Is(a#3_2#1#0, Tclass._module.Context())
                                 && #_module.Context.value_C(a#3_2#0#0, a#3_2#1#0) == C#3_0)
                             && #_module.Term.S() == u#3_0
                             &&
                            _module.__default.IsContext($LS($LS($LZ)), C#3_0)
                             && _module.Term.car(t#0) == _module.__default.EvalExpr($LS($LS($LZ)), C#3_0, u#3_0)
                             && _module.__default.Step(u#3_0) != u#3_0);
                    assert {:subsumption 0} _module.__default.IsTerminal#canCall(_module.Term.car(t#0))
                       ==> _module.__default.IsTerminal(_module.Term.car(t#0))
                         || !(exists C#3_0: DatatypeType, u#3_0: DatatypeType ::
                          { _module.__default.Step(u#3_0), _module.__default.IsContext($LS($LS($LZ)), C#3_0) }
                            { _module.__default.EvalExpr($LS($LS($LZ)), C#3_0, u#3_0) }
                          $Is(C#3_0, Tclass._module.Context())
                             && $Is(u#3_0, Tclass._module.Term())
                             && (forall C$ih#3_0#3_0: DatatypeType, u$ih#3_0#3_0: DatatypeType ::
                              { _module.__default.Step(u$ih#3_0#3_0), _module.__default.IsContext($LS($LZ), C$ih#3_0#3_0) }
                                { _module.__default.EvalExpr($LS($LZ), C$ih#3_0#3_0, u$ih#3_0#3_0) }
                              $Is(C$ih#3_0#3_0, Tclass._module.Context())
                                   && $Is(u$ih#3_0#3_0, Tclass._module.Term())
                                 ==>
                                DtRank(C$ih#3_0#3_0) < DtRank(C#3_0)
                                   || (DtRank(C$ih#3_0#3_0) == DtRank(C#3_0) && DtRank(u$ih#3_0#3_0) < DtRank(u#3_0))
                                 ==> !(
                                  _module.__default.IsContext($LS($LZ), C$ih#3_0#3_0)
                                   && _module.Term.car(t#0)
                                     == _module.__default.EvalExpr($LS($LZ), C$ih#3_0#3_0, u$ih#3_0#3_0)
                                   && _module.__default.Step(u$ih#3_0#3_0) != u$ih#3_0#3_0))
                             &&
                            true
                             && #_module.Context.Hole() == C#3_0
                             && #_module.Term.K() == u#3_0
                             &&
                            _module.__default.IsContext($LS($LS($LZ)), C#3_0)
                             && _module.Term.car(t#0) == _module.__default.EvalExpr($LS($LS($LZ)), C#3_0, u#3_0)
                             && _module.__default.Step(u#3_0) != u#3_0);
                    assert {:subsumption 0} _module.__default.IsTerminal#canCall(_module.Term.car(t#0))
                       ==> _module.__default.IsTerminal(_module.Term.car(t#0))
                         || !(exists C#3_0: DatatypeType, u#3_0: DatatypeType ::
                          { _module.__default.Step(u#3_0), _module.__default.IsContext($LS($LS($LZ)), C#3_0) }
                            { _module.__default.EvalExpr($LS($LS($LZ)), C#3_0, u#3_0) }
                          $Is(C#3_0, Tclass._module.Context())
                             && $Is(u#3_0, Tclass._module.Term())
                             && (forall C$ih#3_0#3_0: DatatypeType, u$ih#3_0#3_0: DatatypeType ::
                              { _module.__default.Step(u$ih#3_0#3_0), _module.__default.IsContext($LS($LZ), C$ih#3_0#3_0) }
                                { _module.__default.EvalExpr($LS($LZ), C$ih#3_0#3_0, u$ih#3_0#3_0) }
                              $Is(C$ih#3_0#3_0, Tclass._module.Context())
                                   && $Is(u$ih#3_0#3_0, Tclass._module.Term())
                                 ==>
                                DtRank(C$ih#3_0#3_0) < DtRank(C#3_0)
                                   || (DtRank(C$ih#3_0#3_0) == DtRank(C#3_0) && DtRank(u$ih#3_0#3_0) < DtRank(u#3_0))
                                 ==> !(
                                  _module.__default.IsContext($LS($LZ), C$ih#3_0#3_0)
                                   && _module.Term.car(t#0)
                                     == _module.__default.EvalExpr($LS($LZ), C$ih#3_0#3_0, u$ih#3_0#3_0)
                                   && _module.__default.Step(u$ih#3_0#3_0) != u$ih#3_0#3_0))
                             &&
                            true
                             && (exists a#3_1#0#0: DatatypeType, a#3_1#1#0: DatatypeType ::
                              { #_module.Context.C_term(a#3_1#0#0, a#3_1#1#0) }
                              $Is(a#3_1#0#0, Tclass._module.Context())
                                 && $Is(a#3_1#1#0, Tclass._module.Term())
                                 && #_module.Context.C_term(a#3_1#0#0, a#3_1#1#0) == C#3_0)
                             && #_module.Term.K() == u#3_0
                             &&
                            _module.__default.IsContext($LS($LS($LZ)), C#3_0)
                             && _module.Term.car(t#0) == _module.__default.EvalExpr($LS($LS($LZ)), C#3_0, u#3_0)
                             && _module.__default.Step(u#3_0) != u#3_0);
                    assert {:subsumption 0} _module.__default.IsTerminal#canCall(_module.Term.car(t#0))
                       ==> _module.__default.IsTerminal(_module.Term.car(t#0))
                         || !(exists C#3_0: DatatypeType, u#3_0: DatatypeType ::
                          { _module.__default.Step(u#3_0), _module.__default.IsContext($LS($LS($LZ)), C#3_0) }
                            { _module.__default.EvalExpr($LS($LS($LZ)), C#3_0, u#3_0) }
                          $Is(C#3_0, Tclass._module.Context())
                             && $Is(u#3_0, Tclass._module.Term())
                             && (forall C$ih#3_0#3_0: DatatypeType, u$ih#3_0#3_0: DatatypeType ::
                              { _module.__default.Step(u$ih#3_0#3_0), _module.__default.IsContext($LS($LZ), C$ih#3_0#3_0) }
                                { _module.__default.EvalExpr($LS($LZ), C$ih#3_0#3_0, u$ih#3_0#3_0) }
                              $Is(C$ih#3_0#3_0, Tclass._module.Context())
                                   && $Is(u$ih#3_0#3_0, Tclass._module.Term())
                                 ==>
                                DtRank(C$ih#3_0#3_0) < DtRank(C#3_0)
                                   || (DtRank(C$ih#3_0#3_0) == DtRank(C#3_0) && DtRank(u$ih#3_0#3_0) < DtRank(u#3_0))
                                 ==> !(
                                  _module.__default.IsContext($LS($LZ), C$ih#3_0#3_0)
                                   && _module.Term.car(t#0)
                                     == _module.__default.EvalExpr($LS($LZ), C$ih#3_0#3_0, u$ih#3_0#3_0)
                                   && _module.__default.Step(u$ih#3_0#3_0) != u$ih#3_0#3_0))
                             &&
                            true
                             && (exists a#3_2#0#0: DatatypeType, a#3_2#1#0: DatatypeType ::
                              { #_module.Context.value_C(a#3_2#0#0, a#3_2#1#0) }
                              $Is(a#3_2#0#0, Tclass._module.Term())
                                 && $Is(a#3_2#1#0, Tclass._module.Context())
                                 && #_module.Context.value_C(a#3_2#0#0, a#3_2#1#0) == C#3_0)
                             && #_module.Term.K() == u#3_0
                             &&
                            _module.__default.IsContext($LS($LS($LZ)), C#3_0)
                             && _module.Term.car(t#0) == _module.__default.EvalExpr($LS($LS($LZ)), C#3_0, u#3_0)
                             && _module.__default.Step(u#3_0) != u#3_0);
                    assert {:subsumption 0} _module.__default.IsTerminal#canCall(_module.Term.car(t#0))
                       ==> _module.__default.IsTerminal(_module.Term.car(t#0))
                         || !(exists C#3_0: DatatypeType, u#3_0: DatatypeType ::
                          { _module.__default.Step(u#3_0), _module.__default.IsContext($LS($LS($LZ)), C#3_0) }
                            { _module.__default.EvalExpr($LS($LS($LZ)), C#3_0, u#3_0) }
                          $Is(C#3_0, Tclass._module.Context())
                             && $Is(u#3_0, Tclass._module.Term())
                             && (forall C$ih#3_0#3_0: DatatypeType, u$ih#3_0#3_0: DatatypeType ::
                              { _module.__default.Step(u$ih#3_0#3_0), _module.__default.IsContext($LS($LZ), C$ih#3_0#3_0) }
                                { _module.__default.EvalExpr($LS($LZ), C$ih#3_0#3_0, u$ih#3_0#3_0) }
                              $Is(C$ih#3_0#3_0, Tclass._module.Context())
                                   && $Is(u$ih#3_0#3_0, Tclass._module.Term())
                                 ==>
                                DtRank(C$ih#3_0#3_0) < DtRank(C#3_0)
                                   || (DtRank(C$ih#3_0#3_0) == DtRank(C#3_0) && DtRank(u$ih#3_0#3_0) < DtRank(u#3_0))
                                 ==> !(
                                  _module.__default.IsContext($LS($LZ), C$ih#3_0#3_0)
                                   && _module.Term.car(t#0)
                                     == _module.__default.EvalExpr($LS($LZ), C$ih#3_0#3_0, u$ih#3_0#3_0)
                                   && _module.__default.Step(u$ih#3_0#3_0) != u$ih#3_0#3_0))
                             &&
                            true
                             && #_module.Context.Hole() == C#3_0
                             && (exists a#3_5#0#0: DatatypeType, a#3_5#1#0: DatatypeType ::
                              { #_module.Term.Apply(a#3_5#0#0, a#3_5#1#0) }
                              $Is(a#3_5#0#0, Tclass._module.Term())
                                 && $Is(a#3_5#1#0, Tclass._module.Term())
                                 && #_module.Term.Apply(a#3_5#0#0, a#3_5#1#0) == u#3_0)
                             &&
                            _module.__default.IsContext($LS($LS($LZ)), C#3_0)
                             && _module.Term.car(t#0) == _module.__default.EvalExpr($LS($LS($LZ)), C#3_0, u#3_0)
                             && _module.__default.Step(u#3_0) != u#3_0);
                    assert {:subsumption 0} _module.__default.IsTerminal#canCall(_module.Term.car(t#0))
                       ==> _module.__default.IsTerminal(_module.Term.car(t#0))
                         || !(exists C#3_0: DatatypeType, u#3_0: DatatypeType ::
                          { _module.__default.Step(u#3_0), _module.__default.IsContext($LS($LS($LZ)), C#3_0) }
                            { _module.__default.EvalExpr($LS($LS($LZ)), C#3_0, u#3_0) }
                          $Is(C#3_0, Tclass._module.Context())
                             && $Is(u#3_0, Tclass._module.Term())
                             && (forall C$ih#3_0#3_0: DatatypeType, u$ih#3_0#3_0: DatatypeType ::
                              { _module.__default.Step(u$ih#3_0#3_0), _module.__default.IsContext($LS($LZ), C$ih#3_0#3_0) }
                                { _module.__default.EvalExpr($LS($LZ), C$ih#3_0#3_0, u$ih#3_0#3_0) }
                              $Is(C$ih#3_0#3_0, Tclass._module.Context())
                                   && $Is(u$ih#3_0#3_0, Tclass._module.Term())
                                 ==>
                                DtRank(C$ih#3_0#3_0) < DtRank(C#3_0)
                                   || (DtRank(C$ih#3_0#3_0) == DtRank(C#3_0) && DtRank(u$ih#3_0#3_0) < DtRank(u#3_0))
                                 ==> !(
                                  _module.__default.IsContext($LS($LZ), C$ih#3_0#3_0)
                                   && _module.Term.car(t#0)
                                     == _module.__default.EvalExpr($LS($LZ), C$ih#3_0#3_0, u$ih#3_0#3_0)
                                   && _module.__default.Step(u$ih#3_0#3_0) != u$ih#3_0#3_0))
                             &&
                            true
                             && (exists a#3_1#0#0: DatatypeType, a#3_1#1#0: DatatypeType ::
                              { #_module.Context.C_term(a#3_1#0#0, a#3_1#1#0) }
                              $Is(a#3_1#0#0, Tclass._module.Context())
                                 && $Is(a#3_1#1#0, Tclass._module.Term())
                                 && #_module.Context.C_term(a#3_1#0#0, a#3_1#1#0) == C#3_0)
                             && (exists a#3_5#0#0: DatatypeType, a#3_5#1#0: DatatypeType ::
                              { #_module.Term.Apply(a#3_5#0#0, a#3_5#1#0) }
                              $Is(a#3_5#0#0, Tclass._module.Term())
                                 && $Is(a#3_5#1#0, Tclass._module.Term())
                                 && #_module.Term.Apply(a#3_5#0#0, a#3_5#1#0) == u#3_0)
                             &&
                            _module.__default.IsContext($LS($LS($LZ)), C#3_0)
                             && _module.Term.car(t#0) == _module.__default.EvalExpr($LS($LS($LZ)), C#3_0, u#3_0)
                             && _module.__default.Step(u#3_0) != u#3_0);
                    assert {:subsumption 0} _module.__default.IsTerminal#canCall(_module.Term.car(t#0))
                       ==> _module.__default.IsTerminal(_module.Term.car(t#0))
                         || !(exists C#3_0: DatatypeType, u#3_0: DatatypeType ::
                          { _module.__default.Step(u#3_0), _module.__default.IsContext($LS($LS($LZ)), C#3_0) }
                            { _module.__default.EvalExpr($LS($LS($LZ)), C#3_0, u#3_0) }
                          $Is(C#3_0, Tclass._module.Context())
                             && $Is(u#3_0, Tclass._module.Term())
                             && (forall C$ih#3_0#3_0: DatatypeType, u$ih#3_0#3_0: DatatypeType ::
                              { _module.__default.Step(u$ih#3_0#3_0), _module.__default.IsContext($LS($LZ), C$ih#3_0#3_0) }
                                { _module.__default.EvalExpr($LS($LZ), C$ih#3_0#3_0, u$ih#3_0#3_0) }
                              $Is(C$ih#3_0#3_0, Tclass._module.Context())
                                   && $Is(u$ih#3_0#3_0, Tclass._module.Term())
                                 ==>
                                DtRank(C$ih#3_0#3_0) < DtRank(C#3_0)
                                   || (DtRank(C$ih#3_0#3_0) == DtRank(C#3_0) && DtRank(u$ih#3_0#3_0) < DtRank(u#3_0))
                                 ==> !(
                                  _module.__default.IsContext($LS($LZ), C$ih#3_0#3_0)
                                   && _module.Term.car(t#0)
                                     == _module.__default.EvalExpr($LS($LZ), C$ih#3_0#3_0, u$ih#3_0#3_0)
                                   && _module.__default.Step(u$ih#3_0#3_0) != u$ih#3_0#3_0))
                             &&
                            true
                             && (exists a#3_2#0#0: DatatypeType, a#3_2#1#0: DatatypeType ::
                              { #_module.Context.value_C(a#3_2#0#0, a#3_2#1#0) }
                              $Is(a#3_2#0#0, Tclass._module.Term())
                                 && $Is(a#3_2#1#0, Tclass._module.Context())
                                 && #_module.Context.value_C(a#3_2#0#0, a#3_2#1#0) == C#3_0)
                             && (exists a#3_5#0#0: DatatypeType, a#3_5#1#0: DatatypeType ::
                              { #_module.Term.Apply(a#3_5#0#0, a#3_5#1#0) }
                              $Is(a#3_5#0#0, Tclass._module.Term())
                                 && $Is(a#3_5#1#0, Tclass._module.Term())
                                 && #_module.Term.Apply(a#3_5#0#0, a#3_5#1#0) == u#3_0)
                             &&
                            _module.__default.IsContext($LS($LS($LZ)), C#3_0)
                             && _module.Term.car(t#0) == _module.__default.EvalExpr($LS($LS($LZ)), C#3_0, u#3_0)
                             && _module.__default.Step(u#3_0) != u#3_0);
                    assume _module.__default.IsTerminal(_module.Term.car(t#0));
                    // ----- if statement ----- Combinators.dfy(223,7)
                    assert _module.Term.Apply_q(t#0);
                    assume true;
                    if (r#0 != _module.Term.cdr(t#0))
                    {
                        // ----- return statement ----- Combinators.dfy(229,9)
                        // ----- update statement ----- Combinators.dfy(229,9)
                        assume true;
                        assume true;
                        assume true;
                        assert _module.Term.Apply_q(t#0);
                        assume true;
                        $rhs#3_0_0 := #_module.Term.Apply(_module.Term.car(t#0), r#0);
                        assert _module.Term.Apply_q(t#0);
                        assume true;
                        $rhs#3_0_1 := #_module.Context.value_C(_module.Term.car(t#0), C#0);
                        assume true;
                        $rhs#3_0_2 := u#0;
                        r#0 := $rhs#3_0_0;
                        C#0 := $rhs#3_0_1;
                        u#0 := $rhs#3_0_2;
                        assume {:captureState "Combinators.dfy(229,52)"} true;
                        return;
                    }
                    else
                    {
                        // ----- forall statement (proof) ----- Combinators.dfy(231,9)
                        if (*)
                        {
                            // Assume Fuel Constant
                            havoc C#3_1, u#3_1;
                            assume $Is(C#3_1, Tclass._module.Context()) && $Is(u#3_1, Tclass._module.Term());
                            ##C#3_0 := C#3_1;
                            // assume allocatedness for argument to function
                            assume $IsAlloc(##C#3_0, Tclass._module.Context(), $Heap);
                            assume _module.__default.IsContext#canCall(C#3_1);
                            if (_module.__default.IsContext($LS($LZ), C#3_1))
                            {
                                ##C#3_1 := C#3_1;
                                // assume allocatedness for argument to function
                                assume $IsAlloc(##C#3_1, Tclass._module.Context(), $Heap);
                                ##t#3_1 := u#3_1;
                                // assume allocatedness for argument to function
                                assume $IsAlloc(##t#3_1, Tclass._module.Term(), $Heap);
                                assert {:subsumption 0} _module.__default.IsContext($LS($LS($LZ)), ##C#3_1);
                                assume _module.__default.EvalExpr#canCall(C#3_1, u#3_1);
                            }

                            assume _module.__default.IsContext#canCall(C#3_1)
                               && (_module.__default.IsContext($LS($LZ), C#3_1)
                                 ==> _module.__default.EvalExpr#canCall(C#3_1, u#3_1));
                            assume _module.__default.IsContext($LS($LZ), C#3_1)
                               && t#0 == _module.__default.EvalExpr($LS($LZ), C#3_1, u#3_1);
                            // ----- assert statement ----- Combinators.dfy(237,11)
                            if (_module.Term.Apply_q(t#0))
                            {
                                assert _module.Term.Apply_q(t#0);
                                ##t#3_2 := _module.Term.car(t#0);
                                // assume allocatedness for argument to function
                                assume $IsAlloc(##t#3_2, Tclass._module.Term(), $Heap);
                                assume _module.__default.IsValue#canCall(_module.Term.car(t#0));
                            }

                            assume _module.Term.Apply_q(t#0)
                               ==> _module.__default.IsValue#canCall(_module.Term.car(t#0));
                            assert {:subsumption 0} _module.Term.Apply_q(t#0);
                            assert {:subsumption 0} _module.__default.IsValue($LS($LS($LZ)), _module.Term.car(t#0));
                            assume _module.Term.Apply_q(t#0)
                               && _module.__default.IsValue($LS($LZ), _module.Term.car(t#0));
                            assume true;
                            havoc at#3_1_0, D#3_1_0;
                            havoc D#3_2_0, bt#3_2_0;
                            if (C#3_1 == #_module.Context.Hole())
                            {
                                // ----- assert statement ----- Combinators.dfy(240,15)
                                assume true;
                                assert t#0 == u#3_1;
                            }
                            else if (C#3_1 == #_module.Context.C_term(D#3_2_0, bt#3_2_0))
                            {
                                assume $Is(D#3_2_0, Tclass._module.Context());
                                assume $Is(bt#3_2_0, Tclass._module.Term());
                                // ----- assert statement ----- Combinators.dfy(242,15)
                                assert _module.Term.Apply_q(t#0);
                                if (bt#3_2_0 == _module.Term.cdr(t#0))
                                {
                                    assert _module.Term.Apply_q(t#0);
                                    ##C#3_2_0 := D#3_2_0;
                                    // assume allocatedness for argument to function
                                    assume $IsAlloc(##C#3_2_0, Tclass._module.Context(), $Heap);
                                    ##t#3_2_0 := u#3_1;
                                    // assume allocatedness for argument to function
                                    assume $IsAlloc(##t#3_2_0, Tclass._module.Term(), $Heap);
                                    assert {:subsumption 0} _module.__default.IsContext($LS($LS($LZ)), ##C#3_2_0);
                                    assume _module.__default.EvalExpr#canCall(D#3_2_0, u#3_1);
                                }

                                assume bt#3_2_0 == _module.Term.cdr(t#0)
                                   ==> _module.__default.EvalExpr#canCall(D#3_2_0, u#3_1);
                                assert {:subsumption 0} bt#3_2_0 == _module.Term.cdr(t#0);
                                assert {:subsumption 0} _module.Term.car(t#0)
                                   == _module.__default.EvalExpr($LS($LS($LZ)), D#3_2_0, u#3_1);
                                assume bt#3_2_0 == _module.Term.cdr(t#0)
                                   && _module.Term.car(t#0) == _module.__default.EvalExpr($LS($LZ), D#3_2_0, u#3_1);
                            }
                            else if (C#3_1 == #_module.Context.value_C(at#3_1_0, D#3_1_0))
                            {
                                assume $Is(at#3_1_0, Tclass._module.Term());
                                assume $Is(D#3_1_0, Tclass._module.Context());
                                // ----- assert statement ----- Combinators.dfy(244,15)
                                assert _module.Term.Apply_q(t#0);
                                if (at#3_1_0 == _module.Term.car(t#0))
                                {
                                    assert _module.Term.Apply_q(t#0);
                                    ##C#3_1_0 := D#3_1_0;
                                    // assume allocatedness for argument to function
                                    assume $IsAlloc(##C#3_1_0, Tclass._module.Context(), $Heap);
                                    ##t#3_1_0 := u#3_1;
                                    // assume allocatedness for argument to function
                                    assume $IsAlloc(##t#3_1_0, Tclass._module.Term(), $Heap);
                                    assert {:subsumption 0} _module.__default.IsContext($LS($LS($LZ)), ##C#3_1_0);
                                    assume _module.__default.EvalExpr#canCall(D#3_1_0, u#3_1);
                                }

                                assume at#3_1_0 == _module.Term.car(t#0)
                                   ==> _module.__default.EvalExpr#canCall(D#3_1_0, u#3_1);
                                assert {:subsumption 0} at#3_1_0 == _module.Term.car(t#0);
                                assert {:subsumption 0} _module.Term.cdr(t#0)
                                   == _module.__default.EvalExpr($LS($LS($LZ)), D#3_1_0, u#3_1);
                                assume at#3_1_0 == _module.Term.car(t#0)
                                   && _module.Term.cdr(t#0) == _module.__default.EvalExpr($LS($LZ), D#3_1_0, u#3_1);
                            }
                            else
                            {
                                assume false;
                            }

                            assert _module.__default.Step(u#3_1) == u#3_1;
                            assume false;
                        }
                        else
                        {
                            assume (forall C#3_2: DatatypeType, u#3_2: DatatypeType ::
                              { _module.__default.Step(u#3_2), _module.__default.IsContext($LS($LZ), C#3_2) }
                                { _module.__default.EvalExpr($LS($LZ), C#3_2, u#3_2) }
                              $Is(C#3_2, Tclass._module.Context())
                                   && $Is(u#3_2, Tclass._module.Term())
                                   &&
                                  _module.__default.IsContext($LS($LZ), C#3_2)
                                   && t#0 == _module.__default.EvalExpr($LS($LZ), C#3_2, u#3_2)
                                 ==> _module.__default.Step(u#3_2) == u#3_2);
                        }

                        assume {:captureState "Combinators.dfy(246,8)"} true;
                        // ----- assignment statement ----- Combinators.dfy(247,11)
                        assume true;
                        assume true;
                        r#0 := t#0;
                        assume {:captureState "Combinators.dfy(247,14)"} true;
                    }
                }
                else
                {
                    // ----- assignment statement ----- Combinators.dfy(250,9)
                    assume true;
                    assume true;
                    r#0 := t#0;
                    assume {:captureState "Combinators.dfy(250,12)"} true;
                }
            }
        }
    }
}



procedure CheckWellformed$$_module.__default.Lemma__ContextPossibilities(t#0: DatatypeType
       where $Is(t#0, Tclass._module.Term())
         && $IsAlloc(t#0, Tclass._module.Term(), $Heap)
         && $IsA#_module.Term(t#0));
  free requires 12 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.Lemma__ContextPossibilities(t#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var C#0: DatatypeType;
  var u#0: DatatypeType;
  var ##C#0: DatatypeType;
  var ##C#1: DatatypeType;
  var ##t#0: DatatypeType;
  var D#0: DatatypeType;
  var ##C#2: DatatypeType;
  var ##t#1: DatatypeType;
  var ##t#2: DatatypeType;
  var D#2: DatatypeType;
  var ##C#3: DatatypeType;
  var ##t#3: DatatypeType;

    // AddMethodImpl: Lemma_ContextPossibilities, CheckWellformed$$_module.__default.Lemma__ContextPossibilities
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "Combinators.dfy(258,6): initial state"} true;
    havoc $Heap;
    assume old($Heap) == $Heap;
    assume {:captureState "Combinators.dfy(259,10): post-state"} true;
    havoc C#0;
    assume $Is(C#0, Tclass._module.Context());
    havoc u#0;
    assume $Is(u#0, Tclass._module.Term());
    if (*)
    {
        ##C#0 := C#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##C#0, Tclass._module.Context(), $Heap);
        assume _module.__default.IsContext#canCall(C#0);
        assume _module.__default.IsContext($LS($LZ), C#0);
        ##C#1 := C#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##C#1, Tclass._module.Context(), $Heap);
        ##t#0 := u#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##t#0, Tclass._module.Term(), $Heap);
        assert {:subsumption 0} _module.__default.IsContext($LS($LS($LZ)), ##C#1);
        assume _module.__default.IsContext($LS($LZ), ##C#1);
        assume _module.__default.EvalExpr#canCall(C#0, u#0);
        assume t#0 == _module.__default.EvalExpr($LS($LZ), C#0, u#0);
        if (*)
        {
            if (*)
            {
                assume C#0 == Lit(#_module.Context.Hole());
                assume t#0 == u#0;
            }
            else
            {
                assume !(C#0 == Lit(#_module.Context.Hole()) && t#0 == u#0);
                assume _module.Term.Apply_q(t#0);
                havoc D#0;
                assume $Is(D#0, Tclass._module.Context());
                assert _module.Term.Apply_q(t#0);
                assume C#0 == #_module.Context.C_term(D#0, _module.Term.cdr(t#0));
                assert _module.Term.Apply_q(t#0);
                ##C#2 := D#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##C#2, Tclass._module.Context(), $Heap);
                ##t#1 := u#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##t#1, Tclass._module.Term(), $Heap);
                assert {:subsumption 0} _module.__default.IsContext($LS($LS($LZ)), ##C#2);
                assume _module.__default.IsContext($LS($LZ), ##C#2);
                assume _module.__default.EvalExpr#canCall(D#0, u#0);
                assume _module.Term.car(t#0) == _module.__default.EvalExpr($LS($LZ), D#0, u#0);
            }
        }
        else
        {
            assume !((C#0 == Lit(#_module.Context.Hole()) && t#0 == u#0)
               || (_module.Term.Apply_q(t#0)
                 && (exists D#1: DatatypeType ::
                  {:_induction D#1} { _module.__default.EvalExpr($LS($LZ), D#1, u#0) }
                    { #_module.Context.C_term(D#1, _module.Term.cdr(t#0)) }
                  $Is(D#1, Tclass._module.Context())
                     &&
                    C#0 == #_module.Context.C_term(D#1, _module.Term.cdr(t#0))
                     && _module.Term.car(t#0) == _module.__default.EvalExpr($LS($LZ), D#1, u#0))));
            assume _module.Term.Apply_q(t#0);
            assert _module.Term.Apply_q(t#0);
            ##t#2 := _module.Term.car(t#0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##t#2, Tclass._module.Term(), $Heap);
            assume _module.__default.IsValue#canCall(_module.Term.car(t#0));
            assume _module.__default.IsValue($LS($LZ), _module.Term.car(t#0));
            havoc D#2;
            assume $Is(D#2, Tclass._module.Context());
            assert _module.Term.Apply_q(t#0);
            assume C#0 == #_module.Context.value_C(_module.Term.car(t#0), D#2);
            assert _module.Term.Apply_q(t#0);
            ##C#3 := D#2;
            // assume allocatedness for argument to function
            assume $IsAlloc(##C#3, Tclass._module.Context(), $Heap);
            ##t#3 := u#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##t#3, Tclass._module.Term(), $Heap);
            assert {:subsumption 0} _module.__default.IsContext($LS($LS($LZ)), ##C#3);
            assume _module.__default.IsContext($LS($LZ), ##C#3);
            assume _module.__default.EvalExpr#canCall(D#2, u#0);
            assume _module.Term.cdr(t#0) == _module.__default.EvalExpr($LS($LZ), D#2, u#0);
        }
    }
    else
    {
        assume _module.__default.IsContext($LS($LZ), C#0)
             && t#0 == _module.__default.EvalExpr($LS($LZ), C#0, u#0)
           ==> (C#0 == Lit(#_module.Context.Hole()) && t#0 == u#0)
             || (_module.Term.Apply_q(t#0)
               && (exists D#1: DatatypeType ::
                {:_induction D#1} { _module.__default.EvalExpr($LS($LZ), D#1, u#0) }
                  { #_module.Context.C_term(D#1, _module.Term.cdr(t#0)) }
                $Is(D#1, Tclass._module.Context())
                   &&
                  C#0 == #_module.Context.C_term(D#1, _module.Term.cdr(t#0))
                   && _module.Term.car(t#0) == _module.__default.EvalExpr($LS($LZ), D#1, u#0)))
             || (
              _module.Term.Apply_q(t#0)
               && _module.__default.IsValue($LS($LZ), _module.Term.car(t#0))
               && (exists D#3: DatatypeType ::
                {:_induction D#3} { _module.__default.EvalExpr($LS($LZ), D#3, u#0) }
                  { #_module.Context.value_C(_module.Term.car(t#0), D#3) }
                $Is(D#3, Tclass._module.Context())
                   &&
                  C#0 == #_module.Context.value_C(_module.Term.car(t#0), D#3)
                   && _module.Term.cdr(t#0) == _module.__default.EvalExpr($LS($LZ), D#3, u#0)));
    }

    assume (forall C#1: DatatypeType, u#1: DatatypeType ::
      {:_induction C#1, u#1} { _module.__default.EvalExpr($LS($LZ), C#1, u#1) }
      $Is(C#1, Tclass._module.Context()) && $Is(u#1, Tclass._module.Term())
         ==>
        _module.__default.IsContext($LS($LZ), C#1)
           && t#0 == _module.__default.EvalExpr($LS($LZ), C#1, u#1)
         ==> (C#1 == Lit(#_module.Context.Hole()) && t#0 == u#1)
           || (_module.Term.Apply_q(t#0)
             && (exists D#4: DatatypeType ::
              {:_induction D#4} { _module.__default.EvalExpr($LS($LZ), D#4, u#1) }
                { #_module.Context.C_term(D#4, _module.Term.cdr(t#0)) }
              $Is(D#4, Tclass._module.Context())
                 &&
                C#1 == #_module.Context.C_term(D#4, _module.Term.cdr(t#0))
                 && _module.Term.car(t#0) == _module.__default.EvalExpr($LS($LZ), D#4, u#1)))
           || (
            _module.Term.Apply_q(t#0)
             && _module.__default.IsValue($LS($LZ), _module.Term.car(t#0))
             && (exists D#5: DatatypeType ::
              {:_induction D#5} { _module.__default.EvalExpr($LS($LZ), D#5, u#1) }
                { #_module.Context.value_C(_module.Term.car(t#0), D#5) }
              $Is(D#5, Tclass._module.Context())
                 &&
                C#1 == #_module.Context.value_C(_module.Term.car(t#0), D#5)
                 && _module.Term.cdr(t#0) == _module.__default.EvalExpr($LS($LZ), D#5, u#1))));
}



procedure Call$$_module.__default.Lemma__ContextPossibilities(t#0: DatatypeType
       where $Is(t#0, Tclass._module.Term())
         && $IsAlloc(t#0, Tclass._module.Term(), $Heap)
         && $IsA#_module.Term(t#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall C#1: DatatypeType, u#1: DatatypeType ::
    { _module.__default.EvalExpr($LS($LZ), C#1, u#1) }
    $Is(C#1, Tclass._module.Context()) && $Is(u#1, Tclass._module.Term())
       ==> _module.__default.IsContext#canCall(C#1)
         && (_module.__default.IsContext($LS($LZ), C#1)
           ==> _module.__default.EvalExpr#canCall(C#1, u#1))
         && (_module.__default.EvalExpr#canCall(C#1, u#1)
             && t#0 == _module.__default.EvalExpr($LS($LZ), C#1, u#1)
           ==> (!(C#1 == Lit(#_module.Context.Hole()) && t#0 == u#1)
               ==>
              _module.Term.Apply_q(t#0)
               ==> (forall D#4: DatatypeType ::
                { _module.__default.EvalExpr($LS($LZ), D#4, u#1) }
                  { #_module.Context.C_term(D#4, _module.Term.cdr(t#0)) }
                $Is(D#4, Tclass._module.Context())
                   ==>
                  C#1 == #_module.Context.C_term(D#4, _module.Term.cdr(t#0))
                   ==> _module.__default.EvalExpr#canCall(D#4, u#1)))
             && ((_module.Term.Apply_q(t#0)
                   ==> (forall D#4: DatatypeType ::
                    { _module.__default.EvalExpr($LS($LZ), D#4, u#1) }
                      { #_module.Context.C_term(D#4, _module.Term.cdr(t#0)) }
                    $Is(D#4, Tclass._module.Context())
                       ==>
                      C#1 == #_module.Context.C_term(D#4, _module.Term.cdr(t#0))
                       ==> _module.__default.EvalExpr#canCall(D#4, u#1)))
                 && !
                (_module.Term.Apply_q(t#0)
                 && (exists D#4: DatatypeType ::
                  {:_induction D#4} { _module.__default.EvalExpr($LS($LZ), D#4, u#1) }
                    { #_module.Context.C_term(D#4, _module.Term.cdr(t#0)) }
                  $Is(D#4, Tclass._module.Context())
                     &&
                    C#1 == #_module.Context.C_term(D#4, _module.Term.cdr(t#0))
                     && _module.Term.car(t#0) == _module.__default.EvalExpr($LS($LZ), D#4, u#1)))
               ==> (_module.Term.Apply_q(t#0)
                   ==> _module.__default.IsValue#canCall(_module.Term.car(t#0)))
                 && (_module.__default.IsValue#canCall(_module.Term.car(t#0))
                     && _module.__default.IsValue($LS($LZ), _module.Term.car(t#0))
                   ==> (forall D#5: DatatypeType ::
                    { _module.__default.EvalExpr($LS($LZ), D#5, u#1) }
                      { #_module.Context.value_C(_module.Term.car(t#0), D#5) }
                    $Is(D#5, Tclass._module.Context())
                       ==>
                      C#1 == #_module.Context.value_C(_module.Term.car(t#0), D#5)
                       ==> _module.__default.EvalExpr#canCall(D#5, u#1))))));
  free ensures (forall C#1: DatatypeType, u#1: DatatypeType ::
    {:_induction C#1, u#1} { _module.__default.EvalExpr($LS($LZ), C#1, u#1) }
    $Is(C#1, Tclass._module.Context()) && $Is(u#1, Tclass._module.Term())
       ==>
      _module.__default.IsContext($LS($LZ), C#1)
         && t#0 == _module.__default.EvalExpr($LS($LZ), C#1, u#1)
       ==> (C#1 == Lit(#_module.Context.Hole()) && t#0 == u#1)
         || (_module.Term.Apply_q(t#0)
           && (exists D#4: DatatypeType ::
            {:_induction D#4} { _module.__default.EvalExpr($LS($LZ), D#4, u#1) }
              { #_module.Context.C_term(D#4, _module.Term.cdr(t#0)) }
            $Is(D#4, Tclass._module.Context())
               &&
              C#1 == #_module.Context.C_term(D#4, _module.Term.cdr(t#0))
               && _module.Term.car(t#0) == _module.__default.EvalExpr($LS($LZ), D#4, u#1)))
         || (
          _module.Term.Apply_q(t#0)
           && _module.__default.IsValue($LS($LZ), _module.Term.car(t#0))
           && (exists D#5: DatatypeType ::
            {:_induction D#5} { _module.__default.EvalExpr($LS($LZ), D#5, u#1) }
              { #_module.Context.value_C(_module.Term.car(t#0), D#5) }
            $Is(D#5, Tclass._module.Context())
               &&
              C#1 == #_module.Context.value_C(_module.Term.car(t#0), D#5)
               && _module.Term.cdr(t#0) == _module.__default.EvalExpr($LS($LZ), D#5, u#1))));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.Lemma__ContextPossibilities(t#0: DatatypeType
       where $Is(t#0, Tclass._module.Term())
         && $IsAlloc(t#0, Tclass._module.Term(), $Heap)
         && $IsA#_module.Term(t#0))
   returns ($_reverifyPost: bool);
  free requires 12 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall C#1: DatatypeType, u#1: DatatypeType ::
    { _module.__default.EvalExpr($LS($LZ), C#1, u#1) }
    $Is(C#1, Tclass._module.Context()) && $Is(u#1, Tclass._module.Term())
       ==> _module.__default.IsContext#canCall(C#1)
         && (_module.__default.IsContext($LS($LZ), C#1)
           ==> _module.__default.EvalExpr#canCall(C#1, u#1))
         && (_module.__default.EvalExpr#canCall(C#1, u#1)
             && t#0 == _module.__default.EvalExpr($LS($LZ), C#1, u#1)
           ==> (!(C#1 == Lit(#_module.Context.Hole()) && t#0 == u#1)
               ==>
              _module.Term.Apply_q(t#0)
               ==> (forall D#4: DatatypeType ::
                { _module.__default.EvalExpr($LS($LZ), D#4, u#1) }
                  { #_module.Context.C_term(D#4, _module.Term.cdr(t#0)) }
                $Is(D#4, Tclass._module.Context())
                   ==>
                  C#1 == #_module.Context.C_term(D#4, _module.Term.cdr(t#0))
                   ==> _module.__default.EvalExpr#canCall(D#4, u#1)))
             && ((_module.Term.Apply_q(t#0)
                   ==> (forall D#4: DatatypeType ::
                    { _module.__default.EvalExpr($LS($LZ), D#4, u#1) }
                      { #_module.Context.C_term(D#4, _module.Term.cdr(t#0)) }
                    $Is(D#4, Tclass._module.Context())
                       ==>
                      C#1 == #_module.Context.C_term(D#4, _module.Term.cdr(t#0))
                       ==> _module.__default.EvalExpr#canCall(D#4, u#1)))
                 && !
                (_module.Term.Apply_q(t#0)
                 && (exists D#4: DatatypeType ::
                  {:_induction D#4} { _module.__default.EvalExpr($LS($LZ), D#4, u#1) }
                    { #_module.Context.C_term(D#4, _module.Term.cdr(t#0)) }
                  $Is(D#4, Tclass._module.Context())
                     &&
                    C#1 == #_module.Context.C_term(D#4, _module.Term.cdr(t#0))
                     && _module.Term.car(t#0) == _module.__default.EvalExpr($LS($LZ), D#4, u#1)))
               ==> (_module.Term.Apply_q(t#0)
                   ==> _module.__default.IsValue#canCall(_module.Term.car(t#0)))
                 && (_module.__default.IsValue#canCall(_module.Term.car(t#0))
                     && _module.__default.IsValue($LS($LZ), _module.Term.car(t#0))
                   ==> (forall D#5: DatatypeType ::
                    { _module.__default.EvalExpr($LS($LZ), D#5, u#1) }
                      { #_module.Context.value_C(_module.Term.car(t#0), D#5) }
                    $Is(D#5, Tclass._module.Context())
                       ==>
                      C#1 == #_module.Context.value_C(_module.Term.car(t#0), D#5)
                       ==> _module.__default.EvalExpr#canCall(D#5, u#1))))));
  ensures (forall C#1: DatatypeType, u#1: DatatypeType ::
    { _module.__default.EvalExpr($LS($LS($LZ)), C#1, u#1) }
    $Is(C#1, Tclass._module.Context())
         && $Is(u#1, Tclass._module.Term())
         && (forall C$ih#1#0: DatatypeType, u$ih#1#0: DatatypeType ::
          { _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0) }
          $Is(C$ih#1#0, Tclass._module.Context()) && $Is(u$ih#1#0, Tclass._module.Term())
             ==>
            DtRank(C$ih#1#0) < DtRank(C#1)
               || (DtRank(C$ih#1#0) == DtRank(C#1) && DtRank(u$ih#1#0) < DtRank(u#1))
             ==>
            _module.__default.IsContext($LS($LZ), C$ih#1#0)
               && t#0 == _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0)
             ==> (C$ih#1#0 == Lit(#_module.Context.Hole()) && t#0 == u$ih#1#0)
               || (_module.Term.Apply_q(t#0)
                 && (exists D#8: DatatypeType ::
                  {:_induction D#8} { _module.__default.EvalExpr($LS($LZ), D#8, u$ih#1#0) }
                    { #_module.Context.C_term(D#8, _module.Term.cdr(t#0)) }
                  $Is(D#8, Tclass._module.Context())
                     &&
                    C$ih#1#0 == #_module.Context.C_term(D#8, _module.Term.cdr(t#0))
                     && _module.Term.car(t#0) == _module.__default.EvalExpr($LS($LZ), D#8, u$ih#1#0)))
               || (
                _module.Term.Apply_q(t#0)
                 && _module.__default.IsValue($LS($LZ), _module.Term.car(t#0))
                 && (exists D#9: DatatypeType ::
                  {:_induction D#9} { _module.__default.EvalExpr($LS($LZ), D#9, u$ih#1#0) }
                    { #_module.Context.value_C(_module.Term.car(t#0), D#9) }
                  $Is(D#9, Tclass._module.Context())
                     &&
                    C$ih#1#0 == #_module.Context.value_C(_module.Term.car(t#0), D#9)
                     && _module.Term.cdr(t#0) == _module.__default.EvalExpr($LS($LZ), D#9, u$ih#1#0))))
         &&
        true
         && #_module.Context.Hole() == C#1
         && #_module.Term.S() == u#1
       ==>
      _module.__default.IsContext($LS($LS($LZ)), C#1)
         && t#0 == _module.__default.EvalExpr($LS($LS($LZ)), C#1, u#1)
       ==> (C#1 == Lit(#_module.Context.Hole()) && t#0 == u#1)
         || (_module.Term.Apply_q(t#0)
           && (exists D#4: DatatypeType ::
            {:_induction D#4} { _module.__default.EvalExpr($LS($LS($LZ)), D#4, u#1) }
              { #_module.Context.C_term(D#4, _module.Term.cdr(t#0)) }
            $Is(D#4, Tclass._module.Context())
               &&
              C#1 == #_module.Context.C_term(D#4, _module.Term.cdr(t#0))
               && _module.Term.car(t#0) == _module.__default.EvalExpr($LS($LS($LZ)), D#4, u#1)))
         || (
          _module.Term.Apply_q(t#0)
           && _module.__default.IsValue($LS($LS($LZ)), _module.Term.car(t#0))
           && (exists D#5: DatatypeType ::
            {:_induction D#5} { _module.__default.EvalExpr($LS($LS($LZ)), D#5, u#1) }
              { #_module.Context.value_C(_module.Term.car(t#0), D#5) }
            $Is(D#5, Tclass._module.Context())
               &&
              C#1 == #_module.Context.value_C(_module.Term.car(t#0), D#5)
               && _module.Term.cdr(t#0) == _module.__default.EvalExpr($LS($LS($LZ)), D#5, u#1))));
  ensures (forall C#1: DatatypeType, u#1: DatatypeType ::
    { _module.__default.EvalExpr($LS($LS($LZ)), C#1, u#1) }
    $Is(C#1, Tclass._module.Context())
         && $Is(u#1, Tclass._module.Term())
         && (forall C$ih#1#0: DatatypeType, u$ih#1#0: DatatypeType ::
          { _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0) }
          $Is(C$ih#1#0, Tclass._module.Context()) && $Is(u$ih#1#0, Tclass._module.Term())
             ==>
            DtRank(C$ih#1#0) < DtRank(C#1)
               || (DtRank(C$ih#1#0) == DtRank(C#1) && DtRank(u$ih#1#0) < DtRank(u#1))
             ==>
            _module.__default.IsContext($LS($LZ), C$ih#1#0)
               && t#0 == _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0)
             ==> (C$ih#1#0 == Lit(#_module.Context.Hole()) && t#0 == u$ih#1#0)
               || (_module.Term.Apply_q(t#0)
                 && (exists D#8: DatatypeType ::
                  {:_induction D#8} { _module.__default.EvalExpr($LS($LZ), D#8, u$ih#1#0) }
                    { #_module.Context.C_term(D#8, _module.Term.cdr(t#0)) }
                  $Is(D#8, Tclass._module.Context())
                     &&
                    C$ih#1#0 == #_module.Context.C_term(D#8, _module.Term.cdr(t#0))
                     && _module.Term.car(t#0) == _module.__default.EvalExpr($LS($LZ), D#8, u$ih#1#0)))
               || (
                _module.Term.Apply_q(t#0)
                 && _module.__default.IsValue($LS($LZ), _module.Term.car(t#0))
                 && (exists D#9: DatatypeType ::
                  {:_induction D#9} { _module.__default.EvalExpr($LS($LZ), D#9, u$ih#1#0) }
                    { #_module.Context.value_C(_module.Term.car(t#0), D#9) }
                  $Is(D#9, Tclass._module.Context())
                     &&
                    C$ih#1#0 == #_module.Context.value_C(_module.Term.car(t#0), D#9)
                     && _module.Term.cdr(t#0) == _module.__default.EvalExpr($LS($LZ), D#9, u$ih#1#0))))
         &&
        true
         && (exists a#7#0#0: DatatypeType, a#7#1#0: DatatypeType ::
          { #_module.Context.C_term(a#7#0#0, a#7#1#0) }
          $Is(a#7#0#0, Tclass._module.Context())
             && $Is(a#7#1#0, Tclass._module.Term())
             && #_module.Context.C_term(a#7#0#0, a#7#1#0) == C#1)
         && #_module.Term.S() == u#1
       ==>
      _module.__default.IsContext($LS($LS($LZ)), C#1)
         && t#0 == _module.__default.EvalExpr($LS($LS($LZ)), C#1, u#1)
       ==> (C#1 == Lit(#_module.Context.Hole()) && t#0 == u#1)
         || (_module.Term.Apply_q(t#0)
           && (exists D#4: DatatypeType ::
            {:_induction D#4} { _module.__default.EvalExpr($LS($LS($LZ)), D#4, u#1) }
              { #_module.Context.C_term(D#4, _module.Term.cdr(t#0)) }
            $Is(D#4, Tclass._module.Context())
               &&
              C#1 == #_module.Context.C_term(D#4, _module.Term.cdr(t#0))
               && _module.Term.car(t#0) == _module.__default.EvalExpr($LS($LS($LZ)), D#4, u#1)))
         || (
          _module.Term.Apply_q(t#0)
           && _module.__default.IsValue($LS($LS($LZ)), _module.Term.car(t#0))
           && (exists D#5: DatatypeType ::
            {:_induction D#5} { _module.__default.EvalExpr($LS($LS($LZ)), D#5, u#1) }
              { #_module.Context.value_C(_module.Term.car(t#0), D#5) }
            $Is(D#5, Tclass._module.Context())
               &&
              C#1 == #_module.Context.value_C(_module.Term.car(t#0), D#5)
               && _module.Term.cdr(t#0) == _module.__default.EvalExpr($LS($LS($LZ)), D#5, u#1))));
  ensures (forall C#1: DatatypeType, u#1: DatatypeType ::
    { _module.__default.EvalExpr($LS($LS($LZ)), C#1, u#1) }
    $Is(C#1, Tclass._module.Context())
         && $Is(u#1, Tclass._module.Term())
         && (forall C$ih#1#0: DatatypeType, u$ih#1#0: DatatypeType ::
          { _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0) }
          $Is(C$ih#1#0, Tclass._module.Context()) && $Is(u$ih#1#0, Tclass._module.Term())
             ==>
            DtRank(C$ih#1#0) < DtRank(C#1)
               || (DtRank(C$ih#1#0) == DtRank(C#1) && DtRank(u$ih#1#0) < DtRank(u#1))
             ==>
            _module.__default.IsContext($LS($LZ), C$ih#1#0)
               && t#0 == _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0)
             ==> (C$ih#1#0 == Lit(#_module.Context.Hole()) && t#0 == u$ih#1#0)
               || (_module.Term.Apply_q(t#0)
                 && (exists D#8: DatatypeType ::
                  {:_induction D#8} { _module.__default.EvalExpr($LS($LZ), D#8, u$ih#1#0) }
                    { #_module.Context.C_term(D#8, _module.Term.cdr(t#0)) }
                  $Is(D#8, Tclass._module.Context())
                     &&
                    C$ih#1#0 == #_module.Context.C_term(D#8, _module.Term.cdr(t#0))
                     && _module.Term.car(t#0) == _module.__default.EvalExpr($LS($LZ), D#8, u$ih#1#0)))
               || (
                _module.Term.Apply_q(t#0)
                 && _module.__default.IsValue($LS($LZ), _module.Term.car(t#0))
                 && (exists D#9: DatatypeType ::
                  {:_induction D#9} { _module.__default.EvalExpr($LS($LZ), D#9, u$ih#1#0) }
                    { #_module.Context.value_C(_module.Term.car(t#0), D#9) }
                  $Is(D#9, Tclass._module.Context())
                     &&
                    C$ih#1#0 == #_module.Context.value_C(_module.Term.car(t#0), D#9)
                     && _module.Term.cdr(t#0) == _module.__default.EvalExpr($LS($LZ), D#9, u$ih#1#0))))
         &&
        true
         && (exists a#8#0#0: DatatypeType, a#8#1#0: DatatypeType ::
          { #_module.Context.value_C(a#8#0#0, a#8#1#0) }
          $Is(a#8#0#0, Tclass._module.Term())
             && $Is(a#8#1#0, Tclass._module.Context())
             && #_module.Context.value_C(a#8#0#0, a#8#1#0) == C#1)
         && #_module.Term.S() == u#1
       ==>
      _module.__default.IsContext($LS($LS($LZ)), C#1)
         && t#0 == _module.__default.EvalExpr($LS($LS($LZ)), C#1, u#1)
       ==> (C#1 == Lit(#_module.Context.Hole()) && t#0 == u#1)
         || (_module.Term.Apply_q(t#0)
           && (exists D#4: DatatypeType ::
            {:_induction D#4} { _module.__default.EvalExpr($LS($LS($LZ)), D#4, u#1) }
              { #_module.Context.C_term(D#4, _module.Term.cdr(t#0)) }
            $Is(D#4, Tclass._module.Context())
               &&
              C#1 == #_module.Context.C_term(D#4, _module.Term.cdr(t#0))
               && _module.Term.car(t#0) == _module.__default.EvalExpr($LS($LS($LZ)), D#4, u#1)))
         || (
          _module.Term.Apply_q(t#0)
           && _module.__default.IsValue($LS($LS($LZ)), _module.Term.car(t#0))
           && (exists D#5: DatatypeType ::
            {:_induction D#5} { _module.__default.EvalExpr($LS($LS($LZ)), D#5, u#1) }
              { #_module.Context.value_C(_module.Term.car(t#0), D#5) }
            $Is(D#5, Tclass._module.Context())
               &&
              C#1 == #_module.Context.value_C(_module.Term.car(t#0), D#5)
               && _module.Term.cdr(t#0) == _module.__default.EvalExpr($LS($LS($LZ)), D#5, u#1))));
  ensures (forall C#1: DatatypeType, u#1: DatatypeType ::
    { _module.__default.EvalExpr($LS($LS($LZ)), C#1, u#1) }
    $Is(C#1, Tclass._module.Context())
         && $Is(u#1, Tclass._module.Term())
         && (forall C$ih#1#0: DatatypeType, u$ih#1#0: DatatypeType ::
          { _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0) }
          $Is(C$ih#1#0, Tclass._module.Context()) && $Is(u$ih#1#0, Tclass._module.Term())
             ==>
            DtRank(C$ih#1#0) < DtRank(C#1)
               || (DtRank(C$ih#1#0) == DtRank(C#1) && DtRank(u$ih#1#0) < DtRank(u#1))
             ==>
            _module.__default.IsContext($LS($LZ), C$ih#1#0)
               && t#0 == _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0)
             ==> (C$ih#1#0 == Lit(#_module.Context.Hole()) && t#0 == u$ih#1#0)
               || (_module.Term.Apply_q(t#0)
                 && (exists D#8: DatatypeType ::
                  {:_induction D#8} { _module.__default.EvalExpr($LS($LZ), D#8, u$ih#1#0) }
                    { #_module.Context.C_term(D#8, _module.Term.cdr(t#0)) }
                  $Is(D#8, Tclass._module.Context())
                     &&
                    C$ih#1#0 == #_module.Context.C_term(D#8, _module.Term.cdr(t#0))
                     && _module.Term.car(t#0) == _module.__default.EvalExpr($LS($LZ), D#8, u$ih#1#0)))
               || (
                _module.Term.Apply_q(t#0)
                 && _module.__default.IsValue($LS($LZ), _module.Term.car(t#0))
                 && (exists D#9: DatatypeType ::
                  {:_induction D#9} { _module.__default.EvalExpr($LS($LZ), D#9, u$ih#1#0) }
                    { #_module.Context.value_C(_module.Term.car(t#0), D#9) }
                  $Is(D#9, Tclass._module.Context())
                     &&
                    C$ih#1#0 == #_module.Context.value_C(_module.Term.car(t#0), D#9)
                     && _module.Term.cdr(t#0) == _module.__default.EvalExpr($LS($LZ), D#9, u$ih#1#0))))
         &&
        true
         && #_module.Context.Hole() == C#1
         && #_module.Term.K() == u#1
       ==>
      _module.__default.IsContext($LS($LS($LZ)), C#1)
         && t#0 == _module.__default.EvalExpr($LS($LS($LZ)), C#1, u#1)
       ==> (C#1 == Lit(#_module.Context.Hole()) && t#0 == u#1)
         || (_module.Term.Apply_q(t#0)
           && (exists D#4: DatatypeType ::
            {:_induction D#4} { _module.__default.EvalExpr($LS($LS($LZ)), D#4, u#1) }
              { #_module.Context.C_term(D#4, _module.Term.cdr(t#0)) }
            $Is(D#4, Tclass._module.Context())
               &&
              C#1 == #_module.Context.C_term(D#4, _module.Term.cdr(t#0))
               && _module.Term.car(t#0) == _module.__default.EvalExpr($LS($LS($LZ)), D#4, u#1)))
         || (
          _module.Term.Apply_q(t#0)
           && _module.__default.IsValue($LS($LS($LZ)), _module.Term.car(t#0))
           && (exists D#5: DatatypeType ::
            {:_induction D#5} { _module.__default.EvalExpr($LS($LS($LZ)), D#5, u#1) }
              { #_module.Context.value_C(_module.Term.car(t#0), D#5) }
            $Is(D#5, Tclass._module.Context())
               &&
              C#1 == #_module.Context.value_C(_module.Term.car(t#0), D#5)
               && _module.Term.cdr(t#0) == _module.__default.EvalExpr($LS($LS($LZ)), D#5, u#1))));
  ensures (forall C#1: DatatypeType, u#1: DatatypeType ::
    { _module.__default.EvalExpr($LS($LS($LZ)), C#1, u#1) }
    $Is(C#1, Tclass._module.Context())
         && $Is(u#1, Tclass._module.Term())
         && (forall C$ih#1#0: DatatypeType, u$ih#1#0: DatatypeType ::
          { _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0) }
          $Is(C$ih#1#0, Tclass._module.Context()) && $Is(u$ih#1#0, Tclass._module.Term())
             ==>
            DtRank(C$ih#1#0) < DtRank(C#1)
               || (DtRank(C$ih#1#0) == DtRank(C#1) && DtRank(u$ih#1#0) < DtRank(u#1))
             ==>
            _module.__default.IsContext($LS($LZ), C$ih#1#0)
               && t#0 == _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0)
             ==> (C$ih#1#0 == Lit(#_module.Context.Hole()) && t#0 == u$ih#1#0)
               || (_module.Term.Apply_q(t#0)
                 && (exists D#8: DatatypeType ::
                  {:_induction D#8} { _module.__default.EvalExpr($LS($LZ), D#8, u$ih#1#0) }
                    { #_module.Context.C_term(D#8, _module.Term.cdr(t#0)) }
                  $Is(D#8, Tclass._module.Context())
                     &&
                    C$ih#1#0 == #_module.Context.C_term(D#8, _module.Term.cdr(t#0))
                     && _module.Term.car(t#0) == _module.__default.EvalExpr($LS($LZ), D#8, u$ih#1#0)))
               || (
                _module.Term.Apply_q(t#0)
                 && _module.__default.IsValue($LS($LZ), _module.Term.car(t#0))
                 && (exists D#9: DatatypeType ::
                  {:_induction D#9} { _module.__default.EvalExpr($LS($LZ), D#9, u$ih#1#0) }
                    { #_module.Context.value_C(_module.Term.car(t#0), D#9) }
                  $Is(D#9, Tclass._module.Context())
                     &&
                    C$ih#1#0 == #_module.Context.value_C(_module.Term.car(t#0), D#9)
                     && _module.Term.cdr(t#0) == _module.__default.EvalExpr($LS($LZ), D#9, u$ih#1#0))))
         &&
        true
         && (exists a#7#0#0: DatatypeType, a#7#1#0: DatatypeType ::
          { #_module.Context.C_term(a#7#0#0, a#7#1#0) }
          $Is(a#7#0#0, Tclass._module.Context())
             && $Is(a#7#1#0, Tclass._module.Term())
             && #_module.Context.C_term(a#7#0#0, a#7#1#0) == C#1)
         && #_module.Term.K() == u#1
       ==>
      _module.__default.IsContext($LS($LS($LZ)), C#1)
         && t#0 == _module.__default.EvalExpr($LS($LS($LZ)), C#1, u#1)
       ==> (C#1 == Lit(#_module.Context.Hole()) && t#0 == u#1)
         || (_module.Term.Apply_q(t#0)
           && (exists D#4: DatatypeType ::
            {:_induction D#4} { _module.__default.EvalExpr($LS($LS($LZ)), D#4, u#1) }
              { #_module.Context.C_term(D#4, _module.Term.cdr(t#0)) }
            $Is(D#4, Tclass._module.Context())
               &&
              C#1 == #_module.Context.C_term(D#4, _module.Term.cdr(t#0))
               && _module.Term.car(t#0) == _module.__default.EvalExpr($LS($LS($LZ)), D#4, u#1)))
         || (
          _module.Term.Apply_q(t#0)
           && _module.__default.IsValue($LS($LS($LZ)), _module.Term.car(t#0))
           && (exists D#5: DatatypeType ::
            {:_induction D#5} { _module.__default.EvalExpr($LS($LS($LZ)), D#5, u#1) }
              { #_module.Context.value_C(_module.Term.car(t#0), D#5) }
            $Is(D#5, Tclass._module.Context())
               &&
              C#1 == #_module.Context.value_C(_module.Term.car(t#0), D#5)
               && _module.Term.cdr(t#0) == _module.__default.EvalExpr($LS($LS($LZ)), D#5, u#1))));
  ensures (forall C#1: DatatypeType, u#1: DatatypeType ::
    { _module.__default.EvalExpr($LS($LS($LZ)), C#1, u#1) }
    $Is(C#1, Tclass._module.Context())
         && $Is(u#1, Tclass._module.Term())
         && (forall C$ih#1#0: DatatypeType, u$ih#1#0: DatatypeType ::
          { _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0) }
          $Is(C$ih#1#0, Tclass._module.Context()) && $Is(u$ih#1#0, Tclass._module.Term())
             ==>
            DtRank(C$ih#1#0) < DtRank(C#1)
               || (DtRank(C$ih#1#0) == DtRank(C#1) && DtRank(u$ih#1#0) < DtRank(u#1))
             ==>
            _module.__default.IsContext($LS($LZ), C$ih#1#0)
               && t#0 == _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0)
             ==> (C$ih#1#0 == Lit(#_module.Context.Hole()) && t#0 == u$ih#1#0)
               || (_module.Term.Apply_q(t#0)
                 && (exists D#8: DatatypeType ::
                  {:_induction D#8} { _module.__default.EvalExpr($LS($LZ), D#8, u$ih#1#0) }
                    { #_module.Context.C_term(D#8, _module.Term.cdr(t#0)) }
                  $Is(D#8, Tclass._module.Context())
                     &&
                    C$ih#1#0 == #_module.Context.C_term(D#8, _module.Term.cdr(t#0))
                     && _module.Term.car(t#0) == _module.__default.EvalExpr($LS($LZ), D#8, u$ih#1#0)))
               || (
                _module.Term.Apply_q(t#0)
                 && _module.__default.IsValue($LS($LZ), _module.Term.car(t#0))
                 && (exists D#9: DatatypeType ::
                  {:_induction D#9} { _module.__default.EvalExpr($LS($LZ), D#9, u$ih#1#0) }
                    { #_module.Context.value_C(_module.Term.car(t#0), D#9) }
                  $Is(D#9, Tclass._module.Context())
                     &&
                    C$ih#1#0 == #_module.Context.value_C(_module.Term.car(t#0), D#9)
                     && _module.Term.cdr(t#0) == _module.__default.EvalExpr($LS($LZ), D#9, u$ih#1#0))))
         &&
        true
         && (exists a#8#0#0: DatatypeType, a#8#1#0: DatatypeType ::
          { #_module.Context.value_C(a#8#0#0, a#8#1#0) }
          $Is(a#8#0#0, Tclass._module.Term())
             && $Is(a#8#1#0, Tclass._module.Context())
             && #_module.Context.value_C(a#8#0#0, a#8#1#0) == C#1)
         && #_module.Term.K() == u#1
       ==>
      _module.__default.IsContext($LS($LS($LZ)), C#1)
         && t#0 == _module.__default.EvalExpr($LS($LS($LZ)), C#1, u#1)
       ==> (C#1 == Lit(#_module.Context.Hole()) && t#0 == u#1)
         || (_module.Term.Apply_q(t#0)
           && (exists D#4: DatatypeType ::
            {:_induction D#4} { _module.__default.EvalExpr($LS($LS($LZ)), D#4, u#1) }
              { #_module.Context.C_term(D#4, _module.Term.cdr(t#0)) }
            $Is(D#4, Tclass._module.Context())
               &&
              C#1 == #_module.Context.C_term(D#4, _module.Term.cdr(t#0))
               && _module.Term.car(t#0) == _module.__default.EvalExpr($LS($LS($LZ)), D#4, u#1)))
         || (
          _module.Term.Apply_q(t#0)
           && _module.__default.IsValue($LS($LS($LZ)), _module.Term.car(t#0))
           && (exists D#5: DatatypeType ::
            {:_induction D#5} { _module.__default.EvalExpr($LS($LS($LZ)), D#5, u#1) }
              { #_module.Context.value_C(_module.Term.car(t#0), D#5) }
            $Is(D#5, Tclass._module.Context())
               &&
              C#1 == #_module.Context.value_C(_module.Term.car(t#0), D#5)
               && _module.Term.cdr(t#0) == _module.__default.EvalExpr($LS($LS($LZ)), D#5, u#1))));
  ensures (forall C#1: DatatypeType, u#1: DatatypeType ::
    { _module.__default.EvalExpr($LS($LS($LZ)), C#1, u#1) }
    $Is(C#1, Tclass._module.Context())
         && $Is(u#1, Tclass._module.Term())
         && (forall C$ih#1#0: DatatypeType, u$ih#1#0: DatatypeType ::
          { _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0) }
          $Is(C$ih#1#0, Tclass._module.Context()) && $Is(u$ih#1#0, Tclass._module.Term())
             ==>
            DtRank(C$ih#1#0) < DtRank(C#1)
               || (DtRank(C$ih#1#0) == DtRank(C#1) && DtRank(u$ih#1#0) < DtRank(u#1))
             ==>
            _module.__default.IsContext($LS($LZ), C$ih#1#0)
               && t#0 == _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0)
             ==> (C$ih#1#0 == Lit(#_module.Context.Hole()) && t#0 == u$ih#1#0)
               || (_module.Term.Apply_q(t#0)
                 && (exists D#8: DatatypeType ::
                  {:_induction D#8} { _module.__default.EvalExpr($LS($LZ), D#8, u$ih#1#0) }
                    { #_module.Context.C_term(D#8, _module.Term.cdr(t#0)) }
                  $Is(D#8, Tclass._module.Context())
                     &&
                    C$ih#1#0 == #_module.Context.C_term(D#8, _module.Term.cdr(t#0))
                     && _module.Term.car(t#0) == _module.__default.EvalExpr($LS($LZ), D#8, u$ih#1#0)))
               || (
                _module.Term.Apply_q(t#0)
                 && _module.__default.IsValue($LS($LZ), _module.Term.car(t#0))
                 && (exists D#9: DatatypeType ::
                  {:_induction D#9} { _module.__default.EvalExpr($LS($LZ), D#9, u$ih#1#0) }
                    { #_module.Context.value_C(_module.Term.car(t#0), D#9) }
                  $Is(D#9, Tclass._module.Context())
                     &&
                    C$ih#1#0 == #_module.Context.value_C(_module.Term.car(t#0), D#9)
                     && _module.Term.cdr(t#0) == _module.__default.EvalExpr($LS($LZ), D#9, u$ih#1#0))))
         &&
        true
         && #_module.Context.Hole() == C#1
         && (exists a#11#0#0: DatatypeType, a#11#1#0: DatatypeType ::
          { #_module.Term.Apply(a#11#0#0, a#11#1#0) }
          $Is(a#11#0#0, Tclass._module.Term())
             && $Is(a#11#1#0, Tclass._module.Term())
             && #_module.Term.Apply(a#11#0#0, a#11#1#0) == u#1)
       ==>
      _module.__default.IsContext($LS($LS($LZ)), C#1)
         && t#0 == _module.__default.EvalExpr($LS($LS($LZ)), C#1, u#1)
       ==> (C#1 == Lit(#_module.Context.Hole()) && t#0 == u#1)
         || (_module.Term.Apply_q(t#0)
           && (exists D#4: DatatypeType ::
            {:_induction D#4} { _module.__default.EvalExpr($LS($LS($LZ)), D#4, u#1) }
              { #_module.Context.C_term(D#4, _module.Term.cdr(t#0)) }
            $Is(D#4, Tclass._module.Context())
               &&
              C#1 == #_module.Context.C_term(D#4, _module.Term.cdr(t#0))
               && _module.Term.car(t#0) == _module.__default.EvalExpr($LS($LS($LZ)), D#4, u#1)))
         || (
          _module.Term.Apply_q(t#0)
           && _module.__default.IsValue($LS($LS($LZ)), _module.Term.car(t#0))
           && (exists D#5: DatatypeType ::
            {:_induction D#5} { _module.__default.EvalExpr($LS($LS($LZ)), D#5, u#1) }
              { #_module.Context.value_C(_module.Term.car(t#0), D#5) }
            $Is(D#5, Tclass._module.Context())
               &&
              C#1 == #_module.Context.value_C(_module.Term.car(t#0), D#5)
               && _module.Term.cdr(t#0) == _module.__default.EvalExpr($LS($LS($LZ)), D#5, u#1))));
  ensures (forall C#1: DatatypeType, u#1: DatatypeType ::
    { _module.__default.EvalExpr($LS($LS($LZ)), C#1, u#1) }
    $Is(C#1, Tclass._module.Context())
         && $Is(u#1, Tclass._module.Term())
         && (forall C$ih#1#0: DatatypeType, u$ih#1#0: DatatypeType ::
          { _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0) }
          $Is(C$ih#1#0, Tclass._module.Context()) && $Is(u$ih#1#0, Tclass._module.Term())
             ==>
            DtRank(C$ih#1#0) < DtRank(C#1)
               || (DtRank(C$ih#1#0) == DtRank(C#1) && DtRank(u$ih#1#0) < DtRank(u#1))
             ==>
            _module.__default.IsContext($LS($LZ), C$ih#1#0)
               && t#0 == _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0)
             ==> (C$ih#1#0 == Lit(#_module.Context.Hole()) && t#0 == u$ih#1#0)
               || (_module.Term.Apply_q(t#0)
                 && (exists D#8: DatatypeType ::
                  {:_induction D#8} { _module.__default.EvalExpr($LS($LZ), D#8, u$ih#1#0) }
                    { #_module.Context.C_term(D#8, _module.Term.cdr(t#0)) }
                  $Is(D#8, Tclass._module.Context())
                     &&
                    C$ih#1#0 == #_module.Context.C_term(D#8, _module.Term.cdr(t#0))
                     && _module.Term.car(t#0) == _module.__default.EvalExpr($LS($LZ), D#8, u$ih#1#0)))
               || (
                _module.Term.Apply_q(t#0)
                 && _module.__default.IsValue($LS($LZ), _module.Term.car(t#0))
                 && (exists D#9: DatatypeType ::
                  {:_induction D#9} { _module.__default.EvalExpr($LS($LZ), D#9, u$ih#1#0) }
                    { #_module.Context.value_C(_module.Term.car(t#0), D#9) }
                  $Is(D#9, Tclass._module.Context())
                     &&
                    C$ih#1#0 == #_module.Context.value_C(_module.Term.car(t#0), D#9)
                     && _module.Term.cdr(t#0) == _module.__default.EvalExpr($LS($LZ), D#9, u$ih#1#0))))
         &&
        true
         && (exists a#7#0#0: DatatypeType, a#7#1#0: DatatypeType ::
          { #_module.Context.C_term(a#7#0#0, a#7#1#0) }
          $Is(a#7#0#0, Tclass._module.Context())
             && $Is(a#7#1#0, Tclass._module.Term())
             && #_module.Context.C_term(a#7#0#0, a#7#1#0) == C#1)
         && (exists a#11#0#0: DatatypeType, a#11#1#0: DatatypeType ::
          { #_module.Term.Apply(a#11#0#0, a#11#1#0) }
          $Is(a#11#0#0, Tclass._module.Term())
             && $Is(a#11#1#0, Tclass._module.Term())
             && #_module.Term.Apply(a#11#0#0, a#11#1#0) == u#1)
       ==>
      _module.__default.IsContext($LS($LS($LZ)), C#1)
         && t#0 == _module.__default.EvalExpr($LS($LS($LZ)), C#1, u#1)
       ==> (C#1 == Lit(#_module.Context.Hole()) && t#0 == u#1)
         || (_module.Term.Apply_q(t#0)
           && (exists D#4: DatatypeType ::
            {:_induction D#4} { _module.__default.EvalExpr($LS($LS($LZ)), D#4, u#1) }
              { #_module.Context.C_term(D#4, _module.Term.cdr(t#0)) }
            $Is(D#4, Tclass._module.Context())
               &&
              C#1 == #_module.Context.C_term(D#4, _module.Term.cdr(t#0))
               && _module.Term.car(t#0) == _module.__default.EvalExpr($LS($LS($LZ)), D#4, u#1)))
         || (
          _module.Term.Apply_q(t#0)
           && _module.__default.IsValue($LS($LS($LZ)), _module.Term.car(t#0))
           && (exists D#5: DatatypeType ::
            {:_induction D#5} { _module.__default.EvalExpr($LS($LS($LZ)), D#5, u#1) }
              { #_module.Context.value_C(_module.Term.car(t#0), D#5) }
            $Is(D#5, Tclass._module.Context())
               &&
              C#1 == #_module.Context.value_C(_module.Term.car(t#0), D#5)
               && _module.Term.cdr(t#0) == _module.__default.EvalExpr($LS($LS($LZ)), D#5, u#1))));
  ensures (forall C#1: DatatypeType, u#1: DatatypeType ::
    { _module.__default.EvalExpr($LS($LS($LZ)), C#1, u#1) }
    $Is(C#1, Tclass._module.Context())
         && $Is(u#1, Tclass._module.Term())
         && (forall C$ih#1#0: DatatypeType, u$ih#1#0: DatatypeType ::
          { _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0) }
          $Is(C$ih#1#0, Tclass._module.Context()) && $Is(u$ih#1#0, Tclass._module.Term())
             ==>
            DtRank(C$ih#1#0) < DtRank(C#1)
               || (DtRank(C$ih#1#0) == DtRank(C#1) && DtRank(u$ih#1#0) < DtRank(u#1))
             ==>
            _module.__default.IsContext($LS($LZ), C$ih#1#0)
               && t#0 == _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0)
             ==> (C$ih#1#0 == Lit(#_module.Context.Hole()) && t#0 == u$ih#1#0)
               || (_module.Term.Apply_q(t#0)
                 && (exists D#8: DatatypeType ::
                  {:_induction D#8} { _module.__default.EvalExpr($LS($LZ), D#8, u$ih#1#0) }
                    { #_module.Context.C_term(D#8, _module.Term.cdr(t#0)) }
                  $Is(D#8, Tclass._module.Context())
                     &&
                    C$ih#1#0 == #_module.Context.C_term(D#8, _module.Term.cdr(t#0))
                     && _module.Term.car(t#0) == _module.__default.EvalExpr($LS($LZ), D#8, u$ih#1#0)))
               || (
                _module.Term.Apply_q(t#0)
                 && _module.__default.IsValue($LS($LZ), _module.Term.car(t#0))
                 && (exists D#9: DatatypeType ::
                  {:_induction D#9} { _module.__default.EvalExpr($LS($LZ), D#9, u$ih#1#0) }
                    { #_module.Context.value_C(_module.Term.car(t#0), D#9) }
                  $Is(D#9, Tclass._module.Context())
                     &&
                    C$ih#1#0 == #_module.Context.value_C(_module.Term.car(t#0), D#9)
                     && _module.Term.cdr(t#0) == _module.__default.EvalExpr($LS($LZ), D#9, u$ih#1#0))))
         &&
        true
         && (exists a#8#0#0: DatatypeType, a#8#1#0: DatatypeType ::
          { #_module.Context.value_C(a#8#0#0, a#8#1#0) }
          $Is(a#8#0#0, Tclass._module.Term())
             && $Is(a#8#1#0, Tclass._module.Context())
             && #_module.Context.value_C(a#8#0#0, a#8#1#0) == C#1)
         && (exists a#11#0#0: DatatypeType, a#11#1#0: DatatypeType ::
          { #_module.Term.Apply(a#11#0#0, a#11#1#0) }
          $Is(a#11#0#0, Tclass._module.Term())
             && $Is(a#11#1#0, Tclass._module.Term())
             && #_module.Term.Apply(a#11#0#0, a#11#1#0) == u#1)
       ==>
      _module.__default.IsContext($LS($LS($LZ)), C#1)
         && t#0 == _module.__default.EvalExpr($LS($LS($LZ)), C#1, u#1)
       ==> (C#1 == Lit(#_module.Context.Hole()) && t#0 == u#1)
         || (_module.Term.Apply_q(t#0)
           && (exists D#4: DatatypeType ::
            {:_induction D#4} { _module.__default.EvalExpr($LS($LS($LZ)), D#4, u#1) }
              { #_module.Context.C_term(D#4, _module.Term.cdr(t#0)) }
            $Is(D#4, Tclass._module.Context())
               &&
              C#1 == #_module.Context.C_term(D#4, _module.Term.cdr(t#0))
               && _module.Term.car(t#0) == _module.__default.EvalExpr($LS($LS($LZ)), D#4, u#1)))
         || (
          _module.Term.Apply_q(t#0)
           && _module.__default.IsValue($LS($LS($LZ)), _module.Term.car(t#0))
           && (exists D#5: DatatypeType ::
            {:_induction D#5} { _module.__default.EvalExpr($LS($LS($LZ)), D#5, u#1) }
              { #_module.Context.value_C(_module.Term.car(t#0), D#5) }
            $Is(D#5, Tclass._module.Context())
               &&
              C#1 == #_module.Context.value_C(_module.Term.car(t#0), D#5)
               && _module.Term.cdr(t#0) == _module.__default.EvalExpr($LS($LS($LZ)), D#5, u#1))));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.Lemma__ContextPossibilities(t#0: DatatypeType) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: Lemma_ContextPossibilities, Impl$$_module.__default.Lemma__ContextPossibilities
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "Combinators.dfy(264,0): initial state"} true;
    $_reverifyPost := false;
}



// function declaration for _module._default.IsTrace
function _module.__default.IsTrace($ly: LayerType, trace#0: DatatypeType, t#0: DatatypeType, r#0: DatatypeType)
   : bool;

function _module.__default.IsTrace#canCall(trace#0: DatatypeType, t#0: DatatypeType, r#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, trace#0: DatatypeType, t#0: DatatypeType, r#0: DatatypeType ::
  { _module.__default.IsTrace($LS($ly), trace#0, t#0, r#0) }
  _module.__default.IsTrace($LS($ly), trace#0, t#0, r#0)
     == _module.__default.IsTrace($ly, trace#0, t#0, r#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, trace#0: DatatypeType, t#0: DatatypeType, r#0: DatatypeType ::
  { _module.__default.IsTrace(AsFuelBottom($ly), trace#0, t#0, r#0) }
  _module.__default.IsTrace($ly, trace#0, t#0, r#0)
     == _module.__default.IsTrace($LZ, trace#0, t#0, r#0));

// consequence axiom for _module.__default.IsTrace
axiom 15 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, trace#0: DatatypeType, t#0: DatatypeType, r#0: DatatypeType ::
    { _module.__default.IsTrace($ly, trace#0, t#0, r#0) }
    _module.__default.IsTrace#canCall(trace#0, t#0, r#0)
         || (15 != $FunctionContextHeight
           &&
          $Is(trace#0, Tclass._module.Trace())
           && $Is(t#0, Tclass._module.Term())
           && $Is(r#0, Tclass._module.Term()))
       ==> true);

function _module.__default.IsTrace#requires(LayerType, DatatypeType, DatatypeType, DatatypeType) : bool;

// #requires axiom for _module.__default.IsTrace
axiom (forall $ly: LayerType, trace#0: DatatypeType, t#0: DatatypeType, r#0: DatatypeType ::
  { _module.__default.IsTrace#requires($ly, trace#0, t#0, r#0) }
  $Is(trace#0, Tclass._module.Trace())
       && $Is(t#0, Tclass._module.Term())
       && $Is(r#0, Tclass._module.Term())
     ==> _module.__default.IsTrace#requires($ly, trace#0, t#0, r#0) == true);

// definition axiom for _module.__default.IsTrace(revealed)
axiom 15 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, trace#0: DatatypeType, t#0: DatatypeType, r#0: DatatypeType ::
    { _module.__default.IsTrace($LS($ly), trace#0, t#0, r#0) }
    _module.__default.IsTrace#canCall(trace#0, t#0, r#0)
         || (15 != $FunctionContextHeight
           &&
          $Is(trace#0, Tclass._module.Trace())
           && $Is(t#0, Tclass._module.Term())
           && $Is(r#0, Tclass._module.Term()))
       ==> (!_module.Trace.EmptyTrace_q(trace#0)
           ==> _module.__default.IsTrace#canCall(_module.Trace._h4(trace#0), t#0, _module.Trace._h5(trace#0))
             && (_module.__default.IsTrace($ly, _module.Trace._h4(trace#0), t#0, _module.Trace._h5(trace#0))
               ==> _module.__default.FindAndStep#canCall(_module.Trace._h5(trace#0))))
         && _module.__default.IsTrace($LS($ly), trace#0, t#0, r#0)
           == (if _module.Trace.EmptyTrace_q(trace#0)
             then t#0 == r#0
             else _module.__default.IsTrace($ly, _module.Trace._h4(trace#0), t#0, _module.Trace._h5(trace#0))
               && _module.__default.FindAndStep($LS($LZ), _module.Trace._h5(trace#0)) == r#0));

// definition axiom for _module.__default.IsTrace for all literals(revealed)
axiom 15 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, trace#0: DatatypeType, t#0: DatatypeType, r#0: DatatypeType ::
    {:weight 3} { _module.__default.IsTrace($LS($ly), Lit(trace#0), Lit(t#0), Lit(r#0)) }
    _module.__default.IsTrace#canCall(Lit(trace#0), Lit(t#0), Lit(r#0))
         || (15 != $FunctionContextHeight
           &&
          $Is(trace#0, Tclass._module.Trace())
           && $Is(t#0, Tclass._module.Term())
           && $Is(r#0, Tclass._module.Term()))
       ==> (!Lit(_module.Trace.EmptyTrace_q(Lit(trace#0)))
           ==> _module.__default.IsTrace#canCall(Lit(_module.Trace._h4(Lit(trace#0))),
              Lit(t#0),
              Lit(_module.Trace._h5(Lit(trace#0))))
             && (Lit(_module.__default.IsTrace($LS($ly),
                  Lit(_module.Trace._h4(Lit(trace#0))),
                  Lit(t#0),
                  Lit(_module.Trace._h5(Lit(trace#0)))))
               ==> _module.__default.FindAndStep#canCall(Lit(_module.Trace._h5(Lit(trace#0))))))
         && _module.__default.IsTrace($LS($ly), Lit(trace#0), Lit(t#0), Lit(r#0))
           == (if _module.Trace.EmptyTrace_q(Lit(trace#0))
             then Lit(t#0) == Lit(r#0)
             else _module.__default.IsTrace($LS($ly),
                Lit(_module.Trace._h4(Lit(trace#0))),
                Lit(t#0),
                Lit(_module.Trace._h5(Lit(trace#0))))
               && Lit(_module.__default.FindAndStep($LS($LZ), Lit(_module.Trace._h5(Lit(trace#0)))))
                 == Lit(r#0)));

procedure CheckWellformed$$_module.__default.IsTrace(trace#0: DatatypeType where $Is(trace#0, Tclass._module.Trace()),
    t#0: DatatypeType where $Is(t#0, Tclass._module.Term()),
    r#0: DatatypeType where $Is(r#0, Tclass._module.Term()));
  free requires 15 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.IsTrace(trace#0: DatatypeType, t#0: DatatypeType, r#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var tr#0: DatatypeType;
  var u#0: DatatypeType;
  var ##trace#0: DatatypeType;
  var ##t#0: DatatypeType;
  var ##r#0: DatatypeType;
  var ##t#1: DatatypeType;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function IsTrace
    assume {:captureState "Combinators.dfy(275,9): initial state"} true;
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
        if (trace#0 == #_module.Trace.EmptyTrace())
        {
            assume _module.__default.IsTrace($LS($LZ), trace#0, t#0, r#0) == (t#0 == r#0);
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.IsTrace($LS($LZ), trace#0, t#0, r#0), TBool);
        }
        else if (trace#0 == #_module.Trace.ReductionStep(tr#0, u#0))
        {
            assume $Is(tr#0, Tclass._module.Trace());
            assume $Is(u#0, Tclass._module.Term());
            ##trace#0 := tr#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##trace#0, Tclass._module.Trace(), $Heap);
            ##t#0 := t#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##t#0, Tclass._module.Term(), $Heap);
            ##r#0 := u#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##r#0, Tclass._module.Term(), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert DtRank(##trace#0) < DtRank(trace#0)
               || (DtRank(##trace#0) == DtRank(trace#0)
                 && (DtRank(##t#0) < DtRank(t#0)
                   || (DtRank(##t#0) == DtRank(t#0) && DtRank(##r#0) < DtRank(r#0))));
            assume _module.__default.IsTrace#canCall(tr#0, t#0, u#0);
            if (_module.__default.IsTrace($LS($LZ), tr#0, t#0, u#0))
            {
                ##t#1 := u#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##t#1, Tclass._module.Term(), $Heap);
                b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                assume _module.__default.FindAndStep#canCall(u#0);
            }

            assume _module.__default.IsTrace($LS($LZ), trace#0, t#0, r#0)
               == (_module.__default.IsTrace($LS($LZ), tr#0, t#0, u#0)
                 && _module.__default.FindAndStep($LS($LZ), u#0) == r#0);
            assume _module.__default.IsTrace#canCall(tr#0, t#0, u#0)
               && (_module.__default.IsTrace($LS($LZ), tr#0, t#0, u#0)
                 ==> _module.__default.FindAndStep#canCall(u#0));
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.IsTrace($LS($LZ), trace#0, t#0, r#0), TBool);
        }
        else
        {
            assume false;
        }

        assert b$reqreads#0;
        assert b$reqreads#1;
    }
}



procedure CheckWellformed$$_module.__default.reduction(t#0: DatatypeType
       where $Is(t#0, Tclass._module.Term())
         && $IsAlloc(t#0, Tclass._module.Term(), $Heap)
         && $IsA#_module.Term(t#0))
   returns (r#0: DatatypeType
       where $Is(r#0, Tclass._module.Term()) && $IsAlloc(r#0, Tclass._module.Term(), $Heap));
  free requires 16 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.reduction(t#0: DatatypeType
       where $Is(t#0, Tclass._module.Term())
         && $IsAlloc(t#0, Tclass._module.Term(), $Heap)
         && $IsA#_module.Term(t#0))
   returns (r#0: DatatypeType
       where $Is(r#0, Tclass._module.Term()) && $IsAlloc(r#0, Tclass._module.Term(), $Heap));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall trace#1: DatatypeType ::
    { _module.__default.IsTrace($LS($LZ), trace#1, t#0, r#0) }
    $Is(trace#1, Tclass._module.Trace())
       ==> _module.__default.IsTrace#canCall(trace#1, t#0, r#0));
  free ensures (exists trace#1: DatatypeType ::
    {:_induction trace#1} { _module.__default.IsTrace($LS($LS($LZ)), trace#1, t#0, r#0) }
    $Is(trace#1, Tclass._module.Trace())
       && _module.__default.IsTrace($LS($LS($LZ)), trace#1, t#0, r#0));
  free ensures _module.__default.IsTerminal#canCall(r#0);
  free ensures _module.__default.IsTerminal#canCall(r#0)
     &&
    _module.__default.IsTerminal(r#0)
     && !(exists C#0: DatatypeType, u#0: DatatypeType ::
      {:_induction C#0, u#0} { _module.__default.Step(u#0), _module.__default.IsContext($LS($LZ), C#0) }
        { _module.__default.EvalExpr($LS($LZ), C#0, u#0) }
      $Is(C#0, Tclass._module.Context())
         && $Is(u#0, Tclass._module.Term())
         &&
        _module.__default.IsContext($LS($LZ), C#0)
         && r#0 == _module.__default.EvalExpr($LS($LZ), C#0, u#0)
         && _module.__default.Step(u#0) != u#0);
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.reduction(t#0: DatatypeType
       where $Is(t#0, Tclass._module.Term())
         && $IsAlloc(t#0, Tclass._module.Term(), $Heap)
         && $IsA#_module.Term(t#0))
   returns (r#0: DatatypeType
       where $Is(r#0, Tclass._module.Term()) && $IsAlloc(r#0, Tclass._module.Term(), $Heap),
    $_reverifyPost: bool);
  free requires 16 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall trace#1: DatatypeType ::
    { _module.__default.IsTrace($LS($LZ), trace#1, t#0, r#0) }
    $Is(trace#1, Tclass._module.Trace())
       ==> _module.__default.IsTrace#canCall(trace#1, t#0, r#0));
  ensures (exists trace#1: DatatypeType ::
    {:_induction trace#1} { _module.__default.IsTrace($LS($LZ), trace#1, t#0, r#0) }
    $Is(trace#1, Tclass._module.Trace())
       && _module.__default.IsTrace($LS($LZ), trace#1, t#0, r#0));
  free ensures _module.__default.IsTerminal#canCall(r#0);
  ensures _module.__default.IsTerminal#canCall(r#0)
     ==> _module.__default.IsTerminal(r#0)
       || !(exists C#1: DatatypeType, u#1: DatatypeType ::
        { _module.__default.Step(u#1), _module.__default.IsContext($LS($LS($LZ)), C#1) }
          { _module.__default.EvalExpr($LS($LS($LZ)), C#1, u#1) }
        $Is(C#1, Tclass._module.Context())
           && $Is(u#1, Tclass._module.Term())
           && (forall C$ih#1#0: DatatypeType, u$ih#1#0: DatatypeType ::
            { _module.__default.Step(u$ih#1#0), _module.__default.IsContext($LS($LZ), C$ih#1#0) }
              { _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0) }
            $Is(C$ih#1#0, Tclass._module.Context()) && $Is(u$ih#1#0, Tclass._module.Term())
               ==>
              DtRank(C$ih#1#0) < DtRank(C#1)
                 || (DtRank(C$ih#1#0) == DtRank(C#1) && DtRank(u$ih#1#0) < DtRank(u#1))
               ==> !(
                _module.__default.IsContext($LS($LZ), C$ih#1#0)
                 && r#0 == _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0)
                 && _module.__default.Step(u$ih#1#0) != u$ih#1#0))
           &&
          true
           && #_module.Context.Hole() == C#1
           && #_module.Term.S() == u#1
           &&
          _module.__default.IsContext($LS($LS($LZ)), C#1)
           && r#0 == _module.__default.EvalExpr($LS($LS($LZ)), C#1, u#1)
           && _module.__default.Step(u#1) != u#1);
  ensures _module.__default.IsTerminal#canCall(r#0)
     ==> _module.__default.IsTerminal(r#0)
       || !(exists C#1: DatatypeType, u#1: DatatypeType ::
        { _module.__default.Step(u#1), _module.__default.IsContext($LS($LS($LZ)), C#1) }
          { _module.__default.EvalExpr($LS($LS($LZ)), C#1, u#1) }
        $Is(C#1, Tclass._module.Context())
           && $Is(u#1, Tclass._module.Term())
           && (forall C$ih#1#0: DatatypeType, u$ih#1#0: DatatypeType ::
            { _module.__default.Step(u$ih#1#0), _module.__default.IsContext($LS($LZ), C$ih#1#0) }
              { _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0) }
            $Is(C$ih#1#0, Tclass._module.Context()) && $Is(u$ih#1#0, Tclass._module.Term())
               ==>
              DtRank(C$ih#1#0) < DtRank(C#1)
                 || (DtRank(C$ih#1#0) == DtRank(C#1) && DtRank(u$ih#1#0) < DtRank(u#1))
               ==> !(
                _module.__default.IsContext($LS($LZ), C$ih#1#0)
                 && r#0 == _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0)
                 && _module.__default.Step(u$ih#1#0) != u$ih#1#0))
           &&
          true
           && (exists a#7#0#0: DatatypeType, a#7#1#0: DatatypeType ::
            { #_module.Context.C_term(a#7#0#0, a#7#1#0) }
            $Is(a#7#0#0, Tclass._module.Context())
               && $Is(a#7#1#0, Tclass._module.Term())
               && #_module.Context.C_term(a#7#0#0, a#7#1#0) == C#1)
           && #_module.Term.S() == u#1
           &&
          _module.__default.IsContext($LS($LS($LZ)), C#1)
           && r#0 == _module.__default.EvalExpr($LS($LS($LZ)), C#1, u#1)
           && _module.__default.Step(u#1) != u#1);
  ensures _module.__default.IsTerminal#canCall(r#0)
     ==> _module.__default.IsTerminal(r#0)
       || !(exists C#1: DatatypeType, u#1: DatatypeType ::
        { _module.__default.Step(u#1), _module.__default.IsContext($LS($LS($LZ)), C#1) }
          { _module.__default.EvalExpr($LS($LS($LZ)), C#1, u#1) }
        $Is(C#1, Tclass._module.Context())
           && $Is(u#1, Tclass._module.Term())
           && (forall C$ih#1#0: DatatypeType, u$ih#1#0: DatatypeType ::
            { _module.__default.Step(u$ih#1#0), _module.__default.IsContext($LS($LZ), C$ih#1#0) }
              { _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0) }
            $Is(C$ih#1#0, Tclass._module.Context()) && $Is(u$ih#1#0, Tclass._module.Term())
               ==>
              DtRank(C$ih#1#0) < DtRank(C#1)
                 || (DtRank(C$ih#1#0) == DtRank(C#1) && DtRank(u$ih#1#0) < DtRank(u#1))
               ==> !(
                _module.__default.IsContext($LS($LZ), C$ih#1#0)
                 && r#0 == _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0)
                 && _module.__default.Step(u$ih#1#0) != u$ih#1#0))
           &&
          true
           && (exists a#8#0#0: DatatypeType, a#8#1#0: DatatypeType ::
            { #_module.Context.value_C(a#8#0#0, a#8#1#0) }
            $Is(a#8#0#0, Tclass._module.Term())
               && $Is(a#8#1#0, Tclass._module.Context())
               && #_module.Context.value_C(a#8#0#0, a#8#1#0) == C#1)
           && #_module.Term.S() == u#1
           &&
          _module.__default.IsContext($LS($LS($LZ)), C#1)
           && r#0 == _module.__default.EvalExpr($LS($LS($LZ)), C#1, u#1)
           && _module.__default.Step(u#1) != u#1);
  ensures _module.__default.IsTerminal#canCall(r#0)
     ==> _module.__default.IsTerminal(r#0)
       || !(exists C#1: DatatypeType, u#1: DatatypeType ::
        { _module.__default.Step(u#1), _module.__default.IsContext($LS($LS($LZ)), C#1) }
          { _module.__default.EvalExpr($LS($LS($LZ)), C#1, u#1) }
        $Is(C#1, Tclass._module.Context())
           && $Is(u#1, Tclass._module.Term())
           && (forall C$ih#1#0: DatatypeType, u$ih#1#0: DatatypeType ::
            { _module.__default.Step(u$ih#1#0), _module.__default.IsContext($LS($LZ), C$ih#1#0) }
              { _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0) }
            $Is(C$ih#1#0, Tclass._module.Context()) && $Is(u$ih#1#0, Tclass._module.Term())
               ==>
              DtRank(C$ih#1#0) < DtRank(C#1)
                 || (DtRank(C$ih#1#0) == DtRank(C#1) && DtRank(u$ih#1#0) < DtRank(u#1))
               ==> !(
                _module.__default.IsContext($LS($LZ), C$ih#1#0)
                 && r#0 == _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0)
                 && _module.__default.Step(u$ih#1#0) != u$ih#1#0))
           &&
          true
           && #_module.Context.Hole() == C#1
           && #_module.Term.K() == u#1
           &&
          _module.__default.IsContext($LS($LS($LZ)), C#1)
           && r#0 == _module.__default.EvalExpr($LS($LS($LZ)), C#1, u#1)
           && _module.__default.Step(u#1) != u#1);
  ensures _module.__default.IsTerminal#canCall(r#0)
     ==> _module.__default.IsTerminal(r#0)
       || !(exists C#1: DatatypeType, u#1: DatatypeType ::
        { _module.__default.Step(u#1), _module.__default.IsContext($LS($LS($LZ)), C#1) }
          { _module.__default.EvalExpr($LS($LS($LZ)), C#1, u#1) }
        $Is(C#1, Tclass._module.Context())
           && $Is(u#1, Tclass._module.Term())
           && (forall C$ih#1#0: DatatypeType, u$ih#1#0: DatatypeType ::
            { _module.__default.Step(u$ih#1#0), _module.__default.IsContext($LS($LZ), C$ih#1#0) }
              { _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0) }
            $Is(C$ih#1#0, Tclass._module.Context()) && $Is(u$ih#1#0, Tclass._module.Term())
               ==>
              DtRank(C$ih#1#0) < DtRank(C#1)
                 || (DtRank(C$ih#1#0) == DtRank(C#1) && DtRank(u$ih#1#0) < DtRank(u#1))
               ==> !(
                _module.__default.IsContext($LS($LZ), C$ih#1#0)
                 && r#0 == _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0)
                 && _module.__default.Step(u$ih#1#0) != u$ih#1#0))
           &&
          true
           && (exists a#7#0#0: DatatypeType, a#7#1#0: DatatypeType ::
            { #_module.Context.C_term(a#7#0#0, a#7#1#0) }
            $Is(a#7#0#0, Tclass._module.Context())
               && $Is(a#7#1#0, Tclass._module.Term())
               && #_module.Context.C_term(a#7#0#0, a#7#1#0) == C#1)
           && #_module.Term.K() == u#1
           &&
          _module.__default.IsContext($LS($LS($LZ)), C#1)
           && r#0 == _module.__default.EvalExpr($LS($LS($LZ)), C#1, u#1)
           && _module.__default.Step(u#1) != u#1);
  ensures _module.__default.IsTerminal#canCall(r#0)
     ==> _module.__default.IsTerminal(r#0)
       || !(exists C#1: DatatypeType, u#1: DatatypeType ::
        { _module.__default.Step(u#1), _module.__default.IsContext($LS($LS($LZ)), C#1) }
          { _module.__default.EvalExpr($LS($LS($LZ)), C#1, u#1) }
        $Is(C#1, Tclass._module.Context())
           && $Is(u#1, Tclass._module.Term())
           && (forall C$ih#1#0: DatatypeType, u$ih#1#0: DatatypeType ::
            { _module.__default.Step(u$ih#1#0), _module.__default.IsContext($LS($LZ), C$ih#1#0) }
              { _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0) }
            $Is(C$ih#1#0, Tclass._module.Context()) && $Is(u$ih#1#0, Tclass._module.Term())
               ==>
              DtRank(C$ih#1#0) < DtRank(C#1)
                 || (DtRank(C$ih#1#0) == DtRank(C#1) && DtRank(u$ih#1#0) < DtRank(u#1))
               ==> !(
                _module.__default.IsContext($LS($LZ), C$ih#1#0)
                 && r#0 == _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0)
                 && _module.__default.Step(u$ih#1#0) != u$ih#1#0))
           &&
          true
           && (exists a#8#0#0: DatatypeType, a#8#1#0: DatatypeType ::
            { #_module.Context.value_C(a#8#0#0, a#8#1#0) }
            $Is(a#8#0#0, Tclass._module.Term())
               && $Is(a#8#1#0, Tclass._module.Context())
               && #_module.Context.value_C(a#8#0#0, a#8#1#0) == C#1)
           && #_module.Term.K() == u#1
           &&
          _module.__default.IsContext($LS($LS($LZ)), C#1)
           && r#0 == _module.__default.EvalExpr($LS($LS($LZ)), C#1, u#1)
           && _module.__default.Step(u#1) != u#1);
  ensures _module.__default.IsTerminal#canCall(r#0)
     ==> _module.__default.IsTerminal(r#0)
       || !(exists C#1: DatatypeType, u#1: DatatypeType ::
        { _module.__default.Step(u#1), _module.__default.IsContext($LS($LS($LZ)), C#1) }
          { _module.__default.EvalExpr($LS($LS($LZ)), C#1, u#1) }
        $Is(C#1, Tclass._module.Context())
           && $Is(u#1, Tclass._module.Term())
           && (forall C$ih#1#0: DatatypeType, u$ih#1#0: DatatypeType ::
            { _module.__default.Step(u$ih#1#0), _module.__default.IsContext($LS($LZ), C$ih#1#0) }
              { _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0) }
            $Is(C$ih#1#0, Tclass._module.Context()) && $Is(u$ih#1#0, Tclass._module.Term())
               ==>
              DtRank(C$ih#1#0) < DtRank(C#1)
                 || (DtRank(C$ih#1#0) == DtRank(C#1) && DtRank(u$ih#1#0) < DtRank(u#1))
               ==> !(
                _module.__default.IsContext($LS($LZ), C$ih#1#0)
                 && r#0 == _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0)
                 && _module.__default.Step(u$ih#1#0) != u$ih#1#0))
           &&
          true
           && #_module.Context.Hole() == C#1
           && (exists a#11#0#0: DatatypeType, a#11#1#0: DatatypeType ::
            { #_module.Term.Apply(a#11#0#0, a#11#1#0) }
            $Is(a#11#0#0, Tclass._module.Term())
               && $Is(a#11#1#0, Tclass._module.Term())
               && #_module.Term.Apply(a#11#0#0, a#11#1#0) == u#1)
           &&
          _module.__default.IsContext($LS($LS($LZ)), C#1)
           && r#0 == _module.__default.EvalExpr($LS($LS($LZ)), C#1, u#1)
           && _module.__default.Step(u#1) != u#1);
  ensures _module.__default.IsTerminal#canCall(r#0)
     ==> _module.__default.IsTerminal(r#0)
       || !(exists C#1: DatatypeType, u#1: DatatypeType ::
        { _module.__default.Step(u#1), _module.__default.IsContext($LS($LS($LZ)), C#1) }
          { _module.__default.EvalExpr($LS($LS($LZ)), C#1, u#1) }
        $Is(C#1, Tclass._module.Context())
           && $Is(u#1, Tclass._module.Term())
           && (forall C$ih#1#0: DatatypeType, u$ih#1#0: DatatypeType ::
            { _module.__default.Step(u$ih#1#0), _module.__default.IsContext($LS($LZ), C$ih#1#0) }
              { _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0) }
            $Is(C$ih#1#0, Tclass._module.Context()) && $Is(u$ih#1#0, Tclass._module.Term())
               ==>
              DtRank(C$ih#1#0) < DtRank(C#1)
                 || (DtRank(C$ih#1#0) == DtRank(C#1) && DtRank(u$ih#1#0) < DtRank(u#1))
               ==> !(
                _module.__default.IsContext($LS($LZ), C$ih#1#0)
                 && r#0 == _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0)
                 && _module.__default.Step(u$ih#1#0) != u$ih#1#0))
           &&
          true
           && (exists a#7#0#0: DatatypeType, a#7#1#0: DatatypeType ::
            { #_module.Context.C_term(a#7#0#0, a#7#1#0) }
            $Is(a#7#0#0, Tclass._module.Context())
               && $Is(a#7#1#0, Tclass._module.Term())
               && #_module.Context.C_term(a#7#0#0, a#7#1#0) == C#1)
           && (exists a#11#0#0: DatatypeType, a#11#1#0: DatatypeType ::
            { #_module.Term.Apply(a#11#0#0, a#11#1#0) }
            $Is(a#11#0#0, Tclass._module.Term())
               && $Is(a#11#1#0, Tclass._module.Term())
               && #_module.Term.Apply(a#11#0#0, a#11#1#0) == u#1)
           &&
          _module.__default.IsContext($LS($LS($LZ)), C#1)
           && r#0 == _module.__default.EvalExpr($LS($LS($LZ)), C#1, u#1)
           && _module.__default.Step(u#1) != u#1);
  ensures _module.__default.IsTerminal#canCall(r#0)
     ==> _module.__default.IsTerminal(r#0)
       || !(exists C#1: DatatypeType, u#1: DatatypeType ::
        { _module.__default.Step(u#1), _module.__default.IsContext($LS($LS($LZ)), C#1) }
          { _module.__default.EvalExpr($LS($LS($LZ)), C#1, u#1) }
        $Is(C#1, Tclass._module.Context())
           && $Is(u#1, Tclass._module.Term())
           && (forall C$ih#1#0: DatatypeType, u$ih#1#0: DatatypeType ::
            { _module.__default.Step(u$ih#1#0), _module.__default.IsContext($LS($LZ), C$ih#1#0) }
              { _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0) }
            $Is(C$ih#1#0, Tclass._module.Context()) && $Is(u$ih#1#0, Tclass._module.Term())
               ==>
              DtRank(C$ih#1#0) < DtRank(C#1)
                 || (DtRank(C$ih#1#0) == DtRank(C#1) && DtRank(u$ih#1#0) < DtRank(u#1))
               ==> !(
                _module.__default.IsContext($LS($LZ), C$ih#1#0)
                 && r#0 == _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0)
                 && _module.__default.Step(u$ih#1#0) != u$ih#1#0))
           &&
          true
           && (exists a#8#0#0: DatatypeType, a#8#1#0: DatatypeType ::
            { #_module.Context.value_C(a#8#0#0, a#8#1#0) }
            $Is(a#8#0#0, Tclass._module.Term())
               && $Is(a#8#1#0, Tclass._module.Context())
               && #_module.Context.value_C(a#8#0#0, a#8#1#0) == C#1)
           && (exists a#11#0#0: DatatypeType, a#11#1#0: DatatypeType ::
            { #_module.Term.Apply(a#11#0#0, a#11#1#0) }
            $Is(a#11#0#0, Tclass._module.Term())
               && $Is(a#11#1#0, Tclass._module.Term())
               && #_module.Term.Apply(a#11#0#0, a#11#1#0) == u#1)
           &&
          _module.__default.IsContext($LS($LS($LZ)), C#1)
           && r#0 == _module.__default.EvalExpr($LS($LS($LZ)), C#1, u#1)
           && _module.__default.Step(u#1) != u#1);
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.reduction(t#0: DatatypeType) returns (r#0: DatatypeType, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var trace#2: DatatypeType
     where $Is(trace#2, Tclass._module.Trace())
       && $IsAlloc(trace#2, Tclass._module.Trace(), $Heap);
  var $PreLoopHeap$loop#0: Heap;
  var $w$loop#0: bool;
  var ##trace#1: DatatypeType;
  var ##t#2: DatatypeType;
  var ##r#1: DatatypeType;
  var u#0_0: DatatypeType
     where $Is(u#0_0, Tclass._module.Term())
       && $IsAlloc(u#0_0, Tclass._module.Term(), $Heap);
  var ##t#0_0: DatatypeType;
  var t##0_0_0: DatatypeType;
  var $rhs#0_0: DatatypeType where $Is($rhs#0_0, Tclass._module.Term());
  var $rhs#0_1: DatatypeType where $Is($rhs#0_1, Tclass._module.Trace());

    // AddMethodImpl: reduction, Impl$$_module.__default.reduction
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "Combinators.dfy(309,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- Combinators.dfy(310,5)
    assume true;
    assume true;
    r#0 := t#0;
    assume {:captureState "Combinators.dfy(310,8)"} true;
    // ----- assignment statement ----- Combinators.dfy(311,19)
    assume true;
    assume true;
    trace#2 := Lit(#_module.Trace.EmptyTrace());
    assume {:captureState "Combinators.dfy(311,31)"} true;
    // ----- while statement ----- Combinators.dfy(312,3)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    havoc $w$loop#0;
    while (true)
      free invariant $w$loop#0 ==> _module.__default.IsTrace#canCall(trace#2, t#0, r#0);
      invariant $w$loop#0 ==> _module.__default.IsTrace($LS($LS($LZ)), trace#2, t#0, r#0);
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
        assume {:captureState "Combinators.dfy(312,2): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            ##trace#1 := trace#2;
            // assume allocatedness for argument to function
            assume $IsAlloc(##trace#1, Tclass._module.Trace(), $Heap);
            ##t#2 := t#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##t#2, Tclass._module.Term(), $Heap);
            ##r#1 := r#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##r#1, Tclass._module.Term(), $Heap);
            assume _module.__default.IsTrace#canCall(trace#2, t#0, r#0);
            assume _module.__default.IsTrace#canCall(trace#2, t#0, r#0);
            assume _module.__default.IsTrace($LS($LZ), trace#2, t#0, r#0);
            assume true;
            assume false;
        }

        assume true;
        if (!Lit(true))
        {
            break;
        }

        // ----- assignment statement ----- Combinators.dfy(316,11)
        assume true;
        ##t#0_0 := r#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##t#0_0, Tclass._module.Term(), $Heap);
        assume _module.__default.FindAndStep#canCall(r#0);
        assume _module.__default.FindAndStep#canCall(r#0);
        u#0_0 := _module.__default.FindAndStep($LS($LZ), r#0);
        assume {:captureState "Combinators.dfy(316,27)"} true;
        // ----- if statement ----- Combinators.dfy(317,5)
        assume true;
        if (u#0_0 == r#0)
        {
            // ----- call statement ----- Combinators.dfy(319,26)
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            // ProcessCallStmt: CheckSubrange
            t##0_0_0 := r#0;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call Call$$_module.__default.Theorem__FindAndStep(t##0_0_0);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "Combinators.dfy(319,28)"} true;
            // ----- return statement ----- Combinators.dfy(320,7)
            return;
        }
        else
        {
        }

        // ----- update statement ----- Combinators.dfy(322,14)
        assume true;
        assume true;
        assume true;
        $rhs#0_0 := u#0_0;
        assume true;
        $rhs#0_1 := #_module.Trace.ReductionStep(trace#2, r#0);
        r#0 := $rhs#0_0;
        trace#2 := $rhs#0_1;
        assume {:captureState "Combinators.dfy(322,42)"} true;
        assume _module.__default.IsTrace#canCall(trace#2, t#0, r#0);
    }
}



// function declaration for _module._default.ContainsS
function _module.__default.ContainsS($ly: LayerType, t#0: DatatypeType) : bool;

function _module.__default.ContainsS#canCall(t#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, t#0: DatatypeType ::
  { _module.__default.ContainsS($LS($ly), t#0) }
  _module.__default.ContainsS($LS($ly), t#0)
     == _module.__default.ContainsS($ly, t#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, t#0: DatatypeType ::
  { _module.__default.ContainsS(AsFuelBottom($ly), t#0) }
  _module.__default.ContainsS($ly, t#0) == _module.__default.ContainsS($LZ, t#0));

// consequence axiom for _module.__default.ContainsS
axiom 2 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, t#0: DatatypeType ::
    { _module.__default.ContainsS($ly, t#0) }
    _module.__default.ContainsS#canCall(t#0)
         || (2 != $FunctionContextHeight && $Is(t#0, Tclass._module.Term()))
       ==> true);

function _module.__default.ContainsS#requires(LayerType, DatatypeType) : bool;

// #requires axiom for _module.__default.ContainsS
axiom (forall $ly: LayerType, t#0: DatatypeType ::
  { _module.__default.ContainsS#requires($ly, t#0) }
  $Is(t#0, Tclass._module.Term())
     ==> _module.__default.ContainsS#requires($ly, t#0) == true);

// definition axiom for _module.__default.ContainsS(revealed)
axiom 2 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, t#0: DatatypeType ::
    { _module.__default.ContainsS($LS($ly), t#0) }
    _module.__default.ContainsS#canCall(t#0)
         || (2 != $FunctionContextHeight && $Is(t#0, Tclass._module.Term()))
       ==> (!_module.Term.S_q(t#0)
           ==>
          !_module.Term.K_q(t#0)
           ==> _module.__default.ContainsS#canCall(_module.Term.car(t#0))
             && (!_module.__default.ContainsS($ly, _module.Term.car(t#0))
               ==> _module.__default.ContainsS#canCall(_module.Term.cdr(t#0))))
         && _module.__default.ContainsS($LS($ly), t#0)
           == (if _module.Term.S_q(t#0)
             then true
             else (if _module.Term.K_q(t#0)
               then false
               else _module.__default.ContainsS($ly, _module.Term.car(t#0))
                 || _module.__default.ContainsS($ly, _module.Term.cdr(t#0)))));

// definition axiom for _module.__default.ContainsS for all literals(revealed)
axiom 2 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, t#0: DatatypeType ::
    {:weight 3} { _module.__default.ContainsS($LS($ly), Lit(t#0)) }
    _module.__default.ContainsS#canCall(Lit(t#0))
         || (2 != $FunctionContextHeight && $Is(t#0, Tclass._module.Term()))
       ==> (!Lit(_module.Term.S_q(Lit(t#0)))
           ==>
          !Lit(_module.Term.K_q(Lit(t#0)))
           ==> _module.__default.ContainsS#canCall(Lit(_module.Term.car(Lit(t#0))))
             && (!Lit(_module.__default.ContainsS($LS($ly), Lit(_module.Term.car(Lit(t#0)))))
               ==> _module.__default.ContainsS#canCall(Lit(_module.Term.cdr(Lit(t#0))))))
         && _module.__default.ContainsS($LS($ly), Lit(t#0))
           == (if _module.Term.S_q(Lit(t#0))
             then true
             else (if _module.Term.K_q(Lit(t#0))
               then false
               else _module.__default.ContainsS($LS($ly), Lit(_module.Term.car(Lit(t#0))))
                 || _module.__default.ContainsS($LS($ly), Lit(_module.Term.cdr(Lit(t#0)))))));

procedure CheckWellformed$$_module.__default.ContainsS(t#0: DatatypeType where $Is(t#0, Tclass._module.Term()));
  free requires 2 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.ContainsS(t#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var x#0: DatatypeType;
  var y#0: DatatypeType;
  var ##t#0: DatatypeType;
  var ##t#1: DatatypeType;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function ContainsS
    assume {:captureState "Combinators.dfy(333,16): initial state"} true;
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
        if (t#0 == #_module.Term.S())
        {
            assume _module.__default.ContainsS($LS($LZ), t#0) == Lit(true);
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.ContainsS($LS($LZ), t#0), TBool);
        }
        else if (t#0 == #_module.Term.K())
        {
            assume _module.__default.ContainsS($LS($LZ), t#0) == Lit(false);
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.ContainsS($LS($LZ), t#0), TBool);
        }
        else if (t#0 == #_module.Term.Apply(x#0, y#0))
        {
            assume $Is(x#0, Tclass._module.Term());
            assume $Is(y#0, Tclass._module.Term());
            ##t#0 := x#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##t#0, Tclass._module.Term(), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert DtRank(##t#0) < DtRank(t#0);
            assume _module.__default.ContainsS#canCall(x#0);
            if (!_module.__default.ContainsS($LS($LZ), x#0))
            {
                ##t#1 := y#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##t#1, Tclass._module.Term(), $Heap);
                b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                assert DtRank(##t#1) < DtRank(t#0);
                assume _module.__default.ContainsS#canCall(y#0);
            }

            assume _module.__default.ContainsS($LS($LZ), t#0)
               == (_module.__default.ContainsS($LS($LZ), x#0)
                 || _module.__default.ContainsS($LS($LZ), y#0));
            assume _module.__default.ContainsS#canCall(x#0)
               && (!_module.__default.ContainsS($LS($LZ), x#0)
                 ==> _module.__default.ContainsS#canCall(y#0));
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.ContainsS($LS($LZ), t#0), TBool);
        }
        else
        {
            assume false;
        }

        assert b$reqreads#0;
        assert b$reqreads#1;
    }
}



procedure CheckWellformed$$_module.__default.VerificationTask2(t#0: DatatypeType
       where $Is(t#0, Tclass._module.Term())
         && $IsAlloc(t#0, Tclass._module.Term(), $Heap)
         && $IsA#_module.Term(t#0))
   returns (r#0: DatatypeType
       where $Is(r#0, Tclass._module.Term()) && $IsAlloc(r#0, Tclass._module.Term(), $Heap));
  free requires 17 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.VerificationTask2(t#0: DatatypeType) returns (r#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##t#0: DatatypeType;
  var trace#0: DatatypeType;
  var ##trace#0: DatatypeType;
  var ##t#1: DatatypeType;
  var ##r#0: DatatypeType;
  var ##t#2: DatatypeType;
  var ##t#3: DatatypeType;

    // AddMethodImpl: VerificationTask2, CheckWellformed$$_module.__default.VerificationTask2
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "Combinators.dfy(356,7): initial state"} true;
    ##t#0 := t#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##t#0, Tclass._module.Term(), $Heap);
    assume _module.__default.ContainsS#canCall(t#0);
    assume !_module.__default.ContainsS($LS($LZ), t#0);
    havoc $Heap;
    assume (forall<alpha> $o: ref, $f: Field alpha ::
      { read($Heap, $o, $f) }
      $o != null && read(old($Heap), $o, alloc)
         ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
    assume $HeapSucc(old($Heap), $Heap);
    havoc r#0;
    assume {:captureState "Combinators.dfy(359,10): post-state"} true;
    havoc trace#0;
    assume $Is(trace#0, Tclass._module.Trace());
    ##trace#0 := trace#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##trace#0, Tclass._module.Trace(), $Heap);
    ##t#1 := t#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##t#1, Tclass._module.Term(), $Heap);
    ##r#0 := r#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##r#0, Tclass._module.Term(), $Heap);
    assume _module.__default.IsTrace#canCall(trace#0, t#0, r#0);
    assume _module.__default.IsTrace($LS($LZ), trace#0, t#0, r#0);
    ##t#2 := r#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##t#2, Tclass._module.Term(), $Heap);
    assume _module.__default.IsTerminal#canCall(r#0);
    assume _module.__default.IsTerminal(r#0);
    ##t#3 := t#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##t#3, Tclass._module.Term(), $Heap);
    assert {:subsumption 0} !_module.__default.ContainsS($LS($LS($LZ)), ##t#3);
    assume !_module.__default.ContainsS($LS($LZ), ##t#3);
    assume _module.__default.TerminatingReduction#canCall(t#0);
    assume r#0 == _module.__default.TerminatingReduction($LS($LZ), t#0);
}



procedure Call$$_module.__default.VerificationTask2(t#0: DatatypeType
       where $Is(t#0, Tclass._module.Term())
         && $IsAlloc(t#0, Tclass._module.Term(), $Heap)
         && $IsA#_module.Term(t#0))
   returns (r#0: DatatypeType
       where $Is(r#0, Tclass._module.Term()) && $IsAlloc(r#0, Tclass._module.Term(), $Heap));
  // user-defined preconditions
  requires !_module.__default.ContainsS($LS($LS($LZ)), t#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall trace#1: DatatypeType ::
    { _module.__default.IsTrace($LS($LZ), trace#1, t#0, r#0) }
    $Is(trace#1, Tclass._module.Trace())
       ==> _module.__default.IsTrace#canCall(trace#1, t#0, r#0));
  free ensures (exists trace#1: DatatypeType ::
    {:_induction trace#1} { _module.__default.IsTrace($LS($LS($LZ)), trace#1, t#0, r#0) }
    $Is(trace#1, Tclass._module.Trace())
       && _module.__default.IsTrace($LS($LS($LZ)), trace#1, t#0, r#0));
  free ensures _module.__default.IsTerminal#canCall(r#0);
  free ensures _module.__default.IsTerminal#canCall(r#0)
     &&
    _module.__default.IsTerminal(r#0)
     && !(exists C#0: DatatypeType, u#0: DatatypeType ::
      {:_induction C#0, u#0} { _module.__default.Step(u#0), _module.__default.IsContext($LS($LZ), C#0) }
        { _module.__default.EvalExpr($LS($LZ), C#0, u#0) }
      $Is(C#0, Tclass._module.Context())
         && $Is(u#0, Tclass._module.Term())
         &&
        _module.__default.IsContext($LS($LZ), C#0)
         && r#0 == _module.__default.EvalExpr($LS($LZ), C#0, u#0)
         && _module.__default.Step(u#0) != u#0);
  free ensures _module.__default.TerminatingReduction#canCall(t#0);
  ensures r#0 == _module.__default.TerminatingReduction($LS($LS($LZ)), t#0);
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.VerificationTask2(t#0: DatatypeType
       where $Is(t#0, Tclass._module.Term())
         && $IsAlloc(t#0, Tclass._module.Term(), $Heap)
         && $IsA#_module.Term(t#0))
   returns (r#0: DatatypeType
       where $Is(r#0, Tclass._module.Term()) && $IsAlloc(r#0, Tclass._module.Term(), $Heap),
    $_reverifyPost: bool);
  free requires 17 == $FunctionContextHeight;
  // user-defined preconditions
  requires !_module.__default.ContainsS($LS($LS($LZ)), t#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall trace#1: DatatypeType ::
    { _module.__default.IsTrace($LS($LZ), trace#1, t#0, r#0) }
    $Is(trace#1, Tclass._module.Trace())
       ==> _module.__default.IsTrace#canCall(trace#1, t#0, r#0));
  ensures (exists trace#1: DatatypeType ::
    {:_induction trace#1} { _module.__default.IsTrace($LS($LZ), trace#1, t#0, r#0) }
    $Is(trace#1, Tclass._module.Trace())
       && _module.__default.IsTrace($LS($LZ), trace#1, t#0, r#0));
  free ensures _module.__default.IsTerminal#canCall(r#0);
  ensures _module.__default.IsTerminal#canCall(r#0)
     ==> _module.__default.IsTerminal(r#0)
       || !(exists C#1: DatatypeType, u#1: DatatypeType ::
        { _module.__default.Step(u#1), _module.__default.IsContext($LS($LS($LZ)), C#1) }
          { _module.__default.EvalExpr($LS($LS($LZ)), C#1, u#1) }
        $Is(C#1, Tclass._module.Context())
           && $Is(u#1, Tclass._module.Term())
           && (forall C$ih#1#0: DatatypeType, u$ih#1#0: DatatypeType ::
            { _module.__default.Step(u$ih#1#0), _module.__default.IsContext($LS($LZ), C$ih#1#0) }
              { _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0) }
            $Is(C$ih#1#0, Tclass._module.Context()) && $Is(u$ih#1#0, Tclass._module.Term())
               ==>
              DtRank(C$ih#1#0) < DtRank(C#1)
                 || (DtRank(C$ih#1#0) == DtRank(C#1) && DtRank(u$ih#1#0) < DtRank(u#1))
               ==> !(
                _module.__default.IsContext($LS($LZ), C$ih#1#0)
                 && r#0 == _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0)
                 && _module.__default.Step(u$ih#1#0) != u$ih#1#0))
           &&
          true
           && #_module.Context.Hole() == C#1
           && #_module.Term.S() == u#1
           &&
          _module.__default.IsContext($LS($LS($LZ)), C#1)
           && r#0 == _module.__default.EvalExpr($LS($LS($LZ)), C#1, u#1)
           && _module.__default.Step(u#1) != u#1);
  ensures _module.__default.IsTerminal#canCall(r#0)
     ==> _module.__default.IsTerminal(r#0)
       || !(exists C#1: DatatypeType, u#1: DatatypeType ::
        { _module.__default.Step(u#1), _module.__default.IsContext($LS($LS($LZ)), C#1) }
          { _module.__default.EvalExpr($LS($LS($LZ)), C#1, u#1) }
        $Is(C#1, Tclass._module.Context())
           && $Is(u#1, Tclass._module.Term())
           && (forall C$ih#1#0: DatatypeType, u$ih#1#0: DatatypeType ::
            { _module.__default.Step(u$ih#1#0), _module.__default.IsContext($LS($LZ), C$ih#1#0) }
              { _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0) }
            $Is(C$ih#1#0, Tclass._module.Context()) && $Is(u$ih#1#0, Tclass._module.Term())
               ==>
              DtRank(C$ih#1#0) < DtRank(C#1)
                 || (DtRank(C$ih#1#0) == DtRank(C#1) && DtRank(u$ih#1#0) < DtRank(u#1))
               ==> !(
                _module.__default.IsContext($LS($LZ), C$ih#1#0)
                 && r#0 == _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0)
                 && _module.__default.Step(u$ih#1#0) != u$ih#1#0))
           &&
          true
           && (exists a#7#0#0: DatatypeType, a#7#1#0: DatatypeType ::
            { #_module.Context.C_term(a#7#0#0, a#7#1#0) }
            $Is(a#7#0#0, Tclass._module.Context())
               && $Is(a#7#1#0, Tclass._module.Term())
               && #_module.Context.C_term(a#7#0#0, a#7#1#0) == C#1)
           && #_module.Term.S() == u#1
           &&
          _module.__default.IsContext($LS($LS($LZ)), C#1)
           && r#0 == _module.__default.EvalExpr($LS($LS($LZ)), C#1, u#1)
           && _module.__default.Step(u#1) != u#1);
  ensures _module.__default.IsTerminal#canCall(r#0)
     ==> _module.__default.IsTerminal(r#0)
       || !(exists C#1: DatatypeType, u#1: DatatypeType ::
        { _module.__default.Step(u#1), _module.__default.IsContext($LS($LS($LZ)), C#1) }
          { _module.__default.EvalExpr($LS($LS($LZ)), C#1, u#1) }
        $Is(C#1, Tclass._module.Context())
           && $Is(u#1, Tclass._module.Term())
           && (forall C$ih#1#0: DatatypeType, u$ih#1#0: DatatypeType ::
            { _module.__default.Step(u$ih#1#0), _module.__default.IsContext($LS($LZ), C$ih#1#0) }
              { _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0) }
            $Is(C$ih#1#0, Tclass._module.Context()) && $Is(u$ih#1#0, Tclass._module.Term())
               ==>
              DtRank(C$ih#1#0) < DtRank(C#1)
                 || (DtRank(C$ih#1#0) == DtRank(C#1) && DtRank(u$ih#1#0) < DtRank(u#1))
               ==> !(
                _module.__default.IsContext($LS($LZ), C$ih#1#0)
                 && r#0 == _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0)
                 && _module.__default.Step(u$ih#1#0) != u$ih#1#0))
           &&
          true
           && (exists a#8#0#0: DatatypeType, a#8#1#0: DatatypeType ::
            { #_module.Context.value_C(a#8#0#0, a#8#1#0) }
            $Is(a#8#0#0, Tclass._module.Term())
               && $Is(a#8#1#0, Tclass._module.Context())
               && #_module.Context.value_C(a#8#0#0, a#8#1#0) == C#1)
           && #_module.Term.S() == u#1
           &&
          _module.__default.IsContext($LS($LS($LZ)), C#1)
           && r#0 == _module.__default.EvalExpr($LS($LS($LZ)), C#1, u#1)
           && _module.__default.Step(u#1) != u#1);
  ensures _module.__default.IsTerminal#canCall(r#0)
     ==> _module.__default.IsTerminal(r#0)
       || !(exists C#1: DatatypeType, u#1: DatatypeType ::
        { _module.__default.Step(u#1), _module.__default.IsContext($LS($LS($LZ)), C#1) }
          { _module.__default.EvalExpr($LS($LS($LZ)), C#1, u#1) }
        $Is(C#1, Tclass._module.Context())
           && $Is(u#1, Tclass._module.Term())
           && (forall C$ih#1#0: DatatypeType, u$ih#1#0: DatatypeType ::
            { _module.__default.Step(u$ih#1#0), _module.__default.IsContext($LS($LZ), C$ih#1#0) }
              { _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0) }
            $Is(C$ih#1#0, Tclass._module.Context()) && $Is(u$ih#1#0, Tclass._module.Term())
               ==>
              DtRank(C$ih#1#0) < DtRank(C#1)
                 || (DtRank(C$ih#1#0) == DtRank(C#1) && DtRank(u$ih#1#0) < DtRank(u#1))
               ==> !(
                _module.__default.IsContext($LS($LZ), C$ih#1#0)
                 && r#0 == _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0)
                 && _module.__default.Step(u$ih#1#0) != u$ih#1#0))
           &&
          true
           && #_module.Context.Hole() == C#1
           && #_module.Term.K() == u#1
           &&
          _module.__default.IsContext($LS($LS($LZ)), C#1)
           && r#0 == _module.__default.EvalExpr($LS($LS($LZ)), C#1, u#1)
           && _module.__default.Step(u#1) != u#1);
  ensures _module.__default.IsTerminal#canCall(r#0)
     ==> _module.__default.IsTerminal(r#0)
       || !(exists C#1: DatatypeType, u#1: DatatypeType ::
        { _module.__default.Step(u#1), _module.__default.IsContext($LS($LS($LZ)), C#1) }
          { _module.__default.EvalExpr($LS($LS($LZ)), C#1, u#1) }
        $Is(C#1, Tclass._module.Context())
           && $Is(u#1, Tclass._module.Term())
           && (forall C$ih#1#0: DatatypeType, u$ih#1#0: DatatypeType ::
            { _module.__default.Step(u$ih#1#0), _module.__default.IsContext($LS($LZ), C$ih#1#0) }
              { _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0) }
            $Is(C$ih#1#0, Tclass._module.Context()) && $Is(u$ih#1#0, Tclass._module.Term())
               ==>
              DtRank(C$ih#1#0) < DtRank(C#1)
                 || (DtRank(C$ih#1#0) == DtRank(C#1) && DtRank(u$ih#1#0) < DtRank(u#1))
               ==> !(
                _module.__default.IsContext($LS($LZ), C$ih#1#0)
                 && r#0 == _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0)
                 && _module.__default.Step(u$ih#1#0) != u$ih#1#0))
           &&
          true
           && (exists a#7#0#0: DatatypeType, a#7#1#0: DatatypeType ::
            { #_module.Context.C_term(a#7#0#0, a#7#1#0) }
            $Is(a#7#0#0, Tclass._module.Context())
               && $Is(a#7#1#0, Tclass._module.Term())
               && #_module.Context.C_term(a#7#0#0, a#7#1#0) == C#1)
           && #_module.Term.K() == u#1
           &&
          _module.__default.IsContext($LS($LS($LZ)), C#1)
           && r#0 == _module.__default.EvalExpr($LS($LS($LZ)), C#1, u#1)
           && _module.__default.Step(u#1) != u#1);
  ensures _module.__default.IsTerminal#canCall(r#0)
     ==> _module.__default.IsTerminal(r#0)
       || !(exists C#1: DatatypeType, u#1: DatatypeType ::
        { _module.__default.Step(u#1), _module.__default.IsContext($LS($LS($LZ)), C#1) }
          { _module.__default.EvalExpr($LS($LS($LZ)), C#1, u#1) }
        $Is(C#1, Tclass._module.Context())
           && $Is(u#1, Tclass._module.Term())
           && (forall C$ih#1#0: DatatypeType, u$ih#1#0: DatatypeType ::
            { _module.__default.Step(u$ih#1#0), _module.__default.IsContext($LS($LZ), C$ih#1#0) }
              { _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0) }
            $Is(C$ih#1#0, Tclass._module.Context()) && $Is(u$ih#1#0, Tclass._module.Term())
               ==>
              DtRank(C$ih#1#0) < DtRank(C#1)
                 || (DtRank(C$ih#1#0) == DtRank(C#1) && DtRank(u$ih#1#0) < DtRank(u#1))
               ==> !(
                _module.__default.IsContext($LS($LZ), C$ih#1#0)
                 && r#0 == _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0)
                 && _module.__default.Step(u$ih#1#0) != u$ih#1#0))
           &&
          true
           && (exists a#8#0#0: DatatypeType, a#8#1#0: DatatypeType ::
            { #_module.Context.value_C(a#8#0#0, a#8#1#0) }
            $Is(a#8#0#0, Tclass._module.Term())
               && $Is(a#8#1#0, Tclass._module.Context())
               && #_module.Context.value_C(a#8#0#0, a#8#1#0) == C#1)
           && #_module.Term.K() == u#1
           &&
          _module.__default.IsContext($LS($LS($LZ)), C#1)
           && r#0 == _module.__default.EvalExpr($LS($LS($LZ)), C#1, u#1)
           && _module.__default.Step(u#1) != u#1);
  ensures _module.__default.IsTerminal#canCall(r#0)
     ==> _module.__default.IsTerminal(r#0)
       || !(exists C#1: DatatypeType, u#1: DatatypeType ::
        { _module.__default.Step(u#1), _module.__default.IsContext($LS($LS($LZ)), C#1) }
          { _module.__default.EvalExpr($LS($LS($LZ)), C#1, u#1) }
        $Is(C#1, Tclass._module.Context())
           && $Is(u#1, Tclass._module.Term())
           && (forall C$ih#1#0: DatatypeType, u$ih#1#0: DatatypeType ::
            { _module.__default.Step(u$ih#1#0), _module.__default.IsContext($LS($LZ), C$ih#1#0) }
              { _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0) }
            $Is(C$ih#1#0, Tclass._module.Context()) && $Is(u$ih#1#0, Tclass._module.Term())
               ==>
              DtRank(C$ih#1#0) < DtRank(C#1)
                 || (DtRank(C$ih#1#0) == DtRank(C#1) && DtRank(u$ih#1#0) < DtRank(u#1))
               ==> !(
                _module.__default.IsContext($LS($LZ), C$ih#1#0)
                 && r#0 == _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0)
                 && _module.__default.Step(u$ih#1#0) != u$ih#1#0))
           &&
          true
           && #_module.Context.Hole() == C#1
           && (exists a#11#0#0: DatatypeType, a#11#1#0: DatatypeType ::
            { #_module.Term.Apply(a#11#0#0, a#11#1#0) }
            $Is(a#11#0#0, Tclass._module.Term())
               && $Is(a#11#1#0, Tclass._module.Term())
               && #_module.Term.Apply(a#11#0#0, a#11#1#0) == u#1)
           &&
          _module.__default.IsContext($LS($LS($LZ)), C#1)
           && r#0 == _module.__default.EvalExpr($LS($LS($LZ)), C#1, u#1)
           && _module.__default.Step(u#1) != u#1);
  ensures _module.__default.IsTerminal#canCall(r#0)
     ==> _module.__default.IsTerminal(r#0)
       || !(exists C#1: DatatypeType, u#1: DatatypeType ::
        { _module.__default.Step(u#1), _module.__default.IsContext($LS($LS($LZ)), C#1) }
          { _module.__default.EvalExpr($LS($LS($LZ)), C#1, u#1) }
        $Is(C#1, Tclass._module.Context())
           && $Is(u#1, Tclass._module.Term())
           && (forall C$ih#1#0: DatatypeType, u$ih#1#0: DatatypeType ::
            { _module.__default.Step(u$ih#1#0), _module.__default.IsContext($LS($LZ), C$ih#1#0) }
              { _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0) }
            $Is(C$ih#1#0, Tclass._module.Context()) && $Is(u$ih#1#0, Tclass._module.Term())
               ==>
              DtRank(C$ih#1#0) < DtRank(C#1)
                 || (DtRank(C$ih#1#0) == DtRank(C#1) && DtRank(u$ih#1#0) < DtRank(u#1))
               ==> !(
                _module.__default.IsContext($LS($LZ), C$ih#1#0)
                 && r#0 == _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0)
                 && _module.__default.Step(u$ih#1#0) != u$ih#1#0))
           &&
          true
           && (exists a#7#0#0: DatatypeType, a#7#1#0: DatatypeType ::
            { #_module.Context.C_term(a#7#0#0, a#7#1#0) }
            $Is(a#7#0#0, Tclass._module.Context())
               && $Is(a#7#1#0, Tclass._module.Term())
               && #_module.Context.C_term(a#7#0#0, a#7#1#0) == C#1)
           && (exists a#11#0#0: DatatypeType, a#11#1#0: DatatypeType ::
            { #_module.Term.Apply(a#11#0#0, a#11#1#0) }
            $Is(a#11#0#0, Tclass._module.Term())
               && $Is(a#11#1#0, Tclass._module.Term())
               && #_module.Term.Apply(a#11#0#0, a#11#1#0) == u#1)
           &&
          _module.__default.IsContext($LS($LS($LZ)), C#1)
           && r#0 == _module.__default.EvalExpr($LS($LS($LZ)), C#1, u#1)
           && _module.__default.Step(u#1) != u#1);
  ensures _module.__default.IsTerminal#canCall(r#0)
     ==> _module.__default.IsTerminal(r#0)
       || !(exists C#1: DatatypeType, u#1: DatatypeType ::
        { _module.__default.Step(u#1), _module.__default.IsContext($LS($LS($LZ)), C#1) }
          { _module.__default.EvalExpr($LS($LS($LZ)), C#1, u#1) }
        $Is(C#1, Tclass._module.Context())
           && $Is(u#1, Tclass._module.Term())
           && (forall C$ih#1#0: DatatypeType, u$ih#1#0: DatatypeType ::
            { _module.__default.Step(u$ih#1#0), _module.__default.IsContext($LS($LZ), C$ih#1#0) }
              { _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0) }
            $Is(C$ih#1#0, Tclass._module.Context()) && $Is(u$ih#1#0, Tclass._module.Term())
               ==>
              DtRank(C$ih#1#0) < DtRank(C#1)
                 || (DtRank(C$ih#1#0) == DtRank(C#1) && DtRank(u$ih#1#0) < DtRank(u#1))
               ==> !(
                _module.__default.IsContext($LS($LZ), C$ih#1#0)
                 && r#0 == _module.__default.EvalExpr($LS($LZ), C$ih#1#0, u$ih#1#0)
                 && _module.__default.Step(u$ih#1#0) != u$ih#1#0))
           &&
          true
           && (exists a#8#0#0: DatatypeType, a#8#1#0: DatatypeType ::
            { #_module.Context.value_C(a#8#0#0, a#8#1#0) }
            $Is(a#8#0#0, Tclass._module.Term())
               && $Is(a#8#1#0, Tclass._module.Context())
               && #_module.Context.value_C(a#8#0#0, a#8#1#0) == C#1)
           && (exists a#11#0#0: DatatypeType, a#11#1#0: DatatypeType ::
            { #_module.Term.Apply(a#11#0#0, a#11#1#0) }
            $Is(a#11#0#0, Tclass._module.Term())
               && $Is(a#11#1#0, Tclass._module.Term())
               && #_module.Term.Apply(a#11#0#0, a#11#1#0) == u#1)
           &&
          _module.__default.IsContext($LS($LS($LZ)), C#1)
           && r#0 == _module.__default.EvalExpr($LS($LS($LZ)), C#1, u#1)
           && _module.__default.Step(u#1) != u#1);
  free ensures _module.__default.TerminatingReduction#canCall(t#0);
  ensures r#0 == _module.__default.TerminatingReduction($LS($LS($LZ)), t#0);
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.VerificationTask2(t#0: DatatypeType) returns (r#0: DatatypeType, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var trace#2: DatatypeType
     where $Is(trace#2, Tclass._module.Trace())
       && $IsAlloc(trace#2, Tclass._module.Trace(), $Heap);
  var $PreLoopHeap$loop#0: Heap;
  var $decr_init$loop#00: int;
  var $w$loop#0: bool;
  var ##trace#1: DatatypeType;
  var ##t#4: DatatypeType;
  var ##r#1: DatatypeType;
  var ##t#5: DatatypeType;
  var ##t#6: DatatypeType;
  var ##t#7: DatatypeType;
  var ##t#8: DatatypeType;
  var $decr$loop#00: int;
  var u#0_0: DatatypeType
     where $Is(u#0_0, Tclass._module.Term())
       && $IsAlloc(u#0_0, Tclass._module.Term(), $Heap);
  var ##t#0_0: DatatypeType;
  var t##0_0_0: DatatypeType;
  var $rhs#0_0: DatatypeType where $Is($rhs#0_0, Tclass._module.Term());
  var $rhs#0_1: DatatypeType where $Is($rhs#0_1, Tclass._module.Trace());

    // AddMethodImpl: VerificationTask2, Impl$$_module.__default.VerificationTask2
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "Combinators.dfy(366,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- Combinators.dfy(367,5)
    assume true;
    assume true;
    r#0 := t#0;
    assume {:captureState "Combinators.dfy(367,8)"} true;
    // ----- assignment statement ----- Combinators.dfy(368,19)
    assume true;
    assume true;
    trace#2 := Lit(#_module.Trace.EmptyTrace());
    assume {:captureState "Combinators.dfy(368,31)"} true;
    // ----- while statement ----- Combinators.dfy(369,3)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    $decr_init$loop#00 := _module.__default.TermSize($LS($LZ), r#0);
    havoc $w$loop#0;
    while (true)
      free invariant $w$loop#0
         ==> _module.__default.IsTrace#canCall(trace#2, t#0, r#0)
           && (_module.__default.IsTrace($LS($LZ), trace#2, t#0, r#0)
             ==> _module.__default.ContainsS#canCall(r#0));
      invariant $w$loop#0 ==> _module.__default.IsTrace($LS($LS($LZ)), trace#2, t#0, r#0);
      invariant $w$loop#0 ==> !_module.__default.ContainsS($LS($LS($LZ)), r#0);
      free invariant $w$loop#0
         ==> _module.__default.TerminatingReduction#canCall(t#0)
           && _module.__default.TerminatingReduction#canCall(r#0);
      invariant $w$loop#0
         ==> _module.__default.TerminatingReduction($LS($LS($LZ)), t#0)
           == _module.__default.TerminatingReduction($LS($LS($LZ)), r#0);
      free invariant (forall<alpha> $o: ref, $f: Field alpha ::
        { read($Heap, $o, $f) }
        $o != null && read(old($Heap), $o, alloc)
           ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0, $o, $f));
      free invariant $HeapSucc($PreLoopHeap$loop#0, $Heap);
      free invariant (forall<alpha> $o: ref, $f: Field alpha ::
        { read($Heap, $o, $f) }
        $o != null && read($PreLoopHeap$loop#0, $o, alloc)
           ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0, $o, $f) || $_Frame[$o, $f]);
      free invariant _module.__default.TermSize($LS($LZ), r#0) <= $decr_init$loop#00
         && (_module.__default.TermSize($LS($LZ), r#0) == $decr_init$loop#00 ==> true);
    {
        assume {:captureState "Combinators.dfy(369,2): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            ##trace#1 := trace#2;
            // assume allocatedness for argument to function
            assume $IsAlloc(##trace#1, Tclass._module.Trace(), $Heap);
            ##t#4 := t#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##t#4, Tclass._module.Term(), $Heap);
            ##r#1 := r#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##r#1, Tclass._module.Term(), $Heap);
            assume _module.__default.IsTrace#canCall(trace#2, t#0, r#0);
            if (_module.__default.IsTrace($LS($LZ), trace#2, t#0, r#0))
            {
                ##t#5 := r#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##t#5, Tclass._module.Term(), $Heap);
                assume _module.__default.ContainsS#canCall(r#0);
            }

            assume _module.__default.IsTrace#canCall(trace#2, t#0, r#0)
               && (_module.__default.IsTrace($LS($LZ), trace#2, t#0, r#0)
                 ==> _module.__default.ContainsS#canCall(r#0));
            assume _module.__default.IsTrace($LS($LZ), trace#2, t#0, r#0)
               && !_module.__default.ContainsS($LS($LZ), r#0);
            ##t#6 := t#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##t#6, Tclass._module.Term(), $Heap);
            assert {:subsumption 0} !_module.__default.ContainsS($LS($LS($LZ)), ##t#6);
            assume _module.__default.TerminatingReduction#canCall(t#0);
            ##t#7 := r#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##t#7, Tclass._module.Term(), $Heap);
            assert {:subsumption 0} !_module.__default.ContainsS($LS($LS($LZ)), ##t#7);
            assume _module.__default.TerminatingReduction#canCall(r#0);
            assume _module.__default.TerminatingReduction#canCall(t#0)
               && _module.__default.TerminatingReduction#canCall(r#0);
            assume _module.__default.TerminatingReduction($LS($LZ), t#0)
               == _module.__default.TerminatingReduction($LS($LZ), r#0);
            ##t#8 := r#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##t#8, Tclass._module.Term(), $Heap);
            assume _module.__default.TermSize#canCall(r#0);
            assume _module.__default.TermSize#canCall(r#0);
            assume false;
        }

        assume true;
        if (!Lit(true))
        {
            break;
        }

        $decr$loop#00 := _module.__default.TermSize($LS($LZ), r#0);
        // ----- assignment statement ----- Combinators.dfy(374,11)
        assume true;
        ##t#0_0 := r#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##t#0_0, Tclass._module.Term(), $Heap);
        assume _module.__default.FindAndStep#canCall(r#0);
        assume _module.__default.FindAndStep#canCall(r#0);
        u#0_0 := _module.__default.FindAndStep($LS($LZ), r#0);
        assume {:captureState "Combinators.dfy(374,27)"} true;
        // ----- if statement ----- Combinators.dfy(375,5)
        assume true;
        if (u#0_0 == r#0)
        {
            // ----- call statement ----- Combinators.dfy(377,26)
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            // ProcessCallStmt: CheckSubrange
            t##0_0_0 := r#0;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call Call$$_module.__default.Theorem__FindAndStep(t##0_0_0);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "Combinators.dfy(377,28)"} true;
            // ----- return statement ----- Combinators.dfy(378,7)
            return;
        }
        else
        {
        }

        // ----- update statement ----- Combinators.dfy(380,14)
        assume true;
        assume true;
        assume true;
        $rhs#0_0 := u#0_0;
        assume true;
        $rhs#0_1 := #_module.Trace.ReductionStep(trace#2, r#0);
        r#0 := $rhs#0_0;
        trace#2 := $rhs#0_1;
        assume {:captureState "Combinators.dfy(380,42)"} true;
        // ----- loop termination check ----- Combinators.dfy(369,3)
        assert 0 <= $decr$loop#00 || _module.__default.TermSize($LS($LZ), r#0) == $decr$loop#00;
        assert _module.__default.TermSize($LS($LZ), r#0) < $decr$loop#00;
        assume _module.__default.IsTrace#canCall(trace#2, t#0, r#0)
           && (_module.__default.IsTrace($LS($LZ), trace#2, t#0, r#0)
             ==> _module.__default.ContainsS#canCall(r#0));
        assume _module.__default.TerminatingReduction#canCall(t#0)
           && _module.__default.TerminatingReduction#canCall(r#0);
    }
}



// function declaration for _module._default.TermSize
function _module.__default.TermSize($ly: LayerType, t#0: DatatypeType) : int;

function _module.__default.TermSize#canCall(t#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, t#0: DatatypeType ::
  { _module.__default.TermSize($LS($ly), t#0) }
  _module.__default.TermSize($LS($ly), t#0)
     == _module.__default.TermSize($ly, t#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, t#0: DatatypeType ::
  { _module.__default.TermSize(AsFuelBottom($ly), t#0) }
  _module.__default.TermSize($ly, t#0) == _module.__default.TermSize($LZ, t#0));

// consequence axiom for _module.__default.TermSize
axiom 1 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, t#0: DatatypeType ::
    { _module.__default.TermSize($ly, t#0) }
    _module.__default.TermSize#canCall(t#0)
         || (1 != $FunctionContextHeight && $Is(t#0, Tclass._module.Term()))
       ==> LitInt(0) <= _module.__default.TermSize($ly, t#0));

function _module.__default.TermSize#requires(LayerType, DatatypeType) : bool;

// #requires axiom for _module.__default.TermSize
axiom (forall $ly: LayerType, t#0: DatatypeType ::
  { _module.__default.TermSize#requires($ly, t#0) }
  $Is(t#0, Tclass._module.Term())
     ==> _module.__default.TermSize#requires($ly, t#0) == true);

// definition axiom for _module.__default.TermSize(revealed)
axiom 1 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, t#0: DatatypeType ::
    { _module.__default.TermSize($LS($ly), t#0) }
    _module.__default.TermSize#canCall(t#0)
         || (1 != $FunctionContextHeight && $Is(t#0, Tclass._module.Term()))
       ==> (!_module.Term.S_q(t#0)
           ==>
          !_module.Term.K_q(t#0)
           ==> _module.__default.TermSize#canCall(_module.Term.car(t#0))
             && _module.__default.TermSize#canCall(_module.Term.cdr(t#0)))
         && _module.__default.TermSize($LS($ly), t#0)
           == (if _module.Term.S_q(t#0)
             then 1
             else (if _module.Term.K_q(t#0)
               then 1
               else 1
                 + _module.__default.TermSize($ly, _module.Term.car(t#0))
                 + _module.__default.TermSize($ly, _module.Term.cdr(t#0)))));

// definition axiom for _module.__default.TermSize for all literals(revealed)
axiom 1 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, t#0: DatatypeType ::
    {:weight 3} { _module.__default.TermSize($LS($ly), Lit(t#0)) }
    _module.__default.TermSize#canCall(Lit(t#0))
         || (1 != $FunctionContextHeight && $Is(t#0, Tclass._module.Term()))
       ==> (!Lit(_module.Term.S_q(Lit(t#0)))
           ==>
          !Lit(_module.Term.K_q(Lit(t#0)))
           ==> _module.__default.TermSize#canCall(Lit(_module.Term.car(Lit(t#0))))
             && _module.__default.TermSize#canCall(Lit(_module.Term.cdr(Lit(t#0)))))
         && _module.__default.TermSize($LS($ly), Lit(t#0))
           == (if _module.Term.S_q(Lit(t#0))
             then 1
             else (if _module.Term.K_q(Lit(t#0))
               then 1
               else 1
                 + _module.__default.TermSize($LS($ly), Lit(_module.Term.car(Lit(t#0))))
                 + _module.__default.TermSize($LS($ly), Lit(_module.Term.cdr(Lit(t#0)))))));

procedure CheckWellformed$$_module.__default.TermSize(t#0: DatatypeType where $Is(t#0, Tclass._module.Term()));
  free requires 1 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.TermSize(t#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var x#0: DatatypeType;
  var y#0: DatatypeType;
  var ##t#0: DatatypeType;
  var ##t#1: DatatypeType;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function TermSize
    assume {:captureState "Combinators.dfy(392,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume LitInt(0) <= _module.__default.TermSize($LS($LZ), t#0);
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
          $o != null && read($Heap, $o, alloc) ==> false);
        if (t#0 == #_module.Term.S())
        {
            assert $Is(LitInt(1), Tclass._System.nat());
            assume _module.__default.TermSize($LS($LZ), t#0) == LitInt(1);
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.TermSize($LS($LZ), t#0), Tclass._System.nat());
        }
        else if (t#0 == #_module.Term.K())
        {
            assert $Is(LitInt(1), Tclass._System.nat());
            assume _module.__default.TermSize($LS($LZ), t#0) == LitInt(1);
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.TermSize($LS($LZ), t#0), Tclass._System.nat());
        }
        else if (t#0 == #_module.Term.Apply(x#0, y#0))
        {
            assume $Is(x#0, Tclass._module.Term());
            assume $Is(y#0, Tclass._module.Term());
            ##t#0 := x#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##t#0, Tclass._module.Term(), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert DtRank(##t#0) < DtRank(t#0);
            assume _module.__default.TermSize#canCall(x#0);
            ##t#1 := y#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##t#1, Tclass._module.Term(), $Heap);
            b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert DtRank(##t#1) < DtRank(t#0);
            assume _module.__default.TermSize#canCall(y#0);
            assert $Is(1
                 + _module.__default.TermSize($LS($LZ), x#0)
                 + _module.__default.TermSize($LS($LZ), y#0),
              Tclass._System.nat());
            assume _module.__default.TermSize($LS($LZ), t#0)
               == 1
                 + _module.__default.TermSize($LS($LZ), x#0)
                 + _module.__default.TermSize($LS($LZ), y#0);
            assume _module.__default.TermSize#canCall(x#0)
               && _module.__default.TermSize#canCall(y#0);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.TermSize($LS($LZ), t#0), Tclass._System.nat());
        }
        else
        {
            assume false;
        }

        assert b$reqreads#0;
        assert b$reqreads#1;
    }
}



// function declaration for _module._default.TerminatingReduction
function _module.__default.TerminatingReduction($ly: LayerType, t#0: DatatypeType) : DatatypeType;

function _module.__default.TerminatingReduction#canCall(t#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, t#0: DatatypeType ::
  { _module.__default.TerminatingReduction($LS($ly), t#0) }
  _module.__default.TerminatingReduction($LS($ly), t#0)
     == _module.__default.TerminatingReduction($ly, t#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, t#0: DatatypeType ::
  { _module.__default.TerminatingReduction(AsFuelBottom($ly), t#0) }
  _module.__default.TerminatingReduction($ly, t#0)
     == _module.__default.TerminatingReduction($LZ, t#0));

// consequence axiom for _module.__default.TerminatingReduction
axiom 7 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, t#0: DatatypeType ::
    { _module.__default.TerminatingReduction($ly, t#0) }
    _module.__default.TerminatingReduction#canCall(t#0)
         || (7 != $FunctionContextHeight
           &&
          $Is(t#0, Tclass._module.Term())
           && !_module.__default.ContainsS($LS($LZ), t#0))
       ==> $Is(_module.__default.TerminatingReduction($ly, t#0), Tclass._module.Term()));

function _module.__default.TerminatingReduction#requires(LayerType, DatatypeType) : bool;

// #requires axiom for _module.__default.TerminatingReduction
axiom (forall $ly: LayerType, t#0: DatatypeType ::
  { _module.__default.TerminatingReduction#requires($ly, t#0) }
  $Is(t#0, Tclass._module.Term())
     ==> _module.__default.TerminatingReduction#requires($ly, t#0)
       == !_module.__default.ContainsS($LS($LZ), t#0));

// definition axiom for _module.__default.TerminatingReduction(revealed)
axiom 7 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, t#0: DatatypeType ::
    { _module.__default.TerminatingReduction($LS($ly), t#0) }
    _module.__default.TerminatingReduction#canCall(t#0)
         || (7 != $FunctionContextHeight
           &&
          $Is(t#0, Tclass._module.Term())
           && !_module.__default.ContainsS($LS($LZ), t#0))
       ==> _module.__default.FindAndStep#canCall(t#0)
         && (_module.__default.FindAndStep($LS($LZ), t#0) != t#0
           ==> _module.__default.FindAndStep#canCall(t#0)
             && _module.__default.TerminatingReduction#canCall(_module.__default.FindAndStep($LS($LZ), t#0)))
         && _module.__default.TerminatingReduction($LS($ly), t#0)
           == (if _module.__default.FindAndStep($LS($LZ), t#0) == t#0
             then t#0
             else _module.__default.TerminatingReduction($ly, _module.__default.FindAndStep($LS($LZ), t#0))));

// definition axiom for _module.__default.TerminatingReduction for all literals(revealed)
axiom 7 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, t#0: DatatypeType ::
    {:weight 3} { _module.__default.TerminatingReduction($LS($ly), Lit(t#0)) }
    _module.__default.TerminatingReduction#canCall(Lit(t#0))
         || (7 != $FunctionContextHeight
           &&
          $Is(t#0, Tclass._module.Term())
           && !Lit(_module.__default.ContainsS($LS($LZ), Lit(t#0))))
       ==> _module.__default.FindAndStep#canCall(Lit(t#0))
         && (Lit(_module.__default.FindAndStep($LS($LZ), Lit(t#0))) != Lit(t#0)
           ==> _module.__default.FindAndStep#canCall(Lit(t#0))
             && _module.__default.TerminatingReduction#canCall(Lit(_module.__default.FindAndStep($LS($LZ), Lit(t#0)))))
         && _module.__default.TerminatingReduction($LS($ly), Lit(t#0))
           == (if Lit(_module.__default.FindAndStep($LS($LZ), Lit(t#0))) == Lit(t#0)
             then t#0
             else _module.__default.TerminatingReduction($LS($ly), Lit(_module.__default.FindAndStep($LS($LZ), Lit(t#0))))));

procedure CheckWellformed$$_module.__default.TerminatingReduction(t#0: DatatypeType where $Is(t#0, Tclass._module.Term()));
  free requires 7 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.TerminatingReduction(t#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##t#0: DatatypeType;
  var b$reqreads#0: bool;
  var ##t#1: DatatypeType;
  var ##t#2: DatatypeType;
  var ##t#3: DatatypeType;
  var ##t#4: DatatypeType;
  var b$reqreads#1: bool;
  var b$reqreads#2: bool;
  var b$reqreads#3: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;
    b$reqreads#2 := true;
    b$reqreads#3 := true;

    // AddWellformednessCheck for function TerminatingReduction
    assume {:captureState "Combinators.dfy(415,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    ##t#0 := t#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##t#0, Tclass._module.Term(), $Heap);
    b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    assume _module.__default.ContainsS#canCall(t#0);
    assume !_module.__default.ContainsS($LS($LZ), t#0);
    assert b$reqreads#0;
    ##t#1 := t#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##t#1, Tclass._module.Term(), $Heap);
    assume _module.__default.TermSize#canCall(t#0);
    if (*)
    {
        assume $Is(_module.__default.TerminatingReduction($LS($LZ), t#0), Tclass._module.Term());
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
          $o != null && read($Heap, $o, alloc) ==> false);
        ##t#2 := t#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##t#2, Tclass._module.Term(), $Heap);
        b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume _module.__default.FindAndStep#canCall(t#0);
        if (_module.__default.FindAndStep($LS($LZ), t#0) == t#0)
        {
            assume _module.__default.TerminatingReduction($LS($LZ), t#0) == t#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.TerminatingReduction($LS($LZ), t#0), Tclass._module.Term());
        }
        else
        {
            ##t#3 := t#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##t#3, Tclass._module.Term(), $Heap);
            b$reqreads#2 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume _module.__default.FindAndStep#canCall(t#0);
            ##t#4 := _module.__default.FindAndStep($LS($LZ), t#0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##t#4, Tclass._module.Term(), $Heap);
            assert {:subsumption 0} !_module.__default.ContainsS($LS($LS($LZ)), ##t#4);
            assume !_module.__default.ContainsS($LS($LZ), ##t#4);
            b$reqreads#3 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert 0 <= _module.__default.TermSize($LS($LZ), t#0)
               || _module.__default.TermSize($LS($LZ), ##t#4)
                 == _module.__default.TermSize($LS($LZ), t#0);
            assert _module.__default.TermSize($LS($LZ), ##t#4)
               < _module.__default.TermSize($LS($LZ), t#0);
            assume _module.__default.TerminatingReduction#canCall(_module.__default.FindAndStep($LS($LZ), t#0));
            assume _module.__default.TerminatingReduction($LS($LZ), t#0)
               == _module.__default.TerminatingReduction($LS($LZ), _module.__default.FindAndStep($LS($LZ), t#0));
            assume _module.__default.FindAndStep#canCall(t#0)
               && _module.__default.TerminatingReduction#canCall(_module.__default.FindAndStep($LS($LZ), t#0));
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.TerminatingReduction($LS($LZ), t#0), Tclass._module.Term());
        }

        assert b$reqreads#1;
        assert b$reqreads#2;
        assert b$reqreads#3;
    }
}



// function declaration for _module._default.ks
function _module.__default.ks($ly: LayerType, n#0: int) : DatatypeType;

function _module.__default.ks#canCall(n#0: int) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, n#0: int ::
  { _module.__default.ks($LS($ly), n#0) }
  _module.__default.ks($LS($ly), n#0) == _module.__default.ks($ly, n#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, n#0: int ::
  { _module.__default.ks(AsFuelBottom($ly), n#0) }
  _module.__default.ks($ly, n#0) == _module.__default.ks($LZ, n#0));

// consequence axiom for _module.__default.ks
axiom 3 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: int ::
    { _module.__default.ks($ly, n#0) }
    _module.__default.ks#canCall(n#0)
         || (3 != $FunctionContextHeight && LitInt(0) <= n#0)
       ==> !_module.__default.ContainsS($LS($LZ), _module.__default.ks($ly, n#0))
         && $Is(_module.__default.ks($ly, n#0), Tclass._module.Term()));

function _module.__default.ks#requires(LayerType, int) : bool;

// #requires axiom for _module.__default.ks
axiom (forall $ly: LayerType, n#0: int ::
  { _module.__default.ks#requires($ly, n#0) }
  LitInt(0) <= n#0 ==> _module.__default.ks#requires($ly, n#0) == true);

// definition axiom for _module.__default.ks(revealed)
axiom 3 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: int ::
    { _module.__default.ks($LS($ly), n#0) }
    _module.__default.ks#canCall(n#0)
         || (3 != $FunctionContextHeight && LitInt(0) <= n#0)
       ==> (n#0 != LitInt(0) ==> _module.__default.ks#canCall(n#0 - 1))
         && _module.__default.ks($LS($ly), n#0)
           == (if n#0 == LitInt(0)
             then #_module.Term.K()
             else #_module.Term.Apply(_module.__default.ks($ly, n#0 - 1), Lit(#_module.Term.K()))));

// definition axiom for _module.__default.ks for all literals(revealed)
axiom 3 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: int ::
    {:weight 3} { _module.__default.ks($LS($ly), LitInt(n#0)) }
    _module.__default.ks#canCall(LitInt(n#0))
         || (3 != $FunctionContextHeight && LitInt(0) <= n#0)
       ==> (LitInt(n#0) != LitInt(0) ==> _module.__default.ks#canCall(LitInt(n#0 - 1)))
         && _module.__default.ks($LS($ly), LitInt(n#0))
           == (if LitInt(n#0) == LitInt(0)
             then #_module.Term.K()
             else #_module.Term.Apply(Lit(_module.__default.ks($LS($ly), LitInt(n#0 - 1))), Lit(#_module.Term.K()))));

procedure CheckWellformed$$_module.__default.ks(n#0: int where LitInt(0) <= n#0);
  free requires 3 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  ensures !_module.__default.ContainsS($LS($LS($LZ)), _module.__default.ks($LS($LS($LZ)), n#0));



implementation CheckWellformed$$_module.__default.ks(n#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##n#0: int;
  var ##t#0: DatatypeType;
  var ##n#1: int;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function ks
    assume {:captureState "Combinators.dfy(432,16): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.ks($LS($LZ), n#0), Tclass._module.Term());
        assert $Is(n#0, Tclass._System.nat());
        ##n#0 := n#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##n#0, Tclass._System.nat(), $Heap);
        assert 0 <= n#0 || ##n#0 == n#0;
        assert n#0 == n#0 || ##n#0 < n#0;
        assume n#0 == n#0 || _module.__default.ks#canCall(n#0);
        ##t#0 := _module.__default.ks($LS($LZ), n#0);
        // assume allocatedness for argument to function
        assume $IsAlloc(##t#0, Tclass._module.Term(), $Heap);
        assume _module.__default.ContainsS#canCall(_module.__default.ks($LS($LZ), n#0));
        assume !_module.__default.ContainsS($LS($LZ), _module.__default.ks($LS($LZ), n#0));
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
          $o != null && read($Heap, $o, alloc) ==> false);
        if (n#0 == LitInt(0))
        {
            assume _module.__default.ks($LS($LZ), n#0) == Lit(#_module.Term.K());
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.ks($LS($LZ), n#0), Tclass._module.Term());
        }
        else
        {
            assert $Is(n#0 - 1, Tclass._System.nat());
            ##n#1 := n#0 - 1;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#1, Tclass._System.nat(), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert 0 <= n#0 || ##n#1 == n#0;
            assert ##n#1 < n#0;
            assume _module.__default.ks#canCall(n#0 - 1);
            assume _module.__default.ks($LS($LZ), n#0)
               == #_module.Term.Apply(_module.__default.ks($LS($LZ), n#0 - 1), Lit(#_module.Term.K()));
            assume _module.__default.ks#canCall(n#0 - 1);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.ks($LS($LZ), n#0), Tclass._module.Term());
        }

        assert b$reqreads#0;
    }
}



procedure CheckWellformed$$_module.__default.VerificationTask3();
  free requires 18 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.VerificationTask3()
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var n#0: int;
  var ##n#0: int;
  var ##t#0: DatatypeType;

    // AddMethodImpl: VerificationTask3, CheckWellformed$$_module.__default.VerificationTask3
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "Combinators.dfy(445,6): initial state"} true;
    havoc $Heap;
    assume old($Heap) == $Heap;
    assume {:captureState "Combinators.dfy(446,10): post-state"} true;
    havoc n#0;
    assume LitInt(0) <= n#0;
    ##n#0 := n#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#0, Tclass._System.nat(), $Heap);
    assume _module.__default.ks#canCall(n#0);
    ##t#0 := _module.__default.ks($LS($LZ), n#0);
    // assume allocatedness for argument to function
    assume $IsAlloc(##t#0, Tclass._module.Term(), $Heap);
    assert {:subsumption 0} !_module.__default.ContainsS($LS($LS($LZ)), ##t#0);
    assume !_module.__default.ContainsS($LS($LZ), ##t#0);
    assume _module.__default.TerminatingReduction#canCall(_module.__default.ks($LS($LZ), n#0));
    assert LitInt(2) != 0;
    if (n#0 mod 2 == LitInt(0))
    {
    }
    else
    {
    }

    assume _module.__default.TerminatingReduction($LS($LZ), _module.__default.ks($LS($LZ), n#0))
       == (if n#0 mod 2 == LitInt(0)
         then #_module.Term.K()
         else #_module.Term.Apply(Lit(#_module.Term.K()), Lit(#_module.Term.K())));
    assume (forall n#1: int ::
      {:_induction n#1} { _module.__default.ks($LS($LZ), n#1) }
      LitInt(0) <= n#1
         ==> _module.__default.TerminatingReduction($LS($LZ), _module.__default.ks($LS($LZ), n#1))
           == (if n#1 mod 2 == LitInt(0)
             then #_module.Term.K()
             else #_module.Term.Apply(Lit(#_module.Term.K()), Lit(#_module.Term.K()))));
}



procedure Call$$_module.__default.VerificationTask3();
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall n#1: int ::
    { _module.__default.ks($LS($LZ), n#1) }
    LitInt(0) <= n#1
       ==> _module.__default.ks#canCall(n#1)
         && _module.__default.TerminatingReduction#canCall(_module.__default.ks($LS($LZ), n#1)));
  free ensures (forall n#1: int ::
    {:_induction n#1} { _module.__default.ks($LS($LZ), n#1) }
    LitInt(0) <= n#1
       ==> _module.__default.TerminatingReduction($LS($LZ), _module.__default.ks($LS($LZ), n#1))
         == (if n#1 mod 2 == LitInt(0)
           then #_module.Term.K()
           else #_module.Term.Apply(Lit(#_module.Term.K()), Lit(#_module.Term.K()))));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.VerificationTask3() returns ($_reverifyPost: bool);
  free requires 18 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall n#1: int ::
    { _module.__default.ks($LS($LZ), n#1) }
    LitInt(0) <= n#1
       ==> _module.__default.ks#canCall(n#1)
         && _module.__default.TerminatingReduction#canCall(_module.__default.ks($LS($LZ), n#1)));
  ensures (forall n#1: int ::
    { _module.__default.ks($LS($LS($LZ)), n#1) }
    LitInt(0) <= n#1
         && (forall n$ih#1#0: int ::
          { _module.__default.ks($LS($LZ), n$ih#1#0) }
          LitInt(0) <= n$ih#1#0
             ==>
            0 <= n$ih#1#0 && n$ih#1#0 < n#1
             ==> _module.__default.TerminatingReduction($LS($LZ), _module.__default.ks($LS($LZ), n$ih#1#0))
               == (if n$ih#1#0 mod 2 == LitInt(0)
                 then #_module.Term.K()
                 else #_module.Term.Apply(Lit(#_module.Term.K()), Lit(#_module.Term.K()))))
         && true
       ==> _module.__default.TerminatingReduction($LS($LS($LZ)), _module.__default.ks($LS($LS($LZ)), n#1))
         == (if n#1 mod 2 == LitInt(0)
           then #_module.Term.K()
           else #_module.Term.Apply(Lit(#_module.Term.K()), Lit(#_module.Term.K()))));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.VerificationTask3() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var n#2: int;
  var n##0: int;
  var $initHeapForallStmt#0: Heap;

    // AddMethodImpl: VerificationTask3, Impl$$_module.__default.VerificationTask3
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "Combinators.dfy(448,0): initial state"} true;
    $_reverifyPost := false;
    // ----- forall statement (call) ----- Combinators.dfy(449,3)
    if (*)
    {
        // Assume Fuel Constant
        havoc n#2;
        assume LitInt(0) <= n#2;
        assume true;
        assume true;
        // ----- call statement ----- Combinators.dfy(450,8)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        assert $Is(n#2, Tclass._System.nat());
        n##0 := n#2;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$_module.__default.VT3(n##0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "Combinators.dfy(450,10)"} true;
        assume false;
    }
    else
    {
        $initHeapForallStmt#0 := $Heap;
        havoc $Heap, $Tick;
        assume $initHeapForallStmt#0 == $Heap;
        assume (forall n#3: int ::
          { _module.__default.ks($LS($LZ), n#3) }
          LitInt(0) <= n#3 && Lit(true)
             ==> _module.__default.TerminatingReduction($LS($LZ), _module.__default.ks($LS($LZ), n#3))
               == (if n#3 mod 2 == LitInt(0)
                 then #_module.Term.K()
                 else #_module.Term.Apply(Lit(#_module.Term.K()), Lit(#_module.Term.K()))));
    }

    assume {:captureState "Combinators.dfy(451,2)"} true;
}



procedure {:_induction n#0} CheckWellformed$$_module.__default.VT3(n#0: int where LitInt(0) <= n#0);
  free requires 8 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:_induction n#0} CheckWellformed$$_module.__default.VT3(n#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##n#0: int;
  var ##t#0: DatatypeType;

    // AddMethodImpl: VT3, CheckWellformed$$_module.__default.VT3
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "Combinators.dfy(454,6): initial state"} true;
    havoc $Heap;
    assume old($Heap) == $Heap;
    assume {:captureState "Combinators.dfy(455,38): post-state"} true;
    assert $Is(n#0, Tclass._System.nat());
    ##n#0 := n#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#0, Tclass._System.nat(), $Heap);
    assume _module.__default.ks#canCall(n#0);
    ##t#0 := _module.__default.ks($LS($LZ), n#0);
    // assume allocatedness for argument to function
    assume $IsAlloc(##t#0, Tclass._module.Term(), $Heap);
    assert {:subsumption 0} !_module.__default.ContainsS($LS($LS($LZ)), ##t#0);
    assume !_module.__default.ContainsS($LS($LZ), ##t#0);
    assume _module.__default.TerminatingReduction#canCall(_module.__default.ks($LS($LZ), n#0));
    assert LitInt(2) != 0;
    if (n#0 mod 2 == LitInt(0))
    {
    }
    else
    {
    }

    assume _module.__default.TerminatingReduction($LS($LZ), _module.__default.ks($LS($LZ), n#0))
       == (if n#0 mod 2 == LitInt(0)
         then #_module.Term.K()
         else #_module.Term.Apply(Lit(#_module.Term.K()), Lit(#_module.Term.K())));
}



procedure {:_induction n#0} Call$$_module.__default.VT3(n#0: int where LitInt(0) <= n#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.ks#canCall(n#0)
     && _module.__default.TerminatingReduction#canCall(_module.__default.ks($LS($LZ), n#0));
  ensures _module.__default.TerminatingReduction($LS($LS($LZ)), _module.__default.ks($LS($LS($LZ)), n#0))
     == (if n#0 mod 2 == LitInt(0)
       then #_module.Term.K()
       else #_module.Term.Apply(Lit(#_module.Term.K()), Lit(#_module.Term.K())));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction n#0} Impl$$_module.__default.VT3(n#0: int where LitInt(0) <= n#0) returns ($_reverifyPost: bool);
  free requires 8 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.ks#canCall(n#0)
     && _module.__default.TerminatingReduction#canCall(_module.__default.ks($LS($LZ), n#0));
  ensures _module.__default.TerminatingReduction($LS($LS($LZ)), _module.__default.ks($LS($LS($LZ)), n#0))
     == (if n#0 mod 2 == LitInt(0)
       then #_module.Term.K()
       else #_module.Term.Apply(Lit(#_module.Term.K()), Lit(#_module.Term.K())));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction n#0} Impl$$_module.__default.VT3(n#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var p#0: int;
  var ##n#1: int;
  var ##t#1: DatatypeType;
  var ##n#2: int;

    // AddMethodImpl: VT3, Impl$$_module.__default.VT3
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "Combinators.dfy(456,0): initial state"} true;
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#n0#0: int ::
      LitInt(0) <= $ih#n0#0 && Lit(true) && 0 <= $ih#n0#0 && $ih#n0#0 < n#0
         ==> _module.__default.TerminatingReduction($LS($LZ), _module.__default.ks($LS($LZ), $ih#n0#0))
           == (if $ih#n0#0 mod 2 == LitInt(0)
             then #_module.Term.K()
             else #_module.Term.Apply(Lit(#_module.Term.K()), Lit(#_module.Term.K()))));
    $_reverifyPost := false;
    // ----- assert statement ----- Combinators.dfy(459,3)
    havoc p#0;
    // Begin Comprehension WF check
    if (LitInt(2) <= p#0)
    {
        assert $Is(p#0, Tclass._System.nat());
        ##n#1 := p#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##n#1, Tclass._System.nat(), $Heap);
        assume _module.__default.ks#canCall(p#0);
        ##t#1 := _module.__default.ks($LS($LZ), p#0);
        // assume allocatedness for argument to function
        assume $IsAlloc(##t#1, Tclass._module.Term(), $Heap);
        assume _module.__default.FindAndStep#canCall(_module.__default.ks($LS($LZ), p#0));
        assert $Is(p#0 - 2, Tclass._System.nat());
        ##n#2 := p#0 - 2;
        // assume allocatedness for argument to function
        assume $IsAlloc(##n#2, Tclass._System.nat(), $Heap);
        assume _module.__default.ks#canCall(p#0 - 2);
    }

    // End Comprehension WF check
    assume (forall p#1: int ::
      { _module.__default.FindAndStep($LS($LZ), _module.__default.ks($LS($LZ), p#1)) }
      LitInt(2) <= p#1
         ==> _module.__default.ks#canCall(p#1)
           && _module.__default.FindAndStep#canCall(_module.__default.ks($LS($LZ), p#1))
           && _module.__default.ks#canCall(p#1 - 2));
    assert {:subsumption 0} (forall p#1: int ::
      { _module.__default.FindAndStep($LS($LS($LZ)), _module.__default.ks($LS($LS($LZ)), p#1)) }
      (forall p$ih#0#0: int ::
            { _module.__default.FindAndStep($LS($LZ), _module.__default.ks($LS($LZ), p$ih#0#0)) }
            true
               ==>
              0 <= p$ih#0#0 && p$ih#0#0 < p#1
               ==>
              LitInt(2) <= p$ih#0#0
               ==> _module.__default.FindAndStep($LS($LZ), _module.__default.ks($LS($LZ), p$ih#0#0))
                 == _module.__default.ks($LS($LZ), p$ih#0#0 - 2))
           && true
         ==>
        LitInt(2) <= p#1
         ==> _module.__default.FindAndStep($LS($LS($LZ)), _module.__default.ks($LS($LS($LZ)), p#1))
           == _module.__default.ks($LS($LS($LZ)), p#1 - 2));
    assume (forall p#1: int ::
      {:matchinglooprewrite false} {:_induction p#1} { _module.__default.FindAndStep($LS($LZ), _module.__default.ks($LS($LZ), p#1)) }
      true
         ==>
        LitInt(2) <= p#1
         ==> _module.__default.FindAndStep($LS($LZ), _module.__default.ks($LS($LZ), p#1))
           == _module.__default.ks($LS($LZ), p#1 - 2));
}

