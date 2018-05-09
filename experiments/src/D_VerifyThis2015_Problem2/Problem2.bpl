// Dafny 2.0.0.00922 technical preview 0
// Command Line Options: /compile:0 /noVerify /print:Problem2.bpl Problem2.dfy

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

function Tclass._System.___hFunc5(Ty, Ty, Ty, Ty, Ty, Ty) : Ty;

// Tclass._System.___hFunc5 Tag
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$T4: Ty, #$R: Ty ::
  { Tclass._System.___hFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R) }
  Tag(Tclass._System.___hFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
     == Tagclass._System.___hFunc5);

const unique Tagclass._System.___hFunc5: TyTag;

// Tclass._System.___hFunc5 injectivity 0
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$T4: Ty, #$R: Ty ::
  { Tclass._System.___hFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R) }
  Tclass._System.___hFunc5_0(Tclass._System.___hFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
     == #$T0);

function Tclass._System.___hFunc5_0(Ty) : Ty;

// Tclass._System.___hFunc5 injectivity 1
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$T4: Ty, #$R: Ty ::
  { Tclass._System.___hFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R) }
  Tclass._System.___hFunc5_1(Tclass._System.___hFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
     == #$T1);

function Tclass._System.___hFunc5_1(Ty) : Ty;

// Tclass._System.___hFunc5 injectivity 2
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$T4: Ty, #$R: Ty ::
  { Tclass._System.___hFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R) }
  Tclass._System.___hFunc5_2(Tclass._System.___hFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
     == #$T2);

function Tclass._System.___hFunc5_2(Ty) : Ty;

// Tclass._System.___hFunc5 injectivity 3
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$T4: Ty, #$R: Ty ::
  { Tclass._System.___hFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R) }
  Tclass._System.___hFunc5_3(Tclass._System.___hFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
     == #$T3);

function Tclass._System.___hFunc5_3(Ty) : Ty;

// Tclass._System.___hFunc5 injectivity 4
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$T4: Ty, #$R: Ty ::
  { Tclass._System.___hFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R) }
  Tclass._System.___hFunc5_4(Tclass._System.___hFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
     == #$T4);

function Tclass._System.___hFunc5_4(Ty) : Ty;

// Tclass._System.___hFunc5 injectivity 5
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$T4: Ty, #$R: Ty ::
  { Tclass._System.___hFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R) }
  Tclass._System.___hFunc5_5(Tclass._System.___hFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
     == #$R);

function Tclass._System.___hFunc5_5(Ty) : Ty;

// Box/unbox axiom for Tclass._System.___hFunc5
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$T4: Ty, #$R: Ty, bx: Box ::
  { $IsBox(bx, Tclass._System.___hFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R)) }
  $IsBox(bx, Tclass._System.___hFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType,
        Tclass._System.___hFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R)));

function Handle5([Heap,Box,Box,Box,Box,Box]Box,
    [Heap,Box,Box,Box,Box,Box]bool,
    [Heap,Box,Box,Box,Box,Box]Set Box)
   : HandleType;

function Apply5(Ty, Ty, Ty, Ty, Ty, Ty, Heap, HandleType, Box, Box, Box, Box, Box) : Box;

function Requires5(Ty, Ty, Ty, Ty, Ty, Ty, Heap, HandleType, Box, Box, Box, Box, Box) : bool;

function Reads5(Ty, Ty, Ty, Ty, Ty, Ty, Heap, HandleType, Box, Box, Box, Box, Box) : Set Box;

axiom (forall t0: Ty,
    t1: Ty,
    t2: Ty,
    t3: Ty,
    t4: Ty,
    t5: Ty,
    heap: Heap,
    h: [Heap,Box,Box,Box,Box,Box]Box,
    r: [Heap,Box,Box,Box,Box,Box]bool,
    rd: [Heap,Box,Box,Box,Box,Box]Set Box,
    bx0: Box,
    bx1: Box,
    bx2: Box,
    bx3: Box,
    bx4: Box ::
  { Apply5(t0, t1, t2, t3, t4, t5, heap, Handle5(h, r, rd), bx0, bx1, bx2, bx3, bx4) }
  Apply5(t0, t1, t2, t3, t4, t5, heap, Handle5(h, r, rd), bx0, bx1, bx2, bx3, bx4)
     == h[heap, bx0, bx1, bx2, bx3, bx4]);

axiom (forall t0: Ty,
    t1: Ty,
    t2: Ty,
    t3: Ty,
    t4: Ty,
    t5: Ty,
    heap: Heap,
    h: [Heap,Box,Box,Box,Box,Box]Box,
    r: [Heap,Box,Box,Box,Box,Box]bool,
    rd: [Heap,Box,Box,Box,Box,Box]Set Box,
    bx0: Box,
    bx1: Box,
    bx2: Box,
    bx3: Box,
    bx4: Box ::
  { Requires5(t0, t1, t2, t3, t4, t5, heap, Handle5(h, r, rd), bx0, bx1, bx2, bx3, bx4) }
  r[heap, bx0, bx1, bx2, bx3, bx4]
     ==> Requires5(t0, t1, t2, t3, t4, t5, heap, Handle5(h, r, rd), bx0, bx1, bx2, bx3, bx4));

axiom (forall t0: Ty,
    t1: Ty,
    t2: Ty,
    t3: Ty,
    t4: Ty,
    t5: Ty,
    heap: Heap,
    h: [Heap,Box,Box,Box,Box,Box]Box,
    r: [Heap,Box,Box,Box,Box,Box]bool,
    rd: [Heap,Box,Box,Box,Box,Box]Set Box,
    bx0: Box,
    bx1: Box,
    bx2: Box,
    bx3: Box,
    bx4: Box,
    bx: Box ::
  { Reads5(t0, t1, t2, t3, t4, t5, heap, Handle5(h, r, rd), bx0, bx1, bx2, bx3, bx4)[bx] }
  Reads5(t0, t1, t2, t3, t4, t5, heap, Handle5(h, r, rd), bx0, bx1, bx2, bx3, bx4)[bx]
     == rd[heap, bx0, bx1, bx2, bx3, bx4][bx]);

function {:inline} Requires5#canCall(t0: Ty,
    t1: Ty,
    t2: Ty,
    t3: Ty,
    t4: Ty,
    t5: Ty,
    heap: Heap,
    f: HandleType,
    bx0: Box,
    bx1: Box,
    bx2: Box,
    bx3: Box,
    bx4: Box)
   : bool
{
  true
}

function {:inline} Reads5#canCall(t0: Ty,
    t1: Ty,
    t2: Ty,
    t3: Ty,
    t4: Ty,
    t5: Ty,
    heap: Heap,
    f: HandleType,
    bx0: Box,
    bx1: Box,
    bx2: Box,
    bx3: Box,
    bx4: Box)
   : bool
{
  true
}

// frame axiom for Reads5
axiom (forall t0: Ty,
    t1: Ty,
    t2: Ty,
    t3: Ty,
    t4: Ty,
    t5: Ty,
    h0: Heap,
    h1: Heap,
    f: HandleType,
    bx0: Box,
    bx1: Box,
    bx2: Box,
    bx3: Box,
    bx4: Box ::
  { $HeapSucc(h0, h1), Reads5(t0, t1, t2, t3, t4, t5, h1, f, bx0, bx1, bx2, bx3, bx4) }
  $HeapSucc(h0, h1)
       &&
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       &&
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $IsBox(bx3, t3)
       && $IsBox(bx4, t4)
       && $Is(f, Tclass._System.___hFunc5(t0, t1, t2, t3, t4, t5))
       && (forall<a> o: ref, fld: Field a ::
        o != null
             && Reads5(t0, t1, t2, t3, t4, t5, h0, f, bx0, bx1, bx2, bx3, bx4)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Reads5(t0, t1, t2, t3, t4, t5, h0, f, bx0, bx1, bx2, bx3, bx4)
       == Reads5(t0, t1, t2, t3, t4, t5, h1, f, bx0, bx1, bx2, bx3, bx4));

// frame axiom for Reads5
axiom (forall t0: Ty,
    t1: Ty,
    t2: Ty,
    t3: Ty,
    t4: Ty,
    t5: Ty,
    h0: Heap,
    h1: Heap,
    f: HandleType,
    bx0: Box,
    bx1: Box,
    bx2: Box,
    bx3: Box,
    bx4: Box ::
  { $HeapSucc(h0, h1), Reads5(t0, t1, t2, t3, t4, t5, h1, f, bx0, bx1, bx2, bx3, bx4) }
  $HeapSucc(h0, h1)
       &&
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       &&
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $IsBox(bx3, t3)
       && $IsBox(bx4, t4)
       && $Is(f, Tclass._System.___hFunc5(t0, t1, t2, t3, t4, t5))
       && (forall<a> o: ref, fld: Field a ::
        o != null
             && Reads5(t0, t1, t2, t3, t4, t5, h1, f, bx0, bx1, bx2, bx3, bx4)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Reads5(t0, t1, t2, t3, t4, t5, h0, f, bx0, bx1, bx2, bx3, bx4)
       == Reads5(t0, t1, t2, t3, t4, t5, h1, f, bx0, bx1, bx2, bx3, bx4));

// frame axiom for Requires5
axiom (forall t0: Ty,
    t1: Ty,
    t2: Ty,
    t3: Ty,
    t4: Ty,
    t5: Ty,
    h0: Heap,
    h1: Heap,
    f: HandleType,
    bx0: Box,
    bx1: Box,
    bx2: Box,
    bx3: Box,
    bx4: Box ::
  { $HeapSucc(h0, h1), Requires5(t0, t1, t2, t3, t4, t5, h1, f, bx0, bx1, bx2, bx3, bx4) }
  $HeapSucc(h0, h1)
       &&
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       &&
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $IsBox(bx3, t3)
       && $IsBox(bx4, t4)
       && $Is(f, Tclass._System.___hFunc5(t0, t1, t2, t3, t4, t5))
       && (forall<a> o: ref, fld: Field a ::
        o != null
             && Reads5(t0, t1, t2, t3, t4, t5, h0, f, bx0, bx1, bx2, bx3, bx4)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Requires5(t0, t1, t2, t3, t4, t5, h0, f, bx0, bx1, bx2, bx3, bx4)
       == Requires5(t0, t1, t2, t3, t4, t5, h1, f, bx0, bx1, bx2, bx3, bx4));

// frame axiom for Requires5
axiom (forall t0: Ty,
    t1: Ty,
    t2: Ty,
    t3: Ty,
    t4: Ty,
    t5: Ty,
    h0: Heap,
    h1: Heap,
    f: HandleType,
    bx0: Box,
    bx1: Box,
    bx2: Box,
    bx3: Box,
    bx4: Box ::
  { $HeapSucc(h0, h1), Requires5(t0, t1, t2, t3, t4, t5, h1, f, bx0, bx1, bx2, bx3, bx4) }
  $HeapSucc(h0, h1)
       &&
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       &&
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $IsBox(bx3, t3)
       && $IsBox(bx4, t4)
       && $Is(f, Tclass._System.___hFunc5(t0, t1, t2, t3, t4, t5))
       && (forall<a> o: ref, fld: Field a ::
        o != null
             && Reads5(t0, t1, t2, t3, t4, t5, h1, f, bx0, bx1, bx2, bx3, bx4)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Requires5(t0, t1, t2, t3, t4, t5, h0, f, bx0, bx1, bx2, bx3, bx4)
       == Requires5(t0, t1, t2, t3, t4, t5, h1, f, bx0, bx1, bx2, bx3, bx4));

// frame axiom for Apply5
axiom (forall t0: Ty,
    t1: Ty,
    t2: Ty,
    t3: Ty,
    t4: Ty,
    t5: Ty,
    h0: Heap,
    h1: Heap,
    f: HandleType,
    bx0: Box,
    bx1: Box,
    bx2: Box,
    bx3: Box,
    bx4: Box ::
  { $HeapSucc(h0, h1), Apply5(t0, t1, t2, t3, t4, t5, h1, f, bx0, bx1, bx2, bx3, bx4) }
  $HeapSucc(h0, h1)
       &&
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       &&
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $IsBox(bx3, t3)
       && $IsBox(bx4, t4)
       && $Is(f, Tclass._System.___hFunc5(t0, t1, t2, t3, t4, t5))
       && (forall<a> o: ref, fld: Field a ::
        o != null
             && Reads5(t0, t1, t2, t3, t4, t5, h0, f, bx0, bx1, bx2, bx3, bx4)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Apply5(t0, t1, t2, t3, t4, t5, h0, f, bx0, bx1, bx2, bx3, bx4)
       == Apply5(t0, t1, t2, t3, t4, t5, h1, f, bx0, bx1, bx2, bx3, bx4));

// frame axiom for Apply5
axiom (forall t0: Ty,
    t1: Ty,
    t2: Ty,
    t3: Ty,
    t4: Ty,
    t5: Ty,
    h0: Heap,
    h1: Heap,
    f: HandleType,
    bx0: Box,
    bx1: Box,
    bx2: Box,
    bx3: Box,
    bx4: Box ::
  { $HeapSucc(h0, h1), Apply5(t0, t1, t2, t3, t4, t5, h1, f, bx0, bx1, bx2, bx3, bx4) }
  $HeapSucc(h0, h1)
       &&
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       &&
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $IsBox(bx3, t3)
       && $IsBox(bx4, t4)
       && $Is(f, Tclass._System.___hFunc5(t0, t1, t2, t3, t4, t5))
       && (forall<a> o: ref, fld: Field a ::
        o != null
             && Reads5(t0, t1, t2, t3, t4, t5, h1, f, bx0, bx1, bx2, bx3, bx4)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Apply5(t0, t1, t2, t3, t4, t5, h0, f, bx0, bx1, bx2, bx3, bx4)
       == Apply5(t0, t1, t2, t3, t4, t5, h1, f, bx0, bx1, bx2, bx3, bx4));

// empty-reads property for Reads5
axiom (forall t0: Ty,
    t1: Ty,
    t2: Ty,
    t3: Ty,
    t4: Ty,
    t5: Ty,
    heap: Heap,
    f: HandleType,
    bx0: Box,
    bx1: Box,
    bx2: Box,
    bx3: Box,
    bx4: Box ::
  { Reads5(t0, t1, t2, t3, t4, t5, $OneHeap, f, bx0, bx1, bx2, bx3, bx4), $IsGoodHeap(heap) }
    { Reads5(t0, t1, t2, t3, t4, t5, heap, f, bx0, bx1, bx2, bx3, bx4) }
  $IsGoodHeap(heap)
       &&
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $IsBox(bx3, t3)
       && $IsBox(bx4, t4)
       && $Is(f, Tclass._System.___hFunc5(t0, t1, t2, t3, t4, t5))
     ==> (Set#Equal(Reads5(t0, t1, t2, t3, t4, t5, $OneHeap, f, bx0, bx1, bx2, bx3, bx4),
        Set#Empty(): Set Box)
       <==> Set#Equal(Reads5(t0, t1, t2, t3, t4, t5, heap, f, bx0, bx1, bx2, bx3, bx4),
        Set#Empty(): Set Box)));

// empty-reads property for Requires5
axiom (forall t0: Ty,
    t1: Ty,
    t2: Ty,
    t3: Ty,
    t4: Ty,
    t5: Ty,
    heap: Heap,
    f: HandleType,
    bx0: Box,
    bx1: Box,
    bx2: Box,
    bx3: Box,
    bx4: Box ::
  { Requires5(t0, t1, t2, t3, t4, t5, $OneHeap, f, bx0, bx1, bx2, bx3, bx4), $IsGoodHeap(heap) }
    { Requires5(t0, t1, t2, t3, t4, t5, heap, f, bx0, bx1, bx2, bx3, bx4) }
  $IsGoodHeap(heap)
       &&
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $IsBox(bx3, t3)
       && $IsBox(bx4, t4)
       && $Is(f, Tclass._System.___hFunc5(t0, t1, t2, t3, t4, t5))
       && Set#Equal(Reads5(t0, t1, t2, t3, t4, t5, $OneHeap, f, bx0, bx1, bx2, bx3, bx4),
        Set#Empty(): Set Box)
     ==> Requires5(t0, t1, t2, t3, t4, t5, $OneHeap, f, bx0, bx1, bx2, bx3, bx4)
       == Requires5(t0, t1, t2, t3, t4, t5, heap, f, bx0, bx1, bx2, bx3, bx4));

axiom (forall f: HandleType, t0: Ty, t1: Ty, t2: Ty, t3: Ty, t4: Ty, t5: Ty ::
  { $Is(f, Tclass._System.___hFunc5(t0, t1, t2, t3, t4, t5)) }
  $Is(f, Tclass._System.___hFunc5(t0, t1, t2, t3, t4, t5))
     <==> (forall h: Heap, bx0: Box, bx1: Box, bx2: Box, bx3: Box, bx4: Box ::
      { Apply5(t0, t1, t2, t3, t4, t5, h, f, bx0, bx1, bx2, bx3, bx4) }
      $IsGoodHeap(h)
           &&
          $IsBox(bx0, t0)
           && $IsBox(bx1, t1)
           && $IsBox(bx2, t2)
           && $IsBox(bx3, t3)
           && $IsBox(bx4, t4)
           && Requires5(t0, t1, t2, t3, t4, t5, h, f, bx0, bx1, bx2, bx3, bx4)
         ==> $IsBox(Apply5(t0, t1, t2, t3, t4, t5, h, f, bx0, bx1, bx2, bx3, bx4), t5)));

axiom (forall f: HandleType,
    t0: Ty,
    t1: Ty,
    t2: Ty,
    t3: Ty,
    t4: Ty,
    t5: Ty,
    u0: Ty,
    u1: Ty,
    u2: Ty,
    u3: Ty,
    u4: Ty,
    u5: Ty ::
  { $Is(f, Tclass._System.___hFunc5(t0, t1, t2, t3, t4, t5)), $Is(f, Tclass._System.___hFunc5(u0, u1, u2, u3, u4, u5)) }
  $Is(f, Tclass._System.___hFunc5(t0, t1, t2, t3, t4, t5))
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
        { $IsBox(bx, u3) } { $IsBox(bx, t3) }
        $IsBox(bx, u3) ==> $IsBox(bx, t3))
       && (forall bx: Box ::
        { $IsBox(bx, u4) } { $IsBox(bx, t4) }
        $IsBox(bx, u4) ==> $IsBox(bx, t4))
       && (forall bx: Box ::
        { $IsBox(bx, t5) } { $IsBox(bx, u5) }
        $IsBox(bx, t5) ==> $IsBox(bx, u5))
     ==> $Is(f, Tclass._System.___hFunc5(u0, u1, u2, u3, u4, u5)));

axiom (forall f: HandleType, t0: Ty, t1: Ty, t2: Ty, t3: Ty, t4: Ty, t5: Ty, h: Heap ::
  { $IsAlloc(f, Tclass._System.___hFunc5(t0, t1, t2, t3, t4, t5), h) }
  $IsGoodHeap(h)
     ==> ($IsAlloc(f, Tclass._System.___hFunc5(t0, t1, t2, t3, t4, t5), h)
       <==> (forall bx0: Box, bx1: Box, bx2: Box, bx3: Box, bx4: Box ::
        { Apply5(t0, t1, t2, t3, t4, t5, h, f, bx0, bx1, bx2, bx3, bx4) }
          { Reads5(t0, t1, t2, t3, t4, t5, h, f, bx0, bx1, bx2, bx3, bx4) }
        $IsBox(bx0, t0)
             && $IsAllocBox(bx0, t0, h)
             &&
            $IsBox(bx1, t1)
             && $IsAllocBox(bx1, t1, h)
             &&
            $IsBox(bx2, t2)
             && $IsAllocBox(bx2, t2, h)
             &&
            $IsBox(bx3, t3)
             && $IsAllocBox(bx3, t3, h)
             &&
            $IsBox(bx4, t4)
             && $IsAllocBox(bx4, t4, h)
             && Requires5(t0, t1, t2, t3, t4, t5, h, f, bx0, bx1, bx2, bx3, bx4)
           ==> (forall r: ref ::
            { Reads5(t0, t1, t2, t3, t4, t5, h, f, bx0, bx1, bx2, bx3, bx4)[$Box(r)] }
            r != null
                 && Reads5(t0, t1, t2, t3, t4, t5, h, f, bx0, bx1, bx2, bx3, bx4)[$Box(r)]
               ==> read(h, r, alloc)))));

axiom (forall f: HandleType, t0: Ty, t1: Ty, t2: Ty, t3: Ty, t4: Ty, t5: Ty, h: Heap ::
  { $IsAlloc(f, Tclass._System.___hFunc5(t0, t1, t2, t3, t4, t5), h) }
  $IsGoodHeap(h)
       && $IsAlloc(f, Tclass._System.___hFunc5(t0, t1, t2, t3, t4, t5), h)
     ==> (forall bx0: Box, bx1: Box, bx2: Box, bx3: Box, bx4: Box ::
      { Apply5(t0, t1, t2, t3, t4, t5, h, f, bx0, bx1, bx2, bx3, bx4) }
      $IsAllocBox(bx0, t0, h)
           && $IsAllocBox(bx1, t1, h)
           && $IsAllocBox(bx2, t2, h)
           && $IsAllocBox(bx3, t3, h)
           && $IsAllocBox(bx4, t4, h)
           && Requires5(t0, t1, t2, t3, t4, t5, h, f, bx0, bx1, bx2, bx3, bx4)
         ==> $IsAllocBox(Apply5(t0, t1, t2, t3, t4, t5, h, f, bx0, bx1, bx2, bx3, bx4), t5, h)));

function Tclass._System.___hPartialFunc5(Ty, Ty, Ty, Ty, Ty, Ty) : Ty;

// Tclass._System.___hPartialFunc5 Tag
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$T4: Ty, #$R: Ty ::
  { Tclass._System.___hPartialFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R) }
  Tag(Tclass._System.___hPartialFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
     == Tagclass._System.___hPartialFunc5);

const unique Tagclass._System.___hPartialFunc5: TyTag;

// Tclass._System.___hPartialFunc5 injectivity 0
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$T4: Ty, #$R: Ty ::
  { Tclass._System.___hPartialFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R) }
  Tclass._System.___hPartialFunc5_0(Tclass._System.___hPartialFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
     == #$T0);

function Tclass._System.___hPartialFunc5_0(Ty) : Ty;

// Tclass._System.___hPartialFunc5 injectivity 1
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$T4: Ty, #$R: Ty ::
  { Tclass._System.___hPartialFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R) }
  Tclass._System.___hPartialFunc5_1(Tclass._System.___hPartialFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
     == #$T1);

function Tclass._System.___hPartialFunc5_1(Ty) : Ty;

// Tclass._System.___hPartialFunc5 injectivity 2
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$T4: Ty, #$R: Ty ::
  { Tclass._System.___hPartialFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R) }
  Tclass._System.___hPartialFunc5_2(Tclass._System.___hPartialFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
     == #$T2);

function Tclass._System.___hPartialFunc5_2(Ty) : Ty;

// Tclass._System.___hPartialFunc5 injectivity 3
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$T4: Ty, #$R: Ty ::
  { Tclass._System.___hPartialFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R) }
  Tclass._System.___hPartialFunc5_3(Tclass._System.___hPartialFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
     == #$T3);

function Tclass._System.___hPartialFunc5_3(Ty) : Ty;

// Tclass._System.___hPartialFunc5 injectivity 4
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$T4: Ty, #$R: Ty ::
  { Tclass._System.___hPartialFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R) }
  Tclass._System.___hPartialFunc5_4(Tclass._System.___hPartialFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
     == #$T4);

function Tclass._System.___hPartialFunc5_4(Ty) : Ty;

// Tclass._System.___hPartialFunc5 injectivity 5
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$T4: Ty, #$R: Ty ::
  { Tclass._System.___hPartialFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R) }
  Tclass._System.___hPartialFunc5_5(Tclass._System.___hPartialFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
     == #$R);

function Tclass._System.___hPartialFunc5_5(Ty) : Ty;

// Box/unbox axiom for Tclass._System.___hPartialFunc5
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$T4: Ty, #$R: Ty, bx: Box ::
  { $IsBox(bx, Tclass._System.___hPartialFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R)) }
  $IsBox(bx, Tclass._System.___hPartialFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType,
        Tclass._System.___hPartialFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R)));

// _System._#PartialFunc5: subset type $Is
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$T4: Ty, #$R: Ty, f#0: HandleType ::
  { $Is(f#0, Tclass._System.___hPartialFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R)) }
  $Is(f#0, Tclass._System.___hPartialFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
     <==> $Is(f#0, Tclass._System.___hFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
       && (forall x0#0: Box, x1#0: Box, x2#0: Box, x3#0: Box, x4#0: Box ::
        $IsBox(x0#0, #$T0)
             && $IsBox(x1#0, #$T1)
             && $IsBox(x2#0, #$T2)
             && $IsBox(x3#0, #$T3)
             && $IsBox(x4#0, #$T4)
           ==> Set#Equal(Reads5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R, $OneHeap, f#0, x0#0, x1#0, x2#0, x3#0, x4#0),
            Set#Empty(): Set Box)));

// _System._#PartialFunc5: subset type $IsAlloc
axiom (forall #$T0: Ty,
    #$T1: Ty,
    #$T2: Ty,
    #$T3: Ty,
    #$T4: Ty,
    #$R: Ty,
    f#0: HandleType,
    $h: Heap ::
  { $IsAlloc(f#0, Tclass._System.___hPartialFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R), $h) }
  $IsAlloc(f#0, Tclass._System.___hPartialFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R), $h)
     <==> $IsAlloc(f#0, Tclass._System.___hFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R), $h));

function Tclass._System.___hTotalFunc5(Ty, Ty, Ty, Ty, Ty, Ty) : Ty;

// Tclass._System.___hTotalFunc5 Tag
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$T4: Ty, #$R: Ty ::
  { Tclass._System.___hTotalFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R) }
  Tag(Tclass._System.___hTotalFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
     == Tagclass._System.___hTotalFunc5);

const unique Tagclass._System.___hTotalFunc5: TyTag;

// Tclass._System.___hTotalFunc5 injectivity 0
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$T4: Ty, #$R: Ty ::
  { Tclass._System.___hTotalFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R) }
  Tclass._System.___hTotalFunc5_0(Tclass._System.___hTotalFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
     == #$T0);

function Tclass._System.___hTotalFunc5_0(Ty) : Ty;

// Tclass._System.___hTotalFunc5 injectivity 1
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$T4: Ty, #$R: Ty ::
  { Tclass._System.___hTotalFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R) }
  Tclass._System.___hTotalFunc5_1(Tclass._System.___hTotalFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
     == #$T1);

function Tclass._System.___hTotalFunc5_1(Ty) : Ty;

// Tclass._System.___hTotalFunc5 injectivity 2
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$T4: Ty, #$R: Ty ::
  { Tclass._System.___hTotalFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R) }
  Tclass._System.___hTotalFunc5_2(Tclass._System.___hTotalFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
     == #$T2);

function Tclass._System.___hTotalFunc5_2(Ty) : Ty;

// Tclass._System.___hTotalFunc5 injectivity 3
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$T4: Ty, #$R: Ty ::
  { Tclass._System.___hTotalFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R) }
  Tclass._System.___hTotalFunc5_3(Tclass._System.___hTotalFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
     == #$T3);

function Tclass._System.___hTotalFunc5_3(Ty) : Ty;

// Tclass._System.___hTotalFunc5 injectivity 4
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$T4: Ty, #$R: Ty ::
  { Tclass._System.___hTotalFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R) }
  Tclass._System.___hTotalFunc5_4(Tclass._System.___hTotalFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
     == #$T4);

function Tclass._System.___hTotalFunc5_4(Ty) : Ty;

// Tclass._System.___hTotalFunc5 injectivity 5
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$T4: Ty, #$R: Ty ::
  { Tclass._System.___hTotalFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R) }
  Tclass._System.___hTotalFunc5_5(Tclass._System.___hTotalFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
     == #$R);

function Tclass._System.___hTotalFunc5_5(Ty) : Ty;

// Box/unbox axiom for Tclass._System.___hTotalFunc5
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$T4: Ty, #$R: Ty, bx: Box ::
  { $IsBox(bx, Tclass._System.___hTotalFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R)) }
  $IsBox(bx, Tclass._System.___hTotalFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType,
        Tclass._System.___hTotalFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R)));

// _System._#TotalFunc5: subset type $Is
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$T4: Ty, #$R: Ty, f#0: HandleType ::
  { $Is(f#0, Tclass._System.___hTotalFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R)) }
  $Is(f#0, Tclass._System.___hTotalFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
     <==> $Is(f#0, Tclass._System.___hPartialFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
       && (forall x0#0: Box, x1#0: Box, x2#0: Box, x3#0: Box, x4#0: Box ::
        $IsBox(x0#0, #$T0)
             && $IsBox(x1#0, #$T1)
             && $IsBox(x2#0, #$T2)
             && $IsBox(x3#0, #$T3)
             && $IsBox(x4#0, #$T4)
           ==> Requires5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R, $OneHeap, f#0, x0#0, x1#0, x2#0, x3#0, x4#0)));

// _System._#TotalFunc5: subset type $IsAlloc
axiom (forall #$T0: Ty,
    #$T1: Ty,
    #$T2: Ty,
    #$T3: Ty,
    #$T4: Ty,
    #$R: Ty,
    f#0: HandleType,
    $h: Heap ::
  { $IsAlloc(f#0, Tclass._System.___hTotalFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R), $h) }
  $IsAlloc(f#0, Tclass._System.___hTotalFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R), $h)
     <==> $IsAlloc(f#0, Tclass._System.___hPartialFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R), $h));

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

const BaseFuel__module._default.Divides: LayerType;

const StartFuel__module._default.Divides: LayerType;

const StartFuelAssert__module._default.Divides: LayerType;

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

procedure CheckWellformed$$_module.__default.SequentialGcd(A#0: int, B#0: int) returns (gcd#0: int);
  free requires 15 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.SequentialGcd(A#0: int, B#0: int) returns (gcd#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##a#0: int;
  var ##b#0: int;

    // AddMethodImpl: SequentialGcd, CheckWellformed$$_module.__default.SequentialGcd
    // initialize fuel constant
    assume AsFuelBottom(StartFuel__module._default.Divides)
       == StartFuel__module._default.Divides;
    assume AsFuelBottom(StartFuelAssert__module._default.Divides)
       == StartFuelAssert__module._default.Divides;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "Problem2.dfy(9,7): initial state"} true;
    assume A#0 > 0;
    assume B#0 > 0;
    havoc $Heap;
    assume (forall<alpha> $o: ref, $f: Field alpha ::
      { read($Heap, $o, $f) }
      $o != null && read(old($Heap), $o, alloc)
         ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
    assume $HeapSucc(old($Heap), $Heap);
    havoc gcd#0;
    assume {:captureState "Problem2.dfy(11,14): post-state"} true;
    ##a#0 := A#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##a#0, TInt, $Heap);
    ##b#0 := B#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##b#0, TInt, $Heap);
    assert {:subsumption 0} ##a#0 > 0;
    assert {:subsumption 0} ##b#0 > 0;
    assume ##a#0 > 0 && ##b#0 > 0;
    assume _module.__default.Gcd#canCall(A#0, B#0);
    assume gcd#0 == _module.__default.Gcd(A#0, B#0);
}



procedure Call$$_module.__default.SequentialGcd(A#0: int, B#0: int) returns (gcd#0: int);
  // user-defined preconditions
  requires A#0 > 0;
  requires B#0 > 0;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Gcd#canCall(A#0, B#0);
  ensures gcd#0 == _module.__default.Gcd(A#0, B#0);
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.SequentialGcd(A#0: int, B#0: int) returns (gcd#0: int, $_reverifyPost: bool);
  free requires 15 == $FunctionContextHeight;
  // user-defined preconditions
  requires A#0 > 0;
  requires B#0 > 0;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Gcd#canCall(A#0, B#0);
  ensures gcd#0 == _module.__default.Gcd(A#0, B#0);
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.SequentialGcd(A#0: int, B#0: int) returns (gcd#0: int, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var a#0: int;
  var b#0: int;
  var $rhs#0: int;
  var $rhs#1: int;
  var $PreLoopHeap$loop#0: Heap;
  var $decr_init$loop#00: int;
  var $w$loop#0: bool;
  var ##a#1: int;
  var ##b#1: int;
  var ##a#2: int;
  var ##b#2: int;
  var $decr$loop#00: int;
  var ##a#0_0_0_0: int;
  var ##b#0_0_0_0: int;
  var a##0_0_0_0: int;
  var b##0_0_0_0: int;
  var ##a#0_0_0_1: int;
  var ##b#0_0_0_1: int;
  var ##a#0_0_1_0: int;
  var ##b#0_0_1_0: int;
  var a##0_0_1_0: int;
  var b##0_0_1_0: int;
  var ##a#0_0_1_1: int;
  var ##b#0_0_1_1: int;
  var ##a#0_0_2_0: int;
  var ##b#0_0_2_0: int;
  var a##0_0_2_0: int;
  var b##0_0_2_0: int;
  var ##a#0_0_2_1: int;
  var ##b#0_0_2_1: int;
  var ##a#0_0_0: int;
  var ##b#0_0_0: int;
  var a##1_0: int;
  var b##1_0: int;
  var a##0: int;

    // AddMethodImpl: SequentialGcd, Impl$$_module.__default.SequentialGcd
    // initialize fuel constant
    assume AsFuelBottom(StartFuel__module._default.Divides)
       == StartFuel__module._default.Divides;
    assume AsFuelBottom(StartFuelAssert__module._default.Divides)
       == StartFuelAssert__module._default.Divides;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "Problem2.dfy(12,0): initial state"} true;
    $_reverifyPost := false;
    // ----- update statement ----- Problem2.dfy(13,12)
    assume true;
    assume true;
    assume true;
    $rhs#0 := A#0;
    assume true;
    $rhs#1 := B#0;
    a#0 := $rhs#0;
    b#0 := $rhs#1;
    assume {:captureState "Problem2.dfy(13,18)"} true;
    // ----- alternative loop statement ----- Problem2.dfy(14,3)
    $PreLoopHeap$loop#0 := $Heap;
    $decr_init$loop#00 := a#0 + b#0;
    havoc $w$loop#0;
    while (true)
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0 ==> 0 < a#0;
      invariant $w$loop#0 ==> 0 < b#0;
      free invariant $w$loop#0
         ==> _module.__default.Gcd#canCall(A#0, B#0)
           && _module.__default.Gcd#canCall(a#0, b#0);
      invariant $w$loop#0 ==> _module.__default.Gcd(A#0, B#0) == _module.__default.Gcd(a#0, b#0);
      free invariant (forall<alpha> $o: ref, $f: Field alpha ::
        { read($Heap, $o, $f) }
        $o != null && read(old($Heap), $o, alloc)
           ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0, $o, $f));
      free invariant $HeapSucc($PreLoopHeap$loop#0, $Heap);
      free invariant (forall<alpha> $o: ref, $f: Field alpha ::
        { read($Heap, $o, $f) }
        $o != null && read($PreLoopHeap$loop#0, $o, alloc)
           ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0, $o, $f) || $_Frame[$o, $f]);
      free invariant a#0 + b#0 <= $decr_init$loop#00 && (a#0 + b#0 == $decr_init$loop#00 ==> true);
    {
        assume {:captureState "Problem2.dfy(14,2): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            if (0 < a#0)
            {
            }

            assume true;
            assume 0 < a#0 && 0 < b#0;
            ##a#1 := A#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##a#1, TInt, $Heap);
            ##b#1 := B#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##b#1, TInt, $Heap);
            assert {:subsumption 0} ##a#1 > 0;
            assert {:subsumption 0} ##b#1 > 0;
            assume _module.__default.Gcd#canCall(A#0, B#0);
            ##a#2 := a#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##a#2, TInt, $Heap);
            ##b#2 := b#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##b#2, TInt, $Heap);
            assert {:subsumption 0} ##a#2 > 0;
            assert {:subsumption 0} ##b#2 > 0;
            assume _module.__default.Gcd#canCall(a#0, b#0);
            assume _module.__default.Gcd#canCall(A#0, B#0)
               && _module.__default.Gcd#canCall(a#0, b#0);
            assume _module.__default.Gcd(A#0, B#0) == _module.__default.Gcd(a#0, b#0);
            assume true;
            assume false;
        }

        assume true;
        if (!Lit(true))
        {
            break;
        }

        $decr$loop#00 := a#0 + b#0;
        if (*)
        {
            assume true;
            assume a#0 > b#0;
            // ----- call statement ----- Problem2.dfy(20,18)
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            // ProcessCallStmt: CheckSubrange
            a##1_0 := a#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            b##1_0 := b#0;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call Call$$_module.__default.GcdDecrease(a##1_0, b##1_0);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "Problem2.dfy(20,23)"} true;
            // ----- assignment statement ----- Problem2.dfy(21,9)
            assume true;
            assume true;
            a#0 := a#0 - b#0;
            assume {:captureState "Problem2.dfy(21,16)"} true;
        }
        else if (*)
        {
            assume true;
            assume b#0 > a#0;
            // ----- calc statement ----- Problem2.dfy(23,7)
            // Assume Fuel Constant
            if (*)
            {
                // ----- assert wf[initial] ----- Problem2.dfy(23,7)
                ##a#0_0_0 := a#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##a#0_0_0, TInt, $Heap);
                ##b#0_0_0 := b#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##b#0_0_0, TInt, $Heap);
                assert {:subsumption 0} ##a#0_0_0 > 0;
                assert {:subsumption 0} ##b#0_0_0 > 0;
                assume _module.__default.Gcd#canCall(a#0, b#0);
                assume _module.__default.Gcd#canCall(a#0, b#0);
                assume false;
            }
            else if (*)
            {
                // ----- assume wf[lhs] ----- Problem2.dfy(23,7)
                ##a#0_0_2_0 := a#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##a#0_0_2_0, TInt, $Heap);
                ##b#0_0_2_0 := b#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##b#0_0_2_0, TInt, $Heap);
                assume {:subsumption 0} ##a#0_0_2_0 > 0;
                assume {:subsumption 0} ##b#0_0_2_0 > 0;
                assume _module.__default.Gcd#canCall(a#0, b#0);
                assume _module.__default.Gcd#canCall(a#0, b#0);
                // ----- Hint0 ----- Problem2.dfy(23,7)
                // ----- call statement ----- Problem2.dfy(25,19)
                // TrCallStmt: Before ProcessCallStmt
                assume true;
                // ProcessCallStmt: CheckSubrange
                a##0_0_2_0 := a#0;
                assume true;
                // ProcessCallStmt: CheckSubrange
                b##0_0_2_0 := b#0;
                assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                // ProcessCallStmt: Make the call
                call Call$$_module.__default.Symmetry(a##0_0_2_0, b##0_0_2_0);
                // TrCallStmt: After ProcessCallStmt
                assume {:captureState "Problem2.dfy(25,24)"} true;
                // ----- assert wf[rhs] ----- Problem2.dfy(23,7)
                ##a#0_0_2_1 := b#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##a#0_0_2_1, TInt, $Heap);
                ##b#0_0_2_1 := a#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##b#0_0_2_1, TInt, $Heap);
                assert {:subsumption 0} ##a#0_0_2_1 > 0;
                assert {:subsumption 0} ##b#0_0_2_1 > 0;
                assume _module.__default.Gcd#canCall(b#0, a#0);
                assume _module.__default.Gcd#canCall(b#0, a#0);
                // ----- assert line0 == line1 ----- Problem2.dfy(23,7)
                assert {:subsumption 0} _module.__default.Gcd(a#0, b#0) == _module.__default.Gcd(b#0, a#0);
                assume false;
            }
            else if (*)
            {
                // ----- assume wf[lhs] ----- Problem2.dfy(23,7)
                ##a#0_0_1_0 := b#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##a#0_0_1_0, TInt, $Heap);
                ##b#0_0_1_0 := a#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##b#0_0_1_0, TInt, $Heap);
                assume {:subsumption 0} ##a#0_0_1_0 > 0;
                assume {:subsumption 0} ##b#0_0_1_0 > 0;
                assume _module.__default.Gcd#canCall(b#0, a#0);
                assume _module.__default.Gcd#canCall(b#0, a#0);
                // ----- Hint1 ----- Problem2.dfy(23,7)
                // ----- call statement ----- Problem2.dfy(27,22)
                // TrCallStmt: Before ProcessCallStmt
                assume true;
                // ProcessCallStmt: CheckSubrange
                a##0_0_1_0 := b#0;
                assume true;
                // ProcessCallStmt: CheckSubrange
                b##0_0_1_0 := a#0;
                assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                // ProcessCallStmt: Make the call
                call Call$$_module.__default.GcdDecrease(a##0_0_1_0, b##0_0_1_0);
                // TrCallStmt: After ProcessCallStmt
                assume {:captureState "Problem2.dfy(27,27)"} true;
                // ----- assert wf[rhs] ----- Problem2.dfy(23,7)
                ##a#0_0_1_1 := b#0 - a#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##a#0_0_1_1, TInt, $Heap);
                ##b#0_0_1_1 := a#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##b#0_0_1_1, TInt, $Heap);
                assert {:subsumption 0} ##a#0_0_1_1 > 0;
                assert {:subsumption 0} ##b#0_0_1_1 > 0;
                assume _module.__default.Gcd#canCall(b#0 - a#0, a#0);
                assume _module.__default.Gcd#canCall(b#0 - a#0, a#0);
                // ----- assert line1 == line2 ----- Problem2.dfy(23,7)
                assert {:subsumption 0} _module.__default.Gcd(b#0, a#0) == _module.__default.Gcd(b#0 - a#0, a#0);
                assume false;
            }
            else if (*)
            {
                // ----- assume wf[lhs] ----- Problem2.dfy(23,7)
                ##a#0_0_0_0 := b#0 - a#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##a#0_0_0_0, TInt, $Heap);
                ##b#0_0_0_0 := a#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##b#0_0_0_0, TInt, $Heap);
                assume {:subsumption 0} ##a#0_0_0_0 > 0;
                assume {:subsumption 0} ##b#0_0_0_0 > 0;
                assume _module.__default.Gcd#canCall(b#0 - a#0, a#0);
                assume _module.__default.Gcd#canCall(b#0 - a#0, a#0);
                // ----- Hint2 ----- Problem2.dfy(23,7)
                // ----- call statement ----- Problem2.dfy(29,19)
                // TrCallStmt: Before ProcessCallStmt
                assume true;
                // ProcessCallStmt: CheckSubrange
                a##0_0_0_0 := b#0 - a#0;
                assume true;
                // ProcessCallStmt: CheckSubrange
                b##0_0_0_0 := a#0;
                assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                // ProcessCallStmt: Make the call
                call Call$$_module.__default.Symmetry(a##0_0_0_0, b##0_0_0_0);
                // TrCallStmt: After ProcessCallStmt
                assume {:captureState "Problem2.dfy(29,28)"} true;
                // ----- assert wf[rhs] ----- Problem2.dfy(23,7)
                ##a#0_0_0_1 := a#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##a#0_0_0_1, TInt, $Heap);
                ##b#0_0_0_1 := b#0 - a#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##b#0_0_0_1, TInt, $Heap);
                assert {:subsumption 0} ##a#0_0_0_1 > 0;
                assert {:subsumption 0} ##b#0_0_0_1 > 0;
                assume _module.__default.Gcd#canCall(a#0, b#0 - a#0);
                assume _module.__default.Gcd#canCall(a#0, b#0 - a#0);
                // ----- assert line2 == line3 ----- Problem2.dfy(23,7)
                assert {:subsumption 0} _module.__default.Gcd(b#0 - a#0, a#0) == _module.__default.Gcd(a#0, b#0 - a#0);
                assume false;
            }

            assume _module.__default.Gcd(a#0, b#0) == _module.__default.Gcd(a#0, b#0 - a#0);
            // ----- assignment statement ----- Problem2.dfy(32,9)
            assume true;
            assume true;
            b#0 := b#0 - a#0;
            assume {:captureState "Problem2.dfy(32,16)"} true;
        }
        else
        {
            assume b#0 >= a#0 && a#0 >= b#0;
            break;
        }

        // ----- loop termination check ----- Problem2.dfy(14,3)
        assert 0 <= $decr$loop#00 || a#0 + b#0 == $decr$loop#00;
        assert a#0 + b#0 < $decr$loop#00;
        assume true;
        assume _module.__default.Gcd#canCall(A#0, B#0)
           && _module.__default.Gcd#canCall(a#0, b#0);
    }

    // ----- call statement ----- Problem2.dfy(34,11)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    a##0 := a#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.GcdEqual(a##0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "Problem2.dfy(34,13)"} true;
    // ----- return statement ----- Problem2.dfy(35,3)
    // ----- assignment statement ----- Problem2.dfy(35,3)
    assume true;
    assume true;
    gcd#0 := a#0;
    assume {:captureState "Problem2.dfy(35,10)"} true;
    return;
}



procedure CheckWellformed$$_module.__default.ParallelGcd__ReadAB__WithoutTermination(A#0: int, B#0: int) returns (gcd#0: int);
  free requires 16 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.ParallelGcd__ReadAB__WithoutTermination(A#0: int, B#0: int) returns (gcd#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##a#0: int;
  var ##b#0: int;

    // AddMethodImpl: ParallelGcd_ReadAB_WithoutTermination, CheckWellformed$$_module.__default.ParallelGcd__ReadAB__WithoutTermination
    // initialize fuel constant
    assume AsFuelBottom(StartFuel__module._default.Divides)
       == StartFuel__module._default.Divides;
    assume AsFuelBottom(StartFuelAssert__module._default.Divides)
       == StartFuelAssert__module._default.Divides;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "Problem2.dfy(38,7): initial state"} true;
    assume A#0 > 0;
    assume B#0 > 0;
    havoc $Heap;
    assume (forall<alpha> $o: ref, $f: Field alpha ::
      { read($Heap, $o, $f) }
      $o != null && read(old($Heap), $o, alloc)
         ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
    assume $HeapSucc(old($Heap), $Heap);
    havoc gcd#0;
    assume {:captureState "Problem2.dfy(40,14): post-state"} true;
    ##a#0 := A#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##a#0, TInt, $Heap);
    ##b#0 := B#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##b#0, TInt, $Heap);
    assert {:subsumption 0} ##a#0 > 0;
    assert {:subsumption 0} ##b#0 > 0;
    assume ##a#0 > 0 && ##b#0 > 0;
    assume _module.__default.Gcd#canCall(A#0, B#0);
    assume gcd#0 == _module.__default.Gcd(A#0, B#0);
}



procedure Call$$_module.__default.ParallelGcd__ReadAB__WithoutTermination(A#0: int, B#0: int) returns (gcd#0: int);
  // user-defined preconditions
  requires A#0 > 0;
  requires B#0 > 0;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Gcd#canCall(A#0, B#0);
  ensures gcd#0 == _module.__default.Gcd(A#0, B#0);
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.ParallelGcd__ReadAB__WithoutTermination(A#0: int, B#0: int) returns (gcd#0: int, $_reverifyPost: bool);
  free requires 16 == $FunctionContextHeight;
  // user-defined preconditions
  requires A#0 > 0;
  requires B#0 > 0;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Gcd#canCall(A#0, B#0);
  ensures gcd#0 == _module.__default.Gcd(A#0, B#0);
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.ParallelGcd__ReadAB__WithoutTermination(A#0: int, B#0: int) returns (gcd#0: int, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var a#0: int;
  var b#0: int;
  var $rhs#0: int;
  var $rhs#1: int;
  var pc0#0: int;
  var pc1#0: int;
  var $rhs#2: int;
  var $rhs#3: int;
  var a0#0: int;
  var b0#0: int;
  var a1#0: int;
  var b1#0: int;
  var $PreLoopHeap$loop#0: Heap;
  var $w$loop#0: bool;
  var ##a#1: int;
  var ##b#1: int;
  var ##a#2: int;
  var ##b#2: int;
  var a##0_2_0: int;
  var b##0_2_0: int;
  var a##0_2_1: int;
  var b##0_2_1: int;
  var a##0_2_2: int;
  var b##0_2_2: int;
  var $rhs#0_2_0: int;
  var $rhs#0_2_1: int;
  var $rhs#0_3_0: int;
  var $rhs#0_3_1: int;
  var $rhs#0_3_2: int;
  var a##0_6_0: int;
  var b##0_6_0: int;
  var $rhs#0_6_0: int;
  var $rhs#0_6_1: int;
  var $rhs#0_7_0: int;
  var $rhs#0_7_1: int;
  var $rhs#0_7_2: int;
  var a##0: int;

    // AddMethodImpl: ParallelGcd_ReadAB_WithoutTermination, Impl$$_module.__default.ParallelGcd__ReadAB__WithoutTermination
    // initialize fuel constant
    assume AsFuelBottom(StartFuel__module._default.Divides)
       == StartFuel__module._default.Divides;
    assume AsFuelBottom(StartFuelAssert__module._default.Divides)
       == StartFuelAssert__module._default.Divides;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "Problem2.dfy(42,0): initial state"} true;
    $_reverifyPost := false;
    // ----- update statement ----- Problem2.dfy(43,12)
    assume true;
    assume true;
    assume true;
    $rhs#0 := A#0;
    assume true;
    $rhs#1 := B#0;
    a#0 := $rhs#0;
    b#0 := $rhs#1;
    assume {:captureState "Problem2.dfy(43,18)"} true;
    // ----- update statement ----- Problem2.dfy(44,16)
    assume true;
    assume true;
    assume true;
    $rhs#2 := LitInt(0);
    assume true;
    $rhs#3 := LitInt(0);
    pc0#0 := $rhs#2;
    pc1#0 := $rhs#3;
    assume {:captureState "Problem2.dfy(44,22)"} true;
    havoc a0#0, b0#0, a1#0, b1#0;
    // ----- while statement ----- Problem2.dfy(46,3)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    havoc $w$loop#0;
    while (true)
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0 ==> 0 < a#0;
      invariant $w$loop#0 ==> 0 < b#0;
      free invariant $w$loop#0
         ==> _module.__default.Gcd#canCall(A#0, B#0)
           && _module.__default.Gcd#canCall(a#0, b#0);
      invariant $w$loop#0 ==> _module.__default.Gcd(A#0, B#0) == _module.__default.Gcd(a#0, b#0);
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0 ==> LitInt(0) <= pc0#0;
      invariant $w$loop#0 ==> pc0#0 < 3;
      invariant $w$loop#0 ==> LitInt(0) <= pc1#0;
      invariant $w$loop#0 ==> pc1#0 < 3;
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0 ==> pc0#0 == LitInt(1) && b0#0 <= a0#0 ==> a0#0 == a#0;
      invariant $w$loop#0 ==> pc0#0 == LitInt(1) && b0#0 <= a0#0 ==> b0#0 == b#0;
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0 ==> pc1#0 == LitInt(1) && a1#0 <= b1#0 ==> a1#0 == a#0;
      invariant $w$loop#0 ==> pc1#0 == LitInt(1) && a1#0 <= b1#0 ==> b1#0 == b#0;
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0 ==> pc0#0 == LitInt(2) ==> a#0 == b#0;
      invariant $w$loop#0 ==> pc1#0 == LitInt(2) ==> a#0 == b#0;
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
        assume {:captureState "Problem2.dfy(46,2): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            if (0 < a#0)
            {
            }

            assume true;
            assume 0 < a#0 && 0 < b#0;
            ##a#1 := A#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##a#1, TInt, $Heap);
            ##b#1 := B#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##b#1, TInt, $Heap);
            assert {:subsumption 0} ##a#1 > 0;
            assert {:subsumption 0} ##b#1 > 0;
            assume _module.__default.Gcd#canCall(A#0, B#0);
            ##a#2 := a#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##a#2, TInt, $Heap);
            ##b#2 := b#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##b#2, TInt, $Heap);
            assert {:subsumption 0} ##a#2 > 0;
            assert {:subsumption 0} ##b#2 > 0;
            assume _module.__default.Gcd#canCall(a#0, b#0);
            assume _module.__default.Gcd#canCall(A#0, B#0)
               && _module.__default.Gcd#canCall(a#0, b#0);
            assume _module.__default.Gcd(A#0, B#0) == _module.__default.Gcd(a#0, b#0);
            if (LitInt(0) <= pc0#0)
            {
            }

            if (LitInt(0) <= pc0#0 && pc0#0 < 3)
            {
                if (LitInt(0) <= pc1#0)
                {
                }
            }

            assume true;
            assume LitInt(0) <= pc0#0 && pc0#0 < 3 && LitInt(0) <= pc1#0 && pc1#0 < 3;
            if (pc0#0 == LitInt(1))
            {
            }

            if (pc0#0 == LitInt(1) && b0#0 <= a0#0)
            {
                if (a0#0 == a#0)
                {
                }
            }

            assume true;
            assume pc0#0 == LitInt(1) && b0#0 <= a0#0 ==> a0#0 == a#0 && b0#0 == b#0;
            if (pc1#0 == LitInt(1))
            {
            }

            if (pc1#0 == LitInt(1) && a1#0 <= b1#0)
            {
                if (a1#0 == a#0)
                {
                }
            }

            assume true;
            assume pc1#0 == LitInt(1) && a1#0 <= b1#0 ==> a1#0 == a#0 && b1#0 == b#0;
            if (pc0#0 == LitInt(2))
            {
            }

            if (pc0#0 == LitInt(2) ==> a#0 == b#0)
            {
                if (pc1#0 == LitInt(2))
                {
                }
            }

            assume true;
            assume (pc0#0 == LitInt(2) ==> a#0 == b#0) && (pc1#0 == LitInt(2) ==> a#0 == b#0);
            assume true;
            assume false;
        }

        if (pc0#0 == LitInt(2))
        {
        }

        assume true;
        if (pc0#0 == LitInt(2) && pc1#0 == LitInt(2))
        {
            break;
        }

        // ----- alternative statement ----- Problem2.dfy(55,5)
        if (*)
        {
            assume true;
            assume pc0#0 == LitInt(0);
            // ----- update statement ----- Problem2.dfy(56,49)
            assume true;
            assume true;
            assume true;
            assume true;
            $rhs#0_7_0 := a#0;
            assume true;
            $rhs#0_7_1 := b#0;
            assume true;
            $rhs#0_7_2 := LitInt(1);
            a0#0 := $rhs#0_7_0;
            b0#0 := $rhs#0_7_1;
            pc0#0 := $rhs#0_7_2;
            assume {:captureState "Problem2.dfy(56,58)"} true;
        }
        else if (*)
        {
            if (pc0#0 == LitInt(1))
            {
            }

            assume true;
            assume pc0#0 == LitInt(1) && b0#0 < a0#0;
            // ----- call statement ----- Problem2.dfy(57,48)
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            // ProcessCallStmt: CheckSubrange
            a##0_6_0 := a#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            b##0_6_0 := b#0;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call Call$$_module.__default.GcdDecrease(a##0_6_0, b##0_6_0);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "Problem2.dfy(57,53)"} true;
            // ----- update statement ----- Problem2.dfy(58,44)
            assume true;
            assume true;
            assume true;
            $rhs#0_6_0 := a0#0 - b0#0;
            assume true;
            $rhs#0_6_1 := LitInt(0);
            a#0 := $rhs#0_6_0;
            pc0#0 := $rhs#0_6_1;
            assume {:captureState "Problem2.dfy(58,56)"} true;
        }
        else if (*)
        {
            if (pc0#0 == LitInt(1))
            {
            }

            assume true;
            assume pc0#0 == LitInt(1) && b0#0 > a0#0;
            // ----- assignment statement ----- Problem2.dfy(59,40)
            assume true;
            assume true;
            pc0#0 := LitInt(0);
            assume {:captureState "Problem2.dfy(59,43)"} true;
        }
        else if (*)
        {
            if (pc0#0 == LitInt(1))
            {
            }

            assume true;
            assume pc0#0 == LitInt(1) && b0#0 == a0#0;
            // ----- assignment statement ----- Problem2.dfy(60,40)
            assume true;
            assume true;
            pc0#0 := LitInt(2);
            assume {:captureState "Problem2.dfy(60,43)"} true;
        }
        else if (*)
        {
            assume true;
            assume pc1#0 == LitInt(0);
            // ----- update statement ----- Problem2.dfy(61,48)
            assume true;
            assume true;
            assume true;
            assume true;
            $rhs#0_3_0 := a#0;
            assume true;
            $rhs#0_3_1 := b#0;
            assume true;
            $rhs#0_3_2 := LitInt(1);
            a1#0 := $rhs#0_3_0;
            b1#0 := $rhs#0_3_1;
            pc1#0 := $rhs#0_3_2;
            assume {:captureState "Problem2.dfy(61,57)"} true;
        }
        else if (*)
        {
            if (pc1#0 == LitInt(1))
            {
            }

            assume true;
            assume pc1#0 == LitInt(1) && a1#0 < b1#0;
            // ----- call statement ----- Problem2.dfy(62,44)
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            // ProcessCallStmt: CheckSubrange
            a##0_2_0 := a#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            b##0_2_0 := b#0;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call Call$$_module.__default.Symmetry(a##0_2_0, b##0_2_0);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "Problem2.dfy(62,49)"} true;
            // ----- call statement ----- Problem2.dfy(62,63)
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            // ProcessCallStmt: CheckSubrange
            a##0_2_1 := b#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            b##0_2_1 := a#0;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call Call$$_module.__default.GcdDecrease(a##0_2_1, b##0_2_1);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "Problem2.dfy(62,68)"} true;
            // ----- call statement ----- Problem2.dfy(62,79)
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            // ProcessCallStmt: CheckSubrange
            a##0_2_2 := b#0 - a#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            b##0_2_2 := a#0;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call Call$$_module.__default.Symmetry(a##0_2_2, b##0_2_2);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "Problem2.dfy(62,88)"} true;
            // ----- update statement ----- Problem2.dfy(63,43)
            assume true;
            assume true;
            assume true;
            $rhs#0_2_0 := b1#0 - a1#0;
            assume true;
            $rhs#0_2_1 := LitInt(0);
            b#0 := $rhs#0_2_0;
            pc1#0 := $rhs#0_2_1;
            assume {:captureState "Problem2.dfy(63,55)"} true;
        }
        else if (*)
        {
            if (pc1#0 == LitInt(1))
            {
            }

            assume true;
            assume pc1#0 == LitInt(1) && a1#0 > b1#0;
            // ----- assignment statement ----- Problem2.dfy(64,40)
            assume true;
            assume true;
            pc1#0 := LitInt(0);
            assume {:captureState "Problem2.dfy(64,43)"} true;
        }
        else if (*)
        {
            if (pc1#0 == LitInt(1))
            {
            }

            assume true;
            assume pc1#0 == LitInt(1) && a1#0 == b1#0;
            // ----- assignment statement ----- Problem2.dfy(65,40)
            assume true;
            assume true;
            pc1#0 := LitInt(2);
            assume {:captureState "Problem2.dfy(65,43)"} true;
        }
        else
        {
            assume pc0#0 != LitInt(0)
               && !
              (pc0#0 == LitInt(1)
               && b0#0 < a0#0)
               && !
              (pc0#0 == LitInt(1)
               && b0#0 > a0#0)
               && !
              (pc0#0 == LitInt(1)
               && b0#0 == a0#0)
               && pc1#0 != LitInt(0)
               && !
              (pc1#0 == LitInt(1)
               && a1#0 < b1#0)
               && !
              (pc1#0 == LitInt(1)
               && a1#0 > b1#0)
               && !
              (pc1#0 == LitInt(1)
               && a1#0 == b1#0);
            assert false;
        }

        assume true;
        assume _module.__default.Gcd#canCall(A#0, B#0)
           && _module.__default.Gcd#canCall(a#0, b#0);
        assume true;
        assume true;
        assume true;
        assume true;
    }

    // ----- call statement ----- Problem2.dfy(68,11)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    a##0 := a#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.GcdEqual(a##0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "Problem2.dfy(68,13)"} true;
    // ----- assignment statement ----- Problem2.dfy(69,7)
    assume true;
    assume true;
    gcd#0 := a#0;
    assume {:captureState "Problem2.dfy(69,10)"} true;
}



procedure CheckWellformed$$_module.__default.ParallelGcd__WithoutTermination(A#0: int, B#0: int) returns (gcd#0: int);
  free requires 17 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.ParallelGcd__WithoutTermination(A#0: int, B#0: int) returns (gcd#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##a#0: int;
  var ##b#0: int;

    // AddMethodImpl: ParallelGcd_WithoutTermination, CheckWellformed$$_module.__default.ParallelGcd__WithoutTermination
    // initialize fuel constant
    assume AsFuelBottom(StartFuel__module._default.Divides)
       == StartFuel__module._default.Divides;
    assume AsFuelBottom(StartFuelAssert__module._default.Divides)
       == StartFuelAssert__module._default.Divides;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "Problem2.dfy(72,7): initial state"} true;
    assume A#0 > 0;
    assume B#0 > 0;
    havoc $Heap;
    assume (forall<alpha> $o: ref, $f: Field alpha ::
      { read($Heap, $o, $f) }
      $o != null && read(old($Heap), $o, alloc)
         ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
    assume $HeapSucc(old($Heap), $Heap);
    havoc gcd#0;
    assume {:captureState "Problem2.dfy(74,14): post-state"} true;
    ##a#0 := A#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##a#0, TInt, $Heap);
    ##b#0 := B#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##b#0, TInt, $Heap);
    assert {:subsumption 0} ##a#0 > 0;
    assert {:subsumption 0} ##b#0 > 0;
    assume ##a#0 > 0 && ##b#0 > 0;
    assume _module.__default.Gcd#canCall(A#0, B#0);
    assume gcd#0 == _module.__default.Gcd(A#0, B#0);
}



procedure Call$$_module.__default.ParallelGcd__WithoutTermination(A#0: int, B#0: int) returns (gcd#0: int);
  // user-defined preconditions
  requires A#0 > 0;
  requires B#0 > 0;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Gcd#canCall(A#0, B#0);
  ensures gcd#0 == _module.__default.Gcd(A#0, B#0);
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.ParallelGcd__WithoutTermination(A#0: int, B#0: int) returns (gcd#0: int, $_reverifyPost: bool);
  free requires 17 == $FunctionContextHeight;
  // user-defined preconditions
  requires A#0 > 0;
  requires B#0 > 0;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Gcd#canCall(A#0, B#0);
  ensures gcd#0 == _module.__default.Gcd(A#0, B#0);
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.ParallelGcd__WithoutTermination(A#0: int, B#0: int) returns (gcd#0: int, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var a#0: int;
  var b#0: int;
  var $rhs#0: int;
  var $rhs#1: int;
  var pc0#0: int;
  var pc1#0: int;
  var $rhs#2: int;
  var $rhs#3: int;
  var a0#0: int;
  var b0#0: int;
  var a1#0: int;
  var b1#0: int;
  var $PreLoopHeap$loop#0: Heap;
  var $w$loop#0: bool;
  var ##a#1: int;
  var ##b#1: int;
  var ##a#2: int;
  var ##b#2: int;
  var a##0_2_0: int;
  var b##0_2_0: int;
  var a##0_2_1: int;
  var b##0_2_1: int;
  var a##0_2_2: int;
  var b##0_2_2: int;
  var $rhs#0_2_0: int;
  var $rhs#0_2_1: int;
  var $rhs#0_3_0: int;
  var $rhs#0_3_1: int;
  var $rhs#0_4_0: int;
  var $rhs#0_4_1: int;
  var a##0_7_0: int;
  var b##0_7_0: int;
  var $rhs#0_7_0: int;
  var $rhs#0_7_1: int;
  var $rhs#0_8_0: int;
  var $rhs#0_8_1: int;
  var $rhs#0_9_0: int;
  var $rhs#0_9_1: int;
  var a##0: int;

    // AddMethodImpl: ParallelGcd_WithoutTermination, Impl$$_module.__default.ParallelGcd__WithoutTermination
    // initialize fuel constant
    assume AsFuelBottom(StartFuel__module._default.Divides)
       == StartFuel__module._default.Divides;
    assume AsFuelBottom(StartFuelAssert__module._default.Divides)
       == StartFuelAssert__module._default.Divides;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "Problem2.dfy(76,0): initial state"} true;
    $_reverifyPost := false;
    // ----- update statement ----- Problem2.dfy(77,12)
    assume true;
    assume true;
    assume true;
    $rhs#0 := A#0;
    assume true;
    $rhs#1 := B#0;
    a#0 := $rhs#0;
    b#0 := $rhs#1;
    assume {:captureState "Problem2.dfy(77,18)"} true;
    // ----- update statement ----- Problem2.dfy(78,16)
    assume true;
    assume true;
    assume true;
    $rhs#2 := LitInt(0);
    assume true;
    $rhs#3 := LitInt(0);
    pc0#0 := $rhs#2;
    pc1#0 := $rhs#3;
    assume {:captureState "Problem2.dfy(78,22)"} true;
    havoc a0#0, b0#0, a1#0, b1#0;
    // ----- while statement ----- Problem2.dfy(80,3)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    havoc $w$loop#0;
    while (true)
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0 ==> 0 < a#0;
      invariant $w$loop#0 ==> 0 < b#0;
      free invariant $w$loop#0
         ==> _module.__default.Gcd#canCall(A#0, B#0)
           && _module.__default.Gcd#canCall(a#0, b#0);
      invariant $w$loop#0 ==> _module.__default.Gcd(A#0, B#0) == _module.__default.Gcd(a#0, b#0);
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0 ==> LitInt(0) <= pc0#0;
      invariant $w$loop#0 ==> pc0#0 < 4;
      invariant $w$loop#0 ==> LitInt(0) <= pc1#0;
      invariant $w$loop#0 ==> pc1#0 < 4;
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0 ==> pc0#0 == LitInt(0) || a0#0 == a#0;
      invariant $w$loop#0 ==> pc1#0 == LitInt(0) || b1#0 == b#0;
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0 ==> pc0#0 == LitInt(2) ==> b#0 <= b0#0;
      invariant $w$loop#0 ==> pc0#0 == LitInt(2) ==> b0#0 <= a0#0 ==> b0#0 == b#0;
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0 ==> pc1#0 == LitInt(2) ==> a#0 <= a1#0;
      invariant $w$loop#0 ==> pc1#0 == LitInt(2) ==> a1#0 <= b1#0 ==> a1#0 == a#0;
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0 ==> pc0#0 == LitInt(3) ==> a#0 == b#0;
      invariant $w$loop#0 ==> pc1#0 == LitInt(3) ==> a#0 == b#0;
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
        assume {:captureState "Problem2.dfy(80,2): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            if (0 < a#0)
            {
            }

            assume true;
            assume 0 < a#0 && 0 < b#0;
            ##a#1 := A#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##a#1, TInt, $Heap);
            ##b#1 := B#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##b#1, TInt, $Heap);
            assert {:subsumption 0} ##a#1 > 0;
            assert {:subsumption 0} ##b#1 > 0;
            assume _module.__default.Gcd#canCall(A#0, B#0);
            ##a#2 := a#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##a#2, TInt, $Heap);
            ##b#2 := b#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##b#2, TInt, $Heap);
            assert {:subsumption 0} ##a#2 > 0;
            assert {:subsumption 0} ##b#2 > 0;
            assume _module.__default.Gcd#canCall(a#0, b#0);
            assume _module.__default.Gcd#canCall(A#0, B#0)
               && _module.__default.Gcd#canCall(a#0, b#0);
            assume _module.__default.Gcd(A#0, B#0) == _module.__default.Gcd(a#0, b#0);
            if (LitInt(0) <= pc0#0)
            {
            }

            if (LitInt(0) <= pc0#0 && pc0#0 < 4)
            {
                if (LitInt(0) <= pc1#0)
                {
                }
            }

            assume true;
            assume LitInt(0) <= pc0#0 && pc0#0 < 4 && LitInt(0) <= pc1#0 && pc1#0 < 4;
            if (pc0#0 != LitInt(0))
            {
            }

            if (pc0#0 == LitInt(0) || a0#0 == a#0)
            {
                if (pc1#0 != LitInt(0))
                {
                }
            }

            assume true;
            assume (pc0#0 == LitInt(0) || a0#0 == a#0) && (pc1#0 == LitInt(0) || b1#0 == b#0);
            if (pc0#0 == LitInt(2))
            {
                if (b#0 <= b0#0)
                {
                    if (b0#0 <= a0#0)
                    {
                    }
                }
            }

            assume true;
            assume pc0#0 == LitInt(2) ==> b#0 <= b0#0 && (b0#0 <= a0#0 ==> b0#0 == b#0);
            if (pc1#0 == LitInt(2))
            {
                if (a#0 <= a1#0)
                {
                    if (a1#0 <= b1#0)
                    {
                    }
                }
            }

            assume true;
            assume pc1#0 == LitInt(2) ==> a#0 <= a1#0 && (a1#0 <= b1#0 ==> a1#0 == a#0);
            if (pc0#0 == LitInt(3))
            {
            }

            if (pc0#0 == LitInt(3) ==> a#0 == b#0)
            {
                if (pc1#0 == LitInt(3))
                {
                }
            }

            assume true;
            assume (pc0#0 == LitInt(3) ==> a#0 == b#0) && (pc1#0 == LitInt(3) ==> a#0 == b#0);
            assume true;
            assume false;
        }

        if (pc0#0 == LitInt(3))
        {
        }

        assume true;
        if (pc0#0 == LitInt(3) && pc1#0 == LitInt(3))
        {
            break;
        }

        // ----- alternative statement ----- Problem2.dfy(90,5)
        if (*)
        {
            assume true;
            assume pc0#0 == LitInt(0);
            // ----- update statement ----- Problem2.dfy(91,44)
            assume true;
            assume true;
            assume true;
            $rhs#0_9_0 := a#0;
            assume true;
            $rhs#0_9_1 := LitInt(1);
            a0#0 := $rhs#0_9_0;
            pc0#0 := $rhs#0_9_1;
            assume {:captureState "Problem2.dfy(91,50)"} true;
        }
        else if (*)
        {
            assume true;
            assume pc0#0 == LitInt(1);
            // ----- update statement ----- Problem2.dfy(92,44)
            assume true;
            assume true;
            assume true;
            $rhs#0_8_0 := b#0;
            assume true;
            $rhs#0_8_1 := LitInt(2);
            b0#0 := $rhs#0_8_0;
            pc0#0 := $rhs#0_8_1;
            assume {:captureState "Problem2.dfy(92,50)"} true;
        }
        else if (*)
        {
            if (pc0#0 == LitInt(2))
            {
            }

            assume true;
            assume pc0#0 == LitInt(2) && a0#0 > b0#0;
            // ----- call statement ----- Problem2.dfy(93,47)
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            // ProcessCallStmt: CheckSubrange
            a##0_7_0 := a#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            b##0_7_0 := b#0;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call Call$$_module.__default.GcdDecrease(a##0_7_0, b##0_7_0);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "Problem2.dfy(93,52)"} true;
            // ----- update statement ----- Problem2.dfy(94,43)
            assume true;
            assume true;
            assume true;
            $rhs#0_7_0 := a0#0 - b0#0;
            assume true;
            $rhs#0_7_1 := LitInt(0);
            a#0 := $rhs#0_7_0;
            pc0#0 := $rhs#0_7_1;
            assume {:captureState "Problem2.dfy(94,55)"} true;
        }
        else if (*)
        {
            if (pc0#0 == LitInt(2))
            {
            }

            assume true;
            assume pc0#0 == LitInt(2) && a0#0 < b0#0;
            // ----- assignment statement ----- Problem2.dfy(95,40)
            assume true;
            assume true;
            pc0#0 := LitInt(0);
            assume {:captureState "Problem2.dfy(95,43)"} true;
        }
        else if (*)
        {
            if (pc0#0 == LitInt(2))
            {
            }

            assume true;
            assume pc0#0 == LitInt(2) && a0#0 == b0#0;
            // ----- assignment statement ----- Problem2.dfy(96,40)
            assume true;
            assume true;
            pc0#0 := LitInt(3);
            assume {:captureState "Problem2.dfy(96,43)"} true;
        }
        else if (*)
        {
            assume true;
            assume pc1#0 == LitInt(0);
            // ----- update statement ----- Problem2.dfy(97,44)
            assume true;
            assume true;
            assume true;
            $rhs#0_4_0 := b#0;
            assume true;
            $rhs#0_4_1 := LitInt(1);
            b1#0 := $rhs#0_4_0;
            pc1#0 := $rhs#0_4_1;
            assume {:captureState "Problem2.dfy(97,50)"} true;
        }
        else if (*)
        {
            assume true;
            assume pc1#0 == LitInt(1);
            // ----- update statement ----- Problem2.dfy(98,44)
            assume true;
            assume true;
            assume true;
            $rhs#0_3_0 := a#0;
            assume true;
            $rhs#0_3_1 := LitInt(2);
            a1#0 := $rhs#0_3_0;
            pc1#0 := $rhs#0_3_1;
            assume {:captureState "Problem2.dfy(98,50)"} true;
        }
        else if (*)
        {
            if (pc1#0 == LitInt(2))
            {
            }

            assume true;
            assume pc1#0 == LitInt(2) && b1#0 > a1#0;
            // ----- call statement ----- Problem2.dfy(99,44)
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            // ProcessCallStmt: CheckSubrange
            a##0_2_0 := a#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            b##0_2_0 := b#0;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call Call$$_module.__default.Symmetry(a##0_2_0, b##0_2_0);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "Problem2.dfy(99,49)"} true;
            // ----- call statement ----- Problem2.dfy(99,63)
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            // ProcessCallStmt: CheckSubrange
            a##0_2_1 := b#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            b##0_2_1 := a#0;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call Call$$_module.__default.GcdDecrease(a##0_2_1, b##0_2_1);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "Problem2.dfy(99,68)"} true;
            // ----- call statement ----- Problem2.dfy(99,79)
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            // ProcessCallStmt: CheckSubrange
            a##0_2_2 := b#0 - a#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            b##0_2_2 := a#0;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call Call$$_module.__default.Symmetry(a##0_2_2, b##0_2_2);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "Problem2.dfy(99,88)"} true;
            // ----- update statement ----- Problem2.dfy(100,43)
            assume true;
            assume true;
            assume true;
            $rhs#0_2_0 := b1#0 - a1#0;
            assume true;
            $rhs#0_2_1 := LitInt(0);
            b#0 := $rhs#0_2_0;
            pc1#0 := $rhs#0_2_1;
            assume {:captureState "Problem2.dfy(100,55)"} true;
        }
        else if (*)
        {
            if (pc1#0 == LitInt(2))
            {
            }

            assume true;
            assume pc1#0 == LitInt(2) && b1#0 < a1#0;
            // ----- assignment statement ----- Problem2.dfy(101,40)
            assume true;
            assume true;
            pc1#0 := LitInt(0);
            assume {:captureState "Problem2.dfy(101,43)"} true;
        }
        else if (*)
        {
            if (pc1#0 == LitInt(2))
            {
            }

            assume true;
            assume pc1#0 == LitInt(2) && b1#0 == a1#0;
            // ----- assignment statement ----- Problem2.dfy(102,40)
            assume true;
            assume true;
            pc1#0 := LitInt(3);
            assume {:captureState "Problem2.dfy(102,43)"} true;
        }
        else
        {
            assume pc0#0 != LitInt(0)
               && pc0#0 != LitInt(1)
               && !
              (pc0#0 == LitInt(2)
               && a0#0 > b0#0)
               && !
              (pc0#0 == LitInt(2)
               && a0#0 < b0#0)
               && !
              (pc0#0 == LitInt(2)
               && a0#0 == b0#0)
               && pc1#0 != LitInt(0)
               && pc1#0 != LitInt(1)
               && !
              (pc1#0 == LitInt(2)
               && b1#0 > a1#0)
               && !
              (pc1#0 == LitInt(2)
               && b1#0 < a1#0)
               && !
              (pc1#0 == LitInt(2)
               && b1#0 == a1#0);
            assert false;
        }

        assume true;
        assume _module.__default.Gcd#canCall(A#0, B#0)
           && _module.__default.Gcd#canCall(a#0, b#0);
        assume true;
        assume true;
        assume true;
        assume true;
        assume true;
    }

    // ----- call statement ----- Problem2.dfy(105,11)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    a##0 := a#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.GcdEqual(a##0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "Problem2.dfy(105,13)"} true;
    // ----- assignment statement ----- Problem2.dfy(106,7)
    assume true;
    assume true;
    gcd#0 := a#0;
    assume {:captureState "Problem2.dfy(106,10)"} true;
}



procedure CheckWellformed$$_module.__default.ParallelGcd(A#0: int, B#0: int) returns (gcd#0: int);
  free requires 20 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.ParallelGcd(A#0: int, B#0: int) returns (gcd#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##a#0: int;
  var ##b#0: int;

    // AddMethodImpl: ParallelGcd, CheckWellformed$$_module.__default.ParallelGcd
    // initialize fuel constant
    assume AsFuelBottom(StartFuel__module._default.Divides)
       == StartFuel__module._default.Divides;
    assume AsFuelBottom(StartFuelAssert__module._default.Divides)
       == StartFuelAssert__module._default.Divides;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "Problem2.dfy(109,7): initial state"} true;
    assume A#0 > 0;
    assume B#0 > 0;
    havoc $Heap;
    assume (forall<alpha> $o: ref, $f: Field alpha ::
      { read($Heap, $o, $f) }
      $o != null && read(old($Heap), $o, alloc)
         ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
    assume $HeapSucc(old($Heap), $Heap);
    havoc gcd#0;
    assume {:captureState "Problem2.dfy(111,14): post-state"} true;
    ##a#0 := A#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##a#0, TInt, $Heap);
    ##b#0 := B#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##b#0, TInt, $Heap);
    assert {:subsumption 0} ##a#0 > 0;
    assert {:subsumption 0} ##b#0 > 0;
    assume ##a#0 > 0 && ##b#0 > 0;
    assume _module.__default.Gcd#canCall(A#0, B#0);
    assume gcd#0 == _module.__default.Gcd(A#0, B#0);
}



procedure Call$$_module.__default.ParallelGcd(A#0: int, B#0: int) returns (gcd#0: int);
  // user-defined preconditions
  requires A#0 > 0;
  requires B#0 > 0;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Gcd#canCall(A#0, B#0);
  ensures gcd#0 == _module.__default.Gcd(A#0, B#0);
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.ParallelGcd(A#0: int, B#0: int) returns (gcd#0: int, $_reverifyPost: bool);
  free requires 20 == $FunctionContextHeight;
  // user-defined preconditions
  requires A#0 > 0;
  requires B#0 > 0;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Gcd#canCall(A#0, B#0);
  ensures gcd#0 == _module.__default.Gcd(A#0, B#0);
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.ParallelGcd(A#0: int, B#0: int) returns (gcd#0: int, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var a#0: int;
  var b#0: int;
  var $rhs#0: int;
  var $rhs#1: int;
  var pc0#0: int;
  var pc1#0: int;
  var $rhs#2: int;
  var $rhs#3: int;
  var a0#0: int;
  var b0#0: int;
  var a1#0: int;
  var b1#0: int;
  var budget0#0: int;
  var budget1#0: int;
  var $rhs#4: int;
  var $rhs#5: int;
  var $PreLoopHeap$loop#0: Heap;
  var $decr_init$loop#00: int;
  var $decr_init$loop#01: int;
  var $decr_init$loop#02: int;
  var $decr_init$loop#03: int;
  var $decr_init$loop#04: int;
  var $w$loop#0: bool;
  var ##a#1: int;
  var ##b#1: int;
  var ##a#2: int;
  var ##b#2: int;
  var ##pcThis#0: int;
  var ##pcThat#0: int;
  var ##a0#0: int;
  var ##b0#0: int;
  var ##b#3: int;
  var ##pcThis#1: int;
  var ##pcThat#1: int;
  var ##a0#1: int;
  var ##b0#1: int;
  var ##b#4: int;
  var $decr$loop#00: int;
  var $decr$loop#01: int;
  var $decr$loop#02: int;
  var $decr$loop#03: int;
  var $decr$loop#04: int;
  var $rhs##0_0_0: int;
  var $rhs##0_0_1: int;
  var inThis##0_0_0: int;
  var inThat##0_0_0: int;
  var pcThat##0_0_0: int;
  var $rhs##0_1_0: int;
  var $rhs##0_1_1: int;
  var inThis##0_1_0: int;
  var inThat##0_1_0: int;
  var pcThat##0_1_0: int;
  var a##0_2_0: int;
  var b##0_2_0: int;
  var a##0_2_1: int;
  var b##0_2_1: int;
  var a##0_2_2: int;
  var b##0_2_2: int;
  var $rhs#0_2_0: int;
  var $rhs#0_2_1: int;
  var $rhs##0_2_0: int;
  var $rhs##0_2_1: int;
  var inThis##0_2_0: int;
  var inThat##0_2_0: int;
  var pcThat##0_2_0: int;
  var $rhs#0_3_0: int;
  var $rhs#0_3_1: int;
  var $rhs#0_4_0: int;
  var $rhs#0_4_1: int;
  var $rhs##0_5_0: int;
  var $rhs##0_5_1: int;
  var inThis##0_5_0: int;
  var inThat##0_5_0: int;
  var pcThat##0_5_0: int;
  var $rhs##0_6_0: int;
  var $rhs##0_6_1: int;
  var inThis##0_6_0: int;
  var inThat##0_6_0: int;
  var pcThat##0_6_0: int;
  var a##0_7_0: int;
  var b##0_7_0: int;
  var $rhs#0_7_0: int;
  var $rhs#0_7_1: int;
  var $rhs##0_7_0: int;
  var $rhs##0_7_1: int;
  var inThis##0_7_0: int;
  var inThat##0_7_0: int;
  var pcThat##0_7_0: int;
  var $rhs#0_8_0: int;
  var $rhs#0_8_1: int;
  var $rhs#0_9_0: int;
  var $rhs#0_9_1: int;
  var a##0: int;

    // AddMethodImpl: ParallelGcd, Impl$$_module.__default.ParallelGcd
    // initialize fuel constant
    assume AsFuelBottom(StartFuel__module._default.Divides)
       == StartFuel__module._default.Divides;
    assume AsFuelBottom(StartFuelAssert__module._default.Divides)
       == StartFuelAssert__module._default.Divides;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "Problem2.dfy(112,0): initial state"} true;
    $_reverifyPost := false;
    // ----- update statement ----- Problem2.dfy(113,12)
    assume true;
    assume true;
    assume true;
    $rhs#0 := A#0;
    assume true;
    $rhs#1 := B#0;
    a#0 := $rhs#0;
    b#0 := $rhs#1;
    assume {:captureState "Problem2.dfy(113,18)"} true;
    // ----- update statement ----- Problem2.dfy(114,16)
    assume true;
    assume true;
    assume true;
    $rhs#2 := LitInt(0);
    assume true;
    $rhs#3 := LitInt(0);
    pc0#0 := $rhs#2;
    pc1#0 := $rhs#3;
    assume {:captureState "Problem2.dfy(114,22)"} true;
    havoc a0#0, b0#0, a1#0, b1#0;
    // ----- assign-such-that statement ----- Problem2.dfy(120,24)
    assume true;
    assume true;
    havoc $rhs#4;
    havoc $rhs#5;
    budget0#0 := $rhs#4;
    budget1#0 := $rhs#5;
    if (budget0#0 > 0)
    {
    }

    assume true;
    assert (
        $Is(LitInt(0 + 1), TInt)
         && $Is(LitInt(0 + 1), TInt)
         && Lit(0 + 1 > 0 && 0 + 1 > 0))
       ||
      ($Is(LitInt(0), TInt) && $Is(LitInt(0 + 1), TInt) && Lit(0 > 0 && 0 + 1 > 0))
       ||
      (exists $as#budget00#0: int ::
        $Is(LitInt(0 + 1), TInt) && $as#budget00#0 > 0 && 0 + 1 > 0)
       ||
      ($Is(LitInt(0 + 1), TInt) && $Is(LitInt(0), TInt) && Lit(0 + 1 > 0 && 0 > 0))
       ||
      ($Is(LitInt(0), TInt) && $Is(LitInt(0), TInt) && Lit(0 > 0 && 0 > 0))
       ||
      (exists $as#budget00#0: int ::
        $Is(LitInt(0), TInt) && $as#budget00#0 > 0 && 0 > 0)
       ||
      (exists $as#budget10#0: int ::
        $Is(LitInt(0 + 1), TInt) && 0 + 1 > 0 && $as#budget10#0 > 0)
       ||
      (exists $as#budget10#0: int ::
        $Is(LitInt(0), TInt) && 0 > 0 && $as#budget10#0 > 0)
       || (exists $as#budget00#0: int, $as#budget10#0: int ::
        $as#budget00#0 > 0 && $as#budget10#0 > 0);
    assume budget0#0 > 0 && budget1#0 > 0;
    assume {:captureState "Problem2.dfy(120,52)"} true;
    // ----- while statement ----- Problem2.dfy(121,3)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    $decr_init$loop#00 := a#0 + b#0;
    $decr_init$loop#01 := _module.__default.FinalStretch(pc0#0, pc1#0, a0#0, b0#0, b#0)
       + _module.__default.FinalStretch(pc1#0, pc0#0, b1#0, a1#0, a#0);
    $decr_init$loop#02 := (if pc0#0 == LitInt(2) && a0#0 < b0#0 && !(a#0 < b#0) then 1 else 0)
       + (if pc1#0 == LitInt(2) && b1#0 < a1#0 && !(b#0 < a#0) then 1 else 0);
    $decr_init$loop#03 := (if a#0 < b#0 then budget0#0 else 0) + (if b#0 < a#0 then budget1#0 else 0);
    $decr_init$loop#04 := 8 - pc0#0 - pc1#0;
    havoc $w$loop#0;
    while (true)
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0 ==> 0 < a#0;
      invariant $w$loop#0 ==> 0 < b#0;
      free invariant $w$loop#0
         ==> _module.__default.Gcd#canCall(A#0, B#0)
           && _module.__default.Gcd#canCall(a#0, b#0);
      invariant $w$loop#0 ==> _module.__default.Gcd(A#0, B#0) == _module.__default.Gcd(a#0, b#0);
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0 ==> LitInt(0) <= pc0#0;
      invariant $w$loop#0 ==> pc0#0 < 4;
      invariant $w$loop#0 ==> LitInt(0) <= pc1#0;
      invariant $w$loop#0 ==> pc1#0 < 4;
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0 ==> pc0#0 == LitInt(0) || a0#0 == a#0;
      invariant $w$loop#0 ==> pc1#0 == LitInt(0) || b1#0 == b#0;
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0 ==> pc0#0 == LitInt(2) ==> b#0 <= b0#0;
      invariant $w$loop#0 ==> pc0#0 == LitInt(2) ==> b0#0 <= a0#0 ==> b0#0 == b#0;
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0 ==> pc1#0 == LitInt(2) ==> a#0 <= a1#0;
      invariant $w$loop#0 ==> pc1#0 == LitInt(2) ==> a1#0 <= b1#0 ==> a1#0 == a#0;
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0 ==> pc0#0 == LitInt(3) ==> a#0 == b#0;
      invariant $w$loop#0 ==> pc1#0 == LitInt(3) ==> a#0 == b#0;
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0 ==> LitInt(0) <= budget0#0;
      invariant $w$loop#0 ==> LitInt(0) <= budget1#0;
      invariant $w$loop#0
         ==> pc0#0 == LitInt(3) || pc1#0 == LitInt(3) || LitInt(1) <= budget0#0 + budget1#0;
      free invariant (forall<alpha> $o: ref, $f: Field alpha ::
        { read($Heap, $o, $f) }
        $o != null && read(old($Heap), $o, alloc)
           ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0, $o, $f));
      free invariant $HeapSucc($PreLoopHeap$loop#0, $Heap);
      free invariant (forall<alpha> $o: ref, $f: Field alpha ::
        { read($Heap, $o, $f) }
        $o != null && read($PreLoopHeap$loop#0, $o, alloc)
           ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0, $o, $f) || $_Frame[$o, $f]);
      free invariant a#0 + b#0 <= $decr_init$loop#00
         && (a#0 + b#0 == $decr_init$loop#00
           ==> _module.__default.FinalStretch(pc0#0, pc1#0, a0#0, b0#0, b#0)
                 + _module.__default.FinalStretch(pc1#0, pc0#0, b1#0, a1#0, a#0)
               <= $decr_init$loop#01
             && (_module.__default.FinalStretch(pc0#0, pc1#0, a0#0, b0#0, b#0)
                   + _module.__default.FinalStretch(pc1#0, pc0#0, b1#0, a1#0, a#0)
                 == $decr_init$loop#01
               ==> (if pc0#0 == LitInt(2) && a0#0 < b0#0 && !(a#0 < b#0) then 1 else 0)
                     + (if pc1#0 == LitInt(2) && b1#0 < a1#0 && !(b#0 < a#0) then 1 else 0)
                   <= $decr_init$loop#02
                 && ((if pc0#0 == LitInt(2) && a0#0 < b0#0 && !(a#0 < b#0) then 1 else 0)
                       + (if pc1#0 == LitInt(2) && b1#0 < a1#0 && !(b#0 < a#0) then 1 else 0)
                     == $decr_init$loop#02
                   ==> (if a#0 < b#0 then budget0#0 else 0) + (if b#0 < a#0 then budget1#0 else 0)
                       <= $decr_init$loop#03
                     && ((if a#0 < b#0 then budget0#0 else 0) + (if b#0 < a#0 then budget1#0 else 0)
                         == $decr_init$loop#03
                       ==> 8 - pc0#0 - pc1#0 <= $decr_init$loop#04
                         && (8 - pc0#0 - pc1#0 == $decr_init$loop#04 ==> true)))));
    {
        assume {:captureState "Problem2.dfy(121,2): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            if (0 < a#0)
            {
            }

            assume true;
            assume 0 < a#0 && 0 < b#0;
            ##a#1 := A#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##a#1, TInt, $Heap);
            ##b#1 := B#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##b#1, TInt, $Heap);
            assert {:subsumption 0} ##a#1 > 0;
            assert {:subsumption 0} ##b#1 > 0;
            assume _module.__default.Gcd#canCall(A#0, B#0);
            ##a#2 := a#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##a#2, TInt, $Heap);
            ##b#2 := b#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##b#2, TInt, $Heap);
            assert {:subsumption 0} ##a#2 > 0;
            assert {:subsumption 0} ##b#2 > 0;
            assume _module.__default.Gcd#canCall(a#0, b#0);
            assume _module.__default.Gcd#canCall(A#0, B#0)
               && _module.__default.Gcd#canCall(a#0, b#0);
            assume _module.__default.Gcd(A#0, B#0) == _module.__default.Gcd(a#0, b#0);
            if (LitInt(0) <= pc0#0)
            {
            }

            if (LitInt(0) <= pc0#0 && pc0#0 < 4)
            {
                if (LitInt(0) <= pc1#0)
                {
                }
            }

            assume true;
            assume LitInt(0) <= pc0#0 && pc0#0 < 4 && LitInt(0) <= pc1#0 && pc1#0 < 4;
            if (pc0#0 != LitInt(0))
            {
            }

            if (pc0#0 == LitInt(0) || a0#0 == a#0)
            {
                if (pc1#0 != LitInt(0))
                {
                }
            }

            assume true;
            assume (pc0#0 == LitInt(0) || a0#0 == a#0) && (pc1#0 == LitInt(0) || b1#0 == b#0);
            if (pc0#0 == LitInt(2))
            {
                if (b#0 <= b0#0)
                {
                    if (b0#0 <= a0#0)
                    {
                    }
                }
            }

            assume true;
            assume pc0#0 == LitInt(2) ==> b#0 <= b0#0 && (b0#0 <= a0#0 ==> b0#0 == b#0);
            if (pc1#0 == LitInt(2))
            {
                if (a#0 <= a1#0)
                {
                    if (a1#0 <= b1#0)
                    {
                    }
                }
            }

            assume true;
            assume pc1#0 == LitInt(2) ==> a#0 <= a1#0 && (a1#0 <= b1#0 ==> a1#0 == a#0);
            if (pc0#0 == LitInt(3))
            {
            }

            if (pc0#0 == LitInt(3) ==> a#0 == b#0)
            {
                if (pc1#0 == LitInt(3))
                {
                }
            }

            assume true;
            assume (pc0#0 == LitInt(3) ==> a#0 == b#0) && (pc1#0 == LitInt(3) ==> a#0 == b#0);
            if (LitInt(0) <= budget0#0)
            {
            }

            if (LitInt(0) <= budget0#0 && LitInt(0) <= budget1#0)
            {
                if (pc0#0 != LitInt(3))
                {
                }

                if (!(pc0#0 == LitInt(3) || pc1#0 == LitInt(3)))
                {
                }
            }

            assume true;
            assume LitInt(0) <= budget0#0
               && LitInt(0) <= budget1#0
               && (pc0#0 == LitInt(3) || pc1#0 == LitInt(3) || LitInt(1) <= budget0#0 + budget1#0);
            assume true;
            ##pcThis#0 := pc0#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##pcThis#0, TInt, $Heap);
            ##pcThat#0 := pc1#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##pcThat#0, TInt, $Heap);
            ##a0#0 := a0#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##a0#0, TInt, $Heap);
            ##b0#0 := b0#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##b0#0, TInt, $Heap);
            ##b#3 := b#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##b#3, TInt, $Heap);
            assume _module.__default.FinalStretch#canCall(pc0#0, pc1#0, a0#0, b0#0, b#0);
            ##pcThis#1 := pc1#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##pcThis#1, TInt, $Heap);
            ##pcThat#1 := pc0#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##pcThat#1, TInt, $Heap);
            ##a0#1 := b1#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##a0#1, TInt, $Heap);
            ##b0#1 := a1#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##b0#1, TInt, $Heap);
            ##b#4 := a#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##b#4, TInt, $Heap);
            assume _module.__default.FinalStretch#canCall(pc1#0, pc0#0, b1#0, a1#0, a#0);
            assume _module.__default.FinalStretch#canCall(pc0#0, pc1#0, a0#0, b0#0, b#0)
               && _module.__default.FinalStretch#canCall(pc1#0, pc0#0, b1#0, a1#0, a#0);
            if (pc0#0 == LitInt(2))
            {
            }

            if (pc0#0 == LitInt(2) && a0#0 < b0#0)
            {
            }

            if (pc0#0 == LitInt(2) && a0#0 < b0#0 && !(a#0 < b#0))
            {
            }
            else
            {
            }

            if (pc1#0 == LitInt(2))
            {
            }

            if (pc1#0 == LitInt(2) && b1#0 < a1#0)
            {
            }

            if (pc1#0 == LitInt(2) && b1#0 < a1#0 && !(b#0 < a#0))
            {
            }
            else
            {
            }

            assume true;
            if (a#0 < b#0)
            {
            }
            else
            {
            }

            if (b#0 < a#0)
            {
            }
            else
            {
            }

            assume true;
            assume true;
            assume false;
        }

        if (pc0#0 == LitInt(3))
        {
        }

        assume true;
        if (pc0#0 == LitInt(3) && pc1#0 == LitInt(3))
        {
            break;
        }

        $decr$loop#00 := a#0 + b#0;
        $decr$loop#01 := _module.__default.FinalStretch(pc0#0, pc1#0, a0#0, b0#0, b#0)
           + _module.__default.FinalStretch(pc1#0, pc0#0, b1#0, a1#0, a#0);
        $decr$loop#02 := (if pc0#0 == LitInt(2) && a0#0 < b0#0 && !(a#0 < b#0) then 1 else 0)
           + (if pc1#0 == LitInt(2) && b1#0 < a1#0 && !(b#0 < a#0) then 1 else 0);
        $decr$loop#03 := (if a#0 < b#0 then budget0#0 else 0) + (if b#0 < a#0 then budget1#0 else 0);
        $decr$loop#04 := 8 - pc0#0 - pc1#0;
        // ----- alternative statement ----- Problem2.dfy(138,5)
        if (*)
        {
            assume true;
            assume pc0#0 == LitInt(0);
            // ----- update statement ----- Problem2.dfy(139,59)
            assume true;
            assume true;
            assume true;
            $rhs#0_9_0 := a#0;
            assume true;
            $rhs#0_9_1 := LitInt(1);
            a0#0 := $rhs#0_9_0;
            pc0#0 := $rhs#0_9_1;
            assume {:captureState "Problem2.dfy(139,65)"} true;
        }
        else if (*)
        {
            assume true;
            assume pc0#0 == LitInt(1);
            // ----- update statement ----- Problem2.dfy(140,59)
            assume true;
            assume true;
            assume true;
            $rhs#0_8_0 := b#0;
            assume true;
            $rhs#0_8_1 := LitInt(2);
            b0#0 := $rhs#0_8_0;
            pc0#0 := $rhs#0_8_1;
            assume {:captureState "Problem2.dfy(140,65)"} true;
        }
        else if (*)
        {
            if (pc0#0 == LitInt(2))
            {
                if (0 >= budget0#0)
                {
                }
            }

            if (pc0#0 == LitInt(2) && (budget0#0 > 0 || pc1#0 == LitInt(3)))
            {
            }

            assume true;
            assume pc0#0 == LitInt(2) && (budget0#0 > 0 || pc1#0 == LitInt(3)) && a0#0 > b0#0;
            // ----- call statement ----- Problem2.dfy(142,62)
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            // ProcessCallStmt: CheckSubrange
            a##0_7_0 := a#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            b##0_7_0 := b#0;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call Call$$_module.__default.GcdDecrease(a##0_7_0, b##0_7_0);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "Problem2.dfy(142,67)"} true;
            // ----- update statement ----- Problem2.dfy(143,58)
            assume true;
            assume true;
            assume true;
            $rhs#0_7_0 := a0#0 - b0#0;
            assume true;
            $rhs#0_7_1 := LitInt(0);
            a#0 := $rhs#0_7_0;
            pc0#0 := $rhs#0_7_1;
            assume {:captureState "Problem2.dfy(143,70)"} true;
            // ----- call statement ----- Problem2.dfy(144,83)
            assume true;
            assume true;
            // TrCallStmt: Adding lhs Microsoft.Dafny.IdentifierExpr with type int
            // TrCallStmt: Adding lhs Microsoft.Dafny.IdentifierExpr with type int
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            // ProcessCallStmt: CheckSubrange
            inThis##0_7_0 := budget0#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            inThat##0_7_0 := budget1#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            pcThat##0_7_0 := pc1#0;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call $rhs##0_7_0, $rhs##0_7_1 := Call$$_module.__default.BudgetUpdate(inThis##0_7_0, inThat##0_7_0, pcThat##0_7_0);
            // TrCallStmt: After ProcessCallStmt
            budget0#0 := $rhs##0_7_0;
            budget1#0 := $rhs##0_7_1;
            assume {:captureState "Problem2.dfy(144,105)"} true;
        }
        else if (*)
        {
            if (pc0#0 == LitInt(2))
            {
                if (0 >= budget0#0)
                {
                }
            }

            if (pc0#0 == LitInt(2) && (budget0#0 > 0 || pc1#0 == LitInt(3)))
            {
            }

            assume true;
            assume pc0#0 == LitInt(2) && (budget0#0 > 0 || pc1#0 == LitInt(3)) && a0#0 < b0#0;
            // ----- assignment statement ----- Problem2.dfy(146,55)
            assume true;
            assume true;
            pc0#0 := LitInt(0);
            assume {:captureState "Problem2.dfy(146,58)"} true;
            // ----- call statement ----- Problem2.dfy(147,83)
            assume true;
            assume true;
            // TrCallStmt: Adding lhs Microsoft.Dafny.IdentifierExpr with type int
            // TrCallStmt: Adding lhs Microsoft.Dafny.IdentifierExpr with type int
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            // ProcessCallStmt: CheckSubrange
            inThis##0_6_0 := budget0#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            inThat##0_6_0 := budget1#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            pcThat##0_6_0 := pc1#0;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call $rhs##0_6_0, $rhs##0_6_1 := Call$$_module.__default.BudgetUpdate(inThis##0_6_0, inThat##0_6_0, pcThat##0_6_0);
            // TrCallStmt: After ProcessCallStmt
            budget0#0 := $rhs##0_6_0;
            budget1#0 := $rhs##0_6_1;
            assume {:captureState "Problem2.dfy(147,105)"} true;
        }
        else if (*)
        {
            if (pc0#0 == LitInt(2))
            {
                if (0 >= budget0#0)
                {
                }
            }

            if (pc0#0 == LitInt(2) && (budget0#0 > 0 || pc1#0 == LitInt(3)))
            {
            }

            assume true;
            assume pc0#0 == LitInt(2) && (budget0#0 > 0 || pc1#0 == LitInt(3)) && a0#0 == b0#0;
            // ----- assignment statement ----- Problem2.dfy(149,55)
            assume true;
            assume true;
            pc0#0 := LitInt(3);
            assume {:captureState "Problem2.dfy(149,58)"} true;
            // ----- call statement ----- Problem2.dfy(150,83)
            assume true;
            assume true;
            // TrCallStmt: Adding lhs Microsoft.Dafny.IdentifierExpr with type int
            // TrCallStmt: Adding lhs Microsoft.Dafny.IdentifierExpr with type int
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            // ProcessCallStmt: CheckSubrange
            inThis##0_5_0 := budget0#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            inThat##0_5_0 := budget1#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            pcThat##0_5_0 := pc1#0;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call $rhs##0_5_0, $rhs##0_5_1 := Call$$_module.__default.BudgetUpdate(inThis##0_5_0, inThat##0_5_0, pcThat##0_5_0);
            // TrCallStmt: After ProcessCallStmt
            budget0#0 := $rhs##0_5_0;
            budget1#0 := $rhs##0_5_1;
            assume {:captureState "Problem2.dfy(150,105)"} true;
        }
        else if (*)
        {
            assume true;
            assume pc1#0 == LitInt(0);
            // ----- update statement ----- Problem2.dfy(151,59)
            assume true;
            assume true;
            assume true;
            $rhs#0_4_0 := b#0;
            assume true;
            $rhs#0_4_1 := LitInt(1);
            b1#0 := $rhs#0_4_0;
            pc1#0 := $rhs#0_4_1;
            assume {:captureState "Problem2.dfy(151,65)"} true;
        }
        else if (*)
        {
            assume true;
            assume pc1#0 == LitInt(1);
            // ----- update statement ----- Problem2.dfy(152,59)
            assume true;
            assume true;
            assume true;
            $rhs#0_3_0 := a#0;
            assume true;
            $rhs#0_3_1 := LitInt(2);
            a1#0 := $rhs#0_3_0;
            pc1#0 := $rhs#0_3_1;
            assume {:captureState "Problem2.dfy(152,65)"} true;
        }
        else if (*)
        {
            if (pc1#0 == LitInt(2))
            {
                if (0 >= budget1#0)
                {
                }
            }

            if (pc1#0 == LitInt(2) && (budget1#0 > 0 || pc0#0 == LitInt(3)))
            {
            }

            assume true;
            assume pc1#0 == LitInt(2) && (budget1#0 > 0 || pc0#0 == LitInt(3)) && b1#0 > a1#0;
            // ----- call statement ----- Problem2.dfy(154,59)
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            // ProcessCallStmt: CheckSubrange
            a##0_2_0 := a#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            b##0_2_0 := b#0;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call Call$$_module.__default.Symmetry(a##0_2_0, b##0_2_0);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "Problem2.dfy(154,64)"} true;
            // ----- call statement ----- Problem2.dfy(154,78)
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            // ProcessCallStmt: CheckSubrange
            a##0_2_1 := b#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            b##0_2_1 := a#0;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call Call$$_module.__default.GcdDecrease(a##0_2_1, b##0_2_1);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "Problem2.dfy(154,83)"} true;
            // ----- call statement ----- Problem2.dfy(154,94)
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            // ProcessCallStmt: CheckSubrange
            a##0_2_2 := b#0 - a#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            b##0_2_2 := a#0;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call Call$$_module.__default.Symmetry(a##0_2_2, b##0_2_2);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "Problem2.dfy(154,103)"} true;
            // ----- update statement ----- Problem2.dfy(155,58)
            assume true;
            assume true;
            assume true;
            $rhs#0_2_0 := b1#0 - a1#0;
            assume true;
            $rhs#0_2_1 := LitInt(0);
            b#0 := $rhs#0_2_0;
            pc1#0 := $rhs#0_2_1;
            assume {:captureState "Problem2.dfy(155,70)"} true;
            // ----- call statement ----- Problem2.dfy(156,83)
            assume true;
            assume true;
            // TrCallStmt: Adding lhs Microsoft.Dafny.IdentifierExpr with type int
            // TrCallStmt: Adding lhs Microsoft.Dafny.IdentifierExpr with type int
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            // ProcessCallStmt: CheckSubrange
            inThis##0_2_0 := budget1#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            inThat##0_2_0 := budget0#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            pcThat##0_2_0 := pc0#0;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call $rhs##0_2_0, $rhs##0_2_1 := Call$$_module.__default.BudgetUpdate(inThis##0_2_0, inThat##0_2_0, pcThat##0_2_0);
            // TrCallStmt: After ProcessCallStmt
            budget1#0 := $rhs##0_2_0;
            budget0#0 := $rhs##0_2_1;
            assume {:captureState "Problem2.dfy(156,105)"} true;
        }
        else if (*)
        {
            if (pc1#0 == LitInt(2))
            {
                if (0 >= budget1#0)
                {
                }
            }

            if (pc1#0 == LitInt(2) && (budget1#0 > 0 || pc0#0 == LitInt(3)))
            {
            }

            assume true;
            assume pc1#0 == LitInt(2) && (budget1#0 > 0 || pc0#0 == LitInt(3)) && b1#0 < a1#0;
            // ----- assignment statement ----- Problem2.dfy(158,55)
            assume true;
            assume true;
            pc1#0 := LitInt(0);
            assume {:captureState "Problem2.dfy(158,58)"} true;
            // ----- call statement ----- Problem2.dfy(159,83)
            assume true;
            assume true;
            // TrCallStmt: Adding lhs Microsoft.Dafny.IdentifierExpr with type int
            // TrCallStmt: Adding lhs Microsoft.Dafny.IdentifierExpr with type int
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            // ProcessCallStmt: CheckSubrange
            inThis##0_1_0 := budget1#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            inThat##0_1_0 := budget0#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            pcThat##0_1_0 := pc0#0;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call $rhs##0_1_0, $rhs##0_1_1 := Call$$_module.__default.BudgetUpdate(inThis##0_1_0, inThat##0_1_0, pcThat##0_1_0);
            // TrCallStmt: After ProcessCallStmt
            budget1#0 := $rhs##0_1_0;
            budget0#0 := $rhs##0_1_1;
            assume {:captureState "Problem2.dfy(159,105)"} true;
        }
        else if (*)
        {
            if (pc1#0 == LitInt(2))
            {
                if (0 >= budget1#0)
                {
                }
            }

            if (pc1#0 == LitInt(2) && (budget1#0 > 0 || pc0#0 == LitInt(3)))
            {
            }

            assume true;
            assume pc1#0 == LitInt(2) && (budget1#0 > 0 || pc0#0 == LitInt(3)) && b1#0 == a1#0;
            // ----- assignment statement ----- Problem2.dfy(161,55)
            assume true;
            assume true;
            pc1#0 := LitInt(3);
            assume {:captureState "Problem2.dfy(161,58)"} true;
            // ----- call statement ----- Problem2.dfy(162,83)
            assume true;
            assume true;
            // TrCallStmt: Adding lhs Microsoft.Dafny.IdentifierExpr with type int
            // TrCallStmt: Adding lhs Microsoft.Dafny.IdentifierExpr with type int
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            // ProcessCallStmt: CheckSubrange
            inThis##0_0_0 := budget1#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            inThat##0_0_0 := budget0#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            pcThat##0_0_0 := pc0#0;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call $rhs##0_0_0, $rhs##0_0_1 := Call$$_module.__default.BudgetUpdate(inThis##0_0_0, inThat##0_0_0, pcThat##0_0_0);
            // TrCallStmt: After ProcessCallStmt
            budget1#0 := $rhs##0_0_0;
            budget0#0 := $rhs##0_0_1;
            assume {:captureState "Problem2.dfy(162,105)"} true;
        }
        else
        {
            assume pc0#0 != LitInt(0)
               && pc0#0 != LitInt(1)
               && !
              (
              pc0#0 == LitInt(2)
               && (budget0#0 > 0 || pc1#0 == LitInt(3))
               && a0#0 > b0#0)
               && !
              (
              pc0#0 == LitInt(2)
               && (budget0#0 > 0 || pc1#0 == LitInt(3))
               && a0#0 < b0#0)
               && !
              (
              pc0#0 == LitInt(2)
               && (budget0#0 > 0 || pc1#0 == LitInt(3))
               && a0#0 == b0#0)
               && pc1#0 != LitInt(0)
               && pc1#0 != LitInt(1)
               && !
              (
              pc1#0 == LitInt(2)
               && (budget1#0 > 0 || pc0#0 == LitInt(3))
               && b1#0 > a1#0)
               && !
              (
              pc1#0 == LitInt(2)
               && (budget1#0 > 0 || pc0#0 == LitInt(3))
               && b1#0 < a1#0)
               && !
              (
              pc1#0 == LitInt(2)
               && (budget1#0 > 0 || pc0#0 == LitInt(3))
               && b1#0 == a1#0);
            assert false;
        }

        // ----- loop termination check ----- Problem2.dfy(121,3)
        assert 0 <= $decr$loop#00 || a#0 + b#0 == $decr$loop#00;
        assert 0 <= $decr$loop#01
           || a#0 + b#0 < $decr$loop#00
           || _module.__default.FinalStretch(pc0#0, pc1#0, a0#0, b0#0, b#0)
               + _module.__default.FinalStretch(pc1#0, pc0#0, b1#0, a1#0, a#0)
             == $decr$loop#01;
        assert 0 <= $decr$loop#02
           || a#0 + b#0 < $decr$loop#00
           || _module.__default.FinalStretch(pc0#0, pc1#0, a0#0, b0#0, b#0)
               + _module.__default.FinalStretch(pc1#0, pc0#0, b1#0, a1#0, a#0)
             < $decr$loop#01
           || (if pc0#0 == LitInt(2) && a0#0 < b0#0 && !(a#0 < b#0) then 1 else 0)
               + (if pc1#0 == LitInt(2) && b1#0 < a1#0 && !(b#0 < a#0) then 1 else 0)
             == $decr$loop#02;
        assert 0 <= $decr$loop#03
           || a#0 + b#0 < $decr$loop#00
           || _module.__default.FinalStretch(pc0#0, pc1#0, a0#0, b0#0, b#0)
               + _module.__default.FinalStretch(pc1#0, pc0#0, b1#0, a1#0, a#0)
             < $decr$loop#01
           || (if pc0#0 == LitInt(2) && a0#0 < b0#0 && !(a#0 < b#0) then 1 else 0)
               + (if pc1#0 == LitInt(2) && b1#0 < a1#0 && !(b#0 < a#0) then 1 else 0)
             < $decr$loop#02
           || (if a#0 < b#0 then budget0#0 else 0) + (if b#0 < a#0 then budget1#0 else 0)
             == $decr$loop#03;
        assert 0 <= $decr$loop#04
           || a#0 + b#0 < $decr$loop#00
           || _module.__default.FinalStretch(pc0#0, pc1#0, a0#0, b0#0, b#0)
               + _module.__default.FinalStretch(pc1#0, pc0#0, b1#0, a1#0, a#0)
             < $decr$loop#01
           || (if pc0#0 == LitInt(2) && a0#0 < b0#0 && !(a#0 < b#0) then 1 else 0)
               + (if pc1#0 == LitInt(2) && b1#0 < a1#0 && !(b#0 < a#0) then 1 else 0)
             < $decr$loop#02
           || (if a#0 < b#0 then budget0#0 else 0) + (if b#0 < a#0 then budget1#0 else 0)
             < $decr$loop#03
           || 8 - pc0#0 - pc1#0 == $decr$loop#04;
        assert a#0 + b#0 < $decr$loop#00
           || (a#0 + b#0 == $decr$loop#00
             && (_module.__default.FinalStretch(pc0#0, pc1#0, a0#0, b0#0, b#0)
                   + _module.__default.FinalStretch(pc1#0, pc0#0, b1#0, a1#0, a#0)
                 < $decr$loop#01
               || (_module.__default.FinalStretch(pc0#0, pc1#0, a0#0, b0#0, b#0)
                     + _module.__default.FinalStretch(pc1#0, pc0#0, b1#0, a1#0, a#0)
                   == $decr$loop#01
                 && ((if pc0#0 == LitInt(2) && a0#0 < b0#0 && !(a#0 < b#0) then 1 else 0)
                       + (if pc1#0 == LitInt(2) && b1#0 < a1#0 && !(b#0 < a#0) then 1 else 0)
                     < $decr$loop#02
                   || ((if pc0#0 == LitInt(2) && a0#0 < b0#0 && !(a#0 < b#0) then 1 else 0)
                         + (if pc1#0 == LitInt(2) && b1#0 < a1#0 && !(b#0 < a#0) then 1 else 0)
                       == $decr$loop#02
                     && ((if a#0 < b#0 then budget0#0 else 0) + (if b#0 < a#0 then budget1#0 else 0)
                         < $decr$loop#03
                       || ((if a#0 < b#0 then budget0#0 else 0) + (if b#0 < a#0 then budget1#0 else 0)
                           == $decr$loop#03
                         && 8 - pc0#0 - pc1#0 < $decr$loop#04)))))));
        assume true;
        assume _module.__default.Gcd#canCall(A#0, B#0)
           && _module.__default.Gcd#canCall(a#0, b#0);
        assume true;
        assume true;
        assume true;
        assume true;
        assume true;
        assume true;
    }

    // ----- call statement ----- Problem2.dfy(165,11)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    a##0 := a#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.GcdEqual(a##0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "Problem2.dfy(165,13)"} true;
    // ----- assignment statement ----- Problem2.dfy(166,7)
    assume true;
    assume true;
    gcd#0 := a#0;
    assume {:captureState "Problem2.dfy(166,10)"} true;
}



// function declaration for _module._default.FinalStretch
function _module.__default.FinalStretch(pcThis#0: int, pcThat#0: int, a0#0: int, b0#0: int, b#0: int) : int;

function _module.__default.FinalStretch#canCall(pcThis#0: int, pcThat#0: int, a0#0: int, b0#0: int, b#0: int) : bool;

// consequence axiom for _module.__default.FinalStretch
axiom 18 <= $FunctionContextHeight
   ==> (forall pcThis#0: int, pcThat#0: int, a0#0: int, b0#0: int, b#0: int ::
    { _module.__default.FinalStretch(pcThis#0, pcThat#0, a0#0, b0#0, b#0) }
    _module.__default.FinalStretch#canCall(pcThis#0, pcThat#0, a0#0, b0#0, b#0)
         || 18 != $FunctionContextHeight
       ==> true);

function _module.__default.FinalStretch#requires(int, int, int, int, int) : bool;

// #requires axiom for _module.__default.FinalStretch
axiom (forall pcThis#0: int, pcThat#0: int, a0#0: int, b0#0: int, b#0: int ::
  { _module.__default.FinalStretch#requires(pcThis#0, pcThat#0, a0#0, b0#0, b#0) }
  _module.__default.FinalStretch#requires(pcThis#0, pcThat#0, a0#0, b0#0, b#0)
     == true);

// definition axiom for _module.__default.FinalStretch(revealed)
axiom 18 <= $FunctionContextHeight
   ==> (forall pcThis#0: int, pcThat#0: int, a0#0: int, b0#0: int, b#0: int ::
    { _module.__default.FinalStretch(pcThis#0, pcThat#0, a0#0, b0#0, b#0) }
    _module.__default.FinalStretch#canCall(pcThis#0, pcThat#0, a0#0, b0#0, b#0)
         || 18 != $FunctionContextHeight
       ==> _module.__default.FinalStretch(pcThis#0, pcThat#0, a0#0, b0#0, b#0)
         == (if pcThat#0 != 3
           then 10
           else (if pcThis#0 == LitInt(3)
             then 0
             else (if pcThis#0 == LitInt(2) && a0#0 == b0#0
               then 1
               else (if pcThis#0 == LitInt(1) && a0#0 == b#0
                 then 2
                 else (if pcThis#0 == LitInt(0)
                   then 3
                   else (if pcThis#0 == LitInt(2) && a0#0 < b0#0 then 4 else 5)))))));

// definition axiom for _module.__default.FinalStretch for all literals(revealed)
axiom 18 <= $FunctionContextHeight
   ==> (forall pcThis#0: int, pcThat#0: int, a0#0: int, b0#0: int, b#0: int ::
    {:weight 3} { _module.__default.FinalStretch(LitInt(pcThis#0), LitInt(pcThat#0), LitInt(a0#0), LitInt(b0#0), LitInt(b#0)) }
    _module.__default.FinalStretch#canCall(LitInt(pcThis#0), LitInt(pcThat#0), LitInt(a0#0), LitInt(b0#0), LitInt(b#0))
         || 18 != $FunctionContextHeight
       ==> _module.__default.FinalStretch(LitInt(pcThis#0), LitInt(pcThat#0), LitInt(a0#0), LitInt(b0#0), LitInt(b#0))
         == (if pcThat#0 != 3
           then 10
           else (if LitInt(pcThis#0) == LitInt(3)
             then 0
             else (if LitInt(pcThis#0) == LitInt(2) && LitInt(a0#0) == LitInt(b0#0)
               then 1
               else (if LitInt(pcThis#0) == LitInt(1) && LitInt(a0#0) == LitInt(b#0)
                 then 2
                 else (if LitInt(pcThis#0) == LitInt(0)
                   then 3
                   else (if LitInt(pcThis#0) == LitInt(2) && a0#0 < b0#0 then 4 else 5)))))));

procedure CheckWellformed$$_module.__default.FinalStretch(pcThis#0: int, pcThat#0: int, a0#0: int, b0#0: int, b#0: int);
  free requires 18 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure CheckWellformed$$_module.__default.BudgetUpdate(inThis#0: int, inThat#0: int, pcThat#0: int)
   returns (outThis#0: int, outThat#0: int);
  free requires 19 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.BudgetUpdate(inThis#0: int, inThat#0: int, pcThat#0: int)
   returns (outThis#0: int, outThat#0: int);
  // user-defined preconditions
  requires pcThat#0 == LitInt(3) || 0 < inThis#0;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures outThis#0 == (if 0 < inThis#0 then inThis#0 - 1 else inThis#0);
  free ensures true;
  ensures pcThat#0 == LitInt(3) ==> outThat#0 == inThat#0;
  ensures pcThat#0 != LitInt(3) ==> outThat#0 > 0;
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.BudgetUpdate(inThis#0: int, inThat#0: int, pcThat#0: int)
   returns (outThis#0: int, outThat#0: int, $_reverifyPost: bool);
  free requires 19 == $FunctionContextHeight;
  // user-defined preconditions
  requires pcThat#0 == LitInt(3) || 0 < inThis#0;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures outThis#0 == (if 0 < inThis#0 then inThis#0 - 1 else inThis#0);
  free ensures true;
  ensures pcThat#0 == LitInt(3) ==> outThat#0 == inThat#0;
  ensures pcThat#0 != LitInt(3) ==> outThat#0 > 0;
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.BudgetUpdate(inThis#0: int, inThat#0: int, pcThat#0: int)
   returns (outThis#0: int, outThat#0: int, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: BudgetUpdate, Impl$$_module.__default.BudgetUpdate
    // initialize fuel constant
    assume AsFuelBottom(StartFuel__module._default.Divides)
       == StartFuel__module._default.Divides;
    assume AsFuelBottom(StartFuelAssert__module._default.Divides)
       == StartFuelAssert__module._default.Divides;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "Problem2.dfy(184,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- Problem2.dfy(185,11)
    assume true;
    if (0 < inThis#0)
    {
    }
    else
    {
    }

    assume true;
    outThis#0 := (if 0 < inThis#0 then inThis#0 - 1 else inThis#0);
    assume {:captureState "Problem2.dfy(185,54)"} true;
    // ----- if statement ----- Problem2.dfy(186,3)
    assume true;
    if (pcThat#0 == LitInt(3))
    {
        // ----- assignment statement ----- Problem2.dfy(187,13)
        assume true;
        assume true;
        outThat#0 := inThat#0;
        assume {:captureState "Problem2.dfy(187,21)"} true;
    }
    else
    {
        // ----- assign-such-that statement ----- Problem2.dfy(189,13)
        assume true;
        havoc outThat#0;
        assume true;
        assert ($Is(LitInt(0 + 1), TInt) && Lit(0 + 1 > 0))
           ||
          ($Is(LitInt(0), TInt) && Lit(0 > 0))
           || (exists $as#outThat0#0: int :: $as#outThat0#0 > 0);
        assume outThat#0 > 0;
        assume {:captureState "Problem2.dfy(189,26)"} true;
    }
}



// function declaration for _module._default.Gcd
function _module.__default.Gcd(a#0: int, b#0: int) : int;

function _module.__default.Gcd#canCall(a#0: int, b#0: int) : bool;

// consequence axiom for _module.__default.Gcd
axiom 8 <= $FunctionContextHeight
   ==> (forall a#0: int, b#0: int ::
    { _module.__default.Gcd(a#0, b#0) }
    _module.__default.Gcd#canCall(a#0, b#0)
         || (8 != $FunctionContextHeight && a#0 > 0 && b#0 > 0)
       ==> true);

function _module.__default.Gcd#requires(int, int) : bool;

// #requires axiom for _module.__default.Gcd
axiom (forall $Heap: Heap, a#0: int, b#0: int ::
  { _module.__default.Gcd#requires(a#0, b#0), $IsGoodHeap($Heap) }
  $IsGoodHeap($Heap)
     ==> _module.__default.Gcd#requires(a#0, b#0) == (a#0 > 0 && b#0 > 0));

function $let#0_d($heap: Heap, a: int, b: int) : int;

function $let#0$canCall($heap: Heap, a: int, b: int) : bool;

axiom (forall $heap: Heap, a: int, b: int ::
  { $let#0_d($heap, a, b) }
  $let#0$canCall($heap, a, b)
     ==> _module.__default.DividesBoth($let#0_d($heap, a, b), a, b)
       && (forall m#0: int ::
        { _module.__default.DividesBoth(m#0, a, b) }
        true
           ==>
          _module.__default.DividesBoth(m#0, a, b)
           ==> m#0 <= $let#0_d($heap, a, b)));

// definition axiom for _module.__default.Gcd(revealed)
axiom 8 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, a#0: int, b#0: int ::
    { _module.__default.Gcd(a#0, b#0), $IsGoodHeap($Heap) }
    _module.__default.Gcd#canCall(a#0, b#0)
         || (8 != $FunctionContextHeight && $IsGoodHeap($Heap) && a#0 > 0 && b#0 > 0)
       ==> $let#0$canCall($Heap, a#0, b#0)
         && _module.__default.Gcd(a#0, b#0) == $let#0_d($Heap, a#0, b#0));

// definition axiom for _module.__default.Gcd for all literals(revealed)
axiom 8 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, a#0: int, b#0: int ::
    {:weight 3} { _module.__default.Gcd(LitInt(a#0), LitInt(b#0)), $IsGoodHeap($Heap) }
    _module.__default.Gcd#canCall(LitInt(a#0), LitInt(b#0))
         || (8 != $FunctionContextHeight && $IsGoodHeap($Heap) && Lit(a#0 > 0 && b#0 > 0))
       ==> $let#0$canCall($Heap, LitInt(a#0), LitInt(b#0))
         && _module.__default.Gcd(LitInt(a#0), LitInt(b#0))
           == $let#0_d($Heap, LitInt(a#0), LitInt(b#0)));

procedure CheckWellformed$$_module.__default.Gcd(a#0: int, b#0: int);
  free requires 8 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.Gcd(a#0: int, b#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var a##0: int;
  var b##0: int;
  var d#0: int;
  var ##d#0: int;
  var ##a#0: int;
  var ##b#0: int;
  var m#1: int;
  var ##d#1: int;
  var ##a#1: int;
  var ##b#1: int;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function Gcd
    assume {:captureState "Problem2.dfy(193,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    // initialize fuel constant
    assume AsFuelBottom(StartFuel__module._default.Divides)
       == StartFuel__module._default.Divides;
    assume AsFuelBottom(StartFuelAssert__module._default.Divides)
       == StartFuelAssert__module._default.Divides;
    assume a#0 > 0;
    assume b#0 > 0;
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
          $o != null && read($Heap, $o, alloc) ==> false);
        // ----- call statement ----- Problem2.dfy(196,9)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        a##0 := a#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        b##0 := b#0;
        // ProcessCallStmt: Make the call
        call Call$$_module.__default.Exists(a##0, b##0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "Problem2.dfy(196,14)"} true;
        havoc d#0;
        ##d#0 := d#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##d#0, TInt, $Heap);
        ##a#0 := a#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##a#0, TInt, $Heap);
        ##b#0 := b#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##b#0, TInt, $Heap);
        assert {:subsumption 0} ##a#0 > 0;
        assert {:subsumption 0} ##b#0 > 0;
        assume ##a#0 > 0 && ##b#0 > 0;
        b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume _module.__default.DividesBoth#canCall(d#0, a#0, b#0);
        if (_module.__default.DividesBoth(d#0, a#0, b#0))
        {
            havoc m#1;
            // Begin Comprehension WF check
            ##d#1 := m#1;
            // assume allocatedness for argument to function
            assume $IsAlloc(##d#1, TInt, $Heap);
            ##a#1 := a#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##a#1, TInt, $Heap);
            ##b#1 := b#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##b#1, TInt, $Heap);
            assert {:subsumption 0} ##a#1 > 0;
            assert {:subsumption 0} ##b#1 > 0;
            assume ##a#1 > 0 && ##b#1 > 0;
            b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume _module.__default.DividesBoth#canCall(m#1, a#0, b#0);
            if (_module.__default.DividesBoth(m#1, a#0, b#0))
            {
            }

            // End Comprehension WF check
        }

        assert ($Is(LitInt(0), TInt)
             &&
            _module.__default.DividesBoth(LitInt(0), a#0, b#0)
             && (forall m#3: int ::
              { _module.__default.DividesBoth(m#3, a#0, b#0) }
              true ==> _module.__default.DividesBoth(m#3, a#0, b#0) ==> m#3 <= LitInt(0)))
           || (exists d#1: int ::
            _module.__default.DividesBoth(d#1, a#0, b#0)
               && (forall m#2: int ::
                { _module.__default.DividesBoth(m#2, a#0, b#0) }
                true ==> _module.__default.DividesBoth(m#2, a#0, b#0) ==> m#2 <= d#1));
        assume _module.__default.DividesBoth(d#0, a#0, b#0)
           && (forall m#4: int ::
            { _module.__default.DividesBoth(m#4, a#0, b#0) }
            true ==> _module.__default.DividesBoth(m#4, a#0, b#0) ==> m#4 <= d#0);
        assume _module.__default.Gcd(a#0, b#0) == $let#0_d($Heap, a#0, b#0);
        assume $let#0$canCall($Heap, a#0, b#0);
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.Gcd(a#0, b#0), TInt);
        assert b$reqreads#0;
        assert b$reqreads#1;
    }
}



// function declaration for _module._default.DividesBoth
function _module.__default.DividesBoth(d#0: int, a#0: int, b#0: int) : bool;

function _module.__default.DividesBoth#canCall(d#0: int, a#0: int, b#0: int) : bool;

// consequence axiom for _module.__default.DividesBoth
axiom 2 <= $FunctionContextHeight
   ==> (forall d#0: int, a#0: int, b#0: int ::
    { _module.__default.DividesBoth(d#0, a#0, b#0) }
    _module.__default.DividesBoth#canCall(d#0, a#0, b#0)
         || (2 != $FunctionContextHeight && a#0 > 0 && b#0 > 0)
       ==> true);

function _module.__default.DividesBoth#requires(int, int, int) : bool;

// #requires axiom for _module.__default.DividesBoth
axiom (forall d#0: int, a#0: int, b#0: int ::
  { _module.__default.DividesBoth#requires(d#0, a#0, b#0) }
  _module.__default.DividesBoth#requires(d#0, a#0, b#0) == (a#0 > 0 && b#0 > 0));

// definition axiom for _module.__default.DividesBoth(revealed)
axiom 2 <= $FunctionContextHeight
   ==> (forall d#0: int, a#0: int, b#0: int ::
    { _module.__default.DividesBoth(d#0, a#0, b#0) }
    _module.__default.DividesBoth#canCall(d#0, a#0, b#0)
         || (2 != $FunctionContextHeight && a#0 > 0 && b#0 > 0)
       ==> (d#0 > 0 ==> _module.__default.Divides#canCall(d#0, a#0))
         && (_module.__default.Divides#canCall(d#0, a#0)
             && _module.__default.Divides(StartFuel__module._default.Divides, d#0, a#0)
           ==> _module.__default.Divides#canCall(d#0, b#0))
         && _module.__default.DividesBoth(d#0, a#0, b#0)
           == (
            d#0 > 0
             && _module.__default.Divides(StartFuel__module._default.Divides, d#0, a#0)
             && _module.__default.Divides(StartFuel__module._default.Divides, d#0, b#0)));

// definition axiom for _module.__default.DividesBoth for all literals(revealed)
axiom 2 <= $FunctionContextHeight
   ==> (forall d#0: int, a#0: int, b#0: int ::
    {:weight 3} { _module.__default.DividesBoth(LitInt(d#0), LitInt(a#0), LitInt(b#0)) }
    _module.__default.DividesBoth#canCall(LitInt(d#0), LitInt(a#0), LitInt(b#0))
         || (2 != $FunctionContextHeight && Lit(a#0 > 0 && b#0 > 0))
       ==> (Lit(d#0 > 0) ==> _module.__default.Divides#canCall(LitInt(d#0), LitInt(a#0)))
         && (_module.__default.Divides#canCall(LitInt(d#0), LitInt(a#0))
             && _module.__default.Divides(StartFuel__module._default.Divides, LitInt(d#0), LitInt(a#0))
           ==> _module.__default.Divides#canCall(LitInt(d#0), LitInt(b#0)))
         && _module.__default.DividesBoth(LitInt(d#0), LitInt(a#0), LitInt(b#0))
           == (
            d#0 > 0
             && _module.__default.Divides(StartFuel__module._default.Divides, LitInt(d#0), LitInt(a#0))
             && _module.__default.Divides(StartFuel__module._default.Divides, LitInt(d#0), LitInt(b#0))));

procedure CheckWellformed$$_module.__default.DividesBoth(d#0: int, a#0: int, b#0: int);
  free requires 2 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.DividesBoth(d#0: int, a#0: int, b#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##d#0: int;
  var ##a#0: int;
  var ##d#1: int;
  var ##a#1: int;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function DividesBoth
    assume {:captureState "Problem2.dfy(201,10): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    // initialize fuel constant
    assume AsFuelBottom(StartFuel__module._default.Divides)
       == StartFuel__module._default.Divides;
    assume AsFuelBottom(StartFuelAssert__module._default.Divides)
       == StartFuelAssert__module._default.Divides;
    assume a#0 > 0;
    assume b#0 > 0;
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
          $o != null && read($Heap, $o, alloc) ==> false);
        if (d#0 > 0)
        {
            ##d#0 := d#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##d#0, TInt, $Heap);
            ##a#0 := a#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##a#0, TInt, $Heap);
            assert {:subsumption 0} ##d#0 > 0;
            assert {:subsumption 0} ##a#0 > 0;
            assume ##d#0 > 0 && ##a#0 > 0;
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume _module.__default.Divides#canCall(d#0, a#0);
        }

        if (d#0 > 0
           && _module.__default.Divides(StartFuel__module._default.Divides, d#0, a#0))
        {
            ##d#1 := d#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##d#1, TInt, $Heap);
            ##a#1 := b#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##a#1, TInt, $Heap);
            assert {:subsumption 0} ##d#1 > 0;
            assert {:subsumption 0} ##a#1 > 0;
            assume ##d#1 > 0 && ##a#1 > 0;
            b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume _module.__default.Divides#canCall(d#0, b#0);
        }

        assume _module.__default.DividesBoth(d#0, a#0, b#0)
           == (
            d#0 > 0
             && _module.__default.Divides(StartFuel__module._default.Divides, d#0, a#0)
             && _module.__default.Divides(StartFuel__module._default.Divides, d#0, b#0));
        assume (d#0 > 0 ==> _module.__default.Divides#canCall(d#0, a#0))
           && (_module.__default.Divides#canCall(d#0, a#0)
               && _module.__default.Divides(StartFuel__module._default.Divides, d#0, a#0)
             ==> _module.__default.Divides#canCall(d#0, b#0));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.DividesBoth(d#0, a#0, b#0), TBool);
        assert b$reqreads#0;
        assert b$reqreads#1;
    }
}



// function declaration for _module._default.Divides
function _module.__default.Divides($ly: LayerType, d#0: int, a#0: int) : bool;

function _module.__default.Divides#canCall(d#0: int, a#0: int) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, d#0: int, a#0: int ::
  { _module.__default.Divides($LS($ly), d#0, a#0) }
  _module.__default.Divides($LS($ly), d#0, a#0)
     == _module.__default.Divides($ly, d#0, a#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, d#0: int, a#0: int ::
  { _module.__default.Divides(AsFuelBottom($ly), d#0, a#0) }
  _module.__default.Divides($ly, d#0, a#0)
     == _module.__default.Divides($LZ, d#0, a#0));

// consequence axiom for _module.__default.Divides
axiom 1 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, d#0: int, a#0: int ::
    { _module.__default.Divides($ly, d#0, a#0) }
    _module.__default.Divides#canCall(d#0, a#0)
         || (1 != $FunctionContextHeight && d#0 > 0 && a#0 > 0)
       ==> true);

function _module.__default.Divides#requires(LayerType, int, int) : bool;

// #requires axiom for _module.__default.Divides
axiom (forall $ly: LayerType, d#0: int, a#0: int ::
  { _module.__default.Divides#requires($ly, d#0, a#0) }
  _module.__default.Divides#requires($ly, d#0, a#0) == (d#0 > 0 && a#0 > 0));

// definition axiom for _module.__default.Divides(revealed)
axiom 1 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, d#0: int, a#0: int ::
    { _module.__default.Divides($LS($ly), d#0, a#0) }
    _module.__default.Divides#canCall(d#0, a#0)
         || (1 != $FunctionContextHeight && d#0 > 0 && a#0 > 0)
       ==> (forall n#0: int ::
          { _module.__default.MulTriple(n#0, d#0, a#0) }
          n#0 > 0 ==> _module.__default.MulTriple#canCall(n#0, d#0, a#0))
         && _module.__default.Divides($LS($ly), d#0, a#0)
           == (exists n#0: int ::
            { _module.__default.MulTriple(n#0, d#0, a#0) }
            n#0 > 0 && _module.__default.MulTriple(n#0, d#0, a#0)));

// definition axiom for _module.__default.Divides for all literals(revealed)
axiom 1 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, d#0: int, a#0: int ::
    {:weight 3} { _module.__default.Divides($LS($ly), LitInt(d#0), LitInt(a#0)) }
    _module.__default.Divides#canCall(LitInt(d#0), LitInt(a#0))
         || (1 != $FunctionContextHeight && Lit(d#0 > 0 && a#0 > 0))
       ==> (forall n#1: int ::
          { _module.__default.MulTriple(n#1, d#0, a#0) }
          n#1 > 0 ==> _module.__default.MulTriple#canCall(n#1, LitInt(d#0), LitInt(a#0)))
         && _module.__default.Divides($LS($ly), LitInt(d#0), LitInt(a#0))
           == (exists n#1: int ::
            { _module.__default.MulTriple(n#1, d#0, a#0) }
            n#1 > 0 && _module.__default.MulTriple(n#1, LitInt(d#0), LitInt(a#0))));

procedure {:opaque} CheckWellformed$$_module.__default.Divides(d#0: int, a#0: int);
  free requires 1 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:opaque} CheckWellformed$$_module.__default.Divides(d#0: int, a#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var n#2: int;
  var ##n#0: int;
  var ##d#0: int;
  var ##a#0: int;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function Divides
    assume {:captureState "Problem2.dfy(207,20): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    // initialize fuel constant
    assume AsFuelBottom(StartFuel__module._default.Divides)
       == StartFuel__module._default.Divides;
    assume AsFuelBottom(StartFuelAssert__module._default.Divides)
       == StartFuelAssert__module._default.Divides;
    assume d#0 > 0;
    assume a#0 > 0;
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
          $o != null && read($Heap, $o, alloc) ==> false);
        havoc n#2;
        // Begin Comprehension WF check
        if (n#2 > 0)
        {
            ##n#0 := n#2;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#0, TInt, $Heap);
            ##d#0 := d#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##d#0, TInt, $Heap);
            ##a#0 := a#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##a#0, TInt, $Heap);
            assert {:subsumption 0} ##n#0 > 0;
            assert {:subsumption 0} ##d#0 > 0;
            assume ##n#0 > 0 && ##d#0 > 0;
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume _module.__default.MulTriple#canCall(n#2, d#0, a#0);
        }

        // End Comprehension WF check
        assume _module.__default.Divides(StartFuel__module._default.Divides, d#0, a#0)
           == (exists n#3: int ::
            { _module.__default.MulTriple(n#3, d#0, a#0) }
            n#3 > 0 && _module.__default.MulTriple(n#3, d#0, a#0));
        assume (forall n#3: int ::
          { _module.__default.MulTriple(n#3, d#0, a#0) }
          n#3 > 0 ==> _module.__default.MulTriple#canCall(n#3, d#0, a#0));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.Divides(StartFuel__module._default.Divides, d#0, a#0), TBool);
        assert b$reqreads#0;
    }
}



// function declaration for _module._default.MulTriple
function _module.__default.MulTriple(n#0: int, d#0: int, a#0: int) : bool;

function _module.__default.MulTriple#canCall(n#0: int, d#0: int, a#0: int) : bool;

// consequence axiom for _module.__default.MulTriple
axiom 0 <= $FunctionContextHeight
   ==> (forall n#0: int, d#0: int, a#0: int ::
    { _module.__default.MulTriple(n#0, d#0, a#0) }
    _module.__default.MulTriple#canCall(n#0, d#0, a#0)
         || (0 != $FunctionContextHeight && n#0 > 0 && d#0 > 0)
       ==> true);

function _module.__default.MulTriple#requires(int, int, int) : bool;

// #requires axiom for _module.__default.MulTriple
axiom (forall n#0: int, d#0: int, a#0: int ::
  { _module.__default.MulTriple#requires(n#0, d#0, a#0) }
  _module.__default.MulTriple#requires(n#0, d#0, a#0) == (n#0 > 0 && d#0 > 0));

// definition axiom for _module.__default.MulTriple(revealed)
axiom 0 <= $FunctionContextHeight
   ==> (forall n#0: int, d#0: int, a#0: int ::
    { _module.__default.MulTriple(n#0, d#0, a#0) }
    _module.__default.MulTriple#canCall(n#0, d#0, a#0)
         || (0 != $FunctionContextHeight && n#0 > 0 && d#0 > 0)
       ==> _module.__default.MulTriple(n#0, d#0, a#0) == (n#0 * d#0 == a#0));

// definition axiom for _module.__default.MulTriple for all literals(revealed)
axiom 0 <= $FunctionContextHeight
   ==> (forall n#0: int, d#0: int, a#0: int ::
    {:weight 3} { _module.__default.MulTriple(LitInt(n#0), LitInt(d#0), LitInt(a#0)) }
    _module.__default.MulTriple#canCall(LitInt(n#0), LitInt(d#0), LitInt(a#0))
         || (0 != $FunctionContextHeight && Lit(n#0 > 0 && d#0 > 0))
       ==> _module.__default.MulTriple(LitInt(n#0), LitInt(d#0), LitInt(a#0))
         ==
        (LitInt(n#0 * d#0)
         == LitInt(a#0)));

procedure CheckWellformed$$_module.__default.MulTriple(n#0: int, d#0: int, a#0: int);
  free requires 0 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure CheckWellformed$$_module.__default.Exists(a#0: int, b#0: int);
  free requires 7 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.Exists(a#0: int, b#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var d#0: int;
  var ##d#0: int;
  var ##a#0: int;
  var ##b#0: int;
  var m#0: int;
  var ##d#1: int;
  var ##a#1: int;
  var ##b#1: int;

    // AddMethodImpl: Exists, CheckWellformed$$_module.__default.Exists
    // initialize fuel constant
    assume AsFuelBottom(StartFuel__module._default.Divides)
       == StartFuel__module._default.Divides;
    assume AsFuelBottom(StartFuelAssert__module._default.Divides)
       == StartFuelAssert__module._default.Divides;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "Problem2.dfy(220,6): initial state"} true;
    assume a#0 > 0;
    assume b#0 > 0;
    havoc $Heap;
    assume old($Heap) == $Heap;
    assume {:captureState "Problem2.dfy(222,10): post-state"} true;
    havoc d#0;
    ##d#0 := d#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##d#0, TInt, $Heap);
    ##a#0 := a#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##a#0, TInt, $Heap);
    ##b#0 := b#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##b#0, TInt, $Heap);
    assert {:subsumption 0} ##a#0 > 0;
    assert {:subsumption 0} ##b#0 > 0;
    assume ##a#0 > 0 && ##b#0 > 0;
    assume _module.__default.DividesBoth#canCall(d#0, a#0, b#0);
    assume _module.__default.DividesBoth(d#0, a#0, b#0);
    havoc m#0;
    if (*)
    {
        ##d#1 := m#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##d#1, TInt, $Heap);
        ##a#1 := a#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##a#1, TInt, $Heap);
        ##b#1 := b#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##b#1, TInt, $Heap);
        assert {:subsumption 0} ##a#1 > 0;
        assert {:subsumption 0} ##b#1 > 0;
        assume ##a#1 > 0 && ##b#1 > 0;
        assume _module.__default.DividesBoth#canCall(m#0, a#0, b#0);
        assume _module.__default.DividesBoth(m#0, a#0, b#0);
        assume m#0 <= d#0;
    }
    else
    {
        assume _module.__default.DividesBoth(m#0, a#0, b#0) ==> m#0 <= d#0;
    }

    assume (forall m#1: int ::
      { _module.__default.DividesBoth(m#1, a#0, b#0) }
      true ==> _module.__default.DividesBoth(m#1, a#0, b#0) ==> m#1 <= d#0);
}



procedure Call$$_module.__default.Exists(a#0: int, b#0: int);
  // user-defined preconditions
  requires a#0 > 0;
  requires b#0 > 0;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall d#1: int ::
    { _module.__default.DividesBoth(d#1, a#0, b#0) }
    _module.__default.DividesBoth#canCall(d#1, a#0, b#0)
       && (_module.__default.DividesBoth(d#1, a#0, b#0)
         ==> (forall m#2: int ::
          { _module.__default.DividesBoth(m#2, a#0, b#0) }
          _module.__default.DividesBoth#canCall(m#2, a#0, b#0))));
  ensures (exists d#1: int ::
    { _module.__default.DividesBoth(d#1, a#0, b#0) }
    _module.__default.DividesBoth(d#1, a#0, b#0)
       && (forall m#2: int ::
        { _module.__default.DividesBoth(m#2, a#0, b#0) }
        true ==> _module.__default.DividesBoth(m#2, a#0, b#0) ==> m#2 <= d#1));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.Exists(a#0: int, b#0: int) returns ($_reverifyPost: bool);
  free requires 7 == $FunctionContextHeight;
  // user-defined preconditions
  requires a#0 > 0;
  requires b#0 > 0;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall d#1: int ::
    { _module.__default.DividesBoth(d#1, a#0, b#0) }
    _module.__default.DividesBoth#canCall(d#1, a#0, b#0)
       && (_module.__default.DividesBoth(d#1, a#0, b#0)
         ==> (forall m#2: int ::
          { _module.__default.DividesBoth(m#2, a#0, b#0) }
          _module.__default.DividesBoth#canCall(m#2, a#0, b#0))));
  ensures (exists d#1: int ::
    { _module.__default.DividesBoth(d#1, a#0, b#0) }
    _module.__default.DividesBoth(d#1, a#0, b#0)
       && (forall m#2: int ::
        { _module.__default.DividesBoth(m#2, a#0, b#0) }
        true ==> _module.__default.DividesBoth(m#2, a#0, b#0) ==> m#2 <= d#1));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.Exists(a#0: int, b#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var d#2: int;
  var $rhs##0: int;
  var a##0: int;
  var b##0: int;

    // AddMethodImpl: Exists, Impl$$_module.__default.Exists
    // initialize fuel constant
    assume AsFuelBottom(StartFuel__module._default.Divides)
       == StartFuel__module._default.Divides;
    assume AsFuelBottom(StartFuelAssert__module._default.Divides)
       == StartFuelAssert__module._default.Divides;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "Problem2.dfy(223,0): initial state"} true;
    $_reverifyPost := false;
    // ----- call statement ----- Problem2.dfy(224,22)
    assume true;
    // TrCallStmt: Adding lhs Microsoft.Dafny.AutoGhostIdentifierExpr with type int
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    a##0 := a#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    b##0 := b#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##0 := Call$$_module.__default.ShowExists(a##0, b##0);
    // TrCallStmt: After ProcessCallStmt
    d#2 := $rhs##0;
    assume {:captureState "Problem2.dfy(224,27)"} true;
}



procedure CheckWellformed$$_module.__default.ShowExists(a#0: int, b#0: int) returns (d#0: int);
  free requires 6 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.ShowExists(a#0: int, b#0: int) returns (d#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##d#0: int;
  var ##a#0: int;
  var ##b#0: int;
  var m#0: int;
  var ##d#1: int;
  var ##a#1: int;
  var ##b#1: int;

    // AddMethodImpl: ShowExists, CheckWellformed$$_module.__default.ShowExists
    // initialize fuel constant
    assume AsFuelBottom(StartFuel__module._default.Divides)
       == StartFuel__module._default.Divides;
    assume AsFuelBottom(StartFuelAssert__module._default.Divides)
       == StartFuelAssert__module._default.Divides;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "Problem2.dfy(227,6): initial state"} true;
    assume a#0 > 0;
    assume b#0 > 0;
    havoc $Heap;
    assume old($Heap) == $Heap;
    havoc d#0;
    assume {:captureState "Problem2.dfy(229,31): post-state"} true;
    ##d#0 := d#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##d#0, TInt, $Heap);
    ##a#0 := a#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##a#0, TInt, $Heap);
    ##b#0 := b#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##b#0, TInt, $Heap);
    assert {:subsumption 0} ##a#0 > 0;
    assert {:subsumption 0} ##b#0 > 0;
    assume ##a#0 > 0 && ##b#0 > 0;
    assume _module.__default.DividesBoth#canCall(d#0, a#0, b#0);
    assume _module.__default.DividesBoth(d#0, a#0, b#0);
    havoc m#0;
    if (*)
    {
        ##d#1 := m#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##d#1, TInt, $Heap);
        ##a#1 := a#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##a#1, TInt, $Heap);
        ##b#1 := b#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##b#1, TInt, $Heap);
        assert {:subsumption 0} ##a#1 > 0;
        assert {:subsumption 0} ##b#1 > 0;
        assume ##a#1 > 0 && ##b#1 > 0;
        assume _module.__default.DividesBoth#canCall(m#0, a#0, b#0);
        assume _module.__default.DividesBoth(m#0, a#0, b#0);
        assume m#0 <= d#0;
    }
    else
    {
        assume _module.__default.DividesBoth(m#0, a#0, b#0) ==> m#0 <= d#0;
    }

    assume (forall m#1: int ::
      { _module.__default.DividesBoth(m#1, a#0, b#0) }
      true ==> _module.__default.DividesBoth(m#1, a#0, b#0) ==> m#1 <= d#0);
}



procedure Call$$_module.__default.ShowExists(a#0: int, b#0: int) returns (d#0: int);
  // user-defined preconditions
  requires a#0 > 0;
  requires b#0 > 0;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.DividesBoth#canCall(d#0, a#0, b#0)
     && (_module.__default.DividesBoth(d#0, a#0, b#0)
       ==> (forall m#1: int ::
        { _module.__default.DividesBoth(m#1, a#0, b#0) }
        _module.__default.DividesBoth#canCall(m#1, a#0, b#0)));
  free ensures _module.__default.DividesBoth#canCall(d#0, a#0, b#0)
     &&
    _module.__default.DividesBoth(d#0, a#0, b#0)
     &&
    d#0 > 0
     && _module.__default.Divides(StartFuel__module._default.Divides, d#0, a#0)
     && _module.__default.Divides(StartFuel__module._default.Divides, d#0, b#0);
  ensures (forall m#1: int ::
    { _module.__default.DividesBoth(m#1, a#0, b#0) }
    true ==> _module.__default.DividesBoth(m#1, a#0, b#0) ==> m#1 <= d#0);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.ShowExists(a#0: int, b#0: int) returns (d#0: int, $_reverifyPost: bool);
  free requires 6 == $FunctionContextHeight;
  // user-defined preconditions
  requires a#0 > 0;
  requires b#0 > 0;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.DividesBoth#canCall(d#0, a#0, b#0)
     && (_module.__default.DividesBoth(d#0, a#0, b#0)
       ==> (forall m#1: int ::
        { _module.__default.DividesBoth(m#1, a#0, b#0) }
        _module.__default.DividesBoth#canCall(m#1, a#0, b#0)));
  ensures _module.__default.DividesBoth#canCall(d#0, a#0, b#0)
     ==> _module.__default.DividesBoth(d#0, a#0, b#0) || d#0 > 0;
  ensures _module.__default.DividesBoth#canCall(d#0, a#0, b#0)
     ==> _module.__default.DividesBoth(d#0, a#0, b#0)
       || _module.__default.Divides(StartFuelAssert__module._default.Divides, d#0, a#0);
  ensures _module.__default.DividesBoth#canCall(d#0, a#0, b#0)
     ==> _module.__default.DividesBoth(d#0, a#0, b#0)
       || _module.__default.Divides(StartFuelAssert__module._default.Divides, d#0, b#0);
  ensures (forall m#1: int ::
    { _module.__default.DividesBoth(m#1, a#0, b#0) }
    true ==> _module.__default.DividesBoth(m#1, a#0, b#0) ==> m#1 <= d#0);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.ShowExists(a#0: int, b#0: int) returns (d#0: int, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var a##0: int;
  var a##1: int;
  var ##d#2: int;
  var ##a#2: int;
  var ##d#3: int;
  var ##a#3: int;
  var ##d#4: int;
  var ##a#4: int;
  var ##b#2: int;
  var ##d#5: int;
  var ##a#5: int;
  var ##b#3: int;
  var d##0: int;
  var a##2: int;
  var d##1: int;
  var a##3: int;
  var $PreLoopHeap$loop#0: Heap;
  var $decr_init$loop#00: int;
  var $w$loop#0: bool;
  var ##d#6: int;
  var ##a#6: int;
  var ##b#4: int;
  var $decr$loop#00: int;
  var k#0_0: int;
  var ##d#0_0: int;
  var ##a#0_0: int;
  var ##b#0_0: int;
  var k#0_0_0: int;
  var ##d#0_0_0: int;
  var ##a#0_0_0: int;
  var ##b#0_0_0: int;
  var ##d#0_0_1: int;
  var ##a#0_0_1: int;
  var d##0_0_0: int;
  var a##0_0_0: int;
  var d##0_0_1: int;
  var a##0_0_1: int;

    // AddMethodImpl: ShowExists, Impl$$_module.__default.ShowExists
    // initialize fuel constant
    assume AsFuelBottom(StartFuel__module._default.Divides)
       == StartFuel__module._default.Divides;
    assume AsFuelBottom(StartFuelAssert__module._default.Divides)
       == StartFuelAssert__module._default.Divides;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "Problem2.dfy(230,0): initial state"} true;
    $_reverifyPost := false;
    // ----- forall statement (proof) ----- Problem2.dfy(231,3)
    if (*)
    {
        // Assume Fuel Constant
        assume true;
        assume true;
        // ----- call statement ----- Problem2.dfy(234,23)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        a##0 := a#0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$_module.__default.OneDividesAnything(a##0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "Problem2.dfy(234,25)"} true;
        // ----- call statement ----- Problem2.dfy(235,23)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        a##1 := b#0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$_module.__default.OneDividesAnything(a##1);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "Problem2.dfy(235,25)"} true;
        // ----- assert statement ----- Problem2.dfy(236,5)
        ##d#2 := LitInt(1);
        // assume allocatedness for argument to function
        assume $IsAlloc(##d#2, TInt, $Heap);
        ##a#2 := a#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##a#2, TInt, $Heap);
        assert {:subsumption 0} ##d#2 > 0;
        assert {:subsumption 0} ##a#2 > 0;
        assume _module.__default.Divides#canCall(LitInt(1), a#0);
        assume _module.__default.Divides#canCall(LitInt(1), a#0);
        assert {:subsumption 0} _module.__default.Divides(StartFuelAssert__module._default.Divides, LitInt(1), a#0);
        assume _module.__default.Divides(StartFuelAssert__module._default.Divides, LitInt(1), a#0);
        // ----- assert statement ----- Problem2.dfy(237,5)
        ##d#3 := LitInt(1);
        // assume allocatedness for argument to function
        assume $IsAlloc(##d#3, TInt, $Heap);
        ##a#3 := b#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##a#3, TInt, $Heap);
        assert {:subsumption 0} ##d#3 > 0;
        assert {:subsumption 0} ##a#3 > 0;
        assume _module.__default.Divides#canCall(LitInt(1), b#0);
        assume _module.__default.Divides#canCall(LitInt(1), b#0);
        assert {:subsumption 0} _module.__default.Divides(StartFuelAssert__module._default.Divides, LitInt(1), b#0);
        assume _module.__default.Divides(StartFuelAssert__module._default.Divides, LitInt(1), b#0);
        // ----- assert statement ----- Problem2.dfy(238,5)
        ##d#4 := LitInt(1);
        // assume allocatedness for argument to function
        assume $IsAlloc(##d#4, TInt, $Heap);
        ##a#4 := a#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##a#4, TInt, $Heap);
        ##b#2 := b#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##b#2, TInt, $Heap);
        assert {:subsumption 0} ##a#4 > 0;
        assert {:subsumption 0} ##b#2 > 0;
        assume _module.__default.DividesBoth#canCall(LitInt(1), a#0, b#0);
        assume _module.__default.DividesBoth#canCall(LitInt(1), a#0, b#0);
        assert {:subsumption 0} _module.__default.DividesBoth#canCall(LitInt(1), a#0, b#0)
           ==> _module.__default.DividesBoth(LitInt(1), a#0, b#0) || Lit(1 > 0);
        assert {:subsumption 0} _module.__default.DividesBoth#canCall(LitInt(1), a#0, b#0)
           ==> _module.__default.DividesBoth(LitInt(1), a#0, b#0)
             || _module.__default.Divides(StartFuelAssert__module._default.Divides, LitInt(1), a#0);
        assert {:subsumption 0} _module.__default.DividesBoth#canCall(LitInt(1), a#0, b#0)
           ==> _module.__default.DividesBoth(LitInt(1), a#0, b#0)
             || _module.__default.Divides(StartFuelAssert__module._default.Divides, LitInt(1), b#0);
        assume _module.__default.DividesBoth(LitInt(1), a#0, b#0);
        assert (exists d#1: int ::
          { _module.__default.DividesBoth(d#1, a#0, b#0) }
          _module.__default.DividesBoth(d#1, a#0, b#0));
        assume false;
    }
    else
    {
        assume Lit(true)
           ==> (exists d#2: int ::
            { _module.__default.DividesBoth(d#2, a#0, b#0) }
            _module.__default.DividesBoth(d#2, a#0, b#0));
    }

    assume {:captureState "Problem2.dfy(239,2)"} true;
    // ----- assign-such-that statement ----- Problem2.dfy(240,5)
    assume true;
    havoc d#0;
    ##d#5 := d#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##d#5, TInt, $Heap);
    ##a#5 := a#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##a#5, TInt, $Heap);
    ##b#3 := b#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##b#3, TInt, $Heap);
    assert {:subsumption 0} ##a#5 > 0;
    assert {:subsumption 0} ##b#3 > 0;
    assume _module.__default.DividesBoth#canCall(d#0, a#0, b#0);
    assume _module.__default.DividesBoth#canCall(d#0, a#0, b#0);
    assert ($Is(LitInt(0), TInt) && _module.__default.DividesBoth(LitInt(0), a#0, b#0))
       || (exists $as#d0#0: int :: _module.__default.DividesBoth($as#d0#0, a#0, b#0));
    assume _module.__default.DividesBoth(d#0, a#0, b#0);
    assume {:captureState "Problem2.dfy(240,27)"} true;
    // ----- call statement ----- Problem2.dfy(241,20)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    d##0 := d#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    a##2 := a#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.DividesUpperBound(d##0, a##2);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "Problem2.dfy(241,25)"} true;
    // ----- call statement ----- Problem2.dfy(242,20)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    d##1 := d#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    a##3 := b#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.DividesUpperBound(d##1, a##3);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "Problem2.dfy(242,25)"} true;
    // ----- while statement ----- Problem2.dfy(243,3)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    $decr_init$loop#00 := a#0 + b#0 - 2 * d#0;
    havoc $w$loop#0;
    while (true)
      free invariant $w$loop#0 ==> _module.__default.DividesBoth#canCall(d#0, a#0, b#0);
      invariant $w$loop#0
         ==>
        _module.__default.DividesBoth#canCall(d#0, a#0, b#0)
         ==> _module.__default.DividesBoth(d#0, a#0, b#0) || d#0 > 0;
      invariant $w$loop#0
         ==>
        _module.__default.DividesBoth#canCall(d#0, a#0, b#0)
         ==> _module.__default.DividesBoth(d#0, a#0, b#0)
           || _module.__default.Divides(StartFuelAssert__module._default.Divides, d#0, a#0);
      invariant $w$loop#0
         ==>
        _module.__default.DividesBoth#canCall(d#0, a#0, b#0)
         ==> _module.__default.DividesBoth(d#0, a#0, b#0)
           || _module.__default.Divides(StartFuelAssert__module._default.Divides, d#0, b#0);
      free invariant $w$loop#0
         ==> _module.__default.DividesBoth#canCall(d#0, a#0, b#0)
           &&
          _module.__default.DividesBoth(d#0, a#0, b#0)
           &&
          d#0 > 0
           && _module.__default.Divides(StartFuel__module._default.Divides, d#0, a#0)
           && _module.__default.Divides(StartFuel__module._default.Divides, d#0, b#0);
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0 ==> d#0 <= a#0;
      invariant $w$loop#0 ==> d#0 <= b#0;
      free invariant $PreLoopHeap$loop#0 == $Heap;
      free invariant (forall<alpha> $o: ref, $f: Field alpha ::
        { read($Heap, $o, $f) }
        $o != null && read($PreLoopHeap$loop#0, $o, alloc)
           ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0, $o, $f) || $_Frame[$o, $f]);
      free invariant a#0 + b#0 - 2 * d#0 <= $decr_init$loop#00
         && (a#0 + b#0 - 2 * d#0 == $decr_init$loop#00 ==> true);
    {
        assume {:captureState "Problem2.dfy(243,2): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            ##d#6 := d#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##d#6, TInt, $Heap);
            ##a#6 := a#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##a#6, TInt, $Heap);
            ##b#4 := b#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##b#4, TInt, $Heap);
            assert {:subsumption 0} ##a#6 > 0;
            assert {:subsumption 0} ##b#4 > 0;
            assume _module.__default.DividesBoth#canCall(d#0, a#0, b#0);
            assume _module.__default.DividesBoth#canCall(d#0, a#0, b#0);
            assume _module.__default.DividesBoth(d#0, a#0, b#0);
            if (d#0 <= a#0)
            {
            }

            assume true;
            assume d#0 <= a#0 && d#0 <= b#0;
            assume true;
            assume false;
        }

        assume true;
        if (!Lit(true))
        {
            break;
        }

        $decr$loop#00 := a#0 + b#0 - 2 * d#0;
        // ----- if statement ----- Problem2.dfy(248,5)
        havoc k#0_0;
        // Begin Comprehension WF check
        ##d#0_0 := k#0_0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##d#0_0, TInt, $Heap);
        ##a#0_0 := a#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##a#0_0, TInt, $Heap);
        ##b#0_0 := b#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##b#0_0, TInt, $Heap);
        assert {:subsumption 0} ##a#0_0 > 0;
        assert {:subsumption 0} ##b#0_0 > 0;
        assume ##a#0_0 > 0 && ##b#0_0 > 0;
        assume _module.__default.DividesBoth#canCall(k#0_0, a#0, b#0);
        if (_module.__default.DividesBoth(k#0_0, a#0, b#0))
        {
        }

        // End Comprehension WF check
        assume (forall k#0_1: int ::
          { _module.__default.DividesBoth(k#0_1, a#0, b#0) }
          _module.__default.DividesBoth#canCall(k#0_1, a#0, b#0));
        if ((exists k#0_1: int ::
          { _module.__default.DividesBoth(k#0_1, a#0, b#0) }
          _module.__default.DividesBoth(k#0_1, a#0, b#0) && k#0_1 > d#0))
        {
            // ----- assign-such-that statement ----- Problem2.dfy(249,13)
            assume true;
            havoc k#0_0_0;
            ##d#0_0_0 := k#0_0_0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##d#0_0_0, TInt, $Heap);
            ##a#0_0_0 := a#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##a#0_0_0, TInt, $Heap);
            ##b#0_0_0 := b#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##b#0_0_0, TInt, $Heap);
            assert {:subsumption 0} ##a#0_0_0 > 0;
            assert {:subsumption 0} ##b#0_0_0 > 0;
            assume _module.__default.DividesBoth#canCall(k#0_0_0, a#0, b#0);
            if (_module.__default.DividesBoth(k#0_0_0, a#0, b#0))
            {
            }

            assume _module.__default.DividesBoth#canCall(k#0_0_0, a#0, b#0);
            assert ($Is(d#0 + 1, TInt)
                 &&
                _module.__default.DividesBoth(d#0 + 1, a#0, b#0)
                 && d#0 + 1 > d#0)
               ||
              ($Is(LitInt(0), TInt)
                 &&
                _module.__default.DividesBoth(LitInt(0), a#0, b#0)
                 && 0 > d#0)
               || (exists $as#k0_0_0#0_0_0: int ::
                _module.__default.DividesBoth($as#k0_0_0#0_0_0, a#0, b#0)
                   && $as#k0_0_0#0_0_0 > d#0);
            assume _module.__default.DividesBoth(k#0_0_0, a#0, b#0) && k#0_0_0 > d#0;
            assume {:captureState "Problem2.dfy(249,44)"} true;
            // ----- assignment statement ----- Problem2.dfy(250,9)
            assume true;
            assume true;
            d#0 := k#0_0_0;
            assume {:captureState "Problem2.dfy(250,12)"} true;
            // ----- assert statement ----- Problem2.dfy(251,7)
            ##d#0_0_1 := d#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##d#0_0_1, TInt, $Heap);
            ##a#0_0_1 := a#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##a#0_0_1, TInt, $Heap);
            assert {:subsumption 0} ##d#0_0_1 > 0;
            assert {:subsumption 0} ##a#0_0_1 > 0;
            assume _module.__default.Divides#canCall(d#0, a#0);
            assume _module.__default.Divides#canCall(d#0, a#0);
            assert {:subsumption 0} _module.__default.Divides(StartFuelAssert__module._default.Divides, d#0, a#0);
            assume _module.__default.Divides(StartFuelAssert__module._default.Divides, d#0, a#0);
            // ----- call statement ----- Problem2.dfy(252,24)
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            // ProcessCallStmt: CheckSubrange
            d##0_0_0 := d#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            a##0_0_0 := a#0;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call Call$$_module.__default.DividesUpperBound(d##0_0_0, a##0_0_0);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "Problem2.dfy(252,29)"} true;
            // ----- assert statement ----- Problem2.dfy(253,7)
            assume true;
            assert d#0 <= a#0;
            // ----- call statement ----- Problem2.dfy(254,24)
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            // ProcessCallStmt: CheckSubrange
            d##0_0_1 := d#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            a##0_0_1 := b#0;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call Call$$_module.__default.DividesUpperBound(d##0_0_1, a##0_0_1);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "Problem2.dfy(254,29)"} true;
            // ----- assert statement ----- Problem2.dfy(255,7)
            assume true;
            assert d#0 <= b#0;
        }
        else
        {
            // ----- return statement ----- Problem2.dfy(257,7)
            return;
        }

        // ----- loop termination check ----- Problem2.dfy(243,3)
        assert 0 <= $decr$loop#00 || a#0 + b#0 - 2 * d#0 == $decr$loop#00;
        assert a#0 + b#0 - 2 * d#0 < $decr$loop#00;
        assume _module.__default.DividesBoth#canCall(d#0, a#0, b#0);
        assume true;
    }
}



procedure CheckWellformed$$_module.__default.OneDividesAnything(a#0: int);
  free requires 4 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.OneDividesAnything(a#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##d#0: int;
  var ##a#0: int;

    // AddMethodImpl: OneDividesAnything, CheckWellformed$$_module.__default.OneDividesAnything
    // initialize fuel constant
    assume AsFuelBottom(StartFuel__module._default.Divides)
       == StartFuel__module._default.Divides;
    assume AsFuelBottom(StartFuelAssert__module._default.Divides)
       == StartFuelAssert__module._default.Divides;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "Problem2.dfy(262,6): initial state"} true;
    assume a#0 > 0;
    havoc $Heap;
    assume old($Heap) == $Heap;
    assume {:captureState "Problem2.dfy(264,17): post-state"} true;
    ##d#0 := LitInt(1);
    // assume allocatedness for argument to function
    assume $IsAlloc(##d#0, TInt, $Heap);
    ##a#0 := a#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##a#0, TInt, $Heap);
    assert {:subsumption 0} ##d#0 > 0;
    assert {:subsumption 0} ##a#0 > 0;
    assume ##d#0 > 0 && ##a#0 > 0;
    assume _module.__default.Divides#canCall(LitInt(1), a#0);
    assume _module.__default.Divides(StartFuel__module._default.Divides, LitInt(1), a#0);
}



procedure Call$$_module.__default.OneDividesAnything(a#0: int);
  // user-defined preconditions
  requires a#0 > 0;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Divides#canCall(LitInt(1), a#0);
  ensures _module.__default.Divides(StartFuelAssert__module._default.Divides, LitInt(1), a#0);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.OneDividesAnything(a#0: int) returns ($_reverifyPost: bool);
  free requires 4 == $FunctionContextHeight;
  // user-defined preconditions
  requires a#0 > 0;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Divides#canCall(LitInt(1), a#0);
  ensures _module.__default.Divides(StartFuelAssert__module._default.Divides, LitInt(1), a#0);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.OneDividesAnything(a#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##n#0: int;
  var ##d#1: int;
  var ##a#1: int;

    // AddMethodImpl: OneDividesAnything, Impl$$_module.__default.OneDividesAnything
    // initialize fuel constant
    assume AsFuelBottom(StartFuel__module._default.Divides)
       == StartFuel__module._default.Divides;
    assume AsFuelBottom(StartFuelAssert__module._default.Divides)
       == StartFuelAssert__module._default.Divides;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "Problem2.dfy(265,0): initial state"} true;
    $_reverifyPost := false;
    // ----- reveal statement ----- Problem2.dfy(266,3)
    // ----- call statement ----- Problem2.dfy(266,17)
    // TrCallStmt: Before ProcessCallStmt
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.reveal__Divides();
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "Problem2.dfy(266,18)"} true;
    // ----- assert statement ----- Problem2.dfy(267,3)
    ##n#0 := a#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#0, TInt, $Heap);
    ##d#1 := LitInt(1);
    // assume allocatedness for argument to function
    assume $IsAlloc(##d#1, TInt, $Heap);
    ##a#1 := a#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##a#1, TInt, $Heap);
    assert {:subsumption 0} ##n#0 > 0;
    assert {:subsumption 0} ##d#1 > 0;
    assume _module.__default.MulTriple#canCall(a#0, LitInt(1), a#0);
    assume _module.__default.MulTriple#canCall(a#0, LitInt(1), a#0);
    assert {:subsumption 0} _module.__default.MulTriple#canCall(a#0, LitInt(1), a#0)
       ==> _module.__default.MulTriple(a#0, LitInt(1), a#0) || a#0 * 1 == a#0;
    assume _module.__default.MulTriple(a#0, LitInt(1), a#0);
}



procedure CheckWellformed$$_module.__default.GcdEqual(a#0: int);
  free requires 14 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.GcdEqual(a#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##a#0: int;
  var ##b#0: int;

    // AddMethodImpl: GcdEqual, CheckWellformed$$_module.__default.GcdEqual
    // initialize fuel constant
    assume AsFuelBottom(StartFuel__module._default.Divides)
       == StartFuel__module._default.Divides;
    assume AsFuelBottom(StartFuelAssert__module._default.Divides)
       == StartFuelAssert__module._default.Divides;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "Problem2.dfy(270,6): initial state"} true;
    assume a#0 > 0;
    havoc $Heap;
    assume old($Heap) == $Heap;
    assume {:captureState "Problem2.dfy(272,20): post-state"} true;
    ##a#0 := a#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##a#0, TInt, $Heap);
    ##b#0 := a#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##b#0, TInt, $Heap);
    assert {:subsumption 0} ##a#0 > 0;
    assert {:subsumption 0} ##b#0 > 0;
    assume ##a#0 > 0 && ##b#0 > 0;
    assume _module.__default.Gcd#canCall(a#0, a#0);
    assume _module.__default.Gcd(a#0, a#0) == a#0;
}



procedure Call$$_module.__default.GcdEqual(a#0: int);
  // user-defined preconditions
  requires a#0 > 0;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Gcd#canCall(a#0, a#0);
  ensures _module.__default.Gcd(a#0, a#0) == a#0;
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.GcdEqual(a#0: int) returns ($_reverifyPost: bool);
  free requires 14 == $FunctionContextHeight;
  // user-defined preconditions
  requires a#0 > 0;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Gcd#canCall(a#0, a#0);
  ensures _module.__default.Gcd(a#0, a#0) == a#0;
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.GcdEqual(a#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var a##0: int;
  var ##d#0: int;
  var ##a#1: int;
  var d##0: int;
  var a##1: int;
  var ##d#1: int;
  var ##a#2: int;
  var ##b#1: int;
  var k#0: int;
  var ##a#3: int;
  var ##b#2: int;
  var ##d#2: int;
  var ##a#4: int;
  var ##b#3: int;
  var m#0: int;
  var ##d#3: int;
  var ##a#5: int;
  var ##b#4: int;
  var ##d#4: int;
  var ##a#6: int;
  var d##1: int;
  var a##2: int;

    // AddMethodImpl: GcdEqual, Impl$$_module.__default.GcdEqual
    // initialize fuel constant
    assume AsFuelBottom(StartFuel__module._default.Divides)
       == StartFuel__module._default.Divides;
    assume AsFuelBottom(StartFuelAssert__module._default.Divides)
       == StartFuelAssert__module._default.Divides;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "Problem2.dfy(273,0): initial state"} true;
    $_reverifyPost := false;
    // ----- call statement ----- Problem2.dfy(274,20)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    a##0 := a#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.DividesIdempotent(a##0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "Problem2.dfy(274,22)"} true;
    // ----- assert statement ----- Problem2.dfy(275,3)
    ##d#0 := a#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##d#0, TInt, $Heap);
    ##a#1 := a#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##a#1, TInt, $Heap);
    assert {:subsumption 0} ##d#0 > 0;
    assert {:subsumption 0} ##a#1 > 0;
    assume _module.__default.Divides#canCall(a#0, a#0);
    assume _module.__default.Divides#canCall(a#0, a#0);
    assert {:subsumption 0} _module.__default.Divides(StartFuelAssert__module._default.Divides, a#0, a#0);
    assume _module.__default.Divides(StartFuelAssert__module._default.Divides, a#0, a#0);
    // ----- call statement ----- Problem2.dfy(276,20)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    d##0 := a#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    a##1 := a#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.DividesUpperBound(d##0, a##1);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "Problem2.dfy(276,25)"} true;
    // ----- assert statement ----- Problem2.dfy(277,3)
    ##d#1 := a#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##d#1, TInt, $Heap);
    ##a#2 := a#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##a#2, TInt, $Heap);
    ##b#1 := a#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##b#1, TInt, $Heap);
    assert {:subsumption 0} ##a#2 > 0;
    assert {:subsumption 0} ##b#1 > 0;
    assume _module.__default.DividesBoth#canCall(a#0, a#0, a#0);
    assume _module.__default.DividesBoth#canCall(a#0, a#0, a#0);
    assert {:subsumption 0} _module.__default.DividesBoth#canCall(a#0, a#0, a#0)
       ==> _module.__default.DividesBoth(a#0, a#0, a#0) || a#0 > 0;
    assert {:subsumption 0} _module.__default.DividesBoth#canCall(a#0, a#0, a#0)
       ==> _module.__default.DividesBoth(a#0, a#0, a#0)
         || _module.__default.Divides(StartFuelAssert__module._default.Divides, a#0, a#0);
    assert {:subsumption 0} _module.__default.DividesBoth#canCall(a#0, a#0, a#0)
       ==> _module.__default.DividesBoth(a#0, a#0, a#0)
         || _module.__default.Divides(StartFuelAssert__module._default.Divides, a#0, a#0);
    assume _module.__default.DividesBoth(a#0, a#0, a#0);
    // ----- assignment statement ----- Problem2.dfy(279,9)
    assume true;
    ##a#3 := a#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##a#3, TInt, $Heap);
    ##b#2 := a#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##b#2, TInt, $Heap);
    assert {:subsumption 0} ##a#3 > 0;
    assert {:subsumption 0} ##b#2 > 0;
    assume ##a#3 > 0 && ##b#2 > 0;
    assume _module.__default.Gcd#canCall(a#0, a#0);
    assume _module.__default.Gcd#canCall(a#0, a#0);
    k#0 := _module.__default.Gcd(a#0, a#0);
    assume {:captureState "Problem2.dfy(279,20)"} true;
    // ----- assert statement ----- Problem2.dfy(280,3)
    if (k#0 > 0)
    {
        ##d#2 := k#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##d#2, TInt, $Heap);
        ##a#4 := a#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##a#4, TInt, $Heap);
        ##b#3 := a#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##b#3, TInt, $Heap);
        assert {:subsumption 0} ##a#4 > 0;
        assert {:subsumption 0} ##b#3 > 0;
        assume _module.__default.DividesBoth#canCall(k#0, a#0, a#0);
    }

    assume k#0 > 0 ==> _module.__default.DividesBoth#canCall(k#0, a#0, a#0);
    assert {:subsumption 0} k#0 > 0;
    assert {:subsumption 0} _module.__default.DividesBoth#canCall(k#0, a#0, a#0)
       ==> _module.__default.DividesBoth(k#0, a#0, a#0) || k#0 > 0;
    assert {:subsumption 0} _module.__default.DividesBoth#canCall(k#0, a#0, a#0)
       ==> _module.__default.DividesBoth(k#0, a#0, a#0)
         || _module.__default.Divides(StartFuelAssert__module._default.Divides, k#0, a#0);
    assert {:subsumption 0} _module.__default.DividesBoth#canCall(k#0, a#0, a#0)
       ==> _module.__default.DividesBoth(k#0, a#0, a#0)
         || _module.__default.Divides(StartFuelAssert__module._default.Divides, k#0, a#0);
    assume k#0 > 0 && _module.__default.DividesBoth(k#0, a#0, a#0);
    // ----- assert statement ----- Problem2.dfy(281,3)
    havoc m#0;
    // Begin Comprehension WF check
    if (m#0 > 0)
    {
        ##d#3 := m#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##d#3, TInt, $Heap);
        ##a#5 := a#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##a#5, TInt, $Heap);
        ##b#4 := a#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##b#4, TInt, $Heap);
        assert {:subsumption 0} ##a#5 > 0;
        assert {:subsumption 0} ##b#4 > 0;
        assume _module.__default.DividesBoth#canCall(m#0, a#0, a#0);
    }

    if (m#0 > 0 && _module.__default.DividesBoth(m#0, a#0, a#0))
    {
    }

    // End Comprehension WF check
    assume (forall m#1: int ::
      { _module.__default.DividesBoth(m#1, a#0, a#0) }
      m#1 > 0 ==> _module.__default.DividesBoth#canCall(m#1, a#0, a#0));
    assert (forall m#1: int ::
      { _module.__default.DividesBoth(m#1, a#0, a#0) }
      true ==> m#1 > 0 && _module.__default.DividesBoth(m#1, a#0, a#0) ==> m#1 <= k#0);
    // ----- assert statement ----- Problem2.dfy(282,3)
    ##d#4 := k#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##d#4, TInt, $Heap);
    ##a#6 := a#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##a#6, TInt, $Heap);
    assert {:subsumption 0} ##d#4 > 0;
    assert {:subsumption 0} ##a#6 > 0;
    assume _module.__default.Divides#canCall(k#0, a#0);
    assume _module.__default.Divides#canCall(k#0, a#0);
    assert {:subsumption 0} _module.__default.Divides(StartFuelAssert__module._default.Divides, k#0, a#0);
    assume _module.__default.Divides(StartFuelAssert__module._default.Divides, k#0, a#0);
    // ----- call statement ----- Problem2.dfy(283,20)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    d##1 := k#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    a##2 := a#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.DividesUpperBound(d##1, a##2);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "Problem2.dfy(283,25)"} true;
}



procedure CheckWellformed$$_module.__default.DividesIdempotent(a#0: int);
  free requires 13 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.DividesIdempotent(a#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##d#0: int;
  var ##a#0: int;

    // AddMethodImpl: DividesIdempotent, CheckWellformed$$_module.__default.DividesIdempotent
    // initialize fuel constant
    assume AsFuelBottom(StartFuel__module._default.Divides)
       == StartFuel__module._default.Divides;
    assume AsFuelBottom(StartFuelAssert__module._default.Divides)
       == StartFuelAssert__module._default.Divides;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "Problem2.dfy(286,6): initial state"} true;
    assume a#0 > 0;
    havoc $Heap;
    assume old($Heap) == $Heap;
    assume {:captureState "Problem2.dfy(288,17): post-state"} true;
    ##d#0 := a#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##d#0, TInt, $Heap);
    ##a#0 := a#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##a#0, TInt, $Heap);
    assert {:subsumption 0} ##d#0 > 0;
    assert {:subsumption 0} ##a#0 > 0;
    assume ##d#0 > 0 && ##a#0 > 0;
    assume _module.__default.Divides#canCall(a#0, a#0);
    assume _module.__default.Divides(StartFuel__module._default.Divides, a#0, a#0);
}



procedure Call$$_module.__default.DividesIdempotent(a#0: int);
  // user-defined preconditions
  requires a#0 > 0;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Divides#canCall(a#0, a#0);
  ensures _module.__default.Divides(StartFuelAssert__module._default.Divides, a#0, a#0);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.DividesIdempotent(a#0: int) returns ($_reverifyPost: bool);
  free requires 13 == $FunctionContextHeight;
  // user-defined preconditions
  requires a#0 > 0;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Divides#canCall(a#0, a#0);
  ensures _module.__default.Divides(StartFuelAssert__module._default.Divides, a#0, a#0);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.DividesIdempotent(a#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##n#0: int;
  var ##d#1: int;
  var ##a#1: int;

    // AddMethodImpl: DividesIdempotent, Impl$$_module.__default.DividesIdempotent
    // initialize fuel constant
    assume AsFuelBottom(StartFuel__module._default.Divides)
       == StartFuel__module._default.Divides;
    assume AsFuelBottom(StartFuelAssert__module._default.Divides)
       == StartFuelAssert__module._default.Divides;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "Problem2.dfy(289,0): initial state"} true;
    $_reverifyPost := false;
    // ----- reveal statement ----- Problem2.dfy(290,3)
    // ----- call statement ----- Problem2.dfy(290,17)
    // TrCallStmt: Before ProcessCallStmt
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.reveal__Divides();
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "Problem2.dfy(290,18)"} true;
    // ----- assert statement ----- Problem2.dfy(291,3)
    ##n#0 := LitInt(1);
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#0, TInt, $Heap);
    ##d#1 := a#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##d#1, TInt, $Heap);
    ##a#1 := a#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##a#1, TInt, $Heap);
    assert {:subsumption 0} ##n#0 > 0;
    assert {:subsumption 0} ##d#1 > 0;
    assume _module.__default.MulTriple#canCall(LitInt(1), a#0, a#0);
    assume _module.__default.MulTriple#canCall(LitInt(1), a#0, a#0);
    assert {:subsumption 0} _module.__default.MulTriple#canCall(LitInt(1), a#0, a#0)
       ==> _module.__default.MulTriple(LitInt(1), a#0, a#0) || 1 * a#0 == a#0;
    assume _module.__default.MulTriple(LitInt(1), a#0, a#0);
}



procedure CheckWellformed$$_module.__default.DividesUpperBound(d#0: int, a#0: int);
  free requires 5 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.DividesUpperBound(d#0: int, a#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##d#0: int;
  var ##a#0: int;

    // AddMethodImpl: DividesUpperBound, CheckWellformed$$_module.__default.DividesUpperBound
    // initialize fuel constant
    assume AsFuelBottom(StartFuel__module._default.Divides)
       == StartFuel__module._default.Divides;
    assume AsFuelBottom(StartFuelAssert__module._default.Divides)
       == StartFuelAssert__module._default.Divides;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "Problem2.dfy(294,6): initial state"} true;
    assume d#0 > 0;
    assume a#0 > 0;
    havoc $Heap;
    assume old($Heap) == $Heap;
    assume {:captureState "Problem2.dfy(296,24): post-state"} true;
    if (*)
    {
        ##d#0 := d#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##d#0, TInt, $Heap);
        ##a#0 := a#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##a#0, TInt, $Heap);
        assert {:subsumption 0} ##d#0 > 0;
        assert {:subsumption 0} ##a#0 > 0;
        assume ##d#0 > 0 && ##a#0 > 0;
        assume _module.__default.Divides#canCall(d#0, a#0);
        assume _module.__default.Divides(StartFuel__module._default.Divides, d#0, a#0);
        assume d#0 <= a#0;
    }
    else
    {
        assume _module.__default.Divides(StartFuel__module._default.Divides, d#0, a#0)
           ==> d#0 <= a#0;
    }
}



procedure Call$$_module.__default.DividesUpperBound(d#0: int, a#0: int);
  // user-defined preconditions
  requires d#0 > 0;
  requires a#0 > 0;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Divides#canCall(d#0, a#0);
  ensures _module.__default.Divides(StartFuel__module._default.Divides, d#0, a#0)
     ==> d#0 <= a#0;
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.DividesUpperBound(d#0: int, a#0: int) returns ($_reverifyPost: bool);
  free requires 5 == $FunctionContextHeight;
  // user-defined preconditions
  requires d#0 > 0;
  requires a#0 > 0;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Divides#canCall(d#0, a#0);
  ensures _module.__default.Divides(StartFuel__module._default.Divides, d#0, a#0)
     ==> d#0 <= a#0;
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.DividesUpperBound(d#0: int, a#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: DividesUpperBound, Impl$$_module.__default.DividesUpperBound
    // initialize fuel constant
    assume AsFuelBottom(StartFuel__module._default.Divides)
       == StartFuel__module._default.Divides;
    assume AsFuelBottom(StartFuelAssert__module._default.Divides)
       == StartFuelAssert__module._default.Divides;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "Problem2.dfy(297,0): initial state"} true;
    $_reverifyPost := false;
    // ----- reveal statement ----- Problem2.dfy(298,3)
    // ----- call statement ----- Problem2.dfy(298,17)
    // TrCallStmt: Before ProcessCallStmt
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.reveal__Divides();
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "Problem2.dfy(298,18)"} true;
}



procedure CheckWellformed$$_module.__default.Symmetry(a#0: int, b#0: int);
  free requires 12 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.Symmetry(a#0: int, b#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##a#0: int;
  var ##b#0: int;
  var ##a#1: int;
  var ##b#1: int;

    // AddMethodImpl: Symmetry, CheckWellformed$$_module.__default.Symmetry
    // initialize fuel constant
    assume AsFuelBottom(StartFuel__module._default.Divides)
       == StartFuel__module._default.Divides;
    assume AsFuelBottom(StartFuelAssert__module._default.Divides)
       == StartFuelAssert__module._default.Divides;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "Problem2.dfy(301,6): initial state"} true;
    assume a#0 > 0;
    assume b#0 > 0;
    havoc $Heap;
    assume old($Heap) == $Heap;
    assume {:captureState "Problem2.dfy(303,20): post-state"} true;
    ##a#0 := a#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##a#0, TInt, $Heap);
    ##b#0 := b#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##b#0, TInt, $Heap);
    assert {:subsumption 0} ##a#0 > 0;
    assert {:subsumption 0} ##b#0 > 0;
    assume ##a#0 > 0 && ##b#0 > 0;
    assume _module.__default.Gcd#canCall(a#0, b#0);
    ##a#1 := b#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##a#1, TInt, $Heap);
    ##b#1 := a#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##b#1, TInt, $Heap);
    assert {:subsumption 0} ##a#1 > 0;
    assert {:subsumption 0} ##b#1 > 0;
    assume ##a#1 > 0 && ##b#1 > 0;
    assume _module.__default.Gcd#canCall(b#0, a#0);
    assume _module.__default.Gcd(a#0, b#0) == _module.__default.Gcd(b#0, a#0);
}



procedure Call$$_module.__default.Symmetry(a#0: int, b#0: int);
  // user-defined preconditions
  requires a#0 > 0;
  requires b#0 > 0;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Gcd#canCall(a#0, b#0)
     && _module.__default.Gcd#canCall(b#0, a#0);
  ensures _module.__default.Gcd(a#0, b#0) == _module.__default.Gcd(b#0, a#0);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.Symmetry(a#0: int, b#0: int) returns ($_reverifyPost: bool);
  free requires 12 == $FunctionContextHeight;
  // user-defined preconditions
  requires a#0 > 0;
  requires b#0 > 0;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Gcd#canCall(a#0, b#0)
     && _module.__default.Gcd#canCall(b#0, a#0);
  ensures _module.__default.Gcd(a#0, b#0) == _module.__default.Gcd(b#0, a#0);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.Symmetry(a#0: int, b#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var k#0: int;
  var l#0: int;
  var $rhs#0: int;
  var ##a#2: int;
  var ##b#2: int;
  var $rhs#1: int;
  var ##a#3: int;
  var ##b#3: int;
  var ##d#0: int;
  var ##a#4: int;
  var ##b#4: int;
  var m#0: int;
  var ##d#1: int;
  var ##a#5: int;
  var ##b#5: int;
  var ##d#2: int;
  var ##a#6: int;
  var ##b#6: int;
  var m#2: int;
  var ##d#3: int;
  var ##a#7: int;
  var ##b#7: int;
  var ##d#4: int;
  var ##a#8: int;
  var ##b#8: int;
  var m#4: int;
  var ##d#5: int;
  var ##a#9: int;
  var ##b#9: int;
  var ##d#6: int;
  var ##a#10: int;
  var ##b#10: int;

    // AddMethodImpl: Symmetry, Impl$$_module.__default.Symmetry
    // initialize fuel constant
    assume AsFuelBottom(StartFuel__module._default.Divides)
       == StartFuel__module._default.Divides;
    assume AsFuelBottom(StartFuelAssert__module._default.Divides)
       == StartFuelAssert__module._default.Divides;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "Problem2.dfy(304,0): initial state"} true;
    $_reverifyPost := false;
    // ----- update statement ----- Problem2.dfy(305,12)
    assume true;
    assume true;
    ##a#2 := a#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##a#2, TInt, $Heap);
    ##b#2 := b#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##b#2, TInt, $Heap);
    assert {:subsumption 0} ##a#2 > 0;
    assert {:subsumption 0} ##b#2 > 0;
    assume ##a#2 > 0 && ##b#2 > 0;
    assume _module.__default.Gcd#canCall(a#0, b#0);
    assume _module.__default.Gcd#canCall(a#0, b#0);
    $rhs#0 := _module.__default.Gcd(a#0, b#0);
    ##a#3 := b#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##a#3, TInt, $Heap);
    ##b#3 := a#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##b#3, TInt, $Heap);
    assert {:subsumption 0} ##a#3 > 0;
    assert {:subsumption 0} ##b#3 > 0;
    assume ##a#3 > 0 && ##b#3 > 0;
    assume _module.__default.Gcd#canCall(b#0, a#0);
    assume _module.__default.Gcd#canCall(b#0, a#0);
    $rhs#1 := _module.__default.Gcd(b#0, a#0);
    k#0 := $rhs#0;
    l#0 := $rhs#1;
    assume {:captureState "Problem2.dfy(305,34)"} true;
    // ----- assert statement ----- Problem2.dfy(306,3)
    ##d#0 := k#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##d#0, TInt, $Heap);
    ##a#4 := a#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##a#4, TInt, $Heap);
    ##b#4 := b#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##b#4, TInt, $Heap);
    assert {:subsumption 0} ##a#4 > 0;
    assert {:subsumption 0} ##b#4 > 0;
    assume _module.__default.DividesBoth#canCall(k#0, a#0, b#0);
    if (_module.__default.DividesBoth(k#0, a#0, b#0))
    {
        havoc m#0;
        // Begin Comprehension WF check
        ##d#1 := m#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##d#1, TInt, $Heap);
        ##a#5 := a#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##a#5, TInt, $Heap);
        ##b#5 := b#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##b#5, TInt, $Heap);
        assert {:subsumption 0} ##a#5 > 0;
        assert {:subsumption 0} ##b#5 > 0;
        assume _module.__default.DividesBoth#canCall(m#0, a#0, b#0);
        if (_module.__default.DividesBoth(m#0, a#0, b#0))
        {
        }

        // End Comprehension WF check
    }

    assume _module.__default.DividesBoth#canCall(k#0, a#0, b#0)
       && (_module.__default.DividesBoth(k#0, a#0, b#0)
         ==> (forall m#1: int ::
          { _module.__default.DividesBoth(m#1, a#0, b#0) }
          _module.__default.DividesBoth#canCall(m#1, a#0, b#0)));
    assert {:subsumption 0} _module.__default.DividesBoth#canCall(k#0, a#0, b#0)
       ==> _module.__default.DividesBoth(k#0, a#0, b#0) || k#0 > 0;
    assert {:subsumption 0} _module.__default.DividesBoth#canCall(k#0, a#0, b#0)
       ==> _module.__default.DividesBoth(k#0, a#0, b#0)
         || _module.__default.Divides(StartFuelAssert__module._default.Divides, k#0, a#0);
    assert {:subsumption 0} _module.__default.DividesBoth#canCall(k#0, a#0, b#0)
       ==> _module.__default.DividesBoth(k#0, a#0, b#0)
         || _module.__default.Divides(StartFuelAssert__module._default.Divides, k#0, b#0);
    assert {:subsumption 0} (forall m#1: int ::
      { _module.__default.DividesBoth(m#1, a#0, b#0) }
      true ==> _module.__default.DividesBoth(m#1, a#0, b#0) ==> m#1 <= k#0);
    assume _module.__default.DividesBoth(k#0, a#0, b#0)
       && (forall m#1: int ::
        { _module.__default.DividesBoth(m#1, a#0, b#0) }
        true ==> _module.__default.DividesBoth(m#1, a#0, b#0) ==> m#1 <= k#0);
    // ----- assert statement ----- Problem2.dfy(307,3)
    ##d#2 := l#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##d#2, TInt, $Heap);
    ##a#6 := b#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##a#6, TInt, $Heap);
    ##b#6 := a#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##b#6, TInt, $Heap);
    assert {:subsumption 0} ##a#6 > 0;
    assert {:subsumption 0} ##b#6 > 0;
    assume _module.__default.DividesBoth#canCall(l#0, b#0, a#0);
    if (_module.__default.DividesBoth(l#0, b#0, a#0))
    {
        havoc m#2;
        // Begin Comprehension WF check
        ##d#3 := m#2;
        // assume allocatedness for argument to function
        assume $IsAlloc(##d#3, TInt, $Heap);
        ##a#7 := b#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##a#7, TInt, $Heap);
        ##b#7 := a#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##b#7, TInt, $Heap);
        assert {:subsumption 0} ##a#7 > 0;
        assert {:subsumption 0} ##b#7 > 0;
        assume _module.__default.DividesBoth#canCall(m#2, b#0, a#0);
        if (_module.__default.DividesBoth(m#2, b#0, a#0))
        {
        }

        // End Comprehension WF check
    }

    assume _module.__default.DividesBoth#canCall(l#0, b#0, a#0)
       && (_module.__default.DividesBoth(l#0, b#0, a#0)
         ==> (forall m#3: int ::
          { _module.__default.DividesBoth(m#3, b#0, a#0) }
          _module.__default.DividesBoth#canCall(m#3, b#0, a#0)));
    assert {:subsumption 0} _module.__default.DividesBoth#canCall(l#0, b#0, a#0)
       ==> _module.__default.DividesBoth(l#0, b#0, a#0) || l#0 > 0;
    assert {:subsumption 0} _module.__default.DividesBoth#canCall(l#0, b#0, a#0)
       ==> _module.__default.DividesBoth(l#0, b#0, a#0)
         || _module.__default.Divides(StartFuelAssert__module._default.Divides, l#0, b#0);
    assert {:subsumption 0} _module.__default.DividesBoth#canCall(l#0, b#0, a#0)
       ==> _module.__default.DividesBoth(l#0, b#0, a#0)
         || _module.__default.Divides(StartFuelAssert__module._default.Divides, l#0, a#0);
    assert {:subsumption 0} (forall m#3: int ::
      { _module.__default.DividesBoth(m#3, b#0, a#0) }
      true ==> _module.__default.DividesBoth(m#3, b#0, a#0) ==> m#3 <= l#0);
    assume _module.__default.DividesBoth(l#0, b#0, a#0)
       && (forall m#3: int ::
        { _module.__default.DividesBoth(m#3, b#0, a#0) }
        true ==> _module.__default.DividesBoth(m#3, b#0, a#0) ==> m#3 <= l#0);
    // ----- assert statement ----- Problem2.dfy(308,3)
    ##d#4 := l#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##d#4, TInt, $Heap);
    ##a#8 := a#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##a#8, TInt, $Heap);
    ##b#8 := b#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##b#8, TInt, $Heap);
    assert {:subsumption 0} ##a#8 > 0;
    assert {:subsumption 0} ##b#8 > 0;
    assume _module.__default.DividesBoth#canCall(l#0, a#0, b#0);
    assume _module.__default.DividesBoth#canCall(l#0, a#0, b#0);
    assert {:subsumption 0} _module.__default.DividesBoth#canCall(l#0, a#0, b#0)
       ==> _module.__default.DividesBoth(l#0, a#0, b#0) || l#0 > 0;
    assert {:subsumption 0} _module.__default.DividesBoth#canCall(l#0, a#0, b#0)
       ==> _module.__default.DividesBoth(l#0, a#0, b#0)
         || _module.__default.Divides(StartFuelAssert__module._default.Divides, l#0, a#0);
    assert {:subsumption 0} _module.__default.DividesBoth#canCall(l#0, a#0, b#0)
       ==> _module.__default.DividesBoth(l#0, a#0, b#0)
         || _module.__default.Divides(StartFuelAssert__module._default.Divides, l#0, b#0);
    assume _module.__default.DividesBoth(l#0, a#0, b#0);
    // ----- assert statement ----- Problem2.dfy(309,3)
    havoc m#4;
    // Begin Comprehension WF check
    ##d#5 := m#4;
    // assume allocatedness for argument to function
    assume $IsAlloc(##d#5, TInt, $Heap);
    ##a#9 := b#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##a#9, TInt, $Heap);
    ##b#9 := a#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##b#9, TInt, $Heap);
    assert {:subsumption 0} ##a#9 > 0;
    assert {:subsumption 0} ##b#9 > 0;
    assume _module.__default.DividesBoth#canCall(m#4, b#0, a#0);
    if (_module.__default.DividesBoth(m#4, b#0, a#0))
    {
        if (m#4 <= l#0)
        {
            ##d#6 := m#4;
            // assume allocatedness for argument to function
            assume $IsAlloc(##d#6, TInt, $Heap);
            ##a#10 := a#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##a#10, TInt, $Heap);
            ##b#10 := b#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##b#10, TInt, $Heap);
            assert {:subsumption 0} ##a#10 > 0;
            assert {:subsumption 0} ##b#10 > 0;
            assume _module.__default.DividesBoth#canCall(m#4, a#0, b#0);
        }
    }

    // End Comprehension WF check
    assume (forall m#5: int ::
      { _module.__default.DividesBoth(m#5, a#0, b#0) }
        { _module.__default.DividesBoth(m#5, b#0, a#0) }
      _module.__default.DividesBoth#canCall(m#5, b#0, a#0)
         && (m#5 <= l#0
           ==> _module.__default.DividesBoth#canCall(m#5, b#0, a#0)
             && (_module.__default.DividesBoth(m#5, b#0, a#0)
               ==> _module.__default.DividesBoth#canCall(m#5, a#0, b#0))));
    assert (forall m#5: int ::
      { _module.__default.DividesBoth(m#5, a#0, b#0) }
        { _module.__default.DividesBoth(m#5, b#0, a#0) }
      true
         ==> (_module.__default.DividesBoth(m#5, b#0, a#0) ==> m#5 <= l#0)
           && (_module.__default.DividesBoth(m#5, b#0, a#0)
             ==> _module.__default.DividesBoth(m#5, a#0, b#0)));
    // ----- assert statement ----- Problem2.dfy(310,3)
    assume true;
    assert k#0 == l#0;
}



procedure CheckWellformed$$_module.__default.GcdDecrease(a#0: int, b#0: int);
  free requires 11 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.GcdDecrease(a#0: int, b#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##a#0: int;
  var ##b#0: int;
  var ##a#1: int;
  var ##b#1: int;

    // AddMethodImpl: GcdDecrease, CheckWellformed$$_module.__default.GcdDecrease
    // initialize fuel constant
    assume AsFuelBottom(StartFuel__module._default.Divides)
       == StartFuel__module._default.Divides;
    assume AsFuelBottom(StartFuelAssert__module._default.Divides)
       == StartFuelAssert__module._default.Divides;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "Problem2.dfy(313,6): initial state"} true;
    if (a#0 > b#0)
    {
    }

    assume a#0 > b#0 && b#0 > 0;
    havoc $Heap;
    assume old($Heap) == $Heap;
    assume {:captureState "Problem2.dfy(315,20): post-state"} true;
    ##a#0 := a#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##a#0, TInt, $Heap);
    ##b#0 := b#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##b#0, TInt, $Heap);
    assert {:subsumption 0} ##a#0 > 0;
    assert {:subsumption 0} ##b#0 > 0;
    assume ##a#0 > 0 && ##b#0 > 0;
    assume _module.__default.Gcd#canCall(a#0, b#0);
    ##a#1 := a#0 - b#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##a#1, TInt, $Heap);
    ##b#1 := b#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##b#1, TInt, $Heap);
    assert {:subsumption 0} ##a#1 > 0;
    assert {:subsumption 0} ##b#1 > 0;
    assume ##a#1 > 0 && ##b#1 > 0;
    assume _module.__default.Gcd#canCall(a#0 - b#0, b#0);
    assume _module.__default.Gcd(a#0, b#0) == _module.__default.Gcd(a#0 - b#0, b#0);
}



procedure Call$$_module.__default.GcdDecrease(a#0: int, b#0: int);
  // user-defined preconditions
  requires a#0 > b#0;
  requires b#0 > 0;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Gcd#canCall(a#0, b#0)
     && _module.__default.Gcd#canCall(a#0 - b#0, b#0);
  ensures _module.__default.Gcd(a#0, b#0) == _module.__default.Gcd(a#0 - b#0, b#0);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.GcdDecrease(a#0: int, b#0: int) returns ($_reverifyPost: bool);
  free requires 11 == $FunctionContextHeight;
  // user-defined preconditions
  requires a#0 > b#0;
  requires b#0 > 0;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Gcd#canCall(a#0, b#0)
     && _module.__default.Gcd#canCall(a#0 - b#0, b#0);
  ensures _module.__default.Gcd(a#0, b#0) == _module.__default.Gcd(a#0 - b#0, b#0);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.GcdDecrease(a#0: int, b#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var k#0: int;
  var ##a#2: int;
  var ##b#2: int;
  var ##d#0: int;
  var ##a#3: int;
  var ##b#3: int;
  var m#0: int;
  var mm#0: int;
  var ##d#1: int;
  var ##a#4: int;
  var ##b#4: int;
  var n#0: int;
  var $rhs##0: int;
  var d##0: int;
  var a##0: int;
  var p#0: int;
  var $rhs##1: int;
  var d##1: int;
  var a##1: int;
  var n##0: int;
  var d##2: int;
  var a##2: int;
  var ##d#2: int;
  var ##a#5: int;
  var ##d#3: int;
  var ##a#6: int;
  var ##b#5: int;
  var l#0: int;
  var ##a#7: int;
  var ##b#6: int;
  var m#2: int;
  var ##d#4: int;
  var ##a#8: int;
  var ##b#7: int;
  var n'#0: int;
  var $rhs##2: int;
  var d##3: int;
  var a##3: int;
  var p'#0: int;
  var $rhs##3: int;
  var d##4: int;
  var a##4: int;
  var n##1: int;
  var d##5: int;
  var a##5: int;
  var ##d#5: int;
  var ##a#9: int;
  var ##d#6: int;
  var ##a#10: int;
  var ##b#8: int;

    // AddMethodImpl: GcdDecrease, Impl$$_module.__default.GcdDecrease
    // initialize fuel constant
    assume AsFuelBottom(StartFuel__module._default.Divides)
       == StartFuel__module._default.Divides;
    assume AsFuelBottom(StartFuelAssert__module._default.Divides)
       == StartFuelAssert__module._default.Divides;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "Problem2.dfy(316,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- Problem2.dfy(317,9)
    assume true;
    ##a#2 := a#0 - b#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##a#2, TInt, $Heap);
    ##b#2 := b#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##b#2, TInt, $Heap);
    assert {:subsumption 0} ##a#2 > 0;
    assert {:subsumption 0} ##b#2 > 0;
    assume ##a#2 > 0 && ##b#2 > 0;
    assume _module.__default.Gcd#canCall(a#0 - b#0, b#0);
    assume _module.__default.Gcd#canCall(a#0 - b#0, b#0);
    k#0 := _module.__default.Gcd(a#0 - b#0, b#0);
    assume {:captureState "Problem2.dfy(317,24)"} true;
    // ----- assert statement ----- Problem2.dfy(318,3)
    ##d#0 := k#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##d#0, TInt, $Heap);
    ##a#3 := a#0 - b#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##a#3, TInt, $Heap);
    ##b#3 := b#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##b#3, TInt, $Heap);
    assert {:subsumption 0} ##a#3 > 0;
    assert {:subsumption 0} ##b#3 > 0;
    assume _module.__default.DividesBoth#canCall(k#0, a#0 - b#0, b#0);
    if (_module.__default.DividesBoth(k#0, a#0 - b#0, b#0))
    {
        havoc m#0;
        havoc mm#0;
        // Begin Comprehension WF check
        if (mm#0 == a#0 - b#0)
        {
            ##d#1 := m#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##d#1, TInt, $Heap);
            ##a#4 := mm#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##a#4, TInt, $Heap);
            ##b#4 := b#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##b#4, TInt, $Heap);
            assert {:subsumption 0} ##a#4 > 0;
            assert {:subsumption 0} ##b#4 > 0;
            assume _module.__default.DividesBoth#canCall(m#0, mm#0, b#0);
            if (_module.__default.DividesBoth(m#0, mm#0, b#0))
            {
            }
        }

        // End Comprehension WF check
    }

    assume _module.__default.DividesBoth#canCall(k#0, a#0 - b#0, b#0)
       && (_module.__default.DividesBoth(k#0, a#0 - b#0, b#0)
         ==> (forall m#1: int, mm#1: int ::
          { _module.__default.DividesBoth(m#1, mm#1, b#0) }
          mm#1 == a#0 - b#0 ==> _module.__default.DividesBoth#canCall(m#1, mm#1, b#0)));
    assert {:subsumption 0} _module.__default.DividesBoth#canCall(k#0, a#0 - b#0, b#0)
       ==> _module.__default.DividesBoth(k#0, a#0 - b#0, b#0) || k#0 > 0;
    assert {:subsumption 0} _module.__default.DividesBoth#canCall(k#0, a#0 - b#0, b#0)
       ==> _module.__default.DividesBoth(k#0, a#0 - b#0, b#0)
         || _module.__default.Divides(StartFuelAssert__module._default.Divides, k#0, a#0 - b#0);
    assert {:subsumption 0} _module.__default.DividesBoth#canCall(k#0, a#0 - b#0, b#0)
       ==> _module.__default.DividesBoth(k#0, a#0 - b#0, b#0)
         || _module.__default.Divides(StartFuelAssert__module._default.Divides, k#0, b#0);
    assert {:subsumption 0} (forall m#1: int, mm#1: int ::
      { _module.__default.DividesBoth(m#1, mm#1, b#0) }
      true
         ==>
        mm#1 == a#0 - b#0
         ==>
        _module.__default.DividesBoth(m#1, mm#1, b#0)
         ==> m#1 <= k#0);
    assume _module.__default.DividesBoth(k#0, a#0 - b#0, b#0)
       && (forall m#1: int, mm#1: int ::
        { _module.__default.DividesBoth(m#1, mm#1, b#0) }
        true
           ==>
          mm#1 == a#0 - b#0
           ==>
          _module.__default.DividesBoth(m#1, mm#1, b#0)
           ==> m#1 <= k#0);
    // ----- call statement ----- Problem2.dfy(319,27)
    assume true;
    // TrCallStmt: Adding lhs Microsoft.Dafny.AutoGhostIdentifierExpr with type int
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    d##0 := k#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    a##0 := a#0 - b#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##0 := Call$$_module.__default.DividesProperty(d##0, a##0);
    // TrCallStmt: After ProcessCallStmt
    n#0 := $rhs##0;
    assume {:captureState "Problem2.dfy(319,34)"} true;
    // ----- assert statement ----- Problem2.dfy(320,3)
    assume true;
    assert n#0 * k#0 == a#0 - b#0;
    // ----- call statement ----- Problem2.dfy(321,27)
    assume true;
    // TrCallStmt: Adding lhs Microsoft.Dafny.AutoGhostIdentifierExpr with type int
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    d##1 := k#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    a##1 := b#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##1 := Call$$_module.__default.DividesProperty(d##1, a##1);
    // TrCallStmt: After ProcessCallStmt
    p#0 := $rhs##1;
    assume {:captureState "Problem2.dfy(321,32)"} true;
    // ----- assert statement ----- Problem2.dfy(322,3)
    assume true;
    assert p#0 * k#0 == b#0;
    // ----- assert statement ----- Problem2.dfy(324,3)
    assume true;
    assert n#0 * k#0 + p#0 * k#0 == a#0 - b#0 + b#0;
    // ----- assert statement ----- Problem2.dfy(325,3)
    assume true;
    assert (n#0 + p#0) * k#0 == a#0;
    // ----- call statement ----- Problem2.dfy(327,18)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    n##0 := n#0 + p#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    d##2 := k#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    a##2 := a#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.MultipleDivides(n##0, d##2, a##2);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "Problem2.dfy(327,28)"} true;
    // ----- assert statement ----- Problem2.dfy(328,3)
    ##d#2 := k#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##d#2, TInt, $Heap);
    ##a#5 := a#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##a#5, TInt, $Heap);
    assert {:subsumption 0} ##d#2 > 0;
    assert {:subsumption 0} ##a#5 > 0;
    assume _module.__default.Divides#canCall(k#0, a#0);
    assume _module.__default.Divides#canCall(k#0, a#0);
    assert {:subsumption 0} _module.__default.Divides(StartFuelAssert__module._default.Divides, k#0, a#0);
    assume _module.__default.Divides(StartFuelAssert__module._default.Divides, k#0, a#0);
    // ----- assert statement ----- Problem2.dfy(329,3)
    ##d#3 := k#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##d#3, TInt, $Heap);
    ##a#6 := a#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##a#6, TInt, $Heap);
    ##b#5 := b#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##b#5, TInt, $Heap);
    assert {:subsumption 0} ##a#6 > 0;
    assert {:subsumption 0} ##b#5 > 0;
    assume _module.__default.DividesBoth#canCall(k#0, a#0, b#0);
    assume _module.__default.DividesBoth#canCall(k#0, a#0, b#0);
    assert {:subsumption 0} _module.__default.DividesBoth#canCall(k#0, a#0, b#0)
       ==> _module.__default.DividesBoth(k#0, a#0, b#0) || k#0 > 0;
    assert {:subsumption 0} _module.__default.DividesBoth#canCall(k#0, a#0, b#0)
       ==> _module.__default.DividesBoth(k#0, a#0, b#0)
         || _module.__default.Divides(StartFuelAssert__module._default.Divides, k#0, a#0);
    assert {:subsumption 0} _module.__default.DividesBoth#canCall(k#0, a#0, b#0)
       ==> _module.__default.DividesBoth(k#0, a#0, b#0)
         || _module.__default.Divides(StartFuelAssert__module._default.Divides, k#0, b#0);
    assume _module.__default.DividesBoth(k#0, a#0, b#0);
    // ----- assignment statement ----- Problem2.dfy(331,9)
    assume true;
    ##a#7 := a#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##a#7, TInt, $Heap);
    ##b#6 := b#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##b#6, TInt, $Heap);
    assert {:subsumption 0} ##a#7 > 0;
    assert {:subsumption 0} ##b#6 > 0;
    assume ##a#7 > 0 && ##b#6 > 0;
    assume _module.__default.Gcd#canCall(a#0, b#0);
    assume _module.__default.Gcd#canCall(a#0, b#0);
    l#0 := _module.__default.Gcd(a#0, b#0);
    assume {:captureState "Problem2.dfy(331,20)"} true;
    // ----- assert statement ----- Problem2.dfy(332,3)
    havoc m#2;
    // Begin Comprehension WF check
    ##d#4 := m#2;
    // assume allocatedness for argument to function
    assume $IsAlloc(##d#4, TInt, $Heap);
    ##a#8 := a#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##a#8, TInt, $Heap);
    ##b#7 := b#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##b#7, TInt, $Heap);
    assert {:subsumption 0} ##a#8 > 0;
    assert {:subsumption 0} ##b#7 > 0;
    assume _module.__default.DividesBoth#canCall(m#2, a#0, b#0);
    if (_module.__default.DividesBoth(m#2, a#0, b#0))
    {
    }

    // End Comprehension WF check
    assume (forall m#3: int ::
      { _module.__default.DividesBoth(m#3, a#0, b#0) }
      _module.__default.DividesBoth#canCall(m#3, a#0, b#0));
    assert (forall m#3: int ::
      { _module.__default.DividesBoth(m#3, a#0, b#0) }
      true ==> _module.__default.DividesBoth(m#3, a#0, b#0) ==> m#3 <= l#0);
    // ----- assert statement ----- Problem2.dfy(333,3)
    assume true;
    assert k#0 <= l#0;
    // ----- call statement ----- Problem2.dfy(335,28)
    assume true;
    // TrCallStmt: Adding lhs Microsoft.Dafny.AutoGhostIdentifierExpr with type int
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    d##3 := l#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    a##3 := a#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##2 := Call$$_module.__default.DividesProperty(d##3, a##3);
    // TrCallStmt: After ProcessCallStmt
    n'#0 := $rhs##2;
    assume {:captureState "Problem2.dfy(335,33)"} true;
    // ----- call statement ----- Problem2.dfy(336,28)
    assume true;
    // TrCallStmt: Adding lhs Microsoft.Dafny.AutoGhostIdentifierExpr with type int
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    d##4 := l#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    a##4 := b#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##3 := Call$$_module.__default.DividesProperty(d##4, a##4);
    // TrCallStmt: After ProcessCallStmt
    p'#0 := $rhs##3;
    assume {:captureState "Problem2.dfy(336,33)"} true;
    // ----- assert statement ----- Problem2.dfy(337,3)
    assume true;
    assert n'#0 * l#0 == a#0;
    // ----- assert statement ----- Problem2.dfy(338,3)
    assume true;
    assert p'#0 * l#0 == b#0;
    // ----- assert statement ----- Problem2.dfy(339,3)
    assume true;
    assert n'#0 * l#0 - p'#0 * l#0 == a#0 - b#0;
    // ----- assert statement ----- Problem2.dfy(340,3)
    assume true;
    assert (n'#0 - p'#0) * l#0 == a#0 - b#0;
    // ----- call statement ----- Problem2.dfy(341,18)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    n##1 := n'#0 - p'#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    d##5 := l#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    a##5 := a#0 - b#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.MultipleDivides(n##1, d##5, a##5);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "Problem2.dfy(341,36)"} true;
    // ----- assert statement ----- Problem2.dfy(342,3)
    ##d#5 := l#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##d#5, TInt, $Heap);
    ##a#9 := a#0 - b#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##a#9, TInt, $Heap);
    assert {:subsumption 0} ##d#5 > 0;
    assert {:subsumption 0} ##a#9 > 0;
    assume _module.__default.Divides#canCall(l#0, a#0 - b#0);
    assume _module.__default.Divides#canCall(l#0, a#0 - b#0);
    assert {:subsumption 0} _module.__default.Divides(StartFuelAssert__module._default.Divides, l#0, a#0 - b#0);
    assume _module.__default.Divides(StartFuelAssert__module._default.Divides, l#0, a#0 - b#0);
    // ----- assert statement ----- Problem2.dfy(343,3)
    ##d#6 := l#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##d#6, TInt, $Heap);
    ##a#10 := a#0 - b#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##a#10, TInt, $Heap);
    ##b#8 := b#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##b#8, TInt, $Heap);
    assert {:subsumption 0} ##a#10 > 0;
    assert {:subsumption 0} ##b#8 > 0;
    assume _module.__default.DividesBoth#canCall(l#0, a#0 - b#0, b#0);
    assume _module.__default.DividesBoth#canCall(l#0, a#0 - b#0, b#0);
    assert {:subsumption 0} _module.__default.DividesBoth#canCall(l#0, a#0 - b#0, b#0)
       ==> _module.__default.DividesBoth(l#0, a#0 - b#0, b#0) || l#0 > 0;
    assert {:subsumption 0} _module.__default.DividesBoth#canCall(l#0, a#0 - b#0, b#0)
       ==> _module.__default.DividesBoth(l#0, a#0 - b#0, b#0)
         || _module.__default.Divides(StartFuelAssert__module._default.Divides, l#0, a#0 - b#0);
    assert {:subsumption 0} _module.__default.DividesBoth#canCall(l#0, a#0 - b#0, b#0)
       ==> _module.__default.DividesBoth(l#0, a#0 - b#0, b#0)
         || _module.__default.Divides(StartFuelAssert__module._default.Divides, l#0, b#0);
    assume _module.__default.DividesBoth(l#0, a#0 - b#0, b#0);
    // ----- assert statement ----- Problem2.dfy(344,3)
    assume true;
    assert l#0 <= k#0;
    // ----- assert statement ----- Problem2.dfy(346,3)
    assume true;
    assert k#0 == l#0;
}



procedure CheckWellformed$$_module.__default.MultipleDivides(n#0: int, d#0: int, a#0: int);
  free requires 10 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.MultipleDivides(n#0: int, d#0: int, a#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##d#0: int;
  var ##a#0: int;

    // AddMethodImpl: MultipleDivides, CheckWellformed$$_module.__default.MultipleDivides
    // initialize fuel constant
    assume AsFuelBottom(StartFuel__module._default.Divides)
       == StartFuel__module._default.Divides;
    assume AsFuelBottom(StartFuelAssert__module._default.Divides)
       == StartFuelAssert__module._default.Divides;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "Problem2.dfy(349,6): initial state"} true;
    assume n#0 > 0;
    assume d#0 > 0;
    assume n#0 * d#0 == a#0;
    havoc $Heap;
    assume old($Heap) == $Heap;
    assume {:captureState "Problem2.dfy(351,17): post-state"} true;
    ##d#0 := d#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##d#0, TInt, $Heap);
    ##a#0 := a#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##a#0, TInt, $Heap);
    assert {:subsumption 0} ##d#0 > 0;
    assert {:subsumption 0} ##a#0 > 0;
    assume ##d#0 > 0 && ##a#0 > 0;
    assume _module.__default.Divides#canCall(d#0, a#0);
    assume _module.__default.Divides(StartFuel__module._default.Divides, d#0, a#0);
}



procedure Call$$_module.__default.MultipleDivides(n#0: int, d#0: int, a#0: int);
  // user-defined preconditions
  requires n#0 > 0;
  requires d#0 > 0;
  requires n#0 * d#0 == a#0;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Divides#canCall(d#0, a#0);
  ensures _module.__default.Divides(StartFuelAssert__module._default.Divides, d#0, a#0);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.MultipleDivides(n#0: int, d#0: int, a#0: int) returns ($_reverifyPost: bool);
  free requires 10 == $FunctionContextHeight;
  // user-defined preconditions
  requires n#0 > 0;
  requires d#0 > 0;
  requires n#0 * d#0 == a#0;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Divides#canCall(d#0, a#0);
  ensures _module.__default.Divides(StartFuelAssert__module._default.Divides, d#0, a#0);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.MultipleDivides(n#0: int, d#0: int, a#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##n#0: int;
  var ##d#1: int;
  var ##a#1: int;

    // AddMethodImpl: MultipleDivides, Impl$$_module.__default.MultipleDivides
    // initialize fuel constant
    assume AsFuelBottom(StartFuel__module._default.Divides)
       == StartFuel__module._default.Divides;
    assume AsFuelBottom(StartFuelAssert__module._default.Divides)
       == StartFuelAssert__module._default.Divides;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "Problem2.dfy(352,0): initial state"} true;
    $_reverifyPost := false;
    // ----- reveal statement ----- Problem2.dfy(353,3)
    // ----- call statement ----- Problem2.dfy(353,17)
    // TrCallStmt: Before ProcessCallStmt
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.reveal__Divides();
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "Problem2.dfy(353,18)"} true;
    // ----- assert statement ----- Problem2.dfy(354,3)
    ##n#0 := n#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#0, TInt, $Heap);
    ##d#1 := d#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##d#1, TInt, $Heap);
    ##a#1 := a#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##a#1, TInt, $Heap);
    assert {:subsumption 0} ##n#0 > 0;
    assert {:subsumption 0} ##d#1 > 0;
    assume _module.__default.MulTriple#canCall(n#0, d#0, a#0);
    assume _module.__default.MulTriple#canCall(n#0, d#0, a#0);
    assert {:subsumption 0} _module.__default.MulTriple#canCall(n#0, d#0, a#0)
       ==> _module.__default.MulTriple(n#0, d#0, a#0) || n#0 * d#0 == a#0;
    assume _module.__default.MulTriple(n#0, d#0, a#0);
}



procedure CheckWellformed$$_module.__default.DividesProperty(d#0: int, a#0: int) returns (n#0: int);
  free requires 9 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.DividesProperty(d#0: int, a#0: int) returns (n#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##d#0: int;
  var ##a#0: int;

    // AddMethodImpl: DividesProperty, CheckWellformed$$_module.__default.DividesProperty
    // initialize fuel constant
    assume AsFuelBottom(StartFuel__module._default.Divides)
       == StartFuel__module._default.Divides;
    assume AsFuelBottom(StartFuelAssert__module._default.Divides)
       == StartFuelAssert__module._default.Divides;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "Problem2.dfy(357,6): initial state"} true;
    assume d#0 > 0;
    assume a#0 > 0;
    ##d#0 := d#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##d#0, TInt, $Heap);
    ##a#0 := a#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##a#0, TInt, $Heap);
    assert {:subsumption 0} ##d#0 > 0;
    assert {:subsumption 0} ##a#0 > 0;
    assume ##d#0 > 0 && ##a#0 > 0;
    assume _module.__default.Divides#canCall(d#0, a#0);
    assume _module.__default.Divides(StartFuel__module._default.Divides, d#0, a#0);
    havoc $Heap;
    assume old($Heap) == $Heap;
    havoc n#0;
    assume {:captureState "Problem2.dfy(360,14): post-state"} true;
    assume n#0 * d#0 == a#0;
}



procedure Call$$_module.__default.DividesProperty(d#0: int, a#0: int) returns (n#0: int);
  // user-defined preconditions
  requires d#0 > 0;
  requires a#0 > 0;
  requires _module.__default.Divides(StartFuelAssert__module._default.Divides, d#0, a#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures n#0 * d#0 == a#0;
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.DividesProperty(d#0: int, a#0: int) returns (n#0: int, $_reverifyPost: bool);
  free requires 9 == $FunctionContextHeight;
  // user-defined preconditions
  requires d#0 > 0;
  requires a#0 > 0;
  requires _module.__default.Divides(StartFuelAssert__module._default.Divides, d#0, a#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures n#0 * d#0 == a#0;
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.DividesProperty(d#0: int, a#0: int) returns (n#0: int, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##n#0: int;
  var ##d#1: int;
  var ##a#1: int;

    // AddMethodImpl: DividesProperty, Impl$$_module.__default.DividesProperty
    // initialize fuel constant
    assume AsFuelBottom(StartFuel__module._default.Divides)
       == StartFuel__module._default.Divides;
    assume AsFuelBottom(StartFuelAssert__module._default.Divides)
       == StartFuelAssert__module._default.Divides;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "Problem2.dfy(361,0): initial state"} true;
    $_reverifyPost := false;
    // ----- reveal statement ----- Problem2.dfy(362,3)
    // ----- call statement ----- Problem2.dfy(362,17)
    // TrCallStmt: Before ProcessCallStmt
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.reveal__Divides();
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "Problem2.dfy(362,18)"} true;
    // ----- assign-such-that statement ----- Problem2.dfy(363,5)
    assume true;
    havoc n#0;
    if (n#0 > 0)
    {
        ##n#0 := n#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##n#0, TInt, $Heap);
        ##d#1 := d#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##d#1, TInt, $Heap);
        ##a#1 := a#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##a#1, TInt, $Heap);
        assert {:subsumption 0} ##n#0 > 0;
        assert {:subsumption 0} ##d#1 > 0;
        assume _module.__default.MulTriple#canCall(n#0, d#0, a#0);
    }

    assume n#0 > 0 ==> _module.__default.MulTriple#canCall(n#0, d#0, a#0);
    assert ($Is(LitInt(0 + 1), TInt)
         &&
        0 + 1 > 0
         && _module.__default.MulTriple(LitInt(0 + 1), d#0, a#0))
       ||
      ($Is(LitInt(0), TInt)
         &&
        0 > 0
         && _module.__default.MulTriple(LitInt(0), d#0, a#0))
       || (exists $as#n0#0: int ::
        $as#n0#0 > 0 && _module.__default.MulTriple($as#n0#0, d#0, a#0));
    assume n#0 > 0 && _module.__default.MulTriple(n#0, d#0, a#0);
    assume {:captureState "Problem2.dfy(363,34)"} true;
}



procedure {:auto_generated} {:opaque_reveal} {:verify false} CheckWellformed$$_module.__default.reveal__Divides();
  free requires 3 == $FunctionContextHeight;
  modifies $Heap, $Tick;



const MoreFuel__module._default.Divides0: LayerType;

procedure {:auto_generated} {:opaque_reveal} {:verify false} Call$$_module.__default.reveal__Divides();
  modifies $Heap, $Tick;
  // frame condition
  free ensures old($Heap) == $Heap;
  free ensures StartFuel__module._default.Divides == $LS(MoreFuel__module._default.Divides0);
  free ensures StartFuelAssert__module._default.Divides
     == $LS($LS(MoreFuel__module._default.Divides0));
  // Shortcut to LZ
  free ensures AsFuelBottom(MoreFuel__module._default.Divides0)
     == MoreFuel__module._default.Divides0;

