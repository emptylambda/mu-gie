// Dafny 2.0.0.00922 technical preview 0
// Command Line Options: /compile:0 /noVerify /print:Tree.bpl Tree.dfy

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

const unique class._module.Tree: ClassName;

// Constructor function declaration
function #_module.Tree.Leaf() : DatatypeType;

const unique ##_module.Tree.Leaf: DtCtorId;

// Constructor identifier
axiom DatatypeCtorId(#_module.Tree.Leaf()) == ##_module.Tree.Leaf;

function _module.Tree.Leaf_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType ::
  { _module.Tree.Leaf_q(d) }
  _module.Tree.Leaf_q(d) <==> DatatypeCtorId(d) == ##_module.Tree.Leaf);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType ::
  { _module.Tree.Leaf_q(d) }
  _module.Tree.Leaf_q(d) ==> d == #_module.Tree.Leaf());

function Tclass._module.Tree() : Ty;

// Tclass._module.Tree Tag
axiom Tag(Tclass._module.Tree()) == Tagclass._module.Tree;

const unique Tagclass._module.Tree: TyTag;

// Box/unbox axiom for Tclass._module.Tree
axiom (forall bx: Box ::
  { $IsBox(bx, Tclass._module.Tree()) }
  $IsBox(bx, Tclass._module.Tree())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.Tree()));

// Constructor $Is
axiom $Is(#_module.Tree.Leaf(), Tclass._module.Tree());

// Constructor $IsAlloc
axiom (forall $h: Heap ::
  { $IsAlloc(#_module.Tree.Leaf(), Tclass._module.Tree(), $h) }
  $IsGoodHeap($h) ==> $IsAlloc(#_module.Tree.Leaf(), Tclass._module.Tree(), $h));

// Constructor literal
axiom #_module.Tree.Leaf() == Lit(#_module.Tree.Leaf());

// Constructor function declaration
function #_module.Tree.Node(DatatypeType, DatatypeType) : DatatypeType;

const unique ##_module.Tree.Node: DtCtorId;

// Constructor identifier
axiom (forall a#19#0#0: DatatypeType, a#19#1#0: DatatypeType ::
  { #_module.Tree.Node(a#19#0#0, a#19#1#0) }
  DatatypeCtorId(#_module.Tree.Node(a#19#0#0, a#19#1#0)) == ##_module.Tree.Node);

function _module.Tree.Node_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType ::
  { _module.Tree.Node_q(d) }
  _module.Tree.Node_q(d) <==> DatatypeCtorId(d) == ##_module.Tree.Node);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType ::
  { _module.Tree.Node_q(d) }
  _module.Tree.Node_q(d)
     ==> (exists a#20#0#0: DatatypeType, a#20#1#0: DatatypeType ::
      d == #_module.Tree.Node(a#20#0#0, a#20#1#0)));

// Constructor $Is
axiom (forall a#21#0#0: DatatypeType, a#21#1#0: DatatypeType ::
  { $Is(#_module.Tree.Node(a#21#0#0, a#21#1#0), Tclass._module.Tree()) }
  $Is(#_module.Tree.Node(a#21#0#0, a#21#1#0), Tclass._module.Tree())
     <==> $Is(a#21#0#0, Tclass._module.Tree()) && $Is(a#21#1#0, Tclass._module.Tree()));

// Constructor $IsAlloc
axiom (forall a#22#0#0: DatatypeType, a#22#1#0: DatatypeType, $h: Heap ::
  { $IsAlloc(#_module.Tree.Node(a#22#0#0, a#22#1#0), Tclass._module.Tree(), $h) }
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Tree.Node(a#22#0#0, a#22#1#0), Tclass._module.Tree(), $h)
       <==> $IsAlloc(a#22#0#0, Tclass._module.Tree(), $h)
         && $IsAlloc(a#22#1#0, Tclass._module.Tree(), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap ::
  { $IsAlloc(_module.Tree._h0(d), Tclass._module.Tree(), $h) }
  $IsGoodHeap($h)
       &&
      _module.Tree.Node_q(d)
       && $IsAlloc(d, Tclass._module.Tree(), $h)
     ==> $IsAlloc(_module.Tree._h0(d), Tclass._module.Tree(), $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap ::
  { $IsAlloc(_module.Tree._h1(d), Tclass._module.Tree(), $h) }
  $IsGoodHeap($h)
       &&
      _module.Tree.Node_q(d)
       && $IsAlloc(d, Tclass._module.Tree(), $h)
     ==> $IsAlloc(_module.Tree._h1(d), Tclass._module.Tree(), $h));

// Constructor literal
axiom (forall a#23#0#0: DatatypeType, a#23#1#0: DatatypeType ::
  { #_module.Tree.Node(Lit(a#23#0#0), Lit(a#23#1#0)) }
  #_module.Tree.Node(Lit(a#23#0#0), Lit(a#23#1#0))
     == Lit(#_module.Tree.Node(a#23#0#0, a#23#1#0)));

function _module.Tree._h0(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#24#0#0: DatatypeType, a#24#1#0: DatatypeType ::
  { #_module.Tree.Node(a#24#0#0, a#24#1#0) }
  _module.Tree._h0(#_module.Tree.Node(a#24#0#0, a#24#1#0)) == a#24#0#0);

// Inductive rank
axiom (forall a#25#0#0: DatatypeType, a#25#1#0: DatatypeType ::
  { #_module.Tree.Node(a#25#0#0, a#25#1#0) }
  DtRank(a#25#0#0) < DtRank(#_module.Tree.Node(a#25#0#0, a#25#1#0)));

function _module.Tree._h1(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#26#0#0: DatatypeType, a#26#1#0: DatatypeType ::
  { #_module.Tree.Node(a#26#0#0, a#26#1#0) }
  _module.Tree._h1(#_module.Tree.Node(a#26#0#0, a#26#1#0)) == a#26#1#0);

// Inductive rank
axiom (forall a#27#0#0: DatatypeType, a#27#1#0: DatatypeType ::
  { #_module.Tree.Node(a#27#0#0, a#27#1#0) }
  DtRank(a#27#1#0) < DtRank(#_module.Tree.Node(a#27#0#0, a#27#1#0)));

// One-depth case-split function
function $IsA#_module.Tree(DatatypeType) : bool;

// One-depth case-split axiom
axiom (forall d: DatatypeType ::
  { $IsA#_module.Tree(d) }
  $IsA#_module.Tree(d) ==> _module.Tree.Leaf_q(d) || _module.Tree.Node_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType ::
  { _module.Tree.Node_q(d), $Is(d, Tclass._module.Tree()) }
    { _module.Tree.Leaf_q(d), $Is(d, Tclass._module.Tree()) }
  $Is(d, Tclass._module.Tree())
     ==> _module.Tree.Leaf_q(d) || _module.Tree.Node_q(d));

const unique class._module.Result: ClassName;

// Constructor function declaration
function #_module.Result.Fail() : DatatypeType;

const unique ##_module.Result.Fail: DtCtorId;

// Constructor identifier
axiom DatatypeCtorId(#_module.Result.Fail()) == ##_module.Result.Fail;

function _module.Result.Fail_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType ::
  { _module.Result.Fail_q(d) }
  _module.Result.Fail_q(d) <==> DatatypeCtorId(d) == ##_module.Result.Fail);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType ::
  { _module.Result.Fail_q(d) }
  _module.Result.Fail_q(d) ==> d == #_module.Result.Fail());

function Tclass._module.Result() : Ty;

// Tclass._module.Result Tag
axiom Tag(Tclass._module.Result()) == Tagclass._module.Result;

const unique Tagclass._module.Result: TyTag;

// Box/unbox axiom for Tclass._module.Result
axiom (forall bx: Box ::
  { $IsBox(bx, Tclass._module.Result()) }
  $IsBox(bx, Tclass._module.Result())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.Result()));

// Constructor $Is
axiom $Is(#_module.Result.Fail(), Tclass._module.Result());

// Constructor $IsAlloc
axiom (forall $h: Heap ::
  { $IsAlloc(#_module.Result.Fail(), Tclass._module.Result(), $h) }
  $IsGoodHeap($h)
     ==> $IsAlloc(#_module.Result.Fail(), Tclass._module.Result(), $h));

// Constructor literal
axiom #_module.Result.Fail() == Lit(#_module.Result.Fail());

// Constructor function declaration
function #_module.Result.Res(DatatypeType, Seq Box) : DatatypeType;

const unique ##_module.Result.Res: DtCtorId;

// Constructor identifier
axiom (forall a#33#0#0: DatatypeType, a#33#1#0: Seq Box ::
  { #_module.Result.Res(a#33#0#0, a#33#1#0) }
  DatatypeCtorId(#_module.Result.Res(a#33#0#0, a#33#1#0)) == ##_module.Result.Res);

function _module.Result.Res_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType ::
  { _module.Result.Res_q(d) }
  _module.Result.Res_q(d) <==> DatatypeCtorId(d) == ##_module.Result.Res);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType ::
  { _module.Result.Res_q(d) }
  _module.Result.Res_q(d)
     ==> (exists a#34#0#0: DatatypeType, a#34#1#0: Seq Box ::
      d == #_module.Result.Res(a#34#0#0, a#34#1#0)));

// Constructor $Is
axiom (forall a#35#0#0: DatatypeType, a#35#1#0: Seq Box ::
  { $Is(#_module.Result.Res(a#35#0#0, a#35#1#0), Tclass._module.Result()) }
  $Is(#_module.Result.Res(a#35#0#0, a#35#1#0), Tclass._module.Result())
     <==> $Is(a#35#0#0, Tclass._module.Tree()) && $Is(a#35#1#0, TSeq(TInt)));

// Constructor $IsAlloc
axiom (forall a#36#0#0: DatatypeType, a#36#1#0: Seq Box, $h: Heap ::
  { $IsAlloc(#_module.Result.Res(a#36#0#0, a#36#1#0), Tclass._module.Result(), $h) }
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Result.Res(a#36#0#0, a#36#1#0), Tclass._module.Result(), $h)
       <==> $IsAlloc(a#36#0#0, Tclass._module.Tree(), $h)
         && $IsAlloc(a#36#1#0, TSeq(TInt), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap ::
  { $IsAlloc(_module.Result.t(d), Tclass._module.Tree(), $h) }
  $IsGoodHeap($h)
       &&
      _module.Result.Res_q(d)
       && $IsAlloc(d, Tclass._module.Result(), $h)
     ==> $IsAlloc(_module.Result.t(d), Tclass._module.Tree(), $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap ::
  { $IsAlloc(_module.Result.sOut(d), TSeq(TInt), $h) }
  $IsGoodHeap($h)
       &&
      _module.Result.Res_q(d)
       && $IsAlloc(d, Tclass._module.Result(), $h)
     ==> $IsAlloc(_module.Result.sOut(d), TSeq(TInt), $h));

// Constructor literal
axiom (forall a#37#0#0: DatatypeType, a#37#1#0: Seq Box ::
  { #_module.Result.Res(Lit(a#37#0#0), Lit(a#37#1#0)) }
  #_module.Result.Res(Lit(a#37#0#0), Lit(a#37#1#0))
     == Lit(#_module.Result.Res(a#37#0#0, a#37#1#0)));

function _module.Result.t(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#38#0#0: DatatypeType, a#38#1#0: Seq Box ::
  { #_module.Result.Res(a#38#0#0, a#38#1#0) }
  _module.Result.t(#_module.Result.Res(a#38#0#0, a#38#1#0)) == a#38#0#0);

// Inductive rank
axiom (forall a#39#0#0: DatatypeType, a#39#1#0: Seq Box ::
  { #_module.Result.Res(a#39#0#0, a#39#1#0) }
  DtRank(a#39#0#0) < DtRank(#_module.Result.Res(a#39#0#0, a#39#1#0)));

function _module.Result.sOut(DatatypeType) : Seq Box;

// Constructor injectivity
axiom (forall a#40#0#0: DatatypeType, a#40#1#0: Seq Box ::
  { #_module.Result.Res(a#40#0#0, a#40#1#0) }
  _module.Result.sOut(#_module.Result.Res(a#40#0#0, a#40#1#0)) == a#40#1#0);

axiom (forall a#41#0#0: DatatypeType, a#41#1#0: Seq Box, i: int ::
  { Seq#Index(a#41#1#0, i), #_module.Result.Res(a#41#0#0, a#41#1#0) }
  0 <= i && i < Seq#Length(a#41#1#0)
     ==> DtRank($Unbox(Seq#Index(a#41#1#0, i)): DatatypeType)
       < DtRank(#_module.Result.Res(a#41#0#0, a#41#1#0)));

// Inductive seq rank
axiom (forall a#42#0#0: DatatypeType, a#42#1#0: Seq Box ::
  { #_module.Result.Res(a#42#0#0, a#42#1#0) }
  Seq#Rank(a#42#1#0) < DtRank(#_module.Result.Res(a#42#0#0, a#42#1#0)));

// One-depth case-split function
function $IsA#_module.Result(DatatypeType) : bool;

// One-depth case-split axiom
axiom (forall d: DatatypeType ::
  { $IsA#_module.Result(d) }
  $IsA#_module.Result(d) ==> _module.Result.Fail_q(d) || _module.Result.Res_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType ::
  { _module.Result.Res_q(d), $Is(d, Tclass._module.Result()) }
    { _module.Result.Fail_q(d), $Is(d, Tclass._module.Result()) }
  $Is(d, Tclass._module.Result())
     ==> _module.Result.Fail_q(d) || _module.Result.Res_q(d));

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

// function declaration for _module._default.toList
function _module.__default.toList($ly: LayerType, d#0: int, t#0: DatatypeType) : Seq Box;

function _module.__default.toList#canCall(d#0: int, t#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, d#0: int, t#0: DatatypeType ::
  { _module.__default.toList($LS($ly), d#0, t#0) }
  _module.__default.toList($LS($ly), d#0, t#0)
     == _module.__default.toList($ly, d#0, t#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, d#0: int, t#0: DatatypeType ::
  { _module.__default.toList(AsFuelBottom($ly), d#0, t#0) }
  _module.__default.toList($ly, d#0, t#0)
     == _module.__default.toList($LZ, d#0, t#0));

// consequence axiom for _module.__default.toList
axiom 0 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, d#0: int, t#0: DatatypeType ::
    { _module.__default.toList($ly, d#0, t#0) }
    _module.__default.toList#canCall(d#0, t#0)
         || (0 != $FunctionContextHeight && $Is(t#0, Tclass._module.Tree()))
       ==> !Seq#Equal(_module.__default.toList($ly, d#0, t#0), Seq#Empty(): Seq Box)
         && $Unbox(Seq#Index(_module.__default.toList($ly, d#0, t#0), LitInt(0))): int
           >= d#0
         && ($Unbox(Seq#Index(_module.__default.toList($ly, d#0, t#0), LitInt(0))): int
           == d#0)
           ==
          (t#0
           == Lit(#_module.Tree.Leaf()))
         && $Is(_module.__default.toList($ly, d#0, t#0), TSeq(TInt)));

function _module.__default.toList#requires(LayerType, int, DatatypeType) : bool;

// #requires axiom for _module.__default.toList
axiom (forall $ly: LayerType, d#0: int, t#0: DatatypeType ::
  { _module.__default.toList#requires($ly, d#0, t#0) }
  $Is(t#0, Tclass._module.Tree())
     ==> _module.__default.toList#requires($ly, d#0, t#0) == true);

// definition axiom for _module.__default.toList(revealed)
axiom 0 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, d#0: int, t#0: DatatypeType ::
    { _module.__default.toList($LS($ly), d#0, t#0) }
    _module.__default.toList#canCall(d#0, t#0)
         || (0 != $FunctionContextHeight && $Is(t#0, Tclass._module.Tree()))
       ==> (!_module.Tree.Leaf_q(t#0)
           ==> _module.__default.toList#canCall(d#0 + 1, _module.Tree._h0(t#0))
             && _module.__default.toList#canCall(d#0 + 1, _module.Tree._h1(t#0)))
         && _module.__default.toList($LS($ly), d#0, t#0)
           == (if _module.Tree.Leaf_q(t#0)
             then Seq#Build(Seq#Empty(): Seq Box, $Box(d#0))
             else Seq#Append(_module.__default.toList($ly, d#0 + 1, _module.Tree._h0(t#0)),
              _module.__default.toList($ly, d#0 + 1, _module.Tree._h1(t#0)))));

// definition axiom for _module.__default.toList for decreasing-related literals(revealed)
axiom 0 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, d#0: int, t#0: DatatypeType ::
    {:weight 3} { _module.__default.toList($LS($ly), d#0, Lit(t#0)) }
    _module.__default.toList#canCall(d#0, Lit(t#0))
         || (0 != $FunctionContextHeight && $Is(t#0, Tclass._module.Tree()))
       ==> (!Lit(_module.Tree.Leaf_q(Lit(t#0)))
           ==> _module.__default.toList#canCall(d#0 + 1, Lit(_module.Tree._h0(Lit(t#0))))
             && _module.__default.toList#canCall(d#0 + 1, Lit(_module.Tree._h1(Lit(t#0)))))
         && _module.__default.toList($LS($ly), d#0, Lit(t#0))
           == (if _module.Tree.Leaf_q(Lit(t#0))
             then Seq#Build(Seq#Empty(): Seq Box, $Box(d#0))
             else Seq#Append(_module.__default.toList($LS($ly), d#0 + 1, Lit(_module.Tree._h0(Lit(t#0)))),
              _module.__default.toList($LS($ly), d#0 + 1, Lit(_module.Tree._h1(Lit(t#0)))))));

// definition axiom for _module.__default.toList for all literals(revealed)
axiom 0 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, d#0: int, t#0: DatatypeType ::
    {:weight 3} { _module.__default.toList($LS($ly), LitInt(d#0), Lit(t#0)) }
    _module.__default.toList#canCall(LitInt(d#0), Lit(t#0))
         || (0 != $FunctionContextHeight && $Is(t#0, Tclass._module.Tree()))
       ==> (!Lit(_module.Tree.Leaf_q(Lit(t#0)))
           ==> _module.__default.toList#canCall(LitInt(d#0 + 1), Lit(_module.Tree._h0(Lit(t#0))))
             && _module.__default.toList#canCall(LitInt(d#0 + 1), Lit(_module.Tree._h1(Lit(t#0)))))
         && _module.__default.toList($LS($ly), LitInt(d#0), Lit(t#0))
           == (if _module.Tree.Leaf_q(Lit(t#0))
             then Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(d#0)))
             else Seq#Append(_module.__default.toList($LS($ly), LitInt(d#0 + 1), Lit(_module.Tree._h0(Lit(t#0)))),
              _module.__default.toList($LS($ly), LitInt(d#0 + 1), Lit(_module.Tree._h1(Lit(t#0)))))));

procedure CheckWellformed$$_module.__default.toList(d#0: int, t#0: DatatypeType where $Is(t#0, Tclass._module.Tree()));
  free requires 0 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  ensures !Seq#Equal(_module.__default.toList($LS($LS($LZ)), d#0, t#0), Seq#Empty(): Seq Box);
  ensures $Unbox(Seq#Index(_module.__default.toList($LS($LS($LZ)), d#0, t#0), LitInt(0))): int
     >= d#0;
  ensures ($Unbox(Seq#Index(_module.__default.toList($LS($LS($LZ)), d#0, t#0), LitInt(0))): int
     == d#0)
     ==
    (t#0
     == Lit(#_module.Tree.Leaf()));



implementation CheckWellformed$$_module.__default.toList(d#0: int, t#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##d#0: int;
  var ##t#0: DatatypeType;
  var ##d#1: int;
  var ##t#1: DatatypeType;
  var ##d#2: int;
  var ##t#2: DatatypeType;
  var l#0: DatatypeType;
  var r#0: DatatypeType;
  var ##d#3: int;
  var ##t#3: DatatypeType;
  var ##d#4: int;
  var ##t#4: DatatypeType;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function toList
    assume {:captureState "Tree.dfy(24,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.toList($LS($LZ), d#0, t#0), TSeq(TInt));
        ##d#0 := d#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##d#0, TInt, $Heap);
        ##t#0 := t#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##t#0, Tclass._module.Tree(), $Heap);
        assert (d#0 == d#0 && t#0 == t#0) || DtRank(##t#0) < DtRank(t#0);
        assume (d#0 == d#0 && t#0 == t#0) || _module.__default.toList#canCall(d#0, t#0);
        assume !Seq#Equal(_module.__default.toList($LS($LZ), d#0, t#0), Seq#Empty(): Seq Box);
        ##d#1 := d#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##d#1, TInt, $Heap);
        ##t#1 := t#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##t#1, Tclass._module.Tree(), $Heap);
        assert (d#0 == d#0 && t#0 == t#0) || DtRank(##t#1) < DtRank(t#0);
        assume (d#0 == d#0 && t#0 == t#0) || _module.__default.toList#canCall(d#0, t#0);
        assert 0 <= LitInt(0)
           && LitInt(0) < Seq#Length(_module.__default.toList($LS($LZ), d#0, t#0));
        assume $Unbox(Seq#Index(_module.__default.toList($LS($LZ), d#0, t#0), LitInt(0))): int
           >= d#0;
        ##d#2 := d#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##d#2, TInt, $Heap);
        ##t#2 := t#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##t#2, Tclass._module.Tree(), $Heap);
        assert (d#0 == d#0 && t#0 == t#0) || DtRank(##t#2) < DtRank(t#0);
        assume (d#0 == d#0 && t#0 == t#0) || _module.__default.toList#canCall(d#0, t#0);
        assert 0 <= LitInt(0)
           && LitInt(0) < Seq#Length(_module.__default.toList($LS($LZ), d#0, t#0));
        assume ($Unbox(Seq#Index(_module.__default.toList($LS($LZ), d#0, t#0), LitInt(0))): int
           == d#0)
           ==
          (t#0
           == Lit(#_module.Tree.Leaf()));
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
          $o != null && read($Heap, $o, alloc) ==> false);
        if (t#0 == #_module.Tree.Leaf())
        {
            assume _module.__default.toList($LS($LZ), d#0, t#0)
               == Seq#Build(Seq#Empty(): Seq Box, $Box(d#0));
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.toList($LS($LZ), d#0, t#0), TSeq(TInt));
        }
        else if (t#0 == #_module.Tree.Node(l#0, r#0))
        {
            assume $Is(l#0, Tclass._module.Tree());
            assume $Is(r#0, Tclass._module.Tree());
            ##d#3 := d#0 + 1;
            // assume allocatedness for argument to function
            assume $IsAlloc(##d#3, TInt, $Heap);
            ##t#3 := l#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##t#3, Tclass._module.Tree(), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert DtRank(##t#3) < DtRank(t#0);
            assume _module.__default.toList#canCall(d#0 + 1, l#0);
            ##d#4 := d#0 + 1;
            // assume allocatedness for argument to function
            assume $IsAlloc(##d#4, TInt, $Heap);
            ##t#4 := r#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##t#4, Tclass._module.Tree(), $Heap);
            b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert DtRank(##t#4) < DtRank(t#0);
            assume _module.__default.toList#canCall(d#0 + 1, r#0);
            assume _module.__default.toList($LS($LZ), d#0, t#0)
               == Seq#Append(_module.__default.toList($LS($LZ), d#0 + 1, l#0),
                _module.__default.toList($LS($LZ), d#0 + 1, r#0));
            assume _module.__default.toList#canCall(d#0 + 1, l#0)
               && _module.__default.toList#canCall(d#0 + 1, r#0);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.toList($LS($LZ), d#0, t#0), TSeq(TInt));
        }
        else
        {
            assume false;
        }

        assert b$reqreads#0;
        assert b$reqreads#1;
    }
}



// function declaration for _module._default.build_rec
function _module.__default.build__rec($ly: LayerType, d#0: int, s#0: Seq Box) : DatatypeType;

function _module.__default.build__rec#canCall(d#0: int, s#0: Seq Box) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, d#0: int, s#0: Seq Box ::
  { _module.__default.build__rec($LS($ly), d#0, s#0) }
  _module.__default.build__rec($LS($ly), d#0, s#0)
     == _module.__default.build__rec($ly, d#0, s#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, d#0: int, s#0: Seq Box ::
  { _module.__default.build__rec(AsFuelBottom($ly), d#0, s#0) }
  _module.__default.build__rec($ly, d#0, s#0)
     == _module.__default.build__rec($LZ, d#0, s#0));

// consequence axiom for _module.__default.build__rec
axiom 1 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, $Heap: Heap, d#0: int, s#0: Seq Box ::
    { _module.__default.build__rec($ly, d#0, s#0), $IsGoodHeap($Heap) }
    _module.__default.build__rec#canCall(d#0, s#0)
         || (1 != $FunctionContextHeight && $IsGoodHeap($Heap) && $Is(s#0, TSeq(TInt)))
       ==> (_module.Result.Res_q(_module.__default.build__rec($ly, d#0, s#0))
           ==> Seq#Length(_module.Result.sOut(_module.__default.build__rec($ly, d#0, s#0)))
               < Seq#Length(s#0)
             && Seq#Equal(_module.Result.sOut(_module.__default.build__rec($ly, d#0, s#0)),
              Seq#Drop(s#0,
                Seq#Length(s#0)
                   - Seq#Length(_module.Result.sOut(_module.__default.build__rec($ly, d#0, s#0))))))
         && (_module.Result.Res_q(_module.__default.build__rec($ly, d#0, s#0))
           ==> Seq#Equal(_module.__default.toList($LS($LZ), d#0, _module.Result.t(_module.__default.build__rec($ly, d#0, s#0))),
            Seq#Take(s#0,
              Seq#Length(s#0)
                 - Seq#Length(_module.Result.sOut(_module.__default.build__rec($ly, d#0, s#0))))))
         && $Is(_module.__default.build__rec($ly, d#0, s#0), Tclass._module.Result()));

function _module.__default.build__rec#requires(LayerType, int, Seq Box) : bool;

// #requires axiom for _module.__default.build__rec
axiom (forall $ly: LayerType, $Heap: Heap, d#0: int, s#0: Seq Box ::
  { _module.__default.build__rec#requires($ly, d#0, s#0), $IsGoodHeap($Heap) }
  $IsGoodHeap($Heap) && $Is(s#0, TSeq(TInt))
     ==> _module.__default.build__rec#requires($ly, d#0, s#0) == true);

// definition axiom for _module.__default.build__rec(revealed)
axiom 1 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, $Heap: Heap, d#0: int, s#0: Seq Box ::
    { _module.__default.build__rec($LS($ly), d#0, s#0), $IsGoodHeap($Heap) }
    _module.__default.build__rec#canCall(d#0, s#0)
         || (1 != $FunctionContextHeight && $IsGoodHeap($Heap) && $Is(s#0, TSeq(TInt)))
       ==> (!(Seq#Equal(s#0, Seq#Empty(): Seq Box)
             || $Unbox(Seq#Index(s#0, LitInt(0))): int < d#0)
           ==>
          $Unbox(Seq#Index(s#0, LitInt(0))): int != d#0
           ==> _module.__default.build__rec#canCall(d#0 + 1, s#0)
             && (!_module.Result.Fail_q(_module.__default.build__rec($ly, d#0 + 1, s#0))
               ==> _module.__default.build__rec#canCall(d#0 + 1, _module.Result.sOut(_module.__default.build__rec($ly, d#0 + 1, s#0)))))
         && _module.__default.build__rec($LS($ly), d#0, s#0)
           == (if Seq#Equal(s#0, Seq#Empty(): Seq Box)
               || $Unbox(Seq#Index(s#0, LitInt(0))): int < d#0
             then #_module.Result.Fail()
             else (if $Unbox(Seq#Index(s#0, LitInt(0))): int == d#0
               then #_module.Result.Res(Lit(#_module.Tree.Leaf()), Seq#Drop(s#0, LitInt(1)))
               else (if _module.Result.Fail_q(_module.__default.build__rec($ly, d#0 + 1, s#0))
                 then #_module.Result.Fail()
                 else (if _module.Result.Fail_q(_module.__default.build__rec($ly,
                      d#0 + 1,
                      _module.Result.sOut(_module.__default.build__rec($ly, d#0 + 1, s#0))))
                   then #_module.Result.Fail()
                   else #_module.Result.Res(#_module.Tree.Node(_module.Result.t(_module.__default.build__rec($ly, d#0 + 1, s#0)),
                      _module.Result.t(_module.__default.build__rec($ly,
                          d#0 + 1,
                          _module.Result.sOut(_module.__default.build__rec($ly, d#0 + 1, s#0))))),
                    _module.Result.sOut(_module.__default.build__rec($ly,
                        d#0 + 1,
                        _module.Result.sOut(_module.__default.build__rec($ly, d#0 + 1, s#0))))))))));

// definition axiom for _module.__default.build__rec for all literals(revealed)
axiom 1 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, $Heap: Heap, d#0: int, s#0: Seq Box ::
    {:weight 3} { _module.__default.build__rec($LS($ly), LitInt(d#0), Lit(s#0)), $IsGoodHeap($Heap) }
    _module.__default.build__rec#canCall(LitInt(d#0), Lit(s#0))
         || (1 != $FunctionContextHeight && $IsGoodHeap($Heap) && $Is(s#0, TSeq(TInt)))
       ==> (!(Seq#Equal(s#0, Seq#Empty(): Seq Box)
             || $Unbox(Seq#Index(Lit(s#0), LitInt(0))): int < d#0)
           ==>
          $Unbox(Seq#Index(Lit(s#0), LitInt(0))): int != LitInt(d#0)
           ==> _module.__default.build__rec#canCall(LitInt(d#0 + 1), Lit(s#0))
             && (!Lit(_module.Result.Fail_q(Lit(_module.__default.build__rec($LS($ly), LitInt(d#0 + 1), Lit(s#0)))))
               ==> _module.__default.build__rec#canCall(LitInt(d#0 + 1),
                Lit(_module.Result.sOut(Lit(_module.__default.build__rec($LS($ly), LitInt(d#0 + 1), Lit(s#0))))))))
         && _module.__default.build__rec($LS($ly), LitInt(d#0), Lit(s#0))
           == (if Seq#Equal(s#0, Seq#Empty(): Seq Box)
               || $Unbox(Seq#Index(Lit(s#0), LitInt(0))): int < d#0
             then #_module.Result.Fail()
             else (if $Unbox(Seq#Index(Lit(s#0), LitInt(0))): int == LitInt(d#0)
               then #_module.Result.Res(Lit(#_module.Tree.Leaf()), Lit(Seq#Drop(Lit(s#0), LitInt(1))))
               else (if _module.Result.Fail_q(Lit(_module.__default.build__rec($LS($ly), LitInt(d#0 + 1), Lit(s#0))))
                 then #_module.Result.Fail()
                 else (if _module.Result.Fail_q(Lit(_module.__default.build__rec($LS($ly),
                        LitInt(d#0 + 1),
                        Lit(_module.Result.sOut(Lit(_module.__default.build__rec($LS($ly), LitInt(d#0 + 1), Lit(s#0))))))))
                   then #_module.Result.Fail()
                   else #_module.Result.Res(Lit(#_module.Tree.Node(Lit(_module.Result.t(Lit(_module.__default.build__rec($LS($ly), LitInt(d#0 + 1), Lit(s#0))))),
                        Lit(_module.Result.t(Lit(_module.__default.build__rec($LS($ly),
                                LitInt(d#0 + 1),
                                Lit(_module.Result.sOut(Lit(_module.__default.build__rec($LS($ly), LitInt(d#0 + 1), Lit(s#0))))))))))),
                    Lit(_module.Result.sOut(Lit(_module.__default.build__rec($LS($ly),
                            LitInt(d#0 + 1),
                            Lit(_module.Result.sOut(Lit(_module.__default.build__rec($LS($ly), LitInt(d#0 + 1), Lit(s#0)))))))))))))));

procedure CheckWellformed$$_module.__default.build__rec(d#0: int, s#0: Seq Box where $Is(s#0, TSeq(TInt)));
  free requires 1 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  ensures _module.Result.Res_q(_module.__default.build__rec($LS($LZ), d#0, s#0))
     ==> Seq#Length(_module.Result.sOut(_module.__default.build__rec($LS($LS($LZ)), d#0, s#0)))
       < Seq#Length(s#0);
  ensures _module.Result.Res_q(_module.__default.build__rec($LS($LZ), d#0, s#0))
     ==> Seq#Equal(_module.Result.sOut(_module.__default.build__rec($LS($LS($LZ)), d#0, s#0)),
      Seq#Drop(s#0,
        Seq#Length(s#0)
           - Seq#Length(_module.Result.sOut(_module.__default.build__rec($LS($LS($LZ)), d#0, s#0)))));
  ensures _module.Result.Res_q(_module.__default.build__rec($LS($LZ), d#0, s#0))
     ==> Seq#Equal(_module.__default.toList($LS($LS($LZ)),
        d#0,
        _module.Result.t(_module.__default.build__rec($LS($LS($LZ)), d#0, s#0))),
      Seq#Take(s#0,
        Seq#Length(s#0)
           - Seq#Length(_module.Result.sOut(_module.__default.build__rec($LS($LS($LZ)), d#0, s#0)))));



implementation CheckWellformed$$_module.__default.build__rec(d#0: int, s#0: Seq Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##d#0: int;
  var ##s#0: Seq Box;
  var ##d#1: int;
  var ##s#1: Seq Box;
  var ##d#2: int;
  var ##s#2: Seq Box;
  var ##d#3: int;
  var ##s#3: Seq Box;
  var ##d#4: int;
  var ##s#4: Seq Box;
  var ##d#5: int;
  var ##s#5: Seq Box;
  var ##d#6: int;
  var ##t#0: DatatypeType;
  var ##d#7: int;
  var ##s#6: Seq Box;
  var left#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var ##d#8: int;
  var ##s#7: Seq Box;
  var right#0: DatatypeType;
  var let#1#0#0: DatatypeType;
  var ##d#9: int;
  var ##s#8: Seq Box;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function build_rec
    assume {:captureState "Tree.dfy(43,16): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    if (Seq#Equal(s#0, Seq#Empty(): Seq Box))
    {
    }
    else
    {
        assert 0 <= LitInt(0) && LitInt(0) < Seq#Length(s#0);
    }

    if (*)
    {
        assume $Is(_module.__default.build__rec($LS($LZ), d#0, s#0), Tclass._module.Result());
        if (*)
        {
            ##d#0 := d#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##d#0, TInt, $Heap);
            ##s#0 := s#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#0, TSeq(TInt), $Heap);
            assert 0 <= Seq#Length(s#0) || Seq#Length(##s#0) == Seq#Length(s#0);
            assert 0
                 <= (if Seq#Equal(s#0, Seq#Empty(): Seq Box)
                   then 0
                   else $Unbox(Seq#Index(s#0, LitInt(0))): int - d#0)
               || Seq#Length(##s#0) < Seq#Length(s#0)
               || (if Seq#Equal(##s#0, Seq#Empty(): Seq Box)
                   then 0
                   else $Unbox(Seq#Index(##s#0, LitInt(0))): int - ##d#0)
                 == (if Seq#Equal(s#0, Seq#Empty(): Seq Box)
                   then 0
                   else $Unbox(Seq#Index(s#0, LitInt(0))): int - d#0);
            assert (d#0 == d#0 && s#0 == s#0)
               ||
              Seq#Length(##s#0) < Seq#Length(s#0)
               || (Seq#Length(##s#0) == Seq#Length(s#0)
                 && (if Seq#Equal(##s#0, Seq#Empty(): Seq Box)
                     then 0
                     else $Unbox(Seq#Index(##s#0, LitInt(0))): int - ##d#0)
                   < (if Seq#Equal(s#0, Seq#Empty(): Seq Box)
                     then 0
                     else $Unbox(Seq#Index(s#0, LitInt(0))): int - d#0));
            assume (d#0 == d#0 && s#0 == s#0) || _module.__default.build__rec#canCall(d#0, s#0);
            assume _module.Result.Res_q(_module.__default.build__rec($LS($LZ), d#0, s#0));
            ##d#1 := d#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##d#1, TInt, $Heap);
            ##s#1 := s#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#1, TSeq(TInt), $Heap);
            assert 0 <= Seq#Length(s#0) || Seq#Length(##s#1) == Seq#Length(s#0);
            assert 0
                 <= (if Seq#Equal(s#0, Seq#Empty(): Seq Box)
                   then 0
                   else $Unbox(Seq#Index(s#0, LitInt(0))): int - d#0)
               || Seq#Length(##s#1) < Seq#Length(s#0)
               || (if Seq#Equal(##s#1, Seq#Empty(): Seq Box)
                   then 0
                   else $Unbox(Seq#Index(##s#1, LitInt(0))): int - ##d#1)
                 == (if Seq#Equal(s#0, Seq#Empty(): Seq Box)
                   then 0
                   else $Unbox(Seq#Index(s#0, LitInt(0))): int - d#0);
            assert (d#0 == d#0 && s#0 == s#0)
               ||
              Seq#Length(##s#1) < Seq#Length(s#0)
               || (Seq#Length(##s#1) == Seq#Length(s#0)
                 && (if Seq#Equal(##s#1, Seq#Empty(): Seq Box)
                     then 0
                     else $Unbox(Seq#Index(##s#1, LitInt(0))): int - ##d#1)
                   < (if Seq#Equal(s#0, Seq#Empty(): Seq Box)
                     then 0
                     else $Unbox(Seq#Index(s#0, LitInt(0))): int - d#0));
            assume (d#0 == d#0 && s#0 == s#0) || _module.__default.build__rec#canCall(d#0, s#0);
            assert _module.Result.Res_q(_module.__default.build__rec($LS($LZ), d#0, s#0));
            assume Seq#Length(_module.Result.sOut(_module.__default.build__rec($LS($LZ), d#0, s#0)))
               < Seq#Length(s#0);
            ##d#2 := d#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##d#2, TInt, $Heap);
            ##s#2 := s#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#2, TSeq(TInt), $Heap);
            assert 0 <= Seq#Length(s#0) || Seq#Length(##s#2) == Seq#Length(s#0);
            assert 0
                 <= (if Seq#Equal(s#0, Seq#Empty(): Seq Box)
                   then 0
                   else $Unbox(Seq#Index(s#0, LitInt(0))): int - d#0)
               || Seq#Length(##s#2) < Seq#Length(s#0)
               || (if Seq#Equal(##s#2, Seq#Empty(): Seq Box)
                   then 0
                   else $Unbox(Seq#Index(##s#2, LitInt(0))): int - ##d#2)
                 == (if Seq#Equal(s#0, Seq#Empty(): Seq Box)
                   then 0
                   else $Unbox(Seq#Index(s#0, LitInt(0))): int - d#0);
            assert (d#0 == d#0 && s#0 == s#0)
               ||
              Seq#Length(##s#2) < Seq#Length(s#0)
               || (Seq#Length(##s#2) == Seq#Length(s#0)
                 && (if Seq#Equal(##s#2, Seq#Empty(): Seq Box)
                     then 0
                     else $Unbox(Seq#Index(##s#2, LitInt(0))): int - ##d#2)
                   < (if Seq#Equal(s#0, Seq#Empty(): Seq Box)
                     then 0
                     else $Unbox(Seq#Index(s#0, LitInt(0))): int - d#0));
            assume (d#0 == d#0 && s#0 == s#0) || _module.__default.build__rec#canCall(d#0, s#0);
            assert _module.Result.Res_q(_module.__default.build__rec($LS($LZ), d#0, s#0));
            ##d#3 := d#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##d#3, TInt, $Heap);
            ##s#3 := s#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#3, TSeq(TInt), $Heap);
            assert 0 <= Seq#Length(s#0) || Seq#Length(##s#3) == Seq#Length(s#0);
            assert 0
                 <= (if Seq#Equal(s#0, Seq#Empty(): Seq Box)
                   then 0
                   else $Unbox(Seq#Index(s#0, LitInt(0))): int - d#0)
               || Seq#Length(##s#3) < Seq#Length(s#0)
               || (if Seq#Equal(##s#3, Seq#Empty(): Seq Box)
                   then 0
                   else $Unbox(Seq#Index(##s#3, LitInt(0))): int - ##d#3)
                 == (if Seq#Equal(s#0, Seq#Empty(): Seq Box)
                   then 0
                   else $Unbox(Seq#Index(s#0, LitInt(0))): int - d#0);
            assert (d#0 == d#0 && s#0 == s#0)
               ||
              Seq#Length(##s#3) < Seq#Length(s#0)
               || (Seq#Length(##s#3) == Seq#Length(s#0)
                 && (if Seq#Equal(##s#3, Seq#Empty(): Seq Box)
                     then 0
                     else $Unbox(Seq#Index(##s#3, LitInt(0))): int - ##d#3)
                   < (if Seq#Equal(s#0, Seq#Empty(): Seq Box)
                     then 0
                     else $Unbox(Seq#Index(s#0, LitInt(0))): int - d#0));
            assume (d#0 == d#0 && s#0 == s#0) || _module.__default.build__rec#canCall(d#0, s#0);
            assert _module.Result.Res_q(_module.__default.build__rec($LS($LZ), d#0, s#0));
            assert 0
                 <= Seq#Length(s#0)
                   - Seq#Length(_module.Result.sOut(_module.__default.build__rec($LS($LZ), d#0, s#0)))
               && Seq#Length(s#0)
                   - Seq#Length(_module.Result.sOut(_module.__default.build__rec($LS($LZ), d#0, s#0)))
                 <= Seq#Length(s#0);
            assume Seq#Equal(_module.Result.sOut(_module.__default.build__rec($LS($LZ), d#0, s#0)),
              Seq#Drop(s#0,
                Seq#Length(s#0)
                   - Seq#Length(_module.Result.sOut(_module.__default.build__rec($LS($LZ), d#0, s#0)))));
        }
        else
        {
            assume _module.Result.Res_q(_module.__default.build__rec($LS($LZ), d#0, s#0))
               ==> Seq#Length(_module.Result.sOut(_module.__default.build__rec($LS($LZ), d#0, s#0)))
                   < Seq#Length(s#0)
                 && Seq#Equal(_module.Result.sOut(_module.__default.build__rec($LS($LZ), d#0, s#0)),
                  Seq#Drop(s#0,
                    Seq#Length(s#0)
                       - Seq#Length(_module.Result.sOut(_module.__default.build__rec($LS($LZ), d#0, s#0)))));
        }

        if (*)
        {
            ##d#4 := d#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##d#4, TInt, $Heap);
            ##s#4 := s#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#4, TSeq(TInt), $Heap);
            assert 0 <= Seq#Length(s#0) || Seq#Length(##s#4) == Seq#Length(s#0);
            assert 0
                 <= (if Seq#Equal(s#0, Seq#Empty(): Seq Box)
                   then 0
                   else $Unbox(Seq#Index(s#0, LitInt(0))): int - d#0)
               || Seq#Length(##s#4) < Seq#Length(s#0)
               || (if Seq#Equal(##s#4, Seq#Empty(): Seq Box)
                   then 0
                   else $Unbox(Seq#Index(##s#4, LitInt(0))): int - ##d#4)
                 == (if Seq#Equal(s#0, Seq#Empty(): Seq Box)
                   then 0
                   else $Unbox(Seq#Index(s#0, LitInt(0))): int - d#0);
            assert (d#0 == d#0 && s#0 == s#0)
               ||
              Seq#Length(##s#4) < Seq#Length(s#0)
               || (Seq#Length(##s#4) == Seq#Length(s#0)
                 && (if Seq#Equal(##s#4, Seq#Empty(): Seq Box)
                     then 0
                     else $Unbox(Seq#Index(##s#4, LitInt(0))): int - ##d#4)
                   < (if Seq#Equal(s#0, Seq#Empty(): Seq Box)
                     then 0
                     else $Unbox(Seq#Index(s#0, LitInt(0))): int - d#0));
            assume (d#0 == d#0 && s#0 == s#0) || _module.__default.build__rec#canCall(d#0, s#0);
            assume _module.Result.Res_q(_module.__default.build__rec($LS($LZ), d#0, s#0));
            ##d#5 := d#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##d#5, TInt, $Heap);
            ##s#5 := s#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#5, TSeq(TInt), $Heap);
            assert 0 <= Seq#Length(s#0) || Seq#Length(##s#5) == Seq#Length(s#0);
            assert 0
                 <= (if Seq#Equal(s#0, Seq#Empty(): Seq Box)
                   then 0
                   else $Unbox(Seq#Index(s#0, LitInt(0))): int - d#0)
               || Seq#Length(##s#5) < Seq#Length(s#0)
               || (if Seq#Equal(##s#5, Seq#Empty(): Seq Box)
                   then 0
                   else $Unbox(Seq#Index(##s#5, LitInt(0))): int - ##d#5)
                 == (if Seq#Equal(s#0, Seq#Empty(): Seq Box)
                   then 0
                   else $Unbox(Seq#Index(s#0, LitInt(0))): int - d#0);
            assert (d#0 == d#0 && s#0 == s#0)
               ||
              Seq#Length(##s#5) < Seq#Length(s#0)
               || (Seq#Length(##s#5) == Seq#Length(s#0)
                 && (if Seq#Equal(##s#5, Seq#Empty(): Seq Box)
                     then 0
                     else $Unbox(Seq#Index(##s#5, LitInt(0))): int - ##d#5)
                   < (if Seq#Equal(s#0, Seq#Empty(): Seq Box)
                     then 0
                     else $Unbox(Seq#Index(s#0, LitInt(0))): int - d#0));
            assume (d#0 == d#0 && s#0 == s#0) || _module.__default.build__rec#canCall(d#0, s#0);
            assert _module.Result.Res_q(_module.__default.build__rec($LS($LZ), d#0, s#0));
            ##d#6 := d#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##d#6, TInt, $Heap);
            ##t#0 := _module.Result.t(_module.__default.build__rec($LS($LZ), d#0, s#0));
            // assume allocatedness for argument to function
            assume $IsAlloc(##t#0, Tclass._module.Tree(), $Heap);
            assume _module.__default.toList#canCall(d#0, _module.Result.t(_module.__default.build__rec($LS($LZ), d#0, s#0)));
            ##d#7 := d#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##d#7, TInt, $Heap);
            ##s#6 := s#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#6, TSeq(TInt), $Heap);
            assert 0 <= Seq#Length(s#0) || Seq#Length(##s#6) == Seq#Length(s#0);
            assert 0
                 <= (if Seq#Equal(s#0, Seq#Empty(): Seq Box)
                   then 0
                   else $Unbox(Seq#Index(s#0, LitInt(0))): int - d#0)
               || Seq#Length(##s#6) < Seq#Length(s#0)
               || (if Seq#Equal(##s#6, Seq#Empty(): Seq Box)
                   then 0
                   else $Unbox(Seq#Index(##s#6, LitInt(0))): int - ##d#7)
                 == (if Seq#Equal(s#0, Seq#Empty(): Seq Box)
                   then 0
                   else $Unbox(Seq#Index(s#0, LitInt(0))): int - d#0);
            assert (d#0 == d#0 && s#0 == s#0)
               ||
              Seq#Length(##s#6) < Seq#Length(s#0)
               || (Seq#Length(##s#6) == Seq#Length(s#0)
                 && (if Seq#Equal(##s#6, Seq#Empty(): Seq Box)
                     then 0
                     else $Unbox(Seq#Index(##s#6, LitInt(0))): int - ##d#7)
                   < (if Seq#Equal(s#0, Seq#Empty(): Seq Box)
                     then 0
                     else $Unbox(Seq#Index(s#0, LitInt(0))): int - d#0));
            assume (d#0 == d#0 && s#0 == s#0) || _module.__default.build__rec#canCall(d#0, s#0);
            assert _module.Result.Res_q(_module.__default.build__rec($LS($LZ), d#0, s#0));
            assert 0
                 <= Seq#Length(s#0)
                   - Seq#Length(_module.Result.sOut(_module.__default.build__rec($LS($LZ), d#0, s#0)))
               && Seq#Length(s#0)
                   - Seq#Length(_module.Result.sOut(_module.__default.build__rec($LS($LZ), d#0, s#0)))
                 <= Seq#Length(s#0);
            assume Seq#Equal(_module.__default.toList($LS($LZ),
                d#0,
                _module.Result.t(_module.__default.build__rec($LS($LZ), d#0, s#0))),
              Seq#Take(s#0,
                Seq#Length(s#0)
                   - Seq#Length(_module.Result.sOut(_module.__default.build__rec($LS($LZ), d#0, s#0)))));
        }
        else
        {
            assume _module.Result.Res_q(_module.__default.build__rec($LS($LZ), d#0, s#0))
               ==> Seq#Equal(_module.__default.toList($LS($LZ),
                  d#0,
                  _module.Result.t(_module.__default.build__rec($LS($LZ), d#0, s#0))),
                Seq#Take(s#0,
                  Seq#Length(s#0)
                     - Seq#Length(_module.Result.sOut(_module.__default.build__rec($LS($LZ), d#0, s#0)))));
        }

        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
          $o != null && read($Heap, $o, alloc) ==> false);
        if (!Seq#Equal(s#0, Seq#Empty(): Seq Box))
        {
            assert 0 <= LitInt(0) && LitInt(0) < Seq#Length(s#0);
        }

        if (Seq#Equal(s#0, Seq#Empty(): Seq Box)
           || $Unbox(Seq#Index(s#0, LitInt(0))): int < d#0)
        {
            assume _module.__default.build__rec($LS($LZ), d#0, s#0) == Lit(#_module.Result.Fail());
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.build__rec($LS($LZ), d#0, s#0), Tclass._module.Result());
        }
        else
        {
            assert 0 <= LitInt(0) && LitInt(0) < Seq#Length(s#0);
            if ($Unbox(Seq#Index(s#0, LitInt(0))): int == d#0)
            {
                assert 0 <= LitInt(1) && LitInt(1) <= Seq#Length(s#0);
                assume _module.__default.build__rec($LS($LZ), d#0, s#0)
                   == #_module.Result.Res(Lit(#_module.Tree.Leaf()), Seq#Drop(s#0, LitInt(1)));
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(_module.__default.build__rec($LS($LZ), d#0, s#0), Tclass._module.Result());
            }
            else
            {
                havoc left#0;
                assume $Is(left#0, Tclass._module.Result());
                ##d#8 := d#0 + 1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##d#8, TInt, $Heap);
                ##s#7 := s#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#7, TSeq(TInt), $Heap);
                b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                assert 0 <= Seq#Length(s#0) || Seq#Length(##s#7) == Seq#Length(s#0);
                assert 0
                     <= (if Seq#Equal(s#0, Seq#Empty(): Seq Box)
                       then 0
                       else $Unbox(Seq#Index(s#0, LitInt(0))): int - d#0)
                   || Seq#Length(##s#7) < Seq#Length(s#0)
                   || (if Seq#Equal(##s#7, Seq#Empty(): Seq Box)
                       then 0
                       else $Unbox(Seq#Index(##s#7, LitInt(0))): int - ##d#8)
                     == (if Seq#Equal(s#0, Seq#Empty(): Seq Box)
                       then 0
                       else $Unbox(Seq#Index(s#0, LitInt(0))): int - d#0);
                assert Seq#Length(##s#7) < Seq#Length(s#0)
                   || (Seq#Length(##s#7) == Seq#Length(s#0)
                     && (if Seq#Equal(##s#7, Seq#Empty(): Seq Box)
                         then 0
                         else $Unbox(Seq#Index(##s#7, LitInt(0))): int - ##d#8)
                       < (if Seq#Equal(s#0, Seq#Empty(): Seq Box)
                         then 0
                         else $Unbox(Seq#Index(s#0, LitInt(0))): int - d#0));
                assume _module.__default.build__rec#canCall(d#0 + 1, s#0);
                assume let#0#0#0 == _module.__default.build__rec($LS($LZ), d#0 + 1, s#0);
                assume _module.__default.build__rec#canCall(d#0 + 1, s#0);
                // CheckWellformedWithResult: any expression
                assume $Is(let#0#0#0, Tclass._module.Result());
                assume left#0 == let#0#0#0;
                if (_module.Result.Fail_q(left#0))
                {
                    assume _module.__default.build__rec($LS($LZ), d#0, s#0) == Lit(#_module.Result.Fail());
                    assume true;
                    // CheckWellformedWithResult: any expression
                    assume $Is(_module.__default.build__rec($LS($LZ), d#0, s#0), Tclass._module.Result());
                }
                else
                {
                    havoc right#0;
                    assume $Is(right#0, Tclass._module.Result());
                    assert _module.Result.Res_q(left#0);
                    ##d#9 := d#0 + 1;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##d#9, TInt, $Heap);
                    ##s#8 := _module.Result.sOut(left#0);
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##s#8, TSeq(TInt), $Heap);
                    b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                    assert 0 <= Seq#Length(s#0) || Seq#Length(##s#8) == Seq#Length(s#0);
                    assert 0
                         <= (if Seq#Equal(s#0, Seq#Empty(): Seq Box)
                           then 0
                           else $Unbox(Seq#Index(s#0, LitInt(0))): int - d#0)
                       || Seq#Length(##s#8) < Seq#Length(s#0)
                       || (if Seq#Equal(##s#8, Seq#Empty(): Seq Box)
                           then 0
                           else $Unbox(Seq#Index(##s#8, LitInt(0))): int - ##d#9)
                         == (if Seq#Equal(s#0, Seq#Empty(): Seq Box)
                           then 0
                           else $Unbox(Seq#Index(s#0, LitInt(0))): int - d#0);
                    assert Seq#Length(##s#8) < Seq#Length(s#0)
                       || (Seq#Length(##s#8) == Seq#Length(s#0)
                         && (if Seq#Equal(##s#8, Seq#Empty(): Seq Box)
                             then 0
                             else $Unbox(Seq#Index(##s#8, LitInt(0))): int - ##d#9)
                           < (if Seq#Equal(s#0, Seq#Empty(): Seq Box)
                             then 0
                             else $Unbox(Seq#Index(s#0, LitInt(0))): int - d#0));
                    assume _module.__default.build__rec#canCall(d#0 + 1, _module.Result.sOut(left#0));
                    assume let#1#0#0
                       == _module.__default.build__rec($LS($LZ), d#0 + 1, _module.Result.sOut(left#0));
                    assume _module.__default.build__rec#canCall(d#0 + 1, _module.Result.sOut(left#0));
                    // CheckWellformedWithResult: any expression
                    assume $Is(let#1#0#0, Tclass._module.Result());
                    assume right#0 == let#1#0#0;
                    if (_module.Result.Fail_q(right#0))
                    {
                        assume _module.__default.build__rec($LS($LZ), d#0, s#0) == Lit(#_module.Result.Fail());
                        assume true;
                        // CheckWellformedWithResult: any expression
                        assume $Is(_module.__default.build__rec($LS($LZ), d#0, s#0), Tclass._module.Result());
                    }
                    else
                    {
                        assert _module.Result.Res_q(left#0);
                        assert _module.Result.Res_q(right#0);
                        assert _module.Result.Res_q(right#0);
                        assume _module.__default.build__rec($LS($LZ), d#0, s#0)
                           == #_module.Result.Res(#_module.Tree.Node(_module.Result.t(left#0), _module.Result.t(right#0)),
                            _module.Result.sOut(right#0));
                        assume true;
                        // CheckWellformedWithResult: any expression
                        assume $Is(_module.__default.build__rec($LS($LZ), d#0, s#0), Tclass._module.Result());
                    }
                }
            }
        }

        assert b$reqreads#0;
        assert b$reqreads#1;
    }
}



// function declaration for _module._default.build
function _module.__default.build($ly: LayerType, s#0: Seq Box) : DatatypeType;

function _module.__default.build#canCall(s#0: Seq Box) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, s#0: Seq Box ::
  { _module.__default.build($LS($ly), s#0) }
  _module.__default.build($LS($ly), s#0) == _module.__default.build($ly, s#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, s#0: Seq Box ::
  { _module.__default.build(AsFuelBottom($ly), s#0) }
  _module.__default.build($ly, s#0) == _module.__default.build($LZ, s#0));

// consequence axiom for _module.__default.build
axiom 2 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, $Heap: Heap, s#0: Seq Box ::
    { _module.__default.build($ly, s#0), $IsGoodHeap($Heap) }
    _module.__default.build#canCall(s#0)
         || (2 != $FunctionContextHeight && $IsGoodHeap($Heap) && $Is(s#0, TSeq(TInt)))
       ==> (_module.Result.Res_q(_module.__default.build($ly, s#0))
           ==> Seq#Equal(_module.__default.toList($LS($LZ), LitInt(0), _module.Result.t(_module.__default.build($ly, s#0))),
            s#0))
         && $Is(_module.__default.build($ly, s#0), Tclass._module.Result()));

function _module.__default.build#requires(LayerType, Seq Box) : bool;

// #requires axiom for _module.__default.build
axiom (forall $ly: LayerType, $Heap: Heap, s#0: Seq Box ::
  { _module.__default.build#requires($ly, s#0), $IsGoodHeap($Heap) }
  $IsGoodHeap($Heap) && $Is(s#0, TSeq(TInt))
     ==> _module.__default.build#requires($ly, s#0) == true);

// definition axiom for _module.__default.build(revealed)
axiom 2 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, $Heap: Heap, s#0: Seq Box ::
    { _module.__default.build($LS($ly), s#0), $IsGoodHeap($Heap) }
    _module.__default.build#canCall(s#0)
         || (2 != $FunctionContextHeight && $IsGoodHeap($Heap) && $Is(s#0, TSeq(TInt)))
       ==> _module.__default.build__rec#canCall(LitInt(0), s#0)
         && _module.__default.build($LS($ly), s#0)
           == (if _module.Result.Res_q(_module.__default.build__rec($LS($LZ), LitInt(0), s#0))
               && Seq#Equal(_module.Result.sOut(_module.__default.build__rec($LS($LZ), LitInt(0), s#0)),
                Seq#Empty(): Seq Box)
             then _module.__default.build__rec($LS($LZ), LitInt(0), s#0)
             else #_module.Result.Fail()));

// definition axiom for _module.__default.build for all literals(revealed)
axiom 2 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, $Heap: Heap, s#0: Seq Box ::
    {:weight 3} { _module.__default.build($LS($ly), Lit(s#0)), $IsGoodHeap($Heap) }
    _module.__default.build#canCall(Lit(s#0))
         || (2 != $FunctionContextHeight && $IsGoodHeap($Heap) && $Is(s#0, TSeq(TInt)))
       ==> _module.__default.build__rec#canCall(LitInt(0), Lit(s#0))
         && _module.__default.build($LS($ly), Lit(s#0))
           == (if _module.Result.Res_q(Lit(_module.__default.build__rec($LS($LZ), LitInt(0), Lit(s#0))))
               && Seq#Equal(_module.Result.sOut(Lit(_module.__default.build__rec($LS($LZ), LitInt(0), Lit(s#0)))),
                Seq#Empty(): Seq Box)
             then _module.__default.build__rec($LS($LZ), LitInt(0), Lit(s#0))
             else #_module.Result.Fail()));

procedure CheckWellformed$$_module.__default.build(s#0: Seq Box where $Is(s#0, TSeq(TInt)));
  free requires 2 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  ensures _module.Result.Res_q(_module.__default.build($LS($LZ), s#0))
     ==> Seq#Equal(_module.__default.toList($LS($LS($LZ)),
        LitInt(0),
        _module.Result.t(_module.__default.build($LS($LS($LZ)), s#0))),
      s#0);



implementation CheckWellformed$$_module.__default.build(s#0: Seq Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##s#0: Seq Box;
  var ##s#1: Seq Box;
  var ##d#0: int;
  var ##t#0: DatatypeType;
  var r#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var ##d#1: int;
  var ##s#2: Seq Box;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function build
    assume {:captureState "Tree.dfy(70,16): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.build($LS($LZ), s#0), Tclass._module.Result());
        if (*)
        {
            ##s#0 := s#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#0, TSeq(TInt), $Heap);
            assert s#0 == s#0 || Seq#Rank(##s#0) < Seq#Rank(s#0);
            assume s#0 == s#0 || _module.__default.build#canCall(s#0);
            assume _module.Result.Res_q(_module.__default.build($LS($LZ), s#0));
            ##s#1 := s#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#1, TSeq(TInt), $Heap);
            assert s#0 == s#0 || Seq#Rank(##s#1) < Seq#Rank(s#0);
            assume s#0 == s#0 || _module.__default.build#canCall(s#0);
            assert _module.Result.Res_q(_module.__default.build($LS($LZ), s#0));
            ##d#0 := LitInt(0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##d#0, TInt, $Heap);
            ##t#0 := _module.Result.t(_module.__default.build($LS($LZ), s#0));
            // assume allocatedness for argument to function
            assume $IsAlloc(##t#0, Tclass._module.Tree(), $Heap);
            assume _module.__default.toList#canCall(LitInt(0), _module.Result.t(_module.__default.build($LS($LZ), s#0)));
            assume Seq#Equal(_module.__default.toList($LS($LZ), LitInt(0), _module.Result.t(_module.__default.build($LS($LZ), s#0))),
              s#0);
        }
        else
        {
            assume _module.Result.Res_q(_module.__default.build($LS($LZ), s#0))
               ==> Seq#Equal(_module.__default.toList($LS($LZ), LitInt(0), _module.Result.t(_module.__default.build($LS($LZ), s#0))),
                s#0);
        }

        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
          $o != null && read($Heap, $o, alloc) ==> false);
        havoc r#0;
        assume $Is(r#0, Tclass._module.Result());
        ##d#1 := LitInt(0);
        // assume allocatedness for argument to function
        assume $IsAlloc(##d#1, TInt, $Heap);
        ##s#2 := s#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##s#2, TSeq(TInt), $Heap);
        b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume _module.__default.build__rec#canCall(LitInt(0), s#0);
        assume let#0#0#0 == _module.__default.build__rec($LS($LZ), LitInt(0), s#0);
        assume _module.__default.build__rec#canCall(LitInt(0), s#0);
        // CheckWellformedWithResult: any expression
        assume $Is(let#0#0#0, Tclass._module.Result());
        assume r#0 == let#0#0#0;
        if (_module.Result.Res_q(r#0))
        {
            assert _module.Result.Res_q(r#0);
        }

        if (_module.Result.Res_q(r#0)
           && Seq#Equal(_module.Result.sOut(r#0), Seq#Empty(): Seq Box))
        {
            assume _module.__default.build($LS($LZ), s#0) == r#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.build($LS($LZ), s#0), Tclass._module.Result());
        }
        else
        {
            assume _module.__default.build($LS($LZ), s#0) == Lit(#_module.Result.Fail());
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.build($LS($LZ), s#0), Tclass._module.Result());
        }

        assert b$reqreads#0;
    }
}



procedure {:_induction t#0, d#0, s#0} CheckWellformed$$_module.__default.lemma0(t#0: DatatypeType
       where $Is(t#0, Tclass._module.Tree())
         && $IsAlloc(t#0, Tclass._module.Tree(), $Heap)
         && $IsA#_module.Tree(t#0),
    d#0: int,
    s#0: Seq Box where $Is(s#0, TSeq(TInt)) && $IsAlloc(s#0, TSeq(TInt), $Heap));
  free requires 3 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:_induction t#0, d#0, s#0} CheckWellformed$$_module.__default.lemma0(t#0: DatatypeType, d#0: int, s#0: Seq Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##d#0: int;
  var ##t#0: DatatypeType;
  var ##d#1: int;
  var ##s#0: Seq Box;
  var ##d#2: int;
  var ##t#1: DatatypeType;
  var ##d#3: int;
  var ##s#1: Seq Box;

    // AddMethodImpl: lemma0, CheckWellformed$$_module.__default.lemma0
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "Tree.dfy(87,6): initial state"} true;
    havoc $Heap;
    assume old($Heap) == $Heap;
    assume {:captureState "Tree.dfy(88,46): post-state"} true;
    ##d#0 := d#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##d#0, TInt, $Heap);
    ##t#0 := t#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##t#0, Tclass._module.Tree(), $Heap);
    assume _module.__default.toList#canCall(d#0, t#0);
    ##d#1 := d#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##d#1, TInt, $Heap);
    ##s#0 := Seq#Append(_module.__default.toList($LS($LZ), d#0, t#0), s#0);
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#0, TSeq(TInt), $Heap);
    assume _module.__default.build__rec#canCall(d#0, Seq#Append(_module.__default.toList($LS($LZ), d#0, t#0), s#0));
    assume _module.Result.Res_q(_module.__default.build__rec($LS($LZ), d#0, Seq#Append(_module.__default.toList($LS($LZ), d#0, t#0), s#0)));
    ##d#2 := d#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##d#2, TInt, $Heap);
    ##t#1 := t#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##t#1, Tclass._module.Tree(), $Heap);
    assume _module.__default.toList#canCall(d#0, t#0);
    ##d#3 := d#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##d#3, TInt, $Heap);
    ##s#1 := Seq#Append(_module.__default.toList($LS($LZ), d#0, t#0), s#0);
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#1, TSeq(TInt), $Heap);
    assume _module.__default.build__rec#canCall(d#0, Seq#Append(_module.__default.toList($LS($LZ), d#0, t#0), s#0));
    assert _module.Result.Res_q(_module.__default.build__rec($LS($LZ), d#0, Seq#Append(_module.__default.toList($LS($LZ), d#0, t#0), s#0)));
    assume Seq#Equal(_module.Result.sOut(_module.__default.build__rec($LS($LZ), d#0, Seq#Append(_module.__default.toList($LS($LZ), d#0, t#0), s#0))),
      s#0);
}



procedure {:_induction t#0, d#0, s#0} Call$$_module.__default.lemma0(t#0: DatatypeType
       where $Is(t#0, Tclass._module.Tree())
         && $IsAlloc(t#0, Tclass._module.Tree(), $Heap)
         && $IsA#_module.Tree(t#0),
    d#0: int,
    s#0: Seq Box where $Is(s#0, TSeq(TInt)) && $IsAlloc(s#0, TSeq(TInt), $Heap));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.toList#canCall(d#0, t#0)
     && _module.__default.build__rec#canCall(d#0, Seq#Append(_module.__default.toList($LS($LZ), d#0, t#0), s#0))
     && (_module.Result.Res_q(_module.__default.build__rec($LS($LZ), d#0, Seq#Append(_module.__default.toList($LS($LZ), d#0, t#0), s#0)))
       ==> _module.__default.toList#canCall(d#0, t#0)
         && _module.__default.build__rec#canCall(d#0, Seq#Append(_module.__default.toList($LS($LZ), d#0, t#0), s#0)));
  ensures _module.Result.Res_q(_module.__default.build__rec($LS($LS($LZ)),
      d#0,
      Seq#Append(_module.__default.toList($LS($LS($LZ)), d#0, t#0), s#0)));
  ensures Seq#Equal(_module.Result.sOut(_module.__default.build__rec($LS($LS($LZ)),
        d#0,
        Seq#Append(_module.__default.toList($LS($LS($LZ)), d#0, t#0), s#0))),
    s#0);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction t#0, d#0, s#0} Impl$$_module.__default.lemma0(t#0: DatatypeType
       where $Is(t#0, Tclass._module.Tree())
         && $IsAlloc(t#0, Tclass._module.Tree(), $Heap)
         && $IsA#_module.Tree(t#0),
    d#0: int,
    s#0: Seq Box where $Is(s#0, TSeq(TInt)) && $IsAlloc(s#0, TSeq(TInt), $Heap))
   returns ($_reverifyPost: bool);
  free requires 3 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.toList#canCall(d#0, t#0)
     && _module.__default.build__rec#canCall(d#0, Seq#Append(_module.__default.toList($LS($LZ), d#0, t#0), s#0))
     && (_module.Result.Res_q(_module.__default.build__rec($LS($LZ), d#0, Seq#Append(_module.__default.toList($LS($LZ), d#0, t#0), s#0)))
       ==> _module.__default.toList#canCall(d#0, t#0)
         && _module.__default.build__rec#canCall(d#0, Seq#Append(_module.__default.toList($LS($LZ), d#0, t#0), s#0)));
  ensures _module.Result.Res_q(_module.__default.build__rec($LS($LS($LZ)),
      d#0,
      Seq#Append(_module.__default.toList($LS($LS($LZ)), d#0, t#0), s#0)));
  ensures Seq#Equal(_module.Result.sOut(_module.__default.build__rec($LS($LS($LZ)),
        d#0,
        Seq#Append(_module.__default.toList($LS($LS($LZ)), d#0, t#0), s#0))),
    s#0);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction t#0, d#0, s#0} Impl$$_module.__default.lemma0(t#0: DatatypeType, d#0: int, s#0: Seq Box) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var l#0_0: DatatypeType;
  var r#0_0: DatatypeType;
  var ##d#0_0: int;
  var ##t#0_0: DatatypeType;
  var ##d#0_1: int;
  var ##t#0_1: DatatypeType;
  var ##d#0_2: int;
  var ##t#0_2: DatatypeType;
  var ##d#1_0: int;
  var ##t#1_0: DatatypeType;

    // AddMethodImpl: lemma0, Impl$$_module.__default.lemma0
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "Tree.dfy(90,0): initial state"} true;
    assume $IsA#_module.Tree(t#0);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#t0#0: DatatypeType, $ih#d0#0: int, $ih#s0#0: Seq Box ::
      $Is($ih#t0#0, Tclass._module.Tree())
           && $Is($ih#s0#0, TSeq(TInt))
           && Lit(true)
           && (DtRank($ih#t0#0) < DtRank(t#0)
             || (DtRank($ih#t0#0) == DtRank(t#0)
               && ((0 <= $ih#d0#0 && $ih#d0#0 < d#0)
                 || ($ih#d0#0 == d#0 && Seq#Rank($ih#s0#0) < Seq#Rank(s#0)))))
         ==> _module.Result.Res_q(_module.__default.build__rec($LS($LZ),
              $ih#d0#0,
              Seq#Append(_module.__default.toList($LS($LZ), $ih#d0#0, $ih#t0#0), $ih#s0#0)))
           && Seq#Equal(_module.Result.sOut(_module.__default.build__rec($LS($LZ),
                $ih#d0#0,
                Seq#Append(_module.__default.toList($LS($LZ), $ih#d0#0, $ih#t0#0), $ih#s0#0))),
            $ih#s0#0));
    $_reverifyPost := false;
    assume true;
    havoc l#0_0, r#0_0;
    if (t#0 == #_module.Tree.Leaf())
    {
        // ----- assert statement ----- Tree.dfy(93,5)
        ##d#1_0 := d#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##d#1_0, TInt, $Heap);
        ##t#1_0 := t#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##t#1_0, Tclass._module.Tree(), $Heap);
        assume _module.__default.toList#canCall(d#0, t#0);
        assume _module.__default.toList#canCall(d#0, t#0);
        assert {:subsumption 0} Seq#Equal(_module.__default.toList($LS($LS($LZ)), d#0, t#0),
          Seq#Build(Seq#Empty(): Seq Box, $Box(d#0)));
        assume Seq#Equal(_module.__default.toList($LS($LZ), d#0, t#0),
          Seq#Build(Seq#Empty(): Seq Box, $Box(d#0)));
    }
    else if (t#0 == #_module.Tree.Node(l#0_0, r#0_0))
    {
        assume $Is(l#0_0, Tclass._module.Tree());
        assume $Is(r#0_0, Tclass._module.Tree());
        // ----- assert statement ----- Tree.dfy(95,5)
        ##d#0_0 := d#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##d#0_0, TInt, $Heap);
        ##t#0_0 := t#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##t#0_0, Tclass._module.Tree(), $Heap);
        assume _module.__default.toList#canCall(d#0, t#0);
        ##d#0_1 := d#0 + 1;
        // assume allocatedness for argument to function
        assume $IsAlloc(##d#0_1, TInt, $Heap);
        ##t#0_1 := l#0_0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##t#0_1, Tclass._module.Tree(), $Heap);
        assume _module.__default.toList#canCall(d#0 + 1, l#0_0);
        ##d#0_2 := d#0 + 1;
        // assume allocatedness for argument to function
        assume $IsAlloc(##d#0_2, TInt, $Heap);
        ##t#0_2 := r#0_0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##t#0_2, Tclass._module.Tree(), $Heap);
        assume _module.__default.toList#canCall(d#0 + 1, r#0_0);
        assume _module.__default.toList#canCall(d#0, t#0)
           &&
          _module.__default.toList#canCall(d#0 + 1, l#0_0)
           && _module.__default.toList#canCall(d#0 + 1, r#0_0);
        assert {:subsumption 0} Seq#Equal(Seq#Append(_module.__default.toList($LS($LS($LZ)), d#0, t#0), s#0),
          Seq#Append(_module.__default.toList($LS($LS($LZ)), d#0 + 1, l#0_0),
            Seq#Append(_module.__default.toList($LS($LS($LZ)), d#0 + 1, r#0_0), s#0)));
        assume Seq#Equal(Seq#Append(_module.__default.toList($LS($LZ), d#0, t#0), s#0),
          Seq#Append(_module.__default.toList($LS($LZ), d#0 + 1, l#0_0),
            Seq#Append(_module.__default.toList($LS($LZ), d#0 + 1, r#0_0), s#0)));
    }
    else
    {
        assume false;
    }
}



procedure {:_induction t#0, s#0} CheckWellformed$$_module.__default.lemma1(t#0: DatatypeType
       where $Is(t#0, Tclass._module.Tree())
         && $IsAlloc(t#0, Tclass._module.Tree(), $Heap)
         && $IsA#_module.Tree(t#0),
    s#0: Seq Box where $Is(s#0, TSeq(TInt)) && $IsAlloc(s#0, TSeq(TInt), $Heap));
  free requires 4 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:_induction t#0, s#0} Call$$_module.__default.lemma1(t#0: DatatypeType
       where $Is(t#0, Tclass._module.Tree())
         && $IsAlloc(t#0, Tclass._module.Tree(), $Heap)
         && $IsA#_module.Tree(t#0),
    s#0: Seq Box where $Is(s#0, TSeq(TInt)) && $IsAlloc(s#0, TSeq(TInt), $Heap));
  // user-defined preconditions
  requires Seq#Equal(s#0,
    Seq#Append(_module.__default.toList($LS($LS($LZ)), LitInt(0), t#0), Seq#Empty(): Seq Box));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.build#canCall(s#0);
  ensures _module.Result.Res_q(_module.__default.build($LS($LS($LZ)), s#0));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction t#0, s#0} Impl$$_module.__default.lemma1(t#0: DatatypeType
       where $Is(t#0, Tclass._module.Tree())
         && $IsAlloc(t#0, Tclass._module.Tree(), $Heap)
         && $IsA#_module.Tree(t#0),
    s#0: Seq Box where $Is(s#0, TSeq(TInt)) && $IsAlloc(s#0, TSeq(TInt), $Heap))
   returns ($_reverifyPost: bool);
  free requires 4 == $FunctionContextHeight;
  // user-defined preconditions
  requires Seq#Equal(s#0,
    Seq#Append(_module.__default.toList($LS($LS($LZ)), LitInt(0), t#0), Seq#Empty(): Seq Box));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.build#canCall(s#0);
  ensures _module.Result.Res_q(_module.__default.build($LS($LS($LZ)), s#0));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction t#0, s#0} Impl$$_module.__default.lemma1(t#0: DatatypeType, s#0: Seq Box) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var t##0: DatatypeType;
  var d##0: int;
  var s##0: Seq Box;

    // AddMethodImpl: lemma1, Impl$$_module.__default.lemma1
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "Tree.dfy(110,0): initial state"} true;
    assume $IsA#_module.Tree(t#0);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#t0#0: DatatypeType, $ih#s0#0: Seq Box ::
      $Is($ih#t0#0, Tclass._module.Tree())
           && $Is($ih#s0#0, TSeq(TInt))
           && Seq#Equal($ih#s0#0,
            Seq#Append(_module.__default.toList($LS($LZ), LitInt(0), $ih#t0#0), Seq#Empty(): Seq Box))
           && (DtRank($ih#t0#0) < DtRank(t#0)
             || (DtRank($ih#t0#0) == DtRank(t#0) && Seq#Rank($ih#s0#0) < Seq#Rank(s#0)))
         ==> _module.Result.Res_q(_module.__default.build($LS($LZ), $ih#s0#0)));
    $_reverifyPost := false;
    // ----- call statement ----- Tree.dfy(111,9)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    t##0 := t#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    d##0 := LitInt(0);
    assume true;
    // ProcessCallStmt: CheckSubrange
    s##0 := Lit(Seq#Empty(): Seq Box);
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.lemma0(t##0, d##0, s##0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "Tree.dfy(111,18)"} true;
}



procedure {:_induction s#0} CheckWellformed$$_module.__default.lemma2(s#0: Seq Box where $Is(s#0, TSeq(TInt)) && $IsAlloc(s#0, TSeq(TInt), $Heap));
  free requires 5 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:_induction s#0} Call$$_module.__default.lemma2(s#0: Seq Box where $Is(s#0, TSeq(TInt)) && $IsAlloc(s#0, TSeq(TInt), $Heap));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall t#1: DatatypeType ::
      { _module.__default.toList($LS($LZ), 0, t#1) }
      $Is(t#1, Tclass._module.Tree())
         ==> _module.__default.toList#canCall(LitInt(0), t#1))
     && ((exists t#1: DatatypeType ::
        {:_induction t#1} { _module.__default.toList($LS($LZ), 0, t#1) }
        $Is(t#1, Tclass._module.Tree())
           && Seq#Equal(_module.__default.toList($LS($LZ), LitInt(0), t#1), s#0))
       ==> _module.__default.build#canCall(s#0));
  ensures (exists t#1: DatatypeType ::
      {:_induction t#1} { _module.__default.toList($LS($LZ), 0, t#1) }
      $Is(t#1, Tclass._module.Tree())
         && Seq#Equal(_module.__default.toList($LS($LZ), LitInt(0), t#1), s#0))
     ==> _module.Result.Res_q(_module.__default.build($LS($LS($LZ)), s#0));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction s#0} Impl$$_module.__default.lemma2(s#0: Seq Box where $Is(s#0, TSeq(TInt)) && $IsAlloc(s#0, TSeq(TInt), $Heap))
   returns ($_reverifyPost: bool);
  free requires 5 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall t#1: DatatypeType ::
      { _module.__default.toList($LS($LZ), 0, t#1) }
      $Is(t#1, Tclass._module.Tree())
         ==> _module.__default.toList#canCall(LitInt(0), t#1))
     && ((exists t#1: DatatypeType ::
        {:_induction t#1} { _module.__default.toList($LS($LZ), 0, t#1) }
        $Is(t#1, Tclass._module.Tree())
           && Seq#Equal(_module.__default.toList($LS($LZ), LitInt(0), t#1), s#0))
       ==> _module.__default.build#canCall(s#0));
  ensures (exists t#1: DatatypeType ::
      {:_induction t#1} { _module.__default.toList($LS($LZ), 0, t#1) }
      $Is(t#1, Tclass._module.Tree())
         && Seq#Equal(_module.__default.toList($LS($LZ), LitInt(0), t#1), s#0))
     ==> _module.Result.Res_q(_module.__default.build($LS($LS($LZ)), s#0));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction s#0} Impl$$_module.__default.lemma2(s#0: Seq Box) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var t#3: DatatypeType;
  var ##d#1: int;
  var ##t#1: DatatypeType;
  var t##0: DatatypeType;
  var s##0: Seq Box;
  var $initHeapForallStmt#1: Heap;

    // AddMethodImpl: lemma2, Impl$$_module.__default.lemma2
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "Tree.dfy(119,0): initial state"} true;
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#s0#0: Seq Box ::
      $Is($ih#s0#0, TSeq(TInt)) && Lit(true) && Seq#Rank($ih#s0#0) < Seq#Rank(s#0)
         ==>
        (exists t#2: DatatypeType ::
          {:_induction t#2} { _module.__default.toList($LS($LZ), 0, t#2) }
          $Is(t#2, Tclass._module.Tree())
             && Seq#Equal(_module.__default.toList($LS($LZ), LitInt(0), t#2), $ih#s0#0))
         ==> _module.Result.Res_q(_module.__default.build($LS($LZ), $ih#s0#0)));
    $_reverifyPost := false;
    // ----- forall statement (call) ----- Tree.dfy(120,3)
    if (*)
    {
        // Assume Fuel Constant
        havoc t#3;
        assume $Is(t#3, Tclass._module.Tree());
        ##d#1 := LitInt(0);
        // assume allocatedness for argument to function
        assume $IsAlloc(##d#1, TInt, $Heap);
        ##t#1 := t#3;
        // assume allocatedness for argument to function
        assume $IsAlloc(##t#1, Tclass._module.Tree(), $Heap);
        assume _module.__default.toList#canCall(LitInt(0), t#3);
        assume _module.__default.toList#canCall(LitInt(0), t#3);
        assume Seq#Equal(_module.__default.toList($LS($LZ), LitInt(0), t#3), s#0);
        // ----- call statement ----- Tree.dfy(121,11)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        t##0 := t#3;
        assume true;
        // ProcessCallStmt: CheckSubrange
        s##0 := s#0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$_module.__default.lemma1(t##0, s##0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "Tree.dfy(121,16)"} true;
        assume false;
    }
    else
    {
        $initHeapForallStmt#1 := $Heap;
        havoc $Heap, $Tick;
        assume $initHeapForallStmt#1 == $Heap;
        assume (forall t#4: DatatypeType ::
          { _module.__default.toList($LS($LZ), 0, t#4) }
          $Is(t#4, Tclass._module.Tree())
               && Seq#Equal(_module.__default.toList($LS($LZ), LitInt(0), t#4), s#0)
             ==> _module.Result.Res_q(_module.__default.build($LS($LZ), s#0)));
    }

    assume {:captureState "Tree.dfy(122,2)"} true;
}



procedure CheckWellformed$$_module.__default.completeness();
  free requires 6 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.completeness();
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall s#1: Seq Box ::
    { _module.__default.build($LS($LZ), s#1) }
    $Is(s#1, TSeq(TInt))
       ==> (forall t#2: DatatypeType ::
          { _module.__default.toList($LS($LZ), 0, t#2) }
          $Is(t#2, Tclass._module.Tree())
             ==> _module.__default.toList#canCall(LitInt(0), t#2))
         && ((exists t#2: DatatypeType ::
            {:_induction t#2} { _module.__default.toList($LS($LZ), 0, t#2) }
            $Is(t#2, Tclass._module.Tree())
               && Seq#Equal(_module.__default.toList($LS($LZ), LitInt(0), t#2), s#1))
           ==> _module.__default.build#canCall(s#1)));
  free ensures (forall s#1: Seq Box ::
    {:_induction s#1} { _module.__default.build($LS($LZ), s#1) }
    $Is(s#1, TSeq(TInt))
       ==>
      (exists t#2: DatatypeType ::
        {:_induction t#2} { _module.__default.toList($LS($LZ), 0, t#2) }
        $Is(t#2, Tclass._module.Tree())
           && Seq#Equal(_module.__default.toList($LS($LZ), LitInt(0), t#2), s#1))
       ==> _module.Result.Res_q(_module.__default.build($LS($LZ), s#1)));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.completeness() returns ($_reverifyPost: bool);
  free requires 6 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall s#1: Seq Box ::
    { _module.__default.build($LS($LZ), s#1) }
    $Is(s#1, TSeq(TInt))
       ==> (forall t#2: DatatypeType ::
          { _module.__default.toList($LS($LZ), 0, t#2) }
          $Is(t#2, Tclass._module.Tree())
             ==> _module.__default.toList#canCall(LitInt(0), t#2))
         && ((exists t#2: DatatypeType ::
            {:_induction t#2} { _module.__default.toList($LS($LZ), 0, t#2) }
            $Is(t#2, Tclass._module.Tree())
               && Seq#Equal(_module.__default.toList($LS($LZ), LitInt(0), t#2), s#1))
           ==> _module.__default.build#canCall(s#1)));
  ensures (forall s#1: Seq Box ::
    { _module.__default.build($LS($LS($LZ)), s#1) }
    $Is(s#1, TSeq(TInt))
         && (forall s$ih#1#0: Seq Box ::
          { _module.__default.build($LS($LZ), s$ih#1#0) }
          $Is(s$ih#1#0, TSeq(TInt))
             ==>
            Seq#Rank(s$ih#1#0) < Seq#Rank(s#1)
             ==>
            (exists t#4: DatatypeType ::
              {:_induction t#4} { _module.__default.toList($LS($LZ), 0, t#4) }
              $Is(t#4, Tclass._module.Tree())
                 && Seq#Equal(_module.__default.toList($LS($LZ), LitInt(0), t#4), s$ih#1#0))
             ==> _module.Result.Res_q(_module.__default.build($LS($LZ), s$ih#1#0)))
         && true
       ==>
      (exists t#2: DatatypeType ::
        {:_induction t#2} { _module.__default.toList($LS($LS($LZ)), 0, t#2) }
        $Is(t#2, Tclass._module.Tree())
           && Seq#Equal(_module.__default.toList($LS($LS($LZ)), LitInt(0), t#2), s#1))
       ==> _module.Result.Res_q(_module.__default.build($LS($LS($LZ)), s#1)));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.completeness() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var s#2: Seq Box;
  var s##0: Seq Box;
  var $initHeapForallStmt#0: Heap;

    // AddMethodImpl: completeness, Impl$$_module.__default.completeness
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "Tree.dfy(133,0): initial state"} true;
    $_reverifyPost := false;
    // ----- forall statement (call) ----- Tree.dfy(134,3)
    if (*)
    {
        // Assume Fuel Constant
        havoc s#2;
        assume $Is(s#2, TSeq(TInt));
        assume true;
        assume true;
        // ----- call statement ----- Tree.dfy(135,11)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        s##0 := s#2;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$_module.__default.lemma2(s##0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "Tree.dfy(135,13)"} true;
        assume false;
    }
    else
    {
        $initHeapForallStmt#0 := $Heap;
        havoc $Heap, $Tick;
        assume $initHeapForallStmt#0 == $Heap;
        assume (forall s#3: Seq Box ::
          { _module.__default.build($LS($LZ), s#3) }
          $Is(s#3, TSeq(TInt)) && Lit(true)
             ==>
            (exists t#5: DatatypeType ::
              {:_induction t#5} { _module.__default.toList($LS($LZ), 0, t#5) }
              $Is(t#5, Tclass._module.Tree())
                 && Seq#Equal(_module.__default.toList($LS($LZ), LitInt(0), t#5), s#3))
             ==> _module.Result.Res_q(_module.__default.build($LS($LZ), s#3)));
    }

    assume {:captureState "Tree.dfy(136,2)"} true;
}



procedure CheckWellformed$$_module.__default.harness0();
  free requires 7 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.harness0()
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##s#0: Seq Box;
  var ##s#1: Seq Box;

    // AddMethodImpl: harness0, CheckWellformed$$_module.__default.harness0
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "Tree.dfy(144,7): initial state"} true;
    havoc $Heap;
    assume (forall<alpha> $o: ref, $f: Field alpha ::
      { read($Heap, $o, $f) }
      $o != null && read(old($Heap), $o, alloc)
         ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
    assume $HeapSucc(old($Heap), $Heap);
    assume {:captureState "Tree.dfy(145,32): post-state"} true;
    ##s#0 := Lit(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(1))), $Box(LitInt(3))),
          $Box(LitInt(3))),
        $Box(LitInt(2))));
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#0, TSeq(TInt), $Heap);
    assume _module.__default.build#canCall(Lit(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(1))), $Box(LitInt(3))),
            $Box(LitInt(3))),
          $Box(LitInt(2)))));
    assume _module.Result.Res_q(Lit(_module.__default.build($LS($LZ),
          Lit(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(1))), $Box(LitInt(3))),
                $Box(LitInt(3))),
              $Box(LitInt(2)))))));
    ##s#1 := Lit(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(1))), $Box(LitInt(3))),
          $Box(LitInt(3))),
        $Box(LitInt(2))));
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#1, TSeq(TInt), $Heap);
    assume _module.__default.build#canCall(Lit(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(1))), $Box(LitInt(3))),
            $Box(LitInt(3))),
          $Box(LitInt(2)))));
    assert _module.Result.Res_q(Lit(_module.__default.build($LS($LZ),
          Lit(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(1))), $Box(LitInt(3))),
                $Box(LitInt(3))),
              $Box(LitInt(2)))))));
    assume Lit(_module.Result.t(Lit(_module.__default.build($LS($LZ),
              Lit(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(1))), $Box(LitInt(3))),
                    $Box(LitInt(3))),
                  $Box(LitInt(2))))))))
       == Lit(#_module.Tree.Node(Lit(#_module.Tree.Leaf()),
          Lit(#_module.Tree.Node(Lit(#_module.Tree.Node(Lit(#_module.Tree.Leaf()), Lit(#_module.Tree.Leaf()))),
              Lit(#_module.Tree.Leaf())))));
}



procedure Call$$_module.__default.harness0();
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.build#canCall(Lit(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(1))), $Box(LitInt(3))),
            $Box(LitInt(3))),
          $Box(LitInt(2)))))
     && (Lit(_module.Result.Res_q(Lit(_module.__default.build($LS($LZ),
              Lit(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(1))), $Box(LitInt(3))),
                    $Box(LitInt(3))),
                  $Box(LitInt(2))))))))
       ==> _module.__default.build#canCall(Lit(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(1))), $Box(LitInt(3))),
              $Box(LitInt(3))),
            $Box(LitInt(2))))));
  ensures Lit(_module.Result.Res_q(Lit(_module.__default.build($LS($LS($LZ)),
          Lit(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(1))), $Box(LitInt(3))),
                $Box(LitInt(3))),
              $Box(LitInt(2))))))));
  ensures Lit(_module.Result.t(Lit(_module.__default.build($LS($LS($LZ)),
            Lit(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(1))), $Box(LitInt(3))),
                  $Box(LitInt(3))),
                $Box(LitInt(2))))))))
     == Lit(#_module.Tree.Node(Lit(#_module.Tree.Leaf()),
        Lit(#_module.Tree.Node(Lit(#_module.Tree.Node(Lit(#_module.Tree.Leaf()), Lit(#_module.Tree.Leaf()))),
            Lit(#_module.Tree.Leaf())))));
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.harness0() returns ($_reverifyPost: bool);
  free requires 7 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.build#canCall(Lit(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(1))), $Box(LitInt(3))),
            $Box(LitInt(3))),
          $Box(LitInt(2)))))
     && (Lit(_module.Result.Res_q(Lit(_module.__default.build($LS($LZ),
              Lit(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(1))), $Box(LitInt(3))),
                    $Box(LitInt(3))),
                  $Box(LitInt(2))))))))
       ==> _module.__default.build#canCall(Lit(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(1))), $Box(LitInt(3))),
              $Box(LitInt(3))),
            $Box(LitInt(2))))));
  ensures Lit(_module.Result.Res_q(Lit(_module.__default.build($LS($LS($LZ)),
          Lit(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(1))), $Box(LitInt(3))),
                $Box(LitInt(3))),
              $Box(LitInt(2))))))));
  ensures Lit(_module.Result.t(Lit(_module.__default.build($LS($LS($LZ)),
            Lit(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(1))), $Box(LitInt(3))),
                  $Box(LitInt(3))),
                $Box(LitInt(2))))))))
     == Lit(#_module.Tree.Node(Lit(#_module.Tree.Leaf()),
        Lit(#_module.Tree.Node(Lit(#_module.Tree.Node(Lit(#_module.Tree.Leaf()), Lit(#_module.Tree.Leaf()))),
            Lit(#_module.Tree.Leaf())))));
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.harness0() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: harness0, Impl$$_module.__default.harness0
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "Tree.dfy(147,0): initial state"} true;
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.__default.harness1();
  free requires 8 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.harness1();
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.build#canCall(Lit(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(1))), $Box(LitInt(3))),
          $Box(LitInt(2))),
        $Box(LitInt(2)))));
  ensures Lit(_module.Result.Fail_q(Lit(_module.__default.build($LS($LS($LZ)),
          Lit(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(1))), $Box(LitInt(3))),
                $Box(LitInt(2))),
              $Box(LitInt(2))))))));
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.harness1() returns ($_reverifyPost: bool);
  free requires 8 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.build#canCall(Lit(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(1))), $Box(LitInt(3))),
          $Box(LitInt(2))),
        $Box(LitInt(2)))));
  ensures Lit(_module.Result.Fail_q(Lit(_module.__default.build($LS($LS($LZ)),
          Lit(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(1))), $Box(LitInt(3))),
                $Box(LitInt(2))),
              $Box(LitInt(2))))))));
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha ::
    { read($Heap, $o, $f) }
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.harness1() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: harness1, Impl$$_module.__default.harness1
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha ::
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "Tree.dfy(157,0): initial state"} true;
    $_reverifyPost := false;
}

