type Field _;
type Set T = [T] bool;
type Box;

const a : [int]int;

function sort ([int]int) returns ([int]int);
axiom (forall x, y : int :: {a[x], a[y]}  sort(a) == sort(a));

function LitInt(int) returns (int);
axiom (forall x: int :: {:identity} { LitInt(x): int } LitInt(x): int == x);


procedure $IterCollectNewObjects(NW: Field (Set (Box))) returns (s: Set (Box));
 ensures true; 
