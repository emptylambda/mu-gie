/*
SOURCE  : ./test/BoogieProgram/sandbox.bpl
MUChain : [L4,L6]
*/
const a: [int] int;

const d: int;

axiom d > 0;

axiom (forall j: int, k: int :: {a[j], a[k]} 0 <= j && j < k ==> a[j] < a[k]);

function hash(int) returns (int);

axiom (forall x: int, y: int :: x > y ==> hash(x) > y);

procedure hash_array(k: int) returns (h: int)
    ensures h > a[k];
    requires 0 <= k && true;
{
    var x: int, phi: int, shi: int;
    var y: int;
    var z: int;
    h := hash(a[k + 1]);
}
