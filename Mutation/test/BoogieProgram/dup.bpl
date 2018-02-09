const a: [int] int;

// const a: [int] int;

// const a: [int] int;

// const a: [int] int;

// const a: [int] int;

// const a: [int] int;

const ab: int;

var jef: int;

type myType = int;

function hash(int) returns (int);

axiom (forall x: int, y: int :: x > y ==> hash(x) > y);

axiom (forall j: int, k: int :: {a[k], a[j]} 0 <= j && j < k ==> a[j] < a[k]);

procedure harray(i: int, jef: int) returns (o: int);
    requires i >= 0;
    ensures o > a[i];
    requires (forall x: int, y: int :: x > y ==> hash(x) > y);
    requires (forall x: int, y: int :: x > y ==> hash(x) > y);

implementation harray(i: int, jef: int) returns (o: int)
{
    o := hash(a[i + 1]);
}
