const a: [int] int;

// axiom (forall i : int :: {a[i]} {:weight 0}		
//          0 <= i ==> a[i] < a [i+1] );


function hash(int) returns (int);
axiom (forall x, y :int ::
         x > y ==> hash(x) > y); 

// (strict inc.) sortedness
// if you know how to boogie-woogie
