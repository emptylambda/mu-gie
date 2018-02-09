const a: [int] int;

// axiom (forall i : int :: {a[i]} {:weight 0}		
//          0 <= i ==> a[i] < a [i+1] );


function hash(int) returns (int);
axiom (forall x, y :int ::
         x > y ==> hash(x) > y); 

// (strict inc.) sortedness
// if you know how to boogie-woogie
axiom (forall j, k : int :: {a[j], a[k]} {a[j], a[k]}
         0 <= j && j < k ==> a[j] < a[k]);

procedure harray (i: int) returns (o: int)
  requires i >= 0;
	ensures o > a[i];
{
  o := hash(a[i+1]);
}				
