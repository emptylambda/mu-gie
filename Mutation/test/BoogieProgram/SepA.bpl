axiom (forall j, k : int ::
         0 <= j && j < k ==> a[j] < a[k]);

procedure harray (i: int) returns (o: int)
  requires i >= 0;
	ensures o > a[i];
{
  o := hash(a[i+1]); 
}				
