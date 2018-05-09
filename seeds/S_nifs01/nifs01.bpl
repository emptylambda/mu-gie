
const bar: int;
procedure main() returns ()
{
  var pos, neg, i: int;
  pos, neg, i :=  0, 0, 0;
if (i >= bar) {
   pos, i := pos + 1, i + 1;
   
  } else {
   neg, i := neg + 1, i + 1;
   
  }

  assert i == pos + neg;
}				
