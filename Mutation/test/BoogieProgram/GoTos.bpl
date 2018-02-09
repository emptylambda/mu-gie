var bg : bool; 
procedure gotoWhere () returns(b: bool)
  ensures b;
{
  goto Here;
Here:

Here2:
	b := (bg  || !bg);
}	
