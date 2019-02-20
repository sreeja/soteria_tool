var counter :int;
//@invariant
function inv(counter:int) returns(bool)
{
  counter >= 0
}
procedure dec(value:int)
modifies counter;
requires (counter > value);

{
counter := counter - value;
}
const _value0:int;
const _value1:int;
procedure stability_test() 
 modifies counter; 
 modifies counter; 
{ 
 assume inv(counter); 
 assume (counter > _value0); 
  assume (counter > _value1);
 call dec(_value0);
call dec(_value1);
}