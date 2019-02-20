var counter :int;
//@invariant
function inv(counter:int) returns(bool)
{
  counter >= 0
}
procedure inc(value:int)
modifies counter;
requires (value > 0);

{
counter := counter + value;
}
const _value0:int;
const _value1:int;
procedure stability_test() 
 modifies counter; 
 modifies counter; 
{ 
 assume inv(counter); 
 assume (_value0 > 0); 
  assume (_value1 > 0);
 call inc(_value0);
call inc(_value1);
}