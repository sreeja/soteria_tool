var counter :int;
//@invariant
function inv(counter:int) returns(bool)
{
  counter >= 0
}
procedure dec(value:int)
modifies counter;

{
counter := counter - value;
}
const _value:int;
procedure safety_dec()
modifies counter;
ensures inv(counter);
{
assume inv(counter);
call dec(_value);
}