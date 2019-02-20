var counter :int;
//@invariant
function inv(counter:int) returns(bool)
{
  counter >= 0
}
const counter1:int;
procedure dec(value:int)
modifies counter;
requires (counter > value);

{
counter := counter - value;
}
const _value:int;
procedure stability_dec()
modifies counter;
ensures counter > 0;
{
assume inv(counter);
assume counter > 0;
assume counter > _value;
call dec(_value);
}