var counter :int;
//@invariant
function inv(counter:int) returns(bool)
{
  counter >= 0
}
procedure dec(value:int)
modifies counter;
requires (counter > value);

ensures ;
{
counter := counter - value;
}