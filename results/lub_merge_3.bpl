var counter :int;
//@invariant
function inv(counter:int) returns(bool)
{
  counter >= 0
}
procedure merge_3(other:int)
modifies counter;
requires (other > 0);


{
counter := (if counter > other then counter else other);
}