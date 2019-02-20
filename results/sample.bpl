var counter :int;

//@gteq
function gteq_counter(counter1:int, counter2:int) returns(bool)
{
  (counter1 >= counter2)
}
//@invariant
function inv(counter:int) returns(bool)
{
  counter >= 0
}
function max(one:int, two:int) returns(int)
{
  if one > two then (one) else (two)
}
procedure inc(value:int)
modifies counter;
requires value > 0;
ensures (counter == old(counter) + value);
{
  counter := counter + value;
}
//@merge
procedure merge_proc(counter1:int)
modifies counter;
ensures (counter >= counter1 && counter >= old(counter));
ensures (counter == counter1 || counter == old(counter));
{
  counter := max(counter1, counter);
}