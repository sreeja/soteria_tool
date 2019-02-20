var counter :int;

//@gteq
function gteq_counter(one:int, two:int) returns(int)
{
  (one >= two)
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
{
  counter := counter + value;
}
procedure dec(value:int)
modifies counter;
requires counter > value;
{
  counter := counter - value;
}

//@merge
procedure merge_proc(counter1:int)
modifies counter;
requires counter1 > 0;
{
  counter := max(counter1, counter);
}