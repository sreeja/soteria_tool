var set:[int]bool;
//@gteq
function gteq(set1:[int]bool, set2:[int]bool) returns(bool)
{(forall i:int :: set2[i] ==> set1[i])}
procedure add(value:int)
modifies set;
ensures ((forall i:int :: (i == value ==> set[i] == true) && (i != value ==> set[i] == old(set)[i])));

{
set[value] := true;
}
const _value:int;
procedure monotonicity_add()
modifies set;
ensures gteq(set,old(set));
{

call add(_value);
}