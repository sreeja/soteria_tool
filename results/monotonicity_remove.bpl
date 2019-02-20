var set:[int]bool;
//@gteq
function gteq(set1:[int]bool, set2:[int]bool) returns(bool)
{(forall i:int :: set2[i] ==> set1[i])}
procedure remove(value:int)
modifies set;

{
set[value] := false;
}
const _value:int;
procedure monotonicity_remove()
modifies set;
ensures gteq(old(on),old(tw));
{

call remove(_value);
}