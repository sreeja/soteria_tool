var set:[int]bool;
//@gteq
function gteq(set1:[int]bool, set2:[int]bool) returns(bool)
{(forall i:int :: set2[i] ==> set1[i])}
procedure merge_5(set1:[int]bool)
modifies set;
ensures ((forall i:int :: set[i] == true));

{
assume false;
}
const _set1:[int]bool;
procedure lub_merge_5()
modifies set;
ensures (gteq(set,old(set)));
ensures (gteq(set,_set1));
ensures (forall _set:[int]bool::gteq(_set,old(set)) && gteq(_set,_set1) ==> gteq(_set,set));
{

call merge_5(_set1);
}