type ReplicaID = int;
const unique me:ReplicaID;
const nr : ReplicaID;
axiom 0 < nr;
axiom 0 <= me && me < nr;
const max:int;

function max(one:int, two:int) returns(int);
axiom(forall a:int :: max(a, a) == a);
axiom (forall a:int, b:int :: max(a,b) >= a && max(a, b) >= b);
axiom (forall a:int, b:int :: max(a,b) == a || max(a, b) == b);

var gcounter : [ReplicaID]int;

//@gteq
function gteq_counter(gcounter1:[ReplicaID]int, gcounter2:[ReplicaID]int) returns(bool)
{
  (forall r:ReplicaID :: (0 <= r && r < nr) ==> (gcounter1[r] >= gcounter2[r]))
}
//@invariant
function inv(gcounter:[ReplicaID]int) returns(bool)
{
  (forall r:ReplicaID :: (0 <= r && r < nr) ==> (gcounter[r] <= max))
}

//procedure inc(value:int)
//modifies gcounter;
//requires value > 0;
//requires gcounter[me] + value <= max;
//ensures (gcounter[me] == old(gcounter)[me] + value);
//ensures (forall r:ReplicaID :: ((r != me) ==> gcounter[r] == old(gcounter)[r]));
//{
//  gcounter[me] := gcounter[me] + value;
//}

//@merge
//procedure merge_proc(gcounter1:[ReplicaID]int)
//modifies gcounter;
//ensures (forall r:ReplicaID :: (0 <= r && r < nr) ==> (gcounter[r] == max(old(gcounter)[r], gcounter1[r])));
//{
//  var temp:[ReplicaID]int;
//  var r:int;
//  temp := gcounter;
//  r := 0;
//  while (r < nr)
//  invariant (0 <= r && r <= nr);
//  invariant (forall k:int :: (0 <= k && k < r) ==> gcounter[k] == max(old(gcounter)[k], gcounter1[k]));
//  invariant (forall k:int :: (r <= k && k < nr) ==> gcounter[k] == old(gcounter)[k]);
//  {
//    gcounter[r] := max(temp[r], gcounter1[r]);
//    r := r + 1;
//  }
//}
const gcounter1:[ReplicaID]int;
procedure merge_proc(gcounter1:[ReplicaID]int)
modifies gcounter;
ensures ((forall r:ReplicaID :: (0 <= r && r < nr) ==> (gcounter[r] == max(old(gcounter)[r], gcounter1[r]))));

{
var temp:[ReplicaID]int;
  var r:int;
  temp := gcounter;
  r := 0;
  while (r < nr)
  invariant (0 <= r && r <= nr);
  invariant (forall k:int :: (0 <= k && k < r) ==> gcounter[k] == max(old(gcounter)[k], gcounter1[k]));
  invariant (forall k:int :: (r <= k && k < nr) ==> gcounter[k] == old(gcounter)[k]);
  {
    gcounter[r] := max(temp[r], gcounter1[r]);
    r := r + 1;
  }
}
const _gcounter1:[ReplicaID]int;
procedure stability_merge_proc()
modifies gcounter;

{
assume inv(gcounter) && inv(_gcounter1);
call merge_proc(_gcounter1);
assume {:captureState "after"} true;
}