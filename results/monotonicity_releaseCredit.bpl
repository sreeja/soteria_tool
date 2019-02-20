type ReplicaID = int;
const unique me:ReplicaID;
const nr : ReplicaID;
axiom 0 < nr;
axiom 0 <= me && me < nr;
type Txn;
const unique w:Txn;
const unique d:Txn;

function max(one:int, two:int) returns(int);
axiom(forall a:int :: max(a, a) == a);
axiom (forall a:int, b:int :: max(a,b) >= a && max(a, b) >= b);
axiom (forall a:int, b:int :: max(a,b) == a || max(a, b) == b);

axiom(forall t:Txn :: t == w || t == d);
const min:int;
axiom min >= 0 ;
var balances : [ReplicaID][Txn]int;

//@gteq
function gteq_counter(balances1:[ReplicaID][Txn]int, balances2:[ReplicaID][Txn]int) returns(bool)
{
  (forall r:ReplicaID :: (0 <= r && r < nr) ==> (balances1[r][d] >= balances2[r][d] && balances1[r][w] >= balances2[r][w]))
}
//@invariant
function inv(balances:[ReplicaID][Txn]int) returns(bool)
{
  (forall r:ReplicaID :: (0 <= r && r < nr) ==> (balances[r][d] -  balances[r][w] >= min))
}

//procedure deposit(value:int)
//modifies balances;
//requires value > 0;
//ensures (balances[me][d] == old(balances)[me][d] + value);
//ensures (forall r:ReplicaID :: ((r != me) ==> balances[r][d] == old(balances)[r][d]));
//ensures (forall r:ReplicaID :: (balances[r][w] == old(balances)[r][w]));
//{
//  balances[me][d] := balances[me][d] + value;
//}
//procedure withdraw(value:int)
//modifies balances;
//requires value > 0;
//requires balances[me][d] - balances[me][w] >= value + min;
//ensures (balances[me][w] == old(balances)[me][w] + value);
//ensures (forall r:ReplicaID :: ((r != me) ==> balances[r][w] == old(balances)[r][w]));
//ensures (forall r:ReplicaID :: (balances[r][d] == old(balances)[r][d]));
//{
//  balances[me][w] := balances[me][w] + value;
//}
//procedure releaseCredit(to:ReplicaID, value:int)
//modifies balances;
//requires 0 <= to && to < nr;
//requires value > 0;
//requires balances[me][d] - balances[me][w] >= value + min;
//ensures balances[me][w] == old(balances)[me][w] + value;
//ensures (balances[to][d] == old(balances)[to][d] + value);
//ensures (forall r:ReplicaID :: ((r != me) ==> balances[r][w] == old(balances)[r][w]));
//ensures (forall r:ReplicaID :: ((r != to) ==> balances[r][d] == old(balances)[r][d]));
//{
//  balances[me][w] := balances[me][w] + value;
//  balances[to][d] := balances[to][d] + value;
//}

//@merge
//procedure merge_proc(balances1:[ReplicaID][Txn]int)
//modifies balances;
//ensures (forall r:ReplicaID :: (0 <= r && r < nr) ==> (balances[r][d] == max(old(balances)[r][d], balances1[r][d])));
//ensures (forall r:ReplicaID :: (0 <= r && r < nr) ==> (balances[r][w] == max(old(balances)[r][w], balances1[r][w])));
//{
//  var temp:[ReplicaID][Txn]int;
//  var r:int;
//  temp := balances;
//  r := 0;
//  while (r < nr)
//  invariant (0 <= r && r <= nr);
//  invariant (forall k:int :: (0 <= k && k < r) ==> balances[k][d] == max(old(balances)[k][d], balances1[k][d]));
//  invariant (forall k:int :: (r <= k && k < nr) ==> balances[k][d] == old(balances)[k][d]);
//  invariant (forall k:int :: (0 <= k && k < r) ==> balances[k][w] == max(old(balances)[k][w], balances1[k][w]));
//  invariant (forall k:int :: (r <= k && k < nr) ==> balances[k][w] == old(balances)[k][w]);
//  {
//    balances[r][d] := max(temp[r][d], balances1[r][d]);
//    balances[r][w] := max(temp[r][w], balances1[r][w]);
//    r := r + 1;
//  }
//}
procedure releaseCredit(to:ReplicaID, value:int)
modifies balances;
requires (0 <= to && to < nr);
requires (value > 0);
requires (balances[me][d] - balances[me][w] >= value + min);
ensures (balances[me][w] == old(balances)[me][w] + value);
ensures ((balances[to][d] == old(balances)[to][d] + value));
ensures ((forall r:ReplicaID :: ((r != me) ==> balances[r][w] == old(balances)[r][w])));
ensures ((forall r:ReplicaID :: ((r != to) ==> balances[r][d] == old(balances)[r][d])));

{
balances[me][w] := balances[me][w] + value;
  balances[to][d] := balances[to][d] + value;
}
const _to:ReplicaID;
const _value:int;
procedure monotonicity_releaseCredit()
modifies balances;
ensures gteq_counter(balances,old(balances));
{
assume 0 <= _to && _to < nr;
assume _value > 0;
assume balances[me][d] - balances[me][w] >= _value + min;
call releaseCredit(_to, _value);
assume {:captureState "after"} true;
}