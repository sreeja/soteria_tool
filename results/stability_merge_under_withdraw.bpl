type Client = int;
type ReplicaID = int;
const unique me:ReplicaID;
type Txn;
const unique w:Txn;
const unique d:Txn;

const nr : int;
axiom 0 < nr;
const nc : int;
axiom 0 < nc;
axiom 0 <= me && me < nr;

function max(one:int, two:int) returns(int);
axiom(forall a:int :: max(a, a) == a);
axiom (forall a:int, b:int :: max(a,b) >= a && max(a, b) >= b);
axiom (forall a:int, b:int :: max(a,b) == a || max(a, b) == b);

axiom(forall t:Txn :: t == w || t == d);
const min:int;
axiom min >= 0 ;
var balances : [Client][ReplicaID][Txn]int;

//@gteq
function gteq_counter(balances1:[Client][ReplicaID][Txn]int, balances2:[Client][ReplicaID][Txn]int) returns(bool)
{
  (forall c:Client, r:ReplicaID :: (0 <= c && c < nc && 0 <= r && r < nr) ==> (balances1[c][r][d] >= balances2[c][r][d] && balances1[c][r][w] >= balances2[c][r][w]))
}
//@invariant
function inv(balances:[Client][ReplicaID][Txn]int) returns(bool)
{
  (forall c:Client, r:ReplicaID :: (0 <= c && c < nc && 0 <= r && r < nr) ==> (balances[c][r][d] >= 0 && balances[c][r][w] >= 0 && balances[c][r][d] -  balances[c][r][w] >= min))
}

//procedure deposit(client:Client, value:int)
//modifies balances;
//requires 0 <= client && client < nc;
//requires value > 0;
//ensures (balances[client][me][d] == old(balances)[client][me][d] + value);
//ensures (forall c:Client, r:ReplicaID :: ((c != client || r != me) ==> balances[c][r][d] == old(balances)[c][r][d]));
//ensures (forall c:Client, r:ReplicaID :: (balances[c][r][w] == old(balances)[c][r][w]));
//{
//  balances[client][me][d] := balances[client][me][d] + value;
//}
//procedure withdraw(client:Client, value:int)
//modifies balances;
//requires 0 <= client && client < nc;
//requires value > 0;
//requires balances[client][me][d] - balances[client][me][w] >= value + min;
//ensures (balances[client][me][w] == old(balances)[client][me][w] + value);
//ensures (forall c:Client, r:ReplicaID :: ((c != client || r != me) ==> balances[c][r][w] == old(balances)[c][r][w]));
//ensures (forall c:Client, r:ReplicaID :: (balances[c][r][d] == old(balances)[c][r][d]));
//{
//  balances[client][me][w] := balances[client][me][w] + value;
//}
//procedure releaseCredit(client:Client, to:ReplicaID, value:int)
//modifies balances;
//requires 0 <= client && client < nc;
//requires 0 <= to && to < nr;
//requires value > 0;
//requires balances[client][me][d] - balances[client][me][w] >= value + min;
//ensures balances[client][me][w] == old(balances)[client][me][w] + value;
//ensures (balances[client][to][d] == old(balances)[client][to][d] + value);
//ensures (forall c:Client, r:ReplicaID :: ((c != client || r != me) ==> balances[c][r][w] == old(balances)[c][r][w]));
//ensures (forall c:Client, r:ReplicaID :: ((c != client || r != to) ==> balances[c][r][d] == old(balances)[c][r][d]));
//{
//  balances[client][me][w] := balances[client][me][w] + value;
//  balances[client][to][d] := balances[client][to][d] + value;
//}

//@merge
//procedure merge_proc(balances1:[Client][ReplicaID][Txn]int)
//modifies balances;
//requires (forall c:Client :: (0 <= c && c < nc) ==> ((balances[c][me][d] >= balances1[c][me][d]) && (balances[c][me][w] >= balances1[c][me][w])));
//ensures (forall c:Client, r:ReplicaID :: (0 <= c && c < nc && 0 <= r && r < nr) ==> (balances[c][r][d] == max(old(balances)[c][r][d], balances1[c][r][d])));
//ensures (forall c:Client, r:ReplicaID :: (0 <= c && c < nc && 0 <= r && r < nr) ==> (balances[c][r][w] == max(old(balances)[c][r][w], balances1[c][r][w])));
//{
//  var temp:[Client][ReplicaID][Txn]int;
//  var c:int;
//  var r:int;
//  temp := balances;
//  c := 0;
//  while (c < nc)
//  invariant (0 <= c && c <= nc);
//  invariant (forall h, k:int :: (0 <= h && h < c && 0 <= k && k < nr) ==> balances[h][k][d] == max(old(balances)[h][k][d], balances1[h][k][d]));
//  invariant (forall h, k:int :: (c <= h && h < nc && 0 <= k && k < nr) ==> balances[h][k][d] == old(balances)[h][k][d]);
//  invariant (forall h, k:int :: (0 <= h && h < c && 0 <= k && k < nr) ==> balances[h][k][w] == max(old(balances)[h][k][w], balances1[h][k][w]));
//  invariant (forall h, k:int :: (c <= h && h < nc && 0 <= k && k < nr) ==> balances[h][k][w] == old(balances)[h][k][w]);
//  {
//    r := 0;
//    while (r < nr)
//    invariant (0 <= r && r <= nr);
//    invariant ( c ==old(c));
//    invariant (forall k:int :: (0 <= k && k < r) ==> balances[c][k][d] == max(old(balances)[c][k][d], balances1[c][k][d]));
//    invariant (forall k:int :: (r <= k && k < nr) ==> balances[c][k][d] == old(balances)[c][k][d]);
//    invariant (forall h, k:int :: (0 <= h && h < c && 0 <= k && k < nr) ==> balances[h][k][d] == max(old(balances)[h][k][d], balances1[h][k][d]));
//    invariant (forall h, k:int :: (c < h && h < nc && 0 <= k && k < nr) ==> balances[h][k][d] == old(balances)[h][k][d]);
//    invariant (forall k:int :: (0 <= k && k < r) ==> balances[c][k][w] == max(old(balances)[c][k][w], balances1[c][k][w]));
//    invariant (forall k:int :: (r <= k && k < nr) ==> balances[c][k][w] == old(balances)[c][k][w]);
//    invariant (forall h, k:int :: (0 <= h && h < c && 0 <= k && k < nr) ==> balances[h][k][w] == max(old(balances)[h][k][w], balances1[h][k][w]));
//    invariant (forall h, k:int :: (c < h && h < nc && 0 <= k && k < nr) ==> balances[h][k][w] == old(balances)[h][k][w]);
//    {
//      balances[c][r][d] := max(temp[c][r][d], balances1[c][r][d]);
//      balances[c][r][w] := max(temp[c][r][w], balances1[c][r][w]);
//      r := r + 1;
//    }
//    c := c + 1;
//  }
//}
const client:Client;
const value:int;
procedure merge_proc(balances1:[Client][ReplicaID][Txn]int)
modifies balances;
requires ((forall c:Client :: (0 <= c && c < nc) ==> ((balances[c][me][d] >= balances1[c][me][d]) && (balances[c][me][w] >= balances1[c][me][w]))));
ensures ((forall c:Client, r:ReplicaID :: (0 <= c && c < nc && 0 <= r && r < nr) ==> (balances[c][r][d] == max(old(balances)[c][r][d], balances1[c][r][d]))));
ensures ((forall c:Client, r:ReplicaID :: (0 <= c && c < nc && 0 <= r && r < nr) ==> (balances[c][r][w] == max(old(balances)[c][r][w], balances1[c][r][w]))));

{
var temp:[Client][ReplicaID][Txn]int;
  var c:int;
  var r:int;
  temp := balances;
  c := 0;
  while (c < nc)
  invariant (0 <= c && c <= nc);
  invariant (forall h, k:int :: (0 <= h && h < c && 0 <= k && k < nr) ==> balances[h][k][d] == max(old(balances)[h][k][d], balances1[h][k][d]));
  invariant (forall h, k:int :: (c <= h && h < nc && 0 <= k && k < nr) ==> balances[h][k][d] == old(balances)[h][k][d]);
  invariant (forall h, k:int :: (0 <= h && h < c && 0 <= k && k < nr) ==> balances[h][k][w] == max(old(balances)[h][k][w], balances1[h][k][w]));
  invariant (forall h, k:int :: (c <= h && h < nc && 0 <= k && k < nr) ==> balances[h][k][w] == old(balances)[h][k][w]);
  {
    r := 0;
    while (r < nr)
    invariant (0 <= r && r <= nr);
    invariant ( c ==old(c));
    invariant (forall k:int :: (0 <= k && k < r) ==> balances[c][k][d] == max(old(balances)[c][k][d], balances1[c][k][d]));
    invariant (forall k:int :: (r <= k && k < nr) ==> balances[c][k][d] == old(balances)[c][k][d]);
    invariant (forall h, k:int :: (0 <= h && h < c && 0 <= k && k < nr) ==> balances[h][k][d] == max(old(balances)[h][k][d], balances1[h][k][d]));
    invariant (forall h, k:int :: (c < h && h < nc && 0 <= k && k < nr) ==> balances[h][k][d] == old(balances)[h][k][d]);
    invariant (forall k:int :: (0 <= k && k < r) ==> balances[c][k][w] == max(old(balances)[c][k][w], balances1[c][k][w]));
    invariant (forall k:int :: (r <= k && k < nr) ==> balances[c][k][w] == old(balances)[c][k][w]);
    invariant (forall h, k:int :: (0 <= h && h < c && 0 <= k && k < nr) ==> balances[h][k][w] == max(old(balances)[h][k][w], balances1[h][k][w]));
    invariant (forall h, k:int :: (c < h && h < nc && 0 <= k && k < nr) ==> balances[h][k][w] == old(balances)[h][k][w]);
    {
      balances[c][r][d] := max(temp[c][r][d], balances1[c][r][d]);
      balances[c][r][w] := max(temp[c][r][w], balances1[c][r][w]);
      r := r + 1;
    }
    c := c + 1;
  }
}
const _balances1:[Client][ReplicaID][Txn]int;
procedure stability_merge_proc()
modifies balances;
ensures 0 <= client && client < nc && value > 0 && balances[client][me][d] - balances[client][me][w] >= value + min;
{
assume inv(balances);
assume 0 <= client && client < nc && value > 0 && balances[client][me][d] - balances[client][me][w] >= value + min;
assume (forall c:Client :: (0 <= c && c < nc) ==> ((balances[c][me][d] >= _balances1[c][me][d]) && (balances[c][me][w] >= _balances1[c][me][w])));
call merge_proc(_balances1);
assume {:captureState "after"} true;
}