type Client = int;
type ReplicaID = int;
const unique me:ReplicaID;
type Txn;
const unique w:Txn;
const unique d:Txn;

axiom(forall t:Txn :: t == w || t == d);
axiom(forall r:ReplicaID :: r >= 0 && r < 3);
axiom(forall c:Client :: c >= 0 && c < 3);

const min:int;
var balances : [Client][ReplicaID][Txn]int;

//@gteq
function gteq_counter(balances1:[Client][ReplicaID][Txn]int, balances2:[Client][ReplicaID][Txn]int) returns(bool)
{
  (forall c:Client, r:ReplicaID :: (c >= 0 && c < 3 && r >= 0 && r < 3) ==> (balances1[c][r][d] >= balances2[c][r][d] && balances1[c][r][w] >= balances2[c][r][w]))
}
//@invariant
function inv(balances:[Client][ReplicaID][Txn]int) returns(bool)
{
  (forall c:Client, r:ReplicaID :: (c >= 0 && c < 3 && r >= 0 && r < 3) ==> (balances[c][r][d] -  balances[c][r][w] >= min))
}
function max(one:int, two:int) returns(int)
{
  if one > two then (one) else (two)
}
procedure deposit(client:Client, value:int)
modifies balances;
requires value > 0;
ensures (balances[client][me][d] == old(balances)[client][me][d] + value);
ensures (forall c:Client, r:ReplicaID :: ((c != client || r != me) ==> balances[c][r][d] == old(balances)[c][r][d]));
ensures (forall c:Client, r:ReplicaID :: (balances[c][r][w] == old(balances)[c][r][w]));
{
  balances[client][me][d] := balances[client][me][d] + value;
}
procedure withdraw(client:Client, value:int)
modifies balances;
requires value > 0;
requires balances[client][me][d] - balances[client][me][w] >= value + min;
ensures (balances[client][me][w] == old(balances)[client][me][w] + value);
ensures (forall c:Client, r:ReplicaID :: ((c != client || r != me) ==> balances[c][r][w] == old(balances)[c][r][w]));
ensures (forall c:Client, r:ReplicaID :: (balances[c][r][d] == old(balances)[c][r][d]));
{
  balances[client][me][w] := balances[client][me][w] + value;
}

//@merge
procedure merge_proc(balances1:[Client][ReplicaID][Txn]int)
modifies balances;
ensures (forall c:Client, r:ReplicaID, t:Txn :: (c >= 0 && c < 3 && r >= 0 && r < 3 && (t == w || t == d)) ==> (balances[c][r][t] == max(old(balances)[c][r][t], balances1[c][r][t])));
{
  balances[0][0][w] := max(balances[0][0][w], balances1[0][0][w]);
  balances[0][1][w] := max(balances[0][1][w], balances1[0][1][w]);
  balances[0][2][w] := max(balances[0][2][w], balances1[0][2][w]);
  balances[1][0][w] := max(balances[1][0][w], balances1[1][0][w]);
  balances[1][1][w] := max(balances[1][1][w], balances1[1][1][w]);
  balances[1][2][w] := max(balances[1][2][w], balances1[1][2][w]);
  balances[2][0][w] := max(balances[2][0][w], balances1[2][0][w]);
  balances[2][1][w] := max(balances[2][1][w], balances1[2][1][w]);
  balances[2][2][w] := max(balances[2][2][w], balances1[2][2][w]);

  balances[0][0][d] := max(balances[0][0][d], balances1[0][0][d]);
  balances[0][1][d] := max(balances[0][1][d], balances1[0][1][d]);
  balances[0][2][d] := max(balances[0][2][d], balances1[0][2][d]);
  balances[1][0][d] := max(balances[1][0][d], balances1[1][0][d]);
  balances[1][1][d] := max(balances[1][1][d], balances1[1][1][d]);
  balances[1][2][d] := max(balances[1][2][d], balances1[1][2][d]);
  balances[2][0][d] := max(balances[2][0][d], balances1[2][0][d]);
  balances[2][1][d] := max(balances[2][1][d], balances1[2][1][d]);
  balances[2][2][d] := max(balances[2][2][d], balances1[2][2][d]);
}
