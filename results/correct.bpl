type ReplicaID;
const unique me:ReplicaID;

type Client;
type Txn;
const unique w:Txn;
const unique d:Txn;
axiom(forall t:Txn :: t == w || t == d);
const min:int;
function max(one:int, two:int) returns(int)
{
  if one > two then (one) else (two)
}

var balances : [Client][ReplicaID][Txn]int;

//@gteq
function gteq(balances_1:[Client][ReplicaID][Txn]int, balances_2:[Client][ReplicaID][Txn]int) returns(bool)
{
  (forall c:Client, r:ReplicaID, t:Txn :: balances[c][r][t] >= old_balances[c][r][t])
}
//@invariant
function inv(balances:[Client][ReplicaID][Txn]int) returns(bool)
{
  (forall c:Client, r:ReplicaID :: balances[c][r][d] -  balances[c][r][w] >= min)
}

procedure deposit(client:Client, value:int)
modifies balances;
requires value > 0;
ensures (balances[client][me][d] == old(balances)[client][me][d] + value);
ensures (forall c:Client, r:ReplicaID :: ((c != client || r != me) ==> balances[c][r][d] == old(balances)[c][r][d]));
ensures (forall c:Client, r:ReplicaID :: (balances[c][r][w] == old(balances)[c][r][w]));
{
  balances[client][me][d] := balances[client][me][d] + value;
  balances[client][me][w] := balances[client][me][w];
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
procedure merge_proc(balances_1:[Client][ReplicaID][Txn]int)
modifies balances;
requires inv(balances_1);
ensures (forall c:Client, r:ReplicaID, t:Txn :: balances[c][r][t] == max(old(balances)[c][r][t], balances1[c][r][t]));
{
  assume false;
}