type Client;
type ReplicaID;
type Txn;
const w:Txn;
const d:Txn;
axiom(forall t:Txn :: t == w || t == d);
axiom(d != w);
const min:int;
var balances : [Client][ReplicaID][Txn]int;

//@gteq
function gteq_counter(balances:[Client][ReplicaID][Txn]int, old_balances:[Client][ReplicaID][Txn]int) returns(bool)
{
  (forall c:Client, r:ReplicaID, t:Txn :: balances[c][r][t] >= old_balances[c][r][t])
}
//@invariant
function inv(balances:[Client][ReplicaID][Txn]int) returns(bool)
{
  (forall c:Client, r:ReplicaID :: balances[c][r][d] -  balances[c][r][w] >= min)
}
function max(one:int, two:int) returns(int)
{
  if one > two then (one) else (two)
}
//procedure deposit(client:Client, replica:ReplicaID, value:int)
//modifies balances;
//requires value > 0;
//ensures (balances[client][replica][d] == old(balances)[client][replica][d] + value);
//ensures (forall c:Client, r:ReplicaID :: ((c != client || r != replica) ==> balances[c][r][d] == old(balances)[c][r][d]));
//ensures (forall c:Client, r:ReplicaID :: (balances[c][r][w] == old(balances)[c][r][w]));
//{
//  balances[client][replica][d] := balances[client][replica][d] + value;
//  balances[client][replica][w] := balances[client][replica][w];
//}
//procedure withdraw(client:Client, replica:ReplicaID, value:int)
//modifies balances;
//requires value > 0;
//requires balances[client][replica][d] - balances[client][replica][w] >= value + min;
//ensures (balances[client][replica][w] == old(balances)[client][replica][w] + value);
//ensures (forall c:Client, r:ReplicaID :: ((c != client || r != replica) ==> balances[c][r][w] == old(balances)[c][r][w]));
//ensures (forall c:Client, r:ReplicaID :: (balances[c][r][d] == old(balances)[c][r][d]));
//{
//  balances[client][replica][w] := balances[client][replica][w] + value;
//}
//@merge
//procedure merge_proc(balances1:[Client][ReplicaID][Txn]int)
//modifies balances;
//requires inv(balances1);
//ensures (forall c:Client, r:ReplicaID, t:Txn :: balances[c][r][t] == max(old(balances)[c][r][t], balances1[c][r][t]));
//{
//  assume false;
//}
procedure merge_proc(balances1:[Client][ReplicaID][Txn]int)
modifies balances;
requires (inv(balances1));
ensures ((forall c:Client, r:ReplicaID, t:Txn :: balances[c][r][t] == max(old(balances)[c][r][t], balances1[c][r][t])));

{
assume false;
}
const _balances10:[Client][ReplicaID][Txn]int;
const _balances11:[Client][ReplicaID][Txn]int;
procedure stability_test() 
 modifies balances; 
 modifies balances; 
{ 
 assume inv(balances); 
 assume (inv(_balances10)); 
  assume (inv(_balances11));
 call merge_proc(_balances10);
call merge_proc(_balances11);
}