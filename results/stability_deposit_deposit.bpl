type Client;
type ReplicaID;
const unique me:ReplicaID;
type Txn;
const unique w:Txn;
const unique d:Txn;
axiom(forall t:Txn :: t == w || t == d);
const min:int;
var balances : [Client][ReplicaID][Txn]int;

//@gteq
function gteq_counter(balances1:[Client][ReplicaID][Txn]int, balances2:[Client][ReplicaID][Txn]int) returns(bool)
{
  (forall c:Client, r:ReplicaID :: balances1[c][r][d] >= balances2[c][r][d] && balances1[c][r][w] >= balances2[c][r][w])
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
//procedure deposit(client:Client, value:int)
//modifies balances;
//requires value > 0;
//ensures (balances[client][me][d] == old(balances)[client][me][d] + value);
//ensures (forall c:Client, r:ReplicaID :: ((c != client || r != me) ==> balances[c][r][d] == old(balances)[c][r][d]));
//ensures (forall c:Client, r:ReplicaID :: (balances[c][r][w] == old(balances)[c][r][w]));
//{
//  balances[client][me][d] := balances[client][me][d] + value;
//}
//procedure withdraw(client:Client, value:int)
//modifies balances;
//requires value > 0;
//requires balances[client][me][d] - balances[client][me][w] >= value + min;
//ensures (balances[client][me][w] == old(balances)[client][me][w] + value);
//ensures (forall c:Client, r:ReplicaID :: ((c != client || r != me) ==> balances[c][r][w] == old(balances)[c][r][w]));
//ensures (forall c:Client, r:ReplicaID :: (balances[c][r][d] == old(balances)[c][r][d]));
//{
//  balances[client][me][w] := balances[client][me][w] + value;
//}
//@merge
//procedure merge_proc(balances1:[Client][ReplicaID][Txn]int)
//modifies balances;
//requires inv(balances1);
//ensures (forall c:Client, r:ReplicaID, t:Txn :: balances[c][r][t] == max(old(balances)[c][r][t], balances1[c][r][t]));
//{
//  assume false;
//}
procedure deposit(client:Client, value:int)
modifies balances;
requires (value > 0);
ensures ((balances[client][me][d] == old(balances)[client][me][d] + value));
ensures ((forall c:Client, r:ReplicaID :: ((c != client || r != me) ==> balances[c][r][d] == old(balances)[c][r][d])));
ensures ((forall c:Client, r:ReplicaID :: (balances[c][r][w] == old(balances)[c][r][w])));

{
balances[client][me][d] := balances[client][me][d] + value;
}
const _client0:Client;
const _value0:int;
const _client1:Client;
const _value1:int;
procedure stability_test() 
 modifies balances; 
 modifies balances; 
{ 
 assume inv(balances); 
 assume (_value0 > 0); 
  assume (_value1 > 0);
 call deposit(_client0,_value0);
call deposit(_client1,_value1);
}