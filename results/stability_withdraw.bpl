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
var balances : [Txn]int;

//@gteq
function gteq_counter(balances1:[Txn]int, balances2:[Txn]int) returns(bool)
{
  (balances1[d] >= balances2[d] && balances1[w] >= balances2[w])
}
//@invariant
function inv(balances:[Txn]int) returns(bool)
{
  (balances[d] - balances[w] >= min)
}

//procedure deposit(value:int)
//modifies balances;
//requires value > 0;
//ensures (balances[d] == old(balances)[d] + value);
//ensures (balances[w] == old(balances)[w]);
//{
//  balances[d] := balances[d] + value;
//}
//procedure withdraw(value:int)
//modifies balances;
//requires value > 0;
//requires balances[d] - balances[w] >= value + min;
//ensures (balances[w] == old(balances)[w] + value);
//ensures (balances[d] == old(balances)[d]);
//{
//  balances[w] := balances[w] + value;
//}

//@merge
//procedure merge_proc(balances1:[Txn]int)
//modifies balances;
//ensures (balances[d] == max(old(balances)[d], balances1[d]));
//ensures (balances[w] == max(old(balances)[w], balances1[w]));
//{
//  var temp:[Txn]int;
//  temp := balances;
//  balances[d] := max(temp[d], balances1[d]);
//  balances[w] := max(temp[w], balances1[w]);
//}
const balances1:[Txn]int;
procedure withdraw(value:int)
modifies balances;
requires (value > 0);
requires (balances[d] - balances[w] >= value + min);
ensures ((balances[w] == old(balances)[w] + value));
ensures ((balances[d] == old(balances)[d]));

{
balances[w] := balances[w] + value;
}
const _value:int;
procedure stability_withdraw()
modifies balances;

{
assume inv(balances) && inv(balances1);
assume _value > 0;
assume balances[d] - balances[w] >= _value + min;
call withdraw(_value);
assume {:captureState "after"} true;
}