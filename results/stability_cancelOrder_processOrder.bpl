type ISBN;
type Store = [ISBN]Counter;
type Selector;
type Counter = [Selector]int;
const unique P:Selector;
const unique N:Selector;
axiom(forall s:Selector :: s == P || s == N);
function value(c:Counter) returns(int){  (c[P]-c[N]) }	
function inc(c:Counter, oldC:Counter, value:int) returns (bool){  (c[P] == oldC[P] + value) && (c[N] == oldC[N]) }
function dec(c:Counter, oldC:Counter, value:int) returns (bool){  (c[P] == oldC[P]) && (c[N] == oldC[N] + value) }
function max(a:int, b:int) returns(int){  (if a > b then a else b)}
type UserId;
type OrderId;
type Field a;
type Order = [OrderId]<a>[Field a]a;
const unique user: Field UserId;
const unique items: Field [ISBN]int;
const unique created:Field bool;
const unique placed:Field bool;
const unique cancelled:Field bool;
const unique processed: Field bool;
axiom(forall orders:Order, o:OrderId :: orders[o][created] == false ==> (orders[o][placed] == false && orders[o][cancelled] == false && orders[o][processed] == false && (forall b:ISBN :: orders[o][items][b] == 0)));
var BookStore:Store;
var UserOrders:Order;
function gteq_store(S1:Store, S2:Store) returns(bool){  (forall b:ISBN :: value(S1[b]) >= value(S2[b]))}
function gteq_order(O1:Order, O2:Order) returns(bool){  (forall o:OrderId :: (O2[o][created] ==> O1[o][created]) && (O2[o][placed] ==> O1[o][placed]) && (O2[o][cancelled] ==> O1[o][cancelled]) && (O2[o][processed] ==> O1[o][processed]) && (forall b:ISBN :: O1[o][items][b] >= O2[o][items][b]))}
function inv(BookStore:Store, UserOrders:Order) returns(bool){  (forall b:ISBN :: value(BookStore[b]) >= 0)}

procedure cancelOrder(id:OrderId, usr:UserId)
modifies UserOrders;
requires (UserOrders[id][placed] == true && UserOrders[id][processed] == false && UserOrders[id][user] == usr);
ensures ((forall o:OrderId :: (o == id ==> (UserOrders[o][created] == old(UserOrders)[o][created] && UserOrders[o][user] == old(UserOrders)[o][user] && UserOrders[o][placed] == old(UserOrders)[o][placed] && UserOrders[o][cancelled] == true && UserOrders[o][processed] == old(UserOrders)[o][processed] && (forall b:ISBN :: UserOrders[o][items][b] == old(UserOrders)[o][items][b]))) && (o != id ==> (UserOrders[o][created] == old(UserOrders)[o][created] && UserOrders[o][user] == old(UserOrders)[o][user] && UserOrders[o][placed] == old(UserOrders)[o][placed] && UserOrders[o][cancelled] == old(UserOrders)[o][cancelled] && UserOrders[o][processed] == old(UserOrders)[o][processed] && (forall b:ISBN :: UserOrders[o][items][b] == old(UserOrders)[o][items][b])))));

{
assume false;
}
procedure processOrder(id:OrderId)
modifies UserOrders, BookStore;
requires (UserOrders[id][placed] == true && UserOrders[id][processed] == false && UserOrders[id][cancelled] == false);
ensures ((forall o:OrderId :: (o == id ==> (UserOrders[o][created] == old(UserOrders)[o][created] && UserOrders[o][user] == old(UserOrders)[o][user] && UserOrders[o][placed] == old(UserOrders)[o][placed] && UserOrders[o][cancelled] == old(UserOrders)[o][cancelled] && UserOrders[o][processed] == true && (forall b:ISBN :: UserOrders[o][items][b] == old(UserOrders)[o][items][b]))) && (o != id ==> (UserOrders[o][created] == old(UserOrders)[o][created] && UserOrders[o][user] == old(UserOrders)[o][user] && UserOrders[o][placed] == old(UserOrders)[o][placed] && UserOrders[o][cancelled] == old(UserOrders)[o][cancelled] && UserOrders[o][processed] == old(UserOrders)[o][processed] && (forall b:ISBN :: UserOrders[o][items][b] == old(UserOrders)[o][items][b])))));

{
assume false;
}
const _id0:OrderId;
const _usr0:UserId;
const _id1:OrderId;
procedure stability_test() 
 modifies UserOrders; 
 modifies UserOrders,BookStore; 
{ 
 assume inv(BookStore,UserOrders); 
 assume (UserOrders[_id0][placed] == true && UserOrders[_id0][processed] == false && UserOrders[_id0][user] == _usr0); 
  assume (UserOrders[_id1][placed] == true && UserOrders[_id1][processed] == false && UserOrders[_id1][cancelled] == false);
  assume (_id0 != _id1);
 call cancelOrder(_id0,_usr0);
call processOrder(_id1);
}