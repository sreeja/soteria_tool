type ISBN;
type Store = [ISBN]Counter;
type Selector;
type ReplicaID;

type Counter = [Selector][ReplicaID]int;
const unique P:Selector;
const unique N:Selector;
axiom(forall s:Selector :: s == P || s == N);

//function value(c:Counter) returns(int)
//{
//  (c[P]-c[N])
//}	

//function inc(c:Counter, oldC:Counter, value:int) returns (bool)
//{
//  (c[P] == oldC[P] + value) && (c[N] == oldC[N])
//}

//function dec(c:Counter, oldC:Counter, value:int) returns (bool)
//{
//  (c[P] == oldC[P]) && (c[N] == oldC[N] + value)
//}

function max(a:int, b:int) returns(int)
{
  (if a > b then a else b)
}

type UserId;
//type Name;
//type User = [UserId]Name;

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
var Users:[UserId]bool;

//@gteq
function gteq_store(S1:Store, S2:Store) returns(bool)
{
  (forall b:ISBN, r:ReplicaID :: (S1[b][P][r] >= S2[b][P][r]) && (S1[b][N][r] >= S2[b][N][r]))
}
//@gteq
function gteq_order(O1:Order, O2:Order) returns(bool)
{
  (forall o:OrderId :: (O2[o][created] ==> O1[o][created]) && (O2[o][placed] ==> O1[o][placed]) && (O2[o][cancelled] ==> O1[o][cancelled]) && (O2[o][processed] ==> O1[o][processed]) && (forall b:ISBN :: O1[o][items][b] >= O2[o][items][b]))
}
//@gteq
function gteq_users(U1:[UserId]bool, U2:[UserId]bool) returns(bool)
{
  (forall u:UserId :: U2[u] ==> U1[u])
}

//@invariant
function inv(BookStore:Store, UserOrders:Order, Users:[UserId]bool) returns(bool)
{
  positiveStock(BookStore) && oderCreationByRegCustomers(UserOrders, Users) && orderUpdateAfterCreation(UserOrders) && ordersPlacedAfterUpdation(UserOrders) && orderCancelledAfterPlaceNotProcessed(UserOrders) && orderProcessedAfterPlaceNotCancelled(UserOrders)
}
function positiveStock(BookStore:Store) returns(bool)
{
  (forall b:ISBN, r:ReplicaID :: (BookStore[b][P][r] - BookStore[b][N][r]) >= 0)
}
function oderCreationByRegCustomers(UserOrders:Order, Users:[UserId]bool) returns(bool)
{
  (forall o:OrderId :: UserOrders[o][created] ==> Users[UserOrders[o][user]])
}
function orderUpdateAfterCreation(UserOrders:Order) returns(bool)
{
  (forall o:OrderId :: (exists i:ISBN :: UserOrders[o][items][i] > 0) ==> UserOrders[o][created])
}
function ordersPlacedAfterUpdation(UserOrders:Order) returns(bool)
{
  (forall o:OrderId :: UserOrders[o][placed] ==> UserOrders[o][created] && (exists i:ISBN :: UserOrders[o][items][i] > 0))
}
function orderCancelledAfterPlaceNotProcessed(UserOrders:Order) returns(bool)
{
  (forall o:OrderId :: UserOrders[o][cancelled] ==> UserOrders[o][placed] && !UserOrders[o][processed])
}
function orderProcessedAfterPlaceNotCancelled(UserOrders:Order) returns(bool)
{
  (forall o:OrderId :: UserOrders[o][processed] ==> UserOrders[o][placed] && !UserOrders[o][cancelled])
}

//@merge
//procedure mergeStore(incoming:Store)
//modifies BookStore;
//ensures (forall b:ISBN, r:ReplicaID :: BookStore[b][P][r] == max(old(BookStore)[b][P][r], incoming[b][P][r]) && BookStore[b][N][r] == max(old(BookStore)[b][N][r], incoming[b][N][r]));
//{
//  assume false;
//}	

//@merge
//procedure mergeOrders(incoming:Order)
//modifies UserOrders;
//ensures (forall o:OrderId :: (UserOrders[o][created] == (old(UserOrders)[o][created] || incoming[o][created])) &&  (UserOrders[o][placed] == (old(UserOrders)[o][placed] || incoming[o][placed])) &&  (UserOrders[o][cancelled] == (old(UserOrders)[o][cancelled] || incoming[o][cancelled])) && (UserOrders[o][processed] == (old(UserOrders)[o][processed] || incoming[o][processed])) && (forall b:ISBN :: (UserOrders[o][items][b] == max(old(UserOrders)[o][items][b], incoming[o][items][b]))));
//{
//  assume false;
//}	

//@merge
//procedure mergeUsers(incoming:[UserId]bool)
//modifies Users;
//ensures (forall u:UserId :: (Users[u] == (old(Users)[u] || incoming[u])));
//{
//  assume false;
//}

//order methods
//procedure createOrder(id:OrderId, usr:UserId)
//modifies UserOrders;
//requires UserOrders[id][created] == false && UserOrders[id][user] == usr;
//ensures (forall o:OrderId :: (o == id ==> (UserOrders[o][created] == true && UserOrders[o][user] == usr && UserOrders[o][placed] == false && UserOrders[o][cancelled] == false && UserOrders[o][processed] == false && (forall b:ISBN :: UserOrders[o][items][b] == 0))) && (o != id ==> (UserOrders[o][created] == old(UserOrders)[o][created] && UserOrders[o][user] == old(UserOrders)[o][user] && UserOrders[o][placed] == old(UserOrders)[o][placed] && UserOrders[o][cancelled] == old(UserOrders)[o][cancelled] && UserOrders[o][processed] == old(UserOrders)[o][processed] && (forall b:ISBN :: UserOrders[o][items][b] == old(UserOrders)[o][items][b]))));
//{
//  //UserOrders[id][created] := true;
//  assume false;
//}	

//procedure updateOrder(id:OrderId, usr:UserId, book:ISBN, qty:int)
//modifies UserOrders;
//requires qty >= 0 && UserOrders[id][created] == true && UserOrders[id][placed] == false && UserOrders[id][user] == usr;
//ensures (forall o:OrderId :: (o == id ==> (UserOrders[o][created] == old(UserOrders)[o][created] && UserOrders[o][user] == old(UserOrders)[o][user] && UserOrders[o][placed] == false && UserOrders[o][cancelled] == false && UserOrders[o][processed] == false && (forall b:ISBN :: (b == book ==> UserOrders[o][items][b] == qty) && (b != book ==> UserOrders[o][items][b] == old(UserOrders)[o][items][b])))) && (o != id ==> (UserOrders[o][created] == old(UserOrders)[o][created] && UserOrders[o][user] == old(UserOrders)[o][user] && UserOrders[o][placed] == old(UserOrders)[o][placed] && UserOrders[o][cancelled] == old(UserOrders)[o][cancelled] && UserOrders[o][processed] == old(UserOrders)[o][processed] && (forall b:ISBN :: UserOrders[o][items][b] == old(UserOrders)[o][items][b]))));
//{
//  //UserOrders[id][items][book] := UserOrders[id][items][book] + qty;
//  assume false;
//}

//procedure placeOrder(id:OrderId, usr:UserId)
//modifies UserOrders;
////requires UserOrders[id][placed] == false && 
//requires (exists b:ISBN :: UserOrders[id][items][b] > 0) && UserOrders[id][user] == usr;
//ensures (forall o:OrderId :: (o == id ==> (UserOrders[o][created] == old(UserOrders)[o][created] && UserOrders[o][user] == old(UserOrders)[o][user] && UserOrders[o][placed] == true && UserOrders[o][cancelled] == old(UserOrders)[o][cancelled] && UserOrders[o][processed] == old(UserOrders)[o][processed] && (forall b:ISBN :: UserOrders[o][items][b] == old(UserOrders)[o][items][b]))) && (o != id ==> (UserOrders[o][created] == old(UserOrders)[o][created] && UserOrders[o][user] == old(UserOrders)[o][user] && UserOrders[o][placed] == old(UserOrders)[o][placed] && UserOrders[o][cancelled] == old(UserOrders)[o][cancelled] && UserOrders[o][processed] == old(UserOrders)[o][processed] && (forall b:ISBN :: UserOrders[o][items][b] == old(UserOrders)[o][items][b]))));
//{
//  //UserOrders[id][placed] := true;
//  assume false;
//}	

//procedure cancelOrder(id:OrderId, usr:UserId)
//modifies UserOrders;
//requires UserOrders[id][placed] == true && UserOrders[id][processed] == false && UserOrders[id][user] == usr;
//ensures (forall o:OrderId :: (o == id ==> (UserOrders[o][created] == old(UserOrders)[o][created] && UserOrders[o][user] == old(UserOrders)[o][user] && UserOrders[o][placed] == old(UserOrders)[o][placed] && UserOrders[o][cancelled] == true && UserOrders[o][processed] == old(UserOrders)[o][processed] && (forall b:ISBN :: UserOrders[o][items][b] == old(UserOrders)[o][items][b]))) && (o != id ==> (UserOrders[o][created] == old(UserOrders)[o][created] && UserOrders[o][user] == old(UserOrders)[o][user] && UserOrders[o][placed] == old(UserOrders)[o][placed] && UserOrders[o][cancelled] == old(UserOrders)[o][cancelled] && UserOrders[o][processed] == old(UserOrders)[o][processed] && (forall b:ISBN :: UserOrders[o][items][b] == old(UserOrders)[o][items][b]))));
//{
//  //UserOrders[id][cancelled] := true;
//  assume false;
//}

//procedure processOrder(id:OrderId, storeloc:ReplicaID)
//modifies UserOrders, BookStore;
//requires UserOrders[id][placed] == true && UserOrders[id][processed] == false && UserOrders[id][cancelled] == false;
//requires (forall b:ISBN :: BookStore[b][P][storeloc] - BookStore[b][N][storeloc] >= UserOrders[id][items][b]);
//ensures (forall b:ISBN, r:ReplicaID :: (r == storeloc ==> (BookStore[b][N][r] == old(BookStore)[b][N][r] + UserOrders[id][items][b])) && (r != storeloc ==> BookStore[b][N][r] == old(BookStore)[b][N][r]) && BookStore[b][P][r] == old(BookStore)[b][P][r]);
//ensures (forall o:OrderId :: (o == id ==> (UserOrders[o][created] == old(UserOrders)[o][created] && UserOrders[o][user] == old(UserOrders)[o][user] && UserOrders[o][placed] == old(UserOrders)[o][placed] && UserOrders[o][cancelled] == old(UserOrders)[o][cancelled] && UserOrders[o][processed] == true && (forall b:ISBN :: UserOrders[o][items][b] == old(UserOrders)[o][items][b]))) && (o != id ==> (UserOrders[o][created] == old(UserOrders)[o][created] && UserOrders[o][user] == old(UserOrders)[o][user] && UserOrders[o][placed] == old(UserOrders)[o][placed] && UserOrders[o][cancelled] == old(UserOrders)[o][cancelled] && UserOrders[o][processed] == old(UserOrders)[o][processed] && (forall b:ISBN :: UserOrders[o][items][b] == old(UserOrders)[o][items][b]))));
//{
//  //UserOrders[id][processed] := true;
//	assume false;
//}	

//procedure purchaseStock(book:ISBN, qty:int, storeloc:ReplicaID)
//modifies BookStore;
//requires qty >= 0;
//ensures (forall b:ISBN, r:ReplicaID :: ((b == book && r == storeloc) ==> (BookStore[b][P][r] == old(BookStore)[b][P][r] + qty)) && ((b != book || r != storeloc) ==> (BookStore[b][P][r] == old(BookStore)[b][P][r])) && BookStore[b][N][r] == old(BookStore)[b][N][r]);
//{
//  //BookStore[book][P] := BookStore[book][P] + qty;
//  assume false;
//}

//customer methods
//procedure registerUser(user:UserId)
//modifies Users;
//requires Users[user] == false;
//ensures (forall u:UserId :: (u == user ==> Users[user] == true) && (u != user ==> Users[user] == old(Users)[user]));
//{
//  assume false;
//}
procedure createOrder(id:OrderId, usr:UserId)
modifies UserOrders;
requires (UserOrders[id][created] == false && UserOrders[id][user] == usr);
ensures ((forall o:OrderId :: (o == id ==> (UserOrders[o][created] == true && UserOrders[o][user] == usr && UserOrders[o][placed] == false && UserOrders[o][cancelled] == false && UserOrders[o][processed] == false && (forall b:ISBN :: UserOrders[o][items][b] == 0))) && (o != id ==> (UserOrders[o][created] == old(UserOrders)[o][created] && UserOrders[o][user] == old(UserOrders)[o][user] && UserOrders[o][placed] == old(UserOrders)[o][placed] && UserOrders[o][cancelled] == old(UserOrders)[o][cancelled] && UserOrders[o][processed] == old(UserOrders)[o][processed] && (forall b:ISBN :: UserOrders[o][items][b] == old(UserOrders)[o][items][b])))));

ensures gteq_order(UserOrders, old(UserOrders));
{
//UserOrders[id][created] := true;
  assume false;
}