type ISBN = int;
type Store = [ISBN]Counter;
type Selector;
type ReplicaID;
const unique me:ReplicaID;
type Counter = [Selector][ReplicaID]int;
const unique P:Selector;
const unique N:Selector;
axiom(forall s:Selector :: s == P || s == N);

const nb : ISBN;
axiom 0 < nb;

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
function gteq_store(BookStore1:Store, BookStore2:Store, UserOrders1:Order, UserOrders2:Order, Users1:[UserId]bool, Users2:[UserId]bool) returns(bool)
{
  (forall b:ISBN, r:ReplicaID :: (BookStore1[b][P][r] >= BookStore2[b][P][r]) && (BookStore1[b][N][r] >= BookStore2[b][N][r])) && (forall o:OrderId :: (UserOrders2[o][created] ==> UserOrders1[o][created]) && (UserOrders2[o][placed] ==> UserOrders1[o][placed]) && (UserOrders2[o][cancelled] ==> UserOrders1[o][cancelled]) && (UserOrders2[o][processed] ==> UserOrders1[o][processed]) && (forall b:ISBN :: UserOrders1[o][items][b] >= UserOrders2[o][items][b])) && (forall u:UserId :: Users2[u] ==> Users1[u])
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
procedure merge(BookStore1:Store, UserOrders1:Order, Users1:[UserId]bool)
modifies BookStore, UserOrders, Users;
ensures (forall b:ISBN, r:ReplicaID :: BookStore[b][P][r] == max(old(BookStore)[b][P][r], BookStore1[b][P][r]) && BookStore[b][N][r] == max(old(BookStore)[b][N][r], BookStore1[b][N][r]));
ensures (forall o:OrderId :: (UserOrders[o][created] == (old(UserOrders)[o][created] || UserOrders1[o][created])) &&  (UserOrders[o][placed] == (old(UserOrders)[o][placed] || UserOrders1[o][placed])) &&  (UserOrders[o][cancelled] == (old(UserOrders)[o][cancelled] || UserOrders1[o][cancelled])) && (UserOrders[o][processed] == (old(UserOrders)[o][processed] || UserOrders1[o][processed])) && (forall b:ISBN :: (UserOrders[o][items][b] == max(old(UserOrders)[o][items][b], UserOrders1[o][items][b]))));
ensures (forall u:UserId :: (Users[u] == (old(Users)[u] || Users[u])));
{
  assume false;
}

procedure createOrder(id:OrderId, usr:UserId)
modifies UserOrders;
requires UserOrders[id][created] == false && UserOrders[id][user] == usr;
ensures (forall o:OrderId :: (o == id ==> (UserOrders[o][created] == true && UserOrders[o][user] == usr && UserOrders[o][placed] == false && UserOrders[o][cancelled] == false && UserOrders[o][processed] == false && (forall b:ISBN :: UserOrders[o][items][b] == 0))) && (o != id ==> (UserOrders[o][created] == old(UserOrders)[o][created] && UserOrders[o][user] == old(UserOrders)[o][user] && UserOrders[o][placed] == old(UserOrders)[o][placed] && UserOrders[o][cancelled] == old(UserOrders)[o][cancelled] && UserOrders[o][processed] == old(UserOrders)[o][processed] && (forall b:ISBN :: UserOrders[o][items][b] == old(UserOrders)[o][items][b]))));
{
  UserOrders[id][created] := true;
}	

procedure updateOrder(id:OrderId, usr:UserId, book:ISBN, qty:int)
modifies UserOrders;
requires qty >= 0 && UserOrders[id][created] == true && UserOrders[id][placed] == false && UserOrders[id][user] == usr;
ensures (forall o:OrderId :: (o == id ==> (UserOrders[o][created] == old(UserOrders)[o][created] && UserOrders[o][user] == old(UserOrders)[o][user] && UserOrders[o][placed] == old(UserOrders)[o][placed] && UserOrders[o][cancelled] == old(UserOrders)[o][cancelled] && UserOrders[o][processed] == old(UserOrders)[o][processed] && (forall b:ISBN :: (b == book ==> UserOrders[o][items][b] == qty) && (b != book ==> UserOrders[o][items][b] == old(UserOrders)[o][items][b])))) && (o != id ==> (UserOrders[o][created] == old(UserOrders)[o][created] && UserOrders[o][user] == old(UserOrders)[o][user] && UserOrders[o][placed] == old(UserOrders)[o][placed] && UserOrders[o][cancelled] == old(UserOrders)[o][cancelled] && UserOrders[o][processed] == old(UserOrders)[o][processed] && (forall b:ISBN :: UserOrders[o][items][b] == old(UserOrders)[o][items][b]))));
{
  UserOrders[id][items][book] := qty;
}

procedure placeOrder(id:OrderId, usr:UserId)
modifies UserOrders;
//requires UserOrders[id][placed] == false && 
requires (exists b:ISBN :: UserOrders[id][items][b] > 0) && UserOrders[id][user] == usr;
ensures (forall o:OrderId :: (o == id ==> (UserOrders[o][created] == old(UserOrders)[o][created] && UserOrders[o][user] == old(UserOrders)[o][user] && UserOrders[o][placed] == true && UserOrders[o][cancelled] == old(UserOrders)[o][cancelled] && UserOrders[o][processed] == old(UserOrders)[o][processed] && (forall b:ISBN :: UserOrders[o][items][b] == old(UserOrders)[o][items][b]))) && (o != id ==> (UserOrders[o][created] == old(UserOrders)[o][created] && UserOrders[o][user] == old(UserOrders)[o][user] && UserOrders[o][placed] == old(UserOrders)[o][placed] && UserOrders[o][cancelled] == old(UserOrders)[o][cancelled] && UserOrders[o][processed] == old(UserOrders)[o][processed] && (forall b:ISBN :: UserOrders[o][items][b] == old(UserOrders)[o][items][b]))));
{
  UserOrders[id][placed] := true;
}	

procedure cancelOrder(id:OrderId, usr:UserId)
modifies UserOrders;
requires UserOrders[id][placed] == true && UserOrders[id][processed] == false && UserOrders[id][user] == usr;
ensures (forall o:OrderId :: (o == id ==> (UserOrders[o][created] == old(UserOrders)[o][created] && UserOrders[o][user] == old(UserOrders)[o][user] && UserOrders[o][placed] == old(UserOrders)[o][placed] && UserOrders[o][cancelled] == true && UserOrders[o][processed] == old(UserOrders)[o][processed] && (forall b:ISBN :: UserOrders[o][items][b] == old(UserOrders)[o][items][b]))) && (o != id ==> (UserOrders[o][created] == old(UserOrders)[o][created] && UserOrders[o][user] == old(UserOrders)[o][user] && UserOrders[o][placed] == old(UserOrders)[o][placed] && UserOrders[o][cancelled] == old(UserOrders)[o][cancelled] && UserOrders[o][processed] == old(UserOrders)[o][processed] && (forall b:ISBN :: UserOrders[o][items][b] == old(UserOrders)[o][items][b]))));
{
  UserOrders[id][cancelled] := true;
}

procedure processOrder(id:OrderId)
modifies UserOrders, BookStore;
requires UserOrders[id][placed] == true && UserOrders[id][processed] == false && UserOrders[id][cancelled] == false;
requires (forall b:ISBN :: BookStore[b][P][me] - BookStore[b][N][me] >= UserOrders[id][items][b]);
ensures (forall b:ISBN :: (b >= 0 && b <= nb) ==> (BookStore[b][N][me] == old(BookStore)[b][N][me] + UserOrders[id][items][b]));
ensures (forall b:ISBN, r:ReplicaID :: (b >= 0 && b <= nb) ==> ((r != me ==> BookStore[b][N][r] == old(BookStore)[b][N][r]) && BookStore[b][P][r] == old(BookStore)[b][P][r]));
ensures (forall b:ISBN, r:ReplicaID :: (b >= 0 && b <= nb) ==> ((r == me ==> (BookStore[b][N][r] == old(BookStore)[b][N][r] + UserOrders[id][items][b])) && (r != me ==> BookStore[b][N][r] == old(BookStore)[b][N][r]) && BookStore[b][P][r] == old(BookStore)[b][P][r]));
ensures (forall o:OrderId :: (o == id ==> (UserOrders[o][created] == old(UserOrders)[o][created] && UserOrders[o][user] == old(UserOrders)[o][user] && UserOrders[o][placed] == old(UserOrders)[o][placed] && UserOrders[o][cancelled] == old(UserOrders)[o][cancelled] && UserOrders[o][processed] == true && (forall b:ISBN :: UserOrders[o][items][b] == old(UserOrders)[o][items][b]))) && (o != id ==> (UserOrders[o][created] == old(UserOrders)[o][created] && UserOrders[o][user] == old(UserOrders)[o][user] && UserOrders[o][placed] == old(UserOrders)[o][placed] && UserOrders[o][cancelled] == old(UserOrders)[o][cancelled] && UserOrders[o][processed] == old(UserOrders)[o][processed] && (forall b:ISBN :: UserOrders[o][items][b] == old(UserOrders)[o][items][b]))));
{
  var book:ISBN;
  UserOrders[id][processed] := true;
  book := 0;
  while (book < nb)
  invariant (0 <= book && book <= nb);
  invariant(forall r:ReplicaID, b:ISBN :: r != me ==> BookStore[b][N][r] == old(BookStore)[b][N][r]);
  invariant(forall r:ReplicaID, b:ISBN :: BookStore[b][P][r] == old(BookStore)[b][P][r]);
  invariant(forall r:ReplicaID, b:ISBN :: (0 <= b && b < book) ==> BookStore[b][N][me] == old(BookStore)[b][N][me] + UserOrders[id][items][b]);
  {
    BookStore[book][N][me] := BookStore[book][N][me] + UserOrders[id][items][book];
    assert (BookStore[book][N][me] == (old(BookStore)[book][N][me] + UserOrders[id][items][book]));
    book := book + 1;
  }
}	

procedure purchaseStock(book:ISBN, qty:int)
modifies BookStore;
requires qty >= 0;
ensures (forall b:ISBN, r:ReplicaID :: ((b == book && r == me) ==> (BookStore[b][P][r] == old(BookStore)[b][P][r] + qty)) && ((b != book || r != me) ==> (BookStore[b][P][r] == old(BookStore)[b][P][r])) && BookStore[b][N][r] == old(BookStore)[b][N][r]);
{
  BookStore[book][P][me] := BookStore[book][P][me] + qty;
}

procedure registerUser(user:UserId)
modifies Users;
requires Users[user] == false;
ensures (forall u:UserId :: (u == user ==> Users[user] == true) && (u != user ==> Users[user] == old(Users)[user]));
{
  Users[user] := true;
}