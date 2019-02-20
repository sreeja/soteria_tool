type ReplicaId = int;

type AuctionId = int;
type Afield a;

const unique reg:Afield bool;
const unique status:Afield bv2;
const unique winner:Afield BidId;

type Auction = [AuctionId]<a>[Afield a] a;

type BidId = int;
type Bfield b;

const unique placed:Bfield bool;
const unique auction:Bfield AuctionId;
const unique amount:Bfield int;

type Bid = [BidId]<b>[Bfield b] b;

const na:int;
axiom 0 < na;
const nb:int;
axiom 0 < nb;
const nr:int;
axiom 0 < nr;

const unique me:ReplicaId;
axiom 0 <= me && me < nr;
const unique null:BidId;
 
function {:bvbuiltin "bvult"} bv2ult(bv2,bv2) returns(bool);
function {:bvbuiltin "bvuge"} bv2uge(bv2,bv2) returns(bool);

function bv2max(x1:bv2, x2:bv2) returns(bv2);
axiom(forall x1, x2:bv2 :: bv2uge(bv2max(x1, x2), x1) && bv2uge(bv2max(x1, x2), x2));
axiom(forall x1, x2:bv2 ::  bv2max(x1, x2) == x1 || bv2max(x1, x2) == x2);
axiom(forall x:bv2 :: bv2max(x, x) == x);

function intmax(x1:int, x2:int) returns(int);
axiom(forall x1, x2:int :: (intmax(x1, x2) >= x1) && (intmax(x1, x2) >= x2));
axiom(forall x1, x2:int ::  intmax(x1, x2) == x1 || intmax(x1, x2) == x2);
axiom(forall x:int :: intmax(x, x) == x);

const invalid:bv2;
const active:bv2;
const closed:bv2;
axiom(invalid == 0bv2);
axiom(active == 1bv2);
axiom(closed == 2bv2);
axiom(forall a:AuctionId, auctions:Auction :: (0 <= a && a < na) ==> (auctions[a][status] == invalid || auctions[a][status] == active || auctions[a][status] == closed));

var auctions:Auction;
var bids:Bid;
var token:[AuctionId][ReplicaId]bool;
var right:[AuctionId]ReplicaId;

function get_winner(auction_identifier:AuctionId, bids:Bid) returns(BidId);
axiom(forall a:AuctionId, bids:Bid :: 0 <= get_winner(a, bids) && get_winner(a, bids) < nb && bids[get_winner(a, bids)][placed] && bids[get_winner(a, bids)][auction] == a && (forall b:BidId :: (0 <= b && b < nb && b != get_winner(a, bids) && bids[b][placed] && bids[get_winner(a, bids)][placed] && bids[b][auction] == a) ==> ((bids[b][amount] < bids[get_winner(a, bids)][amount]) || (bids[b][amount] == bids[get_winner(a, bids)][amount] && get_winner(a, bids) < b))));
function token_released(token:[AuctionId][ReplicaId]bool, a:AuctionId) returns(bool)
{
    !(exists r:ReplicaId:: 0 <= r && r < nr && token[a][r])
}
function is_highest_bid(bids:Bid, a:AuctionId, winner:BidId) returns(bool)
{
    (forall b:BidId :: (0 <= b && b < nb && bids[b][placed] && bids[b][auction] == a && winner != b) ==> ((bids[b][amount] < bids[winner][amount]) || (bids[b][amount] == bids[winner][amount] && winner < b)))
}

axiom(forall bids:Bid :: !bids[null][placed]);
//initialisation
axiom (forall auctions:Auction, bids:Bid, a:AuctionId :: (0 <= a && a < na && !auctions[a][reg]) ==> (auctions[a][status] == invalid && auctions[a][winner] == null && !(exists b:BidId :: bids[b][placed] && bids[b][auction] == a && bids[b][amount] > 0)));
axiom (forall a:AuctionId, auctions:Auction, token:[AuctionId][ReplicaId]bool, r:ReplicaId :: (0 <= a && a < na && 0 <= r && r < nr && !auctions[a][reg]) ==> token[a][r]);

//@gteq
function gteq(auctions1:Auction, bids1:Bid, auctions2:Auction, bids2:Bid, token1:[AuctionId][ReplicaId]bool, token2:[AuctionId][ReplicaId]bool, right1:[AuctionId]ReplicaId, right2:[AuctionId]ReplicaId) returns(bool)
{
    (forall a:AuctionId :: (0 <= a && a < na) ==> ((!auctions1[a][reg] ==> !auctions2[a][reg]) && (auctions2[a][reg] ==> auctions1[a][reg]) && bv2uge(auctions1[a][status], auctions2[a][status]) && (auctions1[a][winner] == null ==> auctions2[a][winner] == null) && (auctions2[a][winner] != null ==> auctions1[a][winner] != null))) && (forall b:BidId :: (0 <= b && b < nb) ==> ((!bids1[b][placed] ==> !bids2[b][placed]) && (bids2[b][placed] ==> bids1[b][placed]))) && (forall a:AuctionId, r:ReplicaId :: (0 <= a && a < na && 0 <= r && r < nr) ==> ((!token2[a][r] ==> !token1[a][r]) && (token1[a][r] ==> token2[a][r])))
}

//@invariant
function inv(auctions:Auction, bids:Bid, token:[AuctionId][ReplicaId]bool, right:[AuctionId]ReplicaId) returns(bool)
{
    (forall b:BidId :: (0 <= b && b < nb && bids[b][placed]) ==> (0 <= bids[b][auction] && bids[b][auction] < na && auctions[bids[b][auction]][reg] && bv2uge(auctions[bids[b][auction]][status], active) && bids[b][amount] > 0))
    && (forall a:AuctionId :: (0 <= a && a < na && bv2uge(active, auctions[a][status])) ==> auctions[a][winner] == null)
    && (forall a:AuctionId :: (0 <= a && a < na && auctions[a][status] == closed) ==> (auctions[a][reg] && (exists b:BidId :: 0 <= b && b < nb && b != null && bids[b][placed] && bids[b][auction] == a && auctions[a][winner] == b && is_highest_bid(bids, a, auctions[a][winner]))))
    && (forall a:AuctionId, r:ReplicaId :: (0 <= a && a < na && auctions[a][status] == closed && 0 <= r && r < nr) ==> !token[a][r])
    && (forall a:AuctionId :: (0 <= a && a < na && (auctions[a][status] == active || auctions[a][status] == closed)) ==> auctions[a][reg])
}

//@merge
//procedure merge(auctions1:Auction, bids1:Bid, token1:[AuctionId][ReplicaId]bool, right1:[AuctionId]ReplicaId)
//requires (forall a:AuctionId :: (0 <= a && a < na) ==> ((auctions[a][winner] == auctions1[a][winner]) || (auctions[a][winner] == null) || (auctions1[a][winner] == null)));
//requires (forall b:BidId :: (0 <= b && b < nb) ==> (bids[b][auction] == bids1[b][auction] && bids[b][amount] == bids1[b][amount]));
//requires (forall a:AuctionId :: (0 <= a && a < na && auctions[a][status] == closed) ==> (is_highest_bid(bids1, a, auctions[a][winner]) && is_highest_bid(bids, a, auctions[a][winner])));
//requires (forall a:AuctionId :: (0 <= a && a < na && auctions1[a][status] == closed) ==> (is_highest_bid(bids, a, auctions1[a][winner]) && is_highest_bid(bids1, a, auctions1[a][winner])));
//requires (forall a:AuctionId :: (0 <= a && a < na) ==> ((token[a][me] ==> token1[a][me]) && (!token1[a][me] ==> !token[a][me])));
//requires ((forall a:AuctionId, b:BidId :: (0 <= a && a < na && auctions[a][reg] && token_released(token, a) && 0 <= b && b < nb && bids[b][auction] == a && !bids[b][placed]) ==> !bids1[b][placed]));
//requires (forall a:AuctionId :: (0 <= a && a < na && right[a] == me) ==> (auctions[a][winner] == auctions1[a][winner] || auctions1[a][winner] == null));
//modifies auctions, bids, token, right;
//
//ensures (forall a:AuctionId :: (0 <= a && a < na) ==> ((auctions[a][reg] == (old(auctions)[a][reg] || auctions1[a][reg])) && (auctions[a][status] == bv2max(old(auctions)[a][status], auctions1[a][status])) && (auctions[a][winner] == (if old(auctions)[a][winner] != null then old(auctions)[a][winner] else auctions1[a][winner]))));
//ensures (forall b:BidId :: (0 <= b && b < nb) ==> ((bids[b][placed] == (old(bids)[b][placed] || bids1[b][placed])) && (bids[b][auction] == old(bids)[b][auction]) && (bids[b][amount] == old(bids)[b][amount])));
//ensures (forall a:AuctionId, r:ReplicaId :: (0 <= a && a < na && 0 <= r && r < nr) ==> (token[a][r] == (old(token)[a][r] && token1[a][r])));
//ensures (forall a:AuctionId :: (0 <= a && a < na) ==> right[a] == old(right)[a]);
//{
//    var a, b, r:int;
//    var temp_auctions:Auction;
//    var temp_bids:Bid;
//    var temp_token:[AuctionId][ReplicaId]bool;
//    temp_auctions := auctions;
//    temp_bids := bids;
//    temp_token := token;
//    a:=0;
//    b:=0;
//    while (a < na)
//    invariant(0 <= a && a <= na);
//    invariant(forall i:int :: (0<=i && i<a) ==> auctions[i][reg] == (temp_auctions[i][reg] || auctions1[i][reg]));
//    invariant(forall i:int :: (a<i && i<na) ==> auctions[i][reg] == temp_auctions[i][reg]);
//    invariant(forall i:int :: (0<=i && i<a) ==> auctions[i][status] == bv2max(temp_auctions[i][status], auctions1[i][status]));
//    invariant(forall i:int :: (a<i && i<na) ==> auctions[i][status] == temp_auctions[i][status]);
//    invariant(forall i:int :: (0<=i && i<a) ==> auctions[i][winner] == (if temp_auctions[i][winner] != null then temp_auctions[i][winner] else auctions1[i][winner]));
//    invariant(forall i:int :: (a<i && i<na) ==> auctions[i][winner] == temp_auctions[i][winner]);
//    {
//        auctions[a][reg] := temp_auctions[a][reg] || auctions1[a][reg];
//        auctions[a][status] := bv2max(temp_auctions[a][status], auctions1[a][status]);
//        if (temp_auctions[a][winner] != null)
//        {
//            auctions[a][winner] := temp_auctions[a][winner];
//        }
//        else
//        {
//            auctions[a][winner] := auctions1[a][winner];
//        }
//        a := a + 1;
//    }
//
//    while (b < nb)
//    invariant(0 <= b && b <= nb);
//    invariant(forall i:int :: (0<=i && i<b) ==> bids[i][placed] == (temp_bids[i][placed] || bids1[i][placed]));
//    invariant(forall i:int :: (b<i && i<nb) ==> bids[i][placed] == temp_bids[i][placed]);
//    invariant(forall i:int :: (0<=i && i<b) ==> bids[i][auction] == temp_bids[i][auction]);
//    invariant(forall i:int :: (b<i && i<nb) ==> bids[i][auction] == temp_bids[i][auction]);
//    invariant(forall i:int :: (0<=i && i<b) ==> bids[i][amount] == temp_bids[i][amount]);
//    invariant(forall i:int :: (b<i && i<nb) ==> bids[i][amount] == temp_bids[i][amount]);
//    {
//        bids[b][placed] := temp_bids[b][placed] || bids1[b][placed];
//        bids[b][auction] := temp_bids[b][auction];
//        bids[b][amount] := temp_bids[b][amount];
//        b := b + 1;
//    }
//    a := 0;
//    while (a < na)
//    invariant(0 <= a && a <= na);
//    invariant(forall i, j:int :: (0 <= i && i < a && 0 <= j && j < nr) ==> (token[i][j] == (temp_token[i][j] && token1[i][j])));
//    invariant(forall i, j:int :: (a < i && i < na && 0 <= j && j < nr) ==> (token[i][j] == temp_token[i][j]));
//    {
//        r := 0;
//        while (r < nr)
//        invariant(0 <= r && r <= nr);
//        invariant(a == old(a));
//        invariant(forall j:int :: (0 <= j && j < r) ==> (token[a][j] == (temp_token[a][j] && token1[a][j])));
//        //invariant(forall j:int :: (r <= j && j < nr) ==> (token[a][j] == temp_token[a][j]));
//        invariant(forall i, j:int :: (0 <= i && i < a && 0 <= j && j < nr) ==> (token[i][j] == (temp_token[i][j] && token1[i][j])));
//        invariant(forall i, j:int :: (a < i && i < na && 0 <= j && j < nr) ==> (token[i][j] == temp_token[i][j]));
//        {
//            token[a][r] := (temp_token[a][r] && token1[a][r]);
//            r := r + 1;
//        }
//        a := a + 1;
//    }
//}

//procedure createAuction(auction_identifier:AuctionId)
//requires 0 <= auction_identifier && auction_identifier < na && !auctions[auction_identifier][reg] && auctions[auction_identifier][status] == invalid && auctions[auction_identifier][winner] == null;
//requires (!token_released(token, auction_identifier));
//modifies auctions;
//ensures (forall a:AuctionId :: ((0 <= a && a < na && a == auction_identifier) ==> (auctions[a][reg] && auctions[a][winner] == null && auctions[a][status] == active)) && ((0 <= a && a < na && a != auction_identifier) ==> (auctions[a][reg] == old(auctions)[a][reg] && auctions[a][winner] == old(auctions)[a][winner] && auctions[a][status] == old(auctions)[a][status])));
//{
//    auctions[auction_identifier][reg] := true;
//    auctions[auction_identifier][winner] := null;
//    auctions[auction_identifier][status] := active;
//}

//procedure placeBid(bid_identifier:BidId, auction_identifier:AuctionId, value:int)
//requires 0 <= bid_identifier && bid_identifier < nb && !bids[bid_identifier][placed] && bids[bid_identifier][auction] == auction_identifier && bids[bid_identifier][amount] == value;
//requires 0 <= auction_identifier && auction_identifier < na && auctions[auction_identifier][reg] && auctions[auction_identifier][status] == active && auctions[auction_identifier][winner] == null;
//requires value > 0;
//requires token[auction_identifier][me];
//modifies bids;
//ensures (forall b:BidId :: ((0 <= b && b < nb && b == bid_identifier) ==> (bids[b][placed] && bids[b][auction] == old(bids)[b][auction] && bids[b][amount] == old(bids)[b][amount])) && ((0 <= b && b < nb && b != bid_identifier) ==> (bids[b][placed] == old(bids)[b][placed] && bids[b][auction] == old(bids)[b][auction] && bids[b][amount] == old(bids)[b][amount])));
//{
//    bids[bid_identifier][placed] := true;
//    bids[bid_identifier][auction] := auction_identifier;
//    bids[bid_identifier][amount] := value;
//}

//procedure closeAuction(auction_identifier:AuctionId)
//requires (0 <= auction_identifier && auction_identifier < na && auctions[auction_identifier][reg] && auctions[auction_identifier][status] == active && auctions[auction_identifier][winner] == null);
//requires (exists b:BidId :: 0 <= b && b < nb && bids[b][placed] && bids[b][auction] == auction_identifier && bids[b][amount] > 0);
//requires (forall r:ReplicaId :: (0 <= r && r < nr) ==> !token[auction_identifier][r]);
//requires (right[auction_identifier] == me);
//modifies auctions;
//ensures (forall a:AuctionId :: ((0 <= a && a < na && a == auction_identifier) ==> (auctions[a][reg] && auctions[a][status] == closed && auctions[a][winner] == get_winner(auction_identifier, bids))) && ((0 <= a && a < na && a != auction_identifier) ==> (auctions[a][reg] == old(auctions)[a][reg] && auctions[a][winner] == old(auctions)[a][winner] && auctions[a][status] == old(auctions)[a][status])));
//{
//    auctions[auction_identifier][status] := closed;
//    auctions[auction_identifier][winner] := get_winner(auction_identifier, bids);
//}
const auctions1:Auction;
const bids1:Bid;
const token1:[AuctionId][ReplicaId]bool;
const right1:[AuctionId]ReplicaId;
procedure createAuction(auction_identifier:AuctionId)
modifies auctions;
requires (0 <= auction_identifier && auction_identifier < na && !auctions[auction_identifier][reg] && auctions[auction_identifier][status] == invalid && auctions[auction_identifier][winner] == null);
requires ((!token_released(token, auction_identifier)));
ensures ((forall a:AuctionId :: ((0 <= a && a < na && a == auction_identifier) ==> (auctions[a][reg] && auctions[a][winner] == null && auctions[a][status] == active)) && ((0 <= a && a < na && a != auction_identifier) ==> (auctions[a][reg] == old(auctions)[a][reg] && auctions[a][winner] == old(auctions)[a][winner] && auctions[a][status] == old(auctions)[a][status]))));

{
auctions[auction_identifier][reg] := true;
    auctions[auction_identifier][winner] := null;
    auctions[auction_identifier][status] := active;
}
const _auction_identifier:AuctionId;
procedure stability_createAuction()
modifies auctions;
ensures (forall a:AuctionId :: (0 <= a && a < na) ==> ((auctions[a][winner] == auctions1[a][winner]) || (auctions[a][winner] == null) || (auctions1[a][winner] == null)));
ensures (forall b:BidId :: (0 <= b && b < nb) ==> (bids[b][auction] == bids1[b][auction] && bids[b][amount] == bids1[b][amount]));
ensures (forall a:AuctionId :: (0 <= a && a < na && auctions[a][status] == closed) ==> (is_highest_bid(bids1, a, auctions[a][winner]) && is_highest_bid(bids, a, auctions[a][winner])));
ensures (forall a:AuctionId :: (0 <= a && a < na && auctions1[a][status] == closed) ==> (is_highest_bid(bids, a, auctions1[a][winner]) && is_highest_bid(bids1, a, auctions1[a][winner])));
ensures (forall a:AuctionId :: (0 <= a && a < na) ==> ((token[a][me] ==> token1[a][me]) && (!token1[a][me] ==> !token[a][me])));
ensures ((forall a:AuctionId, b:BidId :: (0 <= a && a < na && auctions[a][reg] && token_released(token, a) && 0 <= b && b < nb && bids[b][auction] == a && !bids[b][placed]) ==> !bids1[b][placed]));
ensures (forall a:AuctionId :: (0 <= a && a < na && right[a] == me) ==> (auctions[a][winner] == auctions1[a][winner] || auctions1[a][winner] == null));
{
assume inv(auctions,bids,token,right) && inv(auctions1,bids1,token1,right1);
assume (forall a:AuctionId :: (0 <= a && a < na) ==> ((auctions[a][winner] == auctions1[a][winner]) || (auctions[a][winner] == null) || (auctions1[a][winner] == null)));
assume (forall b:BidId :: (0 <= b && b < nb) ==> (bids[b][auction] == bids1[b][auction] && bids[b][amount] == bids1[b][amount]));
assume (forall a:AuctionId :: (0 <= a && a < na && auctions[a][status] == closed) ==> (is_highest_bid(bids1, a, auctions[a][winner]) && is_highest_bid(bids, a, auctions[a][winner])));
assume (forall a:AuctionId :: (0 <= a && a < na && auctions1[a][status] == closed) ==> (is_highest_bid(bids, a, auctions1[a][winner]) && is_highest_bid(bids1, a, auctions1[a][winner])));
assume (forall a:AuctionId :: (0 <= a && a < na) ==> ((token[a][me] ==> token1[a][me]) && (!token1[a][me] ==> !token[a][me])));
assume ((forall a:AuctionId, b:BidId :: (0 <= a && a < na && auctions[a][reg] && token_released(token, a) && 0 <= b && b < nb && bids[b][auction] == a && !bids[b][placed]) ==> !bids1[b][placed]));
assume (forall a:AuctionId :: (0 <= a && a < na && right[a] == me) ==> (auctions[a][winner] == auctions1[a][winner] || auctions1[a][winner] == null));
assume 0 <= _auction_identifier && _auction_identifier < na && !auctions[_auction_identifier][reg] && auctions[_auction_identifier][status] == invalid && auctions[_auction_identifier][winner] == null;
assume (!token_released(token, _auction_identifier));
call createAuction(_auction_identifier);
assume {:captureState "after"} true;
}