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

const unique none:AuctionId;
const unique null:BidId;
 
function {:bvbuiltin "bvugt"} bv2ugt(bv2,bv2) returns(bool);
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

var auctions:Auction;
var bids:Bid;

function get_winner(auction_identifier:AuctionId, bids:Bid) returns(BidId);
axiom(forall a:AuctionId, bids:Bid :: 0 <= get_winner(a, bids) && get_winner(a, bids) < nb && bids[get_winner(a, bids)][placed] && bids[get_winner(a, bids)][auction] == a && (forall b:BidId :: (0 <= b && b < nb && b != get_winner(a, bids) && bids[b][placed] && bids[get_winner(a, bids)][placed] && bids[b][auction] == a) ==> ((bids[b][amount] < bids[get_winner(a, bids)][amount]) || (bids[b][amount] == bids[get_winner(a, bids)][amount] && get_winner(a, bids) < b))));

axiom(forall auctions:Auction:: !auctions[none][reg] && auctions[none][status] == invalid && auctions[none][winner] == null);
axiom(forall bids:Bid :: !bids[null][placed] && bids[null][auction] == none && bids[null][amount] == 0);
//initialisation
axiom (forall auctions:Auction, bids:Bid, a:AuctionId :: (0 <= a && a < na && !auctions[a][reg]) ==> (auctions[a][status] == invalid && auctions[a][winner] == null && !(exists b:BidId :: bids[b][placed] && bids[a][auction] == a)));
axiom (forall bids:Bid, b:BidId :: (0 <= b && b < nb && !bids[b][placed]) ==> (bids[b][amount] == 0 && bids[b][auction] == none));

//@gteq
function gteq(auctions1:Auction, bids1:Bid, auctions2:Auction, bids2:Bid) returns(bool)
{
    (forall a:AuctionId :: (0 <= a && a < na) ==> ((!auctions1[a][reg] ==> !auctions2[a][reg]) && (auctions2[a][reg] ==> auctions1[a][reg]) && bv2uge(auctions1[a][status], auctions2[a][status]) && (auctions1[a][winner] == null ==> auctions2[a][winner] == null) && (auctions2[a][winner] != null ==> auctions1[a][winner] != null))) && (forall b:BidId :: (0 <= b && b < nb) ==> ((!bids1[b][placed] ==> !bids2[b][placed]) && (bids2[b][placed] ==> bids1[b][placed]) && (bids1[b][auction] == none ==> bids2[b][auction] == none) && (bids2[b][auction] != none ==> bids1[b][auction] != none) && (bids1[b][amount] >= bids2[b][amount])))
}

//@invariant
function inv(auctions:Auction, bids:Bid) returns(bool)
{
    (forall b:BidId :: (0 <= b && b < nb && bids[b][placed]) ==> bids[b][auction] != none && 0 <= bids[b][auction] && bids[b][auction] < na && auctions[bids[b][auction]][reg] && bv2uge(auctions[bids[b][auction]][status], active) && bids[b][amount] > 0)
    && (forall a:AuctionId :: (0 <= a && a < na && bv2uge(active, auctions[a][status])) ==> auctions[a][winner] == null)
    && (forall a:AuctionId :: (0 <= a && a < na && auctions[a][status] == closed) ==> (auctions[a][reg] && (exists b:BidId :: 0 <= b && b < nb && b != null && bids[b][placed] && bids[b][auction] == a && auctions[a][winner] == b && (forall b1:BidId :: (0 <= b1 && b1 < nb && b1 != b && bids[b1][placed] && bids[b1][auction] == a) ==> ((bids[b1][amount] < bids[b][amount]) || (bids[b1][amount] == bids[b][amount] && b < b1))))))
    && (forall a:AuctionId :: (0 <= a && a < na && bv2ugt(auctions[a][status], invalid)) ==> auctions[a][reg])
}

//@merge
procedure merge(auctions1:Auction, bids1:Bid)
requires (forall a:AuctionId :: (0 <= a && a < na) ==> ((auctions[a][winner] == auctions1[a][winner]) || (auctions[a][winner] == null) || (auctions1[a][winner] == null)));
requires (forall b:BidId :: (0 <= b && b < nb) ==> ((bids[b][auction] == bids1[b][auction]) || (bids[b][auction] == none) || (bids1[b][auction] == none)));
requires (forall b:BidId :: (0 <= b && b < nb && bids[b][placed] && bids1[b][placed]) ==> (bids1[b][auction] == bids[b][auction] && bids[b][amount] == bids1[b][amount]));
requires (forall a:AuctionId :: (0 <= a && a < na && auctions[a][status] == closed) ==> (forall b:BidId :: (0 <= b && b < nb && bids1[b][placed] && bids1[b][auction] == a && auctions[a][winner] != b) ==> ((bids1[b][amount] < bids1[auctions[a][winner]][amount]) || (bids1[b][amount] == bids1[auctions[a][winner]][amount] && auctions[a][winner] < b))));
requires (forall a:AuctionId :: (0 <= a && a < na && auctions1[a][status] == closed) ==> (forall b:BidId :: (0 <= b && b < nb && bids[b][placed] && bids[b][auction] == a && auctions1[a][winner] != b) ==> ((bids[b][amount] < bids[auctions1[a][winner]][amount]) || (bids[b][amount] == bids[auctions1[a][winner]][amount] && auctions1[a][winner] < b))));
modifies auctions, bids;
ensures (forall a:AuctionId :: (0 <= a && a < na) ==> ((auctions[a][reg] == (old(auctions)[a][reg] || auctions1[a][reg])) && (auctions[a][status] == bv2max(old(auctions)[a][status], auctions1[a][status])) && (auctions[a][winner] == (if old(auctions)[a][winner] != null then old(auctions)[a][winner] else auctions1[a][winner]))));
ensures (forall b:BidId :: (0 <= b && b < nb) ==> ((bids[b][placed] == (old(bids)[b][placed] || bids1[b][placed])) && (bids[b][auction] == (if old(bids)[b][auction] !=  none then old(bids)[b][auction] else bids1[b][auction])) && (bids[b][amount] == intmax(old(bids)[b][amount], bids1[b][amount]))));
{
    var a, b:int;
    var temp_auctions:Auction;
    var temp_bids:Bid;
    temp_auctions := auctions;
    temp_bids := bids;
    a:=0;
    b:=0;
    while (a < na)
    invariant(0 <= a && a <= na);
    invariant(forall i:int :: (0<=i && i<a) ==> auctions[i][reg] == (temp_auctions[i][reg] || auctions1[i][reg]));
    invariant(forall i:int :: (a<i && i<na) ==> auctions[i][reg] == temp_auctions[i][reg]);
    invariant(forall i:int :: (0<=i && i<a) ==> auctions[i][status] == bv2max(temp_auctions[i][status], auctions1[i][status]));
    invariant(forall i:int :: (a<i && i<na) ==> auctions[i][status] == temp_auctions[i][status]);
    invariant(forall i:int :: (0<=i && i<a) ==> auctions[i][winner] == (if temp_auctions[i][winner] != null then temp_auctions[i][winner] else auctions1[i][winner]));
    invariant(forall i:int :: (a<i && i<na) ==> auctions[i][winner] == temp_auctions[i][winner]);
    {
        auctions[a][reg] := temp_auctions[a][reg] || auctions1[a][reg];
        auctions[a][status] := bv2max(temp_auctions[a][status], auctions1[a][status]);
        if (temp_auctions[a][winner] != null)
        {
            auctions[a][winner] := temp_auctions[a][winner];
        }
        else
        {
            auctions[a][winner] := auctions1[a][winner];
        }
        a := a + 1;
    }

    while (b < nb)
    invariant(0 <= b && b <= nb);
    invariant(forall i:int :: (0<=i && i<b) ==> bids[i][placed] == (temp_bids[i][placed] || bids1[i][placed]));
    invariant(forall i:int :: (b<i && i<nb) ==> bids[i][placed] == temp_bids[i][placed]);
    invariant(forall i:int :: (0<=i && i<b) ==> bids[i][auction] == (if temp_bids[i][auction] !=  none then temp_bids[i][auction] else bids1[i][auction]));
    invariant(forall i:int :: (b<i && i<nb) ==> bids[i][auction] == temp_bids[i][auction]);
    invariant(forall i:int :: (0<=i && i<b) ==> bids[i][amount] == intmax(temp_bids[i][amount], bids1[i][amount]));
    invariant(forall i:int :: (b<i && i<nb) ==> bids[i][amount] == temp_bids[i][amount]);
    {
        bids[b][placed] := temp_bids[b][placed] || bids1[b][placed];
        if (temp_bids[b][auction] != none)
        {
            bids[b][auction] := temp_bids[b][auction];
        }
        else
        {
            bids[b][auction] := bids1[b][auction];
        }
        bids[b][amount] := intmax(temp_bids[b][amount], bids1[b][amount]);
        b := b + 1;
    }
}

procedure createAuction(auction_identifier:AuctionId)
requires 0 <= auction_identifier && auction_identifier < na && !auctions[auction_identifier][reg] && auctions[auction_identifier][status] == invalid && auctions[auction_identifier][winner] == null;
modifies auctions;
ensures (forall a:AuctionId :: ((0 <= a && a < na && a == auction_identifier) ==> (auctions[a][reg] && auctions[a][winner] == null && auctions[a][status] == active)) && ((0 <= a && a < na && a != auction_identifier) ==> (auctions[a][reg] == old(auctions)[a][reg] && auctions[a][winner] == old(auctions)[a][winner] && auctions[a][status] == old(auctions)[a][status])));
{
    auctions[auction_identifier][reg] := true;
    auctions[auction_identifier][winner] := null;
    auctions[auction_identifier][status] := active;
}

procedure placeBid(bid_identifier:BidId, auction_identifier:AuctionId, value:int)
requires 0 <= bid_identifier && bid_identifier < nb && !bids[bid_identifier][placed] && bids[bid_identifier][auction] == none && bids[bid_identifier][amount] == 0;
requires 0 <= auction_identifier && auction_identifier < na && auctions[auction_identifier][reg] && auctions[auction_identifier][status] == active && auctions[auction_identifier][winner] == null;
requires value > 0;
requires !(exists b:BidId :: 0 <= b && b < nb && b != bid_identifier && bids[b][placed] && bids[b][auction] == auction_identifier && bids[b][amount] == value);
modifies bids;
ensures (forall b:BidId :: ((0 <= b && b < nb && b == bid_identifier) ==> (bids[b][placed] && bids[b][auction] == auction_identifier && bids[b][amount] == value)) && ((0 <= b && b < nb && b != bid_identifier) ==> (bids[b][placed] == old(bids)[b][placed] && bids[b][auction] == old(bids)[b][auction] && bids[b][amount] == old(bids)[b][amount])));
{
    bids[bid_identifier][placed] := true;
    bids[bid_identifier][auction] := auction_identifier;
    bids[bid_identifier][amount] := value;
}

procedure closeAuction(auction_identifier:AuctionId)
requires (0 <= auction_identifier && auction_identifier < na && auctions[auction_identifier][reg] && auctions[auction_identifier][status] == active && auctions[auction_identifier][winner] == null);
requires (exists b:BidId :: 0 <= b && b < nb && bids[b][placed] && bids[b][auction] == auction_identifier && bids[b][amount] > 0);
modifies auctions;
ensures (forall a:AuctionId :: ((0 <= a && a < na && a == auction_identifier) ==> (auctions[a][reg] && auctions[a][status] == closed && auctions[a][winner] == get_winner(auction_identifier, bids))) && ((0 <= a && a < na && a != auction_identifier) ==> (auctions[a][reg] == old(auctions)[a][reg] && auctions[a][winner] == old(auctions)[a][winner] && auctions[a][status] == old(auctions)[a][status])));
{
    auctions[auction_identifier][status] := closed;
    auctions[auction_identifier][winner] := get_winner(auction_identifier, bids);
}