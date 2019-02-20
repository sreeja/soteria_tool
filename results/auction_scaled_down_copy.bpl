type AuctionId=int;
type BidId=int;

const na:int;
axiom 0 < na;
const nb:int;
axiom 0 < nb;

const unique null:BidId;

var auctions:[AuctionId]bool;
var auction_prep:[AuctionId]bool; 
var auction_active:[AuctionId]bool; 
var auction_closed:[AuctionId]bool; 
var auction_winner:[AuctionId]BidId;
var bids:[BidId]bool;
var bid_auction:[BidId]AuctionId;
var bid_amount:[BidId]int;

axiom(forall a:AuctionId, auctions, auction_prep, auction_active, auction_closed:[AuctionId]bool, auction_winner:[AuctionId]BidId, bids:[BidId]bool, bid_auction:[BidId]AuctionId, bid_amount:[BidId]int :: (0 <= a && a < na && !auctions[a]) ==> (!auction_prep[a] && !auction_active[a] && !auction_closed[a] && auction_winner[a] == null && (forall b:BidId :: (0 <= b && b < nb && bids[b]) ==> (bid_auction[b] != a && bid_amount[b] == 0))));

function get_winner(auction_identifier:AuctionId, bids:[BidId]bool, bid_auction:[BidId]AuctionId, bid_amount:[BidId]int) returns(BidId);

axiom(forall auction_identifier:AuctionId, bids:[BidId]bool, bid_auction:[BidId]AuctionId, bid_amount:[BidId]int, b:BidId :: (get_winner(auction_identifier, bids, bid_auction, bid_amount) == b) ==> (0 <= b && b < nb && bids[b] && bid_auction[b] == auction_identifier && (forall b1:BidId :: (b1 != b && 0 <= b1 && b1 < nb && bids[b1] && bid_auction[b1] == auction_identifier) ==> bid_amount[b1] < bid_amount[b])));

//@gteq
function gteq(auctions1:[AuctionId]bool, auction_winner1:[AuctionId]BidId, auction_prep1:[AuctionId]bool, auction_active1:[AuctionId]bool, auction_closed1:[AuctionId]bool, bids1:[BidId]bool, bid_auction1:[BidId]AuctionId, bid_amount1:[BidId]int, auctions2:[AuctionId]bool, auction_winner2:[AuctionId]BidId, auction_prep2:[AuctionId]bool, auction_active2:[AuctionId]bool, auction_closed2:[AuctionId]bool, bids2:[BidId]bool, bid_auction2:[BidId]AuctionId, bid_amount2:[BidId]int) returns(bool)
{
    (forall a:AuctionId :: (0<= a && a < na && !auctions1[a]) ==> !auctions2[a]) 
    && (forall a:AuctionId :: (0<=a && a<na)==> ((!auction_prep1[a] ==> !auction_prep2[a]) && (!auction_active1[a] ==> !auction_active2[a] ) && (!auction_closed1[a] ==> !auction_closed2[a]))) 
    && (forall a:AuctionId :: (0<=a && a<na)==> ((auction_winner1[a] == null ==> auction_winner2[a] == null) || (auction_winner1[a] == auction_winner2[a]))) 
    && (forall b:BidId :: (0<=b && b<nb && !bids1[b]) ==> !bids2[b])
    && (forall b:BidId :: (0 <= b && b < nb) ==> bid_amount1[b] >= bid_amount2[b])
}

//@invariant
function inv(auctions:[AuctionId]bool, auction_prep:[AuctionId]bool, auction_active:[AuctionId]bool, auction_closed:[AuctionId]bool, auction_winner:[AuctionId]BidId, bids:[BidId]bool, bid_auction:[BidId]AuctionId, bid_amount:[BidId]int) returns(bool)
{
    (forall b:BidId :: (0 <= b && b < nb && bids[b]) ==> ((exists a:AuctionId :: 0 <= a && a < na && auctions[a] && bid_auction[b] == a) && bid_amount[b] >= 0)) 
    && (forall a:AuctionId :: (0 <= a && a < na && auctions[a] && !auction_closed[a] && (auction_active[a] || auction_prep[a])) ==> auction_winner[a] == null)
    && (forall a:AuctionId :: (0 <= a && a < na && auctions[a] && !auction_active[a]) ==> (forall b:BidId :: (0 <= b && b < nb && bid_auction[b] == a) ==> !bids[b])) 
    && (forall a:AuctionId :: (0 <= a && a < na && auctions[a] && auction_closed[a]) ==> (auction_winner[a] != null && (exists b:BidId :: 0 <= b && b < nb && bids[b] && bid_auction[b] == a && (forall b1:BidId :: (0 <= b1 && b1 < nb && b != b1 && bids[b1] && bid_auction[b1] == a) ==> (bid_amount[b1] < bid_amount[b]) ))))  
    && (forall a:AuctionId :: (0 <= a && a < na && auction_closed[a] ==> (auction_prep[a] && auction_active[a])))
    && (forall a:AuctionId :: (0 <= a && a < na && auction_active[a] ==> auction_prep[a]))

}

procedure createAuction(identifier:AuctionId)
requires (0 <= identifier && identifier < na);
requires auctions[identifier] == false && !auction_prep[identifier] && !auction_active[identifier] && !auction_closed[identifier] && auction_winner[identifier] == null;
requires (forall b:BidId :: (0 <= b && b < nb && bid_auction[b] == identifier) ==> (bids[b] == false));
modifies auctions, auction_prep, auction_winner;
ensures (forall a:AuctionId :: ((0 <= a && a < na && a == identifier) ==> (auctions[a] == true && auction_prep[a] && auction_winner[a] == null)) && ((0 <= a && a < na && a != identifier) ==> (auctions[a] == old(auctions)[a] && auction_prep[a] == old(auction_prep)[a] && auction_winner[a] == old(auction_winner)[a])));
{
    auctions[identifier] := true;
    auction_prep[identifier] := true;
    auction_winner[identifier] := null;
}

procedure startAuction(identifier:AuctionId)
requires (0 <= identifier && identifier < na);
requires auctions[identifier] == true && auction_prep[identifier] && !auction_active[identifier] && !auction_closed[identifier];
modifies auction_active;
ensures (forall a:AuctionId :: ((0 <= a && a < na && a == identifier) ==> auction_active[a]) && ((0 <= a && a < na && a != identifier) ==> auction_active[a] == old(auction_active)[a]));
{
    auction_active[identifier] := true;
}

procedure placeBid(bid_identifier:BidId, auction_identifier:AuctionId, value:int)
requires auctions[auction_identifier] == true;
requires (0 <= auction_identifier && auction_identifier < na);
requires (0 <= bid_identifier && bid_identifier < nb);
requires bids[bid_identifier] == false && bid_auction[bid_identifier] == auction_identifier && bid_amount[bid_identifier] == value;
requires auction_prep[auction_identifier] && auction_active[auction_identifier] && !auction_closed[auction_identifier];
requires (forall b:BidId :: (0 <= b && b < nb && b != bid_identifier && bids[b] && bid_auction[b] == auction_identifier) ==> bid_amount[b] != value);
requires value > 0;
modifies bids, bid_auction, bid_amount;
ensures (forall b:BidId :: ((0 <= b && b < nb && b == bid_identifier) ==> bids[b] == true && bid_auction[b] == auction_identifier && bid_amount[b] == value) && ((0 <= b && b < nb && b != bid_identifier) ==> bids[b] == old(bids)[b] && bid_auction[b] == old(bid_auction)[b] && bid_amount[b] == old(bid_amount)[b]));
{
    bids[bid_identifier] := true;
    bid_auction[bid_identifier] := auction_identifier;
    bid_amount[bid_identifier] := value;
}

procedure closeAuction(auction_identifier:AuctionId)
requires auctions[auction_identifier] == true && auction_winner[auction_identifier] == null;
requires auction_prep[auction_identifier] && auction_active[auction_identifier] && !auction_closed[auction_identifier];
requires (0 <= auction_identifier && auction_identifier < na);
requires (exists b:BidId :: 0 <= b && b < nb && bids[b] && bid_auction[b] == auction_identifier);

modifies auction_closed, auction_winner;

ensures (forall a:AuctionId :: ((0 <= a && a < na && a == auction_identifier) ==> auction_closed[a]) && ((0 <= a && a < na && a != auction_identifier) ==> auction_closed[a] == old(auction_closed)[a]));
ensures (forall a:AuctionId :: ((0 <= a && a < na && a == auction_identifier) ==> auction_winner[a] == get_winner(auction_identifier, bids, bid_auction, bid_amount)) && ((0 <= a && a < na && a != auction_identifier) ==> auction_winner[a] == old(auction_winner)[a]));
{
    auction_closed[auction_identifier] := true;
    auction_winner[auction_identifier] := get_winner(auction_identifier, bids, bid_auction, bid_amount);
}

//@merge
procedure merge(auctions1:[AuctionId]bool, auction_winner1:[AuctionId]BidId, auction_prep1:[AuctionId]bool, auction_active1:[AuctionId]bool, auction_closed1:[AuctionId]bool, bids1:[BidId]bool, bid_auction1:[BidId]AuctionId, bid_amount1:[BidId]int)
requires (forall a:AuctionId :: (0 <= a && a < na) ==> (auction_winner[a] == null) || (auction_winner1[a] == null) || auction_winner[a] == auction_winner1[a]);
requires (forall b:BidId :: (0 <= b && b < nb) ==> bid_auction[b] == bid_auction1[b] && bid_amount[b] == bid_amount1[b]);
requires (forall b, b1:BidId :: (0 <= b && b < nb && 0 <= b1 && b1 < nb && bid_auction[b] == bid_auction[b1] && b1 != b) ==> bid_amount[b] != bid_amount[b1]);
requires (forall a:AuctionId :: (0 <= a && a < na && auctions[a] && auction_closed[a]) ==> ((forall b, b1:BidId :: (0 <= b && b < nb && 0 <= b1 && b1 < nb && b1 == auction_winner[a] && b != auction_winner[a] && bids[b] && bids[b1] && bid_auction[b1] == a && bid_auction[b] == a) ==> bid_amount[b] < bid_amount[b1]) && (forall b, b1:BidId :: (0 <= b && b < nb && 0 <= b1 && b1 < nb && b1 == auction_winner[a] && b != auction_winner[a] && bids1[b] && bids1[b1] && bid_auction1[b] == a && bid_auction1[b1] == a) ==> bid_amount1[b] < bid_amount1[b1])));
requires (forall a:AuctionId :: (0 <= a && a < na && auctions1[a] && auction_closed1[a]) ==> ((forall b, b1:BidId :: (0 <= b && b < nb && 0 <= b1 && b1 < nb && b1 == auction_winner1[a] && b != auction_winner1[a] && bids[b] && bids[b1] && bid_auction[b1] == a && bid_auction[b] == a) ==> bid_amount[b] < bid_amount[b1]) && (forall b, b1:BidId :: (0 <= b && b < nb && 0 <= b1 && b1 < nb && b1 == auction_winner1[a] && b != auction_winner1[a] && bids1[b] && bids1[b1] && bid_auction1[b] == a && bid_auction1[b1] == a) ==> bid_amount1[b] < bid_amount1[b1])));
modifies auctions, auction_prep, auction_active, auction_closed, auction_winner, bids, bid_auction, bid_amount;

ensures (forall a:AuctionId :: (0 <= a && a < na) ==> auctions[a] == (old(auctions)[a] || auctions1[a]));
ensures (forall a:AuctionId :: (0 <= a && a < na) ==> (auction_prep[a] == (old(auction_prep)[a] || auction_prep1[a])) && (auction_active[a] == (old(auction_active)[a] || auction_active1[a])) && (auction_closed[a] == (old(auction_closed)[a] || auction_closed1[a])));
ensures (forall a:AuctionId :: (0 <= a && a < na) ==> (if (old(auction_winner)[a] == null) then (auction_winner[a] == auction_winner1[a]) else (auction_winner[a] == old(auction_winner)[a])));
ensures (forall b:BidId :: (0 <= b && b < nb) ==> bids[b] == (old(bids)[b] || bids1[b]));
ensures (forall b:BidId :: (0 <= b && b < nb) ==> bid_auction[b] == old(bid_auction)[b] && bid_amount[b] == old(bid_amount)[b]);
{
    var a, b:int;
    var temp_auctions:[AuctionId]bool;
    var temp_auction_prep:[AuctionId]bool;
    var temp_auction_active:[AuctionId]bool;
    var temp_auction_closed:[AuctionId]bool;
    var temp_auction_winner:[AuctionId]BidId;
    var temp_bids:[BidId]bool;
    var temp_bid_auction:[BidId]AuctionId;
    var temp_bid_amount:[BidId]int;
    a:=0;
    b:=0;
    temp_auctions := auctions;
    temp_auction_prep := auction_prep;
    temp_auction_active := auction_active;
    temp_auction_closed := auction_closed;
    temp_auction_winner := auction_winner;
    temp_bids := bids;
    temp_bid_auction := bid_auction;
    temp_bid_amount := bid_amount;
    //auctions, auction_status, auction_winner
    while(a<na)
    invariant(0<=a && a <=na);
    invariant(forall i:int :: (0<=i && i<a) ==> auctions[i] == (old(auctions)[i] || auctions1[i]));
    invariant(forall i:int :: (a<i && i<na) ==> auctions[i] == old(auctions)[i]);
    invariant(forall i:int :: (0<=i && i<a) ==> ((auction_prep[i] == (old(auction_prep)[i] || auction_prep1[i])) && (auction_active[i] == (old(auction_active)[i] || auction_active1[i])) && (auction_closed[i] == (old(auction_closed)[i] || auction_closed1[i]))));
    invariant(forall i:int :: (a<i && i<na) ==> ((auction_prep[i] == old(auction_prep)[i]) && (auction_active[i] == old(auction_active)[i]) && (auction_closed[i] == old(auction_closed)[i])));
    invariant(forall i:int :: (0<=i && i<a) ==> if (auction_winner1[i] == null) then auction_winner[i] == old(auction_winner)[i] else auction_winner[i] == auction_winner1[i]);
    invariant(forall i:int :: (a<i && i<na) ==> auction_winner[i] == old(auction_winner)[i]);
    {
        auctions[a]:= temp_auctions[a] || auctions1[a];
        auction_closed[a] := (temp_auction_closed[a] || auction_closed1[a]);
        auction_active[a] := (temp_auction_active[a] || auction_active1[a]);
        auction_prep[a] := (temp_auction_prep[a] || auction_prep1[a]);
        if (auction_winner1[a] == null) {
            auction_winner[a] := temp_auction_winner[a];
        }  else {
            auction_winner[a] := auction_winner1[a];
        }
        a := a + 1;
    }
    //bids, bid_auction, bid_amount
    while(b<nb)
    invariant (0 <= b && b <= nb);
    invariant(forall i:int:: (0<=i && i <b) ==> bids[i] == (old(bids)[i] || bids1[i]));
    invariant (forall i:int :: (b<i && i < nb) ==> bids[i] == old(bids)[i]);
    invariant (forall i:BidId :: (0 <= i && i < nb) ==> bid_auction[i] == old(bid_auction)[i] && bid_amount[i] == old(bid_amount)[i]);
    {
        bids[b] := temp_bids[b] || bids1[b];
        bid_auction[b] := temp_bid_auction[b];
        bid_amount[b] := temp_bid_amount[b];
        b := b + 1;
    }
}
