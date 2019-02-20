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

axiom(forall a:AuctionId, auctions, auction_prep, auction_active, auction_closed:[AuctionId]bool, auction_winner:[AuctionId]BidId :: (0 <= a && a < na && !auctions[a]) ==> (!auction_prep[a] && !auction_active[a] && !auction_closed[a] && auction_winner[a] == null));

//@gteq
function gteq(auctions1:[AuctionId]bool, auction_winner1:[AuctionId]BidId, auction_prep1:[AuctionId]bool, auction_active1:[AuctionId]bool, auction_closed1:[AuctionId]bool, bids1:[BidId]bool, bid_auction1:[BidId]AuctionId, bid_amount1:[BidId]int, auctions2:[AuctionId]bool, auction_winner2:[AuctionId]BidId, auction_prep2:[AuctionId]bool, auction_active2:[AuctionId]bool, auction_closed2:[AuctionId]bool, bids2:[BidId]bool, bid_auction2:[BidId]AuctionId, bid_amount2:[BidId]int) returns(bool)
{
    (forall a:AuctionId :: (0<= a && a < na && !auctions1[a]) ==> !auctions2[a]) 
    && (forall a:AuctionId :: (0<=a && a<na)==> ((!auction_prep1[a] ==> !auction_prep2[a]) && (!auction_active1[a] ==> !auction_active2[a] ) && (!auction_closed1[a] ==> !auction_closed2[a]))) 
    && (forall a:AuctionId :: (0<=a && a<na)==> ((auction_winner1[a] == null ==> auction_winner2[a] == null) || (auction_winner1[a] == auction_winner2[a]))) 
    && (forall b:BidId :: (0<=b && b<nb && !bids1[b]) ==> !bids2[b])
}
//@invariant
function inv(auctions:[AuctionId]bool, auction_prep:[AuctionId]bool, auction_active:[AuctionId]bool, auction_closed:[AuctionId]bool, auction_winner:[AuctionId]BidId, bids:[BidId]bool, bid_auction:[BidId]AuctionId, bid_amount:[BidId]int) returns(bool)
{
    (forall b:BidId :: (0 <= b && b < nb && bids[b]) ==> ((exists a:AuctionId :: 0 <= a && a < na && auctions[a] && bid_auction[b] == a) && bid_amount[b] >= 0)) 
    && (forall a:AuctionId :: (0 <= a && a < na && auctions[a] && !auction_closed[a] && (auction_active[a] || auction_prep[a])) ==> auction_winner[a] == null)
    && (forall a:AuctionId :: (0 <= a && a < na && auctions[a] && !auction_active[a]) ==> (forall b:BidId :: (0 <= b && b < nb && bid_auction[b] == a) ==> !bids[b])) 
    && (forall a:AuctionId :: (0 <= a && a < na && auctions[a] && auction_closed[a]) ==> auction_winner[a] != null && (exists b:BidId :: 0 <= b && b < nb && bids[b] && bid_auction[b] == a && (forall b1:BidId :: (0 <= b1 && b1 < nb && b != b1 && bids[b1] && bid_auction[b1] == a) ==> ((bid_amount[b1] < bid_amount[b]) || (bid_amount[b1] == bid_amount[b] && b1 < b)))))    
    && (forall a:AuctionId :: (0 <= a && a < na && auction_closed[a] ==> (auction_prep[a] && auction_active[a])))
    && (forall a:AuctionId :: (0 <= a && a < na && auction_active[a] ==> auction_prep[a]))

}
//(forall a:AuctionId :: (0 <= a && a < na && auctions[a]) ==> (auction_winner[a] == null || (auction_status[a] == closed && (exists b:BidId :: 0 <= b && b < nb && bids[b] && bid_auction[b] == a && auction_winner[a] == b)))) 
    //&& (forall a:AuctionId :: (0 <= a && a < na && auctions[a] && auction_status[a] == closed) ==> 
    //     auction_winner[a] != null && bids[auction_winner[a]] && bid_auction[auction_winner[a]] == a && 
    //     (forall b:BidId :: (0 <= b && b < nb && bids[b] && b != auction_winner[a] && bid_auction[b] == a) ==> bid_amount[b] < bid_amount[auction_winner[a]]))

//createAuction
//procedure createAuction(identifier:AuctionId)
//requires (0 <= identifier && identifier < na);
//requires auctions[identifier] == false && !auction_prep[identifier] && !auction_active[identifier] && !auction_closed[identifier] && auction_winner[identifier] == null;
//requires (forall b:BidId :: (0 <= b && b < nb && bid_auction[b] == identifier) ==> (bids[b] == false));
//modifies auctions, auction_prep, auction_winner;
//ensures (forall a:AuctionId :: ((0 <= a && a < na && a == identifier) ==> (auctions[a] == true && auction_prep[a] && auction_winner[a] == null)) && ((0 <= a && a < na && a != identifier) ==> (auctions[a] == old(auctions)[a] && auction_prep[a] == old(auction_prep)[a] && auction_winner[a] == old(auction_winner)[a])));
//{
//    auctions[identifier] := true;
//    auction_prep[identifier] := true;
//    auction_winner[identifier] := null;
//}
//startAuction
//procedure startAuction(identifier:AuctionId)
//requires (0 <= identifier && identifier < na);
//requires auctions[identifier] == true && auction_prep[identifier] && !auction_active[identifier] && !auction_closed[identifier];
//modifies auction_active;
//ensures (forall a:AuctionId :: ((0 <= a && a < na && a == identifier) ==> auction_active[a]) && ((0 <= a && a < na && a != identifier) ==> auction_active[a] == old(auction_active)[a]));
//{
//    auction_active[identifier] := true;
//}
//addBid
//procedure addBid(bid_identifier:BidId, auction_identifier:AuctionId, value:int)
//requires auctions[auction_identifier] == true;
//requires (0 <= auction_identifier && auction_identifier < na);
//requires (0 <= bid_identifier && bid_identifier < nb);
//requires bids[bid_identifier] == false && bid_auction[bid_identifier] == auction_identifier && bid_amount[bid_identifier] == value;
//requires auction_prep[auction_identifier] && auction_active[auction_identifier] && !auction_closed[auction_identifier];
//requires value > 0;
//modifies bids, bid_auction, bid_amount;
//ensures (forall b:BidId :: ((0 <= b && b < nb && b == bid_identifier) ==> bids[b] == true && bid_auction[b] == auction_identifier && bid_amount[b] == value) && ((0 <= b && b < nb && b != bid_identifier) ==> bids[b] == old(bids)[b] && bid_auction[b] == old(bid_auction)[b] && bid_amount[b] == old(bid_amount)[b]));
//{
//    bids[bid_identifier] := true;
//    bid_auction[bid_identifier] := auction_identifier;
//    bid_amount[bid_identifier] := value;
//}
//closeAuction
//stability test fails for 1 -  in fact should fail :)
//procedure closeAuction(auction_identifier:AuctionId, winning_bid:BidId)
//requires auctions[auction_identifier] == true && auction_winner[auction_identifier] == null;
//requires auction_prep[auction_identifier] && auction_active[auction_identifier] && !auction_closed[auction_identifier];
//requires (0 <= auction_identifier && auction_identifier < na);
//requires winning_bid != null;
//requires (exists b:BidId :: 0 <= b && b < nb && bids[b] == true && bid_auction[b] == auction_identifier);
//requires (0 <= winning_bid && winning_bid < nb && bids[winning_bid] && bid_auction[winning_bid] == auction_identifier && (forall b:BidId :: (0 <= b && b < nb && b != winning_bid && bids[b] == true && bid_auction[b] == auction_identifier) ==> bid_amount[b] < bid_amount[winning_bid]));
//modifies auction_closed, auction_winner;
//ensures (forall a:AuctionId :: ((0 <= a && a < na && a == auction_identifier) ==> auction_closed[a]) && ((0 <= a && a < na && a != auction_identifier) ==> auction_closed[a] == old(auction_closed)[a]));
//ensures (forall a:AuctionId :: ((0 <= a && a < na && a == auction_identifier) ==> auction_winner[a] == winning_bid) && ((0 <= a && a < na && a != auction_identifier) ==> auction_winner[a] == old(auction_winner)[a]));
//{
//    auction_closed[auction_identifier] := true;
//    auction_winner[auction_identifier] := winning_bid;
//}

//safety fails for 1,3,4,5
//@merge
//procedure merge(auctions1:[AuctionId]bool, auction_winner1:[AuctionId]BidId, auction_prep1:[AuctionId]bool, auction_active1:[AuctionId]bool, auction_closed1:[AuctionId]bool, bids1:[BidId]bool, bid_auction1:[BidId]AuctionId, bid_amount1:[BidId]int)
//requires (forall a:AuctionId :: (0 <= a && a < na) ==> (auction_winner[a] == null) || (auction_winner1[a] == null) || auction_winner[a] == auction_winner1[a]);
//requires (forall b:BidId :: (0 <= b && b < nb) ==> bid_auction[b] == bid_auction1[b] && bid_amount[b] == bid_amount1[b]);
////requires (forall a:AuctionId :: auction_status[a] == prep || auction_status[a] == active || auction_status[a] == closed);
////requires (forall a:AuctionId :: auction_status1[a] == prep || auction_status1[a] == active || auction_status1[a] == closed);
//modifies auctions, auction_prep, auction_active, auction_closed, auction_winner, bids, bid_auction, bid_amount;
//
//ensures (forall a:AuctionId :: (0 <= a && a < na) ==> auctions[a] == (old(auctions)[a] || auctions1[a]));
//ensures (forall a:AuctionId :: (0 <= a && a < na) ==> (auction_prep[a] == (old(auction_prep)[a] || auction_prep1[a])) && (auction_active[a] == (old(auction_active)[a] || auction_active1[a])) && (auction_closed[a] == (old(auction_closed)[a] || auction_closed1[a])));
//ensures (forall a:AuctionId :: (0 <= a && a < na) ==> (if (old(auction_winner)[a] == null) then (auction_winner[a] == auction_winner1[a]) else (auction_winner[a] == old(auction_winner)[a])));
//ensures (forall b:BidId :: (0 <= b && b < nb) ==> bids[b] == (old(bids)[b] || bids1[b]));
//ensures (forall b:BidId :: (0 <= b && b < nb) ==> bid_auction[b] == old(bid_auction)[b] && bid_amount[b] == old(bid_amount)[b]);
//{
//    var a, b:int;
//    var temp_auctions:[AuctionId]bool;
//    var temp_auction_prep:[AuctionId]bool;
//    var temp_auction_active:[AuctionId]bool;
//    var temp_auction_closed:[AuctionId]bool;
//    var temp_auction_winner:[AuctionId]BidId;
//    var temp_bids:[BidId]bool;
//    var temp_bid_auction:[BidId]AuctionId;
//    var temp_bid_amount:[BidId]int;
//    a:=0;
//    b:=0;
//    temp_auctions := auctions;
//    temp_auction_prep := auction_prep;
//    temp_auction_active := auction_active;
//    temp_auction_closed := auction_closed;
//    temp_auction_winner := auction_winner;
//    temp_bids := bids;
//    temp_bid_auction := bid_auction;
//    temp_bid_amount := bid_amount;
//    //auctions, auction_status, auction_winner
//    while(a<na)
//    invariant(0<=a && a <=na);
//    invariant(forall i:int :: (0<=i && i<a) ==> auctions[i] == (old(auctions)[i] || auctions1[i]));
//    invariant(forall i:int :: (a<i && i<na) ==> auctions[i] == old(auctions)[i]);
//    invariant(forall i:int :: (0<=i && i<a) ==> ((auction_prep[i] == (old(auction_prep)[i] || auction_prep1[i])) && (auction_active[i] == (old(auction_active)[i] || auction_active1[i])) && (auction_closed[i] == (old(auction_closed)[i] || auction_closed1[i]))));
//    invariant(forall i:int :: (a<i && i<na) ==> ((auction_prep[i] == old(auction_prep)[i]) && (auction_active[i] == old(auction_active)[i]) && (auction_closed[i] == old(auction_closed)[i])));
//    invariant(forall i:int :: (0<=i && i<a) ==> if (auction_winner1[i] == null) then auction_winner[i] == old(auction_winner)[i] else auction_winner[i] == auction_winner1[i]);
//    invariant(forall i:int :: (a<i && i<na) ==> auction_winner[i] == old(auction_winner)[i]);
//    {
//        auctions[a]:= temp_auctions[a] || auctions1[a];
//        auction_closed[a] := (temp_auction_closed[a] || auction_closed1[a]);
//        auction_active[a] := (temp_auction_active[a] || auction_active1[a]);
//        auction_prep[a] := (temp_auction_prep[a] || auction_prep1[a]);
//        if (auction_winner1[a] == null) {
//            auction_winner[a] := temp_auction_winner[a];
//        }  else {
//            auction_winner[a] := auction_winner1[a];
//        }
//        a := a + 1;
//    }
//    //bids, bid_auction, bid_amount
//    while(b<nb)
//    invariant (0 <= b && b <= nb);
//    invariant(forall i:int:: (0<=i && i <b) ==> bids[i] == (old(bids)[i] || bids1[i]));
//    invariant (forall i:int :: (b<i && i < nb) ==> bids[i] == old(bids)[i]);
//    invariant (forall i:BidId :: (0 <= i && i < nb) ==> bid_auction[i] == old(bid_auction)[i] && bid_amount[i] == old(bid_amount)[i]);
//    {
//        bids[b] := temp_bids[b] || bids1[b];
//        bid_auction[b] := temp_bid_auction[b];
//        bid_amount[b] := temp_bid_amount[b];
//        b := b + 1;
//    }
//}

procedure addBid(bid_identifier:BidId, auction_identifier:AuctionId, value:int)
modifies bids, bid_auction, bid_amount;
requires (auctions[auction_identifier] == true);
requires ((0 <= auction_identifier && auction_identifier < na));
requires ((0 <= bid_identifier && bid_identifier < nb));
requires (bids[bid_identifier] == false && bid_auction[bid_identifier] == auction_identifier && bid_amount[bid_identifier] == value);
requires (auction_prep[auction_identifier] && auction_active[auction_identifier] && !auction_closed[auction_identifier]);
requires (value > 0);
ensures ((forall b:BidId :: ((0 <= b && b < nb && b == bid_identifier) ==> bids[b] == true && bid_auction[b] == auction_identifier && bid_amount[b] == value) && ((0 <= b && b < nb && b != bid_identifier) ==> bids[b] == old(bids)[b] && bid_auction[b] == old(bid_auction)[b] && bid_amount[b] == old(bid_amount)[b])));

{
bids[bid_identifier] := true;
    bid_auction[bid_identifier] := auction_identifier;
    bid_amount[bid_identifier] := value;
}
const _bid_identifier:BidId;
const _auction_identifier:AuctionId;
const _value:int;
procedure safety_addBid()
modifies bids, bid_auction, bid_amount;
ensures (forall b:BidId :: (0 <= b && b < nb && bids[b]) ==> ((exists a:AuctionId :: 0 <= a && a < na && auctions[a] && bid_auction[b] == a) && bid_amount[b] >= 0)) 
    && (forall a:AuctionId :: (0 <= a && a < na && auctions[a] && !auction_closed[a] && (auction_active[a] || auction_prep[a])) ==> auction_winner[a] == null)
    && (forall a:AuctionId :: (0 <= a && a < na && auctions[a] && !auction_active[a]) ==> (forall b:BidId :: (0 <= b && b < nb && bid_auction[b] == a) ==> !bids[b])) 
    && (forall a:AuctionId :: (0 <= a && a < na && auctions[a] && auction_closed[a]) ==> auction_winner[a] != null && (exists b:BidId :: 0 <= b && b < nb && bids[b] && bid_auction[b] == a && (forall b1:BidId :: (0 <= b1 && b1 < nb && b != b1 && bids[b1] && bid_auction[b1] == a) ==> ((bid_amount[b1] < bid_amount[b]) || (bid_amount[b1] == bid_amount[b] && b1 < b)))))    
    && (forall a:AuctionId :: (0 <= a && a < na && auction_closed[a] ==> (auction_prep[a] && auction_active[a])))
    && (forall a:AuctionId :: (0 <= a && a < na && auction_active[a] ==> auction_prep[a]));
{
assume inv(auctions,auction_prep,auction_active,auction_closed,auction_winner,bids,bid_auction,bid_amount);
assume auctions[_auction_identifier] == true;
assume (0 <= _auction_identifier && _auction_identifier < na);
assume (0 <= _bid_identifier && _bid_identifier < nb);
assume bids[_bid_identifier] == false && bid_auction[_bid_identifier] == _auction_identifier && bid_amount[_bid_identifier] == _value;
assume auction_prep[_auction_identifier] && auction_active[_auction_identifier] && !auction_closed[_auction_identifier];
assume _value > 0;
call addBid(_bid_identifier, _auction_identifier, _value);
}