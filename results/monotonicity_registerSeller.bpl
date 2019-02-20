type UserId=int;
type AuctionId=int;
type ProductId=int;
type LotId=int;
type BidId=int;
type State;

const unique prep:State;
const unique active:State;
const unique closed:State;
axiom(forall s:State :: s == prep || s == active || s == closed);

const nu:int;
axiom 0 < nu;
const na:int;
axiom 0 < na;
const np:int;
axiom 0 < np;
const nl:int;
axiom 0 < nl;
const nb:int;
axiom 0 < nb;

const unique null:UserId;

var buyers:[UserId]bool;
var sellers:[UserId]bool;
var products:[ProductId]bool;
var auctions:[AuctionId]bool;
var auction_seller:[AuctionId]UserId;
var auction_status:[AuctionId]State; 
var auction_winner:[AuctionId]UserId;
var lots:[LotId]bool;
var lot_auction:[LotId]AuctionId;
var lot_product:[LotId]ProductId;
var bids:[BidId]bool;
var bid_auction:[BidId]AuctionId;
var bid_buyer:[BidId]UserId;
var bid_amount:[BidId]int;

//@gteq
function gteq(buyers1:[UserId]bool, sellers1:[UserId]bool, products1:[ProductId]bool, auctions1:[AuctionId]bool, auction_seller1:[AuctionId]UserId, auction_winner1:[AuctionId]UserId, auction_status1:[AuctionId]State, lots1:[LotId]bool, lot_auction1:[LotId]AuctionId, lot_product1:[LotId]ProductId, bids1:[BidId]bool, bid_auction1:[BidId]AuctionId, bid_buyer1:[BidId]UserId, bid_amount1:[BidId]int, buyers2:[UserId]bool, sellers2:[UserId]bool, products2:[ProductId]bool, auctions2:[AuctionId]bool, auction_seller2:[AuctionId]UserId, auction_winner2:[AuctionId]UserId, auction_status2:[AuctionId]State, lots2:[LotId]bool, lot_auction2:[LotId]AuctionId, lot_product2:[LotId]ProductId, bids2:[BidId]bool, bid_auction2:[BidId]AuctionId, bid_buyer2:[BidId]UserId, bid_amount2:[BidId]int) returns(bool)
{
    (forall b:UserId :: (0 <= b && b < nu && !buyers1[b]) ==> !buyers2[b]) 
    && (forall s:UserId :: (0<= s && s < nu && !sellers1[s]) ==> !sellers2[s]) 
    && (forall p:ProductId :: (0 <= p && p < np && !products1[p]) ==> !products2[p]) 
    && (forall a:AuctionId :: (0<= a && a < na && !auctions1[a]) ==> !auctions2[a]) 
    && (forall a:AuctionId :: (0<=a && a<na && auction_seller1[a] == null) ==> auction_seller2[a] == null) 
    && (forall a:AuctionId :: (0<=a && a<na)==> ((auction_status1[a] == prep ==> auction_status2[a] == prep) || (auction_status1[a] == active ==> (auction_status2[a] == prep || auction_status2[a] == active)) || (auction_status1[a] == closed ==> (auction_status2[a] == active || auction_status2[a] == closed || auction_status2[a] == prep)))) 
    && (forall a:AuctionId :: (0<=a && a<na)==> ((auction_winner1[a] == null ==> auction_winner2[a] == null) || (auction_winner1[a] == auction_winner2[a]))) 
    && (forall l:LotId :: (0<=l && l<nl && !lots1[l]) ==> !lots2[l]) 
    && (forall b:BidId :: (0<=b && b<nb && !bids1[b]) ==> !bids2[b])
}
//@invariant
function inv(buyers:[UserId]bool, sellers:[UserId]bool, products:[ProductId]bool, auctions:[AuctionId]bool, auction_seller:[AuctionId]UserId, auction_status:[AuctionId]State, auction_winner:[AuctionId]UserId, lots:[LotId]bool, lot_auction:[LotId]AuctionId, lot_product:[LotId]ProductId, bids:[BidId]bool, bid_auction:[BidId]AuctionId, bid_buyer:[BidId]UserId, bid_amount:[BidId]int) returns(bool)
{
    (forall a:AuctionId :: (0 <= a && a < na && auctions[a]) ==> (sellers[auction_seller[a]] && (auction_winner[a] == null || buyers[auction_winner[a]]))) 
    && (forall l:LotId :: (0 <= l && l < nl && lots[l] ==> auctions[lot_auction[l]] && products[lot_product[l]])) 
    && (forall b:BidId :: (0 <= b && b < nb && bids[b]) ==> (auctions[bid_auction[b]] && buyers[bid_buyer[b]] && bid_amount[b] >= 0)) 
    && (forall a:AuctionId :: (0 <= a && a < na && auctions[a] && auction_status[a] == active) ==> ((exists l:LotId :: lots[l] && lot_auction[l] == a) && auction_winner[a] == null)) 
    && (forall a:AuctionId :: (0 <= a && a < na && auctions[a] && auction_status[a] == prep) ==> (!(exists b:BidId :: 0 <= b && b < nb && bids[b] && bid_auction[b] == a) && auction_winner[a] == null)) 
    && (forall a:AuctionId :: (0 <= a && a < na && auctions[a] && auction_status[a] == closed) ==> auction_winner[a] != null && (exists b:BidId :: 0 <= b && b < nb && bids[b] && bid_auction[b] == a && bid_buyer[b] == auction_winner[a] && (forall b1:BidId :: 0 <= b1 && b1 < nb && b != b1 && (bid_auction[b1] != a || bid_amount[b1] < bid_amount[b]))))
}
//@merge
//procedure merge(buyers1:[UserId]bool, sellers1:[UserId]bool, products1:[ProductId]bool, auctions1:[AuctionId]bool, auction_seller1:[AuctionId]UserId, auction_winner1:[AuctionId]UserId, auction_status1:[AuctionId]State, lots1:[LotId]bool, lot_auction1:[LotId]AuctionId, lot_product1:[LotId]ProductId, bids1:[BidId]bool, bid_auction1:[BidId]AuctionId, bid_buyer1:[BidId]UserId, bid_amount1:[BidId]int)
////precondition states that either promoters and winners are null or same
//requires (forall a:AuctionId :: (0 <= a && a < na) ==> (auction_seller[a] == null) || (auction_seller1[a] == null) || auction_seller[a] == auction_seller1[a]);
//requires (forall a:AuctionId :: (0 <= a && a < na) ==> (auction_winner[a] == null) || (auction_winner1[a] == null) || auction_winner[a] == auction_winner1[a]);
//requires (forall l:LotId :: (0 <= l && l < nl) ==> lot_auction[l] == lot_auction1[l] && lot_product[l] == lot_product1[l]);
//requires (forall b:BidId :: (0 <= b && b < nb) ==> bid_auction[b] == bid_auction1[b] && bid_buyer[b] == bid_buyer1[b] && bid_amount[b] == bid_amount1[b]);
//
//modifies buyers, sellers, products, auctions, auction_seller, auction_status, auction_winner, lots, lot_auction, lot_product, bids, bid_auction, bid_buyer, bid_amount;
//
//ensures (forall b:UserId :: (0 <= b && b < nu) ==> buyers[b] == (old(buyers)[b] || buyers1[b]));
//ensures (forall s:UserId :: (0 <= s && s < nu) ==> sellers[s] == (old(sellers)[s] || sellers1[s]));
//ensures (forall p:ProductId :: (0 <= p && p < np) ==> products[p] == (old(products)[p] || products1[p]));
//ensures (forall a:AuctionId :: (0 <= a && a < na) ==> auctions[a] == (old(auctions)[a] || auctions1[a]));
//ensures (forall a:AuctionId :: (0 <= a && a < na) ==> (if (old(auction_seller)[a] == null) then (auction_seller[a] == auction_seller1[a]) else (auction_seller[a] == old(auction_seller)[a])));
//ensures (forall a:AuctionId :: (0 <= a && a < na) ==> if (old(auction_status)[a] == closed || auction_status1[a] == closed) then (auction_status[a] == closed) else (if (old(auction_status)[a] == active || auction_status1[a] == active) then (auction_status[a] == active) else auction_status[a] == prep));
//ensures (forall a:AuctionId :: (0 <= a && a < na) ==> (if (old(auction_winner)[a] == null) then (auction_winner[a] == auction_winner1[a]) else (auction_winner[a] == old(auction_winner)[a])));
//ensures (forall l:LotId :: (0 <= l && l < nl) ==> lots[l] == (old(lots)[l] || lots1[l]));
//ensures (forall l:LotId :: (0 <= l && l < nl) ==> lot_auction[l] == old(lot_auction)[l] && lot_product[l] == old(lot_product)[l]);
//ensures (forall b:BidId :: (0 <= b && b < nb) ==> bids[b] == (old(bids)[b] || bids1[b]));
//ensures (forall b:BidId :: (0 <= b && b < nb) ==> bid_auction[b] == old(bid_auction)[b] && bid_buyer[b] == old(bid_buyer)[b] && bid_amount[b] == old(bid_amount)[b]);
////ensures (forall a:AuctionId, b:UserId :: if old(bid)[a][b] > bid1[a][b] then (bid[a][b] == old(bid)[a][b]) else (bid[a][b] == bid1[a][b]));
//{
//    var u, p, a, l, b:int;
//    var temp_buyers:[UserId]bool;
//    var temp_sellers:[UserId]bool;
//    var temp_products:[ProductId]bool;
//    var temp_auctions:[AuctionId]bool;
//    var temp_auction_seller:[AuctionId]UserId;
//    var temp_auction_status:[AuctionId]State;
//    var temp_auction_winner:[AuctionId]UserId;
//    var temp_lots:[LotId]bool;
//    var temp_lot_auction:[LotId]AuctionId;
//    var temp_lot_product:[LotId]ProductId;
//    var temp_bids:[BidId]bool;
//    var temp_bid_auction:[BidId]AuctionId;
//    var temp_bid_buyer:[BidId]UserId;
//    var temp_bid_amount:[BidId]int;
//    u:=0;
//    p:=0;
//    a:=0;
//    l:=0;
//    b:=0;
//    temp_buyers := buyers;
//    temp_sellers := sellers;
//    temp_products := products;
//    temp_auctions := auctions;
//    temp_auction_seller := auction_seller;
//    temp_auction_status := auction_status;
//    temp_auction_winner := auction_winner;
//    temp_lots := lots;
//    temp_lot_auction := lot_auction;
//    temp_lot_product := lot_product;
//    temp_bids := bids;
//    temp_bid_auction := bid_auction;
//    temp_bid_buyer := bid_buyer;
//    temp_bid_amount := bid_amount;
//    //buyers & sellers
//    while(u < nu)
//    invariant (0 <= u && u <= nu);
//    invariant (forall i:int:: (0<=i && i <u) ==> buyers[i] == (old(buyers)[i] || buyers1[i]));
//    invariant (forall i:int:: (u<=i && i<nu) ==> buyers[i] == old(buyers)[i]);
//    invariant (forall i:int:: (0<=i && i <u) ==> sellers[i] == (old(sellers)[i] || sellers1[i]));
//    invariant (forall i:int:: (u<=i && i<nu) ==> sellers[i] == old(sellers)[i]);
//    {
//        buyers[u] := temp_buyers[u] || buyers1[u];
//        sellers[u] := temp_sellers[u] || sellers1[u];
//        u := u + 1;
//    }
//    //products 
//    while(p<np)
//    invariant(0<=p && p <= np);
//    invariant (forall i:int :: (0 <= i && i < p) ==> products[i] == (old(products)[i] || products1[i]));
//    invariant (forall i:int :: (p<i && i<np) ==> products[i] == old(products)[i]);
//    {
//        products[p]:= temp_products[p] || products1[p];
//        p:= p+1;
//    }
//    //auctions, auction_seller, auction_status, auction_winner
//    while(a<na)
//    invariant(0<=a && a <=na);
//    invariant(forall i:int :: (0<=i && i<a) ==> auctions[i] == (old(auctions)[i] || auctions1[i]));
//    invariant(forall i:int :: (a<i && i<na) ==> auctions[i] == old(auctions)[i]);
//    invariant(forall i:int :: (0<=i && i<a) ==> if (auction_seller1[i] == null) then auction_seller[i] == old(auction_seller)[i] else auction_seller[i] == auction_seller1[i]);
//    invariant(forall i:int :: (a<i && i<na) ==> auction_seller[i] == old(auction_seller)[i]);
//    invariant(forall i:int :: (0<=i && i<a) ==> if (old(auction_status)[i] == closed || auction_status1[i] == closed) then auction_status[i] == closed else (if ((old(auction_status)[i] == active || auction_status1[i] == active) && (old(auction_status)[i] != closed || auction_status1[i] == closed)) then auction_status[i] == active else auction_status[i] == prep));
//    invariant(forall i:int :: (a<i && i<na) ==> auction_status[i] == old(auction_status)[i]);
//    invariant(forall i:int :: (0<=i && i<a) ==> if (auction_winner1[i] == null) then auction_winner[i] == old(auction_winner)[i] else auction_winner[i] == auction_winner1[i]);
//    invariant(forall i:int :: (a<i && i<na) ==> auction_winner[i] == old(auction_winner)[i]);
//    {
//        auctions[a]:= temp_auctions[a] || auctions1[a];
//        if (auction_seller1[a] == null) {
//            auction_seller[a] := temp_auction_seller[a];
//        }  else {
//            auction_seller[a] := auction_seller1[a];
//        }
//        if (temp_auction_status[a] == closed || auction_status1[a] == closed){
//            auction_status[a] := closed;
//        } else {
//            if (temp_auction_status[a] == active || auction_status1[a] == active){
//                auction_status[a] := active;
//            } else {
//                auction_status[a] := prep;
//            }
//        }
//        if (auction_winner1[a] == null) {
//            auction_winner[a] := temp_auction_winner[a];
//        }  else {
//            auction_winner[a] := auction_winner1[a];
//        }
//        a := a + 1;
//    }
//    //lots, lot_auction, lot_product
//    while(l<nl)
//    invariant (0 <= l && l <= nl);
//    invariant(forall i:int:: (0<=i && i <l) ==> lots[i] == (old(lots)[i] || lots1[i]));
//    invariant (forall i:int :: (l<i && i < nl) ==> lots[i] == old(lots)[i]);
//    invariant (forall i:int :: (0<=i && i <nl) ==> lot_auction[i] == old(lot_auction)[i] && lot_product[i] == old(lot_product)[i]);
//    {
//        lots[l] := temp_lots[l] || lots1[l];
//        lot_auction[l] := temp_lot_auction[l];
//        lot_product[l] := temp_lot_product[l];
//        l := l + 1;
//    }
//    //bids, bid_auction, bid_buyer, bid_amount
//    while(b<nb)
//    invariant (0 <= b && b <= nb);
//    invariant(forall i:int:: (0<=i && i <b) ==> bids[i] == (old(bids)[i] || bids1[i]));
//    invariant (forall i:int :: (b<i && i < nb) ==> bids[i] == old(bids)[i]);
//    invariant (forall i:BidId :: (0 <= i && i < nb) ==> bid_auction[i] == old(bid_auction)[i] && bid_buyer[i] == old(bid_buyer)[i] && bid_amount[i] == old(bid_amount)[i]);
//    {
//        bids[b] := temp_bids[b] || bids1[b];
//        bid_auction[b] := temp_bid_auction[b];
//        bid_buyer[b] := temp_bid_buyer[b];
//        bid_amount[b] := temp_bid_amount[b];
//        b := b + 1;
//    }
//}

//all operations to go here!!!!
//registerSeller
//procedure registerSeller(sllr:UserId)
//requires (sellers[sllr] == false);
////requires !(exists p:ProductId :: products[p][sllr] == true);
////requires !(exists a:AuctionId :: promoter[a] == sllr);
//modifies sellers;
//ensures (forall s:UserId :: (s == sllr ==> sellers[s] == true) && (s != sllr ==> sellers[s] == old(sellers)[s]));
//{
//    sellers[sllr] := true;
//}
//registerBuyer
//addProduct
//createAuction
//addToLot
//startAuction
//addBid
//closeAuction

procedure registerSeller(sllr:UserId)
modifies sellers;
requires ((sellers[sllr] == false));
ensures ((forall s:UserId :: (s == sllr ==> sellers[s] == true) && (s != sllr ==> sellers[s] == old(sellers)[s])));

{
sellers[sllr] := true;
}
const _sllr:UserId;
procedure monotonicity_registerSeller()
modifies sellers;
ensures gteq(buyers,sellers,products,auctions,auction_seller,auction_winner,auction_status,lots,lot_auction,lot_product,bids,bid_auction,bid_buyer,bid_amount,old(buyers),old(sellers),old(products),old(auctions),old(auction_seller),old(auction_winner),old(auction_status),old(lots),old(lot_auction),old(lot_product),old(bids),old(bid_auction),old(bid_buyer),old(bid_amount));
{
assume (sellers[_sllr] == false);
call registerSeller(_sllr);
}