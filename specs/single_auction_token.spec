type ReplicaId = int;

type BidId = int;
type Bfield b;

const unique placed:Bfield bool;
const unique amount:Bfield int;

type Bid = [BidId]<b>[Bfield b] b;

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

const invalid:bv2;
const active:bv2;
const closed:bv2;
axiom(invalid == 0bv2);
axiom(active == 1bv2);
axiom(closed == 2bv2);
axiom(forall status:bv2 :: status == invalid || status == active || status == closed);

var status:bv2;
var winner:BidId;
var bids:Bid;
var token:[ReplicaId]bool;

function get_winner(bids:Bid) returns(BidId);
axiom(forall bids:Bid :: 0 <= get_winner(bids) && get_winner(bids) < nb && bids[get_winner(bids)][placed] && (forall b:BidId :: (0 <= b && b < nb && b != get_winner(bids) && bids[b][placed] && bids[get_winner(bids)][placed]) ==> ((bids[b][amount] < bids[get_winner(bids)][amount]) || (bids[b][amount] == bids[get_winner(bids)][amount] && get_winner(bids) < b))));
function token_released(token:[ReplicaId]bool) returns(bool)
{
    !(exists r:ReplicaId:: 0 <= r && r < nr && token[r])
}
function is_highest_bid(bids:Bid, winner:BidId) returns(bool)
{
    (forall b:BidId :: (0 <= b && b < nb && bids[b][placed] && winner != b) ==> ((bids[b][amount] < bids[winner][amount]) || (bids[b][amount] == bids[winner][amount] && winner < b)))
}

axiom(forall bids:Bid :: !bids[null][placed]);
//initialisation
axiom (forall status:bv2, winner:BidId, bids:Bid :: (status == invalid) ==> (winner == null && !(exists b:BidId :: bids[b][placed] && bids[b][amount] > 0)));
axiom (forall status:bv2, token:[ReplicaId]bool, r:ReplicaId :: (0 <= r && r < nr && status == invalid) ==> token[r]);

@gteq
function gteq(status1:bv2, winner1:BidId, bids1:Bid, token1:[ReplicaId]bool, status2:bv2, winner2:BidId, bids2:Bid, token2:[ReplicaId]bool) returns(bool)
{
    bv2uge(status1, status2) && (winner1 == null ==> winner2 == null) && (winner2 != null ==> winner1 != null) && (forall b:BidId :: (0 <= b && b < nb) ==> ((!bids1[b][placed] ==> !bids2[b][placed]) && (bids2[b][placed] ==> bids1[b][placed]))) && (forall r:ReplicaId :: (0 <= r && r < nr) ==> ((!token2[r] ==> !token1[r]) && (token1[r] ==> token2[r])))
}

@invariant
function inv(status:bv2, winner:BidId, bids:Bid, token:[ReplicaId]bool) returns(bool)
{
    (forall b:BidId :: (0 <= b && b < nb && bids[b][placed]) ==> (bv2uge(status, active) && bids[b][amount] > 0))
    && (bv2uge(active, status) ==> winner == null)
    && (status == closed ==> (exists b:BidId :: 0 <= b && b < nb && b != null && bids[b][placed] && winner == b && is_highest_bid(bids, winner)))
    && (forall r:ReplicaId :: (status == closed && 0 <= r && r < nr) ==> !token[r])
}

@merge
procedure merge(status1:bv2, winner1:BidId, bids1:Bid, token1:[ReplicaId]bool)
requires (winner == winner1) || (winner == null) || (winner1 == null);
requires (forall b:BidId :: (0 <= b && b < nb) ==> (bids[b][amount] == bids1[b][amount]));
requires ((status == closed) ==> (is_highest_bid(bids1, winner) && is_highest_bid(bids, winner)));
requires ((status1 == closed) ==> (is_highest_bid(bids, winner1) && is_highest_bid(bids1, winner1)));
requires (token[me] ==> token1[me]);
requires ((token_released(token)) ==> (winner == winner1 || winner1 == null));
requires (!token_released(token) ==> (winner == null && winner1 == null));
requires ((forall b:BidId :: (token_released(token) && 0 <= b && b < nb && !bids[b][placed]) ==> !bids1[b][placed]));
requires ((forall b:BidId :: ((forall r:ReplicaId :: (0 <= r && r < nr && r != me) ==> !token[r]) && 0 <= b && b < nb && !bids[b][placed]) ==> !bids1[b][placed]));

modifies status, winner, bids, token;

ensures (status == bv2max(old(status), status1)) && (winner == (if old(winner) != null then old(winner) else winner1));
ensures (forall b:BidId :: (0 <= b && b < nb) ==> ((bids[b][placed] == (old(bids)[b][placed] || bids1[b][placed])) && (bids[b][amount] == old(bids)[b][amount])));
ensures (forall r:ReplicaId :: (0 <= r && r < nr) ==> (token[r] == (old(token)[r] && token1[r])));
{
    var b, r:int;
    var temp_status:bv2;
    var temp_winner:BidId;
    var temp_bids:Bid;
    var temp_token:[ReplicaId]bool;
    temp_status := status;
    temp_winner := winner;
    temp_bids := bids;
    temp_token := token;
    b:=0;
    status := bv2max(temp_status, status1);
    if (temp_winner != null)
    {
        winner := temp_winner;
    }
    else
    {
        winner := winner1;
    }

    while (b < nb)
    invariant(0 <= b && b <= nb);
    invariant(forall i:int :: (0<=i && i<b) ==> bids[i][placed] == (temp_bids[i][placed] || bids1[i][placed]));
    invariant(forall i:int :: (b<i && i<nb) ==> bids[i][placed] == temp_bids[i][placed]);
    invariant(forall i:int :: (0<=i && i<b) ==> bids[i][amount] == temp_bids[i][amount]);
    invariant(forall i:int :: (b<i && i<nb) ==> bids[i][amount] == temp_bids[i][amount]);
    {
        bids[b][placed] := temp_bids[b][placed] || bids1[b][placed];
        bids[b][amount] := temp_bids[b][amount];
        b := b + 1;
    }
    r := 0;
    while (r < nr)
    invariant(0 <= r && r <= nr);
    invariant(forall j:int :: (0 <= j && j < r) ==> (token[j] == (temp_token[j] && token1[j])));
    invariant(forall j:int :: (r <= j && j < nr) ==> (token[j] == temp_token[j]));
    {
        token[r] := (temp_token[r] && token1[r]);
        r := r + 1;
    }
}

procedure startAuction()
requires status == invalid && winner == null;
requires (!token_released(token));
modifies status;
ensures (status == active);
{
    status := active;
}

procedure placeBid(bid_identifier:BidId, value:int)
requires 0 <= bid_identifier && bid_identifier < nb && !bids[bid_identifier][placed] && bids[bid_identifier][amount] == value;
requires status == active && winner == null;
requires value > 0;
requires token[me];
modifies bids;
ensures (forall b:BidId :: ((0 <= b && b < nb && b == bid_identifier) ==> (bids[b][placed] && bids[b][amount] == old(bids)[b][amount])) && ((0 <= b && b < nb && b != bid_identifier) ==> (bids[b][placed] == old(bids)[b][placed] && bids[b][amount] == old(bids)[b][amount])));
{
    bids[bid_identifier][placed] := true;
    bids[bid_identifier][amount] := value;
}

procedure closeAuction()
requires (status == active && winner == null);
requires (exists b:BidId :: 0 <= b && b < nb && bids[b][placed] && bids[b][amount] > 0);
requires (forall r:ReplicaId :: (0 <= r && r < nr) ==> !token[r]);
modifies status, winner;
ensures (status == closed && winner == get_winner(bids));
{
    status := closed;
    winner := get_winner(bids);
}

procedure releaseToken()
requires (token[me]);
modifies token;
ensures (!token[me]);
ensures (forall r:ReplicaId :: (0 <= r && r < nr && r != me) ==> (token[r] == old(token)[r]));
{
    token[me] := false;
}