type rid = int;
const unique me:rid;
const nr : rid;
axiom 0 < nr;
axiom 0 <= me && me < nr;
type pid = int;
const np : pid;
axiom 0 < np;
type tid = int;
const nt : tid;
axiom 0 < nt;

var players_reg:[pid]bool;
var players_unreg:[pid]bool;
var tourn_reg:[tid]bool;
var tourn_unreg:[tid]bool;
var enrollment:[tid][pid]bool;

@gteq
function gteq(players_reg1:[pid]bool, players_unreg1:[pid]bool, tourn_reg1:[tid]bool, tourn_unreg1:[tid]bool, enrollment1:[tid][pid]bool, players_reg2:[pid]bool, players_unreg2:[pid]bool, tourn_reg2:[tid]bool, tourn_unreg2:[tid]bool, enrollment2:[tid][pid]bool) returns(bool)
{
    (forall p:pid :: (0 <= p && p < np) ==> (players_reg1[p] || !players_reg2[p])) && (forall p:pid :: (0 <= p && p < np) ==> (players_unreg1[p] || !players_unreg2[p])) && (forall t:tid :: (0 <= t && t < nt) ==> (tourn_reg1[t] || !tourn_reg2[t])) && (forall t:tid :: (0 <= t && t < nt) ==> (tourn_unreg1[t] || !tourn_unreg2[t])) && (forall p:pid, t:tid :: (0 <= p && p < np && 0 <= t && t < nt) ==> (enrollment1[t][p] || !enrollment2[t][p]))
}

@invariant
function inv(players_reg:[pid]bool, players_unreg:[pid]bool, tourn_reg:[tid]bool, tourn_unreg:[tid]bool, enrollment:[tid][pid]bool) returns(bool)
{
    (forall p:pid, t:tid :: (0 <= p && p < np && 0 <= t && t < nt && enrollment[t][p]) ==> (players_reg[p] && !players_unreg[p] && tourn_reg[t] && !tourn_unreg[t]))
}

procedure addplayer(p1:pid)
modifies players_reg;
requires 0 <= p1 && p1 < np;
ensures players_reg[p1] && (forall p:pid :: (0 <= p && p < np && p != p1) ==> (players_reg[p] == old(players_reg)[p]));
{
    players_reg[p1] := true;
}

procedure remplayer(p1:pid)
modifies players_unreg;
requires 0 <= p1 && p1 < np;
requires !(exists t:tid :: (0 <= t && t < nt && enrollment[t][p1]));
ensures players_unreg[p1] && (forall p:pid :: (0 <= p && p < np && p != p1) ==> (players_unreg[p] == old(players_unreg)[p]));
{
    players_unreg[p1] := true;
}

procedure addtournament(t1:tid)
modifies tourn_reg;
requires 0 <= t1 && t1 < nt;
ensures tourn_reg[t1] && (forall t:tid :: (0 <= t && t < nt && t != t1) ==> (tourn_reg[t] == old(tourn_reg)[t]));
{
    tourn_reg[t1] := true;
}

procedure remtournament(t1:tid)
modifies tourn_unreg;
requires 0 <= t1 && t1 < nt;
requires !(exists p:pid :: (0 <= p && p < np && enrollment[t1][p]));
ensures tourn_unreg[t1] && (forall t:tid :: (0 <= t && t < nt && t != t1) ==> (tourn_unreg[t] == old(tourn_unreg)[t]));
{
    tourn_unreg[t1] := true;
}

procedure enrol(t1:tid, p1:pid)
modifies enrollment;
requires 0 <= p1 && p1 < np && 0 <= t1 && t1 < nt;
requires players_reg[p1] && !players_unreg[p1];
requires tourn_reg[t1] && !tourn_unreg[t1];
ensures enrollment[t1][p1] && (forall t:tid, p:pid :: (0 <= t && t < nt && 0 <= p && p < np && (t != t1 || p != p1)) ==> (enrollment[t][p] == old(enrollment)[t][p]));
{
    enrollment[t1][p1] := true;
}

@merge
procedure merge(players_reg1:[pid]bool, players_unreg1:[pid]bool, tourn_reg1:[tid]bool, tourn_unreg1:[tid]bool, enrollment1:[tid][pid]bool)
modifies players_reg, players_unreg, tourn_reg, tourn_unreg, enrollment;
requires (forall p:pid, t:tid :: (0 <= p && p < np && 0 <= t && t < nt) ==> (enrollment[t][p] ==> (!players_unreg1[p] && !tourn_unreg1[t])));
requires (forall p:pid, t:tid :: (0 <= p && p < np && 0 <= t && t < nt) ==> (enrollment1[t][p] ==> (!players_unreg[p] && !tourn_unreg[t])));

ensures (forall p:pid :: (0 <= p && p < np) ==> (players_reg[p] == (old(players_reg)[p] || players_reg1[p])));
ensures (forall p:pid :: (0 <= p && p < np) ==> (players_unreg[p] == (old(players_unreg)[p] || players_unreg1[p])));
ensures (forall t:tid :: (0 <= t && t < nt) ==> (tourn_reg[t] == (old(tourn_reg)[t] || tourn_reg1[t])));
ensures (forall t:tid :: (0 <= t && t < nt) ==> (tourn_unreg[t] == (old(tourn_unreg)[t] || tourn_unreg1[t])));
ensures (forall t:tid, p:pid :: (0 <= p && p < np && 0 <= t && t < nt) ==> (enrollment[t][p] == (old(enrollment)[t][p] || enrollment1[t][p])));
{
    var p, t:int;
    var temp_players_reg:[pid]bool;
    var temp_players_unreg:[pid]bool;
    var temp_tourn_reg:[tid]bool;
    var temp_tourn_unreg:[tid]bool;
    var temp_enrollment:[tid][pid]bool;

    p := 0;
    temp_players_reg := players_reg;
    temp_players_unreg := players_unreg;
    while (p < np)
    invariant(0 <= p && p <= np);
    invariant(forall i:int :: (0<=i && i<p) ==> (players_reg[i] == (temp_players_reg[i] || players_reg1[i])));
    invariant(forall i:int :: (p<=i && i<np) ==> (players_reg[i] == temp_players_reg[i]));
    invariant(forall i:int :: (0<=i && i<p) ==> (players_unreg[i] == (temp_players_unreg[i] || players_unreg1[i])));
    invariant(forall i:int :: (p<=i && i<np) ==> (players_unreg[i] == temp_players_unreg[i]));
    {
        players_reg[p] := temp_players_reg[p] || players_reg1[p];
        players_unreg[p] := temp_players_unreg[p] || players_unreg1[p];
        p := p + 1;
    }

    t := 0;
    temp_tourn_reg := tourn_reg;
    temp_tourn_unreg := tourn_unreg;
    while (t < nt)
    invariant(0 <= t && t <= nt);
    invariant(forall i:int :: (0<=i && i<t) ==> (tourn_reg[i] == (temp_tourn_reg[i] || tourn_reg1[i])));
    invariant(forall i:int :: (t<=i && i<nt) ==> (tourn_reg[i] == temp_tourn_reg[i]));
    invariant(forall i:int :: (0<=i && i<t) ==> (tourn_unreg[i] == (temp_tourn_unreg[i] || tourn_unreg1[i])));
    invariant(forall i:int :: (t<=i && i<nt) ==> (tourn_unreg[i] == temp_tourn_unreg[i]));
    {
        tourn_reg[t] := temp_tourn_reg[t] || tourn_reg1[t];
        tourn_unreg[t] := temp_tourn_unreg[t] || tourn_unreg1[t];
        t := t + 1;
    }

    p := 0;
    t := 0;
    temp_enrollment := enrollment;
    while(t < nt)
    invariant(0 <= t && t <= nt);
    invariant (forall i, j:int :: (0<=i && i<t && 0<= j && j<np) ==> (enrollment[i][j] == (temp_enrollment[i][j] || enrollment1[i][j])));
    invariant (forall i, j:int :: (t<=i && i<nt && 0<= j && j<np) ==> (enrollment[i][j] == temp_enrollment[i][j]));
    {
        p := 0;
        while(p < np)
        invariant(0 <= p && p <= np);
        invariant(t == old(t));
        invariant (forall j:int :: (0<=j && j<p) ==> (enrollment[t][j] == (temp_enrollment[t][j] || enrollment1[t][j])));
        invariant (forall j:int :: (p<=j && j<np) ==> (enrollment[t][j] == temp_enrollment[t][j]));
        invariant (forall i, j:int :: (0<=i && i<t && 0<= j && j<np) ==> (enrollment[i][j] == (temp_enrollment[i][j] || enrollment1[i][j])));
        invariant (forall i, j:int :: (t<i && i<nt && 0<= j && j<np) ==> (enrollment[i][j] == temp_enrollment[i][j]));        
        {
            enrollment[t][p] := temp_enrollment[t][p] || enrollment1[t][p];
            p := p + 1;
        }
        t := t + 1;
    }
}