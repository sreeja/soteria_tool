type ReplicaId;
const unique me:ReplicaId;

var V:[ReplicaId]bool;
var t:int;

//@invariant
function inv(V:[ReplicaId]bool, t:int) returns(bool)
{
    (exists r:ReplicaId :: V[r]) && (forall r, r0 :ReplicaId :: (V[r] && V[r0]) ==> r == r0)
}

//@gteq
function gteq_V_t(t1:int, V1:[ReplicaId]bool, t2: int, V2:[ReplicaId]bool) returns(bool)
{
  (t1 > t2) || (t1 == t2 && (forall r:ReplicaId :: V1[r] == V2[r]))
}

//procedure transfer(to:ReplicaId)
//modifies V, t;
//requires (forall r:ReplicaId :: (V[r] ==> r == me));
//ensures t > old(t);
//ensures (V[to]);
//ensures (forall r:ReplicaId :: (r != to ==> !V[r]));
//{
//    V[me] := false;
//    V[to] := true;
//    t := t + 1;
//}

//@merge
//procedure merge(V1:[ReplicaId]bool, t1:int)
//modifies V, t;
//requires (t == t1 ==> (forall r:ReplicaId :: V[r] == V1[r]));
//requires (V[me] ==> t >= t1);
//ensures t == (if (t1 > old(t)) then t1 else old(t));
//ensures (forall r:ReplicaId :: (if (t1 > old(t)) then V[r] == V1[r] else V[r] == old(V)[r]));
//{
//    if (t1 > t) {
//        t := t1;
//        V := V1;
//    }
//}

const V1:[ReplicaId]bool;
const t1:int;
procedure transfer(to:ReplicaId)
modifies V, t;
requires ((forall r:ReplicaId :: (V[r] ==> r == me)));
ensures (t > old(t));
ensures ((V[to]));
ensures ((forall r:ReplicaId :: (r != to ==> !V[r])));

{
V[me] := false;
    V[to] := true;
    t := t + 1;
}
const _to:ReplicaId;
procedure stability_transfer()
modifies V, t;
ensures (t == t1 ==> (forall r:ReplicaId :: V[r] == V1[r]));
ensures (V[me] ==> t >= t1);
{
assume inv(V,t) && inv(V1,t1);
assume (t == t1 ==> (forall r:ReplicaId :: V[r] == V1[r]));
assume (V[me] ==> t >= t1);
assume (forall r:ReplicaId :: (V[r] ==> r == me));
call transfer(_to);
assume {:captureState "after"} true;
}