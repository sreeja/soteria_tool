type ReplicaId;
const unique me:ReplicaId;

var V:[ReplicaId]int;
var t:int;
const this:int;

//@invariant
function inv(V:[ReplicaId]int, t:int) returns(bool)
{
    (forall r:ReplicaId :: V[r] == 0 || V[r] == 1) && (exists r:ReplicaId :: V[r] == 1) && (forall r, r0 :ReplicaId :: (V[r] == 1 && V[r0] == 1) ==> r == r0)
}

//@gteq
function gteq_V(t1:int, V1:[ReplicaId]int, t2: int, V2:[ReplicaId]int) returns(bool)
{
    ((t1 > t2) || (t1 == t2 && (forall r:ReplicaId :: V1[r] >= V2[r])))
}

//procedure transfer(to:ReplicaId)
//modifies V, t;
//requires me != to;
//requires V[me] == 1;
//requires inv(V, t);
//ensures t > old(t);
//ensures (forall r:ReplicaId :: (r == to ==> V[r] == 1) && (r != to ==> V[r] == 0));
//ensures (forall r:ReplicaId :: V[r] == 0 || V[r] == 1);
//ensures (exists r:ReplicaId :: V[r] == 1);
//ensures (forall r, r0 :ReplicaId :: (V[r] == 1 && V[r0] == 1) ==> r == r0);
//{
//    V[me] := 0;
//    V[to] := 1;
//    t := t + 1;
//}

//@merge
//procedure merge(V1:[ReplicaId]int, t1:int) 
//modifies V, t;
//requires inv(V1, t1) == true;
//requires (t == t1 ==> (forall r:ReplicaId :: V[r] == V1[r]));
//requires (V[me] == 1 ==> t >= t1);
//ensures t == (if (t1 > old(t)) then t1 else old(t));
//ensures (forall r:ReplicaId :: (if (t1 > old(t)) then V[r] == V1[r] else V[r] == old(V)[r]));
//{
//    if (t1 > t)
//    {
//        t := t1;
//        V := V1;
//    }
//}
procedure transfer(to:ReplicaId)
modifies V, t;
requires (me != to);
requires (V[me] == 1);
requires (inv(V, t));
ensures (t > old(t));
ensures ((forall r:ReplicaId :: (r == to ==> V[r] == 1) && (r != to ==> V[r] == 0)));
ensures ((forall r:ReplicaId :: V[r] == 0 || V[r] == 1));
ensures ((exists r:ReplicaId :: V[r] == 1));
ensures ((forall r, r0 :ReplicaId :: (V[r] == 1 && V[r0] == 1) ==> r == r0));

{
V[me] := 0;
    V[to] := 1;
    t := t + 1;
}
const _to0:ReplicaId;
const _to1:ReplicaId;
procedure stability_test() 
 modifies V,t; 
 modifies V,t; 
{ 
 assume inv(V,t); 
 assume (me != _to0 && V[me] == 1 && inv(V, t)); 
  assume (me != _to1 && V[me] == 1 && inv(V, t));
 call transfer(_to0);
call transfer(_to1);
}