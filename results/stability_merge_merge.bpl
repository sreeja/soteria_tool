var V:[int]int;
var t:int;
const this:int;

//@invariant
function inv(V:[int]int, t:int) returns(bool)
{
    (forall r:int :: V[r] == 0 || V[r] == 1) && (exists r:int :: V[r] == 1) && (forall r, r0 :int :: (V[r] == 1 && V[r0] == 1) ==> r == r0)
}

//@gteq
function gteq_V(t:int, V:[int]int, old_t: int, old_V:[int]int) returns(bool)
{
    ((t > old_t) || (t == old_t && (forall r:int :: V[r] >= old_V[r])))
}

//procedure transfer(from:int, to:int)
//modifies V, t;
//requires from != to;
//requires V[from] == 1;
//requires inv(V, t);
//ensures t > old(t);
//ensures (forall r:int :: (r == to ==> V[r] == 1) && (r != to ==> V[r] == 0));
//ensures (forall r:int :: V[r] == 0 || V[r] == 1);
//ensures (exists r:int :: V[r] == 1);
//ensures (forall r, r0 :int :: (V[r] == 1 && V[r0] == 1) ==> r == r0);
//{
//    V[from] := 0;
//    V[to] := 1;
//    t := t + 1;
//}

//@merge
//procedure merge(V1:[int]int, t1:int) 
//modifies V, t;
//requires inv(V1, t1) == true;
//requires (t == t1 ==> (forall r:int :: V[r] == V1[r]));
//requires (V[this] == 1 ==> t >= t1);
//ensures t == (if (t1 > old(t)) then t1 else old(t));
//ensures (forall r:int :: (if (t1 > old(t)) then V[r] == V1[r] else V[r] == old(V)[r]));
//{
//    if (t1 > t)
//    {
//        t := t1;
//        V := V1;
//    }
//}
procedure merge(V1:[int]int, t1:int)
modifies V, t;
requires (inv(V1, t1) == true);
requires ((t == t1 ==> (forall r:int :: V[r] == V1[r])));
requires ((V[this] == 1 ==> t >= t1));
ensures (t == (if (t1 > old(t)) then t1 else old(t)));
ensures ((forall r:int :: (if (t1 > old(t)) then V[r] == V1[r] else V[r] == old(V)[r])));

{
if (t1 > t)
    {
        t := t1;
        V := V1;
    }
}
const _V10:[int]int;
const _t10:int;
const _V11:[int]int;
const _t11:int;
procedure stability_test() 
 modifies V,t; 
 modifies V,t; 
{ 
 assume inv(V,t); 
 assume (inv(_V10, _t10) == true&& (t == _t10 ==> (forall r:int :: V[r] == _V10[r]))&& (V[this] == 1 ==> t >= _t10)); 
  assume (inv(_V11, _t11) == true&& (t == _t11 ==> (forall r:int :: V[r] == _V11[r]))&& (V[this] == 1 ==> t >= _t11));
 call merge(_V10,_t10);
call merge(_V11,_t11);
}