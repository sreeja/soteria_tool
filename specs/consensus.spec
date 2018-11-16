type ReplicaId=int;
const unique me:ReplicaId;
const nr : int;
axiom 0 < nr;
axiom (0 <= me && me < nr);

var boxes:[ReplicaId]bool;
var flag:bool;

@invariant
function inv(boxes:[ReplicaId]bool, flag:bool) returns(bool)
{
    (flag ==> (forall r:ReplicaId :: (0 <= r && r < nr) ==> boxes[r]))
}

@gteq
function gteq(boxes1:[ReplicaId]bool, flag1:bool, boxes2:[ReplicaId]bool, flag2:bool) returns(bool)
{
  (flag1) || (!flag2 && (forall r:ReplicaId :: (0 <= r && r < nr) ==> (boxes1[r] || !boxes2[r])))
}

procedure mark()
modifies boxes;
ensures (boxes[me]);
ensures (forall r:ReplicaId :: ((0 <= r && r < nr && r != me) ==> (boxes[r] == old(boxes[r]))));
{
    boxes[me] := true;
}

procedure agree()
modifies flag;
requires (forall r:ReplicaId :: (0 <= r && r < nr) ==> boxes[r]);
ensures (flag == true);
{
    flag := true;
}

@merge
procedure merge(boxes1:[ReplicaId]bool, flag1:bool)
modifies boxes, flag;
ensures (flag == (old(flag) || flag1));
ensures (forall r:ReplicaId :: (0 <= r && r < nr) ==> (boxes[r] == (old(boxes)[r] || boxes1[r])));
{
    var temp_flag:bool;
    var temp_boxes:[ReplicaId]bool;
    var r:int;
    temp_flag := flag;
    temp_boxes := boxes;
    r := 0;

    flag := temp_flag || flag1;
    while(r < nr)
    invariant (0 <= r && r <= nr);
    invariant (forall k:int :: (0 <= k && k < r) ==> boxes[k] == (old(boxes)[k] || boxes1[k]));
    invariant (forall k:int :: (r <= k && k < nr) ==> boxes[k] == old(boxes)[k]);
    {
        boxes[r] := temp_boxes[r] || boxes1[r];
        r := r + 1;
    }
}
