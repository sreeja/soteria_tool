type matrix2d=[int][int]int;
type matrix1d=[int]int;
const replicas:int;
const min:int;

function value(R:matrix2d, U:matrix1d) returns(int)
{
  min + diagonal_sum(R, 0) + sum(U, 0)
}

var R :matrix2d;
var U:matrix1d;

@invariant
function inv(R:matrix2d, U:matrix1d) returns(bool)
{
  (value(R, U) >= min)
}

@gteq
function gteq(R1:matrix2d, R2:matrix2d, U1:matrix1d, U2:matrix1d) returns(res:bool)
{
	(forall r1, r2:int :: R1[r1][r2] >= R2[r1][r2]) && (forall r:int :: U1[r] >= U2[r])
}

@merge
procedure merge(newR:matrix2d, newU:matrix1d)
modifies R, U;
ensures update2dmatrix(newR, old(R), R) && update1dmatrix(newU, old(U), U);
{
  assume false;
}

procedure increment(id:int, n:int)
modifies R;
requires n > 0;
requires id >= 0 && id < replicas;
{
  R[id][id] := R[id][id] + n;
}
procedure decrement(id:int, n:int)
modifies U;
requires n > 0 ;
requires id >= 0 && id < replicas;
requires local_rights(id, R, U) >= n;
{
  U[id] := U[id] + n;
}
procedure transfer(from:int, to:int, n:int)
modifies R;
requires n > 0 ;
requires from >= 0 && from < replicas  && to >= 0 && to < replicas && from != to;
requires local_rights(from, R, U) >= n;
{
  R[from][to] := R[from][to] + n;
}