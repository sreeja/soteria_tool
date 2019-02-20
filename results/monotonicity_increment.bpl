type matrix2d=[int][int]int;
type matrix1d=[int]int;
const replicas:int;
const min:int;

axiom(forall r:int, U:matrix1d :: r >= 0  && r < replicas ==> U[r] >= 0);
axiom(forall r1, r2:int, R:matrix2d :: r1 >= 0 && r1 < replicas && r2 >= 0 && r2 < replicas ==> R[r1][r2] >= 0);
axiom(replicas > 0 && replicas < 90);
axiom(forall i:int, R:matrix2d, U:matrix1d :: local_rights(i, R, U) <= value(R, U));

function value(R:matrix2d, U:matrix1d) returns(val:int)
{
  //min + diagonal_sum(R, 0) + sum(U, 0)
  //local_rights(0, R, U) + local_rights
  total_local_rights(0, R, U)
}
function total_local_rights(index:int, R:matrix2d, U:matrix1d) returns(int)
{
  if index < replicas then (local_rights(index, R, U) + total_local_rights(index + 1, R, U)) else 0
}
function diagonal_sum(R:matrix2d, index:int) returns(int)
{
  if index < replicas then (R[index][index] + diagonal_sum(R, index + 1)) else (0) 
}
function sum(U:matrix1d, index:int) returns(int)
{
  if index < replicas then (U[index] + sum(U, index + 1)) else (0)
}	
function local_rights(id:int, R:matrix2d, U:matrix1d) returns(int)
{
  R[id][id] + column_sum(R, id, 0) - row_sum(R, id, 0) - U[id]
}
function column_sum(R:matrix2d, col:int, index:int) returns(int)
{
  if index > replicas then (R[index][col] + column_sum(R, col, index + 1)) else (0)
}
function row_sum(R:matrix2d, row:int, index:int) returns(int)
{
  if index > replicas then (R[row][index] + row_sum(R, row, index + 1)) else (0)
}

function increment_effect(R:matrix2d, oldR:matrix2d, id:int, n:int) returns(bool)
{
  (forall r1, r2:int :: ((r1 == id && r2 == id) ==> R[r1][r2] == oldR[r1][r2] + n) && ((r1 != id || r2 != id) ==> R[r1][r2] == oldR[r1][r2]))
}
function decrement_effect(U:matrix1d, oldU:matrix1d, id:int, n:int) returns(bool)
{
  (forall r:int :: (r == id ==> U[r] == oldU[r] + n) && (r != id ==> U[r] == oldU[r]))
}
function transfer_effect(R:matrix2d, oldR:matrix2d, from:int, to:int, n:int) returns(bool)
{
  (forall r1, r2:int :: ((r1 == from && r2 == to) ==> R[r1][r2] == oldR[r1][r2] + n) && ((r1 != from || r2 != to) ==> R[r1][r2] == oldR[r1][r2]))
}
function max(a:int, b:int) returns(int)
{
  (if a > b then a else b)
}
function update1dmatrix(newU:matrix1d, oldU:matrix1d, U:matrix1d) returns(bool)
{
  (forall r:int :: U[r] == max(newU[r], oldU[r]))
}	
function update2dmatrix(newR:matrix2d, oldR:matrix2d, R:matrix2d) returns(bool)
{
  (forall r1, r2:int :: R[r1][r2] == max(newR[r1][r2], oldR[r1][r2]))
}	

var R:matrix2d;
var U:matrix1d;

//@invariant
function inv(R:matrix2d, U:matrix1d) returns(bool)
{
  (forall i:int :: local_rights(i, R, U) >= 0)
}
//@gteq
function gteq_2d(R1:matrix2d, R2:matrix2d) returns(bool)
{
	(forall r1, r2:int :: R1[r1][r2] >= R2[r1][r2])
}
//@gteq
function gteq_1d(U1:matrix1d, U2:matrix1d) returns(bool)
{
  (forall r:int :: U1[r] >= U2[r])
}	
//procedure increment(id:int, n:int)
//modifies R;
//requires n > 0 && id >= 0 && id < replicas;
//ensures local_rights(id, R, U) == old(local_rights(id, R, U)) + n;
//ensures (forall i, j:int :: ((i == id && j == id) ==> R[i][j] == old(R)[i][j] + n) && ((i != id || j != id) ==> R[i][j] == old(R)[i][j]));
//{
//  //R[id][id] := R[id][id] + n;
//  assume false;
//}
//procedure decrement(id:int, n:int)
//modifies U;
//requires n > 0  && id >= 0 && id < replicas;
//requires local_rights(id, R, U) >= n;
//ensures local_rights(id, R, U) == old(local_rights(id, R, U)) - n;
//ensures (forall i:int :: (i == id ==> U[i] == old(U)[i] + n) && (i != id ==> U[i] == old(U)[i]));
//{
//  //U[id] := U[id] + n;
//  assume false;
//}
//procedure transfer(from:int, to:int, n:int)
//modifies R;
//requires n > 0  && from >= 0 && from < replicas ;
//requires to >= 0 && to < replicas && from != to;
//requires local_rights(from, R, U) >= n;
//ensures local_rights(from, R, U) == old(local_rights(from, R, U)) - n;
//ensures local_rights(to, R, U) == old(local_rights(to, R, U)) + n;
//ensures (forall i, j:int :: ((i == from && j == to) ==> R[i][j] == old(R)[i][j] + n) && ((i != from || j != to) ==> R[i][j] == old(R)[i][j]));
//
//{
//  //R[from][to] := R[from][to] + n;
//  assume false;
//}
//@merge
//procedure merge(newR:matrix2d, newU:matrix1d)
//modifies R, U;
//ensures update2dmatrix(newR, old(R), R) && update1dmatrix(newU, old(U), U);
//{
//  assume false;
//}

procedure increment(id:int, n:int)
modifies R;
requires (n > 0 && id >= 0 && id < replicas);
ensures (local_rights(id, R, U) == old(local_rights(id, R, U)) + n);
ensures ((forall i, j:int :: ((i == id && j == id) ==> R[i][j] == old(R)[i][j] + n) && ((i != id || j != id) ==> R[i][j] == old(R)[i][j])));

ensures gteq_2d(R, old(R));
{
//R[id][id] := R[id][id] + n;
  assume false;
}