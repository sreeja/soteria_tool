type rid = int;
const unique me:rid;
const nr : rid;
axiom 0 < nr;
axiom 0 <= me && me < nr;
type sid = int;
const ns : sid;
axiom 0 < ns;
type cid = int;
const nc : cid;
axiom 0 < nc;

var students_reg:[sid]bool;
var students_unreg:[sid]bool;
var course_reg:[cid]bool;
var course_unreg:[cid]bool;
var enrollment:[cid][sid]bool;

@gteq
function gteq(students_reg1:[sid]bool, students_unreg1:[sid]bool, course_reg1:[cid]bool, course_unreg1:[cid]bool, enrollment1:[cid][sid]bool, students_reg2:[sid]bool, students_unreg2:[sid]bool, course_reg2:[cid]bool, course_unreg2:[cid]bool, enrollment2:[cid][sid]bool) returns(bool)
{
    (forall s:sid :: (0 <= s && s < ns) ==> (students_reg1[s] || !students_reg2[s])) && (forall s:sid :: (0 <= s && s < ns) ==> (students_unreg1[s] || !students_unreg2[s])) && (forall c:cid :: (0 <= c && c < nc) ==> (course_reg1[c] || !course_reg2[c])) && (forall c:cid :: (0 <= c && c < nc) ==> (course_unreg1[c] || !course_unreg2[c])) && (forall s:sid, c:cid :: (0 <= s && s < ns && 0 <= c && c < nc) ==> (enrollment1[c][s] || !enrollment2[c][s]))
}

@invariant
function inv(students_reg:[sid]bool, students_unreg:[sid]bool, course_reg:[cid]bool, course_unreg:[cid]bool, enrollment:[cid][sid]bool) returns(bool)
{
    (forall s:sid, c:cid :: (0 <= s && s < ns && 0 <= c && c < nc && enrollment[c][s]) ==> (students_reg[s] && !students_unreg[s] && course_reg[c] && !course_unreg[c]))
}

procedure addplayer(s1:sid)
modifies students_reg;
requires 0 <= s1 && s1 < ns;
ensures students_reg[s1] && (forall s:sid :: (0 <= s && s < ns && s != s1) ==> (students_reg[s] == old(students_reg)[s]));
{
    students_reg[s1] := true;
}

procedure remplayer(s1:sid)
modifies students_unreg;
requires 0 <= s1 && s1 < ns;
requires !(exists c:cid :: (0 <= c && c < nc && enrollment[c][s1]));
ensures students_unreg[s1] && (forall s:sid :: (0 <= s && s < ns && s != s1) ==> (students_unreg[s] == old(students_unreg)[s]));
{
    students_unreg[s1] := true;
}

procedure addtournament(c1:cid)
modifies course_reg;
requires 0 <= c1 && c1 < nc;
ensures course_reg[c1] && (forall c:cid :: (0 <= c && c < nc && c != c1) ==> (course_reg[c] == old(course_reg)[c]));
{
    course_reg[c1] := true;
}

procedure remtournament(c1:cid)
modifies course_unreg;
requires 0 <= c1 && c1 < nc;
requires !(exists s:sid :: (0 <= s && s < ns && enrollment[c1][s]));
ensures course_unreg[c1] && (forall c:cid :: (0 <= c && c < nc && c != c1) ==> (course_unreg[c] == old(course_unreg)[c]));
{
    course_unreg[c1] := true;
}

procedure enrol(c1:cid, s1:sid)
modifies enrollment;
requires 0 <= s1 && s1 < ns && 0 <= c1 && c1 < nc;
requires students_reg[s1] && !students_unreg[s1];
requires course_reg[c1] && !course_unreg[c1];
ensures enrollment[c1][s1] && (forall c:cid, s:sid :: (0 <= c && c < nc && 0 <= s && s < ns && (c != c1 || s != s1)) ==> (enrollment[c][s] == old(enrollment)[c][s]));
{
    enrollment[c1][s1] := true;
}

@merge
procedure merge(students_reg1:[sid]bool, students_unreg1:[sid]bool, course_reg1:[cid]bool, course_unreg1:[cid]bool, enrollment1:[cid][sid]bool)
modifies students_reg, students_unreg, course_reg, course_unreg, enrollment;
requires (forall s:sid, c:cid :: (0 <= s && s < ns && 0 <= c && c < nc) ==> (enrollment[c][s] ==> (!students_unreg1[s] && !course_unreg1[c])));
requires (forall s:sid, c:cid :: (0 <= s && s < ns && 0 <= c && c < nc) ==> (enrollment1[c][s] ==> (!students_unreg[s] && !course_unreg[c])));

ensures (forall s:sid :: (0 <= s && s < ns) ==> (students_reg[s] == (old(students_reg)[s] || students_reg1[s])));
ensures (forall s:sid :: (0 <= s && s < ns) ==> (students_unreg[s] == (old(students_unreg)[s] || students_unreg1[s])));
ensures (forall c:cid :: (0 <= c && c < nc) ==> (course_reg[c] == (old(course_reg)[c] || course_reg1[c])));
ensures (forall c:cid :: (0 <= c && c < nc) ==> (course_unreg[c] == (old(course_unreg)[c] || course_unreg1[c])));
ensures (forall c:cid, s:sid :: (0 <= s && s < ns && 0 <= c && c < nc) ==> (enrollment[c][s] == (old(enrollment)[c][s] || enrollment1[c][s])));
{
    var s, c, r:int;
    var temp_students_reg:[sid]bool;
    var temp_students_unreg:[sid]bool;
    var temp_course_reg:[cid]bool;
    var temp_course_unreg:[cid]bool;
    var temp_enrollment:[cid][sid]bool;
    
    s := 0;
    temp_students_reg := students_reg;
    temp_students_unreg := students_unreg;
    while (s < ns)
    invariant(0 <= s && s <= ns);
    invariant(forall i:int :: (0<=i && i<s) ==> (students_reg[i] == (temp_students_reg[i] || students_reg1[i])));
    invariant(forall i:int :: (s<=i && i<ns) ==> (students_reg[i] == temp_students_reg[i]));
    invariant(forall i:int :: (0<=i && i<s) ==> (students_unreg[i] == (temp_students_unreg[i] || students_unreg1[i])));
    invariant(forall i:int :: (s<=i && i<ns) ==> (students_unreg[i] == temp_students_unreg[i]));
    {
        students_reg[s] := temp_students_reg[s] || students_reg1[s];
        students_unreg[s] := temp_students_unreg[s] || students_unreg1[s];
        s := s + 1;
    }

    c := 0;
    temp_course_reg := course_reg;
    temp_course_unreg := course_unreg;
    while (c < nc)
    invariant(0 <= c && c <= nc);
    invariant(forall i:int :: (0<=i && i<c) ==> (course_reg[i] == (temp_course_reg[i] || course_reg1[i])));
    invariant(forall i:int :: (c<=i && i<nc) ==> (course_reg[i] == temp_course_reg[i]));
    invariant(forall i:int :: (0<=i && i<c) ==> (course_unreg[i] == (temp_course_unreg[i] || course_unreg1[i])));
    invariant(forall i:int :: (c<=i && i<nc) ==> (course_unreg[i] == temp_course_unreg[i]));
    {
        course_reg[c] := temp_course_reg[c] || course_reg1[c];
        course_unreg[c] := temp_course_unreg[c] || course_unreg1[c];
        c := c + 1;
    }

    s := 0;
    c := 0;
    temp_enrollment := enrollment;
    while(c < nc)
    invariant(0 <= c && c <= nc);
    invariant (forall i, j:int :: (0<=i && i<c && 0<= j && j<ns) ==> (enrollment[i][j] == (temp_enrollment[i][j] || enrollment1[i][j])));
    invariant (forall i, j:int :: (c<=i && i<nc && 0<= j && j<ns) ==> (enrollment[i][j] == temp_enrollment[i][j]));
    {
        s := 0;
        while(s < ns)
        invariant(0 <= s && s <= ns);
        invariant(c == old(c));
        invariant (forall j:int :: (0<=j && j<s) ==> (enrollment[c][j] == (temp_enrollment[c][j] || enrollment1[c][j])));
        invariant (forall j:int :: (s<=j && j<ns) ==> (enrollment[c][j] == temp_enrollment[c][j]));
        invariant (forall i, j:int :: (0<=i && i<c && 0<= j && j<ns) ==> (enrollment[i][j] == (temp_enrollment[i][j] || enrollment1[i][j])));
        invariant (forall i, j:int :: (c<i && i<nc && 0<= j && j<ns) ==> (enrollment[i][j] == temp_enrollment[i][j]));        
        {
            enrollment[c][s] := temp_enrollment[c][s] || enrollment1[c][s];
            s := s + 1;
        }
        c := c + 1;
    }
}