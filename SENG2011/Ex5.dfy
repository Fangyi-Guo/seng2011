//two warnings for this dafny

predicate EOSorted(a: array<int>)
    reads a 
{
    (a == null) || (a!=null && forall i,j :: 0<= j <= i < a.Length && i == j+2 ==> a[j] <= a[i])
}
predicate Sorted (a:array<int>)
reads a
requires a!=null
{ forall j,k:: 0<=j<k<a.Length ==> a[j]<=a[k] }

method Test()
{
    var a := new int[6];
    a[0], a[1], a[2], a[3], a[4], a[5] := 2,1,4,2,6,3;
    var b := new int[4];
    b[0], b[1], b[2], b[3] := 1,2,3,1;
    assert b[0]==1;
    assert b[1]==2;
    assert b[2]==3;
    assert b[3]==1;//trigger
    assert EOSorted(a) == true;
    assert EOSorted(b) == false;
}
