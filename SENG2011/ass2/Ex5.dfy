predicate Sorted(a: array<int>,start:int,end:int)
    reads a;
    requires a != null
    requires 0 <= start < end <= a.Length
{
    forall j, k :: start <= j < k < end ==> a[j] <= a[k]
}

method Shuffle(a:array<int>)
    modifies a;
    requires a != null;
    requires a.Length > 0;
    ensures a.Length > 0;
    ensures Sorted(a,0,a.Length);
    ensures multiset(a[..]) == multiset(old(a[..]));  
{
    if(a.Length > 1){//sort array has at least two values
        var i := 1;

        while(i < a.Length)//start from the second value
        invariant 1 <= i <= a.Length;
        invariant forall x,y:: 0 <= x < y < i  ==> a[x] <= a[y]; 
        invariant multiset(a[..]) == multiset(old(a[..])); 
        {
            var end := a[i];// save for substitution for later
            var j := i - 1;

            a[i] := a[j];
            
            while(j >= 0 && a[j] > end)
            invariant -1 <= j < i;
            invariant forall x,y:: 0 <= x < y < i+1  ==> a[x] <= a[y]; 
            invariant forall x :: j < x < i ==> end < a[x];
            invariant multiset(a[..]) - multiset([a[j+1]]) + multiset([end]) ==  multiset(old(a[..]));
            {
                a[j+1] := a[j];
                j := j - 1;
            }
            
            a[j+1] := end;
            i := i + 1;
        }
    }
}

method Main()
{ // SUBMIT THIS MAIN METHOD WITH YOUR CODE
    var a := new int[2];
    a[0]:=34; a[1]:=12;
    assert a[..]==[34,12];
    ghost var ms := multiset(a[..]);
    Shuffle(a);
    assert a[..]==[12,34];
    assert Sorted(a, 0, a.Length);
    assert ms == multiset(a[..]);
    print a[..];
    var b := new int[4];
    b[0]:=78; b[1]:=56; b[2]:=34; b[3]:=12;
    assert b[..]==[78,56,34,12];
    ms := multiset(b[..]);
    Shuffle(b);
    assert b[..]==[12,34,56,78];
    assert Sorted(a, 0, a.Length);
    assert ms == multiset(b[..]);
    print b[..], '\n';
}

