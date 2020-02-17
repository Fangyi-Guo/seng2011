predicate isClean(a: array<int>, key: int) 
    reads a 
{
    if a == null then a == null else
    forall i ::0<= i < a.Length ==> a[i] != key
}

method IsClean(a: array<int>, key: int) returns (clean: bool)
ensures clean <==> isClean(a, key)
{
    
    clean:=true;
    if a == null {return;}
    
    var i:int := 0;
    while i < a.Length
    invariant 0 <= i <= a.Length
    invariant clean == forall j :: 0<= j < i ==> a[j]!=key
    decreases a.Length - i;
    {
        if a[i] == key 
        {
            clean := false;
            break;
        }
        i := i+1;
    }
    
}

method Main()
{
    var arr :=new int[5];
    arr[0], arr[1], arr[2], arr[3], arr[4] := 1,2,2,2,3;
    var res:= IsClean(arr, 1);
    assert arr[0]==1;
    assert arr[1]==2;
    assert arr[2]==2;
    assert arr[3]==2;
    assert arr[4]==3;
    assert !res;
    print res;
    print "\n";
    
    res:= IsClean(arr, 2);
    assert !res;
    print res;
    print "\n";
    
    res:= IsClean(arr, 3);
    assert !res;
    print res;
    print "\n";
    
    res:= IsClean(arr, 4);
    assert res;
    print res;
    print "\n";

    var arr1 :=new int[1];
    arr1[0] := 1;
    res := IsClean(arr1, 1);
    assert arr1[0] == 1;
    assert !res;
    print res;
    print "\n";
    
    res := IsClean(arr1, 2);
    assert res;
    print res;
    print "\n";
    
    var arr2 :=new int[0];
    res := IsClean(arr2, 1);
    assert res;
    print res;
    print "\n";
}
