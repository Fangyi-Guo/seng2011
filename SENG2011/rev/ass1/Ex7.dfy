predicate just1(a: array<int>, key: int)
reads a
requires a != null
{
    (exists k | 0 <= k < a.Length :: a[k] == key)&&!(exists k, j | 0<=k<j<a.Length :: a[j]==key&&a[k]==key)
}



method Just1(a: array<int>, key: int) returns (b: bool)
requires a!=null
ensures b == just1(a,key)
{
    b := false;
    
    var i :=  0;
    while i < a.Length
    invariant 0<=i<=a.Length
    invariant !(exists j | 0<=j<i :: a[j]==key)
    decreases a.Length - i
    {
        if a[i]==key
        {
            var k := i+1;
            if (k == a.Length){
                b := true;
                return;
            }
            
            while k<a.Length
            invariant i+1<=k<=a.Length
            invariant forall m:: i+1<=m<k ==> a[m]!= key
            decreases a.Length-k
            {
                if a[k]==key{
                    b := false;
                    return;
                }
                k := k+1;
            }
            b:=true;
            return;
        }
        i := i+1;
    }
    
}

method Main(){
    var arr :=new int[4];
    arr[0], arr[1], arr[2], arr[3]:= 1,1,2,1;
    var res:= Just1(arr, 1);
    assert arr[0]==1;
    assert arr[1]==1;
    assert arr[2]==2;
    assert arr[3]==1;
    assert !res;
    print res;
    print "\n";
    
    res:= Just1(arr, 2);
    assert res;
    print res;
    print "\n";
    
    res:= Just1(arr, 3);
    assert !res;
    print res;
    print "\n";
    
    var arr1 :=new int[1];
    arr1[0]:=1;
    res := Just1(arr1, 1);
    assert arr1[0]==1;
    assert res;
    print res;
    print "\n";
    
    res:= Just1(arr1, 2);
    assert !res;
    print res;
    print "\n";
    
    var arr2 := new int[0];
    res := Just1(arr2, 1);
    assert !res;
    print res;
    print "\n";
}
