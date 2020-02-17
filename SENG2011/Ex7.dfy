predicate just1(a:array<int>,key:int)
   reads a
   requires a != null
{
  ((exists k | 0 <= k < a.Length :: a[k] == key) && !(exists k,j | 0 <= k < j < a.Length :: a[k] == key && a[j] == key))

}

method Just1(a: array<int>, key: int) returns (b: bool)
requires a != null
ensures just1(a,key) == b
{
    
    var count := 0;
    var i := 0;
    b:=false;
    
    if(a.Length == 0){
    
        return;
    }
    
    while i < a.Length
    invariant 0 <= i <= a.Length;
    invariant !(exists k | 0 <= k < i :: a[k] == key)
    decreases a.Length - i
    {
        if a[i] == key 
        {
            var next := i+1;
            assert (next == i+1) && (next > i);
            assert a[i] == key ==> exists j | 0 <= j <= i :: a[j] == key;
            if(next == a.Length){
                assert ((a[a.Length - 1] == key) && (forall k :: 0 <= k < (a.Length - 1) ==> a[k] != key));
                b := true;
                return;
            }
            
            while next < a.Length
            invariant a[i] == key
            invariant i+1 <= next <= a.Length;
            invariant forall k:: i+1<= k < next ==> a[k] != key
            decreases a.Length - next
            {
                if(a[next] == key){
                   assert forall k :: 0 <= k < i ==> a[k] != key && a[i] == key && !(forall j ::0<= i < j < a.Length ==> a[i] == key ==> a[j] != key);
                   assert exists  k,j | 0 <= k < j < a.Length :: a[k] == key ==> a[j] == key;
                   b:= false;
                   return;
                }
                next := next+1;
            }
            assert forall k :: (i + 1) <= k < a.Length ==> a[k] != key;
            assert a[i] == key && forall m :: 0 <= m < i ==> a[m] != key;
            b:= true;
            return;
            
        }
        i:=i+1;
    }
    assert i == a.Length;
    assert forall k :: 0<= k < a.Length ==> a[k] != key;
    assert !(exists k | 0 <= k < a.Length :: a[k] == key);
    b:= false;
    return;
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
