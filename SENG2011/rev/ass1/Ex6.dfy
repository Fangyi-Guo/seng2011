predicate isClean(a: array<int>, key: int)
reads a
{
    if a == null then true else forall i :: 0<=i<a.Length ==> a[i] != key
}


method IsClean(a: array<int>, key: int) returns (clean: bool)
    ensures clean == isClean(a, key)
{
    clean := true;
    if a == null {return;}
    
    var i := 0;
    
    while i < a.Length
    invariant 0<=i <=a.Length
    invariant clean == forall j :: 0<= j < i ==> a[j] != key
    decreases a.Length-i
    {
        if a[i] == key 
        {
            clean := false;
            break;
        }
        i := i+1;
    }

}

method Main(){
    var a := new int[5];
    a[0],a[1],a[2],a[3],a[4]:=1,2,2,2,3;
    var cl := IsClean(a, 1);
    assert a[0]==1;
    assert a[1] == 2;
    assert a[2]==2;
    assert a[3]==2;
    assert a[4]==3;
    assert !cl;
    
    cl := IsClean(a, 2);
    assert !cl;
    
    cl := IsClean(a, 3);
    assert !cl;
    
    cl := IsClean(a, 4);
    assert cl;
    
    var b := new int[1];
    b[0]:=1;
    cl:=IsClean(b, 1);
    assert b[0]==1;
    assert !cl;
    
    cl:=IsClean(b, 2);
    assert cl;
    
    var c := new int[0];
    cl:=IsClean(c, 1);
    assert cl;
        
}
