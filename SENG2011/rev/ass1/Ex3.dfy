method Skippy(limit: nat)
{
    var skip := 7;
    var index := 0;
    while index<=limit
    invariant 0 <= index <= (limit/7+1)*7 && (index %7 == 0);//remember to check the index range specify its invariant
    decreases limit - index;
    { index := index+skip; }
    assert index == (limit/7+1)*7;
}
