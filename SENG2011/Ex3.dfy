method Skippy(limit: nat)
{
    var skip := 7;
    var index := 0;
    while index<=limit
    invariant 0<=index
    { index := index+skip; }
    assert limit<=index;
}
