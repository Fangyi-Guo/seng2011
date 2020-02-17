function Abs(x:int):int
{
    if x >= 0 then x else -x
}

method IncDec(x: int, y: int) returns (sum: int)//usually use tmp number to dcr inc
    ensures sum == x + y
{
    sum:=x;
    var tmp := y;
    while tmp != 0
    invariant sum + tmp == x + y;
    decreases Abs(tmp);
    {
        if(tmp > 0){
            sum := sum + 1;
            tmp := tmp - 1;
        }
        else if(tmp < 0){
            sum := sum -1;
            tmp := tmp +1;
        }
    }
}

method Test(){
    var sum := IncDec(5, 15);
    assert sum == 20;
    sum := IncDec(5, -15);
    assert sum == -10;
    sum := IncDec(5, 0);
    assert sum == 5;
    sum := IncDec(-5, 15);
    assert sum == 10;
    sum := IncDec(-5, -15);
    assert sum == -20;
    sum := IncDec(-5, 0);
    assert sum == -5;
}
