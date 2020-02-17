function Abs(x: int):int
{
    if x<0 then -x else x
}

method IncDec(x: int, y: int) returns (sum: int)
ensures sum == x+y;
{
    sum := 0;
    var k, j:= x, y;
    while k!= 0 || j!=0
    invariant x + y == sum + k + j
    decreases Abs(k)
    decreases Abs(j)
    {
        if k < 0{
            sum:=sum-1;
            k:=k+1;
        }
        else if k > 0{
            sum:=sum+1;
            k:=k-1;
        }
        if j < 0{
            sum:=sum-1;
            j:=j+1;
        }
        else if j > 0{
            //remember not include 0
            sum:=sum+1;
            j:=j-1;
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
