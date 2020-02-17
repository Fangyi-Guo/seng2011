class Score{
    var highest_score: int;
    
    predicate Valid()
        reads this;
    {
        highest_score >= 0
    }
    
    constructor()
    modifies this;
    ensures Valid();
    ensures highest_score == 0;
    {
        highest_score := 0;
    }
    
    method NewScore(score:int)returns(b: bool, curr: int)
    modifies this
    requires score >=0;
    ensures Valid();
    ensures if score > old(highest_score) then (b == true && curr == score == highest_score) else(b==false && curr == highest_score == old(highest_score))
    {
        b := true;
        curr:= highest_score;
        if score > this.highest_score {
            this.highest_score := score;
            b := true;
            curr := score;
        }
        else{
            b:=false;
            curr:=this.highest_score;
        }
        return b, curr;
    }

}

method TestScore(){
    var sc := new Score();
    var b, curr := sc.NewScore(2);
    assert b==true && curr == 2;
    
    b, curr := sc.NewScore(0);
    assert b==false && curr == 2;
    
    b, curr := sc.NewScore(4);
    assert b==true&&curr==4;
    
    b, curr := sc.NewScore(4);
    assert b==false&&curr==4;
    
    b, curr := sc.NewScore(6);
    assert b==true&&curr==6;
    
}
