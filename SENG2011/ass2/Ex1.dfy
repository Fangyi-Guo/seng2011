class Score{
    var highest_score: int;
    predicate Valid()//invariant
      reads this;
    {highest_score >= 0}
    constructor()
      modifies this;
      ensures Valid();
      ensures highest_score == 0;
    {
        this.highest_score := 0;
    }
    
    method NewScore(score: int) returns (isChanged: bool, current: int)
      modifies this;
      requires score >= 0 && Valid();
      ensures Valid();
      ensures ((score > old(highest_score) ==> (isChanged == true && current == score == highest_score))&&(score <= old(highest_score) ==> (isChanged == false && current == highest_score == old(highest_score))))
    {
        isChanged:=true;
        current:=this.highest_score;
        if(score > this.highest_score){
            this.highest_score := score;
            isChanged := true;
            current := score;
        }
        else{
            isChanged := false;
            current := this.highest_score;
        }
        return isChanged, current;
    }
}

method TestScore()
{
    var score:= new Score();
    
    //check scores 0, 2, 0, 4, 4, 6 in order
    var s1 := 0;
    assert s1 == 0;
    var isChanged, current := score.NewScore(s1);
    assert isChanged == false && current == 0;
    
    var s2 := 2;
    assert s2 == 2;
    var isChanged1,current1 := score.NewScore(s2);
    assert isChanged1 == true && current1 == 2;

    assert s1 == 0;
    var isChanged2,current2 := score.NewScore(s1);
    assert isChanged2 == false && current2 == 2;

    var s3 := 4;
    assert s3 == 4;
    var isChanged3,current3 := score.NewScore(s3);
    assert isChanged3 == true && current3 == 4;

    var isChanged4,current4 := score.NewScore(s3);
    assert isChanged4 == false && current4 == 4;

    var s4 := 6;
    var isChanged5,current5 := score.NewScore(s4);
    assert isChanged5 == true && current5 == 6;
    assert score.highest_score == 6;

}
