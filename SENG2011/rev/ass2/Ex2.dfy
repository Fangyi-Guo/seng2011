class dishwasher{
    var isLoaded : bool;
    var isAddedDtgt : bool;
    var isWashed: bool;
    
    predicate Valid()
    reads this;
    {
        (!isLoaded&&isWashed)||(!isAddedDtgt && isWashed) ==>false
    }
    
    constructor()
    modifies this;
    ensures Valid();
    ensures this.isLoaded == false && this.isAddedDtgt == false && isWashed==false;
    {
        this.isLoaded:=false;
        this.isAddedDtgt := false;
        this.isWashed:=false;
    }
    
    method Load()
    modifies this;
    ensures Valid();
    ensures this.isWashed == false;
    ensures this.isLoaded == true;
    ensures this.isAddedDtgt == old(this.isAddedDtgt);
    {
        this.isLoaded := true;
        this.isWashed := false;
    }
    
    method AddDtgt()
    modifies this;
    ensures Valid();
    ensures this.isWashed == false;
    ensures this.isAddedDtgt == true;
    ensures this.isLoaded == old(this.isLoaded)
    {
        this.isAddedDtgt := true;
        this.isWashed := false;
    }
    
    method Wash()
    modifies this;
    requires Valid();
    requires this.isAddedDtgt == true;
    requires this.isLoaded == true;
    ensures this.isWashed == true;
    ensures this.isAddedDtgt == false;
    ensures this.isLoaded == false;
    {
        this.isWashed := true;
        this.isAddedDtgt := false;
        this.isLoaded := false;
    }
    
    method Unload()
    modifies this;
    requires this.isWashed == true;
    ensures Valid();
    ensures this.isLoaded == false;
    ensures this.isWashed == false;
    {
        this.isLoaded := false;
        this.isWashed := false;
    }
}

method Test1()
{
    var dw := new dishwasher();
    dw.Load();
    dw.AddDtgt();
    dw.Wash();
    dw.Unload();
}
