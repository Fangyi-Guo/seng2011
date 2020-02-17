//There are 4 distinct actions above: loading, adding detergent, washing and unloading.

class DishWasher{
    var loaded: bool;
    var addedDtgt: bool;
    var washed: bool;
    
    predicate Valid()
      reads this;
    {
      //we cannot have
      (!this.loaded && this.washed)||(!this.addedDtgt && this.washed) ==> false
    }
    
    constructor()
      modifies this;
      ensures this.loaded == false;
      ensures this.addedDtgt == false;
      ensures this.washed == false;
      ensures Valid();
    {
        this.loaded := false;
        this.addedDtgt := false;
        this.washed := false;
    }
    
    method Load()
      modifies this;
      ensures this.loaded == true;
      ensures this.washed == false;
      ensures Valid();
      //addedDtgt no change 
      ensures this.addedDtgt == old(this.addedDtgt);
    {
        this.loaded := true;
        this.washed := false;
    }
    
    method AddDtgt()
      modifies this;
      ensures this.addedDtgt == true;
      //ensures Valid();
      ensures this.loaded == old(this.loaded);
      ensures this.washed == old(this.washed);
    {
        this.addedDtgt := true;
    }
    
    method Wash()
      modifies this;
      requires this.addedDtgt == true;
      requires this.loaded == true;
      ensures this.washed == true;
      ensures this.loaded == old(this.loaded);
    {
        this.addedDtgt := false;
        this.washed := true;
    }
    
    method Unload()
      modifies this;
      requires this.loaded == true;
      requires this.washed == true;
      ensures this.loaded == false;
      ensures this.washed == false;
      ensures Valid();
      ensures this.addedDtgt == old(this.addedDtgt);
    {
        this.loaded := false;
        this.washed := false;
    }
}

method Test1()
{
    var dishwasher := new DishWasher();
    dishwasher.Load();
    dishwasher.AddDtgt();
    dishwasher.Wash();
    dishwasher.Unload();
}

method Test2()
{
    var dishwasher := new DishWasher();
    dishwasher.AddDtgt();
    dishwasher.Load();
    dishwasher.Wash();
    dishwasher.Unload();
}

method Test3()
{
    var dishwasher := new DishWasher();
    dishwasher.Load();
    dishwasher.AddDtgt();
    dishwasher.Wash();
    dishwasher.AddDtgt();
    dishwasher.Unload();
    dishwasher.Load();
    dishwasher.Wash();
    dishwasher.Unload();
}

method Test4()
{
    var dishwasher := new DishWasher();
    dishwasher.Load();
    dishwasher.AddDtgt();
    dishwasher.Wash();
    dishwasher.AddDtgt();
    dishwasher.Wash();
    dishwasher.Unload();
}

method Test5()
{
    var dishwasher := new DishWasher();
    dishwasher.Load();
    dishwasher.Load();
    dishwasher.Load();
    dishwasher.AddDtgt();
    dishwasher.AddDtgt();
    dishwasher.Wash();
    dishwasher.Unload();
}


method ExtraTest1()
{
    var dishwasher := new DishWasher();
    dishwasher.Load();
    dishwasher.Load();
    dishwasher.Load();
    dishwasher.Load();
    dishwasher.AddDtgt();
    dishwasher.Wash();
    dishwasher.Unload();
}

method ExtraTest2()
{
    // heavy duty dish washer 
    var dishwasher := new DishWasher();
    dishwasher.Load();
    dishwasher.AddDtgt();
    dishwasher.Wash();
    dishwasher.Load();
    dishwasher.AddDtgt();
    dishwasher.AddDtgt();
    dishwasher.Wash();
    dishwasher.Unload();
}


// method ErrorTest1()
// {
//     // wash before adding detergented
//     var dishwasher := new DishWasher();
//     dishwasher.Load();
//     dishwasher.Wash();
// }

// method ErrorTest2()
// {
//     // wash before adding detergented
//     var dishwasher := new DishWasher();
//     // forget to load dishes 
//     dishwasher.AddDtgt();
//     dishwasher.Wash();
// }

// method ErrorTest3()
// {
//     // wash before adding detergented
//     var dishwasher := new DishWasher();
//     // nothing to unload 
//     dishwasher.Unload();
// }

