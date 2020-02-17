method HeadTail()
    modifies this, this.buf, this`m, this`n
    requires buf!=null && Valid();
    ensures buf!=null&& 0<=m<=n<=buf.Length && shadow==buf[m..n];
    // no swapping a new main if change buf
    ensures buf==old(buf) || fresh(buf);
    //the index has no change
    ensures n == old(n) && m == old(m);
    // swap the both elements 
    ensures n-m >= 1 ==> buf[n-1] == old(buf[m]);
    ensures n-m >= 1 ==> buf[m] == old(buf[n-1]);
    ensures n-m>1 ==> shadow == [old(shadow[|old(shadow)|-1])] + old(shadow[1..|old(shadow)|-1]) + [old(shadow[0])];
    ensures n-m<=1 ==> shadow == old(shadow);
    // things not changed 
    ensures |shadow| == old(|shadow|);
    ensures forall x:int :: m < x < n -1 ==> buf[x]==old(buf[x]);
{
    // do nothing if there nothing or only one els  
    
    if (n-m>=1){
        buf[n-1], buf[m]:= buf[m], buf[n-1];
        
        if (|shadow|-1 == 0){
            shadow := [shadow[0]];
        }
        else if(|shadow|-1==1){
            shadow := [shadow[|shadow|-1]]+[shadow[0]];
        }
        else{
            shadow:= [shadow[|shadow|-1]] + shadow[1..|shadow|-1] + [shadow[0]];
        }
    }
}

