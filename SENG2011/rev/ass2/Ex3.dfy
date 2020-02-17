class Quack<Data>
{
    var buf: array<Data>;
    var m: int, n: int;

    ghost var shadow: seq<Data>;

    predicate Valid() reads this, this.buf
    { buf!=null && buf.Length!=0 && 0<=m<=n<=buf.Length && shadow==buf[m..n] }

    constructor(size: int) modifies this
    requires size>0;
    ensures shadow == []
    ensures fresh(buf)
    ensures Valid()
    {   buf := new Data[size];
        m, n:= 0, 0;
        shadow:= [];
    }
    method Empty() returns (x: bool)
    ensures x <==> shadow==[]
    requires Valid(); ensures Valid()
    { x := m==n; }

    method Pop() returns(x: Data) modifies this, this`n
    requires buf!=null && Valid()
    requires shadow != [] 
    ensures Valid();
    ensures       x  == old(shadow[|old(shadow)|-1])  // get tail
    ensures   shadow == old(shadow[..|old(shadow)|-1])// chop off tail
    ensures |shadow| == |old(shadow)|-1
    ensures buf == old(buf)  // no change to buf here
    {   x, n:= buf[n-1], n-1;
        shadow:= shadow[..|shadow|-1];
    }

    method Qop() returns(x: Data) modifies this, this`m
    requires buf!=null && Valid()
    requires shadow != [];
    ensures Valid();
    ensures        x == old(shadow[0])   // get head
    ensures   shadow == old(shadow[1..]) // chop off head
    ensures |shadow| == |old(shadow)|-1
    ensures buf == old(buf)  // no change to buf here
    {   x, m:= buf[m], m+1;
        shadow:= shadow[1..];
    }

    method Push(x: Data) modifies this, this.buf, this`m, this`n
    requires buf!=null && Valid();
    ensures   shadow == old(shadow) + [x]; // new tail
    ensures |shadow| == |old(shadow)|+1
    ensures if old(n)==old(buf.Length) then fresh(buf) else buf==old(buf)
    ensures Valid();
    {   if n==buf.Length
        {   var b:= new Data[buf.Length];             // temporary
            if m==0 { b:= new Data[2*buf.Length]; }   // double size
            forall (i | 0<=i<n-m) { b[i]:= buf[m+i]; }// copy m..n to 0..n-m
            buf, m, n:= b, 0, n-m;                    // copy b to buf, reset m,n
        }
        buf[n], n:= x, n+1;         // now we definitely have room
        shadow:= shadow + [x];      // same as previous slide: concat 'x'
    }   
    
    method HeadTail() modifies this, this.buf, this`m, this`n
    requires buf!=null && Valid();
    ensures n == old(n) && m == old(m);
    ensures buf!=null &&  0<=m<=n<=buf.Length && shadow==buf[m..n]
    ensures buf==old(buf)||fresh(buf);
    ensures n-m>1 ==> shadow == [old(shadow[|old(shadow)|-1])] + old(shadow[1..|old(shadow)|-1]) + [old(shadow[0])];
    ensures n-m<=1 ==> shadow == old(shadow);
    ensures n-m >= 1 ==> buf[n-1] == old(buf[m]);
    ensures n-m >= 1 ==> buf[m] == old(buf[n-1]);
    ensures |shadow| == |old(shadow)|
    ensures forall i:int:: old(m)<i<old(n)-1 ==> buf[i] == old(buf[i]);
    {
        if (n-m >=1){
            this.buf[m],this.buf[n-1]:=buf[n-1], buf[m];
            if(|shadow|-1 == 0){
                shadow:=[shadow[0]];
            }
            else if (|shadow|-1 == 1){
                shadow := [shadow[|shadow|-1]]+[shadow[0]];
            }
            else{
                shadow := [shadow[|shadow|-1]]+shadow[1..|shadow|-1]+[shadow[0]];
            }
        }
    }
    
} // end of Quack class

method Main() // Dafny 1.9.7
{   var q:= new Quack<char>(10);
    var l: char;
    q.Push('r'); q.Push('s'); q.Push('k'); q.Push('o'); q.Push('w');
    l:= q.Pop(); assert l=='w'; print l;  
    q.HeadTail();
    l:= q.Qop(); assert l=='o'; print l;
    l:= q.Pop(); assert l=='r'; print l;
    q.HeadTail();
    l:= q.Qop(); assert l=='k'; print l;    
    q.HeadTail();
    l:= q.Qop(); assert l=='s'; print l;        
    var e: bool:= q.Empty();
    if e {print "\nqueue empty\n";} else {print "\nqueue not empty\n";}
}
