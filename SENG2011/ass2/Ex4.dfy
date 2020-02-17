predicate ColourSorted(flag:array<Colour>)
  reads flag
  requires flag != null
{ forall i, j::0 <= i < j < flag.Length && j==i+1==> (flag[i] == RED ==> (flag[j] == RED || flag[j] == WHITE)) || (flag[i] == WHITE ==> (flag[j] == WHITE || flag[j] == BLUE))
 || (flag[i] == BLUE ==> (flag[j] == BLUE ||flag[j] == ORANGE)) || (flag[i] == ORANGE ==> flag[j] == ORANGE)}
//the final sort should be like the following colors are grouped together
datatype Colour = RED| WHITE | BLUE | ORANGE 

method FlagSort(flag:array<Colour>)
requires flag != null;
ensures ColourSorted(flag);
ensures multiset(flag[..]) == multiset(old(flag[..]));
modifies flag;
{

  var next := 0;
  var white := 0;
  var orange := flag.Length;//start from the length of array
  
  while(next != orange)
  invariant 0 <= white <= next <= orange <= flag.Length;
  invariant forall i:: orange <= i < flag.Length ==> flag[i]==ORANGE;
  invariant forall i:: white <= i < next ==> (flag[i] == WHITE || flag[i] == BLUE);
  invariant forall i:: 0 <= i <white ==> flag[i]==RED;
  invariant multiset(flag[..]) == multiset(old(flag[..]));
  {
    match(flag[next]){
      //if red then change position with white
      case RED => flag[next],flag[white] := flag[white],flag[next];
                    white := white + 1;
                    next := next + 1;
      //if white go to next
      case WHITE => next := next + 1;
      //if blue go to next
      case BLUE => next := next + 1; 
      //if orange change position with the color with index that is orange 
      case ORANGE => orange := orange - 1; 
                    flag[next],flag[orange] := flag[orange],flag[next];
    }
  }
  var blue := white;
  var n:= white;
 
  if(white < orange){// sort middle
    while(n != orange)
    invariant 0<= white <= blue <= n <= orange <= flag.Length;
    invariant white == old(white) && orange == old(orange);
    invariant forall i:: white <= i < orange ==> (flag[i] == WHITE || flag[i] == BLUE);
    invariant forall i:: 0 <= i< white ==> flag[i]==RED;
    invariant forall i:: white <= i < blue ==> flag[i] == WHITE;
    invariant forall i:: blue<= i < n ==> flag[i] == BLUE;
    invariant forall i:: orange <= i < flag.Length ==> flag[i] == ORANGE;
    invariant multiset(flag[..]) == multiset(old(flag[..]));
    {
      match(flag[n]){
        case RED => n := n + 1;
        //move white before blue
        case WHITE => flag[n],flag[blue] := flag[blue],flag[n];
                      blue := blue + 1;
                      n := n + 1;
        case BLUE => n := n + 1; 
        case ORANGE => n := n + 1;
      } 
    }
  } 
}

method Main()
{ // SUBMIT THIS MAIN METHOD WITH YOUR CODE
    var flag: array<Colour> := new Colour[10];
    flag[0], flag[1], flag[2], flag[3] := ORANGE, BLUE, WHITE, RED;
    flag[4], flag[5], flag[6], flag[7] := ORANGE, BLUE, WHITE, RED;
    flag[8], flag[9] := RED, RED;
    assert flag[..] == [ORANGE,BLUE,WHITE,RED,ORANGE,BLUE,WHITE,RED,RED,RED];
    var ms := multiset(flag[..]);
    FlagSort(flag);
    assert ColourSorted(flag);
    assert ms == multiset(flag[..]);
    print flag[..];
    flag := new Colour[0];
    ms := multiset(flag[..]);
    FlagSort(flag);
    assert ColourSorted(flag);
    assert ms == multiset(flag[..]);
    print flag[..], '\n';
}
