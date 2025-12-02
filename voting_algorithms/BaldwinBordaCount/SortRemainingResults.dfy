include "./dafnyTypes.dfy"


predicate isSortedDescending(R: map<Candidate, nat>, C: seq<Candidate>)
// Predicate to define what a sorted sequence is
  requires forall c :: c in C ==> c in R
{
  forall i, j :: 0 <= i < j < |C| ==> R[C[i]] >= R[C[j]]
}

method mergeMethod(R: map<Candidate, nat>, left: seq<Candidate>, right: seq<Candidate>) returns (A: seq<Candidate>)
// Merge-Step of MergeSort Algorithm
  requires forall x :: x in left || x in right ==> x in R
  requires isSortedDescending(R, left)
  requires isSortedDescending(R, right)
  ensures forall x :: x in A ==> x in R
  ensures isSortedDescending(R, A)
  ensures multiset(A) == multiset(left) + multiset(right)
{
  var i, j := 0, 0;
  A := [];
  while i < |left| && j < |right|
    invariant 0 <= i <= |left|
    invariant 0 <= j <= |right|
    invariant forall x :: x in A ==> (x in left) || (x in right)
    invariant multiset(A) == multiset(left[..i]) + multiset(right[..j])
    invariant forall x :: x in A ==> (i < |left| ==> R[x] >= R[left[i]]) && (j < |right| ==> R[x] >= R[right[j]])
    invariant isSortedDescending(R, A)
    
  {
    multiset_lemma1(left);
    multiset_lemma1(right);
    if R[left[i]] >= R[right[j]] {
      A := A + [left[i]];
      i := i + 1;      
    } else {
      A := A + [right[j]];
      j := j + 1;
    }

  }
  assert i < |left| ==> right[..j] == right;
  assert j < |right| ==> left[..i] == left;

  if i < |left| {
    A := A + left[i..];
    multiset_lemma2(left);
    assert multiset(A) == multiset(left)  + multiset(right[..j]);
  } else if j < |right|{
    A := A + right[j..];
    multiset_lemma2(right);
    assert multiset(A) == multiset(left[..i])  + multiset(right);
  } else{
    assert i == |left| && j == |right|;
    assert multiset(A) == multiset(left[..i]) + multiset(right[..j]);
    multiset_lemma3(right);
    multiset_lemma3(left);
  }
  
}

method SortRemainingResults(R: map<Candidate, nat>, C: seq<Candidate>) returns (A: seq<Candidate>)
// method to sort Candidates by their Ranking implementing MergSort
requires |C| >= 0
requires forall c :: c in C ==> c in R
ensures forall x :: x in A ==> x in R
ensures isSortedDescending(R, A)
ensures multiset(A) == multiset(C)
{ 
  if |C|==0{
    A:=[];
  }
  else if |C| == 1 {
    A := C;
  } else {
    var split := |C| / 2;
    var left:= C[..split];
    var right:= C[split..];
    


    left:= SortRemainingResults(R, left);
    right:= SortRemainingResults(R, right);
    
    assert C[..split] + C[split..] == C;
    assert multiset(left)+multiset(right) == multiset(C);


    A:=mergeMethod(R,left,right);
  }
}