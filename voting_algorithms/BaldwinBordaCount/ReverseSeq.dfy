ghost function reverseSeq(L : seq ) : (A : seq)
    /*
    Returns L where the order of its elements is reversed.

    Input:
        L (seq) : Sequence

    Output:
        A (seq) : Sequence containing all elements of L in reversed order
    */
    ensures |L| == |A|
    ensures forall i :: 0 <= i < |A| ==> A[i] == L[|L|-1-i]
{
   if |L| == 0 || |L| == 1 then L else reverseSeq(L[1..]) + [L[0]]
}

method ReverseSeq(L : seq ) returns (A : seq)
    /*
    Returns L where the order of its elements is reversed.

    Input:
        L (seq) : Sequence

    Output:
        A (seq) : Sequence containing all elements of L in reversed order
    */
    ensures A == reverseSeq(L)
{
    A := [];
    var i := |L|-1;
    while i >= 0
        invariant -1 <= i <=|L|-1
        invariant A == reverseSeq(L[i+1..])
    {
        A :=  A + [L[i]];
        i := i-1;
    }
}