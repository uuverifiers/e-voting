include "./dafnyTypes.dfy"
include "./RemoveCandidate.dfy"


function getIndicesSet(V : Votes_PreferenceList, c : Candidate) : (I : set<nat>)
    /*
    Returns a set of all indices of V where the given Candidate is at the first position of the ballot.

    Input:
        V (Votes_PreferenceList) : Sequence of preference lists
        c (Candidate) : Candidate

    Output:
        I (set<nat>) : Set of indices from V
    */
    requires forall i :: 0 <= i < |V| ==> |V[i]| > 0
    ensures forall i :: 0 <= i < |V| && V[i][0] == c <==> i in I
{
    set i | 0 <= i < |V| && V[i][0] == c :: i
}

lemma incrementalSeq8(s1 : nat, s2 : Indices)
    ensures s2 == ([s1] + s2)[1..]
{
    assert ([s1] + s2)[1..] == s2;
}

function getIndices(V : Votes_PreferenceList, c : Candidate, j : nat) : (I : Indices)
    requires 0 <= j <= |V|
    requires forall i :: 0 <= i < |V| ==> |V[i]| > 0
    ensures forall i :: j <= i < |V| && V[i][0] == c <==> i in I
    ensures forall i :: 0 <= i < |I| ==>  j <= I[i] < |V|
    ensures forall i :: 0 <= i < |I| ==> V[I[i]][0] == c
    ensures forall i,j :: 0 <= i < j < |I| ==> I[i] != I[j]
    ensures forall i :: i in I <==> i-j in getIndicesSet(V[j..], c)
    ensures |I| == |getIndicesSet(V[j..], c)|
    decreases |V|-j
{
    if |V| == j then [] else 
        assert j < |V|;
        incrementalSeq5(V, j);
        assert j !in getIndices(V, c, j+1);
        assert 0 in getIndicesSet(V[j..], c) <==> V[j][0] == c;
            
        assert j !in getIndices(V, c, j+1);
        if V[j][0] == c then 
            assert 0 in getIndicesSet(V[j..], c);
            SeqSetEquality2([j] + getIndices(V, c, j+1), getIndicesSet(V[j..], c), j);
            assert |V| > j >= j;
            [j] + getIndices(V, c, j+1)
        else 
            assert V[j][0] != c;
            SeqSetEquality2(getIndices(V, c, j+1), getIndicesSet(V[j..], c), j);
            getIndices(V, c, j+1)
}

lemma SeqSetEquality2(L : seq<int>, S : set<int>, j : int)
    requires forall i :: i-j in S <==> i in L
    requires forall i,j :: 0 <= j < i < |L| ==> L[i] != L[j]
    ensures |S| == |L|
{

    var i := 0;
    var L0 := [];
    var S0 := {};
    while i < |L|
        invariant 0 <= i <= |L|
        invariant forall k,l :: 0 <= k < l < i ==> L[l] != L[k]
        invariant forall k :: k-j in S0 <==> k in L0
        invariant L0 == L[..i]
        invariant |S0| == i == |L0|
        decreases |L|-i 
    {
        assert |L0| == |S0|;
        assert L[i] !in L[..i] && L[i] !in L0;
        assert L[i]-j !in S0;
        L0 := L0 + [L[i]];
        S0 := S0 + {L[i] - j};
        i := i+1;
    }
    assert L == L0;
    assert forall k :: k in S <==> k+j in L;
    assert forall k :: k in S0 <==> k in S; 
    
    assert S == S0;
    
}
 

lemma SeqSetEquality(L : seq, S : set)
    //ensures that a sequence and a set are equivalent if they contain the same elements and all elements in the sequence are unique.
    requires forall i :: i in S <==> i in L
    requires forall i,j :: 0 <= j < i < |L| ==> L[i] != L[j]
    ensures |S| == |L|
    ensures (set i | i in L :: i) == S
{
    if |L| == 0
    {
    }
    else
    {
        var L0 := L[1..];
        var S0 := S - {L[0]};

        SeqSetEquality(L0, S0);
    }
}

method GetIndices(V : Votes_PreferenceList, c : Candidate) returns (I : Indices)
    /*
    Returns a sequence of all indices of V where the given Candidate is at the first position of the ballot.

    Input:
        V (Votes_PreferenceList) : Sequence of preference lists
        c (Candidate) : Candidate

    Output:
        I (Indices) : Sequence of indices from V
    */
    requires forall i :: 0 <= i < |V| ==> |V[i]| > 0
    ensures forall i :: 0 <= i < |V| && V[i][0] == c <==> i in I
    ensures forall i :: 0 <= i < |I| ==> I[i] < |V|
    ensures forall i :: 0 <= i < |I| ==> V[I[i]][0] == c
    ensures forall i,j :: 0 <= i < j < |I| ==> I[i] != I[j]
    ensures (set i | i in I :: i) == getIndicesSet(V, c)
    ensures |I| == |getIndicesSet(V, c)|
{
    I := [];
    var i := 0;

    while i < |V|
        invariant 0 <= i <= |V|
        invariant forall j :: 0 <= j < i && V[j][0] == c <==> j in I
        invariant forall i :: 0 <= i < |I| ==> I[i] < |V|
        invariant forall k,j :: 0 <= k < j < |I| ==> I[k] != I[j]

    {
        if V[i][0] == c
        {
            I := I + [i];
        }
        i := i + 1;
    }

    SeqSetEquality(I, getIndicesSet(V, c));
}