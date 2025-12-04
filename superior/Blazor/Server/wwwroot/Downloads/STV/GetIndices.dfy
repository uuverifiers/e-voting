// Formally verified E-Voting using Dafny
// Copyright (C) 2025 Authors Superior Group
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU Affero General Public License as
// published by the Free Software Foundation, either version 3 of the
// License, or (at your option) any later version.
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
// See the GNU Affero General Public License for more details.
// You should have received a copy of the GNU Affero General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

include "./dafnyTypes.dfy"
include "./RemoveCandidate.dfy"
/*function getIndicesHelper(V : Votes, c : Candidate, i : nat) : (I : Indices)
    requires forall i :: 0 <= i < |V| ==> |V[i]| > 0
    requires i == |V|-1
    ensures forall i :: 0 <= i < |V| && V[i][0] == c && |V[i]| > 1 <==> i in I
    ensures forall i :: 0 <= i < |I| ==> I[i] < |V|
    ensures forall i :: 0 <= i < |I| ==> V[I[i]][0] == c && |V[I[i]]| > 1
    ensures forall i,j :: 0 <= i < j < |I| ==> I[i] != I[j]
{
    if i == 0 && V[0][0] == c && |V[0]| > 1 then [i]
    else if i == 0 then []
    else if V[i][0] == c && |V[i]| > 1 then getIndicesHelper(V[..i], c, i-1) + [i]
    else getIndicesHelper(V[..i], c, i-1)
}

function getIndices(V : Votes, c : Candidate) : (I : Indices)
    requires forall i :: 0 <= i < |V| ==> |V[i]| > 0
    ensures forall i :: 0 <= i < |V| && V[i][0] == c && |V[i]| > 1 <==> i in I
    ensures forall i :: 0 <= i < |I| ==> I[i] < |V|
    ensures forall i :: 0 <= i < |I| ==> V[I[i]][0] == c && |V[I[i]]| > 1
    ensures forall i,j :: 0 <= i < j < |I| ==> I[i] != I[j]
{
    if |V| == 0 then [] else getIndicesHelper(V, c, |V|-1)
*/

function getIndicesSet(V : Votes, c : Candidate) : (I : set<nat>)
    /*
    Returns a set of all indices of V where the given Candidate is at the first position of the ballot.

    Input:
        V (Votes) : Sequence of preference lists
        c (Candidate) : Candidate

    Output:
        I (set<nat>) : Set of indices from V
    */
    requires forall i :: 0 <= i < |V| ==> |V[i]| > 0
    ensures forall i :: 0 <= i < |V| && V[i][0] == c <==> i in I
    //ensures forall i :: i in I ==> i < |V|
    //ensures forall i :: i in I ==> V[i][0] == c && |V[i]| > 1
{
    set i | 0 <= i < |V| && V[i][0] == c :: i
}

//lemma IndicesLemma(V : Votes, c : Candidate, j : nat)
//    requires forall i :: 0 <= i < |V| ==> |V[i]| > 0
//    requires 0 <= j < |V|
//    ensures j in getIndicesSet(V[j..], c) <==> V[j][0] == c 
/*{
    assert V[j] in V[j..];
    assert V[j..] ==  [V[j]] + V[j+1..];
    ghost var I := getIndicesSet(V[j..], c);
    //assert forall 
}*/

lemma incrementalSeq8(s1 : nat, s2 : Indices)
    ensures s2 == ([s1] + s2)[1..]
{
    assert ([s1] + s2)[1..] == s2;
}

function /*{:vcs_split_on_every_assert}*/ getIndices(V : Votes, c : Candidate, j : nat) : (I : Indices)
    requires 0 <= j <= |V|
    requires forall i :: 0 <= i < |V| ==> |V[i]| > 0
    ensures forall i :: j <= i < |V| && V[i][0] == c <==> i in I
    ensures forall i :: 0 <= i < |I| ==>  j <= I[i] < |V|
    ensures forall i :: 0 <= i < |I| ==> V[I[i]][0] == c
    ensures forall i,j :: 0 <= i < j < |I| ==> I[i] != I[j]
    ensures forall i :: i in I <==> i-j in getIndicesSet(V[j..], c)
    //ensures (set i | i in I :: i-j) == getIndicesSet(V[j..], c)
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

lemma /*{: vcs_split_on_every_assert}*/ SeqSetEquality2(L : seq<int>, S : set<int>, j : int)
    requires forall i :: i-j in S <==> i in L
    requires forall i,j :: 0 <= j < i < |L| ==> L[i] != L[j]
    //requires (set i | i in L :: i-j) == S
    ensures |S| == |L|
    //ensures forall i :: i-j in S <==> i in L
    
    //ensures (set i | i in L :: i-j) == S
    //decreases |L|,|S|
{

    var i := 0;
    var L0 := [];
    var S0 := {};
    //assert L[..i] == [];
    //assert L == L[..i] + L[i..];
    while i < |L|
        invariant 0 <= i <= |L|
        invariant forall k,l :: 0 <= k < l < i ==> L[l] != L[k]
        invariant forall k :: k-j in S0 <==> k in L0
        invariant L0 == L[..i]
        invariant |S0| == i == |L0|
        //invariant (set i | i in L0 :: i-j ) == S0
        //invariant forall s :: s in L[i..] <==> s - j in S - S0
        decreases |L|-i 
    {
        assert |L0| == |S0|;
        //assert L[..i+1] == L[..i] + [L[i]];
        //assert L[i..] == [L[i]] + L[i+1..];
        //assert forall l :: l in L[..i] ==> l in L;
        assert L[i] !in L[..i] && L[i] !in L0;
        assert L[i]-j !in S0;
        L0 := L0 + [L[i]];
        S0 := S0 + {L[i] - j};
        //assert L[i] in L0 && L[i]-j in S0;
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
        //assert |S| == 0;
    }
    else
    {
        var L0 := L[1..];
        var S0 := S - {L[0]};

        SeqSetEquality(L0, S0);
    }
}

method GetIndices(V : Votes, c : Candidate) returns (I : Indices)
    /*
    Returns a sequence of all indices of V where the given Candidate is at the first position of the ballot.

    Input:
        V (Votes) : Sequence of preference lists
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
    //ghost var J0 := {};
    var i := 0;

    while i < |V|
        invariant 0 <= i <= |V|
        invariant forall j :: 0 <= j < i && V[j][0] == c <==> j in I
        invariant forall i :: 0 <= i < |I| ==> I[i] < |V|
        invariant forall k,j :: 0 <= k < j < |I| ==> I[k] != I[j]
        //invariant |I| == |getIndicesSet(V[..i], c)|
        //invariant I == getIndices(V[..i], c)
    {
        if V[i][0] == c
        {
            //assert i !in I;
            I := I + [i];
            //J0 := J0 + {i};
            //assert forall i :: i in I <==> i in J0;
            //SeqLogic(I);
            //assert forall i :: 0 <= i < |I| ==> I[i] !in I[..i] + I[i+1..];
            //assert forall i :: 0 <= i < |I| ==> multiset(I)[I[i]] == 1;
            //assert |I| == |J0|;
        }
        i := i + 1;
    }

    SeqSetEquality(I, getIndicesSet(V, c));
    //assert |I| == |getIndicesSet(V, c)|;
    /*SeqSetEquality(getIndices(V, c), getIndicesSet(V, c));
    assert |getIndices(V, c)| == |getIndicesSet(V, c)|;
    assert |I| == |getIndices(V, c)|;
    assert I == getIndices(V, c);

    assert forall i :: i in I <==> i in getIndices(V, c);
    assert forall j,k :: 0 <= j < |I| && 0 <= k < |I| && j != k ==> I[j] != I[k];
    assert forall j,k :: 0 <= j < |getIndices(V, c)| && 0 <= k < |getIndices(V, c)| && j != k ==> getIndices(V, c)[j] != getIndices(V, c)[k];
    ghost var J := set j | j in I :: j;
    ghost var K := set k | k in getIndices(V, c) :: k;
    assert J == K;
    assert forall j :: 0 < j < |I| ==> I[j] != I[j-1];
    assert forall i :: i in I <==> i in J;
    assert |J| == |K|;
    //assert |I| == |K|;
    SeqSetEquality(I, J);
    assert |I| == |J|;
    */
    //assert exists j,k :: 0 <= j < |I| && 0 <= k < |I| && j != k && I[j] == I[k];
    //assert |J| == |I|;
    //assert |I| == |getIndices(V, c)|;
    //assert |set i | i in I :: i| == |I|;
    //assert forall i,j :: 0 <= i < j < |getIndices(V, c)| ==> getIndices(V, c)[i] != getIndices(V, c)[j];

    //assert forall j :: j in getIndices(V, c) ==> j in I;


    //assert forall j :: 0 <= j < |I| ==> I[j] == getIndices(V, c)[j];
    //assert forall j :: 0 <= j < |getIndices(V, c)| ==> getIndices(V, c)[j] in I;
    //assert I == getIndices(V, c);


    //assert forall j :: j in I  ==> j in getIndicesHelper(V, c, |V|-1);
    //assert |I| == |getIndicesHelper(V, c, |V|-1)|;
}