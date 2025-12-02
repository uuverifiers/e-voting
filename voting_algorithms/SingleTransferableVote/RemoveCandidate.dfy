include "./dafnyTypes.dfy"
include "./CalculateTotalValue.dfy"

function removeSeq(s : PreferenceList, c : Candidate) : (A0 : PreferenceList)
    requires forall c :: c in s ==> multiset(s)[c] <= 1
    requires multiset(s)[c] <= 1
    ensures forall i :: 0 <= i < |A0| ==> A0[i] != c
    //ensures forall i :: 0 <= i < |s| && s[i] != c ==> exists j :: 0 <= j < |A0| && A0[j] == s[i] 
    ensures c !in s ==> A0 == s
    ensures s == [c] ==> A0 == []
    ensures forall i,j :: 0 <= j < i < |s| <= |A0|+1 && s[i] == c ==> s[j] == A0[j]
    ensures forall i,j :: 0 <= i < j < |s| <= |A0|+1 && s[i] == c ==> s[j] == A0[j-1]
    //new posts
    ensures c in s ==> |A0| == |s| - 1
    ensures forall a :: a in A0 ==> multiset(A0)[a] <= 1
    ensures forall a :: a in A0 ==> a in s
    decreases |s|
/**
    Removes the given element (or candidate) from the given sequence (of votes)

    Input:
        s (PreferenceList) : A sequence of individual votes
        c (Candidate) : The candidate to be removed from the preference list
    
    Output:
        A0 (PreferenceList) : A sequence containing all elements from s in the same order as s except for elements el being equal to c
 */
{
    if c !in s then s else
    assert |s| > 0 ;
    if s[0] == c then 
        assert s == [s[0]]  + s[1..];
        assert forall c :: c in s[1..] ==> c in s;

        s[1..]
    else 
        incrementalSeq6(s);
        assert forall c :: c in s[1..] ==> c in s;
        assert forall c :: c in s[1..] ==> multiset(s[1..])[c] <= 1;
        ghost var r := removeSeq(s[1..], c);

        assert forall i :: 0 <= i < |r| ==> r[i] in ([s[0]] + r);
        assert s[0] == ([s[0]] + r)[0];
        
        assert forall a :: a in ([s[0]] +  r) ==> multiset([s[0]] + r)[a] <= 1;
        [s[0]] + removeSeq(s[1..], c)
}



lemma RemoveSeqLemma(s : PreferenceList, c : Candidate)
    requires forall c :: c in s ==> multiset(s)[c] <= 1
    requires multiset(s)[c] <= 1
    ensures forall i,j :: 0 <= j < i < |s| <= |removeSeq(s,c)|+1 && s[i] == c ==> s[j] == removeSeq(s,c)[j]
    ensures forall i,j :: 0 <= i < j < |s| <= |removeSeq(s,c)|+1 && s[i] == c ==> s[j] == removeSeq(s,c)[j-1]
    ensures forall a :: a in removeSeq(s, c) ==> multiset(removeSeq(s,c))[a] <= 1   
    ensures c in s ==> |s|-1 == |removeSeq(s,c)|
    ensures forall i :: 0 <= i < |removeSeq(s,c)| ==> removeSeq(s, c)[i] != c
    ensures forall i :: 0 <= i < |s| && s[i] != c ==> exists j :: 0 <= j < |removeSeq(s,c)| && removeSeq(s,c)[j] == s[i] 
    
{
    ghost var A0 := removeSeq(s, c);
    assert forall i,j :: 0 <= j < i < |s| <= |A0|+1 && s[i] == c ==> s[j] == A0[j];
    assert forall i,j :: 0 <= i < j < |s| <= |A0|+1 && s[i] == c ==> s[j] == A0[j-1];
}

function removeCandidate(V : Votes_PreferenceList, c : Candidate) : (A0 : Votes_PreferenceList)
    requires forall i,c :: 0 <= i < |V| && c in V[i] ==> multiset(V[i])[c] <= 1 
    requires forall i :: 0 <= i < |V| ==> multiset(V[i])[c] <= 1
    ensures forall v, i :: v in A0 && 0 <= i < |v| ==> v[i] != c
    //ensures forall i, j :: 0 <= i < |V| == |A0| && 0 <= j < |V[i]| && V[i][j] != c ==> exists k :: 0 <= k < |A0[i]| && V[i][j] ==A0[i][k] && A0[i] == removeSeq(V[i], c)
    ensures |V| == |A0|
    ensures forall i :: 0 <= i < |V| == |A0|  ==> A0[i] == removeSeq(V[i], c)
    ensures forall i :: 0 <= i < |V| && c !in V[i] ==> V[i] == A0[i]
    ensures forall i,j,k :: 0 <= i < |V| == |A0| && 0 <= j < k < |V[i]| <= |A0[i]|+1 && V[i][k] == c ==> V[i][j] == A0[i][j] && A0[i] == removeSeq(V[i], c)
    ensures forall i,j,k :: 0 <= i < |V| == |A0| && 0 <= k < j < |V[i]| <= |A0[i]|+1 && V[i][k] == c ==> V[i][j] == A0[i][j-1]
    ensures forall i :: 0 <= i < |A0| ==> c !in A0[i]
    //new posts
    ensures forall i,c :: 0 <= i < |A0| && c in A0[i] ==> multiset(A0[i])[c] <= 1
    ensures forall i :: 0 <= i < |V| ==> c in V[i] ==> |A0[i]| == |V[i]| - 1
    ensures forall i, a :: 0 <= i < |V| == |A0| && a in A0[i] ==> a in V[i]
    decreases |V|
/**
    Removes the given candidate from the given sequence of registered preference lists

    Input:
        V (Votes_PreferenceList) : Sequence of all registered preference lists
        c (Candidate) : The candidate to be removed from each preference list in V

    Output:
        A0 (Votes) : Sequence of preference lists created from V by removing c from every preference list in V while pereserving their order 
 */
{
    if |V| == 0 then V else 
        assert |V| > 0;
        incrementalSeq2(V);
        ghost var r := removeCandidate(V[1..], c);
        ghost var s := removeSeq(V[0], c);
        assert forall i,j :: 0 <= i < |r| && 0 <= j < |r[i]| ==> r[i][j] in ([removeSeq(V[0], c)] + removeCandidate(V[1..], c))[i+1];
        assert s == removeSeq(V[0], c);
        
        RemoveSeqLemma(V[0], c);
        assert s == ([s] + r)[0];
        [removeSeq(V[0], c)] + removeCandidate(V[1..], c)
}

lemma incrementalSeq2(s : Votes_PreferenceList)
    requires |s| > 0
    ensures s == [s[0]] + s[1..]
{
    assert s == [s[0]] + s[1..];
}

lemma incrementalSeq3(s : PreferenceList, i : nat)
    requires -1 <= i < |s|
    ensures s == s[..i+1] + s[i+1..]
{
    assert s == s[..i+1] + s[i+1..];
}


lemma incrementalSeq4(s : PreferenceList, i : nat)
    requires -1 <= i < |s|
    ensures s[i..] == [s[i]] + s[i+1..]
{
    assert s[i..] == [s[i]] + s[i+1..];
}
lemma incrementalSeq5(s : Votes_PreferenceList, i : nat)
    requires -1 <= i < |s|
    ensures s[i..] == [s[i]] + s[i+1..]
{
    assert s[i..] == [s[i]] + s[i+1..];
}

lemma incrementalSeq6(s : PreferenceList)
    requires |s| > 0
    ensures s == [s[0]] + s[1..]
{
    assert s == [s[0]] + s[1..];
}


lemma RemoveVotes(V : Votes_PreferenceList, c : Candidate)
    requires forall i :: 0 <= i < |V| ==> multiset(V[i])[c] <= 1
    requires forall i,c :: 0 <= i < |V| && c in V[i] ==> multiset(V[i])[c] <= 1 
    ensures forall i,j,k :: 0 <= i < |V| == |removeCandidate(V, c)| && 0 <= j < k < |V[i]| <= |removeCandidate(V, c)[i]|+1 && V[i][k] == c ==> V[i][j] == removeCandidate(V, c)[i][j] && removeCandidate(V, c)[i] == removeSeq(V[i], c)
    ensures forall i,j,k :: 0 <= i < |V| == |removeCandidate(V, c)| && 0 <= k < j < |V[i]| <= |removeCandidate(V, c)[i]|+1 && V[i][k] == c ==> V[i][j] == removeCandidate(V, c)[i][j-1]
{
    forall i | 0 <= i < |V|{
        RemoveSeqLemma(V[i], c);
    }
}


method RemoveCandidate(V : Votes_PreferenceList, c : Candidate) returns (A0 : Votes_PreferenceList)
    requires forall i :: 0 <= i < |V| ==> multiset(V[i])[c] <= 1
    requires forall i,a :: 0 <= i < |V| && a in V[i] ==> multiset(V[i])[a] <= 1 
    ensures A0 == removeCandidate(V,c)
    ensures forall i :: 0 <= i < |V| == |A0| ==> A0[i] == removeSeq(V[i], c)
    ensures |A0| == |V|
    ensures forall v, i :: v in A0 && 0 <= i < |v| ==> v[i] != c
    //ensures forall i, j :: 0 <= i < |V| == |A0| && 0 <= j < |V[i]| && V[i][j] != c ==> exists k :: 0 <= k < |A0[i]| && V[i][j] ==A0[i][k]
    ensures forall i :: 0 <= i < |V| && c !in V[i] ==> V[i] == A0[i]
    ensures forall i,j,k :: 0 <= i < |V| == |A0| && 0 <= j < k < |V[i]| <= |A0[i]|+1 && V[i][k] == c ==> V[i][j] == A0[i][j] && A0[i] == removeSeq(V[i], c)
    ensures forall i,j,k :: 0 <= i < |V| == |A0| && 0 <= k < j < |V[i]| <= |A0[i]|+1 && V[i][k] == c ==> V[i][j] == A0[i][j-1]
    ensures forall i :: 0 <= i < |A0| ==> c !in A0[i]
    //new posts
    ensures forall i :: 0 <= i < |V| ==> c in V[i] ==> |A0[i]| == |V[i]| - 1
    ensures forall i,c :: 0 <= i < |A0| && c in A0[i] ==> multiset(A0[i])[c] <= 1
    ensures forall i, a :: 0 <= i < |V| == |A0| && a in A0[i] ==> a in V[i]
    
    
/**
    Removes the given candidate from the given sequence of registered preference lists

    Input:
        V (Votes_PreferenceList) : Sequence of all registered preference lists
        c (Candidate) : The candidate to be removed from each preference list in V

    Output:
        A0 (Votes) : Sequence of preference lists created from V by removing c from every preference list in V while pereserving their order 
 */
{
    A0 := [];
    var i := |V|-1;

    while i >= 0
        invariant -1 <= i <= |V|-1
        invariant |A0| == |V[i+1..]|
        invariant forall k, a :: 0 <= k < |V[i+1..]| && a in V[i+1+k] ==> multiset(V[i+1+k])[a] <= 1
        invariant A0 == removeCandidate(V[i+1..], c)
        decreases i+1
    {
        var l := [];
        var j := |V[i]|-1;

        assert V[i] in V;
        assert multiset(V[i])[c] <= 1;
        assert forall a :: a in V[i] ==> multiset(V[i])[a] <= 1;
        assert A0 == removeCandidate(V[i+1..], c);
        while j >= 0
            invariant -1 <= j <= |V[i]|-1
            invariant multiset(V[i][j+1..])[c] <= 1
            invariant forall a :: a in V[i][j+1..] ==> multiset(V[i][j+1..])[a] <= 1
            invariant l == removeSeq(V[i][j+1..], c)
            decreases j+1
        {
            incrementalSeq3(V[i], j);
            assert multiset(V[i][j+1..])[c] <= 1;
            assert forall a :: a in V[i][j+1..] ==> multiset(V[i][j+1..])[a] <= 1;
            RemoveSeqLemma(V[i][j+1..], c);
            if V[i][j] != c {
                l := [V[i][j]] + l;
            }
            incrementalSeq4(V[i], j);
            j := j-1;
            assert multiset(V[i][j+1..])[c] <= 1;
            assert multiset(V[i])[V[i][j+1]] == 1;
            incrementalSeq4(V[i], j+1);
            assert forall a :: a in V[i][j+1..] ==> multiset(V[i][j+1..])[a] <= 1;
            RemoveSeqLemma(V[i][j+1..], c);
        }
        assert j == -1;
        assert V[i][j+1..] == V[i][0..] == V[i];
        assert multiset(V[i])[c] <= 1;
        
        A0 := [l] + A0;
        incrementalSeq5(V, i);
        i := i - 1;
    }
    assert i == -1;
    assert V[i+1..] == V[0..] == V;
    
}

lemma incrementalSeq7(s1 : PreferenceList, s2 : Votes_PreferenceList)
    ensures ([s1] + s2)[1..] == s2
{
    assert ([s1] + s2)[1..] == s2;
}


lemma emptyBallots(V : Votes_PreferenceList, F : FactorList)
    requires |V| == |F| > 0
    requires forall i,j :: 0 <= i < |V| && 0 <= j < |V[i]| ==> multiset(V[i])[V[i][j]] <= 1
    ensures multiset([V[0]] + removeEmptyBallots(V[1..], F[1..]).0) == multiset([V[0]]) + multiset(removeEmptyBallots(V[1..], F[1..]).0)
    decreases |V|
{
    var (V0, F0) := removeEmptyBallots(V[1..], F[1..]);
    assert V == [V[0]] + V[1..];
    assert multiset([V[0]] + V0) == multiset([V[0]]) + multiset(V0);        
}    

function removeEmptyBallots(V : Votes_PreferenceList, F : FactorList) : (A0 : Tuple)
    requires |V| == |F|
    requires forall i,j :: 0 <= i < |V| && 0 <= j < |V[i]| ==> multiset(V[i])[V[i][j]] <= 1
    ensures |A0.0| == |A0.1|
    ensures forall v :: v in A0.0 ==> |v| > 0
    ensures forall i :: 0 <= i < |V| && |V[i]| > 0 ==> exists j :: 0 <= j < |A0.0| && A0.0[j] == V[i] && A0.1[j] == F[i]
    ensures forall i :: 0 <= i < |V| && |V[i]| > 0 ==> V[i] in A0.0 && F[i] in A0.1
    ensures |V| >= |A0.1|
    ensures forall i :: 0 <= i < |A0.0| ==> A0.0[i] in V
    ensures forall i :: 0 <= i < |A0.1| ==> A0.1[i] in F
    ensures forall i,j :: 0 <= i < |A0.0| && 0 <= j < |A0.0[i]| ==> multiset(A0.0[i])[A0.0[i][j]] <= 1
    //decreases |V| + |F|
/**
    Removes all empty preference lists from V as well as their corresponding factors from F

    Input: 
        V (Votes_PreferenceList) : A sequence of all registered preference lists
        F (FactorList) : A sequence of factors corresponding to the preference list at the same index of V

    Output:
        V0 (Votes) : A sequence of all non-empty registered preference lists
        F0 (FactorList) : A sequence of all factors corresponding to preference lists in V0
 */
{
    if |V| == 0 then (V, F) else if |V[0]| == 0 then 
        assert V == [V[0]] + V[1..];
        removeEmptyBallots(V[1..], F[1..]) 
    else 
        assert |V| == |F| > 0;
        assert V == [V[0]] + V[1..];
        assert |V[1..]| == |F[1..]| < |V| == |F|;
        var (V0, F0) := removeEmptyBallots(V[1..], F[1..]);
        assert forall i :: 0 <= i < |V0| ==> V0[i] in ([V[0]] + V0);
        assert V[0] == ([V[0]] + V0)[0] && |V[0]| > 0;
        assert F[0] == ([F[0]] + F0)[0] && |V[0]| > 0;
        assert forall i :: 0 <= i < |F0| ==> F0[i] == ([F[0]] + F0)[i+1];
        assert V[0] in V;
        assert F[0] in F;
        assert multiset([V[0]] + V0) == multiset([V[0]]) + multiset(V0);
        incrementalSeq7(V[0], V0);
        ([V[0]] + V0, [F[0]] + F0)
}


method RemoveEmptyBallots(V : Votes_PreferenceList, F : FactorList) returns (A0 : Tuple)
    requires |V| == |F|
    requires forall i,j :: 0 <= i < |V| && 0 <= j < |V[i]| ==> multiset(V[i])[V[i][j]] <= 1
    ensures |A0.0| == |A0.1|
    ensures forall v :: v in A0.0 ==> |v| > 0
    ensures forall i :: 0 <= i < |V| && |V[i]| > 0 ==> exists j :: 0 <= j < |A0.0| && A0.0[j] == V[i] && A0.1[j] == F[i]
    ensures A0 == removeEmptyBallots(V, F)
    ensures forall i :: 0 <= i < |V| && |V[i]| > 0 ==> V[i] in A0.0 && F[i] in A0.1
    ensures |V| >= |A0.1|
    ensures forall i,j :: 0 <= i < |A0.0| && 0 <= j < |A0.0[i]| ==> multiset(A0.0[i])[A0.0[i][j]] <= 1
    ensures forall i :: 0 <= i < |A0.0| ==> A0.0[i] in V
    ensures forall i :: 0 <= i < |A0.1| ==> A0.1[i] in F
    
/**
    Removes all empty preference lists from V as well as their corresponding factors from F

    Input: 
        V (Votes_PreferenceList) : A sequence of all registered preference lists
        F (FactorList) : A sequence of factors corresponding to the preference list at the same index of V

    Output:
        V0 (Votes) : A sequence of all non-empty registered preference lists
        F0 (FactorList) : A sequence of all factors corresponding to preference lists in V0
 */
{
    var V0 := [];
    var F0 := [];
    var i := |V|-1;
    while i >= 0
        invariant -1 <= i <= |V|-1
        invariant |F0| == |V0|
        invariant forall v :: v in V0 ==> |v| > 0 
        invariant forall k :: (0 <= k < |V[i+1..]| && |V[k+i+1]| > 0) ==> exists j :: 0 <= j < |V0| == |F0| && V0[j] == V[k+i+1] && F0[j] == F[k+i+1]
        invariant (V0,F0) == removeEmptyBallots(V[i+1..], F[i+1..])
        decreases i
    {
        if |V[i]| > 0{
            V0 := [V[i]] + V0;
            F0 := [F[i]] + F0;
        }
        assert |V[i]| == 0 ==> V[i] !in V0;
        i := i-1;
        assert (V0, F0) == removeEmptyBallots(V[i+1..], F[i+1..]); 
    }
    A0 := (V0, F0);
}