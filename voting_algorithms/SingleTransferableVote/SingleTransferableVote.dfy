include "./MaxSetSTV.dfy"
include "./MinSetSTV.dfy"
include "./GetCandidatesWithScoreSTV.dfy"
include "./TransferVotes.dfy"
include "./RemoveCandidate.dfy"
include "./CalculateTotalValue.dfy"
include "./RemoveSeqCandidates.dfy"

lemma RankingLemma(R : map<Candidate, real>, V : Votes_PreferenceList, F : FactorList,m : Value, C : Candidates)
    requires forall c :: c in C ==> c in R
    requires forall c :: c in R.Keys ==> c in C
    requires |R.Values| > 0
    requires forall f :: f in F ==> f >= 0.0
    requires forall v, c :: v in V && c in v ==> c in C 
    requires |V| == |F|
    requires forall v :: v in V ==> |v| > 0
    requires forall c :: c in R ==> R[c] == calculateTotalValue(V, C, F, c)
    requires m == maxSTV(R.Values) || m == minSTV(R.Values)
    ensures m > 0.0 ==> R[getCandidatesWithScoreSTV(R, C, m)[0]] > 0.0
    ensures |R.Values| == 0 ==> m == 0.0
    ensures getCandidatesWithScoreSTV(R, C, m)[0] in C
    ensures m > 0.0 ==> exists i :: 0 <= i < |V| && V[i][0] == getCandidatesWithScoreSTV(R, C, m)[0]
    ensures m > 0.0 ==> exists v :: v in V && getCandidatesWithScoreSTV(R, C, m)[0] in v
{
    ghost var C1 := getCandidatesWithScoreSTV(R, C, m);
    assert C1[0] in C1;
    assert m > 0.0 ==> R[C1[0]] > 0.0;
    assert forall i :: 0 <= i < |V| ==> V[i] in V;
}

lemma removingLemma(V : Votes_PreferenceList, A0 : Votes_PreferenceList, C : Candidates, c : Candidate)
    requires forall i,c :: 0 <= i < |V| && c in V[i] ==> multiset(V[i])[c] <= 1 
    requires forall i :: 0 <= i < |V| ==> multiset(V[i])[c] <= 1
    requires forall v,c :: v in V && c in v ==> c in C
    requires forall i :: 0 <= i < |A0| ==> A0[i] in removeCandidate(V, c)
    ensures forall i, a :: 0 <= i < |V| == |removeCandidate(V, c)| && a in removeCandidate(V, c)[i] ==> a in V[i]
    ensures forall v,c :: v in A0 && c in v ==> c in C
    ensures forall a,c :: a in A0 && c in a ==> exists v :: v in V && c in v 
{
    assert forall i, a :: 0 <= i < |V| == |removeCandidate(V, c)| && a in removeCandidate(V, c)[i] ==> a in V[i];
}

lemma candidatesLemma(C : Candidates, W : Candidates, c : Candidate, s : seats)
    requires c in C
    requires forall c :: c in C && s - |W| != 0 ==> c !in W 
    requires s - |W| != 0
    requires forall a :: a in C ==> multiset(C)[a] <= 1 
    ensures c !in W 
    ensures forall a :: a in C && a != c ==> a in removeSeqCandidates(C, c)
    ensures forall a :: a in removeSeqCandidates(C, c) ==> multiset(removeSeqCandidates(C, c))[a] == 1
    ensures forall a :: a in removeSeqCandidates(C, c) ==> a in C
    ensures c in C ==> c !in W
{
}

lemma winnersUniqueness(V : Votes_PreferenceList, W : Candidates,  C : Candidates ,c : Candidate)
    requires c !in W && c in C
    requires forall c :: c in W ==> exists v :: v in V && c in v
    requires exists v :: v in V && c in v
    requires forall c :: c in W ==> multiset(W)[c] == 1
    ensures forall a :: a in W + [c] ==> multiset(W + [c])[a] == 1
    ensures forall a :: a in (W + [c]) ==> exists v :: v in V && a in v
    {
    }

lemma containmentLemma(V : Votes_PreferenceList)
    ensures forall i :: 0 <= i < |V| ==> V[i] in V
{
}

lemma concatenationLemma(stateSet : seq<Triple>, V0 :Votes_PreferenceList, F0 : FactorList, C0 : Candidates, W : Candidates, V : Votes_PreferenceList, s : seats)
    requires |W| == |stateSet| + 1 
    requires forall i :: 0 <= i < |stateSet| ==> |stateSet[i].0| == |stateSet[i].1| && (forall v,c :: v in stateSet[i].0 && c in v ==> c in stateSet[i].2) && (forall v :: v in stateSet[i].0 ==> |v| > 0) && (W[i] in stateSet[i].2) && (forall f :: f in stateSet[i].1 ==> f >= 0.0)
    requires forall v,c :: v in V0 && c in v ==> c in C0
    requires forall v :: v in V0 ==> |v| > 0
    requires |V0| == |F0|
    requires forall f :: f in F0 ==> f >= 0.0
    requires W[|W|-1] in C0
    requires forall i :: 0 <= i < |stateSet| ==> calculateTotalValue(stateSet[i].0, stateSet[i].2, stateSet[i].1, W[i]) >= (((((|V| as real)/ (s + 1) as real)) + 1.0).Floor) as real
    requires calculateTotalValue(V0, C0, F0, W[|W|-1]) >= (((((|V| as real)/ (s + 1) as real)) + 1.0).Floor) as real
    ensures |W| == |(stateSet + [(V0, F0 , C0)])|
    ensures forall i :: 0 <= i < |stateSet + [(V0, F0 , C0)]| ==> |(stateSet + [(V0, F0 , C0)])[i].0| == |(stateSet + [(V0, F0 , C0)])[i].1| && (forall v,c :: v in (stateSet + [(V0, F0 , C0)])[i].0 && c in v ==> c in (stateSet + [(V0, F0 , C0)])[i].2) && (forall v :: v in (stateSet + [(V0, F0 , C0)])[i].0 ==> |v| > 0) && (W[i] in (stateSet + [(V0, F0 , C0)])[i].2) && (forall f :: f in (stateSet + [(V0, F0 , C0)])[i].1 ==> f >= 0.0)
    ensures forall i :: 0 <= i < |(stateSet + [(V0, F0 , C0)])| == |W| ==> calculateTotalValue((stateSet + [(V0, F0 , C0)])[i].0, (stateSet + [(V0, F0 , C0)])[i].2, (stateSet + [(V0, F0 , C0)])[i].1, W[i]) >= (((((|V| as real)/ (s + 1) as real)) + 1.0).Floor) as real
{

}

method {:vcs_split_on_every_assert} SingleTransferableVote(V : Votes_PreferenceList, C : Candidates, s : seats) returns (W : Candidates, Rest : Candidates, stateSet : seq<Triple>)
    requires ValidInputsSTV(V, C)
    requires s <= |C|
    ensures |W| + |Rest| == s
    ensures forall c :: c in W ==> c in C
    ensures forall c :: c in Rest ==> c in C
    ensures forall c :: c in W ==> multiset(W)[c] == 1
    ensures forall c :: c in Rest ==> multiset(Rest)[c] == 1
    ensures forall c :: c in W ==> c !in Rest
    ensures forall c :: c in Rest ==> c !in W
    ensures s == |C| <==> Rest == C && W == []
    ensures forall c :: c in W ==> exists v :: v in V && c in v
    ensures |W| == |stateSet|
    ensures forall i :: 0 <= i < |stateSet| ==> |stateSet[i].0| == |stateSet[i].1| && (forall v,c :: v in stateSet[i].0 && c in v ==> c in stateSet[i].2) && (forall v :: v in stateSet[i].0 ==> |v| > 0) && (W[i] in stateSet[i].2) && (forall f :: f in stateSet[i].1 ==> f >= 0.0)
    ensures forall i :: 0 <= i < |W| ==> calculateTotalValue(stateSet[i].0, stateSet[i].2, stateSet[i].1, W[i]) >= (((((|V| as real)/ (s + 1) as real)) + 1.0).Floor) as real
/*
    Evaluates the sequence of registered votes and registered candidates with respect to the given number of desired seats according to the Single Transferable Vote 
    voting rule and returns a sorted sequence of winners, unsorted sequence of s - |W| candidates due to the AUTOFILL rule and a sequence of states
    in that a unique winner was classified

    Input:
        V (Votes_PreferenceList) : Sequence of all registered votes
        C (Candidates) : Sequence of all registered candidates
        s (seats) : The desired number of seats
    
    Output:
        W (Candidates) : Sorted sequence of uniquelly classified winners
        Rest (Candidates) : Unsorted sequence of candidates, needed to fullfill all s seats
        stateSet (seq<Triple>) : Sequence of states in that a unique winner was classified 
 */    
{
    expect ValidInputsSTV(V, C), "Votes or Candidates don't match pre-conditions!";
    expect 0 <= s <= |C|, "Seat count doesn't match pre-conditions!";

    var q := (((((|V| as real)/ (s + 1) as real)) + 1.0).Floor) as real;
    assert q > 0.0;
    W := [];
    Rest := [];
    var F : FactorList := seq(|V|, i => 1.0);
    var F0 := F;
    var C0 := C;
    var V0 := V;
    assert V0 == V;
    assert C == C0;
    assert forall c :: c in W ==> exists v :: v in V && c in v;
    stateSet := [];
    
    ghost var Wpre : Candidates := W;
    ghost var Vpre: Votes_PreferenceList := V0;
    ghost var Fpre : FactorList := F0;
    ghost var Cpre : Candidates := C0;
    assert W == [];
    while |W| + |Rest| < s
        invariant 0 <= |W| + |Rest| <= s
        invariant forall v, c :: v in V0 && c in v ==> c in C0
        invariant |C0| >= s - |W| >= 0
        invariant forall v :: v in V0 ==> |v| > 0
        invariant |V0| == |F0|
        invariant forall f :: f in F0 ==> f >= 0.0
        invariant forall v,c :: v in V0 && c in v ==> multiset(v)[c] == 1
        invariant forall c :: c in C0 ==> multiset(C0)[c] == 1
        invariant forall c :: c in C0 ==> c in C
        invariant forall c :: c in W ==> c in C 
        invariant forall c :: c in C0 ==> c !in W
        invariant forall c :: c in W ==> c !in C0
        invariant Rest == [] || Rest == C0
        invariant forall c :: c in W ==> multiset(W)[c] == 1
        invariant s == |C| ==> C0 == C
        invariant s == |C| ==> (W == [] && (Rest == [] || Rest == C))
        invariant Rest == C && W == [] ==> s == |C|
        invariant forall v0,c :: v0 in V0 && c in v0 ==> exists v :: v in V && c in v
        invariant forall c :: c in W ==> exists v :: v in V && c in v
        invariant |Vpre| == |Fpre|
        invariant forall v :: v in Vpre ==> |v| > 0
        invariant forall v,c :: v in Vpre && c in v ==> c in Cpre
        invariant forall f :: f in Fpre ==> f >= 0.0
        invariant Wpre != W ==> |W| > 0 && W[|W|-1] in Cpre 
        invariant Wpre != W ==> |W| > 0 && W[|W| - 1] in W && calculateTotalValue(Vpre, Cpre, Fpre, W[|W|-1]) >= q
        invariant |stateSet| == |W|
        invariant forall i :: 0 <= i < |stateSet| ==> |stateSet[i].0| == |stateSet[i].1| && (forall v,c :: v in stateSet[i].0 && c in v ==> c in stateSet[i].2) && (forall v :: v in stateSet[i].0 ==> |v| > 0) && (W[i] in stateSet[i].2) && (forall f :: f in stateSet[i].1 ==> f >= 0.0)
        invariant forall i :: 0 <= i < |W| ==> calculateTotalValue(stateSet[i].0, stateSet[i].2, stateSet[i].1, W[i]) >= q
        decreases s - |W| - |Rest| + |C0|
    {
        assert s == |C| ==> C0 == C;
        assert forall c :: c in W ==> multiset(W)[c] == 1;
        assert Rest != C;
        assert forall c :: c in W ==> exists v :: v in V && c in v;
        assert forall i :: 0 <= i < |stateSet| ==> |stateSet[i].0| == |stateSet[i].1| && (forall v,c :: v in stateSet[i].0 && c in v ==> c in stateSet[i].2) && (forall v :: v in stateSet[i].0 ==> |v| > 0) && (W[i] in stateSet[i].2) && (forall f :: f in stateSet[i].1 ==> f >= 0.0);
        assert forall i :: 0 <= i < |W| ==> calculateTotalValue(stateSet[i].0, stateSet[i].2, stateSet[i].1, W[i]) >= q;
 
        Vpre := V0;
        Fpre := F0;
        Cpre := C0;
        
        Wpre := W;
            
        if |C0| == s - |W|
        {
            Rest := C0;
            
            assert Rest == C0;
            assert s == |C| ==> Rest == C;
            assert |W| + |Rest|== s;
            assert forall c :: c in W ==> c !in Rest;
            
        }
        else
        {   
            assert s < |C|;
            assert Rest == [];
            assert |C0| > s - |W|;
            
            assert forall v,c :: v in V0 && c in v ==> c in C0; 
            var R := CalculateTotalValue(V0, C0, F0);
            assert forall c :: c in R && R[c] > 0.0 ==> exists i :: 0 <= i < |V0| && V0[i][0] == c;
            assert C0[0] in R; 
            var m : real := MaxSTV(R.Values);
            if m < q{
                m := MinSTV(R.Values);
            }
            assert forall i :: 0 <= i < |F0| ==> F0[i] in F0;
            var C1 := getCandidatesWithScoreSTV(R, C0, m);

            candidatesLemma(C0, W, C1[0], s);
            assert C1[0] in C0 ==> C1[0] in C;
            assert C1[0] in C0 ==> C1[0] !in W;

            assert m == R[C1[0]];
            assert m == calculateTotalValue(V0, C0, F0, C1[0]);
            RankingLemma(R,V0 , F0, m, C0);
            assert m > 0.0 ==> exists v :: v in V && C1[0] in v;
            
            assert Wpre == W;
            if m >= q {
                assert m > 0.0;
                
                winnersUniqueness(V, W, C, C1[0]);
                assert forall c :: c in W ==> exists v :: v in V && c in v;
                W := W + [C1[0]];
                
                assert W == Wpre + [C1[0]];
                
                concatenationLemma(stateSet, V0, F0, C0, W, V, s);
                stateSet := stateSet + [(V0, F0, C0)];
                
            }
            
            assert m == calculateTotalValue(Vpre, Cpre, Fpre, C1[0]); 
            assert Wpre == W <==> m < q;
            assert Wpre + [C1[0]] == W <==> m >= q;
             
            
            var A0 : Tuple := TransferVotes(V0, F0, C1[0], q, m);
            containmentLemma(V0);
            removingLemma(V0,A0.0, C0, C1[0]);
            
            V0 := A0.0;
            F0 := A0.1;
            
            C0 := RemoveSeqCandidates(C0, C1[0]);                
            assert m > 0.0 ==> exists v :: v in V && C1[0] in v;
            assert forall c :: c in W ==> multiset(W)[c] == 1;
              
        }

    }
    assert |W| + |Rest| == s;
    assert forall c :: c in C0 <== c in Rest;
}