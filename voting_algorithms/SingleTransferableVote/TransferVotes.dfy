include "./dafnyTypes.dfy"
include "./SetToSeq.dfy"
include "./GetIndices.dfy"
include "./UpdateFactors.dfy"
include "./RemoveCandidate.dfy"
include "./CalculateTotalValue.dfy"

predicate isTransferable(v : PreferenceList, c : Candidate)
//predicate that describes a transferable ballot.
    requires |v| > 0
{
    v[0] == c && |v| > 1
}

predicate isNonTransferable(v : PreferenceList, c : Candidate)
//predicate that describes a non-transferable ballot.
    requires |v| > 0
{
    v[0] == c && |v| == 1
}

predicate existsVotesForCandidate(V : Votes_PreferenceList, c : Candidate)
//predicate that describes the existence of votes for the given candidate
    requires forall i :: 0 <= i < |V| ==> |V[i]| > 0
{
    |getIndicesSet(V, c)| > 0
}

predicate quotaReached(score : real, quota : real)
//predicate that describes when the quota is reached.
{
    score - quota >= 0.0
}

function newFactor(f : real, score : real, quota : real, voteCount : nat) : real
    /*
    Calculates the new factor of a transferable ballot by the Gregory method.

    Input:
        f (real) : Old factor of the ballot
        score (real) : Score achieved by the candidate
        quota (real) : Quota of the election
        voteCount (nat) : Number of votes that currently prefer the candidate

    Output:
        real : New factor of the ballot
    */
    requires voteCount > 0
{
    f*((score - quota) / (voteCount as real))
}

method {:vcs_split_on_every_assert} TransferVotes(V : Votes_PreferenceList, F : FactorList, c : Candidate, q : real, m : real) returns (A0 : Tuple)
    /*
    Transfers votes after electing or eliminating candidate c. Removes c
    from ballots and redistributes votes using the Gregory method.

    Input:
        V (Votes_PreferenceList) : Sequence of the current ballots
        F (FactorList) : Sequence of current value of the ballots
        c (Candidate) : Candidate which was elected or is eliminated
        q (real) : Quota of the election
        m (real) : Current score achieved by the given candidate

    Output:
        A0 : (Updated sequence of ballots, Updated sequence of factors)
    */
    requires forall i :: 0 <= i < |V| ==> |V[i]| > 0
    requires forall v,c :: v in V && c in v ==> multiset(v)[c] == 1
    requires m > 0.0 ==> exists i :: 0 <= i < |V| && V[i][0] == c
    requires |V| == |F|
    requires forall i :: 0 <= i < |F| ==> F[i] >= 0.0

    //Postconditions that secure Output is still valid for input in next iteration
    ensures |A0.0| <= |V|
    ensures |A0.0| == |A0.1| // Votes and factors size match
    ensures forall v :: v in A0.0 ==> |v| > 0 // Output Votes have no empty ballots
    ensures forall v,c :: v in A0.0 && c in v ==> multiset(v)[c] == 1 // All candidates stay unique

    //Postconditions for Votes
    ensures forall i :: 0 <= i < |V| && c !in V[i] ==> V[i] in A0.0 // C not in ballot --> vote doesn't get changed
    ensures forall i :: 0 <= i < |V| && isTransferable(V[i], c) ==> removeSeq(V[i], c) in A0.0 // Transferable votes: updated ballot in new ballot list
    ensures forall i :: 0 <= i < |V| && isNonTransferable(V[i], c) ==> removeSeq(V[i], c) !in A0.0 // Ballots with only c (non-transferable) get removed

    //Postconditions for FactorList
    ensures forall i :: 0 <= i < |A0.1| ==> A0.1[i] >= 0.0
    ensures forall i :: 0 <= i < |V| && c != V[i][0] ==> F[i] in A0.1 // Ballots from other candidates don't loose factor
    ensures forall i :: 0 <= i < |V| && isTransferable(V[i], c) && !quotaReached(m, q) ==> F[i] in A0.1 // Transferable ballots keep factor if quota not reached
    ensures forall i :: 0 <= i < |V| && isTransferable(V[i], c) && quotaReached(m, q) ==> newFactor(F[i], m, q, |getIndicesSet(V, c)|) in A0.1// New factors of transferable votes are in Output

    //Further Postconditions
    ensures forall i :: 0 <= i < |V| && V[i][0] == c <==> i in getIndicesSet(V, c) // All votes for c are in index list

    //PreConditions for last post-condition
    ensures forall i :: 0 <= i < |setToSeq(getIndicesSet(V, c))| ==> setToSeq(getIndicesSet(V, c))[i] < |F|
    ensures existsVotesForCandidate(V, c) && quotaReached(m, q) ==> ((m - q) / (|getIndicesSet(V, c)| as real)) >= 0.0

    //Outputs derive from inputs
    ensures forall i :: 0 <= i < |A0.0| ==> A0.0[i] in removeCandidate(V, c) // No new votes added
    ensures forall i :: 0 <= i < |A0.1| && (!existsVotesForCandidate(V, c) || !quotaReached(m, q)) ==> A0.1[i] in F // If quota isn't reached or no votes for the given candidate exist ==> Output factors are from F
    ensures forall i :: 0 <= i < |A0.1| && existsVotesForCandidate(V, c) && quotaReached(m, q) ==> A0.1[i] in updateFactors(F, setToSeq(getIndicesSet(V, c)), (m - q) / (|getIndicesSet(V, c)| as real), 0) // If quota is reached and votes for the given candidate exist ==> Output factors are correctly 0updated versions from f
{
    var I := GetIndices(V, c);
    
    var s : real := m - q;
    var F1 := F;
    ghost var G1 := F;
    
    if |I| != 0 && s >= 0.0
    {
        var f := s / (|I| as real);
        F1 := UpdateFactors(F, I, f);
        assert forall i :: 0 <= i < |V| && isTransferable(V[i], c) && quotaReached(m, q) ==> F1[i] == newFactor(F[i], m, q, |getIndicesSet(V, c)|); // pc9

        assert (m - q) / (|getIndicesSet(V, c)| as real) >= 0.0;
        G1 := updateFactors(F, I, (m - q) / (|getIndicesSet(V, c)| as real), 0);
        assert F1 == G1;
        ghost var J := getIndicesSet(V, c);
        ghost var JSeq := setToSeq(J);
        IndicesBelowF(V, c, F, m);

        ghost var G0 := updateFactors(F, JSeq, (m - q) / (|getIndicesSet(V, c)| as real), 0);
        assert G1 == G0;
    }
    else
    {
        IndicesBelowF(V, c, F, m);
    }
    
    var V0 := V;
    var c0 := c;
    var V1 := RemoveCandidate(V0, c0);

    A0 := RemoveEmptyBallots(V1, F1);

    return A0;
}

lemma IndicesBelowF(V : Votes_PreferenceList, c : Candidate, F : FactorList, m : real)
    //Shows that the gathered indices aren't out of range
    requires forall i :: 0 <= i < |V| ==> |V[i]| > 0
    requires |V| == |F|
    ensures forall i :: 0 <= i < |setToSeq(getIndicesSet(V, c))| ==> setToSeq(getIndicesSet(V, c))[i] < |F|
{
    ghost var J := getIndicesSet(V, c);
    ghost var JSeq := setToSeq(getIndicesSet(V, c));
    assert forall i :: 0 <= i < |JSeq| ==> JSeq[i] in J;
}