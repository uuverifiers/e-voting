include "./dafnyTypes.dfy"

function getCandidateWithScore(R: Ranking, C : Candidates, s : Score) : (A : Candidates)
    /*
    Finds all candidates in R with score s.

    Input:
        R (Ranking) : A map containing all registered candidates as keys and points achieved in this voting session by those as values
        s (Score) : A natural number describing the score that the returned candidates have in R

    Output:
        A (Candidates) : Sequence containing all candidates with score s
    */
    requires forall c :: c in C ==> c in R
    ensures forall a :: a in A ==> a in R
    ensures forall a :: a in A ==> R[a] == s
    ensures forall c :: c in C && R[c] == s ==> c in A
    ensures forall a :: a in A ==> a in C //important for SortCandidatesHelper
    ensures |A| <= |C|
    ensures forall a :: a in C && a !in A ==> R[a] != s
    ensures (forall c :: c in R ==> R[c] ==0) && s == 0 ==> A == C
{
    if |C| == 0 then [] else if R[C[0]] == s
    then [C[0]] + getCandidateWithScore(R, C[1..], s)
    else [] + getCandidateWithScore(R, C[1..], s)
}

lemma linearity(R: Ranking, C : Candidates, s : Score)
    requires forall c :: c in C ==> c in R
    ensures forall i :: 0 <= i < |C| ==> getCandidateWithScore(R, [C[i]] + C[i..], s) == getCandidateWithScore(R, [C[i]], s) + getCandidateWithScore(R, C[i..], s)
{
    if |C| == 0
    {
        assert [] == getCandidateWithScore(R, C, s);
    }
    else if R[C[0]] == s
    {
        assert [C[0]] ==  getCandidateWithScore(R, [C[0]], s);
        linearity(R, C[1..], s);
    }
    else
    {
        assert [] ==  getCandidateWithScore(R, [C[0]], s);
        linearity(R, C[1..], s);
    }
}