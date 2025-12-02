include "./dafnyTypes.dfy"

function getCandidatesWithScoreSTVHelper(R: ValueRanking, C : Candidates, s : Value) : (A : Candidates)
    /*
    Recursive helper function for getCandidatesWithScoreSTV. Finds all candidates in R with score s.

    Input:
        R (Ranking) : A map containing all active candidates as keys and the current value of their ballots as values
        C (Candidates) : Sequence of all active candidates
        s (Value) : A real number describing the score that the returned candidates have in R

    Output:
        A (Candidates) : Sequence of all candidates in R with value s
    */
    requires forall c :: c in C ==> c in R
    ensures forall a :: a in A ==> a in R
    ensures forall a :: a in A ==> R[a] == s
    ensures forall c :: c in C && R[c] == s ==> c in A
{
    if |C| == 0 then [] else if R[C[0]] == s
    then [C[0]] + getCandidatesWithScoreSTVHelper(R, C[1..], s)
    else [] + getCandidatesWithScoreSTVHelper(R, C[1..], s)
}

function getCandidatesWithScoreSTV(R: ValueRanking, C : Candidates, s : Value) : (A : Candidates)
    /*
    Finds all candidates in R with score s.

    Input:
        R (Ranking) : A map containing all active candidates as keys and the current value of their ballots as values
        C (Candidates) : Sequence of all active candidates
        s (Value) : A real number describing the score that the returned candidates have in R

    Output:
        A (Candidates) : Sequence of all candidates in R with value s
    */
    requires forall c :: c in C ==> c in R
    requires forall r :: r in R.Keys ==> r in C
    ensures forall a :: a in A ==> a in R
    ensures forall a :: a in A ==> R[a] == s
    ensures forall c :: c in C && R[c] == s ==> c in A
    ensures forall r :: r in R.Keys ==> R[r] == s ==> r in A
{
    getCandidatesWithScoreSTVHelper(R, C, s)
}