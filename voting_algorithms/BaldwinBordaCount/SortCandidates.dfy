include "./SortCandidatesHelper.dfy"

method SortCandidates(V : Votes_PreferenceList, C : Candidates, R : Ranking, e : nat) returns (A : Candidates)
    requires ValidInputs(V, C)
    requires forall c :: c in C ==> c in R
    requires forall c :: c in C ==> R[c] == getScore(V, C, c)
    ensures forall a :: a in A ==> a in R
    ensures e == 0 ==> isSortedDescending(R, A)
    ensures !(|getHighestCandidates(C,R)| > ((|C| as real)/3.0).Floor + 1) ==> forall c :: c in C <==> c in A
    ensures multiset(C) == multiset(A) || (|getHighestCandidates(C,R)| > ((|C| as real)/3.0).Floor + 1 ==> A == [])
    /*
    Orders candidates by score (from R) with Baldwin’s elimination method applied to the first e positions.
    If more than ⌈ |C| / 3 ⌉ candidates tie for first place, returns an empty list

    Input:
        V (Votes) : Sequence of preference lists to be evaluated
        C (Candidates) : Sequence of registered candidates
        R (Ranking) : A map containing all registered candidates as keys and points achieved in this voting session by those as values
        e (nat) : A natural number describing the amount places on that a tie must not exist

    Output:
        A (Candidates) : A sequence of all registered candidates sorted descendingly according the amount of points achieved in this voting session
    */
{
    var e1 := Min({e,|C|});
    var A1 := GetHighestCandidates(C,R);

    if |A1| > ((|C| as real)/3.0).Floor + 1
    {
        A := [];
    }
    else if e == 0
    {
        A := SortRemainingResults(R, C);
        assert forall c :: c in C <==> c in multiset(C);

    }
    else    
    {
        var R_out;
        var W_out;
        var W_States;
        Uniqueness(C); //ensures Pre-Conditions
        V_Uniqueness(V); //ensures Pre-Conditions
        A, R_out, W_out,W_States := SortCandidatesHelper(V, C, R, e);
        ElementEquivalence(C, A);
        return A;
    }
}