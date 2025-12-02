include "dafnyTypes.dfy"

ghost function filterMapBySeq(R : Ranking, C : Candidates) : (R_filtered : Ranking)
    /*
    Removes all entries from R which are not in C.

    Input:
        R (Ranking) : A map containing all registered candidates as keys and points achieved in this voting session by those as values
        C (Candidates) : Sequence of registered candidates

    Output:
        R_filtered (Ranking) : A map containing all entries from R that are also in C
    */
    requires forall c :: c in C ==> c in R
    ensures forall k :: k in R_filtered  ==> k in C
    ensures forall c :: c in C ==> c in R_filtered
    ensures forall k :: k in R_filtered ==> k in R && R_filtered[k] == R[k]
    ensures |C| > 0 ==> |R_filtered| > 0
{
    assert |C| > 0 ==> C[0] in C;
    var K := R.Keys * set c | c in C :: c;
    map k | k in K :: R[k]
}

method FilterMapBySeq(R : Ranking, C : Candidates) returns (R_filtered : Ranking)
    /*
    Removes all entries from R which are not in C.

    Input:
        R (Ranking) : A map containing all registered candidates as keys and points achieved in this voting session by those as values
        C (Candidates) : Sequence of registered candidates

    Output:
        R_filtered (Ranking) : A map containing all entries from R that are also in C
    */
    requires forall c :: c in C ==> c in R
    ensures R_filtered == filterMapBySeq(R, C)
{
    R_filtered := map[];
    ghost var C_looped : Candidates := [];
    var i := 0;

    while i < |C|
        invariant 0 <= i <= |C|
        invariant forall k :: k in R_filtered ==> k in C
        invariant forall c :: c in C_looped ==> c in R_filtered && c in C
        invariant C_looped == C[..i]
        invariant forall k :: k in R_filtered ==> R_filtered[k] == R[k]
    {
        R_filtered := R_filtered[C[i] := R[C[i]]];
        C_looped := C_looped + [C[i]];
        i := i + 1;
    }

    assert |C| > 0 ==> C[0] in R_filtered;

    return R_filtered;
}