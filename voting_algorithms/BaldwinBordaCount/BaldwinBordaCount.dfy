include "./CountVotes.dfy"
include "./SortCandidates.dfy"

method BaldwinBordaCount(V : Votes_PreferenceList, C : Candidates, e : nat) returns (R : Ranking, F : Candidates)
    requires ValidInputs(V, C)
    ensures forall c :: c in C ==> c in R
    ensures forall f :: f in F ==> f in R
    ensures e == 0 ==> isSortedDescending(R, F)
    ensures !(|getHighestCandidates(C,R)| > ((|C| as real)/3.0).Floor + 1) ==> forall c :: c in C <==> c in F
    ensures multiset(C) == multiset(F) || (|getHighestCandidates(C,R)| > ((|C| as real)/3.0).Floor + 1 ==> F == [])
    ensures forall c :: c in C ==> R[c] == getScore(V, C, c)
   /*
    Returns a mapping that contains all objects in C mapped to the amount of achieved points by those
    and a list which is sorted descendingly after the corresponding value in that
    mapping. Additionally the ’elimination of the weakest’-tie-breaker is
    applied to the first e placements. If there are > ⌈ |C| / 3 ⌉ ties for the first
    place, an empty list is returned.

    Input:
        V (Votes_PreferenceList) : A two dimensional list of all registered votes structured as list of registered preference lists
        C (Candidates) : A sequence of all registered candidates
        e (nat) : A natural number describing the amount of first places on that a tie must not exist
    Output:
        R (Ranking) : A mapping containing all registered candidates as keys and the amount of achieved points by those as values
        F (Candidates) : A sequence of registered candidates sorted descendingly according to achieved rank
   */ 
{  
    expect ValidInputs(V, C), "Votes or Candidates don't match pre-conditions!";
    expect e >= 0, "e doesn't match pre-conditions!";
    R := countVotes(V, C);
    F := SortCandidates(V, C, R, e);
    return R, F;
}