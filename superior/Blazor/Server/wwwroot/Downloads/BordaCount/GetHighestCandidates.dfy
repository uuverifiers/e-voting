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

include "./MaxSet.dfy"
include "./FilterMapBySeq.dfy"
include "GetCandidatesWithScore.dfy"

ghost function getHighestCandidates(C : Candidates, R: Ranking) : (A : Candidates)
    /*
    Finds all candidates in C with the maximum score in R.

    Input:
        C (Candidates) : Sequence of registered candidates
        R (Ranking) : A map containing all registered candidates as keys and points achieved in this voting session by those as values

    Output:
        A (Candidates) : Sequence containing all top tied candidates
    */
    requires |C|>0
    requires forall c :: c in C ==> c in R
    ensures |A| > 0
    ensures forall a :: a in A ==> a in C
    ensures forall a, a2 :: a in A && a2 in A <==> a in filterMapBySeq(R, C) && a2 in filterMapBySeq(R, C) && R[a] == R[a2] == max(filterMapBySeq(R, C).Values)
    ensures forall a, c :: a in A && c in C && c !in A ==> R[a] > R[c]
    ensures |A| <= |C|
    ensures (forall c :: c in R && R[c] == 0) ==> A == C
{
    var R_filtered : Ranking := filterMapBySeq(R, C);
    var s := max(R_filtered.Values);
    assert forall r :: r in R_filtered ==> R_filtered[r] in R_filtered.Values;

    getCandidateWithScore(R_filtered, C, s)
}

method GetHighestCandidates(C : Candidates, R: Ranking) returns (A : Candidates)
    /*
    Finds all candidates in C with the maximum score in R.

    Input:
        C (Candidates) : Sequence of registered candidates
        R (Ranking) : A map containing all registered candidates as keys and points achieved in this voting session by those as values

    Output:
        A (Candidates) : Sequence containing all top tied candidates
    */
    requires |C|>0
    requires forall c :: c in C ==> c in R
    ensures A == getHighestCandidates(C, R)
{
    var R_filtered := FilterMapBySeq(R, C);
    var s := Max(R_filtered.Values);
    assert forall r :: r in R_filtered ==> R_filtered[r] in R_filtered.Values;

    A := getCandidateWithScore(R_filtered, C, s);
    return A;
}