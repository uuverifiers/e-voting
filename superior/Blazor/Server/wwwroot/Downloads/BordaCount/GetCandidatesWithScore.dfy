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

/*lemma linearity2(R: Ranking, C : Candidates, s : Score)
    requires forall c :: c in C ==> c in R
    ensures forall i :: 0 <= i < |C| ==> getCandidateWithScore(R, C[..i] + [C[i]], s) == getCandidateWithScore(R, C[..i], s) + getCandidateWithScore(R, [C[i]], s)
{
    if |C| == 0
    {
        assert [] == getCandidateWithScore(R, C, s);
    }
    else if R[C[|C|-1]] == s
    {
        assert C[..|C|-1] + [C[|C|-1]] == C[..|C|];
        assert [C[|C|-1]] ==  getCandidateWithScore(R, [C[|C|-1]], s);
        assert getCandidateWithScore(R, C[..|C|-1], s) + getCandidateWithScore(R, [C[|C|-1]], s) == getCandidateWithScore(R, C[..|C|-1], s) + [C[|C|-1]];
        assert getCandidateWithScore(R, C[..|C|-1] + [C[|C|-1]], s) == getCandidateWithScore(R, C[..|C|-1], s) + [C[|C|-1]];
        assert getCandidateWithScore(R, C[..|C|-1] + [C[|C|-1]], s) == getCandidateWithScore(R, C[..|C|-1], s) + getCandidateWithScore(R, [C[|C|-1]], s);
        
        linearity2(R, C[..|C|-1], s);
        assume false;
    }
    else
    {
        assert C[..|C|-1] + [C[|C|-1]] == C[..|C|];
        assert [] ==  getCandidateWithScore(R, [C[|C|-1]], s);
        assume false;
        //linearity2(R, C[..|C|-1], s);
    }
}

/*method GetCandidateWithScore(R: Ranking, C : Candidates, s : Score) returns (A : Candidates)
    requires forall c :: c in C ==> c in R
    ensures A == getCandidateWithScore(R, C, s)
    /*ensures forall a :: a in A ==> a in R
    ensures forall a :: a in A ==> R[a] == s
    ensures forall a :: a in R.Keys && R[a] == s ==> a in A*/
{
    var i := 0;
    A := [];
    assert A == getCandidateWithScore(R, C[..i], s);
    assert forall i :: 0 <= i < |C| ==> C[i] in R;
    linearity(R, C, s);
    assert forall i :: 0 <= i < |C| ==> getCandidateWithScore(R, [C[i]] + C[i..], s) == getCandidateWithScore(R, [C[i]], s) + getCandidateWithScore(R, C[i..], s);
    assume |C| > 5;

    if R[C[i]] == s
    {
            A := A + [C[i]];
    }
    i := i + 1;
    assert A == getCandidateWithScore(R, C[..i], s);



    assume false;
    
    while i < |C|
        invariant 0 <= i <= |C|
        invariant A == getCandidateWithScore(R, C[..i], s)
        
    {
        assert forall c :: c in C ==> c in R;
        assert C[i] in R;
        assert A == getCandidateWithScore(R, C[..i], s);
        assert R[C[i]] == s ==> A + [C[i]] == getCandidateWithScore(R, C[..i], s) + [C[i]];
        if R[C[i]] == s
        {
            A := A + [C[i]];
        }
        assert R[C[i]] == s ==> C[i] in A;
        i := i + 1;
        assert A == getCandidateWithScore(R, C[..i], s);
    }
    return A;
}