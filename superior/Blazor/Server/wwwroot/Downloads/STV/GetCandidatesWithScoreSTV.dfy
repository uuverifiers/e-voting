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