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

ghost function Pick(S : set<Candidate>) : (s : Candidate)
    /*
    Returns an element from the given set of Candidates.

    Input:
        S (set<Candidate>) : Set of Candidates

    Output:
        s (Candidate) : Candidate
    */
    requires S != {}
    ensures s in S
{
    var s :| s in S;
    s
}

ghost function setToSeq(S : set<Candidate>) : (L: Candidates)
    /*
    Converts a set of Candidates to a sequence of Candidates.

    Input:
        S (set<Candidate>) : Set of Candidates

    Output:
        s (Candidates) : Sequence of Candidates
    */
    ensures forall s :: s in S <==> s in L
    ensures |S| == |L|
    ensures forall i,j :: 0 <= j < i < |L| ==> L[j] != L[i]
{
    if S == {} then [] else var s := Pick(S); [s] + setToSeq(S - {s})
}

method SetToSeq(S : set<Candidate>) returns (L : Candidates)
    /*
    Converts a set of Candidates to a sequence of Candidates.

    Input:
        S (set<Candidate>) : Set of Candidates

    Output:
        s (Candidates) : Sequence of Candidates
    */
    ensures forall s :: s in S <==> s in L
    ensures |S| == |L|
    ensures forall i,j :: 0 <= j < i < |L| ==> L[j] != L[i]
{
    var S_2 := S;
    ghost var S_2_inv := {};
    L := [];

    while S_2 != {}
        invariant S_2 + S_2_inv == S
        invariant S_2 * S_2_inv == {}
        invariant |L| == |S_2_inv|
        invariant forall l :: l in L ==> l in S_2_inv
        invariant forall s :: s in S_2_inv ==> s in L
        invariant forall i,j :: 0 <= j < i < |L| ==> L[j] != L[i]
    {
        var s :| s in S_2;
        S_2_inv := S_2_inv + {s};
        S_2 := S_2 - {s};
        L := L + [s];
    }
    return L;
}