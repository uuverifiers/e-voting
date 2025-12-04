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


function delete(S : PreferenceList, el : Vote) : (S_new : PreferenceList)
    requires multiset(S)[el] <= 1
    ensures forall s :: s in S_new ==> s != el
    ensures el in S ==> |S_new| == |S|-1
    ensures el !in S ==> S_new == S 

    ensures multiset(S_new)<= multiset(S) // important for SortCandidatesHelper
    ensures |S| != 0 && multiset(S)[el] == 1==> multiset(S_new) + multiset([el]) == multiset(S) //important for SortCandidatesHelper
    ensures forall i, k :: 0 <= i < |S| && S[i] == el && 0 <= k < i ==> S[k] == S_new[k] //important for new Elim
    ensures forall i, k :: 0 <= i < |S| && S[i] == el && i < k < |S| ==> S[k] == S_new[k-1] // //important for new Elim
    /*
        Deletes the given element of the given sequence if the element is contained in it, otherwise the same sequence is returned

        Input:
            S (PreferenceList) : A sequence from that the element should be removed
            el (Vote) : The element to remove
        Output:
            S_new (PreferenceList) : The sequence perserving the order of elements in the sequence S, yet removing only the element el
    */

{
    if |S| == 0 then [] else 
        assert S == [S[0]] + S[1..];
        (if S[0] == el then 
            S[1..] 
        else 
            [S[0]] + delete(S[1..], el))
}

//new EliminateLowestCandidate with more detailed contract, 
// but without function call
// this is used to verify SortCandidateshelper 
method elim(V: Votes, l: Candidate, C: Candidates) returns (V_new: Votes)
requires forall i :: 0 <= i < |V| ==> multiset(V[i])[l] <= 1
requires |V|>0
requires forall c,v :: (v in V) && (c in v) ==> c in C // new
requires forall v,c :: v in V && c in v ==> multiset(v)[c] <= 1 // new

ensures |V_new| == |V|
ensures forall i :: 0 <= i < |V| && l in V[i] ==> |V[i]| - 1 == |V_new[i]|
ensures forall i :: 0 <= i < |V| && l !in V[i] ==> |V[i]| == |V_new[i]|
ensures forall i :: 0 <= i < |V| ==> l !in V_new[i]
ensures forall i :: 0 <= i < |V| ==> forall k, j :: 0 <= j < |V[i]| && V[i][j] == l && 0 <= k < j ==> V[i][k] == V_new[i][k]
ensures forall i :: 0 <= i < |V| ==> forall k, j :: 0 <= j < |V[i]| && V[i][j] == l && j < k < |V[i]| ==> V[i][k] == V_new[i][k-1]
ensures forall v,c :: v in V_new && c in v ==> multiset(v)[c] <= 1
ensures forall c,v :: (v in V_new) && (c in v) ==> c in C
{
  V_new := [];
  var i := |V|;
  while i >0

    invariant |V_new|<=|V|
    invariant |V_new| == |V|-i 
    invariant forall k :: 0 <= k <|V_new| ==> l !in V_new[k]
    invariant forall k :: 0 <= k <|V_new|&& l in V[k] ==> |V[k]| - 1 == |V_new[k]|
    invariant forall k :: 0 <= k <|V_new|&& l !in V[k] ==> |V[k]|  == |V_new[k]|
    invariant forall k,j,p :: 0 <= k <|V_new| && 0 <= j < |V[k]| && 0 <= p < j &&V[k][j] == l ==>V[k][p] == V_new[k][p]
    invariant forall k,j,p :: 0 <= k <|V_new| && 0 <= j < |V[k]| && j < p < |V[k]| &&V[k][j] == l ==>V[k][p] == V_new[k][p-1]
    invariant forall v,c :: v in V_new && c in v ==> multiset(v)[c] <= 1
    invariant forall c,v :: v in V_new && c in v ==> c in C
    decreases i
  {
    var original_vote := V[|V|-i];
    var new_vote := delete(original_vote, l);
    MultisetEqualityImpliesElementInclusion(new_vote,original_vote);

    V_new := V_new + [new_vote];
    i := i - 1;
  }
}

lemma MultisetEqualityImpliesElementInclusion<T>(s1: seq<T>, s2: seq<T>)
  requires multiset(s1) <= multiset(s2)
  ensures forall x :: x in s1 ==> x in s2
{
  forall x | x in s1
    ensures x in s2
  {
    assert multiset(s1)[x] >= 1;
    assert multiset(s2)[x] >= 1;
  }
}