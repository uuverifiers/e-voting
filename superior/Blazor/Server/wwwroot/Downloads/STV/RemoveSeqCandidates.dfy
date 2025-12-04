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
include "./RemoveCandidate.dfy"


function removeSeqCandidates(s : Candidates, c : Candidate) : (A0 : PreferenceList)
    requires forall c :: c in s ==> multiset(s)[c] == 1
    requires multiset(s)[c] <= 1
    ensures forall i :: 0 <= i < |A0| ==> A0[i] != c
    //ensures forall i :: 0 <= i < |s| && s[i] != c ==> exists j :: 0 <= j < |A0| && A0[j] == s[i] 
    ensures c !in s ==> A0 == s
    ensures s == [c] ==> A0 == []
    ensures forall i,j :: 0 <= j < i < |s| <= |A0|+1 && s[i] == c ==> s[j] == A0[j]
    ensures forall i,j :: 0 <= i < j < |s| <= |A0|+1 && s[i] == c ==> s[j] == A0[j-1]
    //new posts
    ensures c in s ==> |A0| == |s| - 1
    ensures forall a :: a in A0 ==> multiset(A0)[a] == 1
    ensures forall a :: a in A0 ==> a in s
    ensures forall a :: a in s && a != c ==> a in A0
    decreases |s|
/**
    Removes the given element (or candidate) from the given sequence (of votes)

    Input:
        s (PreferenceList) : A sequence of individual votes
        c (Candidate) : The candidate to be removed from the preference list
    
    Output:
        A0 (PreferenceList) : A sequence containing all elements from s in the same order as s except for elements el being equal to c
 */
{
    if c !in s then s else
    assert |s| > 0 ;
    if s[0] == c then 
        assert s == [s[0]]  + s[1..];
        assert forall c :: c in s[1..] ==> c in s;
        assert forall a :: a in s && a != c ==> a in s[1..];
        s[1..]
    else 
        incrementalSeq6(s);
        assert forall c :: c in s[1..] ==> c in s;
        assert forall c :: c in s[1..] ==> multiset(s[1..])[c] <= 1;
        ghost var r := removeSeqCandidates(s[1..], c);
        
        
        assert forall i :: 0 <= i < |r| ==> r[i] in ([s[0]] + r);
        assert s[0] == ([s[0]] + r)[0];
        assert forall a :: a in ([s[0]] +  r) ==> multiset([s[0]] + r)[a] <= 1;

        [s[0]] + removeSeqCandidates(s[1..], c)
}

lemma removeSeqCandidatesLemma(s : Candidates, c : Candidate)
    requires forall c :: c in s ==> multiset(s)[c] <= 1
    requires multiset(s)[c] <= 1
    ensures forall a :: a in s && a != c ==> a in removeSeqCandidates(s, c)
{

}
    

method RemoveSeqCandidates(s : Candidates, c : Candidate) returns (A0 : Candidates)
    requires forall c :: c in s ==> multiset(s)[c] == 1
    requires multiset(s)[c] <= 1
    ensures A0 == removeSeqCandidates(s, c)
    ensures forall i :: 0 <= i < |A0| ==> A0[i] != c
    //ensures forall i :: 0 <= i < |s| && s[i] != c ==> exists j :: 0 <= j < |A0| && A0[j] == s[i] 
    ensures c !in s ==> A0 == s
    ensures s == [c] ==> A0 == []
    ensures forall i,j :: 0 <= j < i < |s| <= |A0|+1 && s[i] == c ==> s[j] == A0[j]
    ensures forall i,j :: 0 <= i < j < |s| <= |A0|+1 && s[i] == c ==> s[j] == A0[j-1]
    //new posts
    ensures c in s ==> |A0| == |s| - 1
    ensures forall a :: a in A0 ==> multiset(A0)[a] == 1
    ensures forall a :: a in A0 ==> a in s
    ensures forall a :: a in s && a != c ==> a in A0
    
{
    A0 := [];
    var i := |s| - 1;
    while i >= 0 
        invariant -1 <= i < |s|
        invariant multiset(s[i+1..])[c] <= 1
        invariant forall c :: c in s[i+1..] ==> multiset(s[i+1..])[c] <= 1
        invariant A0 == removeSeqCandidates(s[i+1..], c)
        decreases i + 1
    {
        assert s == s[..i+1] + s[i+1..];
        assert s[i..] == [s[i]] + s[i+1..];
        if s[i] != c{
            A0 := [s[i]] + A0;
        }
        i := i-1;
        
        assert forall c :: c in s[i+2..] ==> multiset(s[i+2..])[c] <= 1;
        assert multiset(s)[s[i+1]] == 1;
        assert s[i+1..] == [s[i+1]] + s[i+2..];
    }
}

