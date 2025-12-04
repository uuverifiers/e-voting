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

type Candidate = nat
type Candidates = seq<Candidate>

type Vote = Candidate
type PreferenceList = seq<Vote> 
type Votes = seq<PreferenceList>

type Score = nat 
type Ranking = map<Candidate, Score>

type Value = real
type ValueRanking = map<Candidate, Value>

type MaxTieBreaks = nat
type factor = real
type seats = nat

type FactorList = seq<factor>
type Tuple = (Votes, FactorList)
type Indices = seq<nat>
type Triple = (Votes, FactorList, Candidates)


predicate ValidInputs(V : Votes, C : Candidates)
//defines valid inputs for the list of votes and candidates
{
    (1 < |C|) &&
    (forall i, j :: 0 <= i < j < |C| ==> C[i]!= C[j]) &&
    (forall v,c :: v in V && c in v ==> c in C) &&
    (forall v,i,j :: v in V && 0 <= i < j < |v| ==> v[i] != v[j])
}

predicate ValidInputsSTV(V : Votes, C : Candidates)
//defines valid inputs for the list of votes and candidates
{
    (0 < |C|) &&
    (forall c :: c in C ==> multiset(C)[c] == 1) &&
    (forall v,c :: v in V && c in v ==> c in C) &&
    (forall v,c :: v in V && c in v ==> multiset(v)[c] == 1) &&
    (forall i :: 0 <= i < |V| ==> V[i] != [])
}

lemma SeqLogic(S : seq)
//various statements about sequences in Dafny
    ensures |S| > 0 ==> S[0] in S
    ensures forall i :: 0 <= i < |S| ==> S == S[..i] + [S[i]] + S[i+1..]
    ensures forall s :: s !in S <==> forall i :: 0 <= i < |S| ==> s != S[i]
{

}

lemma multiset_lemma1(A:seq<Candidate>)
ensures forall i :: 0 <= i < |A| ==> multiset(A[..i])+ multiset([A[i]]) == multiset(A[..i+1])
{

  assert forall i :: 0 <= i < |A|==> A[..i+1] == A[..i] + [A[i]];
}
lemma multiset_lemma2(A:seq<Candidate>)
ensures forall i :: 0 <= i < |A| ==> multiset(A[..i])+ multiset(A[i..])==multiset(A)
{

  assert forall i :: 0 <= i < |A|==> A[..i]+ A[i..]==A;
}
lemma multiset_lemma3(A:seq<Candidate>)
ensures multiset(A[..|A|]) ==multiset(A)
{

  assert  A[..|A|]==A;
}

lemma Uniqueness(C : seq<int>)
//Shows implication of different uniqueness statements for a list of integers
  requires forall i, j :: 0 <= i < j < |C| ==> C[i]!= C[j]
  ensures forall c :: c in C ==> multiset(C)[c] ==1
{
    var i := 0;
    while i < |C|
        invariant 0 <= i <= |C|
        invariant forall j :: 0 <= j < i ==> multiset(C)[C[j]] == 1
    {
        assert C == C[..i] + [C[i]] + C[i+1..];
        i := i + 1;
    }
}

lemma V_Uniqueness(V : Votes)
//Shows implication of different uniqueness statements for Votes
    requires forall v,i,j :: v in V && 0 <= i < j < |v| ==> v[i] != v[j]
    ensures forall v,c :: v in V && c in v ==> multiset(v)[c] == 1
{
    var i := 0;
    while i < |V|
        invariant 0 <= i <= |V|
        invariant forall j,k :: 0 <= j < i && 0 <= k < |V[j]| ==> multiset(V[j])[V[j][k]] == 1
    {
        Uniqueness(V[i]);
        i := i + 1;
    }
}

lemma SetEquivalence(A : set, B : set)
//Shows equivalence of sets
    requires forall a :: a in A ==> a in B
    requires |A| == |B|
    ensures A == B
{
    if |A| == 0 {}
    else
    {
        var a :| a in A;
        SetEquivalence(A - {a}, B - {a});
    }
}

lemma MultisetEquivalence(A : multiset, B : multiset)
//Shows equivalence of multisets
    requires forall a :: a in A ==> a in B
    requires forall a :: a in A ==> A[a] == 1
    requires |A| == |B|
    ensures A == B
{
    if |A| == 0 {}
    else
    {
        var a :| a in A;
        MultisetEquivalence(A - multiset({a}), B - multiset({a}));
    }

}

lemma SetMultisetEquivalence(A : multiset, B : set)
//Shows equivalence of sets and multisets
    requires forall a :: a in A <==> a in B
    requires forall a :: a in A ==> A[a] == 1
    ensures |A| == |B|
    ensures A == multiset(B)
    ensures (set a | a in A :: a) == B
{
    var A_set := {};
    var A1 := A;

    while |A1| != 0
        invariant |A| == |A1| + |A_set|
        invariant A == A1 + multiset(A_set)
        invariant forall a :: a in A_set ==> a in A
    {
        var c :| c in A1;
        A_set := A_set + {c};
        A1 := A1 - multiset({c});
    }
    assert A_set == B;
}

lemma ElementEquivalence(C : Candidates, A : Candidates)
//Shows equivalence of Candidate lists
    requires forall c :: c in C ==> c in A
    requires forall c :: c in C ==> multiset(C)[c] == 1
    requires |C| == |A|
    ensures forall a :: a in A <==> a in C
    ensures multiset(C) == multiset(A)
{
    var C_mult := multiset(C);
    var A_mult := multiset(A);
    assert forall c :: c in C_mult <==> c in C;
    MultisetEquivalence(C_mult, A_mult);    
}