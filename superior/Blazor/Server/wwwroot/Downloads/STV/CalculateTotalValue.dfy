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


function sum_real(sequence : seq<real>) : (result : Value)
    requires forall s :: s in sequence ==> s >= 0.0
    ensures (|sequence| == 0|| forall i :: 0 <= i < |sequence| ==> sequence[i] == 0.0) <==> sum_real(sequence) == 0.0 
    ensures |sequence| > 0 ==> (forall i :: 0 <= i < |sequence[..|sequence| - 1]| ==> sequence[i] >= 0.0) && (sum_real(sequence[..|sequence| - 1]) + sequence[|sequence| - 1] == sum_real(sequence)) 
    ensures |sequence| == 1 ==> result == sequence[0]
    ensures result >= 0.0
    decreases |sequence|
    /*
    Computes the sum of all elements of the given sequence

    Input:
        sequence (seq<nat>) : Sequence of real numbers
    Output:
        result (real) : The sum of all natural numbers contained in the given sequence
    */
{
    if |sequence| == 0 then 
        0.0 
    else 
        assert |sequence| > 0;
        assert forall i :: 0 <= i < |sequence[..|sequence| - 1]| ==> sequence[..|sequence| - 1][i] == sequence[i] && sequence[..|sequence| - 1][i] in sequence;
        assert forall i :: 0 <= i < |sequence[..|sequence| - 1]| ==> sequence[i] >= 0.0;
        assert sequence[|sequence| - 1] in sequence;
        assert sequence[|sequence| - 1] >= 0.0;
        assert sum_real(sequence[..|sequence| - 1]) >= 0.0;
        sequence[|sequence| - 1] + sum_real(sequence[..|sequence| - 1])
}

function relevantFactors(V: Votes, F: FactorList, c: Candidate): (A0 : seq<real>)
    requires |V| == |F|
    requires forall v :: v in V ==> |v| > 0
    requires forall f :: f in F ==> f >= 0.0
    ensures |A0| == |V|
    ensures forall a :: a in A0 ==> a >= 0.0
/*
    Computes the sequence of all factors corresponding to the votes containing the given candidate on the first place or zeros otherwise

    Input:
        V (Votes) : Sequence of all registered preference lists
        F (FactorList) : Sequence of all factors corresponding to the value of the preference list stored at the same index in V as this factor in F
        c (Candidate) : A candidate for whom this calculation is supposed to be executed
    
    Output:
        A0 (seq<real>) : Sequence containing either 0 if the given candidate is not placed on the first place in a certain preference list, or the corresponding factor otherwise
*/
    
{
    if |V| == 0 then
        []
    else 
        if V[|V| - 1][0] == c then
            assert F[|F|-1] in F;
            assert forall i :: 0 <= i < |F[..|F|-1]| ==> F[..|F|-1][i] == F[i] && F[..|F|-1][i] in F;
            relevantFactors(V[..|V|-1], F[..|F|-1], c) + [F[|F|-1]]
        else
            assert forall i :: 0 <= i < |F[..|F|-1]| ==> F[..|F|-1][i] == F[i] && F[..|F|-1][i] in F;
            relevantFactors(V[..|V|-1], F[..|F|-1], c) + [0.0]
}


function calculateTotalValue(V : Votes, C : Candidates, F : FactorList, c : Candidate) : (r : real)
    requires c in C
    requires forall f :: f in F ==> f >= 0.0
    requires forall v, c :: v in V && c in v ==> c in C 
    requires |V| == |F|
    requires forall v :: v in V ==> |v| > 0
    ensures (forall v :: v in V && c !in v) ==> r == 0.0
    ensures r == sum_real(relevantFactors(V, F, c)) 
    ensures exists i :: (0 <= i < |V| && V[i][0] == c ==> r >= F[i])
    ensures r >= 0.0
    ensures |V| > 0 && |F| > 0  && c == V[|V|-1][0] ==> (forall i :: 0 <= i < |F[..|F|-1]| ==> F[i] >= 0.0) && r == calculateTotalValue(V[..|V| - 1], C, F[..|F|-1], c) + F[|F|-1]
    ensures r > 0.0 ==> exists i :: 0 <= i < |V| && V[i][0] == c
    
    /*
    Calculates the amount of first places according to the factors corresponding to the preference lists

    Input:
        V (Votes) : Sequence of all registered preference lists
        F (FactorList) : Sequence of factors corresponding to the preference lists
        c (Candidate) : A candidate whose score should be calculates
    
    Output:
        r (real) : The score of candidate c calculated according to registered preference lists and their corresponding factors
    */
{
    ghost var res := relevantFactors(V, F, c);
    if |V| == 0 then 
        assert forall i :: 0 <= i < |V| ==> V[i][0] != c;
        assert |res| == 0 ==> sum_real(res) == 0.0;
        0.0
    else if V[|V| - 1][0] == c then 
        assert F[|F|-1] in F && V[|V|-1] in V;
        assert forall i :: (0 <= i < |F|-1 ==> F[..|F|-1][i] == F[i] && F[..|F|-1][i] in F);

        assert res[|F| - 1] == F[|F|-1];
        assert sum_real(res) == sum_real(res[..|F|-1]) + res[|F|-1];
        assert sum_real(res[..|F|-1]) == calculateTotalValue(V[..|V|-1], C, F[..|F|-1], c);
        F[|F| - 1] + calculateTotalValue(V[..|V|-1], C, F[..|F|-1], c)
        
    else 
        assert res[|F| - 1] == 0.0;
        assert forall i :: (0 <= i < |F|-1 ==> F[..|F| - 1][i] == F[i] && F[..|F|-1][i] in F);

        calculateTotalValue(V[..|V|-1], C, F[..|F|-1], c)
}


lemma incrementalSeq(V : Votes, F : FactorList, i : nat)
    requires 0 <= i < |V| == |F|
    ensures V[..i+1] == V[..i] + [V[i]] && F[..i+1] == F[..i] + [F[i]]
    ensures V[i..] == [V[i]] + V[i+1..] && F[i..] == [F[i]] + F[i+1..]
    /*
    Proves the property of sequences, describing that the concatenation of the first i elements and the ith element 
    results in the sequence of the first i+1 elements
    */
{
    assert V[..i+1] == V[..i] + [V[i]] && F[..i+1] == F[..i] + [F[i]];
    assert V[i..] == [V[i]] + V[i+1..] && F[i..] == [F[i]] + F[i+1..];
}

lemma rankingValue(V : Votes, C : Candidates, F : FactorList, c : Candidate)
    requires c in C
    requires forall f :: f in F ==> f >= 0.0
    requires forall v, c :: v in V && c in v ==> c in C 
    requires |V| == |F|
    requires forall v :: v in V ==> |v| > 0
    ensures calculateTotalValue(V, C, F, c) > 0.0 ==> exists i :: 0 <= i < |V| && V[i][0] == c
{

}

lemma RankingValue(V : Votes, C : Candidates, F : FactorList, R : map<Candidate, real>)
    requires forall f :: f in F ==> f >= 0.0
    requires forall v, c :: v in V && c in v ==> c in C 
    requires |V| == |F|
    requires forall v :: v in V ==> |v| > 0
    requires forall c:: c in R.Keys ==> c in C
    requires forall c :: c in R ==> R[c] == calculateTotalValue(V, C, F, c) 
    ensures forall c :: c in R && R[c] > 0.0 ==> exists i :: 0 <= i < |V| && V[i][0] == c
    
{
    forall c | c in R
        {rankingValue(V, C, F, c);}
    

}
method CalculateTotalValue(V : Votes, C : Candidates, F : FactorList) returns (R : map<Candidate, real>)
    requires forall f :: f in F ==> f >= 0.0
    requires forall v, c :: v in V && c in v ==> c in C 
    requires |V| == |F|
    requires forall v :: v in V ==> |v| > 0
    ensures forall c :: c in C ==> c in R
    ensures forall c :: c in C ==> R[c] >= 0.0
    ensures forall c :: c in C ==> (forall v :: v in V && c !in v)==> R[c] == 0.0
    ensures forall c :: c in C ==> (exists i :: (0 <= i < |V| && V[i][0] == c ==> R[c] >= F[i]))
    ensures forall c :: c in C ==> R[c] == calculateTotalValue(V, C, F, c) 
    ensures forall c :: c in C ==> R[c] == sum_real(relevantFactors(V, F, c))
    ensures forall r :: r in R.Keys ==> r in C
    ensures forall c :: c in R && R[c] > 0.0 ==> exists i :: 0 <= i < |V| && V[i][0] == c
    
    /*
    Calculates the amount of first places according to the factors corresponding to the preference lists for every registered candidate

    Input:
        V (Votes) : Sequence of all registered preference lists
        C (Candidates) : Sequence of all registered candidates
        F (FactorList) : Sequence of factors corresponding to the preference lists
    
    Output:
        R (map<Candidate, real>) : The score of each candidate c from C calculated according to registered preference lists and their corresponding factors
                                   is stored as the value to the corresponding c, which represents the key
    */
{
    R := map c | c in C :: 0.0;
    var i := 0;
    assert forall v, c :: v in V && c in v ==> c in C;
    
    while i < |V|
        invariant 0 <= i <= |V|
        invariant forall c :: c in C ==> c in R
        invariant forall c :: c in C ==> (forall v :: v in V[..i] && c !in v)==> R[c] == 0.0
        invariant forall v, c :: v in V[..i] && c in v ==> c in C
        invariant forall c :: c in C ==> R[c] >= 0.0
        invariant forall f :: f in F ==> f >= 0.0 
        invariant forall f :: f in F[..i] ==> f in F
        invariant forall c :: c in C ==> R[c] == calculateTotalValue(V[..i], C, F[..i], c)
        invariant forall c :: c in R.Keys ==> c in C
        decreases |V| - i 
    {
        var c := V[i][0];
        assert c in V[i];
        rankingValue(V[..i], C, F[..i], c);
        
        R := R[c := R[c] + F[i]];
        
        incrementalSeq(V, F, i);
        
        assert F[i] in F;
        rankingValue(V[..i] + [V[i]], C, F[..i] + [F[i]], c);
        
        i := i+1;
        
    }
    assert i == |V|;
    assert V[..i] == V[..|V|] == V;
    assert F[..i] == F[..|F|] == F;
    
    RankingValue(V,C, F,R);
}