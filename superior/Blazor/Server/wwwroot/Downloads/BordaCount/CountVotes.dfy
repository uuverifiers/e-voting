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

function IndexOf(sequence: PreferenceList, el: Candidate):(x : int)
    /*
    Returns the index of the given element in the given sequence, if the element is contained. Otherwise -1 is returned.
    Input:
        sequence: A sequence of votes
        el: A candidate or vote that might be contained in the sequence
    Output:
        x (int) : -1 if el is not contained in sequence, else an index x with sequence[x] == el

    */
    ensures (0 <= x < |sequence| ==> sequence[x] == el)
    ensures (x == -1 <==> el !in sequence)
    ensures -1 <= x < |sequence|
    decreases sequence
{
    if |sequence| == 0 then -1
    else if sequence[0] == el then 0
    else
        var rest := IndexOf(sequence[1..], el);
        if rest == -1 then -1 else 1 + rest
}

function sum(sequence : seq<nat>) : (result : nat)
    ensures (|sequence| == 0|| forall i :: 0 <= i < |sequence| ==> sequence[i] == 0) <==> sum(sequence) == 0 
    ensures |sequence| > 0 ==> sum(sequence[..|sequence| - 1]) + sequence[|sequence| - 1] == sum(sequence)
    ensures |sequence| == 1 ==> result == sequence[0]
    decreases |sequence|
    /*
    Computes the sum of all elements of the given sequence

    Input:
        sequence (seq<nat>) : Sequence of natural numbers
    Output:
        result (nat) : The sum of all natural numbers contained in the given sequence
    */
{
    if |sequence| == 0 then 
        0 
    else 
        assert |sequence| > 0;
        sequence[|sequence| - 1] + sum(sequence[..|sequence| - 1])
}


function getScore(V : Votes, C : Candidates, c : Candidate) :(result : nat)
    requires forall v, cand :: (v in V) && (cand in v) ==> cand in C
    requires forall v :: v in V ==> (forall i, j :: 0 <= i < j < |v| ==> v[i] != v[j])
    requires c in C 
    ensures |V| > 0 ==> result == (if IndexOf(V[|V|-1], c) == -1 then 0 else |V[|V|-1]| - IndexOf(V[|V|-1], c)) + getScore(V[..|V|-1], C, c)
    ensures |V| == 0 ==> result == 0
    /*
    Evaluates a list of preference lists for a certain registered candidate and returns the amount of points this one has achieved

    Input:
        V (Votes) : sequence of preference lists given by voters
        C (Candidates) : sequence of registered candidates
        c (Candidate) : a candidate whose achieved amount of points should be computed
    Output:
        result (nat) : the achieved amount of points by c
    */
    
{
    if |V| == 0 then 0
    else
        var score := if c in V[|V|-1] then |V[|V|-1]| - IndexOf(V[|V|-1], c) else 0; //if the candidate is not in this vote he gets 0 points, else |vote| - index points
        assert forall v :: v in V[..|V|-1] ==> v in V; 
        getScore(V[..|V|-1], C,c) + score
    
}



method countVotes(V : Votes, C : Candidates) returns (R : Ranking)
    requires forall c,v :: (v in V) && (c in v) ==> c in C
    requires forall v :: v in V ==> forall i,j :: 0<= i < j < |v| ==> v[i] != v[j]
    requires |C| >= 0
    ensures forall c :: c in C ==> c in R
    ensures forall c :: c in C ==> R[c] == getScore(V, C,c)
    /*
    Evaluates the given list of preferenceLists for the registered candidates and creates a mapping saving the achieved amount of points for every registered candidate

    Input:
        V (Votes) : sequence of preference lists given by voters
        C (Candidates) : sequence of registered candidates
    Output:
        R (Ranking) : a ranking containing registered candidates as keys and their achieved points in this voting session as values
    */
{
    // initialization of a ranking
    R := map c | c in C :: 0;
    var i := 0;
        
    while i < |V|
        invariant 0 <= i <= |V|
        invariant forall c :: c in C ==> c in R 
        invariant forall c :: c in C ==> R[c] == getScore(V[..i], C,c)
    {   
        var j := |V[i]|-1;
            
        // the vote that is to be evaluated
        var preferenceList := V[i];

        assert forall c :: c in C ==> R[c] == getScore(V[..i], C,c);
        assert forall c :: c in C ==> R[c] == getScore(V[..i] + [preferenceList[j+1..]], C,c);
            
        while j >= 0
            invariant -1 <= j <= |V[i]|-1
            invariant forall c :: c in preferenceList ==> c in C
            invariant forall c :: c in C ==> c in R 
            invariant forall c :: c in C ==> R[c] == getScore(V[..i] + [preferenceList[j+1..]], C,c)
        {
                
            var c := preferenceList[j];
            // forall candidates in the vote, the achieved amount of points is |preferenceList| - index of this candidate in this vote
            // --> evaluating backwards
            var new_points := |preferenceList| - j;
            var new_ranking := R[c] + new_points;

            // add the achieved amount of points from this vote to the last score
            R := R[c := new_ranking];
            j := j-1;             
        }
                       
        assert j == -1;
        assert V[..i] + [preferenceList[j+1..]] == V[..i+1];  
        i := i+1;
           
        assert forall c :: c in C ==> R[c] == getScore(V[..i], C,c);    
    }
        
    assert V[..i] == V[..|V|] == V;
    
}  


