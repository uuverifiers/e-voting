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

include "./MinSet.dfy"
include "./ReverseSeq.dfy"
include "./SetToSeq.dfy"
include "./GetHighestCandidates.dfy"
include "./CountVotes.dfy"
include "./SortRemainingResults.dfy"
include "./EliminateLowestCandidate.dfy"


// Updated version of SortCandidatesHelper
// - recursion changed to While-Loop
// - calls easy to verify sub-methods to verify if-else faster
method SortCandidatesHelper (Votes_in: Votes, Candidates_in: Candidates, Ranking_in: Ranking, MaxTieBreaks: nat) 
returns (Candidates_out : Candidates, R_out: Ranking, W_out: Candidates)

requires |Votes_in|>0
//requires |Candidates_in| >= 0
requires forall c :: c in Candidates_in ==> multiset(Candidates_in)[c] <=1
requires forall c :: c in Candidates_in ==> c in Ranking_in
requires forall v,c :: v in Votes_in && c in v ==> multiset(v)[c] <= 1
requires forall v,c :: v in Votes_in && c in v ==> c in Candidates_in
//requires isSortedDescending(Ranking_in,Candidates_in)

ensures forall c :: c in W_out ==> c in R_out
ensures forall c :: c in Candidates_in ==> c in Candidates_out // all Candidates of Candidates_in are still in 
ensures |Candidates_out| == |Candidates_in| // Number of Candidates doesnt change
ensures |W_out|<=MaxTieBreaks // at most "MaxTieBreaks" many tie breaks
{
  var V, C, R := Votes_in, Candidates_in, Ranking_in;
  var L : Candidates := [];
  var W : Candidates := [];
  var WC:Candidates := W + C;
  var dec:= |C|;


  while dec > 0
    invariant forall c :: c in C==> c in R
    invariant forall w :: w in WC==> w in R
    invariant forall v,c :: v in V && c in v ==> multiset(v)[c] <= 1
    invariant forall c :: c in C ==> multiset(C)[c] <=1
    invariant WC == W + C
    invariant forall c,v :: (v in V) && (c in v) ==> c in WC
    invariant forall c :: c in Candidates_in ==> c in C || c in W || c in L
    invariant dec == |C|
    invariant |V|>0
    invariant |Candidates_in| == |C|+|W|+|L|
    invariant |W|<= MaxTieBreaks
    decreases dec
  {
    var A1 := GetHighestCandidates(C, R);
    if |W| >= MaxTieBreaks || |A1| == |C|{
      // If Max number of Ties are broken
      // or all remaing Candidates have the same Ranking -> no fair Tie break possible 
      W_out := W;
      var C_sorted := SortRemainingResults(R, C);
      Candidates_out := W_out + C_sorted + L;
      return Candidates_out,R,W_out;
    }
    if |A1|==1{
      // If one of the remaining Candidate has a strictly higher Rating then every other Candidate
      V,C,R,W,L,WC := handleIf(V,C,R,W,L,WC,Candidates_in,MaxTieBreaks);
    } else {
      // If more than one remaining Candidate have the highest Rating together
      V,C,R,W,L,WC := handleElse(V,C,R,W,L,WC,Candidates_in,MaxTieBreaks);
    }
    dec := dec-1;
  }
  W_out := W;
  var C_sorted := SortRemainingResults(R, C);
  Candidates_out := W_out + C_sorted + L;
  return Candidates_out,R,W_out;
}


// Adds the Single highest ranked Candidate to the Winners and removes this Candidate from the remaining Candidates List
method handleIf(V: Votes, C: Candidates, R: Ranking, W: Candidates,L: Candidates, WC: Candidates, ALL: Candidates,MaxTieBreaks: nat)
returns(V_out: Votes, Candidates_out: Candidates, R_out: Ranking, W_out: Candidates,L_out: Candidates, WC_out: Candidates)
requires forall c :: c in C ==> c in R
requires forall v,c :: v in V && c in v ==> multiset(v)[c] <= 1
requires forall c :: c in C ==> multiset(C)[c] <=1
requires WC == W + C
requires forall c,v :: (v in V) && (c in v) ==> c in WC
requires forall c :: c in ALL ==> c in C || c in W || c in L
requires forall w :: w in WC==> w in R
requires|V|>0
requires |ALL| == |C|+|W|+|L|
requires |W|< MaxTieBreaks
requires |C| > 0

ensures forall c :: c in Candidates_out ==> c in R_out
ensures forall v,c :: v in V_out && c in v ==> multiset(v)[c] <= 1
ensures forall c :: c in Candidates_out ==> multiset(Candidates_out)[c] <=1
ensures WC_out == W_out + Candidates_out
ensures forall c,v :: (v in V_out) && (c in v) ==> c in WC_out
ensures |C|==|Candidates_out|+1
ensures forall c :: c in ALL ==> c in Candidates_out || c in W_out || c in L_out
ensures  forall w :: w in WC_out==> w in R_out
ensures |V_out|>0
ensures |ALL| == |Candidates_out|+|W_out|+|L_out|
ensures |W_out|<= MaxTieBreaks
{
  R_out := R;
  V_out := V;
  L_out := L;

  var A1 := GetHighestCandidates(C, R_out);

  W_out := W + [A1[0]];
  Candidates_out := delete(C, A1[0]);
  WC_out := W_out + Candidates_out;
  assert forall c :: c in Candidates_out ==> multiset(C)[c] == multiset(Candidates_out)[c];
}


// No Single Candidates has the highest Ranking
// Determines the Candidte with the lowest Ranking, removes this Candidate from the remaining Candidates and all the Votes
// and adds this Candidate to the Loser list
// Recount the votes without Loser
method handleElse(V: Votes, C: Candidates, R: Ranking, W: Candidates,L: Candidates, WC: Candidates, ALL : Candidates,MaxTieBreaks: nat)
returns(V_out: Votes, Candidates_out: Candidates, R_out: Ranking, W_out: Candidates,L_out: Candidates, WC_out: Candidates)

requires forall c :: c in C ==> c in R
requires forall v,c :: v in V && c in v ==> multiset(v)[c] <= 1
requires forall c :: c in C ==> multiset(C)[c] <=1
requires WC == W + C
requires forall c,v :: (v in V) && (c in v) ==> c in WC
requires forall c :: c in ALL ==> c in C || c in W || c in L
requires forall w :: w in WC==> w in R
requires|V|>0
requires |ALL| == |C|+|W|+|L|
requires |W|< MaxTieBreaks
requires |C| > 0

ensures forall c :: c in Candidates_out ==> c in R_out
ensures forall v,c :: v in V_out && c in v ==> multiset(v)[c] <= 1
ensures forall c :: c in Candidates_out ==> multiset(Candidates_out)[c] <=1
ensures WC_out == W_out + Candidates_out
ensures forall c,v :: (v in V_out) && (c in v) ==> c in WC_out
ensures |C|==|Candidates_out|+1
ensures forall c :: c in ALL ==> c in Candidates_out || c in W_out || c in L_out
ensures  forall w :: w in WC_out==> w in R_out
ensures |V_out|>0
ensures |ALL| == |Candidates_out|+|W_out|+|L_out|
ensures |W_out|<= MaxTieBreaks
{
  // find Candidate with lowest Score
  var S := FilterMapBySeq(R,C);
  var s := Min(S.Values);
  var A3 := getCandidateWithScore(R,C,s);
  //----------------------------

  //remove Loser from Candidates and Votes
  Candidates_out := delete(C,A3[0]); 
  W_out := W;
  WC_out:= W_out + Candidates_out;
  V_out := elim(V, A3[0],WC);
  UniqueElementsImplication(V_out);
  L_out := [A3[0]] + L;

  //Recount Votes without the Loser 
  R_out := countVotes(V_out,WC_out);

}

// predicate to define uniqueness of elements of a sequence
// via multiset
predicate HasUniqueElements_Multiset(V : Votes)
{
  forall v,c :: v in V && c in v ==> multiset(v)[c] <= 1
}
// predicate to define uniqueness of elements of a sequence
// via pairwise comparison of elements
predicate HasUniqueElements_Pairwise(V : Votes)
{
  forall v :: v in V ==> forall i,j :: 0<= i < j < |v| ==> v[i] != v[j]
}

// Shows that Multiset-uniqueness implies Pairwise-uniqueness
// via contradiction
lemma UniqueElementsImplication(V : Votes)
requires HasUniqueElements_Multiset(V)
ensures HasUniqueElements_Pairwise(V)
{
  forall v, i, j | v in V && 0 <= i < j < |v|
    ensures v[i] != v[j]
  {
    if v[i] == v[j] {
      TwoDistinctIndicesImpliesCountTwo(v,i,j);
      assert multiset(v)[v[i]] >= 2; // contradiction
    }
  }
}
// lemma that shows:
// if a element apears twice in a Sequence than the multiset entry of this element is equal to 2
lemma TwoDistinctIndicesImpliesCountTwo<T>(s: seq<T>, i: int, j: int)
requires 0 <= i < j < |s|
requires s[i] == s[j]
ensures multiset(s)[s[i]] >= 2
{
  var c := s[i];

  var s_head := s[..i+1];
  var s_tail := s[i+1..];

  assert s[i] in s_head;
  assert multiset(s_head)[c] >= 1;

  var j_tail := j - (i + 1); 
  assert 0 <= j_tail < |s_tail|;
  assert s_tail[j_tail] == s[j];
  assert s[j] == c;
  assert c in s_tail;
  assert multiset(s_tail)[c] >= 1;

  assert s == s_head + s_tail;
  assert multiset(s)[c] == multiset(s_head)[c] + multiset(s_tail)[c];

}

