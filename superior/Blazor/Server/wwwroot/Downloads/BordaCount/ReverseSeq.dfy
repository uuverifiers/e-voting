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

ghost function reverseSeq(L : seq ) : (A : seq)
    /*
    Returns L where the order of its elements is reversed.

    Input:
        L (seq) : Sequence

    Output:
        A (seq) : Sequence containing all elements of L in reversed order
    */
    ensures |L| == |A|
    ensures forall i :: 0 <= i < |A| ==> A[i] == L[|L|-1-i]
{
   if |L| == 0 || |L| == 1 then L else reverseSeq(L[1..]) + [L[0]]
}

method ReverseSeq(L : seq ) returns (A : seq)
    /*
    Returns L where the order of its elements is reversed.

    Input:
        L (seq) : Sequence

    Output:
        A (seq) : Sequence containing all elements of L in reversed order
    */
    ensures A == reverseSeq(L)
{
    A := [];
    var i := |L|-1;
    while i >= 0
        invariant -1 <= i <=|L|-1
        invariant A == reverseSeq(L[i+1..])
    {
        A :=  A + [L[i]];
        i := i-1;
    }
}