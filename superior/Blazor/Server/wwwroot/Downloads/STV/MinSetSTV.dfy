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

lemma SetMinSTV(S : set<real>)
//ensures that every set of reals has a minimal value
    requires S != {}
    ensures exists m :: m in S && (forall s :: s in S ==> m <= s)
    {
        var s :| s in S;
        var A := S - {s};
        assert |S| > |A|;

        if A != {}
        {
            SetMinSTV(A);
            assert forall a :: a in S ==> a in A || a == s;
        }
    }
    
ghost function minSTV(S : set<real>) : (m : real)
    /*
    Returns the lowest value in a set of reals.

    Input:
        S (set<real>) : Set of reals

    Output:
        m (real) : lowest real in S
    */
    requires |S| > 0
    ensures forall s :: s in S ==> m <= s
    ensures m in S
{
    SetMinSTV(S);
    var m :| m in S && (forall s :: s in S ==> m <= s);
    m
}

method MinSTV(S : set<real>) returns (m : real)
    /*
    Returns the lowest value in a set of reals.

    Input:
        S (set<real>) : Set of reals

    Output:
        m (real) : lowest real in S
    */
    requires |S| > 0
    ensures m in S
    ensures m == minSTV(S)
{
    var A := S;
    ghost var A_inv : set<real> := {};
    var a :| a in A;
    m := a;

    while A != {}
        invariant m in S
        invariant A + A_inv == S
        invariant forall a :: a in A_inv ==> a >= m
    {
        a :| a in A;

        if a < m
        {
            m := a;
        }

        A := A - {a};
        A_inv := A_inv + {a};
    }
}