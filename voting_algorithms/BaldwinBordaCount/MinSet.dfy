lemma SetMin(S : set<int>)
//ensures that every set of integers has a minimal value
    requires S != {}
    ensures exists m :: m in S && (forall s :: s in S ==> m <= s)
    {
        var s :| s in S;
        var A := S - {s};
        assert |S| > |A|;

        if A != {}
        {
            SetMin(A);
            assert forall a :: a in S ==> a in A || a == s;
        }
    }
    
ghost function min(S : set<int>) : (m : int)
    /*
    Returns the lowest value in a set of integers.

    Input:
        S (set<int>) : Set of integers

    Output:
        m (int) : lowest integer in S
    */
    requires |S| > 0
    ensures forall s :: s in S ==> m <= s
    ensures m in S
{
    SetMin(S);
    var m :| m in S && (forall s :: s in S ==> m <= s);
    m
}

method Min(S : set<int>) returns (m : int)
    /*
    Returns the lowest value in a set of integers.

    Input:
        S (set<int>) : Set of integers

    Output:
        m (int) : lowest integer in S
    */
    requires |S| > 0
    ensures m in S
    ensures m == min(S)
{
    var A := S;
    ghost var A_inv : set<int> := {};
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