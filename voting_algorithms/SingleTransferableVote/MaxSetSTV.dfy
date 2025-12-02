lemma SetMaxSTV(S : set<real>)
//ensures that every set of reals has a maximal value
    requires S != {}
    ensures exists m :: m in S && (forall s :: s in S ==> s <= m)
    {
        var s :| s in S;
        var A := S - {s};
        assert |S| > |A|;

        if A != {}
        {
            SetMaxSTV(A);
            assert forall a :: a in S ==> a in A || a == s;
        }
    }
    
ghost function maxSTV(S : set<real>) : (m : real)
    /*
    Returns the highest value in a set of reals.

    Input:
        S (set<real>) : Set of reals

    Output:
        m (real) : highest real in S
    */
    requires |S| > 0
    ensures forall s :: s in S ==> m >= s
    ensures m in S
{
    SetMaxSTV(S);
    var m :| m in S && (forall s :: s in S ==> m>=s);
    m
}

method MaxSTV(S : set<real>) returns (m : real)
    /*
    Returns the highest value in a set of reals.

    Input:
        S (set<real>) : Set of reals

    Output:
        m (real) : highest real in S
    */
    requires |S| > 0
    ensures m in S
    ensures m == maxSTV(S)
{
    var A := S;
    ghost var A_inv : set<real> := {};
    var a :| a in A;
    m := a;

    while A != {}
        invariant m in S
        invariant A + A_inv == S
        invariant forall a :: a in A_inv ==> a <= m
    {
        a :| a in A;

        if a > m
        {
            m := a;
        }

        A := A - {a};
        A_inv := A_inv + {a};
    }
}