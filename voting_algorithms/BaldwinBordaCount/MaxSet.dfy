lemma SetMax(S : set<int>)
//ensures that every set of integers has a maximal value
    requires S != {}
    ensures exists m :: m in S && (forall s :: s in S ==> s <= m)
    {
        var s :| s in S;
        var A := S - {s};
        assert |S| > |A|;

        if A != {}
        {
            SetMax(A);
            assert forall a :: a in S ==> a in A || a == s;
        }
    }
    
ghost function max(S : set<int>) : (m : int)
    /*
    Returns the highest value in a set of integers.

    Input:
        S (set<int>) : Set of integers

    Output:
        m (int) : highest integer in S
    */
    requires |S| > 0
    ensures forall s :: s in S ==> m >= s
    ensures m in S
{
    SetMax(S);
    var m :| m in S && (forall s :: s in S ==> m>=s);
    m
}

method Max(S : set<int>) returns (m : int)
    /*
    Returns the highest value in a set of integers.

    Input:
        S (set<int>) : Set of integers

    Output:
        m (int) : highest integer in S
    */
    requires |S| > 0
    ensures m in S
    ensures m == max(S)
{
    var A := S;
    ghost var A_inv : set<int> := {};
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