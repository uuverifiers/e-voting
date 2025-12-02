include "./dafnyTypes.dfy"


function updateFactors(F : FactorList, I : Indices, f : real, j : nat) : (A0 : FactorList)
    requires 0 <= j <= |F| && 0 <= |F|
    requires forall i :: 0 <= i < |I| ==> 0 <= I[i] < |F|
    requires forall i,j :: 0 <= i < j < |I| ==> I[i] != I[j]
    requires forall i :: 0 <= i < |F| ==> F[i] >= 0.0
    requires f >= 0.0
    ensures |A0| == |F| - j
    ensures forall i :: j <= i < |F| && i !in I ==> A0[i-j] == F[i]
    ensures forall i :: j <= i < |F| && i in I ==> A0[i-j] == F[i]*f 
    ensures forall i :: j <= i < |F| && A0[i-j] == F[i] && F[i] != 0.0 && f != 1.0==> i !in I
    ensures forall i :: j <= i < |F| && A0[i-j] == F[i]*f && F[i] != 0.0 && f != 1.0 ==> i in I
    ensures forall i :: 0 <= i < |A0| ==> A0[i] >= 0.0
    decreases |F| - j
     
{
    if j == |F| then [] else if j in I then 
        assert ([F[j] * f] + updateFactors(F, I, f, j+1))[0] == F[j]*f ==> j in I;
        [F[j] * f] + updateFactors(F, I, f, j+1) 
    else [F[j]] + updateFactors(F, I, f, j+1)
}

method UpdateFactors(F : FactorList, I : Indices, f : real) returns (A0 : FactorList)
    requires forall i :: 0 <= i < |I| ==> 0 <= I[i] < |F|
    requires forall i,j :: 0 <= i < j < |I| ==> I[i] != I[j]
    requires forall i :: 0 <= i < |F| ==> F[i] >= 0.0
    requires f >= 0.0
    ensures A0 == updateFactors(F, I, f, 0)
    ensures forall i :: 0 <= i < |F| && i !in I ==> A0[i] == F[i]
    ensures forall i :: 0 <= i < |F| && A0[i] == F[i] && F[i] != 0.0 && f != 1.0==> i !in I
    ensures forall i :: 0 <= i < |F| && A0[i] == F[i]*f && F[i] != 0.0 && f != 1.0 ==> i in I
    ensures forall i :: 0 <= i < |F| && i in I ==> A0[i] == F[i]*f
    ensures forall i :: 0 <= i < |A0| ==> A0[i] >= 0.0
    
{
    var i := |F|-1;
    A0 := [];
    while i >= 0
        invariant -1 <= i <= |F|-1
        invariant A0 == updateFactors(F, I, f, i+1)
        invariant forall j :: i+1 <= j < |F| && F[j] != 0.0 && f != 1.0 && A0[j-i-1] == F[j] ==> j !in I
        invariant forall j :: i+1 <= j < |F| && F[j] != 0.0 && f != 1.0 && A0[j-i-1] == F[j]*f ==> j in I
        decreases i 
    {
        var a := 0.0;
        if i in I{
            a := F[i]*f;
            assert a == F[i] * f ==> i in I;
        } else {
            a := F[i];
            
        }
        assert F[i] != 0.0 && f != 1.0 && a == F[i] ==> i !in I;
        assert F[i] != 0.0 && f != 1.0 && a == F[i] * f ==> i in I;
        
        A0 := [a] + A0;
        i := i-1;
        
    }
    assert i == -1;
    assert F[i+1..] == F[0..] == F;
}