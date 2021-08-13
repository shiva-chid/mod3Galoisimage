function standardgenus2curve(defpols);
//    P<x> := PolynomialRing(RationalField());
    f := defpols[1];
    h := defpols[2];

    p := f + (h/2)^2;
    Li := Coefficients(p);
    n := #Li;
    Li := Li cat [0 : i in [1..7-n]];
    return Li;
end function;

function eqns_2PequalsnegativeP(defpols);

    A<k1,k2,k3,k4,f0,f1,f2,f3,f4,f5,f6,alpha,l1,l2,l3,l4> := PolynomialRing(RationalField(),16);

    Coefficients := standardgenus2curve(defpols);

    R := k2^2-4*k1*k3;
    S := -4*k1^3*f0-2*k1^2*k2*f1-4*k1^2*k3*f2-2*k1*k2*k3*f3-4*k1*k3^2*f4-2*k2*k3^2*f5-4*k3^3*f6;
    T := -4*k1^4*f0*f2+k1^4*f1^2-4*k1^3*k2*f0*f3-2*k1^3*k3*f1*f3-4*k1^2*k2^2
*f0*f4+4*k1^2*k2*k3*f0*f5-4*k1^2*k2*k3*f1*f4-4*k1^2*k3^2*f0*f6+2*k1^2*k3^
2*f1*f5-4*k1^2*k3^2*f2*f4+k1^2*k3^2*f3^2-4*k1*k2^3*f0*f5+8*k1*k2^2*k3*f0
*f6-4*k1*k2^2*k3*f1*f5+4*k1*k2*k3^2*f1*f6-4*k1*k2*k3^2*f2*f5-2*k1*k3^3*f3*
f5-4*k2^4*f0*f6-4*k2^3*k3*f1*f6-4*k2^2*k3^2*f2*f6-4*k2*k3^3*f3*f6-4*k3^4*
f4*f6+k3^4*f5^2;

    kummeqn := R*k4^2+S*k4+T;

    B14 :=
k1*k4*l4^2+l4*k4^2*l1-l2*k4*k2*f5*f1*l1-k3*l2*f5*k1*f1*f3*l1-l3*l4*k1*f3*k3*f5+
k1*k4*f1*f3*l1^2-l3*l4*k2*f5*k4-l2*l4*f1*k1*k2*f5+l3^2*k2*f5^2*k3*f3+l3*k2^2*l2
*f5^2*f1-l2*l4*k4*k3*f5+l4*k1^2*f3*f1*l1-f1*k1*k2*f5*l3*f3*l1+l3*k3^2*f5^2*l2*
f3-k4*k3*f5*l3*f3*l1+k3*l2^2*f5^2*k2*f1+2*l3*l4*k3^2*f5^2+2*f0*f5^2*k1^2*l3^2-4
*l2*f1*f6*k1^2*f0*l1+2*l2*f5*k1^2*f1^2*l1+2*l3^2*k3*f5^2*k4-4*l2*f0*f5*f6*k3^2*
l1-8*l2^2*f0*k1*f6*k4+4*f0*f6*k1*k3*l2*f3*l1-4*l2*f0*f6*k2*k4*l1-4*f1*k3*f6*k1*
l2*f2*l1-6*l2*f0*f5*k1*k4*l1-2*k4*k2*l2^2*f6*f1-2*k3*l2^2*f6*k1*f1*f3-2*l2^2*f0
*f5^2*k1*k3-4*k3*f6*k2*f1*l2*f3*l1-4*l2*f0*f5*f4*k1*k3*l1-8*f0*f6*k2^2*l2*f3*l1
-4*l2*f0*f5*f3*k1*k2*l1-2*l2*f0*f5^2*k3*k2*l1+2*l2*f6*k1*k2*f1^2*l1-8*l2*f0*f5*
k1^2*f2*l1-16*l2*f0*f6*k1*k2*f2*l1+2*l2^2*f6*k1^2*f1^2-2*f1*l2*f6*k3*k4*l1-8*f0
*f5*k1*k2*f2*l1^2+2*f1^2*k1*k2*f5*l1^2-4*f0*k1*f6*k2*f1*l1^2+2*k1^2*f4*f1^2*l1^
2-8*f0*f6*k2^2*f2*l1^2+8*f0*f2*f6*k1*k3*l1^2-4*k3*f6*k2*f3*f0*l1^2+2*k3^2*f6*f3
*f1*l1^2+2*k2^2*f6*f1^2*l1^2-8*k3^2*f6*f4*f0*l1^2-4*f0*k3*f6*k4*l1^2-4*f1^2*f6*
k1*k3*l1^2-4*f0*f3*f5*k1*k3*l1^2-8*f0*f4*k1^2*f2*l1^2+2*f0*f3^2*k1^2*l1^2-8*f6*
k1^2*f0^2*l1^2-4*f0*f4*k1*k4*l1^2-2*f0*f5*k2*k4*l1^2+2*k3^2*f5^2*f0*l1^2-4*l2*
l4*f0*k1*f6*k2-4*l2*l4*k3*f6*k2*f2-4*l3*l4*k1*f2*k3*f6-2*l3*l4*f1*k1*f6*k2-6*l3
*l4*k4*k3*f6+2*l4*k1*f2*k4*l1-8*l3*l4*k3^2*f6*f4-4*l4*f4*k1^2*f0*l1-4*l4*k3*f6*
k2*f1*l1-8*l4*f0*f6*k2^2*l1-2*l4*k3*k1*f5*f1*l1-4*l3*k3*l2*f5*k2*f6*f1-8*k3*f6*
k2*f2*l3*l2*f4-2*l2*l4*k1*f2*k3*f5-2*l2*l4*k3^2*f6*f3-6*l4*f0*k1*k2*f5*l1-4*l3*
k1*l2*f3*k2*f6*f1-2*l2*l4*f0*f5*k1^2+4*l4*f0*f6*k1*k3*l1-4*l3*l4*k3*f6*k2*f3-2*
l2*l4*k2^2*f6*f1-4*l3*l4*f6*k1^2*f0-4*l3^2*f0*f5*k1*f6*k2-8*k3^2*f6*f4^2*l3^2-4
*k3*f6*k2*f3*l3^2*f4+4*l3^2*k3^2*f5*f6*f3-8*l3^2*k3*f6^2*k2*f1+2*k3^2*f5^2*l3^2
*f4-8*f0*f6^2*k2^2*l3^2+2*l3^2*k1^2*f3*f6*f1-8*f6*k1^2*f0*l3^2*f4-4*k2^2*f6*f1*
l3*l2*f4-4*l3*l2*f0*f5*f6*k2^2-4*l3*l2*f0*k1^2*f6*f3-2*l3*l2*f0*f5^2*k1*k2+8*l3
*k1*f3*k3*f1*f6*l1-2*l3^2*k4*k2*f6*f3-2*k1*k4*l3*f5*f1*l1-2*l3*k4*k2*f5*f2*l1-8
*l3^2*k3*f6*k4*f4+8*l3^2*f0*k1*f6^2*k3-4*l3^2*k3*f5*k1*f6*f1-2*l3^2*k1*f3^2*k3*
f6-8*l3^2*f2*k3^2*f6^2+4*l3*f0*f6*f3*k1*k2*l1-8*l3*f0*f4*f6*k1*k3*l1+4*l3*f0*f5
^2*k1*k3*l1-2*l3*f0*f5^2*k2^2*l1-8*l3*f2^2*k3*f6*k1*l1-4*l3*f1*k3^2*f6*f5*l1-4*
l3*k3*f5*k1*f4*f1*l1+4*k1*k4*l3*f6*f0*l1+8*l3*f0*f6^2*k3^2*l1-2*k3^2*f6*f3^2*l3
*l1-4*l3*f0*f4*k1*k2*f5*l1-2*k2^2*f6*f1*l3*f3*l1-4*k3*f6*k2*f2*l3*f3*l1-2*l3*k3
*f5^2*k2*f1*l1-4*l3*k1*f2*k2*f1*f6*l1+8*l3*f2*f6*k1^2*f0*l1-4*l3*f0*f5*k1^2*f3*
l1-4*l3*k1*f2*k3*l2*f6*f3-2*l3*k3*l2*f5^2*k1*f1-4*l3*k4*k3*f2*f6*l1-4*k3^2*f6*
f3*l3*l2*f4-8*l3*l2*f1*f6^2*k3^2+2*l3*k3*f5^2*k2*l2*f2-4*k1*k4*l3*l2*f6*f1-4*l3
*k4*k2*l2*f6*f2-4*l3*k4*k3*l2*f6*f3-4*l3*f1^2*k1^2*f6*l1-8*f0*f6*k2^2*l2^2*f4-8
*l2^2*f2*f6*k1^2*f0-8*l3*l2*f0*f6^2*k3*k2-8*l2^2*f0*f6*f3*k1*k2+2*l2^2*f0*f5^2*
k2^2-4*k3*f6*k2*f1*l2^2*f4-8*l2^2*f0*f6^2*k3^2-4*l2^2*f0*f6*k3*k2*f5;

    B24 :=
l2*l4*k4^2+k2*k4*l4^2-k1^2*f3*f1*l3^2*f5-l3*k2*f3^2*k4*l1-k1^2*f3*f1^2*l1^2-k3^
2*f5^2*f3*l3^2+f1*f3*k2*k4*l1^2-k3^2*f5*f3*f1*l1^2+l3^2*k2*f3*k4*f5+l2*k3*f3*k2
*f5*f1*l1+l3*k3*f3^3*k1*l1+k2*k4*l2^2*f5*f1+l2*l4*k2*f3*k4+l2*l4*k2^2*f5*f1+l2*
l4*k1^2*f3*f1+k4*l2*k1*f1*f3*l1+l3*l4*k4*k1*f3+l2*l4*k3^2*f5*f3+l4*k2*f3*k1*f1*
l1-l2*l4*k3*f3^2*k1+l3*k3*f3*k4*l2*f5+l4*k3*f3*k4*l1+l3*l4*k3*f5*k2*f3+l3*k2*l2
*f3*k1*f5*f1+2*l4*f0*k2^2*f5*l1+4*l4*f0*k1^2*f3*l1+2*l4*k4*k1*f1*l1+2*l4*k2*f2*
k4*l1+4*l3*f0*f4*k1^2*f3*l1+4*l3*k2*f2*k1*f5*f1*l1-8*l3*f0*f2*f6*k2*k1*l1+4*l3^
2*k3*f3*k1*f6*f2+8*l3^2*f0*f6^2*k3*k2+4*l3^2*k3*f5*k2*f6*f1+2*l3^2*k3*f3^2*k2*
f6+4*f5*k3*k1*f1^2*l1^2+4*f0*f4*k3*k1*f3*l1^2+4*k3*f6*k2*f1^2*l1^2+4*f0*k2^2*f6
*f1*l1^2+8*f5*k1^2*f0^2*l1^2+4*f0*k1^2*f3*f2*l1^2+4*f0*k4*k1*f3*l1^2+4*f0*f5*f1
*k2*k1*l1^2-8*f0*f5*k3*k1*f2*l1^2+2*l3*k3^2*f3^2*l2*f6+8*l3*l2*f0*f5*f6*k3*k2+8
*l3*l2*f0*f6^2*k3^2+4*f0*f5^2*k3*k1*l2*l3+4*l3^2*f0*f5^2*k2*k1+4*l3^2*k3*f5^2*
k1*f1+4*k3^2*f6*f3*l3^2*f4-8*l3^2*f0*f4*f6*k2*k1+4*l3*k3*l2*f4*k1*f5*f1+4*l3*l2
*f1*k3^2*f6*f5-8*l3^2*k3*f4*k1*f6*f1+8*l3*f0*f4^2*k2*k1*l1+4*l3*f6*k2*k1*f1^2*
l1-8*l3*f1*k3^2*f6*f4*l1+4*l3^2*k3*f3*k4*f6+4*l3*k2*f2*k4*f4*l1+4*f0*f4*k2*k1*
l2*f3*l1-8*l2*f0*f6*k3^2*f4*l1+4*l3*f0*f4*k2^2*f5*l1-4*l3*f1*f6*k3*k4*l1+4*l3*
k3*f5*k4*f2*l1-8*l3*f0*f5*f2*k1^2*l1-8*l3*f0*f5*f3*k2*k1*l1-8*l3*f0*f6*k2^2*f3*
l1+4*l3^2*f0*f6*k2^2*f5-12*l2*f0*f6*k2*k3*f3*l1+4*l2*f0*f5*k2*k3*f4*l1+2*l2^2*
f6*k2*k1*f1^2+4*l2*f0*f5^2*k3^2*l1+4*f1*f5*k3*k1*l2*f2*l1-8*l3*k3*f3*k1*f5*f1*
l1-4*f0*f6*k3*k1*l3*f3*l1-4*l3*f0*f5*k1*k4*l1-4*l3*f0*f6*k2*k4*l1+4*l3*k4*k1*f4
*f1*l1+4*l3*f5*k1^2*f1^2*l1+4*l2^2*f0*f6*k3^2*f5+2*l2^2*f0*f5*f3*k2*k1-8*l2^2*
f0*f6*k3*k1*f3+2*l2^2*f0*f5^2*k3*k2+2*k3*f3*k2*l2^2*f6*f1+4*f1*l2^2*f6*k3*k1*f2
+4*l2^2*f0*f5*k3*k1*f4+2*f1*l2^2*f6*k3*k4+8*l2*f1*f0*f6*k2*k1*l1+2*l2^2*f0*f5*
k1*k4+4*l2*f1*f5*k1^2*f0*l1+2*l2*f0*k1^2*f3^2*l1+8*l2*k1^2*f6*f0^2*l1+2*l2*k2^2
*f6*f1^2*l1+2*f0*k2^2*f5*l2*f3*l1+2*l2*f5*k2*k1*f1^2*l1+8*l2*f0*f4^2*k3*k1*l1-8
*l2*f0*f5*k3*k1*f3*l1-8*l2*f0*f6*k3*k1*f2*l1+2*f1*l2*f5*k3*k4*l1-4*l2*f0*f6*k3*
k4*l1+8*l3^2*f1*k3^2*f6^2+4*l2^2*f0*f6*k2^2*f3+4*l2^2*f1*k1^2*f6*f0+2*f1*l2*f4*
k2*k4*l1+4*l2*f0*f4*k1*k4*l1+4*l2*f6*k3*k1*f1^2*l1+4*f1*k3*f6*k2*l2*f2*l1-8*f0*
f6*k3*k2*f2*l1^2+2*f0*f3^2*k2*k1*l1^2+8*f0^2*f6*k2*k1*l1^2+2*l3*l4*k3*f5*k4-4*
l3*l4*f6*f0*k2*k1+2*l3*l4*k2^2*f6*f1-4*l2*l4*f0*f6*k3*k1+2*l2*l4*k3*f5*k2*f2+4*
l2*l4*k3*f4*k1*f2+2*l3*l4*k2*k4*f4+2*l2*l4*k3*k4*f4+2*l2*l4*k4*k1*f2+2*l2*l4*k2
*f4*k1*f1+4*l4*f0*f4*k2*k1*l1+4*l3*k3*f4*k2*f5*f1*l1-4*l3*k3*f3*k1*f4*f2*l1+4*
l4*k3*f4*k1*f1*l1-4*l4*f0*f5*k3*k1*l1+4*l3*k2^2*f2*f1*f6*l1+8*l3*f2^2*k3*f6*k2*
l1+4*l3*f2*k3^2*f6*f3*l1+4*l3*f1*f5^2*k3^2*l1+4*l3*f0*f5^2*k3*k2*l1+8*l3*k3*f4^
2*k1*f1*l1-8*l3*f0*f6*k2*k3*f4*l1+8*l3*f2^2*f5*k3*k1*l1+2*l3*k3*l2*f5^2*k2*f1-8
*l3*k3*f3*k2*f1*f6*l1-4*l4*f0*f6*k3*k2*l1+2*l4*k3*f5*k2*f1*l1+4*l3*l4*k3^2*f6*
f3-4*l3*l4*k3*f6*k1*f1+4*l3*l4*k3*f5*k1*f2+4*l3*l4*k3*f6*k2*f2+2*l3*l4*k2*f5*k1
*f1-12*l3*l2*f0*f3*f6*k2*k1+4*l3*l2*k1^2*f6*f1^2-8*l3*l2*f2*f0*f6*k1^2+4*l3*l2*
f0*f5*f4*k2*k1+4*l3*k3*f3*k2*l2*f6*f2-4*l3*l2*f0*f6*k1*k4+2*l3*k4*l2*k1*f5*f1+4
*l3*k2*f2*k1*l2*f6*f1+2*l3*k2^2*l2*f3*f6*f1+2*l3*l2*f0*f5^2*k2^2-8*l3*k3*f3*k1*
l2*f6*f1+4*l3*k3*l2*f6*k4*f2+8*l3*f2^2*k3*f6*k1*l2+2*l3*k2*f2*k4*l2*f5-8*f0*f6*
k3*k1*l3*l2*f4;

    B34 :=
l3*l4*k4^2+k3*k4*l4^2-l4*f1*k2*k4*l1+l3*l4*f5*k3^2*f3-l2*l4*k1*f1*k4-l2*l4*k3*
f5*k2*f1-l4*k1*f3*k3*f1*l1+k3*k4*f3*l3^2*f5-l3*k3*l2*f3*k1*f5*f1-k3*f5*k2*f1*l3
*f3*l1-k1*f1*k4*l3*f3*l1-l3*k2*f1*k4*l2*f5+k1*f1^2*l2^2*k2*f5+k2^2*f1^2*l2*f5*
l1+k1^2*f1^2*l2*f3*l1+k2*f1^2*k1*f3*l1^2-6*l4*k4*k1*f0*l1-8*l4*k1^2*f2*f0*l1-2*
l2*l4*f1*k3^2*f6-2*l2*l4*f0*k1^2*f3-2*l2*l4*f0*f5*k2^2-4*l2*l4*f0*k2*k1*f4-2*l4
*f0*k3*f5*k2*l1-4*l4*f4*f0*k3*k1*l1-4*l4*f6*k3^2*f0*l1-4*l3*l4*f0*f5*k2*k1-8*l3
*l4*f0*f6*k2^2-4*l2*l4*f0*f6*k3*k2-2*l2*l4*k3*f4*k1*f1-4*l4*f0*k2*k1*f3*l1-4*l3
^2*f0*f5^2*k3*k1-4*l3^2*k3*f3*k1*f6*f1-8*l3^2*k3*f4*k2*f6*f1+8*l3^2*f0*f4*f6*k3
*k1-4*l3^2*f0*f5*f6*k3*k2+4*l3*l4*f0*f6*k3*k1-6*l3*l4*k2*f1*k3*f6+2*l3*l4*k3*f4
*k4-2*l3*l4*k1*f1*k3*f5-4*l3*l4*f2*f6*k3^2+2*l4*f1^2*k1^2*l1-4*k3*k4*l3^2*f6*f2
-4*l3^2*f0*f6*k1*k4-4*l3*f0*f5^2*k3^2*l1-2*l3*f6*k2^2*f1^2*l1-2*l3^2*k2*f1*k4*
f6-4*l3*l2*f0*f5*f4*k3*k1-4*l3*f0*f4*k1*k4*l1-2*k3*k4*l3*f5*f1*l1-2*l3*k2*f1*k4
*f4*l1+8*l3*f0*f5*k3*k1*f3*l1+4*k3*k4*l3*f6*f0*l1-4*l3*f1*k3^2*f6*f3*l1+2*l3^2*
k3^2*f3^2*f6+4*l3*f0*f6*f3*k3*k2*l1+8*l3*f0*f4*f6*k3^2*l1-8*l3*f0*f4^2*k3*k1*l1
-8*l3*f0*f2*f6*k3*k1*l1-4*f0*k2*k1*f4*l3*f3*l1-2*f0*k1^2*f3^2*l3*l1-2*l3*k2*f1^
2*k1*f5*l1-4*l3*f1*f5*f0*k1^2*l1-2*f0*f5*k2^2*l3*f3*l1+4*l3*f6*k3*k1*f1^2*l1-4*
l3*l2*f0*f5*f3*k2*k1-4*l3*f0*f4*f5*k3*k2*l1+2*l3^2*f2*f5^2*k3^2-4*l3*f6*k1*f1*
l2*k3*f2-8*l3*l2*f0*f6*k2^2*f3-2*l3*f6*k1*f1^2*l2*k2-6*k3*k4*l3*l2*f6*f1-4*l3*
l2*f0*f6*k2*k4+8*l3*k1^2*f6*f0^2*l1+2*l3*l2*f1*f5^2*k3^2-4*l3*l2*f0*f5*f6*k3^2-
16*l3*l2*f0*f4*f6*k3*k2-8*k1^2*f2*f0*l3^2*f6+2*f0*k1^2*f3*l3^2*f5-8*l3^2*f0*f6^
2*k3^2-8*l3^2*f2*f6*k3^2*f4-4*l3*f6*k2*f1*k3*l2*f3+2*l3^2*k3*f5^2*k2*f1-8*f0*f6
*k2^2*l3^2*f4+2*f0*f5^2*k2^2*l3^2-8*l2^2*f0*f6*f3*k3*k2-4*f0*k2*k1*f3*l3^2*f6+2
*f0*k3*f5^2*k2*l2*l3+4*l3*l2*f0*f3*f6*k3*k1-2*l3*l2*f0*f5*k1*k4-8*l3*l2*f1*k3^2
*f6*f4-4*l3*l2*f1*f0*f6*k1^2+2*f1^2*k1^2*l3^2*f6-2*l2^2*f0*f5*k3*k1*f3-2*l2^2*
f6*k3*k1*f1^2-4*l2*f0*f6*k2^2*f1*l1-4*l2*f0*f5*k2^2*f2*l1-4*l2*f1*f5*f0*k2*k1*
l1+2*k2*f1^2*k1*l2*f4*l1-4*l2*f0*f3*k1^2*f2*l1-8*l2^2*f0*f6*k3*k4-8*l2*f0^2*f6*
k2*k1*l1-2*l2^2*f0*f5*k2*k4+2*l2^2*f0*f5^2*k3^2-8*l2^2*f0*f4*f6*k3^2-2*l2*f5*k3
*k1*f1^2*l1-4*l2*f0*f4*k2*k4*l1-4*l2*f0*f5*k3*k4*l1-4*l2*f0*f3*k1*k4*l1-4*f6*k3
^2*f0*l2*f3*l1-8*l2*f0*f4*f2*k2*k1*l1-8*l2*f5*k1^2*f0^2*l1-4*l2^2*f2*f5*f0*k2*
k1-8*l2^2*k1^2*f6*f0^2-2*l2*k3*f6*k2*f1^2*l1-4*l2*f0*f5*f3*k3*k2*l1-4*f4*f0*k3*
k1*l2*f3*l1-8*l2^2*f0*f6*k2^2*f2-4*l2^2*f1*f0*f6*k2*k1+8*f0^2*f6*k3*k1*l1^2-4*
f0*k3*f6*k2*f1*l1^2+2*k2^2*f1^2*l2^2*f6-8*f2*f6*k3^2*f0*l1^2-4*f0*f5*f1*k3*k1*
l1^2-2*f0*f3^2*k3*k1*l1^2+2*f0*f3*f5*k3^2*l1^2-2*f0*f3*k2*k4*l1^2+2*k1*f1^2*k4*
l1^2+2*f1^2*k3^2*f6*l1^2-8*f5*f0^2*k2*k1*l1^2-4*f0*k2*k1*f3*f2*l1^2-8*k1^2*f2^2
*f0*l1^2+2*f1^2*k1^2*f2*l1^2+4*f0*f3*k1^2*f1*l1^2-8*f4*k1^2*f0^2*l1^2-8*f0*f2*
k1*k4*l1^2-8*f0^2*f6*k2^2*l1^2-4*l3*f6*k2*f1*k3*f2*l1-4*l3*k3*f2*k1*f5*f1*l1;

    B44 :=
k4^2*l4^2+k2^2*l2^2*f5^2*f1^2+k1^2*f1^2*f3^2*l1^2+l3^2*k3^2*f3^2*f5^2-2*f5*k1^2
*f1^3*l1^2+16*l2*f0*f6*k2*f2*k4*l1+16*f4*f0*f6*k3^2*l2*f3*l1-4*k2^2*f6*f1^2*l2*
f3*l1+16*l2*f0*f3*f6*k3*k4*l1-4*l2*f5*k1*f1^2*k4*l1-16*l2*f1*f0*f6*k3*k1*f4*l1+
4*l2*f0*f5*k3*f3^2*k1*l1+16*l2^2*f2*f0*f6^2*k3^2-4*k2^2*f6*f1^2*l2^2*f4-4*k1*f1
^2*f3*k2*l2^2*f6+16*l2^2*f0^2*f6*k2*f5*k1-4*l2^2*f2*f5^2*f0*k2^2-4*l2*f6*k2*f1^
2*k4*l1+16*l2*f1*f0*f6^2*k3^2*l1+8*l2^2*f1*f0*f6*k3*f5*k1+16*l2^2*f1*f0*f6^2*k3
*k2-4*l2^2*f0*f5^2*f3*k3*k2-8*l2^2*f0*f5*f3*f6*k3^2+16*l3^2*f2^2*k3^2*f6^2-4*f0
*f5^2*k3^2*l2^2*f4+16*f4^2*f0*f6*k3^2*l2^2+8*l2^2*f0*f6*k3*f3^2*k1-8*l2^2*f1*f0
*f6*k1^2*f3+16*l2^2*f0^2*f6*k1^2*f4-4*l2^2*f2*f6*k1^2*f1^2-2*f5*k2*f1^2*k4*l1^2
+16*l2^2*f0*f6*k1^2*f2^2+16*f3*f0*f6*k3*k2*l2^2*f4+8*f0*f5*k2*f2*k4*l1^2+16*l2^
2*f0^2*f6^2*k2^2+16*f0^2*f6*f4*k2^2*l1^2-4*k2^2*f6*f1^2*f2*l1^2+16*f0*f6*k2*f1*
k1*f2*l1^2+16*l3^2*f0^2*f6^2*k1^2+16*f3*f0*f6*k3*k2*f2*l1^2-8*f0*f6*k2^2*f3*f1*
l1^2-4*k3^2*f6*f3^2*f0*l1^2-8*f1^2*k3^2*f6*f4*l1^2+16*f0^2*f6^2*k3^2*l1^2-4*f1^
2*f6*k3*k4*l1^2-2*f5*k3*f3*k1*f1^2*l1^2-32*f0^2*f6*k3*k1*f4*l1^2+16*f5*f0^2*f6*
k3*k2*l1^2+16*f5^2*f0^2*k3*k1*l1^2+8*f3*f0*k3*f5*k1*f2*l1^2-4*k2*f6*f1^2*k3*f3*
l1^2-8*f2*f5^2*k3^2*f0*l1^2+16*f2*f6*k3*k4*f0*l1^2+16*f0*f4*f2*k1*k4*l1^2-4*f0*
f3^2*k1*k4*l1^2+32*f2*k3^2*f6*f4*f0*l1^2+8*f0*f6*k3*f3*k1*f1*l1^2+8*f0*f5*k1^2*
f1*f2*l1^2-16*f5*f0^2*k1^2*f3*l1^2-4*f3^2*f0*k1^2*f2*l1^2-8*f0*f4*f1*k1^2*f3*l1
^2-4*f4*k1^2*f1^2*f2*l1^2+16*f2^2*f0*f6*k2^2*l1^2+16*f4^2*f0^2*k1^2*l1^2+16*f0^
2*f6*k1^2*f2*l1^2-4*k1^2*f6*f1^2*f0*l1^2+16*f2^2*f0*k1^2*f4*l1^2-4*f4*k1*f1^2*
k4*l1^2+2*f1^2*k3^2*f5^2*l1^2+16*f2^2*f0*k2*f5*k1*l1^2-4*k2*f6*f1^3*k1*l1^2-4*
f5*k2*f1^2*k1*f2*l1^2-16*f0^2*f6*k2*k1*f3*l1^2+16*f4*f0^2*k2*f5*k1*l1^2+4*l2*l4
*f0*f5*k1*f3*k2+16*l3*l4*f0*f6*k1^2*f2-4*l3*l4*k1^2*f6*f1^2+16*l2*l4*f0*k1*f6*
f2*k2+8*l3*l4*f2*f6*k3*k4-2*l3*l4*f5*k3*f3*k4+16*l3*l4*f2*k3^2*f6*f4+8*l3*l4*f0
*f6*k1*k4-4*l3*l4*k3^2*f6*f3^2-4*l3*l4*f5^2*k2*f1*k3-4*l3*l4*f2*f5^2*k3^2+16*l3
*l4*f0*f6*f4*k2^2+16*l3*l4*f0*f6*k2*k1*f3+8*l2*l4*f0*k4*f6*k2+8*l2*l4*f0*k1*f6*
f3*k3+16*l4*f2*f0*k2*f5*k1*l1+4*l3*l4*k4*k2*f1*f6-4*l3*l4*f0*f5^2*k2^2+8*l3*l4*
f6*k3*f3*k1*f1+16*l3*l4*k2*f6*f1*k3*f4+4*l4*f0*k2*f5*k4*l1+16*l4*f3*f0*f6*k3*k2
*l1+16*l4*f2*f0*f6*k2^2*l1-4*l4*f4*k1^2*f1^2*l1+16*l4*f2*f0*k1^2*f4*l1-4*l2*l4*
f0*k2*f5^2*k3+4*l2*l4*f1*f6*k3*k4-2*l2*l4*k1^2*f5*f1^2-4*l4*k2^2*f6*f1^2*l1+16*
l4*f4*f0*f6*k3^2*l1+8*l4*f0*f6*k3*k4*l1+8*l4*f3*f0*k3*f5*k1*l1-4*l4*f0*f5^2*k3^
2*l1-4*l4*f3^2*f0*k1^2*l1+2*l2*l4*f5*k3*f3*k1*f1+4*l2*l4*k2*f6*f1*k3*f3+16*l3*
l2*f1*k3*f6*f4*k4+16*l3*l2*f1^2*f6^2*k3*k2+8*l2*l4*f0*f6*k2^2*f3+16*l2*l4*f0*f6
*k3*f4*k2-2*l2*l4*f1*k3^2*f5^2+4*l2*l4*f0*f5*k4*k1+8*l2*l4*f0*f5*k1^2*f2-4*l2*
l4*k2*k1*f6*f1^2+8*l4*f4*f0*k1*k4*l1-2*l4*f3*k1*f1*k4*l1+16*k2*f6*f1*k3*f4^2*l3
^2+8*l3^2*f1*k3^2*f6*f4*f5+4*l3*k4*l2*f3*k2*f6*f1+16*l3*l2*f1*f0*f6^2*k2^2-4*l3
*l2*f0*f5^2*f3*k2^2+16*l3*f0^2*f6*k2*f5*k1*l1+4*f0*f5*k1*f3^2*k2*l3*l1-4*l3*l2*
f1*f5^2*k3*k4+16*l3*l2*f0*k4*f6*k1*f3+16*f0*k4*f6*k2*l3*l2*f4-2*l3^2*k2*f5^2*f1
*k4+8*l3*f1*f5^2*f0*k2*k1*l1-4*l3^2*f2*f5^2*k3*k4+16*l3^2*f2*f6*k3*f4*k4-16*l3*
f0*f4*f1*f6*k2*k1*l1+16*f0*k1*f6*f2*k2*l3*f3*l1-2*k1^2*f5*f1^2*l3*f3*l1+8*f0*f5
*k1^2*f2*l3*f3*l1+8*l3*f1*f5*f0*f6*k2^2*l1-32*l3*f0^2*f6*k1^2*f4*l1+8*l3*f0*f5*
f3*k3*k1*f4*l1-16*l3*f0*f5^2*f2*k3*k1*l1+8*l3*f2*k3*f6*f3*k1*f1*l1-16*l3*k3*f6*
f4*k1*f1^2*l1+32*l3*f0*f4*f2*f6*k3*k1*l1+32*l3*f0^2*f6^2*k3*k1*l1-32*l3*f2*f0*
f6^2*k3^2*l1+16*l3*f1*f0*f6^2*k3*k2*l1+8*f1*k3^2*f6*f4*l3*f3*l1-2*f1*k3^2*f5^2*
l3*f3*l1+8*l3*f0*f5*k4*k1*f3*l1-8*l3*l2*f1*f5*f3*f6*k3^2-2*l3*k2*f5^2*f1*k3*l2*
f3+8*l3*f0*f5*f3*f6*k3^2*l1+8*l3*k2*f6*f1^2*k3*f5*l1+4*k2*f6*f1*k3*f3^2*l3*l1+8
*f0*f6*k2^2*f3^2*l3*l1+8*f0*k4*f6*k2*l3*f3*l1+8*l3*f1*k3*f6*f3*k4*l1-8*l3*f0*f6
*k3*f3^2*k1*l1+8*l3*f5^2*k3*k1*f1^2*l1+16*f0*f6*k3*f4*k2*l3*f3*l1-16*l3*f0*f5*
f2*f6*k3*k2*l1+8*l3*f1*f0*f6*k1^2*f3*l1+16*l3*f5^2*f0^2*k1^2*l1-8*f0*k2*f5^2*k3
*l3*l2*f4+16*l3*l2*f0*f5*f4*f6*k3^2-4*f0*k2*f5^2*k4*l2*l3+16*l3*l2*f0^2*f6*f5*
k1^2+16*l3*l2*f2*f0*f6*k1^2*f3+32*l3*l2*f0^2*f6^2*k2*k1+16*l3*l2*f0*f3^2*f6*k2*
k1+2*l3*k2*f5*f1*k4*f3*l1-4*l3*k1^2*f1^2*f3*l2*f6+4*l3*k1*f1*f3^2*k3*l2*f6-8*l3
*l2*f0*f5*f3*f6*k3*k2-16*l3*l2*f0*f3*f6^2*k3^2+8*l3*l2*f1*f5*f0*f6*k2*k1+16*l3*
l2*f1*f0*f6^2*k3*k1+8*l3*l2*k3*f6*f5*k1*f1^2+16*l3*l2*f2*f1*k3^2*f6^2+16*f1*k3^
2*f6*f4^2*l3*l2-4*f1*k3^2*f5^2*l3*l2*f4-4*l3*l2*f0*f5^3*k3^2+16*l3*f1^2*k3^2*f6
^2*l1-4*f0*f5^2*k1*f3*k2*l3^2+16*f0*f6*k2^2*f3*l3*l2*f4+8*k2*f6*f1*k3*f3*l3*l2*
f4+32*f0*f6*k3*f4^2*k2*l3*l2-16*l3*l2*f2*f5*f0*f6*k3*k1+16*f0*k1*f6*f3*k3*l3*l2
*f4+16*f2*f0*f6^2*k2^2*l3^2+16*l3^2*f1*f0*f6^2*k2*k1+8*f6*k3*f3*k1*f1*l3^2*f4+
16*l3^2*f2*k2*f6^2*f1*k3-16*l3^2*f0*k3*f6^2*f3*k2-4*f5^2*k2*f1*k3*l3^2*f4+16*l3
^2*f0*f5*f4*f6*k3*k2-4*l3^2*f0*f5^3*k3*k2-8*l3^2*k2*f5*f1*k3*f6*f3-2*f5^2*k3*f3
*k1*f1*l3^2-4*f3^2*f0*k1^2*l3^2*f6-8*k1^2*f6*f1^2*l3^2*f4+2*k1^2*f5^2*f1^2*l3^2
+16*f4*f0*f6^2*k3^2*l3^2-4*k3^2*f6*f3^2*l3^2*f4-4*f0*f5^2*k3^2*l3^2*f6-4*f2*f5^
2*k3^2*l3^2*f4+16*f2*k3^2*f6*f4^2*l3^2-16*l3^2*f1*k3^2*f6^2*f3-32*l3^2*f0*f2*f6
^2*k3*k1+8*l3^2*f0*f5*k1*f6*f3*k3+16*l3^2*k3*f6^2*k1*f1^2-8*l3^2*f2*k3^2*f6*f3*
f5+16*f0*f6*f4^2*k2^2*l3^2+8*l2^2*f0*f6*k2*f3*k4-8*l2*f1*f0*f6*k2*k1*f3*l1-4*l2
^2*f0*f5^2*k3*k4+16*l2^2*f0*f4*f6*k3*k4+16*l2^2*f2*f0*f6*k1*k4+16*f0*f6*k2*k1*
f3*l3^2*f4-4*f0*f5^2*k2^2*l3^2*f4-8*f0*f6*k2^2*f3*l3^2*f5+16*l2*f0^2*f6*k3*f5*
k1*l1+16*f3^2*f0*f6*k3*k2*l2*l1-2*k1*f1^2*f3*k2*l2*f5*l1+32*l2*f0*f6*k2*f2^2*k1
*l1+16*l2*f5^2*f0^2*k2*k1*l1+16*l2*f5*f0^2*k1^2*f4*l1+8*l2*f0*f5*f2*k2*k1*f3*l1
-8*l2*f2*k2*f6*f1^2*k1*l1-2*l3^2*f1*f5^3*k3^2-4*l2*f6*k1^2*f1^3*l1-16*l2*f0^2*
f6*k1^2*f3*l1+16*l2*f0*f5*k1^2*f2^2*l1-4*l2^2*f6*k1*f1^2*k4+16*l2*f0*f6*k3*f3*
k1*f2*l1-4*f0*f5^2*k3^2*l2*f3*l1+4*f0*k2*f5*k4*l2*f3*l1+16*l2*f0*f5*f2*k1*k4*l1
+8*l2*f1*f5^2*f0*k3*k1*l1+32*l2*f0^2*f6^2*k3*k2*l1+8*l2*f1*f5*f0*f6*k3*k2*l1-4*
f5*k1^2*f1^2*l2*f2*l1+16*l2*f0*f6*k1^2*f1*f2*l1-8*l2*f1*f5*f0*k1^2*f3*l1+16*l2*
f5*f0^2*f6*k2^2*l1+16*f2*f0*f6*k2^2*l2*f3*l1+16*l2^2*f2*f0*f6*k2*k1*f3+16*f2*f0
*f6*k2^2*l2^2*f4-8*f0*f5*f1*k2*k1*f3*l1^2+8*l2*l4*f1*k3^2*f6*f4-4*l4*f5*k2*f1^2
*k1*l1+32*f0*f6*k1^2*f2*l3^2*f4-8*f0*f5^2*k1^2*f2*l3^2+16*f0*f6*k1*k4*l3^2*f4-4
*f0*f5^2*k4*k1*l3^2-4*l3^2*k4*f3^2*k3*f6+8*l3^2*k2*f6*f1*k4*f4;

    B := [kummeqn, B14, B24, B34, B44];
    k_s := [k1, k2, k3, k4];

    for i := 1 to #B do
	B[i] := Evaluate(B[i],k_s cat Coefficients cat [alpha] cat k_s);
    end for;

    pol1 := B[1];
    pol2 := B[2] - k1*alpha;
    pol3 := B[3] - k2*alpha;
    pol4 := B[4] - k3*alpha;
    pol5 := B[5] - 2*k4*alpha;

    Pols := [pol1, pol2, pol3, pol4, pol5];

    Affine_Pols := [];

    for i := 1 to #Pols do
	temp := Evaluate(Pols[i],1,1);
	Append(~Affine_Pols,temp);
    end for;

    return Pols, Affine_Pols;
end function;

function monicintegraldefpol(numfld);
    defpolnf := DefiningPolynomial(numfld);
    P<t> := Parent(defpolnf);
    coefs := Coefficients(defpolnf);
    coefs := [coefs[i]/coefs[#coefs] : i in [1..#coefs]];
    dencoefs := [Denominator(coefs[i]) : i in [1..#coefs]];
    lcmofdens := 1;
    for den in dencoefs do
	lcmofdens := LCM(lcmofdens,den);
    end for;
    return &+[coefs[i]*lcmofdens^(#coefs-i)*t^(i-1) : i in [1..#coefs]];
end function;

function definingfieldoflifts(JacKbar, KumKbar, pt);
    K := BaseRing(Parent(pt));
    Qbar := BaseRing(KumKbar);
    if K eq RationalField() then
	F := K;
	includ := hom<K -> Qbar | []>;
    else
	F, i_F := sub<K | Eltseq(pt)>;
	includ := hom<K -> Qbar | Roots(MinimalPolynomial(K.1),Qbar)[1][1]>;
    end if;
    pt := KumKbar ! includ(Eltseq(pt));
    liftedpt := Points(JacKbar,pt)[1];
    a_coefs := Coefficients(liftedpt[1]);
    b_coefs := Coefficients(liftedpt[2]);
    L := F;
    LK := K;
    for x in a_coefs do
	minpolx := MinimalPolynomial(x);
	if #Roots(minpolx,L) eq 0 then
	    L := ext<L|Factorisation(minpolx)[1][1]>;
	end if;
	if #Roots(minpolx,LK) eq 0 then
	    LK := ext<LK|Factorisation(minpolx)[1][1]>;
	end if;
    end for;
    for x in b_coefs do
	minpolx := MinimalPolynomial(x);
	if #Roots(minpolx,L) eq 0 then
	    L := ext<L|Factorisation(minpolx,L)[1][1]>;
	end if;
	if #Roots(minpolx,LK) eq 0 then
	    LK := ext<LK|Factorisation(minpolx,LK)[1][1]>;
	end if;
    end for;
    L := AbsoluteField(L);
    LK := AbsoluteField(LK);
    return monicintegraldefpol(L), monicintegraldefpol(LK);
end function;


function modifying_goodsexticpoly(f);
    P<x> := PolynomialRing(Rationals());
    a6 := Coefficient(f,6);
    d := SquareFree(a6);
    f := f/a6;
    a5 := Coefficient(f,5);
    f := Evaluate(f,x-a5/6);
    return f, d;
end function;



