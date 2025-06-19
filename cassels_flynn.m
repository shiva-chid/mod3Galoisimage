intrinsic eqns_2PequalsnegativeP(F::Any, C :: CrvHyp) -> SeqEnum, SeqEnum
{Given a field and a genus 2 curve, return the homogenous and affine polynomials in Kummer coordinates,
which cut out the image of the 3-torsion points on the Kummer surface.}
    A<k1,k2,k3,k4,f0,f1,f2,f3,f4,f5,f6,alpha,l1,l2,l3,l4> := PolynomialRing(F,16);

    coeffs := Coefficients(HyperellipticPolynomials(SimplifiedModel(C)));
    coeffs := coeffs cat [0 : i in [1..7-#coeffs]];

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
    	B[i] := Evaluate(B[i],k_s cat coeffs cat [alpha] cat k_s);
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
end intrinsic;


intrinsic goodsexticpoly(f :: RngUPolElt) -> RngUPolElt, RngIntElt
{return a suppressed sextic polynomial g(x) and an integer d such that y^2 = dg(x) is isomorphic to the curve y^2=f(x)}
    P<x> := Parent(f);
    if Degree(f) eq 6 then
        a6 := Coefficient(f,6);
        d := SquareFree(IntegerRing() ! (a6*Denominator(a6)^2));
        f := f/a6;
        f := Evaluate(f,x-Coefficient(f,5)/6);
    elif Degree(f) eq 5 and Evaluate(f,0) eq 0 then
        f := P ! ((x+1)^6*Evaluate(f,x/(x+1)));
        a6 := Coefficient(f,6);
        if a6 ne 0 then
            d := SquareFree(IntegerRing() ! (a6*Denominator(a6)^2));
            f := f/a6;
            f := Evaluate(f,x-Coefficient(f,5)/6);
        else
            return goodsexticpoly(f);
        end if;
    else
        f := P ! (x^6*Evaluate(f,1/x));
        a6 := Coefficient(f,6);
        d := SquareFree(IntegerRing() ! (a6*Denominator(a6)^2));
        f := f/a6;
        f := Evaluate(f,x-Coefficient(f,5)/6);
    end if;
    return f, d;
end intrinsic;



