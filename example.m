AttachSpec("spec");

P<x> := PolynomialRing(Rationals());
C := HyperellipticCurveOfGenus(2,[x^5+x^4,x^3+x+1]);
torsimglabel, torsimg, X := mod3Galoisimage(C);

torsimglabel;
torsimg;
X[torsimglabel]`subgroup eq torsimg;

