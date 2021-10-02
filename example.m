load "threetorsimage.m";

P<x> := PolynomialRing(Rationals());
C := HyperellipticCurveOfGenus(2,[x^5+x^4,x^3+x+1]);
torsimglabel, torsimg := threetorsimage(C);

torsimglabel;
torsimg;
X[torsimglabel]`subgroup eq torsimg;
