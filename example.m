load "threetorsimage.m";
P<x> := PolynomialRing(Rationals());
C := HyperellipticCurveOfGenus(2,[x^5+x^4,x^3+x+1]);
label, torsimage := threetorsimage(C);

torsimage;

label;


G := CSp(4,3);
H := X[label]`subgroup;
IsConjugate(G,torsimage,sub<G|Generators(H)>);

