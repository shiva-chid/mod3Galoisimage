AttachSpec("spec");

P<x> := PolynomialRing(Rationals());
C := HyperellipticCurveOfGenus(2,[x^5+x^4,x^3+x+1]);
imglabel, img, X := mod3Galoisimage(C);

imglabel;
img;
X[imglabel]`subgroup eq img;
GSpLookupLabel(X,img) eq imglabel;

