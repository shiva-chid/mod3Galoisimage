AttachSpec("spec");
R<x> := PolynomialRing(Rationals());
N := 3;
CCs, phi := GSpConjugacyClasses(4,N);
ClassSigns, SignPhi := GSpConjugacyClassSigns(4,N);
X := GSpLattice(4,N,0:CCs:=CCs,phi:=phi,ClassSigns:=ClassSigns,SignPhi:=SignPhi,Verbose:=true);
Ls := Setseq(Keys(X));
// Ls := Sort(Ls);
Ls := Sort(Ls,func<x,y|(xs[1] ne ys[1]) select xs[1]-ys[1] else (xs[2] ne ys[2]) select xs[2]-ys[2] else xs[3]-ys[3] where xs is [StringToInteger(a) : a in Split(x,".")] where ys is [StringToInteger(a) : a in Split(y,".")]>);
Ls := [lbl : lbl in Ls | lbl eq "1.1.1" or exists(cc){cc[3] : cc in ConjugacyClasses(H) | cc[1] eq 2 and GSpSimilitudeCharacter(cc[3]) eq -1} where H is X[lbl]`subgroup];

// 169.a.169.1
C := HyperellipticCurveOfGenus(2,[x^5+x^4,x^3+x+1]);
time imglabel, img := mod3Galoisimage(C : errorbound:=0.0001,primesbounds:=[100,20],Ls:=Ls,CCs:=CCs,phi:=phi,ClassSigns:=ClassSigns,SignPhi:=SignPhi,X:=X,Verbose:=true);
assert X[imglabel]`subgroup eq img;
print imglabel;

// Example 2.5
C := HyperellipticCurve(R![0, 2, 5, -1, -5, 2], R![]);
time imglabel, img := mod3Galoisimage(C : errorbound:=0.0001,primesbounds:=[100,20],Ls:=Ls,CCs:=CCs,phi:=phi,ClassSigns:=ClassSigns,SignPhi:=SignPhi,X:=X,Verbose:=true);
assert X[imglabel]`subgroup eq img;
print imglabel;

// Example 2.6
C := HyperellipticCurve(-27*x^6 + 54*x^5 - 693*x^4 + 1278*x^3 - 543*x^2 - 60*x - 16);
time imglabel, img := mod3Galoisimage(C : errorbound:=0.0001,primesbounds:=[100,20],Ls:=Ls,CCs:=CCs,phi:=phi,ClassSigns:=ClassSigns,SignPhi:=SignPhi,X:=X,Verbose:=true);
assert X[imglabel]`subgroup eq img;
print imglabel;

// Example 2.11
C := HyperellipticCurve(R![-6, 11, -19, 14, -9, 1], R![1]);
time imglabel, img := mod3Galoisimage(C : errorbound:=0.0001,primesbounds:=[100,20],Ls:=Ls,CCs:=CCs,phi:=phi,ClassSigns:=ClassSigns,SignPhi:=SignPhi,X:=X,Verbose:=true);
assert X[imglabel]`subgroup eq img;
print imglabel;

// Example 4.1
C := HyperellipticCurveOfGenus(2,x*(x^4 - 2^3*855*x^2 + 2^4*13^4));
time imglabel, img := mod3Galoisimage(C : errorbound:=0.0001,primesbounds:=[100,20],Ls:=Ls,CCs:=CCs,phi:=phi,ClassSigns:=ClassSigns,SignPhi:=SignPhi,X:=X,Verbose:=true);
assert X[imglabel]`subgroup eq img;
print imglabel;

// Example 4.1
C := QuadraticTwist(C,2);
time imglabel, img := mod3Galoisimage(C : errorbound:=0.0001,primesbounds:=[100,20],Ls:=Ls,CCs:=CCs,phi:=phi,ClassSigns:=ClassSigns,SignPhi:=SignPhi,X:=X,Verbose:=true);
assert X[imglabel]`subgroup eq img;
print imglabel;


// A curve where bruteforce is needed, and the image is 3.3240.6
C := HyperellipticCurveOfGenus(2,3*x^6 + 198*x^4 - 396*x^2 - 24);
time imglabel, img := mod3Galoisimage(C : errorbound:=0.0001,primesbounds:=[100,20],Ls:=Ls,CCs:=CCs,phi:=phi,ClassSigns:=ClassSigns,SignPhi:=SignPhi,X:=X,Verbose:=true);
assert X[imglabel]`subgroup eq img;
print imglabel;
