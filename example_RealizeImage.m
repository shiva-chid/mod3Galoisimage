AttachSpec("spec");
ZZ := Integers();
QQ := Rationals();
R<x> := PolynomialRing(Rationals());
N := 3;
CCs, phi := GSpConjugacyClasses(4,N);
ClassSigns, SignPhi := GSpConjugacyClassSigns(4,N);
X := GSpLattice(4,N,0:CCs:=CCs,phi:=phi,ClassSigns:=ClassSigns,SignPhi:=SignPhi,Verbose:=true);
Ls := Sort(Setseq(Keys(X)));

lbl := "3.12960.9";
G := CSp(4,3);
H := X[lbl]`subgroup; H := ChangeRing(H,GF(3));

R<x> := PolynomialRing(QQ);
K<a> := SplittingField(x^8 - x^4 + 1);
time A, auts, tau := AutomorphismGroup(K);
boo, iso := IsIsomorphic(A,H); assert boo; // need to choose the right isomorphism though
rho := hom<A->G|[G!iso(g) : g in GeneratorsSequence(A)]>;
for g in GL(3,2) do
    Autg := hom<A->A|[A.1^(ZZ!g[i,1])*A.2^(ZZ!g[i,2])*A.3^(ZZ!g[i,3]) : i in [1..3]]>;
    try
        rho := Autg*rho;
        time F, MtoB := BurkhardtModel(K,tau,rho);
        break;
    catch e;
        continue;
    end try;
end for;

for a, b, c, d in [-3..3] do
    randomptinP3 := [a,b,c,d];
    try
        time Cnew := Genus2CurveFromBurkhardtTwistPoint(F,MtoB : P3pt := randomptinP3); // the point can be varied.
        break a;
    catch e;
        continue;
    end try;
end for;

time Cnew := IntegralModel(Cnew); Cnew;
imglbl, img := mod3Galoisimage(Cnew : certainty:=0.9999,Ls:=Ls,CCs:=CCs,phi:=phi,ClassSigns:=ClassSigns,SignPhi:=SignPhi,X:=X,Verbose:=true);
if imglbl ne lbl then
    time Cnew := CorrectTwist(Cnew,K,tau,rho); Cnew;
    imglbl, img := mod3Galoisimage(Cnew);
    assert imglbl eq lbl;
    img := ChangeRing(img,GF(3));
    assert IsConjugate(G,Image(rho),img);
end if;
imglbl, GroupName(img);

