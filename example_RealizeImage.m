AttachSpec("spec");
ZZ := Integers();

X := GSpLattice(4,3,0);
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

time Cnew := Genus2CurveFromBurkhardtTwistPoint(F,MtoB : P3pt := [1,-1,1,2]);
time Cnew := IntegralModel(Cnew); Cnew;
imglbl, img, X := mod3Galoisimage(Cnew);
if imglbl ne lbl then
    time Cnew := CorrectTwist(Cnew,K,tau,rho); Cnew;
    imglbl, img, X := mod3Galoisimage(Cnew);
    assert imglbl eq lbl;
    imglbl, GroupName(img);
    img := ChangeRing(img,GF(3));
    assert IsConjugate(G,Image(rho),img);
end if;
