intrinsic BurkhardtModel(K::FldNum, tau::Map, rho::Map) -> RngMPolElt, SeqEnum
{Given a number field K with tau identifying an abstract permutation group A with the group of automorphisms of K,
and the mod 3 rep rho A --> GSp(4,3), returns a model of the Burkhardt quartic corresponding to the twist, and a
parametrization of it by P^3}
    QQ := Rationals();
    G := Sp(4,3);
    Ggen := GeneratorsSequence(G);
    F<omega> := CyclotomicField(3);
    bool, psi := IsSubfield(F,K);
    zeta := psi(omega);
    GL4K := GL(4,K);
    rep := hom<G -> GL4K | [[0,-1,0,0],[-1,0,0,0],[0,0,-1,0],[0,0,0,1]],[
    [  1/3*(-zeta - 2),1/3*(zeta - 1),0, 1/3*(-2*zeta - 1)],
    [ 1/3*(2*zeta + 1) ,1/3*(-2*zeta - 1) ,  0, 1/3*(-2*zeta - 1)],
    [   1/3*(zeta - 1)  , 1/3*(-zeta - 2)    ,          0,  1/3*(2*zeta + 1)],
    [             0        ,      0         ,     1   ,           0]]>;

    perm := Domain(tau);
    gens := GeneratorsSequence(perm);
    n := Degree(K);
    basis := Basis(K);
    V := VectorSpace(K,4);
    kerQ := VectorSpace(QQ,4*n);
    yy := DiagonalMatrix(GF(3),4,[1,1,-1,-1]);
    for g in gens do
        if tau(g)(zeta) eq zeta then
            M := rep(rho(g));
        end if;
        if tau(g)(zeta) eq -1-zeta then
            M := rep(rho(g)*yy);
        end if;
        N1 := BlockMatrix(4,4,[RepresentationMatrix(x) : x in Eltseq(M)]);
        gmat := Matrix(QQ,n,n,[Eltseq(tau(g)(b)) : b in basis]);
        N2 := DirectSum([gmat : i in [1..4]]);
        kerg := Kernel(N1-N2);
        kerQ := kerQ meet kerg;
    end for;

    N := Matrix([V![&+[v[n*i+j]*basis[j] : j in [1..n]] : i in [0..3]] : v in Basis(kerQ)]);
    newrep := hom<G -> GL4K | [N*rep(g)*N^-1: g in Ggen]>;

    Mat4K := MatrixAlgebra(K,4);
    GL35K := GL(35,K);
    sym4mod := GModule(G,[GL35K!SymmetricPower(Mat4K!newrep(g),4): g in Ggen]);
    mod5 := DirectSumDecomposition(sym4mod)[1];
    dimmod5 := Dimension(mod5);
    require dimmod5 eq 5 : "Dimension of the smallest component of Sym^4 of the GSp(4,3)-module is %o. Expected 5\n", dimmod5;
    inc := Morphism(mod5,sym4mod);

    P4x<[x]>:=PolynomialRing(QQ,4);
    P5y<[Y]> := PolynomialRing(QQ,5);
    deg4mons := Setseq(MonomialsOfDegree(P4x,4));
    flist := [&+[(QQ!inc[i][j])*deg4mons[j] : j in [1..35]] : i in [1..5]];
    f := hom<P5y -> P4x | flist>;

    P5ymons := Setseq(MonomialsOfDegree(P5y,4));
    P4xmons := Setseq(MonomialsOfDegree(P4x,16));
    coeffmat := [[MonomialCoefficient(f(r),m) : m in P4xmons] : r in P5ymons];
    ker_coeffmat := Kernel(Matrix(coeffmat));
    printf "Dimension of kernel of coeffmat = %o\n", Dimension(ker_coeffmat);
    polyvec := Basis(ker_coeffmat)[1];
    polyeq := &+[polyvec[i]*P5ymons[i] : i in [1..#P5ymons]];
    return polyeq, flist;
end intrinsic;


intrinsic Genus2CurveFromBurkhardtTwistPoint(F :: RngMPolElt, MtoB :: SeqEnum : P3pt := [], ht := 10) -> CrvHyp
{given a Burkhardt twist model F(Y0,Y1,Y2,Y3,Y4) = 0 with a P^3-parametrization given as a sequence MtoB
of 5 deg 4 monomials in 4 variables, and optionally the coordinates of a point P3pt in P^3,
return the genus 2 hyperelliptic curve parametrized by that point (upto finding the right twist).
If a point P3pt is not given, a low height point search upto height ht is done on the Burkhardt twist model
and a random point is chosen}
    require Evaluate(F,MtoB) eq 0 : "Burkhardt model or its parametrization is wrong";

    ZZ := Integers();
    QQ := Rationals();
    P5y<[Y]> := Parent(F);
    PP4 := ProjectiveSpace(P5y);
    BB := Scheme(PP4,F);
    printf "Formed the twisted Burkhardt model\n";

    if P3pt eq [] then
        BB_pts := [Eltseq(x) : x in PointSearch(BB,ht : Dimension := 3, SkipSingularityCheck := true)];
        require #BB_pts ne 0 : "Point search upto height ", ht, " returned no points. Increase height.";
        printf "PointSearch found %o points on twisted Burkhardt model\n", #BB_pts;
    else
        alp := [Evaluate(fi,P3pt) : fi in MtoB];
        BB_pts := [alp];
    end if;
    boo := false;
    printf "Trying the point(s): ";
    for alp in BB_pts do
        try
//            printf "%o ", alp;
            Palps := [F];
            for i := 2 to 4 do
                Append(~Palps,&+[alp[j]*Derivative(Palps[i-1],j) : j in [1..5]]);
            end for;
            C := Curve(PP4,Palps[2..4]);
            boo := true;
        catch e;
            printf "%o\n%o\n%o\n%o\n", e`Object, e`Position, e`Traceback, e`Type;
            continue;
        end try;
    end for;
    require boo : "No good points of height < ", ht, ". Increase height.";
    printf "The intersection of the three polars is a degree %o curve C in P^4. Is it irreducible? %o\n", Degree(C), IsIrreducible(C);
    irrcomps_C := IrreducibleComponents(C);
    printf "C has %o irreducible components, with genus \n%o\n and degree \n%o\n", #irrcomps_C, [Genus(Curve(x)) : x in irrcomps_C], [Degree(x) : x in irrcomps_C];
    assert exists(PP){x : x in irrcomps_C | Degree(x) eq 1};
    // assert Genus(Curve(PP)) eq 0;
    // assert exists(deg5PP){x : x in irrcomps_C | Degree(x) eq 5};
    // assert Genus(Curve(deg5PP)) eq 0;
    H := Scheme(PP4,Y[1]);
    Z := H meet C;
    pts_Z := RationalPoints(Z);
    // printf "Points on Z = \n%o\n", pts_Z;
    // assert #pts_Z eq 1;
    pt := pts_Z[1];
    // assert #PointsOverSplittingField(Z) eq 6;

    cone := Scheme(PP4,Palps[3..4]);
    curve := Curve(H meet cone);
    Divgrp := DivisorGroup(curve);
    CC, conicmap := Conic(curve);
    PP1 := Curve(ProjectiveSpace(QQ,1));
    R<x,y> := CoordinateRing(PP1);
    phi := Parametrization(CC, conicmap(pt), PP1);
    assert Domain(phi) eq PP1;

//    D := Divgrp ! Place(curve,Ideal(DefiningEquations(deg5PP)));
    D := &+[Divgrp ! Place(curve,Ideal(DefiningEquations(irrcomp))) : irrcomp in irrcomps_C[2..#irrcomps_C]];
    // assert Degree(D) eq 5;
    D_CC := Pushforward(conicmap,D);
    // assert Degree(D_CC) eq 5;
    deg5locus := Pullback(phi,D_CC);
    I_deg5locus := Ideal(deg5locus);
    // I_deg5locus;
    I_deg5locus_basis := Basis(I_deg5locus);
    assert #I_deg5locus_basis eq 1;
    Pt<t> := PolynomialRing(QQ);
    deg5pol := Pt ! Reverse(Coefficients(I_deg5locus_basis[1]));
    newg2C := HyperellipticCurveOfGenus(2,deg5pol);
    // newg2C := IntegralModel(newg2C);
    // printf "The proposed genus 2 curve (before twisting) is \n%o\n", newg2C;
    return newg2C;
end intrinsic;

intrinsic CorrectTwist(C :: CrvHyp, K::FldNum, tau::Map, rho::Map : tracesoffrob := []) -> CrvHyp
{Given a genus 2 hyperelliptic curve C, and a number field K with tau identifying an abstract
permutation group A with the group of automorphisms of K, and the mod 3 rep rho A --> GSp(4,3),
returns a quadratic twist of C whose three-torsion representation is isomorphic to rho (if it exists)}
    ZZ := Integers();
    discK := Discriminant(K);
    OK := RingOfIntegers(K);
    if tracesoffrob eq [] then
        tracesoffrob := [<p,Trace(rho(Frobp))> where Frobp is DecompositionGroup(PrimeIdealsOverPrime(K,p)[1]).1 : p in PrimesUpTo(1000) | 2*discK mod p ne 0];
    end if;
    badprimes := BadPrimes(C);
    nonmatching_primes := [];
    for x in tracesoffrob do
        p := x[1]; traceoffrob := x[2];
        if p in badprimes then continue; end if;
        Lp_C := EulerFactor(C,p);
        ap := -Coefficient(Lp_C,1);
        apmod3 := ap mod 3;
        if apmod3 ne traceoffrob then
            require apmod3 eq -traceoffrob : "Something wrong. Trace of frob != +- ap mod 3";
            Append(~nonmatching_primes, p);
            // print p;
        end if;
    end for;

    BP := [-1] cat BadPrimes(C);
    // print #BP;
    M := Matrix(GF(2),1,#BP,[0 : i in [1..#BP]]);
    b := Matrix(GF(2),1,1,[0]);
    for p in nonmatching_primes do
        M := VerticalJoin(M,Matrix(GF(2),1,#BP,[(LegendreSymbol(BP[i],p) eq 1) select 0 else 1 : i in [1..#BP]]));
        b := VerticalJoin(b,Matrix(GF(2),1,1,[1]));
        // print Rank(M);
        if Rank(M) eq #BP-1 then
            v := Solution(Transpose(M),Transpose(b));
            // print v;
            D1 := &*[BP[i]^(ZZ!v[1][i]) : i in [1..#BP]];
            printf "Twisting factor = %o\n", D1;
            break;
        end if;
    end for;

    Ctwist := QuadraticTwist(C,D1);
    for x in tracesoffrob do
        if (x[1] in badprimes) or (2*discK*D1 mod x[1] eq 0) then continue; end if;
        boo := x[2] eq (-Coefficient(EulerFactor(Ctwist,x[1]),1) mod 3);
        require boo : "Something wrong. Trace of frob != +- ap mod 3 for p=%o for the twist found.", x[1];
    end for;
    return Ctwist;
end intrinsic;

