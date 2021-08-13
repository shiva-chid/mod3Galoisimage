load "cassels_flynn.m";
load "dave.m";

G := ConformalSymplecticGroup(4,GF(3));
CC := ConjugacyClasses(G);
ZG := Subgroups(G);

SG := SymplecticGroup(4,GF(3));
possible_subs := [];
for i := 1 to #ZG do
    H := ZG[i]`subgroup;
    for x in H do
	if Order(x) eq 2 and not x in SG then
	    Append(~possible_subs,i);
	    break;
	end if;
    end for;
end for;
// #possible_subs;

U, incl := UnitGroup(GF(3));
chi := hom<G -> U | [Identity(U),Identity(U),U.1]>;
sigs := [];
CCG := ConjugacyClasses(G);
for i := 1 to #CCG do
    x := CCG[i][3];
    sigx := <[incl(chi(x)), Trace(x)], Dimension(Kernel(Matrix(x) - Identity(G)))>;
    if not sigx in sigs then
	Append(~sigs,sigx);
    end if;
end for;

function sigstat(H);
    sigstatH := [0/1 : i in [1..#sigs]];
    CCH := ConjugacyClasses(H);
    for i := 1 to #CCH do
	x := CCH[i][3];
	sigx := <[incl(chi(x)), Trace(x)], Dimension(Kernel(Matrix(x) - Identity(G)))>;
	n := Index(sigs,sigx);
	sigstatH[n] := sigstatH[n] + CCH[i][2]/#H;
    end for;
    return sigstatH;
end function;

all_sigstats := [];
subs_with_sigstat := [];
for i := #possible_subs to 1 by -1 do
    ii := possible_subs[i];
    H := ZG[ii]`subgroup;
    dat := sigstat(H);
    bool1 := false;
    for j := 1 to #subs_with_sigstat do
	jj := subs_with_sigstat[j][1][1];
	H2 := ZG[jj]`subgroup;
	if dat eq sigstat(H2) then
	    bool1 := true;
	    bool2 := false;
	    for k := 1 to #subs_with_sigstat[j] do
		jjj := subs_with_sigstat[j][k][1];
		H3 := ZG[jjj]`subgroup;
		if IsConjugate(GL(4,GF(3)),H,H3) then
		    subs_with_sigstat[j][k] := subs_with_sigstat[j][k] cat [ii];
		    bool2 := true;
		    break;
		end if;
	    end for;
	    if not bool2 then
		subs_with_sigstat[j] := subs_with_sigstat[j] cat [[ii]];
	    end if;
	    break;
	end if;
    end for;
    if not bool1 then
	Append(~all_sigstats,dat);
	Append(~subs_with_sigstat,[[ii]]);
    end if;
end for;

function mindist_nthsigstat(n);
    V := VectorSpace(RealField(),18);
    mindist := 1;
    for j := 1 to #all_sigstats do
	if j ne n then
	    mindist := Minimum(mindist,Norm(V ! all_sigstats[j] - V ! all_sigstats[n]));
	end if;
    end for;
    return mindist/2;
end function;

allmindists := [mindist_nthsigstat(n) : n in [1..#all_sigstats]];

function allvalidsigs(sig);
    validsigs := [];
    for i := 1 to #sig do
	if sig[i] ne 0 then
	    Append(~validsigs,i);
	end if;
    end for;
    return validsigs;
end function;

// ##########################################################################################################

// function to compute dimension of rational three torsion subgroup of Jacobian of a given curve

function dim_rationalthreetors(definingpols);
    C := HyperellipticCurveOfGenus(2,definingpols[1]+definingpols[2]^2/4);
    Jac := Jacobian(C);
    Kum := KummerSurface(Jac);
    zeropt := Kum ! 0;

    hompols, affpols := eqns_2PequalsnegativeP(definingpols);
    A16<k1,k2,k3,k4,f0,f1,f2,f3,f4,f5,f6,alpha,l1,l2,l3,l4> := PolynomialRing(RationalField(),16);
    A5<k1,k2,k3,k4,alpha> := PolynomialRing(Rationals(),5);
    projec1 := hom<A16 -> A5 | [A5.i : i in [1..4]] cat [0 : i in [1..7]] cat [A5.5] cat [0 : i in [1..4]]>;
    A4<K1,K2,K3,K4> := PolynomialRing(Rationals(),4);
    projec2 := hom<A5 -> A4 | [A4.i : i in [1..4]] cat [0]>;
    temppols1 := [projec1(hompols[1])] cat [Resultant(projec1(hompols[j-1]), projec1(hompols[j]), alpha) : j in [2..#hompols]];
    temppols2 := [projec2(temppols1[j]) : j in [1..#temppols1]];

    P3 := ProjectiveSpace(Rationals(),3);
    X := Scheme(P3,temppols2);
    Xpts := RationalPoints(X);
    count := 0;
    for Xpt in Xpts do
	kumpt := Kum ! Eltseq(Xpt);
	if 3*kumpt eq zeropt then
	    possible_points := Points(Jac, kumpt);
//	    print #possible_points;
	    count := count + #possible_points;
	end if;
    end for;

    return Valuation(count,3);
end function;


// function to compute dimension of Jac(C)[3](Q(sqrt(-3))

function dim_cyclotomicthreetors(definingpols);
    C := HyperellipticCurveOfGenus(2,definingpols[1]+definingpols[2]^2/4);
    Q3 := CyclotomicField(3);
    Jac := BaseExtend(Jacobian(C),Q3);
    Kum := KummerSurface(Jac);
    zeropt := Kum ! 0;

    hompols, affpols := eqns_2PequalsnegativeP(definingpols);
    A16<k1,k2,k3,k4,f0,f1,f2,f3,f4,f5,f6,alpha,l1,l2,l3,l4> := PolynomialRing(RationalField(),16);
    A5<k1,k2,k3,k4,alpha> := PolynomialRing(Rationals(),5);
    projec1 := hom<A16 -> A5 | [A5.i : i in [1..4]] cat [0 : i in [1..7]] cat [A5.5] cat [0 : i in [1..4]]>;
    A4<K1,K2,K3,K4> := PolynomialRing(Rationals(),4);
    projec2 := hom<A5 -> A4 | [A4.i : i in [1..4]] cat [0]>;
    temppols1 := [projec1(hompols[1])] cat [Resultant(projec1(hompols[j-1]), projec1(hompols[j]), alpha) : j in [2..#hompols]];
    temppols2 := [projec2(temppols1[j]) : j in [1..#temppols1]];

    P3 := ProjectiveSpace(Q3,3);
    X := Scheme(P3,temppols2);
    Xpts := RationalPoints(X);
    count := 0;
    for Xpt in Xpts do
	kumpt := Kum ! Eltseq(Xpt);
	if 3*kumpt eq zeropt then
	    possible_points := Points(Jac, kumpt);
//	    print #possible_points;
	    count := count + #possible_points;
	end if;
    end for;

    return Valuation(count,3);
end function;


// function to compute maximum dimension of a subgroup of Jac(C)[3] defined over a degree n number field.

function dim_threetors_overnfield(definingpols,n : notnormal := false);
    C := HyperellipticCurveOfGenus(2,definingpols[1]+definingpols[2]^2/4);
    f := HyperellipticPolynomials(C);
    coeffs := Coefficients(f);
    lencoeffs := #coeffs;
    coeffs := coeffs cat [0 : i in [7-lencoeffs]];
    Jac := Jacobian(C);
    Kum := KummerSurface(Jac);
    zeropt := Kum ! 0;
    hompols, affpols := eqns_2PequalsnegativeP(definingpols);

    A16<k1,k2,k3,k4,f0,f1,f2,f3,f4,f5,f6,alpha,l1,l2,l3,l4> := PolynomialRing(RationalField(),16);
    A5<k1,k2,k3,k4,alpha> := PolynomialRing(Rationals(),5);
    projec1 := hom<A16 -> A5 | [A5.i : i in [1..4]] cat [0 : i in [1..7]] cat [A5.5] cat [0 : i in [1..4]]>;
    A4<K1,K2,K3,K4> := PolynomialRing(Rationals(),4);
    projec2 := hom<A5 -> A4 | [A4.i : i in [1..4]] cat [0]>;
    temppols1 := [projec1(hompols[1])] cat [Resultant(projec1(hompols[j-1]), projec1(hompols[j]), alpha) : j in [2..#hompols]];
    temppols2 := [projec2(temppols1[j]) : j in [1..#temppols1]];
    P3 := ProjectiveSpace(Rationals(),3);
    X := Scheme(P3,temppols2);


    A<k1,k2,k3,k4,f0,f1,f2,f3,f4,f5,f6,alpha,l1,l2,l3,l4> := PolynomialRing(RationalField(),16);
    Pols := [A ! affpols[i] : i in [1..#affpols]];
    kummeqn := Pols[1];
    new_pols1 := [kummeqn];
    new_pols1 := new_pols1 cat [Resultant(Pols[j-1],Pols[j],alpha) : j in [3..#Pols]];
    new_pols2 := [Resultant(new_pols1[j-1],new_pols1[j],k4) : j in [2..#new_pols1]];
    new_pols3 := [Resultant(new_pols2[j-1],new_pols2[j],k3) : j in [2..#new_pols2]];
    D := GCD(new_pols3[1],new_pols3[2]);
    Fac := Factorisation(D);


    max_dim := dim_rationalthreetors(definingpols);
    nfieldK := RationalField();
    list_of_fields := [];

/* the patch with k1 = 1 suggests we must check the following fields
of degree dividing n */

    for j := 1 to #Fac do
	degfac := Degree(Fac[j][1]);
	if n mod degfac eq 0 then
	    def_pol := UnivariatePolynomial(Fac[j][1]);
	    K := NumberField(def_pol);
//	    print K;

	    JacK := BaseExtend(Jac,K);
	    KumK := BaseExtend(Kum,K);
	    zeroptK := KumK ! 0;
	    XptsK := RationalPoints(X,K);
	    Kbar := AlgebraicClosure(RationalField());
	    JacKbar := BaseExtend(JacK,Kbar);
	    KumKbar := BaseExtend(KumK,Kbar);
	    count := 0;
	    for Xpt in XptsK do
		kumpt := KumK ! Eltseq(Xpt);
		if 3*kumpt eq zeroptK then
//		    print kumpt, KumK, Parent(kumpt) eq KumK;
		    Append(~list_of_fields, definingfieldoflifts(JacKbar,KumKbar,kumpt));
		    possible_points := Points(JacK, kumpt);
//		    print #possible_points;
		    count := count + #possible_points;
		end if;
	    end for;

//	    print count;
	    if notnormal and K ne RationalField() then
		K := NumberField(monicintegraldefpol(K));
		if not IsNormal(K) and Degree(K) eq n and Valuation(count,3) ge max_dim then
		    max_dim := Valuation(count,3);
		    nfieldK := K;
		end if;
	    else
		if Degree(K) eq n and Valuation(count,3) ge max_dim then
		    max_dim := Valuation(count,3);
		    nfieldK := K;
		end if;
	    end if;

	end if;
    end for;

/* the patch with k1 = 0 and k2 = 1 suggests we must check the following fields
of degree dividing n */

    A<k1,k2,k3,k4,f0,f1,f2,f3,f4,f5,f6,alpha,l1,l2,l3,l4> := PolynomialRing(RationalField(),16);
    Pols := [A ! hompols[i] : i in [1..#hompols]];
    kummeqn := Pols[1];
    new_pols1 := [kummeqn];
    new_pols1 := new_pols1 cat [Resultant(Pols[j-1],Pols[j],alpha) : j in [3..#Pols]];
    new_pols1 := [Evaluate(Evaluate(new_pols1[j],k1,0),k2,1) : j in [1..#new_pols1]];
    new_pols2 := [Resultant(new_pols1[j-1],new_pols1[j],k4) : j in [2..#new_pols1]];
    D := GCD(GCD(new_pols2[1],new_pols2[2]),new_pols2[3]);
    Fac := Factorisation(D);

    for j := 1 to #Fac do
	degfac := Degree(Fac[j][1]);
	if n mod degfac eq 0 then
	    def_pol := UnivariatePolynomial(Fac[j][1]);
	    K := NumberField(def_pol);
//	    print K;

	    JacK := BaseExtend(Jac,K);
	    KumK := BaseExtend(Kum,K);
	    zeroptK := KumK ! 0;
	    XptsK := RationalPoints(X,K);
	    Kbar := AlgebraicClosure(RationalField());
	    JacKbar := BaseExtend(JacK,Kbar);
	    KumKbar := BaseExtend(KumK,Kbar);
	    count := 0;
	    for Xpt in XptsK do
		kumpt := KumK ! Eltseq(Xpt);
		if 3*kumpt eq zeroptK then
//		    print kumpt;
		    Append(~list_of_fields, definingfieldoflifts(JacKbar,KumKbar,kumpt));
		    possible_points := Points(JacK, kumpt);
//		    print #possible_points;
		    count := count + #possible_points;
		end if;
	    end for;

//	    print count;
	    if notnormal and K ne RationalField() then
		K := NumberField(monicintegraldefpol(K));
		if not IsNormal(K) and Degree(K) eq n and Valuation(count,3) ge max_dim then
		    max_dim := Valuation(count,3);
		    nfieldK := K;
		end if;
	    else
		if Degree(K) eq n and Valuation(count,3) ge max_dim then
		    max_dim := Valuation(count,3);
		    nfieldK := K;
		end if;
	    end if;

	end if;
    end for;

/*
    print list_of_fields;
*/
    for x in list_of_fields do
	L := NumberField(x);
	if Degree(L) eq n then
	    JacL := BaseExtend(Jac,L);
	    KumL := BaseExtend(Kum,L);
	    zeroptL := KumL ! 0;
	    XptsL := RationalPoints(X,L);
	    count := 0;
	    for Xpt in XptsL do
		kumpt := KumL ! Eltseq(Xpt);
		if 3*kumpt eq zeroptL then
		    possible_points := Points(JacL, kumpt);
//		    print #possible_points;
		    count := count + #possible_points;
		end if;
	    end for;

//	    print count;
	    if notnormal and L ne RationalField() then
		if not IsNormal(L) and Valuation(count,3) ge max_dim then
		    max_dim := Valuation(count,3);
		    nfieldK := L;
		end if;
	    else
		if Valuation(count,3) ge max_dim then
		    max_dim := Valuation(count,3);
		    nfieldK := L;
		end if;
	    end if;
	end if;
    end for;

    return max_dim, nfieldK;
end function;


// ##########################################################################################################
// further global tests based on the maximum number of three-torsion points over small degree number fields.
// to distinguish among the multiple possibilities outputted by the signature test.

function max_pts_over_ext(H,n);
    ZH := Subgroups(H);
    MH := GModule(H);
    max_pts := 0;
    ordH := #H;
    for i := 1 to #ZH do
	K := ZH[i]`subgroup;
	if ordH/#K eq n then
	    max_pts := Maximum(max_pts,Dimension(FixMod(MH,K)));
	end if;
    end for;
    return max_pts;
end function;

function final_test(poss);
    if #poss eq 3 then
	ii := poss[1][1];
	jj := poss[2][1];
	kk := poss[3][1];
	H1 := ZG[ii]`subgroup;
	H2 := ZG[jj]`subgroup;
	H3 := ZG[kk]`subgroup;
	for n := 1 to Maximum([#H1,#H2,#H3]) do
	    tempset := {max_pts_over_ext(H1,n),max_pts_over_ext(H2,n),max_pts_over_ext(H3,n)};
	    if #tempset eq 3 then
		return n;
	    end if;
	end for;
	return -3;
    elif #poss eq 4 then
	ii := poss[1][1];
	jj := poss[2][1];
	kk := poss[3][1];
	ll := poss[4][1];
	H1 := ZG[ii]`subgroup;
	H2 := ZG[jj]`subgroup;
	H3 := ZG[kk]`subgroup;
	H4 := ZG[ll]`subgroup;
	for n := 1 to Maximum([#H1,#H2,#H3,#H4]) do
	    tempset := {max_pts_over_ext(H1,n),max_pts_over_ext(H2,n),max_pts_over_ext(H3,n),max_pts_over_ext(H4,n)};
	    if #tempset eq 4 then
		return n;
	    end if;
	end for;
	return -4;
    end if;
    ii := poss[1][1];
    jj := poss[2][1];
    H1 := ZG[ii]`subgroup;
    H2 := ZG[jj]`subgroup;
    for n := 1 to Maximum(#H1,#H2) do
	if max_pts_over_ext(H1,n) ne max_pts_over_ext(H2,n) then
	    return n;
	end if;
    end for;
/*
    print "Test failure: For any given degree, the maximum number of three 
torsion points over a number field of that degree is the same.";
*/
    return -1;
end function;

function distinguish(defpols, poss);
    if #poss eq 3 then
	dimtors := dim_rationalthreetors(defpols);
	for i := 1 to #poss do
	    if max_pts_over_ext(ZG[poss[i][1]]`subgroup,1) eq dimtors then
		return poss[i], [ZG[poss[i][j]]`subgroup : j in [1..#poss[i]]];
	    end if;
	end for;
    elif #poss eq 4 then
	if ZG[poss[1][1]]`order eq 324 then
	    possreordered := poss;
	    for i := 1 to #poss do
		if max_pts_over_ext(ZG[poss[i][1]]`subgroup,1) eq 1 then
		    possreordered[1] := poss[i];
		elif max_pts_over_ext(ZG[poss[i][1]]`subgroup,3) eq 1 then
		    possreordered[2] := poss[i];
		elif Dimension(FixMod(GModule(ZG[poss[i][1]]`subgroup),SG meet ZG[poss[i][1]]`subgroup)) eq 1 then
		    possreordered[3] := poss[i];
		else
		    possreordered[4] := poss[i];
		end if;
	    end for;
	    if dim_rationalthreetors(defpols) eq 1 then
		return possreordered[1], [ZG[possreordered[1][j]]`subgroup : j in [1..#possreordered[1]]];
	    elif dim_threetors_overnfield(defpols,3) eq 1 then
		return possreordered[2], [ZG[possreordered[2][j]]`subgroup : j in [1..#possreordered[2]]];
	    elif dim_cyclotomicthreetors(defpols) eq 1 then
		return possreordered[3], [ZG[possreordered[3][j]]`subgroup : j in [1..#possreordered[3]]];
	    else
		return possreordered[4], [ZG[possreordered[4][j]]`subgroup : j in [1..#possreordered[4]]];
	    end if;
	elif ZG[poss[1][1]]`order eq 162 then
	    possreordered := poss;
	    for i := 1 to #poss do
		if max_pts_over_ext(ZG[poss[i][1]]`subgroup,1) eq 1 then
		    if max_pts_over_ext(ZG[poss[i][1]]`subgroup,3) eq 2 then
			possreordered[1] := poss[i];
		    else
			possreordered[2] := poss[i];
		    end if;
		elif max_pts_over_ext(ZG[poss[i][1]]`subgroup,3) eq 1 then
		    possreordered[3] := poss[i];
		else
		    possreordered[4] := poss[i];
		end if;
	    end for;
	    if dim_rationalthreetors(defpols) eq 1 then
		if dim_threetors_overnfield(defpols,3) eq 2 then
		    return possreordered[1], [ZG[possreordered[1][j]]`subgroup : j in [1..#possreordered[1]]];
		else
		    return possreordered[2], [ZG[possreordered[2][j]]`subgroup : j in [1..#possreordered[2]]];
		end if;
	    elif dim_threetors_overnfield(defpols,3) eq 1 then
		return possreordered[3], [ZG[possreordered[3][j]]`subgroup : j in [1..#possreordered[3]]];
	    else
		return possreordered[4], [ZG[possreordered[4][j]]`subgroup : j in [1..#possreordered[4]]];
	    end if;
	end if;
    elif #poss eq 2 then
	n := final_test(poss);
	if n eq -1 then
	    C := HyperellipticCurveOfGenus(2,defpols);
	    C1 := SimplifiedModel(C);
	    f1 := HyperellipticPolynomials(C1);
	    f1_twisted, twistby_d := modifying_goodsexticpoly(f1);
	    abcde := [Coefficient(f1_twisted,4-j) : j in [0..4]];
	    torspoly1 := torspoly_part1(abcde[1],abcde[2],abcde[3],abcde[4],abcde[5]);
	    torspoly2 := torspoly_part2(abcde[1],abcde[2],abcde[3],abcde[4],abcde[5]);
	    fulltorspoly := torspoly1 + torspoly2;
	    Fac := Factorisation(fulltorspoly);
	    Gal := GaloisGroup(&*[pol : pol in [x[1] : x in Fac] | Degree(pol) gt 1]);
	    idGal := IdentifyGroup(Gal);
	    for i := 1 to #poss do
		if IdentifyGroup(ZG[poss[i][1]]`subgroup) eq idGal then
		    return poss[i], [ZG[poss[i][j]]`subgroup : j in [1..#poss[i]]];
		end if;
	    end for;
// This is the twisted Galois group.
// But the Galois group for f1 will also be the same.
// This is because -Id belongs to each of the four possible groups that arise in this case, and furthermore
// -Id belongs to all the index 2 subgroups of each of these four possible groups.
	elif n eq 1 then
	    dimtors := dim_rationalthreetors(defpols);
	    for i := 1 to #poss do
		if max_pts_over_ext(ZG[poss[i][1]]`subgroup,n) eq dimtors then
		    return poss[i], [ZG[poss[i][j]]`subgroup : j in [1..#poss[i]]];
		end if;
	    end for;
	elif (n gt 1 and n le 6) or (n eq 8 and ZG[poss[1][1]]`order eq 32) then
	    dimtors := dim_threetors_overnfield(defpols,n);
	    for i := 1 to #poss do
		if max_pts_over_ext(ZG[poss[i][1]]`subgroup,n) eq dimtors then
		    return poss[i], [ZG[poss[i][j]]`subgroup : j in [1..#poss[i]]];
		end if;
	    end for;
	else
	    dimtors := dim_threetors_overnfield(defpols,4 : notnormal := true);
	    Hcand := ZG[poss[1][1]]`subgroup;
	    Mcand := GModule(Hcand);
	    ZHcand := [Kind`subgroup : Kind in Subgroups(Hcand) | Kind`order eq #Hcand/4];
	    boo := false;
	    for Kcand in ZHcand do
		if Dimension(FixMod(Mcand,Kcand)) eq 1 and not IsNormal(Hcand,Kcand) then
		    boo := true;
		    break;
		end if;
	    end for;
	    if (boo and dimtors eq 1) or (not boo and dimtors eq 0) then
		return poss[1], [ZG[poss[1][j]]`subgroup : j in [1..#poss[1]]];
	    else
		return poss[2], [ZG[poss[2][j]]`subgroup : j in [1..#poss[2]]];
	    end if;
	end if;
    end if;
end function;


// ###########################################################################################################

function find3torsimage(cond,definingpols : primesstart := 3, primesend := 500, list_of_counts := [0/1 : i in [1..18]]);
    C := HyperellipticCurveOfGenus(2,definingpols);
    for N := primesstart to primesend do
	p := NthPrime(N);
	if cond mod p ne 0 then
	    Cp := ChangeRing(C,GF(p));
	    Jp := Jacobian(Cp);
	    ordJp := Order(Jp: UseGenus2 := true);
	    if ordJp mod 9 ne 0 then
		n := Valuation(ordJp,3);
	    else
		A3 := Sylow(Jp,3);
		A3mod3A3 := quo<A3|3*A3>;
		n := Valuation(#A3mod3A3,3);
	    end if;

	    traceoffrobp := (1 + p - #Cp) mod 3;
	    sigp := <[p mod 3, traceoffrobp], n>;
	    iii := Index(sigs,sigp);
	    list_of_counts[iii] := list_of_counts[iii]+1;
	end if;
/*
	if N mod 100 eq 0 then
	    print N;
	end if;
*/
    end for;
    totalprimes := &+list_of_counts;
    freqstat := [list_of_counts[i]/totalprimes : i in [1..#list_of_counts]];
    sigsshowingup := allvalidsigs(freqstat);

/*
    if #sigsshowingup eq 2 then
	return subs_with_sigstat[211][1], ZG[subs_with_sigstat[211][1][1]]`order;
    elif #sigsshowingup eq 16 then
	return subs_with_sigstat[7][1], ZG[subs_with_sigstat[7][1][1]]`order;
    elif #sigsshowingup eq 17 then
	return subs_with_sigstat[3][1], ZG[subs_with_sigstat[3][1][1]]`order;
    elif #sigsshowingup eq 18 then
	return subs_with_sigstat[1][1], ZG[subs_with_sigstat[1][1][1]]`order;
    end if;
*/

    if #sigsshowingup eq 18 or (#sigsshowingup eq 17 and not 1 in sigsshowingup) then
	return subs_with_sigstat[1], ZG[subs_with_sigstat[1][1][1]]`order;
    end if;

    V := VectorSpace(RealField(),18);
    possibilities := [];
    errors := [];
    for i := 1 to #all_sigstats do
	sigstatH := all_sigstats[i];
	sigH := allvalidsigs(sigstatH);
	if Set(sigH) meet Set(sigsshowingup) eq Set(sigsshowingup) then
	    err := V ! sigstatH - V ! freqstat;
//	    print i, sigH, Norm(err);
	    if Norm(err) lt allmindists[i] then
		Append(~possibilities,subs_with_sigstat[i]);
		Append(~errors,Norm(err));
	    end if;
	end if;
    end for;

    if #possibilities ne 1 then
//	print "More primes need to be sampled. Sampling more primes...";
	newprimesstart := primesend + 1;
	newprimesend := primesend + 300;
	return find3torsimage(cond, definingpols : primesstart := newprimesstart, primesend := newprimesend, list_of_counts := list_of_counts);
    elif #possibilities[1] gt 1 then
//	print "Sampled data about frobenius cannot distinguish the image upto GL conjugacy uniquely.";
//	print "The image could be a subgroup of one of the following index:";
//	print possibilities[1];
//	print "Looking at global data to distinguish between the", #possibilities[1], "possible images...";
	return distinguish(definingpols,possibilities[1]);
    else
	return possibilities[1][1], [ZG[possibilities[1][1][j]]`subgroup : j in [1..#possibilities[1][1]]];
    end if;
end function;
#G, #ZG, #possible_subs, #all_sigstats, #subs_with_sigstat, #allmindists;











/*
P<x> := PolynomialRing(Rationals());
load "../../Users/13129/Documents/MIT/Research/LMFDBgenus2curves.txt";
load "../../Users/13129/Documents/MIT/Research/LMFDBgenus2curves_conductors.txt";
#LMFDBg2curves;
#conds_LMFDBg2curves;


images_that_occur := [];
curves_needing_distinguish := [];
images_needing_distinguish_upto_duplicates := [];
for i := 11003 to #LMFDBg2curves do
    definingpols := LMFDBg2curves[i];
    condC := conds_LMFDBg2curves[i];
    torsimage, torsimageorder := find3torsimage(condC,definingpols);
    if #torsimage gt 1 then
	Append(~curves_needing_distinguish,i);
	if not torsimage in images_needing_distinguish_upto_duplicates then
	    Append(~images_needing_distinguish_upto_duplicates,torsimage);
	end if;
    else
	if not torsimage[1][1] in images_that_occur then
	    images_that_occur := images_that_occur cat torsimage[1];
	end if;
    end if;

    if i mod 100 eq 0 then
	print i;
    end if;
end for;
*/


