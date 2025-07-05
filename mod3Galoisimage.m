intrinsic monicintegralpol(p :: RngUPolElt) -> RngUPolElt
{returns a monic integral polynomial whose roots are some rational multiple of the roots of given polynomial}
    P<x> := Parent(p);
    degp := Degree(p);
    p := p/Coefficient(p,degp);
    for i := 1 to degp do
		ai := Denominator(Coefficient(p,degp-i));
		if ai ne 1 then
			facai := Factorisation(ai);
			ci := &*[fac[1]^(Ceiling(fac[2]/i)) : fac in facai];
			p := Evaluate(p,x/ci)*ci^degp;
			if LCM([Denominator(Coefficient(p,j)) : j in [0..degp-1]]) eq 1 then
				break;
			end if;
		end if;
    end for;
    return p;
end intrinsic;

intrinsic dim_rationalthreetors(C :: CrvHyp) -> RngIntElt
{compute dimension of Jac(C)(Q)[3] over F_3}
	C := SimplifiedModel(C);
    Jac := Jacobian(C);
    Kum := KummerSurface(Jac);
    zeropt := Kum ! 0;

    hompols, affpols := eqns_2PequalsnegativeP(Rationals(),C);
    A16<k1,k2,k3,k4,f0,f1,f2,f3,f4,f5,f6,alpha,l1,l2,l3,l4> := PolynomialRing(RationalField(),16);
    A5<k1,k2,k3,k4,alpha> := PolynomialRing(Rationals(),5);
    projec1 := hom<A16 -> A5 | [A5.i : i in [1..4]] cat [0 : i in [1..7]] cat [A5.5] cat [0 : i in [1..4]]>;
    A4<K1,K2,K3,K4> := PolynomialRing(Rationals(),4);
    projec2 := hom<A5 -> A4 | [A4.i : i in [1..4]] cat [0]>;
    temppols1 := [projec1(hompols[1])] cat [Resultant(projec1(hompols[j-1]), projec1(hompols[j]), alpha) : j in [3..#hompols]];
    temppols2 := [projec2(temppols1[j]) : j in [1..#temppols1]];

    P3 := ProjectiveSpace(Rationals(),3);
    X := Scheme(P3,temppols2);
    Xpts := RationalPoints(X);
    count := 0;
    for Xpt in Xpts do
		kumpt := Kum ! Eltseq(Xpt);
		if 3*kumpt eq zeropt then
			possible_points := Points(Jac, kumpt);
//		    print #possible_points;
			count := count + #possible_points;
		end if;
    end for;

    return Valuation(count,3);
end intrinsic;

intrinsic dim_cyclotomicthreetors(C :: CrvHyp) -> RngIntElt
{compute dimension of Jac(C)(Q_zeta3)[3] over F_3}
	C := SimplifiedModel(C);
    Q3 := CyclotomicField(3);
    Jac := BaseExtend(Jacobian(C),Q3);
    Kum := KummerSurface(Jac);
    zeropt := Kum ! 0;

    hompols, affpols := eqns_2PequalsnegativeP(Rationals(),C);
    A16<k1,k2,k3,k4,f0,f1,f2,f3,f4,f5,f6,alpha,l1,l2,l3,l4> := PolynomialRing(RationalField(),16);
    A5<k1,k2,k3,k4,alpha> := PolynomialRing(Rationals(),5);
    projec1 := hom<A16 -> A5 | [A5.i : i in [1..4]] cat [0 : i in [1..7]] cat [A5.5] cat [0 : i in [1..4]]>;
    A4<K1,K2,K3,K4> := PolynomialRing(Rationals(),4);
    projec2 := hom<A5 -> A4 | [A4.i : i in [1..4]] cat [0]>;
    temppols1 := [projec1(hompols[1])] cat [Resultant(projec1(hompols[j-1]), projec1(hompols[j]), alpha) : j in [3..#hompols]];
    temppols2 := [projec2(temppols1[j]) : j in [1..#temppols1]];

    P3 := ProjectiveSpace(Q3,3);
    X := Scheme(P3,temppols2);
    Xpts := RationalPoints(X);
    count := 0;
    for Xpt in Xpts do
		kumpt := Kum ! Eltseq(Xpt);
		if 3*kumpt eq zeropt then
			possible_points := Points(Jac, kumpt);
//		    print #possible_points;
			count := count + #possible_points;
		end if;
    end for;

    return Valuation(count,3);
end intrinsic;


intrinsic dim_threetors_overnfield(C :: CrvHyp, n :: RngIntElt, expectedorderofGal :: RngIntElt : notnormal := false, minusoneinGal := true) -> RngIntElt, FldNum
{compute the maximum over degree n number fields K of dimension of Jac(C)(K)[3] over F_3}
	C := SimplifiedModel(C);
    f := HyperellipticPolynomials(C);
	P<x> := Parent(f);
    coeffs := Coefficients(f);
    coeffs := coeffs cat [0 : i in [1..7-#coeffs]];
    Jac := Jacobian(C);
    Kum := KummerSurface(Jac);
    zeropt := Kum ! 0;
    hompols, affpols := eqns_2PequalsnegativeP(Rationals(),C);

    A16<k1,k2,k3,k4,f0,f1,f2,f3,f4,f5,f6,alpha,l1,l2,l3,l4> := PolynomialRing(RationalField(),16);
    A5<k1,k2,k3,k4,alpha> := PolynomialRing(Rationals(),5);
    projec1 := hom<A16 -> A5 | [A5.i : i in [1..4]] cat [0 : i in [1..7]] cat [A5.5] cat [0 : i in [1..4]]>;
    A4<K1,K2,K3,K4> := PolynomialRing(Rationals(),4);
    projec2 := hom<A5 -> A4 | [A4.i : i in [1..4]] cat [0]>;
    temppols1 := [projec1(hompols[1])] cat [Resultant(projec1(hompols[j-1]), projec1(hompols[j]), alpha) : j in [3..#hompols]];
    temppols2 := [projec2(temppols1[j]) : j in [1..#temppols1]];
    P3 := ProjectiveSpace(Rationals(),3);
    X := Scheme(P3,temppols2);

	ffnew, ggnew, _ := separablethreedivpoly(C);

    Fac := Factorisation(ffnew);
    Facproj := Factorisation(ggnew);

    if minusoneinGal then
		Ga, Ra, Sa := GaloisGroup(Fac[#Fac][1]);
		if #Ga ne expectedorderofGal then
			Ga, Ra, Sa := GaloisGroup(ffnew);
		end if;
	else
		Ga, Ra, Sa := GaloisGroup(Facproj[#Facproj][1]);
		if #Ga ne expectedorderofGal then
			Ga, Ra, Sa := GaloisGroup(ggnew);
		end if;
    end if;

    indexnsubs := Subgroups(Ga : IndexEqual := n);
    nsubfields := [GaloisSubgroup(Sa,indexnsub`subgroup) : indexnsub in indexnsubs];
//    nirredsubfields := [nsubfield : nsubfield in nsubfields | IsIrreducible(nsubfield)];
	QasNF := RationalsAsNumberField();
	nirredsubfields := [IsIrreducible(nsub) select nsub else DefiningPolynomial(AbsoluteField(ext<QasNF|[x[1] : x in Factorisation(nsub)]>)) : nsub in nsubfields];

    max_dim := dim_rationalthreetors(C);
    nfieldK := RationalField();
    for temp in nirredsubfields do
		L := NumberField(temp);
		JacL := BaseExtend(Jac,L);
		KumL := BaseExtend(Kum,L);
		zeroptL := KumL ! 0;
		XptsL := RationalPoints(X,L);
		count := 0;
		for Xpt in XptsL do
			kumpt := KumL ! Eltseq(Xpt);
			if 3*kumpt eq zeroptL then
				possible_points := Points(JacL, kumpt);
//				print #possible_points;
				count := count + #possible_points;
			end if;
		end for;

//		print count;
		if notnormal then
			if not IsNormal(NumberField(monicintegralpol(DefiningPolynomial(L)))) and Valuation(count,3) ge max_dim then
				max_dim := Valuation(count,3);
				nfieldK := L;
//				print max_dim, nfieldK;
			end if;
		else
			if Valuation(count,3) ge max_dim then
				max_dim := Valuation(count,3);
				nfieldK := L;
			end if;
		end if;
    end for;
    return max_dim, nfieldK;
end intrinsic;


intrinsic projmod3Galoisimage(C :: CrvHyp, projimageorder :: RngIntElt) -> Tup
{returns the Magma SmallGroupDatabase id of the projective mod-3 Galois image}
	C := SimplifiedModel(C);
	f := HyperellipticPolynomials(C);
	P<x> := Parent(f);
	ffnew, ggnew, _ := separablethreedivpoly(C);

    Facproj := Factorisation(ggnew);
    Ga := GaloisGroup(Facproj[#Facproj][1] : Type := "Complex");
    if #Ga eq projimageorder then
		return IdentifyGroup(Ga);
    else
		poly := Facproj[#Facproj][1];
		P2<t,u> := PolynomialRing(Rationals(),2);
		for j := #Facproj-1 to 1 by -1 do
			newfac := Facproj[j][1];
			poly := Resultant(Evaluate(poly,t),Evaluate(newfac,u-t),t);
			poly := P ! UnivariatePolynomial(poly);
			if IsIrreducible(poly) then
				Ga := GaloisGroup(poly : Type := "Complex");
				if #Ga eq projimageorder then
					return IdentifyGroup(Ga);
				end if;
			elif projimageorder le 36 then
				Ga := GaloisGroup(poly);
				if #Ga eq projimageorder then
					return IdentifyGroup(Ga);
				end if;
			end if;
		end for;
    end if;
end intrinsic;


// ##########################################################################################################
// further global tests based on the maximum number of N-torsion points over small degree number fields.
// to distinguish among the multiple possibilities outputted by the signature test.

intrinsic max_pts_over_ext(H :: GrpMat, n :: RngIntElt : normal := false) -> RngIntElt
{returns the maximum F_N-dimension of N-torsion points over some degree n field,
if the modN-Galois image is H. If normal is true, only normal degree n fields are considered.}
    MH := GModule(H);
	ordH := #H;
	if ordH mod n ne 0 then return 0; end if;
    if normal then
	    ZH := NormalSubgroups(H : OrderEqual := ExactQuotient(ordH,n));
    else
	    ZH := Subgroups(H : OrderEqual := ExactQuotient(ordH,n));
    end if;
	max_pts := Maximum([0] cat [Dimension(FixMod(MH,x`subgroup)) : x in ZH]);
	return max_pts;
end intrinsic;

intrinsic fixedspaces(H :: GrpMat, n :: RngIntElt : normal := false) -> RngIntElt
{returns a multiset consisting of 0,1,2,3,4. For each 0 <= k <= 4, the number of occurences of k
denotes the number of degree n fields F such that N-torsion over F is a k-dimensional space.
H is the the modN-Galois image. If normal is true, only normal degree n fields are considered.}
    MH := GModule(H);
	ordH := #H;
    if normal then
	    ZH := NormalSubgroups(H : OrderEqual := ExactQuotient(ordH,n));
    else
	    ZH := Subgroups(H : OrderEqual := ExactQuotient(ordH,n));
    end if;
	dat := {* Dimension(FixMod(MH,x`subgroup)) : x in ZH *};
	return dat;
end intrinsic;

intrinsic twodimfixedspaces(H :: GrpMat, n :: RngIntElt : normal := false) -> RngIntElt
{returns a multiset consisting of 0s and 1s. The number of 0s denotes the number of degree n fields F
such that N-torsion over F is an isotropic 2-dimensional space. The number of 1s denotes the number
of such F with N-torsion over F being a non-degenerate 2-dimensional space.
H is the the modN-Galois image. If normal is true, only normal degree n fields are considered.}
	N := #BaseRing(H);
	ZN := Integers(N);
	JJ := StandardAlternatingForm(4,ZN);
    MH := GModule(H);
	ordH := #H;
	dat := {* *};
    if normal then
	    ZH := NormalSubgroups(H : OrderEqual := ExactQuotient(ordH,n));
    else
	    ZH := Subgroups(H : OrderEqual := ExactQuotient(ordH,n));
    end if;
	for x in ZH do
		W, incl := FixMod(MH,x`subgroup);
		if Dimension(W) ne 2 then continue; end if;
		w1mat := Matrix(ZN,1,4,Eltseq(incl(W.1)));
		w2mat := Matrix(ZN,1,4,Eltseq(incl(W.2)));
		// printf "%o, %o, %o\n", W, w1mat, w2mat;
		if w1mat*JJ*Transpose(w2mat) eq 0 then
			Include(~dat,0);
		else
			Include(~dat,1);
		end if;
	end for;
	return dat;
end intrinsic;


intrinsic whatindexsubgroupdistinguishes(Ls :: SeqEnum) -> SetEnum
{given a sequence containing a full set of Gassmann-equivalent non-conjugate subgroups of GSp(4,F_3)
returns a set S of small integers such that the maximum F_3-dimension of the subspace of F_3^4 fixed
by an index-n subgroup for n in S, distinguishes the different groups given as input.
The value n=0 corresponds to considering the subgroup formed by intersecting with Sp(4).
returns false if no such set of integers exists.}
	Ls := Seqset(Ls);
	if Ls eq {"3.320.1","3.320.2","3.320.5","3.320.6"} then
		return {0,1,3};
	elif Ls eq {"3.640.1","3.640.2","3.640.3","3.640.4"} then
		return {1,3};
	elif Ls eq {"3.2880.13","3.2880.17"} then
		return {2};
	elif Ls eq {"3.5760.2","3.5760.5"} then
		return {3};
	elif Ls eq {"3.8640.2","3.8640.4"} then
		return {2};
	elif Ls eq {"3.8640.12","3.8640.13"} then
		return {2};
	elif Ls eq {"3.240.6","3.240.7"} then
		return {12};
	elif Ls eq {"3.320.3","3.320.4"} then
		return {6};
	elif Ls eq {"3.2160.9","3.2160.10"} then
		return {8};
	elif Ls in [{"3.3240.6","3.3240.7"}, {"3.6480.13", "3.6480.17"}, {"3.6480.3", "3.6480.16"}, {"3.6480.14", "3.6480.15"}, {"3.12960.5", "3.12960.11"}] then
		return false;
	else
		return {1};
	end if;
end intrinsic;

intrinsic distinguish(C :: CrvHyp, Ls :: SeqEnum, X :: Assoc : Verbose:=false) -> MonStgElt, GrpMat
{distinguish among the multiple possibilities Ls using global tests based
on the maximum number of three-torsion points over small degree number fields.}
	C := SimplifiedModel(C);
	indexdata := whatindexsubgroupdistinguishes(Ls);
//	if #Keys(X) eq 0 then X := GSpLattice(4,3,0); end if;
	if Type(indexdata) eq BoolElt then return constructmod3image(C,Ls,X:Verbose:=Verbose); end if;
	Lsset := Seqset(Ls);
	if Verbose then printf "Possibilities = %o\nComputing fixed space under subgroups of index %o will distinguish\n", Ls, indexdata; end if;
    if #Lsset eq 4 and #indexdata eq 3 then
		Ls1 := ["3.320.1","3.320.2","3.320.5","3.320.6"]; assert Seqset(Ls1) eq Lsset;
		Hs := [X[l]`subgroup : l in Ls1];
		ordH := #Hs[1];
		assert max_pts_over_ext(Hs[1],1) eq 1;
		SG := Symp(4,3);
		assert Dimension(FixMod(GModule(Hs[2]),SG meet Hs[2])) eq 1;
		assert max_pts_over_ext(Hs[3],3) eq 1;
		if Verbose then printf "Computing dimension of rational three torsion..."; end if;
		dimtors := dim_rationalthreetors(C);
		if Verbose then printf "It is %o.\n", dimtors; end if;
		if dimtors eq 1 then
			return Ls1[1], Hs[1];
		else
			if Verbose then printf "Computing dimension of three torsion over Q(zeta_3)..."; end if;
			dimcyctors := dim_cyclotomicthreetors(C);
			if Verbose then printf "It is %o.\n", dimcyctors; end if;
			if dimcyctors eq 1 then
				return Ls1[2], Hs[2];
			else
				if Verbose then printf "Computing maximum dimension of three torsion over degree %o fields...", 3; end if;
				dimtors3field := dim_threetors_overnfield(C,3,ordH : minusoneinGal := false);
				if Verbose then printf "It is %o.\n", dimtors3field; end if;
				if dimtors3field eq 1 then
					return Ls1[3], Hs[3];
				else
					return Ls1[4], Hs[4];
				end if;
			end if;
		end if;
    elif #Lsset eq 4 and #indexdata eq 2 then
		Ls1 := ["3.640.1","3.640.2","3.640.3","3.640.4"]; assert Seqset(Ls1) eq Lsset;
		Hs := [X[l]`subgroup : l in Ls1];
		ordH := #Hs[1];
		assert max_pts_over_ext(Hs[1],1) eq 1;
		assert max_pts_over_ext(Hs[2],1) eq 1;
		assert max_pts_over_ext(Hs[1],3) eq 2;
		assert max_pts_over_ext(Hs[2],3) eq 1;
		assert max_pts_over_ext(Hs[3],3) eq 0;
		assert max_pts_over_ext(Hs[4],3) eq 1;
		if Verbose then printf "Computing dimension of rational three torsion..."; end if;
		dimtors := dim_rationalthreetors(C);
		if Verbose then printf "It is %o.\n", dimtors; end if;
		if Verbose then printf "Computing projective mod-3 Galois image..."; end if;
		idGal := projmod3Galoisimage(C,162);
		if Verbose then printf "It is the group with SmallGroup id %o.\n", idGal; end if;
		if dimtors eq 1 and idGal eq <162,11> then
			return Ls1[1], Hs[1];
		elif dimtors eq 1 and idGal eq <162,19> then
			return Ls1[2], Hs[2];
		elif dimtors eq 0 and idGal eq <162,11> then
			return Ls1[3], Hs[3];
		else
			assert dimtors eq 0 and idGal eq <162,19>;
			return Ls1[4], Hs[4];
		end if;
	elif indexdata ne {1} then
		assert #Lsset eq 2;
		n := Random(indexdata);
		Ls1 := Ls;
		Hs := [X[l]`subgroup : l in Ls1];
		ordH := #Hs[1];
		if Verbose then printf "Computing maximum dimension of three torsion over degree %o fields...", n; end if;
		dimtorsnfield := dim_threetors_overnfield(C,n,ordH);
		if Verbose then printf "It is %o.\n", dimtorsnfield; end if;
		if dimtorsnfield eq max_pts_over_ext(Hs[1],n) then
			return Ls1[1], Hs[1];
		else
			assert dimtorsnfield eq max_pts_over_ext(Hs[2],n);
			return Ls1[2], Hs[2];
		end if;
	else
		Ls1 := Ls;
		Hs := [X[l]`subgroup : l in Ls1];
		ordH := #Hs[1];
		if Verbose then printf "Computing dimension of rational three torsion..."; end if;
		dimtors := dim_rationalthreetors(C);
		if Verbose then printf "It is %o.\n", dimtors; end if;
		for i := 1 to #Ls1 do
			if max_pts_over_ext(Hs[i],1) eq dimtors then
				return Ls1[i], Hs[i];
			end if;
		end for;
	end if;
end intrinsic;


// ###########################################################################################################

intrinsic degofthreetorsfield(C :: CrvHyp : minusoneinGal := true) -> RngIntElt
{returns the degree of the three torsion field of Jacobian of C}
	C := SimplifiedModel(C);
	ffnew, ggnew, lcmofdens := separablethreedivpoly(C);
	if minusoneinGal then
		G := GaloisGroup(ggnew); ans := 2*#G;
	else
		G := GaloisGroup(ffnew); ans := #G;
	end if;
	return ans;
end intrinsic;

intrinsic threetorsfield(C :: CrvHyp, n :: RngIntElt) -> FldNum, RngIntElt
{compute the three torsion field of Jac(C) and the lcm of all denominators in the
suppressed sextic hyperelliptic polynomial used in computing the three torsion polynomial}
	C := SimplifiedModel(C);
	ffnew, ggnew, lcmofdens := separablethreedivpoly(C);

    Fac := Factorisation(ffnew);
	K := SplittingField(Fac[#Fac][1]);
    if Degree(K) eq n or Degree(K) eq 2*n then
		return K, lcmofdens;
    else
		for g in [fa[1] : fa in Fac[1..#Fac-1] | Degree(fa[1]) ne 1] do
			newfacs := Factorisation(ChangeRing(g,K));
			K := SplittingField([h[1] : h in newfacs | Degree(h[1]) ne 1]);
			K := AbsoluteField(K);
			if Degree(K) eq n or Degree(K) eq 2*n then
				break;
			end if;
		end for;
    end if;
    return K, lcmofdens;
end intrinsic;


intrinsic constructmod3image(C :: CrvHyp, Ls :: SeqEnum, X :: Assoc : Verbose := false) -> MonStgElt, GrpMat
{distinguish among the multiple possibilities Ls by globally fixing a basis of Jac(C)[3]
over the three torsion field, and sampling Frobenius elements up to simultaneous conjugation.}
	Z3 := Integers(3);
	G := GSp(4,3);
//	if #Keys(X) eq 0 then X := GSpLattice(4,3,0); end if;
	Hs := [X[l]`subgroup : l in Ls];
	ordH := #Hs[1];
    C1 := SimplifiedModel(C);
    badprimes := &*BadPrimes(C1)*2;
    P<x> := PolynomialRing(Rationals());
    K, lcmofdens := threetorsfield(C,ordH);
    Jac := Jacobian(C1);
    JacK := BaseExtend(Jac,K);
    KumK := KummerSurface(JacK);
    zeropt := KumK ! 0;

    hompols, affpols := eqns_2PequalsnegativeP(Rationals(),C1);
    A16<k1,k2,k3,k4,f0,f1,f2,f3,f4,f5,f6,alpha,l1,l2,l3,l4> := PolynomialRing(RationalField(),16);
    A5<k1,k2,k3,k4,alpha> := PolynomialRing(Rationals(),5);
    projec1 := hom<A16 -> A5 | [A5.i : i in [1..4]] cat [0 : i in [1..7]] cat [A5.5] cat [0 : i in [1..4]]>;
    A4<K1,K2,K3,K4> := PolynomialRing(Rationals(),4);
    projec2 := hom<A5 -> A4 | [A4.i : i in [1..4]] cat [0]>;
    temppols1 := [projec1(hompols[1])] cat [Resultant(projec1(hompols[j-1]), projec1(hompols[j]), alpha) : j in [2..#hompols]];
    temppols2 := [projec2(temppols1[j]) : j in [1..#temppols1]];

    P3 := ProjectiveSpace(K,3);
    XX := Scheme(P3,temppols2);
    XXpts := RationalPoints(XX);
    all_pts := [JacK!0];
    count := 0;
    printf "Total count of K-rational points on Kummer surface = %o\n", #XXpts;
    for XXpt in XXpts do
        kumpt := KumK ! Eltseq(XXpt);
        if kumpt ne zeropt and 3*kumpt eq zeropt then
	        printf "Kummer pt constructed...";
            possible_points := Points(JacK, kumpt);
            printf "lifted to Jacobian...";
            count +:= #possible_points;
            if not possible_points[1] in all_pts then
                printf "it is a new point!\n";
                all_pts := all_pts cat [pt+possible_points[1] : pt in all_pts] cat [pt+possible_points[2] : pt in all_pts];
                if #all_pts eq 81 then break; end if;
            end if;
        end if;
    end for;

    if #all_pts ne 81 then
		print "Did not find the correct three torsion field to distinguish between the possibilities", Ls;
		return 0, "Error";
    end if;

    defK := DefiningPolynomial(K);
    dens := 1;
    for i := 1 to #all_pts do
		if all_pts[i] ne JacK ! 0 then
			dens1 := LCM([LCM([Denominator(coe[j]) : j in [1..Degree(K)]]) : coe in Coefficients(all_pts[i][1])]);
			dens2 := LCM([LCM([Denominator(coe[j]) : j in [1..Degree(K)]]) : coe in Coefficients(all_pts[i][2])]);
			dens := LCM([dens,dens1,dens2]);
		end if;
    end for;

/* Fixing a symplectic basis */

    basisfound := false;
    p := 4;
    while not basisfound do
		p := NextPrime(p);
		if badprimes mod p eq 0 or lcmofdens mod p eq 0 or dens mod p eq 0 then
			p := NextPrime(p);
			continue;
		end if;
		k := SplittingField(ChangeRing(defK,GF(p)));
		Roos := Roots(defK,k);
		alp := Roos[1][1];
		Jack := BaseExtend(JacK,k);
		all_pts_k := [];
		Pred<x> := PolynomialRing(k);
		for i := 1 to #all_pts do
			pt1 := Coefficients(all_pts[i][1]);
			pt2 := Coefficients(all_pts[i][2]);
			pt3 := all_pts[i][3];
			pt1red := Pred ! [&+[coe[j]*alp^(j-1) : j in [1..Degree(K)]] : coe in pt1];
			pt2red := Pred ! [&+[coe[j]*alp^(j-1) : j in [1..Degree(K)] ] : coe in pt2];
			reducedpt := elt<Jack | [pt1red,pt2red]>;
			Append(~all_pts_k,reducedpt);
		end for;

		for i := 1 to #all_pts_k do
			P1 := all_pts_k[i];
			if P1 eq Jack ! 0 then continue; end if;
			for j := i+1 to #all_pts_k do
				P4 := all_pts_k[j];
				zeta3 := WeilPairing(P1,P4,3);
				if zeta3 eq 1 then continue; end if;
				for i2 := j+1 to #all_pts_k do
					P2 := all_pts_k[i2];
					if WeilPairing(P1,P2,3) ne 1 or WeilPairing(P4,P2,3) ne 1 then continue; end if;
					for j2 := i2+1 to #all_pts_k do
						P3 := all_pts_k[j2];
						if WeilPairing(P1,P3,3) eq 1 and WeilPairing(P4,P3,3) eq 1 and WeilPairing(P2,P3,3) eq zeta3 then
							basisfound := true;
							break i;
						end if;
					end for;
				end for;
			end for;
		end for;

		if basisfound then
			basismodp := [P1, P2, P3, P4];
			basisindices := [Index(all_pts_k,basismodp[i]) : i in [1..#basismodp]];
			basis := [all_pts[basisindices[i]] : i in [1..#basisindices]];
		end if;
    end while;

/* Computing frobenius images for several primes with respect to the fixed basis
and deducing the mod 3 Galois image. */

    torsimage := sub<G | Identity(G)>;
    while true do
		basisk := basismodp;
		all_pts_k := [];
		coords := [];
		for i1, i2, i3, i4 in [0..2] do
			po := i1*basisk[1] + i2*basisk[2] + i3*basisk[3] + i4*basisk[4];
			Append(~all_pts_k,po);
			Append(~coords,[i1, i2, i3, i4]);
		end for;

		sigmabasis := [];
		for i := 1 to #basisk do
			Pi := basisk[i];
			sigmai1 := Pred ! [Frobenius(coe) : coe in Coefficients(Pi[1])];
			sigmai2 := Pred ! [Frobenius(coe) : coe in Coefficients(Pi[2])];
			sigmai3 := Pi[3];
			sigmaPi := elt<Jack | sigmai1, sigmai2, sigmai3>;
			Append(~sigmabasis,sigmaPi);
		end for;

		sigmabasiscoords := [coords[Index(all_pts_k,sigmabasis[i])] : i in [1..#sigmabasis]];
		frobpmat := G ! Matrix(Z3,4,4,sigmabasiscoords);
		if not frobpmat in torsimage then
			torsimage := sub<G | torsimage, frobpmat>;
		end if;
		boo := exists(l){l : l in Ls | IsConjugate(G,X[l]`subgroup,torsimage)};
		if boo then return l, X[l]`subgroup; end if;

		p := NextPrime(p);
		while dens mod p eq 0 do
			p := NextPrime(p);
		end while;
		k := SplittingField(ChangeRing(defK,GF(p)));
		Roos := Roots(defK,k);
		alp := Roos[1][1];
		Pred<x> := PolynomialRing(k);
		Jack := BaseExtend(JacK,k);
		basismodp := [];
		for i := 1 to #basis do
			pt1 := Coefficients(basis[i][1]);
			pt2 := Coefficients(basis[i][2]);
			pt3 := basis[i][3];
			pt1red := Pred ! [&+[k ! (coe[j])*alp^(j-1) : j in [1..Degree(K)]] : coe in pt1];
			pt2red := Pred ! [&+[k ! (coe[j])*alp^(j-1) : j in [1..Degree(K)] ] : coe in pt2];
			reducedpt := elt<Jack | [pt1red,pt2red]>;
			Append(~basismodp,reducedpt);
		end for;
    end while;
end intrinsic;


// ###########################################################################################################

/*
intrinsic findmod3Galoisimage(cond :: RngIntElt, C :: CrvHyp : primesstart := 3, primesend := 500, list_of_counts := [0/1 : i in [1..18]], ZG := []) -> SeqEnum, SeqEnum
{returns list of possible subgroups and their indices in the stored database ZG of all subgroups of GSp(4,3),
based on sampling trace and similitude of frobenius. This list includes the correct mod 3 Galois image.
cond should be a multiple of the product of all bad primes.}
	G := CSp(4,3);
	if #ZG eq 0 then ZG := Subgroups(G); end if;
	C := SimplifiedModel(C);
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
//		if N mod 100 eq 0 then print N; end if;
    end for;
    totalprimes := &+list_of_counts;
    freqstat := [list_of_counts[i]/totalprimes : i in [1..#list_of_counts]];
    sigsshowingup := nonzeroentries(freqstat);


//    if #sigsshowingup eq 2 then
//	 	return subs_with_sigstat[211][1], ZG[subs_with_sigstat[211][1][1]]`order;
//    elif #sigsshowingup eq 16 then
//		return subs_with_sigstat[7][1], ZG[subs_with_sigstat[7][1][1]]`order;
//    elif #sigsshowingup eq 17 then
//		return subs_with_sigstat[3][1], ZG[subs_with_sigstat[3][1][1]]`order;
//    elif #sigsshowingup eq 18 then
//		return subs_with_sigstat[1][1], ZG[subs_with_sigstat[1][1][1]]`order;
//    end if;

    if #sigsshowingup eq 18 or (#sigsshowingup eq 17 and not 1 in sigsshowingup) then
		return subs_with_sigstat[1][1], [ZG[subs_with_sigstat[1][1][1]]`subgroup];
    end if;

    V := VectorSpace(RealField(),18);
    possibilities := [];
    errors := [];
    for i := 1 to #all_sigstats do
		sigstatH := all_sigstats[i];
		sigH := nonzeroentries(sigstatH);
		if Set(sigsshowingup) subset Set(sigH) then
			err := V ! sigstatH - V ! freqstat;
		    print i, sigH, Norm(err);
			if Norm(err) lt allmindists[i] then
				Append(~possibilities,subs_with_sigstat[i]);
				Append(~errors,Norm(err));
			end if;
		end if;
    end for;

    if #possibilities ne 1 then
		print "More primes need to be sampled. Sampling more primes...";
		newprimesstart := primesend + 1;
		newprimesend := primesend + 300;
		return findmod3Galoisimage(cond, C : primesstart := newprimesstart, primesend := newprimesend, list_of_counts := list_of_counts, ZG := ZG);
    elif #possibilities[1] gt 1 then
	//	print "Sampled data about frobenius cannot distinguish the image upto GL conjugacy uniquely.";
	//	print "The image could be a subgroup of one of the following index:";
	//	print possibilities[1], whatindexsubgroupdistinguishes(possibilities[1] : ZG := ZG);
	//	print "Looking at global data to distinguish between the", #possibilities[1], "possible images...";
		return distinguish(C,possibilities[1] : ZG := ZG);
    else
	//  printf "Sampled data about frobenius has determined a unique GL(4)-conjugacy class, but there could be multiple GSp(4)-conjugacy classes.\n";
		return possibilities[1][1], [ZG[possibilities[1][1][j]]`subgroup : j in [1..#possibilities[1][1]]];
    end if;
end intrinsic;
*/

intrinsic mod3Galoisimage(C :: CrvHyp : errorbound:=0.0001,primesbounds:=[100,20],order:=0,AbstractGalGrp:=Sym(1),CCs:=[],phi:=map<{1}->{1}|x:->1>,ClassSigns:=[],SignPhi:=map<{1}->{1}|x:->1>,Ls:=[],X:=AssociativeArray(),Verbose:=false) -> MonStgElt, GrpMat
{returns the mod-3 Galois image as a matrix group and its label}
	N := 3;
	GSpord := GSpSize(4,N);
    if CCs eq [] then CCs, phi := GSpConjugacyClasses(4,N); end if;
    if ClassSigns eq [] then ClassSigns, SignPhi := GSpConjugacyClassSigns(4,N); end if;
    if #Keys(X) eq 0 then X := GSpLattice(4,N,0:CCs:=CCs,phi:=phi,ClassSigns:=ClassSigns,SignPhi:=SignPhi); end if;
    if Ls eq [] then
		Ls := Setseq(Keys(X));
		Ls := Sort(Ls,func<x,y|(xs[1] ne ys[1]) select xs[1]-ys[1] else (xs[2] ne ys[2]) select xs[2]-ys[2] else xs[3]-ys[3] where xs is [StringToInteger(a) : a in Split(x,".")] where ys is [StringToInteger(a) : a in Split(y,".")]>);
		Ls := [lbl : lbl in Ls | lbl eq "1.1.1" or exists(cc){cc[3] : cc in ConjugacyClasses(H) | cc[1] eq 2 and GSpSimilitudeCharacter(cc[3]) eq -1} where H is X[lbl]`subgroup];
	end if;
	if order ne 0 then
		Ls := [lbl : lbl in Ls | order*X[lbl]`index eq GSpord];
		if Verbose then printf "Initial possibilities: %o\n", Ls; end if;
	end if;
	if #AbstractGalGrp ne 1 then
		Ls1 := [lbl : lbl in Ls | IsIsomorphic(X[lbl]`subgroup,AbstractGalGrp)];
		Ls := Setseq(&join[{lbl : lbl in Ls | X[lbl]`gassmanndist eq X[lbl1]`gassmanndist} : lbl1 in Ls1]);
		Ls := Sort(Ls,func<x,y|(xs[1] ne ys[1]) select xs[1]-ys[1] else (xs[2] ne ys[2]) select xs[2]-ys[2] else xs[3]-ys[3] where xs is [StringToInteger(a) : a in Split(x,".")] where ys is [StringToInteger(a) : a in Split(y,".")]>);
		Ls := [lbl : lbl in Ls | lbl eq "1.1.1" or exists(cc){cc[3] : cc in ConjugacyClasses(H) | cc[1] eq 2 and GSpSimilitudeCharacter(cc[3]) eq -1} where H is X[lbl]`subgroup];
		if Verbose then printf "Initial possibilities: %o\n", Ls; end if;
	end if;

	if #Ls eq 1 then return Ls[1], X[Ls[1]]`subgroup; end if;

    Ls, S, boo := GSpModNImageProbablisticFromFrobSign(C,N,errorbound:B:=primesbounds[1],Ls:=Ls,CCs:=CCs,phi:=phi,ClassSigns:=ClassSigns,SignPhi:=SignPhi,X:=X,Verbose:=Verbose);
//    if Verbose then printf "%o, %o, %o\n%o\n\n", Ls, [<GSpLookupLabel(X,s[1]), s[2]> : s in S], boo, #{[x[2] : x in X[l]`ClassSignDist] : l in Ls}; end if;

    Ls, S, boo := GSpModNImageProbablisticFromFrob(C,N,errorbound:B:=primesbounds[2],Ls:=Ls,CCs:=CCs,phi:=phi,ClassSigns:=ClassSigns,SignPhi:=SignPhi,X:=X,Verbose:=Verbose);
//    if Verbose then printf "%o, %o, %o\n%o\n\n", Ls, [<GSpLookupLabel(X,s[1]), s[2]> : s in S], boo, #{[x[2] : x in X[l]`gassmanndist] : l in Ls}; end if;

	if #Ls eq 1 then return Ls[1], X[Ls[1]]`subgroup; end if;
	return distinguish(C,Ls,X : Verbose:=Verbose);
end intrinsic;


