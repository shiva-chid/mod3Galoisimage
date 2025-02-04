G := CSp(4,GF(3));

/*
intrinsic degofthreetorsfield(C :: CrvHyp) -> RngIntElt
{returns the degree of the three torsion field of Jacobian of C}

end intrinsic;
*/

intrinsic threetorsfield(C :: CrvHyp, n :: RngIntElt : ignoretwists := false) -> FldNum, RngIntElt
{returns the three torsion field of Jacobian of C, and the lcm of all denominators in the
suppressed sextic hyperelliptic polynomial used in computing the three torsion polynomial}
//	n := degofthreetorsfield(C);
	C1 := SimplifiedModel(C);
	f := HyperellipticPolynomials(C1);
    P<x> := Parent(f);
    newf, twistbyd := modifying_goodsexticpoly(f);
    atoe := [Coefficient(newf,4-i) : i in [0..4]];
    if atoe[2] eq 0 and atoe[4] eq 0 then
		newf := P ! ((x+1)^6*Evaluate(newf,x/(x+1)));
		newf, twistbyd1 := modifying_goodsexticpoly(newf);
		twistbyd *:= twistbyd1;
		atoe := [Coefficient(newf,4-i) : i in [0..4]];
    end if;
    lcmofdens := LCM([Denominator(atoe[i]) : i in [1..#atoe]]);
    fulltp := threetorspoly(Rationals(), atoe);
    if not IsSeparable(fulltp) then
//		printf "3-division poly is not separable...\n";
		for a, b, c, d in [1..5] do
			if a*d-b*c eq 0 then continue; end if;
			newf := P ! ((c*x+d)^6*Evaluate(newf,(a*x+b)/(c*x+d)));
			newf, twistbyd2 := modifying_goodsexticpoly(newf);
			twistbyd *:= twistbyd2;
			atoe := [Coefficient(newf,4-i) : i in [0..4]];
			lcmofdens := LCM([Denominator(atoe[i]) : i in [1..#atoe]]);
			fulltp := threetorspoly(Rationals(), atoe);
			if IsSeparable(fulltp) then
//			    printf "It is separable after transformation by %o\n", [a,b,c,d];
				break a;
			end if;
		end for;
    end if;

    Fac := Factorisation(fulltp);
    if ignoretwists then
		K := SplittingField(Fac[#Fac][1]);
    else
		ff := Fac[#Fac][1];
		gg := P ! [Coefficient(ff,2*i) : i in [0..Degree(ff)/2]];
		ggnew := P ! [Coefficient(gg,i)*twistbyd^(Degree(gg)-i) : i in [0..Degree(gg)]];
		ffnew := Evaluate(ggnew,x^2);
		K := SplittingField(ffnew);
		K := Polredabs(K);
    end if;

    if Degree(K) eq n or Degree(K) eq 2*n then
		return K, lcmofdens;
    else
		for g in [fa[1] : fa in Fac[1..#Fac-1] | Degree(fa[1]) ne 1] do
			newfacs := Factorisation(ChangeRing(g,K));
			if #newfacs ne Degree(g) then
				K := SplittingField(&*[h[1] : h in newfacs | Degree(h[1]) ne 1]);
				K := AbsoluteField(K);
				K := Polredabs(K);
				if Degree(K) eq n or Degree(K) eq 2*n then
					break;
				end if;
			end if;
		end for;
    end if;
    return K, lcmofdens;
end intrinsic;


intrinsic Mod3GaloisRepresentation(C :: CrvHyp, n :: RngIntElt) -> GrpHom, Map, FldNum
{Given n = the degree of the three torsion field of Jacobian of C,
returns the data associated to the mod-3 Galois representation.
The first return value is the representation, as a homomorphism from a permutation group A to GSp(4,3).
The second return value is a map from A to the set of automorphisms of the 3-torsion field K, which is
returned as the third return value.}
	G := CSp(4,GF(3));
    C1 := SimplifiedModel(C);
    badprimes := &*BadPrimes(C1)*2;
    P<x> := PolynomialRing(Rationals());
    K, lcmofdens := threetorsfield(C, n);
    Jac := Jacobian(C1);
    JacK := BaseExtend(Jac,K);
    KumK := KummerSurface(JacK);
    zeropt := KumK ! 0;

    f := HyperellipticPolynomials(C1);
    hompols, affpols := eqns_2PequalsnegativeP(Rationals(),[f,0]);
    A16<k1,k2,k3,k4,f0,f1,f2,f3,f4,f5,f6,alpha,l1,l2,l3,l4> := PolynomialRing(RationalField(),16);
    A5<k1,k2,k3,k4,alpha> := PolynomialRing(Rationals(),5);
    projec1 := hom<A16 -> A5 | [A5.i : i in [1..4]] cat [0 : i in [1..7]] cat [A5.5] cat [0 : i in [1..4]]>;
    A4<K1,K2,K3,K4> := PolynomialRing(Rationals(),4);
    projec2 := hom<A5 -> A4 | [A4.i : i in [1..4]] cat [0]>;
    temppols1 := [projec1(hompols[1])] cat [Resultant(projec1(hompols[j-1]), projec1(hompols[j]), alpha) : j in [2..#hompols]];
    temppols2 := [projec2(temppols1[j]) : j in [1..#temppols1]];

    P3 := ProjectiveSpace(K,3);
    X := Scheme(P3,temppols2);
    Xpts := RationalPoints(X);
    all_pts := [JacK!0];
	coords := [[0,0,0,0]];
	somebasis := [];

    printf "Total count of K-rational points on Kummer surface = %o\n", #Xpts;
    for Xpt in Xpts do
        kumpt := KumK ! Eltseq(Xpt);
        printf "Kummer pt constructed...";
        if kumpt ne zeropt and 3*kumpt eq zeropt then
            possible_points := Points(JacK, kumpt);
            printf "lifted to Jacobian...";
            if not possible_points[1] in all_pts then
                printf "it's a new point!\n";
				Append(~somebasis,possible_points[1]);
				newptcoord := [(i eq #somebasis) select 1 else 0 : i in [1..4]];
                all_pts := all_pts cat [pt+possible_points[1] : pt in all_pts] cat [pt+possible_points[2] : pt in all_pts];
				coords := coords cat [[x[i]+newptcoord[i] : i in [1..4]] : x in coords] cat [[x[i]+2*newptcoord[i] : i in [1..4]] : x in coords];
                if #all_pts eq 81 then break; end if;
            end if;
        end if;
    end for;


    if #all_pts ne 81 then
		printf "Did not find the correct three torsion field\n";
		return 0, "Error";
    end if;

    defK := DefiningPolynomial(K);
    dens := 1;
    for i := 2 to #all_pts do
		dens1 := LCM([LCM([Denominator(coe[j]) : j in [1..Degree(K)]]) : coe in Coefficients(all_pts[i][1])]);
		dens2 := LCM([LCM([Denominator(coe[j]) : j in [1..Degree(K)]]) : coe in Coefficients(all_pts[i][2])]);
		dens := LCM([dens,dens1,dens2]);
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
							basisindices := [i,i2,j2,j];
							basismodp := all_pts_k[basisindices];
							basis := all_pts[basisindices];
							coords_of_sympbasis := coords[basisindices];
							cofb_mat := Matrix(GF(3),4,4,coords_of_sympbasis);
							cofb_mat_inv := cofb_mat^-1;
							newcoords := [Eltseq(Matrix(GF(3),1,4,coord)*cofb_mat_inv) : coord in coords];
							assert newcoords[basisindices] eq [[(i eq j) select 1 else 0 : j in [1..4]] : i in [1..4]];
							break i;
						end if;
					end for;
				end for;
			end for;
		end for;
    end while;

/* Computing the Automorphism group of the three-torsion field and the action of each generator on the
three-torsion of Jac(C) as a matrix in GSp(4,3) wrt the fixed basis found above.*/

	AutK, auts, tau := AutomorphismGroup(K);
	gens := [tau(g) : g in GeneratorsSequence(AutK)];
	actionmats := [];
	PK := PolynomialRing(K);
	for g in gens do
		g_basis := [elt<JacK | PK![g(coe) : coe in Coefficients(Pi[1])], PK![g(coe) : coe in Coefficients(Pi[2])], Pi[3]> : Pi in basis];
		g_mat := G!Matrix(GF(3),4,4,[newcoords[Index(all_pts,P)] : P in g_basis]);
		Append(~actionmats,g_mat);
	end for;
	galrep := hom<AutK -> G | actionmats>;
	return galrep, tau, K;
end intrinsic;
