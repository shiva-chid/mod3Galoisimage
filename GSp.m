ZZ := Integers();

function lmset(M)
    return Sort([r cat [Multiplicity(M,r)]:r in Set(M)]);
end function;

function index(S,f:Project:=func<x|x>,Unique:=false)
    A := AssociativeArray();
    if Unique then
        for x in S do A[f(x)] := Project(x); end for;
    else
        for x in S do y := f(x); A[y] := IsDefined(A,y) select Append(A[y],Project(x)) else [Project(x)]; end for;
    end if;
    return A;
end function;

intrinsic GSpSize(d::RngIntElt, N::RngIntElt) -> RngIntElt
{ The order of the group of symplectic similitudes of degree d over Z/NZ. }
    require IsPrimePower(N) : "Currently only prime power level is supported.";
    p := PrimeFactors(N)[1]; e := Valuation(N,p);
    dby2 := ExactQuotient(d,2);
    ans := p^((e-1)*(2*dby2^2+dby2))*EulerPhi(p^e)*p^(dby2^2);
    for i := 1 to dby2 do
	ans := ans*(p^(2*i)-1);
    end for;
    return ans;
end intrinsic;

intrinsic Symp(d::RngIntElt, N::RngIntElt) -> GrpMat
{ The group of symplectic similitudes of degree d over Z/NZ. }
    require IsPrimePower(N) : "Currently only prime power level is supported.";
    p := PrimeFactors(N)[1]; e := Valuation(N,p);
    if e eq 1 then return sub<GL(d,Integers(p))|Generators(Sp(d,p))>; end if;
    dby2 := ExactQuotient(d,2);
    idmat := IdentityMatrix(Integers(p^(e-1)),dby2);
    zeromat := ZeroMatrix(Integers(p^(e-1)),dby2);
    J := BlockMatrix(2,2,[zeromat,idmat,-idmat,zeromat]);
    Jstd := StandardAlternatingForm(d,Integers(p^(e-1)));
    antidiagidmat := Matrix(Integers(p^(e-1)),dby2,dby2,[[((i+j) eq dby2+1) select 1 else 0 : j in [1..dby2]] : i in [1..dby2]]);
    permmat := GL(d,Integers(p^(e-1))) ! DirectSum(idmat,antidiagidmat);
    H := Conjugate(Symp(d,p^(e-1)),permmat);
    gens := Generators(H);
    assert &and[g*J*Transpose(g) eq J : g in gens];    

    liftsofgens := [];
    Mdp := MatrixRing(Integers(p),d);
    idmat := IdentityMatrix(Integers(p^e),dby2);
    zeromat := ZeroMatrix(Integers(p^e),dby2);
    J := BlockMatrix(2,2,[zeromat,idmat,-idmat,zeromat]);
    for x in gens do
	for y in Mdp do
	    g := ChangeRing(x,Integers(p^e))+p^(e-1)*ChangeRing(y,Integers(p^e));
	    if g*J*Transpose(g) eq J then
		Append(~liftsofgens,g);
		break;
	    end if;
	end for;
    end for;
    kernelgens := [];
    idmat := IdentityMatrix(Integers(p^e),d);
    zeromat := ZeroMatrix(Integers(p^e),dby2);
    for i := 1 to dby2 do
	for j := i to dby2 do
	    if i eq j then
		symmat := Matrix(Integers(p^e),dby2,dby2,[<i,j,p^(e-1)>]);
	    else
		symmat := Matrix(Integers(p^e),dby2,dby2,[<i,j,p^(e-1)>, <j,i,p^(e-1)>]);
	    end if;
	    uppermat := idmat + BlockMatrix(2,2,[zeromat,symmat,zeromat,zeromat]);
	    lowermat := idmat + BlockMatrix(2,2,[zeromat,zeromat,symmat,zeromat]);
	    Append(~kernelgens,uppermat);
	    Append(~kernelgens,lowermat);
	end for;
    end for;
    for i := 1 to dby2 do
	for j := 1 to dby2 do
	    elmtmat := Matrix(Integers(p^e),dby2,dby2,[<i,j,p^(e-1)>]);
	    Append(~kernelgens,idmat+BlockMatrix(2,2,[elmtmat,zeromat,zeromat,-Transpose(elmtmat)]));
	end for;
    end for;
    G := sub<GL(d,Integers(p^e))|liftsofgens cat kernelgens>;
    assert #G*EulerPhi(N) eq GSpSize(d,N);
    permmat := GL(d,Integers(p^e)) ! ChangeRing(permmat,Integers(p^e));
    G := Conjugate(G,permmat);
    Jstd := StandardAlternatingForm(d,Integers(p^e));
    assert &and[g*Jstd*Transpose(g) eq Jstd : g in Generators(G)];
    return G;
end intrinsic;

intrinsic GSp(d::RngIntElt, N::RngIntElt) -> GrpMat
{ The group of symplectic similitudes of degree d over Z/NZ. }
    require IsPrimePower(N) : "Currently only prime power level is supported.";
    p := PrimeFactors(N)[1]; e := Valuation(N,p);
    if e eq 1 then return sub<GL(d,Integers(p))|Generators(CSp(d,p))>; end if;
    H := Symp(d,N);
    a := PrimitiveRoot(N);
    idmat := IdentityMatrix(Integers(N),ExactQuotient(d,2));
    mat := GL(d,Integers(N)) ! DirectSum(idmat,a*idmat);
    return sub<GL(d,Integers(N))|Generators(H) join {mat}>;
end intrinsic;

intrinsic GSpLevel(H::GrpMat) -> RngIntElt, GrpMat
{ The least integer N such that H is the full inverse image of its reduction modulo N. }
    R := BaseRing(H); d := Degree(H); if not IsFinite(R) and #H eq 1 then return 1,sub<GL(d,ZZ)|>; end if;
    N := #R;
    cH := #H; cGSp := GSpSize(d,N);
    if cH eq cGSp then return 1,sub<GL(d,ZZ)|>; end if;
    if IsPrime(N) then return N,H; end if;
    for p in PrimeDivisors(N) do
        while N gt p and N mod p eq 0 and cH eq #ChangeRing(H,Integers(N div p))*cGSp/GSpSize(d,N div p) do N div:= p; end while;
    end for;
    return N,ChangeRing(H,Integers(N));
end intrinsic;

intrinsic GLLift(H::GrpMat,M::RngIntElt) -> GrpMat
{ The full preimage in GL(n,Z/MZ) of H in GL(n,Z/NZ) for a multiple M of N. }
    R := BaseRing(H);  if not IsFinite(R) and #H eq 1 then return GL(Degree(H),Integers(M)); end if;
    require Type(R) eq RngIntRes: "H must be a subgroup of GL(n,Z/NZ) for some positive integer N.";
    N := #R;
    require IsDivisibleBy(M,N): "M must be divisible by N for H in GL(n,Z/NZ)";
    GLn:=GL(Degree(H),Integers(M));
    _,pi:=ChangeRing(GLn,R);
    return sub<GLn|Kernel(pi),H @@ pi>; // Note: H @@ pi does not compute the full preimage!
end intrinsic;

intrinsic GLProject(H::GrpMat,M::RngIntElt) -> GrpMat
{ The projection of the preimage of H in GL(n,Zhat) to GL(n,Z/MZ). }
    R := BaseRing(H);  if not IsFinite(R) and #H eq 1 then return GSp(Degree(H),M); end if;
    require Type(R) eq RngIntRes: "H must be a subgroup of GL(n,Z/NZ) for some positive integer N.";
    N := #R; if N eq M then return H; end if;
    if IsDivisibleBy(N,M) then return ChangeRing(H,Integers(M)); end if;
    return ChangeRing(GLLift(H,LCM(M,N)),Integers(M));
end intrinsic;

intrinsic GSpLift(H::GrpMat,M::RngIntElt) -> GrpMat
{ The full preimage in GSp(n,Z/MZ) of H in GSp(n,Z/NZ) for a multiple M of N. }
    R := BaseRing(H);  if not IsFinite(R) and #H eq 1 then return GSp(Degree(H),M); end if;
    require Type(R) eq RngIntRes: "H must be a subgroup of GSp(n,Z/NZ) for some positive integer N.";
    N := #R;
    require IsDivisibleBy(M,N): "M must be divisible by N for H in GL(n,Z/NZ)";
    GSpn:=GSp(Degree(H),M);
    _,pi:=ChangeRing(GSpn,R);
    return sub<GSpn|Kernel(pi),H @@ pi>; // Note: H @@ pi does not compute the full preimage!
end intrinsic;

intrinsic GSpProject(H::GrpMat,M::RngIntElt) -> RngIntElt
{ The index of H in GSp. }
    R := BaseRing(H);  if not IsFinite(R) and #H eq 1 then return GSp(Degree(H),M); end if;
    require Type(R) eq RngIntRes: "H must be a subgroup of GSp(n,Z/NZ) for some positive integer N.";
    N := #R; if N eq M then return H; end if;
    if IsDivisibleBy(N,M) then return sub<GSp(Degree(H),M) | ChangeRing(H,Integers(M))>; end if;
    return sub<GSp(Degree(H),M) | ChangeRing(GSpLift(H,LCM(M,N)),Integers(M))>;
end intrinsic;

intrinsic GSpIndex(H::GrpMat) -> RngIntElt
{ The index of H in GSp. }
    return IsFinite(BaseRing(H)) select GSpSize(Degree(H),#BaseRing(H)) div #H else 1;
end intrinsic;

intrinsic GLDeterminantImage(H::GrpMat) -> GrpMat
{ det(H) as a subgroup of GL1. }
    R := BaseRing(H);  if not IsFinite(R) and #H eq 1 then return sub<GL(1,ZZ)|>; end if;
    return sub<GL(1,R)|[[Determinant(h)]:h in Generators(H)]>;
end intrinsic;

intrinsic GLDeterminantIndex(H::GrpMat) -> RngIntElt
{ The index of det(H) in GL1. }
    R := BaseRing(H);  if not IsFinite(R) and #H eq 1 then return 1; end if;
    return Index(GL(1,R),GLDeterminantImage(H));
end intrinsic;

intrinsic GLTranspose(H::GrpMat) -> GrpMat
{ Given a subgroup H of GL(n,R) for some ring R returns the transposed subgroup. }
    return sub<GL(Degree(H),#BaseRing(H))|[Transpose(g):g in Generators(H)]>;
end intrinsic;

intrinsic GLOrbitSignature(H::GrpMat:N:=0) -> SeqEnum[SeqEnum[RngIntElt]]
{ The orbit signature of H (the ordered list of triples [e,s,m] where m is the number of non-trivial right H-orbits of V of size s and exponent e). }
    if N eq 0 then N,H := GSpLevel(H); else require N eq 1 or #BaseRing(H) eq N: "N must be equal to the cardinality of the base ring of H"; end if;
    if N eq 1 then return [Universe([[1]])|]; end if;
    D := Divisors(N);
    function ord(v) return Min([n:n in D|n*v eq 0*v]); end function;
    return lmset({*[ord(o[1]),#o]:o in Orbits(H)|o ne {RSpace(H)!0}*});
end intrinsic;

intrinsic GSpSimilitudeCharacter(A::GrpMatElt) -> RngIntResElt
{ Given a matrix A in GSp(2g,Z/NZ) returns a such that A*J*Transpose(A) = a*J, where J is the symplectic form on Sp(2g,Z/NZ). }
    J := StandardAlternatingForm(Degree(A),BaseRing(A));
    M := Parent(J); A := M!A;
    B := Transpose(A)*J*A;
//    return [a:a in BaseRing(A)|B eq a*J][1];
    sim := B[1][4];
    assert B eq sim*J;
    return sim;
end intrinsic;

intrinsic GSpSimilitudeImage(H::GrpMat) -> GrpMat
{ Similitude of H as a subgroup of GL1. }
    R := BaseRing(H);  if not IsFinite(R) and #H eq 1 then return sub<GL(1,ZZ)|>; end if;
    return sub<GL(1,R)|[[GSpSimilitudeCharacter(h)]:h in Generators(H)]>;
end intrinsic;

intrinsic GSpSimilitudeIndex(H::GrpMat) -> RngIntElt
{ The index of similitude of H in GL1. }
    R := BaseRing(H);  if not IsFinite(R) and #H eq 1 then return 1; end if;
    return Index(GL(1,R),GSpSimilitudeImage(H));
end intrinsic;

function csig(c) return [c[1]] cat [ZZ|f:f in Coefficients(CharacteristicPolynomial(c[3]))] cat [ZZ|GSpSimilitudeCharacter(c[3]),c[2]]; end function;

intrinsic GSpClassSignature(H::GrpMat:N:=0) -> SeqEnum[Tup]
{ The class signature of H (the ordered list of 5-tuples (o,a,d,s,m) where m is the number of conjugacy classes of elements of H of size s, order o, similitude d, and coefficients of characteristic polynomial a). }
    if N eq 0 then N,H := GSpLevel(H); else require N eq 1 or #BaseRing(H) eq N: "N must be equal to the cardinality of the base ring of H"; end if;
    if N eq 1 then return []; end if;
    C := ConjugacyClasses(H);
    S := {* csig(c) : c in C *};
    return lmset(S);
end intrinsic;

intrinsic GSpConjugacyClasses(d::RngIntElt, N::RngIntElt) -> SeqEnum[Tup], Map
{ An ordered sequence of tuples <order,length,similitude,rep> giving the conjugacy classes of GSp(4,Integers(N)), and the classmap. }
    if N eq 1 then return [<1,1,1,GL(4,Integers())!IdentityMatrix(4,Integers())>]; end if;
    require IsPrimePower(N) : "Currently only prime power level is supported.";
    G := GSp(d,N);
    CCs := ConjugacyClasses(G);
    phi := ClassMap(G);
    return [ <r[1],r[2],GSpSimilitudeCharacter(r[3]),r[3]>:r in CCs], phi;
end intrinsic;

intrinsic GSpConjugacyClassSigns(d::RngIntElt, N::RngIntElt:CCs:=[],phi:=map<{1}->{1}|x:->1>) -> SeqEnum[Tup], Map
{ An ordered sequence of tuples <sign,size> where sign is <[ap,bp,p] mod N,n> where ap, bp are the cubic and quadratic coefficients of the characteristic polynomials of elements of GSp(4,Integers(N)) and n is the dimension of fixed space, and an index map of these signs. }
    if N eq 1 then return [<1,1>]; end if;
    require IsPrimePower(N) : "Currently only prime power level is supported.";
    ZN := Integers(N);
    if CCs eq [] then CCs, phi := GSpConjugacyClasses(d,N); end if;
    ClassSigns := [];
//    counts := [];
    for x in CCs do
        pol := CharacteristicPolynomial(x[4]);
        dim := Dimension(Kernel(x[4]-IdentityMatrix(ZN,d)));
        sign := <[Coefficient(pol,3),Coefficient(pol,2),x[3]],dim>;
        if not sign in ClassSigns then Append(~ClassSigns,sign); end if;
/*
        if sign in ClassSigns then
            counts[Index(ClassSigns,sign)] +:= x[2];
        else
            Append(~ClassSigns,sign); Append(~counts,x[2]);
        end if;
*/
    end for;
    return ClassSigns, map<Seqset(ClassSigns)->{1..#ClassSigns}|x:->Index(ClassSigns,x)>;
//    return [<ClassSigns[i],counts[i]> : i in [1..#ClassSigns]], map<Seqset(ClassSigns)->{1..#ClassSigns}|x:->Index(ClassSigns,x)>;
end intrinsic;

intrinsic GSpCharpolsDistribution(H::GrpMat:N:=0,ClassSigns:=[],SignPhi:=map<{1}->{1}|x:->1>) -> SeqEnum[Tup], RngIntElt
{ The non-normalized distribution of characteristic polynomials of elements in H, stored as [ap,bp,p] mod N. }
    ClassSignsdist, cH := GSpClassSignsDistribution(H:N:=N,ClassSigns:=ClassSigns,SignPhi:=SignPhi);
    Charpols := [];
    for x in ClassSigns do
        if x[1] in Charpols then continue; end if;
        Append(~Charpols,x[1]);
    end for;
//    print Charpols;
    Charpolsdist := [<x,0> : x in Charpols];
    for x in ClassSignsdist do
        n := Index(Charpols,x[1][1]);
//        print x[1][1], n;
        assert Charpolsdist[n][1] eq x[1][1];
        oldorder := Charpolsdist[n][2];
        Charpolsdist[n] := <Charpolsdist[n][1],oldorder+x[2]>;
    end for;
    return Charpolsdist, cH;
end intrinsic;

intrinsic GSpClassSignsDistribution(H::GrpMat:N:=0,ClassSigns:=[],SignPhi:=map<{1}->{1}|x:->1>) -> SeqEnum[Tup], RngIntElt
{ The non-normalized distribution of conjugacy class signs <[ap,bp,p] mod N,n> of elements in H. }
    R := BaseRing(H); if not IsFinite(R) and #H eq 1 then H := GSp(Degree(H),N); end if;
    if N eq 0 then N := #BaseRing(H); end if;
    require #BaseRing(H) eq N: "N must be equal to the cardinality of the base ring of H";
    d := Degree(H); ZN := Integers(N);
    if ClassSigns eq [] then ClassSigns, SignPhi := GSpConjugacyClassSigns(d,N); end if;
    cH := #H;
    C := ConjugacyClasses(H);
    ClassSignsdist := [<x,0> : x in ClassSigns];
    for c in C do
        pol := CharacteristicPolynomial(c[3]);
        sim := GSpSimilitudeCharacter(c[3]);
        dim := Dimension(Kernel(c[3]-IdentityMatrix(ZN,d)));
        sign := <[Coefficient(pol,3),Coefficient(pol,2),sim],dim>;
        ii := SignPhi(sign);
//        print ii, ClassSigns[ii], sign;
        assert &and[ClassSigns[ii][j] eq sign[j] : j in [1,2]];
        oldorder := ClassSignsdist[ii][2];
        ClassSignsdist[ii] := <ClassSignsdist[ii][1],oldorder+c[2]>;
    end for;
    return ClassSignsdist, cH;
end intrinsic;

/*
intrinsic GSpConjugacyClassCanonicalRepresentative(g::GrpMatElt:N:=0) -> GrpMatElt
{returns a canonical representative of the GSp-conjugacy class of g. It is the
smallest element in lexicographical ordering}

end intrinsic;
*/

intrinsic GSpGassmannDistribution(H::GrpMat:N:=0,CCs:=[],phi:=map<{1}->{1}|x:->1>) -> SeqEnum[Tup], RngIntElt
{ The non-normalized distribution of GSp-conjugacy classes of elements in H. }
    R := BaseRing(H);
    if not IsFinite(R) and #H eq 1 then
        d := Degree(H);
        if CCs eq [] then CCs, phi := GSpConjugacyClasses(d,N); end if;
        return [<x[4],x[2]> : x in CCs], GSpSize(d,N);
    end if;
    if N eq 0 then N := #BaseRing(H); end if;
    require #BaseRing(H) eq N: "N must be equal to the cardinality of the base ring of H";
    d := Degree(H);
    if CCs eq [] then CCs, phi := GSpConjugacyClasses(d,N); end if;
    cH := #H;
    C := ConjugacyClasses(H);
    ccsdist := [<x[4],0> : x in CCs];
    for c in C do
/*
        for ii in [1..#CCs] do
            if IsConjugate(G,c[3],CCs[ii][3]) then
                oldorder := ccsdist[ii][2];
                ccsdist[ii] := <ccsdist[ii][1],oldorder+c[2]>;
                break;
            end if;
        end for;
*/
        ii := phi(c[3]);
        oldorder := ccsdist[ii][2];
        ccsdist[ii] := <ccsdist[ii][1],oldorder+c[2]>;
    end for;
    ccsdist := [<ccsdist[i][1],ccsdist[i][2]> : i in [1..#ccsdist]];
    return ccsdist, cH;
end intrinsic;

/*
intrinsic GSpGassmannSignature(H::GrpMat:N:=0) -> SeqEnum[Tup]
{ Sorted list of pairs <r,m> where r is a similarity invariant of GSp_4(N) and m > 0 is its multiplicity in H; this uniquely identifies the Gassmann equivalence class of H as a subgroup of GSp_4(N). }
// TODO: not implemented yet. Need to write GSpSimilarityMultiset
    if N eq 0 then N,H := GSpLevel(H); else require N eq 1 or #BaseRing(H) eq N: "N must be equal to the cardinality of the base ring of H"; end if;
    if N eq 1 then return []; end if;
    S := GSpSimilarityMultiset(H);
    return Sort([<r,Multiplicity(S,r)>:r in Set(S)]);
end intrinsic;
*/

intrinsic GSpCanonicalize(G::GrpMat,H::GrpMat:Verbose:=false) -> SeqEnum[GrpMat]
{ Computes a canonical set of generators for a conjugate of a subgroup H of GSp (the returned list generates a conjugate of H and depends only on the conjugacy class of H, not H itself). }
    if G eq GSp(Degree(G),#BaseRing(G)) then G := GSpLift(sub<GL(Degree(G),ZZ)|>,#BaseRing(H)); end if;
    if #BaseRing(G) lt #BaseRing(H) then G := GSpLift(G,#BaseRing(H)); end if;
    if not H subset G then b,g := IsConjugateSubgroup(GSp(Degree(H),#BaseRing(H)),G,H); assert b; H := H^g; assert H subset G; end if;
    M := #G;
    if Verbose then cnt := M div #Normalizer(G,H); printf "Canonicalizing subgroup of size %o and index %o with %o conjugates\n", #H, M div #H, cnt; s := Cputime(); end if;
    C := ConjugacyClasses(H); C := C[2..#C];
    X := index([1..#C],func<i|csig(C[i])>);
    S := [k:k in Keys(X)];
    Z := [&+[M div #Centralizer(G,C[j][3]):j in X[S[i]]]:i in [1..#S]];
    I := Sort([1..#S],func<a,b|Z[a] ne Z[b] select Z[a]-Z[b] else (S[a] lt S[b] select -1 else 1)>); 
    S := [S[i]:i in I];  Z := [Z[i]:i in I];
    a := Min([Min([h:h in Conjugates(G,C[j][3])]):j in X[S[1]]]);
    gens := [a];
    K := sub<G|gens>;
    if #K eq #H then return gens; end if;
    if Verbose and cnt gt 1 then printf "Enumerating %o conjugates of subgroup H of size %o...",cnt,#H; t := Cputime(); end if;
    T := Conjugates(G,H);
    if Verbose and cnt gt 1 then printf "%.3os\n", Cputime()-t; end if;
    n := 1;
    while #K lt #H do
        if #T gt 1 then
            T := [H:H in T|K subset H];
            if #T eq 1 then _,g := IsConjugate(G,H,T[1]);  H:=H^g; C:=[<c[1],c[2],c[3]^g>:c in C]; end if;
        end if;
        //if Verbose then printf "Expanding canonical subgroup K of size %o contained in %o conjugates of H...", #K, #T; t:=Cputime(); end if;
        for i:=n to #S do
            if #T eq 1 then
                A := &cat[[h:h in C[j][3]^H|not h in K]:j in X[S[i]]];
            else
                A := &cat[[h:h in C[j][3]^G|not h in K and &or[h in H:H in T]]:j in X[S[i]]];
            end if;
            if #A eq 0 then continue; end if;
            n := i;
            a := Min(A);
            Append(~gens,a); K := sub<G|gens>;
            break;
        end for;
        //if Verbose then printf "%.3os\n", Cputime()-t; end if;
    end while;
    if Verbose then printf "Canonicalized subgroup of size %o with %o conjugates in %.3os\n", #H, cnt, Cputime()-s; end if;
    return gens;
end intrinsic;

intrinsic GSpCompareLabels(a::MonStgElt,b::MonStgElt) -> RngIntElt
{ Lexicographically compares subgroup labels of the form N.i.n (N=level, i=index, n=ordinal) as lists of integers.  Returns -1,0,1. }
    if a eq b then return 0; end if; if a eq "?" then return 1; end if; if b eq "?" then return -1; end if;
    r := [StringToInteger(x):x in Split(a,".")]; s := [StringToInteger(x):x in Split(b,".")];
    require #r eq 3 and #s eq 3: "Invalid subgroup label";
    return r lt s select -1 else 1;
end intrinsic;

intrinsic GSpSortLabels(L::SeqEnum[MonStgElt]) -> SeqEnum[MonStgElt]
{ Sorts the specified list of labels of subgroups of GSp(d,Zhat). }
    L := Sort(L,func<a,b|GSpCompareLabels(a,b)>);
    return L;
end intrinsic;

intrinsic GSpCompareLabelLists(a::SeqEnum[MonStgElt],b::SeqEnum[MonStgElt]) -> RngIntElt
{ Lexicographically compares two lists of subgroup labels. }
    if a eq b then return 0; end if;
    for i in [1..#a] do
        if i gt #b then return 1; end if;
        if a[i] ne b[i] then return GSpCompareLabels(a[i],b[i]); end if;
    end for;
    return #a lt #b select -1 else 0;
end intrinsic;

intrinsic GLMinimizeGenerators(G::Grp) -> Grp
{ Attempts to minimize the number of generators of a finite group by sampling random elements.  Result is not guaranteed to be optimal unless G is abelian (but it very likely will be optimal or very close to it, see https://doi.org/10.1016/S0021-8693(02)00528-8). }
    require IsFinite(G): "G must be a finite group";
    n := #G;
    if IsAbelian(G) then Gab,pi := AbelianGroup(G); B := AbelianBasis(Gab); return sub<G|[Inverse(pi)(b):b in B]>; end if;
    r := 2;
    while true do
        for i:=1 to 100 do H := sub<G|[Random(G):i in [1..r]]>; if #H eq n then return H; end if; end for;
        r +:= 1;
    end while;
end intrinsic;

gspnode := recformat<
    label:MonStgElt,
    level:RngIntElt,
    index:RngIntElt,
    orbits:SeqEnum,
    children:SeqEnum,
    parents:SeqEnum,
    subgroup:GrpMat,
    ClassSignDist:SeqEnum,
    gassmanndist:SeqEnum>;

intrinsic GSpLattice(d::RngIntElt, N::RngIntElt, IndexLimit::RngIntElt: CCs:=[], phi:=map<{1}->{1}|x:->1>, ClassSigns:=[], SignPhi:=map<{1}->{1}|x:->1>, Verbose:=true, IndexDivides:=false, excludepgroups:=1) -> Assoc
{ Lattice of subgroups of GSp(d,N) with surjective similitude character and index bounded by IndexLimit. Returns a list of records with attributes label, level, index, orbits, children, parents, subgroup where children and parents are lists of labels that identify maximal subgroups and minimal supergroups. }
    require d ge 2 and IsEven(d): "Degree must be a positive even integer";
    require N gt 1: "Level must be an integer greater than 1";
    G := GSp(d,N);
    if IndexLimit eq 0 then IndexLimit := #G; end if;
    O := IndexDivides select ExactQuotient(#G,IndexLimit) else 1;
    if excludepgroups ne 1 then
	require IsPrime(excludepgroups) : "Currently only p-groups for prime p can be excluded";
	p := excludepgroups;
	if Verbose then printf "Enumerating subgroups of GSp(%o,Z/%oZ) of index %o %o that are not %o-groups and that have maximal similitude...", d, N, IndexDivides select "dividing" else "at most", IndexLimit, p; s := Cputime(); end if;
	di := GSpSimilitudeIndex(G);
	filter := func<H|GSpSimilitudeIndex(H) eq di>;
	if not PrimeFactors(O) in {[],[p]} then
	    S := [H`subgroup: H in Subgroups(G : IndexLimit:=IndexLimit, OrderMultipleOf:=O) | filter(H`subgroup)];
	else
	    divs := [d : d in Divisors(#G div O) | IndexLimit*O*d gt #G and not PrimeFactors(d) in {[],[p]}];
	    S := &cat[[H`subgroup : H in Subgroups(G : OrderEqual:=O*d) | filter(H`subgroup)] : d in divs];
	end if;
    else
	if Verbose then printf "Enumerating subgroups of GSp(%o,Z/%oZ) of index %o %o with maximal similitude...", d, N, IndexDivides select "dividing" else "at most", IndexLimit; s := Cputime(); end if;
	di := GSpSimilitudeIndex(G);
	filter := func<H|GSpSimilitudeIndex(H) eq di>;
	S := [H`subgroup: H in Subgroups(G : IndexLimit:=IndexLimit, OrderMultipleOf:=O) | filter(H`subgroup)];
    end if;
    if Verbose then
        printf "found %o subgroups in %.3os\n", #S, Cputime()-s;
        printf "Computing level, index, orbit signature, and class signature for %o groups...", #S; s := Cputime();
    end if;
    T := [<level,GSpIndex(H),GLOrbitSignature(H:N:=level),GSpClassSignature(H:N:=level)> where level,H:=GSpLevel(K) : K in S];
    X := index([1..#T],func<i|<T[i][1],T[i][2],T[i][3]>>);
    if Verbose then printf "%.3os\nComputing lattice edges for %o groups...", Cputime()-s, #T; s:=Cputime(); end if;
    M := {};
    for i:= 1 to #T do
        if 2*T[i][2] gt IndexLimit then continue; end if;
        if excludepgroups eq 1 then
            m := [H`subgroup:H in MaximalSubgroups(S[i] : IndexLimit:=IndexLimit div T[i][2], OrderMultipleOf:=O) | filter(H`subgroup)];
        else
            m := [H`subgroup:H in MaximalSubgroups(S[i] : IndexLimit:=IndexLimit div T[i][2], OrderMultipleOf:=O) | filter(H`subgroup) and not PrimeFactors(H`order) in {[],[excludepgroups]}];
        end if;
        for H in m do
            level,K := GSpLevel(H);
            J := X[<level,GSpIndex(K),GLOrbitSignature(K:N:=level)>]; j := 1;
            if #J gt 1 then
                c := GSpClassSignature(K:N:=level);
                J := [k:k in J|T[k][4] eq c];
                if #J gt 1 then
                    G:=GSp(d,level);
                    while j lt #J do if IsConjugate(G,GSpProject(S[J[j]],level),K) then break; end if; j+:=1; end while;
                end if;
            end if;
            Include(~M,<i,J[j]>);
        end for;
    end for;
    if Verbose then printf "found %o edges in %.3os\n", #M, Cputime()-s; end if;
    for i:=1 to #S do if T[i][1] gt 1 and T[i][1] lt N then S[i] := ChangeRing(S[i],Integers(T[i][1])); end if; end for;
    Xsubs := index(M,func<r|r[1]>:Project:=func<r|r[2]>); subs := func<i|IsDefined(Xsubs,i) select Xsubs[i] else []>;
    Xsups := index(M,func<r|r[2]>:Project:=func<r|r[1]>); sups := func<i|IsDefined(Xsups,i) select Xsups[i] else []>;
    X := index([1..#T],func<i|<T[i][1],T[i][2]>>);
    L := ["" : i in [1..#T]];
    Lsups := [[] : i in [1..#T]];
    G := GSp(d,N);
    B := [false:i in [1..#T]];  assert S[#S] eq G; B[#S] := true;
    if Verbose then printf "Labeling %o subgroups\n", #S; s := Cputime(); end if;
    cmpkeys := function(a,b)
        n := GSpCompareLabelLists(a[1],b[1]); if n ne 0 then return n; end if;
        if a[2] lt b[2] then return -1; elif a[2] gt b[2] then return 1; end if;
        if a[3] lt b[3] then return -1; elif a[3] gt b[3] then return 1; end if;
        return 0;
    end function;
    label := func<N,i,n|Sprintf("%o.%o.%o",N,i,n)>; IL := AssociativeArray();
    ntab := AssociativeArray(); for k in Keys(X) do ntab[k] := 1; end for;
    for k in Sort([k:k in Keys(X)]) do
        // all parents of subgroups in X[k] must have smaller index and have already been labeled
        for i in X[k] do Lsups[i] := Sort([L[j]:j in sups(i)],func<a,b|GSpCompareLabels(a,b)>); end for;
        if #X[k] eq 1 then
            i := X[k][1]; L[i] := label(k[1],k[2],ntab[k]); IL[L[i]] := i; ntab[k] +:= 1;
        else
            Y := index(X[k],func<i|<Lsups[i],T[i][3],T[i][4]>>);
            Z := Sort([r:r in Keys(Y)],cmpkeys);
            for r in Z do
                if #Y[r] gt 1 then
                    j := IL[r[1][#r[1]]];
                    if not B[j] then
                        J := []; i := j; repeat J := [i] cat J; i := IL[Lsups[i][#Lsups[i]]]; until B[i]; J := [i] cat J;
                        for i:=2 to #J do S[J[i]] := sub<GSp(d,#BaseRing(S[J[i]]))|GSpCanonicalize(S[J[i-1]],S[J[i]]:Verbose:=Verbose)>; B[J[i]] := true; end for;
                    end if;
                    A := [GSpCanonicalize(S[j],S[i]:Verbose:=Verbose):i in Y[r]];
                    for i:=1 to #A do S[Y[r][i]] := sub<G|A[i]>; B[i] := true; end for;
                    I := Sort([1..#A],func<i,j|A[i] lt A[j] select -1 else 1>);
                    for i in [Y[r][j]:j in I] do L[i] := label(k[1],k[2],ntab[k]); IL[L[i]] := i; ntab[k] +:= 1; end for;
                else
                    i := Y[r][1]; L[i] := label(k[1],k[2],ntab[k]); IL[L[i]] := i; ntab[k] +:= 1;
                end if;
            end for;
        end if;
    end for;
    Lsubs := [GSpSortLabels([L[j]:j in subs(i)]): i in [1..#S]];
    if Verbose then printf "Labeling took %.3os\nMinimizing generators for %o groups...", Cputime()-s, #L; s:=Cputime(); end if;
    X := AssociativeArray();
    if CCs eq [] then CCs, phi := GSpConjugacyClasses(d,N); end if;
    if ClassSigns eq [] then ClassSigns, SignPhi := GSpConjugacyClassSigns(d,N); end if;
    for i:=1 to #L do
        H := T[i][1] eq 1 select sub<GL(d,ZZ)|> else GLMinimizeGenerators(S[i]);
        ccdist := GSpGassmannDistribution(H:N:=N,CCs:=CCs,phi:=phi);
        ClassSignDis := GSpClassSignsDistribution(H:N:=N,ClassSigns:=ClassSigns,SignPhi:=SignPhi);
        X[L[i]]:= rec<gspnode|label:=L[i],level:=T[i][1],index:=T[i][2],orbits:=T[i][3],children:=Lsubs[i],parents:=Lsups[i],subgroup:=H,ClassSignDist:=ClassSignDis,gassmanndist:=ccdist>;
    end for;
    if Verbose then printf "%.3os\n", Cputime()-s; end if;
    return X;
end intrinsic;

intrinsic GSpLookupLabel(X::Assoc, H::GrpMat : NotFound:="?") -> MonStgElt
{ The label of the specified subgroup of GSp(d,Z/NZ) if it is present in the specified subgroup lattice (up to conjugacy). }
    if Type(BaseRing(H)) eq FldFin and IsPrime(#BaseRing(H)) then H := ChangeRing(H,Integers(#BaseRing(H))); end if;
    N,H := GSpLevel(H);
    if N eq 1 then return "1.1.1"; end if;
    i := GSpIndex(H);
    G := GSp(Degree(H),#BaseRing(H));
    prefix := Sprintf("%o.%o.",N,i);
    S := [k:k in Keys(X)|#k ge #prefix and k[1..#prefix] eq prefix];
    if #S eq 0 then return NotFound; end if;
    o := GLOrbitSignature(H:N:=N);
    S := [k:k in S|X[k]`orbits eq o];
    for k in S do if IsConjugate(G,H,X[k]`subgroup) then return k; end if; end for;
    return NotFound;
end intrinsic;

intrinsic GSpProbabilityOfFrobSignsArisingFromH(FrobSigns::SeqEnum,H::GrpMat:N:=0,ClassSigns:=[],SignPhi:=map<{1}->{1}|x:->1>,prec:=10) -> FldRatElt
{ Given a subgroup H and a list of Frobenius characteristic polynomials, returns the probability of getting these assuming each Frobenius matrix is drawn from H independently and randomly. }
    R := BaseRing(H); if not IsFinite(R) and #H eq 1 then H := GSp(Degree(H),N); end if;
    if N eq 0 then N := #BaseRing(H); end if;
    require #BaseRing(H) eq N: "N must be equal to the cardinality of the base ring of H";
    d := Degree(H);
    if ClassSigns eq [] then ClassSigns, SignPhi := GSpConjugacyClassSigns(d,N); end if;
    Re := RealField(prec);
    S, cH := GSpClassSignsDistribution(H:N:=N,ClassSigns:=ClassSigns,SignPhi:=SignPhi);
//    printf "Indeed ClassSigns are ordered: %o\n", &and[SignPhi(S[i][1]) eq i : i in [1..#S]];
    HClassSigns_inds := {i : i in [1..#S] | S[i][2] ne 0};
    FrobSign_inds := {* SignPhi(x) : x in FrobSigns *};
//    print FrobSign_inds, HClassSigns_inds;
    if not Set(FrobSign_inds) subset HClassSigns_inds then return 0; end if;
    n := #FrobSign_inds;
    FrobSign_occurences := [Multiplicity(FrobSign_inds,i) : i in [1..#ClassSigns]];
//    print n, FrobSign_occurences, cH, [s[2] : s in S];
    return Re!Multinomial(n,FrobSign_occurences)*(1/cH)^n*&*[S[i,2]^FrobSign_occurences[i] : i in [1..#S]];
end intrinsic;

intrinsic GSpProbabilityOfFrobsArisingFromH(FrobMats::SeqEnum[AlgMatElt],H::GrpMat:N:=0,CCs:=[],phi:=map<{1}->{1}|x:->1>,prec:=10) -> FldRatElt
{ Given a subgroup H and a list of Frobenius Matrices, returns the probability of getting these conjugacy classes of Frobenius matrices assuming each Frobenius matrix is drawn from H independently and randomly. }
    R := BaseRing(H); if not IsFinite(R) and #H eq 1 then H := GSp(Degree(H),N); end if;
    if N eq 0 then N := #BaseRing(H); end if;
    d := Degree(H);
    if CCs eq [] then CCs, phi := GSpConjugacyClasses(d,N); end if;
    Re := RealField(prec);
    S, cH := GSpGassmannDistribution(H:N:=N,CCs:=CCs,phi:=phi);
//    printf "Indeed ConjugacyClasses are ordered: %o\n", &and[phi(S[i][1]) eq i : i in [1..#S]];
    Hccs_inds := {i : i in [1..#S] | S[i][2] ne 0};
    FrobMat_inds := {* phi(x) : x in FrobMats *};
    if not Set(FrobMat_inds) subset Hccs_inds then return 0; end if;
    n := #FrobMat_inds;
    FrobMat_occurences := [Multiplicity(FrobMat_inds,i) : i in [1..#CCs]];
    return Re!Multinomial(n,FrobMat_occurences)*(1/cH)^n*&*[S[i,2]^FrobMat_occurences[i] : i in [1..#S]];
end intrinsic;

intrinsic GSpBayesianProbabilityUpdateFrobSign(FrobSigns::SeqEnum[Tup],S::SeqEnum[Tup]:N:=0,ClassSigns:=[],SignPhi:=map<{1}->{1}|x:->1>,prec:=10) -> SeqEnum[Tup]
{ Given a list S of tuples <H,p> giving a prior distribution p on subgroups H, and a list of sampled Frobenius characteristic polynomials, return the groups in S sorted in decreasing order of the updated probabilities for each group, and the probabilities. }
    if N eq 0 then N := LCM([#BaseRing(x[1]) : x in S]); S := [<GSpLift(x[1],N),x[2]> : x in S]; end if;
    d := Degree(S[1,1]);
    if ClassSigns eq [] then ClassSigns, SignPhi := GSpConjugacyClassSigns(d,N); end if;
    prior := [x[2] : x in S];
//    printf "prior = %o\n", prior;
    ProbabilityOfFrobSignsGivenH := [GSpProbabilityOfFrobSignsArisingFromH(FrobSigns,x[1]:N:=N,ClassSigns:=ClassSigns,SignPhi:=SignPhi,prec:=prec) : x in S];
//    print ProbabilityOfFrobSignsGivenH;
    posterior := [prior[i]*ProbabilityOfFrobSignsGivenH[i] : i in [1..#S]];
//    printf "posterior = %o\n", posterior;
    normalization_const := &+posterior;
    posterior := [x/normalization_const : x in posterior];
    S_updated := [<S[i,1],posterior[i]> : i in [1..#S] | posterior[i] ne 0];
    return Sort(S_updated, func<H1,H2|H2[2]-H1[2]>);
end intrinsic;

intrinsic GSpBayesianProbabilityUpdateFrobMat(FrobMats::SeqEnum[AlgMatElt],S::SeqEnum[Tup]:N:=0,CCs:=[],phi:=map<{1}->{1}|x:->1>,prec:=10) -> SeqEnum[Tup]
{ Given a list S of tuples <H,p> giving a prior distribution p on subgroups H, and a list of sampled Frobenius Matrices, return the groups in S sorted in decreasing order of the updated probabilities for each group, and the probabilities. }
    if N eq 0 then N := LCM([#BaseRing(x[1]) : x in S]); S := [<GSpLift(x[1],N),x[2]> : x in S]; end if;
    d := Degree(S[1,1]);
    if CCs eq [] then CCs, phi := GSpConjugacyClasses(d,N); end if;
    prior := [x[2] : x in S];
    ProbabilityOfFrobMatsGivenH := [GSpProbabilityOfFrobsArisingFromH(FrobMats,x[1]:N:=N,CCs:=CCs,phi:=phi,prec:=prec) : x in S];
    posterior := [prior[i]*ProbabilityOfFrobMatsGivenH[i] : i in [1..#S]];
//    print posterior;
    normalization_const := &+posterior;
    posterior := [x/normalization_const : x in posterior];
    S_updated := [<S[i,1],posterior[i]> : i in [1..#S] | posterior[i] ne 0];
    return Sort(S_updated, func<H1,H2|H2[2]-H1[2]>);
end intrinsic;


intrinsic symplecticbasis(fourpoints :: SeqEnum, N :: RngIntElt) -> SeqEnum
{return a symplecticbasis of the 4-dimensional space spanned by the given four
N-torsion points with respect to the Weil pairing}
    require #fourpoints eq 4 : "Need 4 points on Jacobian";
    require {Order(P) : P in fourpoints} eq {N} : "All 4 points must have order N";
    ZN := Integers(N);
    P1 := fourpoints[1];
    for pt in fourpoints do
		temp := WeilPairing(P1,pt,N);
		if temp ne 1 then
			P4 := pt;
			zetaN := temp;
			break;
		end if;
    end for;
    m := AssociativeArray();
    for i := 0 to N-1 do
        m[zetaN^i] := i;
    end for;

    remainingpoints := Exclude(Exclude(fourpoints,P1),P4);
    P2 := remainingpoints[1];
    P3 := remainingpoints[2];
    P2 := P2 + m[WeilPairing(P4,P2,N)]*P1 - m[WeilPairing(P1,P2,N)]*P4;
    P3 := ZZ!(ZN!(m[WeilPairing(P2,P3,N)]^-1))*P3;
    P3 := P3 + m[WeilPairing(P4,P3,N)]*P1 - m[WeilPairing(P1,P3,N)]*P4;
    sympbasis := [P1, P2, P3, P4];

    pairingsmat := Matrix(GF(N),4,4,[[m[WeilPairing(x,y,N)] : y in sympbasis] : x in sympbasis]);
    J := StandardAlternatingForm(4,N);
    assert pairingsmat eq J;
    return sympbasis;
end intrinsic;


intrinsic GSpFrobMatrixModN(C::CrvHyp,N::RngIntElt,p::RngIntElt:CCs:=[])->AlgMatElt
{returns a matrix in the conjugacy class of the Frobenius matrix at p for the action on Jac(C)[N]}
    P<t> := PolynomialRing(Rationals());
    if CCs eq [] then CCs, phi := GSpConjugacyClasses(4,N); end if;
    C1 := SimplifiedModel(C);
    JacC1 := Jacobian(C1);
    badprimes := &*BadPrimes(C)*2;
    require N*badprimes mod p ne 0 : "Bad prime"; 
    charpol := P ! Reverse(Coefficients(EulerFactor(BaseExtend(JacC1, GF(p)))));
    possible_ccs := [x[4] : x in CCs | CharacteristicPolynomial(x[4]) eq ChangeRing(charpol,Integers(N))];
    possible_orders := Sort(Setseq({Order(x) : x in possible_ccs}));
    printf "p = %o, possible_orders of Frob_p = %o\n", p, possible_orders;
//    for n in possible_orders do
    n := Maximum(possible_orders);
	    kpn := GF(p,n);
	    Jackpn := BaseExtend(JacC1,kpn);
	    A, incl := Sylow(Jackpn,N);
        print #quo<A|N*A>;
//	    if #quo<A|N*A> ne N^4 then continue; end if;
	    assert #AbelianInvariants(A) eq 4;
        print n;
        Pred<x> := PolynomialRing(kpn);
        ords := [Order(A.i) : i in [1..4]];
        basis := [incl(ExactQuotient(ords[i],N)*A.i) : i in [1..4]];
        sympbasis := symplecticbasis(basis,N);
        sigmabasis := [];
        for i := 1 to #basis do
            Pi := sympbasis[i];
            sigmai1 := Pred ! [Frobenius(coe) : coe in Coefficients(Pi[1])];
            sigmai2 := Pred ! [Frobenius(coe) : coe in Coefficients(Pi[2])];
            sigmaPi := elt<Jackpn | sigmai1, sigmai2, Pi[3]>;
            Append(~sigmabasis,sigmaPi);
        end for;
        all_pts_k := [];
        coords := [];
        for i1, i2, i3, i4 in [0..N-1] do
            po := i1*sympbasis[1] + i2*sympbasis[2] + i3*sympbasis[3] + i4*sympbasis[4];
            Append(~all_pts_k,po);
            Append(~coords,[i1, i2, i3, i4]);
        end for;
        sigmabasiscoords := [coords[Index(all_pts_k,sigmabasis[i])] : i in [1..#sigmabasis]];
        frobpmat := Matrix(Integers(N),4,4,sigmabasiscoords);
        return frobpmat;
//    end for;
end intrinsic;

intrinsic GSpFrobMatricesModN(C::CrvHyp,N::RngIntElt,B::RngIntElt:B0:=3,CCs:=[],phi:=map<{1}->{1}|x:->1>,ClassSigns:=[],SignPhi:=map<{1}->{1}|x:->1>,Ls:=[],X:=AssociativeArray(),Verbose:=false)->SeqEnum,SeqEnum,BoolElt
{returns matrices in the conjugacy class of the Frobenius matrix for the action on Jac(C)[N], for primes upto Bth prime.
The second return values is a list of labels of the remaining possible images.
If the remaining possible images all have same GassmannDistribution, the third boolean return value says to stop computing more Frobenius matrices. }
    if CCs eq [] then CCs, phi := GSpConjugacyClasses(4,N); end if;
    if ClassSigns eq [] then ClassSigns, SignPhi := GSpConjugacyClassSigns(4,N); end if;
    if #Keys(X) eq 0 then X := GSpLattice(4,N,0:CCs:=CCs,phi:=phi,ClassSigns:=ClassSigns,SignPhi:=SignPhi); end if;
    if Ls eq [] then Ls := Sort(Setseq(Keys(X))); end if;
    possibleimages := [(l eq "1.1.1") select GSp(4,N) else X[l]`subgroup : l in Ls];
    Ls_Gassmanndists := [X[l]`gassmanndist : l in Ls];
//    print [x[2] : x in X["1.1.1"]`gassmanndist], #Ls_Gassmanndists, {#x : x in Ls_Gassmanndists}, [x[2] : x in Ls_Gassmanndists[#Ls_Gassmanndists]];
//    assert &and[&+[x[2] : x in X[l]`gassmanndist] eq GSpSize(4,N)/X[l]`index : l in Ls];
    A := [];
    if Verbose then printf "Number of possible images remaining:\n"; end if;
    for p in PrimesInInterval(NthPrime(B0),NthPrime(B)) do
//        print p;
        try
            frobmat := GSpFrobMatrixModN(C,N,p:CCs:=CCs);
//            print p, frobmat;
        catch e;
//            printf "Error for p=%o", p;
//            print e;
            continue;
        end try;
        Append(~A,frobmat);
        frobind := phi(frobmat);
//        print frobind;
//        printf "Frob matrices computed = %o.\n", #A;
        remaining_inds := [i : i in [1..#Ls] | Ls_Gassmanndists[i][frobind][2] ne 0];
        Ls := Ls[remaining_inds];
        possibleimages := possibleimages[remaining_inds];
        Ls_Gassmanndists := Ls_Gassmanndists[remaining_inds];
        if #Set(Ls_Gassmanndists) eq 1 then return A, Ls, true; end if;
        if Verbose then printf "%o after Frob_%o. ", #Ls, p; end if;
    end for;
    return A, Ls, false;
end intrinsic;

intrinsic GSpFrobSignModN(C::CrvHyp,N::RngIntElt,p::RngIntElt)->Tup
{ returns a list consisiting of a tuple <ap mod N, bp mod N, p mod N> and an integer n, where ap and bp are the linear and quadratic coefficients of the characteristic polynomial of Frobenius matrix at p for the action on Jac(C)[N], and n is the F_p-dimension of Jac(C)[N](F_p). }
    badprimes := &*BadPrimes(C)*2;
    require N*badprimes mod p ne 0 : "Bad prime"; 
    ZN := Integers(N);
    P<t> := PolynomialRing(Rationals());
    Cp := ChangeRing(C,GF(p));
    Jp := Jacobian(Cp);
    ordJp := Order(Jp: UseGenus2 := true);
    if ordJp mod N^2 ne 0 then
        n := Valuation(ordJp,N);
    else
        A := Sylow(Jp,N);
        n := #AbelianInvariants(A);
    end if;
    Lpol := ChangeRing(EulerFactor(Jp),ZN);
    sign := <[Coefficient(Lpol,1), Coefficient(Lpol,2), ZN!p], n>;
    return sign;
end intrinsic;

intrinsic GSpFrobSignsModN(C::CrvHyp,N::RngIntElt,B::RngIntElt:B0:=3,CCs:=[],phi:=map<{1}->{1}|x:->1>,ClassSigns:=[],SignPhi:=map<{1}->{1}|x:->1>,Ls:=[],X:=AssociativeArray(),Verbose:=false)->SeqEnum,SeqEnum,BoolElt
{ returns a list of Frobenius signatures, where a Frobenius signature consists of a tuple <ap mod N, bp mod N, p mod N> and an integer n, where ap and bp are the linear and quadratic coefficients of the characteristic polynomial of Frobenius matrix at p for the action on Jac(C)[N], and n is the F_p-dimension of Jac(C)[N](F_p).
The second return values is a list of labels of the remaining possible images.
If the remaining possible images all have same ClassSignDistribution, the third boolean return value says to stop computing more Frobenius signs. }
    if CCs eq [] then CCs, phi := GSpConjugacyClasses(4,N); end if;
    if ClassSigns eq [] then print "Recomputing"; ClassSigns, SignPhi := GSpConjugacyClassSigns(4,N); end if;
    if #Keys(X) eq 0 then X := GSpLattice(4,N,0:CCs:=CCs,phi:=phi,ClassSigns:=ClassSigns,SignPhi:=SignPhi); end if;
    if Ls eq [] then Ls := Sort(Setseq(Keys(X))); end if;
    possibleimages := [(l eq "1.1.1") select GSp(4,N) else X[l]`subgroup : l in Ls];
    Ls_ClassSignDists := [X[l]`ClassSignDist : l in Ls];
//    print [x[2] : x in X["1.1.1"]`ClassSignDist], #Ls_ClassSignDists, {#x : x in Ls_ClassSignDists}, [x[2] : x in Ls_ClassSignDists[#Ls_ClassSignDists]];
//    assert &and[&+[x[2] : x in X[l]`ClassSignDist] eq GSpSize(4,N)/X[l]`index : l in Ls];
    A := [];
    if Verbose then printf "Number of possible images remaining:\n"; end if;
    for p in PrimesInInterval(NthPrime(B0),NthPrime(B)) do
//        print p;
        try
            frobsign := GSpFrobSignModN(C,N,p);
//            print p, frobsign;
        catch e;
//            printf "Error for p=%o", p;
//            print e;
            continue;
        end try;
        Append(~A,frobsign);
        frobind := SignPhi(frobsign);
//        print frobind;
//        printf "Frob signs computed = %o.\n", #A;
        remaining_inds := [i : i in [1..#Ls] | Ls_ClassSignDists[i][frobind][2] ne 0];
        Ls := Ls[remaining_inds];
        possibleimages := possibleimages[remaining_inds];
        Ls_ClassSignDists := Ls_ClassSignDists[remaining_inds];
        if #Set(Ls_ClassSignDists) eq 1 then return A, Ls, true; end if;
        if Verbose then printf "%o after Frob_%o. ", #Ls, p; end if;
    end for;
    return A, Ls, false;
end intrinsic;

intrinsic GSpModNImageProbablisticFromFrob(C::CrvHyp,N::RngIntElt,eps::FldReElt:B:=20,prec:=10,CCs:=[],phi:=map<{1}->{1}|x:->1>,ClassSigns:=[],SignPhi:=map<{1}->{1}|x:->1>,Ls:=[],X:=AssociativeArray(),Verbose:=false) -> SeqEnum, SeqEnum, BoolElt
{ Given a genus 2 hyperelliptic curve C/Q, an integer N > 1, and a number eps close to 1 (and less than 1), returns the label of a subgroup H of GSp(4,Z/NZ) that is the mod-N image with probability >= eps, followed by a boolean that will be true if H is provably equal to the mod-N image.
If a unique subgroup H is not determined, a list of labels of possible subgroups is returned. }
    require N gt 1: "N must be greater than 1";
    if CCs eq [] then CCs, phi := GSpConjugacyClasses(4,N); end if;
    if ClassSigns eq [] then ClassSigns, SignPhi := GSpConjugacyClassSigns(4,N); end if;
    if #Keys(X) eq 0 then X := GSpLattice(4,N,0:CCs:=CCs,phi:=phi,ClassSigns:=ClassSigns,SignPhi:=SignPhi); end if;
    if Ls eq [] then Ls := Sort(Setseq(Keys(X))); end if;
    if Verbose then printf "Computing Frobenius matrices...\n"; end if;
    A, Ls, stop := GSpFrobMatricesModN(C,N,B:B0:=3,CCs:=CCs,phi:=phi,Ls:=Ls,X:=X,Verbose:=Verbose); assert #Ls gt 0;
    if Verbose then printf "Done. %o possible images: %o.\n", #Ls, Ls; end if;
    if #Ls eq 1 then return Ls, [], true; end if;
    if Verbose then printf "Bayesian probability update\n"; end if;
    possibleimages := [<(l eq "1.1.1") select GSp(4,N) else X[l]`subgroup,1/#Ls> : l in Ls];
    S := GSpBayesianProbabilityUpdateFrobMat(A,possibleimages:N:=N,CCs:=CCs,phi:=phi,prec:=prec);
    Ls := [GSpLookupLabel(X,s[1]) : s in S];
    if stop then return Ls, S, false; end if;
    if S[1,2] ge eps then return Ls[[1]], S[[1]], false; end if;
    Re := RealField();
    B0 := B+1; size := B div 2;
    B := B+size;
    while B le 3*size do
        if Verbose then printf "Computing more Frobenius matrices...\n"; end if;
        A, Ls, stop := GSpFrobMatricesModN(C,N,B:B0:=B0,CCs:=CCs,phi:=phi,Ls:=Ls,X:=X,Verbose:=Verbose);
        if Verbose then printf "Done. %o possible images still remain: %o.\n", #Ls, Ls; end if;
        if #Ls eq 1 then return Ls, [], true; end if;
        if Verbose then printf "Bayesian probability update\n"; end if;
        possibleimages := [s : s in S | GSpLookupLabel(X,s[1]) in Ls];
        S := GSpBayesianProbabilityUpdateFrobMat(A,possibleimages:N:=N,CCs:=CCs,phi:=phi,prec:=prec);
        Ls := [GSpLookupLabel(X,s[1]) : s in S];
        if stop then return Ls, S, false; end if;
        if S[1,2] ge eps then return Ls[[1]], S[[1]], false; end if;
        B0 := B+1;
        B := B+size;
        if Verbose then printf "Based on Frobenius up to the %oth prime, %o possibilities remain for the mod-%o Galois image, with probabilities:\n%o\n", B0-1, #S, N, [Re ! x[2] : x in S]; end if;
    end while;
    inds := [i : i in [1..#S] | S[i][2] ge 1-eps]; assert #inds ge 1;
    return Ls[inds], S[inds], false;
end intrinsic;

intrinsic GSpModNImageProbablisticFromFrobSign(C::CrvHyp,N::RngIntElt,eps::FldReElt:B:=50,prec:=10,CCs:=[],phi:=map<{1}->{1}|x:->1>,ClassSigns:=[],SignPhi:=map<{1}->{1}|x:->1>,Ls:=[],X:=AssociativeArray(),Verbose:=false) -> SeqEnum, SeqEnum, BoolElt
{ Given a genus 2 hyperelliptic curve C/Q, an integer N > 1, and a number eps close to 1 (and less than 1), returns the label of a subgroup H of GSp(4,Z/NZ) that is the mod-N image with probability >= eps, followed by a boolean that will be true if H is provably equal to the mod-N image.
If a unique subgroup H is not determined, a list of labels of possible subgroups is returned. }
    require N gt 1: "N must be greater than 1";
    if CCs eq [] then CCs, phi := GSpConjugacyClasses(4,N); end if;
    if ClassSigns eq [] then ClassSigns, SignPhi := GSpConjugacyClassSigns(4,N); end if;
    if #Keys(X) eq 0 then X := GSpLattice(4,N,0:CCs:=CCs,phi:=phi,ClassSigns:=ClassSigns,SignPhi:=SignPhi); end if;
    if Ls eq [] then Ls := Sort(Setseq(Keys(X))); end if;
    if Verbose then printf "Computing Frobenius signs...\n"; end if;
    A, Ls, stop := GSpFrobSignsModN(C,N,B:B0:=3,CCs:=CCs,phi:=phi,ClassSigns:=ClassSigns,SignPhi:=SignPhi,Ls:=Ls,X:=X,Verbose:=Verbose); assert #Ls gt 0;
    if Verbose then printf "Done. %o possible images: %o.\n", #Ls, Ls; end if;
    if #Ls eq 1 then return Ls, [], true; end if;
    if Verbose then printf "Bayesian probability update\n"; end if;
    possibleimages := [<(l eq "1.1.1") select GSp(4,N) else X[l]`subgroup,1/#Ls> : l in Ls];
    S := GSpBayesianProbabilityUpdateFrobSign(A,possibleimages:N:=N,ClassSigns:=ClassSigns,SignPhi:=SignPhi,prec:=prec);
    Ls := [GSpLookupLabel(X,s[1]) : s in S];
    if stop then return Ls, S, false; end if;
    if S[1,2] ge eps then return Ls[[1]], S[[1]], false; end if;
    Re := RealField();
    B0 := B+1; size := B div 2;
    B := B+size;
    while B le 4*size do
        if Verbose then printf "Computing more Frobenius signs...\n"; end if;
        A, Ls, stop := GSpFrobSignsModN(C,N,B:B0:=B0,CCs:=CCs,phi:=phi,ClassSigns:=ClassSigns,SignPhi:=SignPhi,Ls:=Ls,X:=X,Verbose:=Verbose);
        if Verbose then printf "Done. %o possible images still remain: %o.\n", #Ls, Ls; end if;
        if #Ls eq 1 then return Ls, [], true; end if;
        if Verbose then printf "Bayesian probability update\n"; end if;
        possibleimages := [s : s in S | GSpLookupLabel(X,s[1]) in Ls];
        S := GSpBayesianProbabilityUpdateFrobSign(A,possibleimages:N:=N,ClassSigns:=ClassSigns,SignPhi:=SignPhi,prec:=prec);
        Ls := [GSpLookupLabel(X,s[1]) : s in S];
        if stop then return Ls, S, false; end if;
//        print #S, #Ls, [s[2] : s in S];
        if S[1,2] ge eps then return Ls[[1]], S[[1]], false; end if;
        B0 := B+1;
        B := B+size;
        if Verbose then printf "Based on Frobenius signs up to the %oth prime, %o possibilities remain for the mod-%o Galois image, with probabilities:\n%o\n", B0-1, #S, N, [Re ! x[2] : x in S]; end if;
    end while;
    inds := [i : i in [1..#S] | S[i][2] ge 1-eps]; assert #inds ge 1;
    return Ls[inds], S[inds], false;
end intrinsic;
