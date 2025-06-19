// This code produces all eligible subgroups of GSp(4,F_3)
// which give rise to a failure of local-global principle
// for (3,3)-isogenies over Q
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

J := StandardAlternatingForm(4,GF(3));
idmat := IdentityMatrix(GF(3),4);
G := CSp(4,3);
goodconjclasses := {};
for n := 1 to #CCs do
    c := CCs[n][4];
    cmat := ChangeRing(c,GF(3));
    H := sub<G|cmat>;
    MH := GModule(H);
    SMH := Submodules(MH);
    dim2SMH := [x : x in SMH | Dimension(x) eq 2];
    for x in dim2SMH do
        allGhoms := GHom(x,MH);
        for hommat in allGhoms do
            if Rank(hommat) ne 2 then continue; end if;
            vs := [Matrix(GF(3),1,4,Eltseq(hommat[i])) : i in [1,2]];
//            print vs[1], vs[2];
            if vs[1]*J*Transpose(vs[2]) eq 0 then
                Include(~goodconjclasses,n);
                break;
            end if;
        end for;
    end for;
end for;
goodconjclasses;
// { 1, 2, 3, 4, 5, 6, 7, 8, 9, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 25, 27, 29, 30, 31, 34, 37, 38 }
Ls_local := [lbl : lbl in Ls | {n : n in [1..#gd] | gd[n][2] ne 0} subset goodconjclasses where gd is X[lbl]`gassmanndist];
Ls_local;
// [ 3.40.2, 3.80.3, 3.80.4, 3.120.2, 3.160.1, 3.240.3, 3.240.4, 3.240.9, 3.240.11, 3.240.12, 3.320.1, 3.320.2, 3.320.3, 3.320.4, 3.320.5, 3.320.6, 3.360.1, 3.480.1, 3.480.2, 3.480.7, 3.480.9, 3.480.12, 3.640.1, 3.640.2, 3.640.3, 3.640.4, 3.720.1, 3.720.2, 3.720.3, 3.720.6, 3.720.7, 3.720.8, 3.960.1, 3.960.2, 3.960.3, 3.960.4, 3.960.5, 3.960.6, 3.960.7, 3.960.8, 3.960.9, 3.1080.1, 3.1080.4, 3.1080.5, 3.1080.7, 3.1080.14, 3.1080.17, 3.1440.1, 3.1440.2, 3.1440.3, 3.1440.4, 3.1440.5, 3.1440.6, 3.1440.7, 3.1440.8, 3.1440.11, 3.1440.12, 3.1440.14, 3.1440.15, 3.1920.1, 3.1920.2, 3.1920.3, 3.1920.4, 3.1920.5, 3.1920.6, 3.1920.7, 3.2160.1, 3.2160.2, 3.2160.3, 3.2160.4, 3.2160.7, 3.2160.13, 3.2160.14, 3.2160.17, 3.2160.18, 3.2160.19, 3.2160.25, 3.2880.1, 3.2880.2, 3.2880.3, 3.2880.4, 3.2880.5, 3.2880.6, 3.2880.7, 3.2880.8, 3.2880.9, 3.2880.10, 3.2880.11, 3.2880.12, 3.2880.13, 3.2880.14, 3.2880.15, 3.2880.16, 3.2880.17, 3.2880.18, 3.3240.1, 3.3240.3, 3.3240.9, 3.3240.11, 3.3240.14, 3.4320.2, 3.4320.3, 3.4320.4, 3.4320.11, 3.4320.12, 3.4320.13, 3.4320.14, 3.4320.15, 3.4320.16, 3.4320.17, 3.4320.18, 3.4320.20, 3.5760.1, 3.5760.2, 3.5760.3, 3.5760.4, 3.5760.5, 3.5760.6, 3.5760.7, 3.5760.8, 3.5760.9, 3.5760.10, 3.5760.11, 3.5760.12, 3.5760.13, 3.6480.1, 3.6480.2, 3.6480.3, 3.6480.6, 3.6480.7, 3.6480.14, 3.6480.15, 3.6480.16, 3.6480.18, 3.6480.21, 3.6480.22, 3.8640.1, 3.8640.2, 3.8640.4, 3.8640.7, 3.8640.8, 3.8640.9, 3.8640.10, 3.8640.11, 3.8640.12, 3.8640.13, 3.8640.14, 3.8640.15, 3.8640.16, 3.8640.17, 3.8640.18, 3.12960.3, 3.12960.5, 3.12960.9, 3.12960.10, 3.12960.11, 3.17280.1, 3.17280.2, 3.17280.3, 3.17280.4, 3.17280.5, 3.17280.6, 3.17280.7, 3.17280.8, 3.17280.9, 3.25920.1, 3.25920.3, 3.51840.1 ]

Ls_local_global := [ ];
for lbl in Ls_local do
    H := ChangeRing(X[lbl]`subgroup,GF(3));
    MH := GModule(H);
    SMH := Submodules(MH);
    dim2SMH := [x : x in SMH | Dimension(x) eq 2];
    for x in dim2SMH do
        allGhoms := GHom(x,MH);
        for hommat in allGhoms do
            if Rank(hommat) ne 2 then continue; end if;
            vs := [Matrix(GF(3),1,4,Eltseq(hommat[i])) : i in [1,2]];
//            print vs[1], vs[2];
            if vs[1]*J*Transpose(vs[2]) eq 0 then
                continue lbl;
            end if;
        end for;
    end for;
    Append(~Ls_local_global,lbl);
end for;
Ls_local_global;
// [ 3.1080.4, 3.1080.5, 3.1080.14, 3.1080.17, 3.2160.17, 3.2160.18, 3.2160.25, 3.3240.3, 3.3240.9, 3.3240.11, 3.3240.14, 3.6480.14, 3.6480.15, 3.6480.16, 3.6480.18, 3.6480.21, 3.6480.22, 3.12960.11 ]

// Verifying that none of these groups have "3.40.2"
// as a parent of a parent of a parent ... That is,
// as a node above them in the subgroup lattice.
// "3.40.2" is the stabilizer of an isotropic plane
for lbl in Ls_local_global do
    pars := [[lbl]];
    while pars[#pars] ne ["1.1.1"] do
        pars_next := Sort(Setseq(Seqset(&cat[X[l]`parents : l in pars[#pars]])));
        Append(~pars,pars_next);
    end while;
    assert not "3.40.2" in &cat(pars);
end for;
