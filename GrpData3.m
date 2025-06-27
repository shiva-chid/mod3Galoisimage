// Analysing the subgroups of GSp(4,F_3)
// including code to generate tables in the paper.

N := 3;
filename := Sprintf("GrpData%o.log",N);
SetLogFile(filename);
AttachSpec("spec");
CCs, phi := GSpConjugacyClasses(4,N);
ClassSigns, SignPhi := GSpConjugacyClassSigns(4,N);
X := GSpLattice(4,N,0:CCs:=CCs,phi:=phi,ClassSigns:=ClassSigns,SignPhi:=SignPhi);
assert #X eq 330;
G := GSp(4,3);

L := [lbl : lbl in Setseq(Keys(X)) | lbl eq "1.1.1" or exists(cc){cc[3] : cc in ConjugacyClasses(H) | cc[1] eq 2 and GSpSimilitudeCharacter(cc[3]) eq -1} where H is X[lbl]`subgroup];
L := Sort(L,func<x,y|(xs[1] ne ys[1]) select xs[1]-ys[1] else (xs[2] ne ys[2]) select xs[2]-ys[2] else xs[3]-ys[3] where xs is [StringToInteger(a) : a in Split(x,".")] where ys is [StringToInteger(a) : a in Split(y,".")]>);
Xsubs := [lbl eq "1.1.1" select GSp(4,3) else X[lbl]`subgroup : lbl in L];
assert #Xsubs eq 280;

// how many subgroups have same distribution of characteristic polynomials?
dat1 := [[x[2]/totalord : x in ords] where ords,totalord is GSpCharpolsDistribution(H : ClassSigns:=ClassSigns,SignPhi:=SignPhi) : H in Xsubs];
sdat1 := SequenceToSet(dat1); #sdat1;
msdat1 := SequenceToMultiset(dat1);
dat1_dups := [<x,n> : x in sdat1 | n gt 1 where n is Multiplicity(msdat1,x)];
{* x[2] : x in dat1_dups *};

// how many subgroups have same distribution of conjugacy classes, i.e., are Gassmann-equivalent?
dat2 := [GSpGassmannDistribution(H : CCs:=CCs,phi:=phi) : H in Xsubs];
sdat2 := SequenceToSet(dat2); #sdat2;
msdat2 := SequenceToMultiset(dat2);
dat2_dups := [<x,n> : x in sdat2 | n gt 1 where n is Multiplicity(msdat2,x)];
Gassmanndups_lbls := [L[[i : i in [1..#dat2] | dat2[i] eq dat]] : dat in Set(dat2) | Multiplicity(dat2,dat) gt 1];
{*#x : x in Gassmanndups_lbls *};
Gassmanndups_lbls;
// These are the Gassmann-equivalent subgroups that need to be distinguished.

////////////////////////////////////////////////////////////////////////////////////////////
// distinguishing using dimension of fixed subspace, i.e., dimension of 3-torsion over Q. //
////////////////////////////////////////////////////////////////////////////////////////////

maxptsoverQ := [[max_pts_over_ext(H,1) where H is X[y]`subgroup : y in x] : x in Gassmanndups_lbls];
maxptsoverQ;
Gassmanndups_lbls1 := [Gassmanndups_lbls[i] : i in [1..#Gassmanndups_lbls] | #maxptsoverQ[i] ne #Set(maxptsoverQ[i])];
{*#x : x in Gassmanndups_lbls1 *};
Gassmanndups_lbls1;
// These are the Gassmann-equivalent groups that are not distinguished by dimension of fixed subspace

/////////////////////////////////////////////////////////////////////////////////////////////
// distinguishing using maximum dimension of subspace fixed by index-n subgroup for n <= 3 //
// or the subspace fixed by intersection with Sp(4,F_3)                                    //
// i.e., using maximum dimension of 3-torsion over a degree-n number field or Q(zeta_3).   //
/////////////////////////////////////////////////////////////////////////////////////////////

SG := Symp(4,3);
maxptsoversmalldegextns := [[<max_pts_over_ext(H,n) : n in [1..3]> cat <max_pts_over_ext(H meet SG,1)> where H is X[y]`subgroup : y in x] : x in Gassmanndups_lbls1];
maxptsoversmalldegextns;
Gassmanndups_lbls2 := [Gassmanndups_lbls1[i] : i in [1..#Gassmanndups_lbls1] | #maxptsoversmalldegextns[i] ne #Set(maxptsoversmalldegextns[i])];
{*#x : x in Gassmanndups_lbls2 *};
Gassmanndups_lbls2;
// These are the Gassmann-equivalent groups that are not distinguished by
// dimension of fixed subspace,
// dimension of subspace fixed by intersection with Sp(4,F_3)
// or maximum dimension of subspace fixed by an index-n subgroup

///////////////////////////////////////////////////////////////////////////////////////////////////
// distinguishing using maximum dimension of subspace fixed by index-n subgroup for n = 6, 8, 12 //
// i.e., using maximum dimension of 3-torsion over a degree-n number field.                      //
///////////////////////////////////////////////////////////////////////////////////////////////////

Gassmanndups_nonGLconjugate_lbls := [x : x in Gassmanndups_lbls2 | not IsConjugate(GL(4,Integers(3)),H1,H2) where H1, H2 is Explode([X[y]`subgroup : y in x])];
Gassmanndups_nonGLconjugate_lbls;
largedegrees := [6,8,12];
maxptsoverlargedegextns := [[<max_pts_over_ext(H,n) : n in largedegrees> where H is X[y]`subgroup : y in x] : x in Gassmanndups_nonGLconjugate_lbls];
maxptsoverlargedegextns;

groupid := [[IdentifyGroup(X[y]`subgroup) : y in x] : x in Gassmanndups_nonGLconjugate_lbls];
groupid;

negativeone := G!ScalarMatrix(4,-1);
negativeonesub := sub<G|negativeone>;
projgroupid := [[<y,IdentifyGroup(quo<H|negativeonesub>)> : y in x | negativeone in H where H is X[y]`subgroup] : x in Gassmanndups_nonGLconjugate_lbls];
projgroupid;

/////////////////////////////////////////////////////////////////////////////////////////////////////////
// The remaining group are GL-conjugate. So they cannot be distinguished using these methods any more. //
/////////////////////////////////////////////////////////////////////////////////////////////////////////

Gassmanndups_GLconjugate_lbls := [x : x in Gassmanndups_lbls2 | IsConjugate(GL(4,Integers(3)),H1,H2) where H1, H2 is Explode([X[y]`subgroup : y in x])];
Gassmanndups_GLconjugate_lbls;

//////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Data of isotropic and non-isotropic 2-dimensional subspaces fixed by index n-subgroups                   //
// How useful is it for distinguishing?                                                                     //
// Not useful for Gassmann-equivalent GL-conjugate pairs, but can be useful for non-GL-conjugate subgroups. //
//////////////////////////////////////////////////////////////////////////////////////////////////////////////

twodimsubs := [[[<n,twodimfixedspaces(X[y]`subgroup,n),twodimfixedspaces(X[y]`subgroup,n:normal:=true)> : n in Divisors(ExactQuotient(#G,X[y]`index))] : y in x] : x in Gassmanndups_GLconjugate_lbls];
assert { x[1] eq x[2] : x in twodimsubs } eq {true};
// This data can distinguish the three Gassmann-equivalent non-GL-conjugate pairs, where we had to
// go up to 6,8,12 degree extensions, without going up to such large degree extensions.
fixedsubs := [[[<n,fixedspaces(X[y]`subgroup,n),fixedspaces(X[y]`subgroup,n:normal:=true)> : n in Divisors(ExactQuotient(#G,X[y]`index)) | n le 12] : y in x] : x in Gassmanndups_nonGLconjugate_lbls];
assert {* x[1] eq x[2] : x in fixedsubs *} eq {* false^^3 *};
for x in fixedsubs do
    for i := 1 to #x[1] do
        if x[1][i] eq x[2][i] then continue; end if;
        printf "%o, %o\n", x[1][i], x[2][i];
        break;
    end for;
end for;



// does the outer automorphism of GSp(4,F_3) swap these Gassmann-equivalent GL-conjugate pairs?
// No. It fixes each of them.
A := AutomorphismGroup(G); assert #A eq #G;
assert exists(ou){g : g in Generators(A) | not IsInner(g)};
assert { IsConjugate(G,X[x[1]]`subgroup,ou(X[x[2]]`subgroup)) : x in Gassmanndups_GLconjugate_lbls } eq {false};
assert Gassmanndups_GLconjugate_lbls eq [[GSpLookupLabel(X,ou(X[y]`subgroup)) : y in x] : x in Gassmanndups_GLconjugate_lbls];


//////////////////////////////////////
// Code to generate tables in paper //
//////////////////////////////////////

#Gassmanndups_lbls1;
maxptsoverextns := [[<max_pts_over_ext(H meet SG,1)> cat <max_pts_over_ext(H,n) : n in [1,2,3,6,8,12]> where H is X[y]`subgroup : y in x] : x in Gassmanndups_lbls1];
maxptsoverextns;
inds := [i : i in [1..#maxptsoverextns] | #Set(maxptsoverextns[i]) eq #maxptsoverextns[i]];
inds;

s := "\\href{https://www.lmfdb.org/knowledge/show/gsp4.subgroup_data?label=";

for i in inds do
    for j in [1..#Gassmanndups_lbls1[i]] do
        lbl := Gassmanndups_lbls1[i][j];
        lblwithlink := Sprintf("%o%o}{%o}", s, lbl, lbl);
        gens := &cat[Sprint(Eltseq(g)) cat "\\newline" : g in GeneratorsSequence(X[lbl]`subgroup)]; gens := gens[1..#gens-8];
        dims := &cat[IntegerToString(n) cat "&" : n in maxptsoverextns[i][j]]; dims := dims[1..#dims-1];
        printf "%o & %o & %o\\\\\n", lblwithlink, gens, dims;
    end for;
    printf "\\hline\n";
end for;

ordG := #G; ordG;
for i := 1 to #Gassmanndups_GLconjugate_lbls do
    for j := 1 to #Gassmanndups_GLconjugate_lbls[i] do
        lbl := Gassmanndups_GLconjugate_lbls[i][j];
        H := X[lbl]`subgroup;
        ordH := ordG/X[lbl]`index;
        lblwithlink := Sprintf("%o%o}{%o}", s, lbl, lbl);
        gens := &cat[Sprint(Eltseq(g)) cat "\\newline" : g in GeneratorsSequence(H)]; gens := gens[1..#gens-8];
        printf "%o & %o & %o\\\\\n", ordH, lblwithlink, gens;
    end for;
    printf "\\hline\n";
end for;
