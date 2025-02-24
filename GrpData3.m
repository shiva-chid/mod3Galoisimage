AttachSpec("spec");
X := GSpLattice(4,3,0);
assert #X eq 330;
G := GSp(4,3);
CCs := ConjugacyClasses(G);
phi := ClassMap(G);

L := [lbl : lbl in Setseq(Keys(X)) | lbl eq "1.1.1" or exists(cc){cc[3] : cc in ConjugacyClasses(H) | cc[1] eq 2 and GSpSimilitudeCharacter(cc[3]) eq -1} where H is X[lbl]`subgroup];
Xsubs := [lbl eq "1.1.1" select GSp(4,3) else X[lbl]`subgroup : lbl in L];
assert #Xsubs eq 280;
dat1 := [GSpCharpolsDistribution(H) : H in Xsubs];
dat2 := [GSpGassmannDistribution(H : CCs := CCs, phi := phi) : H in Xsubs];

// how many subgroups have same distribution of characteristic polynomials?
sdat1 := SequenceToSet(dat1); #sdat1;
// 84
msdat1 := SequenceToMultiset(dat1);
dat1_dups := [<x,n> : x in sdat1 | n gt 1 where n is Multiplicity(msdat1,x)];
{* x[2] : x in dat1_dups *};
// {* 2^^11, 3^^7, 4^^4, 5^^5, 6, 7, 8^^2, 9, 12, 15, 21, 29, 34 *}

// how many subgroups have same distribution of conjugacy classes, i.e., are Gassmann-equivalent?
sdat2 := SequenceToSet(dat2); #sdat2;
// 230
msdat2 := SequenceToMultiset(dat2);
dat2_dups := [<x,n> : x in sdat2 | n gt 1 where n is Multiplicity(msdat2,x)];
Gassmanndups_lbls := [L[[i : i in [1..#dat2] | dat2[i] eq dat]] : dat in Set(dat2) | Multiplicity(dat2,dat) gt 1];
{*#x : x in Gassmanndups_lbls *};
// {* 2^^38, 3^^3, 4^^2 *}
Gassmanndups_lbls;
// These are the Gassmann-equivalent subgroups that need to be distinguished.
/*
[
[ 3.2880.5, 3.2880.9 ],
[ 3.6480.16, 3.6480.3 ],
[ 3.17280.2, 3.17280.7, 3.17280.8 ],
[ 3.8640.2, 3.8640.4 ],
[ 3.5760.4, 3.5760.12 ],
[ 3.17280.4, 3.17280.6, 3.17280.9 ],
[ 3.320.1, 3.320.2, 3.320.5, 3.320.6 ],
[ 3.5760.3, 3.5760.6, 3.5760.11 ],
[ 3.8640.12, 3.8640.13 ],
[ 3.1920.2, 3.1920.6 ],
[ 3.2160.22, 3.2160.24 ],
[ 3.8640.14, 3.8640.15 ],
[ 3.960.1, 3.960.3 ],
[ 3.4320.7, 3.4320.5 ],
[ 3.8640.8, 3.8640.10 ],
[ 3.2880.4, 3.2880.8 ],
[ 3.2160.21, 3.2160.23 ],
[ 3.2880.1, 3.2880.2 ],
[ 3.2160.5, 3.2160.6 ],
[ 3.1920.4, 3.1920.7 ],
[ 3.480.3, 3.480.5 ],
[ 3.5760.9, 3.5760.13 ],
[ 3.640.2, 3.640.3, 3.640.4, 3.640.1 ],
[ 3.720.4, 3.720.5 ],
[ 3.320.3, 3.320.4 ],
[ 3.5760.2, 3.5760.5 ],
[ 3.960.2, 3.960.4 ],
[ 3.2880.6, 3.2880.10 ],
[ 3.80.1, 3.80.2 ],
[ 3.2160.10, 3.2160.9 ],
[ 3.3240.6, 3.3240.7 ],
[ 3.17280.1, 3.17280.5 ],
[ 3.6480.14, 3.6480.15 ],
[ 3.240.1, 3.240.2 ],
[ 3.240.6, 3.240.7 ],
[ 3.6480.13, 3.6480.17 ],
[ 3.8640.16, 3.8640.17 ],
[ 3.5760.1, 3.5760.10 ],
[ 3.8640.9, 3.8640.11 ],
[ 3.12960.5, 3.12960.11 ],
[ 3.2880.13, 3.2880.17 ],
[ 3.2880.3, 3.2880.7 ],
[ 3.1920.1, 3.1920.5 ]
]
*/

////////////////////////////////////////////////////////////////////////////////////////////
// distinguishing using dimension of fixed subspace, i.e., dimension of 3-torsion over Q. //
////////////////////////////////////////////////////////////////////////////////////////////
maxptsoverQ := [[max_pts_over_ext(H,1) where H is X[y]`subgroup : y in x] : x in Gassmanndups_lbls];
maxptsoverQ;
/*
[
[ 1, 0 ],
[ 0, 0 ],
[ 2, 1, 0 ],
[ 0, 0 ],
[ 2, 0 ],
[ 2, 1, 0 ],
[ 1, 0, 0, 0 ],
[ 2, 1, 0 ],
[ 0, 0 ],
[ 2, 0 ],
[ 1, 0 ],
[ 1, 0 ],
[ 1, 0 ],
[ 0, 1 ],
[ 1, 0 ],
[ 1, 0 ],
[ 1, 0 ],
[ 1, 0 ],
[ 1, 0 ],
[ 1, 0 ],
[ 1, 0 ],
[ 1, 0 ],
[ 1, 0, 0, 1 ],
[ 1, 0 ],
[ 0, 0 ],
[ 1, 1 ],
[ 1, 0 ],
[ 1, 0 ],
[ 1, 0 ],
[ 0, 0 ],
[ 0, 0 ],
[ 2, 1 ],
[ 0, 0 ],
[ 1, 0 ],
[ 0, 0 ],
[ 0, 0 ],
[ 1, 0 ],
[ 2, 0 ],
[ 1, 0 ],
[ 0, 0 ],
[ 0, 0 ],
[ 1, 0 ],
[ 1, 0 ]
]
*/

Gassmanndups_lbls1 := [Gassmanndups_lbls[i] : i in [1..#Gassmanndups_lbls] | #maxptsoverQ[i] ne #Set(maxptsoverQ[i])];
{*#x : x in Gassmanndups_lbls1 *};
// {* 2^^12, 4^^2 *}
Gassmanndups_lbls1;
// These are the Gassmann-equivalent groups that are not distinguished by dimension of fixed subspace
/*
[
[ 3.6480.16, 3.6480.3 ],
[ 3.8640.2, 3.8640.4 ],
[ 3.320.1, 3.320.2, 3.320.5, 3.320.6 ],
[ 3.8640.12, 3.8640.13 ],
[ 3.640.2, 3.640.3, 3.640.4, 3.640.1 ],
[ 3.320.3, 3.320.4 ],
[ 3.5760.2, 3.5760.5 ],
[ 3.2160.10, 3.2160.9 ],
[ 3.3240.6, 3.3240.7 ],
[ 3.6480.14, 3.6480.15 ],
[ 3.240.6, 3.240.7 ],
[ 3.6480.13, 3.6480.17 ],
[ 3.12960.5, 3.12960.11 ],
[ 3.2880.13, 3.2880.17 ]
]
*/

/////////////////////////////////////////////////////////////////////////////////////////////
// distinguishing using maximum dimension of subspace fixed by index-n subgroup for n <= 3 //
// or the subspace fixed by intersection with Sp(4,F_3)                                    //
// i.e., using maximum dimension of 3-torsion over a degree-n number field or Q(zeta_3).   //
/////////////////////////////////////////////////////////////////////////////////////////////
SG := Symp(4,3);
maxptsoversmalldegextns := [[<max_pts_over_ext(H,n) : n in [1..3]> cat <max_pts_over_ext(H meet SG,1)> where H is X[y]`subgroup : y in x] : x in Gassmanndups_lbls1];
maxptsoversmalldegextns;
/*
[
[ <0, 0, 0, 0>, <0, 0, 0, 0> ],
[ <0, 2, 0, 0>, <0, 1, 0, 0> ],
[ <1, 1, 1, 1>, <0, 1, 0, 1>, <0, 1, 1, 0>, <0, 1, 0, 0> ],
[ <0, 2, 0, 0>, <0, 1, 0, 0> ],
[ <1, 1, 1, 1>, <0, 1, 0, 1>, <0, 1, 1, 1>, <1, 1, 2, 1> ],
[ <0, 1, 0, 0>, <0, 1, 0, 0> ],
[ <1, 2, 2, 2>, <1, 2, 1, 2> ],
[ <0, 1, 0, 0>, <0, 1, 0, 0> ],
[ <0, 0, 0, 0>, <0, 0, 0, 0> ],
[ <0, 0, 0, 0>, <0, 0, 0, 0> ],
[ <0, 1, 0, 0>, <0, 1, 0, 0> ],
[ <0, 0, 0, 0>, <0, 0, 0, 0> ],
[ <0, 0, 0, 0>, <0, 0, 0, 0> ],
[ <0, 2, 0, 0>, <0, 1, 0, 0> ]
]
*/

Gassmanndups_lbls2 := [Gassmanndups_lbls1[i] : i in [1..#Gassmanndups_lbls1] | #maxptsoversmalldegextns[i] ne #Set(maxptsoversmalldegextns[i])];
{*#x : x in Gassmanndups_lbls2 *};
// {* 2^^8 *}
Gassmanndups_lbls2;
// These are the Gassmann-equivalent groups that are not distinguished by
// dimension of fixed subspace,
// dimension of subspace fixed by intersection with Sp(4,F_3)
// or maximum dimension of subspace fixed by an index-n subgroup
/*
[
[ 3.6480.16, 3.6480.3 ],
[ 3.320.3, 3.320.4 ],
[ 3.2160.10, 3.2160.9 ],
[ 3.3240.6, 3.3240.7 ],
[ 3.6480.14, 3.6480.15 ],
[ 3.240.6, 3.240.7 ],
[ 3.6480.13, 3.6480.17 ],
[ 3.12960.5, 3.12960.11 ]
]
*/

///////////////////////////////////////////////////////////////////////////////////////////////////
// distinguishing using maximum dimension of subspace fixed by index-n subgroup for n = 6, 8, 12 //
// i.e., using maximum dimension of 3-torsion over a degree-n number field.                      //
///////////////////////////////////////////////////////////////////////////////////////////////////

Gassmanndups_nonGLconjugate_lbls := [x : x in Gassmanndups_lbls2 | not IsConjugate(GL(4,Integers(3)),H1,H2) where H1, H2 is Explode([X[y]`subgroup : y in x])];
Gassmanndups_nonGLconjugate_lbls;
/*
[
[ 3.320.3, 3.320.4 ],
[ 3.2160.10, 3.2160.9 ],
[ 3.240.6, 3.240.7 ]
]
*/
largedegrees := [6,8,12];
maxptsoverlargedegextns := [[<max_pts_over_ext(H,n) : n in largedegrees> where H is X[y]`subgroup : y in x] : x in Gassmanndups_nonGLconjugate_lbls];
maxptsoverlargedegextns;
/*
[
[ <2, 0, 2>, <1, 0, 2> ],
[ <1, 2, 2>, <1, 1, 2> ],
[ <0, 1, 0>, <0, 1, 1> ]
]
*/
groupid := [[IdentifyGroup(X[y]`subgroup) : y in x] : x in Gassmanndups_nonGLconjugate_lbls];
groupid;
/*
[
[ <324, 69>, <324, 77> ],
[ <48, 17>, <48, 17> ],
[ <432, 520>, <432, 520> ]
]
*/
negativeone := G!ScalarMatrix(4,-1);
negativeonesub := sub<G|negativeone>;
projgroupid := [[<y,IdentifyGroup(quo<H|negativeonesub>)> : y in x | negativeone in H where H is X[y]`subgroup] : x in Gassmanndups_nonGLconjugate_lbls];
projgroupid;
/*
[
[ <"3.320.3", <162, 11>>, <"3.320.4", <162, 19>> ],
[],
[]
]
*/

/////////////////////////////////////////////////////////////////////////////////////////////////////////
// The remaining group are GL-conjugate. So they cannot be distinguished using these methods any more. //
/////////////////////////////////////////////////////////////////////////////////////////////////////////

Gassmanndups_GLconjugate_lbls := [x : x in Gassmanndups_lbls2 | IsConjugate(GL(4,Integers(3)),H1,H2) where H1, H2 is Explode([X[y]`subgroup : y in x])];
Gassmanndups_GLconjugate_lbls;
/*
[
[ 3.6480.16, 3.6480.3 ],
[ 3.3240.6, 3.3240.7 ],
[ 3.6480.14, 3.6480.15 ],
[ 3.6480.13, 3.6480.17 ],
[ 3.12960.5, 3.12960.11 ]
]
*/

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
/*
<3, {* 0^^4 *}, {* 0 *}>, <3, {* 0^^12 *}, {* *}>
<4, {* 0^^2, 1^^3 *}, {* 1 *}>, <4, {* 0^^4, 1 *}, {* 1 *}>
<4, {* 0^^4, 1 *}, {* 1 *}>, <4, {* 0^^2, 1^^3 *}, {* 1 *}>
*/


// does the outer automorphism of GSp(4,F_3) swap these Gassmann-equivalent GL-conjugate pairs?
// No. It fixes each of them.
A := AutomorphismGroup(G); assert #A eq #G;
assert exists(ou){g : g in Generators(A) | not IsInner(g)};
assert { IsConjugate(G,X[x[1]]`subgroup,ou(X[x[2]]`subgroup)) : x in Gassmanndups_GLconjugate_lbls } eq {false};
assert Gassmanndups_GLconjugate_lbls eq [[GSpLookupLabel(X,ou(X[y]`subgroup)) : y in x] : x in Gassmanndups_GLconjugate_lbls];


/////////////////////////////////////
// Code to generate table in paper //
/////////////////////////////////////

#Gassmanndups_lbls1;
maxptsoverextns := [[<max_pts_over_ext(H meet SG,1)> cat <max_pts_over_ext(H,n) : n in [1,2,3,6,8,12]> where H is X[y]`subgroup : y in x] : x in Gassmanndups_lbls1];
maxptsoverextns;
/*
[
[ <0, 0, 0, 0, 0, 2, 0>, <0, 0, 0, 0, 0, 2, 0> ],
[ <0, 0, 2, 0, 2, 0, 4>, <0, 0, 1, 0, 2, 0, 4> ],
[ <1, 1, 1, 1, 2, 0, 2>, <1, 0, 1, 0, 1, 0, 2>, <0, 0, 1, 1, 2, 0, 2>, <0, 0, 1, 0, 1, 0, 2> ],
[ <0, 0, 2, 0, 2, 0, 4>, <0, 0, 1, 0, 2, 0, 4> ],
[ <1, 1, 1, 1, 2, 0, 0>, <1, 0, 1, 0, 2, 0, 0>, <1, 0, 1, 1, 2, 0, 0>, <1, 1, 1, 2, 2, 0, 0> ],
[ <0, 0, 1, 0, 2, 0, 2>, <0, 0, 1, 0, 1, 0, 2> ],
[ <2, 1, 2, 2, 3, 0, 0>, <2, 1, 2, 1, 3, 0, 0> ],
[ <0, 0, 1, 0, 1, 2, 2>, <0, 0, 1, 0, 1, 1, 2> ],
[ <0, 0, 0, 0, 0, 1, 0>, <0, 0, 0, 0, 0, 1, 0> ],
[ <0, 0, 0, 0, 0, 2, 0>, <0, 0, 0, 0, 0, 2, 0> ],
[ <0, 0, 1, 0, 0, 1, 0>, <0, 0, 1, 0, 0, 1, 1> ],
[ <0, 0, 0, 0, 0, 2, 0>, <0, 0, 0, 0, 0, 2, 0> ],
[ <0, 0, 0, 0, 0, 4, 0>, <0, 0, 0, 0, 0, 4, 0> ],
[ <0, 0, 2, 0, 2, 0, 3>, <0, 0, 1, 0, 2, 0, 3> ]
]
*/
inds := [i : i in [1..#maxptsoverextns] | #Set(maxptsoverextns[i]) eq #maxptsoverextns[i]];
inds;
// [ 2, 3, 4, 5, 6, 7, 8, 11, 14 ]

for i in inds do
    for j in [1..#Gassmanndups_lbls1[i]] do
        lbl := Gassmanndups_lbls1[i][j];
        gens := &cat[Sprint(Eltseq(g)) cat "\\newline" : g in GeneratorsSequence(X[lbl]`subgroup)]; gens := gens[1..#gens-8];
        dims := &cat[IntegerToString(n) cat "&" : n in maxptsoverextns[i][j]]; dims := dims[1..#dims-1];
        printf "%o & %o & %o\\\\\n", lbl, gens, dims;
    end for;
    printf "\\hline\n";
end for;
/*
3.8640.2 & [ 1, 2, 1, 0, 2, 1, 0, 1, 2, 2, 2, 1, 2, 2, 1, 2 ]\newline[ 2, 1, 2, 0, 1, 2, 0, 2, 1, 0, 2, 2, 0, 1, 2, 2 ] & 0&0&2&0&2&0&4\\
3.8640.4 & [ 1, 0, 0, 2, 0, 1, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2 ]\newline[ 0, 1, 2, 0, 1, 0, 0, 2, 2, 2, 1, 2, 2, 2, 2, 1 ] & 0&0&1&0&2&0&4\\
\hline
3.320.1 & [ 1, 2, 2, 2, 1, 0, 1, 0, 2, 0, 1, 2, 2, 1, 2, 1 ]\newline[ 1, 1, 0, 1, 2, 1, 2, 0, 2, 0, 0, 2, 1, 0, 1, 1 ] & 1&1&1&1&2&0&2\\
3.320.2 & [ 2, 1, 1, 2, 0, 1, 0, 2, 2, 1, 0, 1, 0, 1, 0, 0 ]\newline[ 1, 2, 0, 1, 1, 1, 1, 2, 0, 0, 1, 1, 2, 1, 2, 0 ] & 1&0&1&0&1&0&2\\
3.320.5 & [ 2, 2, 1, 1, 2, 0, 2, 2, 0, 2, 1, 0, 1, 2, 1, 0 ]\newline[ 0, 0, 1, 1, 1, 2, 1, 2, 0, 0, 2, 1, 2, 2, 2, 2 ] & 0&0&1&1&2&0&2\\
3.320.6 & [ 2, 1, 1, 2, 2, 2, 2, 2, 1, 0, 2, 0, 1, 0, 1, 0 ]\newline[ 2, 2, 0, 2, 1, 2, 1, 0, 2, 1, 1, 1, 2, 2, 2, 1 ] & 0&0&1&0&1&0&2\\
\hline
3.8640.12 & [ 2, 1, 0, 1, 0, 2, 0, 0, 0, 1, 2, 2, 0, 0, 0, 2 ]\newline[ 1, 0, 0, 1, 0, 2, 0, 0, 0, 2, 1, 0, 0, 0, 0, 2 ] & 0&0&2&0&2&0&4\\
3.8640.13 & [ 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 2, 2, 0, 0, 0, 2 ]\newline[ 2, 0, 2, 2, 0, 2, 0, 2, 0, 0, 1, 0, 0, 0, 0, 1 ] & 0&0&1&0&2&0&4\\
\hline
3.640.2 & [ 2, 2, 1, 0, 0, 2, 0, 1, 2, 2, 0, 1, 0, 2, 0, 0 ]\newline[ 2, 0, 0, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 0, 2, 2 ]\newline[ 1, 0, 0, 2, 2, 1, 2, 1, 1, 2, 2, 2, 1, 0, 1, 0 ] & 1&1&1&1&2&0&0\\
3.640.3 & [ 1, 0, 0, 2, 0, 1, 0, 0, 1, 2, 2, 2, 0, 1, 0, 2 ]\newline[ 2, 0, 1, 1, 1, 2, 1, 0, 2, 1, 0, 0, 2, 0, 2, 2 ] & 1&0&1&0&2&0&0\\
3.640.4 & [ 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1 ]\newline[ 1, 1, 0, 1, 0, 2, 0, 0, 0, 1, 1, 2, 0, 0, 0, 2 ]\newline[ 0, 2, 2, 2, 2, 0, 2, 2, 2, 1, 0, 1, 1, 2, 1, 0 ] & 1&0&1&1&2&0&0\\
3.640.1 & [ 2, 2, 1, 2, 1, 1, 1, 2, 1, 2, 2, 0, 2, 0, 2, 2 ]\newline[ 1, 1, 2, 1, 0, 1, 0, 2, 0, 0, 2, 1, 0, 0, 0, 2 ] & 1&1&1&2&2&0&0\\
\hline
3.320.3 & [ 1, 0, 2, 2, 2, 1, 2, 0, 2, 2, 1, 2, 1, 1, 1, 2 ]\newline[ 2, 0, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 1, 0, 1, 0 ] & 0&0&1&0&2&0&2\\
3.320.4 & [ 0, 2, 1, 2, 0, 0, 0, 1, 2, 1, 1, 1, 0, 2, 0, 1 ]\newline[ 0, 0, 1, 2, 0, 0, 0, 2, 2, 2, 1, 2, 0, 1, 0, 2 ]\newline[ 0, 0, 2, 1, 1, 1, 1, 1, 0, 0, 1, 1, 2, 1, 2, 1 ] & 0&0&1&0&1&0&2\\
\hline
3.5760.2 & [ 2, 1, 1, 2, 2, 1, 2, 0, 0, 1, 1, 0, 1, 1, 1, 2 ]\newline[ 0, 0, 2, 0, 0, 0, 0, 1, 1, 0, 2, 1, 0, 2, 0, 1 ] & 2&1&2&2&3&0&0\\
3.5760.5 & [ 1, 1, 2, 0, 0, 2, 0, 1, 1, 0, 0, 0, 0, 2, 0, 0 ]\newline[ 2, 1, 0, 2, 2, 1, 2, 1, 1, 1, 0, 1, 1, 0, 1, 0 ] & 2&1&2&1&3&0&0\\
\hline
3.2160.10 & [ 2, 2, 1, 0, 1, 1, 1, 1, 0, 2, 1, 0, 2, 1, 2, 1 ]\newline[ 0, 1, 1, 2, 1, 2, 1, 1, 2, 0, 1, 1, 2, 0, 2, 1 ] & 0&0&1&0&1&2&2\\
3.2160.9 & [ 1, 2, 2, 1, 2, 2, 2, 2, 2, 0, 1, 0, 1, 0, 1, 0 ]\newline[ 1, 2, 0, 1, 0, 2, 0, 0, 0, 1, 1, 1, 0, 0, 0, 2 ] & 0&0&1&0&1&1&2\\
\hline
3.240.6 & [ 2, 0, 1, 2, 1, 2, 1, 2, 0, 0, 1, 0, 1, 0, 0, 2 ]\newline[ 2, 0, 0, 0, 2, 1, 1, 0, 0, 0, 2, 0, 0, 0, 1, 1 ] & 0&0&1&0&0&1&0\\
3.240.7 & [ 2, 0, 0, 2, 0, 2, 1, 0, 0, 0, 2, 0, 2, 0, 0, 1 ]\newline[ 0, 0, 1, 2, 2, 2, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0 ] & 0&0&1&0&0&1&1\\
\hline
3.2880.13 & [ 1, 1, 2, 2, 2, 0, 2, 2, 1, 0, 0, 2, 1, 1, 1, 2 ]\newline[ 2, 1, 1, 0, 0, 2, 0, 1, 0, 2, 1, 2, 0, 0, 0, 1 ]\newline[ 2, 2, 0, 2, 2, 1, 2, 0, 0, 1, 2, 1, 1, 0, 1, 1 ] & 0&0&2&0&2&0&3\\
3.2880.17 & [ 2, 1, 0, 2, 0, 1, 0, 0, 0, 1, 2, 2, 0, 0, 0, 1 ]\newline[ 2, 2, 0, 2, 0, 2, 0, 0, 0, 1, 2, 1, 0, 0, 0, 2 ]\newline[ 2, 2, 1, 1, 1, 0, 1, 1, 1, 2, 2, 1, 2, 1, 2, 0 ] & 0&0&1&0&2&0&3\\
\hline
*/