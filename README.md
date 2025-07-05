# mod-3 Galois image of abelian surfaces
This directory has code associated with the paper [Computing the mod-3 Galois image of a principally polarized abelian surface over the rationals](https://arxiv.org/abs/2502.02044)

The main function is called `mod3Galoisimage`. It takes a genus 2 curve over Q as input and returns the image of the mod-3 Galois representation, coming from the Galois action on the 3-torsion points Jac(C)[3] of the Jacobian, as a subgroup H of GSp(4,Z/3) upto conjugacy.

If calling this function for multiple curves, it is better to pre-compute data about the subgroup lattice of GSp(4,Z/3). This is done using the intrinsics `GSpConjugacyClasses`, `GSpConjugacyClassSigns` and `GSpLattice`. This data is passed as input to the main function through optional parameters. See the file `examples.m` for how to.

## Labelling convention
Up to conjugacy, the subgroups H of GSp(4,Z/3) with surjective similitude character, are identified using unique labels. The label of a subgroup is a string "N.i.a" where N is the level (which will be 3 for all proper subgroups of GSp(4,Z/3)), and i is the index in GSp(4,Z/3). The last entry a is a positive integer which distinguishes the conjugacy classes of subgroups of the same level and index. It is computed deterministically using the subgroup lattice structure, orbit signature for the natural action on F_3^4, conjugacy class signature and if necessary, by lexicographical ordering of canonicalized generators. This labelling is due to Drew Sutherland. The command `X := GSpLattice(4,3,0)` creates an associative array X listing all such subgroups. The keys of X are the labels, and `X[label]` gives access to the stored information about the corresponding subgroup. The label of a subgroup H can be obtained by calling `GSpLookupLabel(X,H)`.

## Realization problem
The file `example_RealizeImage.m` contains a worked-out example illustrating how to produce a genus 2 curve C realizing a given small subgroup H of GSp(4,Z/3) as its mod-3 Galois image. The first step is to construct an appropriate Galois representation with image equal to H. Then we use the intrinsics `BurkhardtModel` and `Genus2CurveFromBurkhardtTwistPoint` to construct a genus 2 curve C with this mod-3 Galois representation.

### List of all main intrinsics:
Given a genus 2 hyperelliptic curve C/Q
- `mod3Galoisimage(C)` returns the mod-3 Galois image as a matrix subgroup of GSp(4,Z/3) and its label.
Optional parameters:
  * `errorbound` is a positive real number close to 0. It sets the probability bound used in the Monte-Carlo method coming from Chebotarev density theorem. Distributions which are unlikely (probability < errorbound) to yield the sampled Frobenius distribution are discarded. Default value is 0.0001.
  * `primesbounds` is a sequence of two positive integers B1, B2. Frobenius signature is computed for the first B1 primes of good reduction. The conjugacy class of Frobenius is computed for the first B2 primes of good reduction. Default values are B1 = 100, B2 = 20.
  * `order` is the order of the mod-3 image. It is also the degree of the 3-torsion field.
  * `AbstractGalGrp` is a group abstractly isomorphic to the mod-3 image. Such a group can be computed from a 3-torsion polynomial.
  * `CCs, phi, ClassSigns, SignPhi, Ls, X` are the precomputed data of conjugacy classes, conjugacy class signatures, labels of eligible subgroups and the subgroup lattice. See `examples.m`.
  * `Verbose`.
- `constructmod3image(C, Ls, X)` distinguishes among the Gassmann-equivalent GL-conjugate subgroups with labels Ls, by globally fixing a basis of Jac(C)[3] over the 3-torsion field, and computing enough Frobenius matrices (all with respect to the globally fixed basis). X is the associative array containing all subgroups of GSp(4,Z/3) as computed by `GSpSubgroupLattice`. Output is the label and the group corresponding to the correct mod-3 Galois image.
Optional parameter: `Verbose`.

#### The Monte-Carlo methods using Chebotarev density
- `GSpModNImageProbablisticFromFrobSign(C,N,eps)` - returns the label of H and the subgroup H of GSp(4,Z/N) that is the mod-N image with probability >= 1-eps, followed by a boolean that will be true if H is provably equal to the mod-N image. If a unique subgroup H is not determined, a list of labels of possible subgroups is returned. This works by computing Frobenius signatures for the mod-N representation of Jac(C).
Optional parameters:
  * `B` specifies the number of primes to consider.
  * `prec` specifies the precision used for the probability calculations.
  * `CCs, phi, ClassSigns, SignPhi, Ls, X` are the precomputed data of conjugacy classes, conjugacy class signatures, labels of eligible subgroups and the subgroup lattice.
  * `Verbose`.
- `GSpModNImageProbablisticFromFrob(C,N,eps)` returns two lists giving the labels of H and the subgroups H in a Gassmann-equivalence class of subgroups of GSp(4,Z/NZ), and a third boolean. This class contains the mod-N image H with probability >= 1-eps. The third boolean is true if H is provably equal to the mod-N image. This works by computing Frobenius conjugacy classes for the mod-N representation of Jac(C).
Optional parameters:
  * `B` specifies the number of primes to consider.
  * `prec` specifies the precision used for the probability calculations.
  * `CCs, phi, ClassSigns, SignPhi, Ls, X` are the precomputed data of conjugacy classes, conjugacy class signatures, labels of eligible subgroups and the subgroup lattice.
  * `Verbose`.

#### Local information about C at a given prime
- `GSpFrobSignModN(C,N,p)` returns a list consisting of a tuple <ap mod N, bp mod N, p mod N> and an integer n, where ap and bp are the linear and quadratic coefficients of the characteristic polynomial of Frobenius matrix at p for the action on Jac(C)[N], and n is the F_p-dimension of Jac(C)(F_p)[N].
- `GSpFrobMatrixModN(C,N,p)` returns a matrix in the GSp(4,Z/3)-conjugacy class of the Frobenius matrix at p for the action on Jac(C)[N].
Optional parameter:
  * `CCs` is the list of all conjugacy classes.

#### Precomputing data about the subgroup lattice
- `GSpLattice(d, N, IndexLimit)` computes the lattice of subgroups of GSp(d,Z/N) with surjective similitude character and index bounded by IndexLimit. Returns an associative array containing records with attributes label, level, index, orbits, children, parents, subgroup where children and parents are lists of labels that identify maximal subgroups and minimal supergroups.
Optional parameters:
  * `IndexDivides` if set to true, only computes the lattice of subgroups whose index exactly divides IndexLimit.
  * `excludepgroups` if set to a prime p, only computes the lattice of subgroups that are not p-groups.
  * `CCs, phi, ClassSigns, SignPhi` are the precomputed data of conjugacy classes and conjugacy class signatures.
  * `Verbose`.
- `GSpConjugacyClasses(d, N)` returns an ordered sequence of tuples <order,length,similitude,representative> giving the conjugacy classes of GSp(d,Z/N), and the classmap.
- `GSpConjugacyClassSigns(d, N)` returns an ordered sequence of tuples <signature,size> where signature is <[ap,bp,p] mod N,n> where ap, bp are the cubic and quadratic coefficients of the characteristic polynomials of elements of GSp(4,N) and n is the dimension of fixed space, and an index map of these signatures.
Optional parameters:
  * `CCs, phi` is the data of conjugacy classes and class map.

#### Other notable intrinsics:
- `dim_rationalthreetors(C)` computes dimension of Jac(C)(Q)[3] over Z/3
- `dim_cyclotomicthreetors(C)` computes dimension of Jac(C)(Q_zeta3)[3] over Z/3
- `dim_threetors_overnfield(C, n, m)` computes the maximum over degree n number fields K of dimension of Jac(C)(K)[3] over Z/3. The third argument m is the expected degree of the 3-torsion field.
Optional parameters:
  * `notnormal` if set to true, will only consider non-normal degree n number fields.
  * `minusoneinGal` if set to false, specifies that -I is not in the mod-3 Galois image, i.e., that the projective mod-3 Galois representation is the same as the mod-3 Galois representation.
- `separablethreetorspoly(C)` returns a separable 3-torsion polynomial of Jac(C). Its splitting field is the 3-torsion field. Its Galois group is abstractly isomorphic to the mod-3 Galois image.
- `degofthreetorsfield(C)` returns the degree of the 3-torsion field of Jac(C). Optional parameter: `minusoneinGal`.
- `threetorsfield(C, m)` computes the 3-torsion field of Jac(C), given that it has degree m.
- `projmod3Galoisimage(C, m)` returns the Magma SmallGroupDatabase id of the projective mod-3 Galois image, given that it has order m.
- `max_pts_over_ext(H, n)` computes the maximum F_p-dimension of the subspace of F_p^r fixed by an index n subgroup of H, where H is a given subgroup of GL(r,F_p). If H is the mod-p Galois image, then this is exactly the maximum F_p-dimension of Jac(C)(K)[p] over degree n number fields K.
Optional parameter:
  * `normal` if set to true, only considers normal subgroups of H.
