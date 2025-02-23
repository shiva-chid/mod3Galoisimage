# mod-3 Galois image of abelian surfaces
Computes the image of the Galois representation on the three torsion points of the Jacobian of a given genus 2 curve

Given a genus 2 curve C, the function mod3Galoisimage(C) returns the image of the Galois representation on Jac(C)[3],
as a subgroup H of GSp(4,F_3) upto conjugacy. It also returns a label for the subgroup H which can be used to access
information about H by calling X[label]. X is an associative array listing all subgroups of GSp(4,F_3) with surjective
similitude character, upto conjugacy using unique labels. The label of a subgroup is a string "N.i.a" where N is the
level (which will be 3 for all proper subgroups of GSp(4,3)), and i is the index in GSp(4,3). The last entry a is a
positive integer which distinguishes the conjugacy classes of subgroups of the same level and index. It is computed
deterministically using the subgroup lattice structure, orbit signature for the natural action on F_3^4, conjugacy class
signature and if necessary, by lexicographical ordering of canonicalized generators. This labelling is due to Drew Sutherland.
The label of a subgroup H can be obtained by calling GSpLookupLabel(X,H);

For an example implementation, see the file example.m
