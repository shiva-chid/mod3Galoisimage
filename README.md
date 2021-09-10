# threetorsimage
Computes the image of the Galois representation on the three torsion points of the Jacobian of a given genus 2 curve

Given a genus 2 curve C, the function threetorsimage(C) returns the image of the Galois representation on Jac(C)[3], 
as a subgroup H of GSp(4,F_3) upto conjugacy. It also returns a label for the subgroup H which can be used to access 
information about H by calling X[label]. X is an associative array listing all subgroups of GSp(4,F_3) upto conjugacy
using unique labels. This labelling is constructed in GSp.m which was written by Drew Sutherland.

For an example implementation, see the file example.m
