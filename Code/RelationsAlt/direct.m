SetMemoryLimit(32*10^9);
load "ingredients.m";

F := FiniteField(43);
R<f0,g2,g1,g0> := PolynomialRing(F, 4);
K := FieldOfFractions(R);
S<x, z> := PolynomialRing(K, 2);

f := x^2 + x*z + f0*z^2;
h := x*z;
g := g2*x^2 + g1*x*z + g0*z^2;

mons := [ x^2, x*z, z^2 ];
A := Matrix(K, [ [  MonomialCoefficient(pol, mon) : mon in mons ] : pol in [f, h, g] ]);
//A := Matrix(K, [ [  MonomialCoefficient(pol, mon) : mon in mons ] : pol in [f, g, h] ]);
B := A^(-1);

a1 := B[1,1]; b1 := B[1,2]; c1 := B[1,3];
a2 := B[2,1]; b2 := B[2,2]; c2 := B[2,3];
a3 := B[3,1]; b3 := B[3,2]; c3 := B[3,3];

a := a1 + 2*a2*x + a3*x^2;
b := b1 + 2*b2*x + b3*x^2;
c := c1 + 2*c2*x + c3*x^2;

p := h^2 - 4*f*g;
q := b*(b^2 - a*c);

j := jInv(p);
g2s := G2Invs(q);

D := F;
j0 := Random(D);
g2s0 := [ Random(D) : i in [1..3] ];

eqj := R ! (Numerator(j) - j0*Denominator(j));
eqsg2 := [ R ! (Numerator(g2s[i]) - g2s0[i]*Denominator(g2s[i])) : i in [1..3] ];
eqs := [ eqj ] cat eqsg2;

A := AffineSpace(R);
Sch := Scheme(A, eqs);
print Dimension(Sch);
print Degree(Sch);
print Points(Sch);

exit;
