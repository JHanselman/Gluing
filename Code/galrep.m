load "ingredients.m";

F := Rationals();
S<x, z> := PolynomialRing(F, 2);
R<t> := PolynomialRing(F);
hSR := hom<S -> R | [t,1]>;

K := F;
f := x^2 + x*z - 2*z^2;
g := -2*x^2 + 5*z^2;
h := x*z;

mons := [ x^2, x*z, z^2 ];
A := Matrix(K, [ [  MonomialCoefficient(pol, mon) : mon in mons ] : pol in [f, h, g] ]);
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

print j;
print g2s;

q2 := hSR(q);
Y2 := HyperellipticCurve(q2);
R2 := PolynomialRing(FiniteField(2));
for p in [ n : n in [100..1000] | IsPrime(n) and not ((Integers() ! Discriminant(q2)) mod n eq 0) ] do
    print p;
    Factorization(R2 ! EulerFactor(Jacobian(ChangeRing(Y2, FiniteField(p)))));
end for;

q3 := -61*x^6 + 60*x^5 - 146*x^4 + 26*x^3 - 145*x^2 + 34*x - 69;
q3 := hSR(q3);
Y3 := HyperellipticCurve(q3);
R3 := PolynomialRing(FiniteField(3));
for p in [ n : n in [100..1000] | IsPrime(n) and not ((Integers() ! Discriminant(q3)) mod n eq 0) ] do
    print p;
    Factorization(R3 ! EulerFactor(Jacobian(ChangeRing(Y3, FiniteField(p)))));
end for;
