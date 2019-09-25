SetMemoryLimit(32*10^9);

load "ingredients.m";

R<a4,a3,a2,a1,a0> := PolynomialRing(QQ, 5);
S<x> := PolynomialRing(R);
f1 := a4*x^4 + a3*x^3 + a2*x^2 + a1*x + a0;
f2 := x*(a4*x^4 + a3*x^3 + a2*x^2 + a1*x + a0);

I1s := BinaryQuarticInvariants(f1);
I2s := IgusaInvariants(f2);
I2s := [ I2s[1], I2s[2], I2s[3], I2s[5] ];

P := ProjectiveSpace(R);
Q := ProjectiveSpace(QQ, [2, 3] cat [2, 4, 6, 10]);
h := map< P -> Q | I1s cat I2s >;
im := Image(h);
print im;

exit;
