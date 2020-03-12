load "GeometricGluing.m";

//Define Rings
QQ := Rationals();
R<x> := PolynomialRing(QQ);
// Define the curves we want to glue
// The elliptic curve
f := (x - 1)*x*(x + 1)*(x + 2);
//g := x^4 + x^3 + x^2 + x + 1;
// The hyperelliptic curve
g := (x + 3)*(x + 1)*x*(x - 1)*(x - 3)*(x - 4);
//g := (x-5)*(x+2)*(x-31)*(x+15)*x*(x+1);
//g := (x-5)*(x+2)*(x-31)*(x+15)*x*(x-4); // sent this one to J. Sizzle
//g := (x^4 + x^3 + x^2 + x + 1)*(x+2)*(x+3);

GeometricGluing(f,g);
