// Example for Jacobian equations

load "KummerFunctions.m";

QQ := Rationals();
R<x> := PolynomialRing(QQ);
f := x*(x-1)*(x-2)*(x-3)*(x-4)*(x-5);
X := HyperellipticCurve(f);
CantorEquations(X);
