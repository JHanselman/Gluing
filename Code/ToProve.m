load "ingredients.m";

R<x> := PolynomialRing(Rationals());
CC := ComplexFieldExtra(100);

f := x^8 + 2*x^6 - 3*x^4 + 7*x^2 - 1;
g := x*(x^4 + 2*x^3 - 3*x^2 + 7*x - 1);
h := x^4 + 2*x^3 - 3*x^2 + 7*x - 1;

P := Transpose(PeriodMatrix(f : Prec := 100));
Q2 := Transpose(PeriodMatrix(g : Prec := 100));
Q1 := Transpose(PeriodMatrix(h : Prec := 100));
P := ChangeRing(P, CC); Q1 := ChangeRing(Q1, CC); Q2 := ChangeRing(Q2, CC);

print "Check E --> Jac (X) injective:";
GeoEndoRep1 := GeometricIsogenyRepresentationPartial(Q1, P);
T1, R1 := Explode(GeoEndoRep1[1]);
R1 := Transpose(R1); T1 := Transpose(T1);
KCCG := KerModKer0(R1, Q1, P);
print KCCG;

print "Check kernel of Jac (X) --> E connected:";
GeoEndoRep1 := GeometricIsogenyRepresentationPartial(P, Q1);
T1, R1 := Explode(GeoEndoRep1[1]);
R1 := Transpose(R1); T1 := Transpose(T1);
KCCG := KerModKer0(R1, P, Q1);
print KCCG;

print "Check 2-isogeny Jac (Y) --> Prym:";
K := Ker0(R1, P, Q1);
GeoEndoRep := GeometricIsogenyRepresentationPartial(Q2, K);
T, R := Explode(GeoEndoRep[1]);
R := Transpose(R); T := Transpose(T);
KCCG := KerModKer0(R, Q2, K);
print KCCG;

exit;
