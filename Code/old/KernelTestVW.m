load "ingredients.m";

R<x> := PolynomialRing(Rationals());
CC := ComplexFieldExtra(100);

f := x^8 + 2*x^6 - 3*x^4 + 7*x^2 - 1;
g := x*(x^4 + 2*x^3 - 3*x^2 + 7*x - 1);
h := x^4 + 2*x^3 - 3*x^2 + 7*x - 1;

X := HyperellipticCurve(f); Y := HyperellipticCurve(g);
JX := AnalyticJacobian(X : Precision := 200);
JY := AnalyticJacobian(Y : Precision := 200);
P := Transpose(BigPeriodMatrix(JX));
Q := Transpose(BigPeriodMatrix(JY));
P := ChangeRing(P, CC); Q := ChangeRing(Q, CC);

GeoEndoRep := GeometricIsogenyRepresentationPartial(Q, P);
print "Number of elements in isogeny basis:", #GeoEndoRep;
T, R := Explode(GeoEndoRep[1]);
R := Transpose(R); T := Transpose(T);
RCC := ChangeRing(R, CC);
comm := Q*T - RCC*P;

print "Test almost 0:";
print Maximum([ Abs(c) : c in Eltseq(comm) ]);

PY1 := Y ! [0, 0];
APY1 := ToAnalyticJacobian(Y ! [0, 0], JY);
MPY1 := Matrix(CC, [ Eltseq(APY1) ]);
PX := MPY1*T;
print ChangeRing(Solution(SplitMatrix(P), SplitMatrix(PX)), ComplexField(5));

exit;
