load "ingredients.m";

R<x> := PolynomialRing(Rationals());
CC := ComplexFieldExtra(100);

f := x^8 + 2*x^6 - 3*x^4 + 7*x^2 - 1;
g := x*(x^4 + 2*x^3 - 3*x^2 + 7*x - 1);
m := 2;
Prec := 200;

X := SE_Curve(f,m:Prec:=Prec);
Y := SE_Curve(g,m:Prec:=Prec);
P := X`BigPeriodMatrix;
Q := Y`BigPeriodMatrix;
P := Transpose(P); Q := Transpose(Q);
P := ChangeRing(P, CC); Q := ChangeRing(Q, CC);

Q1 := [0, 0];
Q2 := [1];
E := SE_Divisor([<Q1,1>,<Q2,-1>],Y);
v := SE_AbelJacobi(E,Y);

GeoEndoRep := GeometricIsogenyRepresentationPartial(Q, P);
print "Number of elements in isogeny basis:", #GeoEndoRep;
T, R := Explode(GeoEndoRep[1]);
R := Transpose(R); T := Transpose(T);
RCC := ChangeRing(R, CC);
comm := Q*T - RCC*P;

print "Test almost 0:";
print Maximum([ Abs(c) : c in Eltseq(comm) ]);

v := Matrix(CC, [ [ c : c in Eltseq(v) ] ]);
print "Torsion point:";
print v;
print "Image:";
print v * RCC;

exit;
