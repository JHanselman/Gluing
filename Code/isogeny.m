FF := FiniteField(2017);

R<x> := PolynomialRing(FF);
S<x1,x2,x3> := PolynomialRing(FF, 3);
P2 := ProjectiveSpace(S);

g := (x - 1)*x*(x + 1)*(x + 2);
E := HyperellipticCurve(g);

f := (x + 3)*(x + 1)*x*(x - 1)*(x - 3)*(x - 4);
Y := HyperellipticCurve(f);

F1 := x1^4 + 1117*x1^3*x2 + 1463*x1^2*x2^2 + 830*x1*x2^3 + 549*x2^4 + 1584*x1^2*x3^2 + 1790*x1*x2*x3^2 + 1062*x2^2*x3^2 + 95*x3^4;
F2 := x1^4 + 1624*x1^3*x2 + 337*x1^2*x2^2 + 1946*x1*x2^3 + 1636*x2^4 + 1059*x1^2*x3^2 + 749*x1*x2*x3^2 + 795*x2^2*x3^2 + 1405*x3^4;
F3 := x1^4 + 756*x1^3*x2 + 978*x1^2*x2^2 + 531*x1*x2^3 + 800*x2^4 + 469*x1^2*x3^2 + 765*x1*x2*x3^2 + 1222*x2^2*x3^2 + 644*x3^4;
F3 := x1^4 + 1366*x1^3*x2 + 948*x1^2*x2^2 + 280*x1*x2^3 + 1427*x2^4 + 397*x1^2*x3^2 + 167*x1*x2*x3^2 + 1464*x2^2*x3^2 + 366*x3^4;

I1, W := DixmierOhnoInvariants(F1);
I2, W := DixmierOhnoInvariants(F2);
I3, W := DixmierOhnoInvariants(F3);
print WPSNormalize(W, I1);
print WPSNormalize(W, I2);

X1 := Curve(P2, F1);
X2 := Curve(P2, F2);
X3 := Curve(P2, F3);
 
p1 := LPolynomial(E);
p2 := LPolynomial(Y);
print p1;
print p2;

p3 := LPolynomial(X3);
print Factorization(p3);

