R<x,y> := PolynomialRing(Rationals(), 2);
p := y^2 - (x^3 + 1);
C := Curve(AffineSpace(R), p);
L := FunctionField(C);
x := L.1; y := L.2;
f := -2/x^2*y + 2/x^2;
print Degree(f);

//print sub< L | f >;
//L, iso := AlgorithmicFunctionField(L);
//f := iso(f);
//K := sub< L | f >;
//print K eq L;
//MinimalPolynomial(L.1, K);

phi := ProjectiveMap([f, x, 1]);
D := Image(phi);
phi := Restriction(phi, ProjectiveClosure(C), D);
assert Degree(phi) eq 1; //otherwise choose different auxiliary function

R<F,X> := PolynomialRing(Rationals(), 2);
print Evaluate(DefiningPolynomial(D), [F, X, 1]);
