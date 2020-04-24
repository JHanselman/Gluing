load "KummerFunctions.m";
load "PolynomialExtra.m";
load "JInvariant.m";

QQ := Rationals();
R<x> := PolynomialRing(QQ);
f := (x - 1)*x*(x + 5)*(x + 6);
g := (x + 3)*(x + 1)*x*(x - 1)*(x - 3)*(x - 4);

RL := PolynomialRing(QQ);
L := FieldOfFractions(RL);

T<x,y> := PolynomialRing(QQ,2);
A2:=AffineSpace(T);

Rf := Parent(f);
Rg := Parent(g);
phif := hom< Rf -> T | [x]>;
phig := hom< Rg -> T | [x]>;
fy := phif(f)-y^2;
gy := phig(g)-y^2;
X1 := Scheme(A2,fy);
X1 := Curve(X1);
X1 := ProjectiveClosure(X1);
X1 := EllipticCurve(X1);
Y2 := Scheme(A2,gy);
Y2 := Curve(Y2);

K,ysq := CalculateKummer(g);
F:= DefiningEquation(K);

S3<x1,x2,x3,x4> := PolynomialRing(L,4);

Sing := SingularSubscheme(K);
nodes := [ P : P in Points(Sing) ];
O:=K![0,0,0,1];
Remove(~nodes, Index(nodes,O)) ;

print nodes;
Q2:= nodes[2];

// Find all planes that go through the two nodes with a given j-invariant.
j, Cmu, ysq := FindJInvariantFunction(K,O,Q2,ysq);
j_old := j;
j := j_old - jInvariant(X1);
joos := [el[1] : el in Roots(Denominator(j),QQ)];
singular_eqns := [];
Cs := [];
C_eqn := DefiningEquation(Cmu);
for el in joos do
  eqn := EvaluateField(C_eqn,[el]);
  Append(~singular_eqns, T!eqn);
  Append(~Cs, Curve(AffineSpace(T), T!eqn));
end for;
