load "KummerFunctions.m";
load "PolynomialExtra.m";
load "JInvariant.m";

QQ := Rationals();
R<x> := PolynomialRing(QQ);
f := (x - 1)*x*(x + 5)*(x + 6);
g := (x + 3)*(x + 1)*x*(x - 1)*(x - 3)*(x - 4);

RL := PolynomialRing(QQ);
L := FieldOfFractions(RL);
mu := L.1;

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

// make last nodal curve corresponding to mu = oo
S:=[];
for i:=1 to 4 do
  Append(~S, O[i]);
end for;
for i:=1 to 4 do
  Append(~S, Q2[i]);
end for;
M:=Matrix(L,2,4,S);
Ker:= NullspaceOfTranspose(M);
H1, H2 := Explode(Basis(Ker));
H := H2;
KummerEquation:= DefiningEquation(K);

S3<x1,x2,x3,x4>:= Parent(KummerEquation);
S2<x1,x2,x3> := PolynomialRing(L,3);

P2 := ProjectiveSpace(S2);
if H[1] ne 0 then
    h := hom<S3 -> S2 | [ 1/H[1]*(-H[2]*x1-H[3]*x2-H[4]*x3), x1, x2, x3 ]>;
elif H[2] ne 0 then
    h := hom<S3 -> S2 | [ x1,1/H[2]*(-H[1]*x1-H[3]*x2-H[4]*x3), x2, x3 ]>;
elif H[3] ne 0 then
    h := hom<S3 -> S2 | [x1,x2, 1/H[3]*(-H[1]*x1-H[2]*x2-H[4]*x3), x3 ]>;
end if;

// intersect Kummer with the plane
H_K := h(KummerEquation);
Coo := Curve(Scheme(P2, H_K));
Coo := AffinePatch(Coo,1);
Coo_eqn := T!DefiningEquation(Coo);
Coo := Curve(A2, Coo_eqn);
Append(~singular_eqns, Coo_eqn);
Append(~Cs, Coo);

// looking at elliptic fibration using Legendre form
pts := ComputeBranchPoints(Cmu);
lambda := CrossRatio(pts[1],pts[2],pts[3],pts[4]);
Rmu<X> := PolynomialRing(L);
Emu := EllipticCurve(X*(X-1)*(X-lambda));
fmu := DefiningEquation(Emu);
Fmu := (mu - 1/4)*fmu;
Es_eqns := [];
for el in joos do
  eqn := EvaluateField(Fmu, [el]);
  Append(~Es_eqns, eqn);
end for;
U<X,Y,Z> := Parent(Es_eqns[1]);
Umu<XX,YY,ZZ> := Parent(Fmu);
cs, mons := CoefficientsAndMonomials(Fmu);
SL<a,b> := PolynomialRing(QQ,2);
homog := hom< RL -> SL | a >;
cs_homog := [Homogenization(homog(RL!el), b, 2) : el in cs];
csoo := [Evaluate(el,[1,0]) : el in cs_homog];
Foo := &+[csoo[i]*mons[i] : i in [1..#mons]];
Append(~Es_eqns, U!Foo);
BadPlaces(Emu);
KodairaSymbols(Emu);


// copy pasta
/*
Rmu<X> := PolynomialRing(L);
EllipticCurve(X*(X-1)*(X-lambda));
Emu := $1;
Emu_eqn := DefiningEquation(Emu);
Es := [];
Es_eqns := [];
joos;
for el in joos do
eqn := EvaluateField(Emu_eqn, el);
Append(~Es_eqns, eqn);
Append(~Es, Curve(AffineSpace(L,2),eqn));
end for;
Emu_eqn;
Es_eqns;
Es;
for el in joos do
eqn := EvaluateField(Emu_eqn, [el]);
Append(~Es_eqns, eqn);
Append(~Es, Curve(AffineSpace(L,2),eqn));
end for;
for el in joos do
Es_eqns;
Es_eqns := [];
for el in joos do
eqn := EvaluateField(Emu_eqn, [el]);
Append(~Es_eqns, eqn);
end for;
Emu_eqn;
joos;
fmu := Emu_eqn;
Fmu := (mu - 1/4)*fmu;
L.1;
mu := L.1;
Fmu := (mu - 1/4)*fmu;
Fmu;
for el in joos do
eqn := EvaluateField(Fmu, [el]);
Append(~Es_eqns, eqn);
end for;
Es_eqns;
Parent(Es_eqns[1]);
U<X,Y,Z> := $1;
Es_eqns;
Es := [Curve(ProjectiveSpace(U), el) : el in Es_eqns];
Es;
[Genus(el) : el in Es];
Es_eqns;
Es_eqns[5];
Factorization($1);
*/
