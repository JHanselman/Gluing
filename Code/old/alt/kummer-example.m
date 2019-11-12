load "KummerFunctions.m";
load "brainstorm-help.m";
load "FunctionFinder.m";
load "bqinvs.m";
SetSeed(1);

//Define the base field and the function field
//FFp := FiniteField(37);
FFp := Rationals();
RL := PolynomialRing(FFp);
L<mu> := FieldOfFractions(RL);

//The hyperelliptic curve
//Roots need to be rational for Kummer to have 16 distinct points?
R<x> := PolynomialRing(FFp);
f := (x + 3)*(x + 1)*x*(x - 1)*(x - 3)*(x - 4);

/* Eq of divisor:
    x^2 + a1 x + a2 = 0
    y = b1 x + b2
*/

K,ysq:=CalculateKummer(f);
KummerEquation:= DefiningEquation(K);
print K;

Sing := SingularSubscheme(K);
nodes := [ P : P in Points(Sing) ];
print nodes;

Q1:= nodes[1];
Q2:= nodes[2];

S:=[];
for i:=1 to 4 do
    Append(~S, Q1[i]);
end for;
for i:=1 to 4 do
    Append(~S, Q2[i]);
end for;

M:=Matrix(L,2,4,S);
Ker:= NullspaceOfTranspose(M);

//We find a family of planes depending on L.1 that go through the pair of singular points.
H:= Basis(Ker)[1] - L.1*Basis(Ker)[2];
print Parent(KummerEquation);
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

H_K := h(KummerEquation);
print H_K;

C := Curve(Scheme(P2, H_K));
C := AffinePatch(C,1);
R2<xC, yC> := CoordinateRing(Ambient(C));

Sing := SingularSubscheme(C);
nodes2 := [ C ! P : P in Points(Sing) ];
    
print "The curve has singular points in:";
print nodes2;

print "The curve (parametrized by mu) is given by:";
print C;

P1 := Curve(ProjectiveSpace(L, 1));
f := map< C -> P1 | [ yC/(xC + 4/9), 1 ] >;

M := FunctionField(C);
xC := M.1; yC := M.2;
f := yC/(xC + 4/9);

phi := ProjectiveMap([f, xC, 1]);
D := Image(phi);
phi := Restriction(phi, ProjectiveClosure(C), D);
assert Degree(phi) eq 1; //otherwise choose different auxiliary function

R<X,Y> := PolynomialRing(L, 2);
G := Evaluate(DefiningPolynomial(D), [X, Y, 1]);
S<x> := PolynomialRing(L);
T<y> := PolynomialRing(S);
h := hom< R -> T | [x, y] >;
H := h(G);

num := Numerator(Discriminant(H));
F := Factorization(num);
q := &*[ fac[1] : fac in F | fac[2] eq 1 ];
j := BinaryQuarticInvariants(q);
print j;

