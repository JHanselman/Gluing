load "ingredients.m";
load "fastthetasgenus3.m";

R<t> := PolynomialRing(Rationals());
S<x,y,z> := PolynomialRing(Rationals(), 3);
hSR := hom<S -> R | [t, 1, 1]>;
CC := ComplexFieldExtra(100);

f := x^2 + x*z - 3*z^2;
g := 2*x^2 - x*z + 5*z^2;
h := x^2 - x*z + 2*z^2;
F := y^4 - h*y^2 + f*g;

mons := [ x^2, x*z, z^2 ];
fs := [ MonomialCoefficient(f, mon) : mon in mons ];
gs := [ MonomialCoefficient(g, mon) : mon in mons ];
hs := [ MonomialCoefficient(h, mon) : mon in mons ];
A := Matrix([ fs, hs, gs ]);
B := Transpose(A^(-1));

a := B[1,1] + 2*B[1,2]*t + B[1,3]*t^2;
b := B[2,1] + 2*B[2,2]*t + B[2,3]*t^2;
c := B[3,1] + 2*B[3,2]*t + B[3,3]*t^2;

p := b*(b^2 - a*c);
q := hSR(h^2 - 4*f*g);

T<x,y> := PolynomialRing(Rationals(), 2);
hST := hom<S -> T | [x, y, 1]>;
F := hST(F);
g := t*(t^4 + 2*t^3 - 3*t^2 + 7*t - 1);
h := t^4 + 2*t^3 - 3*t^2 + 7*t - 1;

P := Transpose(PeriodMatrix(F : Prec := 100));
Q1 := Transpose(PeriodMatrix(g : Prec := 100));
Q2 := Transpose(PeriodMatrix(h : Prec := 100));
Q := DiagonalJoin(Q1, Q2);
P := ChangeRing(P, CC); Q1 := ChangeRing(Q1, CC); Q2 := ChangeRing(Q2, CC);

rowsQ := Rows(Q);
indices := [1,2,5,3,4,6];
Q := Matrix(BaseRing(Q), [ Eltseq(rowsQ[i]) : i in indices ]);
Q := Transpose(Q);
Q1 := Submatrix(Q, 1,1, 3,3);
Q2 := Submatrix(Q, 1,4, 3,3);
tau := Q1^(-1)*Q2;
print ChangeRing(tau, ComplexField(5));

fundamentalThetas := CalculThetas(tau/2);
thetas := AllDuplication(fundamentalThetas);
print Minimum([ Abs(theta) : theta in thetas ]);
print [ ComplexField(5) ! theta : theta in thetas ];
print #[ theta : theta in thetas | Abs(theta) lt 10^(-10) ];

P := Transpose(P);
P1 := Submatrix(P, 1,1, 3,3);
P2 := Submatrix(P, 1,4, 3,3);
tau := P1^(-1)*P2;
print ChangeRing(tau, ComplexField(5));

fundamentalThetas := CalculThetas(tau/2);
thetas := AllDuplication(fundamentalThetas);
print Minimum([ Abs(theta) : theta in thetas ]);
print [ ComplexField(5) ! theta : theta in thetas ];
print #[ theta : theta in thetas | Abs(theta) lt 10^(-10) ];
print #thetas;

exit;
