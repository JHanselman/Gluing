//load "ingredients.m";
load "fastthetasgenus3.m";

R<t> := PolynomialRing(Rationals());
g := t*(t^4 + 2*t^3 - 3*t^2 + 7*t - 1);
h := t^4 + 2*t^3 - 3*t^2 + 7*t - 1;
f := Evaluate(h, t^2);

Q1 := Transpose(PeriodMatrix(g : Prec := 100));
Q2 := Transpose(PeriodMatrix(h : Prec := 100));
Q := DiagonalJoin(Q1, Q2);

rowsQ := Rows(Q);
indices := [1,2,5,3,4,6];
Q := Matrix(BaseRing(Q), [ Eltseq(rowsQ[i]) : i in indices ]);
//Q := Transpose(PeriodMatrix(f : Prec := 100));
Q := Transpose(Q);
print ChangeRing(Q, ComplexField(5));

Q1 := Submatrix(Q, 1,1, 3,3);
Q2 := Submatrix(Q, 1,4, 3,3);
tau := Q1^(-1)*Q2;
print ChangeRing(tau, ComplexField(5));

/* Check niet-niet-hyperelliptisch door na te gaan dat meer dan 28 waarden niet 0 zijn: */
fundamentalThetas := CalculThetas(tau/2);
thetas := AllDuplication(fundamentalThetas);
print Minimum([ Abs(theta) : theta in thetas ]);
print [ ComplexField(5) ! theta : theta in thetas ];
print #[ theta : theta in thetas | Abs(theta) lt 10^(-10) ];

Q2 := Transpose(PeriodMatrix(g : Prec := 100));
Q1 := Transpose(PeriodMatrix(h : Prec := 100));
Q := DiagonalJoin(Q1, Q2);
print ChangeRing(Q, ComplexField(5));

alpha := Matrix(Rationals(), [
[0,1,0],
[0,1,0],
[1,0,1]
]);
I3 := IdentityMatrix(Rationals(), 3);
H1 := HorizontalJoin(I3, 0*I3);
H2 := HorizontalJoin((1/2)*alpha, (1/2)*I3);
R2 := VerticalJoin(H1, H2);

E1 := StandardSymplecticMatrix(1);
E2 := StandardSymplecticMatrix(2);
E3 := DiagonalJoin(E1, E2);
print "E3:", E3;

for R in [ R2, R2^(-1), Transpose(R2), Transpose(R2^(-1)) ] do
    print "R:", R;
    E := R*(2*E3)*Transpose(R);
    print "E:", E;
end for;

exit;

RCC := ChangeRing(R, BaseRing(Parent(Q)));
P := RCC*Q;
P := Transpose(P);
P1 := Submatrix(P, 1,1, 3,3);
P2 := Submatrix(P, 1,4, 3,3);
tau := P1^(-1)*P2;
print ChangeRing(tau, ComplexField(5));

/* Check niet-niet-hyperelliptisch door na te gaan dat meer dan 28 waarden niet 0 zijn: */
fundamentalThetas := CalculThetas(tau/2);
thetas := AllDuplication(fundamentalThetas);
print Minimum([ Abs(theta) : theta in thetas ]);
print [ ComplexField(5) ! theta : theta in thetas ];
print #[ theta : theta in thetas | Abs(theta) lt 10^(-10) ];

exit;
