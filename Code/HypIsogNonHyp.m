//load "ingredients.m";
load "fastthetasgenus3.m";
load "riemann.m";
load "rationality.m";

R<t> := PolynomialRing(Rationals());
h := t^4 + 2*t^3 - 3*t^2 + 7*t - 1;
h := (t - 1)*(t - 2)*(t + 4)*(t - 5);
g := t*h;
f := Evaluate(h, t^2);

Q1 := Transpose(PeriodMatrix(g : Prec := 400));
Q2 := Transpose(PeriodMatrix(h : Prec := 400));
Q := DiagonalJoin(Q1, Q2);

rowsQ := Rows(Q);
indices := [1,2,5,3,4,6];
Q := Matrix(BaseRing(Q), [ Eltseq(rowsQ[i]) : i in indices ]);
//Q := Transpose(PeriodMatrix(f : Prec := 400));
Q := Transpose(Q);
print "Period matrix of product:", ChangeRing(Q, ComplexField(5));

Q1 := Submatrix(Q, 1,1, 3,3);
Q2 := Submatrix(Q, 1,4, 3,3);
tau := Q1^(-1)*Q2;
print "Small period matrix of product:", ChangeRing(tau, ComplexField(5));

/* Check niet-niet-hyperelliptisch door na te gaan dat meer dan 28 waarden niet 0 zijn: */
fundamentalThetas := CalculThetas(tau/2);
thetas := AllDuplication(fundamentalThetas);
print "Number of non-zero thetas:", #[ theta : theta in thetas | Abs(theta) lt 10^(-10) ];

/* Opnieuw :-P */
Q2 := Transpose(PeriodMatrix(g : Prec := 400));
Q1 := Transpose(PeriodMatrix(h : Prec := 400));
Q := DiagonalJoin(Q2, Q1);
rowsQ := Rows(Q);
indices := [1,2,5,3,4,6];
Q := Matrix(BaseRing(Q), [ Eltseq(rowsQ[i]) : i in indices ]);
print "Period matrix of product:", ChangeRing(Q, ComplexField(5));

I3 := IdentityMatrix(Rationals(), 3);
H1 := HorizontalJoin((1/2)*I3, 0*I3);
H2 := HorizontalJoin(0*I3, I3);
R2 := VerticalJoin(H1, H2);
print "Quotient matrix with respect to symplectic basis (transformed to by indices):", R2;

E3 := StandardSymplecticMatrix(3);
R := R2*RandomSymplecticMatrix(3, 1);
//R := R2;
E := R*(2*E3)*Transpose(R);

R := Matrix(Rationals(), [
[-1/2, -1/2,  3/2,    0,  1/2,    0],
[   0, -1/2,  3/2,  1/2,    0,    0],
[ 1/2, -1/2,  1/2,    1,    1,  1/2],
[   1,   -3,    6,    3,    2,    1],
[  -4,    1,    3,   -4,   -3,   -2],
[   0,    0,   -3,    0,    3,    1]
]);

print "Matrix defining index 8 overlattice with principal polarization:", R;
print "Determinant:", Determinant(R);
print "Pairing on new lattice:", E;

RCC := ChangeRing(R, BaseRing(Parent(Q)));
P := RCC*Q;
P := Transpose(P);
P1 := Submatrix(P, 1,1, 3,3);
P2 := Submatrix(P, 1,4, 3,3);
tau := P1^(-1)*P2;
print "New small period matrix:", ChangeRing(tau, ComplexField(5));

/* Check niet-niet-hyperelliptisch door na te gaan dat meer dan 28 waarden niet 0 zijn: */
fundamentalThetas := CalculThetas(tau/2);
thetas := AllDuplication(fundamentalThetas);
thetas_zero := #[ theta : theta in thetas | Abs(theta) lt 10^(-10) ];
print "Number of non-zero thetas:", thetas_zero;


/* Turn crank */

// computation of theta[0,b](tau/2)
fundamentalThetas := CalculThetas(tau/2);
fundamentalThetas:=NaiveThetaConstantsGenus3(tau/2,false,2000);

// computation of theta[a,b](tau)^2
thetas := AllDuplication(fundamentalThetas);
// square root extraction
thetas:=Rotate(thetas,-1);
Clow := ComplexField(50); taulow :=Matrix(Clow,3,3,[ Clow!tau[i][j] : i,j in [1..3]]);
for i:=1 to 64 do
    // tau or taulow below? It should be taulow but sometimes it leads to errors.
    thetas[i] := Sqrt(thetas[i]); if ( average(ThetaGenus3(i,taulow)-thetas[i]) gt -20) then thetas[i] := -thetas[i]; end if;
end for;

// compute the Moduli of Weber
M:=ModuliFromTheta(thetas);
// compute a Riemann model of the curve from the Moduli
F:=RiemannModelFromModuli(M);

// The Dixmier-Ohno invariants of F
DO, W := DixmierOhnoInvariants(F);

for i in [2..#DO] do
    print DO[i]/DO[1]^(W[i] div 3);
    print ContinuedFraction(Real(DO[i]/DO[1]^(W[i] div 3)));
end for;

// look for a good rational approximation of the (absolute) invariants below

I6:=RationalReconstruction(DO[2]/DO[1]^2);
I9:=RationalReconstruction(DO[3]/DO[1]^3);
J9:=RationalReconstruction(DO[4]/DO[1]^3);
I12:=RationalReconstruction(DO[5]/DO[1]^4);
J12:=RationalReconstruction(DO[6]/DO[1]^4);
I15:=RationalReconstruction(DO[7]/DO[1]^5);
J15:=RationalReconstruction(DO[8]/DO[1]^5);
I18:=RationalReconstruction(DO[9]/DO[1]^6);
J18:=RationalReconstruction(DO[10]/DO[1]^6);
I21:=RationalReconstruction(DO[11]/DO[1]^7);
J21:=RationalReconstruction(DO[12]/DO[1]^7);
I27:=RationalReconstruction(DO[13]/DO[1]^9);

// look for a weighted projective equivalent of the absolute invariants above with small denominators
I3:=2*3*Denominator(I9)/Denominator(I6);
DOr:=[I3,I3^2*I6,I3^3*I9,I3^3*J9,I3^4*I12,I3^4*J12,I3^5*I15,I3^5*J15,I3^6*I18,I3^6*J18,I3^7*I21,I3^7*J21,I3^9*I27];
d:=Lcm([Denominator(I) : I in DOr]);
print "Final Dixmier-Ohno invariants:", DOr;

exit;
