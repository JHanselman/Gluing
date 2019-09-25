load "ingredients.m";

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

P := Transpose(PeriodMatrix(F : Prec := 100));
Q1 := Transpose(PeriodMatrix(p : Prec := 100));
Q2 := Transpose(PeriodMatrix(q : Prec := 100));
P := ChangeRing(P, CC); Q1 := ChangeRing(Q1, CC); Q2 := ChangeRing(Q2, CC);

GeoEndoRep1 := GeometricIsogenyRepresentationPartial(Q1, P);
T1, R1 := Explode(GeoEndoRep1[1]);
R1 := Transpose(R1); T1 := Transpose(T1);

GeoEndoRep2 := GeometricIsogenyRepresentationPartial(Q2, P);
T2, R2 := Explode(GeoEndoRep2[1]);
R2 := Transpose(R2); T2 := Transpose(T2);

Q := DiagonalJoin(Q1, Q2);
R := VerticalJoin(R1, R2);
T := VerticalJoin(T1, T2);

RCC := ChangeRing(R, CC);
comm := Q*T - RCC*P;

print "Test almost 0:";
print Maximum([ Abs(c) : c in Eltseq(comm) ]);

print "Matrix dimensions:";
printf "P is a matrix with %o rows of length %o\n", #Rows(P), #Rows(Transpose(P));
printf "Q is a matrix with %o rows of length %o\n", #Rows(Q), #Rows(Transpose(Q));
printf "R is a matrix with %o rows of length %o\n", #Rows(R), #Rows(Transpose(R));
printf "T is a matrix with %o rows of length %o\n", #Rows(T), #Rows(Transpose(T));

print "Rank of R:";
print Rank(R);

print "Connected component group of kernel:";
KCCG := KerModKer0(R, Q, P);
print KCCG;

print "Trivial component of kernel:";
K := Ker0(R, Q, P);
if not Type(K) eq RngIntElt then
    print ChangeRing(K, ComplexField(5));
else
    print K;
end if;

print "Cokernel:";
C := Coker(R, Q, P);
if not Type(C) eq RngIntElt then
    print ChangeRing(C, ComplexField(5));
else
    print C;
end if;

print "Check induced polarization is product:";
S := StandardSymplecticMatrix(3);
print R*S*Transpose(R);

exit;
