load "ingredients.m";

R<x> := PolynomialRing(Rationals());
CC := ComplexFieldExtra(100);

f := x^8 + 2*x^6 - 3*x^4 + 7*x^2 - 1;
g := x*(x^4 + 2*x^3 - 3*x^2 + 7*x - 1);
h := x^4 + 2*x^3 - 3*x^2 + 7*x - 1;

P := Transpose(PeriodMatrix(f : Prec := 100));
Q1 := Transpose(PeriodMatrix(g : Prec := 100));
Q2 := Transpose(PeriodMatrix(h : Prec := 100));
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
