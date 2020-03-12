load "ingredients.m";

R<x> := PolynomialRing(Rationals());

CC := ComplexFieldExtra(100);
I:=CC.1;

f := (x^2-1)*(x^2-4)*(x^2-9)*(x^2-16);
g := x*(x-1)*(x-4)*(x-9)*(x-16);
h := (x-1)*(x-4)*(x-9)*(x-16);

P3 := Transpose(SE_BigPeriodMatrix(f, 2 : Prec := 200));
P2 := Transpose(SE_BigPeriodMatrix(g, 2 : Prec := 200));
P1 := Transpose(SE_BigPeriodMatrix(h, 2 : Prec := 200));
P3 := ChangeRing(P3, CC);
P2 := ChangeRing(P2, CC);
P1 := ChangeRing(P1, CC);

GeoEndoRep1 := GeometricIsogenyRepresentationPartial(P1, P3);
print "Number of elements in isogeny basis:", #GeoEndoRep1;
T1, R1 := Explode(GeoEndoRep1[1]);
R1 := Transpose(R1); T1 := Transpose(T1);
R1CC := ChangeRing(R1, CC);
comm1 := P1*T1 - R1CC*P3;

print "Test almost 0:";
print Maximum([ Abs(c) : c in Eltseq(comm1) ]);

GeoEndoRep2 := GeometricIsogenyRepresentationPartial(P2, P3);
print "Number of elements in isogeny basis:", #GeoEndoRep2;
T2, R2 := Explode(GeoEndoRep2[1]);
R2 := Transpose(R2); T2 := Transpose(T2);
R2CC := ChangeRing(R2, CC);
comm2 := P2*T2 - R2CC*P3;

print "Test almost 0:";
print Maximum([ Abs(c) : c in Eltseq(comm2) ]);

P := P3;
Q := DiagonalJoin(P1, P2);
T := VerticalJoin(T1, T2);
R := VerticalJoin(R1, R2);
RCC := ChangeRing(R, CC);
comm := Q*T - RCC*P3;

print "Test almost 0:";
print Maximum([ Abs(c) : c in Eltseq(comm2) ]);

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

exit;
