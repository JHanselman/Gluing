load "ingredients.m";

R<t> := PolynomialRing(Rationals());
S<x,y,z> := PolynomialRing(Rationals(), 3);
hSR := hom<S -> R | [t, 1, 1]>;
prec := 100;
CC := ComplexFieldExtra(prec);

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

p := hSR(h^2 - 4*f*g);
q := b*(b^2 - a*c);
Y := SE_Curve(q, 2 : Prec := prec);

T<x,y> := PolynomialRing(Rationals(), 2);
hST := hom<S -> T | [x, y, 1]>;
F := hST(F);

P := Transpose(PeriodMatrix(F : Prec := prec));
//Q := Transpose(PeriodMatrix(p : Prec := prec));
Q := Transpose(Y`BigPeriodMatrix);
P := ChangeRing(P, CC); Q := ChangeRing(Q, CC);

GeoEndoRep := GeometricIsogenyRepresentationPartial(Q, P);
print #GeoEndoRep;
T, R := Explode(GeoEndoRep[1]);
R := Transpose(R); T := Transpose(T);

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

b5, b6 := Explode([ tup[1] : tup in Roots(b, CC) ]);
b5 := [ b5, 0 ];
b6 := [ b6, 0 ];
v := SE_AbelJacobi(SE_Divisor([<b5, 1>, <b6, -1>], Y), Y);

RR := RealField(CC);
v := Transpose(ChangeRing(v, RR));
RRR := ChangeRing(R, RR);

print "Check that entries are integral:";
print v*RRR;

exit;
