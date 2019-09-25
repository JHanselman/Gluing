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

pairs := [[* F, p *], [* p, F *], [* F, q *], [* q, F *]];

for i in [1..#pairs] do
    print "Pair number", i;
    pair := pairs[i];
    f := pair[1];
    g := pair[2];

    P := Transpose(PeriodMatrix(f : Prec := 100));
    Q := Transpose(PeriodMatrix(g : Prec := 100));
    P := ChangeRing(P, CC); Q := ChangeRing(Q, CC);

    /* We take a morphism from the curve Y defined by g and Q to the curve X
     * defined by f and P. Note the transpose, which really ticks me off. */

    GeoEndoRep := GeometricIsogenyRepresentationPartial(Q, P);
    print "Number of elements in isogeny basis:", #GeoEndoRep;
    T, R := Explode(GeoEndoRep[1]);
    R := Transpose(R); T := Transpose(T);
    RCC := ChangeRing(R, CC);
    comm := Q*T - RCC*P;

    print "Test almost 0:";
    print Maximum([ Abs(c) : c in Eltseq(comm) ]);

    print "Curves:";
    print "from";
    print g;
    print "to";
    print f;

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

end for;

exit;
