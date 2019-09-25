load "ingredients.m";

R<x> := PolynomialRing(Rationals());
CC := ComplexFieldExtra(100);

f := x^8 + 2*x^6 - 3*x^4 + 7*x^2 - 1;
g := x*(x^4 + 2*x^3 - 3*x^2 + 7*x - 1);
h := x^4 + 2*x^3 - 3*x^2 + 7*x - 1;

fs := [f, g, h];
pairs := [[f, g], [g, f], [f, h], [h, f]];
pairs := [[f, g]];

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
    print HyperellipticCurve(g);
    print "to";
    print HyperellipticCurve(f);

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
