function BinaryQuarticInvariants(bq);

R<x> := Parent(bq);

a := Coefficient(bq, 4);
b := Coefficient(bq, 3);
c := Coefficient(bq, 2);
d := Coefficient(bq, 1);
e := Coefficient(bq, 0);

I := 12*a*e - 3*b*d + c^2;
J := 72*a*c*e + 9*b*c*d - 27*a*d^2 - 27*e*b^2 - 2*c^3;
Delta := 4*I^3 - J^2;
a := -I/3; b := -J/27;
j := 1728*(a^3/(a^3 + 27/4*b^2));

return j, I, J;

end function;


R<x,y,z> := PolynomialRing(Rationals(), 3);
S<t> := PolynomialRing(Rationals());
h := hom< R -> S | [t,1,0] >;

F := -132*x^4 - 168*x^3*y + 66*x^2*y^2 + 5538555990734597384122535449*x^2*z - 312*x*y^3 + 10146262235127245628056409478*x*y*z - 72*y^4 + 10285889697078537999084708691*y^2*z - 25994437507946131700879908927492903820278521941892492*z^2;

F0 := Evaluate(F, [x,y,(1/(151*631*1733*3541*12613*64937*97187))*z]);
print "Smaller genus 1 curve:";
print F0;

print [ Factorization(Integers() ! MonomialCoefficient(F0, mon)) : mon in [ x^2*z, x*y*z, y^2*z, z^2 ] ];
G0 := R ! MinimizeReducePlaneQuartic(Evaluate(F0, [x,y,z^2]));
print "Smaller quartic:";
print G0;

I0, W := DixmierOhnoInvariants(G0);
I := [
1,
2109277839/53522392810,
-89443009291408765/1174693420676037,
-55599228132882455/3524080262028111,
6780789614658833554675/171878791926476381766,
16178051366872471755217/85939395963238190883,
5289364213013316316636263365/12574480538549085613618794,
11554001052769450233888257717/314362013463727140340469850,
5241613985342223537727845542431225/5519618530318275326440424101476,
-186052415477606199911764545609269/1839872843439425108813474700492,
606432174635893377764392459272631577233/9085719871339980853658737203897360390,
-8186787527516960455972485019847907461489/605714658089332056910582480259824026,
-574721404340529749306341150313547201090093355200000/60035736779689026704617538063648837742680839
];
print "Check invariants equal:";
print WPSNormalize(W, I0) eq I;

f0 := &+[ MonomialCoefficient(G0, z^4)*t^0 ];
f2 := &+[ MonomialCoefficient(G0, x^i*y^(2-i)*z^2)*t^i : i in [0..2] ];
f4 := &+[ MonomialCoefficient(G0, x^i*y^(4-i))*t^i : i in [0..4] ];
j := BinaryQuarticInvariants(S ! (-(f2/(2*f0))^2 + (f4/f0)));
print "Check genus 1 invariant:";
print j;

K := SplittingField(h(G0));
H0 := ChangeRing(G0, K);
R<x,y,z> := Parent(H0);
S<t> := PolynomialRing(K);
H0 /:= MonomialCoefficient(H0, z^4);

rts := [ rt[1] : rt in Factorization(ChangeRing(h(H0), K)) ];
for pair in [ [1,2,3,4], [1,3,2,4], [1,4,2,3] ] do
    hX := -&+[ MonomialCoefficient(H0, x^i*y^(2-i)*z^2)*t^i : i in [0..2] ];
    fX := MonomialCoefficient(H0, x^4)*rts[pair[1]]*rts[pair[2]];
    gX := rts[pair[3]]*rts[pair[4]];
    print "Check that factorization works:";
    print H0 eq (z^4 - y^2*Evaluate(hX, x/y)*z^2 + y^4*Evaluate(fX*gX, x/y));

    f2 := Coefficient(fX, 2); f1 := Coefficient(fX, 1); f0 := Coefficient(fX, 0);
    g2 := Coefficient(gX, 2); g1 := Coefficient(gX, 1); g0 := Coefficient(gX, 0);
    h2 := Coefficient(hX, 2); h1 := Coefficient(hX, 1); h0 := Coefficient(hX, 0);

    A := Matrix([ [ f2, f1, f0 ], [ h2, h1, h0 ], [ g2, g1, g0 ] ]);
    B := A^(-1);

    a1 := B[1,1]; b1 := B[1,2]; c1 := B[1,3];
    a2 := B[2,1]; b2 := B[2,2]; c2 := B[2,3];
    a3 := B[3,1]; b3 := B[3,2]; c3 := B[3,3];

    a := a1 + 2*a2*t + a3*t^2;
    b := b1 + 2*b2*t + b3*t^2;
    c := c1 + 2*c2*t + c3*t^2;

    f0 := 2*b*(b^2 - a*c);
    p0 := f0/LeadingCoefficient(f0);
    J := IgusaInvariants(p0);

    print "New Igusa invariants:";
    print WPSNormalize([2,4,6,8,10], J);
    // [ 1, 709/23762, 1216/1295029, 27495/2258530576, 153/61544958196 ]
end for;

X := Curve(ProjectiveSpace(Parent(G0)), G0);
I := DixmierOhnoInvariants(G0);
DX := Integers() ! I[#I];

R0<t> := PolynomialRing(Rationals());
f0 := 2*t^5 + 7*t^4 + 2*t^3 - 9*t^2 - 2*t;
//for d in [ m : m in [-125000..125000] | not IsSquare(m) ] do
for d in [ m : m in [ -9390 ] | not IsSquare(m) ] do
    Y := HyperellipticCurve(d*f0);
    J := IgusaInvariants(Y);
    DY := Integers() ! J[#J];
    n := 1;

    for p in [ n : n in [1..100] | IsPrime(n) ] do
        test := true;
        if Valuation(DX, p) eq 0 and Valuation(DY, p) eq 0 then

            fs0 := Factorization(LPolynomial(ChangeRing(X, FiniteField(p))));
            fs := [ ];
            for f in fs0 do
                K := SplittingField(f[1]);
                R := PolynomialRing(K);
                rts := Roots(f[1], K);
                Append(~fs, R0 ! &*[ R.1 - rt[1]^n : rt in rts ]);
            end for;

            gs0 := Factorization(LPolynomial(ChangeRing(Y, FiniteField(p))));
            gs := [ ];
            for g in gs0 do
                K := SplittingField(g[1]);
                R := PolynomialRing(K);
                rts := Roots(g[1], K);
                Append(~gs, R0 ! &*[ R.1 - rt[1]^n : rt in rts ]);
            end for;

            for g in gs do
                if not g in fs then
                    test := false;
                end if;
            end for;
        end if;
        if not test then
            break;
        end if;
    end for;
    if test then
        print d;
    end if;
end for;
