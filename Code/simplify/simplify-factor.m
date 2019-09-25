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
q := x^3 - 27*I*x - 27*J;

return j, q;

end function;


R<x,y,z> := PolynomialRing(Rationals(), 3);
S<t> := PolynomialRing(Rationals());
h := hom< R -> S | [t,1,0] >;

F := -132*x^4 - 168*x^3*y + 66*x^2*y^2 + 5538555990734597384122535449*x^2*z - 312*x*y^3 + 10146262235127245628056409478*x*y*z - 72*y^4 + 10285889697078537999084708691*y^2*z - 25994437507946131700879908927492903820278521941892492*z^2;

F0 := Evaluate(F, [x,y,(1/(151*631*1733*3541*12613*64937*97187))*z]);
print "Smaller genus 1 curve:";
print F0;

a := &+[ MonomialCoefficient(F0, z^2)*t^0 ];
b := &+[ MonomialCoefficient(F0, x^i*y^(2-i)*z)*t^i : i in [0..2] ];
c := &+[ MonomialCoefficient(F0, x^i*y^(4-i))*t^i : i in [0..4] ];
j, q := BinaryQuarticInvariants(S ! (b^2 - 4*a*c));
print j;
print q;

print Conductor(EllipticCurve(q));
