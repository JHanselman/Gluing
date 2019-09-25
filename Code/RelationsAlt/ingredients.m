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

return [ I, J ];

end function;


function jInv(bq);

S<x,z> := Parent(bq);
a := MonomialCoefficient(bq, x^4);
b := MonomialCoefficient(bq, x^3*z);
c := MonomialCoefficient(bq, x^2*z^2);
d := MonomialCoefficient(bq, x*z^3);
e := MonomialCoefficient(bq, z^4);

I := 12*a*e - 3*b*d + c^2;
J := 72*a*c*e + 9*b*c*d - 27*a*d^2 - 27*e*b^2 - 2*c^3;
return I^3 / J^2;

end function;


function G2Invs(b);

S<x,z> := Parent(b);
R<t> := PolynomialRing(BaseRing(S));
h := hom< S -> R | [t, 1] >;
return G2Invariants(HyperellipticCurve(h(b)));

end function;
