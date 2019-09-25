function BinaryQuarticInvariants(bq); 
 
R<x> := Parent(bq); 
 
a := Coefficient(bq,4); 
b := Coefficient(bq,3); 
c := Coefficient(bq,2); 
d := Coefficient(bq,1); 
e := Coefficient(bq,0); 
 
I := 12*a*e - 3*b*d + c^2; 
J := 72*a*c*e + 9*b*c*d - 27*a*d^2 - 27*e*b^2 - 2*c^3; 
Delta := 4*I^3 - J^2; 
 
return I,J,Delta; 
 
end function; 


R<a,b,c,g1,g2,g3,j1,j2> := PolynomialRing(Rationals(), 8);
S<x> := PolynomialRing(R);
p := x^6 + a*x^4 + b*x^2 + c;
q1 := x^3 + a*x^2 + b*x + c;
q2 := x^4 + a*x^3 + b*x^2 + c*x;

g2ev := G2Invariants(HyperellipticCurve(p));
I1, J1, Delta1 := BinaryQuarticInvariants(q1); j1ev := I1^3 / Delta1;
I2, J2, Delta2 := BinaryQuarticInvariants(q2); j2ev := I2^3 / Delta2;

rel1 := Denominator(g2ev[1])*g1 - Numerator(g2ev[1]);
rel2 := Denominator(g2ev[2])*g2 - Numerator(g2ev[2]);
rel3 := Denominator(g2ev[3])*g3 - Numerator(g2ev[3]);
rel4 := Denominator(j1ev)*j1 - Numerator(j1ev);
rel5 := Denominator(j2ev)*j2 - Numerator(j2ev);
rels := [ rel1, rel2, rel3, rel4, rel5 ];

I := ideal<R | rels>;
print I;
print EliminationIdeal(I,  { j1, j2 });

exit;

