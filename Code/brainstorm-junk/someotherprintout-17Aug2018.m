blah, line1, line2, line3 := HyperellipticDivisor(E3,pts);
Support(Divisor(blah));
blah;
f3;
RR := RiemannRochSpace(Divisor(blah));
RR;
line1;
lin2;
line2;
line3;
line1*line2;
  A := CoordinateRing(Ambient(AffinePatch(E,1)));
A!line1;
Numerator(line1);
Parent($1);
Denominator(line1);
A2;
AE := Parent(Numerator(line1));
A3;
P<x,y,z> := PolynomialRing(BaseRing(E3),3);
mp_poly := hom< AE -> P | [P.1, P.2]>;
mp_poly(Numerator(line1));
DefiningEquation(AffinePatch(E3,1));
mp_poly($1);
P!DefiningEquation(AffinePatch(E3,1));
P!DefiningEquation(AffinePatch(E3,1));
DefiningEquation(AffinePatch(E3,1));
Parent($1);
Parent(line1);
AE := Parent(Numerator(line1));
P<x,y,z> := PolynomialRing(BaseRing(E3),3);
mp_poly := hom< AE -> P | [P.1, P.2]>;
line1 := mp_poly(Numerator(line1));
line2 := mp_poly(Numerator(line2));
line3 := mp_poly(Numerator(line3));
E3_eqn := DefiningEquation(E3);
mp_poly2 := hom< Parent(E3_eqn) -> P | [P.1, P.2] >;
E3_eqn := mp_poly2(E3_eqn);
P<x,y,z> := PolynomialRing(BaseRing(E3),3);
mp_poly := hom< AE -> P | [P.1, P.2]>;
line1 := mp_poly(Numerator(line1));
line2 := mp_poly(Numerator(line2));
line3 := mp_poly(Numerator(line3));
E3_eqn := DefiningEquation(E3);
mp_poly2 := hom< Parent(E3_eqn) -> P | [P.1, P.2, P.3] >;
E3_eqn := mp_poly2(E3_eqn);
E3_eqn;
AE := Parent(Numerator(line1));
P<x,y,z> := PolynomialRing(BaseRing(E3),3);
mp_poly := hom< AE -> P | [P.1, P.2]>;
line1 := mp_poly(Numerator(line1));
line2 := mp_poly(Numerator(line2));
line3 := mp_poly(Numerator(line3));
E3_eqn := DefiningEquation(AffinePatch(E3,1));
mp_poly2 := hom< Parent(E3_eqn) -> P | [P.1, P.2] >;
E3_eqn := mp_poly2(E3_eqn);
Scheme(AffineSpace(BaseRing(E3),3), [line3*z^2 - line1*line2, E3_eqn]);
AE;
AE := CoordinateRing(AffinePatch(E3,1))
Numerator(line1);
line1;
Parent($1);
fs;