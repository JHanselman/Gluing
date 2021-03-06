R<x,y> := PolynomialRing(Rationals(),2);
f := y^2 - (x^3 - x);
line := 2*x + 3*y;
Resultant;
Resultant(f,line,1);
Resultant(f,line,2);
C := Curve(AffineSpace(Rationals(),2),f);
C;
Ambient(C);
CoordinateRing($1);
GenericPoint(C);
KC<t> := FunctionField(C);
GenericPoint(C);
P_gen := GenericPoint(C);
P_gen[1];
f;
Parent(f);
x_gen := P_gen[1];
y_gen := P_gen[2];
line := y - y_gen/x_gen*x;
A := Ambient(C);
  K<mu> := BaseRing(A);
  R<x,y> := CoordinateRing(A); 
  f := DefiningEquation(C);
  x0 := P[1];
  y0 := P[2];
  line := y - y0/x0*x;
GenericPoint(A);
P_gen := $1;
P_gen[1];
Parent($1);
FunctionField(C);
KC<t> := $1;
KC;
f;
x;
Parent(x);
KC!x;
KC!y;
KC!y/KC!x;
proj := $1;
Support(Divisor(Differential(proj)));
pts := $1[2..3];
pts;
pt := pts[1];
RepresentativePoint(pt);
Eltseq($1);
$1[1];
Parent($1);
pts := [RepresentativePoint(pt) : pt in pts];
proj(pts[1]);
proj(pts[2]);
RamificationPoints(proj);
ProjectiveMap(proj);
RamificationPoints($1);
RamificationDivisor(proj);
ProjectiveMap(proj);
RamificationDivisor($1);
RamificationPoints;
RamificationDivisor;
proj;
ProjectiveMap(proj);
proj_map;
proj_map := $1;
Type(proj_map);
Domain(proj_map);
Type($1);
Codomain(proj_map);
Type($1);
ProjectiveLine;
ProjectiveLineAsCurve;
Support(Divisor(Differential(proj)));
Support(Divisor(proj));
pts;
proj(pts[1]);
proj(pts[2]);
F<i> := QuadraticField(-1);
ChangeRing(proj,F);
ChangeRing(Parent(proj),F);
C;
ChangeRing(C,F);
pts;
pts[1];
Parent($1);
BaseRing($1);
Eltseq(pts[1]);
Parent($1[1];
Parent($1[1]);
Eltseq(pts[1]);
Eltseq(pts[3]);
Eltseq(pts[1]);
Parent($1[3]);
proj(Eltseq(pts[1]));
C_F := ChangeRing(C,F);
KC_F<t> := FunctionField(KC_F);
KC_F<t> := FunctionField(C_F);
Type(proj);
KC_F!proj;
proj := KC_F!y/x;
y;x
y/x;
KC!y/x;
A := Ambient(C_F);
  R<x,y> := CoordinateRing(A); 
proj := KC_F!y/x;
proj;
Support(Divisor(Differential(proj)));
proj;
Differential(proj);
proj := KC_F!y/KC_F!x;
Support(Divisor(Differential(proj)));
pts := $1;
pts := pts[2..4];
pts;
Support(Divisor(Differential(proj)));
pts := $1;
pts := pts[2..5];
pts;
pts_down := [proj(pt) : pt in pts];
pts_down := [proj(RepresentativePoint(pt)) : pt in pts];
pts_down;
function CrossRatio(z1,z2,z3,z4)
  return (z3-z1)*(z4-z2)/((z3-z2)*(z4-z1));
end function;
CrossRatio(pts_down[1], pts_down[2], pts_down[3], pts_down[4]);
lambda := $1;
jInvariant;
jFunction;
function jInvariantFromLegendre(lambda)
  return 2^8*(lambda^2 - lambda + 1)^3/(lambda^2*(lambda-1)^2);
end function;
jInvariantFromLegendre(lambda);
2^8;
