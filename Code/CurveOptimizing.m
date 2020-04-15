function CurveAndMapToLegendreForm(C,ysq)

// First compute the two-torsion points on C to find equation of the form v^2 = (u-u1)(u-u2)(u-u3)(u-u4) for ui in us.
us := ComputeBranchPoints(C);
AC<x,y> := CoordinateRing(C);
KC:=FunctionField(C);
fld:=BaseRing(C);

u_mp := KC!y/KC!x;
vsq_mp := &*[u_mp - us[i] : i in [1..#us]];
vsq_mp_div := Divisor(vsq_mp);
v_mp_div := vsq_mp_div div 2;

bool, v_mp := IsPrincipal(v_mp_div);
assert bool;

const := v_mp^2/(&*[u_mp - us[i] : i in [1..#us]]);
assert Degree(const) eq 0;
const := fld!const;

// Define the equation and construct the map sending x,y to u,v and push ysq along
Ruv<u,v> := PolynomialRing(fld,2);
E_poly := v^2 - const*&*[u - us[i] : i in [1..#us]];
E_crv := ProjectiveClosure(Curve(AffineSpace(fld,2),E_poly));
mp_crv := map< C -> E_crv | [u_mp, v_mp, 1]>;
E, mp_E := EllipticCurve(E_crv, E_crv![us[1], 0, 1]);
ysq_E := Pushforward(mp_E,Pushforward(mp_crv,ysq));

// Compute the Legendre form of the curve.
// There might be a better way to obtain a simpler equation for the curve...have to base change for Legendre form
// If the class number of fld is 1, can just take MinimalWeierstrass model
lambda := CrossRatio(us[1],us[2],us[3],us[4]);
R0<X> := PolynomialRing(fld);
E_leg := EllipticCurve(X*(X-1)*(X - lambda));

// if not isomorphic, should be quadratic twist, so base change
// FIXME: except in case where j = 0 or 1728, where higher twists are possible
if not IsIsomorphic(E,E_leg) then
  twist_bool, new := IsQuadraticTwist(E, E_leg);
  assert twist_bool;
  fld2 := NumberField(X^2 - new);
  fld2_abs := AbsoluteField(fld2);
  fld2_best, mp2_best := Polredabs(fld2_abs : Best := true);
  ainvs := aInvariants(E);
  ainvs_abs := [fld2_abs!(fld2!el) : el in ainvs];
  ainvs_best := [mp2_best(el) : el in ainvs_abs];
  E_best := EllipticCurve(ainvs_best);
  ainvs_leg := aInvariants(E_leg);
  ainvs_leg_abs := [fld2_abs!(fld2!el) : el in ainvs_leg];
  ainvs_leg_best := [mp2_best(el) : el in ainvs_leg_abs];
  E_leg_best := EllipticCurve(ainvs_leg_best);
  iso_bool, mp_leg := IsIsomorphic(E_best, E_leg_best);
  assert iso_bool;
end if;

// map ysq into base-chaged curves
A := CoordinateRing(AffinePatch(E,1));
A_best := CoordinateRing(AffinePatch(E_best,1));
coerce_2 := Coercion(fld,fld2);
coerce_abs := Coercion(fld2,fld2_abs);
coerce_best := Coercion(fld2_best, A_best);
cs_map := coerce_2*coerce_abs*mp2_best*coerce_best;
mp_best := hom<A -> A_best | cs_map, [A_best.1, A_best.2]>;

ysq_num_best := mp_best(Numerator(ysq_E));
ysq_den_best := mp_best(Denominator(ysq_E));

KE_best := FunctionField(E_best);

ysq_E_best := KE_best!(ysq_num_best)/KE_best!(ysq_den_best);
ysq_leg_best := Pushforward(mp_leg,ysq_E_best);

pts_y := Support(Divisor(ysq_leg_best));
pts_y := [* RepresentativePoint(pt) : pt in pts_y *];
K1 := Parent(pts_y[1][2]);
K1_abs := AbsoluteField(K1);

K1_best, mp1_best := Polredabs(K1_abs : Best := true);
K2 := Parent(pts_y[2][2]);
K2_abs := AbsoluteField(K2);
K2_best, mp2_best := Polredabs(K2_abs : Best := true);

h := hom< fld2_best -> K1_best | mp1_best(K1!fld2_best.1)>;
E1_best := ChangeRing(E_leg_best, K1_best);
KE1_best:= FunctionField(E1_best);
h2 := hom< fld2_best -> KE1_best | h(fld2_best.1)>;
A_leg_best := CoordinateRing(AffinePatch(E_leg_best,1));
A1_best := CoordinateRing(AffinePatch(E1_best,1));
mp1_best_func := hom< A_leg_best -> KE1_best | h2, [KE1_best.1, KE1_best.2]>;
ysq_1_best := (KE1_best!(mp1_best_func(Numerator(ysq_leg_best))))/(KE1_best!(mp1_best_func(Denominator(ysq_leg_best))));
// TODO: when polredabs-ing the compositum, can give it product of discriminants of the fields, which may help
comps := CompositeFields(K1_best, K2_best);
// TODO: comps[1] is smaller (only degree 8), but pts[3] and pts[4] not defined over it
K3<nu> := comps[2];
// should we Polredabs(K3)?
E3 := ChangeRing(E_leg_best, K3);
KE3 := FunctionField(E3);
A3<x3,y3> := CoordinateRing(AffinePatch(E3,1));
mp3 := hom< A1_best -> A3 | [A3.1, A3.2]>;
ysq_3 := (KE3!(mp3(Numerator(ysq_1_best))))/(KE3!(mp3(Denominator(ysq_1_best))));


return E3,ysq_3,lambda;
end function;
