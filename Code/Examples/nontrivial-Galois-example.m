load "../KummerFunctions.m";
//load "../brainstorm-help.m";
//SetSeed(1);

QQ := Rationals();
RL := PolynomialRing(QQ);
L := FieldOfFractions(RL);

// Define the curves we want to glue

T<x,y> := PolynomialRing(QQ,2);
// The elliptic curve
//g := (x - 1)*x*(x + 1)*(x + 2);
g := x^4 + x^3 + x^2 + x + 1;
g := g-y^2;
A2:= AffineSpace(T);
X1:=Curve(A2,g);
X1:=ProjectiveClosure(X1);
X1:=EllipticCurve(X1);

// The hyperelliptic curve
R<x> := PolynomialRing(QQ);
f := (x^4 + x^3 + x^2 + x + 1)*(x+2)*(x+3);

// base change to field where 2-torsion is defined
facts := Factorization(f);
facts :=[el[1] : el in facts];
fields := [*NumberField(el) : el in facts*];
KK := QQ;
for i := 1 to #fields do
  KK := Compositum(KK,fields[i]);
end for;
f := ChangeRing(f,KK);
X1 := ChangeRing(X1,KK);

K,ysq := CalculateKummer(f);
F:= DefiningEquation(K);
S3<x1,x2,x3,x4> := PolynomialRing(L,4);
nodes := SetToSequence(SingularPoints(K));
O:=K![0,0,0,1];
Remove(~nodes, Index(nodes,O)) ;
print nodes;
Q2:= nodes[1];

// Find all planes that go through the two nodes with a given j-invariant.
j, C, ysq := FindPlanes(K,X1,O,Q2,ysq);
value := jInvariant(X1);
j_num := Numerator(j - value);
facts := Factorization(j_num);
facts := [fact[1] : fact in facts];
fields := [* *];
for poly in facts do
  if Degree(poly) eq 1 then
    Append(~fields, Rationals());
  else
    Append(~fields,NumberField(poly));
    // maybe we should do Polredabs or OptimizedRepresentation to make the fields nicer
  end if;
end for;

// Plug mu into the equation for the curve
fld<nu> := fields[5];
eqn := DefiningEquation(C);
eqn := EvaluateField(eqn,[fld.1]);
ysq := EvaluateField(Numerator(ysq),[fld.1]);
C := Curve(AffineSpace(fld,2),eqn);
KC := FunctionField(C);
S2_aff := PolynomialRing(fld,2);

// Map ysq into the function field of C
h_crv := hom< S2_aff -> KC | [KC.1, KC.2]>;
ysq := h_crv(ysq);

// Compute the two-torsion points on C to find equation of the form v^2 = (u-u1)(u-u2)(u-u3)(u-u4) for ui in us.
us := ComputeBranchPoints(C);
AC<x,y> := CoordinateRing(C);

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

// See p. 47 of Silverman
// doesn't seem any better: still have to base change
/*
// Caution: only works when j-invariant is not 0 or 1728.
f_silv := T.2^2 + T.1*T.2 - (T.1^3 - 36/(value - 1728)*T.1 - 1/(value - 1728));
C_silv := ProjectiveClosure(Curve(A2, f_silv));
E_silv := EllipticCurve(C_silv);
E_silv_fld := ChangeRing(E_silv, fld);
*/

// if not isomorphic, should be quadratic twist, so base change
if not IsIsomorphic(E,E_leg) then
  _, new := IsQuadraticTwist(E, E_leg);
  fld2 := NumberField(X^2 - new);
  E_al := ChangeRing(E, fld2);
  E_leg_al := ChangeRing(E_leg, fld2);
  iso_bool, mp_leg := IsIsomorphic(E_al, E_leg_al);
  assert iso_bool;
end if;

// map ysq into base-chaged curves
A := CoordinateRing(AffinePatch(E,1));
A_al := CoordinateRing(AffinePatch(E_al,1));
mp_al := hom<A -> A_al | [A_al.1, A_al.2]>;

ysq_num_al := mp_al(Numerator(ysq_E));
ysq_den_al := mp_al(Denominator(ysq_E));

KE_al := FunctionField(E_al);

ysq_E_al := KE_al!(ysq_num_al)/KE_al!(ysq_den_al);
mp_leg;
ysq_leg_al := Pushforward(mp_leg,ysq_E_al);

KC<x,y> := FunctionField(C);
pts_y := Support(Divisor(ysq_leg_al));
pts_y := [* RepresentativePoint(pt) : pt in pts_y *];
K1 := Parent(pts_y[1][2]);
K2 := Parent(pts_y[2][2]);
poly2 := DefiningPolynomial(K2);
cs2 := Coefficients(poly2);
R2 := PolynomialRing(K1);
K3 := NumberField(R2!cs2);
E3 := ChangeRing(E_leg_al, K3);
KE3 := FunctionField(E3);
A_leg_al := CoordinateRing(AffinePatch(E_leg_al,1));
A3<x3,y3> := CoordinateRing(AffinePatch(E3,1));
mp3 := hom< A_leg_al -> A3 | [A3.1, A3.2]>;
ysq_3 := (KE3!(mp3(Numerator(ysq_leg_al))))/(KE3!(mp3(Denominator(ysq_leg_al))));
pts := Support(Divisor(ysq_3));
// this is slow; might be worth computing the points beforehand and then pushing them forward along these isomorphisms
pts := pts[1..4];
pts := [RepresentativePoint(pt) : pt in pts];
lines, Q := HyperellipticLines(E3,pts);
lines := [KE3!line : line in lines];
v := KE3!(lines[1]*lines[2]/lines[3]);

// find the function corresponding to the correct genus 3 curve
// original function v might be off by a 2-torsion point
// this is slow: computing IsPrincipal takes a while, I think
print "Finding function that yields correct curve...";
KE3<x,y> := FunctionField(E3);
vs := [v, v/x, v/(x-1), v/(x-lambda)];
D_diffs := [Divisor(v0) - Divisor(ysq_3) : v0 in vs];
for i := 1 to #vs do
  D_div2 := D_diffs[i] div 2;
  princ_bool2, gen := IsPrincipal(D_div2);
  if princ_bool2 then
    print "Success: divisor is principal!";
    print i;
    rr_ind := i;
    //print gen;
    v := vs[i];
    break i;
  end if;
end for;

// choose corresponding 2-torsion point
Ts := [E3!0, E3![0,0], E3![1,0], E3![lambda,0]];
T := Ts[rr_ind];

// now make the u (the other coordinate for the map (x,y) -> (u,v))
// this is slow and gives a nasty answer; maybe could do it by hand
RR_u, mp_RR_u := RiemannRochSpace(Divisor(Q)+Divisor(T));
b := Basis(RR_u);
b := [mp_RR_u(el) : el in b];
for el in b do
  if Degree(el) gt 0 then
    u := el;
  end if;
end for;

// make the projective map (x,y) -> (u,v) and take its image as the new curve
// this is slow...maybe use Riemann-Roch space instead:
// pull monomials u^i*v*j into L(4*Q + 4*oo), u^i*v^j @@ mp_RR, to obtain change of basis matrix
// then pull in v^2
/*
phi := ProjectiveMap([u,v,1]);
X1_final_old := Image(phi);
phi := Restriction(phi, E3, X1_final_old);
assert Degree(phi) eq 1;
*/

// find new curve using Riemann-Roch space
RR, mp_RR := RiemannRochSpace(4*Divisor(Q) + 4*Divisor(T));
mons := [u^i : i in [0..4]] cat [u^i*v : i in [0..2]];
cs_list := [];
for mon in mons do
  mon_list := mon @@ mp_RR;
  Append(~cs_list, mon_list);
end for;
M := Matrix(cs_list);

// express v^2 as linear combination of these monomials
vsq_vec := (v^2) @@ mp_RR;
vsq_cs := vsq_vec*(M^-1);
vsq_cs := Eltseq(vsq_cs);
vsq_check := &+[vsq_cs[i]*mons[i] : i in [1..#mons]];
assert vsq_check eq (v^2); // double-check

// now make nice model of the genus 1 curve
RUV<U,V> := PolynomialRing(BaseRing(Parent(v)),2);
mons := [U^i : i in [0..4]] cat [U^i*V : i in [0..2]];
F := V^2;
for i := 1 to #mons do
  F -:= vsq_cs[i]*mons[i];
end for;
F := F/LeadingCoefficient(F);
X1_final := Curve(AffineSpace(BaseRing(RUV),2), F);
// hmmm...commands like Genus(X1_final_new) and IsIrreducible(X1_final_new) just seem to hang...


// now make genus 3 cover
//F := DefiningEquation(AffinePatch(X1_final,1));
//RF<x,y> := Parent(F);
G := Evaluate(F,[U,V^2]);
X3 := Curve(AffineSpace(BaseRing(X1_final),2),G);
Genus(X3);
I, W :=DixmierOhnoInvariants(G);
invs := WPSNormalize(W,I);
print invs;

/*
print "Weird genus thing...";
phi := ProjectiveMap([u,v,1]);
X1_final_old := Image(phi);
phi := Restriction(phi, E3, X1_final_old);
assert Degree(phi) eq 1;
printf "Old curve using Bruin's method (image of ProjectiveMap([u,v,1])): %o\n", X1_final_old;
printf "\n";
printf "New curve using Riemann-Roch space: %o\n", X1_final;
printf "Genus of old curve: %o\n", Genus(X1_final_old);
print "Computing genus of new curve...";
printf "Genus of new curve: %o\n", Genus(X1_final);
*/

/*
P<x,y,z> := PolynomialRing(BaseRing(E3),3);
mp_poly := hom< Parent(line1) -> P | [P.1, P.2]>;
line1 := mp_poly(Numerator(line1));
line2 := mp_poly(Numerator(line2));
line3 := mp_poly(Numerator(line3));
*/
/*
E3_eqn := DefiningEquation(AffinePatch(E3,1));
E3_eqn := mp_poly(E3_eqn);
Scheme(AffineSpace(BaseRing(E3),3), [line3*z^2 - line1*line2, E3_eqn]);
*/

/*
pt_new := (&+pts)/2;
oo := E3!0;
D := Divisor(pts[1]) + Divisor(pts[2]) + Divisor(pts[3]) + Divisor(pts[4]) - 2*Divisor(Q) - 2*Divisor(oo);
princ_bool1, f3 := IsPrincipal(D);
assert princ_bool1;
KE3<x,y> := FunctionField(E3);
fs := [f3, f3/x, f3/(x-1), f3/(x-lambda)];
D_diffs := [Divisor(f) - Divisor(ysq_3) : f in fs];
for i := 1 to #fs do
  D_div2 := D_diffs[i] div 2;
  princ_bool2, gen := IsPrincipal(D_div2);
  if princ_bool2 then
    print "Success: divisor is principal!";
    print i;
    print gen;
  end if;
end for;
*/

// now push the points forward
/*
sing_pts := SingularPoints(C);
Cbar := ProjectiveClosure(C);
u_num := Numerator(u_mp);
u_den := Denominator(u_mp);
v_num := Numerator(v_mp);
v_den := Denominator(v_mp);
mp_crv_bar := map< Cbar -> E_crv | [u_num*v_den, v_num*u_den, u_den*v_den]>;
//mp_crv_bar := map< Cbar -> E_crv | [u_mp, v_mp, 1]>;
sing_pts_bar := [Cbar!pt : pt in sing_pts];
sing_pts_crv := [mp_crv_bar(pt) : pt in sing_pts];
*/


