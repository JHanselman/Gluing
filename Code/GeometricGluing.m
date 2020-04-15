AttachSpec("spec");
load "KummerFunctions.m";
load "PolynomialExtra.m";
load "JInvariant.m";
load "CurveOptimizing.m";
SetSeed(1);

function GeometricGluing(f,g)

//In our algorithm we assume our curves are defined over a common base field.
QQ1 := CoefficientRing(f);
QQ2 := CoefficientRing(g);

if QQ1 ne QQ2 then
   error "Base field of X1 does not equal base field of Y2.";
end if; 

QQ := QQ1;
RL := PolynomialRing(QQ);
L := FieldOfFractions(RL);

//Define the curves.
T<x,y> := PolynomialRing(QQ,2);
A2:=AffineSpace(T);

Rf := Parent(f);
Rg := Parent(g);

phif := hom< Rf -> T | [x]>;
phig := hom< Rg -> T | [x]>;

fy := phif(f)-y^2;
gy := phig(g)-y^2;

X1 := Scheme(A2,fy);
X1 := Curve(X1);
X1 := ProjectiveClosure(X1);
X1 := EllipticCurve(X1);

Y2 := Scheme(A2,gy);
Y2 := Curve(Y2);

//Check that our curves are smooth
if IsSingular(Y2) then
    error "Y2 is singular.";
end if;
if Genus(Y2) ne 2 then
    error "Y2 is not of genus 2.";
end if;

//Calculate the Kummer surface associated to the genus 2 curve.
K,ysq := CalculateKummer(g);
F:= DefiningEquation(K);

S3<x1,x2,x3,x4> := PolynomialRing(L,4);

Sing := SingularSubscheme(K);
nodes := [ P : P in Points(Sing) ];

O:=K![0,0,0,1];
Remove(~nodes, Index(nodes,O)) ;

print nodes;
Q2:= nodes[2];

// Find all planes that go through the two nodes with a given j-invariant.
j, C, ysq := FindJInvariantFunction(K,O,Q2,ysq);
fields, js := jInvariantMatch(j,jInvariant(X1));
fields, js := PolredjInvariants(fields,js);

// Plug mu into the equation for the curve
fld<nu> := fields[1];
j := js[1];
eqn := DefiningEquation(C);
eqn := EvaluateField(eqn,[j]);
ysq := EvaluateField(Numerator(ysq),[j]);
C := Curve(AffineSpace(fld,2),eqn);
KC := FunctionField(C);
S2_aff := PolynomialRing(fld,2);

// Map ysq into the function field of C
h_crv := hom< S2_aff -> KC | [KC.1, KC.2]>;
ysq := h_crv(ysq);
// I think this is the first place where we can compute the divisor of ysq
// Then we could just push the points along instead of the function
// Pushforward is also defined for divisors on curves if that's easier

E,ysq,lambda :=CurveAndMapToLegendreForm(C,ysq);
KE<x,y> := FunctionField(E);
K:=BaseRing(E);
print E;

D := Divisor(ysq); // can we just base change the divisor of ysq_leg_al?
pts := Support(D);
// this is slow; might be worth computing the points beforehand and then pushing them forward along these isomorphisms
pts := pts[1..4]; // why the first 4 points?
pts := [*RepresentativePoint(pt) : pt in pts*];
lines, Q := HyperellipticLines(E,pts);
lines := [KE!line : line in lines];

// make function with divisor pts[1] + pts[2] + pts[3] + pts[4] - 2*(Q) - 2*(oo)
v := KE!(lines[1]*lines[2]/lines[3]);
D_v := Divisor(lines[1]) + Divisor(lines[2]) - Divisor(lines[3]);
// since Divisor(ysq_3) has mults 1, 1, 3, 3, 2, -4, we can use v to create a function
// whose divisor D has all even mults, so D/2 has some hope of being principal

// find the function corresponding to the correct genus 3 curve
// original function v might be off by a 2-torsion point
// this is slow: computing IsPrincipal takes a while, I think
// I think Jeroen might've said we could get rid of the IsPrincipal if we made another base extension...
print "Finding function that yields correct curve...";
//KE<x,y> := FunctionField(E);
vs := [v, v/x, v/(x-1), v/(x-K!lambda)];
oo := E!0;
for i := 1 to #vs do
  t0 := Cputime();
  D_diff := Divisor(vs[i]) - D;
  D_div2 := D_diff div 2;
  princ_bool2, gen := IsPrincipal(D_div2);
  t1 := Cputime();
  printf "i = %o took %o secs\n", i, t1 - t0;
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
Ts := [E!0, E![0,0], E![1,0], E![lambda,0]];
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

// find new curve using Riemann-Roch space
RR, mp_RR := RiemannRochSpace(4*(Divisor(Q) + Divisor(T)));
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
RUV<U,V> := PolynomialRing(K,2);
mons := [U^i : i in [0..4]] cat [U^i*V : i in [0..2]];
F := V^2;
for i := 1 to #mons do
  F -:= (RUV!vsq_cs[i])*mons[i];
end for;
F := F/LeadingCoefficient(F);
X1_final := Curve(AffineSpace(BaseRing(RUV),2), F);
A2<s,t> := Ambient(X1_final);

// now make genus 3 cover
G := Evaluate(F,[U,V^2]);
X3 := Curve(Ambient(X1_final),G);
Genus(X3);
I, W := DixmierOhnoInvariants(G);
invs := WPSNormalize(W,I);
print invs;
return invs;
end function;

