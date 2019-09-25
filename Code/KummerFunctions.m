// Change to point to necessary packages if running on different machine.
AttachSpec("/Users/samschiavone/github/quartic_reconstruction/package/spec");
AttachSpec("/Users/samschiavone/github/quartic_reconstruction/g3twists_v2-0/spec");

function MultivariableToSingleVariablePolynomial(f)
  // Input: A polynomial of type RingMPolElt, but which only involves one of the variables
  // Output: The same polynomial, but now of type RingUPolElt
  K := BaseRing(Parent(f));
  cs := Coefficients(f);
  cs := Reverse(cs);
  R<u> := PolynomialRing(K);
  f_new := R!cs;
  return f_new;
end function;

function HomogeneousPartOfDegree(f,d)
  cs, mons:= CoefficientsAndMonomials(f);
  f_d := Parent(f)!0;
  for i := 1 to #cs do
    if Degree(mons[i]) eq d then
      f_d +:= cs[i]*mons[i];
    end if;
  end for;
  return f_d;
end function;

/*
function MobiusTransformationFixed(z1,z2,z3)
  // Output: Mobius transformation mapping z1, z2, z3 to 0, 1, oo, respectively.
  K! := Parent(z1);

end function;
*/

function MakeLine(C,P1,P2)
  // C must be a plane curve
  if IsProjective(C) then
    A<x,y> := CoordinateRing(Ambient(AffinePatch(C,1)));
  else
    assert IsAffine(C);
    A<x,y> := CoordinateRing(Ambient(C));
  end if;
  return ((P2[1] - P1[1])*(y - P1[2]) - (P2[2] - P1[2])*(x - P1[1]));
end function;

function HyperellipticLines(E,Ps)
  A<x,y> := CoordinateRing(Ambient(AffinePatch(E,1)));
  // make lines
  line1 := MakeLine(E,Ps[1],Ps[2]);
  line2 := MakeLine(E,Ps[3],Ps[4]);
  Q0 := -(Ps[3] + Ps[4]);
  Q := -(Q0/2);
  line3 := MakeLine(E,Q0,Q);
  //line4 := MakeLine(E,Q,-Q);
  //line5 := MakeLine(E,-Q,-Q_2);
  lines := [line1, line2, line3];
  return lines, Q; 
end function;

/*
function FunctionFieldToPolynomial(f)
  
end function;

function MakeHyperellipticCurve(E,num,den);

end function;
*/

/*
function HyperellipticDivisor(E,Ps)
  A<x,y> := CoordinateRing(Ambient(AffinePatch(E,1)));
  KE := FunctionField(E);
  x := KE!x;
  y := KE!y;
  // make lines
  line1 := MakeLine(E,Ps[1],Ps[2]);
  line2 := MakeLine(E,Ps[3],Ps[4]);
  Q1 := -(Ps[1] + Ps[2]);
  Q2 := -(Ps[3] + Ps[4]);
  line3 := MakeLine(E,Q1,Q2);
  D := -(Q1 + Q2);
  D_2 := -D/2;
  line4 := MakeLine(E,D,D_2);
  for el in [line1,line2,line3,line4] do
    print Support(Divisor(el));
  end for;
  x0 := D_2[1];
  print Support(Divisor(x-x0));
  f := line1*line2*line4/(line3*(x - x0)^2);
  return f, line1, line2, line3, line4;  
end function;
*/

function CantorEquations(X);
/* Gives the equations in the description a (x) = 0, y = b (x)
 * May not use usual parameter if uniformizer differs */
// see Cantor's Computing in the Jacobian of a Hyperelliptic Curve for explanation of a(x), b(x)

g := Genus(X);
f := DefiningEquations(AffinePatch(X, 1))[1];
F := BaseRing(X);
S := PolynomialRing(F, 2*g);
T<t> := PolynomialRing(S);
/* Names:
 * a1 is trace term before t^(g - 1), a_g is norm term before t^0,
 * b1 is term before t^(g - 1), bg is term before t^0 */
varnames := [ Sprintf("a%o", i) : i in [1..g] ] cat [ Sprintf("b%o", i) : i in [1..g] ];
AssignNames(~S, varnames);

/* Start with trace and end with norm */
canpol := t^g + &+[ S.i * t^(g - i) : i in [1..g] ];
print canpol;
substpol := &+[ S.(g + i) * t^(g - i) : i in [1..g] ];
print substpol;
P := [t, substpol];
print f;
print P;
print Evaluate(f,P);
eqpol := Evaluate(f, P) mod canpol;
print eqpol;
return Coefficients(eqpol);

end function;


function EvaluateGen(pol, vals)

if #vals eq 1 then
    return Evaluate(pol, vals[1]);
end if;
return Evaluate(pol, vals);

end function;


function MonomialGen(R, exps);

if #exps eq 1 then
    return R.1^exps[1];
end if;
return Monomial(R, exps);

end function;


function EvaluateField(f, vals)

R := Parent(f);
n := Rank(R);
K := BaseRing(R);


K0 := Parent(vals[1]);
R0 := PolynomialRing(K0, n);

f0 := R0 ! 0;
for mon in Monomials(f) do
    coeff := MonomialCoefficient(f, mon);
    num := Numerator(coeff);
    den := Denominator(coeff);
    num0 := EvaluateGen(num, vals);
    den0 := EvaluateGen(den, vals);
    coeff0 := num0/den0;
    mon0 := MonomialGen(R0, Exponents(mon));
    f0 +:= coeff0*mon0;
end for;
return f0;

end function;

function CalculateKummer(f)

//Calculating the Jacobian, the Kummer and the map to the Kummer
X:= HyperellipticCurve(f);

FFp:= BaseRing(X);
jeqs := CantorEquations(X);

//Calculating the equations for the Kummer surface
// See section 3 of Mueller's Explicit Kummer surface formulas for arbitrary characteristic
R<a1,a2,b1,b2> := Parent(jeqs[1]);
f0 := Coefficient(f, 0);
f1 := Coefficient(f, 1);
f2 := Coefficient(f, 2);
f3 := Coefficient(f, 3);
f4 := Coefficient(f, 4);
f5 := Coefficient(f, 5);
f6 := Coefficient(f, 6);

tr := -a1;
nm := a2;

F0 := 2*f0 + f1*tr + 2*f2*nm + f3*tr*nm + 2*f4*nm^2 + f5*tr*nm^2 + 2*f6*nm^3;
kappa1 := 1;
kappa2 := tr;
kappa3 := nm;
kappa4 := (F0 - 2*(b1^2*nm + b1*b2*tr + b2^2))/(tr^2 - 4*nm);

K2 := kappa2^2 - 4*kappa1*kappa3;
K1 := -4*kappa1^3*f0 - 2*kappa1^2*kappa2*f1 - 4*kappa1^2*kappa3*f2 - 2*kappa1*kappa2*kappa3* f3 - 4*kappa1*kappa3^2*f4 -2*kappa2*kappa3^2*f5 - 4*kappa3^3*f6;

K0 := -4*kappa1^4*f0*f2 + kappa1^4*f1^2 - 4*kappa1^3*kappa2*f0*f3 - 2*kappa1^3*kappa3*f1*    f3 - 4*kappa1^2*kappa2^2*f0*f4 + 4*kappa1^2*kappa2*kappa3*f0*f5 - 4*kappa1^2*kappa2*kappa3*f1*f4 - 4*kappa1^2*kappa3^2*f0*f6 + 2*kappa1^2*kappa3^2*f1*f5 -4*kappa1^2*kappa3^2*f2*f4 +   kappa1^2*kappa3^2*f3^2 - 4*kappa1*kappa2^3*f0*f5 + 8*kappa1*kappa2^2*kappa3*f0*f6 - 4*kappa1*kappa2^2*kappa3*f1*f5 + 4*kappa1*kappa2*kappa3^2*f1*f6 - 4*kappa1*kappa2*kappa3^2*f2*f5 - 2* kappa1*kappa3^3*f3*f5 - 4*kappa2^4*f0*f6 - 4*kappa2^3*kappa3*f1*f6 - 4*kappa2^2*kappa3^2*f2* f6 -4*kappa2*kappa3^3*f3*f6 - 4*kappa3^4*f4*f6 + kappa3^4*f5^2;
K := K2*kappa4^2 + K1*kappa4 + K0;

num := Numerator(K);
I := ideal<R | jeqs>;
print "Maps to Kummer well-defined?";
print num in I;

A := AffineSpace(R);
print A;
J := Scheme(A, jeqs);
print "Equation for Jacobian:";
print J;

//Define the Kummer as a scheme.
P3<x1,x2,x3,x4> := ProjectiveSpace(FFp, 3);
K2 := x2^2 - 4*x1*x3;
K1 := -4*x1^3*f0 - 2*x1^2*x2*f1 - 4*x1^2*x3*f2 - 2*x1*x2*x3*f3 - 4*x1*x3^2*f4 -2*x2*x3^2*f5 - 4*x3^3*f6;
K0 := -4*x1^4*f0*f2 + x1^4*f1^2 - 4*x1^3*x2*f0*f3 - 2*x1^3*x3*f1*f3 - 4*x1^2*x2^2*f0*f4 + 4*x1^2*x2*x3*f0*f5 - 4*x1^2*x2*x3*f1*f4 - 4*x1^2*x3^2*f0*f6 + 2*x1^2*x3^2*f1*f5 -4*x1^2*x3^2*f2*f4 + x1^2*x3^2*f3^2 - 4*x1*x2^3*f0*f5 + 8*x1*x2^2*x3*f0*f6 - 4*x1*x2^2*x3*f1*f5 + 4*x1*x2*x3^2*f1*f6 - 4*x1*x2*x3^2*f2*f5 - 2*x1*x3^3*f3*f5 - 4*x2^4*f0*f6 - 4*x2^3*x3*f1*f6 - 4*x2^2* x3^2*f2*f6 -4*x2*x3^3*f3*f6 - 4*x3^4*f4*f6 + x3^4*f5^2;
F := K2*x4^2 + K1*x4 + K0;
print F;
print "Equation for Kummer:";
K := Scheme(P3, F);
print K;


//Express b_1^2 and b1*b2 in terms of a1,a2 and b2^2.


b2sq:=jeqs[1]+b2^2;
b1b2:=jeqs[2]/2+b1*b2;
b1sqcoeff:= Coefficient(b2sq+tr*b1b2,b1,2);

temp := R!(kappa4*(tr^2-4*nm))-F0;
temp := -temp/2 -(b2sq+tr*b1b2-b1sqcoeff*b1^2);


KK<a1,a2,b1,b2>:= FieldOfFractions(R);
b1sq:= temp/(nm+b1sqcoeff);

num := Numerator(b1sq);
den := Denominator(b1sq);

print "Test relation for b1^2";
print (R ! (den*b1^2 - num)) in I;

SF3<x1,x2,x3,x4> := PolynomialRing(FFp,4);
S3<x1,x2,x3,x4>:=FieldOfFractions(SF3);
h:= hom<KK -> S3 |[-x2,x3,0,0]>;


func := (x4*h(tr^2-4*nm))-h(F0);
func := -func/2 -h(b2sq+tr*b1b2);
func:=SF3!(func/h(nm+b1sqcoeff));

deg := TotalDegree(func);
homfunc:=0;
for term in Terms(func) do
  d:= deg - TotalDegree(term);
  homfunc+:=term*x1^d;
end for;

print func;
print homfunc;

return K,homfunc;

end function;


function CalculateKummer_old(f)

//Calculating the Jacobian, the Kummer and the map to the Kummer
X:= HyperellipticCurve(f);
FFp:= BaseRing(X);
jeqs := CantorEquations(X);

//Calculating the equations for the Kummer surface
R<a1,a2,b1,b2> := Parent(jeqs[1]);
f0 := Coefficient(f, 0);
f1 := Coefficient(f, 1);
f2 := Coefficient(f, 2);
f3 := Coefficient(f, 3);
f4 := Coefficient(f, 4);
f5 := Coefficient(f, 5);
f6 := Coefficient(f, 6);

tr := -a1;
nm := a2;

F0 := 2*f0 + f1*tr + 2*f2*nm + f3*tr*nm + 2*f4*nm^2 + f5*tr*nm^2 + 2*f6*nm^3;
kappa1 := 1;
kappa2 := tr;
kappa3 := nm;
kappa4 := (F0 - 2*(b1^2*nm + b1*b2*tr + b2^2))/(tr^2 - 4*nm);

K2 := kappa2^2 - 4*kappa1*kappa3;
K1 := -4*kappa1^3*f0 - 2*kappa1^2*kappa2*f1 - 4*kappa1^2*kappa3*f2 - 2*kappa1*kappa2*kappa3* f3 - 4*kappa1*kappa3^2*f4 -2*kappa2*kappa3^2*f5 - 4*kappa3^3*f6;

K0 := -4*kappa1^4*f0*f2 + kappa1^4*f1^2 - 4*kappa1^3*kappa2*f0*f3 - 2*kappa1^3*kappa3*f1*    f3 - 4*kappa1^2*kappa2^2*f0*f4 + 4*kappa1^2*kappa2*kappa3*f0*f5 - 4*kappa1^2*kappa2*kappa3*f1*f4 - 4*kappa1^2*kappa3^2*f0*f6 + 2*kappa1^2*kappa3^2*f1*f5 -4*kappa1^2*kappa3^2*f2*f4 +   kappa1^2*kappa3^2*f3^2 - 4*kappa1*kappa2^3*f0*f5 + 8*kappa1*kappa2^2*kappa3*f0*f6 - 4*kappa1*kappa2^2*kappa3*f1*f5 + 4*kappa1*kappa2*kappa3^2*f1*f6 - 4*kappa1*kappa2*kappa3^2*f2*f5 - 2* kappa1*kappa3^3*f3*f5 - 4*kappa2^4*f0*f6 - 4*kappa2^3*kappa3*f1*f6 - 4*kappa2^2*kappa3^2*f2* f6 -4*kappa2*kappa3^3*f3*f6 - 4*kappa3^4*f4*f6 + kappa3^4*f5^2;
K := K2*kappa4^2 + K1*kappa4 + K0;

num := Numerator(K);
I := ideal<R | jeqs>;
print "Maps to Kummer well-defined?";
print num in I;

A := AffineSpace(R);
print A;
J := Scheme(A, jeqs);
print "Equation for Jacobian:";
print J;

//Define the Kummer as a scheme.
P3<x1,x2,x3,x4> := ProjectiveSpace(FFp, 3);
K2 := x2^2 - 4*x1*x3;
K1 := -4*x1^3*f0 - 2*x1^2*x2*f1 - 4*x1^2*x3*f2 - 2*x1*x2*x3*f3 - 4*x1*x3^2*f4 -2*x2*x3^2*f5 - 4*x3^3*f6;
K0 := -4*x1^4*f0*f2 + x1^4*f1^2 - 4*x1^3*x2*f0*f3 - 2*x1^3*x3*f1*f3 - 4*x1^2*x2^2*f0*f4 + 4*x1^2*x2*x3*f0*f5 - 4*x1^2*x2*x3*f1*f4 - 4*x1^2*x3^2*f0*f6 + 2*x1^2*x3^2*f1*f5 -4*x1^2*x3^2*f2*f4 + x1^2*x3^2*f3^2 - 4*x1*x2^3*f0*f5 + 8*x1*x2^2*x3*f0*f6 - 4*x1*x2^2*x3*f1*f5 + 4*x1*x2*x3^2*f1*f6 - 4*x1*x2*x3^2*f2*f5 - 2*x1*x3^3*f3*f5 - 4*x2^4*f0*f6 - 4*x2^3*x3*f1*f6 - 4*x2^2* x3^2*f2*f6 -4*x2*x3^3*f3*f6 - 4*x3^4*f4*f6 + x3^4*f5^2;
F := K2*x4^2 + K1*x4 + K0;
print F;
print "Equation for Kummer:";
K := Scheme(P3, F);
print K;


//Express b_1^2 and b1*b2 in terms of a1,a2 and b2^2.


b2sq:=jeqs[1]+b2^2;
b1b2:=jeqs[2]/2+b1*b2;
b1sqcoeff:= Coefficient(b2sq+tr*b1b2,b1,2);

temp := R!(kappa4*(tr^2-4*nm))-F0;
temp := -temp/2 -(b2sq+tr*b1b2-b1sqcoeff*b1^2);


KK<a1,a2,b1,b2>:= FieldOfFractions(R);
b1sq:= temp/(nm+b1sqcoeff);

num := Numerator(b1sq);
den := Denominator(b1sq);

print "Test relation for b1^2";
print (R ! (den*b1^2 - num)) in I;

SF3<x1,x2,x3,x4,y> := PolynomialRing(FFp,5);
S3<x1,x2,x3,x4,y>:=FieldOfFractions(SF3);
h:= hom<KK -> S3 |[-x2,x3,0,0]>;


func := (x4*h(tr^2-4*nm))-h(F0);
func := -func/2 -h(b2sq+tr*b1b2);
func:=SF3!(func/h(nm+b1sqcoeff)-y^2);

deg := TotalDegree(func);
homfunc:=0;
for term in Terms(func) do
  d:= deg - TotalDegree(term);
  homfunc+:=term*x1^d;
end for;

print func;
print homfunc;

return K,homfunc;

end function;

function InterpolateJInvariant(f)

  R := Parent(f);
  K<lambda> := BaseRing(R);
  FFp := BaseRing(K);
  
  f_ev := EvaluateField(f,[FFp!2]);

  
  R3<x,y,z> := Parent(f_ev);
  P3<x,y,z> := ProjectiveSpace(R3);
  print f_ev;
  C := Scheme(P3,f_ev);
  C := Curve(C);
  IsReduced(C);
  IsIrreducible(C);
  T<x3> := PolynomialRing(FFp);
  f_temp := Evaluate(f_ev, [1,2,x3]);
  M := FieldOfFractions(quo< T | f_temp >);
  CM := ChangeRing(C, M);
  //print CM;
  EM := EllipticCurve(CM, CM ! [1,2,M.1]);
 // print EM;
  j := jInvariant(EM);
 // print j;
  return C;
return 0;

end function;

function CrossRatio(z1,z2,z3,z4)
  // Compute the cross ratio of the four numbers z1, z2, z3, z4
  return (z3-z1)*(z4-z2)/((z3-z2)*(z4-z1));
end function;

function jInvariantFromLegendre(lambda)
  // Given the Legendre lambda invariant, compute the j-invariant of the corresponding elliptic curve
  return 2^8*(lambda^2 - lambda + 1)^3/(lambda^2*(lambda-1)^2);
end function;

function ComputeBranchPoints(C)
  // Given the elliptic curve C, given as a plane quartic with two nodes, one at (0,0), compute the branch points of the map y/x, taking a pencil of lines through (0,0)
  // Input: Elliptic curve C
  // Output: The branch points of y/x on C

  QQ := Rationals();
  A := Ambient(C);
  K := BaseRing(A);
  R<x,y> := CoordinateRing(A); 
  KC<t> := FunctionField(C);
  f := DefiningEquation(C);
  fx := Derivative(f,1);
  fy := Derivative(f,2);
  der := x*fx + y*fy;
  //res := Resultant(f,der,y);
  QQ<u> := PolynomialRing(QQ);
  Ram := Scheme(A, [f, der]);
  print Points(Ram);
  ram_pts := Points(Ram) diff SingularPoints(Ram);
  branch_pts := [pt[2]/pt[1] : pt in ram_pts];
  return branch_pts;
end function;  
  

function FindjInvariantForParameter(C)
  // Wrapper
  printf "Computing ramification points of slope map\n";
  pts := ComputeBranchPoints(C);
  printf "Computing j-invariant\n";
  lambda := CrossRatio(pts[1],pts[2],pts[3],pts[4]); 
  j := jInvariantFromLegendre(lambda);
  return j;
end function;

function FindPlanes(K,E,Q1,Q2,ysq)
	
  FFp := BaseRing(K);
  RL := PolynomialRing(FFp);
  L<mu> := FieldOfFractions(RL);

  KummerEquation:= DefiningEquation(K);

  S:=[];
  for i:=1 to 4 do
      Append(~S, Q1[i]);
  end for;
  for i:=1 to 4 do
      Append(~S, Q2[i]);
  end for;

  M:=Matrix(L,2,4,S);
  Ker:= NullspaceOfTranspose(M);

  // We find a family of planes depending on L.1 that go through the pair of singular points.
  H:= Basis(Ker)[1]-mu*Basis(Ker)[2];
  print Parent(KummerEquation);
  S3<x1,x2,x3,x4>:= Parent(KummerEquation);
  S2<x1,x2,x3> := PolynomialRing(L,3);

  P2 := ProjectiveSpace(S2);
  if H[1] ne 0 then
      h := hom<S3 -> S2 | [ 1/H[1]*(-H[2]*x1-H[3]*x2-H[4]*x3), x1, x2, x3 ]>;
  elif H[2] ne 0 then
      h := hom<S3 -> S2 | [ x1,1/H[2]*(-H[1]*x1-H[3]*x2-H[4]*x3), x2, x3 ]>;
  elif H[3] ne 0 then
      h := hom<S3 -> S2 | [x1,x2, 1/H[3]*(-H[1]*x1-H[2]*x2-H[4]*x3), x3 ]>;
  end if;

  // intersect Kummer with the plane
  H_K := h(KummerEquation);

  C := Curve(Scheme(P2, H_K));
  ysq := h(Numerator(ysq));
  C := AffinePatch(C,1);
  KC := FunctionField(C);
  S2_aff := PolynomialRing(L,2);
  h_aff := hom<S2 -> S2_aff | [S2_aff.1, S2_aff.2, 1]>;
  ysq := h_aff(ysq);
  h_crv := hom< S2_aff -> KC | [KC.1, KC.2]>;
  ysq := h_crv(ysq);
  //ysq := KC!ysq;
  //R2<xC, yC> := CoordinateRing(Ambient(C));
  
  

  Sing := SingularSubscheme(C);
  nodes2 := [ C ! P : P in Points(Sing) ];
	    
	print "The curve has singular points in:";
	print nodes2;
        
	print "The curve (parametrized by mu) is:";
	print C;

  //C := ProjectiveClosure(C);
  //F2 := DefiningEquations(C)[1];
  //S<x1,x2,x3> := Parent(F2);

  //return InterpolateJInvariant(F2);
  

  ///Calculate the j-invariant of the family of elliptic curves that go through the singular points
  //T<x3> := PolynomialRing(L);
  //f := Evaluate(F2, [1,2,x3]);
  //M := FieldOfFractions(quo< T | f >);
  //CM := ChangeRing(C, M);
  //print CM;
  // TODO: The following is very slow, probably b/c Magma trying to compute Weierstrass form. Instead compute j-invariant directly
  
  //EM := EllipticCurve(CM, CM ! [1,2,M.1]);
  //printf "The elliptic curve is, %o\n\n", EM;
  j := FindjInvariantForParameter(C);
  printf "with j-invariant %o\n", j;

  // Find all the planes whose j-invariant is equal to the j-invariant of the elliptic  curve E
  // ...this looks unfinished: currently this is done in brainstorm.m instead
  value := jInvariant(E);
  numj := Numerator(L ! (j - value));

  //Redefine everything over the splitting field of j(E).
  /*
  newK:= SplittingField(numj);
  roots:= Roots(numj, newK);
  */
	/*	
	Planes:=[];
	for r in roots do
                Append(~Planes,Evaluate(H, r[1]));
	end for;
    
	return Planes;
  */
  return j, C, ysq;
end function;


// OLD

/*
function DefineSlopeMap(C)
  A := Ambient(C);
  K := BaseRing(A);
  R<x,y> := CoordinateRing(A); 
  KC<t> := FunctionField(C);
  proj := KC!y/KC!x;
  return proj;
end function;

function BaseChangeSlopeMap(proj,F)
  KC := Parent(proj);
  C := Curve(KC);
  C_F := ChangeRing(C, F);
  C_F_aff := AffinePatch(C_F,1);
  KC_F<t> := FunctionField(C_F);
  A_F := Ambient(C_F_aff);
  R<x,y> := CoordinateRing(A_F); 
  proj_F := KC_F!y/KC_F!x;
  return proj_F;
end function;

function ComputeRamificationPointsOld(proj)
  pts, vals := Support(Divisor(Differential(proj)));
  pts_up := [* *];
  for i := 1 to #vals do
    if vals[i] gt 0 then
      Append(~pts_up, RepresentativePoint(pts[i]));
    end if;
  end for;
  pts := [*proj(pt) : pt in pts_up*];
  return pts;
end function;

function FindjInvariantForParameter(C)
  printf "Computing ramification points of slope map\n";
  pts := ComputeBranchPoints(C);
  printf "Making base change to field of definition of branch points\n";
  flds := [Parent(pt) : pt in pts];
  F := flds[1];
  for i := 2 to #flds do
    F<nu> := Compositum(F,flds[i]);
  end for;
  if Degree(F) gt 1 then
    proj := BaseChangeSlopeMap(proj,F);
    pts := ComputeRamificationPoints(proj);
  end if;
  printf "Computing j-invariant\n";
  lambda := CrossRatio(pts[1],pts[2],pts[3],pts[4]); 
  j := jInvariantFromLegendre(lambda);
  return j;
end function;

*/
