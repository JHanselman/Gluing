// Change to point to necessary packages if running on different machine.
//AttachSpec("/Users/samschiavone/github/quartic_reconstruction/package/spec");
//AttachSpec("/Users/samschiavone/github/quartic_reconstruction/g3twists_v2-0/spec");

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
