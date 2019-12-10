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

  j := FindjInvariantForParameter(C);
  printf "with j-invariant %o\n", j;

  return j, C, ysq;
end function;

function jInvariantMatch(j,j0)
  // Find all the planes whose j-invariant is equal to j0
  j_num := Numerator(j - j0);
  facts := Factorization(j_num);
  facts := [fact[1] : fact in facts];
  fields := [* *];
  for poly in facts do
    if Degree(poly) eq 1 then
      Append(~fields, Rationals());
      // should really record the j, too...
    else
      Append(~fields,NumberField(poly));
    end if;
  end for;
  return fields;
end function;

function PolredjInvariants(fields)
  fields_red := [* *];
  js_red := [* *];
  for K in fields do
    K_red, mp := Polredbestabs(K);
    Append(~fields_red, K_red);
    Append(~js_red, mp(K.1));
  end for;
  return fields_red, js_red;
end function;

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
