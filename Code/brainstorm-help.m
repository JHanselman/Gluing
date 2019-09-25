function CurveAndAmbientFunctionFromPlane(F, H, ysq)

S4<x1,x2,x3,x4> := Parent(F);
P3 := ProjectiveSpace(S4);
S:= Scheme(P3, [F,H]);
S:= ReducedSubscheme(S);
E:= Curve(S);

print ysq;
ysq := Numerator(ysq);
S5<u1,u2,u3,u4,y> := Parent(ysq);
num := &+[ MonomialCoefficient(ysq, mon)*mon : mon in Monomials(ysq) | Exponents(mon)[5] eq 0 ];
den := -&+[ MonomialCoefficient(ysq, mon)*mon : mon in Monomials(ysq) | Exponents(mon)[5] ne 0 ];
h := hom< S5 -> S4 | [ x1,x2,x3,x4,x1 ] >;
f := h(num)/h(den);
return E, f;

end function;


function DesingularizedCurveAndAmbientFunctionAndPoints(C, f)
/* Kijk uit met mogelijke uitbreiding bij singuliere punten! */

  S4 := CoordinateRing(Ambient(C));
  num := Numerator(f); den := Denominator(f);

  CAff := AffinePatch(C,1);
  R3<x1, y1, z1> := CoordinateRing(Ambient(CAff));
  KK := BaseRing(R3);
  h := hom< S4 -> R3 | [ x1,y1,z1,1 ] >;
  num := h(num); den := h(den);

  Sing := SingularSubscheme(CAff);
  nodes := [ C ! P : P in Points(Sing) ];
  node1:=nodes[1];
  node2:=nodes[2];

  R4<x1,y1,z1,t1> := PolynomialRing(KK, 4);
  A4 := AffineSpace(R4);
  h := hom< R3 -> R4 | [ x1, y1,z1 ] >;
  f1 := h(DefiningEquations(CAff)[1]);
  f2 :=h(DefiningEquations(CAff)[2]);
  B1 := Scheme(A4, [ f1,f2, (y1-nodes[1][2] - t1*(x1 -nodes[1][1])) ]);
  Is := IrreducibleComponents(B1);
  for I in Is do
    if Genus(Curve(ReducedSubscheme(I))) ne 0 then
      B1 := I;
    end if;
  end for;
  num := h(num); den := h(den);

return B1, num/den;

end function;

// Pts1 := [ P : P in Points(ReducedSubscheme(Scheme(B2, [x1-nodes[1][1], y1-nodes[1][2]]))) ];

function DesingularizedCurveAndAmbientFunctionAndPoints_old(C, f)
/* Kijk uit met mogelijke uitbreiding bij singuliere punten! */

  S4 := CoordinateRing(Ambient(C));
  num := Numerator(f); den := Denominator(f);

  CAff := AffinePatch(C,1);
  R3<x1, y1, z1> := CoordinateRing(Ambient(CAff));
  KK := BaseRing(R3);
  h := hom< S4 -> R3 | [ x1,y1,z1,1 ] >;
  num := h(num); den := h(den);

  Sing := SingularSubscheme(CAff);
  nodes := [ C ! P : P in Points(Sing) ];
  node1:=nodes[1];
  node2:=nodes[2];

  R4<x1,y1,z1,t1> := PolynomialRing(KK, 4);
  A4 := AffineSpace(R4);
  h := hom< R3 -> R4 | [ x1, y1,z1 ] >;
  f1 := h(DefiningEquations(CAff)[1]);
  f2 :=h(DefiningEquations(CAff)[2]);
  B1 := Scheme(A4, [ f1,f2, (y1-nodes[1][2] - t1*(x1 -nodes[1][1])) ]);
  Is := IrreducibleComponents(B1);
  for I in Is do
      if Genus(Curve(ReducedSubscheme(I))) ne 0 then
          B1 := I;
      end if;
  end for;
  num := h(num); den := h(den);

  R5<x2,y2,z2,t2,u2> := PolynomialRing(KK, 5);
  A5 := AffineSpace(R5);
  h := hom< R4 -> R5 | [ x2, y2, z2, t2 ] >;
  fs := [ h(f) : f in DefiningEquations(B1) ];
  B2 := Scheme(A5, fs cat [ (y2 - nodes[2][2]) - u2*(x2 - nodes[2][1]) ]);
  Is := IrreducibleComponents(B2);
  for I in Is do
      if Genus(Curve(ReducedSubscheme(I))) ne 0 then
          B2 := I;
      end if;
  end for;
  num := h(num); den := h(den);

  Pts1 := [ P : P in Points(ReducedSubscheme(Scheme(B2, [x2-nodes[1][1], y2-nodes[1][2]]))) ];
  Pts2 := [ P : P in Points(ReducedSubscheme(Scheme(B2, [x2-nodes[2][1], y2-nodes[2][2]]))) ];
  Pts := Pts1 cat Pts2;

  return B2, num/den, Pts;

end function;


function EllipticCurveAndAmbientFunctionAndPoints(Ct, ft, Ps)

R := CoordinateRing(Ambient(Ct));
CP := Curve(ProjectiveClosure(Ct));
Ps := [ CP ! P : P in Ps ];

S := CoordinateRing(Ambient(CP)); r := Rank(S);
h := hom< R -> S | [ S.i : i in [1..(r - 1)] ] >;
num := Numerator(ft); den := Denominator(ft);
num := Homogenization(h(num), S.r);
den := Homogenization(h(den), S.r);
ft := num/den;
K := FunctionField(CP);
ft := K ! ft;

ds := [ Maximum([ Degree(MinimalPolynomial(c)) : c in Eltseq(P) ])  : P in Ps ];
d, i := Minimum(ds);
P := Ps[i];
Et, phi := EllipticCurve(CP, P);

Ps := [ phi(P) : P in Ps ];
ft := Pushforward(phi, ft);

return Et, ft, Ps;

end function;

function DoubleCover(Et,g)

R := CoordinateRing(Ambient(Et));
r:=Rank(R);
S := Parent(Numerator(g));

num := Numerator(g);
den := Denominator(g);

R2 := PolynomialRing(BaseRing(R),r+1);
h := hom<R -> R2 |[R2.i : i in [1..r]]>;
h2 := hom<S -> R2 | [R2.1,R2.2]>;
X3 := Scheme(ProjectiveSpace(R2),[h(equ) : equ in DefiningEquations(Et)] cat [Homogenization((R2.(r+1)^2*h2(den)-h2(num)),R2.3)]);

Irr:=IrreducibleComponents(X3);

for comp in Irr do
    C := ReducedSubscheme(comp);
    C := Curve(C);
    if Genus(C) eq 3 then
        phi:=CanonicalMap(C);
        D := phi(C);
        if Genus(D) eq 3 then
           return D;
	else
	    return Error;
        end if;
    end if;
end for;

end function;
