load "KummerFunctions.m";
load "brainstorm-help.m";
load "FunctionFinder.m";
SetSeed(1);


//Define the base field and the function field
//FFp := FiniteField(37);
FFp := Rationals();
RL := PolynomialRing(FFp);
L := FieldOfFractions(RL);

//Define the curves we want to glue

T<x,y> :=PolynomialRing(FFp,2);

//The elliptic curve
g := (x - 1)*x*(x + 1)*(x + 2);
g := g-y^2;
A2:= AffineSpace(T);
X1:=Scheme(A2,g);
X1:=Curve(X1);
X1:=ProjectiveClosure(X1);
X1:=EllipticCurve(X1);

//The hyperelliptic curve
//Roots need to be rational for Kummer to have 16 distinct points?
R<x> := PolynomialRing(FFp);
//f := (x + 3)*(x + 1)*x*(x - 1)*(x - 3)*(x - 4);
f := (x-5)*(x+2)*(x-31)*(x+15)*x*(x+1);
f := (x-5)*(x+2)*(x-31)*(x+15)*x*(x-4);

/* Eq of divisor:
    x^2 + a1 x + a2 = 0
    y = b1 x + b2
*/

K,ysq:=CalculateKummer(f);
F:= DefiningEquation(K);


S3<x1,x2,x3,x4> := PolynomialRing(L,4);

Sing := SingularSubscheme(K);
nodes := [ P : P in Points(Sing) ];

O:=K![0,0,0,1];
Remove(~nodes, Index(nodes,O)) ;

Q2:= nodes[1];

//Find all planes that go through the two nodes with a given j-invariant.
j, value, H:=FindPlanes(K,X1,O,Q2);
j_num := Numerator(j - value);
facts := Factorization(j_num);
facts := [fact[1] : fact in facts];
fields := [* *];
for poly in facts do
  if Degree(poly) eq 1 then
    Append(~fields, Rationals());
  else
    Append(~fields,OptimizedRepresentation(NumberField(poly)));
  end if;
end for;

plane := Evaluate(H,Roots(facts[1],fields[1])[1][1]);
//Equation for the Kummer
K_eq := S3 ! F;        
print plane;
KK:=BaseRing(plane);

S3<x1,x2,x3,x4>:=PolynomialRing(KK,4);
P3:= ProjectiveSpace(S3);


//Equation for Kummer
F_eq := S3!F;

//Equation for the plane.
H:=plane[1];
H_eq:= x1*H[1]+x2*H[2]+x3*H[3]+x4*H[4];


S:= Scheme(ProjectiveSpace(S3),[S3!F, H_eq]);
S:= ReducedSubscheme(S);
C:= Curve(S);
if Genus(C) eq 1 then
  //E:= EllipticCurve(C);
  //print "j(H intersect K) equal to j(X1)?";
  //print jInvariant(X1) eq jInvariant(E);

  //Map equation for y^2=b2^2 to S4.
  ysq:= Numerator(ysq);
  S4<x1,x2,x3,x4,y> := ChangeRing(Parent(ysq),KK);
  ysq := S4!ysq;
  h := hom<S3 -> S4|[x1,x2,x3,x4]>;

  print h(K_eq);
  print h(H_eq);
  print ysq;

  C, f := CurveAndAmbientFunctionFromPlane(F_eq, H_eq, ysq);
  KC := FunctionField(C);
  f_old := f;
  f := KC!f;

  //Calculate the glueing of the curve.
  /*
  S:=Scheme(ProjectiveSpace(S4),[h(K_eq),h(H_eq),ysq]);
  Irr := IrreducibleComponents(S);
  print "The number of irreducible components is:";
  print #Irr;
  for comp in Irr do
      C := ReducedSubscheme(comp);
      C := Curve(C);
      if Genus(C) eq 3 then
          phi:=CanonicalMap(C);
          D := phi(C);
          if Genus(D) eq 3 then

              print D;
              I,W := DixmierOhnoInvariants(DefiningEquation(D));
              print WPSNormalize(I,W);
          end if;
      end if;
  end for;
end if;  
*/
/*
C, f := CurveAndAmbientFunctionFromPlane(F_eq, H_eq, ysq);
KC := FunctionField(C);
f_new := KC!f;
Ct, ft, Ps := DesingularizedCurveAndAmbientFunctionAndPoints(C, f);
Et, ft, Ps := EllipticCurveAndAmbientFunctionAndPoints(Ct, ft, Ps);

for i in [[0,0],[0,1],[1,0],[1,1]] do
    g := FunctionFinder(Et,Ps,i[1],i[2]);
    if IsSquare(ft/g) then
        print i;
        print g;
        X3:=DoubleCover(Et,g);
    end if;
end for;

print X3;
*/
/*
GT, phiGT := TwoTorsionSubgroup(BFinal);

Pts:= Pts1 cat Pts2;
Ds:=[];

for P in Pts do
    print phi(P);
    Append(~Ds,Divisor(phi(P)));
end for;

Dz:= Ds[1]+Ds[2]+Ds[3]+Ds[4] - 4*Ds[1];
//test, f := IsPrincipal(Dz);
print test;
print Dz;
err
print f;


quit;


if Genus(C) eq 1 then
    E:= EllipticCurve(C);
    print "j(H intersect K) equal to j(X1)?";
    print jInvariant(X1) eq jInvariant(E);
end if;

//Map equation for y^2=b2^2 to S4.
y2:= Numerator(y2);
S4<x1,x2,x3,x4,y>:=ChangeRing(Parent(y2),KK);
y2:= S4!y2;
h:= hom<S3 -> S4|[x1,x2,x3,x4]>;

print h(K_eq);
print h(H_eq);
print y2;
*/

