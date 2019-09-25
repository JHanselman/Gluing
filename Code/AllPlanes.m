load "KummerFunctions.m";

SetSeed(1);


//Define the base field and the function field
FFp := FiniteField(2017);
//FFp := Rationals();
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
f := (x + 3)*(x + 1)*x*(x - 1)*(x - 3)*(x - 4);
//f := (x-5)*(x+2)*(x-31)*(x+15)*x*(x+1);

/* Eq of divisor:
    x^2 + a1 x + a2 = 0
    y = b1 x + b2
*/

K,ysq:=CalculateKummer(f);
F:= DefiningEquation(K);


S3<x1,x2,x3,x4> := PolynomialRing(L,4);

Sing := SingularSubscheme(K);
nodes := [ P : P in Points(Sing) ];

print nodes;

m:= 1;
n:= 2;
Is := [];
Xs := [];
Irrs := [];
Q1:= nodes[m];
Q2:= nodes[n];

print m,n;
//Find all planes that go through the two nodes with a given j-invariant.
Planes:=FindPlanes(K,X1,Q1,Q2);
plane := Planes[[1][1]];
 //Equation for the Kummer
K_eq := S3 ! F;
           
print plane;
KK:=BaseRing(plane);

S3<x1,x2,x3,x4>:=PolynomialRing(KK,4);
P3:= ProjectiveSpace(S3);


//Equation for the plane.
H:=plane[1];
H_eq:= x1*H[1]+x2*H[2]+x3*H[3]+x4*H[4];

//Eqquation for Kummer
F_eq := S3!F;

//Check if H intersected with K actually gives an elliptic curve with given j-invariant.
S:= Scheme(P3,[F_eq,H_eq]);
S:= ReducedSubscheme(S);
C:= Curve(S);
print C;
CAff := AffinePatch(C,1);

R3<x1, y1, z1> := CoordinateRing(Ambient(CAff));
Sing := SingularSubscheme(CAff);
nodes := [ C ! P : P in Points(Sing) ];
print C;
print nodes;

node1:=nodes[1];
node2:=nodes[2];

R4<x1,y1,z1,t1> := PolynomialRing(KK, 4);
A4 := AffineSpace(R4);
h := hom< R3 -> R4 | [ x1, y1,z1 ] >;
f1 := h(DefiningEquations(CAff)[1]);
f2 :=h(DefiningEquations(CAff)[2]);
B1 := Scheme(A4, [ f1,f2, (y1-nodes[1][2] - t1*(x1 -nodes[1][1])) ]);
Is := IrreducibleComponents(B1);
print Is[2];
B1 := Is[1];


R5<x2,y2,z2,t2,u2> := PolynomialRing(KK, 5);
A5 := AffineSpace(R5);
h := hom< R4 -> R5 | [ x2, y2, z2, t2 ] >;
fs := [ h(f) : f in DefiningEquations(B1) ];
B2 := Scheme(A5, fs cat [ (y2 - nodes[2][2]) - u2*(x2 - nodes[2][1]) ]);
Is := IrreducibleComponents(B2);
print Is[2];
B2 := Is[1];

R<s1,s2,s3,s4,y>:=FieldOfFractions(Parent(ysq));

Efield<x2,y2,z2,t2,u2>:= FieldOfFractions(R5);

psi:= hom< FieldOfFractions(R) -> Efield |[x2,y2,z2,1,0]>;
f := (R!ysq)/(s1^2);
f :=psi(f);


Pts1 := [ P : P in Points(ReducedSubscheme(Scheme(B2, [x2-nodes[1][1], y2-nodes[1][2]]))) ];
Pts2 := [ P : P in Points(ReducedSubscheme(Scheme(B2, [x2-nodes[2][1], y2-nodes[2][2]]))) ];

BFinal,phi:=EllipticCurve(ProjectiveClosure(Curve(B2)),Pts1[1]);

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

