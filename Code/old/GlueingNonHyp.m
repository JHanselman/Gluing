AttachSpec("../spec" );
load "fastthetasgenus3.m";
load "rationality.m";
load "riemann.m";
//load "Polarizations.m";
load "helpfunctions.m";

prec := 200;
CC:=ComplexFieldExtra(prec);
I:=CC.1;
CCSmall:=ComplexFieldExtra(5);
R<x> := PolynomialRing(CC);


//Definieer krommen
f := (x-1)*(x-4)*(x-9)*(x-16);
g := x*f;
h := (x^2-1)*(x^2-4)*(x^2-9)*(x^2-16);

m := 2;
Prec := 500;


//Bereken periodematrices
E := SE_Curve(f,m:Prec:=prec);
Y := SE_Curve(g,m:Prec:=prec);
//X := SE_Curve(h,m:Prec:=prec);

P := E`BigPeriodMatrix;
Q := Y`BigPeriodMatrix;
//J := X`BigPeriodMatrix;

P := Transpose(P); Q := Transpose(Q);
P := ChangeRing(P, CC); Q := ChangeRing(Q, CC);
//J := ChangeRing(J,CC); J:= Transpose(J);


v:=[];
w:=[];


froots:=Roots(f);
groots:=Roots(g);

a1:= [froots[1][1],0];
a2:= [froots[2][1],0];
a3:= [froots[3][1],0];

b1:= [groots[2][1],0];
b2:= [groots[4][1],0];
b3:= [groots[3][1],0];

b5:= [groots[1][1],0];
b6:= [1];


Append(~v,SE_AbelJacobi(SE_Divisor([<a1,1>,<a1,-1>],E),E));
Append(~v,SE_AbelJacobi(SE_Divisor([<a2,1>,<a1,-1>],E),E));
Append(~v,SE_AbelJacobi(SE_Divisor([<a3,1>,<a1,-1>],E),E));

Append(~w,SE_AbelJacobi(SE_Divisor([<b5,1>,<b6,-1>],Y),Y));
Append(~w,SE_AbelJacobi(SE_Divisor([<b2,1>,<b1,-1>],Y),Y));
Append(~w,SE_AbelJacobi(SE_Divisor([<b3,1>,<b1,-1>],Y),Y));


printf "The kernel k  of Jac(Y)[2]-> Jac(X) is given by the divisor %o - %o \n", Vector(CCSmall,b5), Vector(CCSmall,b6);

print "The isomorphism E[2] -> Jac[Y][2] is given by:";
printf "%o - %o maps to %o - %o\n",Vector(CCSmall,
a2),Vector(CCSmall,a1),Vector(CCSmall,  b2), Vector(CCSmall,b1);
printf "%o - %o maps to %o - %o\n",Vector(CCSmall,
a3),Vector(CCSmall,a1),Vector(CCSmall,  b3), Vector(CCSmall,b1);


V:= Matrix(v);
W:= Matrix(w);

GlueMatrix:= HorizontalJoin(V,W);

PQ:=DiagonalJoin(P,Q);

for i:=1 to 6 do
    padding:= [ BaseRing(GlueMatrix)!0*j : j in [1..6]];
    padding[i]:=1;
    B:= VerticalJoin(GlueMatrix,Matrix([padding]));
    if Rank(B) gt  Rank(GlueMatrix) then
        GlueMatrix:= B;
    end if;
    if Rank(B) eq 6 then
        break;
    end if;
end for;


S:=DiagonalJoin(StandardPol(CC,1),StandardPol(CC,2));

NewPol:=2*GlueMatrix*S*Transpose(GlueMatrix);

Glued:= ChangeRing(GlueMatrix,BaseRing(PQ))*PQ;

/*
GeoEndoRep := GeometricIsogenyRepresentationPartial(J, Glued);
print "Number of elements in isogeny basis:", #GeoEndoRep;
T, R := Explode(GeoEndoRep[1]);
R := Transpose(R); T := Transpose(T);
RCC := ChangeRing(R, CC);
comm := Glued*T - RCC*J;
comm := J*T - RCC*Glued;

print Minimum([ Abs(c) : c in Eltseq(comm) ]);
B := 1;
D := [-B..B];
CP := CartesianPower(D, #GeoEndoRep);
for tup in CP do
    det := Determinant(&+[ tup[i]*GeoEndoRep[i][2] : i in [1..#GeoEndoRep] ]);
    if Abs(det) le 10 then
        print tup, det;
    end if;
end for;
*/


BaseChange:=ChangeRing(ReducePol(NewPol),CC);

GluedPF:= BaseChange*Glued;


P1 := Submatrix(Transpose(GluedPF), 1,1, 3,3);
P2 := Submatrix(Transpose(GluedPF), 1,4, 3,3);
tau := P1^(-1)*P2;


print IsPositiveDefinite(Matrix(RealField(10), [ [ Im(c) : c in Eltseq(row)
]:row in Rows(tau) ]));


/* Check niet-niet-hyperelliptisch door na te gaan dat meer dan 28 waarden niet
* 0 zijn: */
/*
fundamentalThetas := CalculThetas(tau/2);
thetas := AllDuplication(fundamentalThetas);
print Minimum([ Abs(theta) : theta in thetas ]);
print [ ComplexField(5) ! theta : theta in thetas ];
thetas_zero := #[ theta : theta in thetas | Abs(theta) lt 10^(-10) ];
print thetas_zero;
*/

ReconstructNonHyp(tau);
