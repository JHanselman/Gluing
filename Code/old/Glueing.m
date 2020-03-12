AttachSpec("../spec" );
AttachSpec("../../CM/reconstruction/package/spec");
load "fastthetasgenus3.m";
load "rationality.m";
load "riemann.m";
load "Polarizations.m";
load "helpfunctions.m";


//QQ:= Rationals();
//R<x> := PolynomialRing(QQ);
//g := x*(x^4 + 2*x^3 - 3*x^2 + 7*x - 1);
//f := x^4 + 2*x^3 - 3*x^2 + 7*x - 1;

CC:=ComplexFieldExtra(50);
I:=CC.1;
R<x> := PolynomialRing(CC);


//Definieer krommen
f := (x-1)*(x-4)*(x-9)*(x-16);
g := x*f;
h := (x^2-1)*(x^2-4)*(x^2-9)*(x^2-16);

//Bereken periodematrices
J1:= AnalyticJacobian(f);
P1:= BigPeriodMatrix(J1);

J2:= AnalyticJacobian(g);
P2:= BigPeriodMatrix(J2);

J3:= AnalyticJacobian(h);
P3:= BigPeriodMatrix(J3);

v:=[];
w:=[];

//Schrijf de coordinaten van de wortels in een matrix
for i:=1 to 4 do
    Append(~v, ToAnalyticJacobian(CC!i^2,CC!0,J1));
   
    Append(~w,ToAnalyticJacobian(CC!i^2,CC!0,J2));
  
end for;

print "kernelpoint";
print ToAnalyticJacobian(CC!0,CC!0,J2);

quit;

Append(~v,ToAnalyticJacobian(CC!4^2,CC!0,J1));
Append(~w,ToAnalyticJacobian(CC!0,CC!0,J2));

vnew:=SplitMatrix((Matrix(v)));
p1new:=SplitMatrix(Transpose(P1))^(-1);


wnew:=SplitMatrix(Matrix(w));
p2new:=SplitMatrix(Transpose(P2))^(-1);




//print wnew*p2new;


//print HorizontalJoin(vnew*p1new,wnew*p2new);

//Hier kan het fout gaan als de input niet uit wortels bestaat omdat alles naar
//Z/2 wordt gestuurd. Check dit.
p1new:= ChangeRing(2*vnew*p1new,map<BaseRing(vnew) -> ZZ| x :-> Round(x)>);
p2new:= ChangeRing(2*wnew*p2new,map<BaseRing(wnew) -> ZZ| x :-> Round(x)>);

//Bereken de lijmmatrix
B:=  HorizontalJoin(p1new,p2new);

B:= ChangeRing(B,map<ZZ -> quo<ZZ | 2>| x :-> x mod 2>);

for i:=1 to 3 do
    AddRow(~B,1,4,i);
end for;

//print B;

SwapRows(~B,4,5);

B:=RowSubmatrix(B,4);
B:=ChangeRing(B,ZZ );
B:= 1/2*ChangeRing(B,QQ);
//print B;


for i:=1 to 6 do
    padding:= [ QQ!0*j : j in [1..6]];
    padding[i]:=1;
    B2:= VerticalJoin(B,Matrix([padding]));
    if Rank(B2) gt  Rank(B) then
        B:= B2;
    end if;
    if Rank(B) eq 6 then
        break;
    end if;
end for;

//print B;
//Determinant(B);

BCC:=ChangeRing(B,CC);

P:= DiagonalJoin(P1,P2);
//print "start";
//GeometricIsogenyRepresentationPartial(Transpose(P), Transpose(P3));
//print ChangeRing(P,ComplexField(3));
//print "pause";

//print ChangeRing(P3,ComplexField(3));




//Lijm de krommen
NewP:= BCC*Transpose(P);
//NewP:= Transpose(P);

GeoEndoRep := GeometricIsogenyRepresentationPartial(Transpose(P2),Transpose(P3) );
//print GeoEndoRep;

print P2;

//HJ:= GeoEndoRep[2][2];
//print Determinant(HJ);

quit;

FPol:=FindPolarizationBasis(NewP);


//print FPol[1];
//print FPol[2];




//S:=GluePol(QQ,1,2);
//NewPol:=2*B*S*Transpose(B);
//print NewPol;
//Determinant(NewPol);

NewPol:=FPol[1];

//print ReducePol(NewPol);

BaseChange:=ChangeRing(ReducePol(NewPol),CC);

NewPolCC:=ChangeRing(NewPol,CC);

SympP:=Transpose(BaseChange*NewP);


print "Test1";
SympP*StandardPol(CC,3)^(-1)*Transpose(SympP);

P1 := Submatrix(SympP, 1,1, 3,3);
P2 := Submatrix(SympP, 1,4, 3,3);
tau := -P1^(-1)*P2;

ReconstructHyp(tau);
quit;

print ChangeRing(tau,ComplexField(5));
print tau;

print IsPositiveDefinite(Matrix(RealField(10), [ [ Im(c) : c in Eltseq(row) ] :
row in       Rows(tau) ]));



/* Check niet-niet-hyperelliptisch door na te gaan dat meer dan 28 waarden niet
* 0 zijn: */

fundamentalThetas := CalculThetas(tau/2);
thetas := AllDuplication(fundamentalThetas);
print Minimum([ Abs(theta) : theta in thetas ]);
print [ ComplexField(5) ! theta : theta in thetas ];
thetas_zero := #[ theta : theta in thetas | Abs(theta) lt 10^(-10) ];
print thetas_zero;

quit;

print ReconstructNonHyp(tau);
quit;

if thetas_zero gt 28 then
        ReconstructHyp(tau);
    else
            ReconstructNonHyp(tau);
        end if;


quit;


/*pr:=50;

P1 := Transpose(PeriodMatrix(f : Prec := pr));
P2 := Transpose(PeriodMatrix(g : Prec := pr));
P := DiagonalJoin(P1, P2);
//P := ChangeRing(P, ComplexFieldExtra(Precision(BaseRing(P))));
//print FindPolarizationBasis(P);

CC:=BaseRing(P);

I:=CC.1;

Gluedata := 1/2*Matrix(QQ,[[1,0,1,0,0,0],[1,1,0,1,1,0],[0,1,0,0,1,1]]);
Padding:= Matrix(QQ,[[0,0,0,0,0,1]]);

TTop:= HorizontalJoin(IdentityMatrix(QQ,2),ZeroMatrix(QQ,2,4));
TBottom:= VerticalJoin(Gluedata,Padding);

T:= VerticalJoin(TTop,TBottom);
print T;
NewP:= ChangeRing(T,CC)*P;

S:=GluePol(QQ,1,2);
NewPol:=2*T*S*Transpose(T);
print NewPol;


BaseChange:=ChangeRing(ReducePol(NewPol),CC);

NewPolCC:=ChangeRing(NewPol,CC);

print "Test1";
Transpose(NewP)*NewPolCC^(-1)*NewP;

print "Test2";
I*Transpose(NewP)*NewPolCC^(-1)*CConjugateMatrix(NewP);

//SympP:=Transpose(BaseChange*NewP);


print "Test1";
SympP*StandardPol(CC,3)^(-1)*Transpose(SympP);

P1 := Submatrix(SympP, 1,1, 3,3);
P2 := Submatrix(SympP, 1,4, 3,3);
tau :=P1^(-1)*P2;

print ChangeRing(tau,ComplexField(5));
print tau;
print IsPositiveDefinite(Matrix(RealField(10), [ [ Im(c) : c in Eltseq(row) ] : row in Rows(tau) ]));

/* Check niet-niet-hyperelliptisch door na te gaan dat meer dan 28 waarden niet
* 0 zijn: */


fundamentalThetas := CalculThetas(tau/2);
thetas := AllDuplication(fundamentalThetas);
print Minimum([ Abs(theta) : theta in thetas ]);
print [ ComplexField(5) ! theta : theta in thetas ];
thetas_zero := #[ theta : theta in thetas | Abs(theta) lt 10^(-10) ];
print thetas_zero;
print ReconstructNonHyp(tau);
quit;

if thetas_zero gt 28 then
    ReconstructHyp(tau);
else
    ReconstructNonHyp(tau);
end if;
     
  
   
    
 
end function;

