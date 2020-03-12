QQ:= Rationals();

function CConjugateMatrix(M);
L:=BaseRing(M);
I:=L.1;
sigma:= hom<L -> L|a :-> ComplexConjugate(a)>;
return ConjugateMatrix(sigma,M);
end function;

function StandardPol(F,n);
return
BlockMatrix([[ZeroMatrix(F,n,n),IdentityMatrix(F,n)],[-IdentityMatrix(F,n),ZeroMatrix(F,n,n)]]);
end function;

function GluePol(F,g1,g2);
return DiagonalJoin(StandardPol(F,g1),StandardPol(F,g2));
end function;


function ReconstructHyp(t);

R<x>:=PolynomialRing(BaseRing(t));
f:=x*(x-1);
for alpha in RosenhainInvariants(t) do
    f:=f*(x-alpha);
end for;
S, W := ShiodaInvariants(f);

lambda1 := S[2]/S[1];
for i in [2..#S] do
    print ContinuedFraction(Real(S[i]/lambda1^W[i]));
end for;

// look for a good rational approximation of the (absolute) invariants
// below

I2:=RationalReconstruction(S[2 - 1]/lambda1^2);
I3:=RationalReconstruction(S[3 - 1]/lambda1^3);
I4:=RationalReconstruction(S[4 - 1]/lambda1^4);
I5:=RationalReconstruction(S[5 - 1]/lambda1^5);
I6:=RationalReconstruction(S[6 - 1]/lambda1^6);
I7:=RationalReconstruction(S[7 - 1]/lambda1^7);
I8:=RationalReconstruction(S[8 - 1]/lambda1^8);
I9:=RationalReconstruction(S[9 - 1]/lambda1^9);
I10:=RationalReconstruction(S[10 - 1]/lambda1^10);

S := [ I2, I3, I4, I5, I6, I7, I8, I9, I10 ];
return S;
return WPSMinimize(W, S);

end function;


function ReconstructNonHyp(tau);

// computation of theta[0,b](tau/2)
//fundamentalThetas := CalculThetas(tau/2);
fundamentalThetas := NaiveThetaConstantsGenus3(tau/2,false,2000);

// computation of theta[a,b](tau)^2
thetas := AllDuplication(fundamentalThetas);
// square root extraction
thetas:=Rotate(thetas,-1);
Clow := ComplexField(50); taulow :=Matrix(Clow,3,3,[ Clow!tau[i][j] : i,j in [1..3]]);
for i:=1 to 64 do
// tau or taulow below? It should be taulow but sometimes it
// leads to errors.
    thetas[i] := Sqrt(thetas[i]); if (
    average(ThetaGenus3(i,taulow)-thetas[i]) gt -20) then
    thetas[i] := -thetas[i]; end if;
end for;

// compute the Moduli of Weber
M:=ModuliFromTheta(thetas);
// compute a Riemann model of the curve from the Moduli
F:=RiemannModelFromModuli(M);

// The Dixmier-Ohno invariants of F
DO, W :=DixmierOhnoInvariants(F);

//for i in [2..#DO] do
//    print ContinuedFraction(Real(DO[i]/DO[1]^(W[i] div 3)));
//end for;

// look for a good rational approximation of the (absolute) invariants
// below

I6:=RationalReconstructionAlt(DO[2]/DO[1]^2);
I9:=RationalReconstructionAlt(DO[3]/DO[1]^3);
J9:=RationalReconstructionAlt(DO[4]/DO[1]^3);
I12:=RationalReconstructionAlt(DO[5]/DO[1]^4);
J12:=RationalReconstructionAlt(DO[6]/DO[1]^4);
I15:=RationalReconstructionAlt(DO[7]/DO[1]^5);
J15:=RationalReconstructionAlt(DO[8]/DO[1]^5);
I18:=RationalReconstructionAlt(DO[9]/DO[1]^6);
J18:=RationalReconstructionAlt(DO[10]/DO[1]^6);
I21:=RationalReconstructionAlt(DO[11]/DO[1]^7);
J21:=RationalReconstructionAlt(DO[12]/DO[1]^7);
I27:=RationalReconstructionAlt(DO[13]/DO[1]^9);

// look for a weighted projective equivalent of the absolute invariants
// above with small denominators
I3:=2*3*Denominator(I9)/Denominator(I6);
DOr:=[I3,I3^2*I6,I3^3*I9,I3^3*J9,I3^4*I12,I3^4*J12,I3^5*I15,I3^5*J15,I3^6*I18,I3^6*   J18,I3^7*I21,I3^7*J21,I3^9*I27];
d:=Lcm([Denominator(I) : I in DOr]);
return DOr;

DO := [ 1, I6, I9, J9, I12, J12, I15, J15, I18, J18, I21, J21, I27 ];
return WPSMinimize(W, DO);

end function;


function ReducePol(M);
B:=M;
Determinant(M);

n:=NumberOfRows(M);
I:=IdentityMatrix(BaseRing(M),n);
for i:=1 to (n-1) by 2  do
    for j:=i to n do
        if (M[i][j] eq 1) then
            sweep:=j;
            break;
        elif (M[i][j] eq -1) then
            sweep:=j;
            MultiplyRow(~M,-1, i);
            MultiplyColumn(~M, -1, i);

            MultiplyRow(~I,-1, i);

            break;
        end if;
    end for;

    for j:=1 to n do
        if j eq sweep then
            ;
        elif M[i][j] ne 0 then
            d:= -M[i][j];
            AddRow(~M,d, sweep, j);
            AddColumn(~M,d, sweep,j);
            AddRow(~I,d, sweep, j);

        end if;
    end for;

    for j:=1 to n do
        if j eq i then
            ;
        elif M[j][sweep] ne 0 then
            d:= -M[j][sweep];
            AddRow(~M,d, i, j);
            AddColumn(~M, d, i, j);
            AddRow(~I,d, i, j);


        end if;
    end for;

SwapColumns(~M,i+1,sweep);
SwapRows(~M,i+1,sweep);

SwapRows(~I,i+1,sweep);



end for;

m:=Floor(n/2);
for i:=1 to m   do
    if (i mod 2 eq 1) then
        SwapColumns(~M,i,m+i-1);
        SwapRows(~M,i,m+i-1);
        SwapRows(~I,i,m+i-1);

    else
        SwapColumns(~M,i,m+i-2);
        SwapRows(~M,i,m+i-2);
        SwapRows(~I,i,m+i-2);

    end if;
end for;

return I;
end function;


function CalculateDOInvariants(tau,thetas)

// square root extraction
thetas:=Rotate(thetas,-1);
Clow := ComplexField(50); taulow :=Matrix(Clow,3,3,[ Clow!tau[i][j] : i,j in [1..3]]);
for i:=1 to 64 do
// tau or taulow below? It should be taulow but sometimes it
// leads to errors.
    thetas[i] := Sqrt(thetas[i]); if (
    average(ThetaGenus3(i,taulow)-thetas[i]) gt -20) then
    thetas[i] := -thetas[i]; end if;
end for;

// compute the Moduli of Weber
M:=ModuliFromTheta(thetas);
// compute a Riemann model of the curve from the Moduli
F:=RiemannModelFromModuli(M);

// The Dixmier-Ohno invariants of F
DO, W :=DixmierOhnoInvariants(F);

for i in [2..#DO] do
    print ContinuedFraction(Real(DO[i]/DO[1]^(W[i] div 3)));
end for;

// look for a good rational approximation of the (absolute) invariants
// below

I6:=RationalReconstruction(DO[2]/DO[1]^2);
I9:=RationalReconstruction(DO[3]/DO[1]^3);
J9:=RationalReconstruction(DO[4]/DO[1]^3);
I12:=RationalReconstruction(DO[5]/DO[1]^4);
J12:=RationalReconstruction(DO[6]/DO[1]^4);
I15:=RationalReconstruction(DO[7]/DO[1]^5);
J15:=RationalReconstruction(DO[8]/DO[1]^5);
I18:=RationalReconstruction(DO[9]/DO[1]^6);
J18:=RationalReconstruction(DO[10]/DO[1]^6);
I21:=RationalReconstruction(DO[11]/DO[1]^7);
J21:=RationalReconstruction(DO[12]/DO[1]^7);
I27:=RationalReconstruction(DO[13]/DO[1]^9);

// look for a weighted projective equivalent of the absolute invariants
// above with small denominators
I3:=2*3*Denominator(I9)/Denominator(I6);
DOr:=[I3,I3^2*I6,I3^3*I9,I3^3*J9,I3^4*I12,I3^4*J12,I3^5*I15,I3^5*J15,I3^6*I18,I3^6*J18,I3^7*I21,I3^7*J21,I3^9*I27];
d:=Lcm([Denominator(I) : I in DOr]);
return DOr;
end function;

