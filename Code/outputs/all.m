//AttachSpec("../spec" );
load "fastthetasgenus3.m";
load "rationality.m";
load "riemann.m";
load "helpfunctions.m";

prec := 2000;
ZZ := Integers();
CC := ComplexFieldExtra(prec);
CCSmall<I> := ComplexFieldExtra(5);
R<x> := PolynomialRing(CC);

//Definieer krommen
f := (x + 2)*(x + 1)*x*(x - 1)*(x - 2)*(x - 4);
g := (x - 1)*x*(x + 1)*(x + 3);

//Bereken periodematrices
X2 := SE_Curve(f,2:Prec:=prec + 20);
X1 := SE_Curve(g,2:Prec:=prec + 20);

P2 := X2`BigPeriodMatrix;
P1 := X1`BigPeriodMatrix;

P2 := ChangeRing(P2, CC);
P1 := ChangeRing(P1, CC);

E1 := StandardSymplecticMatrix(1);
E2 := StandardSymplecticMatrix(2);
E3 := StandardSymplecticMatrix(3);

S6 := Sym(6);
sigma := S6 ! (3,5,4);
T := PermutationMatrix(ZZ, sigma);

/*
Ed := DiagonalJoin(E2, E1);
for U in [ T, T^(-1), Transpose(T), Transpose(T^(-1)) ] do
    print "---";
    print U*Ed*Transpose(U);
end for;
*/

T := T^(-1);
P3 := DiagonalJoin(P2, P1)*ChangeRing(T, CC);
//print FindPolarizationBasis(P3);
/* We now have a period matrix of the period that admits the standard polarization */

FF := FiniteField(2);
E3 := ChangeRing(StandardSymplecticMatrix(3), FF);
W := VectorSpace(FF, 6);
Vs := [ ];
for tup in CartesianPower(W, 3) do
    v1, v2, v3 := Explode(tup);
    V := sub<W | [v1, v2, v3]>;
    if #V eq 8 and not V in Vs then
        test1 := Matrix(v1)*E3*Transpose(Matrix(v2)) eq 0;
        test2 := Matrix(v1)*E3*Transpose(Matrix(v3)) eq 0;
        test3 := Matrix(v2)*E3*Transpose(Matrix(v3)) eq 0;
        if &and([ test1, test2, test3 ]) then
            Append(~Vs, V);
        end if;
    end if;
end for;

Ws := [];
for V in Vs do
    V1 := [ v : v in V | &and([ v[1] eq 0, v[2] eq 0, v[4] eq 0, v[5] eq 0 ]) ];
    V2 := [ v : v in V | &and([ v[3] eq 0, v[6] eq 0 ]) ];
    if #V1 eq 2 and #V2 eq 4 then
        Append(~Ws, V);
    end if;
end for;
Vs := [ V : V in Vs | not V in Ws ];
print "Number of interesting symplectic subgroups:";
print #Vs;
/* We now have all symplectic subgroup of the two-torsion that do not a priori
 * induce product polarization on corresponding quotient */


function Lift(c)

if c eq 0 then
    return Rationals() ! 0;
else
    return Rationals() ! 1/2;
end if;

end function;

//Vs := [ Vs[1] ];
Is := [* *];
Xs := [* *];

for i := 1 to #Vs do
    print "Subgroup number:", i;
    V := Vs[i];
    print V;
    L1 := Lattice(IdentityMatrix(Rationals(), 6));
    M2 := Matrix(Basis(V));
    M2 := Matrix(Rationals(), #Rows(M2), #Rows(Transpose(M2)), [ Lift(c) : c in Eltseq(M2) ]);
    L2 := Lattice(M2);
    L := L1 + L2;
    T := Matrix(Basis(L));
    E3 := StandardSymplecticMatrix(3);
    /* Welke? */
    /*
    for U in [ T, T^(-1), Transpose(T), Transpose(T^(-1)) ] do
        E := U*E3*Transpose(U);
        print E;
    end for;
    */
    E := T*E3*Transpose(T);
    T1 := T;


    _, T2 := FrobeniusFormAlternating(ChangeRing(2*E, Integers()));

    BT:=T2*T1;

    Glued:= P3*ChangeRing(BT,BaseRing(P3));
    print "Check principal:";
    print BT*2*E3*Transpose(BT) eq E3;

    P1 := Submatrix(Glued, 1,1, 3,3);
    P2 := Submatrix(Glued, 1,4, 3,3);
    tau := P1^(-1)*P2;

    print "Check small and true:";
    print CCSmall ! Maximum([ Abs(c) : c in Eltseq(tau - Transpose(tau)) ]);
    print IsPositiveDefinite(Matrix(RealField(10), [ [ Im(c) : c in Eltseq(row) ] : row in Rows(tau) ]));

    /* T1 en T2 combineren geeft symplectische basis voor de geinduceerde hoofdpol
     * op het grotere rooster */

    /* Daarna: transformeer het product van de periodmatrices op een
     * corresponderende manier. Vind theta's. Is alles niet-hyperelliptisch? Bereken
     * de invarianten. */

    fundamentalThetas := CalculThetas(tau/2);
    thetas := AllDuplication(fundamentalThetas);
    //print [ ComplexField(5) ! theta : theta in thetas ];
    thetas_zero := #[ theta : theta in thetas | Abs(theta) lt 10^(-10) ];
    is_hyp := thetas_zero gt 28;
    print "Hyperelliptic?";
    print is_hyp;

    if is_hyp then
    I := ReconstructHyp(tau);
    else
        I := ReconstructNonHyp(tau);
    end if;
    print "Invariants:";
    print I;
    Append(~Is, I);

    // Optional
    /*
    if is_hyp then
        X := HyperellipticCurveFromShiodaInvariants(I);
    else
        F := TernaryQuarticFromDixmierOhnoInvariants(I);
        P2 := ProjectiveSpace(Parent(F));
        X := Curve(P2, F);
    end if;
    Append(~Xs, X);
    */
end for;
Write("all90.m", Is);
//Write("all90.m", Xs);
