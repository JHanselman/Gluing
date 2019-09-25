function StandardSymplecticMatrix(g)

A := ScalarMatrix(g, 0); B := ScalarMatrix(g, 1); C := -B; D := A;
return VerticalJoin(HorizontalJoin(A, B), HorizontalJoin(C, D));

end function;


function SubmatrixOfRankAlt(M, rk : ColumnsOrRows := "Columns")

// Reducing to columns
if ColumnsOrRows eq "Columns" then
    M := Transpose(M);
end if;

// Elementary invariants
CC := BaseRing(M);
r := #Rows(M); c := #Rows(Transpose(M));

RM := Rows(M);
for s in Subsets({1..r}, rk) do
    s0 := s;
    M0 := Matrix([ RM[i] : i in s ]);
    N0 := SplitMatrix(Transpose(M0));
    if NumericalRank(N0 : Epsilon := CC`epsinv) eq 2*rk then
        if ColumnsOrRows eq "Rows" then
            return M0, s0;
        else
            return Transpose(M0), s0;
        end if;
    end if;
end for;
error Error("Failed to find submatrix of the desired rank");

end function;


function KerModKer0(R, Q, P)
    L := Lattice(R);
    return quo< PureLattice(L) | L >;
end function;


function Ker0(R, Q, P);
    RMS := RMatrixSpace(Integers(), #Rows(R), #Rows(Transpose(R)));
    R0 := RMS ! R;
    B := Basis(Kernel(R0));
    if #B eq 0 then
        return 0, 0;
    end if;
    B := [ Eltseq(b) : b in B ];
    rowsQ := Rows(Q);
    rowsQnew := [ &+[ b[i]*rowsQ[i] : i in [1..#b] ] : b in B ];
    Qnew := Matrix(rowsQnew);
    Qnew, s := SubmatrixOfRankAlt(Qnew, #B div 2 : ColumnsOrRows := "Columns");
    Rnew := Matrix(Integers(), [ [ c : c in Eltseq(row) ] : row in B ]);
    return Qnew, Rnew;
    Tnew := TangentRepresentationIsogeny(Rnew, Qnew, Q);
    return Qnew, Rnew, Tnew;
end function;


function Coker(R, Q, P)
    L := PureLattice(Lattice(R));
    Zd := StandardLattice(Degree(L));
    Q, proj := quo< Zd | L >;
    gensQ := [ gen : gen in Generators(Q) ];
    if #gensQ eq 0 then
        return 0, 0;
    end if;
    B := [ Zd ! b : b in Basis(L) ];
    Bc := [ Zd ! g @@ proj : g in gensQ ];
    rowsP := Rows(P);
    rowsPnew := [ &+[ b[i]*rowsP[i] : i in [1..#Eltseq(b)] ] : b in Bc ];
    ImP := Matrix(rowsPnew);
    ImP, s := SubmatrixOfRankAlt(ImP, #Bc div 2 : ColumnsOrRows := "Columns");
    Pnew := Matrix([ [ row[i] : i in s ] : row in rowsPnew]);
    M := Matrix([ Eltseq(b) : b in B cat Bc ]);
    Rs := VerticalJoin(ZeroMatrix(Integers(), #B, #Bc), IdentityMatrix(Integers(), #Bc));
    Rnew := M^(-1)*Rs;
    return Pnew, Rnew;
    Tnew := TangentRepresentationIsogeny(Rnew, P, Pnew);
    return Pnew, Rnew, Tnew;
end function;
