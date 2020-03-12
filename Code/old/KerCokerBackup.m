load "ingredients.m";

R<x> := PolynomialRing(Rationals());

CC := ComplexFieldExtra(100);
I:=CC.1;
R2<x> := PolynomialRing(CC);

f := (x^2-1)*(x^2-4)*(x^2-9)*(x^2-16);
g := x*(x-1)*(x-4)*(x-9)*(x-16);
h := (x-1)*(x-4)*(x-9)*(x-16);

fs := [f, g, h];
//pairs := [[f, g], [g, f], [f, h], [h, f]];
pairs := [[f, g]];

for i in [1..#pairs] do
    print "Pair number", i;
    pair := pairs[i];
    f := pair[1];
    g := pair[2];

    P := Transpose(PeriodMatrix(f : Prec := 100));
    Q := Transpose(PeriodMatrix(g : Prec := 100));
    //print Q;
    
    J1:= AnalyticJacobian(h);
    P1:= Transpose(BigPeriodMatrix(J1));


    J2:= AnalyticJacobian(R2!g);
    Q:= Transpose(BigPeriodMatrix(J2));
 
    w:=[];
//Schrijf de coordinaten van de wortels in een matrix
   // for i:=0 to 4 do

       // Append(~w,ToAnalyticJacobian(CC!i^2,CC!0,J2));

 //   end for;
    
   // wnew:=SplitMatrix(Matrix(w));
    p2new:=SplitMatrix(Q)^(-1);
    
    wnew:=Vector(BaseRing(p2new),[0.5,0,0,0]);
    //wnew:= ChangeRing(wnew,BaseRing(p2new))*p2new;
    

    for i:=1 to 6 do
        padding:= [BaseRing(wnew)! 0*j : j in [1..4]];
        padding[i]:=1;
        B2:= VerticalJoin(wnew,Matrix([padding]));
        if Rank(B2) gt  Rank(wnew) then
            wnew:= B2;
        end if;
        if Rank(wnew) eq 4 then
            break;
        end if;
    end for;

   // print wnew;
    
   // Q:= Matrix(BaseRing(Q),wnew)*Q;
    Q:= DiagonalJoin(P1,Q);
 
 
    print Q;
    print "P:";
    print P;

    P := ChangeRing(P, CC); Q := ChangeRing(Q, CC);

    /* We take a morphism from the curve Y defined by g and Q to the curve X
     * defined by f and P. Note the transpose, which really ticks me off. */

    GeoEndoRep := GeometricIsogenyRepresentationPartial(Q, P);
    print "Number of elements in isogeny basis:", #GeoEndoRep;
    T, R := Explode(GeoEndoRep[1]);
    R := Transpose(R); T := Transpose(T);
    RCC := ChangeRing(R, CC);
    comm := Q*T - RCC*P;
    
    
   // print "Q";
   // print Q;
    
   // R2:=Matrix(CC,[[0,-1,0,0,0,0],[1,-1,-1,0,0,0],[0,0,0,0,1,-1],[0,0,0,-1,0,1]]);

  //  print "RP";
   // print R2*P;
  

    print "Test almost 0:";
    print Maximum([ Abs(c) : c in Eltseq(comm) ]);

    print "Curves:";
    print "from";
    print HyperellipticCurve(g);
    print "to";
    print HyperellipticCurve(f);

    print "Matrix dimensions:";
    printf "P is a matrix with %o rows of length %o\n", #Rows(P), #Rows(Transpose(P));
    printf "Q is a matrix with %o rows of length %o\n", #Rows(Q), #Rows(Transpose(Q));
    printf "R is a matrix with %o rows of length %o\n", #Rows(R), #Rows(Transpose(R));
    printf "T is a matrix with %o rows of length %o\n", #Rows(T), #Rows(Transpose(T));

    print "Rank of R:";
    print Rank(R);

    print "Connected component group of kernel:";
    KCCG := KerModKer0(R, Q, P);
    print KCCG;

    print "Trivial component of kernel:";
    K := Ker0(R, Q, P);
    if not Type(K) eq RngIntElt then
        print ChangeRing(K, ComplexField(5));
    else
        print K;
    end if;

    print "Cokernel:";
    C := Coker(R, Q, P);
    if not Type(C) eq RngIntElt then
        print ChangeRing(C, ComplexField(5));
    else
        print C;
    end if;

end for;

exit;
