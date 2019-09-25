function BinaryQuarticInvariants(bq); 
 
R<x> := Parent(bq); 
 
a := Coefficient(bq,4); 
b := Coefficient(bq,3); 
c := Coefficient(bq,2); 
d := Coefficient(bq,1); 
e := Coefficient(bq,0); 
 
I := 12*a*e - 3*b*d + c^2; 
J := 72*a*c*e + 9*b*c*d - 27*a*d^2 - 27*e*b^2 - 2*c^3; 
Delta := 4*I^3 - J^2; 
 
return I,J,Delta; 
 
end function; 


function SmoothSample(D);

F := Parent(Random(D));
R<x> := PolynomialRing(F);

while true do
    a := Random(D);
    b := Random(D);
    c := Random(D);

    pX := x^8 + a*x^6 + b*x^4 + c*x^2 + 1;
    pY := x^5 + a*x^4 + b*x^3 + c*x^2 + x;
    pE := x^4 + a*x^3 + b*x^2 + c*x + 1;

    DX := Discriminant(pX);
    DY := Discriminant(pY);
    DE := Discriminant(pE);
    test := &and[ D ne 0 : D in [ DX, DY, DE ] ];
    if test then
        g2ev := G2Invariants(HyperellipticCurve(pY));
        I, J, Delta := BinaryQuarticInvariants(pE); jev := I^3 / Delta;
        return g2ev, jev;
    end if;
end while;

end function;


function TestDegree(d, F, B);

if Type(F) eq FldFin then
    D := F;
else
    D := [-B..B];
end if;

R<g1,g2,g3,j> := PolynomialRing(F, 4);
mons := &cat[ [ mon : mon in MonomialsOfDegree(R, i) ] : i in [0..d] ];
print #mons;

N := #mons + 100;
rows := [ ];
for i:=1 to N do
    if i mod 1000 eq 0 then
        print i;
    end if;
    g2sev, jev := SmoothSample(D);
    monsev := [ Evaluate(mon, g2sev cat [ jev ]) : mon in mons ];
    Append(~rows, monsev);
end for;

repeat
    g2sev, jev := SmoothSample(D);
    monsev := [ Evaluate(mon, g2sev cat [ jev ]) : mon in mons ];
    Append(~rows, monsev);
    print "Calculating kernel...";
    K := Kernel(Transpose(Matrix(rows)));
    dimK := Dimension(K);
    print dimK;
until dimK eq 0;
return K;

end function;


d := 1;
F := FiniteField(1009);
B := 100;

//print SmoothSample(F);
print TestDegree(30, F, B);

exit;

