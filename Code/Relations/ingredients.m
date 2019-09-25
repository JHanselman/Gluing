function BinaryQuarticInvariants(bq);

R<x> := Parent(bq);

a := Coefficient(bq, 4);
b := Coefficient(bq, 3);
c := Coefficient(bq, 2);
d := Coefficient(bq, 1);
e := Coefficient(bq, 0);

I := 12*a*e - 3*b*d + c^2;
J := 72*a*c*e + 9*b*c*d - 27*a*d^2 - 27*e*b^2 - 2*c^3;
Delta := 4*I^3 - J^2;

return [ I, J ];

end function;
