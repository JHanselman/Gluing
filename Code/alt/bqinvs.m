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
 
a := I/(-3);
b := J/(-27);
D := (16/27)*Delta;
j := 1728*a^3/(a^3 + 27/4*b^2);

return j,I,J,Delta; 
 
end function; 
