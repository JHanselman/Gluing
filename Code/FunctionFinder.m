function FunctionFinder(E,Ps,i,j)

K<x,y>:=FunctionField(E);

P1:=Ps[1];
P2:=Ps[2];
P3:=Ps[3];
P4:=Ps[4];

Q := (P2+P3+P4)/2;

T,phi := TwoTorsionSubgroup(E);
T1:=phi(T.1);
T2:=phi(T.2);

D1:=Divisor(P1);
D2:=Divisor(P2);
D3:=Divisor(P3);
D4:=Divisor(P4);
DQ:=Divisor(Q);

D:=D2+D3+D4-2*DQ-D1;

bool, f := IsPrincipal(D);

g:=1;

if i eq 1 or j eq 1 then
    g:= x-(i*T1+j*T2)[1];
end if;
return f/g;

end function;

/*
E:= EllipticCurve([1, -1, 1, -41, 96]);
K<x,y>:=FunctionField(E);
P1:= E![2,3];
P2:= E![6,3];
P3:=E![9,15];

Ps:=([P1,P2,P3]);
FunctionFinder(E,Ps);
*/
