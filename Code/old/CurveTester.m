F:=GF(37);

R<t> := PolynomialRing(F);
P<u,v>:= PolynomialRing(F,2);
S<x,y,z> := PolynomialRing(F, 3);

C:=   x^4 + 15*x^3*y + 2*x^2*y^2 + 26*x*y^3 + 4*y^4 + 20*x^2*z^2 + 15*x*y*z^2 + 23*y^2*z^2 + 11*z^4;
C := x^4 + 32*x^3*y + 8*x^2*y^2 + 19*x*y^3 + 28*y^4 +9*x^2*z^2 + 35*x*y*z^2 + 35*z^4;
//x^4 + 1117*x^3*y + 1463*x^2*y^2 + 830*x*y^3 + 549*y^4 +1584*x^2*z^2 + 1790*x*y*z^2 + 1062*y^2*z^2 + 95*z^4;
C:=C/(MonomialCoefficient(C,z^4));


hmons := [x^2*z^2,x*y*z^2,y^2*z^2];
hs := [ MonomialCoefficient(C, hmon) : hmon in hmons ];

h := -hs[1]*x^2-hs[2]*x*y -hs[3]*y^2;

fgmons := [x^4,x^3*y,x^2*y^2,x*y^3,y^4];
fgs := [ MonomialCoefficient(C, fgmon) : fgmon in fgmons ];

fg:= fgs[1]*x^4+fgs[2]*x^3*y+fgs[3]*x^2*y^2+fgs[4]*x*y^3+fgs[5]*y^4;


fac := Factorization(fg);
print fac;
if #fac eq 4 then
	g:= fac[1][1]*fac[4][1];
	f:= fac[2][1]*fac[3][1];
end if;
if #fac eq 2 then
        if TotalDegree(fac[1][1]) eq 2 then
    	    f:=fac[1][1];
            g:=fac[2][1];
        end if;
end if;
if #fac eq 3 then
     if TotalDegree(fac[1][1]) eq 2 then
        f:=fac[1][1];
        g:=fac[2][1]*fac[3][1];
    end if;
    if TotalDegree(fac[2][1]) eq 2 then
        f:=fac[2][1];
        g:=fac[3][1]*fac[1][1];
    else 
        f:=fac[3][1];
        g:=fac[1][1]*fac[2][1];
    end if;
end if;

mons := [ x^2, x*y, y^2 ];
fs := [ MonomialCoefficient(f, mon) : mon in mons ];
gs := [ MonomialCoefficient(g, mon) : mon in mons ];



A := Matrix([ fs, hs, gs ]);
B := Transpose(A^(-1));

print B;

a := B[1,1] + 2*B[2,1]*t + B[3,1]*t^2;
b := B[1,2] + 2*B[2,2]*t + B[3,2]*t^2;
c := B[1,3] + 2*B[2,3]*t + B[3,3]*t^2;

print a;
print b;
print c;

p := b*(b^2 - a*c);
H:= HyperellipticCurve(p);
print LPolynomial(H,5);


I := IgusaInvariants(H);
W := [ 2, 4, 6, 8, 10 ];
print WPSNormalize(W, I);

p2 := (t + 3)*(t + 1)*t*(t - 1)*(t - 3)*(t - 4);
H2:= HyperellipticCurve(p2);
print LPolynomial(H2,5);

I := IgusaInvariants(H2);
print WPSNormalize(W, I);
/*
A2 := AffineSpace(P); 
Eeq := fgs[1]*u^4+fgs[2]*u^3+fgs[3]*u^2+fgs[4]*u+fgs[5]+v^2 -hs[1]*u^2*v-hs[2]*u*v -hs[3]*v;
Sch := Scheme(A2,Eeq);
E := Curve(Sch);
E := ProjectiveClosure(E);
E := EllipticCurve(E);
print jInvariant(E);
E0 := EllipticCurve(HyperellipticCurve((t - 1)*t*(t + 1)*(t + 2)));
print jInvariant(E0);*/
