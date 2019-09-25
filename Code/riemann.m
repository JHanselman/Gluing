
/* given the list T of theta constants, we compute the moduli [a1,a2,a3,ap1,ap2,ap3,as1,as2,as3]

Note that the characteristic of the theta is given by the binary expansion (a,b) of its index in the list and we but in place 64 the [0,0] characteristic.

Note that we only need 18 of them!
*/

function ModuliFromTheta(T);
	I:=Parent(T[1]).1;
	a1:=I*T[33]*T[5]/(T[40]*T[12]);
	a2:=I*T[21]*T[49]/(T[28]*T[56]);
	a3:=I*T[7]*T[35]/(T[14]*T[42]);
	ap1:=I*T[5]*T[54]/(T[27]*T[40]);
	ap2:=I*T[49]*T[2]/(T[47]*T[28]);
	ap3:=I*T[35]*T[16]/(T[61]*T[14]);
	as1:=-T[54]*T[33]/(T[12]*T[27]);
	as2:=T[2]*T[21]/(T[56]*T[47]);
	as3:=T[16]*T[7]/(T[42]*T[61]);
	return [a1,a2,a3,ap1,ap2,ap3,as1,as2,as3];
end function;

/* let us assume that we have an Aronhold system of the form
x1,x2,x3,x1+x2+x3,a1*x1+a2*x2+a3*x3,ap1*x1+ap2*x2+ap3*x3,as1*x1+as2*x2+as3*x3
given by the list [a1,a2,a3,ap1,ap2,ap3,as1,as2,as3] of its "moduli".
Compute the u1,u2,u3 such that sqrt(x1*u1)+sqrt(x2*u2)+sqrt(x3*u3)=0 is a Riemann model of the quartic.

Note that, as I understand Weber's formula we should get that the k,kp,ks are respectively -1,-1,1. If this is the case, we can simplify the computation below.
*/


function RiemannModelFromModuli(l);
	a1:=l[1];a2:=l[2];a3:=l[3];
	ap1:=l[4];ap2:=l[5];ap3:=l[6];
	as1:=l[7];as2:=l[8];as3:=l[9];
	F:=Parent(a1);
	P<x1,x2,x3>:=PolynomialRing(F,3);
/*
	M:=Matrix([[1/a1,1/ap1,1/as1],[1/a2,1/ap2,1/as2],[1/a3,1/ap3,1/as3]]);
	V:=Vector(F,[-1,-1,-1]);
	S:=V*Transpose(M^(-1));
	lambda:=S[1];lambdap:=S[2];lambdas:=S[3];
	M2:=Matrix([[lambda*a1,lambdap*ap1,lambdas*as1],[lambda*a2,lambdap*ap2,
	lambdas*as2],[lambda*a3,lambdap*ap3,lambdas*as3]]);
	S2:=V*Transpose(M2^(-1));
	k:=S2[1];kp:=S2[2];ks:=S2[3];
*/
	k:=1;kp:=1;ks:=1;
	M:=Matrix([[1,1,1],[k*a1,k*a2,k*a3],[kp*ap1,kp*ap2,kp*ap3]]);
	Mb:=Matrix([[1,1,1],[1/a1,1/a2,1/a3],[1/ap1,1/ap2,1/ap3]]);
	U:=-Mb^(-1)*M;
	u1:=U[1];
	u2:=U[2];
	u3:=U[3];
	u1:=u1[1]*x1+u1[2]*x2+u1[3]*x3;
	u2:=u2[1]*x1+u2[2]*x2+u2[3]*x3;
	u3:=u3[1]*x1+u3[2]*x2+u3[3]*x3;
	return (x1*u1+x2*u2-x3*u3)^2-4*x1*u1*x2*u2;
end function;


/*
F:=GF(37);
l:=[Random(F) : i in [1..9]];
C:=RiemannModelFromModuli(l);
DixmierOhnoInvariantsLight(C);
*/



//tau:=Matrix(C,[[3/2+3*I*Sqrt(19)/2,1/2+I*Sqrt(19)/2,0],[1/2+I*Sqrt(19)/2,-29/5+I*Sqrt(19)/5,-3/5],[0,-3/5,29/50+I*Sqrt(19)/50]]);
