function RationalReconstruction(r);
	r1:=Real(r);
	r2:=Imaginary(r);
	p:=Precision(r2);
	if r2 ne Parent(r2)!0 then
		e:=Log(AbsoluteValue(r2));
	else
		e:=-p;
	end if;
	if -e lt p/2 then
		print "not a real";
		return false;
	end if;
	best:=0;
	i:=p div 10;
	b:=BestApproximation(r1,10^i);
	while b ne best and i le p do
		i:=i+5;
		best:=b;
		b:=BestApproximation(r1,10^i);
		//print b;
	end while;
	if b ne best then
		print "not enough precision";
		return false;
	else
		return b,i;
	end if;
end function;


function RationalRelation(a2,a1,a);
	L2:= LinearRelation([1,a1,a1^2,a1^3,a1^4,a1^5,a2]);
	return -1/L2[7]*(1*L2[1]+L2[2]*a+L2[3]*a^2+L2[4]*a^3+L2[5]*a^4+L2[6]*a^5);
end function;



function average(a);
 if a eq 0 then
 	return -Precision(a);
 else
 	return Floor(Log(AbsoluteValue(a)));
 end if;
end function;


function RationalReconstructionAlt(alpha);

if Abs(Im(alpha)) gt 10^-30 then
    print Abs(Im(alpha));
    print Abs(Re(alpha));
    error "Imaginary part too large";
end if;
L := ContinuedFraction(Real(alpha));
L0 := [ ];
for c in L do
    if Abs(c) lt 10^100 then
        Append(~L0, c);
    else
        break;
    end if;
end for;
M := Convergents(L0);
return M[1,1]/M[2,1];

end function;
