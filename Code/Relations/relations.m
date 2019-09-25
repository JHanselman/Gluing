SetMemoryLimit(16*10^9);
load "ingredients.m";

R<a4,a3,a2,a1,a0> := PolynomialRing(QQ, 5);
S<x> := PolynomialRing(R);
f1 := a4*x^4 + a3*x^3 + a2*x^2 + a1*x + a0;
f2 := x*(a4*x^4 + a3*x^3 + a2*x^2 + a1*x + a0);

I1s := BinaryQuarticInvariants(f1);
I2s := IgusaInvariants(f2);
I2s := [ I2s[1], I2s[2], I2s[3], I2s[5] ];

B1 := 12;
B2 := 60;
bidegs := [ [i, j] : i in [B1..B1], j in [B2..B2] ];

for bideg in bidegs do
    print bideg;
    deg := &+bideg;
    R1 := PolynomialRing(QQ, [2, 3]);
    R2 := PolynomialRing(QQ, [2, 4, 6, 10]);

    mons1 := MonomialsOfWeightedDegree(R1, bideg[1]);
    mons2 := MonomialsOfWeightedDegree(R2, bideg[2]);

    if #mons1*#mons2 ne 0 then
        evs := [ ];
        for mon1 in mons1 do
            for mon2 in mons2 do
                ev1 := Evaluate(mon1, I1s);
                ev2 := Evaluate(mon2, I2s);
                ev := ev1*ev2;
                Append(~evs, ev);
            end for;
        end for;

        mons := MonomialsOfDegree(R, deg);
        M := Matrix([ [ MonomialCoefficient(ev, mon) : mon in mons ] : ev in evs ]);
        K := Kernel(M);
        if Dimension(K) ne 0 then
            print "Non-zero kernel!";
        end if;
    end if;
end for;

exit;
