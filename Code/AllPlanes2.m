load "KummerFunctions.m";

SetSeed(1);


//Define the base field and the function field
FFp := FiniteField(37);
//FFp := Rationals();
RL := PolynomialRing(FFp);
L := FieldOfFractions(RL);

//Define the curves we want to glue

T<x,y> :=PolynomialRing(FFp,2);

//The elliptic curve
g := (x - 1)*x*(x + 1)*(x + 2);
g := g-y^2;
A2:= AffineSpace(T);
X1:=Scheme(A2,g);
X1:=Curve(X1);
X1:=ProjectiveClosure(X1);
X1:=EllipticCurve(X1);

//The hyperelliptic curve
R<x> := PolynomialRing(FFp);
f := (x + 3)*(x + 1)*x*(x - 1)*(x - 3)*(x - 4);

/* Eq of divisor:
    x^2 + a1 x + a2 = 0
    y = b1 x + b2
*/

K,y2:=CalculateKummer(f);
F:= DefiningEquation(K);


S3<x1,x2,x3,x4> := PolynomialRing(L,4);

Sing := SingularSubscheme(K);
nodes := [ P : P in Points(Sing) ];

//Iterate over every pair of singular points
D:= [1..16];
CP:= CartesianPower(D,2);
CP:= [<1,2>,<1,3>,<1,4>,<1,5>,<1,6>,<1,7>,<1,8>,<1,9>,<1,10>,<1,11>,<1,12>,<1,13>,<1,14>,<1,15>,<1,16>];
for tup in CP do
    m,n:= Explode(tup);
    if m lt n then


        Is := [];
        Xs := [];
        Irrs := [];
        Q1:= nodes[m];
        Q2:= nodes[n];
        
        print m,n;
        //Find all planes that go through the two nodes with a given j-invariant.
        Planes:=FindPlanes(K,X1,Q1,Q2);
        //Planes := Planes[[1]];

        //Equation for the Kummer.
	K_eq := S3 ! F;

        for plane in Planes do
            
            print plane;
            KK:=BaseRing(plane);
            S3<x1,x2,x3,x4>:=PolynomialRing(KK,4);


            //Equation for the plane.
            H:=plane[1];
            H_eq:= x1*H[1]+x2*H[2]+x3*H[3]+x4*H[4];

            //Check if H intersected with K actually gives an elliptic curve with given j-invariant.
            S:= Scheme(ProjectiveSpace(S3),[S3!F,H_eq]);
            S:= ReducedSubscheme(S);
            C:= Curve(S);
            if Genus(C) eq 1 then
                E:= EllipticCurve(C);
                print "j(H intersect K) equal to j(X1)?";
                print jInvariant(X1) eq jInvariant(E);

                //Map equation for y^2=b2^2 to S4.
                y2:= Numerator(y2);
	        S4<x1,x2,x3,x4,y>:=ChangeRing(Parent(y2),KK);
                y2:= S4!y2;
	        h:= hom<S3 -> S4|[x1,x2,x3,x4]>;

                print h(K_eq);
                print h(H_eq);
                print y2;

                //Calculate the glueing of the curve.
                S:=Scheme(ProjectiveSpace(S4),[h(K_eq),h(H_eq),y2]);
                Irr := IrreducibleComponents(S);
                print "The number of irreducible components is:";
                print #Irr;
                Append(~Irrs, #Irr);
                for comp in Irr do
                    C := ReducedSubscheme(comp);
                    C := Curve(C);
                    if Genus(C) eq 3 then
                        phi:=CanonicalMap(C);
                        D := phi(C);
                        if Genus(D) eq 3 then

                            print D;
                            I,W := DixmierOhnoInvariants(DefiningEquation(D));
                            Append(~Is, WPSNormalize(W, I));
                            Append(~Xs, D);
                        else
                            Append(~Is, [0,0]);
                            Append(~Xs, D);
                        end if;
                    end if;
                end for;
            end if;
        end for;
        Write("algebraicall3.m", [m,n]);
        Write("algebraicall3.m", Planes);
        Write("algebraicall3.m", Irrs);
        Write("algebraicall3.m", Is);
        Write("algebraicall3.m", Xs);

    end if;
end for;

