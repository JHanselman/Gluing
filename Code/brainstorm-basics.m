function MultivariableToSingleVariablePolynomial(f)
  // Input: A polynomial of type RingMPolElt, but which only involves one of the variables
  // Output: The same polynomial, but now of type RingUPolElt
  K := BaseRing(Parent(f));
  cs := Coefficients(f);
  cs := Reverse(cs);
  R<u> := PolynomialRing(K);
  f_new := R!cs;
  return f_new;
end function;

function HomogeneousPartOfDegree(f,d)
  cs, mons:= CoefficientsAndMonomials(f);
  f_d := Parent(f)!0;
  for i := 1 to #cs do
    if Degree(mons[i]) eq d then
      f_d +:= cs[i]*mons[i];
    end if;
  end for;
  return f_d;
end function;

function CrossRatio(z1,z2,z3,z4)
  // Compute the cross ratio of the four numbers z1, z2, z3, z4
  return (z3-z1)*(z4-z2)/((z3-z2)*(z4-z1));
end function;

function EvaluateGen(pol, vals)
  if #vals eq 1 then
      return Evaluate(pol, vals[1]);
  end if;
  return Evaluate(pol, vals);
end function;

function MonomialGen(R, exps);
  if #exps eq 1 then
    return R.1^exps[1];
  end if;
  return Monomial(R, exps);
end function;

function EvaluateField(f, vals)
  R := Parent(f);
  n := Rank(R);
  K := BaseRing(R);

  K0 := Parent(vals[1]);
  R0 := PolynomialRing(K0, n);

  f0 := R0 ! 0;
  for mon in Monomials(f) do
      coeff := MonomialCoefficient(f, mon);
      num := Numerator(coeff);
      den := Denominator(coeff);
      num0 := EvaluateGen(num, vals);
      den0 := EvaluateGen(den, vals);
      coeff0 := num0/den0;
      mon0 := MonomialGen(R0, Exponents(mon));
      f0 +:= coeff0*mon0;
  end for;
  return f0;
end function;

/*
function MobiusTransformationFixed(z1,z2,z3)
  // Output: Mobius transformation mapping z1, z2, z3 to 0, 1, oo, respectively.
  K! := Parent(z1);

end function;
*/

/*
function FunctionFieldToPolynomial(f)

end function;

function MakeHyperellipticCurve(E,num,den);

end function;
*/
