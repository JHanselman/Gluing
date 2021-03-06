intrinsic Polredabs(f::RngUPolElt : Best := false) -> RngUPolElt, SeqEnum, BoolElt
  { A smallest generating polynomial of the number field, using pari. }

  if Best then
    cmdp := "polredbest";
  else
    cmdp := "polredabs";
  end if;
  
  try
    cmd := Sprintf(
       "{u = %o(Pol(Vecrev(%o)),1); print(Vecrev(Vec(u[1])),Vecrev(Vec(lift(u[2]))))}", 
       cmdp, Coefficients(f));
    s := Pipe("gp -q", cmd);
    c := Index(s,"][");
    spol := s[1..c];
    sroot := s[c+1..#s-1];
    sspol := [ StringToInteger(x) : x in Split(spol, ", []\n") | x ne "" ];
    ssroot := [ StringToRational(x) : x in Split(sroot, ", []\n") | x ne "" ];
    assert #ssroot le Degree(f);
    ssroot := ssroot cat [0 : i in [1..Degree(f)-#ssroot]];
  catch e
    printf "WARNING: need gp at command-line for polredabs!";
    return f, [0,1] cat [0: i in [1..Degree(f)-2]], false;
  end try; 
  return Parent(f) ! sspol, ssroot, true;
end intrinsic;

intrinsic Polredbestabs(f::RngUPolElt) -> RngUPolElt, SeqEnum, BoolElt
  { A smallest generating polynomial of the number field, using pari.  First polredbest, then polredabs.}

  fbest, fbest_root := Polredabs(f : Best := true);
  fredabs, fredabs_root, bl := Polredabs(fbest);
  
  K := NumberField(f);
  Kbest := NumberField(fbest);
  iotabest := hom<K -> Kbest | fbest_root>;
  Kredabs := NumberField(fredabs);
  iotaredabs := hom<Kbest -> Kredabs | fredabs_root>;
  iota := iotabest*iotaredabs;  // functional composition is backwards in Magma, for some reason
  return fredabs, Eltseq(iota(K.1)), bl;
end intrinsic;

intrinsic Polredabs(K::FldNum : Best := false) -> FldNum, Map, BoolElt
  { A smallest generating polynomial of the number field, using pari. }

  if Degree(K) le 1 then
    assert K eq RationalsAsNumberField();
    return K;
  else
    fredabs, fredabs_root, bl := Polredabs(DefiningPolynomial(K));
    Kredabs := NumberField(fredabs);
    iotaredabs := hom<K -> Kredabs | fredabs_root>;
    return Kredabs, iotaredabs, bl;
  end if;
end intrinsic;

intrinsic Polredbestabs(K::FldNum) -> RngUPolElt, Map, BoolElt
  { A smallest generating polynomial of the number field, using pari.  First polredbest, then polredabs.}

  if Degree(K) le 1 then
    assert K eq RationalsAsNumberField();
    return K;
  else
    f := DefiningPolynomial(K);
    fbest, fbest_root, bl0 := Polredabs(f : Best := true);
    fredabs, fredabs_root, bl1 := Polredabs(fbest);
    assert bl0 eq bl1;
    
    Kbest := NumberField(fbest);
    iotabest := hom<K -> Kbest | fbest_root>;
    Kredabs := NumberField(fredabs);
    iotaredabs := hom<Kbest -> Kredabs | fredabs_root>;
    iota := iotabest*iotaredabs;  // functional composition is backwards in Magma, for some reason
    return Kredabs, iota, bl0;
  end if;
end intrinsic;
