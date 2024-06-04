/*  

 *** sl2f16.m ***

Add-on appendix to the paper "A polynomial with Galois group SL2(F16)".
Author: Johan Bosman.
Date: 13-08-2008.

    
 *** Usage of this file. ***

This file is to be used with MAGMA. Attach its intrinsics by typing the following in a MAGMA prompt:
> Attach("sl2f16.m");

You will now be able to compute polynomials that belong to Galois representations associated to modular forms. As an 
example of how to use it, we will show how to compute the polynomial described in the paper. First, we need the right 
modular forms space:
> S := CuspForms(Gamma0(137),2);

There are two Galois orbits of newforms in this space and we wish to pick the first one:
> f := Newform(S,1);

Now we want to pick the prime (2) of the number field Kf:
> OKf := MaximalOrder(BaseRing(Parent(f)));
> two := Decomposition(OKf,2)[1][1];

And we call the intrinsic that computes the polynomial:
> pol := ComputePGLPolynomial(f,two);

Note that this result is not proven. The computations described in the paper to prove the result is correct have all 
standard implementations in MAGMA hence are not included in this file.



 *** Remarks ***

This packages runs best under MAGMA versions 2.13-*. Older versions tend to have weak LLL-implementations and have a 
memory leak in the computation of hecke operators.

Note that there are many bugs in this code. The code currently doesn't work for modular forms of composite level and 
weight 2; also, for weight bigger than 2 the level has to be 1. It doesn't work for exceptional representations, nor for 
representations that can be found as the l-torsion of  an elliptic curve (these cases can be treated with old methods 
anyway).

Any user who makes bug fixes and/or improvements to this software is encouraged to make the author aware of this by 
sending a mail describing his/her modifications to jgbosman@math.leidenuniv.nl

*/








intrinsic Mul(M :: Mtrx, N :: Mtrx) -> Mtrx
{}
  m := NumberOfColumns(M);
  n := NumberOfRows(N);
  assert m eq n;
  
  r1 := NumberOfRows(M);
  r2 := NumberOfColumns(N);
  
  return Matrix([[ &+[M[j][k]*N[k][i] : k in [1 .. n] ] : i in [1 .. r2] ] : j in [1 .. r1] ]);
end intrinsic;


intrinsic 'in'(a :: ., bs :: Tup) -> BoolElt
{}
  for b in bs do
    if a eq b then return true; end if;
  end for;
  return false;
end intrinsic;


intrinsic 'cat'(as :: Tup, bs :: Tup) -> Tup
{}
  result := as;
  for b in bs do 
    Append(~result,b);
  end for;
  return result;
end intrinsic; 


intrinsic Remove(as :: Tup, a :: .) -> Tup
{}
  res := <>;
  i := 1;
  while (i le #as) and not(as[i] cmpeq a) do
    Append(~res,as[i]);
    i +:= 1;
  end while;
  
  for j := i+1 to #as do
    Append(~res,as[j]);
  end for;
  
  return res;
end intrinsic;



intrinsic Zeroes(K :: FldNum, n :: RngIntElt) -> SeqEnum
{}
  res := [];
  for place in InfinitePlaces(K) do
    root := Evaluate(K.1, place : Precision := n);
    if IsReal(place) then
      Append(~res,root);
    else
      res cat:= [root,ComplexConjugate(root)];
    end if;
  end for;
  return res;
end intrinsic;


intrinsic Zeroes(P :: RngUPolElt, n :: RngIntElt) -> SeqEnum
{}
  return Zeroes(NumberField(P),n);
end intrinsic;



intrinsic Inverse(M :: Mtrx) -> Mtrx
{ Computes the inverse and is numerically much better than MAGMA's standard procedure.
}
  M1 := M; n := NumberOfRows(M);
  assert n eq NumberOfColumns(M);
  Re := BaseRing(M); N := IdentityMatrix(Re,n);
  for i := 1 to n do
    if i ne n then
      _, goodrow := Max([ Abs(M1[j,i]) : j in [i .. n] ]);
      goodrow +:= i-1;
      if goodrow ne i then
        SwapRows(~M1,i,goodrow);
        SwapRows(~N,i,goodrow);
      end if;
    end if;
    factor := One(Re)/M1[i,i];
    MultiplyRow(~M1,factor,i);
    MultiplyRow(~N,factor,i);
    for j := 1 to i-1 do 
      AddRow(~N,-M1[j,i],i,j);
      AddRow(~M1,-M1[j,i],i,j);
    end for;
    for j := i+1 to n do
      AddRow(~N,-M1[j,i],i,j);
      AddRow(~M1,-M1[j,i],i,j);
    end for;
  end for;
  return N, M1;
end intrinsic;


intrinsic '+'(x::SeqEnum, y::SeqEnum) -> SeqEnum
{ Addition of complex numbers in terms of pairs of reals, or of vectors in terms of sequences.}
  return [ x[i]+y[i] : i in [1 .. #x] ];
end intrinsic;

intrinsic '+'(x::Tup, y::Tup) -> Tup
{ Componentwise addition. }
  return < x[i]+y[i] : i in [1 .. #x] >;
end intrinsic;

intrinsic '-'(x::SeqEnum, y::SeqEnum) -> SeqEnum
{ Subtraction of complex numbers in terms of pairs of reals, or of vectors in terms of sequences. }
  return [ x[i]-y[i] : i in [1 .. #x] ];
end intrinsic;



intrinsic Mul(x::SeqEnum, y::SeqEnum) -> SeqEnum
{ Multiplication of complex numbers in terms of pairs of reals. }
  return [ x[1]*y[1]-x[2]*y[2], x[1]*y[2]+x[2]*y[1] ];
end intrinsic;

intrinsic '*'(x::SeqEnum, y::SeqEnum) -> SeqEnum
{ Multiplication of complex numbers in terms of pairs of reals. }
  return [ x[1]*y[1]-x[2]*y[2], x[1]*y[2]+x[2]*y[1] ];
end intrinsic;


intrinsic Div(x::SeqEnum, y::SeqEnum) -> SeqEnum
{ Division of complex numbers in terms of pairs of reals. }
  d := y[1]*y[1]+y[2]*y[2];
  return [ (x[1]*y[1]+x[2]*y[2])/d, (x[2]*y[1]-x[1]*y[2])/d ];
end intrinsic; 

intrinsic '/'(x::SeqEnum, y::SeqEnum) -> SeqEnum
{ Division of complex numbers in terms of pairs of reals. }
  d := y[1]*y[1]+y[2]*y[2];
  return [ (x[1]*y[1]+x[2]*y[2])/d, (x[2]*y[1]-x[1]*y[2])/d ];
end intrinsic; 


intrinsic Pow(x::SeqEnum, n::RngIntElt) -> SeqEnum
{ Complex number raised to an integer power in terms of pairs or reals. }
  if n eq 0 then return [One(Parent(x[1])),Zero(Parent(x[2]))]; end if;
  if n gt 0 then 
    if IsEven(n) then
      temp := Pow(x, n div 2);
      return Mul(temp,temp);
    else
      return Mul(x, Pow(x,n-1));
    end if;
  else
    temp := Pow(x,-n);
    return Div( [One(Parent(x[1])),Zero(Parent(x[2]))], temp);
  end if;
end intrinsic;

intrinsic '^'(x::SeqEnum, n::RngIntElt) -> SeqEnum
{ Complex number raised to an integer power in terms of pairs or reals. }
  if n eq 0 then return [One(Parent(x[1])),Zero(Parent(x[2]))]; end if;
  if n gt 0 then 
    if IsEven(n) then
      temp := Pow(x, n div 2);
      return Mul(temp,temp);
    else
      return Mul(x, Pow(x,n-1));
    end if;
  else
    temp := Pow(x,-n);
    return Div( [One(Parent(x[1])),Zero(Parent(x[2]))], temp);
  end if;
end intrinsic;



intrinsic Exp(x::SeqEnum) -> FldComElt
{ Exponential of a complex number represented as a pair of reals. Output is represented as a complex number. }
  C<I> := ComplexField(Precision(x[2]));
  return Exp(I*x[2])*Exp(x[1]);
end intrinsic;


intrinsic '*'(gamma :: Mtrx, tau :: SeqEnum[FldReElt]) -> SeqEnum
{ }
  a := gamma[1][1]; b := gamma[1][2]; c := gamma[2][1]; d := gamma[2][2];
  return Div([a*tau[1]+b,a*tau[2]],[c*tau[1]+d,c*tau[2]]);
end intrinsic;


intrinsic Random(a :: FldReElt, b :: FldReElt) -> FldReElt
{ Input: two real numbers a and b of a fixed precision field
  Output: a random number in [a,b]
}
  Re := Parent(a);
  prec := Precision(a);
  factor := 10^prec;
  inta := Ceiling(a*factor); intb := Floor(b*factor);
  
  return Re!(Random(inta,intb)/factor);
end intrinsic;



intrinsic Rows(M :: Mtrx) -> SeqEnum
{ Outputs the sequence of row vectors of M.
}
  rowlength := NumberOfColumns(M);
  eltseq := Partition(Eltseq(M),rowlength);
  return [Vector(x) : x in eltseq];
end intrinsic;  




intrinsic ComplexToRealRows(M :: ModMatFldElt) -> ModMatFldElt
{ Input: a matrix over the complex numbers
  Output: the matrix obtained over the real numbers by interpreting a+bi as a row vector (a b)
} 
  C := BaseRing(Parent(M));
  rows := NumberOfRows(M); columns := NumberOfColumns(M);
  M1 := &cat [[Real(elt),Imaginary(elt)]: elt in Eltseq(M)];
  R := Parent(M1[1]);
  MR := KMatrixSpace(R,rows,2*columns);
  M2 := MR!M1;
  return M2;
end intrinsic;


intrinsic ComplexToRealVector(vec :: ModTupFldElt) -> ModTupFldElt
{ Input: a row vector over the complex numbers
  Output: the vector obtained over the real numbers bij interpreting a+bi as (a b)
}
  C := BaseRing(Parent(vec));
  g := Dimension(Parent(vec));
  v1 := &cat [[Real(elt),Imaginary(elt)]: elt in Eltseq(vec)];
  R := Parent(v1[1]);
  VR := KSpace(R,2*g);
  return VR!v1;
end intrinsic;



intrinsic RealToComplexVector(vec :: ModTupFldElt) -> ModTupFldElt
{ Input: a row vector over the real numbers.
  Output: the corresponding vector over the complex numbers
}
  Re := BaseRing(Parent(vec));
  C<I> := ComplexField(Precision(Re));
  dim := Dimension(Parent(vec));
  elts := [];
  for i := 1 to dim-1 by 2 do
    Append(~elts, C![vec[i],vec[i+1]]);
  end for;
  return KSpace(C,dim div 2)!elts;
end intrinsic;



intrinsic MatrixToVector(M :: Mtrx) -> ModTupRngElt
{ Writes the matrix as vector consisting of all the entries.
}
  return Vector(Eltseq(M));
end intrinsic;


WtoV := function(W,v,BK,degK,degV)
  vec := [];
  for i := 1 to degV do
    a := Zero(BaseRing(W));
    for j := 1 to degK do
      a +:= v[(i-1)*degK+j]*BK[j];
    end for;
    Append(~vec,a);
  end for;  
  return vec;
end function;



VtoW := function(v,BV)
  vec := [];
  for w in Eltseq(v) do
    vec cat:=Eltseq(w);
  end for;
  return vec;
end function;


intrinsic ToQSpace(V :: ModTupFld) -> ModTupFld, Map, Map
{ Input: a vectorspace V over a cyclotomic field K.
  Output: the vectorspave W over Q that V is, with maps V->W and W->V
}
  BV := Basis(V);
  K := BaseRing(V);
  if (Type(K) eq FldRat) then
    idV := map < V -> V | v :-> v >;
    return V, idV, idV;
  end if;
 //hmm, er kunnen blijkbaar ook cyclotomische lichamen van orde 2 uitkomen.
 
    
  BK := Basis(K);
  zm := BK[2];
  degV := Degree(V);
  degK := Degree(K);
  dimV := Dimension(V);
  
  vec := []; c := One(K);
  for i := 1 to degK do
    for v in BV do
      for w in Eltseq(c*v) do
        vec cat:=Eltseq(w);
      end for;
    end for;
    c *:= zm;
  end for;
  
  m := dimV*degK;
  n := degV*degK;
  M := KMatrixSpace(Rationals(),m,n) ! vec;
  
  W := KSpaceWithBasis(M);  
  m1 :=  map < W -> V | v :-> V!WtoV(W,v,BK,degK,degV) >;
  m := map < V -> W | v :-> W!VtoW(v,BV) >;
  return W, m, m1;
end intrinsic;



intrinsic MakeMonic(f :: RngUPolElt) -> RngUPolElt
{ Turns a polynomial into a monic one defining the same number field.
}
  R := BaseRing(Parent(f));
  n := Degree(f);
  an := Eltseq(f)[n+1];
  coeffs := [an^(n-k)*Eltseq(f)[k] : k in [1 .. n]];
  Append(~coeffs,R!1);
  return Polynomial(coeffs);
end intrinsic;



intrinsic Matrix(b :: FldAlgElt) -> Mtrx
{ Input: an element b of a number field K.
  Output: multiplication with b is a Q-linear map from K to K. The output is the matrix that corresponds to this map (with right multiplication).
}
  return Matrix([Eltseq(x*b) : x in Basis(Parent(b))]);
end intrinsic;


intrinsic QMatrix(M :: Mtrx) -> Mtrx
{ Input: a matrix over a number field.
  Output: the corresponding matrix over Q: a K-vector space is a Q-vector space. 
      Right multiplication with M is a linear transformation of a Q-vector space this way.
}
  cols := NumberOfColumns(M);
  entries := Partition(Eltseq(M),cols);
  return VerticalJoin([HorizontalJoin([Matrix(entry) : entry in row]) : row in entries]);
end intrinsic;


intrinsic Matrix(b :: FldRatElt) -> Mtrx
{}
  return Matrix([[b]]);
end intrinsic;


intrinsic TraceMatrix(b :: FldRatElt) -> Mtrx
{}
  return Matrix([[b]]);
end intrinsic;


intrinsic InverseImage(M :: Mtrx, V :: ModTupFld) -> ModTupFld
{ Input: a matrix M and a vectorspace V, which is a subspace of the space on which M acts.
  Output: the inverse image of this map.
  Note: we assume that M is invertible and acts with right multiplication.
}
  K := BaseRing(V);
  basis := [b*M^(-1) : b in Basis(V)];
  return VectorSpaceWithBasis(basis);
end intrinsic;


intrinsic InverseImage(Ms :: SeqEnum[Mtrx], V :: ModTupFld) -> ModTupFld
{ Input: a sequence of matrices and a vectorspace. 
  Output: the intersection of InverseImage(M,V), with M running trough the sequence.
}
  return &meet [InverseImage(M,V) : M in Ms];
end intrinsic;


intrinsic TraceMatrix(a :: FldAlgElt) -> Mtrx
{ Input: an element of a number field.
  Output: the matrix belonging to x :-> Tr(xa) (seen as Q-linear map by right multiplication).
}
  return Matrix([[Trace(a*b)] : b in Basis(Parent(a))]);
end intrinsic;


intrinsic TraceMatrix(as :: SeqEnum[FldAlgElt]) -> Mtrx
{ Input: a sequence of elements of the same number field.
  Output: the matrix belonging to x :-> (Tr(xa[1]),...,Tr(xa[n])).
}
  return HorizontalJoin([TraceMatrix(a) : a in as]);
end intrinsic;  


intrinsic TraceMatrix(as :: SeqEnum[FldRatElt]) -> Mtrx
{ Input: a sequence of elements of the same number field.
  Output: the matrix belonging to x :-> (Tr(xa[1]),...,Tr(xa[n])).
}
  return HorizontalJoin([TraceMatrix(a) : a in as]);
end intrinsic;  


intrinsic TraceMatrix(ass :: Tup) -> Mtrx
{ Input: a tuple of sequences, each one separately consisting of elements of the same number field, but each sequence has to be of the same length.
  Output: the matrix belonging to (x1,...,xn) -> ( Sum_j Tr(x[j]a[j][1]), ..., Sum_j Tr(x[j]a[j][m]) ).
}
  return VerticalJoin(<TraceMatrix(as) : as in ass>);
end intrinsic;



intrinsic ClosestVector(lattice :: Lat, point :: ModTupFldElt) -> LatElt,FldReElt
{ Input: a lattice (sublattice of a real vectorspace.
    AND  a point in the overlying vectorspace.
  Output: the point of the lattice closest to the input point.
    AND  the distance between those points.
  Note: this seems to work better than the standard procedure??????
}
  n := 1;
  repeat
    vecs := CloseVectors(lattice,point,n);
    n *:= 2;
  until #vecs ne 0;
  return vecs[1][1], vecs[1][2];
end intrinsic;



intrinsic CloseVector(lattice :: Lat, point :: ModTupFldElt) -> LatElt, FldReElt
{ Input: a lattice (sublattice of a real vectorspace.
    AND  a point in the overlying vectorspace.
  Output: a point of the lattice close to the input point.
    AND  the distance between those points.
}
  lllmatrix := LLLBasisMatrix(lattice);
  vec := point*Inverse(lllmatrix);
  closepoint := &+ [Round(Eltseq(vec)[i])*lllmatrix[i] : i in [1 .. #Eltseq(vec)]];
  
  return closepoint, Norm(closepoint-point);
end intrinsic;




intrinsic ScalarMultiple(alpha :: FldNumElt, x :: SeqEnum, roots :: SeqEnum) -> SeqEnum
{ Multiplies the sequence x of complex numbers with alpha, embedded into C^deg(alpha) using all embeddings.
}
  beta := [EmbeddingAtRoot(alpha,root) : root in roots];
  return [beta[i]*x[i] : i in [1 .. #beta]];
end intrinsic;


intrinsic ScalarMultiple(alpha :: FldRatElt, x :: SeqEnum, roots :: SeqEnum) -> SeqEnum
{}
  return [alpha*x[1]];
end intrinsic;


intrinsic EmbeddingAtRoot(a :: FldNumElt, root :: FldComElt) -> FldComElt
{ Input: an element a of an absolute number field defined by an equation.
    AND  a complex number which is an approximation of the basic root of that equation.
  Output: the complex number that approximates a in this embedding.
}
  //Kan natuurlijk iets sneller door een tabel met root^i vantevoren te berekenen.
  //Hopelijk is dit niet de bottleneck dus laat het zo maar even.
  
  rooti := One(Parent(root));
  res := Zero(Parent(root));
  l := Flat(a);
  for i := 1 to #l do
    res +:= l[i]*rooti;
    rooti *:= root;
  end for;
  return res;
end intrinsic;



intrinsic EmbeddingAtRoot(a :: FldCycElt, root :: FldComElt) -> FldComElt
{}
  rooti := One(Parent(root));
  res := Zero(Parent(root));
  l := Eltseq(a);
  for i := 1 to #l do
    res +:= l[i]*rooti;
    rooti *:= root;
  end for;
  return res;
end intrinsic;



intrinsic EmbeddingAtRoot(a :: FldRatElt, root :: FldComElt) -> FldComElt
{ }  
  return Parent(root)!a;
end intrinsic;


intrinsic SeriesEmbeddingAtRoot(p :: RngSerPowElt, root :: FldComElt) -> RngSerPowElt
{ Input: a power series P over a number field K defined by an equation.
    AND  a complex number which is an approximation of the basic root of that equation.
  Output: the power series over C obtained by calculating the embeddings of the coefficients of P
}
  C := Parent(root);
  P<q> := PowerSeriesRing(C);
  qprec := AbsolutePrecision(p);
  res := O(q^qprec);
  for i := 0 to qprec-1 do
    res +:= EmbeddingAtRoot(Coefficient(p,i),root)*q^i;
  end for;
  return res;
end intrinsic;
  

intrinsic AllSeriesEmbeddings(p :: RngSerPowElt, roots :: SeqEnum) -> SeqEnum
{ Input: a power series over a number field K defined by an equation.
     AND the sequence of complex roots of the equation of K calculated to a certain precision.
  Output: the sequence of power series obtained by numerical substition of those roots.
}
  return [SeriesEmbeddingAtRoot(p,root) : root in roots];
end intrinsic;


intrinsic SeriesEmbeddingAtRoot(p :: RngSerLaurElt, root :: FldComElt) -> RngSerPowElt
{ Input: a Laurent series P over a number field K defined by an equation without negative terms.
    AND  a complex number which is an approximation of the basic root of that equation.
  Output: the power series over C obtained by calculating the embeddings of the coefficients of P
}
  C := Parent(root);
  P<q> := PowerSeriesRing(C);
  qprec := AbsolutePrecision(p);
  res := O(q^qprec);
  for i := 0 to qprec-1 do
    res +:= EmbeddingAtRoot(Coefficient(p,i),root)*q^i;
  end for;
  return res;
end intrinsic;
  

intrinsic AllSeriesEmbeddings(p :: RngSerLaurElt, roots :: SeqEnum) -> SeqEnum
{ Input: a Laurent series without negative terms over a number field K defined by an equation.
     AND the sequence of complex roots of the equation of K calculated to a certain precision.
  Output: the sequence of power series obtained by numerical substition of those roots.
}
  return [SeriesEmbeddingAtRoot(p,root) : root in roots];
end intrinsic;



intrinsic Divides(d :: RngIntElt, n :: RngIntElt) -> BoolElt, RngIntElt
{ Returns true iff d|n and if so the quotient.
} 
  if d eq 0 then
    if n eq 0 then return true,0; else return false,_; end if;
  end if;
  k := n div d;
  if k*d eq n then return true, k; else return false,_; end if;
end intrinsic;



intrinsic Split(n :: RngIntElt, Q :: RngIntElt) -> RngIntElt, RngIntElt
{ Returns n1 and n2 such that n1=prod_{p|Q)p^(v_p(n)) and n2=n/n1;
}
  primesinQ := [x[1] : x in Factorisation(Q)];
  n1 := &*[Integers()|p^Valuation(n,p) : p in primesinQ];
  return n1, n div n1;
end intrinsic;


intrinsic WQ(Q :: RngIntElt, N :: RngIntElt) -> Mtrx
{}
  if Q eq N then return Matrix([[0,-1],[N,0]]); end if;
  if Q eq 1 then return Matrix([[1,0],[0,N]]); end if;
  
  Q1 := N div Q;
  _,d,b := Xgcd(Q,-Q1);
  return Matrix([[Q,b],[N,Q*d]]);
end intrinsic;


intrinsic DecomposeSL2ZMatrix0(N :: RngIntElt, gamma :: Mtrx) -> ModMatRngElt, ModMatRngElt
{ Input: a squarefree number N.
    AND  a matrix gamma in SL2(Z).
  Output: matrices gamma' and gamma'' such that gamma' in Gamma0(N), gamma'' in the list of representants produced by RepresentantsForGamma0
          and gamma'*gamma''=gamma.
}
  MZ := RMatrixSpace(Integers(),2,2);
  c := gamma[2][1]; d := gamma[2][2];
  
  if (c mod N) eq 0 then
    return gamma, MZ![1,0,0,1];
  end if;
  
  if IsPrime(N) and IsOdd(N) then
    c1 := Modinv(c,N);
    j := (c1*d) mod N;
    if 2*j gt N then j -:= N; end if;
    return gamma*(MZ![j,1,-1,0]), MZ![0,-1,1,j];
  end if;
  
  Q1 := Gcd(N,c);
  Q := N div Q1;
  c1 := Modinv(c,Q);
  Q11 := Modinv (Q1,Q);
  j := (c1*d - Q11) mod Q;
  dd := 1 + Q1*j;
  
  _,a,b := Xgcd(Q+N*j,-Q1);
  a *:= Q;
  
  gamma1 := MZ![a,b,Q1,dd];
  j := a div Q1;
  gamma1 := MZ![1,-j,0,1] * gamma1;
  //blabla
  return gamma*gamma1^(-1),gamma1;
end intrinsic;



intrinsic RepresentantsForGamma0(N :: RngIntElt) -> SeqEnum
{ Input: squarefree number N.
  Output: a sequence of matrices which are representants for Gamma0(N)\SL2(Z)
}
  MZ := RMatrixSpace(Integers(),2,2);
  
  if (IsPrime(N) and IsOdd(N)) then
    result := [MZ![1,0,0,1]];
    for j:= -((N-1) div 2) to ((N-1) div 2) do 
      Append(~result,MZ![0,-1,1,j]);
    end for;
    return result;
  end if;
  
  result := [MZ![1,0,0,1]];
  
  for Q in Exclude(Divisors(N),1) do
    Q1 := N div Q;
    for j := 0 to Q-1 do
      dd := 1 + Q1*j;
      _,a,b := Xgcd(Q+N*j,-Q1);
      a *:= Q;
      gamma1 := MZ![a,b,Q1,dd];
      jj := a div Q1;
      gamma1 := MZ![1,-jj,0,1] * gamma1;
      Append(~result,gamma1);
    end for;
  end for;
  
  return result;  
end intrinsic;



intrinsic DecomposeSL2ZMatrix1(N :: RngIntElt, gamma :: Mtrx) -> ModMatRngElt, ModMatRngElt
{ Input: a squaurefree number N.
    AND  a matrix gamma in SL2(Z).
  Output: matrices gamma' and gamma'' such that gamma' in Gamma1(N), gamma'' in the list of representants produced by RepresentantsForGamma1
          and gamma'*gamma''=(+/-)gamma.
}
  MZ := RMatrixSpace(Integers(),2,2);
  gamma1,gamma2 := DecomposeSL2ZMatrix0(N,gamma);
  a := gamma1[1][1] mod N;
  if a gt (N-1) div 2 then
    gamma1 := -gamma1;
    a := gamma1[1][1] mod N;
  end if;
  if a ne 1 then c := N; else c := 0; end if;
  _, d, b := Xgcd(a,c); b := -b;
  gamma3 := MZ![a,b,c,d];
  
  return gamma1*gamma3^(-1), gamma3*gamma2;
end intrinsic;


//Als N even is gaat dit niet goed: 
intrinsic RepresentantsForGamma1(N :: RngIntElt) -> SeqEnum
{ Input: a squarefree number N.
  Output: a sequence of matrices gamma such that (+/-)gamma are representants for Gamma1(N)\SL2(Z)
}
  MZ := RMatrixSpace(Integers(),2,2);
  subresult := RepresentantsForGamma0(N);  
  result := [];
  for gamma in subresult do  
    for a:=1 to (N-1) div 2 do
      if Gcd(a,N) eq 1 then
        if a ne 1 then c:=N; else c:=0; end if;
        _, d, b := Xgcd(a,c); b := -b;
        Append(~result,(MZ![a,b,c,d])*gamma);
      end if;
    end for;
  end for;
  return result;
end intrinsic;




intrinsic RandomPointInFSL2(Re :: FldRe) -> SeqEnum
{ Input: a fixed precision real field.
  Output: a random point in SL2(Z)\h,   with respect to the hyperbolic area measure
}
  repeat
    x := Random(-One(Re)/2,One(Re)/2);
    a := Random(Zero(Re),2/3*Sqrt(3*One(Re)));
    y := One(Re)/a;
  until x^2 + y^2 ge One(Re);
  
  return [x,y];
end intrinsic;



intrinsic RandomPointInX0(Re :: FldRe, N :: RngIntElt) -> Tup
{}
  reps := RepresentantsForGamma0(N);
  gamma := reps[Random(1,#reps)];
  tau := RandomPointInFSL2(Re);
  return <gamma,tau>;
end intrinsic;  



intrinsic RandomPointInX1(Re :: FldRe, N :: RngIntElt) -> Tup
{}
  reps := RepresentantsForGamma1(N);
  gamma := reps[Random(1,#reps)];
  tau := RandomPointInFSL2(Re);
  return <gamma,tau>;
end intrinsic;  



intrinsic RandomPointsInX1(Re :: FldRe, N :: RngIntElt, n :: RngIntElt) -> SeqEnum
{ Input: a fixed precision real field.
    AND  a prime number N.
    AND  a positive integer n.
  Output: a sequence of n random points in X1(N).
}
  return [RandomPointInX1(Re,N) : i in [1 .. n] ];
end intrinsic;



intrinsic RewriteTau(tau :: SeqEnum) -> Tup
{ Input: tau in the upper half plane.
  Output: a tuple <gamma,tau1>, with gamma(tau1)=tau.
}
  gamma,tau1 := MatrixForTau0(tau,1);
  return <gamma^(-1), tau1>;
end intrinsic;


intrinsic RewriteTau(tau :: Tup) -> Tup
{ Input: tau in the upper half plane, represented as a tuple <gamma,tau'>.
  Output: a tuple <gamma,tau1>, with gamma(tau1)=tau.
}
  gamma,tau1 := MatrixForTau0(tau[2],1);
  return <tau[1]*gamma^(-1), tau1>;
end intrinsic;


intrinsic RewriteTaus(taus :: SeqEnum) -> SeqEnum
{ }
  return [ RewriteTau(tau) : tau in taus];
end intrinsic;



intrinsic '*'(r :: RngIntElt, tau :: Tup) -> Tup
{ Multiplies gamma*tau by r.
}
  gamma := tau[1];
  gamma11, gamma12 := DecomposeSL2ZMatrix0(r,gamma);
  a,b,c,d := Explode(Eltseq(gamma11));
  b *:= r; c div:= r;
  gamma1 := Matrix([[a,b],[c,d]]);
  a,b,c,d := Explode(Eltseq(gamma12));
  a *:= r; b *:= r;
  gamma2 := Matrix([[a,b],[c,d]]);
  tau1 := RewriteTau(gamma2*tau[2]);
  return <gamma1*tau1[1],tau1[2]>;
end intrinsic;




//Real and Imaginary also work on SeqEnums! 
//This is important because we have to store elements of h as pairs of real numbers, because of precision reasons.
findcd := function(tau, dd, N)
  xtau := Real(tau);
  ytau := Imaginary(tau);
  M := RMatrixSpace(RealField(),2,2) ! [xtau,ytau, 1,0];
  L := LatticeWithBasis(M);
  v := RSpace(RealField(), 2) ! [-dd/N,0];
  wtemp, dist := ClosestVectors(L,v); w := wtemp[1];
  coeffs := RSpace(RealField(),2)!w*Inverse(M);
  c := Round(coeffs[1]); d := Round(coeffs[2]);
  return <c,d,dist>;
end function;

findcd2 := function(tau,eps,N)
  if N eq 1 then
    xtau := Real(tau);
    ytau := Imaginary(tau);
    M := RMatrixSpace(RealField(),2,2) ! [xtau,ytau, 1,0];
    L := LatticeWithBasis(M);
    wtemp := ShortestVectors(L); w := wtemp[1];
    coeffs := RSpace(RealField(),2)!w*Inverse(M);
    c := Round(coeffs[1]); d := Round(coeffs[2]);
    return c,d;
  else  
    dist := 10; //>1 is sufficient
    for dd := 1 to N do
      if Evaluate(eps,dd) eq 1 then
        tup := findcd(tau,dd,N);
        if tup[3] lt dist then
          c := N*tup[1]; 
	  d := N*tup[2] + dd;
	  dist := tup[3];
        end if;
      end if;
    end for;
  end if;
  return c,d;
end function;

findcd3 := function(tau,N)
if N eq 1 then
    xtau := Real(tau);
    ytau := Imaginary(tau);
    M := RMatrixSpace(RealField(),2,2) ! [xtau,ytau, 1,0];
    L := LatticeWithBasis(M);
    wtemp := ShortestVectors(L); w := wtemp[1];
    coeffs := RSpace(RealField(),2)!w*Inverse(M);
    c := Round(coeffs[1]); d := Round(coeffs[2]);
    return c,d;
  else  
    dist := 10; //>1 is sufficient
    for dd := 1 to N do
      if(Gcd(dd,N) eq 1) then
        tup := findcd(tau,dd,N);
        if tup[3] lt dist then
          c := N*tup[1]; 
	  d := N*tup[2] + dd;
	  dist := tup[3];
        end if;
      end if;
    end for;
  end if;
  return c,d;
end function;


intrinsic MatrixForTau1(tau :: SeqEnum, N :: RngIntElt, eps :: GrpDrchElt) -> ModMatRngElt, SeqEnum
{ Input: a complex number tau in the upper half plane
    AND  an integer N indicating the level
    AND  a Dirichlet character eps on (Z/NZ)^*.
  Output: a 2x2-Matrix a,b,c,d in Gamma0(N) with eps(d)=1 which transforms tau to tau' 
          such that tau' has imaginary part maximized and -1/2<=Re(tau')<1/2.
    AND   tau'
  tau and tau' are represented as pairs of reals.
}
  c, d := findcd2(tau,eps,N);
  _, b, a := Xgcd(c,d);
  b := -b;
  //tau1 := (a*tau+b)/(c*tau+d);
  tau1 := Div([a*tau[1]+b,a*tau[2]],[c*tau[1]+d,c*tau[2]]);
  n := -Floor(Real(tau1)+1/2);
  a := a+n*c; b := b+n*d;
  return RMatrixSpace(Integers(),2,2) ! [a,b,c,d], [tau1[1]+n,tau1[2]];
end intrinsic;


intrinsic MatrixForTau0(tau :: SeqEnum, N :: RngIntElt) -> ModMatRngElt, SeqEnum
{ Input: a complex number tau in the upper half plane
    AND  an integer N indicating the level
  Output: a 2x2-Matrix a,b,c,d in Gamma0(N) which transforms tau to tau' 
          such that tau' has imaginary part maximized and -1/2<=Re(tau')<1/2.
    AND   tau'
  tau and tau' are represented as pairs of reals.  
}
  c, d := findcd3(tau,N);
  _, b, a := Xgcd(c,d);
  b := -b;
  //tau1 := (a*tau+b)/(c*tau+d);
  tau1 := Div([a*tau[1]+b,a*tau[2]],[c*tau[1]+d,c*tau[2]]);
  n := -Floor(Real(tau1)+1/2);
  a := a+n*c; b := b+n*d;
  return RMatrixSpace(Integers(),2,2) ! [a,b,c,d], [tau1[1]+n,tau1[2]];
end intrinsic;



intrinsic Zeroes(Q :: FldRat, prec :: RngIntElt) -> SeqEnum[FldPrElt]
{}
  return [RealField()!1];
end intrinsic;

  
  
intrinsic JacSymbol(n :: RngIntElt, m :: RngIntElt) -> RngIntElt
{}
  if m eq 1 then 
    return 1;
  else 
    return JacobiSymbol(n,m);
  end if;
end intrinsic;



intrinsic TwistedSymbol(CMKf :: ModSym, l :: RngIntElt) -> ModSymElt
{}
  if l eq 1 then 
    return CMKf!<1,[Cusps()|Infinity(),0]>;
  end if;
  G<ch> := DirichletGroup(l,Integers());
  chi := BaseChange(ch,BaseField(CMKf));
  
  return TwistedWindingElement(CMKf,1,chi);
end intrinsic;



intrinsic IsLinearlyIndependent(vs :: SeqEnum[ModTupFldElt]) -> BoolElt
{}
  return #vs eq Rank(Matrix(vs));
end intrinsic;



intrinsic SearchGoodVectorSum(vs :: SeqEnum[ModTupFldElt], m :: RngIntElt, v :: ModTupFldElt, Lambda :: Lat, N :: RngIntElt) 
             -> SeqEnum, ModTupFldElt, ModTupFldElt, FldReElt
{ Input: a sequence of vectors, a natural number m, a target vector v, a lattice and an integer.
  Output:  the sequence of indices corresponding to a subset of vs of m elements and an element of Lambda such that ||v-lambda-sum(subset)|| 
  is as small as possible. This sum and this (squared) norm are returned as well.
  N is used as a parameter of how many tries should be made.
}
  n := #vs;
  V := Parent(vs[1]);
  for i := 1 to N do
    tryseq := RandomSequence(n,m);
    ws := [vs[i] : i in tryseq];
    w := &+ ws;
    //print "Searching closest vector";
    lambda,l := CloseVector(Lambda,v-w);
    if not assigned lmin or l lt lmin then
      subseqmin := tryseq;
      wsmin := ws;
      wmin := w;
      lambdamin := V!lambda;
      lmin := l;
    end if;
  end for;
  
  return subseqmin, lambdamin, wmin, lmin;
end intrinsic;



intrinsic RandomSequence(n :: RngIntElt, m :: RngIntElt) -> SeqEnum
{ Returns a random sequence of m distinct elements of [1 .. n];
}
  assert n ge m;
  result := [];
  for i := 1 to m do
    repeat
      henk := Random(1,n);
    until not(henk in result);
    Append(~result,henk);
  end for;
  return result;
end intrinsic;



intrinsic Conjugates(a :: FldElt) -> SeqEnum[FldElt]
{ Input: an element a of some field K.
  Output: all conjugates of a in K.
}
  K := Parent(a);
  return [x[1] : x in Roots(PolynomialRing(K)!MinimalPolynomial(a))];
end intrinsic;  
  
  

intrinsic UnitGenerators(N :: RngIntElt) -> SeqEnum[RngIntElt]
{ The ordered sequence of integers that reduce to "canonical" generators of (Z/N)^*.
}
  D := DirichletGroup(N,Rationals());
  return UnitGenerators(D);
end intrinsic;



intrinsic Radical(N :: RngIntElt) -> RngIntElt
{}
  pf := Factorisation(N);
  primes := [Integers()|pp[1] : pp in pf];
  return &*primes;
end intrinsic;



intrinsic InverseImage(M :: Mtrx, P :: Mtrx) -> Mtrx
{ M is a matrix representing a linear map f from Z^n to Z^m. P is a matrix representing a subspace V of Z^m.
  This intrinsic returns a matrix representing f^(-1)(V).
}
  image := RowSpace(M) meet RowSpace(P);
  Q := Matrix(Basis(image));
  V,N := Solution(M,Q);
  S := N + RowSpace(V);
  return Matrix(Basis(S));
end intrinsic;


intrinsic MinkowskiVector(a :: FldNumElt, prec :: RngIntElt) -> ModTupFldElt
{ Computes the Minkowski vector associated to a to precision n.
}
  K := Parent(a);
  R := RealField(prec);
  infs := InfinitePlaces(K);
  res := [R|];
  for inf in infs do
    ev := Evaluate(a, inf : Precision := prec);
    if IsReal(inf) then
      Append(~res,ev);
    else
      res cat:= [Sqrt(R!2)*Real(ev),Sqrt(R!2)*Imaginary(ev)];
    end if;
  end for;
  return Vector(res);
end intrinsic;




intrinsic MinkowskiMatrix(R :: RngOrd, pol :: RngUPolElt, prec :: RngIntElt) -> Mtrx
{ Computes the basis matrix of the Minkowski lattice of R to precision prec, where pol is a defining polynomial for the fraction field of R.
  The underlying equation order of R has to be defined by MakeMonic(pol). The idea is that the coefficients of pol are smaller than 
  of MakeMonic(pol), which helps to speed up the computation considerably.
}
  K<a> := NumberField(pol);
  K2 := NumberField(R);
  lc := LeadingCoefficient(pol);
  phi := hom<K2 -> K | a*lc>;
  
  return Matrix([MinkowskiVector(phi(K2!a), prec) : a in Basis(R)]);
end intrinsic;







intrinsic MinkowskiMatrix(R :: RngOrd, prec :: RngIntElt) -> Mtrx
{}
  K2 := NumberField(R);
  return Matrix([MinkowskiVector(K2!a, prec) : a in Basis(R)]);
end intrinsic;




intrinsic LLL(R :: RngOrd, pol :: RngUPolElt, steps :: RngIntElt) -> RngOrd
{ Outputs an order with reduced basis.  The underlying equation order of R has to be defined by MakeMonic(pol).
  Steps indicates how many LLL reductions we do, increasing the precision every time.
}
  prec := 3*Log(Max([Abs(x) : x in Eltseq(pol)]))/Log(10); //this is a bit arbitary.
  prec := Max(Floor(prec),100);
  RR := R;
  for i := 1 to steps do
    print "Building Minkowski lattice to precision", prec;
    LR := MinkowskiMatrix(RR,pol,prec);
    print "LLL-reducing Minkowski lattice";
    LLLR,MMM := LLL(LR : Delta := 0.99, TimeLimit := 3600);
    print "Adjusting order";
    RR := Simplify(Order(RR,MMM,1));
    print "Basis vectors have length <=", RealField(10)!Sqrt(Max([Norm(b) : b in Rows(LLLR)]));
    prec := 6*prec div 5;
  end for;
  return RR;
end intrinsic;
    


intrinsic LLL(R :: RngOrd, steps :: RngIntElt, prec :: FldReElt) -> RngOrd
{}
  prec := Max(Floor(prec),100);
  RR := R;
  for i := 1 to steps do
    print "Building Minkowski lattice to precision", prec;
    LR := MinkowskiMatrix(RR,prec);
    print "LLL-reducing Minkowski lattice";
    LLLR,MMM := LLL(LR : Delta := 0.99, TimeLimit := 3600);
    print "Adjusting order";
    RR := Simplify(Order(RR,MMM,1));
    print "Basis vectors have length <=", RealField(10)!Sqrt(Max([Norm(b) : b in Rows(LLLR)]));
    prec := 6*prec div 5;
  end for;
  return RR;
end intrinsic;

  

HeckeAlg := recformat<
              basis : SeqEnum, 
	      indices : SeqEnum,
	      CM : ModSym,
	      CMbasis : SeqEnum,
	      grouptype : MonStgElt,
	      
	      misc
	    >;


/* The Hecke algebra is represented by a basis of matrices. The matrices indicate how it acts on CM, with given CMbasis.
   The indices indicate which T_n belong to the given basis.
*/

/*BLABLA
Er moeten intrinsics komen die:
Bij een modspace een basis bepaalt voor de Hecke-algebra. OK.
In Arith.mg een intrinsic die bij een afbeelding tussen vrije Z-modulen het inverse beeld bepaalt.
Een gegeven matrix uitdrukken in de basis.
Een gegeven rijtje coefficienten als matrix representeert.
Bij een modvorm het ideaal van de hecke-algebra bepaalt.
Bij een modvorm en een priemideaal het ideaal van de hecke-algebra bepaalt.
De kern van zo'n ideaal in de Jacobiaan bepaalt.
*/



intrinsic HeckeMatrix(CMKf :: ModSym, p :: RngIntElt, basis :: SeqEnum) -> Mtrx
{ Input: a modular symbols space CMKf.
    AND  an integer p.
    AND  a Q-basis for CMKf.
  Output: the matrix of Tp relative to the basis (here a matrix is, as usual in MAGMA, a linear map by right multiplication).
}
  M := AmbientSpace(CMKf);
  m1 := RationalMapping(CMKf);
  V := Codomain(m1);
  W, n, n1 := ToQSpace(V);
  Kf := BaseRing(CMKf);
  CMtoW := map < M -> W | cm :-> n(m1(cm)) >;
  MZ := MatrixAlgebra(Integers(),Dimension(W));
  
  B := Matrix(&cat[[CMtoW(k*b) : k in Basis(Kf) ] : b in Basis(CMKf)]);
  
  basisvectors := [CMtoW(b): b in basis];
  outputvectors := [n(m1(b))*B^(-1)*QMatrix(HeckeOperator(CMKf,p))*B : b in basis];
  
  matr := Matrix(outputvectors)*Matrix(basisvectors)^(-1);
  return MZ![Numerator(x): x in Eltseq(matr)];
end intrinsic;


intrinsic DiamondMatrix(CMKf :: ModSym, d :: RngIntElt, basis :: SeqEnum) -> Mtrx
{ Input: a modular symbols space CMKf.
    AND  an integer d.
    AND  a Q-basis for CMKf.
  Output: the matrix of <d> relative to the basis (here a matrix is, as usual in MAGMA, a linear map by right multiplication).
}
  result := HeckeMatrix(CMKf,1,basis);
  MZ := Parent(result);
  factors := Factorisation(d);
  for factor in factors do
    p := factor[1];
    matr := (HeckeMatrix(CMKf,p,basis)^2-HeckeMatrix(CMKf,p^2,basis))^factor[2];
    result *:= MZ![x div p^factor[2] : x in Eltseq(matr)];
  end for;
  
  return result;
end intrinsic;



intrinsic AtkinLehnerMatrix(CMKf :: ModSym, Q :: RngIntElt, basis :: SeqEnum) -> Mtrx
{ Input: a modular symbols space CMKf.
    AND  an integer Q.
    AND  a Q-basis for CMKf.
  Output: the matrix of W_n relative to the basis (here a matrix is, as usual in MAGMA, a linear map by right multiplication).
}
  M := AmbientSpace(CMKf);
  m1 := RationalMapping(CMKf);
  V := Codomain(m1);
  W, n, n1 := ToQSpace(V);
  Kf := BaseRing(CMKf);
  CMtoW := map < M -> W | cm :-> n(m1(cm)) >;
  MZ := MatrixAlgebra(Integers(),Dimension(W));
  
  B := Matrix(&cat[[CMtoW(k*b) : k in Basis(Kf) ] : b in Basis(CMKf)]);
  
  basisvectors := [CMtoW(b): b in basis];
  outputvectors := [n(m1(b))*B^(-1)*QMatrix(AtkinLehnerOperator(CMKf,Q))*B : b in basis];
  
  matr := Matrix(outputvectors)*Matrix(basisvectors)^(-1);
  return MZ![Numerator(x): x in Eltseq(matr)];
end intrinsic;




intrinsic FindRepresentationSpace(CMKf :: ModSym, basis :: SeqEnum, l :: RngIntElt, ap :: Map, eps :: Map) -> ModTupFld
{ Input: a modular symbols space CMKf.
    AND  a Q-basis for CMKf.
    AND  a prime number l.
    AND  two maps ap and eps.
  Output: a 2-dimensional vector space W over Fl as a subspace of a full #basis-dimensional vector space over Fl, such that the l-torsion that corresponds to 
          W is the space for the Galois representation that belongs to ap en eps.
}
  N := Level(CMKf);
  Fl := FiniteField(l);
  W := VectorSpace(Fl,#basis);
  MF := MatrixAlgebra(Fl,#basis);
  
  print "Starting to calculate diamond eigenspaces.";
  for d := 1 to Lcm(N,l)-1 do
    if Gcd(d,N*l) eq 1 then
      print "d =",d;
      matr := DiamondMatrix(CMKf,d,basis);
      W meet:= NullSpace(MF!matr-eps(d)*One(MF));
      print "dim(W) =",Dimension(W);
    end if;
  end for;
  
  print "Starting to calculate Hecke eigenspaces.";
  p := 2;
  while Dimension(W) gt 2 do
    if N*l mod p ne 0  then
      print "p =", p;
      matr := HeckeMatrix(CMKf,p,basis);
      W meet:= NullSpace(MF!matr-ap(p)*One(MF));
      print "dim(W) =",Dimension(W);
    end if;
    p := NextPrime(p);
  end while;
  return W;
end intrinsic;





intrinsic WipeSuperfluousMatrices(ha :: Rec) -> Rec
{ Throws away the shit in the generating set of the Hecke-algebra as Z-module that is already in the Z-module generated by the rest.
}
  res := ha;
  n := #res`basis;
  vectorbasis := [MatrixToVector(b) : b in res`basis];
  for i := n to 1 by -1 do
    if #vectorbasis gt 1 then
      L := Lattice(Matrix(Remove(vectorbasis,i)));
      if vectorbasis[i] in L then
        Remove(~vectorbasis,i);
        Remove(~res`basis,i);
        Remove(~res`indices,i);
      end if;
    end if;
  end for;
  
  return res;
end intrinsic;



intrinsic CreateHeckeAlgebra(CM :: ModSym, CMbasis :: SeqEnum[ModSymElt], indexbound :: RngIntElt) -> Rec
{ Creates the Hecke algebra associated to CM, where the matrices are expressed in CMbasis. 
  It tries Hecke operators T_n up to index bound. 
}
  ha := rec< HeckeAlg | basis := [], indices := [], CM := CM, CMbasis := CMbasis>;
  N := Level(CM);
  for n := 1 to indexbound do  
    if Gcd(n,N) eq 1 then
      Tn := HeckeMatrix(CM,n,CMbasis);
      Append(~ha`basis,Tn);
      Append(~ha`indices,n);
    end if;
  end for;
  return WipeSuperfluousMatrices(ha);
end intrinsic;


intrinsic CreateHeckeAlgebra(CM :: ModSym, CMbasis :: SeqEnum[ModSymElt]) -> Rec
{ Creates the Hecke algebra associated to CM, where the matrices are expressed in CMbasis. 
}
  N := Level(CM);
  B := HeckeBound(CM);
  return CreateHeckeAlgebra(CM,CMbasis,B);
end intrinsic;



intrinsic CreateHeckeAlgebra(ms :: Rec) -> Rec
{ Creates the Hecke algebra for the modular space ms.
}
  return CreateHeckeAlgebra(ms`CM, ms`H1basis, ms`index div 6 + 1);
end intrinsic;




intrinsic HeckeMapForModularForm(f :: ModFrmElt, ha :: Rec) -> Mtrx
{ Computes the map Tn :-> an, expressed as a matrix associated to the following coordinate systems. 
  For the Hecke algebra we take the basis defined in ha and for OKf we take the basis Basis(OKf).
}
  OKf := MaximalOrder(BaseRing(Parent(f)));
  M := Matrix([Eltseq(OKf!Coefficient(f,n)) : n in ha`indices]);
  n := NumberOfRows(M); 
  m := NumberOfColumns(M);
  return RMatrixSpace(Integers(),n,m)!M;
end intrinsic;



intrinsic HeckeIdealForModularForm(f :: ModFrmElt, ha :: Rec) -> ModTupRng
{ Computes the kernel of the homomorphism T->Kf, expressed as a submodule of Z^n relative to the basis of ha.
}
  return Kernel(HeckeMapForModularForm(f,ha));
end intrinsic;



intrinsic HeckeIdealForModularForm(f :: ModFrmElt, ha :: Rec, pp :: .) -> ModTupRng
{ Computes the kernel of the homomorphism T->OKf/pp, expressed as a submodule of Z^n relative to the basis of ha.
}
  Zm := RSpace(Integers(),#ha`basis);
  M := HeckeMapForModularForm(f,ha);
  
  OKf := MaximalOrder(BaseRing(Parent(f)));
  if Type(OKf) eq RngInt then
    POKf<X> := PolynomialRing(OKf);
    OKf := EquationOrder(X-1);
  end if;
  
  if Type(pp) eq RngInt then
    ppp := Decomposition(OKf,Generator(pp))[1][1];
  else
    ppp := pp;
  end if;
  
  Zn := RSpace(Integers(),Degree(OKf));
  I := sub<Zn|[Eltseq(x) : x in Basis(ppp)]>;
  //_,p1 := quo<Zn|I>;
 // m := hom<Zm->Zn|M>;
  
  //return Kernel(m*p1);
  return RowSpace(InverseImage(M,Matrix(Basis(I))));
end intrinsic;



intrinsic FindRepresentationSpace(f :: ModFrmElt, ha :: Rec, pp :: .) -> ModTupFld
{ Input: a modular form f, a Hecke algebra and a prime ideal pp of OKf.
  Output: a vector space corresponding to the torsion in the jacobian associated to ha which gives the 
     Galois representation for f mod pp.
  Note: we do assume that we can indeed find the representation inside this jacobian.
}
  OKf := MaximalOrder(BaseRing(Parent(f)));
  if Type(OKf) eq RngInt then
    POKf<X> := PolynomialRing(OKf);
    OKf := EquationOrder(X-1);
  end if;
  
  if Type(pp) eq RngInt then
    ppp := Decomposition(OKf,Generator(pp))[1][1];
  else
    ppp := pp;
  end if;
  
  p := Radical(Norm(ppp));
  Fp := FiniteField(p);
  Ifp := HeckeIdealForModularForm(f,ha,ppp);
  V := VectorSpace(Fp,#ha`CMbasis);
  M := MatrixAlgebra(Fp,#ha`CMbasis);
  for b in Basis(Ifp) do
    eb := Eltseq(b);
    mat := &+[Fp!eb[i] * M!ha`basis[i] : i in [1 .. #eb]];
    V meet:= Kernel(mat);
  end for;
  
  return V;
end intrinsic;



intrinsic FindRepresentationSpace(f :: ModFrmElt, pp :: .) -> Rec, ModTupFld
{ Outputs a Hecke algebra and a representation space for f.
  We assume that N(f) is coprime to pp and that the weight of f is equal to the weight of f mod pp.
  We also assume for k(f)>2 that a representation mod pp exists in a Jacobian with multiplicity one (surely true if k>=p+2).
}
  N := Level(f);
  dc := DirichletCharacter(f);
  
    
  OKf := MaximalOrder(BaseRing(Parent(f)));
  if Type(OKf) eq RngInt then
    POKf<X> := PolynomialRing(OKf);
    OKf := EquationOrder(X-1);
  end if;
  
  if Type(pp) eq RngInt then
    ppp := Decomposition(OKf,Generator(pp))[1][1];
  else
    ppp := pp;
  end if;
  p := Radical(Norm(ppp));
  Fp := FiniteField(p);
  
  print "Creating Gamma1-HeckeAlgebra. This may take time.";
  
  //If f is a weight 2 form for Gamma0, we should skip this part:
  
  
  if Weight(f) eq 2 then
    if not IsGamma0(Parent(f)) then
      CM := CuspidalSubspace(ModularSymbols(Gamma1(N),2));
      CMbasis := IntegralBasis(CM);
      //ha := CreateHeckeAlgebra(CM,CMbasis);
      ha := CreateHeckeAlgebra(CM,CMbasis,HeckeBound(CM));
      ha`grouptype := "Gamma1";
    else
      CM := CuspidalSubspace(ModularSymbols(Gamma0(N),2));
      CMbasis := IntegralBasis(CM);
      //ha := CreateHeckeAlgebra(CM,CMbasis);
      ha := CreateHeckeAlgebra(CM,CMbasis,HeckeBound(CM));
      ha`grouptype := "Gamma0";
    end if;
  else
    CM := CuspidalSubspace(ModularSymbols(Gamma1(N*p),2));
    CMbasis := IntegralBasis(CM);
    //ha := CreateHeckeAlgebra(CM,CMbasis);
    ha := CreateHeckeAlgebra(CM,CMbasis,HeckeBound(CM));
    ha`grouptype := "Gamma1";
  end if;
  
  space := FindRepresentationSpace(f,ha,pp);
  M := MatrixAlgebra(Fp,Degree(space));
  
//Nu checken of de zaak invariant is onder diamanten.
  print "Checking whether Gamma0 can be used.";
  if ha`grouptype ne "Gamma0" then
    mats := [DiamondMatrix(CM,d,CMbasis) : d in UnitGenerators(Level(CM))];
    if not &and[&and[b*M!mat eq b : b in Basis(space)] : mat in mats] then
      return ha, space;
    end if;
  end if;
    
  print "It can!";
    
  if Weight(f) eq 2 then
    CM := CuspidalSubspace(ModularSymbols(Gamma0(N),2));
    CMbasis := IntegralBasis(CM);
    ha := CreateHeckeAlgebra(CM,CMbasis, HeckeBound(CM));
    ha`grouptype := "Gamma0";
  else
    CM := CuspidalSubspace(ModularSymbols(Gamma0(N*p),2));
    CMbasis := IntegralBasis(CM);
    ha := CreateHeckeAlgebra(CM,CMbasis, HeckeBound(CM));
    ha`grouptype := "Gamma0";
  end if;
  
  space := FindRepresentationSpace(f,ha,pp);
  M := MatrixAlgebra(Fp,Degree(space));
  
  print "Checking whether Gamma0+ can be used.";
//Nu checken of de zaak invariant is onder Atkin-Lehner.
  //mat := AtkinLehnerMatrix(CM,N,CMbasis);
 // if not &and[b*M!mat eq b : b in Basis(space)] then
  if not (AtkinLehnerEigenvalue(f,N) eq 1) then  
    return ha, space;
  end if;
  
    
  CM0 := AtkinLehnerDecomposition(CM)[1];
  if Dimension(CM0) gt 2 then
    print "It can!";
    CM0basis := H1basis0plus(CM0);
    ha := CreateHeckeAlgebra(CM0,CM0basis, HeckeBound(CM));
    space := FindRepresentationSpace(f,ha,pp);
    ha`grouptype := "Gamma0plus";
  end if;
  
  return ha, space;
end intrinsic;



intrinsic Annihilator(ha :: Rec, space :: ModTupFld) -> ModTupFld
{ Input: a Hecke algebra and a vector space (over some Fl) on which it acts.
  Output: annihilator ideal of this action, represented as a vector space over Fl.
   (so actually it is the annihilator mod l that we output).
}
  spbm := Matrix(Basis(space));
  MM := MatrixAlgebra(BaseField(space),Degree(space));
  mat := Matrix([Vector(Eltseq(spbm*MM!T)):T in ha`basis]);
  
  return Kernel(mat);
//blabla
end intrinsic;


intrinsic CreateModSpace(ha :: Rec, prec :: RngIntElt) -> Rec
{ Creates the modular space belonging to Hecke algebra ha, with precision prec.
}
  N := Level(ha`CM); 
  qprec := prec * N div 2;
  
  if ha`grouptype eq "Gamma1" then
    return CreateModSpace(Gamma1(N),prec,qprec);
  end if;
  
  if ha`grouptype eq "Gamma0" then 
    return CreateModSpace(Gamma0(N),prec,qprec);
  end if;
  
  if ha`grouptype eq "Gamma0plus" then
    return CreateModSpace0plus(N,prec,qprec);
  end if;
  
  assert false;
end intrinsic;




intrinsic AtkinLehner(tau :: Tup, N :: RngIntElt) -> Tup
{ Performs Atkin-Lehner operator w_N on tau, also puts tau into a fundamental domain of Gamma_1(N).
}
  gamma, tau1 := Explode(tau);
  _,gamma := DecomposeSL2ZMatrix1(N,gamma);
  atkinlehnermatrix := Matrix([[0,-1],[N,0]]);
  gamma,tau2 := Explode(RewriteTau(atkinlehnermatrix*(gamma*tau1)));
  _,gamma := DecomposeSL2ZMatrix1(N,gamma);
  return <gamma,tau2>;
end intrinsic;


  
nodigeprecisie := function(prec, ytau)
  return Max(20,Ceiling(2/5*prec/ytau));
end function;



EpsilonValueAtPrime := function(f,p)
  k := Weight(f);
  ap := Coefficient(f,p);
  ap2 := Coefficient(f,p^2);
  return (ap^2-ap2)/(p^(k-1));
end function;

EpsilonValue := function(f,d)
  res := 1;
  pf := Factorization(d);
  for pp in pf do
    res *:= EpsilonValueAtPrime(f,pp[1])^pp[2];
  end for;
  return res;
end function;


intrinsic TableOfEpsilonValues(f :: ModFrmElt, N :: RngIntElt) -> SeqEnum
{ Input: a newform f AND its level N.
  Output: a sequence eps of the character values attached to f (with values in the field of definition of f).
}
  res := [BaseRing(Parent(f)) | ];
  for d := 1 to N do
    if Gcd(d,N) ne 1 then
      Append(~res,0);
    else
      Append(~res,EpsilonValue(f,d));
    end if;
  end for;
  return res;
end intrinsic;


intrinsic EvaluateEpsilon(epstable :: SeqEnum, d :: RngIntElt) -> RngElt
{ Evaluates epsilon from the created table
}
  N := #epstable;
  if N eq 1 then return 1; end if;
  _, i := Quotrem(d,N);
  if i eq 0 then return 0; end if;
  return epstable[i];
end intrinsic;


nexttestpair := procedure(~a,~c,N,eps)
  K := BaseRing(eps);
  a +:= 1; if a ge c then a := 1; c +:= N; end if;
  while (Gcd(a,c) ne 1) or (Evaluate(eps,a) ne One(K)) do
    a +:= 1; if a ge c then a := 1; c +:= N; end if;
  end while;
end procedure;


nexttestpair2 := procedure(~a,~c)
  repeat 
    a +:=1; 
    if a ge c then a := 0; c +:= 1; end if;
  until Gcd(a,c) eq 1;
end procedure;



testvector := function(vectors,vec)
  V := VectorSpace(Rationals(), #vec);
  W := sub < V | [V!v : v in vectors] >;
  return not ((V!vec) in W);
end function;


searchgoodindex := function(vectors,vec,result)
  V := VectorSpace(Rationals(),#vec);
  W := VectorSpaceWithBasis([V!v : v in vectors]);
  coeffs := Coordinates(W,W!vec);
  dmax := -1; dindex := -1;
  for i := 1 to #vectors do
    if coeffs[i] ne Zero(BaseRing(W)) and Abs(Eltseq(result[i])[4]) gt dmax then
      dmax := Abs(Eltseq(result[i])[4]);
      dindex := i;
    end if;
  end for;
  return dindex;
end function; 
  



intrinsic FindGoodCuspsForHomology(CM :: ModSym) -> SeqEnum[FldRat]
{ Input: a modular symbols space over Q belonging to a modular curve.
  Output: a sequence of rational numbers alpha such that <oo,alpha> form a basis for H_1(X_1(N),Q).
}
  m1 := RationalMapping(CM);
  result := []; vectors := [];
  a := 0; c := 1;
  while #result lt Dimension(CM) do
    vec := Eltseq(m1(AmbientSpace(CM)!<1,[Cusps()|Infinity(),a/c]>));
    if testvector(vectors,vec) then
      Append(~vectors,vec);
      Append(~result,a/c);
    end if;
    nexttestpair2(~a,~c);
  end while;
  
  return result;
end intrinsic;



intrinsic FindHeckeModuleBasis(CM :: ModSym : FocusOnD := true) -> SeqEnum
{ Input: a modular symbols space CM
  Output: a sequence of two matrices gamma such that <oo,gamma(oo)> are a basis of CM over the Hecke algebra T (x) Q.
}
  N := Level(CM);
  eps := DirichletCharacter(CM);
  G := Gamma0(N);
/*  
  a := 1; c := N;
  bestd := N^3;
  while (c le N^2) do
    modsym1 := mCM!<1,[Cusps()|Infinity(),a/c]>;
    modsym2 := mCM!<1,[Cusps()|Infinity(),-a/c]>;
    if (modsym1 ne modsym2) and (modsym1 ne -modsym2) then
      _, gamma1 := IsEquivalent(G,Cusps()!Infinity(),Cusps()!(a/c));
      _, gamma2 := IsEquivalent(G,Cusps()!Infinity(),Cusps()!(-a/c));
      if FocusOnD then
        d := Abs(Eltseq(gamma1)[4]);
        if d lt bestd then
          bestd := d;
	  candidate := [gamma1,gamma2];
        end if;
      else 
        if not assigned candidate then
	  candidate := [gamma1,gamma2];
	  c := N^2;
	end if;
      end if;
    end if;
    nexttestpair(~a,~c,N,eps);
  end while; 
  
  if assigned candidate then return candidate; end if;
  
  print "First try failed.";
*/  
  candidate := []; vecs := [];
  m1 := RationalMapping(CM);
  VCM := Codomain(m1);
  a := 1; c := N;
  while #candidate lt 2 do
    modsym1 := CM!<1,[Cusps()|Infinity(),a/c]>;
   // print "a=",a, "; c=",c, "; modsym1=", modsym1; 
    _, gamma1 := IsEquivalent(G,Cusps()!Infinity(),Cusps()!(a/c));
    vec := m1(modsym1);
    if IsIndependent(vecs cat [vec]) then
   //   print "Vector found.";
      Append(~vecs,vec);
      Append(~candidate,gamma1);
    end if;
    nexttestpair(~a,~c,N,eps);
  end while;  
  
  return candidate;
end intrinsic;



intrinsic PeriodLattice(CMKfs :: Tup, modulebases :: Tup, basisperiods :: Tup, rootss :: SeqEnum, basisforH1 :: SeqEnum) -> ModMatFldElt
{ Input: a tuple of bases for the modular symbols spaces for several modular forms.
    AND  s tuple of integrals of the modular forms over the modular symbols.
    AND  a sequence of sequences of roots belonging to those modular forms.     
    AND  a sequence of cuspidal modular symbols for X1 that is a basis for H1(X1).
  Output: a matrix representing the period lattice belonging to this.
}
  CM := CuspidalSubspace(Parent(basisforH1[1])); M := AmbientSpace(CM);
  m1 := RationalMapping(CM);
  MC := KMatrixSpace(Parent(rootss[1][1]),Dimension(CM),Dimension(CM));
  
  cuspbasis := FindGoodCuspsForHomology(CM);
  periodsforcuspbasis := Matrix([IntegralToCusp(CMKfs,modulebases,basisperiods,rootss,alpha) : alpha in cuspbasis]);
  matrixforcuspbasis := Matrix([m1(M!<1,[Cusps()|Infinity(),alpha]>) : alpha in cuspbasis]);
  matrixforH1basis := Matrix([m1(symbol) : symbol in basisforH1]);

  return Mul(MC!(matrixforH1basis*Inverse(matrixforcuspbasis)),periodsforcuspbasis);
end intrinsic;





intrinsic PeriodLattice(CM :: ModSym, CMKfs :: Tup, modulebases ::Tup, 
                        basisperiods :: Tup, rootss :: SeqEnum, basisforH1 ::SeqEnum) -> ModMatFldElt
{ Input: a modular symbols space, which could be a subspace of a full CM.
    AND  a tuple of bases for the modular symbols spaces for several modular forms.
    AND  s tuple of integrals of the modular forms over the modular symbols.
    AND  a sequence of sequences of roots belonging to those modular forms.     
    AND  a sequence of cuspidal modular symbols for X1 that is a basis for H1(X1).
  Output: a matrix representing the period lattice belonging to this.
}
  M := AmbientSpace(CM);
  m1 := RationalMapping(CM);
  MC := KMatrixSpace(Parent(rootss[1][1]),Dimension(CM),Dimension(CM));
  
  cuspbasis := FindGoodCuspsForHomology(CM);
  periodsforcuspbasis := Matrix([IntegralToCusp(CMKfs,modulebases,basisperiods,rootss,alpha) : alpha in cuspbasis]);
  matrixforcuspbasis := Matrix([m1(M!<1,[Cusps()|Infinity(),alpha]>) : alpha in cuspbasis]);
  matrixforH1basis := Matrix([m1(symbol) : symbol in basisforH1]);

  return Mul(MC!(matrixforH1basis*Inverse(matrixforcuspbasis)),periodsforcuspbasis);
end intrinsic;

 


intrinsic IntegralToCusp(CM :: ModSym, cmbasis :: SeqEnum, periods :: ModMatFldElt, symbol :: ModSymElt) -> ModMatFldElt
{ Input: a modular symbols space.
    AND  a basis for this space.
    AND  a matrix of period integrals over this basis.
    AND  a modular symbol in this space.
  Output: the integral over this modular symbol.
}
  m1 := RationalMapping(CM); 
  VC := KSpace(BaseRing(Parent(periods)),Dimension(Codomain(m1)));
  
  matrixforcmbasis := Matrix([m1(cm) : cm in cmbasis]); 
  return (VC!(m1(symbol)*matrixforcmbasis^(-1)))*periods;
end intrinsic;


intrinsic IntegralToCusp(CM :: ModSym, cmbasis :: SeqEnum, periods :: ModMatFldElt, symbol :: ModTupFldElt) -> ModMatFldElt
{ Input: a modular symbols space.
    AND  a basis for this space.
    AND  a matrix of period integrals over this basis.
    AND  a modular symbol in this space.
  Output: the integral over this modular symbol.
}
  m1 := RationalMapping(CM); 
  VC := KSpace(BaseRing(Parent(periods)),Dimension(Codomain(m1)));
  
  matrixforcmbasis := Matrix([m1(cm) : cm in cmbasis]); 
  return VC!(m1(symbol)*matrixforcmbasis^(-1))*periods;
end intrinsic;




intrinsic IntegralToCusp(CMKf :: ModSym, modulebasis :: SeqEnum[GrpPSL2Elt], basisperiods :: SeqEnum, roots :: SeqEnum, alpha :: ModSymElt) -> SeqEnum
{ Input: a modular symbols space over Kf representing a modular form f.
    AND  a Kf-basis of this space
    AND  the period integrals for this basis
    AND  the complex roots of the defining equation of Kf.
    AND  a modular symbol alpha.
  Output: the integral of fdq/q over alpha
}
  m1 := RationalMapping(CMKf);
  Kf := BaseRing(CMKf);
  modulebasis2 := [CMKf!<1,[Cusps()|Infinity(),Eltseq(mat)[1]/Eltseq(mat)[3]]> : mat in modulebasis];
  matrix1 := Matrix([m1(sym) : sym in modulebasis2]);
  coeffs := m1(alpha)*matrix1^(-1);
  return ScalarMultiple(coeffs[1],basisperiods[1],roots) + ScalarMultiple(coeffs[2],basisperiods[2],roots);
end intrinsic;



intrinsic IntegralToCusp(CMKf :: ModSym, modulebasis :: SeqEnum[GrpPSL2Elt], basisperiods :: SeqEnum, roots :: SeqEnum, alpha :: ModTupFldElt) -> SeqEnum
{ Input: a modular symbols space over Kf representing a modular form f.
    AND  a Kf-basis of this space
    AND  the period integrals for this basis
    AND  the complex roots of the defining equation of Kf.
    AND  a modular symbol alpha.
  Output: the integral of fdq/q over alpha
}
  m1 := RationalMapping(CMKf);
  Kf := BaseRing(CMKf);
  modulebasis2 := [CMKf!<1,[Cusps()|Infinity(),Eltseq(mat)[1]/Eltseq(mat)[3]]> : mat in modulebasis];
  matrix1 := Matrix([m1(sym) : sym in modulebasis2]);
  coeffs := m1(alpha)*matrix1^(-1);
  return ScalarMultiple(coeffs[1],basisperiods[1],roots) + ScalarMultiple(coeffs[2],basisperiods[2],roots);
end intrinsic;



intrinsic IntegralToCusp(CMKf :: ModSym, modulebasis :: SeqEnum[ModSymElt], basisperiods :: SeqEnum, roots :: SeqEnum, alpha :: ModSymElt) -> SeqEnum
{ Input: a modular symbols space over Kf representing a modular form f.
    AND  a Kf-basis of this space
    AND  the period integrals for this basis
    AND  the complex roots of the defining equation of Kf.
    AND  a modular symbol alpha.
  Output: the integral of fdq/q over alpha
}
  m1 := RationalMapping(CMKf);
  Kf := BaseRing(CMKf);
  matrix1 := Matrix([m1(sym) : sym in modulebasis]);
  //print "matrix1 = ", matrix1;
  coeffs := m1(alpha)*matrix1^(-1);
  return ScalarMultiple(coeffs[1],basisperiods[1],roots) + ScalarMultiple(coeffs[2],basisperiods[2],roots);
end intrinsic; 
 


intrinsic IntegralToCusp(CMKf :: ModSym, modulebasis :: SeqEnum[ModSymElt], basisperiods :: SeqEnum, roots :: SeqEnum, alpha :: ModTupFldElt) -> SeqEnum
{ Input: a modular symbols space over Kf representing a modular form f.
    AND  a Kf-basis of this space
    AND  the period integrals for this basis
    AND  the complex roots of the defining equation of Kf.
    AND  a modular symbol alpha.
  Output: the integral of fdq/q over alpha
}
  m1 := RationalMapping(CMKf);
  Kf := BaseRing(CMKf);
  matrix1 := Matrix([m1(sym) : sym in modulebasis]);
 // print "matrix1 = ", matrix1;
  coeffs := m1(alpha)*matrix1^(-1);
  return ScalarMultiple(coeffs[1],basisperiods[1],roots) + ScalarMultiple(coeffs[2],basisperiods[2],roots);
end intrinsic; 





intrinsic IntegralToCusp(CMKfs :: Tup, modulebases :: Tup, basisperiods :: Tup, rootss :: SeqEnum, symbols :: Tup) -> SeqEnum
{}
  result := [];
  for i:= 1 to #modulebases do
    result cat:= IntegralToCusp(CMKfs[i],modulebases[i],basisperiods[i],rootss[i],symbols[i]);
  end for;
  return result;
end intrinsic;



intrinsic IntegralToCusp(CMKfs :: Tup, modulebases :: Tup, basisperiods :: Tup, rootss :: SeqEnum, alpha :: FldRatElt) -> SeqEnum
{}
  result := [];
  for i:= 1 to #modulebases do
    beta := AmbientSpace(CMKfs[i])!<1,[Cusps()|Infinity(),alpha]>;
    result cat:= IntegralToCusp(CMKfs[i],modulebases[i],basisperiods[i],rootss[i],beta);
  end for;
  return result;
end intrinsic;





intrinsic NewformCoefficientsAt(S :: ModFrm, n :: RngIntElt) -> Tup
{ Input: a cusp forms space S and an integer n.
  Output: the tuple consiting of an(f) where f runs through the newform classes of S.
}
  result := <>;
  for i := 1 to #Newforms(S) do 
    f := Newform(S,i);
    Append(~result, Coefficient(f,n));
  end for;
  return result;
end intrinsic;



intrinsic NewformCoefficientsAt(newforms :: Tup, n :: RngIntElt) -> Tup
{ Input: tuple of newforms and an integer n.
  Output: the tuple consiting of an(f) where f runs through the newforms.
}
  return <Coefficient(f,n) : f in newforms>;
end intrinsic;




intrinsic EvaluateGoodFunctionAtTorsionPoints(formevals :: SeqEnum, rootss :: SeqEnum, numerator :: Tup, denominator :: Tup) -> SeqEnum
{ Input: the sequence produced by EvaluateNewformsAtTorsionPoints
    AND  the rootss of the defining polynomials of the coefficient fields of the newforms
    AND  the numerator and denominator of a good function
  Output: a sequence of pairs <x,P> where P is a torsionpoint and x is a sequence consisting of the good function evaluated at
          the tau-values that make up the torsion point.
}
  numevals := [[ &+[&+ScalarMultiple(numerator[i],taueval[i],rootss[i]) : i in [1 .. #rootss]] : taueval in formeval[1] ] : formeval in formevals];
  denomevals := [[ &+[&+ScalarMultiple(denominator[i],taueval[i],rootss[i]) : i in [1 .. #rootss]] : taueval in formeval[1] ] : formeval in formevals];
  funcevals := [[numevals[i][j]/denomevals[i][j] : j in [1 .. #numevals[i]]] : i in [1 .. #formevals]];
  return [<funcevals[i],formevals[i][2]> : i in [1 .. #formevals]];
end intrinsic;



intrinsic EvaluateAtkinLehnerNewformsAtTorsionPoints(newforms :: Tup, torsionpoints :: SeqEnum) -> SeqEnum
{ Input: a tuple of newforms, each one stored as a record.
    AND  a sequence of torsion points of the jacobian of the modular curve, calculated by FindAllTorsionPointsInSubspace.
  Output: a sequence of tuples <x,P> where P is an element of the Fl-vector space that corresponds to the l-torsion of the abelian variety 
          and where x is the sequence that has for each tau in P the sequence of evaluated newforms. The newforms are seen as q-expansions 
	  around the cusp 0, which is rational for the X_1 model rather than the X_mu model.
}
  N := newforms[1]`level; //dit moet anders als er ook oudvormen zijn.
  wntorsion := [<[AtkinLehner(tau,N) : tau in point[1]],point[2]> : point in torsionpoints];
  formevals := EvaluateNewformsAtTorsionPoints(newforms,wntorsion);
  
  return formevals;
end intrinsic;



intrinsic EvaluateGoodFunctionAtTorsionPoints(ms :: Rec, torsion :: SeqEnum) -> SeqEnum
{ Input: A modular forms space and a sequence of torsion points of the Jacobian.
  Output: A sequence of evaluations of a good function on the Jacobian at these points.
}
  newformevals := EvaluateAtkinLehnerNewformsAtTorsionPoints(ms`forms,torsion);
  gfs := GoodFunctions(ms`forms);
  num := gfs[#gfs-1]; den := gfs[#gfs];
  rootss := [mf`roots : mf in ms`forms];
  funcevals := EvaluateGoodFunctionAtTorsionPoints(newformevals,rootss,num,den);
  pointevals := [<&+x[1],x[2]> : x in funcevals];
  
  return pointevals;
end intrinsic;  




ModForm := recformat<
             form : ModFrmElt,
	     series : RngSerPowElt,
	     embeddedseries : SeqEnum,
	     twiddledseries : SeqEnum,
	     level : RngIntElt,
	     degeneracy : RngIntElt,
	     roots : SeqEnum,
	     pseudoeigenvalues : SeqEnum,
	     epsilonvalues : SeqEnum,
	     CM : ModSym,
	     CMKf : ModSym,
	     heckemodulebasis : SeqEnum,  
	     heckebasisinsymbols : SeqEnum,
	     periodsforheckebasis : SeqEnum,
	     twistedperiods : BoolElt,
	     periodtwists : SeqEnum,
	     precision : RngIntElt,
	       
	     misc
	   >;
	   


ModSpace := recformat<
              forms : Tup,
	      S : ModFrm,
	      dimension : RngIntElt,
	      CM : ModSym,
	      H1basis : SeqEnum,
	      periodlattice : ModMatFldElt,
	      inttozero : ModTupFldElt,
	      precision : RngIntElt,
	      index : RngIntElt, //index of largest congruence subgroup of PSL2(Z) for ms.
	      	      	      
	      misc
	    >;
	     



intrinsic CreateModForm(S1 :: ModFrm, i :: RngIntElt, prec :: RngIntElt, qprec :: RngIntElt) -> Rec
{ Creates the record mf with series calculated to qprec and roots to prec for the i'th newform of cusp forms space S.
  S should be a character space.
}
    
  eps := DirichletCharacters(S1)[1];
  phi := hom< Rationals() -> CyclotomicField(1) | >;
  
  if BaseRing(eps) eq Rationals() then
    S := BaseChange(S1, phi);
    eps := BaseChange(eps,phi);
    //This pathological statement is because some procedures want to see a cyclotomic field.
  else
    S := S1;
  end if;
    
  f := Newform(S,i);
  Kf := BaseRing(Parent(f));
  if Kf eq Rationals() then
    Kf := CyclotomicField(1);
    f := Basis(BaseChange(Parent(f),phi))[1];
  end if;
  
  mf := rec< ModForm | form := f, precision := prec>;
  
  print "Calculating q-expansion.";
  mf`series := qExpansion(f,qprec);
  
  C<I> := ComplexField(prec);
  
  mf`roots := [C!x : x in Zeroes(Kf,prec+10)];
  N := Level(f);
  mf`epsilonvalues := TableOfEpsilonValues(f,N);
    
  mf`level := N;
  mf`degeneracy := 1;
  
  print "Calculating complex embeddings of q-expansion.";
  StoreEmbeddedSeries(~mf);
  StorePseudoEigenvalues(~mf);
  
  print "Calculating complex embeddings of W-twists.";
  mf`twiddledseries := [[PowerSeriesRing(C)|] : Q in [1 .. N]];
  for Q in Divisors(N) do 
    mf`twiddledseries[Q] := Twiddle(mf,Q);
  end for;
  
  CM := CuspidalSubspace(ModularSymbols(eps,Weight(mf`form)));
  mf`CM := NewformDecomposition(CM)[i];
    
  Qzm<zm> := BaseRing(CM);
  n := [x : x in [0 .. N-1] | eps(x) eq zm or eps(x) eq -zm][1];
  zmKf := EvaluateEpsilon(mf`epsilonvalues,n);
  if eps(n) eq -zm then zmKf := -zmKf; end if;
  if Qzm ne Kf then
     Embed(Qzm,Kf,zmKf);
    CMKf1 := BaseChange(mf`CM,EmbeddingMap(BaseRing(CM),BaseRing(Parent(f))));
  else
    CMKf1 := mf`CM;
  end if;
  
  mf`CMKf := NewformDecomposition(CMKf1)[1];
  
  mf`heckemodulebasis := FindHeckeModuleBasis(mf`CMKf : FocusOnD := false);
  mf`heckebasisinsymbols := [mf`CMKf!<1,[Cusps()|Infinity(),Eltseq(gamma)[1]/Eltseq(gamma)[3]]> : gamma in mf`heckemodulebasis];
  
  maxc := Max([Eltseq(gamma)[3] : gamma in mf`heckemodulebasis]);
  otherbasis := WindingBasisUpTo(mf`CMKf,Floor(maxc/Sqrt(N)));
      
  if #otherbasis eq 2 then
    print "Calculating period integrals using twists.";
    mf`twistedperiods := true;
    mf`periodtwists := otherbasis;
    mf`periodsforheckebasis := [TwistedPeriodIntegral(mf,l) : l in otherbasis];
    mf`heckebasisinsymbols := [TwistedSymbol(mf`CMKf,l) : l in otherbasis];
  else
    print "Calculating period integrals naively.";
    mf`twistedperiods := false;
    mf`periodsforheckebasis := [PeriodIntegral(mf,MatrixAlgebra(Integers(),2)!Eltseq(b)) : b in mf`heckemodulebasis];
  end if;
    
  return mf; 
end intrinsic;



intrinsic CreateModSpace(G :: GrpPSL2, prec :: RngIntElt, qprec :: RngIntElt) -> Rec
{ Creates the space S_2(G), together with relevant information.
  G has to be Gamma1(N) or Gamma0(N).
}
  ms := rec< ModSpace | forms := <>, precision := prec >;

  N := Level(G);  

  ms`S := CuspForms(G,2);
  ms`dimension := Dimension(ms`S);
  ms`index := Index(G);
  
  print "Dimension is", Dimension(ms`S);
  
  for M in Divisors(Level(G)) do
    if G eq Gamma1(N) then
      S := CuspForms(Gamma1(M),2);
    else
      S := CuspForms(Gamma0(M),2);
    end if;
    chars1 := < DirichletCharacter(Newform(S,i)) : i in [1 .. #Newforms(S)] >;
    chars := <>;
    for char in chars1 do
      if not char in chars then
        Append(~chars,char);
      end if;
    end for;
      
    for char in chars do
      S1 := CuspForms(char,2);
      for i := 1 to #Newforms(S1) do
        print "Creating a modular form.";
	mf := CreateModForm(S1,i,prec,qprec);
	mf`level := N;
	for d in Divisors(N div M) do
	  mf`degeneracy := d;
	  if d ne 1 then 
	    print "Calculating period integrals.";
	    if mf`twistedperiods then
	    //  mf`periodsforheckebasis := [TwistedPeriodIntegral(mf,l) : l in mf`periodtwists];
	      mf`periodsforheckebasis := [PeriodIntegral(mf,MatrixAlgebra(Integers(),2)!Eltseq(b)) : b in mf`heckemodulebasis];
	    else
	      mf`periodsforheckebasis := [PeriodIntegral(mf,MatrixAlgebra(Integers(),2)!Eltseq(b)) : b in mf`heckemodulebasis];
	    end if;
	  end if;
	  Append(~(ms`forms),mf);
	end for;
      end for;
    end for;
  end for;
  
  ms`CM := CuspidalSubspace(ModularSymbols(G,2));
  ms`H1basis := IntegralBasis(ms`CM);
  
  infos3 := <<mf`CMKf,mf`heckemodulebasis,mf`periodsforheckebasis> : mf in ms`forms>;
  rootss := [mf`roots : mf in ms`forms];
  modulebases := <mf`heckebasisinsymbols : mf in ms`forms>;
  basisperiods := <mf`periodsforheckebasis : mf in ms`forms>;
  CMKfs := <mf`CMKf : mf in ms`forms>;
  
  print "Calculating period lattice.";
  ms`periodlattice := PeriodLattice(CMKfs,modulebases,basisperiods,rootss,ms`H1basis);
  
  ms`inttozero := Vector(&cat[IntegralToCusp(mf,(mf`CMKf)!<1,[Cusps()|Infinity(),0]>) : mf in ms`forms]);
          
  return ms;
end intrinsic;


intrinsic CreateModSpace0plus(N :: RngIntElt, prec :: RngIntElt, qprec :: RngIntElt) -> Rec
{ Creates the +1 eigenspace of wN in S2(Gamma0(N)), together with relevant information.
}
  ms := rec< ModSpace | forms := <>, precision := prec >;
  G := Gamma0(N);
  ms`S := CuspForms(G,2);
  ms`index := Index(G); 
  
  print "Dimension of full space is", Dimension(ms`S);
  
  for M in Divisors(Level(G)) do
    if G eq Gamma1(N) then
      S := CuspForms(Gamma1(M),2);
    else
      S := CuspForms(Gamma0(M),2);
    end if;
    chars1 := < DirichletCharacter(Newform(S,i)) : i in [1 .. #Newforms(S)] >;
    chars := <>;
    for char in chars1 do
      if not char in chars then
        Append(~chars,char);
      end if;
    end for;
    
    for char in chars do
      S1 := CuspForms(char,2);
      for i := 1 to #Newforms(S1) do
        f := Newform(S1,i);
	if AtkinLehnerEigenvalue(f,N) eq 1 then
	  print "Creating a modular form.";
	  mf := CreateModForm(S1,i,prec,qprec);
	  mf`level := N;
	  for d in Divisors(N div M) do
	    mf`degeneracy := d;
	    if d ne 1 then 
	      print "Calculating period integrals.";
	      if mf`twistedperiods then
	      //  mf`periodsforheckebasis := [TwistedPeriodIntegral(mf,l) : l in mf`periodtwists];
	        mf`periodsforheckebasis := [PeriodIntegral(mf,MatrixAlgebra(Integers(),2)!Eltseq(b)) : b in mf`heckemodulebasis];
	      else
	        mf`periodsforheckebasis := [PeriodIntegral(mf,MatrixAlgebra(Integers(),2)!Eltseq(b)) : b in mf`heckemodulebasis];
	      end if;
	    end if;
	    Append(~(ms`forms),mf);
	  end for;
        end if;      
      end for;
    end for;
  end for;
    
  ms`CM := AtkinLehnerDecomposition(CuspidalSubspace(ModularSymbols(G,2)))[1];
  print "Dimension of eigenspace is", Dimension(ms`CM)/2;
  ms`dimension := Dimension(ms`CM) div 2;
  
  basis := Basis(ms`CM);
  rm := RationalMapping(ms`CM);
  mat := Matrix([rm(b) : b in basis]);
  ms`H1basis := [ &+[row[i]*basis[i] : i in [1 .. #basis]] : row in RowSequence(mat^(-1)) ];
  //The last line is based on the fact that RationalMapping(ms`CM) maps the integral homology bijectively to the 
  //submodule of all vectors with integer coordinates.
  
  infos3 := <<mf`CMKf,mf`heckemodulebasis,mf`periodsforheckebasis> : mf in ms`forms>;
  rootss := [mf`roots : mf in ms`forms];
  modulebases := <mf`heckebasisinsymbols : mf in ms`forms>;
  basisperiods := <mf`periodsforheckebasis : mf in ms`forms>;
  CMKfs := <mf`CMKf : mf in ms`forms>;
  
  print "Calculating period lattice.";
  ms`periodlattice := PeriodLattice(ms`CM,CMKfs,modulebases,basisperiods,rootss,ms`H1basis);
  
  ms`inttozero := Vector(&cat[IntegralToCusp(mf,(mf`CMKf)!<1,[Cusps()|Infinity(),0]>) : mf in ms`forms]);
          
  return ms;

end intrinsic;



intrinsic H1basis0plus(CM :: ModSym) -> SeqEnum
{ Computes the basis for X0(N)/wN, where CM is the modular symbols space for X0(N)/wN.
}
  basis := Basis(CM);
  rm := RationalMapping(CM);
  mat := Matrix([rm(b) : b in basis]);
  return [ &+[row[i]*basis[i] : i in [1 .. #basis]] : row in RowSequence(mat^(-1)) ];
  //The last line is based on the fact that RationalMapping(ms`CM) maps the integral homology bijectively to the 
  //submodule of all vectors with integer coordinates.
end intrinsic;



intrinsic Twiddle(mf :: Rec, Q :: RngIntElt) -> SeqEnum[RngSerPowElt]
{ Input: a newform and an integer.
  Output: the form f~ which is used in the calculation of W_Q(f), as a sequence of q-series over C, each one according to an embedding of
          Kf into C.
}
  fp := mf`series;
  
  if assigned mf`twiddledseries then
    preresult := mf`twiddledseries[Q];
    if not IsEmpty(preresult) then
      qprecf := AbsolutePrecision(fp);
      qprecknown := AbsolutePrecision(preresult[1]);
      if qprecknown ge qprecf then 
        return preresult;
      end if;
    end if;
  end if;
    
  C<I> := Parent(mf`roots[1]);
  PPC<q> := PowerSeriesRing(C);
  
  N := Level(mf`form);
  Q1 := N div Q;
  epsilonvaluesforQ := [mf`epsilonvalues[x + N*((N-x) div N) where x is ChineseRemainderTheorem([n,1],[Q,Q1])] : n in [1 .. Q]];
  epsilonvaluesforQ1 := [mf`epsilonvalues[x + N*((N-x) div N) where x is ChineseRemainderTheorem([n,1],[Q1,Q])] : n in [1 .. Q1]];
    
  result := [];
  for root in mf`roots do
    epsQ := [EmbeddingAtRoot(x,root) : x in epsilonvaluesforQ];
    epsQ1 := [EmbeddingAtRoot(x,root) : x in epsilonvaluesforQ1];
    
    coeffs := [];
    for n := 1 to AbsolutePrecision(fp)-1 do
      n1,n2 := Split(n,Q);
      coeff := epsQ1[x + Q1*((Q1-x) div Q1) where x is n1 mod Q1]  
             * ComplexConjugate(EmbeddingAtRoot(Coefficient(fp,n1),root))
             * ComplexConjugate(epsQ[x + Q*((Q-x) div Q) where x is n2 mod Q]) 
	     * EmbeddingAtRoot(Coefficient(fp,n2),root);
      Append(~coeffs,coeff);
    end for;
    
    Append(~result, q*PPC!coeffs + O(q^AbsolutePrecision(fp)));
  end for;
  
  //mf`twiddledseries[Q] := result;
  return result;   
end intrinsic;



intrinsic NaiveModularFormEvaluation(mf :: Rec, tau :: Tup : 
                                     TwiddleQ := 1,
				     UseDegeneracy := true) -> SeqEnum
{  The optional parameter TwiddleQ is for evaluating f~ instead of f.
}
  Re := Parent(tau[2][1]);
  
  if UseDegeneracy then 
    tau1 := [Re|mf`degeneracy,0]*(tau[1]*tau[2]);
  else 
    tau1 := tau[1]*tau[2];
  end if;
  
   
  fp := mf`series;
  ytau := Imaginary(tau1);
  
  prec := Precision(tau1[1]);
  qprec := AbsolutePrecision(fp);
  qprecneeded := nodigeprecisie(prec,ytau);
  
  if qprecneeded gt qprec then 
    fp := qExpansion(mf`form,qprecneeded);
    mf`series := fp;
    StoreEmbeddedSeries(~mf);
  end if;  
  
  TwoPiI := [Zero(Parent(tau1[1])),2*Pi(Parent(tau1[2]))];
  qq := Exp(Mul(TwoPiI,tau1));
  
  P<q> := Parent(mf`embeddedseries[1]);
  
  if TwiddleQ eq 1 then
    return [Evaluate(p+O(q^qprecneeded),qq) : p in mf`embeddedseries];
  end if;
  
  return [Evaluate(p+O(q^qprecneeded),qq) : p in Twiddle(mf,TwiddleQ)];
end intrinsic;  



intrinsic StoreEmbeddedSeries(~mf :: Rec)
{}
  mf`embeddedseries := [SeriesEmbeddingAtRoot(mf`series,root) : root in mf`roots];
end intrinsic;



//This does not work if things are 0!
intrinsic PseudoEigenvalues(mf :: Rec, Q :: RngIntElt) -> SeqEnum
{ We assume that Q is not 1 here. Pseudoeigenvalues are used in the calculation of WQ(f). Note that these are sligthly different than
  the ones used in the article of Atkin and Li.
}
  Re := RealField(Precision(mf`roots[1]));
  C<I> := Parent(mf`roots[1]);
  N := Level(mf`form);
  k := Weight(mf`form);
  Q1 := N div Q;
  y := Re!(Sqrt(Q)+Random(Re!-1/10,Re!1/10))/N;
  wQ := WQ(Q,N);
  
  IdM := Matrix([[1,0],[0,1]]);
  a,b,c,d := Explode(Eltseq(wQ));
  x := Re!-d/c+Random(Re!-1/10,Re!1/10);
  tau1 := <IdM,[x,y]>;
  tau2 := <IdM,wQ*[x,y]>;
  
  ftau1 := NaiveModularFormEvaluation(mf,tau1 : TwiddleQ := Q);
  ftau2 := NaiveModularFormEvaluation(mf,tau2);
  
  if IsEven(k) then 
    qpow := Re ! Q^(k div 2); 
  else 
    qpow := Sqrt(One(Re)*Q) * Q^((k-1) div 2);
  end if;
  taupow := Pow([c*x+d,c*y],-k);
  scalingfactor := C!([qpow,Re!0]*taupow);
  
  return [scalingfactor*ftau2[i]/ftau1[i] : i in [1 .. #mf`roots]];
end intrinsic;



intrinsic StorePseudoEigenvalues(~mf :: Rec)
{}
  N := Level(mf`form);
  C := Parent(mf`roots[1]);
  mf`pseudoeigenvalues := [];
  divisors := Exclude(Divisors(N),1);
  for Q in divisors do
    mf`pseudoeigenvalues[Q] := PseudoEigenvalues(mf,Q);
  end for;
  mf`pseudoeigenvalues[1] := [C!1 : root in mf`roots];
end intrinsic;
  
  

intrinsic ModularFormEvaluation(mf :: Rec, tautje :: Tup) -> SeqEnum
{ The optional parameter EnoughSeriesPrecision is to indicate whether enough terms have been precalculated.
}
  N := Level(mf`form);
  k := Weight(mf`form);
  
  tau := mf`degeneracy*tautje;
  
  C<I> := Parent(mf`roots[1]);
  Re := Parent(tau[2][1]);
  IdM := Matrix([[1,0],[0,1]]);
  
  gamma := tau[1];
  gamma1, gamma2 := DecomposeSL2ZMatrix0(N,gamma);
  
  if Eltseq(gamma2) eq [1,0,0,1] then
    //print "Naive evaluation suffices.";
    fg2tau := NaiveModularFormEvaluation(mf,<gamma2,tau[2]>: UseDegeneracy := false);
  else
    z := C!tau[2];
    a1,b1,Q1,d1 := Explode(Eltseq(gamma2));
    Q := N div Q1;
    
    if Norm(Q1*z+d1) le Q then
    //if false then //even testen of de rest werkt.
      //print "Naive evaluation suffices.";
      fg2tau := NaiveModularFormEvaluation(mf,<gamma2,tau[2]>: UseDegeneracy := false);
    else
      //print "Atkin-Lehner trick needed.";
      wQ := WQ(Q,N);
      
      //print "gamma2:", gamma2;
      //print "wQ:", wQ;
      
      wQ1 := Adjoint(wQ);
      tau1 := ((wQ1*gamma2)*tau[2]);
      //print "tau1:",tau1;
      
      x,y := Explode(tau1);
      
      twftau1 := NaiveModularFormEvaluation(mf,<IdM,tau1> : TwiddleQ := Q, UseDegeneracy := false);
      wqftau1 := [mf`pseudoeigenvalues[Q][i]*twftau1[i] : i in [1 .. #mf`roots]];
      
      if IsEven(k) then 
        qpow := Re ! Q^(k div 2); 
      else 
        qpow := Sqrt(One(Re)*Q) * Q^((k-1) div 2);
      end if;
      
      a2,b2,c2,d2 := Explode(Eltseq(wQ));
      tau1pow := Pow([c2*x+d2,c2*y],k);
      scalarfactor := C!(tau1pow/[Re|qpow,0]);
      fg2tau := [scalarfactor*x : x in wqftau1];
    end if;
  end if;
  
  a,b,c,d := Explode(Eltseq(gamma1));
  epsvalue := EvaluateEpsilon(mf`epsilonvalues,d);
  tau2 := gamma2*tau[2];
  tau2pow := C!Pow([c*tau2[1]+d,c*tau2[2]],k);
  
  return [EmbeddingAtRoot(epsvalue,mf`roots[i])*tau2pow*fg2tau[i] : i in [1 .. #mf`roots]];
end intrinsic;



intrinsic WindingBasisUpTo(CMKf :: ModSym, n :: RngIntElt) -> SeqEnum
{ Finds a Kf-basis for CMKf (which we assume to be 2-dimenstional) of twisted winding elements where we search up to l=n.
  If no 2 are found, the returned sequence will have less than 2 elements.
  The result is given as a sequence of integers l.
}
  m1 := RationalMapping(CMKf);
  V := Codomain(m1);
  
  l := [1] cat [p : p in [3 .. n] | IsPrime(p) and not Divides(p,Level(CMKf))];
  success := false;
  i := 1;
  while not(success) and i le #l do
    te := TwistedSymbol(CMKf,l[i]);
    if m1(te) ne V!0 then
      success := true;
      firsttwist := l[i];
    end if;
    i +:= 1;
  end while;
  
  if not(success) then 
    return [];
  end if;
  
  te1 := m1(TwistedSymbol(CMKf,firsttwist));
  
  success := false;
  while not(success) and i le #l do
    te := TwistedSymbol(CMKf,l[i]);
    if IsLinearlyIndependent([te1,m1(te)]) then
      success := true;
      secondtwist := l[i];
    end if;
    i +:= 1;
  end while;
      
  if not(success) then
    return [firsttwist];
  end if;
  
  return [firsttwist,secondtwist];
end intrinsic;



intrinsic PeriodIntegral(mf :: Rec, gamma :: Mtrx) -> SeqEnum
{ Integral of f(dq)/q from oo to gamma(oo).
}
  a,b,c,d := Explode(Eltseq(gamma));
  C<I> := Parent(mf`roots[1]);
  prec := Precision(C);
  f := mf`form;
  r := mf`degeneracy;
  Re := RealField(prec);
  fp := mf`series;
  qprec := AbsolutePrecision(fp);
  qprecneeded := nodigeprecisie(prec,r/c);
  print "qprec =",qprec;
  print "qprecneeded =",qprecneeded;
  if qprecneeded gt qprec then
    fp := qExpansion(mf`form,qprecneeded);
  end if;
  
  alpha := [Re|-d/c,1/c];
  ralpha := [Re|r,0]*alpha;
  galpha := gamma*alpha;
  rgalpha := [Re|r,0]*galpha;
  
  TwoPiI := [Re!0,2*Pi(Re)];
  
  q1 := Exp(TwoPiI*ralpha);
  q2 := Exp(TwoPiI*rgalpha);
  
  P<q> := PowerSeriesRing(BaseRing(Parent(f)));
  intf := Integral( fp/q + O(q^qprecneeded) );
  intfemb := AllSeriesEmbeddings(intf,mf`roots);
  
  //P<q> := Parent(mf`embeddedseries[1]);
  //intfemb := [Integral(g/q+O(q^qprecneeded)) : g in mf`embeddedseries];
  return [r*(Evaluate(intfemb[i],q2) - Evaluate(intfemb[i],q1)) : i in [1 .. #mf`roots]];
end intrinsic;
  


intrinsic TwistedPeriodIntegral(mf :: Rec, l :: RngIntElt) -> SeqEnum
{ Integral of f(x)chi_l(dq)/q from oo to 0, where chi_l is the Jacobi symbol mod l (and trivial if l=1).
  This is then also equal to IntegralToCusp(mf,TwistedWindingElement(mf`CMKf,1,chi)).
}
  C<I> := Parent(mf`roots[1]);
  prec := Precision(C);
  f := mf`form;
  N := Level(f);
  r := mf`degeneracy;
  Re := RealField(prec);
  fp := mf`series;
  qprec := AbsolutePrecision(fp);
  alpha := [Re|0,1/(l*Sqrt(Re!N))];
  qprecneeded := nodigeprecisie(prec, Imaginary(alpha));
  print "qprec =",qprec;
  print "qprecneeded =",qprecneeded;
  if qprecneeded gt qprec then
    fp := qExpansion(mf`form,qprecneeded);
  end if;
  
  TwoPiI := [Re!0,2*Pi(Re)];
  q1 := Exp(TwoPiI*alpha);
  
  epstable := mf`epsilonvalues;
  
  P<q> := Parent(fp);
  fp := q*P![Eltseq(fp)[n] * JacSymbol(n,l) : n in [1 .. #Eltseq(fp)] ] + O(q^AbsolutePrecision(fp));
  intf := Integral( fp/q + O(q^qprecneeded) );
    
  intfemb := AllSeriesEmbeddings(intf,mf`roots);
  R<qq> := Parent(intfemb[1]);
  twiddleintfemb := [qq*R![ComplexConjugate(x) : x in Eltseq(ff)] + O(qq^AbsolutePrecision(intf)) : ff in intfemb]; 
  
  if l eq 1 then 
    gaussfactor := C!1;
  else
    if JacobiSymbol(-1,l) eq 1 then
      gaussfactor := Sqrt(C!l)/l;
    else
      gaussfactor := -I*Sqrt(C!l)/l;
    end if;
  end if;
   
    
  result := [1/gaussfactor * Evaluate(
           intfemb[i] - 
	     EmbeddingAtRoot(EvaluateEpsilon(epstable,l),mf`roots[i])*
	     JacSymbol(-N,l)*
	     (Parent(twiddleintfemb[i])!mf`pseudoeigenvalues[N][i])*
	     twiddleintfemb[i], 
	       q1) :
	   i in [1 .. #mf`roots]];
  return [JacSymbol(r,l)/r*x : x in result];

end intrinsic;
  
  


intrinsic IntegralToCusp(mf :: Rec, alpha :: ModSymElt) -> SeqEnum
{ alpha is in the Ambientspace of mf`CMKf here 
}
  return IntegralToCusp(mf`CMKf, mf`heckebasisinsymbols, mf`periodsforheckebasis, mf`roots, alpha);
end intrinsic;



intrinsic IntegralToCusp(mf :: Rec, alpha :: ModTupFldElt) -> SeqEnum
{ alpha is in the Ambientspace of mf`CMKf here 
}
  return IntegralToCusp(mf`CMKf, mf`heckebasisinsymbols, mf`periodsforheckebasis, mf`roots, alpha);
end intrinsic;



intrinsic NaiveModularFormIntegration(mf :: Rec, tau :: Tup : 
                                      UseDegeneracy := true,
		                      TwiddleQ := 1) -> SeqEnum
{ This works for now, should be optimized later using precalculated series over C.
}
  Re := Parent(tau[2][1]);
    
  if UseDegeneracy then
    r := mf`degeneracy;
  else
    r := 1;
  end if;
  tau1 := [Re|r,0]*(tau[1]*tau[2]);
  
  /*if TwiddleQ eq 1 then
    res := NaiveModularFormIntegration(mf`form,mf`series,mf`roots,tau1);
    return [r*x : x in res];
  end if;
  */
    
  fp := mf`series;
  ytau := Imaginary(tau1);
  
  prec := Precision(tau1[1]);
  qprec := AbsolutePrecision(fp);
  qprecneeded := nodigeprecisie(prec,ytau);
  
   if qprecneeded gt qprec then
     print "q-precision needed:", qprecneeded;
     fp := qExpansion(mf`form,qprecneeded);
     mf`series := fp;
     StoreEmbeddedSeries(~mf);
  end if;  
  
  TwoPiI := [Zero(Parent(tau1[1])),2*Pi(Parent(tau1[2]))];
  qq := Exp(Mul(TwoPiI,tau1));
  
  P<q> := Parent(mf`embeddedseries[1]);
  
  return [r*Evaluate(Integral(p/q+O(q^qprecneeded)),qq) : p in Twiddle(mf,TwiddleQ)];
  
end intrinsic;



intrinsic ModularFormIntegration(mf :: Rec, tautje :: Tup) -> SeqEnum
{ This works for now, should be optimized later using precalculated series over C.
}
 // print "Starting integration.";
  
  N := Level(mf`form);
  r := mf`degeneracy;
  tau := r*tautje;
  gamma := tau[1];
  gamma1,gamma2 := DecomposeSL2ZMatrix0(N,gamma);
   
  C<I> := Parent(mf`roots[1]);
  Re := Parent(tau[2][1]);
  IdM := Matrix([[1,0],[0,1]]);

//Nu eerst integraal van gamma2(oo) naar gamma2(tau[2]) uitrekenen.
  if Eltseq(gamma2) eq [1,0,0,1] then
   // print "Naive evaluation suffices.";
    int1 := NaiveModularFormIntegration(mf,<gamma2,tau[2]> : UseDegeneracy := false);
  else
    z := C!tau[2];
    a1,b1,Q1,d1 := Explode(Eltseq(gamma2));
    Q := N div Q1; 
    
    if Norm(Q1*z+d1) le Q then
    //if false then //even testen of de rest werkt.
    //  print "Naive evaluation suffices.";
      int1 := NaiveModularFormIntegration(mf,<gamma2,tau[2]> : UseDegeneracy := false);
    else
    //  print "Atkin-Lehner trick needed.";
      wQ := WQ(Q,N);  
      //print "wQ =", wQ;
      
      a,b,c,d := Explode(Eltseq(wQ));
      a div:= Q; d div:= Q;
      
      wQ1 := Adjoint(wQ);
      tau1 := ((wQ1*gamma2)*tau[2]);
      twint1 := NaiveModularFormIntegration(mf,<IdM,tau1> : TwiddleQ := Q, UseDegeneracy := false);
      int10 := [mf`pseudoeigenvalues[Q][i]*twint1[i] : i in [1 .. #mf`roots]];
      
     // print "tau1 =",tau1;
    
      int1 := int10 + IntegralToCusp(mf,AmbientSpace(mf`CMKf)!<1,[Cusps()|Infinity(),a1/Q1]>);
     // print "Integral from oo to gamma2(tau) is", int1;
    end if;
  end if;
  
//Daarna geschikte cuspidale integralen en epsilon-twists toepassen.
  a,b,c,d := Explode(Eltseq(gamma1));
  int2 := [EmbeddingAtRoot(EvaluateEpsilon(mf`epsilonvalues,d),mf`roots[i])*int1[i] : i in [1 .. #mf`roots]];
  
 // if assigned cuspint then
 //   cuspint := [EmbeddingAtRoot(EvaluateEpsilon(mf`epsilonvalues,d),mf`roots[i])*cuspint[i] : i in [1 .. #mf`roots]];
 // end if;
  
  if c eq 0 then blaat := Cusps()!Infinity(); else blaat := Cusps()!(a/c); end if;
  int3 := int2 + IntegralToCusp(mf,AmbientSpace(mf`CMKf)!<1,[Cusps()|Infinity(),blaat]>);
  
//  if assigned cuspint then 
//    cuspint +:= IntegralToCusp(mf,AmbientSpace(mf`CMKf)!<1,[Cusps()|Infinity(),blaat]>);
//  else
//    cuspint := IntegralToCusp(mf,AmbientSpace(mf`CMKf)!<1,[Cusps()|Infinity(),blaat]>);
//  end if;
  
  //print "Sum of cuspidal integrals is", cuspint;
  
//En met r vermenigvuldigen natuurlijk.
  return [r*x : x in int3];
end intrinsic; 




intrinsic EvaluateNewformsAtTorsionPoints(newforms :: Tup, torsionpoints :: SeqEnum) -> SeqEnum
{ Input: newforms, or forms arising from newforms in a lower level.
    AND  a sequence of torsion points of the jacobian of the modular curve, calculated by FindAllTorsionPointsInSubspace.
  Output: a sequence of tuples <x,P> where P is an element of the Fl-vector space that corresponds to the l-torsion of the abelian variety 
          and where x is the sequence that has for each tau in P the sequence of evaluated newforms.
}
  formevals := [];
  left := #torsionpoints;
  for point in torsionpoints do
    print "Still", left, "points left.";
    Append(~formevals,<[[ModularFormEvaluation(mf,tau) : mf in newforms] : tau in point[1]],point[2]>);
    left -:= 1;
  end for;
  
  return formevals;
end intrinsic;



intrinsic GoodFunctions(forms :: Tup) -> Tup
{ Input: a tuple of forms, like ms`forms.
  Output: a tuple of tuples of coefficietns for these forms, such that the corresponding linear combinations are divisible by 
          a high power of q. This power of q increases along the output tuple. The corresponding coefficient of the power of q in the linear 
	  combination will be equal to 1.
}
  newforms := <mf`form : mf in forms>;
  dimensions := [Degree(BaseRing(Parent(newform))) : newform in newforms];
  g := &+ dimensions;
  
  ns := []; n := 1; 
  V := VectorSpace(Rationals(),g); 
  W := V;
  d := g;
  Ms := [];
  
  repeat
    M := TraceMatrix(NewformCoefficientsAt(newforms,n));
    W meet:= NullSpace(M);
    if Dimension(W) lt d then
      Append(~ns,n);
      Append(~Ms,M);
      d := Dimension(W);
    end if;
    n +:= 1;
  until d eq 0;
  
 // print "ns =",ns;
  
  M := (HorizontalJoin(Ms))^(-1);
 // print "M =",M;
  vs := [M[i] : i in [1 .. NumberOfRows(M)]];
  vvs := [Partition(Eltseq(v),dimensions) : v in vs];
  
  forms := <<BaseRing(Parent(newforms[i]))!vv[i] : i in [1 .. #dimensions]> : vv in vvs>;
  
  return forms;
//blabla
end intrinsic;



intrinsic ClosestTorsionPoint(periodlattice :: Lat, P :: ModTupFldElt, l :: RngIntElt) -> ModTupFldElt, FldReElt
{ Input: a (period) lattice.
    AND  a point P in the overlying C-vector space
    AND  an integer l.
  Output: the point of (1/l)*periodlattice that is closest to P.
    AND the squared distance between P and that point.
}
//print "Entering ClosestTorsionPoint";
  vec1 := ComplexToRealVector(l*P); VR := Parent(vec1);
  Re := BaseRing(VR);
//print "Calling ClosestVector";
  vecs, dist := ClosestVector(periodlattice,vec1);
//print "vecs=", vecs, ", dist=", dist;  
  henk := Re!(1/l) * (VR!vecs);
//print "henk=", henk;
//print "Calling RealToComplexVector";  
  point := RealToComplexVector(henk);
//print "point=", point;  
  dist /:= Re!(l*l); 
//print "dist=",dist;
//print "Leaving ClosestTorsionPoint";  
  return point, dist;
end intrinsic;





intrinsic TorsionPointToVector(point :: ModTupFldElt, periodlattice :: Lat, l :: RngIntElt) -> ModTupFldElt
{ Input: a point in a C-vector space.
    AND  a periodlattice according to which point is a torsion point.
    AND  an prime number l for which it is l-torsion.
  Output: the vector in the Fl-vector space (1/l)lattice/lattice that belongs to the point
}
  periods := Matrix(Basis(periodlattice));
  coeffs := ComplexToRealVector(point*l)*Inverse(periods);
  
  Fl := FiniteField(l);
  VF := VectorSpace(Fl,Dimension(Parent(coeffs)));
  return VF ! [ (Fl ! Round(coeff)) : coeff in Eltseq(coeffs)];
end intrinsic;



intrinsic LiftToZ(vec :: ModTupFldElt) -> ModTupRngElt
{ Input: a vector in a vector field over a finite field of prime order.
  Output: the vector over Z with all the coefficients lifted
}
  return RSpace(Integers(),Degree(Parent(vec))) ! [Integers()!a : a in Eltseq(vec)];
end intrinsic;



intrinsic MapToJacobian(ms :: Rec, taus :: SeqEnum : FromZero := true) -> ModTupFldElt
{ Input: a modular forms space and a sequence of points in the upper half plane.
  Output: a point in C^g that it is mapped to by the Abel-Jacobi map.
  Note: the optional parameter FromZero is to indicate whether the integration should be done from 0 or oo.
}
  result := &+[Vector(&cat[ModularFormIntegration(mf,tau) : mf in ms`forms ]): tau in taus];
  if FromZero then 
    result -:= (#taus)*ms`inttozero;
  end if;
  return result;
//blabla
end intrinsic;



intrinsic JacobianMatrix(ms :: Rec, taus :: SeqEnum) -> Mtrx
{ Returns the jacobian matrix needed in the Newton-Raphson iteration.
}
  Re := Parent(taus[1][2][1]);
  C<I> := ComplexField(Precision(Re));
  
  matrelts := [];
  for tau in taus do
    gamma := tau[1]; tau1 := tau[2];
    c := gamma[2][1]; d := gamma[2][2];
    modeval := Vector(&cat[ModularFormEvaluation(mf,tau): mf in ms`forms]);
    factor := 2*Pi(C)*I*(C!Pow([c,0]*tau1 + [d,0],-2));
    Append(~matrelts,factor*modeval);
  end for;
  
  return Matrix(matrelts);
end intrinsic;    



intrinsic NewtonRaphsonIteration(ms :: Rec, taus :: SeqEnum, phitaus :: ModTupFldElt, aim :: ModTupFldElt, maxlength :: FldReElt) -> SeqEnum
{ Input: a cusp forms space, belonging to a modular curve.
    AND  a sequence taus of numbers in the upper half plane
    AND  the vector phitaus which is the image of taus under the map to J(ms).
    AND  the (torsion) point we want to approximate.
    AND  the maximum length of the adjustment.
  Output: a new sequence of taus that hopefully maps to a point closer to aim.
}
  matr := JacobianMatrix(ms,taus);
  vec := (aim-phitaus)*Inverse(matr);
  if Real(Norm(vec)) ge maxlength*maxlength then
    vec *:= maxlength/Sqrt(Norm(vec));
  end if;
  
  result := [];
  for i in [1 .. #taus] do
    tau := taus[i];
    Append( ~result, <tau[1], [ tau[2][1] + Real(vec[i]), tau[2][2] + Imaginary(vec[i]) ]> );
  end for;
  
  return result;
end intrinsic;



intrinsic TrackAimedPoint(ms :: Rec, starttaus :: SeqEnum, point :: ModTupFldElt, aim :: ModTupFldElt, precloss ::RngIntElt : FromZero := true) -> SeqEnum
{ Input: a cusp forms space, belonging to a modular curve.
    AND  a sequence of taus that we start with.
    AND  the point that it maps to.
    AND  the aimed image of taus under integration.
    AND  the allowed loss of precision that we may have.
  Output: the sequence of taus mapping to the aimed point. The output will be the empty sequence if the process doesn't converge in time.
  Note: the optional parameter FromZero is to indicate whether we integrate from 0 of oo. 
}
  N := Level(ms`S);
  g := ms`dimension;
  
  prec := Precision(BaseRing(aim));
  Re := RealField(prec);
    
  aimeddistance := Re!10^(2*(precloss-prec));
  NRmaxlength := One(Re)/2;
    
  taus := starttaus;
  upperhalfplanebadluck := 0;
  steps := 0;
  
  dist := Norm(ComplexToRealVector(point-aim));
  NRlength := NRmaxlength;
    
  repeat
    //print "point=", point;
    //print "aim=", aim;
    newtaus := NewtonRaphsonIteration(ms,taus,point,aim,NRlength);
    newtaus := RewriteTaus(newtaus);
    //print "Mapping newtaus to Jacobian.";
    //print "newtaus= ", newtaus;
    newpoint :=  MapToJacobian(ms, newtaus : FromZero := FromZero);
    newdist := Norm(ComplexToRealVector(newpoint-aim));
    print "Distance to lattice point: ", RealField(10)!Sqrt(newdist);
    //print "Done.";
    if newdist ge dist then
      NRlength /:= 2;
    else
      taus := newtaus;
      point := newpoint;
      dist := newdist;
      NRlength := NRmaxlength;
    end if;
    
    steps +:= 1;
    if Divides(10,steps) then
      print "This was step number", steps;
    end if;
    
    if steps ge 1000 then
      return [];
    end if;
  until dist lt aimeddistance;

  return taus;
end intrinsic;



intrinsic TrackAimedPoint(ms :: Rec, starttaus :: SeqEnum, aim :: ModTupFldElt, precloss :: RngIntElt : FromZero := true) -> SeqEnum
{ Input: a cusp forms space, belonging to a modular curve.
    AND  a sequence of taus that we start with.
    AND  the aimed image of taus under integration.
    AND  the allowed loss of precision that we may have.
  Output: the sequence of taus mapping to the aimed point.
  Note: the optional parameter FromZero is to indicate whether we integrate from 0 of oo. 
}
  point := MapToJacobian(ms,starttaus : FromZero := FromZero);
  return TrackAimedPoint(ms,starttaus,point,aim,precloss : FromZero := FromZero);
end intrinsic;



nextpoint := procedure(~seq, l)
  i := 1; seq[1] +:= 1;
  while((seq[i] eq l) and (i lt #seq)) do
    seq[i] := 0;
    seq[i+1] +:= 1;
    i +:= 1;
  end while;
end procedure;



intrinsic FindAllTorsionPointsInSubspace(ms :: Rec, subspace :: ModTupFld, precloss :: RngIntElt : FromZero := true) -> SeqEnum
{ Input: the cusp forms belonging to a modular curve.
    AND  a subspace of the l-torsion (l-torsion basis is coming from periodlattice).
    AND  the allowed loss of precision that we may have.
  Output: a sequence consisting of tuples <taus,v> that gives us all the nonzero points of the subspace.
}
  print "Perfoming precalculations for torsion approximation";
  periodsr := ComplexToRealRows(ms`periodlattice);
  periodlattice := Lattice(periodsr);
  periodlr := Matrix(Basis(periodlattice));
  M := periodlr*Inverse(periodsr);
  nr := NumberOfRows(M);
  eltseq := Partition([Round(x) : x in Eltseq(M)],nr);
  MM := Matrix(eltseq);
  
  Fl := BaseRing(subspace);
  l := Characteristic(Fl);
  VF := VectorSpace(Fl,Degree(subspace));
  complement := Complement(VF,subspace);
  transitionmatrix := MatrixAlgebra(Fl,Degree(subspace))!MM;
    
  N := Level(ms`S);
  g := ms`dimension;
  prec := ms`precision;
  C<I> := ComplexField(prec);
  Re := RealField(prec);
  VR := VectorSpace(Re,Degree(subspace));
  numberofpoints := l^Dimension(subspace)-1;
  CMs := [mf`CMKf : mf in ms`forms];
  result1 := []; result2 := []; result := [];
  
  infos3 := <<mf`CMKf,mf`heckemodulebasis,mf`periodsforheckebasis> : mf in ms`forms>;
  rootss := [mf`roots : mf in ms`forms];
  
  overlatticebasis1 := [VR!LiftToZ(vec)/l : vec in Basis(subspace)] cat [VR!LiftToZ(vec) : vec in Basis(complement)];
  overlatticematrix1 := Matrix(overlatticebasis1);
  overlatticematrix := Mul(overlatticematrix1,periodsr);
  overlattice := Lattice(overlatticematrix);
  overlatticebasis := Basis(LLL(overlattice));
  interestingvectors := []; flvectors := [];
  for vector in overlatticebasis do
    vec := RealToComplexVector(VR!vector); flvec := TorsionPointToVector(vec,periodlattice,l);
    if IsIndependent(Append(flvectors,flvec)) then
      Append(~interestingvectors,vec);
      Append(~flvectors,flvec);
    end if;
  end for;
  VC := Parent(interestingvectors[1]);
  
  sjaak := g+10;
  randomtaus := RandomPointsInX1(Re,N,sjaak); //bevat nu meer dan genoeg punten.
  print "Mapping",sjaak,"random points to Jacobian.";
  imagesoftaus := [MapToJacobian(ms, [tau] : FromZero := FromZero) : tau in randomtaus];
  realimages := [ComplexToRealVector(v) : v in imagesoftaus];
  //nu goede deelverzameling vinden.
  
  thispoint := [0 : i in [1 .. Dimension(subspace)]];
  
  while(numberofpoints gt 0) do
   
    nextpoint(~thispoint,l);
    print "Now doing point number", thispoint;

    print "Trying to find point close to lattice point now.";
    interestingvector := &+[thispoint[i]*interestingvectors[i] : i in [1 .. #thispoint]];
        
    indices, lambda,point, afstand := SearchGoodVectorSum(realimages,g,ComplexToRealVector(interestingvector),periodlattice,1000);
  
    aim := interestingvector-RealToComplexVector(lambda);
    taus := [randomtaus[i] : i in indices];
  
    print "Distance to lattice point: ", RealField(10)!Sqrt(afstand);
  
    point := VC!RealToComplexVector(point);
  
    repeat
      newtaus := TrackAimedPoint(ms,taus,point,aim,precloss : FromZero := FromZero);
      if newtaus eq [] then
	print "Convergence failed.";
	randomtaus := RandomPointsInX1(Re,N,sjaak); //bevat nu meer dan genoeg punten.
        print "Mapping",sjaak,"random points to Jacobian.";
	imagesoftaus := [MapToJacobian(ms, [tau] : FromZero := FromZero) : tau in randomtaus];
        realimages := [ComplexToRealVector(v) : v in imagesoftaus];
	    
	print "Trying to find point close to lattice point now.";
        interestingvector := &+[thispoint[i]*interestingvectors[i] : i in [1 .. #thispoint]];
	indices, lambda,point, afstand := SearchGoodVectorSum(realimages,g,ComplexToRealVector(interestingvector),periodlattice,1000);
  
        aim := interestingvector-RealToComplexVector(lambda);
        taus := [randomtaus[i] : i in indices];
  
        print "Distance to lattice point: ", RealField(10)!Sqrt(afstand);
  
        point := VC!RealToComplexVector(point);
      end if;  
    until newtaus ne [];
	
    Append(~result,<newtaus,TorsionPointToVector(aim,periodlattice,l)*transitionmatrix>);
    print "Point found!";
   
    print newtaus; 
    numberofpoints -:= 1;
    print "Still", numberofpoints, "to go.";
   
  end while;
  return result;
end intrinsic;

  
intrinsic FindAllTorsionPointsInSubspace(ms :: Rec, subspace :: ModTupFld, precloss :: RngIntElt, previousresult :: SeqEnum : FromZero := true) -> SeqEnum
{ Input: the cusp forms belonging to a modular curve.
    AND  a subspace of the l-torsion (l-torsion basis is coming from periodlattice).
    AND  the allowed loss of precision that we may have.
    AND  the output of this intrinsic, calculated to a smaller precision.
  Output: a sequence consisting of tuples <taus,v> that gives us all the nonzero points of the subspace.
}
  print "performing precalculations for torsion approximation";
  periodsr := ComplexToRealRows(ms`periodlattice);
  periodlattice := Lattice(periodsr);
  Fl := BaseRing(subspace);
  l := Characteristic(Fl);
  VF := VectorSpace(Fl,Degree(subspace));
  complement := Complement(VF,subspace);
  N := Level(ms`S);
  g := ms`dimension;
  prec := ms`precision;
  C<I> := ComplexField(prec);
  Re := RealField(prec);
  VR := VectorSpace(Re,Degree(subspace));
  //numberofpoints := l^Dimension(subspace)-1;
  numberofpoints := #previousresult;
  CMs := [mf`CMKf : mf in ms`forms];
  result1 := []; result2 := []; result := [];
  
  infos3 := <<mf`CMKf,mf`heckemodulebasis,mf`periodsforheckebasis> : mf in ms`forms>;
  rootss := [mf`roots : mf in ms`forms];
  
  overlatticebasis1 := [VR!LiftToZ(vec)/l : vec in Basis(subspace)] cat [VR!LiftToZ(vec) : vec in Basis(complement)];
  overlatticematrix1 := Matrix(overlatticebasis1);
  overlatticematrix := Mul(overlatticematrix1,periodsr);
  overlattice := Lattice(overlatticematrix);
  overlatticebasis := Basis(LLL(overlattice));
  interestingvectors := []; flvectors := [];
  for vector in overlatticebasis do
    vec := RealToComplexVector(VR!vector); flvec := TorsionPointToVector(vec,periodlattice,l);
    if IsIndependent(Append(flvectors,flvec)) then
      Append(~interestingvectors,vec);
      Append(~flvectors,flvec);
    end if;
  end for;
  VC := Parent(interestingvectors[1]);

  typeofpoint := PowerSequence(car<RMatrixSpace(IntegerRing(), 2, 2), PowerSequence(Re)>);

  print "Starting to find points.";
  for prevpoint in previousresult do
    
    VFlpart := prevpoint[2];
    previoustaus := typeofpoint!prevpoint[1];
    taus := [];

//We moeten previoustaus reduceren, dwz de matrices terugbrengen naar representanten voor Gamma1(N)\SL2(Z).
    for tau in previoustaus do
      _,gamma1 := DecomposeSL2ZMatrix1(N,tau[1]);
      Append(~taus,<gamma1,tau[2]>);
    end for;
    //print "Point from previous calculation: ";
    //print taus;
    
//Daarna moeten we het beeld in C^g/L pakken.
    point := MapToJacobian(ms,taus : FromZero := FromZero);
    //print "Image point:";
    //print point;
//Daarna moeten we het dichtstbijzijnde punt van (1/l)L/L pakken als aim.
    aim,afstand := ClosestTorsionPoint(periodlattice,point,l);
    //print "Closest torsion point:";
    //print aim;    
    print "Distance to lattice point: ", RealField(10)!Sqrt(afstand);
//En we kunnen het aimpoint gaan tracken.
    newtaus := TrackAimedPoint(ms,taus,point,aim,precloss : FromZero := FromZero);
    Append(~result,<newtaus,VFlpart>);
    print "Point found!"; 
    print newtaus;
    //PrintFileMagma("dumpfile",newtaus);
    numberofpoints -:= 1;
    print "Still", numberofpoints, "to go.";
  
  end for;
  
  return result;
end intrinsic;




intrinsic FindAllTorsionPointsInSubspace(ms :: Rec, subspace :: ModTupFld, precloss :: RngIntElt, 
                                         previousresult :: SeqEnum, startpoint :: RngIntElt, endpoint :: RngIntElt : FromZero := true) -> SeqEnum
{ Input: the cusp forms belonging to a modular curve.
    AND  a subspace of the l-torsion (l-torsion basis is coming from periodlattice).
    AND  the allowed loss of precision that we may have.
    AND  the output of this intrinsic, calculated to a smaller precision.
    AND  two indices of this precalculated sequence.
  Output: a sequence consisting of tuples <taus,v> that gives us all the nonzero points of the subspace, from index startpoint to endpoint.
}
  prevres := previousresult[startpoint .. endpoint];
  return FindAllTorsionPointsInSubspace(ms,subspace,precloss,prevres : FromZero := FromZero);
end intrinsic;
intrinsic SearchPointList(torsionpoints :: SeqEnum, point :: .) -> Tup
{ Input: a sequence of torsion points and a vector in an Fl-vector space.
  Output: the element of the sequence corresponding to the vector.
}
  return [x : x in torsionpoints | x[2] eq point][1];
end intrinsic;



psqq := function(as,C)
  n := #as;
  prec := Max(Precision(as[1]),n);
  Re := RealField(prec);
  M := IdentityMatrix(Re,n+1);
  for i := 1 to n do
    M[n+1][i] := Re!(-as[i]);
  end for;
  M[n+1][n+1] := Re!10^(-C);
  N,L := LLL(M);
  return Eltseq(L[1]);
end function;


intrinsic NewCommonDenominator(xs :: SeqEnum) -> BoolElt, RngIntElt
{ Input: a sequence of real numbers which are supposed to be close to rational numbers.
  Output: a bool indicating whether they have a common denominator (i.e. whether they are accurate enough)
     AND if true, the common denominator.
  Note: makes use of LLL 
}
  prec := Precision(xs[1]);
  n := #xs;
  for C := prec-10 to 10 by -10 do
    ppqq := psqq(xs,C);
    q := ppqq[#ppqq];
    if q ne 0 then
      if &and [ Abs(ppqq[i]-q*xs[i]) lt 10^(-10)/Abs(q)^(1/n) : i in [1 .. n] ] then
        return true,Abs(q);
      end if;
    end if;
  end for;
  return false,0;
end intrinsic;



intrinsic CommonDenominator(xs :: SeqEnum : Method := "LLL") -> BoolElt, RngIntElt
{ Input: a sequence of real numbers which are supposed to be close to rational numbers.
  Output: a bool indicating whether they have a common denominator (i.e. whether they are accurate enough)
     AND if true, the common denominator.
  Note: Method can be either "LLL" or "ContFrac".
}
  if Method eq "LLL" then 
    return NewCommonDenominator(xs);
  end if;
  
  temp := Reverse(xs); denom := 1;
  while &or[Abs(x-Round(x)) gt 10^(-10) : x in temp] do
    testcase := [x : x in temp | Abs(x-Round(x)) gt 10^(-10)][1];
    d := Denominator(testcase);
    if d eq 0 then return false, 0; end if;
    denom *:= d; 
    temp := [d*x : x in temp];
  end while;
  return true,denom;
end intrinsic;



intrinsic ComputeBigPGLPolynomial(G :: GrpPSL2, space :: ModTupFld) -> RngUPolElt
{ space is an Fl-vector space, which is a subspace of H1(X(G),Fl). 
  The output is a polynomial for the PGL-representation 
  associated to the subspace of Jac(X(G)) that corresponds to space.
  Or actually the subgroup of PGL corresponding to G.
}
  print "Performing precalculations.";
  N := Level(G);
  Fl := BaseRing(space); 
  l := Characteristic(Fl);
  Malg := MatrixAlgebra(FiniteField(l),Degree(space)); 
  ms := CreateModSpace(G, 20, 20*N div 2);
  hecke := {Malg!HeckeMatrix(ms`CM,p,ms`H1basis) : p in [2 .. 500] | Gcd(N*l,p) eq 1};
  hecke := SetToSequence(hecke);
  Exclude(~hecke,0);
  eltseq := [x : x in space];
  Exclude(~eltseq,0);
  lines := {{x*y : y in hecke}: x in eltseq};
  
  torsion := FindAllTorsionPointsInSubspace(ms,space,10);
  prec := 30;
  repeat
    prec := 2*prec - 20;
    ms := CreateModSpace(G, prec, prec*N div 2);
    torsion := FindAllTorsionPointsInSubspace(ms,space,10,torsion);
    pointevals := EvaluateGoodFunctionAtTorsionPoints(ms,torsion);
    C<I> := Parent(pointevals[1][1]);
    PC<X> := PolynomialRing(C);
    pol := &*[X-&+[x[1] : x in pointevals | x[2] in line]: line in lines];
    polr := Polynomial([Real(x) : x in Eltseq(pol)]);
    b, d := CommonDenominator(Eltseq(polr));
  until b;  
  
  return Polynomial([Round(x*d): x in Eltseq(polr)]);
end intrinsic;



intrinsic ComputeBigPGLPolynomial0plus(N :: RngIntElt, space :: ModTupFld) -> RngUPolElt
{ space is an Fl-vector space, which is a subspace of H1(X0(N)+,Fl). 
  The output is a polynomial for the PGL-representation 
  associated to the subspace of Jac(X0(N)+) that corresponds to space.
  Or actually the subgroup of PGL corresponding to G.
}
  print "Performing precalculations.";
  Fl := BaseRing(space); 
  l := Characteristic(Fl);
  Malg := MatrixAlgebra(FiniteField(l),Degree(space)); 
  ms := CreateModSpace0plus(N, 20, 20*N div 2);
  hecke := {Malg!HeckeMatrix(ms`CM,p,ms`H1basis) : p in [2 .. 500] | Gcd(N*l,p) eq 1};
  hecke := SetToSequence(hecke);
  Exclude(~hecke,0);
  eltseq := [x : x in space];
  Exclude(~eltseq,0);
  lines := {{x*y : y in hecke}: x in eltseq};
  
  torsion := FindAllTorsionPointsInSubspace(ms,space,10);
  prec := 30;
  repeat
    prec := 2*prec - 20;
    ms := CreateModSpace0plus(N, prec, prec*N div 2);
    torsion := FindAllTorsionPointsInSubspace(ms,space,10,torsion);
    pointevals := EvaluateGoodFunctionAtTorsionPoints(ms,torsion);
    C<I> := Parent(pointevals[1][1]);
    PC<X> := PolynomialRing(C);
    pol := &*[X-&+[x[1] : x in pointevals | x[2] in line]: line in lines];
    polr := Polynomial([Real(x) : x in Eltseq(pol)]);
    b, d := CommonDenominator(Eltseq(polr));
  until b;  
  
  return Polynomial([Round(x*d): x in Eltseq(polr)]);
end intrinsic;



intrinsic pMaximalOverOrder(O :: RngOrd, p :: RngIntElt : Reduce := false) -> RngOrd
{ p needs not be prime.
}
  if p eq 1 then
    return O;
  end if;
    
  ovr := MultiplicatorRing(pRadical(O,p));
  if Reduce then
    print "Performing lattice reduction";
    ovr := LLL(ovr);
  end if;
  print "index is", Index(ovr,O); 
  return  (Index(ovr,O) eq 1) select ovr else pMaximalOverOrder(ovr,p : Reduce := Reduce);
end intrinsic;  

  
intrinsic LenstraTrick(f :: RngUPolElt) -> RngOrd
{ f is a polynomial in Z[x], not monic. We'll output a good order in the number field defined by f.
}
  K:=NumberField(f);
  L:=Eltseq(f);
  L:=Reverse(L);
  M:=[K ! 1];
  for j in [1..Degree(f)-1] do 
    a:=0;
    for k in [1..j] do
      a:=a+L[k]*K.1^(j-k+1);
    end for;
    Append(~M,a);
  end for;
  return Order(M);
end intrinsic;


intrinsic NewMaximalOrder(f :: RngUPolElt : TestPrimeLimit := 100000000, Reduce := false) -> RngOrd
{ Reduce indicated whether lattice reduction should be performed in each step.
}
  print "Maximalising the order at small primes";
  disc := Discriminant(f);
  ltt := Coefficient(f,Degree(f));
  smallprimes := [p : p in [2 .. TestPrimeLimit] | IsPrime(p) and (disc mod p eq 0 or ltt mod p eq 0)];
  O := LenstraTrick(f);
  for p in smallprimes do
    O := pMaximalOverOrder(O,p : Reduce := Reduce);
  end for;
  discO := Abs(Discriminant(O));
  smallprimes2 := [p : p in smallprimes | discO mod p eq 0];
  ltred := Gcd(ltt,discO);
  ltred div:= &*[p^Valuation(ltred,p) : p in smallprimes2];
  O := pMaximalOverOrder(O,ltred); //We assume that ltred is squarefree;
  discO := Abs(Discriminant(O));\
  discO div:= Gcd(ltt,discO);
  q := discO div &*[p^Valuation(discO,p) : p in smallprimes2];
  b,qq := IsSquare(q);
  if not b then
    print "Warning: computed order might not be maximal.";
    qq := q;
  end if;
   
  O := pMaximalOverOrder(O,qq);
  return O;
end intrinsic;



intrinsic SmallPolynomial(f :: RngUPolElt : TestPrimeLimit := 100000000 , Reduce := false) -> RngUPolElt
{ Outputs a polynomial with small coefficients defining the same number field as f.
  Reduce indicates whether a lattice reduction should be performed at each step or only at the end.
}
  O := NewMaximalOrder(f : TestPrimeLimit := TestPrimeLimit, Reduce := Reduce);
  print "Performing lattice reduction.";
  //O := LLL(O,f,7);//Here, 7 is a bit arbitrary.
  O := LLL( O, 7, 3*Log(Max([Abs(x) : x in Eltseq(f)]))/Log(10) );
  g := MinimalPolynomial(O.2);
  assert Degree(g) eq Degree(f);
  return PolynomialRing(Integers())!g;
end intrinsic;






intrinsic ComputeBigPGLPolynomial(f :: ModFrmElt, pp :: . : MinimumPrecision := 100) -> RngUPolElt
{ Computes a polynomial for the PGL-representation associated to f mod pp.
}
  ha, space := FindRepresentationSpace(f,pp);
  N := Level(f);
  print "Performing precalculations.";
  Fl := BaseRing(space); 
  l := Characteristic(Fl);
  M := MatrixAlgebra(FiniteField(l),Degree(space)); 
  //V := VectorSpace(Fl,#ha`basis);
  V := Complement(VectorSpace(Fl,#ha`basis),Annihilator(ha,space));
  ms := CreateModSpace(ha,20);
  print "Performing certain Hecke calculations";
//print "  hecke := { &+[ v[i] * M!ha`basis[i] : i in [1 .. #ha`basis] ] : v in V};";
  hecke := { &+[ v[i] * M!ha`basis[i] : i in [1 .. #ha`basis] ] : v in V};
//print "  hecke := SetToSequence(hecke);";
  hecke := SetToSequence(hecke);
  Exclude(~hecke,0);
//print "  eltseq := [x : x in space];";
  eltseq := [x : x in space];
  Exclude(~eltseq,0);
//print "  lines := {{x*y : y in hecke}: x in eltseq};";
  lines := {{x*y : y in hecke}: x in eltseq};
  
  print "Starting torsion approximation";
  FromZero := true;
  torsion := FindAllTorsionPointsInSubspace(ms,space,10);
  prec := 30;
  repeat
    prec := 2*prec - 20;
    ms := CreateModSpace(ha,prec);
    //if prec ge MinimumPrecision then
    torsion := FindAllTorsionPointsInSubspace(ms,space,10,torsion : FromZero := FromZero);
    if prec ge MinimumPrecision then
      pointevals := EvaluateGoodFunctionAtTorsionPoints(ms,torsion);
      C<I> := Parent(pointevals[1][1]);
      PC<X> := PolynomialRing(C);
      pol := &*[X-&+[x[1] : x in pointevals | x[2] in line]: line in lines];
      polr := Polynomial([Real(x) : x in Eltseq(pol)]);
      b, d := CommonDenominator(Eltseq(polr));
    else
      b := false;
    end if;
  until b;

  return Polynomial([Round(x*d): x in Eltseq(polr)]);
//blabla
end intrinsic



intrinsic ComputeBigGLPolynomial(f :: ModFrmElt, pp :: . : MinimumPrecision := 100) -> RngUPolElt
{ Computes a polynomial for the GL-representation associated to f mod pp.
}
  ha, space := FindRepresentationSpace(f,pp);
  N := Level(f);
  print "Performing precalculations.";
  Fl := BaseRing(space); 
  l := Characteristic(Fl);
  ms := CreateModSpace(ha,20);
  
  print "Starting torsion approximation";
  FromZero := true;
  torsion := FindAllTorsionPointsInSubspace(ms,space,10);
  prec := 30;
  repeat
    prec := 2*prec - 20;
    ms := CreateModSpace(ha,prec);
    //if prec ge MinimumPrecision then
    torsion := FindAllTorsionPointsInSubspace(ms,space,10,torsion : FromZero := FromZero);
    if prec ge MinimumPrecision then
      pointevals := EvaluateGoodFunctionAtTorsionPoints(ms,torsion);
      C<I> := Parent(pointevals[1][1]);
      PC<X> := PolynomialRing(C);
      pol := &*[X-x[1] : x in pointevals];
      polr := Polynomial([Real(x) : x in Eltseq(pol)]);
      b, d := CommonDenominator(Eltseq(polr));
    else
      b := false;
    end if;
  until b;
  
  return Polynomial([Round(x*d): x in Eltseq(polr)]);
end intrinsic;



intrinsic ComputePGLPolynomial(f :: ModFrmElt, pp :: . : MinimumPrecision := 100) -> RngUPolElt
{ Computes a polynomial for the PGL-representation associated to f mod pp.
}
  pol := ComputeBigPGLPolynomial(f,pp : MinimumPrecision := MinimumPrecision);
  return SmallPolynomial(pol);
end intrinsic;
