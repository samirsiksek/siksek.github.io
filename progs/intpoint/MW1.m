declare verbose GroupInfo, 2;
declare verbose DeepInfo, 3;
declare verbose MWSieve, 3;

/***********************************************************
 disclog.m
 
 General purpose discrete log for groups of smooth order
 
 M. Stoll, started 2005-06-07
 converted to package file 2006-03-05
 ***********************************************************/

// given: Abelian group G, bijective map G -> X, X some structure
// #G smooth (so that for groups of order p^f|#G, lookup is feasible)

// Exported intrinsics: 
//  MakeDL(G, m, mul, sub)
//     m : G -> X  is the map (UserProgram)
//   mul : Z x X -> X  is multiplication by integers (UserProgram)
//   sub : X x X -> X  is subtraction (UserProgram)
// MakeDL(G, m)
//     m : G -> X is the map (Map), * and + defined on X

function MakeLookup(G, m)
  pairs := [<m(g), g> : g in G];
  return pmap<{p[1] : p in pairs} -> G| pairs>;
end function;

function MakeDLp(G, m, p, mul, sub)
  // G a p-group
  // mul = scalar multplication in image group
  // sub = subtraction
  if #G le 25 then
    return MakeLookup(G, m);
  end if;
  invs := Invariants(G);
  // printf "MakeDLp: Invariants(G) = %o\n", invs;
  pp := ExactQuotient(invs[#invs], p);
  if pp eq 1 then
    return MakeLookup(G, m);
  end if;
  // printf "MakeDLp: pp = %o\n", pp;
  h := hom<G -> G | [pp*G.i : i in [1..#invs]]>;
  G1 := Image(h);
  // printf "MakeDLp: Invariants(Image(h)) = %o\n", Invariants(G1);
  f1 := MakeLookup(G1, func<x | m(G!x)>);
  G2 := Kernel(h);
  // printf "MakeDLp: Invariants(Kernel(h)) = %o\n", Invariants(G2);
  f2 := MakeDLp(G2, func<x | m(G!x)>, p, mul, sub);
  return func<x | f2(sub(x, m(G!a))) + a where a := f1(mul(pp,x)) @@ h>;
end function;

intrinsic MakeDL(G::GrpAb, m::UserProgram, mul::UserProgram, sub::UserProgram) -> UserProgram
{ Given bijection  m : G -> X, multiplication by integers on X, subtraction 
  on X, compute the inverse of m. Assumes that #G is smooth.}
  n := #Invariants(G);
  f := Factorization(#G);
  cofs := [&*[Integers()|f[i,1]^f[i,2] : i in [1..#f] | i ne j] : j in [1..#f]];
  _, refs := XGCD(cofs);
  assert &+[Integers()|refs[i]*cofs[i] : i in [1..#f]] eq 1;
  DLs := [**];
  for i := 1 to #f do
    p := f[i,1];
    hp := hom<G -> G | [cofs[i]*G.j : j in [1..n]]>;
    Gp := Image(hp);
    DLp := MakeDLp(Gp, func<x | m(G!x)>, p, mul, sub);
    Append(~DLs, DLp);
  end for;
  return func<x | &+[G|refs[i]*G!(DLs[i](mul(cofs[i],x))) : i in [1..#f]]>;
end intrinsic;

function MakeLookup1(G, m)
  return pmap<Codomain(m) -> G| [<m(g), g> : g in G]>;
end function;

function MakeDLp1(G, m, p)
  // G a p-group
  if #G le 25 then
    return MakeLookup1(G, m);
  end if;
  invs := Invariants(G);
  // printf "MakeDLp: Invariants(G) = %o\n", invs;
  pp := ExactQuotient(invs[#invs], p);
  if pp eq 1 then
    return MakeLookup1(G, m);
  end if;
  // printf "MakeDLp: pp = %o\n", pp;
  h := hom<G -> G | [pp*G.i : i in [1..#invs]]>;
  G1 := Image(h);
  // printf "MakeDLp: Invariants(Image(h)) = %o\n", Invariants(G1);
  m1 := map<G1 -> Codomain(m) | x:->m(x)>;
  f1 := MakeLookup1(G1, m1);
  G2 := Kernel(h);
  // printf "MakeDLp: Invariants(Kernel(h)) = %o\n", Invariants(G2);
  m2 := map<G2 -> Codomain(m) | x:->m(x)>;
  f2 := MakeDLp1(G2, m2, p);
  return pmap<Codomain(m) -> G |
               x :-> f2(x - m(a)) + a where a := f1(pp*x) @@ h>;
end function;

intrinsic MakeDL(G::GrpAb, m::Map) -> Map
{ Given bijection  m : G -> X, where X has group structure, compute the
  inverse of m. Assumes that #G is smooth.}
  n := #Invariants(G);
  f := Factorization(#G);
  cofs := [&*[Integers()|f[i,1]^f[i,2] : i in [1..#f] | i ne j] : j in [1..#f]];
  _, refs := XGCD(cofs);
  assert &+[Integers()|refs[i]*cofs[i] : i in [1..#f]] eq 1;
  DLs := [**];
  for i := 1 to #f do
    p := f[i,1];
    hp := hom<G -> G | [cofs[i]*G.j : j in [1..n]]>;
    Gp := Image(hp);
    mp := map<Gp -> Codomain(m) | x:->m(x)>;
    DLp := MakeDLp1(Gp, mp, p);
    Append(~DLs, DLp);
  end for;
  return pmap<Codomain(m) -> G
               | x :-> &+[G|refs[i]*G!(DLs[i](cofs[i]*x)) : i in [1..#f]]>;
end intrinsic;

/********************************************************
 * g2-jacobian-equations.m
 *
 * smooth projective model of genus 2 Jacobian in P^15
 *
 * M. Stoll, started 2006-03-05
 ********************************************************/

intrinsic JacEquations(fpol::RngUPolElt) -> SeqEnum
{ Given polynomial f, return the 72 quadrics defining the Jacobian of
  y^2 = f(x) in P^15. }
  R := Universe(Coefficients(fpol));
  require Degree(fpol) le 6: "The polynomial must be of degree at most 6.";
  P16<[z]> := PolynomialRing(R, 16);
  a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15 := Explode(z);
  f0,f1,f2,f3,f4,f5,f6 := Explode([Coefficient(fpol, i) : i in [0..6]]);
  eqns := [
     -a0*a11+f1*a14*a3+f3*a10*a5+f5*a3*a10+2*a4*a3,
     -a0*a10+a3^2,
     -a0*a12+a3*a5,
     -f0*f2*a14^2-f0*a14*a5-8*f0*f6*a12^2-f3*f5*a12*a10-f1*f6*a13*a10
       -f2*f5*a13*a10-f1*f5*a13*a11-3*f5*f0*a13*a12-f1*f3*a14*a12
       -f3*f0*a14*a13-f0*f6*a14*a10-f2*f4*a14*a10+a4^2-a0*a12-6*f0*f6*a12*a15
       -f2*f6*a10*a15-f1*f6*a11*a15-f5*f0*a13*a15-f1*f4*a14*a11-f2*a12*a5
       -f4*f0*a13^2-f0*f6*a15^2-f4*f6*a10^2-f6*a10*a3-f4*a10*a5-f3*f6*a10*a11
       -4*f2*f6*a10*a12-2*f1*f6*a11*a12,
     -a0*a13+f1*a14*a5+f3*a14*a3+f5*a10*a5+2*a5*a4,
     -a0*a14+a5^2,
     -4*f0*f2*a14^2-4*f0*a14*a5+a0*a15-36*f0*f6*a12^2-4*f3*f5*a12*a10
       -4*f1*f6*a13*a10-4*f2*f5*a13*a10-12*f5*f0*a13*a12-2*f1*f3*a14*a12
       -4*f3*f0*a14*a13-4*f2*f4*a14*a10-4*f5*a10*a4-f5^2*a10^2-24*f0*f6*a12*a15
       -4*f2*f6*a10*a15-4*f1*f6*a11*a15-4*f5*f0*a13*a15-4*f1*f4*a14*a11
       +f3^2*a14*a10-2*f3*a11*a5-16*f1*f5*a12^2-2*f1*a13*a5-4*f2*a12*a5
       -4*f0*f6*a15^2-4*f4*f6*a10^2-4*f6*a10*a3-4*f4*a10*a5-4*f3*f6*a10*a11
       -16*f2*f6*a10*a12-8*f1*f6*a11*a12+f1^2*a14^2-16*f0*f4*a14*a12
       -4*f1*f5*a12*a15-4*f0*f4*a14*a15,
     -f1*a14^2-f3*a14*a12+2*f4*a13*a12-f5*a12^2-2*a4*a14-2*f4*a14*a11+a5*a13,
     -f1*a14*a12-f3*a14*a10-f5*a12*a10-2*a4*a12+a5*a11,
     2*f4*a14*a10+2*f5*a12*a11-4*a5*a12-2*f4*a12^2-a5*a15+f1*a14*a13
       +f3*a14*a11-f5*a13*a10+2*a4*a13,
     -f5*a10^2-f3*a10*a12+2*f2*a11*a12-f1*a12^2-2*a4*a10-2*f2*a13*a10+a3*a11,
     f2*a12^2+f1*a13*a12-a5*a10-f1*a14*a11-f2*a10*a14+a3*a12,   
     f5*a13*a10+f4*a14*a10-a5*a12-f4*a12^2-f5*a12*a11+a3*a14,   
     -f1*a14*a12-f3*a14*a10-f5*a12*a10-2*a4*a12+a3*a13,
     4*f1*a13*a12-2*a5*a10-3*f1*a14*a11-a3*a15-2*a3*a12+f5*a10*a11
       +f3*a10*a13+2*a4*a11,
     -a14*a15-4*a12*a14+a13^2,
     -a10*a14+a12^2,
     -a10*a15-4*a10*a12+a11^2,
     -a11*a13+2*a10*a14+a12*a15+2*a12^2,
     -a12*a13+a11*a14,
     -a11*a12+a10*a13,
     -a10^2*f2*f5^2-a11^2*f0*f5^2+a1^2-a0*a3+8*f0*f6*a4*a11-a10^2*f3^2*f6
       -f4*a3^2-f0*a5^2+4*a10^2*f1*f5*f6+4*a10^2*f2*f4*f6-a10*a3*f3*f5
       +4*a10*a3*f2*f6+8*f1*f6*a10*a4+f1*f5*a10*a5+4*a11^2*f0*f4*f6
       -a10*a11*f1*f5^2+4*a10*a11*f0*f5*f6+4*a10*a11*f1*f4*f6+4*f0*f5*a12*a4
       +2*a12*a10*f0*f5^2+6*a12*a10*f1*f3*f6+8*f0*f3*f6*a12*a11
       +4*a14*a10*f0*f2*f6+2*a14*a10*f0*f3*f5+3*a14*a10*f1^2*f6
       +4*f0*f1*f6*a14*a11+2*f0*f1*f5*a14*a12,
     a1*a2-a0*a4+3*a13*a10*f0*f5^2+a13*a10*f1*f3*f6+2*a10^2*f2*f5*f6
       +f3*f6*a10*a3+4*f2*f6*a10*a4+a10*a5*f2*f5+5*a10*a5*f1*f6+4*f1*f6*a12*a3
       +20*f0*f6*a12*a4+10*f0*f5*f6*a10*a12+2*a12^2*f1*f3*f5+28*a12^2*f0*f3*f6
       +4*a12^2*f1*f2*f6+3*f1*f5*a12*a4+2*a12*a10*f1*f4*f6+2*a12*a10*f2*f3*f6
       +a12*a10*f1*f5^2-4*f0*f5^2*a12*a11-4*f0*f6*f4*a12*a11+2*f0*f4*a13*a5
       +8*a10*a13*f0*f4*f6+8*a13*a12*f0*f2*f6+3*a13*a12*f0*f3*f5
       -a13*a12*f1^2*f6+9*a14*a3*f0*f5+a14*a3*f1*f4+f0*f3*a14*a5
       -2*f1*f6*f2*a14*a10-8*f0*f6*f3*a14*a10-2*f0*f5*f3*a14*a11
       -4*f0*f6*f2*a14*a11+10*f1*f6*f0*a14*a12+2*a14*a12*f0*f2*f5
       +a14*a12*f1^2*f5+2*f1*f6*a3*a15+4*f0*f6*a4*a15+2*f0*f5*a5*a15
       +2*f0*f5*f6*a10*a15+4*f0*f3*f6*a12*a15+2*f1*f6*f0*a14*a15,
     -a14^2*f0*f3^2-a14^2*f1^2*f4+a2^2-a0*a5-f6*a3^2-f2*a5^2+8*a13*a4*f0*f6
       +4*f0*f5*a13*a5+4*a13*a10*f0*f5*f6-4*a13*a10*f1*f4*f6+4*f0*f4*a14*a5
       +4*a10*a14*f0*f4*f6-a10*a14*f0*f5^2+4*a10*a14*f1*f3*f6+8*f1*f6*a12*a4
       +4*f1*f5*f6*a12*a10+4*f1*f6*f4*a12*a11-2*f1*f6*a13*a3+4*a14*a13*f0*f1*f6
       +4*a14*a13*f0*f2*f5-a14*a13*f1^2*f5+4*a14^2*f0*f2*f4+f1*f5*a14*a3
       -a14*a5*f1*f3+8*a14*a11*f0*f3*f6+16*a14*a12*f0*f2*f6+2*a14*a12*f0*f3*f5
       +4*a14*f0*f2*f6*a15-a14*f1^2*f6*a15,
     -a0*a14-f2*a14*a5-f3*a14*a4-2*f4*a14*a3-3*f5*a4*a12-f6*a3*a15
       -5*f6*a3*a12-f1*f3*a14^2-f1*f4*a14*a13-f1*f5*a14*a15-5*f1*f5*a12*a14
       -f1*f6*a13*a15-3*f1*f6*a13*a12-2*f2*f4*a14*a12-2*f2*f5*a13*a12
       -2*f2*f6*a13*a11-3*f3*f5*a14*a10-2*f3*f6*a12*a11-2*f4*f6*a12*a10
       -f5^2*a12*a10+a2*a9,
     -a0*a13+f1*a14*a5+f3*a5*a12-f5*a10*a5-2*f6*a11*a3+2*f0*f3*a14^2
       +4*f0*f4*a14*a13+4*f5*f0*a14*a15+14*f5*f0*a14*a12+4*f0*f6*a13*a15
       +8*f0*f6*a13*a12+4*f0*f6*a14*a11+2*f1*f4*a14*a12+2*f1*f5*a13*a12
       +2*f1*f6*a12*a15+8*f1*f6*a12^2+2*a2*a8,
     2*f2*a3*a14-a0*a15+40*f0*f6*a12^2+6*f3*f5*a12*a10+4*f2*f5*a13*a10
       +8*f5*f0*a13*a12+3*f1*f3*a14*a12+2*f3*f0*a14*a13+8*f0*f6*a14*a10
       +4*f2*f4*a14*a10-2*a0*a12+4*f5*a10*a4+f5^2*a10^2+4*f3*a12*a4
       +28*f0*f6*a12*a15+4*f1*f6*a11*a15+4*f5*f0*a13*a15+4*f1*f4*a14*a11
       +f3^2*a14*a10+4*f2*f6*a11^2+16*f1*f5*a12^2+f1*a13*a5+2*a2*a7
       +4*f0*f6*a15^2+4*f4*f6*a10^2+2*f6*a10*a3+4*f4*a10*a5+4*f3*f6*a10*a11
       +14*f1*f6*a11*a12+16*f0*f4*a14*a12+4*f1*f5*a12*a15+4*f0*f4*a14*a15
       +f1*f5*a14*a10+6*a14*a11*f0*f5,
     -a0*a11-4*f0*a13*a5-f1*a15*a5-5*f1*a12*a5-2*f2*a11*a5-f3*a10*a5
       +f5*a3*a10-4*f0*f2*a14*a13-2*f3*f0*a15*a14-10*f0*f3*a14*a12
       -4*f0*f4*a14*a11-2*a15*a12*f0*f5-6*f0*f5*a12^2+f1^2*a14*a13
       -f1*f3*a14*a11-2*f1*f4*a12^2-f1*f5*a13*a10+2*a2*a6,
     -a0*a10-f4*a3*a10-f3*a4*a10-2*f2*a10*a5-3*f1*a12*a4-f0*a15*a5
       -5*f0*a12*a5-f5*f3*a10^2-f5*f2*a10*a11-f1*f5*a15*a10-5*f1*f5*a10*a12
       -a15*a11*f0*f5-3*f5*f0*a11*a12-2*f4*f2*a10*a12-2*f4*f1*a11*a12
       -2*f0*f4*a13*a11-3*a14*a10*f1*f3-2*f3*f0*a13*a12-2*f0*f2*a14*a12
       -f1^2*a14*a12+a6*a1,
     -a0*a11+f5*a3*a10+f3*a3*a12-f1*a14*a3-2*f0*a13*a5+2*f6*f3*a10^2
       +4*f2*f6*a10*a11+4*a10*f1*f6*a15+14*a10*a12*f1*f6+4*f0*f6*a15*a11
       +8*f0*f6*a12*a11+4*f0*f6*a13*a10+2*f2*f5*a12*a10+2*f1*f5*a12*a11
       +2*a15*a12*f0*f5+8*f0*f5*a12^2+2*a1*a7,
     4*f0*f2*a14^2+2*f0*a14*a5+f5*a3*a11-a0*a15+40*f0*f6*a12^2
       +3*f3*f5*a12*a10+6*f1*f6*a13*a10+14*f5*f0*a13*a12+6*f1*f3*a14*a12
       +4*f3*f0*a14*a13+8*f0*f6*a14*a10-2*a0*a12+4*f3*a12*a4+28*f0*f6*a12*a15
       +4*f2*f6*a10*a15+4*f1*f6*a11*a15+4*f5*f0*a13*a15+4*f1*f4*a14*a11
       +f3^2*a14*a10+2*a1*a8+16*f1*f5*a12^2+4*f2*a12*a5+4*f4*f0*a13^2
       +4*f0*f6*a15^2+2*f4*a10*a5+2*f3*f6*a10*a11+16*f2*f6*a10*a12
       +8*f1*f6*a11*a12+f1^2*a14^2+4*f1*f5*a12*a15+f1*f5*a14*a10
       +4*f2*f4*a12^2+4*f1*a14*a4+2*a12*a11*f3*f4+4*f2*f5*a12*a11
       -2*a10*a13*f3*f4-2*a13*a12*f2*f3+2*a14*a11*f2*f3,
     -a0*a13-4*f6*a11*a3-f5*a3*a15-5*f5*a3*a12-2*f4*a13*a3-f3*a14*a3
       +f1*a14*a5-4*f6*f4*a10*a11-2*f6*f3*a10*a15-10*f6*f3*a10*a12
       -4*f2*f6*a13*a10-2*f1*f6*a12*a15-6*f1*f6*a12^2+f5^2*a10*a11
       -f3*f5*a13*a10-2*f5*f2*a12^2-f1*f5*a14*a11+2*a1*a9,
     -a5*a14-f2*a14^2-f3*a14*a13-f4*a13^2-3*f5*a13*a12-f5*a13*a15
       -f6*a14*a10-6*f6*a12*a15-8*f6*a12^2-f6*a15^2+a9^2,
     a9*a8-a4*a14-f3*a14*a12-f4*a14*a11-f5*a12*a15-4*f5*a12^2-f6*a11*a15
       -2*f6*a11*a12-f6*a13*a10,
     2*a9*a7-a5*a15-2*a5*a12+f1*a14*a13+2*f2*a14*a12+f3*a14*a11-f5*a13*a10
       -2*f6*a15*a10-6*f6*a10*a12,
     a6*a9-a4*a15-a4*a12+f2*a14*a11+2*f3*a14*a10+f4*a12*a11+f1*a14*a12
       +f5*a12*a10,
     a8^2-a5*a12-f0*a14^2-f4*a12^2-f5*a12*a11-f6*a15*a10-4*f6*a10*a12,
     a7*a8-a4*a12-f0*a14*a13-f1*a14*a12-f5*a12*a10-f6*a10*a11, 
     2*a6*a8-a3*a15-2*a3*a12+f5*a10*a11+2*f4*a12*a10+f3*a10*a13-f1*a14*a11
       -2*f0*a15*a14-6*f0*a14*a12,
     a7^2-a5*a10-f0*a15*a14-4*f0*a14*a12-f1*a14*a11-f2*a10*a14-f6*a10^2,
     a6*a7-a4*a10-f3*a10*a12-f2*a13*a10-f1*a12*a15-4*f1*a12^2-f0*a15*a13
       -2*f0*a13*a12-f0*a11*a14,
     -a3*a10-f4*a10^2-f3*a11*a10-f2*a11^2-3*f1*a11*a12-f1*a15*a11
       -f0*a14*a10-6*f0*a15*a12-8*f0*a12^2-f0*a15^2+a6^2,
     -f1*a9*a3+a14*a8*f1^2+4*f1*a8*a4+2*f3*a3*a7+a3*a1-f3*a2*a10
       +4*f0*a8*a5-a6*a0+2*f2*a8*a3-2*f0*f5*a10*a9+3*f1*f5*a10*a8
       +2*f1*f6*a11*a6+12*f0*f5*a12*a7+12*f0*f6*a12*a6+4*a12*a8*f0*f4
       +2*a12*a8*f1*f3+2*a12*a7*f1*f4+2*a12*a6*f1*f5+4*a14*a8*f0*f2
       +4*f0*f3*a14*a7+4*f0*f4*a14*a6+4*f0*f5*a7*a15+4*f0*f6*a6*a15,
     -a7*a0+2*f0*a9*a5+f1*a8*a5+a2*a3,
     f5*a10*a2+a2*a4+a14*a8*f2^2-a0*a8+f6*a6*a3-f2*a9*a4-f2*f4*a11*a9
       +a11*a8*f1*f6-a11*a8*f2*f5+4*f2*f4*a12*a8+4*a12*a7*f2*f5
       -4*a12*a7*f1*f6+3*f2*f6*a12*a6+f0*f5*a12*a9-f0*f3*a14*a9
       -a14*a8*f1*f3+a14*a7*f2*f3-a14*a7*f1*f4-f1*f5*a14*a6+f2*f4*a8*a15
       +a7*f2*f5*a15-a7*f1*f6*a15+f2*f6*a6*a15,
     -f3^2*a14*a7-2*a10*a7*f5^2+4*f6*a7*a3+a2*a5+4*f1*f6*a11*a9-a0*a9
       +f3*a9*a4+3*f5*a3*a8+2*f4*a7*a5+4*f0*f5*a13*a9-2*f5*f6*a10*a6
       +4*a10*a7*f4*f6+4*f3*f6*a10*a8+4*f2*f6*a10*a9+12*f0*f6*a12*a9
       -f3*f6*a12*a6+4*a12*a8*f2*f5+4*a12*a9*f1*f5+4*a12*a7*f2*f6
       +2*a12*a7*f3*f5-a12*a8*f3*f4-f3*f5*a13*a6+2*f1*f5*a14*a7
       -a14*a6*f3*f4-a14*a8*f2*f3+2*a14*a6*f1*f6+4*f0*f6*a9*a15-f3*f6*a6*a15, 
     -a0*a8+2*f6*a6*a3+f5*a3*a7+a5*a1,
     f0*a9*a5+a1*a4-f4*f2*a13*a6+a10*a7*f4^2+f1*a14*a1-f4*a6*a4
       +f6*f1*a12*a6-a7*a0+a13*a7*f0*f5-a13*a7*f1*f4-f6*f3*a10*a6
       -a10*a7*f3*f5+a10*a8*f3*f4-a10*a8*f2*f5-f5*f1*a10*a9
       +4*f2*f4*a12*a7+4*a12*a8*f1*f4-4*f0*f5*a12*a8+3*f4*f0*a12*a9
       +f2*f4*a7*a15+a8*f1*f4*a15-f0*f5*a8*a15+f4*f0*a9*a15,
     -a9*a5+f3*a14*a8+2*f4*a14*a7+2*f5*a14*a6+2*f6*a13*a6+f5*a8*a12+a2*a14,
     -2*a5*a8-f1*a14*a9-2*f2*a14*a8-f3*a14*a7+f5*a7*a12+2*f6*a12*a6+a2*a13,
     -a5*a7+2*f0*a14*a9+f1*a14*a8+a2*a12,
     -a3*a7+2*f0*a12*a9+f1*a12*a8+a2*a10,
     -2*a8*a3-f1*a12*a9-2*f2*a12*a8-f3*a12*a7+f5*a10*a7+2*f6*a10*a6+a2*a11,
     -2*a5*a7-f1*a13*a9-2*f2*a14*a7-2*f2*a12*a9-f3*a14*a6-3*f3*a8*a12
       -4*f4*a12*a7-3*f5*a12*a6-f5*a10*a8-2*f6*a11*a6+a2*a15+2*a2*a12,
     -a3*a6+f3*a10*a7+2*f2*a10*a8+2*f1*a10*a9+2*f0*a11*a9+f1*a12*a7+a1*a10,
     -2*a3*a7-f5*a10*a6-2*f4*a10*a7-f3*a10*a8+f1*a12*a8+2*f0*a12*a9+a1*a11,
     -a8*a3+2*f6*a10*a6+f5*a10*a7+a1*a12,
     -a5*a8+2*f6*a12*a6+f5*a7*a12+a1*a14,
     -2*a5*a7-f5*a12*a6-2*f4*a12*a7-f3*a8*a12+f1*a14*a8+2*f0*a14*a9+a1*a13,
     -2*a8*a3-f5*a11*a6-2*f4*a8*a10-2*f4*a12*a6-f3*a10*a9-3*f3*a12*a7
       -4*f2*a12*a8-3*f1*a12*a9-f1*a14*a7-2*f0*a13*a9+a1*a15+2*a1*a12,
     -a9*a4+f2*a14*a8+f3*a14*a7+f4*a14*a6+f4*a12*a8+f5*a13*a6+f6*a6*a15
       +3*f6*a12*a6+a5*a8,
     -a4*a8-f0*a14*a9-f1*a14*a8+f4*a12*a7+f5*a12*a6+f6*a11*a6+a5*a7,
     -a4*a7-f0*a13*a9-f1*a14*a7-f1*a12*a9-f2*a12*a8-f3*a12*a7+f6*a10*a6+a6*a5,
     -a4*a6+f4*a10*a7+f3*a10*a8+f2*a10*a9+f2*a7*a12+f1*a11*a9+f0*a15*a9
       +3*f0*a12*a9+a3*a7,
     -a4*a7-f6*a10*a6-f5*a10*a7+f2*a12*a8+f1*a12*a9+f0*a13*a9+a8*a3,
     -a4*a8-f6*a11*a6-f5*a10*a8-f5*a12*a6-f4*a12*a7-f3*a8*a12+f0*a14*a9+a9*a3,
     -4*a7*a12-a7*a15+a8*a11+a6*a13,
     -4*a8*a12-a8*a15+a7*a13+a9*a11,
     -a8*a13+a7*a14+a9*a12,
     -a7*a13+a6*a14+a8*a12,
     -a8*a11+a9*a10+a7*a12,
     -a7*a11+a8*a10+a6*a12];
  return eqns;
end intrinsic;

intrinsic JacEquations(J::JacHyp) -> SeqEnum
{ Return the 72 quadrics defining the model of J in P^15.}
  C := Curve(J);
  require Genus(C) eq 2: "J must be the Jacobian of a genus 2 curve.";
  f, h := HyperellipticPolynomials(C);
  require h eq 0: "The curve of J must be of the form y^2 = f(x).";
  return JacEquations(f);
end intrinsic;

intrinsic JPttoCoords(pt::JacHypPt) -> SeqEnum
{ Given a point on the genus 2 Jacobian J, return the sequence of coordinates
  of its image on the model of J in P^15.}
  J := Parent(pt);
  C := Curve(J);
  require Genus(C) eq 2: "pt must be on the Jacobian of a genus 2 curve.";
  R := BaseField(C);
  f, h := HyperellipticPolynomials(C);
  require h eq 0: "The curve of pt must be of the form y^2 = f(x).";
  f2,f3,f4,f5,f6 := Explode([Coefficient(f, i) : i in [2..6]]);
  a := pt[1]; b := pt[2]; d := pt[3];
  if Degree(a) eq 2 then
    al1 := -Coefficient(a, 1); al2 := Coefficient(a, 0);
    b1 := Coefficient(b, 1); b2 := Coefficient(b, 0);
    a15 := al1^2 - 4*al2;
    a14 := 1;
    a13 := al1;
    a12 := al2;
    a11 := al1*al2;
    a10 := al2^2;
    a9 := b1;
    a8 := -b2;
    a7 := -(al2*b1 + al1*b2);
    a6 := al1*a7 + al2*b2;
    c := al1^2 - al2;
    a5 := b1^2 - (f6*c^2 + f5*al1*c + f4*al1^2 + f3*al1 + f2);
    a4 := -(b1*b2 + f6*al1*al2*c + f5*al1^2*al2 + f4*al1*al2 + f3*al2);
    a3 := al2*a5;
    a2 := a5*a9 - f3*a8 - 2*f4*a7 - 2*f5*a6 - 2*f6*a6*al1 - f5*a8*al2;
    a1 := a5*a8 - 2*f6*a6*al2 - f5*a7*al2;
    a0 := a5^2;
  elif Degree(a) eq 1 then
    s := Coefficient(b, 3);
    assert s^2 eq f6;
    u := -Coefficient(a, 0);
    v := Evaluate(b, u);
    a15 := 1; a14 := 0; a13 := 0; a12 := 0;
    a11 := u; a10 := u^2; a9 := s; a8 := s*u;
    a7 := s*u^2; a6 := s*u^3 - v; a5 := 0; a4 := s*a6;
    t := 2*s*a6 + f5*u^2;
    a3 := t*u; a2 := s*a3; 
    a1 := a7*(4*f6*u^3 + 3*f5*u^2 + 2*f4*u + f3) - u*v*(4*f6*u + f5);
    a0 := t^2;
  elif d eq 2 then // and Degree(a) eq 0
    s := Coefficient(b, 3);
    assert s ne 0 and s^2 eq f6;
    a15 := 0; a14 := 0; a13 := 0; a12 := 0;
    a11 := 0; a10 := 1; a9 := 0; a8 := 0;
    a7 := s; a6 := -f5/(2*s); a5 := 0; a4 := s*a6;
    a3 := a6^2 - f4; a2 := s*a3; a1 := a3*a6 - s*f3; a0 := a3^2;
  else // origin
    return [R | 1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0];
  end if;
  return [R | a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15];
end intrinsic;

function NormSeq(seq)
  l := LCM([Denominator(s) : s in seq]);
  seq := [Numerator(s)*ExactQuotient(l, Denominator(s)) : s in seq];
  g := GCD(seq);
  return [ExactQuotient(s, g) : s in seq];
end function;

intrinsic JPtToCoordsModN(pt::JacHypPt, n::RngIntElt) -> SeqEnum
{ Given a point pt on a genus 2 Jacobian over Q, return its image mod n
  on the model of the Jacobian in P^15.}
  s := ChangeUniverse(NormSeq(JPttoCoords(pt)), Integers(n));
  i := 1; while not IsInvertible(s[i]) do i +:= 1; end while;
  return [a/s[i] : a in s];
end intrinsic;

intrinsic JPtIsNonSingularModP(pt::JacHypPt, p::RngIntElt : Eqns := []) -> BoolElt
{ Given a point pt on a genus 2 Jacobian over Q, check whether its image
  modulo the prime p is nonsingular. The parameter Eqns can be used to 
  specify the equations of the model of the Jacobian in P^15.}
  if IsEmpty(Eqns) then
  C := Curve(Parent(pt));
  require Genus(C) eq 2: "pt must be on the Jacobian of a genus 2 curve.";
  f, h := HyperellipticPolynomials(C);
  require h eq 0: "The curve of pt must be of the form y^2 = f(x).";
    Eqns := JacEquations(PolynomialRing(GF(p))!f);
  end if;
  coords := ChangeUniverse(JPtToCoordsModN(pt, p), GF(p));
  i := 1;
  while coords[i] eq 0 do i +:= 1; end while;
  // affine patch given by ith coordinate = 1
  jmat := Matrix([[Evaluate(Derivative(e, j), coords) : j in [1..16] | j ne i]
                    : e in Eqns]);
  return Rank(jmat) eq 13;
end intrinsic;

/**************************************************************
 * groupinfo.m
 *
 * construct image of C and J(Q) in J mod powers of p
 *
 * M. Stoll, 2006-03-05, 2007-04-23 (MakeInjBad also for point)
 **************************************************************/

function ending(n)
  if n eq 1 then return "st";
  elif n eq 2 then return "nd";
  elif n eq 3 then return "rd";
  else return "th";
  end if;
end function;

function MakeInj(J, p, deg3)
// Construct the injection C(F_p) --> J(F_p) --> G
// given by P |--> [P + M - D], M = polar divisor of x, D = point of degree 3;
// G is an abstract abelian group isomorphic with J(F_p)
// deg3 = <b, a, c> or pt
  C := Curve(J);
  Cp := BaseChange(C, Bang(Rationals(), GF(p)));
  f := HyperellipticPolynomials(Cp);
  Jp := BaseChange(J, GF(p));
  if Type(deg3) eq PtHyp then
    ptp := Cp!deg3;
    return func<pt | (Cp!pt) - ptp>;
  end if;
  PP<xx> := PolynomialRing(GF(p));
  pol1 := PP!(deg3[2]*LCM([Denominator(c) : c in Coefficients(deg3[2])])); 
  pol2 := PP!(deg3[3]*LCM([Denominator(c) : c in Coefficients(deg3[3])]));
  polb := PP!deg3[1];
  f1 := Factorization(pol1);
  if #f1 ge 2 and Degree(pol1) eq 3 then
    r := Roots(pol1, GF(p))[1,1];
    pol := ExactQuotient(pol1, xx-r);
    ptb := -elt<Jp | pol, polb, 2>;
    ptc := -Cp![r, Evaluate(polb, r)];
    return func<pt | ptb + (ptc - (-Cp!pt)) >;
  elif Degree(pol1) lt 3 then
    // Leading coefficient of f reduces to 0
    // (we assume deg3[1] to be p-integral)
    ptb := -elt<Jp | pol1, polb, 2>;
    ptc := -Cp![1, 0, 0];
    return func<pt | ptb + (ptc - (-Cp!pt)) >;
  else
    f2 := Factorization(pol2);
    if #f2 ge 2 and Degree(pol2) eq 3 then
      r := Roots(pol2, GF(p))[1,1];
      pol := ExactQuotient(pol2, xx-r);
      ptb := elt<Jp | pol, polb, 2>;
      ptc := Cp![r, Evaluate(polb, r)];
      return func<pt | ptb + (ptc - (-Cp!pt)) >;
    elif Degree(pol2) lt 3 then
      // Leading coefficient of f reduces to 0
      // (we assume deg3[1] to be p-integral)
      ptb := elt<Jp | pol2, polb, 2>;
      ptc := Cp![1, 0, 0];
      return func<pt | ptb + (ptc - (-Cp!pt)) >;
    else
      // extend to GF(prime, 3)
      Jp3 := BaseChange(Jp, 3);
      Cp3 := BaseChange(Cp, 3);
      r := Roots(pol1, GF(p, 3))[1,1];
      PP<xx> := PolynomialRing(GF(p, 3));
      polb := PP!polb;
      pol := ExactQuotient(PP!pol1, xx-r);
      ptb := -elt<Jp3 | pol, polb, 2>;
      ptc := -Cp3![r, Evaluate(polb, r)];
      return func<pt | Jp!(ptb + (ptc - Cp3!(-pt))) >;      
    end if;
  end if;
end function;


function GroupInfo(J, bound, bas, deg3, excluded, GIlb, PrimeBound, SmoothBound)
// Construct a list of "interesting" primes and information on
// C(F_p) and J(F_p)
// An entry is [* p, imbas, imC *],
// where p is the prime,
//       imbas is the image of the given generators of J(Q) in G ~ J(F_p),
//       imC is the image of C(F_p) in G.
// Primes in excluded are not considered, GIlb is a lower bound on the primes.
  bp := Seqset(BadPrimes(J));
  den := Type(deg3) eq PtHyp select 1
          else LCM([Integers() | Denominator(c) : c in Coefficients(deg3[1])]);
  bp join:= {f[1] : f in Factorization(den)};
  bp join:= {p : p in excluded};
  res := [Parent([**]) | ];
  lb := Max(3, IsEven(GIlb) select GIlb+1 else GIlb);
  for p in Type(bound) eq RngIntElt select [lb..bound by 2] else bound do
    if IsPrime(p) and p notin bp then
      Jp := BaseChange(J, GF(p));
      Cp := BaseChange(Curve(J), Bang(Rationals(), GF(p)));
      pts := Points(Cp);
      oG := #Jp;
      if Max(PrimeDivisors(oG)) lt SmoothBound
      then
        G, m := AbelianGroup(Jp);
        vprintf GroupInfo, 1: " GroupInfo: p = %o...\n", p;
        I := Invariants(G);
        vprintf GroupInfo, 1:"   #C(F_p) = %o, Invariants(G) = %o\n", #pts, I;
        fI := Factorization(I[#I]);
        vprintf GroupInfo, 2: "   Exponent = %o\n", fI;
        imbas := [(Jp!b) @@ m : b in bas];
        orders := [Order(g) : g in imbas];
        fL := Factorization(LCM(orders));
        vprintf GroupInfo, 2: "   Exponent of image = %o\n", fL;
        inj := MakeInj(J, p, deg3);
        DL := MakeDL(G, m); // func<x | x @@ m>; // 
        imC := {DL(inj(pt)) : pt in pts};
        Gsub := sub<G | imbas>;
        imC := {Gsub | pt : pt in imC | pt in Gsub};
        imbas := ChangeUniverse(imbas, Gsub);
        e1 := &*[Integers()| a[1]^a[2] : a in fL | a[1] lt PrimeBound];
        if e1 lt LCM(orders) then
          // kick out primes larger than PrimeBound
          Gq, qmap := quo<Gsub | [e1*g : g in Generators(Gsub)]>;
          imbas := [qmap(b) : b in imbas];
          imC := {qmap(c) : c in imC};
          if #imC eq #Gq then
            vprintf GroupInfo, 1:
                    "   Relevant part does not give information ==> discard.\n";
          else
            Append(~res, [* p, imbas, imC *]);
            if IsEmpty(imC) then
              vprintf GroupInfo, 1: 
                      "GroupInfo: p = %o ==> empty intersection!\n", p;
              return res, p;
            end if;
          end if;
        else // e1 = LCM(orders)
          Append(~res, [* p, imbas, imC *]);
          // new 2004-08-12
          if IsEmpty(imC) then
            vprintf GroupInfo, 1: 
                    "GroupInfo: p = %o ==> empty intersection!\n", p;
            return res, p;
          end if;
        end if; // e1 lt LCM(orders)
      end if; // Max(PrimeDivisors(oG)) lt SmoothBound
    end if; // IsPrime(p) and p notin bp
  end for; // p
  return res, 0;
end function;

// Test if curve is regular at p (p odd for now)
function IsRegularAtp(C, p)
  // need equation to be (p-)integral
  f, h := HyperellipticPolynomials(C);
  assert h eq 0;
  assert forall{c : c in Coefficients(f) | Valuation(c, p) ge 0};
  assert IsPrime(p) and p ge 3;
  PF := PolynomialRing(GF(p));
  fp := PF!f;
  if fp eq 0 then return false; end if;
  v := Valuation(Discriminant(f), p);
  fact := Factorization(fp);
  w := &+[Degree(a[1])*(a[2]-1) : a in fact];
  if Degree(fp) le 4 then w +:= 5-Degree(fp); end if;
  if v eq w then return true; end if;
  if p gt 5 then return false; end if;
  // can have wild ramification
  if Degree(fp) le 4 and Valuation(Coefficient(f, 6), p) gt 1 then
    return false;
  end if;
  for a in fact do
    if a[2] ge 2 then
      la := Parent(f)!ChangeUniverse(Coefficients(a[1]), Integers());
      r := f mod la;
      if r eq 0 or Min([Valuation(c, p) : c in Coefficients(r)]) ge 2 then
        return false;
      end if;
    end if;
  end for;
  return true;
end function;

// Arithmetic in Pic^0(C/F_p) for C as above and of genus 2
// Elements are represented as triples <a, b, d> as usual, such that
// * a divides f - b^2
// * deg(a) le d le 2
// * deg(b) le 3; if deg(a) = d then deg(b) lt d
// * if z is a multiple root of f,
//   then (x-z)|a implies a = (x-z)^2 and b = c(x-z) with c /= (f(x)/(x-z)^2)(z)
// * zero is <1,0,0>

function Dres(f, pt)
  // reduce a divisor
  a := pt[1]; b := pt[2]; d := pt[3];
  a *:= 1/LeadingCoefficient(a);
  if pt[3] le 3 then return <a, b, d>; end if;
  a1 := ExactQuotient(f - b^2, a);
  a1 *:= 1/LeadingCoefficient(a1);
  d1 := Degree(b) le 3 select 6 - d else d - 2;
  if Degree(a1) eq d1 then
    b1 := (-b) mod a1;
    return Dres(f, <a1, b1, d1>);
  else
    // contributions at infinity
    bl := Parent(b)![Coefficient(b, i) : i in [0..Degree(a1)+1]];
    b1 := -((b-bl) + (bl mod a1));
    return Dres(f, <a1, b1, d1>);
  end if;
end function;


// Copied from old version of jacobian.m:

function Dcomp(a1, b1, a2, b2, f)
  // special case: hit singularity in a1 and a2
  x := Parent(f).1;
  if a1 eq a2 and Degree(GCD([a1, f, Derivative(f)])) gt 0 then
    z := -Coefficient(a1, 1)/2; // singular point
    c1 := Coefficient(b1 mod a1, 1);
    c2 := Coefficient(b2 mod a2, 1);
    // pt1 = <(x-z)^2, c1*(x-z)>, pt2 = <(x-z)^2, c2*(x-z)>
    if c1 + c2 eq 0 then
      return Parent(f)!1, Parent(f)!0;
    else
      alpha := Evaluate(ExactQuotient(f, (x-z)^2), z);
      return (x-z)^2, (alpha + c1*c2)/(c1 + c2)*(x-z);
    end if;
  end if;
  if a1 eq a2 and b1 eq b2 then
    // point doubling
    d, h1, h3 := XGCD(a1, 2*b1);
    a := (a1 div d)^2;
    b := (b1 + h3*((f - b1^2) div d)) mod a;
  else
    d0, _, h2 := XGCD(a1, a2);
    if d0 eq 1 then
      a := a1*a2; b := (b2 + h2*a2*(b1-b2)) mod a;
    else
      d, l, h3 := XGCD(d0, b1 + b2);
      a := (a1*a2) div d^2;
      b := (b2 + l*h2*(b1-b2)*(a2 div d) + h3*((f - b2^2) div d)) mod a;
    end if;
  end if;
  return a, b;
end function;    

function Dadd(f, pt1, pt2)
  // Add two points using Cantor's algorithm (Math. Comp. 48, 95-101 (1987)),
  // generalized to the case y^2 = f(x) with deg(f) even and genus = 2.
  P := Parent(f);
  x := P.1;
  a1 := pt1[1]; b1 := pt1[2]; di1 := pt1[3] - Degree(a1);
  a2 := pt2[1]; b2 := pt2[2]; di2 := pt2[3] - Degree(a2);
  fi := P!Reverse(Eltseq(f) cat [0 : i in [Degree(f)+1..6]]);
  // first split into finite and infinite parts
  if di1 gt 0 then // there is something at infty
    b1f := b1 mod a1; 
    a1i := x^di1;
    b1i := (P!Reverse(Eltseq(b1) cat [0:i in [Degree(b1)+1..3]])) mod a1i; 
  else
    b1f := b1; b1i := P!0; a1i := P!1;
  end if;
  if di2 gt 0 then
    b2f := b2 mod a2; 
    a2i := x^di2;
    b2i := (P!Reverse(Eltseq(b2) cat [0:i in [Degree(b2)+1..3]])) mod a2i; 
  else
    b2f := b2; b2i := P!0; a2i := P!1;
  end if;
  // first step: composition
  af, bf := Dcomp(a1, b1f, a2, b2f, f);
  if di1 eq 0 and di2 eq 0 then
    a := af; b := bf; d := Degree(af);
  else
    ai, bi := Dcomp(a1i, b1i, a2i, b2i, fi);
    a := af;
    bi := P!Reverse(Eltseq(bi) cat [0 : i in [Degree(bi)+1..3]]); 
    b := bf + bi - (bi mod a);
    d := Degree(af) + Degree(ai);
  end if;
  // second step: reduction
  return Dres(f, <a, b, d>);
end function;

function Dneg(f, pt)
  return <pt[1], -pt[2], pt[3]>;
end function;

function Dred(f, pt, p)
  // reduction mod p for divisors of degree <= 3
  a0 := pt[1]; b0 := pt[2]; d := pt[3];
  PZ := PolynomialRing(Integers());
  PF := PolynomialRing(GF(p));
  a := PZ!(LCM([Integers() | Denominator(c) : c in Coefficients(a0)])*a0);
  bden := LCM([Integers() | Denominator(c) : c in Coefficients(b0)]);
  b := PZ!(bden*b0);
  if IsDivisibleBy(bden, p) then
    as := Eltseq(a) cat [ 0 : i in [Degree(a)+1..d] ];
    mat := Matrix([[0 : i in [1..j]] cat as cat [0 : i in [1..3-d-j]]
                     : j in [0..3-d]]);
    matp := ChangeRing(mat, GF(p));
    V := KSpace(GF(p), 4);
    VZ := RSpace(Integers(), 4-d);
    n := Valuation(bden, p);
    while n gt 0 do
      bs := Eltseq(b) cat [ 0 : i in [Degree(b)..2] ];
      flag, sol := IsConsistent(matp, V!bs);
      if not flag then
        assert d ge 2;
        if d eq 2 then
          return <PF!1, PF!0, 0>; 
        else
          ap := PF!a;
          if Degree(ap) le d-2 then
            // problem at infinity -> move to zero
            fi := Parent(f)![Coefficient(f, 6-i) : i in [0..6]];
            ai := Parent(f)![Coefficient(a0, d-i) : i in [0..d]];
            bi := Parent(f)![Coefficient(b0, 3-i) : i in [0..3]];
            dri := Dred(fi, <ai, bi, d>, p);
            dr := dri[3];
            return Dres(PF!f, <PF![Coefficient(dri[1], dr-i) : i in [0..dr]],
                               PF![Coefficient(dri[2], 3-i) : i in [0..3]],
                               dr>);
          end if;
          ap1 := GCD(ap, Derivative(ap));
          apr := Degree(ap1) eq 1 select ExactQuotient(ap, ap1^2)
                                  else ExactQuotient(ap, ap1);
          z := -Coefficient(apr, 0);
          assert Evaluate(Derivative(PF!f), z) ne 0;
          v := Evaluate(ExactQuotient(PF!f, (PF.1-z)^2), z);
          ypol := PF!Evaluate(Resultant(P2.2-Evaluate(b0, P2.1),
                                        Evaluate(a0, P2.1),
                                        P2.1),
                             [0, PZ.1])
                  where P2 := PolynomialRing(Rationals(), 2);
          yval := -Coefficient(ExactQuotient(ypol, PF.1^2-v), 0);
          return <apr, PF!yval, 1>;
        end if;
      end if;
      b -:= PZ!Eltseq((VZ!sol)*mat);
      b := ExactQuotient(b, p);
      bden := ExactQuotient(bden, p);
      n -:= 1;
    end while;
  end if;
  return Dres(PF!f, <PF!a, (GF(p)!bden)^-1*PF!b, d>);
end function;

function Dmul(f, n, pt)
  P := Parent(f);
  if n eq 0 then return <P!1, P!0, 0>; end if;
  if n lt 0 then n := -n; pt := Dneg(f, pt); end if;
  r := <P!1, P!0, 0>;
  // n*pt + r is invariant
  while n gt 1 do
    if IsOdd(n) then r := Dadd(f, r, pt); end if;
    n div:= 2; 
    // pt +:= pt;
    pt := Dadd(f, pt, pt);
  end while;
  return Dadd(f, pt, r);
end function;

function MakeInjBad(f, deg3, p)
  PF := PolynomialRing(GF(p));
  fp := PF!f;
  divpt := func<pt | pt[3] eq 0 select <PF!1, pt[2]/pt[1]^3*PF.1^3, 1>
                      else <PF.1 - pt[1]/pt[3], PF!(pt[2]/pt[3]^3), 1>>;
  if Type(deg3) eq PtHyp then
    ptp := divpt([GF(p) | deg3[1], -deg3[2], deg3[3]]); // Cp!deg3;
    return func<pt | Dadd(fp, divpt(pt), ptp)>;
  end if;
  // deg3 = <b, a, c>
  d3r := Dred(f, <deg3[2], -deg3[1], 3>, p); // subtract deg3 !
  return func<pt | Dadd(fp, divpt(pt), d3r)>;
end function;

function Drand(f)
  P := Parent(f);
  F := CoefficientRing(P);
  x := P.1;
  if f eq 0 then
    s := Random([0..#F]);
    repeat z := Random(F); until z ne 0;
    if s eq #F then
      return <P!1, z*x^2, 2>; 
    else
      s := Random(F);
      return <(x - s)^2, z*(x-s), 2>;
    end if;
  end if;
  ok := false;
  sing := {<r[1], F!1> : r in Roots(GCD(f, Derivative(f)))};
  if Degree(f) le 4 then Include(~sing, <F!1, F!0>); end if;
  if not IsEmpty(sing) and Random([0..4]) eq 0 then
    s := Random(sing);
    if s[2] eq 0 then
      v := Coefficient(f, 4);
    else
      v := Evaluate(ExactQuotient(f, (x-s[1])^2), s[1]);
    end if;
    z := Random(F);
    while z^2 eq v do
      z := Random(F);
    end while;
    if s[2] eq 0 then
      return <P!1, z*x^2, 2>;
    else
      return <(x - s[1])^2, z*(x - s[1]), 2>;
    end if;
  end if;
  bad := GCD(f, Derivative(f));
  while not ok do
    // take a random polynomial of degree 2
    repeat
      a := P![ Random(F) : i in [0..2] ];
      if a eq 0 then return <P!1, P!0, 0>; end if;
      a *:= 1/LeadingCoefficient(a);
    until GCD(a, bad) eq 1 and (Degree(f) ge 5 or Degree(a) eq 2);
    // for each factor, find a point on the curve of corresponding
    //  degree (if possible) and put them together
    ok := true;
    case Degree(a):
      when 2:
        ra := Roots(a);
        if IsEmpty(ra) then
          // a is irreducible
          FE<w> := ext< F | a >;
          PE<y> := PolynomialRing(FE);
          rs := Roots(y^2 - Evaluate(f,w));
          if IsEmpty(rs) then
            ok := false;
          else
            return <a, P!Eltseq(Random(rs)[1]), 2>;
          end if;
        else
          // a splits into two linear factors
          PE<y> := PolynomialRing(F);
          x1 := ra[1][1];
          rs1 := Roots(y^2 - Evaluate(f,x1));
          if IsEmpty(rs1) then ok := false;
          else
            y1 := Random(rs1)[1];
            if #ra eq 1 then
              // a is the square of a linear polynomial
              if 2*y1 eq 0 then ok := false;
              else
                df1 := Evaluate(Derivative(f),x1);
                return <a, y1+(df1/(2*y1))*(x-x1), 2>;
              end if;
            else
              // a is the product of two distinct linear factors
              x2 := ra[2][1];
              rs2 := Roots(y^2 - Evaluate(f,x2));
              if IsEmpty(rs2) then
                ok := false;
              else
                y2 := Random(rs2)[1];
                return <a, ((y1-y2)*x + (x1*y2-x2*y1))/(x1-x2), 2>;
              end if;
            end if;
          end if;
        end if;
      when 1:
        // a is linear -- must use one point at infinity
        PE<y> := PolynomialRing(F);
        x1 := -Coefficient(a,0);
        rs1 := Roots(y^2 - Evaluate(f,x1));
        if IsEmpty(rs1) then ok := false;
        else
          flag, rt := IsSquare(Coefficient(f, 6));
         if not flag then
            ok := false;
          else
            y1 := Random(rs1)[1];
            y2 := Random({rt, -rt}); // y-coordinate of point at infty
            return <a, y1+y2*(x^3-x1^3), 2>;
          end if;
        end if;
      when 0:
        // a is constant -- must use twice a point at infinity
        PE<y> := PolynomialRing(F);
        flag, rt := IsSquare(Coefficient(f, 6));
        if not flag then
          ok := false;
        else
          yinf := Random({rt, -rt}); // y-coordinate of point at infty
          if yinf eq 0 then
            return <P!1, P!0, 0>;
          end if;
          df := Coefficient(f,5)/(2*yinf);
          return <P!1, yinf*x^3 + df*x^2, 2>;
        end if;
    end case;
  end while;
end function;

function BadOrder(f, p)
  PF := PolynomialRing(GF(p));
  fp := PF!f;
  if fp eq 0 then return p^2; end if; // purely additive
  fact := Factorization(fp);
  mults := {* a[2]^^Degree(a[1]) : a in fact *};
  if Degree(fp) lt 6 then mults join:= {* (6-Degree(fp))^^1 *}; end if;
  case mults:
    when {* 1, 1, 1, 1, 1, 1 *}:
      error "BadOrder: p =", p, "is a good prime for f =", f;
    when {* 1, 1, 1, 1, 2 *}:
      // C mod p has a node
      if Degree(fp) le 4 then
        a := Coefficient(fp, 4);
        E := HyperellipticCurveOfGenus(1, fp);
      else
        z := -Coefficient(Rep([a[1] : a in fact | a[2] eq 2]), 0);
        fq := ExactQuotient(fp, (PF.1-z)^2);
        a := Evaluate(fq, z);
        E := HyperellipticCurveOfGenus(1, fq);
      end if;
      return (#E)*(IsSquare(a) select p-1 else p+1);
    when {* 1, 1, 1, 3 *}:
        // a cusp
        if Degree(fp) eq 3 then
          qu := PF!1;
        else
          z := -Coefficient(Rep([a[1] : a in fact | a[2] eq 3]), 0);
          qu := (PF.1 - z)^2;
        end if;
        return (#HyperellipticCurveOfGenus(1, ExactQuotient(fp, qu)))*p;
    when {* 1, 1, 2, 2 *}:
      // two nodes
      // find action of Frob on H_1(bouquet of two circles)
      gcd := &*[a[1] : a in fact | a[2] eq 2];
      disc := Discriminant(gcd);
      if IsSquare(disc) then
        // two nodes individually defined / F_p
        rs := [Evaluate(ExactQuotient(fp, (PF.1-z)^2), z) where z := r[1]
                : r in Roots(gcd)];
        o1 := IsSquare(rs[1]) select p-1 else p+1;
        o2 := #rs eq 1 select
               (IsSquare(Coefficient(fp, 4)) select p-1 else p+1)
              else (IsSquare(rs[2]) select p-1 else p+1);
        return o1*o2;
      else
        // nodes conjugate, defined over F_{p^2}
        if IsSquare(Evaluate(ExactQuotient(fp, gcd^2), 
                    Rep(Roots(gcd, GF(p,2)))[1]))
        then
          return p^2 - 1;
        else
          return p^2 + 1;
        end if;
      end if;
    when {* 2, 2, 2 *}:
      // three nodes (which may be conjugate to some degree),
      s := IsSquare(LeadingCoefficient(fp)); // decides on c_p
      degs := {* Degree(a[1]) : a in fact | a[2] eq 2 *};
      if &+degs lt 3 then degs join:= {* 1 *}; end if;
      case degs:
        when {* 1, 1, 1 *}:
          return s select 3*(p-1)^2 else (p+1)^2;
        when {* 1, 2 *}:
          return s select 3*(p^2-1) else (p^2-1);
        when {* 3 *}:
          return s select 3*(p^2+p+1) else (p^2-p+1);
        else
          error "Error in BadOrder, case 3 nodes.\n";
      end case;
    when {* 1, 2, 3 *}: // node + cusp
      if Degree(fp) eq 4 then
        s := IsSquare(Coefficient(fp, 4));
      else
        z := -Coefficient(Rep([a[1] : a in fact | a[2] eq 2]), 0);
        s := IsSquare(Evaluate(ExactQuotient(fp, (PF.1-z)^2), z));
      end if;
      return s select p*(p-1) else p*(p+1);
    when {* 1, 1, 4 *}: // tacnode
      if Degree(fp) eq 2 then
        s := IsSquare(Coefficient(fp, 2));
      else
        z := -Coefficient(Rep([a[1] : a in fact | a[2] eq 4]), 0);
        s := IsSquare(Evaluate(ExactQuotient(fp, (PF.1-z)^4), z));
      end if;
      return s select p*(p-1) else p*(p+1);
    when {* 3, 3 *}: // two cusps
      return p^2;
    when {* 2, 4 *}: // node & tacnode
      s := IsSquare(LeadingCoefficient(fp));
      return s select 3*p*(p-1) else p*(p+1);
    when {* 1, 5 *}: // (2,5)-cusp
      return p^2;
    when {* 6 *}:
      // y^2 = l^6
      s := IsSquare(LeadingCoefficient(fp));
      return s select 3*p^2 else p^2;
    else
      error "BadOrder: Case ",mults,"not yet implemented.\n";
  end case;
end function;

function MakeGroup(f, p)
  PF := PolynomialRing(GF(p));
  fp := PF!f;
  return <func< | Drand(fp)>,                  // random point
          <PF!1, PF!0, 0>,                     // zero
          func<pt1, pt2 | Dadd(fp, pt1, pt2)>, // addition
          func<n, pt | Dmul(fp, n, pt)>,       // scalar multplication
          BadOrder(f, p)>;                     // group order
end function;

///////////////////////
//                   //
//  Group structure  //
//                   //
///////////////////////

// Find the group structure of the rational points on the Jacobian
// over a finite field.

function MypSubgroup(Gr, p)
// Computes the p-subgroup of the abelian group Gr = <rand, zero, add, mul, ord>
// where rand() gives a random element of Gr, add(g,h) adds g and h in Gr
// and mul(n, g) computes n*g in Gr and ord = #Gr (supposed to be known)
    rand := Gr[1];
    zero := Gr[2];
    add := Gr[3];
    mul := Gr[4];
    order := Gr[5];
    e := Valuation(order, p);
    if e eq 0 then
      G := AbelianGroup([]);
      return G, func<g | zero>;
    end if;
    d := order div p^e;
    // Find points in the p-subgroup
    curr_size := 0; // logarithmic
    end_size := e;
    // generators found so far, with their relations
    gens := [];
    rels := [];
    // points lists all the points in the current subgroup,
    // with base representations listed in reps
    points := [ Gr[2] ];
    reps := [ [] ];
    while curr_size lt end_size do
      // find a random point in the p-subgroup
      rpt := rand();
      new_pt := mul(d, rpt);
      // check if already in current subgroup
      if new_pt notin points then
        q := mul(p, new_pt);
        f := 1;
        pos := Position(points, q);
        while pos eq 0 do
          q := mul(p, q);
          pos := Position(points, q); 
          f +:= 1;
          assert f + curr_size le end_size;
        end while;
        // now p^f*new_pt is in the known subgroup
        // treat the special case that the first try already generates
        if q eq zero and IsEmpty(gens) and f eq e then
          G<[P]> := AbelianGroup([p^e]);
          return G, func< g | mul(s[1], new_pt)  where s := Eltseq(g) >;
        end if;
        // get its base rep
        rep := reps[pos];
        // enlarge gens
        Append(~gens, new_pt);
        rels := [ r cat [0] : r in rels ] cat [ rep cat [-p^f] ];
        // enlarge current subgroup
        curr_size +:= f;
        if curr_size eq end_size then break; end if;
        new_points := [];
        new_reps := [];
        pta := zero;
        for i := 0 to p^f-1 do
          new_points cat:= [ add(z, pta) : z in points ];
          new_reps cat:= [ r cat [i] : r in reps ];
          pta := add(pta, new_pt);
        end for;
        points := new_points;
        reps := new_reps;
      end if;
    end while;
    // Now construct the group
    GF<[t]> := FreeAbelianGroup(#gens);
    G<[P]>, proj
       := quo< GF | [ &+[ r[i]*t[i] : i in [1..#r] ] : r in rels ] >;
    new_gens := [];
    function linc(cofs, elts)
      res := zero;
      for i := 1 to #cofs do
        res := add(res, mul(cofs[i], elts[i]));
      end for;
      return res;
    end function;
    for i := 1 to #Generators(G) do
      s := Eltseq(G.i @@ proj);
      Append(~new_gens, linc(s, gens));
    end for;
    return G, func< g | linc(Eltseq(g), new_gens) >;
end function; 

function MyAbelianGroup(Gr)
    rand := Gr[1];
    zero := Gr[2];
    add := Gr[3];
    mul := Gr[4];
    order := Gr[5];
    function linc(cofs, elts)
      res := zero;
      for i := 1 to #cofs do
        res := add(res, mul(cofs[i], elts[i]));
      end for;
      return res;
    end function;
    fo := Factorization(order);
    ed := [];
    gL := [];
    for tr in fo do
      Gp, m := MypSubgroup(Gr, tr[1]);
      Lp := [ m(Gp.i) : i in [1..#Generators(Gp)] ];
      inv := Invariants(Gp);
      error if #inv gt 1 and &or[ inv[i] gt inv[i+1] : i in [1..#inv-1] ],
            "Group returned by pSubgroup has unusual invariant ordering:",inv;
      d := #inv-#ed;
      if d gt 0 then
        ed := inv[[1..d]] cat [ Lcm(ed[i], inv[i+d]) : i in [1..#ed] ];
        gL := Lp[[1..d]] cat [ add(gL[i], Lp[i+d]) : i in [1..#gL] ];
      else
        ed := ed[[1..-d]] cat [ Lcm(ed[i-d], inv[i]) : i in [1..#inv] ];
        gL := gL[[1..-d]] cat [ add(gL[i-d], Lp[i]) : i in [1..#Lp] ];
      end if;
    end for;
    G<[P]> := AbelianGroup(ed);
    return G, func< g | linc(Eltseq(g), gL) >;
end function;


function BadGroupInfo(C, bas, deg3, p)
  // deg3 = <b, a, c>
  f := HyperellipticPolynomials(C);
  G := MakeGroup(f, p);
  A, mA := MyAbelianGroup(G);
  DL := MakeDL(A, mA, G[4], func<x,y | G[3](x, G[4](-1,y))>);
  imbas := [DL(Dred(f, b, p)) : b in bas];
  fp := PolynomialRing(GF(p))!f;
  bad := GCD(fp, Derivative(fp));
  ptsC := &join{flag select {<a, r, GF(p)!1>, <a, -r, GF(p)!1>} else {}
                where flag, r := IsSquare(Evaluate(fp, a))
                 : a in GF(p)
                 | Evaluate(bad, a) ne 0};
  flag, r := IsSquare(Coefficient(fp, 6));
  if Degree(fp) ge 5 and flag then
    ptsC join:= {<GF(p)!1, r, GF(p)!0>, <GF(p)!1, -r, GF(p)!0>};
  end if;
  inj := MakeInjBad(f, deg3, p);
  imC := {DL(inj(pt)) : pt in ptsC};
  As := sub<A | imbas>;
  imC := {As!pt : pt in imC | pt in As};
  ChangeUniverse(~imbas, As); 
  return [* p, imbas, imC *];
end function;

function ToDualKummer(f, a, b)
  // maps a degree 3 divisor given by polynomials a and b to a point
  // on the dual Kummer surface
  P := Parent(f);
  R := CoefficientRing(P);
  P4<[x]> := PolynomialRing(R, 4);
  al := &+[x[i]*Coefficient(a,i-1) : i in [1..4]];
  bl := &+[x[i]*Coefficient(b,i-1) : i in [1..4]];
  c := ExactQuotient(f - b^2, a);
  cl := &+[x[i]*Coefficient(c,i-1) : i in [1..4]];
  s1 := -x[2]^2 + x[1]*x[3];
  s2 := -x[2]*x[3] + x[1]*x[4];
  s3 := -x[3]^2 + x[2]*x[4];
  s4 := &+[Coefficient(f,i)*x[(i div 2)+1]*x[((i+1) div 2)+1] : i in [0..6]];
  mons := MonomialsOfDegree(P4, 2);
  q := al*cl + bl^2;
  mat := Matrix([[MonomialCoefficient(pol, m) : m in mons]
                   : pol in [q, s1, s2, s3, s4]]);
  ker := Kernel(mat);
  assert Dimension(ker) ge 1;
  assert Basis(ker)[1,1] ne 0;
  res := Eltseq(Basis(ker)[1]);
  res := [-res[i]/res[1] : i in [2..5]];
  f0,f1,f2,f3,f4,f5,f6 := Explode([Coefficient(f,i) : i in [0..6]]);
  eqn := Determinant(Matrix([[2*f0*x[4], f1*x[4], x[1], x[2]],
                     [f1*x[4], 2*(f2*x[4]-x[1]), f3*x[4]-x[2], x[3]],
                     [x[1], f3*x[4]-x[2], 2*(f4*x[4]-x[3]), f5*x[4]],
                     [x[2], x[3], f5*x[4], 2*f6*x[4]]]));
  assert Evaluate(eqn, res) eq 0;
  return res;
end function;

function TDK(f, deg3, lc, bas)
  // here deg3 = <deg3a, deg3b> or point,
  // lc = sequence of coeffs for bas = sequence
  //      of points on Jac(y^2 = f(x))
  ptJ := &+[lc[i]*bas[i] : i in [1..#bas]];
  if Type(deg3) eq PtHyp then
    pt := Dadd(f, baspt, <ptJ[1], ptJ[2], ptJ[3]>)
          where baspt := deg3[3] eq 0 
                         select deg3[2] eq 0 
                                select <P!1, P!0, 0> 
                                else <P!1, deg3[2]/deg3[1]^3*x^3, 1>
                         else <x - deg3[1]/deg3[3], P!deg3[2]/deg3[3]^3, 1>
          where x := P.1
          where P := Parent(f);
  else
    pt := Dadd(f, <deg3[1], deg3[2], 3>, <ptJ[1], ptJ[2], ptJ[3]>);
  end if;
  function norm(seq)
    l := LCM([Denominator(a) : a in seq]);
    seq := [Numerator(a)*ExactQuotient(l, Denominator(a)) : a in seq];
    g := GCD(seq);
    return [ExactQuotient(a, g) : a in seq];
  end function;
  if pt[3] le 1 then
    if Degree(pt[1]) eq 1 then
      return norm([1, a, a^2, 0]) where a := -Coefficient(pt[1], 0);
    else // infty
      return [CoefficientRing(Parent(pt[1])) | 1,0,0,0];
    end if;
  else
    return norm(ToDualKummer(f, pt[1], pt[2]));
  end if;
end function;

function DistanceFromCurve(pt, p)
  return (Valuation(pt[4], p) + 1) div 2;
end function;


// Compute higher kernels of reduction. Use Kummer Surface and p-adic
// arithmetic.

function GetSubgroup(A, test)
  // A = free abelian group.
  // finds subgroup of A (assumed of finite index) on which test is true
  // (assuming this _is_ a subgroup!)
  bas := OrderedGenerators(A);
  gens := [];
  As := { A!0 }; // known part of quotient group
  for b in bas do
    // find smallest multiple of b such that As + b meets the subgroup
    j := 1; 
    bb := b;
    repeat
      flag := exists(a){ a : a in As | test(bb+a) };
      if not flag then
        j +:= 1;
        bb +:= b;
      end if;
    until flag;
    // note new kernel generator
    Append(~gens, bb + a);
    // extend As to get set of representatives of the image of the
    // group generated by the first few generators of A in the quotient
    As := { a + i*b : i in [0..j-1], a in As };
  end for;
  return sub< A | gens >;
end function;


function KernelOfReduction(bas, p)
  // compute the kernel of reduction mod p on the Mordell-Weil group
  // (or rather, the subgroup generated by bas).
  // return MW, K where
  // + MW is a free abelian group on #bas generators,
  // + K is a subgroup of MW such that
  //   SUM n_i*bas[i] is in the kernel of reduction <==> SUM n_i*MW.i in K
  vprintf DeepInfo, 1: "KernelOfReduction mod p = %o...\n", p;
  MW := FreeAbelianGroup(#bas);
  J := Universe(bas);
  C := Curve(J);
  f, h := HyperellipticPolynomials(C);
  assert h eq 0;
  if not IsDivisibleBy(Integers()!Discriminant(C), p) then
    // use reduction mod p
    vprintf DeepInfo, 2: "  p = %o is a good prime, use Jacobian mod p.\n", p;
    Jp := BaseChange(J, GF(p));
    basp := ChangeUniverse(bas, Jp);
    Gp, mp := AbelianGroup(Jp);
    K := Kernel(hom< MW -> Gp | [b @@ mp : b in basp] >);
    return MW, K;
  end if;
  // here, p is bad.
  if IsOdd(p) and IsRegularAtp(C, p) then
    // use reduction mod p again (from bad-reduction.magma)
    vprintf DeepInfo, 2: "  Model is regular at p = %o, use group mod p.\n", p;
    G := MakeGroup(f, p);
    Gp, mp := MyAbelianGroup(G);
    DL := MakeDL(Gp, mp, G[4], func<x,y | G[3](x, G[4](-1,y))>);
    basp := [DL(Dred(f, b, p)) : b in bas];
    K := Kernel(hom< MW -> Gp | basp >);
    return MW, K;
  end if;
  // now p is "very bad"; first find connected component: 
  // subgroup that maps into regular part
  vprintf DeepInfo, 2: "  Model is not regular or p = 2. Find connected component...\n"; 
  fp := PolynomialRing(GF(p))!f;
  Jpeqns := JacEquations(fp);
  // Pr15 := ProjectiveSpace(Universe(Jpeqns));
  // JpS := Scheme(Pr15, Jpeqns);
  redpt := func< ptJ | ChangeUniverse(JPtToCoordsModN(ptJ, p), GF(p)) >;
  test := func< pt | JPtIsNonSingularModP(ptJ, p : Eqns := Jpeqns)
                     where ptJ := &+[s[i]*bas[i] : i in [1..#bas]]
                     where s := Eltseq(pt) >;
  K0 := GetSubgroup(MW, test);
  bas0 := [&+[s[i]*bas[i] : i in [1..#bas]] where s := Eltseq(b)
            : b in ChangeUniverse(OrderedGenerators(K0), MW)];
     // basis of K0 as rational points on J
  vprintf DeepInfo, 2: "    Found connected component, generated by";
  vprintf DeepInfo, 2: "    %o\n", ChangeUniverse(OrderedGenerators(K0), MW);
  // now do the regular part as before (unless p = 2)
  vprintf DeepInfo, 2: "  Find kernel of reduction in connected component.\n";
  if IsOdd(p) then
    vprintf DeepInfo, 2: "    p = %o is odd: use group mod p.\n", p;
    G := MakeGroup(f, p);
    Gp, mp := MyAbelianGroup(G);
    DL := MakeDL(Gp, mp, G[4], func<x,y | G[3](x, G[4](-1,y))>);
    basp := [DL(Dred(f, b, p)) : b in bas0];
    K := Kernel(hom< K0 -> Gp | basp >);
    return MW, K;
  end if;
  // finally, if p = 2, find next level by enumeration again
  vprintf DeepInfo, 2: "  Use enumeration and test.\n";
  zero := [GF(p) | 1,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0];
  test := func< pt | redpt(ptJ) eq zero
                     where ptJ := &+[s[i]*bas0[i] : i in [1..#bas0]]
                     where s := Eltseq(pt) >;
  K := GetSubgroup(K0, test);
  return MW, K;
end function;

//----------------------------------------------------------------------
// from Nils:

// intrinsic LCInit(B::[JacHypPt])->SeqEnum
function LCInit(B)
  J := Universe(B);
  K := KummerSurface(J);
  V := [J!0];
  for j in B do
    V cat:= [j + v : v in V];
  end for;
  return [K!b : b in V];
end function;

// intrinsic LinearCombination(n::[RngIntElt],V::[SrfKumPt])->SrfKumPt
// V as given by LCInit
function LinearCombination(n, V)
  B := [V[2^(i-1)+1] :i in [1..#n]];
  for i in [1..#n] do
    V := [PseudoAddMultiple(V[j],B[i],V[j+1],n[i]) : j in [1..#V-1 by 2]];
  end for;
  assert #V eq 1;
  return V[1];
end function;

//----------------------------------------------------------------------

// Logarithms

function LogSeries(f, s2, s1, n)
  f0,f1,f2,f3,f4,f5,f6 := Explode([Coefficient(f, i) : i in [0..6]]);
  // taken from Victor Flynn's files
  log1 := s2
           + (n ge 3 select 1/3*f5*s1^3 - 2/3*f2*s2^3 else 0)
           + (n ge 5 select
              (2/5*f3*f6 - 3/5*f4*f5)*s1^5 + 2*f2*f6*s1^4*s2 + 4*f1*f6*s1^3*s2^2
               + (12*f0*f6 + f1*f5)*s1^2*s2^3 + 5*f0*f5*s1*s2^4
               + (12/5*f0*f4 - 3/5*f1*f3 + 6/5*f2^2)*s2^5
               else 0)
           + (n ge 7 select
              (-4/7*f1*f6^2 + 20/7*f2*f5*f6 - 8/7*f3*f4*f6 - 4/7*f3*f5^2
                + 10/7*f4^2*f5)*s1^7
               + (-4*f0*f6^2 + 7*f1*f5*f6 - 4*f2*f4*f6)*s1^6*s2
               + (18*f0*f5*f6 - 4*f1*f4*f6 + f1*f5^2)*s1^5*s2^2
               + (-4*f0*f4*f6 + 6*f0*f5^2 + 4*f1*f3*f6 - f1*f4*f5
                   - 4*f2^2*f6)*s1^4*s2^3
               + (16*f0*f3*f6 + 2*f0*f4*f5 - 8*f1*f2*f6)*s1^3*s2^4
               + (-24*f0*f2*f6 + 4*f0*f3*f5 - 3*f1*f2*f5)*s1^2*s2^5
               + (8*f0*f1*f6 - 14*f0*f2*f5 - f1^2*f5)*s1*s2^6
               + (-4/7*f0^2*f6 + 13/7*f0*f1*f5 - 64/7*f0*f2*f4 - 4/7*f0*f3^2
                   - 4/7*f1^2*f4 + 20/7*f1*f2*f3 - 20/7*f2^3)*s2^7
              else 0);
  log2 := s1
           + (n ge 3 select  -2/3*f4*s1^3 + 1/3*f1*s2^3 else 0)
           + (n ge 5 select
              (12/5*f2*f6 - 3/5*f3*f5 + 6/5*f4^2)*s1^5 + 5*f1*f6*s1^4*s2
               + (12*f0*f6 + f1*f5)*s1^3*s2^2 + 4*f0*f5*s1^2*s2^3
               + 2*f0*f4*s1*s2^4 + (2/5*f0*f3 - 3/5*f1*f2)*s2^5
               else 0)
           + (n ge 7 select
              (-4/7*f0*f6^2 + 13/7*f1*f5*f6 - 64/7*f2*f4*f6 - 4/7*f2*f5^2
                - 4/7*f3^2*f6 + 20/7*f3*f4*f5 - 20/7*f4^3)*s1^7
               + (8*f0*f5*f6 - 14*f1*f4*f6 - f1*f5^2)*s1^6*s2
               + (-24*f0*f4*f6 + 4*f1*f3*f6 - 3*f1*f4*f5)*s1^5*s2^2
               + (16*f0*f3*f6 - 8*f0*f4*f5 + 2*f1*f2*f6)*s1^4*s2^3
               + (-4*f0*f2*f6 + 4*f0*f3*f5 - 4*f0*f4^2 + 6*f1^2*f6
                   - f1*f2*f5)*s1^3*s2^4
               + (18*f0*f1*f6 - 4*f0*f2*f5 + f1^2*f5)*s1^2*s2^5
               + (-4*f0^2*f6 + 7*f0*f1*f5 - 4*f0*f2*f4)*s1*s2^6
               + (-4/7*f0^2*f5 + 20/7*f0*f1*f4 - 8/7*f0*f2*f3 - 4/7*f1^2*f3
                   + 10/7*f1*f2^2)*s2^7
              else 0);
  return [log1, log2];
end function;

// Find the precision (max. exponent) needed in a power series
// with Z_p coefficients to get p-adic precision prec for the
// integral, when plugging in something in p*Z_p

function precNeeded(p, prec)
  prec0 := prec;
  k := 1;
  pk := p;
  while pk lt k + prec do
    r := pk*Ceiling(prec/pk);
    if r lt k + prec then
      prec0 := r;
    end if;
    k +:= 1;
    pk *:= p;
  end while;
  return prec0;
end function;

// Compute the p-adic abelian logarithm in Q_p x Q_p of a point
// on the Jacobian in the kernel of reduction

function pAdicLogG2(ptJ, p, prec)
  // for now, ptJ is rational
  J := Parent(ptJ);
  f, h := HyperellipticPolynomials(Curve(J));
  assert h eq 0;
  K := KummerSurface(J);
  // check that ptJ is in the kernel of reduction
  ptK := K!ptJ;
  assert forall{j : j in [1..3] | Valuation(ptK[j], p) ge 2};
  // trivial case
  Qp := pAdicField(p, prec);
  bigO := O(Qp!p^prec);
  if ptJ eq J!0 then return [Qp|0, 0]; end if;
  // find local coordinates at origin
  coords := JPttoCoords(ptJ);
  assert coords[1] ne 0;
  ll1 := Qp!coords[3]/Qp!coords[1];
  ll2 := Qp!coords[2]/Qp!coords[1];
  // check if precision of series is sufficient
  pr := Min(Valuation(ll1), Valuation(ll2));
  if prec lt 9*pr then
    if p eq 3 then
      if prec le 3*pr-1 then return LogSeries(f, ll1, ll2, 1); 
      elif prec le 5*pr then return LogSeries(f, ll1, ll2, 3);
      elif prec le 7*pr then return LogSeries(f, ll1, ll2, 5);        
      elif prec le 9*pr-2 then return LogSeries(f, ll1, ll2, 7);
      end if;
    elif p eq 5 then
      if prec le 3*pr then return LogSeries(f, ll1, ll2, 1);
      elif prec le 5*pr-1 then return LogSeries(f, ll1, ll2, 3);
      elif prec le 7*pr then return LogSeries(f, ll1, ll2, 5);        
      elif prec le 9*pr then return LogSeries(f, ll1, ll2, 7);
      end if;
    elif p eq 7 then
      if prec le 3*pr then return LogSeries(f, ll1, ll2, 1);
      elif prec le 5*pr then return LogSeries(f, ll1, ll2, 3);
      elif prec le 7*pr-1 then return LogSeries(f, ll1, ll2, 5);        
      elif prec le 9*pr then return LogSeries(f, ll1, ll2, 7);
      end if;
    else
      if prec le 3*pr then return LogSeries(f, ll1, ll2, 1);
      elif prec le 5*pr then return LogSeries(f, ll1, ll2, 3);
      elif prec le 7*pr then return LogSeries(f, ll1, ll2, 5);        
      elif prec le 9*pr then return LogSeries(f, ll1, ll2, 7);
      end if;
    end if;
  end if;
  // get components
  a := ptJ[1]; 
  b := ptJ[2];
  b1 := Coefficient(b, 1);
  // assert ptJ[3] eq 2;
  if Valuation(Coefficient(a, 1), p) ge 0 
      and Valuation(Coefficient(a, 0), p) ge 0
  then
    // relevant points have p-adically integral x-ccordinate
    xi := Qp!(-Coefficient(a, 1)/2);
    fxi := Evaluate(f, xi);
    if IsOdd(p) and Valuation(fxi) eq 0 then
      // p odd: use x-xi as local coordinate
      prec1 := precNeeded(p, Ceiling((p-1)/(p-2)*prec));
              // (p-1)/(p-2) to compensate for denominators in the square root
      Qp1 := pAdicField(p, prec1);
      xi := Qp!(-Coefficient(a, 1)/2);
      fxi := Evaluate(f, xi);
      del := xi^2 - Coefficient(a, 0);
        // disc/4, points have x = xi +- sqrt(del)
      Pws<t> := PowerSeriesRing(Qp1, prec1);
      f1 := Evaluate(f, t+xi)/fxi;
      diff1 := f1^(-1/2);
      diff2 := (t + xi)*diff1;
      log1 := Integral(diff1);
      log2 := Integral(diff2);
      l1 := &+[del^j*Coefficient(log1, 2*j+1) : j in [0..(prec1 div 2)-1]];
      l2 := &+[del^j*Coefficient(log2, 2*j+1) : j in [0..(prec1 div 2)-1]];
      s := Sqrt(del/fxi);
      if Valuation(b1*s-1) lt Valuation(b1*s+1) then s := -s; end if;
      return [(Qp!(s*l1)) + bigO, (Qp!(s*l2)) + bigO];
    else
      // use Kummer Surface
      pr2 := (4 + 5*Valuation(Discriminant(f), p))*prec;
      Kp := BaseChange(K, pAdicField(p, pr2));
      ptKp := Kp!ptK;
      mptK := p^(prec-1)*ptKp;
      assert forall{j : j in [1..3] | AbsolutePrecision(mptK[j]) ge 3*prec};
      lls := [mptK[j]/p^(2*prec) : j in [1..3]];
      // lls = [l1^2, 2*l1*l2, l2^2]
      //  with l1, l2 = 1/p times the logs we want
      assert Valuation(lls[1]) le Valuation(lls[3]);
      l1 := Sqrt(lls[1]);
      l2 := lls[2]/(2*l1);
      l1 *:= p;
      l2 *:= p;
      // fix the sign
      if Valuation(ll1 + Qp!l1) gt Valuation(ll1 - Qp!l1) then
        l1 := -l1;
        l2 := -l2;
      end if;
      assert Valuation(ll1 - Qp!l1) gt Valuation(ll1)
              and Valuation(ll2 - Qp!l2) gt Valuation(ll1);
      return [(Qp!l1) + bigO, (Qp!l2) + bigO];
    end if;
  else
    // relevant points map to infinity mod p:
    // reduce to known case
    J1 := Jacobian(HyperellipticCurve(Parent(f)![Coefficient(f,6-i)
                                                  : i in [0..6]]));
    a1r := Parent(f)![Coefficient(a, 2-i) : i in [0..2]];
    b1r := (Parent(f)![0, 0, Coefficient(b, 1), Coefficient(b, 0)]) mod a1r;
    ptJ1 := elt<J1 | a1r, b1r, 2>;
    l := pAdicLogG2(ptJ1, p, prec);
    return [-l[2], -l[1]];
  end if;
end function;

//----------------------------------------------------------------------

function HigherKernelsOfReduction(bas, p, m, MW, K1, hp)
  // bas = basis of MW group of J
  // p = prime
  // m = max exponent
  // MW = free abelian group on #bas generators
  // K1 = subgroup of MW, gives kernel of reduction
  // hp = height pairing matrix of bas
  // returns sequence of subgroups of free abelian group generated by bas
  
  vprintf DeepInfo, 2: "HigherKernelsOfReduction: p = %o, m = %o...\n", p, m;
  
  // find small generators of K1
  gens1 := [MW!k : k in OrderedGenerators(K1)];
  L := LatticeWithGram(Matrix([[Round(1000*hp[i,j]) : j in [1..#bas]]
                                 : i in [1..#bas]]));
  // set up sublattice
  Ls := sub<L | [L | Eltseq(g) : g in gens1]>;
  Lsub := LLL(Ls);
  gens1 := [MW!Eltseq(b) : b in Basis(Lsub)];
  vprintf DeepInfo, 2: "  Generators of kernel of red.: %o\n", gens1;
  J := Universe(bas);
  bas1 := [&+[J| es[i]*bas[i] : i in [1..#es]] where es := Eltseq(g)
            : g in gens1];
  vprintf DeepInfo, 2: "  ... computed as elements of MW group.\n";
  // compute logs
  logs := [ChangeUniverse(pAdicLogG2(b, p, m), Integers()) : b in bas1];
  vprintf DeepInfo, 2: "  %o-adic logarithms mod %o^%o: \n%o\n", p, p, m, logs;
  Ks := [MW, K1];
  FK1 := FreeAbelianGroup(#bas1);
  toMW := hom<FK1 -> MW | gens1>;
  for j := 2 to m do
    // find jth kernel
    Gj := AbelianGroup([p^j, p^j]);
    imgs := [Gj| l : l in logs];
    kerj := toMW(Kernel(hom<FK1 -> Gj | imgs>));
    Append(~Ks, sub<MW | [MW!k : k in Generators(kerj)]>);
  end for;
  return Ks;
end function;

//----------------------------------------------------------------------

function GoodReps(MW, ker, bas, hp)
  // gives sets of "small" representatives of the quotient by ker
  // ker given as subgroup of free abelian group MW on bas
  // hp := HeightPairingMatrix(bas);
  L := LatticeWithGram(Matrix([[Round(1000*hp[i,j]) : j in [1..#bas]]
                                 : i in [1..#bas]]));
  // get elements of quotient and lift to MW
  G, m := quo<MW | ker>;
  elts := {MW | g @@ m : g in G};
  // get generators of ker
  gens := ChangeUniverse(OrderedGenerators(ker), MW);
  // set up sublattice
  Ls := sub<L | [L | Eltseq(g) : g in gens]>;
  return {e - MW![Round(a) : a in Eltseq(ClosestVectors(Ls, L!Eltseq(e))[1])]
           : e in elts};
end function;

function FirstLevel(bas, p, deg3, mat)
  // deg3 = <a, b> or pt
  J := Universe(bas);
  C := Curve(J);
  f, h := HyperellipticPolynomials(C);
  assert h eq 0;
  vprintf GroupInfo, 1: "  GroupInfo: p = %o...\n", p;
  if Type(deg3) eq PtHyp then
    dflag := false;
  else
    dflag := IsDivisibleBy(LCM([Integers() | Denominator(c)
                                 : c in Coefficients(deg3[2])]),
                           p);
    polc := ExactQuotient(f - deg3[2]^2, deg3[1]);
    polc *:= 1/LeadingCoefficient(polc);
    deg3 := <deg3[2], deg3[1], polc>;
  end if;
  MW := FreeAbelianGroup(#bas);
  if not dflag and Valuation(Discriminant(C), p) eq 0 then
    Jp := BaseChange(J, GF(p));
    Cp := Curve(Jp);
    pts := Points(Cp);
    G, m := AbelianGroup(Jp);
    imbas := [(Jp!b) @@ m : b in bas];
    inj := MakeInj(J, p, deg3);
    DL := MakeDL(G, m);
    imC := {<DL(inj(pt)), pt> : pt in pts};
    Gsub := sub<G | imbas>;
    imC := {<Gsub!pt[1], pt[2]> : pt in imC | pt[1] in Gsub};
    imbas := ChangeUniverse(imbas, Gsub);
    K1 := Kernel(hom<MW -> Gsub | imbas>);
    vprintf GroupInfo, 1: "    #C(F_p) = %o, Invariants(G) = %o\n",
                          #imC, Invariants(Gsub);
    return [* p, imbas, imC *], MW, K1, true;
  elif not dflag and IsOdd(p) and IsRegularAtp(C, p) then
    vprintf GroupInfo, 1: 
            "    p = %o is bad, but not too bad ==> use BadGroupInfo\n", p;
    res := BadGroupInfo(C, bas, deg3, p);
    G := Universe(res[2]);
    K1 := Kernel(hom<MW -> G | res[2]>); 
    vprintf GroupInfo, 1: "    #C(F_p) = %o, Invariants(G) = %o\n",
                          #res[3], Invariants(Universe(res[2]));
    return res, MW, K1, false;
  end if;
  // worst case: do it by enumeration on group
  vprintf GroupInfo, 1: "    p = %o is very bad ==> use enumeration\n", p;
  MW, ker := KernelOfReduction(bas, p);
  reps := GoodReps(MW, ker, bas, mat); // representatives of quotient in MW
  G, qG := quo<MW | ker>;
  function test(b)
    coords := TDK(f, deg3, Eltseq(b), bas);
    if Valuation(coords[4], p) gt 0 then
      if Valuation(coords[1], p) eq 0 then
        // check if point mod p lifts to p-adic point
        x := (GF(p)!coords[2])/GF(p)!coords[1];
        fx := Evaluate(ChangeRing(f, Integers()), x);
        if fx ne 0 then return IsSquare(fx); end if;
        // now p divides f(x)
        return HasPoint(Evaluate(f, p*Parent(f).1 + Integers()!x), p);
      else
        return HasPoint(Evaluate(Parent(f)![Coefficient(f,6-i) : i in [0..6]],
                                 p*Parent(f).1),
                                 p);
      end if;
    end if;
    return false;
  end function;
  imC := {qG(b) : b in reps | test(b)};
  vprintf GroupInfo, 1: "    #C(F_p) = %o, Invariants(G) = %o\n",
                        #imC, Invariants(G);
  return [* p, [qG(MW.i) : i in [1..#bas]], imC *], MW, ker, false;
end function;

//----------------------------------------------------------------------
// Take some stuff from kummer.m and adapt it

// Given Kummer surface, get matrix of biquadratic forms giving action
// on the dual Kummer.
function DualActionMatrix(Kum)
  B := Kum`BBMatrix;
  PB := Parent(B[1,1]);
  v0 := [PB.i : i in [1..8]];
  PP := PolynomialRing(BaseField(Kum), 12);
  v1 := [PP.i : i in [1..4]];
  v2 := [PP.i : i in [5..8]];
  v3 := [PP.i : i in [9..12]];
  B := Matrix([[Evaluate(B[i,j], v2 cat v3) : j in [1..4]] : i in [1..4]]);
  expr := &+[v1[i]*B[i,j]*v1[j] : i,j in [1..4]];
  A := Matrix([[i eq j select Coefficient(expr, v3[i], 2)
                       else Coefficient(Coefficient(expr, v3[i], 1), v3[j], 1)/2
                 : j in [1..4]] : i in [1..4]]);
  // assert expr eq &+[v3[i]*Evaluate(A[i,j], v1 cat v2 cat [0,0,0,0])*v3[j] : i,j in [1..4]];
  return Matrix([[Evaluate(A[i,j], v0 cat [PB|0,0,0,0]) : j in [1..4]]
                  : i in [1..4]]);
end function;

function PseudoAddDual(P1, P2, P3, A)
  // P1 and P3 on dual Kummer (coordinate sequence), P2 in Kummer
  K := Parent(P2);
  L12 := P1 cat Eltseq(P2);
  L3 := P3;
  i := K`SelectCoordinate(L3);
  BB := A;
  c1 := 2*L3[i]; c2 := Evaluate(BB[i,i], L12);
  L := [ c1*Evaluate(BB[i,j], L12) - L3[j]*c2 : j in [1..4] ];
  // assume p-adic numbers here...
  prec := Precision(Universe(L));
  v := Min([ Min(Valuation(x),prec) : x in L ]); // | x ne 0 ]);
  a := UniformizingElement(BaseField(K))^(-v);
  xs1 := [a*x : x in L];
  i := 1; while Valuation(xs1[i]) gt 0 do i +:= 1; end while;
  xs1 := [x/xs1[i] : x in xs1];
  return xs1;
end function;

function PseudoAddMultipleDual(P1, P2, P3, n, A)
  if n lt 0 then
    P3 := PseudoAddDual(P1, P2, P3, A); n := -n;
  end if;
  while true do
    if IsOdd(n) then
      P1 := PseudoAddDual(P1, P2, P3, A);
    else
      P3 := PseudoAddDual(P3, P2, P1, A);
    end if;
    n div:= 2;
    if n eq 0 then return P1; end if;
    P2 := Double(P2);
  end while;
end function;

function AddJPtDeg3ToDualKummer(pt, deg3)
  // deg3 = <a, b, 3>
  f, h := HyperellipticPolynomials(Curve(Parent(pt)));
  F := CoefficientRing(Parent(f));
  assert h eq 0;
  sum := Dadd(f, <pt[1], pt[2], pt[3]>, deg3);
  if sum[3] le 1 then
    if Degree(sum[1]) eq 0 then
      return [F | 1, 0, 0, 0];
    else
      x := -Coefficient(sum[1], 0);
      return [x^2, -x, 1, 0];
    end if;
  else
    return ToDualKummer(f, sum[1], sum[2]);
  end if;
end function;

function LCInitDual(deg3, B)
  // deg3 = <a, b, 3>
  J := Universe(B);
  K := KummerSurface(J);
  V := [J!0];
  for j in B do
    V cat:= [j + v : v in V];
  end for;
  return [AddJPtDeg3ToDualKummer(-b, deg3) : b in V], ChangeUniverse(B, K);
end function;

// intrinsic LinearCombination(n::[RngIntElt],V::[SrfKumPt])->SrfKumPt
// V as given by LCInitDual
function LinearCombinationDual(n, B, V, A)
  for i in [1..#n] do
    V := [PseudoAddMultipleDual(V[j],B[i],V[j+1],n[i],A) : j in [1..#V-1 by 2]];
  end for;
  assert #V eq 1;
  return V[1];
end function;

//----------------------------------------------------------------------

// Logarithm series at points on C that have non-singular reduction

function LogSeriesOnC(ptC, f, p, prec)
  fp := ChangeRing(ChangeRing(f, Integers()), GF(p));
  ptx := GF(p)!ptC[1];
  pty := GF(p)!ptC[2];
  ptz := GF(p)!ptC[3];
  // check that point is smooth mod p
  assert 2*pty ne 0 or (ptz ne 0 and Evaluate(Derivative(fp), ptx/ptz) ne 0)
          or (ptz eq 0 and Coefficient(fp, 5) ne 0);
  Qp := pAdicField(p, prec);
  Pw<t> := PowerSeriesRing(Qp, prec);
  if 2*pty ne 0 and ptz ne 0 then
    // use t = x - (lift of ptx)
    ptx := ptx/ptz;
    pty := pty/ptz^3;
    x1 := Qp!ptx;
    parx := t + x1;
    pary := Sqrt(Evaluate(f, parx));
    if GF(p)!Coefficient(pary, 0) ne pty then pary := -pary; end if;
    om1 := 1/2*pary^-1;
    om2 := parx*om1;
    log1 := Integral(om1);
    log2 := Integral(om2);
    return [log1, log2, parx, pary];
  elif ptz ne 0 then
    // use t = y
    ptx := ptx/ptz;
    pary := t;
    // for x, solve t^2 = f(x)
    parx := Pw!Qp!ptx;
    while true do
      df := Evaluate(Derivative(f), Coefficient(parx, 0));
      temp := parx + 1/df*(t^2 - Evaluate(f, parx));
      if temp eq parx then break; end if;
      parx := temp;
    end while;
    om1 := Evaluate(Derivative(f), parx)^-1;
    om2 := parx*om1;
    log1 := Integral(om1);
    log2 := Integral(om2);
    return [log1, log2, parx, pary];
  elif 2*pty ne 0 then // ptz eq 0
    // use t = 1/x
    pty := pty/ptx^3;
    parx := t;
    pary := Sqrt(Pw![Coefficient(f, 6-i) : i in [0..6]]);
    if GF(p)!Coefficient(pary, 0) ne pty then pary := -pary; end if;
    om2 := -1/2*pary^-1;
    om1 := parx*om2;
    log1 := Integral(om1);
    log2 := Integral(om2);
    return [log1, log2, parx, pary];
  else // 2*pty eq 0 and ptz eq 0
    // use t = y/x^3
    pary := t;
    parx := Pw!Qp!0;
    fr := Parent(f)![Coefficient(f, 6-i) : i in [0..6]];
    while true do
      df := Evaluate(Derivative(fr), Coefficient(parx, 0));
      temp := parx + 1/df*(t^2 - Evaluate(fr, parx));
      if temp eq parx then break; end if;
      parx := temp;
    end while;
    om2 := -Evaluate(Derivative(fr), parx)^-1;
    om1 := parx*om2;
    log1 := Integral(om1);
    log2 := Integral(om2);
    return [log1, log2, parx, pary];
  end if;
end function;

//----------------------------------------------------------------------

function DeepenLevel(first, bas, deg3, n, MW, K1, hp);
  // first: as returned by FirstLevel
  // deg3 = <a, b> or pt
  
  if n le 1 then return first; end if;
  
  p := first[1];
  vprintf GroupInfo, 1: "  DeepenLevel for %o^%o...\n", p, n;
  
  if Type(deg3) eq PtHyp then
    P<x> := PolynomialRing(Rationals());
    deg3 := deg3[3] eq 0
            select <P!1, deg3[2]/deg3[1]^3*x^3, deg3[2] eq 0 select 0 else 1>
            else <x - deg3[1]/deg3[3], deg3[2]/deg3[3]^3, 1>;
  else
    deg3 := <deg3[1], deg3[2], 3>;
  end if;
  J := Universe(bas);
  K := KummerSurface(J);
  A := DualActionMatrix(K);

  // need higher kernels of reduction
  Ks := HigherKernelsOfReduction(bas, p, n, MW, K1, hp); // change from n+1
  
  // work in quotient modulo nth kernel
  Kn := Ks[n+1];
  QG, qmap := quo<MW | Kn>;
  Qgens := [q @@ qmap : q in OrderedGenerators(QG)];
  // Compute "small" representatives of the quotient by Kn
  // hp := HeightPairingMatrix(bas);
  L := LatticeWithGram(Matrix([[Round(1000*hp[i,j]) : j in [1..#bas]]
                                 : i in [1..#bas]]));
  // get generators of Kn
  gens := ChangeUniverse(OrderedGenerators(Kn), MW);
  // set up sublattice
  Ls := sub<L | [L | Eltseq(g) : g in gens]>;
  Qgens := [e - MW![Round(a)
                     : a in Eltseq(ClosestVectors(Ls, L!Eltseq(e))[1])]
           : e in Qgens];
  vprintf DeepInfo, 2: "Generators of quotient by %o%o kernel:\n   %o\n",
                       n, ending(n), Qgens;
  assert [qmap(q) : q in Qgens] eq OrderedGenerators(QG);

  Qbas := [&+[J | es[i]*bas[i] : i in [1..#es]] where es := Eltseq(q)
            : q in Qgens];
  vprintf DeepInfo, 2: " ... computed as points in MW group.\n";

  // (replace bas by Qbas in the following)
  V0 := LCInit(Qbas);
  V, B := LCInitDual(deg3, Qbas);
  v := Valuation(Discriminant(Curve(J)), p);
  Qp := pAdicField(p, 2*n+20+v); // 20 was 3 -- precision!
  Kp := BaseChange(K, Qp);
  B := ChangeUniverse(B, Kp);
  V0 := ChangeUniverse(V0, Kp);
  function norm(s)
    v := Min([Valuation(a) : a in s]);
    s := [a/p^v : a in s];
    i := 1; while Valuation(s[i]) gt 0 do i +:= 1; end while;
    return [a/s[i] : a in s];
  end function;
  V := [norm(ChangeUniverse(s, Qp)) : s in V];
  
  imbas := first[2];
  G := Universe(imbas);
  h := hom<MW -> G | imbas>;
  assert Ks[2] eq Kernel(h);
  imQbas := [h(q) : q in Qgens]; // work with these...
  Qh := hom<QG -> G | imQbas>;
  imC := first[3];
  
  // map kernels of reduction into QG
  OldKs := Ks;
  Ks := [qmap(Ks[i]) : i in [1..#Ks]];
  
  // get images of representatives of imC in G on dual Kummer
  genses := [Eltseq(QG!b) : b in OrderedGenerators(Ks[2])];
  function rep(a)
    r := Eltseq(a @@ Qh);
    lcs := [[0 : b in Qbas]];
    for es in genses do
      lcs cat:= [[lc[i] + es[i] : i in [1..#es]] : lc in lcs];
    end for;
    lcs := [[r[i] - lc[i] : i in [1..#r]] : lc in lcs];
    Vr := [LinearCombinationDual(lc, B, V, A) : lc in lcs];
    // check
    /*
    vprintf DeepInfo: "  %o --> v(e4) = %o, v(del) = %o\n",
                   r, Valuation(Vr[1,4]),
                   Valuation(Vr[1,2]^2 - Vr[1,1]*Vr[1,3]);
    */
    assert Valuation(Vr[1,4]) gt 0
            and Valuation(Vr[1,2]^2 - Vr[1,1]*Vr[1,3]) gt 0;
    return <QG!r, Vr>;
  end function;
  imCplus := {rep(pt) : pt in imC};
  
  vprintf DeepInfo, 2: "First Level: Group = %o, #points = %o\n",
                       Invariants(G), #imCplus;
  
  for i := 2 to n do
    // set up next level of B, V
    genses := [Eltseq(Ks[i-1]!b) : b in OrderedGenerators(Ks[i])];
    vprintf DeepInfo, 3: "*** genses = %o\n", genses;
    lcs := [[0 : b in OrderedGenerators(Ks[i-1])]];
    for es in genses do
      lcs cat:= [[lc[i] + es[i] : i in [1..#es]] : lc in lcs];
    end for;
    B := [LinearCombination(es, V0) : es in genses];
    // check
    assert forall{b : b in B | Min([Valuation(b[i]) : i in [1..3]]) ge 2*(i-1)};
    V0 := [LinearCombination(lc, V0) : lc in lcs];
    
    // set up quotient group generators
    G, q := quo<Ks[i] | Ks[i+1]>;
    qgens := [g @@ q : g in OrderedGenerators(G)];
    genses := [Eltseq(Ks[i]!b) : b in OrderedGenerators(Ks[i+1])];
    /*
    vprintf DeepInfo: "generators of quotient:\n  ";
    for g in qgens do
      vprintf DeepInfo: "%o ", Eltseq(MW!g);
    end for;
    vprintf DeepInfo: "\n";
    */
    lcs := [[0 : b in OrderedGenerators(Ks[i+1])]];
    for es in genses do
      lcs cat:= [[lc[i] + es[i] : i in [1..#es]] : lc in lcs];
    end for;
    
    function lift(pair)
      // construct linear form
      vprintf DeepInfo, 3: " lift(%o), v(e4) = %o, v(del) = %o\n",
                     Eltseq(pair[1]), Valuation(pair[2,1,4]),
                     Valuation(pair[2,1,2]^2 - pair[2,1,1]*pair[2,1,3]);
      z0 := GF(p)!((pair[2,1,2]^2 - pair[2,1,1]*pair[2,1,3])/p^(i-1));
      mat := Matrix([[(GF(p)!((pt[2]^2 - pt[1]*pt[3])/p^(i-1))) - z0]
                    where pt := LinearCombinationDual(Eltseq(g), B, pair[2], A)
                               : g in qgens]);
      // vprintf DeepInfo, 3: "  z0 = %o, mat = %o\n", z0, Eltseq(mat);
      flag, sol, ker := IsConsistent(mat, Vector([-z0]));
      if not flag then
        vprintf DeepInfo, 3: "   no solution\n";
        return {};
      else
        vprintf DeepInfo, 3: "   sol = %o, dim ker = %o\n", sol, Dimension(ker);
        solns := {sol + k : k in ker};
        function rep(s)
          s1 := &+[(Integers()!s[i])*G.i : i in [1..#qgens]] @@ q;
          r := Eltseq(s1);
          if i eq n then
            Vr := [LinearCombinationDual(r, B, pair[2], A)];
          else
            lcsr := [[r[i] - lc[i] : i in [1..#r]] : lc in lcs];
            Vr := [LinearCombinationDual(lc, B, pair[2], A) : lc in lcsr];
          end if;
          // check
          /* vprintf DeepInfo, 3: "  %o --> v(e4) = %o, v(del) = %o\n",
                         Eltseq(pair[1] + QG!s1), Valuation(Vr[1,4]),
                         Valuation(Vr[1,2]^2 - Vr[1,1]*Vr[1,3]);
          */
          assert Valuation(Vr[1,4]) gt 0
                  and Valuation(Vr[1,2]^2 - Vr[1,1]*Vr[1,3]) ge i;
          // change this so that it increases precision and recomputes
          // if there is precision loss:
          assert forall{r : r in Vr, j in [1..4]
                          | AbsolutePrecision(r[j]) gt 2*i};
          return <pair[1] + QG!s1, Vr>;
        end function;
        return {pair : s in solns | Valuation(pair[2,1,4]) ge 2*i
                                      where pair := rep(s)};
      end if;
    end function;    
    imCplus := &join{lift(pair) : pair in imCplus};
    if IsEmpty(imCplus) then return [* p^i, [], {} *]; end if;

    vprintf DeepInfo, 2: "Level %o: Group = %o, #points = %o\n",
                   i, Invariants(quo<QG | Ks[i+1]>), #imCplus;

  end for;
  
  imbas := [qmap(MW.i) : i in [1..#bas]];
  imC := {pair[1] : pair in imCplus};
  vprintf GroupInfo, 1: "    #C(Z/%o^%oZ) = %o, Invariants(G) = %o\n",
                        p, n, #imC, Invariants(QG);
  return [* p^n, imbas, imC *];
end function;

function LogHelp(f, ll1, ll2, p, n)
  pr := Min(Valuation(ll1), Valuation(ll2));
  if p eq 3 then
    if n le 3*pr-1 then return LogSeries(f, ll1, ll2, 1); 
    elif n le 5*pr then return LogSeries(f, ll1, ll2, 3);
    elif n le 7*pr then return LogSeries(f, ll1, ll2, 5);        
    elif n le 9*pr-2 then return LogSeries(f, ll1, ll2, 7);
    end if;
  elif p eq 5 then
    if n le 3*pr then return LogSeries(f, ll1, ll2, 1);
    elif n le 5*pr-1 then return LogSeries(f, ll1, ll2, 3);
    elif n le 7*pr then return LogSeries(f, ll1, ll2, 5);        
    elif n le 9*pr then return LogSeries(f, ll1, ll2, 7);
    end if;
  elif p eq 7 then
    if n le 3*pr then return LogSeries(f, ll1, ll2, 1);
    elif n le 5*pr then return LogSeries(f, ll1, ll2, 3);
    elif n le 7*pr-1 then return LogSeries(f, ll1, ll2, 5);        
    elif n le 9*pr then return LogSeries(f, ll1, ll2, 7);
    end if;
  else
    if n le 3*pr then return LogSeries(f, ll1, ll2, 1);
    elif n le 5*pr then return LogSeries(f, ll1, ll2, 3);
    elif n le 7*pr then return LogSeries(f, ll1, ll2, 5);        
    elif n le 9*pr then return LogSeries(f, ll1, ll2, 7);
    end if;
  end if;
end function;

function DeepenLevelLog(first, bas, deg3, n, MW, K1, hp);
  // first: as returned by FirstLevel
  // deg3 = <a, b> or pt
  first[3] := {a[1] : a in first[3]};
  return DeepenLevel(first, bas, deg3, n, MW, K1, hp);
  
  if n le 1 then return first; end if;
  
  p := first[1];
  vprintf GroupInfo, 1: "  DeepenLevelLog for %o^%o...\n", p, n;
  
  if Type(deg3) eq PtHyp then
    P<x> := PolynomialRing(Rationals());
    deg3 := deg3[3] eq 0
            select <P!1, deg3[2]/deg3[1]^3*x^3, deg3[2] eq 0 select 0 else 1>
            else <x - deg3[1]/deg3[3], deg3[2]/deg3[3]^3, 1>;
  else
    deg3 := <deg3[1], deg3[2], 3>;
  end if;
  J := Universe(bas);
  C := Curve(J);
  f := HyperellipticPolynomials(C);
  
    // need higher kernels of reduction
  Ks := HigherKernelsOfReduction(bas, p, n, MW, K1, hp);
 
  // work in quotient modulo nth kernel
  Kn := Ks[n+1];
  QG, qmap := quo<MW | Kn>;
  Qgens := [q @@ qmap : q in OrderedGenerators(QG)];
  // Compute "small" representatives of generators of the quotient by Kn
  L := LatticeWithGram(Matrix([[Round(1000*hp[i,j]) : j in [1..#bas]]
                                 : i in [1..#bas]]));
  // get generators of Kn
  gens := ChangeUniverse(OrderedGenerators(Kn), MW);
  // set up sublattice
  Ls := sub<L | [L | Eltseq(g) : g in gens]>;
  Qgens := [e - MW![Round(a)
                     : a in Eltseq(ClosestVectors(Ls, L!Eltseq(e))[1])]
           : e in Qgens];
  vprintf DeepInfo, 2: "Generators of quotient by %o%o kernel:\n   %o\n",
                       n, ending(n), Qgens;
  assert [qmap(q) : q in Qgens] eq OrderedGenerators(QG);
  Qbas := [&+[J | es[i]*bas[i] : i in [1..#es]] where es := Eltseq(q)
            : q in Qgens];
  vprintf DeepInfo, 2: " ... computed as points in MW group.\n";
  // find logs
  logsQbas := [pAdicLogG2(g, p, n) : g in Qbas];
  logsQbas := [[Integers()|a[1]/p, a[2]/p] : a in logsQbas];
  vprintf DeepInfo, 2: "%o-adic logs/%o mod %o^%o:\n%o\n",
                       p, p, p, n-1, logsQbas;
  // find small representatives of points on J mapping to C(F_p)
  // set up quotient map to MW/K1
  m := hom<MW -> Universe(first[2]) | first[2]>;
  // get generators of first kernel
  gens1 := ChangeUniverse(OrderedGenerators(Kernel(m)), MW);
  // set up sublattice
  Ls1 := sub<L | [L | Eltseq(g) : g in gens1]>;
  elts := {<e[1] @@ m, e[1], e[2]> : e in first[3]};
  vprintf DeepInfo, 2: "Find small representatives of C(F_%o) in MW group...\n",
                       p;
  reps := {<e[1] - MW![Round(a)
                       : a in Eltseq(ClosestVectors(Ls, L!Eltseq(e[1]))[1])],
            e[2],
            e[3]>
            : e in elts};
  vprintf DeepInfo, 2: "Compute them as actual points in J(Q)...\n";
  reps := {<&+[J| es[i]*bas[i] : i in [1..#es]] where es := Eltseq(e[1]),
            e[2], e[3], e[4]>
             : e in reps};
  vprintf DeepInfo, 2: "  ...done.\n";
  
  // for each quadruple <ptJ, ptMW, ptQG, ptC> in reps, ...
  imC := {QG| };
  P := Parent(f);
  x := P.1;
  Qp := pAdicField(p, n+5); // to be safe...
  fact := Factorization(ChangeRing(f, Integers()));
  for entry in reps do
    ptJ, ptMW, ptQG, ptC := Explode(entry);
    logpar := LogSeriesOnC(ptC, f, p, n+2);
    // find suitable algebraic -> p-adic point
    if ptC[3] ne 0 and ptC[2] ne 0 then
      ptx := Integers()!(ptC[1]/ptC[3]);
      y2 := Evaluate(f, ptx);
      flag, pty := IsSquare(y2);
      if flag then // can work over Q
        // pick correct square root
        if GF(p)!pty ne ptC[2]/ptC[3]^3 then pty := -pty; end if;
        impt := Dadd(f, deg3, <x - ptx, P!-pty, 1>);
           // this is the negative of the image of the point on J
        dif := ptJ + elt<J | impt[1], impt[2], impt[3]>;
        logdiff := pAdicLogG2(dif, p, n);
        logdiff := [Integers() | l/p : l in logdiff];
      else // need to work in quadratic extension
        pty := Sqrt(Qp!y2);
        // pick correct square root
        if GF(p)!pty ne ptC[2]/ptC[3]^3 then pty := -pty; end if;
        // set up quadratic field
        L<w> := NumberField(x^2 - y2);
        loc := hom<L -> Qp | pty>; // completion map
        PL := PolynomialRing(L);
        X := PL.1;
        impt := Dadd(PL!f, PL!deg3, <X - L!ptx, -w, 1>);
        JL := BaseChange(J, L);
        dif := JL!ptJ + elt<JL | impt[1], impt[2], impt[3]>;
        coords := JPttoCoords(dif);
        ll1 := loc(coords[3]/coords[1]);
        ll2 := loc(coords[2]/coords[1]);
        logdiff := LogHelp(f, ll1, ll2, p, n);
        logdiff := [Integers() | l/p : l in logdiff];
      end if;
    elif ptC[2] ne 0 then // non Weierstrass point at infinity
      flag, pty := IsSquare(y2);
      y2 := Coefficient(f, 6);
      if flag then // can work over Q
        // pick correct square root
        if GF(p)!pty ne ptC[2]/ptC[1]^3 then pty := -pty; end if;
        impt := Dadd(f, deg3, <P!1, -pty*x^3, 1>);
           // this is the negative of the image of the point on J
        dif := ptJ + elt<J | impt[1], impt[2], impt[3]>;
        logdiff := pAdicLogG2(dif, p, n);
        logdiff := [Integers() | l/p : l in logdiff];
      else // need to work in quadratic extension
        pty := Sqrt(Qp!y2);
        // pick correct square root
        if GF(p)!pty ne ptC[2]/ptC[1]^3 then pty := -pty; end if;
        // set up quadratic field
        L<w> := NumberField(x^2 - y2);
        loc := hom<L -> Qp | pty>; // completion map
        PL := PolynomialRing(L);
        X := PL.1;
        impt := Dadd(PL!f, PL!deg3, <PL!1, -w*X^3, 1>);
        JL := BaseChange(J, L);
        dif := JL!ptJ + elt<JL | impt[1], impt[2], impt[3]>;
        coords := JPttoCoords(dif);
        ll1 := loc(coords[3]/coords[1]);
        ll2 := loc(coords[2]/coords[1]);
        logdiff := LogHelp(f, ll1, ll2, p, n);
        logdiff := [Integers() | l/p : l in logdiff];
      end if;
    elif ptC[3] ne 0 then // affine Weierstrass point
      for ff in fact do
        f1 := ff[1];
        if Evaluate(f1, ptC[1]/ptC[3]) eq 0 then break; end if;
      end for;
      rs := [r[1] : r in Roots(f1, Qp)];
      for r1 in rs do
        if GF(p)!r1 eq ptC[1]/ptC[3] then r := r1; break; end if;
      end for;
      // set up number field
      L<w> := NumberField(f1);
      loc := hom<L -> Qp | r>; // completion map
      PL := PolynomialRing(L);
      X := PL.1;
      impt := Dadd(PL!f, PL!deg3, <X - w, PL!0, 1>);
      JL := BaseChange(J, L);
      dif := JL!ptJ + elt<JL | impt[1], impt[2], impt[3]>;
      coords := JPttoCoords(dif);
      ll1 := loc(coords[3]/coords[1]);
      ll2 := loc(coords[2]/coords[1]);
      logdiff := LogHelp(f, ll1, ll2, p, n);
      logdiff := [Integers() | l/p : l in logdiff];
    else // Weierstrass point at infinity
      if Degree(f) eq 5 then
        logdiff := pAdicLogG2(ptJ, p, n);
        logdiff := [Integers() | l/p : l in logdiff];
      else
        for ff in fact do
          f1 := ff[1];
          if GF(p)!LeadingCoefficient(f1) eq 0 then break; end if;
        end for;
        rs := [r[1] : r in Roots(f1, Qp)];
        for r1 in rs do
          if Valuation(r1) lt 0 then r := r1; break; end if;
        end for;
        // set up number field
        L<w> := NumberField(f1);
        loc := hom<L -> Qp | r>; // completion map
        PL := PolynomialRing(L);
        X := PL.1;
        impt := Dadd(PL!f, PL!deg3, <X - w, PL!0, 1>);
        JL := BaseChange(J, L);
        dif := JL!ptJ + elt<JL | impt[1], impt[2], impt[3]>;
        coords := JPttoCoords(dif);
        ll1 := loc(coords[3]/coords[1]);
        ll2 := loc(coords[2]/coords[1]);
        logdiff := LogHelp(f, ll1, ll2, p, n);
        logdiff := [Integers() | l/p : l in logdiff];
      end if;
    end if;
    // find image of curve in terms of logs
    o := O(Qp!p^n);
    clogs := {[Integers()!((Evaluate(ls, p*t) + o)/p)
                : ls in [logpar[1], logpar[2]]]
               : t in [0..p^(n-1)-1]};
    // now shift by log of diff
    clogsd := {[l[1]-logdiff[1], l[2]-logdiff[2]] : l in clogs};
    // solve linear systems
    // ???
  end for;
  return [* p, [qmap(MW.i) : i in [1..#bas]], imC *];
end function;

//----------------------------------------------------------------------

intrinsic DeepGI(J::JacHyp, bound::RngIntElt, bas::SeqEnum, deg3::. : Deep := [], Exclude := [], LowerBound := 2, PrimeBound := 50, SmoothBound := 250) -> SeqEnum, RngIntElt
{ }
  // deep = [<p, e>, ...]
  // deg3 = <b, a, c> or pt
  if Type(deg3) eq PtHyp then
    d3 := deg3;
  else
    d3 := <deg3[2], deg3[1]>;
  end if;
  dl := [];
  if not IsEmpty(Deep) then 
    mat := HeightPairingMatrix(bas);
    for p in Deep do
      res, MW, K1, flag := FirstLevel(bas, p[1], d3, mat);
      if IsEmpty(res[3]) then return [res], res[1]; end if;
      if flag and ((p[1] eq 3 and p[2] le 7) or p[2] le 9) then
        res := DeepenLevelLog(res, bas, d3, p[2], MW, K1, mat);
      elif flag then
        res[3] := {a[1] : a in res[3]};
        res := DeepenLevel(res, bas, d3, p[2], MW, K1, mat);
      else
        res := DeepenLevel(res, bas, d3, p[2], MW, K1, mat);
      end if;
      if IsEmpty(res[3]) then return [res], res[1]; end if;
      Append(~dl, res);
    end for;
  end if;
  GI, p := GroupInfo(J, bound, bas, deg3, 
                     [p[1] : p in Deep] cat Exclude, LowerBound,
                     PrimeBound, SmoothBound);
  return dl cat GI, p;
end intrinsic;
