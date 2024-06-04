clear;
Minimise := func< U | GenusOneModel(Minimise(Equation(U))) >;
Reduce := func< U | GenusOneModel(Reduce(Equation(U))) >;
//
//  Visibility of Tate-Shafarevich groups 
//
//  Magma examples
//  30th April 2008
//
//=================================================================
//
//  Example 1
//
//  Compute the space of weight 2 newforms for Gamma_0(681)
M := ModularSymbols(681);
N := NewSubspace(CuspidalSubspace(M));
D := SortDecomposition(NewformDecomposition(N));
//  
//  There are modular abelian varieties of level 681 with the 
//  following dimensions.
[Dimension(x)/2: x in D];
[CremonaReference(EllipticCurve(D[i])): i in [1..5]];
//  
CD := CremonaDatabase();
E := EllipticCurve(CD,"681b1");E;
F := EllipticCurve(CD,"681c1");F;
//
//  The intersection of E and F inside J_0(681) can be computed 
//  using modular symbols.
//
IntersectionGroup(D[2],D[3]); 
//
//  So E[3] and F[3] are isomorphic as Galois modules
//  (Terminology: E and F are 3-congruent.)
//
AnalyticRank(E);
AnalyticRank(F);
MW,MWmap := MordellWeilGroup(F);MW;
[#TorsionSubgroup(A) : A in IsogenousCurves(E)];
[#TorsionSubgroup(A) : A in IsogenousCurves(F)];
//
// So F(Q)/3F(Q) = (Z/3Z)^2 injects into H^1(Q,E).
//
// Might these be elements of the Tate-Shafarevich group?
// The value of #III(E/Q) * Reg(E(Q)) predicted by BSD is
ConjecturalRegulator(E); 
//
// The Tamagawa numbers are computed by Tate's algorithm.
//
BadPrimes(E);
TamagawaNumbers(E);
TamagawaNumbers(F);
//
// So local solubility is guaranteed except possibly at 3.
//
// We check local solubility at 3 by writing these torsors
// as plane cubics.
// First we compute the Hesse pencil of F.
//
P<t> := PolynomialRing(Rationals());
U := GenusOneModel(3,F);U;
//
H := Hessian(U);H;
//
vecU := Vector(P,Eltseq(U)); vecH := Vector(P,Eltseq(H));
HessePencil := GenusOneModel(3,Eltseq(t*vecU+vecH));
HessePencil;
//
//  We put this family of elliptic curves in Weierstrass form 
//  (i.e. y^2 = x^3 - 27*c4*x - 54*c6) by computing the invariants.
//  
c4,c6,Delta := Invariants(HessePencil);
c4;
c6;
//
//  Alternatively, we can compute these invariants directly from F.
//
DD,cc4,cc6 := 
   HessePolynomials(3,1,cInvariants(F):Variables := [t,1]);
[c4,c6,Delta] eq [cc4,cc6,Discriminant(F)*DD^3];
//
//  Can we find E in the Hesse pencil of F?
//
poly := c4^3 - jInvariant(E)*Delta;
Roots(poly);
//  Apparently not!
//
//  Problem : the isomorphism E[3] = F[3] does not respect
//  the Weil pairing.
//  One solution is to use the contravariants P,Q in place of
//  the covariants U,H. An alternative, that works in this case, 
//  is to switch to a 2-isogenous curve.
//
E1 := EllipticCurve(CD,"681b4");
flag,isog := IsIsogenous(E,E1);flag,Degree(isog);
poly := c4^3 - jInvariant(E1)*Delta;
rts := Roots(poly); rts;
//  Good.
//
//  We pick some representatives for F(Q)/3F(Q) = (Z/3Z)^2
//
pts := [MWmap(MW!x): x in [[1,0],[0,1],[1,1],[1,-1]]];
//
//  We compute their images under the map F(Q)/3F(Q) -> H^1(Q,E).
//    
for pt in pts do
  print "pt =",pt;
  D := 2*Divisor(F!0) + Divisor(pt);
  U := GenusOneModel(Image(DivisorMap(D)));
  U := Reduce(Minimise(U));
  assert cInvariants(U) eq cInvariants(F);
  H := Hessian(U);
  vecU := Vector(Eltseq(U));vecH := Vector(Eltseq(H));
  V := GenusOneModel(3,Eltseq(rts[1][1]*vecU + vecH));
  V := Reduce(Minimise(V));
  assert IsIsomorphic(Jacobian(V),E1);
  print Equation(V);
  assert IsLocallySolvable(Curve(V),3);
end for;
//
// N.B. Mazur checks local solubility at 3 in a much more
// high-brow way - using flat cohomology.
//
//=================================================================
//
//  Example 2
//
E := EllipticCurve(CD,"1058d1");
F := EllipticCurve(CD,"1058c1");
AnalyticRank(E);
ConjecturalRegulator(E);
// 
//  In fact E is the first elliptic curve (by conductor) 
//  with no rational 5-isogeny that is predicted to have 
//  an element of order 5 in its Tate-Shafarevich group.
//
//  Conveniently there is a rank 2 curve at the same level.
//
MW,MWmap := MordellWeilGroup(F); MW;
//  
//  We check for a 5-congruence using the analogue of the
//  Hesse family in degree 5.
//
DD,c4,c6 := 
   HessePolynomials(5,1,cInvariants(F):Variables := [t,1]);
poly := c4^3 - jInvariant(E)*Discriminant(F)*DD^5;
rts := Roots(poly);rts;
E1 := EllipticCurve([Evaluate(x,rts[1][1]): x in [-27*c4,-54*c6]]);
IsIsomorphic(E,E1);
//
//  We have found E in the Hesse pencil of F.
//  So E[5] and F[5] are isomorphic as Galois modules
//  (and the isomorphism respects the Weil pairing).
//
[#TorsionSubgroup(A) : A in IsogenousCurves(E)];
[#TorsionSubgroup(A) : A in IsogenousCurves(F)];
BadPrimes(E);
TamagawaNumbers(E);
TamagawaNumbers(F);
//
//  So F(Q)/5F(Q) = (Z/5Z)^2 injects into III(E/Q)
//
//  N.B. Can also give equations for these elements of III,
//  exactly as in Example 1 - using my degree 5 "Hessian".
//  (Warning: Minimise and Reduce are not yet in Magma.)
//
//=================================================================
//
//  Example 3
//
E := EllipticCurve(CD,"3364c1");E;
F := EllipticCurve(CD,"10092c1");F;
//
AnalyticRank(E);
ConjecturalRegulator(E);
//
//  In the paper by Cremona and Mazur, III(E/Q)[7] is listed 
//  as invisible, since E satisfies no congruence modulo 7 
//  to any curve of conductor <= 5500 (the range of 
//  Cremona's tables at that time).
//
//  We show that it is visible at 3 times the level. 
// 
MW,MWmap := MordellWeilGroup(F);MW;
//
//  The modular forms attached to E and F are
//
fE := ModularForm(E);SetPrecision(Parent(fE),15);fE;
fF := ModularForm(F);SetPrecision(Parent(fF),15);fF;
//
// They seem to satisfy a 7-congruence.
//
function SturmBound(N)
  ff := Factorization(N);
  prod := &*[q^r + q^(r-1) where q,r is Explode(f): f in ff];
  return prod/6;
end function;
SturmBound(10092);
aE := TracesOfFrobenius(E,3500);
bE := TracesOfFrobenius(F,3500);
[i : i in [1..#aE] | (aE[i] - bE[i]) mod 7 ne 0];
//
// So E[7] and F[7] are equal in J_0(10092)
// (See Jetchev, Stein, "Visibility of the Shafarevich-Tate
// at Higher Level", for an explanation why this is enough.)
//
#IsogenousCurves(E), #IsogenousCurves(F);
BadPrimes(E);
TamagawaNumbers(E); 
TamagawaNumbers(F);
//
//  So F(Q)/7F(Q) = (Z/7Z)^2 injects into III(E/Q).
//
//=================================================================
//
//  Example 4    A higher dimensional example    
//               (taken from notes by William Stein)
//
M := ModularSymbols(389);
N := NewSubspace(CuspidalSubspace(M));
D := SortDecomposition(NewformDecomposition(N));
[Dimension(x)/2: x in D];
A := D[5]; B := D[1];
//
//  These are abelian varieties of dimensions 20 and 1
//  inside J_0(389).
//
WeqnB := EllipticCurve(B);WeqnB;
CremonaReference(WeqnB);
MW,MWmap := MordellWeilGroup(WeqnB);MW;
//
//  The intersection of A and B inside J_0(389) can be 
//  computed using modular symbols.
//
IntersectionGroup(A,B);
//
//  Reducing modulo some small primes (up to 7) gives 
//  some bounds on #A(Q)_tors and #B(Q)_tors.
//
TorsionBound(A,7);
TorsionBound(B,7);
//
//  These bound also apply to any abelian varieties
//  isogenous to A and B. 
//
TamagawaNumber(A,389);
TamagawaNumber(B,389);
//
//  So B(Q)/5B(Q) = (Z/5Z)^2 injects into III(A/Q).
//  Since dim(A) = 20 there is no chance of giving equations!
//
//==================================================================
// 
//   THE END
//
 





