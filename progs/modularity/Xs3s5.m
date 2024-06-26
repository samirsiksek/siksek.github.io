
// We give a model for X=X(s3,s5) 
// (isomorphic to X_0(225)/<w_9,w_{25}>)
// (together with a proof of the model's correctness)
// and we determine \Sym^{(2)}(X)(\Q) 


S:=CuspForms(225);
V1:=Eigenspace(AtkinLehnerOperator(S,25),1);
V2:=Eigenspace(AtkinLehnerOperator(S,9),1);
V:=V1 meet V2;
assert Dimension(V) eq 4;

B:=Basis(V);
B:=[Eltseq(b) : b in B];
B:=[&+[b[i]*S.i : i in [1..#b]] : b in B];  // B is a basis for intersection of the +1 eigenspaces
						// for w_{25}, w_9 acting on S_2(225).
						// Thus the elements of B are 
						// holomorphic differentials on
						// X_0(225)/<w_9,w_{25}>.

assert #B eq 4;
// Hence X=X_0(225)/<w_9,w_{25}> has genus 4.

C:=[ [ -1, 0, 0, 2 ], [ 1, -1, 2, -1 ], [ 1, 1, -2, -1 ], [ 0, 1, 0, -1 ] ];

// We shall now change basis for this subspace, using the matrix C.
// The reason for changing the basis is that the automorphisms
// of the resulting model for X are simpler to describe, as we will see.

assert Determinant(Matrix(C)) eq -4; // Change of basis is non-singular!

B:=[&+[c[i]*B[i] : i in [1..4]] : c in C];

// We now write down equations for X

R<[x]>:=PolynomialRing(Rationals(),4);


eqn1:=3*x[1]^2 - x[2]^2 - 2*x[3]^2 + 2*x[3]*x[4] - 3*x[4]^2;
eqn2:=x[2]^2*x[3] - x[3]^3 + 4*x[3]^2*x[4] - 12*x[3]*x[4]^2 + 12*x[4]^3;


// We claim that eqn1 and eqn2 define X in P^3 via the canonical 
// embedding.  To do this we will show that eqn1, eqn2 evaluated on the basis 
// of differentials B is identically 0.
// To do this we need to work to a precision that is at least equal to 
// the Hecke (=Sturm) bound.

k:=6; // this is the maximum of weights of eqn1, eqn2 evaluated at the cuspforms 
m:=225*(1+1/3)*(1+1/5);   // index of Gamma_0(225) = 360

hecke:=Ceiling(k*m/12);  // Hecke bound

Bexp:=[ qExpansion(f,hecke+10) : f in B];  // The differentials=cusp forms as 
					// power series to precision hecke+10.

assert Valuation(Evaluate(eqn1,Bexp)) ge hecke;
assert Valuation(Evaluate(eqn2,Bexp)) ge hecke;

X:=Curve(ProjectiveSpace(R),[eqn1,eqn2]);
assert IsSingular(X) eq false;
assert Genus(X) eq 4;

// This completes the proof that eqn1, eqn2 give a smooth model
// for X in P^3.

// We note following obvious involutions of X, which clearly commute.

a1:=iso<X->X | [ -x[1] ,  x[2] , x[3] , x[4] ] , [ -x[1] ,  x[2] , x[3] , x[4] ] >;

a2:=iso<X->X | [ x[1] , -x[2] , x[3] , x[4] ] , [ x[1] , -x[2] , x[3] , x[4] ] >;

// We can use MAGMA to show that these generated the automorphism
// group of X, but we shall not need that. However, it is clear
// that the function field of X can be written in the form
// L(sqrt(h1),sqrt(h2)), where L is the fixed field of the 
// group generated by a_1, a_2 (with structure \Z/2 x \Z/2),
// and h1,h2 \in L.
// By inspection we see that L is fact generated by w:=x[3]/x[4].
// Thus we can write h1, h2 as rational functions in w.

// A little manipulation of the defining equations for X shows that
//x[1]^2*x[3]= x[3]^3-2*x[3]^2*x[4]+5*x[3]*x[4]^2-4*x[4]^3;
//x[2]^2*x[3]= x[3]^3-4*x[3]^2*x[4]+12*x[3]*x[4]^2-12*x[4]^3;

// It is easy to see that X is isomorphic to the curve C
// given by
// C :  u^2=w(w-1)(w^2-w+4), v^2=w(w^3-4w^2+12w-12)
Qz<z>:=PolynomialRing(Rationals());
h1:=z*(z-1)*(z^2-z+4);
h2:=z*(z^3-4*z^2+12*z-12);
h3:=(z-1)*(z^2-z+4)*(z^3-4*z^2+12*z-12);
A3<u,v,w>:=AffineSpace(Rationals(),3);
C:=Curve(A3, [-u^2+Evaluate(h1,w), -v^2+Evaluate(h2,w)]);
// We check our hand calculations, that C and X are indeed isomorphic. 

K:=FunctionField(X);
phi:=map<X->C | [ K!(x[1]*x[3]/x[4]^2), K!(x[2]*x[3]/x[4]^2) , K!(x[3]/x[4])  ] >;

assert Genus(C) eq 4;
// Hence phi : X -> C is an isomorphism.

// Next we write down the j-map on X.
// This was 'guessed' by solving linear equations, as in for example
// the paper of Banwait and Cremona. However, we prove below the 
// correctness of our guess, by using the cusp forms.

j1:=x[3]^15 - 10*x[3]^14*x[4] + 45*x[3]^13*x[4]^2 - 115*x[3]^12*x[4]^3 + 
    155*x[3]^11*x[4]^4 - 54*x[3]^10*x[4]^5 + 185*x[3]^9*x[4]^6 - 
    2395*x[3]^8*x[4]^7 + 10465*x[3]^7*x[4]^8 - 27055*x[3]^6*x[4]^9 + 
    47072*x[3]^5*x[4]^10 - 56090*x[3]^4*x[4]^11 + 43405*x[3]^3*x[4]^12 - 
    19485*x[3]^2*x[4]^13 + 4020*x[3]*x[4]^14 - 132*x[4]^15;

j2:=x[3]^13 - 8*x[3]^12*x[4] + 25*x[3]^11*x[4]^2 - 35*x[3]^10*x[4]^3 + 
    5*x[3]^9*x[4]^4 + 94*x[3]^8*x[4]^5 - 467*x[3]^7*x[4]^6 + 
    1805*x[3]^6*x[4]^7 - 5175*x[3]^5*x[4]^8 + 9685*x[3]^4*x[4]^9 - 
    11216*x[3]^3*x[4]^10 + 7698*x[3]^2*x[4]^11 - 2715*x[3]*x[4]^12 + 
    315*x[4]^13;

j3:=x[3]^2-x[3]*x[4]-x[4]^2;


jNum:=1/8*(j1+j2*x[2]*x[3])^3;
jDen:=j3^15*x[4]^15;

// The map j: X --> X(1) is given by jNum/jDen. We prove the
// correctness of this shortly.


assert IsHomogeneous(jNum);
assert IsHomogeneous(jDen);

assert Degree(jNum) eq 45;
assert Degree(jDen) eq 45;


// Let g_1,..,g_4 be the basis for the space of cuspforms B
// above. Then \H --> X,  \tau :-> (f_1(q),..,f_4(q)) 
// parametrizes X (see above), where \H is the upper-half plane.
// Now we want to think of X as X(s3,s5), and not as
// X_0(225)/<w_9,w_{25}>. The isomorphism X_0(225)/<w_9,w_{25}>--> X
// pulled back to \H is given by \tau :-> 15 \tau.
// Thus the expansion \H -> X -> X(1) is given by j(q^{15})
// we j has the usual expansion. To verify the correctness of
// our 'guess', we must show that jNum(f_1,..,f_4)/jDen(f_1,..,f_4)=j(q^{15}).
// This is a relation between modular forms and so needs to checked
// only to a certain finite precision. Note that the relation is equivalent
// to 
// (E_4(q^15))^3 jDen(f_1,..,f_4) = Delta(q^15) jNum(f_1,..,f_4).
// Now both sides are cusp forms of level 225 and weight 12+45x2=102.

// Hecke bound= 102 x 360/12 = 3060  (360=225x4/3*6/5 is the index of
					// \Gamma_0(225) )

Qq<q>:=PowerSeriesRing(Rationals(),3500);
Bexp:=[ Qq!qExpansion(g,3400) : g in B];  // the differentials=cusp forms 
					// to a precision of 3400
j:=jInvariant(q^15);

assert Valuation(Evaluate(jNum,Bexp)-j*Evaluate(jDen,Bexp)) ge 3350; // Exceeds
								// the Hecke bounds.
// This completes the proof of the correctness of our claimed 
// X -> X(1).

j:=K!(jNum/jDen); // The j-invariant on X as an element of the function field.


// We now go through some sanity checks on the j-invariant.
// We shall make use of the ramification data for X_s(3) -> X(1)
// and X_s(5) -> X(1). These can be derived from the explicit
// formulae on page 68 of Chen's thesis.
// First we know that X_s(3) -> X(1) has degree 6,
// and X_s(5) -> X(1) has degree 15. Thus
// X -> X(1) must have degree 6 x 15 = 90.


assert Degree(j) eq 90; 

// X_s(3) has two points above \infty, both with ramification indices 3.
// X_s(5) has has three points above \infty, all have ramification index 5.
// Hence X must have 6 points above infinity, all having ramification index 15. 

P:=Poles(j);

assert &+[Degree(p) : p in P] eq 6; // The number points above infinity.
assert &and[Valuation(j,p) eq -15 : p in P]; // All have ramification index 15.

// X_s(3) has two points above 0, both with ramification indices 3.
// X_s(5) has has five points above 0, all have ramification index 3.
// Hence X must have 30 points above 0, all having ramification index 3. 

P:=Zeros(j);
assert &+[Degree(p) : p in P] eq 30; // The number points above 0.
assert &and[Valuation(j,p) eq 3 : p in P]; // All have ramification index 3.

// X_s(3) has two points above 1728 with ramification index 1
// and two with ramification index 2.
// X_s(5) has three points above 1728 with ramification index 1
// and six with ramification index 2.
// Hence X must have six points above 1728 with ramification index 1,
// and (2x3+6x2+6x2x2)=42 points with ramification index 2. 

P:=Zeros(j-1728);
P1:=[p : p in P | Valuation(j-1728,p) eq 1];
P2:=[p : p in P | Valuation(j-1728,p) eq 2];

assert Set(P) eq Set(P1) join Set(P2); // All points above 1728 have ramification index 1 or 2.
assert &+[Degree(p) : p in P1] eq 6; // The number points with ramification index 1.
assert &+[Degree(p) : p in P2] eq 42; // The number points with ramification index 2.


// This completes our first sanity check. 
// Here is a second sanity check. The map 
// X(s3) -> X(1) actually factors as
// X(s3) -> X(ns3) -> X(1) where the first have degree 2 and the second
// is given by j=n^3, where n is a Hauptmodul on X(ns3) (Chen's thesis page 68).
// Thus j must be a cube in the function field of X=X(s3,s5).
// This is clear from the formulae for jNum and jDen above! 
// In particular, X is a double cover of X(ns3, s5). 
// It is easy to write down a model for the latter. By Chen, page 68,
// X(s5) -> X(1) is given by
//        (s^2-5)^3 (s^2+5s+10)^3 (s+5)^3
//    j= ---------------------------------
//                 (s^2+5s+5)^5
// Equating this with j=n^3, we obtain the following model for X(ns3,s5) 
//        X(ns3,s5)    :   s^2+5s+5=m^3
// where m is a rational function of s and n.

E:=EllipticCurve([0,0,5,0,-5]);  // X(ns3,s5)

// Let us verify that X is a double cover of this.
// Recall (see above ) that X is isomorphic to C, which is given by
// C :  u^2=w(w-1)(w^2-w+4), v^2=w(w^3-4w^2+12w-12)

// Clearly C is a double cover of the curve given by the second equation:

D2:=HyperellipticCurve(z*(z^3-4*z^2+12*z-12));  // v^2=w(w^3-4w^2+12w-12)

_<t,s>:=FunctionField(E);

psi:=map<E->D2 | [ (t-2-s)/(t+1), (-t^3-3*t^2+5+s)/(t+1)^2 ,  1    ]>;

assert Degree(psi) eq 1;

// Hence psi : E-->D2 is an isomorphism, and so X \cong C
// is really a double cover of X(ns3,s5).

// In particular, j : X--> X(1) should factor through X(ns3,s5).
// Hence it should be possible to check that the expression
// for j thought of a function on C, involves only v,w (not u).

// We now give this expression for j as a function on C:

_<u,v,w>:=AmbientSpace(C);
jC1:=    w^15 - 10*w^14 + 45*w^13 - 115*w^12 + 155*w^11 - 54*w^10 + 185*w^9 - 
        2395*w^8 + 10465*w^7 - 27055*w^6 + 47072*w^5 - 56090*w^4 + 43405*w^3 - 
        19485*w^2 + 4020*w - 132;
jC2:=    w^13 - 8*w^12 + 25*w^11 - 35*w^10 + 5*w^9 + 94*w^8 - 467*w^7 + 1805*w^6 - 
        5175*w^5 + 9685*w^4 - 11216*w^3 + 7698*w^2 - 2715*w + 315;
jC3:= w^2-w-1;

jC:=FunctionField(C)!(1/8*(jC1+jC2*v)^3/jC3^15);


assert j eq Pullback(phi,jC); // Recall phi is the isomorphism X -> C.
			      // Thus the expression jC really gives
				// the j-map C -> X(1).
				// By expressions
				// for jC1, jC2, jC3 only involve w
				// and jC therefore only involves
				// w and v. Hence it is a function
				// of X(ns3,s5) as expected.

// This completes our sanity checks!

// Next we write down the quadratic points on C.
// The curve C has the following obvious quotients:
// (1) The genus 1 curve D2 above, which is isomorphic to
assert CremonaReference(E) eq "225a1";
// the elliptic curve E with Cremona reference "225a1"
assert Rank(E) eq 1;
assert #TorsionSubgroup(E) eq 1;
// whose Mordell--Weil group is free of rank 1.

// Note as C is a double cover of D2, we see that C has infinitly
// many quadratic points. We want the quadratic points
// on C whose image in D is not a rational point.

// (2) The curve

D3:=HyperellipticCurve((z-1)*(z^2-z+4)*(z^3-4*z^2+12*z-12)); 
assert Genus(D3) eq 2;
mu:=map<C->D3 | [w^2, u*v*w^2,w]>;
J:=Jacobian(D3);
assert RankBound(J) eq 0;
T,eps:=TorsionSubgroup(J);
assert #T eq 10;
// We now write down a generator for the Mordell--Weil group of J.

pt:=J![z^2-z-1,5*z-10];

assert Order(pt) eq 10;
// Thus pt generates J(\Q)

// Next we write down the rational points on D3.

pts:=Set(Chabauty0(J));
assert pts eq {D3![1,1,0], D3![1,-1,0], D3![1,0,1]};

ptsJ:=[eps(t) : t in T]; // The 10 rational points on J

ptsQuad:=[ t : t in ptsJ | Degree(t[1]) eq 2 and IsIrreducible(t[1])];
			// We keep only the ones of the form
			// P+conj(P)-\inf_{+}-\inf_{-}
			// where P is a quadratic point.

KH<xH,yH>:=FunctionField(D3);

quadPlaces:=&join[Set(Zeros(D3,Evaluate(t[1],xH))) : t in ptsQuad]; // These are all the 
					// quadratic points on D3.


// The rational and quadratic points on D3,
// apart from the preimage of P^1
ratAndQuadPlaces:={Place(p) : p in pts} join quadPlaces;

// We now pull these back to C

pullsC:=&cat[Support(Pullback(mu,p)) : p in ratAndQuadPlaces];


// We only keep the ones which are rational or quadratic.
pullsC:=[ p : p in pullsC | Degree(p) in {1,2}];

// Any quadratic point on C that is not in this
// list must have rational w-coordinate, and u*v must be irrational.
// We now consider the third quotient.

// (3) The third quotient is the curve

D1:=HyperellipticCurve(z*(z-1)*(z^2-z+4));
mu1:=map<C->D1 | [w, u, 1]>;
E1,pi1:=EllipticCurve(D1);

assert CremonaReference(E1) eq "15a8";
assert Rank(E1) eq 0;
T:=TorsionSubgroup(E1);
assert #T eq 4; // Thus E1 and so D1 has four rational points.
// This must be the complete list:
ptsD1:=[ D1![1 , -1 , 0], D1![1 , 1 , 0], D1![0 , 0] , D1![1 , 0 ]];

// These pullback to points on C already on our list,
// except for (0,0) which pulls back to (0,0,0)

pullsC:=pullsC cat Places(C![0,0,0]);

// Any quadratic point not in pullsC must have
// rational w coordinate, and u*v is irrational and u is irrational.
// Hence v must be rational. Thus (w,v) is a rational point on D2.
// Also jC is a function of w and v. Hence the value of jC
// is rational. Thus all these points (if they are non-cuspidal
// and real) must be modular!


// Finally for the points in pullsC, we note that their
// j-invariants are rational.


for pt in pullsC do
	print Evaluate(jC,pt);
end for;

