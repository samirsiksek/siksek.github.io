
// We write down a model for X(e7)
// and the associated j: X(e7) -> X(1).



// X(e7) is the modular curve associated to the subgroup H_2 (say) of
// GL_2(\F_7) generated by the two matrices
//  [0  5]              [5  0]
//  [3  0]              [3  2]

load "gl.m";
G:=GL(2,7); // GL_2(\F_7)

H2:=sub<G | [G![0,5,3,0], G![5,0,3,2]]>; 
assert isSurjective(H2); // From gl.m
			// Thus X(e7) is defined over \Q

H:=H2 meet SL(2,7);
assert G![-1,0,0,-1] in H;


// Following Ligozat
// "Courbes Modulaires de Niveau 11", Antwerp V
// page 191
muH:=Index(SL(2,7),H);  // This gives us the degree of X-->X(1)
assert muH eq 42;

assert IsDivisibleBy(Order(H),7) eq false;
// 7 does not divide the order of H.
// In this case H/{\pm I} acts freely on the cusps.

einfH:=muH div 7; // The number of cusps=6

e2H:=(7+1)*#{h : h in H | Trace(h) eq 0}/Order(H);
// The number of elliptic points of order 2.

assert e2H eq 2;


e3H:=(7-1)*#{h : h in H | Trace(h) eq -1}/Order(H);
// The number of elliptic points of order 3.

assert e3H eq 0;

gen:=1+(muH/12)-(e2H/4)-(e3H/3)-(einfH/2);

assert gen eq 1;

// Therefore X(e7) has genus 1.
// From the above we deduce the following ramification data for
// X(e7)--> X(1) :
// (a) Above 0 there are zero (=e3H) points with ramification index 1
//     and (42-0)/3=14 points with ramification index 3.
// (b) Above 1728 there two (=e2H) points with ramification index 1
//     and (42-2)/2=20 points with ramification index 2.
// (c) Above \infty there are 6 points of ramification index 42/6=7.

_,C:=nonSplitCartan(7);  // from gl.m
			// C is the normalizer of the non-split Cartan subgroup.

assert isContained(H2,C);
assert #(C meet SL(2,7))/#H eq 2;

// Thus X(e7) is a double cover of X(ns7). 


Qx<x>:=PolynomialRing(Rationals());

// Following Imin Chen's thesis, page 68:
// X(ns7) has genus 0
// x is a Hauptmodul for X(ns7)
// j=num/den is the map X(ns7) -> X(1):
num:=(4*x^2+5*x+2)^3*(x^2+3*x+4)^3*(x^2+10*x+4)^3*(3*x+1)^3;
den:=(x^3+x^2-2*x-1)^7;

assert Degree(num) eq 21;
assert Degree(den) eq 21; 

// Note that X(ns7) -> X(1) has degree 21=42/2 as expected.

assert num-1728*den eq 
	49*(16*x^4 + 68*x^3 + 111*x^2 + 62*x + 11)*
	(9*x^4 + 26*x^3 + 34*x^2 + 20*x + 4)^2*
	(x^4 + 6*x^3 + 17*x^2 + 10*x + 2)^2;

// The factorisation of num-1728*den tells us about the 
// ramification above 1728, just as the factorisations
// of num and den tell us about the ramification above 0 and \infty.
// We deduce the following ramification data for X(ns7) -> X(1):

// (A) Above 0 there are seven points of ramification index 3.
// (B) Above 1728 there are eight points of ramification index 2
//     five of ramification index 1
//     (one of these is \infty, since num-1728*den has degree 20)
// (C) Above \infty there are three points of ramification index 7.

// Comparing (a) with (A), (b) with (B), and (c) with (C),
// we see that all places of X(s7) above 0, 1728 and \infty split
// in X(e7) -> X(ns7) except for the four points above 1728
// with ramification index 1, which must ramify in X(e7) -> X(ns7).
// There are five points on X(ns7) above 1728 with ramification
// index 1. But the set of four that ramify must be stable under Galois.
// Thus they correspond to the factor 
// 16*x^4 + 68*x^3 + 111*x^2 + 62*x + 11 of num-1728*den;
// Hence an equation for X(e7) has the form
// y^2=c(16*x^4 + 68*x^3 + 111*x^2 + 62*x + 11)
// for some squarefree integer c.
// X(e7) has a model of \Z[1/7]. We will use this fact to narrow
// down the possibilities for c.

Qc<c>:=PolynomialRing(Rationals());
Qcx<x>:=PolynomialRing(Qc);
Dc:=HyperellipticCurve(c*(16*x^4 + 68*x^3 + 111*x^2 + 62*x + 11));
delta:=Discriminant(Jacobian(GenusOneModel(Dc))); // The discriminant
						// of the Jacobian elliptic
						// curve of Dc
assert delta eq 2^12*7^3*c^6;
// If p \mid c, and p \ne 7 then it is clear (from the discriminant)
// that the minimal model of the Jacobian elliptic curve of Dc 
// has bad reduction at p. Hence c=\pm 1, \pm 7.

Qx<x>:=Parent(num);

// Try c=1
c:=1;
Dc:=HyperellipticCurve(c*(16*x^4 + 68*x^3 + 111*x^2 + 62*x + 11));
delta:=Discriminant(MinimalModel(Jacobian(GenusOneModel(Dc))));

assert Valuation(delta,2) eq 12; // Minimal model of Jacobian
				// has bad reduction at 2.
// Thus c \ne 1.


// Try c=-7
c:=-7;
Dc:=HyperellipticCurve(c*(16*x^4 + 68*x^3 + 111*x^2 + 62*x + 11));
delta:=Discriminant(MinimalModel(Jacobian(GenusOneModel(Dc))));

assert Valuation(delta,2) eq 12; // Minimal model of Jacobian
				// has bad reduction at 2.

// Thus c \ne -7

// Try c=-1
c:=-1;
Dc:=HyperellipticCurve(c*(16*x^4 + 68*x^3 + 111*x^2 + 62*x + 11));
delta:=Discriminant(MinimalModel(Jacobian(GenusOneModel(Dc))));

assert Valuation(delta,2) eq 0; // Minimal model of Jacobian
				// has good reduction at 2.

// We are unable to eliminate the possibility c=1
// by looking at the reduction modulo 2.
// However,

assert #Roots(16*x^4 + 68*x^3 + 111*x^2 + 62*x + 11, RealField()  ) eq 0; 

// the hyperelliptic polynomial does not have real roots.
// Thus Dc does not have real points with c=-1.
// However if E is any real elliptic curve, then
// \overline{\rho}_{E/\R,7} consists of a subgroup
// of GL_2(\F_7) of order 2. We now show that all
// such subgroups are contained in H2 (up to conjugation).

subs:=Subgroups(GL(2,7) : OrderEqual:=2);
subs:=[K`subgroup : K in subs]; // all subgroups of GL_2(\F_7) of order 2.

assert &and[isContained(K,H2) : K in subs]; // They are all contained in H2
					// up to conjugation.

// Thus X(d7) has a real point corresponding to E/\R.
// It follows that c \ne -1. The only remaining possibility
// for c is 7. Thus X(e7) is given by


D7:=HyperellipticCurve(7*(16*x^4 + 68*x^3 + 111*x^2 + 62*x + 11));
pt1:=D7![-1/3,14/9];
pt2:=D7![-1/3,-14/9];

E:=MinimalModel(EllipticCurve(D7,pt1));
assert CremonaReference(E) eq "49a4";
assert Rank(E) eq 0;
assert #TorsionSubgroup(E) eq 2;

// Hence D7 has exactly two rational points pt1, pt2.
// Clearly J(\Q)=\Z/2 \cdot [pt1-pt2] 
// where J is the Jacobian of D7.
// Finally we compute the j-invariants of the two points pt1,pt2 

j:=Evaluate(num,-1/3)/Evaluate(den,-1/3);

assert j eq 0;
