
// Want to prove the modularity of elliptic curves defined over
// K=\Q(\sqrt{5}). For this it is enough to show that the non-cuspidal
// K-points on the following modular curves are modular:


// X(d7)
// X(e7)
// X(b3,b7) = X_0(21)
// X(s3,b7) = X_0(63)/w_9

Qx<x>:=PolynomialRing(Rationals());
K<t>:=NumberField(x^2-5);

// =============================================================

// X(d7) over K=Q(\sqrt{5})

X:=HyperellipticCurve(-7*(x^4 - 10*x^3 + 27*x^2 - 10*x - 27));
// This is the curve X=X(d7) (see the file Xd7.m)
pt1:=X![5/2,7/4];
pt2:=X![5/2,-7/4];
// where we showed that the only two rational points on X are these.

E:=MinimalModel(EllipticCurve(X,pt1)); // A minimal Weierstrass
					// model obtained by sending pt1
					// to infinity.

assert CremonaReference(E) eq "49a3"; 
assert Rank(E) eq 0;
assert #TorsionSubgroup(E) eq 2; // Confirming that X has exactly two rational
				// points.

assert Rank(QuadraticTwist(E,5)) eq 0; // Hence Rank(E/K)=0.

EK:=ChangeRing(E,K);
assert #TorsionSubgroup(EK) eq 2;

// Thus E(K) consists of two points. These are the two
// rational points on E! Thus X(K)=X(\Q).
// So all the K-points on X(d7) are modular.

//=========================================================

// X(e7) over K=\Q(\sqrt{5})


X:=HyperellipticCurve(7*(16*x^4 + 68*x^3 + 111*x^2 + 62*x + 11));
// This is the curve X=X(e7) (see the file Xe7.m)
pt1:=X![-1/3,14/9];
pt2:=X![-1/3,-14/9];
// where we showed that the only two rational points on X are these.

E:=MinimalModel(EllipticCurve(X,pt1)); // A minimal Weierstrass
					// model obtained by sending pt1
					// to infinity.

assert CremonaReference(E) eq "49a4"; 
assert Rank(E) eq 0;
assert #TorsionSubgroup(E) eq 2; // Confirming that X has exactly two rational
				// points.

assert Rank(QuadraticTwist(E,5)) eq 0; // Hence Rank(E/K)=0.

EK:=ChangeRing(E,K);
assert #TorsionSubgroup(EK) eq 2;

// Thus E(K) consists of two points. These are the two
// rational points on E! Thus X(K)=X(\Q).
// So all the K-points on X(e7) are modular.

// ===================================================

// X(b3,b7) over K=\Q(\sqrt{5})

X:=SmallModularCurve(21);  // X_0(21)=X(b3,b7)
assert CremonaReference(X) eq "21a1";
assert Rank(X) eq 0;
assert Rank(QuadraticTwist(X,5)) eq 0; // Hence rank(X/K) =0

XK:=ChangeRing(X,K);
assert IsIsomorphic(TorsionSubgroup(X),AbelianGroup([2,4]));
assert IsIsomorphic(TorsionSubgroup(XK),AbelianGroup([2,4]));
// Thus: all K-points on X are in fact \Q-points
// and the Mordell--Weil group is isomorphic to \Z/2 \times \Z/4
T,phi:=TorsionSubgroup(X);
T:=[phi(t) : t in T];  // all the K-points on X_0(21)
assert #T eq 8;

cusps:=&cat[CuspPlaces(X,21,d) : d in [1,3,7,21]];
noncusps:=[p : p in T | Place(p) notin cusps];
assert #noncusps eq 4;

jinvs:=[jInvariant(p,21) : p in noncusps];
assert Set(jinvs) eq { -189613868625/128, 3375/2, -1159088625/2097152, -140625/8 };

// Since all the j-invariants of the K-points are rational,
// they are already known to be modular.

// =================================================================


// X=X(s3,b7)=X_0(63)/w_9 over K=\Q(\sqrt{5})
// We shall not determine all the K-points on X.
// Instead we consider Y=X_0(63)/<w_9,w_7>. This is quotient
// of X. We show that this quotient is precisely
// the elliptic curve 21A1. Since all the K-points
// on 21A1 are \Q-points (see above), the image of
// X(K) ---> Y(K)
// belongs to Y(\Q). Thus any point K-point on X
// is related to its conjugate by w_7. It follows that
// it corresponds to a \Q-curve, and hence is modular. 

X063:=SmallModularCurve(63);
p0:=X063![0,1,0];
assert Genus(X063) eq 5;
w9:=AtkinLehnerInvolution(X063,63,9);
w7:=AtkinLehnerInvolution(X063,63,7);
Y:=CurveQuotient(AutomorphismGroup(X063,[w7,w9])); // X_0(63)/<w_7,w_9>
assert Genus(Y) eq 1;


X,toX:=CurveQuotient(AutomorphismGroup(X063,[w9]));  // X(s3,b7)=X_0(63)/w_9
assert IsHyperelliptic(X) eq true;
assert Genus(X) eq 3;  // which is a genus 3 hyperelliptic curve.
A,mu:=AutomorphismGroup(X);
A:=[mu(a) : a in A];
A:=[ a : a in A | Genus(CurveQuotient(AutomorphismGroup(X,[a]))) eq 1];
assert #A eq 1;
a:=A[1];  // a must be w_7
Y,pi:=CurveQuotient(AutomorphismGroup(X,[a])); //Y= X_0(63)/<w_7,w_9>
p1:=pi(toX(p0));
E,psi:=EllipticCurve(Y,p1);
assert CremonaReference(E) eq "21a1";  // Y is isomorphic 21A1 

assert Rank(E) eq 0;
assert Rank(QuadraticTwist(E,5)) eq 0;
assert IsIsomorphic(TorsionSubgroup(E),AbelianGroup([2,4]));
EK:=ChangeRing(E,K);
assert IsIsomorphic(TorsionSubgroup(EK),AbelianGroup([2,4])); 

// Thus every K-point on E (and hence Y) is a \Q-point. This completes
// the proof.

