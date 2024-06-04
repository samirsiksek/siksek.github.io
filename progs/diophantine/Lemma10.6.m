// This Magma script verifies the computations described
// in the proof of Lemma 10.6.

L<zet>:=CyclotomicField(13);
Kp:=Subfields(L,3)[1,1]; // K' which is the unique subfield of Q(zeta_{13})
			// of degree 3. 

print "We will be doing computations with certain modular curves over the field", Kp;

print "This is the unique cubic subfield of Q(zeta_{13})";



// Computations for X_0(14).

E:=SmallModularCurve(14);  // X_0(14)
print "The modular curve X_0(14) is the elliptic curve",

E;

print "with Cremona label", CremonaReference(E);


EKp:=BaseChange(E,Kp);

A,phi:=MordellWeilGroup(EKp);

assert IsIsomorphic(A,AbelianGroup([6])); // The Mordell--Weil group
					// E(Kp) is \Z/6\Z.

pts:=[phi(a) : a in A];

print "Points on X_0(14) over K^prime are", pts;

cusps:=&cat[CuspPlaces(EKp,14,d) : d in Divisors(14)];

print "The cusps of X_0(14) are",

cusps;

noncusps:=[P : P in pts | Place(P) in cusps eq false];

print "The non-cuspidal points on X_0(14) over K^prime are", noncusps;

print "These have j-invariants",

[jInvariant(P,14) : P in noncusps];

// Computations for X_0(11).

E:=SmallModularCurve(11);  // X_0(11)
print "The modular curve X_0(11) is the elliptic curve",

E;

print "with Cremona label", CremonaReference(E);


EKp:=BaseChange(E,Kp);

A,phi:=MordellWeilGroup(EKp);

assert IsIsomorphic(A,AbelianGroup([5])); // The Mordell--Weil group
					// E(K) is \Z/5\Z.

pts:=[phi(a) : a in A];

print "Points on X_0(11) over K^prime are", pts;

cusps:=&cat[CuspPlaces(EKp,11,d) : d in Divisors(11)];

print "The cusps of X_0(11) are",

cusps;

noncusps:=[P : P in pts | Place(P) in cusps eq false];

print "The non-cuspidal points on X_0(11) over K^prime are", noncusps;

print "These have j-invariants",

[jInvariant(P,11) : P in noncusps];

// Computations for X_0(20).

print "Now we check the claim made in the proof that
every point on X_0(20) over Q(zeta_{13})^+
is in fact defined over Q(sqrt{13})";

print "   ";

E:=SmallModularCurve(20);  // X_0(20)
print "The modular curve X=X_0(20) is the elliptic curve",

E;

print "with Cremona label", CremonaReference(E);


EKp:=BaseChange(E,Kp);

A,phi:=MordellWeilGroup(EKp);

assert IsIsomorphic(A,AbelianGroup([6])); // The Mordell--Weil group
					// E(Kp) is \Z/6\Z.

pts:=[phi(a) : a in A];

print "Points on X_0(20) over K^prime are", pts;

EKptwist:=QuadraticTwist(EKp,13);

print "The quadratic twist of E by 13 is",

EKptwist;

A,phi:=MordellWeilGroup(EKptwist);

assert IsIsomorphic(A,AbelianGroup([2,0])); // The Mordell--Weil group
					// E(Kp) is \Z/2+\Z.
print "The Mordell--Weil group of this twist over K^prime is",
A;

print "The generators are", phi(A.1), phi(A.2);

print "Thus if P belongs to X(K) then P+P^sigma and P-P^sigma
	both belong to X(Q(sqrt{13}))";

print "Thus 2P belongs to X(Q(sqrt{13}})";

print "As the extension K/Q(sqrt{13}) is cubic, and the equation
	2P=R has four solutions, it follows that 2P=2Q
	where Q belongs to X(Q(sqrt{13}))";

print "To see that P belongs to X(Q(sqrt{13})), it is
	enough to observe that X has full 2-torsion
	already over the rationals.";
