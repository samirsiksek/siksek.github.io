// This Magma script verifies the computations described
// in the proof of Lemma 10.4.

L<zet>:=CyclotomicField(7);
K<t>:=sub<L | zet+1/zet>; // Q(zeta_7)^+

// Computations for X_0(20).


E:=SmallModularCurve(20);  // X_0(20)
print "The modular curve X_0(20) is the elliptic curve",

E;

print "with Cremona label", CremonaReference(E);


EK:=BaseChange(E,K);

A,phi:=MordellWeilGroup(EK);

assert IsIsomorphic(A,AbelianGroup([6])); // The Mordell--Weil group
					// E(K) is \Z/6\Z.

pts:=[phi(a) : a in A];

print "Points on X_0(20) over Q(zeta_7)^+ are", pts;

print "The cusps of X_0(20) are",

&cat[CuspPlaces(EK,20,d) : d in Divisors(20)];

print "Thus every Q(zeta_7)^+ point on X_0(20) is a cusp.";

// Computations for X_0(11).

E:=SmallModularCurve(11);  // X_0(11)
print "The modular curve X_0(11) is the elliptic curve",

E;

print "with Cremona label", CremonaReference(E);


EK:=BaseChange(E,K);

A,phi:=MordellWeilGroup(EK);

assert IsIsomorphic(A,AbelianGroup([5])); // The Mordell--Weil group
					// E(K) is \Z/5\Z.

pts:=[phi(a) : a in A];

print "Points on X_0(11) over Q(zeta_7)^+ are", pts;

cusps:=&cat[CuspPlaces(EK,11,d) : d in Divisors(11)];

print "The cusps of X_0(11) are",

cusps;

noncusps:=[P : P in pts | Place(P) in cusps eq false];

print "The non-cuspidal points on X_0(11) over Q(zeta_7)^+ are", noncusps;

print "These have j-invariants",

[jInvariant(P,11) : P in noncusps];

