// This Magma script verifies the computations described
// in the proof of Lemma 10.5.

L<zet>:=CyclotomicField(11);
K<t>:=sub<L | zet+1/zet>; // Q(zeta_{11})^+

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

print "Points on X_0(20) over Q(zeta_{11})^+ are", pts;

print "The cusps of X_0(20) are",

&cat[CuspPlaces(EK,20,d) : d in Divisors(20)];

print "Thus every Q(zeta_{11})^+ point on X_0(20) is a cusp.";

// Computations for X_0(14).

E:=SmallModularCurve(14);  // X_0(14)
print "The modular curve X_0(14) is the elliptic curve",

E;

print "with Cremona label", CremonaReference(E);


EK:=BaseChange(E,K);

A,phi:=MordellWeilGroup(EK);

assert IsIsomorphic(A,AbelianGroup([6])); // The Mordell--Weil group
					// E(K) is \Z/6\Z.

pts:=[phi(a) : a in A];

print "Points on X_0(14) over Q(zeta_{11})^+ are", pts;

cusps:=&cat[CuspPlaces(EK,14,d) : d in Divisors(14)];

print "The cusps of X_0(14) are",

cusps;

noncusps:=[P : P in pts | Place(P) in cusps eq false];

print "The non-cuspidal points on X_0(14) over Q(zeta_{11})^+ are", noncusps;

print "These have j-invariants",

[jInvariant(P,14) : P in noncusps];

// Computations for X_0(19).

E:=SmallModularCurve(19);  // X_0(19)
print "The modular curve X_0(19) is the elliptic curve",

E;

print "with Cremona label", CremonaReference(E);


EK:=BaseChange(E,K);

A,phi:=MordellWeilGroup(EK);

assert IsIsomorphic(A,AbelianGroup([3])); // The Mordell--Weil group
					// E(K) is \Z/3\Z.

pts:=[phi(a) : a in A];

print "Points on X_0(19) over Q(zeta_{11})^+ are", pts;

cusps:=&cat[CuspPlaces(EK,19,d) : d in Divisors(19)];

print "The cusps of X_0(19) are",

cusps;

noncusps:=[P : P in pts | Place(P) in cusps eq false];

print "The non-cuspidal points on X_0(19) over Q(zeta_{11})^+ are", noncusps;

print "These have j-invariants",

[jInvariant(P,19) : P in noncusps];

