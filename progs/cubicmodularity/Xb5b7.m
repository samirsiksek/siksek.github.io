// We verify the computations in Section 5 of the paper.
// Precisely, we prove that $X(b5,b7)(K)$ consists of only of cusps,
// for any totally real cubic field $K$.

Qx<x>:=PolynomialRing(Rationals());

X:=SmallModularCurve(35);  // X_0(35) over Q --- this is the model given by the "Small Modular Curves" package.

cusps:=&cat[CuspPlaces(X,35,d) : d in Divisors(35)];  // the cusps on X_0(35).

assert #cusps eq 4;
assert &and[Degree(P) eq 1 : P in cusps];  // MAGMA gives the cusps as places
				// this verifies that they're rational points
				// This must be true as 35 is squarefree
				// and has precisely four divisors.

assert #NonCuspidalQRationalPoints(X,35) eq 0;  // all rational points on X_0(35)
						// are cuspidal
						


// The Model for X(b5,b7) given in Galbraith's thesis, Section 4.4.
Y:=HyperellipticCurve((x^2 + x - 1)*(x^6 - 5*x^5 - 9*x^3 - 5*x - 1));

tf,phi:=IsIsomorphic(X,Y);
assert tf;   // Y is a model for X(b5,b7)



cusps:={Pushforward(phi,c) : c in cusps}; // the cusps on the model Y

ptsY:= [ Y![1 , 1 , 0], Y![1 , -1 , 0], Y![0 , -1 , 1], Y![0 , 1 , 1]];

// four points on Y found by a short search

assert cusps eq {Place(p) : p in ptsY}; // checking that the 
					// four points are precisely 
					//the cusps
					// which they must be as Y and X
					// are isomorphic.

// We now verify the information about the Mordell--Weil group of
// J_0(35) which is quoted from the paper of Freitas, Le Hung and Siksek.


p0:=ptsY[1];  // inf_+: we use as base point for the Abel-Jacobi map
		// Y -> J.

J:=Jacobian(Y);

ptsJ:=[ p-p0 : p in ptsY   ]; // image of the 4 pts under the Abel-Jacobi map

assert &and[24*Q eq J!0 : Q in ptsJ]; // Check that all the points are torsion.
				// Of course the cuspidal
				// subgroup is contained in the torsion subgroup.

assert BadPrimes(J) eq [2,5,7];

// we now determine the structure of the cuspidal subgroup
// using the fact that the torsion subgroup injects
// into J(\F_3)

J3:=BaseChange(J,GF(3));
B,mu:=AbelianGroup(J3);
A:=FreeAbelianGroup(4);
eps:=hom<A->B | [ (J3!Q)@@mu : Q in ptsJ  ] >;
C:=Image(eps);  // injective image of the cuspidal subgroup in J(\F_3).


// We now write down two elements Q1, Q2 of the cuspidal subgroup
// and show that they're a basis for it
Q1:=ptsJ[2]; // inf_{-} - inf_{+}.
Q2:=3*ptsJ[3]; // 3(0,-1) - 3 inf_{-}.

mu1:=(J3!Q1)@@mu; 
mu2:=(J3!Q2)@@mu;


cuspGp:=AbelianGroup([24,2]);
delta:=hom<cuspGp->C | [mu1,mu2]>;
assert #Kernel(delta) eq 1; 
assert Image(delta) eq C; // Thus the cuspidal subgroup
			// is (Z/24)Q1 \oplus (Z/2)Q2.

assert #J3 eq 48;
// Thus the cuspidal group is equal to the torsion subgroup.

cuspGpElts:={a*Q1+b*Q2 : a in [0..23], b in [0..1]};
assert #cuspGpElts eq 48;

TS:=TwoSelmerGroup(J);

assert IsIsomorphic(TS,AbelianGroup([2,2]));
// The 2-Selmer group is isomorphic to Z/2 \times Z/2
// thus J(Q)=torsion subgroup=cuspidal subgroup. 
// We have now verified that J(Q) = (Z/24Z) Q1 oplus (Z/2Z) Q2.

D1:=Place(ptsY[2])-Place(ptsY[1]);
D2:=3*Place(ptsY[3])-3*Place(ptsY[1]);  // D1 and D2 are Q1, Q2 above
					// in the language of degree 0 divisors.

infdiv:=3*Place(ptsY[1]);  // The divisor at infinity.

deg3:=[a*D1+b*D2+infdiv : a in [0..23], b in [0..1]];
					// Every rational divisor of
					// degree 3 is linearly equivalent to 
					// one of these.

assert #deg3 eq 48;
assert &and[Degree(D) eq 3 : D in deg3];

// Let D be a degree 3 divisor on Y. What are the possibilities for l(D)?
// By Riemann-Roch l(D)-l(K-D)=deg(D)-g+1=1.
// If l(K-D)=0 then l(D)=1.
// Suppose l(K-D) \ge 1. Thus D is special. By Clifford's Inequality 
// l(D) \le deg(D)/2+1=5/2. Thus l(D)=2.
// Let's check this.

assert &and[Dimension(RiemannRochSpace(D)) in [1,2] : D in deg3];

// We know that if l(D)=2 then |D| has a base point and so every divisor
// in the linear system is a reducible divisor. Thus we pick out D in deg3
// such that l(D)=1.

deg3:=[ D : D in deg3 | Dimension(RiemannRochSpace(D)) eq 1];
			// Every effective irreducible rational divisor of degree 3
			// is linearly equivalent to one of these.

assert #deg3 eq 44;

deg3new:=[];
for D in deg3 do
	L,mu:=RiemannRochSpace(D);
	assert Dimension(L) eq 1;
	D1:=D+Divisor(mu(L.1)); //  This is the unique effective divisor linearly equivalent to D;
	assert IsEffective(D1);
	decomp:=Decomposition(D1);
	if #decomp eq 1 and decomp[1,2] eq 1 then // This means that D1 is irreducible.
		Append(~deg3new,decomp[1,1]);
	end if;
end for;

assert #deg3new eq 28; // deg3new is the set of effective irreducible degree 3 divisors.

for D in deg3new do
	K:=ResidueClassField(D);
	assert IsNumberField(K);
	assert Degree(K) eq 3;
	assert IsTotallyReal(K) eq false;
	assert Discriminant(K) lt 0; // For a cubic field, this is equivalent to having a complex embedding!
end for;

// Thus Y has no totally real degree 3 points that are not already rational points.

