
// We show that all non-cuspidal real quadratic points
// on X=X(b5,b7) are modular.

X:=SmallModularCurve(35);  // X_0(35) over Q

cusps:=&cat[CuspPlaces(X,35,d) : d in Divisors(35)];  // the cusps on X_0(35)

assert #cusps eq 4;
assert &and[Degree(P) eq 1 : P in cusps];  // MAGMA gives the cusps as places
				// this verifies that they're rational points
				// This must be true as 35 is squarefree
				// and has precisely four divisors.

assert #NonCuspidalQRationalPoints(X,35) eq 0;  // all rational points on X_0(35)
						// are cuspidal
						


// The Model for X(b5,b7) given in Galbraith's thesis, Section 4.4.
Qx<x>:=PolynomialRing(Rationals());
Y:=HyperellipticCurve(x^8 - 4*x^7 - 6*x^6 - 4*x^5 - 9*x^4 + 4*x^3 - 6*x^2 + 4*x + 1);

tf,phi:=IsIsomorphic(X,Y);
assert tf;   // Y is a model for X(b5,b7)



cusps:={Pushforward(phi,c) : c in cusps}; // the cusps on the model Y

ptsY:= [ Y![1 , 1 , 0], Y![1 , -1 , 0], Y![0 , -1 , 1], Y![0 , 1 , 1]];

// four points on Y found by a short search

assert cusps eq {Place(p) : p in ptsY}; // checking that the 
					// four points are precisely 
					//the cusps
					// which they must be as Y and X
					// are isomorphic


p0:=ptsY[1];  // inf_+: we use as base point for the Abel-Jacobi map
		// Y -> J

J:=Jacobian(Y);

ptsJ:=[ p-p0 : p in ptsY   ]; // image of the 4 pts under the Abel-Jacobi map

assert &and[24*Q eq J!0 : Q in ptsJ]; // Check that all the points
				// are torsion.
				// Of course the cuspidal
				// subgroup is contained.

assert BadPrimes(J) eq [2,5,7];

// we now determine the structure of the cuspidal subgroup
// using the fact that the torsion subgroup injects
// into J(\F_3)

J3:=BaseChange(J,GF(3));
B,mu:=AbelianGroup(J3);
A:=FreeAbelianGroup(4);
eps:=hom<A->B | [ (J3!Q)@@mu : Q in ptsJ  ] >;
C:=Image(eps);  // injective image of the cuspidal subgroup in J(\F_3)


// we now write down two elements Q1, Q2 of the cuspidal subgroup
// and show that they're a basis for it
Q1:=ptsJ[2]; // inf_{-} - inf_{+}
Q2:=3*ptsJ[3];

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

D1:=Place(ptsY[2])-Place(ptsY[1]);
D2:=3*Place(ptsY[3])-3*Place(ptsY[1]);  // D1 and D2 are Q1, Q2 above
					// in the language of degree 0 divisors.

infdiv:=Place(ptsY[1])+Place(ptsY[2]);  // The divisor at infinity.

deg2:=[a*D1+b*D2+Place(ptsY[1])+Place(ptsY[2]) : a in [0..23], b in [0..1] | a ne 0 or b ne 0];
					// Every rational divisor of
					// degree 2 is linearly equivalent to 
					// one of these, unless it is linearly
					// equivalent to inf_{+} + inf_{-}

deg2:=[ D : D in deg2 | Dimension(RiemannRochSpace(D)) ge 1];
			// Every effective rational divisor of degree 2
			// is linearly equivalent to one of theser,
			// unless it is linearly equivalent to
			// inf_{+} + inf_{-}.

K<u,v>:=FunctionField(Y);
for D in deg2 do
	L,mu:=RiemannRochSpace(D);
	D1:=D+Divisor(mu(L.1)); // Replace D by a linearly equivalent 
				// effective divisor.
	decomp:=Decomposition(D1);
	if #decomp eq 1 and decomp[1,2] eq 1 then
		// If D1 is irreducible of degree 2
		// (i.e. comes from a sum P+P^\sigma
		// where P is quadratic) then
		assert J!(decomp[1,1]-infdiv) eq  J![x^2 + x - 1, 0];
		// it is the zeros of x^2+x-1, the quadratic factor
		// of the hyperelliptic polynomial.
	end if;
end for;


// Thus the only real
// quadratic points that don't
// have rational x-coordinates
// are ((-1+sqrt{5})/2,0)
// and its conjugate. Note that
// These are fixed by the hyperelliptic
// involution which happens to be
// w_{35}. Thus they correspond to
// elliptic curves with CM.
// We now verify this fact by
// writing the j-invariant of the
// corresponding points.

f:=Qx!HyperellipticPolynomials(Y);

K<t>:=NumberField(x^2-5); // Discriminant of x^2+x-1 is 5.
YK:=BaseChange(Y,K);
XK:=BaseChange(X,K);  // X(b5,b7) over K
tf,phiK:=IsIsomorphic(XK,YK);
assert tf;  // phiK : X -> Y
            // is the isomorphism considered over K
P:=YK![(-1+t)/2,0];  // The only quadratic point on Y (up to conjugation),
			// that doesn't have rational x-coordinate.
Q:=P@@phiK;   // The corresponding point on X.

j:= 26378240*t - 58982400;

assert jInvariant(Q,35) eq j; // The j-map X->X(1) gives the claimed value of j.
assert jNInvariant(Q,35) eq j;

Ej:=EllipticCurveWithjInvariant(j);

tf,D:=HasComplexMultiplication(Ej);

assert tf;
assert D eq -35;  // Ej, the elliptic curve corresponding to P, has
		// complex multiplication by \Z[\sqrt{-35}] 

