// We verify the computations in Sections 6 and 7 of the paper.
// Precisely, we show that $X^{(3)}(\Q)$ consists of the two
// cuspidal divisors, where $X=X(b5,ns7)$.


PxP<x1,x2,y1,y2>:=ProductProjectiveSpace(Rationals(),[1,1]); // P^1 x P^1
F1:=(x1^2+10*x1*x2+5*x2^2)^3;
F2:=x1*x2^5;


G1:= 64*(y1*(y1^2+7*y2^2)*(y1^2-7*y1*y2+14*y2^2)*(5*y1^2-14*y1*y2-7*y2^2))^3;
G2:=(y1^3-7*y1^2*y2+7*y1*y2^2+7*y2^3)^7;

// C is Le Hung's model for X(b5,ns7) as a curve in P^1 x P^1.
C:=Curve(PxP,F1*G2-G1*F2);
assert Genus(C) eq 6;



// Next we write down the cusps on this model.
Qzet<zet>:=CyclotomicField(7);
L<eta>:=sub<Qzet | 2*(zet^3+zet^-3)+3>;
assert Evaluate(ChangeRing(G2,L),[0,0,eta,1]) eq 0; // (\eta : 1) is a zero of G2.
c0C:=C(L)![0,1,eta,1];  // The 0 cusps on C are the Galois orbit of this.
cinfC:=C(L)![1,0,eta,1]; // The infty cusps on C are the Galois orbit of this. 

// Let's check that difference of the Galois orbit of cusps really gives
// a point of order 7 on the Jacobian.

plsc0C:=Places(c0C);
assert #plsc0C eq 1;
c0:=plsc0C[1]; // The 0 cusps as a place of degree 3.
assert Degree(c0) eq 3;
plscinfC:=Places(cinfC); 
assert #plscinfC eq 1;
cinf:=plscinfC[1];  // The infinity cusps as a place of degree 3.
assert Degree(cinf) eq 3;
assert IsPrincipal(c0-cinf) eq false;
tf,f:=IsPrincipal(7*(c0-cinf)); // Slow!
assert tf; // Therefore [c0-cinf] has order 7.
assert f/(FunctionField(C)!(x1/x2)) in Rationals();
// Therefore div(x_1/x_2)=7(c_0-c_\infty).



// Constructing the canonical image.
canon:=CanonicalMap(C);
canonImage:=CanonicalImage(C,canon);
assert Genus(canonImage) eq 6;
assert &and[Degree(f) eq 2 : f in DefiningEquations(canonImage)];
assert #DefiningEquations(canonImage) eq 6;

canonAmb<[w]>:=AmbientSpace(canonImage);
assert Dimension(canonAmb) eq 5;
// Thus the canonical image is cut out by 6 quadrics in P^5.

// We will now use Magma to write down a plane model cut out by
// a single degree 6 equations, which has exactly four nodes
// as its singular locus. We shall call this model F,
// and later change coordinates to obtain a better plane model
// that is denoted by D in the paper.
tf, CtoF := Genus6PlaneCurveModel(C);
assert tf; 
F := Codomain(CtoF); // F is a planar model for C.
assert Genus(F) eq 6;
assert #DefiningEquations(F) eq 1;
assert Degree(DefiningEquations(F)[1]) eq 6;
assert IsProjective(F);
assert Dimension(AmbientSpace(F)) eq 2;
// Thus F is cut out in P^2 by one degree 6 equation.


// We transfer the cusps to F.
def:=DefiningEquations(CtoF);
FFC:=FunctionField(C);
c0F:=[Evaluate(FFC!(def[1]/def[3]),c0C),Evaluate(FFC!(def[2]/def[3]),c0C),1]; // A representative
										// of the Galois orbit of cusps at 0 on F.  
cinfF:=[Evaluate(FFC!(def[1]/def[3]),cinfC),Evaluate(FFC!(def[2]/def[3]),cinfC),1]; // A representative
										// of the Galois orbit of cusps at infinity on F. 

// We now put the coordinates of these cusp representatives in L.
tf,ism:=IsIsomorphic(Universe(c0F),L);
assert tf;
c0F:=[ism(a) : a in c0F];
tf,ism:=IsIsomorphic(Universe(cinfF),L);
assert tf;
cinfF:=[ism(a) : a in cinfF];


// We want to check the claim that F has four singular points,
// and that these are ordinary double points.
S:=SingularSubscheme(F);
assert Dimension(S) eq 0;
assert #PointsOverSplittingField(S) eq 4;
// Thus F has four singular points.
// We shall show that these are nodes,
// and that two are defined over \Q(i)
// and the other two are defined over \Q(\sqrt{5}).

assert #Points(S) eq 0;
// None of the four singular points are defined over \Q.

K1 := QuadraticField(-1);
K2 := QuadraticField(5);

singPointsK1:=Points(S,K1);
assert #singPointsK1 eq 2;
FK1:=ChangeRing(F,K1);
assert IsNode(FK1!Eltseq(singPointsK1[1]));
assert IsNode(FK1!Eltseq(singPointsK1[2]));

singPointsK2:=Points(S,K2);
assert #singPointsK2 eq 2;
FK2:=ChangeRing(F,K2);
assert IsNode(FK2!Eltseq(singPointsK2[1]));
assert IsNode(FK2!Eltseq(singPointsK2[2]));
// We have now checked that all four
// singular points are nodes,
// with two defined over K1=\Q(i)
// and two defined over K2:=\Q(\sqrt{5}).

// Let the two points defined over \Q(i)
// be x_1, x_2
// and the two points defined over \Q(\sqrt{5})
// by y_1, y_2.
// We change coordinates so that
// x_1, x_2 map to 
// a_1=(i : 0 : 1), a_2=(-i:0:1)
// and y_1, y_2 map to 
// b_1=(0 : 1/\sqrt{5} : 1), b_2= (0 : -1/\sqrt{5} :1).

K := Compositum(K1,K2);
PK<u,v,w> := ProjectiveSpace(K,2);
x1,x2 := Explode(Setseq(RationalPoints(S,K1)));
y1,y2 := Explode(Setseq(RationalPoints(S,K2)));
x1 := PK ! Eltseq(x1);
x2 := PK ! Eltseq(x2);
y1 := PK ! Eltseq(y1);
y2 := PK ! Eltseq(y2);
a1 := PK ! [K1.1,0,1];
a2 := PK ! [-K1.1,0,1];
b1 := PK ! [0,K2.1/5,1];
b2 := PK ! [0,-K2.1/5,1];
T1 := TranslationOfSimplex(PK,[x1,x2,y1,y2]);
T2 := TranslationOfSimplex(PK,[a1,a2,b1,b2]);
T := T2^(-1)*T1;
// T^-1 gives our desired change of coordinates.

PQ<u,v,w> := AmbientSpace(F);

// T is defined over K. However it preserves Q-conjugacy
// and so must be defined over Q. 
// We now write a model for T over Q.
Teqs := DefiningEquations(T);
T1 :=  Numerator(Teqs[1]/Teqs[2]);
lambda := K ! (T1/Teqs[1]);
TeqsQ := [CoordinateRing(PQ) ! (lambda*t) : t in Teqs];
TQ := map< PQ -> PQ | TeqsQ>; // This is a model for T over Q.
// As a sanity check we base change TQ back to K and check that
// we get T.
TK := map< PK -> PK |  [ CoordinateRing(PK)!t : t in DefiningEquations(TQ)  ]  >;
assert TK eq T; // Sanity check.

D := Pullback(TQ,F);  
// Now D is our new model. It has the four singularities at a0, a2, b1, b2.
// Let check!
assert {PK!Eltseq(q) : q in Points(SingularSubscheme(ChangeRing(D,K)))} eq {a1,a2,b1,b2}; 
// Next we check that D has the same equation as claimed in the paper, up to scaling the equation.
eqn:=5*u^6 - 50*u^5*v + 206*u^4*v^2 - 408*u^3*v^3 + 321*u^2*v^4 + 10*u*v^5 - 100*v^6 
    + 9*u^4*w^2 - 60*u^3*v*w^2 + 80*u^2*v^2*w^2 + 48*u*v^3*w^2 + 15*v^4*w^2 + 
    3*u^2*w^4 - 10*u*v*w^4 + 6*v^2*w^4 - w^6; // This is the equation for D in the paper.
assert DefiningEquation(D)/eqn in Rationals(); // The equation for D is a rational multiple of eqn.


// Next we write down the two cusp representatives on this new model.
c0D:=[Evaluate(f,c0F) : f in DefiningEquations(Inverse(TQ))];
cinfD:=[Evaluate(f,cinfF) : f in DefiningEquations(Inverse(TQ))];

// Let's check that these are the same as the ones in the paper.

c0paper:=[-4*eta^2 + 21*eta + 7, -eta^2 + 7*eta , 14];
cinfpaper:=[4*eta^2 - 21*eta - 7, eta^2 - 7*eta , 14];

auts:=Automorphisms(L);
cuspOrbits:={PQ(L)!a(c0D) : a in auts} join {PQ(L)!a(cinfD) : a in auts};
cuspOrbitsPaper:={ PQ(L)!a(c0paper) : a in auts} join { PQ(L)!a(cinfpaper) : a in auts};

assert cuspOrbits eq cuspOrbitsPaper; // Yes, they give the same Galois orbits! 

// Remarks: note we cannot be more precise about which cusp on C maps to which cusp on D.
// This is because of the involution (u:v:w) :-> (-u:-v:w) that interchanges the cusps.
// Composing the map C -> D with this involution changes the ordering of the cusps.
// All we are saying is that there is a birational map C->D that takes c0 on C to
// the Galois orbit of c0paper, and takes cinf on C to the Galois orbit of cinpaper.

// Let's turn these cusps into places.
plsc0D:=Places(D(L)!c0D);
assert #plsc0D eq 1;
c0:=plsc0D[1];
plscinfD:=Places(D(L)!cinfD);
assert #plscinfD eq 1;
cinf:=plscinfD[1];

assert Degree(c0) eq 3;
assert Degree(cinf) eq 3;



w5:=iso<D->D | [-u,-v,w], [-u,-v,w]>; // We prove in the paper that w_5 is the obvious involution on the model D.
assert Pullback(w5,c0) eq cinf; // Thus w_5 swaps the 0 and infinity cusps as expected.

assert IsPrincipal(c0-cinf) eq false;
assert IsPrincipal(7*(c0-cinf)); // As a sanity check, we verify that [c0-cinf] is a point of order 7 for the Jacobian of the new model.

// Let's check that the torsion subgroup of J(b5,ns7)(\Q) is 
// \Z/7\Z.

assert  Invariants(ClassGroup(ChangeRing(D,GF(3)))) eq [ 7, 7*23, 0 ]; // Thus J(\F_3) = Z/7Z x Z/(7*23 Z).
assert Invariants(ClassGroup(ChangeRing(D,GF(17)))) eq [ 2, 2^2*7^3*31*271, 0]; // J(\F_{17}) = Z/2Z x Z/(2^2*7^3*31*271 Z).

// It follows that the torsion subgroup is isomorphic to \Z/7\Z and generated by [c_0-c_inf].


// Next we compute the reduction of D modulo 3, and the of the two cusps.

Dmod3:=Curve(Reduction(D,3));
assert Genus(Dmod3) eq 6;
P<u,v,w>:=AmbientSpace(Dmod3);
w5:=iso<Dmod3->Dmod3 | [-u,-v,w], [-u,-v,w]>;

// We also compute the cusps mod 3.
OL:=MaximalOrder(L);
assert IsPrime(3*OL); // 3 is inert in L.
F27,mod3:=ResidueClassField(3*OL);
assert #F27 eq 27;
id:=hom<F27->F27 | x:->x>;
frob:=hom<F27->F27 | x:->x^3>;
frobsq:=hom<F27->F27 | x:->x^9>;

c0Reds:=[ Dmod3(F27)!a(mod3(c0paper)) :  a in [id,frob,frobsq]]; // The reduction of the three 0 cusps.
cinfReds:=[ Dmod3(F27)!a(mod3(cinfpaper)) :  a in [id,frob,frobsq]]; // The reduction of the three infinity cusps.

assert #Set(c0Reds) eq 3; 
assert #Set(cinfReds) eq 3; 
assert #Set(c0Reds cat cinfReds) eq 6; // The reductions are all distinct.
assert &and[IsSingular(P) eq false : P in c0Reds cat cinfReds]; // The reductions are all smooth on Dmod3/F_{27}.

// Now let's turn these into places.

c0mod3:=Place(c0Reds[1]);
cinfmod3:=Place(cinfReds[1]);

assert Pullback(w5,cinfmod3) eq c0mod3; // Sanity check: the involution still swaps the cusps.

// Next we'll write down all effective divisors on Dmod3 of degree 3.

deg1:=Places(Dmod3,1); // Places of degree 1. 
deg2:=Places(Dmod3,2); // Places of degree 2. 
deg3:=Places(Dmod3,3); // Places of degree 3.

assert c0mod3 in deg3;
assert cinfmod3 in deg3;

div3:={p+q+r : p,q,r in deg1} join {p+q : p in deg1, q in deg2} join Set(deg3); // The effective divisors of degree 3 on Dmod3.

assert #div3 eq 40;
assert &and[Degree(d) eq 3 : d in div3];
assert &and[IsEffective(d) : d in div3];

// We check the claim made in the paper, that the only effective degree 3 divisors d on Dmod3
// satisfying [d-w5(d)]= k [c0mod3-cinfmod3] (k in [-3..3])
// are c0mod3, cinfmod3. 

for d in div3 do
	for k in [-3..3] do
		if IsPrincipal(d-Pullback(w5,d) - k*(c0mod3-cinfmod3)) then  // Since w_5 is an involution, pull-back
										// is the same as pushforward. We use
										// pull-back as it is easier to compute.
			assert (d eq c0mod3) or (d eq cinfmod3);
		end if;
	end for; 
end for;

// Finally we want to check the formal immersion criterion at cinfmod3.

V,phi:=SpaceOfDifferentialsFirstKind(Dmod3); 
assert Dimension(V) eq 6;
t1:=hom<V->V | [ Pullback(w5,phi(V.i))@@phi - V.i : i in [1..6] ]>; // The (w5-1)* acting on holomorphic differentials.
W1:=Image(t1); 
t2:=hom<V->V | [ Pullback(w5,phi(V.i))@@phi + V.i : i in [1..6] ]>; // The (w5+1)* acting on holomorphic differentials.
W2:=Kernel(t2); 
assert W1 eq W2; // Sanity check, since w5^2=1.
W:=W2; // This is the -1-eigenspace of w_5^*. 
assert Dimension(W) eq 4; // This is the subspace of regular 1-forms coming from the 4-dimensional abelian subvariety A.
Adiffs:=[ phi(W.i) : i in [1..4] ]; // Basis for these regular 1-forms coming from A.

// Now that we have the basis, we write down the Derickx matrix cinfmod3 and check that it has rank 3.

du:=Differential(UniformizingParameter(cinfmod3));
v:=[ Evaluate(omega/du,cinfmod3) : omega in Adiffs]; // This is one of the rows. The other three rows are its conjugates.
A:=Matrix( [[ v[1]^i, v[2]^i, v[3]^i, v[4]^i ] : i in [1,3,9]] ); // The Derickx matrix at cinfmod3.
assert Rank(A) eq 3;


