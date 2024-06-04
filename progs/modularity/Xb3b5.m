


// Let X:=X(b3,b5)=X_0(15). We will verify the correctness
// of the model and j-map on X given by the MAGMA Small Modular Curves database.
// (We do this since no reference is given for the j-map in the
// MAGMA documentation).

// In this case the genus is 1 and so 
// the canonical map does not give an embedding.
// We shall instead have rely on higher weight cusp forms.

// For now let \Gamma be a congruence subgroup of SL_2(\Z)
// and let X be the corresponding (compactified) modular curve,
// and write g for the genus of X.
// Let m \ge 3, and let f_1,\dots, f_t be a basis for 
// S_m(\Gamma). Assume that t \ge g+2. Then
// by G. Moic, "On embeddings of modular curves in projective spaces",
// Theorem 3.3, the map
// z :-> (f_1(z),\dots,f_t(z))
// induces an embedding of X into \P^{t-1}.


// We now return to X=X(b3,b5)=X_0(15)
S:=CuspForms(15,2);
assert Dimension(S) eq 1;
// Thus X has genus 1. 

S:=CuspForms(15,4); 
assert Dimension(S) eq 4;
// This satisfies the bound dim(S) \ge g+2.
// Hence a basis for S gives an embedding of X in P^3.


R<[x]>:=PolynomialRing(Rationals(),4);
eqn1:=x[1]*x[3] - x[2]^2 + 2*x[2]*x[4] - 2*x[3]^2 + 4*x[3]*x[4] - x[4]^2;
eqn2:=x[1]*x[4] - x[2]*x[3] + x[2]*x[4] + 4*x[3]*x[4] - 2*x[4]^2;

// We will show that eqn1, eqn2 cut out the image of X in P^3.

k:=8;                   // Weight of eqn1, eqn2 evaluated at a basis
			// of cuspforms of level 4.
m:=15*(1+1/3)*(1+1/5);  // Index of Gamma_0(15) in SL_2(\Z).

hecke:=Ceiling(m*k/12);  // Hecke=Sturm bound.

Bexp:=[qExpansion(S.i,hecke+10) : i in [1..4]]; // q-expansions
						// of basis for S
						// up to precision hecke+10.
assert Valuation(Evaluate(eqn1,Bexp)) gt hecke;
assert Valuation(Evaluate(eqn2,Bexp)) gt hecke;

// Thus eqn1=0 and eqn2=0 contain the image of X.

P:=ProjectiveSpace(R);
X:=Curve(P,[eqn1,eqn2]);
assert IsSingular(X) eq false;
assert Genus(X) eq 1;
assert IsIrreducible(X);

// Hence eqn1=eqn2=0 define X in P^3.

jnum:=-x[1]^6 - 714*x[1]^5*x[2] - 174969*x[1]^4*x[2]^2 - 15885364*x[1]^3*x[2]^3 - 
    296863926*x[1]^2*x[2]^4 - 2404683972*x[1]*x[2]^5 - 10308218600*x[2]^6 - 
    25891622028*x[2]^5*x[3] - 39146661507*x[2]^4*x[3]^2 - 
    44174739678*x[2]^3*x[3]^3 - 181400389479*x[2]^2*x[3]^4 - 
    128154475788*x[2]*x[3]^5 + 251612254876*x[2]*x[3]^4*x[4] - 
    613581565922*x[2]*x[3]^3*x[4]^2 + 287663070740*x[2]*x[3]^2*x[4]^3 + 
    949399589384*x[2]*x[3]*x[4]^4 + 72647360040*x[2]*x[4]^5 - 
    218711265561*x[3]^6 + 44729522298*x[3]^5*x[4] + 488906458767*x[3]^4*x[4]^2 -
    3122600785500*x[3]^3*x[4]^3 + 2449201220690*x[3]^2*x[4]^4 - 
    102896056670*x[3]*x[4]^5 - 59865673119*x[4]^6;

jden:=-x[1]^5*x[2] + 30*x[1]^4*x[2]^2 - 405*x[1]^3*x[2]^3 + 3195*x[1]^2*x[2]^4 - 
    15791*x[1]*x[2]^5 + 46743*x[2]^6 - 56172*x[2]^5*x[3] - 114344*x[2]^4*x[3]^2 
    + 391694*x[2]^3*x[3]^3 + 725811*x[2]^2*x[3]^4 - 5697673*x[2]*x[3]^5 + 
    9656137*x[2]*x[3]^4*x[4] - 5106526*x[2]*x[3]^3*x[4]^2 + 
    1309321*x[2]*x[3]^2*x[4]^3 - 3882779*x[2]*x[3]*x[4]^4 - 223628*x[2]*x[4]^5 +
    5000*x[3]^6 + 34008730*x[3]^5*x[4] - 81251468*x[3]^4*x[4]^2 + 
    61888012*x[3]^3*x[4]^3 - 11924202*x[3]^2*x[4]^4 + 806573*x[3]*x[4]^5 + 
    189857*x[4]^6;

assert IsHomogeneous(jnum);
assert IsHomogeneous(jden);

// We claim that jnum/jden gives the j-map X-->X(1).
// To do this we show that jnum(Bexp)-jden(Bexp)*j(q) is zero to the 
// necessary Hecke bound, which is now larger at the weights of the
// modular forms are 6x4=24

k:=24;
hecke:=Ceiling(m*k/12);  // New Hecke=Sturm bound.
Qq<q>:=PowerSeriesRing(Rationals(), hecke+30);

Bexp:=[Qq!qExpansion(S.i,hecke+30) : i in [1..4]]; // q-expansions
						// of basis for S
						// up to precision hecke+30.
j:=jInvariant(q);   // q^-1+744+...

assert Valuation(Evaluate(jnum,Bexp) -j*Evaluate(jden,Bexp) ) gt hecke;

// This shows that jnum/jden is the j-map on X.

K:=FunctionField(X);
jX:=K!(jnum/jden);


pt:=X![1,0,0,0];
E,phi:=EllipticCurve(X,pt);
assert CremonaReference(E) eq "15a1";  // X_0(15) !

// Now we check the model for X_0(15) and the j-map 
// in the MAGMA small curves database.

Y:=SmallModularCurve(15);
jY:=FunctionField(Y)!jInvariant(Y,15);

tf,mu:=IsIsomorphic(E,Y);

assert tf;
assert Pullback(phi,Pullback(mu,jY)) eq jX;

// Thus MAGMA's j-map agrees with our own.
