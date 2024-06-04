


// Let X:=X(s3,b5)=X_0(45)/w_9. We give a model for X
// and the j-map. 

S:=CuspForms(45);
V:=Eigenspace(AtkinLehnerOperator(S,9),1);
assert Dimension(V) eq 1;

// In this case the genus is 1 and so 
// we cannot use the canonical map.
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


// We now return to X=X(s3,b5)=X_0(45)/w_9

S:=CuspForms(45,4); 
V:=Eigenspace(AtkinLehnerOperator(S,9),1);
assert Dimension(V) eq 8;
// This satisfies the bound dim(V) \ge g+2.
// Hence a basis for V gives an embedding of X in P^7.


B:=Basis(V);
B:=[Eltseq(b) : b in B];
B:=[&+[b[i]*S.i : i in [1..#b]] : b in B];
R<[x]>:=PolynomialRing(Rationals(),8);

// We claim that the following sequence of polynomials
// cuts out the image of X in P^7

eqns:=[
    x[1]*x[3] - x[2]^2 + 8*x[4]*x[5] + 18*x[5]^2 + 6*x[5]*x[6] - 6*x[6]*x[7] + 
        82*x[6]*x[8] - 26*x[7]^2 + 4*x[7]*x[8] - 70*x[8]^2,
    x[1]*x[4] - x[2]*x[3] - 4*x[4]*x[5] - 8*x[5]^2 + 12*x[5]*x[6] + 14*x[6]^2 + 
        46*x[6]*x[7] + 78*x[6]*x[8] + 4*x[7]^2 - 18*x[7]*x[8] - 84*x[8]^2,
    x[1]*x[5] - x[3]^2 - 16*x[5]*x[6] - 20*x[6]*x[7] - 160*x[6]*x[8] + 40*x[7]^2
        + 32*x[7]*x[8] + 180*x[8]^2,
    x[1]*x[6] - x[3]*x[4] + 2*x[4]*x[5] + 3*x[5]*x[6] - 9*x[6]^2 - 6*x[6]*x[7] +
        90*x[6]*x[8] - 27*x[7]^2 - x[7]*x[8] - 84*x[8]^2,
    x[1]*x[7] - x[4]^2 - 2*x[4]*x[5] + x[5]*x[6] + 10*x[6]^2 + 13*x[6]*x[7] - 
        47*x[6]*x[8] + 17*x[7]^2 - 8*x[7]*x[8] + 36*x[8]^2,
    x[1]*x[8] - x[5]^2 - x[5]*x[6] - 2*x[6]^2 - 3*x[6]*x[7] + 17*x[6]*x[8] - 
        5*x[7]^2 + 2*x[7]*x[8] - 13*x[8]^2,
    x[2]*x[4] - x[3]^2 - 4*x[5]^2 - 16*x[5]*x[6] - 6*x[6]^2 - 24*x[6]*x[7] - 
        126*x[6]*x[8] + 30*x[7]^2 + 30*x[7]*x[8] + 156*x[8]^2,
    x[2]*x[5] - x[3]*x[4] + 4*x[5]*x[6] - 8*x[6]^2 - 4*x[6]*x[7] + 86*x[6]*x[8] 
        - 26*x[7]^2 - 6*x[7]*x[8] - 88*x[8]^2,
    x[2]*x[6] - x[4]^2 + 2*x[5]^2 + 7*x[6]^2 - x[6]*x[7] - 75*x[6]*x[8] + 
        14*x[7]^2 - 9*x[7]*x[8] + 60*x[8]^2,
    x[2]*x[7] - x[4]*x[5] - 2*x[5]^2 + x[6]^2 + 6*x[6]*x[7] + 29*x[6]*x[8] - 
        5*x[7]^2 - 5*x[7]*x[8] - 28*x[8]^2,
    x[2]*x[8] - x[5]*x[6] - x[6]^2 - 4*x[6]*x[7] - 22*x[6]*x[8] + 3*x[7]^2 - 
        x[7]*x[8] + 18*x[8]^2,
    x[3]*x[5] - x[4]^2 + 8*x[6]^2 + 8*x[6]*x[7] - 34*x[6]*x[8] + 10*x[7]^2 - 
        10*x[7]*x[8] + 24*x[8]^2,
    x[3]*x[6] - x[4]*x[5] + 2*x[5]*x[6] + 7*x[6]*x[7] + 36*x[6]*x[8] - 7*x[7]^2 
        - 6*x[7]*x[8] - 40*x[8]^2,
    x[3]*x[7] - x[5]^2 - 2*x[5]*x[6] - 3*x[6]*x[7] - 25*x[6]*x[8] + 8*x[7]^2 + 
        5*x[7]*x[8] + 28*x[8]^2,
    x[3]*x[8] - x[6]^2 - x[6]*x[7] + 13*x[6]*x[8] - 4*x[7]^2 + x[7]*x[8] - 
        14*x[8]^2,
    x[4]*x[6] - x[5]^2 + 2*x[6]^2 - 13*x[6]*x[8] + 3*x[7]^2 - x[7]*x[8] + 
        12*x[8]^2,
    x[4]*x[7] - x[5]*x[6] - 2*x[6]^2 - 2*x[6]*x[7] + 7*x[6]*x[8] - 3*x[7]^2 + 
        3*x[7]*x[8] - 4*x[8]^2,
    x[4]*x[8] - x[6]*x[7] - 8*x[6]*x[8] + x[7]^2 - 2*x[7]*x[8] + 8*x[8]^2,
    x[5]*x[7] - x[6]^2 - 2*x[6]*x[7] - 3*x[6]*x[8] + x[7]*x[8] + 4*x[8]^2,
    x[5]*x[8] + 3*x[6]*x[8] - x[7]^2 - x[7]*x[8] - 4*x[8]^2
];


assert &and[Degree(E) eq 2  :E in eqns];
assert &and[IsHomogeneous(E) : E in eqns]; // The polynomials
					// are all homogeneous of degree 2.


k:=8;                   // Weight of the polynomials evaluated at the basis
			// of cuspforms of level 4.
m:=45*(1+1/3)*(1+1/5);  // Index of Gamma_0(45) in SL_2(\Z).

hecke:=Ceiling(m*k/12);  // Hecke=Sturm bound.

Bexp:=[qExpansion(B[i],hecke+10) : i in [1..8]]; // q-expansions
						// of basis for V
						// up to precision hecke+10.
assert &and[Valuation(Evaluate(E,Bexp)) gt hecke  : E in eqns];


P:=ProjectiveSpace(R);
X:=Curve(P,eqns);
assert Genus(X) eq 1;
assert IsIrreducible(X);

// Hence eqns define X in P^7.


jnum:=
-x[1]^5 + 710*x[1]*x[2]^4 + 334825*x[2]^4*x[3] + 506900*x[2]^3*x[3]^2 - 
    710*x[2]^2*x[3]^3 + 109039620*x[2]*x[3]^4 + 124202470*x[3]^5 + 
    2178110*x[3]^4*x[4] + 11039974485*x[3]^3*x[4]^2 + 11264212770*x[3]^2*x[4]^3 
    + 3363527580*x[3]*x[4]^4 + 213238180338*x[4]^5 + 121616854550*x[4]^4*x[5] + 
    117427915190*x[4]^3*x[5]^2 + 1871206664625*x[4]^2*x[5]^3 - 
    2468045234620*x[4]*x[5]^4 - 2132310187690*x[5]^5 + 
    10606744729000*x[5]^4*x[6] - 2388054786860*x[5]^3*x[6]^2 + 
    2768644395780*x[5]^2*x[6]^3 + 25546706607210*x[5]*x[6]^4 + 
    91966804276770*x[6]^5 + 250179078115710*x[6]^4*x[7] + 
    371770406138100*x[6]^3*x[7]^2 - 34157970210520*x[6]^2*x[7]^3 + 
    1364439279669600*x[6]*x[7]^4 + 35371352699804740*x[6]*x[7]^3*x[8] + 
    76842700336903380*x[6]*x[7]^2*x[8]^2 + 47540711715353390*x[6]*x[7]*x[8]^3 + 
    3113965277574250*x[6]*x[8]^4 - 6600392619193120*x[7]^5 - 
    16668683119528710*x[7]^4*x[8] - 44745497652313570*x[7]^3*x[8]^2 - 
    77743653648293980*x[7]^2*x[8]^3 - 47730849875412110*x[7]*x[8]^4 - 
    3218682080045790*x[8]^5;

jden:=
-x[1]^2*x[2]^3 + 744*x[2]^4*x[3] + 710*x[2]^3*x[3]^2 - 21800*x[2]*x[3]^4 - 
    21316*x[3]^5 + 5242*x[3]^4*x[4] + 275590*x[3]^3*x[4]^2 + 
    266908*x[3]^2*x[4]^3 - 678406*x[3]*x[4]^4 - 2965066*x[4]^5 - 
    4187132*x[4]^4*x[5] + 3446378*x[4]^3*x[5]^2 + 28500734*x[4]^2*x[5]^3 + 
    79976034*x[4]*x[5]^4 + 75123720*x[5]^5 - 84581320*x[5]^4*x[6] - 
    343266872*x[5]^3*x[6]^2 - 377844724*x[5]^2*x[6]^3 - 1371999280*x[5]*x[6]^4 -
    3000964242*x[6]^5 - 10248223982*x[6]^4*x[7] - 1650665734*x[6]^3*x[7]^2 - 
    34592412092*x[6]^2*x[7]^3 + 167023055286*x[6]*x[7]^4 + 
    4827536574506*x[6]*x[7]^3*x[8] + 12921341352058*x[6]*x[7]^2*x[8]^2 + 
    12702420917026*x[6]*x[7]*x[8]^3 + 4357061936166*x[6]*x[8]^4 - 
    884620138200*x[7]^5 - 2716445777792*x[7]^4*x[8] - 
    7325394087210*x[7]^3*x[8]^2 - 13785504331300*x[7]^2*x[8]^3 - 
    12689300138050*x[7]*x[8]^4 - 4351958170424*x[8]^5;



assert IsHomogeneous(jnum);
assert IsHomogeneous(jden);
assert Degree(jnum) eq 5;
assert Degree(jden) eq 5;

// We claim that jnum/jden gives the j-map X-->X(1).
// To do this we show that jnum(Bexp)-jden(Bexp)*j(q) is zero to the 
// necessary Hecke bound, which is now larger at the weights of the
// modular forms are 5x4=20

k:=20;
hecke:=Ceiling(m*k/12);  // New Hecke=Sturm bound.
Qq<q>:=PowerSeriesRing(Rationals(), hecke+30);


Bexp:=[Qq!qExpansion(B[i],hecke+30) : i in [1..8]]; // q-expansions
						// of basis for V
						// up to precision hecke+30.
j:=jInvariant(q^3);   // q^-3+744+...

assert Valuation(Evaluate(jnum,Bexp) -j*Evaluate(jden,Bexp) ) gt hecke;

// This shows that jnum/jden is the j-map on X.

K:=FunctionField(X);
pK:=[K.i : i in [1..7]] cat [1];

assert &and[ Evaluate(E,pK) eq 0 : E in eqns];  // pK is the generic point of X

jX:=Evaluate(jnum,pK)/Evaluate(jden,pK);

// jX is the j-map as an element of the function field of X

pt:=X![1,0,0,0,0,0,0,0];
E,phi:=EllipticCurve(X,pt);
assert CremonaReference(E) eq "15a3";  


// Now we check that the above X and j are consistent
// with the Weierstrass X and j given in the paper
// and used in the file sieve.m 

Y:=EllipticCurve([ 1, 1, 1, -5, 2 ]);
assert CremonaReference(Y) eq "15a3";

Zabc<a,b,c>:=PolynomialRing(Integers(),3);
num:=20*a^20 + a^19*b + 764*a^19*c + 198*a^18*b*c - 93375*a^18*c^2 - 5751*a^17*b*c^2
    - 753327*a^17*c^3 - 487899*a^16*b*c^3 + 92440395*a^16*c^4 +
    11853027*a^15*b*c^4 + 172229814*a^15*c^5 + 270788724*a^14*b*c^5 -
    23525413659*a^14*c^6 - 4225070808*a^13*b*c^6 - 130984659090*a^13*c^7 -
    58790769084*a^12*b*c^7 + 388950511392*a^12*c^8 + 17020166634*a^11*b*c^8 +
    1701267503040*a^11*c^9 + 962390170098*a^10*b*c^9 - 5138057183184*a^10*c^10 -
    1225792198458*a^9*b*c^10 - 2802529136907*a^9*c^11 - 4233386478519*a^8*b*c^11
    + 25124440867110*a^8*c^12 + 12721947498873*a^7*b*c^12 -
    37576898359344*a^7*c^13 - 13522468139748*a^6*b*c^13 +
    26254233683775*a^6*c^14 + 6570090062109*a^5*b*c^14 - 9020868831972*a^5*c^15
    - 1225384900488*a^4*b*c^15 + 1225391297463*a^4*c^16 - 1633689*a^3*b*c^16 -
    3346110*a^3*c^17 + 118098*a^2*b*c^17 + 334611*a^2*c^18 - 118098*a*b*c^18 -
    295245*a*c^19 + 59049*b*c^19 + 118098*c^20;
den:=-a^19*c - 178*a^18*c^2 - 18*a^17*b*c^2 - 6207*a^17*c^3 - 1096*a^16*b*c^3 -
    96289*a^16*c^4 - 23052*a^15*b*c^4 - 827873*a^15*c^5 - 246759*a^14*b*c^5 -
    4248050*a^14*c^6 - 1529013*a^13*b*c^6 - 12778784*a^13*c^7 -
    5616723*a^12*b*c^7 - 18221027*a^12*c^8 - 11082681*a^11*b*c^8 +
    7860821*a^11*c^9 - 4999672*a^10*b*c^9 + 66082972*a^10*c^10 +
    24193626*a^9*b*c^10 + 58814247*a^9*c^11 + 41855832*a^8*b*c^11 -
    64866933*a^8*c^12 - 3429432*a^7*b*c^12 - 102739293*a^7*c^13 -
    51095529*a^6*b*c^13 + 35165664*a^6*c^14 - 11946123*a^5*b*c^14 +
    59713848*a^5*c^15 + 23890059*a^4*b*c^15 - 23881311*a^4*c^16 -
    2187*a^3*b*c^16 - 4374*a^3*c^17;
_<x,y>:=FunctionField(Y);
jY:=Evaluate(num,[x,y,1])/Evaluate(den,[x,y,1]);


tf,psi:=IsIsomorphic(E,Y);
assert tf;   // Y is isomorphic to E and hence to X
assert Pullback(phi,Pullback(psi,jY)) eq jX;


