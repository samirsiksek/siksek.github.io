
// We give a model for X=X(b3,s5) (isomorphic to X_0(75)/w_{25})
// (together with a proof of the model's correctness)
// and we determine \Sym^{(2)}(X)(\Q) 


S:=CuspForms(75);
V:=Eigenspace(AtkinLehnerOperator(S,25),1);   
B:=Basis(V);
B:=[Eltseq(b) : b in B];
B:=[&+[b[i]*S.i : i in [1..#b]] : b in B];  // B is a basis for +1 eigenspace
						// for w_{25} acting on S_2(75).
						// Thus the elements of B are 
						// holomorphic differentials on
						// X_0(75)/w_{25}.

assert #B eq 3;
// Hence X has genus 3.

// We now write down an equation for X

R<[x]>:=PolynomialRing(Rationals(),3);

eqn:=3*x[1]^3*x[3] - 3*x[1]^2*x[2]^2 + 5*x[1]^2*x[3]^2 - 3*x[1]*x[2]^3 - 
    19*x[1]*x[2]^2*x[3] - x[1]*x[2]*x[3]^2 + 3*x[1]*x[3]^3 + 2*x[2]^4 + 
    7*x[2]^3*x[3] - 7*x[2]^2*x[3]^2 - 3*x[2]*x[3]^3;

// We claim that eqn defines X=X_0(75)/w_{25} in P^3 via the canonical 
// embedding.  To do this we will show that eqn evaluated on the basis 
// of differentials B is identically 0.
// To do this we need to work to a precision that is at least equal to 
// the Hecke (=Sturm) bound.

k:=8; // This is the weight of eqn evaluated at the cuspforms.
m:=75*(1+1/3)*(1+1/5);   // index of Gamma_0(75).

hecke:=Ceiling(k*m/12);  // Hecke bound

Bexp:=[ qExpansion(f,hecke+10) : f in B];  // The differentials=cusp forms as power series to precision hecke+10.

assert Valuation(Evaluate(eqn,Bexp)) ge hecke;

P2:=ProjectiveSpace(R);
X:=Curve(P2,eqn);  
assert IsSingular(X) eq false;
assert Genus(X) eq 3;

// This proves that eqn is the canonical image of X=X_0(75)/w_{25}
// and as it is a plane quartic, the canonical image is an embedding.

// Next we will give the j-Invariant as a function on X.
// This curve classifies unordered pairs {E_1,E_2} connected by a 25-isogeny
// with both having a rational subgroup of order 3.
// The j-invariants of these are not in general defined over the 
// ground field, but over a quadratic extension. However
// the 25-isogeny breaks up as composition of two 5-isogenies
// E_1 -> E -> E_2
// where j-invariant of E is defined over the ground field.
// If tau represents E_1 or E_2 in the upper half-plane
// then 5*tau represents E.
// Hence the j-invariant of E is given by j(q^5) 
// where q=exp(2\pi i \tau).

// Next we give the numerator and denominator
// of the j-Invariant
// and prove that they're correct.


num:=-1594323*x[1]^15 - 23914845*x[1]^12*x[2]^3 - 47829690*x[1]^11*x[2]^4 - 
    1167044436*x[1]^10*x[2]^5 - 310892985*x[1]^9*x[2]^6 - 
    6122200320*x[1]^8*x[2]^7 - 12674867850*x[1]^7*x[2]^8 - 
    47335449870*x[1]^6*x[2]^9 - 345162957885*x[1]^5*x[2]^10 - 
    301901003280*x[1]^4*x[2]^11 - 3112389530910*x[1]^3*x[2]^12 - 
    2873775179115*x[1]^2*x[2]^13 - 22981261509819*x[1]^2*x[2]^12*x[3] + 
    20597315531751*x[1]^2*x[2]^11*x[3]^2 + 436439889848817*x[1]^2*x[2]^10*x[3]^3
    + 863530947621036*x[1]^2*x[2]^9*x[3]^4 + 
    715408227809325*x[1]^2*x[2]^8*x[3]^5 + 286146993271842*x[1]^2*x[2]^7*x[3]^6 
    + 35838990928773*x[1]^2*x[2]^6*x[3]^7 - 15174858540600*x[1]^2*x[2]^5*x[3]^8 
    - 7688499629796*x[1]^2*x[2]^4*x[3]^9 - 1534243934340*x[1]^2*x[2]^3*x[3]^10 -
    169623787182*x[1]^2*x[2]^2*x[3]^11 - 13267348416*x[1]^2*x[2]*x[3]^12 - 
    854432816*x[1]^2*x[3]^13 + 930913485399*x[1]*x[2]^14 - 
    40044423642120*x[1]*x[2]^13*x[3] - 495719299207197*x[1]*x[2]^12*x[3]^2 - 
    1849982999431113*x[1]*x[2]^11*x[3]^3 - 2364393478770747*x[1]*x[2]^10*x[3]^4 
    - 1191928712881878*x[1]*x[2]^9*x[3]^5 - 8078714157042*x[1]*x[2]^8*x[3]^6 + 
    245524209985926*x[1]*x[2]^7*x[3]^7 + 98308222944345*x[1]*x[2]^6*x[3]^8 + 
    7908885850077*x[1]*x[2]^5*x[3]^9 - 5007728363427*x[1]*x[2]^4*x[3]^10 - 
    1860582758838*x[1]*x[2]^3*x[3]^11 - 316610706284*x[1]*x[2]^2*x[3]^12 - 
    33327673010*x[1]*x[2]*x[3]^13 - 2011567584*x[1]*x[3]^14 + 
    494036475102*x[2]^15 + 22185422051319*x[2]^14*x[3] + 
    206379719888886*x[2]^13*x[3]^2 + 618583025898387*x[2]^12*x[3]^3 + 
    384894441565038*x[2]^11*x[3]^4 - 386136500612931*x[2]^10*x[3]^5 - 
    661951767048489*x[2]^9*x[3]^6 - 375426584388360*x[2]^8*x[3]^7 - 
    94599125940861*x[2]^7*x[3]^8 - 3137425183848*x[2]^6*x[3]^9 + 
    3803672027610*x[2]^5*x[3]^10 + 549679274179*x[2]^4*x[3]^11 - 
    181348296148*x[2]^3*x[3]^12 - 85843780625*x[2]^2*x[3]^13 - 
    15422354421*x[2]*x[3]^14 - 1162261467*x[3]^15;

den:=-1594323*x[1]^10*x[2]^5 - 7971615*x[1]^8*x[2]^7 - 15943230*x[1]^7*x[2]^8 - 
    63772920*x[1]^6*x[2]^9 - 36669429*x[1]^5*x[2]^10 - 414523980*x[1]^4*x[2]^11 
    + 55801305*x[1]^3*x[2]^12 - 1809556605*x[1]^2*x[2]^13 + 
    5113328472*x[1]^2*x[2]^12*x[3] + 3820109445*x[1]^2*x[2]^11*x[3]^2 + 
    1779835275*x[1]^2*x[2]^10*x[3]^3 + 549558108*x[1]^2*x[2]^9*x[3]^4 - 
    161149095*x[1]^2*x[2]^8*x[3]^5 + 103401360*x[1]^2*x[2]^7*x[3]^6 - 
    38107746*x[1]^2*x[2]^6*x[3]^7 - 21459330*x[1]^2*x[2]^5*x[3]^8 + 
    708588*x[1]^2*x[2]^4*x[3]^9 + 2066715*x[1]^2*x[2]^3*x[3]^10 + 
    181521*x[1]^2*x[2]^2*x[3]^11 - 78732*x[1]^2*x[2]*x[3]^12 - 
    9477*x[1]^2*x[3]^13 - 3016793727*x[1]*x[2]^14 - 
    17888664915*x[1]*x[2]^13*x[3] + 548952309*x[1]*x[2]^12*x[3]^2 - 
    6027487911*x[1]*x[2]^11*x[3]^3 + 2225007873*x[1]*x[2]^10*x[3]^4 + 
    642360537*x[1]*x[2]^9*x[3]^5 + 32051214*x[1]*x[2]^8*x[3]^6 + 
    214251156*x[1]*x[2]^7*x[3]^7 - 77663772*x[1]*x[2]^6*x[3]^8 - 
    28490778*x[1]*x[2]^5*x[3]^9 + 8437446*x[1]*x[2]^4*x[3]^10 + 
    2103894*x[1]*x[2]^3*x[3]^11 - 355023*x[1]*x[2]^2*x[3]^12 - 
    72900*x[1]*x[2]*x[3]^13 + 2187*x[1]*x[3]^14 + 1772801883*x[2]^15 + 
    5936576508*x[2]^14*x[3] - 6156186300*x[2]^13*x[3]^2 + 
    1602360225*x[2]^12*x[3]^3 - 3618504495*x[2]^11*x[3]^4 - 
    610816707*x[2]^10*x[3]^5 - 149314266*x[2]^9*x[3]^6 - 68728905*x[2]^8*x[3]^7 
    + 115095492*x[2]^7*x[3]^8 + 15738381*x[2]^6*x[3]^9 - 12597120*x[2]^5*x[3]^10
    - 1770012*x[2]^4*x[3]^11 + 525609*x[2]^3*x[3]^12 + 80190*x[2]^2*x[3]^13 - 
    2187*x[2]*x[3]^14;

// We want to show that num-j(q^5)*den is identically 0
// when evaluated at the differentials.

assert IsHomogeneous(num);
assert IsHomogeneous(den);
assert Degree(num) eq 15;
assert Degree(den) eq 15;

// The expression num-j*den has weight 30, so we need to work
// to more precision. 

k:=30; // this is the weight of num-j(q^5)*den evaluated at the differentials
m:=75*(1+1/3)*(1+1/5);   // index of Gamma_0(75)

hecke:=Ceiling(k*m/12);  // Hecke bound

Qq<q>:=PowerSeriesRing(Rationals(),hecke+10);

Bexp:=[ Qq!qExpansion(f,hecke+10) : f in B];  // The differentials=cusp forms as power series to precision hecke+10.

j:=jInvariant(q^5); // j(q^5) as powerseries.

assert Valuation(Evaluate(num,Bexp)-j*Evaluate(den,Bexp)) ge hecke;

// It follows that num/den=j(E). 



K:=FunctionField(X);
j:=Evaluate(num,[K.1,K.2,1])/Evaluate(den,[K.1,K.2,1]);

Pr1:=ProjectiveSpace(Rationals(),1);
Pr1:=Curve(Pr1,[]);  // projective line


// Next we show that the Mordell-Weil rank of the
// Jacobian of X over \Q is 0

J075:=JZero(75);
J:=DecomposeUsing(AtkinLehnerOperator(J075,25))[1];  // The Jacobian of X.
decomp:=Decomposition(J);  
assert #decomp eq 3;
assert &and[Dimension(A) eq 1 : A in decomp];  // J decomposes as a product of three elliptic curves.
decomp:=[EllipticCurve(E) : E in decomp];
assert {CremonaReference(E) : E in decomp} eq { "75b1", "75c1", "15a1" };

assert &and[Rank(E) eq 0 : E in decomp]; // Thus J has rank 0 over \Q.
assert &and[Rank(QuadraticTwist(E,5)) eq 0 : E in decomp];  // Thus J has rank 0 over \Q(\sqrt{5});
								// this will be relevant later.

// Now we want to determine the torsion subgroup over \Q(\sqrt{5}).

L<t>:=QuadraticField(5);
OL:=MaximalOrder(L);

pts:=   // Some points  on X/L produced by a short search
	// minus [0,0,1] which will be the base point of the Abel-Jacobi map
[
    [ 1, 0, 0 ],
    [ 1/2, -1/2, 1 ],
    [ -2, 1/2*(-t - 1), 1 ],
    [ -2, 1/2*(t - 1), 1 ],
    [ 1/2*(-t + 1), t - 3, 1 ],
    [ 1/2*(t + 1), -t - 3, 1 ],
    [ 1/2*(t + 1), t + 2, 1 ],
    [ 1/2*(-t + 1), -t + 2, 1 ]
];
// Note that all of these in fact belong to X(\sqrt{5})
// and so their images under the Abel-Jacobi map are torsion points in J(\Q(\sqrt{5})).
// We will show that these generate the torsion subgroup of J(L)
// and determine its structure.
// Note that the first two are rational, whilst the rest are arranged in conjugate pairs.

assert &and [Evaluate(eqn,pt) eq 0 : pt in pts];  // Checking that these points
						// really lie on X.


// The difference of any two of these points generates an element of Pic^0(X)
// and so an element of J(L).

p19:=ideal<OL | [19,9+t]>;  // The ideal generated by 19 and 9+sqrt{5}
assert IsPrime(p19);
assert Degree(p19) eq 1;
F19,pi:=ResidueClassField(p19);
assert #F19 eq 19;


// We use the fact that J(L)_{tors} --> J(\F_{19}) is injective
// to determine the structure of the subgroup of J(L)
// generated by P-P_0 where P ranges over pts and P0=[0,0,1]


X19:=ChangeRing(X,F19);
pts19:=[ Place(X19![pi(r) : r in P  ]) : P in pts]; 
P0:=Place(X19![0,0,1]);

divs19:=[P-P0 : P in pts19];

Cl19,phi,psi:=ClassGroup(X19);
Z:=FreeAbelianGroup(1);
degr:=hom<Cl19->Z | [Degree(phi(g)) : g in OrderedGenerators(Cl19)] >;
J19:=Kernel(degr);  // Pic^0(X / F_{19}) = J(F_{19})
assert IsIsomorphic(J19, AbelianGroup([2,2,8,200])); 
// J(\F_{19}) is isomorphic to \Z/2 x \Z/2 x \Z/8 x \Z/200
                                        


ZN:=FreeAbelianGroup(#pts);

h:=hom<ZN->J19 | [ J19!psi(D) : D in divs19  ]>; 
H:=Image(h);
assert IsIsomorphic(H, AbelianGroup([2,2,8,40])); 
// Image of P-P_0 as P ranges in pts is \Z/2 x \Z/2 x \Z/8 x \Z/40.
// It follows that the P-P_0 either generate the torsion subgroup of J(L)
// or a subgroup of index 5. 


// To verify that we have the full torsion subgroup,
// we look at the image in J(\F_{49}).

p7:=7*OL;
assert IsPrime(p7);
assert Degree(p7) eq 2;
F49,pi49:=ResidueClassField(p7);
assert #F49 eq 49;

X49:=ChangeRing(X,F49);
pts49:=[ Place(X49![pi49(r) : r in P  ]) : P in pts]; 

divs49:=[P-  Place(X49![0,0,1]) : P in pts49];

Cl49,phi49,psi49:=ClassGroup(X49);
degr49:=hom<Cl49->Z | [Degree(phi49(g)) : g in OrderedGenerators(Cl49)] >;
J49:=Kernel(degr49);  // Pic^0(X / F_{49}) = J(F_{49})
assert IsIsomorphic(J49, AbelianGroup([8,8,8,440])); 
// J(\F_{49}) is isomorphic to \Z/8 x \Z/8 x \Z/8 x \Z/440
// whose order is divisible by 5 only once. Thus the 
// order the torsion subgroup of J(L) is divisible by 5 only once.
// Thus the torsion subgroup of J(L) is precisely isomorphic to
// \Z/2 x \Z/2 x \Z/8 x \Z/40. 
                                        

h49:=hom< ZN->J49 | [ J49!psi49(D) : D in divs49  ]>; 
assert IsIsomorphic(Image(h49),AbelianGroup([2,2,8,40])); //sanity check!


// We will determine Sym^2(X) (\Q).
// But first we determine J(\Q), by taking Galois invariants.
// In fact we shall use the embedding J(\Q) -> J(\F_{19}) to help us do this.
// Recall we have arranged the points in pts so that the
// first two are rational, and the rest are in Galois conjugate pairs.
// Thus \oplus_{P in pts} \Z \cdot P  is the free abelian group ZN
// The following gives the action of conjugation on this free abelian group.

conj:=hom< ZN->ZN | [ZN.1,ZN.2,ZN.4,ZN.3,ZN.6,ZN.5,ZN.8,ZN.7] >;

mu:=hom< ZN-> J19 | [h(ZN.i)-h(conj(ZN.i)) : i in [1..8]]>;  

Ker:=Kernel(mu);  
M:=sub< ZN | [ZN.2,ZN.3+ZN.4-5*ZN.2]>;

imKer:=sub< J19 | [h(k) : k in Generators(Ker)]>;  
imM:= sub< J19 | [h(k) : k in Generators(M)]>;

assert imKer eq imM;
assert IsIsomorphic(imKer,AbelianGroup([2,40]));  // J(\Q) is isomorphic to \Z/2 x \Z/40 
// and is generated by pts[2]-P_0, pts[3]+pts[4]-2 P_0

assert Order(h(ZN.2)) eq 40;
assert Order(h(ZN.3+ZN.4-5*ZN.2)) eq 2;

// Hence J(\Q)= (\Z/40) (pts[2]-P0)+ (\Z/2) (pts[3]+pts[4]-5 pts[2] + 3P0).

// We will construct the degree 2 place that corresponds to pts[3]+pts[4].

decomp:=Decomposition(Divisor(K.1+2));  // Note that the x-coordinate of 
					// of pts[3], pts[4] is -2.

decomp:=[D[1] : D in decomp | D[2] ge 0]; // Throw away the multiplicities and poles.
decomp:=[ D : D in decomp | IsIsomorphic(ResidueClassField(D),QuadraticField(5))]; 


assert #decomp eq 1;

D:=decomp[1];

assert Evaluate(K.1,D) eq -2;

// Thus D is pts[3]+pts[4].


P0:=Place(X![0,0,1]);  // base point of Abel-Jacobi map
P:=Place(X![1/2,-1/2,1]); // pts[2]

D1:=P-P0;
D2:=D-5*P+3*P0;  
// so J(Q)=(Z/40)D1 + (Z/2) D2

assert &or[ IsPrincipal(a*D1) : a in [1..39] ] eq false;
assert IsPrincipal(40*D1); // Sanity check: D1 has order 40 in J(\Q).
assert IsPrincipal(D2) eq false;
assert IsPrincipal(2*D2) eq true; // D2 has order 2 in J(\Q).
assert &or[ IsPrincipal(a*D1+D2) : a in [0..39] ] eq false; // another check!

// We determine Sym^2(X)(\Q). 

deg2:=[a*D1+b*D2+2*P0 : a in [0..39], b in [0..1]]; 
// Every element of Sym^2(X)(\Q) is linearly equivalent to one of these.

sym2:=[];

for D in deg2 do
	V,pi:=RiemannRochSpace(D);
	assert Dimension(V) le 1; // As X is a plane quartic, not hyperelliptic!
	if Dimension(V) eq 0 then
		if IsEffective(D) then
			Append(~sym2,D);
		end if;
	else
		Append(~sym2,D+Divisor(pi(V.1)));	
	end if;
end for;

// sym2 now contains all the elements of Sym^2(X)(\Q) 

places:=&join{ {D[1] : D in Decomposition(A)} : A in sym2  };
// All the rational and quadratic points.


rats:={pl : pl in places | Degree(ResidueClassField(pl)) eq 1}; 
// The rational points on X.

quads:=[pl : pl in places | pl in rats eq false];
// The quadratic points on X.

disc:=function(pl); // For pl a quadratic place
			// return d such that Q(\sqrt{d})
			// is the residue class field.
	K:=ResidueClassField(pl);
	assert Degree(K) eq 2;
	d:=Discriminant(MaximalOrder(K));
	if d mod 4 eq 0 then
		d:=d div 4;
	end if;
	return d;
end function;

discSort:=func<pl1,pl2 | disc(pl1)-disc(pl2)>;

Sort(~quads,discSort);  // We sort the quadratic places of X
	 // according to d where \Q(\sqrt{d}) is the residue class field


// We now print the j-invariants of these points
// together with information to show that these points
// are modular.

for pl in quads do
	d:=disc(pl);
	print d;
	L<m>:=QuadraticField(d);
	pt:=Representative(Support(Cluster(pl),L));
	pt:=Eltseq(pt);
	R:=LCM([Denominator(a) : a in pt]);
	pt:=[R*a : a in pt];
	print "Point on X defined over \Q(m) where m is square root of", d;
	pt;
	print "has j-invariant";
	jpl:=Evaluate(j,pl);
	if Type(jpl) eq Infty then // cusp
		print jpl;
	else
		jpl:=Roots(MinimalPolynomial(jpl),L)[1,1];
		print jpl;
		if d le 0 then
			print "field is complex quadratic";
		
		else
			Epl:=EllipticCurveWithjInvariant(jpl);
			tf,D:=HasComplexMultiplication(Epl);
			if tf then
				print "j is modular because of complex multiplication by",D;
			else 
				assert IsIrreducible(DivisionPolynomial(Epl,7));
				// This shows that the image mod 7 is not Borel.
				OL:=MaximalOrder(L);
				ps:=[fact[1] : fact in Factorisation(2*OL)];
				ps:=[p : p in ps | Valuation(jpl,p) lt 0];
				ps:=[p : p in ps | IsDivisibleBy(Valuation(jpl,p),7) eq false];
				assert #ps ne 0;
				// This shows that the image mod 7 is not dihedral or exceptional
				// (since the image of inertia at any prime
				// in the non-empty set ps has order divisible by 7).
				print "j is modular because im rho_{E,7} contains SL_2(F_7)";
			end if;
		end if;
	end if;
	print "++++++++++++++++++++++++++++++++++++++++++++++++";
end for;

