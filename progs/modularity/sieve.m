
// X is a curve over a finite field F
// j is an element of the function field of X
// this function computes all the points on X over F
// and splits them into four lists:
// pts0, pts1728, ptsinf are points where j takes the value 0, 1728, \infty respectively
// ptsrest is a list of lists of points (with value of j not 0, 1728, \infty).
// A point P \in X(F) belongs to the ith list in ptsrest where
// i=Log(j(P))+1, where Log is the discrete logarithm on F.

points:=function(X,j);
	F:=BaseRing(X);
	assert Characteristic(F) in {2,3} eq false;
	// if the characteristic of F is 2 or 3 then
	// 1728=0. The subdivision of points below
	// does not make sense!
	pts0:=[];
	pts1728:=[];
	ptsinf:=[];
	ptsrest:=[ [] : a in F  ];
	for Q in Points(X) do
		jQ:=j(Q);
		if Type(jQ) eq Infty then // Q is a cusp
			Append(~ptsinf,Q);
		elif jQ eq 0 then  
			Append(~pts0,Q);
		elif jQ eq 1728 then
			Append(~pts1728,Q);
		else
			ind:=Log(jQ)+1;
			ptsrest[ind]:=ptsrest[ind] cat [Q];
		end if;
	end for;
	return pts0, pts1728, ptsinf, ptsrest;
end function;


// X, Y are curves over a finite field F
// and jX, jY are elements of their function fields
// such that jX : X -> P^1, jY : Y-> P^1
// are ramified only above 0, 1728, \infty.
// Let Z be the normalization of X x_\P^1 Y.
// Returns the image of Z(F) in X(F) x Y(F).
// The following assumptions are made by the script:
// the ramification indicies above 0 are all 1 or 3;
// the ramification indicies above 1728 are all 1 or 2;
// the ramification indicies above \infty for jX are coprime
// to the ramification indicies for jY;
// the characteristic is coprime to all the ramification indicies.
fibreProd:=function(X,jX,Y,jY);
	F:=BaseRing(X);
	assert F eq BaseRing(Y);
	assert Characteristic(F) notin {2,3};
	X0,X1728,Xinf,Xrest:=points(X,jX);
	Y0,Y1728,Yinf,Yrest:=points(Y,jY);
	assert #Xrest eq #Yrest;
	prs:=[* *];
	for i in [1..#Xrest] do
		for P in Xrest[i] do
			for Q in Yrest[i] do
				// The index i is 1+log j.
				// P and Q have the same log j
				// and so the same j.
				prs:=prs cat [* [* P, Q *] *];
			end for;
		end for;
	end for;
	for P in X0 do
		pl:=Place(P);
		m:=Valuation(jX,pl);
		assert m in [1,3];
		alpha:=LeadingCoefficient(Expand(jX,pl));
		for Q in Y0 do
			ql:=Place(Q);
			n:=Valuation(jY,ql);
			assert n in [1,3];	
			beta:=LeadingCoefficient(Expand(jY,ql));
			d:=GCD(m,n);
			if IsPower(alpha/beta,d) then
				// P, Q both map to zero, so
				// (P,Q) is a point on the fibre
				// product. The condition
				// that alpha/beta is a d-th point
				// is the condition that (P,Q)
				// lifts to a F-point on the normalization Z
				// (see paper for details).
				prs:=prs cat [* [* P, Q *] *];
			end if;
		end for;
	end for;
	for P in X1728 do
		pl:=Place(P);
		m:=Valuation(jX-1728,pl);
		assert m in [1,2];
		alpha:=LeadingCoefficient(Expand(jX-1728,pl));
		for Q in Y1728 do
			ql:=Place(Q);
			n:=Valuation(jY-1728,ql);
			assert n in [1,2];	
			beta:=LeadingCoefficient(Expand(jY-1728,ql));
			d:=GCD(m,n);
			if IsPower(alpha/beta,d) then
				prs:=prs cat [* [* P, Q *] *];
			end if;
		end for;
	end for;
	for P in Xinf do
		pl:=Place(P);
		m:=Valuation(jX,pl);
		assert GCD(m,Characteristic(F)) eq 1;
		for Q in Yinf do
			ql:=Place(Q);
			n:=Valuation(jY,ql);
			assert GCD(n,Characteristic(F)) eq 1;
			d:=GCD(m,n);
			assert d eq 1;
			// This guarantees that (P,Q) lifts
			// to a F-point of Z.
			prs:=prs cat [* [* P, Q *] *];
		end for;
	end for;
	return prs;
end function;



// q is a prime power.
// Returns
// X: the curve X(d7) over \F_q
// j: the j-map as an element of the function field of X(d7)
// J: the Jacobian elliptic curve of X(d7) over \F_q
// toJ: the Abel-Jacobi map X(d7) -> J 
//      given by sending P to P-(5/2,7/4)
// [toJ( (5/2,7/4) ) , toJ( (5/2, 7/4)) ] This is the image
// of the Mordell--Weil group J(\Q) in J(\F_q)
Xd7:=function(q);
	F:=GF(q);
	Fx<x>:=PolynomialRing(F);
	// X(d7) 
	X:=HyperellipticCurve(-7*(x^4 - 10*x^3 + 27*x^2 - 10*x - 27));	
	pt1:=X![5,7,2];
	pt2:=X![5,-7,2];
	K<x,y>:=FunctionField(X);
	num:= (x^2-5*x+8)^3*(x^2-5*x+1)^3*(x^4-5*x^3+8*x^2-7*x+7)^3*(x+1)^3*x;
	den:=(x^3-4*x^2+3*x+1)^7;
	// map X -> X(1) sends (v:y:w) --> num/den
	// here v/w is the x-coordinate on X
	J,toJ:=EllipticCurve(X,pt1);
	return X,num/den,J,toJ,[toJ(pt1),toJ(pt2)];
end function;

// q is a prime power.
// Returns
// X: the curve X(e7) over \F_q
// j: the j-map as an element of the function field of X(e7)
// J: the Jacobian elliptic curve of X(e7) over \F_q
// toJ: the Abel-Jacobi map X(e7) -> J 
//      given by sending P to P-(-1/3,14/9)
// [toJ( (-1/3,14/9) ) , toJ( (-1/3, -14/9)) ] This is the image
// of the Mordell--Weil group J(\Q) in J(\F_q)
Xe7:=function(q);
	F:=GF(q);
	Fx<x>:=PolynomialRing(F);
	// X(e7)
	X:=HyperellipticCurve(7*(16*x^4 + 68*x^3 + 111*x^2 + 62*x + 11));
	pt1:=X![-1,14,3];
	pt2:=X![-1,-14,3];
	K<x,y>:=FunctionField(X);
	// Map to the j-line is given by (x,y) :-> num(x,1)/den(x,1) 
	num:=(4*x^2+5*x+2)^3*(x^2+3*x+4)^3*(x^2+10*x+4)^3*(3*x+1)^3;
	den:=(x^3+x^2-2*x-1)^7;
	J,toJ:=EllipticCurve(X,pt1);
	return X,num/den,J,toJ,[toJ(pt1),toJ(pt2)];
end function;

// q is a prime power.
// Returns
// X: the curve X(b3,b5) over \F_q
// j: the j-map as an element of the function field of X
// and the image
// of the Mordell--Weil group X(\Q) in X(\F_q)
// (X is a Weierstrass elliptic curve, so we view it
// as its own Jacobian, where the Abel-Jacobi map
// is P :-> P-infty)

Xb3b5:=function(q);
	F:=GF(q);
	X:=EllipticCurve([F | 1,1,1,-10,-10]);
	Zabc<a,b,c>:=PolynomialRing(Integers(),3);
	num:= 744*a^22 + a^21*b + 21610291*a^21*c + 196775*a^20*b*c + 19679221742*a^20*c^2 + 
    864535710*a^19*b*c^2 + 3097839821170*a^19*c^3 + 280874875745*a^18*b*c^3 + 
    160398172634520*a^18*c^4 + 23427619194045*a^17*b*c^4 + 
    3581173749860067*a^17*c^5 + 744608178506178*a^16*b*c^5 + 
    39574700116945818*a^16*c^6 + 10955908577873520*a^15*b*c^6 + 
    221300586074546016*a^15*c^7 + 81503050771678260*a^14*b*c^7 + 
    452164484292474720*a^14*c^8 + 285194718207394695*a^13*b*c^8 - 
    1536589608349883805*a^13*c^9 + 55762990556996795*a^12*b*c^9 - 
    11573711625503130004*a^12*c^10 - 3279590771772625931*a^11*b*c^10 - 
    23644170283687901576*a^11*c^11 - 11441615253798830655*a^10*b*c^11 + 
    14841566873865098288*a^10*c^12 - 10484829378897207230*a^9*b*c^12 + 
    163746939998047776840*a^9*c^13 + 31407913121012464215*a^8*b*c^13 + 
    297626145005589222540*a^8*c^14 + 106648797633809053140*a^7*b*c^14 + 
    72591051644033404488*a^7*c^15 + 116765289776668630797*a^6*b*c^15 - 
    565465392032860949808*a^6*c^16 - 13918837770636323685*a^5*b*c^16 - 
    1009732256085615281421*a^5*c^17 - 177759025944909563070*a^4*b*c^17 - 
    732163177372393977090*a^4*c^18 - 205255459996057885640*a^3*b*c^18 - 
    110250390131324956040*a^3*c^19 - 110429392381676331040*a^2*b*c^19 + 
    186005298368862992624*a^2*c^20 - 27254582640918459024*a*b*c^20 + 
    122302223586818158576*a*c^21 - 1931362137071926240*b*c^21 + 
    23939065157786620512*c^22;
	den:=
a^22 - 108*a^21*c + 5341*a^20*c^2 - 159470*a^19*c^3 + 3185320*a^18*c^4 - 
    44411312*a^17*c^5 + 434502416*a^16*c^6 - 2866286432*a^15*c^7 + 
    10827879680*a^14*c^8 - 2448660480*a^13*c^9 - 203804164096*a^12*c^10 + 
    908424511488*a^11*c^11 - 199387774976*a^10*c^12 - 10229529968640*a^9*c^13 + 
    22534149898240*a^8*c^14 + 51427401531392*a^7*c^15 - 202726751338496*a^6*c^16
    - 174581830647808*a^5*c^17 + 916717819658240*a^4*c^18 + 
    780653255720960*a^3*c^19 - 1917548278841344*a^2*c^20 - 
    2955487255461888*a*c^21 - 1125899906842624*c^22;
	K<x,y>:=FunctionField(X);
	j:=Evaluate(num,[x,y,1])/Evaluate(den,[x,y,1]);
	return X,j, 
	[X![0,1,0], X![-1,0], X![-2,-2], X![8,-27],
			X![3,-2], X![-13/4,9/8], X![-2,3], X![8,18]];
end function;


// q is a prime power.
// Returns
// X: the curve X(s3,b5) over \F_q
// j: the j-map as an element of the function field of X
// and the image
// of the Mordell--Weil group X(\Q) in X(\F_q)
// (X is a Weierstrass elliptic curve, so we view it
// as its own Jacobian, where the Abel-Jacobi map
// is P :-> P-infty)

Xs3b5:=function(q);
	F:=GF(q);
	X:=EllipticCurve([F | 1, 1, 1, -5, 2 ]);

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
	K<x,y>:=FunctionField(X);
	j:=Evaluate(num,[x,y,1])/Evaluate(den,[x,y,1]);
	return X,j, 
			[X![0,1,0], X![3/4,-7/8], X![0,-2], X![2,-4],
			X![1,-1], X![-3,1], X![0,1], X![2,1]];
end function;


// The input is two labels and a prime.
// label1 is either "Xb3b5","Xs3b5". This denotes the first curve X
// which is either X(b3,b5) or X(s3,b5).
// label2 is either "Xd7","Xe7". This denotes the second curve Y
// which is either X(d7) or X(e7).
// p is a prime \ge 11.
// Let Z be the normalization of the fibre product
// of X and Y. 
// Write Sym^2 Z for the symmetric square of Z,
// and JX, JY for the Jacobians of X, Y.
// There is a natural map
// alpha : Sym^2 Z -> JX x JY
// obtained by composing Z -> X x Y
// with the Abel-Jacobi maps X x Y -> JX x JY.
// (Here, as X is a Weierstrass elliptic curve, we 
// take JX=X). The function computes the 
// red^{-1} alpha (Sym^2 Z (\F_p)).
// The result is a subset of JX(\Q) x JY(\Q).
// We have imposed ordering on the elements of JX(\Q), JY(\Q)
// as listed in the above functions. Thus the function returns
// a list of pairs [i,j] where i=1,..,8 and j=1,2.

pSieve:=function(label1,label2,p);
	assert p ge 11;  // 3, 5 are primes of bad reduction for X(b3,b5)
			// and X(s3,b5).
			// 7 is a prime of bad reduction for X(d7) and X(e7).
			// 2 is a prime of bad reduction for the models
			// used for X(d7) and X(e7). There are models
			// with good reduction at 2, but anyway we
			// want to employ primes that do not divide
			// the ramification indicies of the j-maps.
	assert IsPrime(p);
	F:=GF(p);
	F2:=GF(p^2);
	assert label1 in ["Xb3b5","Xs3b5"];
	assert label2 in ["Xd7","Xe7"];
	if label1 eq "Xb3b5" then
		X,jX,redJXQ:=Xb3b5(p); // redJXQ is the reduction of JX(\Q)
					// in JX(F_p), as an ordered list
					// of eight elements.
		X2,jX2:=Xb3b5(p^2);    // For the points on the symmetric
					// square we need the points on X
					// over F_p and F_{p^2}
					// so we construct both curves.
	else
		X,jX,redJXQ:=Xs3b5(p);
		X2,jX2:=Xs3b5(p^2);
	end if;
	assert #redJXQ eq 8;
	if label2 eq "Xd7" then
		Y,jY,JY,toJY,redJYQ:=Xd7(p);
		Y2,jY2,JY2,toJY2:=Xd7(p^2);
	else
		Y,jY,JY,toJY,redJYQ:=Xe7(p);
		Y2,jY2,JY2,toJY2:=Xe7(p^2);
	end if;
	assert #redJYQ eq 2; 
	fb1:=fibreProd(X,jX,Y,jY);  // These are the points of Z over F_p
	fb2:=fibreProd(X2,jX2,Y2,jY2); // These are the points of Z over F_p^2 
	indprs:={};
	for pr1,pr2 in fb1 do // The F_p-points of the 
				// symmetric square consists of pairs
				// of F_p points, ...
		s1:=pr1[1]+pr2[1];  // The image under the Abel-Jacobi
					// map in JX.
		ind1:=[i : i in [1..8] | s1 eq redJXQ[i]];
					// The indicies of the pull-back
					// to JX(Q).
		s2:=toJY(pr1[2])+toJY(pr2[2]); // The image under the
						// Abel-Jacobi map
						// in JY
		ind2:=[i : i in [1,2] | s2 eq redJYQ[i]];
					// The indicies of the pull-back
					// to JY(Q).
		indprs:=indprs join {[i,j] : i in ind1, j in ind2};	
	end for;
	for pr in fb2 do // .. or a pair of conjugate  F_{p^2} - points.
		s1:=pr[1]+X2![a^p : a in Eltseq(pr[1])]; 
			// Conjugating using Frobenius.
		s1:=X(F)!Eltseq(s1);		
		ind1:=[i : i in [1..8] | s1 eq redJXQ[i]];
		pr2:=toJY2(pr[2]);	
		s2:=pr2+JY2![a^p : a in Eltseq(pr2)];
		s2:=JY(F)!Eltseq(s2);
		ind2:=[i : i in [1,2] | s2 eq redJYQ[i]];
		indprs:=indprs join {[i,j] : i in ind1, j in ind2};	
	end for;
	return indprs;
 end function;



// The input is two labels and a list of primes.
// label1 is either "Xb3b5","Xs3b5". This denotes the first curve X
// which is either X(b3,b5) or X(s3,b5).
// label2 is either "Xd7","Xe7". This denotes the second curve Y
// which is either X(d7) or X(e7).
// Computes the intersection in J_X(\Q) x J_Y(\Q) described 
// \cap_{p=p_i} red_p^{-1} alpha (Sym^2 Z (\F_p))
sieve:=function(label1,label2,primes);
	indprs:={[i,j] : i in [1..8], j in [1,2]};
	for p in primes do
		indprsp:=pSieve(label1,label2,p);
		indprs:=indprs meet indprsp;
		print "++++++++++++++++++++++++++++++++++++++++++++++++";
		print p, indprsp, indprs;
	end for;
	return indprs;
end function;


// We now verify the results claimed in the paper for 
// the four curves X(b3,b5,d7), X(s3,b5,d7), X(b3,b5,e7), X(s3,b5,e7)

// Warning! This part is very slow (perhaps 2 hours).

//==========================================================

// X(b3,b5,d7);

indprs:=sieve("Xb3b5","Xd7",PrimesInInterval(11,100));
assert indprs eq { [1,2], [5,2], [8,2] };

// 1, 5, 8 denote the divisors [0], [ (3,-2)-infty] , [ (8,18)-infty ]
// on X(b3,b5) (see the list of points in the command Xb3b5).
// 2 denotes the divisor [(5/2,-7/4) - (5/2,7/4)] on X(d7)
// (see the list of points in the command Xd7).

// =======================================================

// X(s3,b5,d7);

indprs:=sieve("Xs3b5","Xd7",PrimesInInterval(11,100));
assert indprs eq { [1,2], [4,2], [5,2] };

// 1, 4, 5 denote the divisors [0], [ (2,-4)-infty] , [ (1,-1)-infty ]
// on X(s3,b5) (see the list of points in the command Xs3b5).
// 2 denotes the divisor [(5/2,-7/4) - (5/2,7/4)] on X(d7)
// (see the list of points in the command Xd7).

// ========================================================

// X(b3,b5,e7);

indprs:=sieve("Xb3b5","Xe7",PrimesInInterval(11,100));
assert indprs eq { };

// Returns the empty set. So X(b3,b5,e7) has no quadratic points.

// =======================================================

// X(s3,b5,e7);

indprs:=sieve("Xs3b5","Xe7",PrimesInInterval(11,100));
assert indprs eq { [7,2] };

// Note 7 denotes the divisors [ (0,1)-infty ]
// on X(s3,b5) (see the list of points in the command Xs3b5).
// Note 2 denotes the divisor [ (-1/3,-14/9) - (-1/3,14/9) ] on X(e7)
// (see the list of points in the command Xe7).


