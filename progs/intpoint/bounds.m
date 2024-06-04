

// \partial_K in the notation of Lemma 4.2
// input d is the degree of K
partialK:=function(d);
	if d in {1,2} then
		return Log(2)/d;
	else
		return 0.25*(Log(Log(d))/Log(d))^3;
	end if;
end function;


// \partial_K^\prime in the notation of Lemma 4.3
// input d is the degree of K
partialDashK:=function(d);
	pK:=partialK(d);
	pi:=Pi(RealField());
	return (1+pi^2/pK^2)^0.5;
end function;


// partial_{L/K} in the notation of Lemma 7.1
// input dK, dL are the degrees of K, L
partialLoverK:=function(dK,dL);
	pK:=partialK(dK);
	pdK:=partialDashK(dK);
	m:=Max([dL,dK*pdK,0.16*dK/pK]);
	return m;
end function;

// returns c_1(K),\dots,c_5(K)
// in the notation of Lemmas 6.1, 6.2, 6.3
cConstants:=function(K);
	d:=Degree(K);
	u,v:=Signature(K);
	r:=u+v-1;
	pK:=partialK(d);
	c1:=Factorial(r)^2/(2^(r-1)*d^r)+0.0;
	c2:=c1*(d/pK)^(r-1);
	c3:=c1*d^r/pK;
	c4:=r*d*c3;
	c5:=r^(r+1)/(2*pK^(r-1));
	return c1,c2,c3,c4,c5;
end function;

// returns C(L,n) in the notation of Lemma 7.2
// input d (degree of L)
// n (number of alphas in the "linear form")
CConstant:=function(d,n);
	return 3*30^(n+4)*(n+1)^5.5*d^2*(1+Log(d));
end function;


// upper bound for the regulator of number field K given by Lemma 5.1
// input OOK: the maximal order of K
regBound:=function(OOK);
	K:=NumberField(OOK);
	d:=Degree(K);
	u,v:=Signature(K);
	DK:=AbsoluteValue(Discriminant(OOK));
        if u gt 0 then // w will be the number of roots of unity
			//
                w:=2;  // MAGMA doesn't seem to check if a field has
			// real embeddings before it computes the 
			// roots of unity!!
		// and it is very slow for fields with real embd!!
        else
                w:=#TorsionUnitGroup(OOK);
        end if;
	pi:=Pi(RealField());
	a:=2^(-v)*SquareRoot(DK/pi^d);
        f:=2^(-u)*w*a^2*2^(d+1);
        for t in [1..999] do
                s:=2-t/1000.0;
                f1:=2^(-u)*w*a^s*Gamma(s/2)^u*Gamma(s)^v*s^(d+1)*(s-1)^(1-d);
                f:=Min(f,f1);
        end for;
        return f;
end function;


// This function gives a bound on $x$ such that
// x-\alpha=\kappa \xi^2
// the bound is the one given in Thm 3.
// input p, k
// p is the monic polynomial defining \alpha
// k is a polynomial such that $k(\alpha)=\kappa$.

logxBoundk:=function(p,k);
	d:=Degree(p);
	Qa1<alpha1>:=NumberField(p);
	Qa2<alpha2>:=NumberField(p);
	Qa12<a>:=MergeFields(Qa1,Qa2)[2];
	if Degree(Qa12) ne d*(d-1) then
		error("program written on assumption that Galois action is 2-transitive"); // this makes K_1, K_2, K_3 in Thm 2 isomorphic 
	end if;
	OO:=MaximalOrder(Qa12);
	OOy<y>:=PolynomialRing(OO);
	kappa1:=OO!(Qa12!Evaluate(k,alpha1));
	kappa2:=OO!(Qa12!Evaluate(k,alpha2));
	kappa12:=kappa1*kappa2;
	if #Factorisation(y^2-kappa12) eq 1 then
		subOrderK:=ext<OO | y^2-kappa12>;
		subOrderK:=AbsoluteOrder(subOrderK);
		D:=Discriminant(subOrderK);
		for p in PrimeDivisors(D) do
        	        subOrderK:=pMaximalOrder(subOrderK,p);
                	// remarkably this gives the maximal order much
	                // quicker than MaximalOrder();
        	end for;
		OOK:=subOrderK; // maximal order
		dL:=4*d*(d-1)*(d-2);  //upper bound for the degree of L
	else
		OOK:=OO;
		dL:=d*(d-1)*(d-2);
	end if;
	R:=regBound(OOK); // upper bound for regs of K_i
	//print "regulator bound is", R;
	K:=NumberField(OOK);
	dK:=Degree(K);
	u,v:=Signature(K);
	r:=u+v-1;
	//print "unit rank is", r;
	cs1,cs2,cs3,cs4,cs5:=cConstants(K); // $c^*_j(K_i)$
	N:=(Norm((Qa12!kappa1)*((Qa12!alpha1)-(Qa12!alpha2))))^2;
	hkappa:=AbsoluteLogarithmicHeight(kappa1);
	halpha:=AbsoluteLogarithmicHeight(alpha1);
	Hs:=cs5*R+Log(N)/Degree(K)+hkappa;
	As1:=2*Hs*CConstant(dL,2*r+1)*cs1^2*partialLoverK(dL,dL)*partialLoverK(dK,dL)^(2*r)*R^2;
	As2:=2*Hs+As1+As1*Log((2*r+1)*Max(cs4,1));
	return 8*As1*Log(4*As1)+8*As2+Hs+20*Log(2)+13*hkappa+19*halpha;
end function;


// gives a bound on log(x)
// for integral points on the curve
// d y^2 = p(x)
// input: p, knownPoints
// p is a monic polynomial in $x$ with integral coefficients
// points is a list of known rational points on the model Y^2=d*p(X)
// Crucial Assumption 1: every integral point is congruent to an
// element of knownPoints modulo 2J(\Q)
// Crucial Assumption 2: p is irreducible and the action of Galois
// on its roots is 2-transitive

logxBoundSimplified:=function(p,knownPoints);
	x:=Parent(p).1;
	kappaSet:={};
	for P in knownPoints do
		if P[3] eq 0 then
			kappaSet:=kappaSet join {Parent(p)!1};
		else
			num:=P[1];
			denom:=P[3];
			kappaSet:=kappaSet join {denom*x-num};
		end if;
	end for;
	return Max({logxBoundk(p,k) : k in kappaSet});	
end function;

// gives a bound on log(x)
// for integral points on the curve
// y^2 = h(x)
// input: h, knownPoints
// h is a polynomial in $x$ with integral coefficients with degree 5
// points is a list of known rational points on the model y^2=h(x)
// Crucial Assumption 1: every integral point is congruent to an
// element of knownPoints modulo 2J(\Q)
// Crucial Assumption 2: h is irreducible and the action of Galois
// on its roots is 2-transitive
// Assumption 2 is checked. Assumption 1 is not.

logxBound:=function(h,knownPoints);
	if (Degree(h) ne 5)  then
		error "degree of poly in logxBound must be 5";
	end if;
	if not IsIrreducible(h) then
		error "poly in logxBound must be irreducible";
	end if;
	if not IsTransitive(GaloisGroup(h),2) then
		error "poly in logxBound must have 2-transitive Galois group";
	end if;
	x:=Parent(h).1;
	a0,a1,a2,a3,a4,a5:=Explode(Coefficients(h));
	p:=x^5+a4*x^4+a5*a3*x^3+a5^2*a2*x^2+a5^3*a1*x+a5^4*a0;
	kPNew:=[];
	for P in knownPoints do
		Pnew:=<Integers()!(a5*P[1]),Integers()!(a5^2*P[2]),Integers()!(P[3])>;
		g:=GCD(Pnew[1],Pnew[3]);
		Pnew:=<Pnew[1] div g, Pnew[2] div g^3, Pnew[3] div g>;
		Append(~kPNew,Pnew);
	end for;
	return logxBoundSimplified(p,kPNew);
end function;
