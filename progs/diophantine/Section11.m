// This Magma script carries out the computations 
// described in Section 11 of the paper. Namely, it computes
// the eigenforms in Table 1, and the (factorizations)
// of the constants B_S(ff) appearing in Table 2.

eigenNum:=0;
for p in [5,7,11,13] do 
	print "+++++++++++++++++++++"; 
	print "Treating the case p=",p; 
	L<zet>:=CyclotomicField(p);
	K:=sub<L | zet+1/zet>; // Q(zeta_p)^+.
	OK:=MaximalOrder(K); 
	for cs in [1,2] do 
	// cs will denote the case number.
	// cs=1 corresponds to p \nmid x
	// cs=2 corresponds to p \mid x.
		if cs eq 1 then
			print "treating the case", p, "doesn't divide x";
		else
			print "treating the case", p, "divides x";
		end if;
		if p in [5,7,11] then
			thj:=OK!(zet+1/zet); // As in Section 11 we take j=1 
			thk:=OK!(zet^2+1/zet^2); // and k=2.
			M:=K;
			OO:=MaximalOrder(M);
		elif cs eq 1 then    // p=13 and 13 doesn't divide x
			thj:=OK!(zet+1/zet);  // Again as in Section 11.
			thk:=OK!(zet^5+1/zet^5); 
			M:=K;
			OO:=MaximalOrder(M);
		else
			Kp:=Subfields(K,3)[1,1];
			assert Degree(Kp) eq 3;  // The unique real subfield of degree 3.
			thj:=OK!(zet+1/zet);  // Again as in Section 11.
			thk:=OK!(zet^5+1/zet^5); 
			M:=Kp;
			OO:=MaximalOrder(M);
		end if;
		if p ne 13 or cs eq 1 then
			P:=Factorisation(p*OO)[1,1];
			if cs eq 1 then
				level:=2*OK;
			else
				level:=2*P;
			end if;
		else
			P:=Factorisation(p*OO)[1,1];
			level:=2*P;  
		end if;
		//======================================
		//
		//  Given eta, mu, computes the pair u(eta,mu)
		//  and v(eta,mu).
		//
		//======================================
		uv:=function(eta,mu);
			if cs eq 1 then
				u:=(thj+2)*eta^2+(thj-2)*mu^2;
				v:=-(thj-2)/(thk-2)*((thk+2)*eta^2+(thk-2)*mu^2);
				return u,v;
			else
				u:=((thj+2)*eta^2+(thj-2)*mu^2)/(thj-2);
				v:=-((thk+2)*eta^2+(thk-2)*mu^2)/(thk-2);
				return u,v;
			end if;
		end function;
		//=========================================
		//
		// Given:
		// an eigenform ff; 
		// a prime ideal Q of OO_K (if p ne 13 or cs=1) or of OO_K^\prime (otherwise);
		// integers eta, mu;
		// returns B_Q(ff,eta,mu) in the notation of Section 11.
		//
		//=========================================
		BQ:=function(ff,Q,eta,mu);	
			aQ:=HeckeEigenvalue(ff,Q);
			FQ,piQ:=ResidueClassField(Q);	
			u,v:=uv(eta,mu);
			w:=-u-v;
			a2:=piQ(M!(v-u));
			a4:=piQ(M!(-u*v));
			if piQ(M!(u^2*v^2*w^2)) eq 0 then
				c4:=M!(16*(w^2-u*v));
				c6:=M!(-32*(u-v)*(v-w)*(w-u));
				gam:=piQ(-c4/c6);
				assert gam ne 0;
				if IsSquare(gam) then 
					return ((Norm(Q)+1)-aQ);
				else
					return ((Norm(Q)+1)+aQ);
				end if;
			else
				E:=EllipticCurve([0,a2,0,a4,0]);
				return (TraceOfFrobenius(E)-aQ);
			end if;
		end function;
		//=========================================
		//
		// Given:
		// an eigenform ff; 
		// the maximal order Off of the field of Hecke eigenvalues Off;
		// a rational prime q;
		// integers eta, mu;
		// returns B_q(ff,\eta,\mu) in the notation of Section 11.
		//
		//=========================================
		Bqetamu:=function(ff,Off,q,eta,mu);	
			Qlist:=[fact[1] : fact in Factorisation(q*OO)];
			B:=0*Off;
			for Q in Qlist do
				B:=B+BQ(ff,Q,eta,mu)*Off;
			end for;
			return B;	
		end function;
		//=========================================
		//
		// Given:
		// an eigenform ff; 
		// the maximal order Off of the field of Hecke eigenvalues Off;
		// a rational prime q;
		// returns B_q(ff) in the notation of Section 11.
		//
		//=========================================
		Bq:=function(ff,Off,q);
			B:=q*Off;
			for eta, mu in [0..(q-1)] do
				if eta ne 0 or mu ne 0 then
					B:=B*(Bqetamu(ff,Off,q,eta,mu));
				end if;
			end for;
			return B;
		end function;
		//=========================================
		//
		// Given:
		// an eigenform ff; 
		// the maximal order Off of the field of Hecke eigenvalues Off;
		// a set S of rational primes q different from 2, p
		// returns B_S(ff) in the notation of Section 11.
		//
		//=========================================
		BS:=function(ff,Off,S);
			B:=&+[Bq(ff,Off,q) : q in S];
			return Integers()!Norm(B);
		end function;
		if p in [5,7] then
			S:=[3];
		elif p eq 11 then
			S:=[ 23, 43 ];
		elif cs eq 1 then
			S:=[79, 103];
		else
			S:=[3,5,31,47];
		end if;
		H:=HilbertCuspForms(M,level); 
		Hnew:=NewSubspace(H); 
		decomp:=NewformDecomposition(Hnew);
		if #decomp eq 0 then
			print "the space of newforms is trivial";
		end if;
		for i in [1..#decomp] do
			eigenNum:=eigenNum+1;
			print "+++++++++++";
			print "Dealing with the", eigenNum, "-th eigenform";
			V:=decomp[i];
			ff:=Eigenform(V);
			Qff:=HeckeEigenvalueField(V);
			print "this has Hecke eigenvalue field of degree", Degree(Qff);
			Off:=MaximalOrder(Qff);
			B:=BS(ff,Off,S);
			print "Factoristion of B_S(ff)", Factorisation(B);
			survivors:=[l : l in PrimeDivisors(Norm(B)) | l in {2,3,p} eq false];
			print "surviving primes ell=", survivors;
			print "list S of primes used in the sieve=", S;
		end for;	
	end for;
end for;
	
