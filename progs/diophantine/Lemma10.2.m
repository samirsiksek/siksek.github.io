// Here we carry out the computation described in the
// proof of Lemma 10.2 of the paper.

for p in [5,7,11,13] do
	print "++++++++++++++++++++++++++++++++";
	print "Treating p=",p;
	L<zet>:=CyclotomicField(p);
	K<th>:=sub<L | zet+1/zet>;
	OK:=MaximalOrder(K);
	assert NarrowClassNumber(K) eq 1;
	U,phi:=UnitGroup(K);
	// We will determine a system of totally positive units.
	V:=U;
	A:=AbelianGroup([2]);
	for i in [1..((p-1) div 2)] do
		img:=[];
		for u in OrderedGenerators(U) do
			if RealEmbeddings(phi(u))[i] gt 0 then
				Append(~img,A!0);
			else
				Append(~img,A!1);
			end if;
		end for;
		psi:=hom<U->A | img>;
		V:=V meet Kernel(psi);
	end for;
	posunits:=[phi(U!v) : v in OrderedGenerators(V)];
	assert &and[IsTotallyPositive(u) : u in posunits];
	assert &and[Norm(u) eq 1 : u in posunits];
	print "The following is our system of totally positive units",
		[K!u : u in posunits];
	G,S,mu:=AutomorphismGroup(K);
	subG:=[D`subgroup : D in Subgroups(G)];
	BSet:={};
	for D in subG do   // D is a subgroup of the Galois group.
		T,pi:=quo<G|D>; // T is the cosets of G/D.
		for Tp in Subsets({q : q in T}) do // Tp is T^prime
					// in the notation of the paper.
			if #Tp ne 0 and #Tp ne #T then
				// We check that Tp is non-empty and proper.
				TpD:=[mu(t@@pi) : t in Tp];
				// TpD is the set of products
				// sigma tau 
				// where sigma is in D
				// tau is in T^prime.
				BTpD:=GCD( [ Integers()!Norm(&*[u@t : t in TpD]-1)  : u in posunits  ]  );
				// This B_{T^prime,D}(u_1,...,u_d) in the
				// notation of the paper.
				BSet:=BSet join {BTpD};
			end if;
		end for;
	end for;
	print "The set of B_{T^prime,D}(u_1,...,u_d) is ", BSet;
	lset:=&cat[PrimeDivisors(B) : B in BSet];
	lset:=[l : l in lset | l ge 5];  // We're only interested in ell >= 5.
	print "The set of surviving primes ell is", lset;
	for l in lset do
		Sl:={fact[1] : fact in Factorisation(l*OK)}; // As in the paper
								// this is the
								// set of primes 								// above l.
		for S in Subsets(Sl) do
			if #S ne 0 and #S ne #Sl then // We run through the
							// non-empty proper
							// subsets of S_l
				prdS:={};	
				// We compute the products 
				// \prod_{lambda in S} Norm (u+lambda)
				// as u runs through our system
				// of totally positive units.
				for u in posunits do
					prd:=1;
					for lam in S do
						Flam,pilam:=ResidueClassField(lam);
						prd:=prd*Norm(pilam(u));
					end for;
					prdS:=prdS join {prd};
				end for;	
				// prdS is now the set of products
				// \prod_{lambda in S} Norm (u+lambda).
				// We finally check that there is 
				// such a product that does not equal 1.
				assert #{a : a in prdS | a ne 1} ge 1;
			end if;
		end for; 
	end for;	
end for;
