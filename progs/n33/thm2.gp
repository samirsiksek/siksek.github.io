\\
\\  These gp functions may be used to verify Theorem 2 of the paper 
\\ 
\\     Perfect Powers Expressible as Sums of Two Curves 
\\
\\  by Samir Siksek.
\\
\\
\\  The command    proofrange(a,b) produced as output a list of
\\  pairs [n,k], one for each prime n in the interval [a,b], such that
\\  the pair n,k satisfies the conditions of Proposition 4.1 in that 
\\  paper, thus demonstrating  that the equation $a^3+b^3=c^n$
\\ has no non-trivial primitive solutions
\\ 
\\ last modified by SS, 4/7/08 

\\
E=ellinit([0,0,0,6,-7]);     \\ E is a global variable
\\ this curve 72A1

\\ tests to see if k satisfies condition (c) of Proposition 4.1
\\ given that k already satisfies condition (a), (b).
\\ If the test succeeds the output is $1$,
\\ otherwise the output is  a pair [zet,del];
\\ in this second case condition (c) of the Theorem is not satisfied
\\ for this zet=\zeta
{
testc(n,k,l,al)=local(h,zet,del,Ezet);
	h=lift(znprimroot(l)^n); \\ generates $\mu_k(\F_l)$
	zet=1;
	for(j=0,k-1,
	if(kronecker(324*zet-3,l)!=-1,  \\ equivalent to saying
					\\ 4*\zeta-1/27 is a square
					\\ in \F_l
		del=lift(sqrt(Mod(4*zet-1/27,l)));
				\\ this a choice of $\delta_\zeta$
		Ezet=ellinit([0,del,0,zet,0],1);
		if(ellapEquiv(Ezet,al,l), \\ tests if 
					\\ a_l(E_\zeta)=a_l(E)
			return([zet,del]) \\ failure
		)
	);
	zet=(zet*h)%l);
	return(1);
}

\\ Given elliptic curve E2, integer alE, prime l
\\ checks if a_l(E2) = \pm alE
\\ returns 1 if true, 0 if false
{
ellapEquiv(E2,alE,l)=local(ans,card1,card2,r,v,P,nP1,nP2);
	card1=l+1-alE;
	card2=l+1+alE;
	r=1;
	v=ellordinate(E2,Mod(r,l));
	while(v==[],
		r=r+1;
		v=ellordinate(E2,Mod(r,l))
	);
	P=[Mod(r,l),v[1]];  \\ a "random point" on E2
	nP1=ellpow(E2,P,card1);
	nP2=ellpow(E2,P,card2);
	if((nP1==[0])||(nP2==[0]),ans=(ellap(E2,l)^2==alE^2),ans=0);
	ans
}


\\ For a prime n>=17, this function finds an even k 
\\ satisfying the conditions 
\\ (a),(b),(c) of Proposition 4.1. 
\\ The existence of such k implies that there are no 
\\ non-trivial primitive solutions to the equation a^3+b^3=c^n.
\\ An error message is output if no suitable k is found 

{
proof(n)=local(k,l,aq);
	k=2;
	while(k<n/4-1, \\ this part of condition (a)
  		l=n*k+1;
  		if(isprime(l), \\ condition a
     			al=ellap(E,l);
     			if((al!=2)&&(al!=(-2)), \\ condition (b)
        			if(testc(n,k,l,al)==1, \\ condition (c)
					return(k)
				)
       			)
    		);
  		k=k+2;
  	);
	print("n=",n,": no suitable k found");
	return(0);
}

{
proofrange(n1,n2)=
	n=nextprime(n1);
	while(n<=n2,print([n,proof(n)]);n=nextprime(n+1));
}

{
quietproofrange(n1,n2,nmax)=
	n=nextprime(n1);
	while(n<=n2,proof(n);n=nextprime(n+1));
}

#
proofrange(10^4,10^9);
\q
