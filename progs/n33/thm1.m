//
//  These magma functions may be used to verify the computation
//  details of Theorem 1 of the paper
//
//     Perfect Powers Expressible as Sums of Two Curves
//
//  by Samir Siksek.
//  last changed 4/7/2008

F107:=GF(107);
E:=EllipticCurve([F107|0,0,0,6,-7]); //72A1 over $\F_{107}
a107:=Trace(E);
assert a107 eq 12;

cE:={};
for a,b in [0..106] do
	if IsDivisibleBy(a^3+b^3,107) eq false then
				// note $107 \nmid c$ by Lemma 2.2
		Eab:=EllipticCurve([F107|0,0,0,3*a*b,b^3-a^3]);	
		if Trace(Eab) eq 12 then
			epn:=(a^2-a*b+b^2)/(27*(a+b)^2);
			cE:=cE join {F107!epn};
		end if;
	end if;
end for;


// The following proves Lemma 3.3
assert cE eq {F107!13, F107!14, F107!36, F107!37, F107!48, F107!57,
F107!62};				

Z106:=Integers(106); // $\Z/106\Z$



// The following routine generates the Table 1 of the paper 

for R in [1..105] do 
	if GCD(R,106) eq 1 then
		Rs:=Integers()!(1/Z106!R); //$R^*$
		SR:={alpha^Rs : alpha in cE}; //$S_R$
		SRd:={beta : beta in SR | IsSquare(beta-1)}; //$S_R^\prime$
		print "$", R,"$ & $", Rs, "$ & $ \\{",  SR, "\\} $ & $ \\{ " , SRd, "\\} $ \\\\ \\hline";
	end if;
end for;
