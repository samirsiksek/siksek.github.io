
Attach("g2-jac.m");
Attach("add.m");
load "JSearch.m";

Qu<u>:=PolynomialRing(Rationals());
K<t>:=NumberField(u^3-2);
eps:=1-t;

Kx<x>:=PolynomialRing(K);

for s in [-2..2] do
	print "s=",s;
	C:=HyperellipticCurve(3*(4*eps^(-s)*x^5-eps^(2*s)));
	pts:=ratPointsC(C);
	for P in pts do
		if P[3] ne 0 then      // P ne infty
			assert P[3] eq 1;
			Y:=P[2];
			if Y ne 3*eps^s then
				uoverv:=t*(Y+3*eps^s)/(Y-3*eps^s);
				uoverv:=Eltseq(uoverv);
				if uoverv[2] eq 0 and uoverv[3] eq 0 then
					print "u/v=", uoverv[1];
					print "this solution corresponds to $K$-rational point", P;
				end if;
			end if;
		end if;
	end for;
	print "############################################################";
end for;	

