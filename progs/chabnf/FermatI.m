

// to solve the equation x^2-z^{10}=y^3
// in coprime integers x,y,z
// note that Dahmen has solved x^2+z^{10}=y^3 (check)

///////////////////////////////////////////////
// Case I: y is odd
///////////////////////////////////////////////
// then 
// x+z^5=u^3
// x-z^5=v^3
// where u,v are coprime and odd

// hence 2z^5=u^3-v^3

//////////////////////////////////////////////
// Case I.1
// 3 does not divide z
/////////////////////////////////////////////

// then u-v=2a^5
// u^2+uv+v^2=b^5

// now use the identity (u-v)^2+3(u+v)^2=4(u^2+uv+v^2)
// to obtain 4a^10+3c^2=4b^5, where c=u+v
// hence Y^2=3(X^5-1) where X=b/a, Y=3c/2a^5

Qx<x>:=PolynomialRing(Rationals());
C:=HyperellipticCurve(3*(x^5-1));
J:=Jacobian(C);

assert #TwoSelmerGroup(J) eq 2;
assert #TorsionSubgroup(J) eq 2;

// Hence J(\Q) has rank 0

inf:=PointsAtInfinity(C)[1];
P:=C![1,0];

// these are the obvious rational points on C
// now consider the embedding C->J given by Q:->Q-inf;

assert Order(P-inf) eq 2;

// thus C(\Q)={inf,P}
// working backwards we get (x,y,z)=(0,-1, \pm 1)  
// and (x,y,z)=(\pm 1,1,0)

/////////////////////////////////////////////////////
// Case I.2
// 3 divides z
////////////////////////////////////////////////////

// recall 2z^5=u^3-v^3 and u,v are odd and coprime

// thus u-v=2*3^4 a^5
//      u^2+uv+v^2=3 b^5 
// now use the identity (u-v)^2+3(u+v)^2=4(u^2+uv+v^2)
// to obtain 4*3^8 a^10+3c^2=12b^5, where c=u+v
// hence Y^2=X^5-3^7 where X=b/a, Y=c/2a^5

Qx<x>:=PolynomialRing(Rationals());
C:=HyperellipticCurve(x^5-3^7);
J:=Jacobian(C);
assert #TorsionSubgroup(J) eq 1;
m,M:=RankBounds(J);
assert (M eq 1);

// hence J(\Q) is free of rank at most 1


P:=elt<J| [x^2 + 9*x + 27, 9*x + 81]>;

// want to show that P is the generator

hc:=HeightConstant(J : Effort:=3);

B:=Exp(1/4*Height(P)+hc);

// if P is not a generator, then the generator must have
// naive height leq B

pts:=Points(J : Bound:=Ceiling(B));

assert ReducedBasis(pts) eq [P];

// this completes the proof that P is the generator

// now we apply Chabauty 

inf:=PointsAtInfinity(C)[1];  // point at infinity on C

assert Chabauty(P : ptC:=inf) eq {inf};

// thus the only point on C is the point at infinity

///////////////////////////////////////////
// Case II, y is even.
//////////////////////////////////////////

// x^2-z^10=y^3
// y even, and x,y are coprime

// replacing x by -x if necessary
// we obtain x \equiv z^5 mod 4
// thus
// x+z^5=2u^3
// x-z^5=4v^3

// hence
// u^3-2v^3=z^5
// where u,v are coprime and u odd
// note the the equation is impossible mod 9, if $3 \mid z$,
// hence 3 \nmid z.

Qx<x>:=PolynomialRing(Rationals());
K<t>:=NumberField(x^3-2);
OK:=MaximalOrder(K);
assert #ClassGroup(OK) eq 1;
U,phi:=UnitGroup(OK);
assert U.1@phi eq OK!(-1);  // -1 generates the roots of unity in K
assert UnitRank(OK) eq 1;
assert U.2@phi eq (1-t);   // thus 1-t is a fundamental unit

// write \epsilon=1-t
// hence u-vt=\epsilon^r \alpha^5
// u^2+uvt+v^2 t^2=\epsilon^(-r) \beta^5
// now use the identity (u-vt)^2+3(u+vt)^2=4(u^2+uvt+v^2 t^2)



