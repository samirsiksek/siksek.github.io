
Attach("add.m");
Attach("g2-jac.m");
Attach("JSearch.m");

//  a check! Comparing the exact addition and multiplication by n with the padic one

Qx<x>:=PolynomialRing(Rationals());
C:=HyperellipticCurve(x^5+4*x^4-3*x^2-2*x+1);
J:=Jacobian(C);
inf:=PointsAtInfinity(C)[1];

D1:=3*(C![0,1]-inf);
D2:=3*(C![1,1]-inf);

Qp:=pAdicField(5 : Precision:=1000);
Qpx<x>:=PolynomialRing(Qp);
f:=Qpx!HyperellipticPolynomials(C);
Dp1:=[Qpx!D1[1],Qpx!D1[2]];  // D1 padically
Dp2:=[Qpx!D2[1],Qpx!D2[2]];  // D2 padically

Qpx!((D1+D2)[1])-add(f,Dp1,Dp2)[1]; //  note that this is zero within the limits of accuracy
Qpx!((D1+D2)[2])-add(f,Dp1,Dp2)[2]; // ditto
Qpx!((15*D1)[1])-pow(f,Dp1,15)[1]; //  ditto
Qpx!((15*D1)[2])-pow(f,Dp1,15)[2]; // ditto
Qpx!((28*D1)[1])-pow(f,Dp1,28)[1]; //  ditto
Qpx!((28*D1)[2])-pow(f,Dp1,28)[2]; // ditto


// another check
Qx<x>:=PolynomialRing(Rationals());
C:=HyperellipticCurve(4*x^6+6*x^5-3*x^3-2*x^2-x-3);
J:=Jacobian(C);
inf1:=PointsAtInfinity(C)[1];
inf2:=PointsAtInfinity(C)[2];

D1:=3*(C![1,1]-inf1);
D2:=3*(C![1,1]-inf2);

Qp:=pAdicField(5 : Precision:=1000);
Qpx<x>:=PolynomialRing(Qp);
f:=Qpx!HyperellipticPolynomials(C);
Dp1:=[Qpx!D1[1],Qpx!D1[2]];  // D1 padically
Dp2:=[Qpx!D2[1],Qpx!D2[2]];  // D2 padically

Qpx!((D1+D2)[1])-add(f,Dp1,Dp2)[1]; //  note that this is zero within the limits of accuracy
Qpx!((D1+D2)[2])-add(f,Dp1,Dp2)[2]; // ditto
Qpx!((12*D1)[1])-pow(f,Dp1,12)[1]; //  ditto
Qpx!((12*D1)[2])-pow(f,Dp1,12)[2]; // ditto
Qpx!((19*D1)[1])-pow(f,Dp1,19)[1]; //  ditto
Qpx!((19*D1)[2])-pow(f,Dp1,19)[2]; // ditto


// another check
Q:=NumberField(Rationals());
Qx<x>:=PolynomialRing(Q);
C:=HyperellipticCurve(4*x^6+6*x^5-3*x^3-2*x^2-x-3);
J:=Jacobian(C);
inf1:=PointsAtInfinity(C)[1];
inf2:=PointsAtInfinity(C)[2];

D1:=(C![1,1]-inf1);
D2:=(C![1,1]-inf2);

OQ:=Integers(Q);
P:=7*OQ;
localpow(D1,10,P,50);
localpow(2*D1,92,P,50);


// some checks
//
K<t>:=QuadraticField(8);
Kx<x>:=PolynomialRing(K);
C:=HyperellipticCurve(x^5-x^2+3+2*t);
inf:=PointsAtInfinity(C)[1];
P1:=C![0,1+t];
P2:=C![1,1+t];
J:=Jacobian(C);
D1:=P1-inf;
D2:=P2-inf;
OK:=Integers(K);
P:=Factorisation(5*OK)[1,1];
D,h,hx:=preIntLocal(D1,D2,21,P,50); // this should be 21*D1+D2
// let's check
Dexact:=21*D1+D2;
hx(Dexact[1])-D[1];
hx(Dexact[2])-D[2];

//
//
// Now let's do another calculation where we can't write the exact 
// answer, but where we can check that the answer is plausible
//
D,h,hx:=preIntLocal(D1,2*D2,640,P,50); // this should be 640*D1+2*D2
// the order of J mod P is 640,
// so this must be congruent to 2*D2 mod P
f1:=hx((2*D2)[1])-D[1];
f2:=hx((2*D2)[2])-D[2];
Min([Valuation(c) : c in Coefficients(f1) cat Coefficients(f2)]);
// all the coefficients are divisible by 5, so 2*D2 \equiv D mod 5
// now let's move deep into the formal group
D,h,hx:=preIntLocal(D1,2*D2,5^5*640,P,50); // this should be 640*D1+2*D2
f1:=hx((2*D2)[1])-D[1];
f2:=hx((2*D2)[2])-D[2];
Min([Valuation(c) : c in Coefficients(f1) cat Coefficients(f2)]);
// we see that D = D2 mod P^6 as we expect.


// another check
K<t>:=QuadraticField(8);
Kx<x>:=PolynomialRing(K);
C:=HyperellipticCurve(x^5-x^2+3+2*t);
inf:=PointsAtInfinity(C)[1];
P1:=C![0,1+t];
P2:=C![1,1+t];
J:=Jacobian(C);
D1:=P1-inf;
D2:=P2-inf;
OK:=Integers(K);
P:=Factorisation(5*OK)[1,1];
Dl,h,hx:=preIntLocal(D1,D2,21,P,50); // this should be 21*D1+D2
Dg:=preInt(D1,D2,21,P,50);
Dg[1]@hx-Dl[1];
Dg[2]@hx-Dl[2];
