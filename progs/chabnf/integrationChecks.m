

// we test our p-adic integration routine by evaluating the integrals
//  for a curve appearing in McCallum-Poonen survey paper
// "The Method of Chabauty and Coleman"
// and comparing our answer against theirs.



K:=NumberField(Rationals());  // the rationals thought of a number field
				// a MAGMA-tism

OK:=Integers(K); //=Z
P:=3*OK;     // we integrate in K_P=Q_3

Kx<x>:=PolynomialRing(K);

C:=HyperellipticCurve(x^6+8*x^5+22*x^4+22*x^3+5*x^2+6*x+1);
J:=Jacobian(C);

pt0:=C![0,1];
D:=C![-3,1]-pt0;

// McCallum and Poonen obtain 
//           \int_D dx/y = 2*3+3^4 mod 3^5
//           \int_D xdx/y = 2*3^2+2*3^3 mod 3^5


// let's check

Attach("g2-jac.m");
Attach("add.m");
ints:=integrals(D,P,pt0,5);  // 5 indicate the 3-adic precision
print ints;
assert Valuation(ints[1]-(2*3+3^4)) ge 5;
assert Valuation(ints[2]-(2*3^2+2*3^3)) ge 5;

// try with a different base point

ints:=integrals(D,P,C![-3,1],5);
print ints;
assert Valuation(ints[1]-(2*3+3^4)) ge 5;
assert Valuation(ints[2]-(2*3^2+2*3^3)) ge 5;



