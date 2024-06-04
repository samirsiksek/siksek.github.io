
// For p=3,5,7 we determine the subgroups of GL_2(\F_p)
// satisfying the following four conditions: 
// (i) irreducible
// (ii) odd
// (iii) surjective
// (iv) have intersection with SL_2(\F_p) that is absolutely reducible.


// pt is a point on the projective line 
// g is a 2x2 matrix
// act on pt (viewed as a column vector) by g
act:=function(g,pt);
	P:=Parent(pt);
	pt:=Eltseq(pt);
	F:=Universe(pt);
	g:=GL(2,F)!g;
	pt:=Matrix([[a] : a in pt]);
	pt:=Eltseq(Transpose(g*pt));
	return P!pt;
end function;

// H is a subgroup of GL(2,F_p)
// return true if H is reducible
// false otherwise
redTest:=function(H);
	F:=BaseRing(H);
	PF:=Points(ProjectiveSpace(F,1));
	gens:=Generators(H);
	for pt in PF do
		if &and[act(g,pt) eq pt : g in gens] then
			return true, pt;
		end if;
	end for;
	return false;
end function;

// H is a subgroup of GL(2,F_p)
// return true if H is absolutely reducible
// false otherwise

abRedTest:=function(H);
	p:=#BaseRing(H);
	assert IsPrime(p);
	F:=GF(p^2);
	PF:=Points(ProjectiveSpace(F,1));
	gens:=Generators(H);
	for pt in PF do
		if &and[act(g,pt) eq pt : g in gens] then
			return true, pt;
		end if;
	end for;
	return false;
end function;

// has an element that looks like complex conjugation
isOdd:=function(H);
	F:=BaseRing(H);
	return #{a : a in H | Order(a) eq 2 and Determinant(a) eq F!-1} ge 1;
end function;

// Is the determinant map H->F_p^* surjective
isSurjective:=function(H);
	F:=BaseRing(H);
	im:={Determinant(h) : h in H};
	return #im eq (#F-1);
end function;

// H1, H2 subgroups of GL_2(F_p)
// return true if H1 is a conjugate in GL_2(F_p) to some subgroup of H2
isContained:=function(H1,H2);
	subs:=Subgroups(H2);
	subs:=[K`subgroup : K in subs];
	subs:=[K : K in subs | #K eq #H1];
	if #subs eq 0 then
		return false;
	end if;
	gl:=GL(2,BaseRing(H1));
	assert H1 subset gl;
	assert H2 subset gl;
	return &or[IsConjugate(gl,H1,K) : K in subs];	
end function;

// returns the split Cartan and its normalizer 
splitCartan:=function(p);
	G:=GL(2,GF(p));
	H:=sub<G | [G![[a,b],[b,a]] : a,b in GF(p) | a ne b and a ne -b]>;
	N:=Normalizer(G,H);
	// check -- using the recipe in Chen's thesis
	Nd:=sub<G | [a : a in H] cat [G![1,0,0,-1]]>;
	assert Nd eq N;
	return H,N;
end function;

// returns the a non-split Cartan and its normalizer 
nonSplitCartan:=function(p);
	G:=GL(2,GF(p));
	lam:=PrimitiveElement(GF(p));
	assert IsSquare(lam) eq false;
	H:=sub<G | [G![[a,b],[lam*b,a]] : a,b in GF(p) | a ne 0 or b ne 0]>;
	N:=Normalizer(G,H);
	// check -- using the recipe in Chen's thesis
	Nd:=sub<G | [a : a in H] cat [G![1,0,0,-1]]>;
	assert Nd eq N;
	return H,N;
end function;

// Returns the Borel subgroup of GL_2(F_p)
borel:=function(p);
	G:=GL(2,GF(p));
	H:=sub<G | [G![[a,b],[0,c]] : a, b, c in GF(p) | a*c ne 0]>;
	return H;
end function;

// Want subgroups of GL(2,F_p) that
// are odd, irreducible, having surjective determinant,
// but the intersection with SL_2(F_p)
// is absolutely reducible.
possImages:=function(p);
	gl:=GL(2,GF(p));
	subs:=Subgroups(gl);
	subs:=[K`subgroup : K in subs]; // the subgroups of GL(2,p)
					// up to conjugacy
	for K in subs do  // check -- odd and irreducible implies absolutely irreducible (this is just a sanity check!)
		if isOdd(K) and redTest(K) eq false then
			assert abRedTest(K) eq false;
		end if;
	end for;	
	subs:=[ K : K in subs | isOdd(K)]; 
	subs:=[ K : K in subs | isSurjective(K)];
	subs:=[ K : K in subs | redTest(K) eq false];
	sl:=SL(2,GF(p));
	subs:=[ K : K in subs | abRedTest(K meet sl) ];
	return subs;
end function;

// Given a subgroup H in GL_2(\F_p),
// determine its image in PGL_2(\F_p)
imPGL:=function(H);
	F:=BaseRing(H);
	gl:=GL(2,F);
	scalars:=[ gl![a,0,0,a] : a in F | a ne 0];
	scalarsH:=[ A : A in scalars | A in H];
	scalarsH:=sub<H | scalarsH>;
	imH:=quo<H | scalarsH>;
	return imH;	
end function;

// #######################################################

G:=GL(2,3);
_,A:=splitCartan(3);  // A is the normalizer of the split Cartan group in G
_,B:=nonSplitCartan(3); // B is the normalizer of the nonsplit Cartan group in G
I:=possImages(3); // (Up to conjugacy), 
		// the odd irreducible subgroups of GL_2(F_3), having
		// surjective determinant, and so that the intersection
		// with SL_2(F_3) is absolutely reducible.
assert #I eq 1; // There is exactly one such subgroup.

assert IsConjugate(G,I[1],A); // This subgroup is conjugate
			// to the normalizer of a split Cartan subgroup

assert isContained(A,B); // The normalizer of a split Cartan is contained
assert #B/#A eq 2;  // as a subgroup of index 2 in the normalizer
			// of a non-split Cartan

K:=imPGL(A); // The image of the normalizer of a non-split Cartan
	// in PGL_2(\F_3)

assert #K eq 4;
assert IsAbelian(K) eq true;
assert IsCyclic(K) eq false;
// Hence K \cong (\Z/2\Z)^2

// ######################################################

G:=GL(2,5);
_,A:=splitCartan(5);  // A is the normalizer of the split Cartan group in G
_,B:=nonSplitCartan(5); // B is the normalizer of the nonsplit Cartan group in G
I:=possImages(5); // (Up to conjugacy), 
		// the odd irreducible subgroups of GL_2(F_5), having
		// surjective determinant, and so that the intersection
		// with SL_2(F_5) is absolutely reducible.
assert #I eq 1; // There is exactly one such subgroup.

H:=sub<G | [G![0,1,2,0], G![1,0,0,4]]>;  // subgroup generated by
				// [0,1]
				// [2,0]
				// and
				// [1,0]
				// [0,4]

assert IsConjugate(G,I[1],H); // The unique subgroup satisfying
			// the above conditions is
			// H (up to conjugacy)

assert isContained(H,A); // H is conjugate to a subgroup of the normalizer
			// of the split Cartan.
assert isContained(H,B); // H is conjugate to a subgroup of the normaizer
			// of the non-split Cartan.

assert G![-1,0,0,-1] in H; // H contains -I


assert Order(H) eq 16;
assert #A/#H eq 2;  // Index of H in the normalizer of split Cartan is 2.
assert #B/#H eq 3;  // Index of H in the normalizer of a non-split Cartan is 3.
assert G![-1,0,0,-1] in H;

K:=imPGL(H); // The image of H in PGL_2(\F_5)

assert #K eq 4;
assert IsAbelian(K) eq true;
assert IsCyclic(K) eq false;
// Hence K \cong (\Z/2\Z)^2


// ############################################################

G:=GL(2,7);
_,A:=splitCartan(7);  // A is the normalizer of the split Cartan group in G
_,B:=nonSplitCartan(7); // B is the normalizer of the nonsplit Cartan group in G
I:=possImages(7); // (Up to conjugacy), 
		// the odd irreducible subgroups of GL_2(F_7), having
		// surjective determinant, and so that the intersection
		// with SL_2(F_7) is absolutely reducible.
assert #I eq 4; // There is exactly four such subgroups.

ordCompare:=func<H1,H2 | #H1 - #H2>;

Sort(~I, ordCompare);  // Sort I according to size.

assert isContained(I[1],I[3]);
assert isContained(I[2],I[4]);

H1:=sub< G | [G![3,0,0,5], G![0,2,2,0]]>;
// subgroup generated by
//[3 0]
//[0 5]
// and
//[0 2]
//[2 0]

H2:=sub<G | [G![0,5,3,0], G![5,0,3,2]]>;
// subgroup generated by
//[0 5]
//[3 0]
// and
// [5 0]
// [3 2]


assert IsConjugate(G,H1,I[3]);
assert IsConjugate(G,H2,I[4]);


assert isContained(H1,H2) eq false;
assert isContained(H2,H1) eq false;  // We only keep the two maximal such
					// subgroups.

assert isContained(H1,A);
assert #A/#H1 eq 2; // H1 is a subgroup of index 2 in the normalizer
		// of a split Cartan

assert #H1 eq 36;

assert isContained(H2,B);
assert #B/#H2 eq 2; // H2 is a subgroup of index 2 in the normalizer
		// of a non-split Cartan
assert #H2 eq 48;

assert G![-1,0,0,-1] in H1;
assert G![-1,0,0,-1] in H2;

K1:=imPGL(H1); // The image of H1 in PGL_2(\F_7)
K2:=imPGL(H2); // The image of H2 in PGL_2(\F_7)

assert IsIsomorphic(K1,DihedralGroup(3));
assert IsIsomorphic(K2,DihedralGroup(4));

