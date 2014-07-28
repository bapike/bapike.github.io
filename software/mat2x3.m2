load "calc_smn.m2";

-- Brian Pike, bpike@utsc.utoronto.ca, April 10, 2013
-- This file contains Macaulay2 code used to compute the reduced Euler characteristics of
-- singular Milnor fibers associated to sections of 2x3 matrix singularities.
-- See 'Solvable groups, free divisors and nonisolated matrix singularities II: vanishing topology'
-- by James Damon and Brian Pike

-- What should our coefficient ring be?  QQ is hard, so use a finite field.
--  Some primes: 101, 31019, 32003, 65521, 4294967291
R=(ZZ/32003)[a,b,c,d,e,f,MonomialOrder=>RevLex,Global=>false];
--R=QQ[a,b,c,d,e,f,MonomialOrder=>RevLex,Global=>false];

-- If we compute the answer successfully, it may be useful to do some other computations
--  to, e.g., test hypotheses 
doSupplementaryCalculations = false;

elemMatrix := (i,j,R,n,m) -> (
        if (n<=0 or i<0 or j<0 or i>=n or j>=m) then (
                error "parameters to elem_matrix don't make sense";
        );
        mat := mutableMatrix(R,n,m);
        mat_(i,j)=1_R;
        return (matrix mat);
);

-- Generate the vector fields used to compute 'tau', which is the
-- K_M-codimension.
tauVectorFields = (M) -> (
	-- M should be a 2x3 matrix of our variables.
	-- Left.
	vfs:=    transpose matrix {flatten entries (elemMatrix(0,0,ring(M),2,2) * M)};
	vfs=vfs| transpose matrix {flatten entries (elemMatrix(0,1,ring(M),2,2) * M)};
	vfs=vfs| transpose matrix {flatten entries (elemMatrix(1,0,ring(M),2,2) * M)};
	vfs=vfs| transpose matrix {flatten entries (elemMatrix(1,1,ring(M),2,2) * M)};
	-- Right.
	vfs=vfs| transpose matrix {flatten entries (M * elemMatrix(0,0,ring(M),3,3))};
	vfs=vfs| transpose matrix {flatten entries (M * elemMatrix(0,1,ring(M),3,3))};
	vfs=vfs| transpose matrix {flatten entries (M * elemMatrix(0,2,ring(M),3,3))};
	vfs=vfs| transpose matrix {flatten entries (M * elemMatrix(1,0,ring(M),3,3))};
	vfs=vfs| transpose matrix {flatten entries (M * elemMatrix(1,1,ring(M),3,3))};
	vfs=vfs| transpose matrix {flatten entries (M * elemMatrix(1,2,ring(M),3,3))};
	vfs=vfs| transpose matrix {flatten entries (M * elemMatrix(2,0,ring(M),3,3))};
	vfs=vfs| transpose matrix {flatten entries (M * elemMatrix(2,1,ring(M),3,3))};
	vfs=vfs| transpose matrix {flatten entries (M * elemMatrix(2,2,ring(M),3,3))};
	return vfs; 
);

vanishingTopTwoMinors = (Fmat) -> (
	-- Fmat is a 2x3 matrix.  Compute the vanishing topology of
	-- (ae-bd)*(bf-ce).  In reality, we'll permute the columns of
	-- Fmat to compute similar terms.

	F:=flatten entries Fmat;

	mu:=0;
	-- Start with the free divisors.
	mu=mu+( 1)*muFD(F,a);
	collectGarbage();
	mu=mu+( 1)*muFD(F,b);
	collectGarbage();
	mu=mu+(-1)*muFD(F,a*b*(a*e-b*d)*(b*f-c*e));
	collectGarbage();
	-- Then go with the AFD on ICIS, codimension 2
	mu=mu+( 1)*muAFDonICIS(F,b*d*e*(b*f-c*e),ideal (a));
	mu=mu+( 1)*muAFDonICIS(F,a*c*e,ideal (b));
	mu=mu+(-1)*muAFDonICIS(F,e,ideal (a));
	-- Then go with the AFD on ICIS, codimension 3
	mu=mu+(-1)*muAFDonICIS(F,b*d*f,ideal (a,e));
	collectGarbage();
	return mu;
);

vanishingTopOneMinor = (Fmat) -> (
	-- Fmat is a 2x3 matrix.  Compute the vanishing topology of
	-- (ae-bd).  In reality, we'll permute the columns of
	-- Fmat to compute similar terms.

	F:=flatten entries Fmat;

	mu:=0;
	-- Start with the free divisors.
	mu=mu+( 1)*muFD(F,a);
	mu=mu+( 1)*muFD(F,b);
	mu=mu+(-1)*muFD(F,a*b*(a*e-b*d));
	-- Then go with the AFD on ICIS, codimension 2
	mu=mu+( 1)*muAFDonICIS(F,b*d,ideal (a));
	mu=mu+( 1)*muAFDonICIS(F,a*e,ideal (b));
	collectGarbage();
	return mu;
);

-- If we successfully compute the answer, take a wild guess at what this number
-- actually is.
supplementaryCalcs = (F) -> (
	calcDim(KHeNormalSpaceVfs(F,a,derlogH(ideal (a*e-b*d))));
	calcDim(KHeNormalSpaceVfs(F,a,derlogH(ideal (a*f-c*d))));
	calcDim(KHeNormalSpaceVfs(F,a,derlogH(ideal (b*f-c*e))));

	calcDim(KHeNormalSpaceVfs(F,a,derlogV(ideal (a*e-b*d))));
	calcDim(KHeNormalSpaceVfs(F,a,derlogV(ideal (a*f-c*d))));
	calcDim(KHeNormalSpaceVfs(F,a,derlogV(ideal (b*f-c*e))));

	calcDim(KHeNormalSpaceVfs(F,a,derlogH(ideal ((a*e-b*d)*(b*f-c*e)))));
	calcDim(KHeNormalSpaceVfs(F,a,derlogH(ideal ((a*e-b*d)*(a*f-c*d)))));
	calcDim(KHeNormalSpaceVfs(F,a,derlogH(ideal ((b*f-c*e)*(a*f-c*d)))));

	calcDim(KHeNormalSpaceVfs(F,a,derlogV(ideal ((a*e-b*d)*(b*f-c*e)))));
	calcDim(KHeNormalSpaceVfs(F,a,derlogV(ideal ((a*e-b*d)*(a*f-c*d)))));
	calcDim(KHeNormalSpaceVfs(F,a,derlogV(ideal ((b*f-c*e)*(a*f-c*d)))));

	calcDim(KHeNormalSpaceVfs(F,a,derlogH(ideal ((a*e-b*d)*(b*f-c*e)*(a*f-c*d)))));
	calcDim(KHeNormalSpaceVfs(F,a,derlogV(ideal ((a*e-b*d)*(b*f-c*e)*(a*f-c*d)))));
);

tryFinFormula = (F) -> (
	--print(concatenate("Trying to compute the vanishing topology of ",toString(F)));
	if (checkDimsWithSingular) then (
		stderr<<"print(\"Checking map "<<toString(F)<<"\");"<<endl;
		tau:=calcDim(KHeNormalSpaceVfs(flatten entries F,a,tauVectorFields(matrix {{a,b,c},{d,e,f}})));
		stderr<<"print(\"tau="<<toString(tau)<<"\");"<<endl;
	);
	mu:=0;

	--print(concatenate("****First trying one minor"));
	-- First compute the vanishing topology of one minor.
	-- this does (a*e-b*d)
	mu=mu+( 1)*vanishingTopOneMinor(F_{0,1,2});
	-- this does (a*f-c*d)
	mu=mu+( 1)*vanishingTopOneMinor(F_{0,2,1});
	-- this does (b*f-c*e)
	mu=mu+( 1)*vanishingTopOneMinor(F_{2,1,0});
	--print(concatenate("****After one minor, we have ",toString(mu)));

	-- Now all three minors.
	-- Though this is hard, I don't think it's as hard as some of the
	-- later problems and we have no way to work around it.
	--print(concatenate("****Now trying 3 minors"));
	mu=mu+(-1)*muFD(flatten entries F,(a*e-b*d)*(b*f-c*e)*(a*f-c*d));
	--print(concatenate("****After three minors, we have ",toString(mu)));

	-- Now two minors.
	-- this does (a*e-b*d)*(b*f-c*e)
	--print(concatenate("****Now trying 2 minors"));
	mu=mu+(-1)*vanishingTopTwoMinors(F_{0,1,2});
	-- this does (a*e-b*d)*(a*f-c*d)
	mu=mu+(-1)*vanishingTopTwoMinors(F_{1,0,2});
	-- this does (b*f-c*e)*(a*f-c*d)
	mu=mu+(-1)*vanishingTopTwoMinors(F_{0,2,1});
	--print(concatenate("****After two minors, we have ",toString(mu)));
	if (instance(mu,ZZ) and doSupplementaryCalculations) then (
		-- compute some other quantities.
		supplementaryCalcs(flatten entries F);
	);
	if (checkDimsWithSingular) then (
		stderr<<"print(\"Answer is "<<toString(mu)<<"\");"<<endl;
	);

	return mu;
);

--S=(ZZ/31019)[w,x,y,z,MonomialOrder=>RevLex,Global=>false];
--S=(ZZ/32003)[w,x,y,z,MonomialOrder=>RevLex,Global=>false];
--S=QQ[w,x,y,z,MonomialOrder=>RevLex,Global=>false];
--S=(ZZ/101)[w,x,y,z,MonomialOrder=>RevLex,Global=>false];
-- Better method: take linear combinations of the columns and rows of the 'normal form' to make it transverse to the things we're interested in.
-- The set where it has rank < 2 should stay the same.
-- Her example 1:
--L= flatten entries (   (matrix {{1,(1/3)},{0,1}}) * (matrix {{w,y,x},{z,w,y}}) * (matrix {{1,(1/10),(1/3)},{0,1,(1/7)},{(1/8),0,1}})   );
--print(tryFinFormula(L,formula2)+tryFinFormula(L,formula3)+tryFinFormula(L,formula4)+tryFinFormula(L,formula5)+tryFinFormula(L,formula6));
-- get -1

-- Her example 2, k=2
--L= flatten entries (   (matrix {{1,(1/3)},{0,1}}) * (matrix {{w,y,x},{z,w,y^2}}) * (matrix {{1,(1/10),(1/3)},{0,1,(1/7)},{(1/8),0,1}})   )
-- get -2

-- Her example 2, k=3
--L= flatten entries (   (matrix {{1,(1/3)},{0,1}}) * (matrix {{w,y,x},{z,w,y^3}}) * (matrix {{1,(1/10),(1/3)},{0,1,(1/7)},{(1/8),0,1}})   )
-- get -3

-- Her example 2, k=4
--L= flatten entries (   (matrix {{1,(1/3)},{0,1}}) * (matrix {{w,y,x},{z,w,y^4}}) * (matrix {{1,(1/10),(1/3)},{0,1,(1/7)},{(1/8),0,1}})   )
-- get -4

-- Her example 5, k=1
--L= flatten entries (   (matrix {{1,(1/3)},{0,1}}) * (matrix {{z,y,x},{x,w,y*z+y^1*w}}) * (matrix {{1,(1/10),(1/3)},{0,1,(1/7)},{(1/8),0,1}})   )
--L= flatten entries (   (matrix {{1,(1/3)},{0,1}}) * (matrix {{z,y,x},{x,w,y*z+y^1*w}}) * (matrix {{1,(1/10),(1/3)},{0,1,(1/7)},{(1/8),0,1}})   )
-- get 1-13   +???   =

-- A working example:
-- L= (matrix {{1,2},{-3,1}}) * (matrix {{z,y,x},{x,w,y*z+y^4*w}}) * (matrix {{1,2,3},{-1,1,2},{0,0,1}})

print(concatenate(
"A reminder how this works:
  0) (Optional) Set any settings: 
      infoDepth to 0,1,2 for level-of-detail (now=",toString(infoDepth),")
      basisLimit for the maximum number of basis elements to compute.  If this
         is reached, we return infinity; -1=keep going forever, although we may
         conclude that the correct answer is infinity. (now=",toString(basisLimit),")
      checkDimsWithSingular to true or false (now=",toString(checkDimsWithSingular),")
         to generate Singular code on stderr to check module computations.
  1) F=(matrix {{1,0},{0,1}}) * (matrix {{z,y,x},{x,w,y}}) * (matrix {{1,0,0},{0,1,0},{0,0,1}})
  2) tryFinFormula(F)
The coefficient ring we're using is: ",toString(coefficientRing(R))));
--The earliest instance of 'infinity' or 'indeterminate' means that one
--of the modules has infinite dimension.
