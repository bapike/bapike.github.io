--   "calc_smn.m2", by Brian Pike, bpike@utsc.utoronto.ca, April 10, 2013
--   version 1.0
-- This file contains routines used for computing singular Milnor numbers.
-- See, for example, several papers of James Damon, or my own dissertation
-- at the University of North Carolina at Chapel Hill.
-- The routines are the following:
--   muFD = compute the sMn of a section of a H-holonomic free divisor
--   doLeGreuel = compute the Milnor number of an ICIS
--   muAFDonICIS = compute the sMn of an 'almost free divisor' on an ICIS.
--       That is, a type of pullback of a free divisor, intersected with an ICIS
-- All of these computations involve computing the length of a module, which
-- can be a rather tricky and computationally intensive task -- especially
-- when the module is not weighted homogeneous.  The routine 'calcDim'
-- computes the length of a module, up to a given timeLimit.  The idea is
-- that if we're interested in the sMn of f:X\to Y as a section of some V, then
-- we may actually compute the sMn of g\cdot f as a section of V, for any
-- g in \mathscr{K}_{V}.  In practical situations, then, it turns out to be
-- useful to choose a 'good' g; if we have picked a bad one, then we should
-- give up and try something else.
--     There are also a few routines to check our computations with
-- Singular.  If checkDimsWithSingular is true, then for every length
-- computation we successfully do, we generate some Singular code on
-- standard error to check our computations. 

needsPackage "VectorFields";

-- If we don't actually complete one portion of a larger computation, then
-- we want the whole computation to be spoiled!
ZZ * IndeterminateNumber := (x,y) -> indeterminate;
IndeterminateNumber * ZZ := (x,y) -> indeterminate;
ZZ + IndeterminateNumber := (x,y) -> indeterminate;
ZZ - IndeterminateNumber := (x,y) -> indeterminate;
IndeterminateNumber + ZZ := (x,y) -> indeterminate;
IndeterminateNumber - ZZ := (x,y) -> indeterminate;
IndeterminateNumber + InfiniteNumber := (x,y) -> indeterminate;
InfiniteNumber + IndeterminateNumber := (x,y) -> indeterminate;
IndeterminateNumber + IndeterminateNumber := (x,y) -> indeterminate;
IndeterminateNumber - InfiniteNumber := (x,y) -> indeterminate;
InfiniteNumber - IndeterminateNumber := (x,y) -> indeterminate;
IndeterminateNumber - IndeterminateNumber := (x,y) -> indeterminate;

-- Set this variable to a higher value to get more output.
--  0 = Bare description of what it's doing now and the answers received, with info. about failed calculations
--  1 = More information on what it's doing
--  2 = Most information on what it's doing, including all modules for which a basis is computed. 
infoDepth=0;

-- Maximum number of seconds to wait for a module computation before assuming the answer is 'indeterminate'
timeLimit=-1;

-- Sometimes M2 has trouble believing that there are infinitely many basis
-- elements, and we want our attempted computation to actually terminate.
-- So, setting this to something like 4444 might be useful.
--   Set to -1 to find all basis elements... 
basisLimit=-1;

-- Set to true to generate Singular code on stderr to verify module
-- computations.
checkDimsWithSingular=false;

KHeNormalSpaceVfs = (F,H,vfs) -> (
	-- Here we consider the following situation:
	--       F      H
	--   C^m -> C^n -> C
	-- So H is an element of Ocn
	-- F is just a list of n elements of Ocm, corresponding to vars(Ocn)
	-- vfs is a matrix with gens of Derlog(H), vector fields on C^n

	Ocn:=ring(H);
	n:=numColumns(vars(Ocn));
	Ocm:=ring(F_0);
	if (n!=length(F)) then (
		error("Incorrect number of parameters for F");
		return;
	);
	Fstar:=map(Ocm,Ocn,F);
	
	-- setup the matrix
	TKHeF:=(transpose jacobian(matrix {F})) | Fstar(vfs);
	return (coker TKHeF);
);

KHeNormalSpace = (F,H) -> (
	-- This is a version of this routine where the vector fields
	-- in Derlog(H) are calculated.
	vfs:=derlogH(ideal H);
	return KHeNormalSpaceVfs(F,H,vfs);
);

-- This makes a vector in r^len whose ith entry (starting from 0) is 1_r.
elementaryVector := (len,i,r) -> (
	return vector apply(len,j-> if (j==i) then 1_r else 0_r);
);

deleteCertainConstantVfs := (vfs,badvars) -> (
	-- vfs is a matrix whose columns are vector fields.  We return
	-- the same, after deleting those vector fields which take the form
	-- 1\frac{\partial}{\partial x}, for x\in badvars.
	-- badvars is a list of variables in ring(vfs).
	-- We expect to find one such v.f. for each element of badvars, and
	-- should complain if this does not happen.

	--allvars:=flatten entries vars(ring vfs);
	colstokeep:=toList(0..(numColumns(vfs)-1));
	if length(badvars)==0 then error("Why aren't there any badvars?");
	for v in badvars do (
		-- this gives the row corresponding to the variable v
		i:=index(v);
		lookingfor:=elementaryVector(numRows(vfs),i,ring vfs);
		startlength:=length(colstokeep);
		for j in colstokeep do (
			if vfs_j==lookingfor then (
				colstokeep=delete(j,colstokeep);
			);
		);
		if startlength==length(colstokeep) then (
			error(concatenate("Didn't find an expected constant vf for variable ",toString(v)));
		);
	);
	assert(length(colstokeep)==numColumns(vfs)-length(badvars));
	return vfs_colstokeep;
);

AFDonICISmodule = (F,H,I) -> (
	-- Here we consider the following situation:
	--       F      H
	--   C^m -> C^n -> C
	-- We factor C^n as C^(p1+p2), and assume that H is a good defining
	-- equation for a free divisor on C^(p2).  We assume that this
	-- factorization respects the 'coordinates' (variables) we've
	-- chosen in Ocn.
	-- We also have the ICIS {0} in C^(p1), defined by the ideal I. 

	Ocn:=ring(H);
	n:=numColumns(vars(Ocn));
	Ocm:=ring(F_0);
	if (n!=length(F)) then (
		error("Incorrect number of parameters for F");
		return;
	);
	Fstar:=map(Ocm,Ocn,F);
	Op1vars:=for v in flatten entries vars(Ocn) list (
		if isSubset(ideal v,I) then 
			v
		else
			continue
	);

	-- Get the vfs annihilating H on C^n.  We only want the 'lifts' of the
	-- vfs from C^(p2); the vfs we don't want should only be of the form
	-- 1* \frac{d}{dx}, where x is a coordinate on C^(p1).  Remove such
	-- constant vfs. 
	vfs:=deleteCertainConstantVfs(derlogH(ideal (H)),Op1vars);
	-- Sanity check: n=p1+p2=numGens(I)+numColumns(vfs)+1.
	-- This might fail if we don't have a free divisor or we deleted the
	-- wrong vector fields.
	assert(n==numgens(I)+numColumns(vfs)+1);
	-- now construct the map, and return the cokernel.
	M:=(transpose jacobian(matrix {F})) | Fstar(vfs) | gens(Fstar(I)*Ocm^n);
	return (coker M);
);

-- Compute the dimension of the module m as a vector space.
-- We use this function everywhere because it might often fail, and
-- we can change what happens by just changing this one function.
calcDim = (m) -> (
	if infoDepth>1 then (
		print(concatenate("   Calculating dimension of ",toString(m)));
	);
	d:=0;
	try (
		if (timeLimit>0) then (
			alarm timeLimit;
		);
		d=numColumns(basis(m,Limit=>basisLimit));
	) else (
		a:=alarm 0;
		if (timeLimit>0 and a==0) then (
			d=indeterminate;
		) else (
			print(concatenate("   Failed to compute the dimension of:"));
			print(m);
			print(concatenate("   Paste-able version: ",toString(m)));
			d=infinity;
		);
	);
	alarm 0;
	if (instance(d,ZZ) and d==basisLimit) then (
		d=infinity;
	);
	if infoDepth>1 then (
		print(concatenate("   Got ",toString(d),"!"));
	);
	if (checkDimsWithSingular) then (
		calcDimCheck(m,d);
	);
	return d;
);

calcDimCheck = (m,val) -> (
	-- m is a module, usually of the form "coker m2", for a matrix
	-- m2.  We've already computed val=dim m as a vector space.
	-- This function writes part of a Singular script to double-
	-- check our answers.	
	m2:=presentation m;
	s:="";
	-- Singular uses a list of vectors which serve as a basis for
	-- the module.
	for cols from 0 when cols<numColumns(m2) do (
		-- m2_cols is a column of m2.
		s2:=toString flatten entries (m2_cols);
		-- s2 should look like "{x1n2,x1n3,0,x1n4,0,0}"
		s2=replace("^\\{","[",s2);
		s2=replace("\\}$","]",s2);
		if cols<numColumns(m2)-1 then (
			s2=s2|",";
		);
		s=s|s2;
	);
	-- Now s should be a description of the module.
	stderr<<"m="<<s<<";"<<endl;
	stderr<<"m2=std(m);"<<endl;
	stderr<<"n=vdim(m2);"<<endl;
	stderr<<"assert(n=="<<toString(val)<<");"<<endl<<endl;
	return val;
);

muFD = (F,H) -> (
	-- the answer is the K_{H,e}-codim(F), if that number is finite
	if infoDepth>0 then (
		print(concatenate("Computing SMN of section of FD ",toString(factor(H))));
	);
	m:=KHeNormalSpace(F,H);
	md:=calcDim(m);
	if infoDepth>0 then (
		print(concatenate("Got ",toString(md)));
	);
	return md;
);

doLeGreuel = (J) -> (
	-- J is an ideal defining an ICIS.  We assume that the generators
	-- of J form an acceptable sequence for the Le-Greuel formula.
	if infoDepth>0 then (
		print(concatenate("   Computing Milnor number of ICIS formed by ",toString(J)));
	);
	r:=numgens J;
	-- The ideal should certainly have fewer generators than the dimension
	-- of the space we're in.
	assert(r<=numgens ring(J));
	musofar:=0;
	for i from 0 to (r-1) do (
		-- A list containing the first i functions.
		firsti:=(J_*)_{0..(i-1)};
		-- A list containing the first i+1 functions.
		firstip1:=(J_*)_{0..(i+1-1)};
		-- A matrix of the first partials of the first i+1 functions;
		-- this should be (i+1)x numgens ring(J).
		jacfirstip1:=jacobian(ideal firstip1);
		m:=minors(i+1,jacfirstip1);
		-- This is a matrix, representing an ideal (its image).
		Ii:=0;
		if (i>0) then (
			Ii=(matrix {firsti})|(flatten gens m);
		) else (
			Ii=(flatten gens m);
		);
		if infoDepth>1 then (
			print(concatenate("   At step ",toString(i)," we're computing the dimension of the module formed by the cokernel of ",toString(Ii)));
		);
		musofar=musofar+(-1)^(r-i-1)*calcDim(coker Ii);
		if infoDepth>1 then (
			print(concatenate("   After step ",toString(i)," musofar=",toString(musofar)));
		);
	);
	if infoDepth>0 then (
		print(concatenate("   Got ",toString(musofar)));
	);
	return musofar;
);

muAFDonICIS = (F,H,I) -> (
	-- Compute the singular Milnor number of the nonlinear section of an
	-- "almost free divisor on an ICIS".  Here, H is the function defining
	-- the free divisor, I is the function defining an ICIS, and F maps
	-- into the space containing these two algebraic sets.
	-- The answer is given by the dimension of a 'correction module'
	--                        minus the Milnor number of the ICIS F^*(I).
	-- The latter is calculated using the Le-Greuel formula.
	
	if infoDepth>0 then (
		print(concatenate("Computing SMN of AFD on ICIS formed by section of the FD ",toString(factor(H))," and ICIS ",toString(I),"."));
	);
	Ocn:=ring(I);
	n:=numColumns(vars(Ocn));
	Ocm:=ring(F_0);
	if (n!=length(F)) then (
		error("Incorrect number of parameters for F");
		return;
	);
	Fstar:=map(Ocm,Ocn,F);

	-- The "correction module"
	m:=AFDonICISmodule(F,H,I);
	if infoDepth>1 then (
		print(concatenate("   Computing dimension of the correction module ",toString(m)));
	);
	mu1:=calcDim(m);

	-- Take Fstar of each generator of I to get the ICIS.
	J:=ideal apply(flatten entries gens I,asdf -> Fstar(asdf));
	if infoDepth>1 then (
		print(concatenate("   Computing dimension of the ICIS ",toString(J)));
	);
	mu2:=doLeGreuel(J);

	-- Return the answer.
	if infoDepth>0 then (
		print(concatenate("   Got ",toString(mu1-mu2)));
	);
	return (mu1-mu2); 

);

-- Don't execute these tests.
if (0==1) then (
	whichex=2;
	-- Example 6.2.5
	R=QQ[a,b,c,MonomialOrder=>RevLex,Global=>false];
	S=QQ[x,y,MonomialOrder=>RevLex,Global=>false];
	blah=KHeNormalSpace(a*(a*c-b^2),{x,y,x^5});
	assert(numColumns(basis(blah))==5);
	
	R=QQ[a,b,c,MonomialOrder=>RevLex,Global=>false];
	S=QQ[u,v,w,x,MonomialOrder=>RevLex,Global=>false];
	blah=KHeNormalSpace(a*(a*c-b^2),{u,u^3+v^2+w^2+x^2,v});
	assert(numColumns(basis(blah))==2);
	
	R=QQ[a,b,c,d,MonomialOrder=>RevLex,Global=>false];
	S=QQ[u,v,w,x,y,MonomialOrder=>RevLex,Global=>false];
	F={u,v,w,x^3+y^3+u^2+v^2+w^2};
	blah=KHeNormalSpace(a*b*(a*d-b*c),F);
	assert(numColumns(basis(blah))==16);
	blah=KHeNormalSpace(a*d,F);
	assert(numColumns(basis(blah))==8);
	blah=KHeNormalSpace(a*b*d,F);
	assert(numColumns(basis(blah))==16);

	--  Our formula for the sMN of matrix singularities for 2x2 general;
	--  the coefficients are missing.
	tryanF = F -> (
	for f in {a*b*(a*d-b*c),a*d,a*b*d} do (
		X=KHeNormalSpace(f,F);
		X=prune trim X;
		try (
			print(concatenate("For ",toString(factor(f))," we get ",toString(numColumns(basis(X)))  ));
		) else (
			print(X);
		);
	);
	);
	
	-- This is for 2x2gen:
	coeffs := new HashTable from {
		b*c => 1,a*b*c=> -1,a*d => 1,a*b*d=> -1,a*b*(a*d-b*c)=> 1};

);

