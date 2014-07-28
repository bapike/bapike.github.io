load "calc_smn.m2";
load "mat2x3.m2";

-- Brian Pike, bpike@utsc.utoronto.ca, April 10, 2013
-- This file contains Macaulay2 code used to compute many examples of the reduced Euler characteristics of
-- singular Milnor fibers associated to sections of 2x3 matrix singularities.
-- See 'Solvable groups, free divisors and nonisolated matrix singularities II: vanishing topology'
-- by James Damon and Brian Pike

-- For the computation, we apply an element of \mathscr{K}_M to make the function transverse off 0 to
-- some additional varieties.  We've stuck to multiplying our 2x3 matrix of functions (defining the map)
-- on the left and right by invertible integer matrices.  Different matrices seem to be better for different maps,
-- depending on whether the resulting modules are homogeneous.  A fairly effective way of finding these matrices
-- is to try (with timeLimit set) a number of randomly generated pairs of invertible matrices, and take whichever one
-- works best.

-- The examples are taken from
-- Fruhbis-Kruger, A. and Neumer, A. 'Simple Cohen-Macaulay Codimension 2 Singularities'. Comm. Algebra 38 no. 2 (2010) 454-495,
-- and we have numbered the examples in the order in which they appear.

infoDepth=0;
basisLimit=-1;
checkDimsWithSingular=false;

-- How many seconds to wait before one part of the computation times out, and the whole computation is ruined?
-- Put -1 for 'forever'
timeLimit=-1;

--------------------- BEGIN MAPS FROM C^4 -----------------------------

S=coefficientRing(R)[w,x,y,z,MonomialOrder=>RevLex,Global=>false];

if (checkDimsWithSingular) then (
	-- Some preliminary Singular code to stderr.
	stderr<<"ring S=32003,(w,x,y,z),ls;"<<endl;
	--stderr<<"ring S=0,(w,x,y,z),ls;"<<endl;
	stderr<<"proc assert (int param) { if (param==0) { printf(\"ASSERTION FAILED!\"); } else { printf(\"Passed.\"); } }"<<endl<<endl;
	stderr<<"module m=[w];"<<endl;
	stderr<<"module m2=[w];"<<endl;
	stderr<<"int n=0;"<<endl;
);

stdio<<"INFO: Beginning  Type 1"<<endl;
stderr<<"printf(\"INFO: Beginning  Type 1\");"<<endl;
F=(matrix {{1,2},{-3,1}}) * (matrix {{w,y,x},{z,w,y}}) * (matrix {{1,2,3},{-1,1,2},{1,2,1}});
mu=tryFinFormula(F);
stdio<<"INFO: Answer="<<mu<<endl;
-- get 1

stdio<<"INFO: Beginning  Type 2-k"<<endl;
for k in {2,3,4,5,6} do (
	F=(matrix {{1,2},{-3,1}}) * (matrix {{w,y,x},{z,w,y^k}}) * (matrix {{1,2,3},{-1,1,2},{1,2,1}});
	stdio<<"INFO: Beginning  Type 2-k with k="<<k<<endl;
	stderr<<"printf(\"INFO: Beginning  Type 2-k with k="<<k<<"\");"<<endl;
	mu=tryFinFormula(F);
	stdio<<"INFO: Answer="<<mu<<endl;
);

stdio<<"INFO: Beginning  Type 3-k-l"<<endl;
--for asdf in {{2,2},{3,2},{4,2},{5,2},{6,2},{3,3},{4,3},{5,3},{6,3},{4,4}} do (
for asdf in {{2,2},{3,2},{4,2},{3,3},{4,3},{4,4}} do (
	k=asdf_0;
	l=asdf_1;
	F=(matrix {{1,3},{-2,1}}) * (matrix {{w^l,y,x},{z,w,y^k}}) * (matrix {{1,0,3},{-2,3,0},{1,0,1}});
	--F=(matrix {{1,3},{-2,1}}) * (matrix {{w^l,y,x},{z,w,y^k}}) * (matrix {{2,2,3},{-1,2,2},{1,2,1}});
	stdio<<"INFO: Beginning  Type 3-k-l with k="<<k<<", l="<<l<<endl;
	stderr<<"printf(\"INFO: Beginning  Type 3-k-l with k="<<k<<", l="<<l<<"\");"<<endl;
	mu=tryFinFormula(F);
	stdio<<"INFO: Answer="<<mu<<endl;
);
-- (k,l)=(2,2) -> get 3
-- (k,l)=(3,2) -> get 4
-- (k,l)=(4,2) -> get 5
-- (k,l)=(5,2) -> get 6  (getting hard)
-- (k,l)=(6,2) -> get 7
-- (k,l)=(3,3) -> get 5
-- (k,l)=(4,3) -> get 6
-- (k,l)=(5,3) -> get 7
-- (k,l)=(6,3) -> get 8  (really hard for 1st; used 2nd)
-- (k,l)=(4,4) -> get 7
-- (k,l)=(5,4) -> get    (really hard)
-- (k,l)=(6,4) -> get
-- (k,l)=(5,5) -> get
-- (k,l)=(6,5) -> get
-- (k,l)=(6,6) -> get

stdio<<"INFO: Beginning  Type 4-k"<<endl;
--for k in {2,3,4,5} do (
for k in {2,3,4} do (
	F=(matrix {{1,2},{0,1}}) * (matrix {{z,y,x},{x,w,y^2+z^k}}) * (matrix {{1,2,3},{-1,1,2},{0,0,1}});
	stdio<<"INFO: Beginning  Type 4-k with k="<<k<<endl;
	stderr<<"printf(\"INFO: Beginning  Type 4-k with k="<<k<<"\");"<<endl;
	mu=tryFinFormula(F);
	stdio<<"INFO: Answer="<<mu<<endl;
);
-- k=2 -> get 4 
-- k=3 -> get 5
-- k=4 -> get 6 (harder) 
-- k=5 -> get 7
-- k=6 -> get 

stdio<<"INFO: Beginning  Type 5-k"<<endl;
for k in {1,2,3,4,5,6} do (
	F=(matrix {{1,0},{0,1}}) * (matrix {{z,y,x},{x,w,y*z+y^k*w}}) * (matrix {{1,2,3},{-1,1,2},{0,0,1}});
	stdio<<"INFO: Beginning  Type 5-k with k="<<k<<endl;
	stderr<<"printf(\"INFO: Beginning  Type 5-k with k="<<k<<"\");"<<endl;
	mu=tryFinFormula(F);
	stdio<<"INFO: Answer="<<mu<<endl;
);
-- k=1 -> get 5
-- k=2 -> get 7
-- k=3 -> get 9
-- k=4 -> get 11
-- k=5 -> get 13
-- k=6 -> get 15

stdio<<"INFO: Beginning  Type 6-k"<<endl;
for k in {3,4,5,6,7,8} do (
	F=(matrix {{1,0},{0,1}}) * (matrix {{z,y,x},{x,w,y*z+y^k}}) * (matrix {{1,2,3},{-1,1,2},{0,0,1}});
	stdio<<"INFO: Beginning  Type 6-k with k="<<k<<endl;
	stderr<<"printf(\"INFO: Beginning  Type 6-k with k="<<k<<"\");"<<endl;
	mu=tryFinFormula(F);
	stdio<<"INFO: Answer="<<mu<<endl;
);
-- k=3 -> get 6
-- k=4 -> get 8
-- k=5 -> get 10
-- k=6 -> get 12 
-- k=7 -> get 14
-- k=8 -> get 16
--  These don't seem to get very time-consuming.

stdio<<"INFO: Beginning  Type 7"<<endl;
stderr<<"printf(\"INFO: Beginning  Type 7"<<"\");"<<endl;
F=(matrix {{1,0},{0,1}}) * (matrix {{z,y,x},{x,w,z^2+y*w}}) * (matrix {{1,2,3},{-1,1,2},{0,0,1}});
mu=tryFinFormula(F);
stdio<<"INFO: Answer="<<mu<<endl;
-- get 6

stdio<<"INFO: Beginning  Type 8"<<endl;
stderr<<"printf(\"INFO: Beginning  Type 8"<<"\");"<<endl;
F=(matrix {{1,0},{0,1}}) * (matrix {{z,y,x},{x,w,z^2+y^3}}) * (matrix {{1,2,3},{-1,1,2},{0,0,1}});
mu=tryFinFormula(F);
stdio<<"INFO: Answer="<<mu<<endl;
-- get 7

-----------------------------------------------------------------------------

stdio<<"INFO: Beginning  Type 9-k-l-m"<<endl;
for asdf in {{2,2,2},{2,2,3},{2,3,2},{3,2,2},{2,3,3},{3,2,3},{3,3,2},{3,3,3},{4,4,4},{6,4,5}} do (
	k=asdf_0;
	l=asdf_1;
	m=asdf_2;
	F=(matrix {{2,7},{12,1}}) * (matrix {{z,y+w^l,w^m},{w^k,y,x}}) * (matrix {{3,2,3},{-2,3,2},{1,2,2}});
	stdio<<"INFO: Beginning  Type 9-k-l-m with k="<<k<<", l="<<l<<", m="<<m<<endl;
	stderr<<"printf(\"INFO: Beginning  Type 9-k-l-m with k="<<k<<", l="<<l<<", m="<<m<<"\");"<<endl;
	mu=tryFinFormula(F);
	stdio<<"INFO: Answer="<<mu<<endl;
);
-- (k,l,m)=(2,2,2) -> get 4
-- (k,l,m)=(2,2,3) -> get 5
-- (k,l,m)=(2,3,2) -> get 5
-- (k,l,m)=(3,2,2) -> get 5
-- (k,l,m)=(2,3,3) -> get 6
-- (k,l,m)=(3,2,3) -> get 6
-- (k,l,m)=(3,3,2) -> get 6
-- (k,l,m)=(3,3,3) -> get 7
-- (k,l,m)=(4,4,4) -> get 10
-- (k,l,m)=(6,4,5) -> get 13
-- It doesn't seem like these get much harder.

stdio<<"INFO: Beginning  Type 10-k-l"<<endl;
--for asdf in {{2,2},{2,3},{2,4},{3,2},{3,3},{3,4},{4,2},{4,3},{4,4}} do (
for asdf in {{2,2},{2,3},{2,4},{3,2},{3,3},{4,2},{4,3}} do (
	k=asdf_0;
	l=asdf_1;
	F=(matrix {{1,2},{-3,1}}) * (matrix {{z,y,x^l+w^2},{w^k,x,y}}) * (matrix {{1,2,3},{-1,1,2},{1,2,1}});
	--F=(matrix {{1,3},{-2,1}}) * (matrix {{z,y,x^l+w^2},{w^k,x,y}}) * (matrix {{2,2,3},{-1,2,2},{1,2,1}});
	stdio<<"INFO: Beginning  Type 10-k-l with k="<<k<<", l="<<l<<endl;
	stderr<<"printf(\"INFO: Beginning  Type 10-k-l with k="<<k<<", l="<<l<<"\");"<<endl;
	mu=tryFinFormula(F);
	stdio<<"INFO: Answer="<<mu<<endl;
);
-- (k,l)=(2,2) -> get 5
-- (k,l)=(2,3) -> get 6
-- (k,l)=(2,4) -> get 7
-- (k,l)=(3,2) -> get 6
-- (k,l)=(3,3) -> get 7
-- (k,l)=(3,4) -> get 8 (harder...?)
-- (k,l)=(4,2) -> get 7
-- (k,l)=(4,3) -> get 8
-- (k,l)=(4,4) -> get 9 (harder...?)
-- (k,l)=(,) -> get 

stdio<<"INFO: Beginning  Type 11-k-l"<<endl;
for asdf in {{2,2},{2,3},{2,4},{3,2},{3,3},{3,4},{4,2},{4,3},{4,4}} do (
	k=asdf_0;
	l=asdf_1;
	F=(matrix {{1,2},{-3,1}}) * (matrix {{z,y+w^l,x*w},{w^k,x,y}}) * (matrix {{2,2,3},{-1,2,2},{1,2,1}});
	stdio<<"INFO: Beginning  Type 11-k-l with k="<<k<<", l="<<l<<endl;
	stderr<<"printf(\"INFO: Beginning  Type 11-k-l with k="<<k<<", l="<<l<<"\");"<<endl;
	mu=tryFinFormula(F);
	stdio<<"INFO: Answer="<<mu<<endl;
);
-- (k,l)=(2,2) -> get 6
-- (k,l)=(2,3) -> get 8
-- (k,l)=(2,4) -> get 10
-- (k,l)=(3,2) -> get 7
-- (k,l)=(3,3) -> get 9
-- (k,l)=(3,4) -> get 11
-- (k,l)=(4,2) -> get 8
-- (k,l)=(4,3) -> get 10
-- (k,l)=(4,4) -> get 12

stdio<<"INFO: Beginning  Type 12-k-l"<<endl;
for asdf in {{2,3},{2,4},{2,5},{3,3},{3,4},{3,5},{4,3},{4,4},{4,5}} do (
	k=asdf_0;
	l=asdf_1;
	F=(matrix {{1,2},{-3,1}}) * (matrix {{z,y,x*w+w^l},{w^k,x,y}}) * (matrix {{2,2,3},{-1,2,2},{1,2,1}});
	--F=(matrix {{1,2},{-3,1}}) *(matrix {{z,y,x*w+w^l},{w^k,x,y}}) * (matrix {{2,-1,3},{-1,2,2},{1,2,1}});
	stdio<<"INFO: Beginning  Type 12-k-l with k="<<k<<", l="<<l<<endl;
	stderr<<"printf(\"INFO: Beginning  Type 12-k-l with k="<<k<<", l="<<l<<"\");"<<endl;
	mu=tryFinFormula(F);
	stdio<<"INFO: Answer="<<mu<<endl;
);
-- (k,l)=(2,3) -> get 7 
-- (k,l)=(2,4) -> get 9
-- (k,l)=(2,5) -> get 11
-- (k,l)=(3,3) -> get 8
-- (k,l)=(3,4) -> get 10
-- (k,l)=(3,5) -> get 12
-- (k,l)=(4,3) -> get 9 
-- (k,l)=(4,4) -> get 11
-- (k,l)=(4,5) -> get 13
-- these don't seem to get that hard.

stdio<<"INFO: Beginning  Type 13-k"<<endl;
for k in {2,3,4} do (
	F=(matrix {{1,2},{-3,1}}) * (matrix {{z,y+w^2,x^2},{w^k,x,y}}) * (matrix {{2,2,3},{-1,2,2},{1,2,1}});
	stdio<<"INFO: Beginning  Type 13-k with k="<<k<<endl;
	stderr<<"printf(\"INFO: Beginning  Type 13-k with k="<<k<<"\");"<<endl;
	mu=tryFinFormula(F);
	stdio<<"INFO: Answer="<<mu<<endl;
);
-- k=2 -> get 7
-- k=3 -> get 8
-- k=4 -> get 9
-- k=5 -> get   (hard...) 
-- k=6 -> get

stdio<<"INFO: Beginning  Type 14-k"<<endl;
for k in {2,3,4,5,6} do (
	F=(matrix {{1,0},{0,1}}) * (matrix {{z,y,x^2+w^3},{w^k,x,y}}) * (matrix {{2,2,3},{-1,2,2},{1,2,1}});
	stdio<<"INFO: Beginning  Type 14-k with k="<<k<<endl;
	stderr<<"printf(\"INFO: Beginning  Type 14-k with k="<<k<<"\");"<<endl;
	mu=tryFinFormula(F);
	stdio<<"INFO: Answer="<<mu<<endl;
);
-- k=2 -> get 8 
-- k=3 -> get 9
-- k=4 -> get 10
-- k=5 -> get 11
-- k=6 -> get 12
-- These don't get that hard.

stdio<<"INFO: Beginning  Type 15-k"<<endl;
for k in {1,2,3,4,5,6} do (
	F=(matrix {{1,0},{0,1}}) * (matrix {{z,y,x*w+w^k},{y,x,z}}) * (matrix {{2,2,3},{-1,2,2},{1,2,1}});
	stdio<<"INFO: Beginning  Type 15-k with k="<<k<<endl;
	stderr<<"printf(\"INFO: Beginning  Type 15-k with k="<<k<<"\");"<<endl;
	mu=tryFinFormula(F);
	stdio<<"INFO: Answer="<<mu<<endl;
);
-- k=1 -> get 1  (This doesn't seem to match the pattern?)
-- k=2 -> get 6
-- k=3 -> get 9
-- k=4 -> get 12
-- k=5 -> get 15
-- k=6 -> get 18
-- These don't get that hard.

stdio<<"INFO: Beginning  Type 16-k"<<endl;
for k in {1,2,3,4,5,6} do (
	F=(matrix {{1,0},{0,1}}) * (matrix {{z,y,x*w},{y,x,z+w^k}}) * (matrix {{2,2,3},{-1,2,2},{1,2,1}});
	stdio<<"INFO: Beginning  Type 16-k with k="<<k<<endl;
	stderr<<"printf(\"INFO: Beginning  Type 16-k with k="<<k<<"\");"<<endl;
	mu=tryFinFormula(F);
	stdio<<"INFO: Answer="<<mu<<endl;
);
-- k=1 -> get 4
-- k=2 -> get 7 
-- k=3 -> get 10
-- k=4 -> get 13 
-- k=5 -> get 16 
-- k=6 -> get 19

stdio<<"INFO: Beginning  Type 17-k"<<endl;
for k in {1,2,3,4,5,6} do (
	F=(matrix {{1,0},{0,1}}) * (matrix {{z,y,x*w},{y+w^k,x,z}}) * (matrix {{2,2,3},{-1,2,2},{1,2,1}});
	stdio<<"INFO: Beginning  Type 17-k with k="<<k<<endl;
	stderr<<"printf(\"INFO: Beginning  Type 17-k with k="<<k<<"\");"<<endl;
	mu=tryFinFormula(F);
	stdio<<"INFO: Answer="<<mu<<endl;
);
-- k=1 -> get 5 
-- k=2 -> get 8 
-- k=3 -> get 11
-- k=4 -> get 14
-- k=5 -> get 17
-- k=6 -> get 20

stdio<<"INFO: Beginning  Type 18"<<endl;
stderr<<"printf(\"INFO: Beginning  Type 18"<<"\");"<<endl;
F=(matrix {{1,2},{-3,1}}) * (matrix {{z,y,w^2},{y,x,z+x^2}}) * (matrix {{2,2,3},{-1,2,2},{1,2,1}});
mu=tryFinFormula(F);
stdio<<"INFO: Answer="<<mu<<endl;
-- get 7

stdio<<"INFO: Beginning  Type 19"<<endl;
stderr<<"printf(\"INFO: Beginning  Type 19"<<"\");"<<endl;
F=(matrix {{1,0},{0,1}}) * (matrix {{z,y,x^3+w^2},{y,x,z}}) * (matrix {{2,2,3},{-1,2,2},{1,2,1}});
mu=tryFinFormula(F);
stdio<<"INFO: Answer="<<mu<<endl;
-- get 8

stdio<<"INFO: Beginning  Type 20"<<endl;
stderr<<"printf(\"INFO: Beginning  Type 20"<<"\");"<<endl;
F=(matrix {{1,2},{0,1}}) * (matrix {{z,y,x^2},{y,x,z+w^2}}) * (matrix {{2,2,3},{-1,2,2},{1,2,1}});
mu=tryFinFormula(F);
stdio<<"INFO: Answer="<<mu<<endl;
-- get 8

stdio<<"INFO: Beginning non-simple 1"<<endl;
stderr<<"printf(\"INFO: Beginning non-simple 1"<<"\");"<<endl;
--F=(matrix {{1,2},{-3,1}}) * (matrix {{z,y,x},{x,w,z^2+y^4}}) * (matrix {{2,2,3},{-1,2,2},{1,2,1}});
F=(matrix {{1,0},{0,1}}) * (matrix {{z,y,x},{x,w,z^2+y^4}}) * (matrix {{2,2,3},{-1,2,2},{1,2,1}});
mu=tryFinFormula(F);
stdio<<"INFO: Answer="<<mu<<endl;

stdio<<"INFO: Beginning non-simple 2"<<endl;
stderr<<"printf(\"INFO: Beginning non-simple 2"<<"\");"<<endl;
F=(matrix {{1,2},{-3,1}}) * (matrix {{z,y,x},{x,w,y^3+z^3}}) * (matrix {{2,2,3},{-1,2,2},{1,2,1}});
--F=(matrix {{1,2},{-3,1}}) * (matrix {{z,y,x},{x,w,y^3+z^3}}) * (matrix {{2,-1,3},{-1,2,2},{1,2,1}});
--F=(matrix {{1,2},{0,1}}) * (matrix {{z,y,x},{x,w,y^3+z^3}}) * (matrix {{2,2,3},{-1,2,2},{1,2,1}});
mu=tryFinFormula(F);
stdio<<"INFO: Answer="<<mu<<endl;

stdio<<"INFO: Beginning non-simple 3"<<endl;
stderr<<"printf(\"INFO: Beginning non-simple 3"<<"\");"<<endl;
F=(matrix {{1,2},{0,1}}) * (matrix {{z,y,x^2+y^2},{x,w,w^2+x*w+z^2}}) * (matrix {{2,2,3},{-1,2,2},{1,2,1}});
mu=tryFinFormula(F);
stdio<<"INFO: Answer="<<mu<<endl;

stdio<<"INFO: Beginning non-simple 4"<<endl;
stderr<<"printf(\"INFO: Beginning non-simple 4"<<"\");"<<endl;
F=(matrix {{1,2},{-3,1}}) * (matrix {{x,y,z},{w,z*x+x^2,w+y*z}}) * (matrix {{1,2,3},{1,2,2},{3,2,1}});
mu=tryFinFormula(F);
stdio<<"INFO: Answer="<<mu<<endl;

stdio<<"INFO: Beginning non-simple 5"<<endl;
stderr<<"printf(\"INFO: Beginning non-simple 5"<<"\");"<<endl;
F=(matrix {{1,2},{-3,1}}) * (matrix {{z,y,x^2},{w^2,x,y+w^2}}) * (matrix {{2,2,3},{-1,2,2},{1,2,1}});
--F=(matrix {{1,-2},{3,1}}) * (matrix {{z,y,x^2},{w^2,x,y+w^2}}) * (matrix {{2,-1,3},{-1,2,2},{1,2,1}});
mu=tryFinFormula(F);
stdio<<"INFO: Answer="<<mu<<endl;

stdio<<"INFO: Beginning non-simple 6"<<endl;
stderr<<"printf(\"INFO: Beginning non-simple 6"<<"\");"<<endl;
F=(matrix {{1,2},{-3,1}}) * (matrix {{z,y,x^2+z^2},{w^2,x,y+w^2}}) * (matrix {{2,2,3},{-1,2,2},{1,2,1}});
--F=(matrix {{1,-2},{3,1}}) * (matrix {{z,y,x^2+z^2},{w^2,x,y+w^2}}) * (matrix {{2,-1,3},{-1,2,2},{1,2,1}});
mu=tryFinFormula(F);
stdio<<"INFO: Answer="<<mu<<endl;

--------------------- BEGIN MAPS FROM C^5 -----------------------------

S=coefficientRing(R)[v,w,x,y,z,MonomialOrder=>RevLex,Global=>false];

stdio<<"INFO: Beginning type 1"<<endl;
stderr<<"printf(\"INFO: Beginning type 1"<<"\");"<<endl;
--F=(matrix {{1,2},{-3,1}}) * (matrix {{x,y,z},{w,v,x}}) * (matrix {{2,2,3},{-1,2,2},{1,2,1}});
F=(matrix {{1,0},{0,1}}) * (matrix {{x,y,z},{w,v,x}}) * (matrix {{2,2,3},{-1,2,2},{1,2,1}});
mu=tryFinFormula(F);
stdio<<"INFO: Answer="<<mu<<endl;

stdio<<"INFO: Beginning Type 2"<<endl;
for k in {1,2,3,4} do (
	--F=(matrix {{1,2},{-3,1}}) * (matrix {{x,y,z},{w,v,x^(k+1)+y^2}}) * (matrix {{2,2,3},{-1,2,2},{1,2,1}});
	F=(matrix {{1,0},{0,1}}) * (matrix {{x,y,z},{w,v,x^(k+1)+y^2}}) * (matrix {{2,2,3},{-1,2,2},{1,2,1}});
	stdio<<"INFO: Beginning Type 2-k with k="<<k<<endl;
	stderr<<"printf(\"INFO: Beginning Type 2-k with k="<<k<<"\");"<<endl;
	mu=tryFinFormula(F);
	stdio<<"INFO: Answer="<<mu<<endl;
);

stdio<<"INFO: Beginning Type 3"<<endl;
for k in {4,5,6} do (
	--F=(matrix {{1,2},{-3,1}}) * (matrix {{x,y,z},{w,v,x*y^2+x^(k-1)}}) * (matrix {{2,2,3},{-1,2,2},{1,2,1}});
	F=(matrix {{1,0},{0,1}}) * (matrix {{x,y,z},{w,v,x*y^2+x^(k-1)}}) * (matrix {{2,2,3},{-1,2,2},{1,2,1}});
	stdio<<"INFO: Beginning Type 3-k with k="<<k<<endl;
	stderr<<"printf(\"INFO: Beginning Type 3-k with k="<<k<<"\");"<<endl;
	mu=tryFinFormula(F);
	stdio<<"INFO: Answer="<<mu<<endl;
);

stdio<<"INFO: Beginning type 4"<<endl;
stderr<<"printf(\"INFO: Beginning type 4"<<"\");"<<endl;
--F=(matrix {{1,2},{-3,1}}) * (matrix {{x,y,z},{w,v,x^3+y^4}}) * (matrix {{2,2,3},{-1,2,2},{1,2,1}});
F=(matrix {{1,0},{0,1}}) * (matrix {{x,y,z},{w,v,x^3+y^4}}) * (matrix {{2,2,3},{-1,2,2},{1,2,1}});
mu=tryFinFormula(F);
stdio<<"INFO: Answer="<<mu<<endl;

stdio<<"INFO: Beginning type 5"<<endl;
stderr<<"printf(\"INFO: Beginning type 5"<<"\");"<<endl;
--F=(matrix {{1,2},{-3,1}}) * (matrix {{x,y,z},{w,v,x^3+x*y^3}}) * (matrix {{2,2,3},{-1,2,2},{1,2,1}});
F=(matrix {{1,0},{0,1}}) * (matrix {{x,y,z},{w,v,x^3+x*y^3}}) * (matrix {{2,2,3},{-1,2,2},{1,2,1}});
mu=tryFinFormula(F);
stdio<<"INFO: Answer="<<mu<<endl;

stdio<<"INFO: Beginning type 6"<<endl;
stderr<<"printf(\"INFO: Beginning type 6"<<"\");"<<endl;
--F=(matrix {{1,2},{-3,1}}) * (matrix {{x,y,z},{w,v,x^3+y^5}}) * (matrix {{2,2,3},{-1,2,2},{1,2,1}});
F=(matrix {{1,0},{0,1}}) * (matrix {{x,y,z},{w,v,x^3+y^5}}) * (matrix {{2,2,3},{-1,2,2},{1,2,1}});
mu=tryFinFormula(F);
stdio<<"INFO: Answer="<<mu<<endl;

stdio<<"INFO: Beginning Type 7"<<endl;
for k in {2,3,4,5} do (
	--F=(matrix {{1,2},{-3,1}}) * (matrix {{w,y,x},{z,w,y+v^k}}) * (matrix {{2,2,3},{-1,2,2},{1,2,1}});
	F=(matrix {{1,0},{0,1}}) * (matrix {{w,y,x},{z,w,y+v^k}}) * (matrix {{2,2,3},{-1,2,2},{1,2,1}});
	stdio<<"INFO: Beginning Type 7-k with k="<<k<<endl;
	stderr<<"printf(\"INFO: Beginning Type 7-k with k="<<k<<"\");"<<endl;
	mu=tryFinFormula(F);
	stdio<<"INFO: Answer="<<mu<<endl;
);

stdio<<"INFO: Beginning Type 8"<<endl;
for k in {2,3,4,5} do (
	--F=(matrix {{1,2},{-3,1}}) * (matrix {{w,y,x},{z,w,y^k+v^2}}) * (matrix {{2,2,3},{-1,2,2},{1,2,1}});
	F=(matrix {{1,0},{0,1}}) * (matrix {{w,y,x},{z,w,y^k+v^2}}) * (matrix {{2,2,3},{-1,2,2},{1,2,1}});
	stdio<<"INFO: Beginning Type 8-k with k="<<k<<endl;
	stderr<<"printf(\"INFO: Beginning Type 8-k with k="<<k<<"\");"<<endl;
	mu=tryFinFormula(F);
	stdio<<"INFO: Answer="<<mu<<endl;
);

stdio<<"INFO: Beginning Type 9"<<endl;
for k in {2,3,4,5} do (
	--F=(matrix {{1,2},{-3,1}}) * (matrix {{w,y,x},{z,w,y*v+v^k}}) * (matrix {{2,2,3},{-1,2,2},{1,2,1}});
	F=(matrix {{1,0},{0,1}}) * (matrix {{w,y,x},{z,w,y*v+v^k}}) * (matrix {{2,2,3},{-1,2,2},{1,2,1}});
	stdio<<"INFO: Beginning Type 9-k with k="<<k<<endl;
	stderr<<"printf(\"INFO: Beginning Type 9-k with k="<<k<<"\");"<<endl;
	mu=tryFinFormula(F);
	stdio<<"INFO: Answer="<<mu<<endl;
);

stdio<<"INFO: Beginning Type 10"<<endl;
for k in {2,3,4,5} do (
	--F=(matrix {{1,2},{-3,1}}) * (matrix {{w+v^k,y,x},{z,w,y*v}}) * (matrix {{2,2,3},{-1,2,2},{1,2,1}});
	F=(matrix {{1,0},{0,1}}) * (matrix {{w+v^k,y,x},{z,w,y*v}}) * (matrix {{2,2,3},{-1,2,2},{1,2,1}});
	stdio<<"INFO: Beginning Type 10-k with k="<<k<<endl;
	stderr<<"printf(\"INFO: Beginning Type 10-k with k="<<k<<"\");"<<endl;
	mu=tryFinFormula(F);
	stdio<<"INFO: Answer="<<mu<<endl;
);

stdio<<"INFO: Beginning Type 11"<<endl;
for k in {2,3,4,5} do (
	--F=(matrix {{1,2},{-3,1}}) * (matrix {{w+v^2,y,x},{z,w,y^2+v^k}}) * (matrix {{2,2,3},{-1,2,2},{1,2,1}});
	F=(matrix {{1,0},{0,1}}) * (matrix {{w+v^2,y,x},{z,w,y^2+v^k}}) * (matrix {{2,2,3},{-1,2,2},{1,2,1}});
	stdio<<"INFO: Beginning Type 11-k with k="<<k<<endl;
	stderr<<"printf(\"INFO: Beginning Type 11-k with k="<<k<<"\");"<<endl;
	mu=tryFinFormula(F);
	stdio<<"INFO: Answer="<<mu<<endl;
);

stdio<<"INFO: Beginning Type 12"<<endl;
stderr<<"printf(\"INFO: Beginning type 12"<<"\");"<<endl;
--F=(matrix {{1,2},{-3,1}}) * (matrix {{w,y,x},{z,w,y^2+v^3}}) * (matrix {{2,2,3},{-1,2,2},{1,2,1}});
F=(matrix {{1,0},{0,1}}) * (matrix {{w,y,x},{z,w,y^2+v^3}}) * (matrix {{2,2,3},{-1,2,2},{1,2,1}});
mu=tryFinFormula(F);
stdio<<"INFO: Answer="<<mu<<endl;

stdio<<"INFO: Beginning Type 13-k-l"<<endl;
for asdf in {{2,2},{2,3},{2,4},{2,5},{3,3},{3,4},{4,4}} do (
	k=asdf_0;
	l=asdf_1;
	--F=(matrix {{1,3},{-2,1}}) * (matrix {{v^2+w^k,y,x},{z,w,v^2+y^l}}) * (matrix {{2,2,3},{-1,2,2},{1,2,1}});
	F=(matrix {{-7,3},{2,0}}) * (matrix {{v^2+w^k,y,x},{z,w,v^2+y^l}}) * (matrix {{2,-8,0},{-7,2,2},{6,-6,0}});
	stdio<<"INFO: Beginning Type 13-k-l with k="<<k<<", l="<<l<<endl;
	stderr<<"printf(\"INFO: Beginning Type 13-k-l with k="<<k<<", l="<<l<<"\");"<<endl;
	mu=tryFinFormula(F);
	stdio<<"INFO: Answer="<<mu<<endl;
);

stdio<<"INFO: Beginning Type 14"<<endl;
for k in {2,3,4,5} do (
	F=(matrix {{1,3},{-2,1}}) * (matrix {{v^2+w^k,y,x},{z,w,y*v}}) * (matrix {{2,2,3},{-1,2,2},{1,2,1}});
	stdio<<"INFO: Beginning Type 14-k with k="<<k<<endl;
	stderr<<"printf(\"INFO: Beginning Type 14-k with k="<<k<<"\");"<<endl;
	mu=tryFinFormula(F);
	stdio<<"INFO: Answer="<<mu<<endl;
);

stdio<<"INFO: Beginning Type 15-k-l"<<endl;
for asdf in {{2,3},{2,4},{2,5},{3,3},{3,4},{3,5},{4,3},{4,4},{5,3}} do (
	k=asdf_0;
	l=asdf_1;
	--F=(matrix {{1,3},{-2,1}}) * (matrix {{v^2+w^k,y,x},{z,w,y^2+v^l}}) * (matrix {{2,2,3},{-1,2,2},{1,2,1}});
	-- (matrix {{2,2,3},{-1,2,2},{1,2,1}});
	F=(matrix {{-6,-8},{1,2}}) * (matrix {{v^2+w^k,y,x},{z,w,y^2+v^l}}) * (matrix {{0,5,3},{5,0,10},{0,6,8}});
	stdio<<"INFO: Beginning Type 15-k-l with k="<<k<<", l="<<l<<endl;
	stderr<<"printf(\"INFO: Beginning Type 15-k-l with k="<<k<<", l="<<l<<"\");"<<endl;
	mu=tryFinFormula(F);
	stdio<<"INFO: Answer="<<mu<<endl;
);

stdio<<"INFO: Beginning Type 16"<<endl;
for k in {3,4,5} do (
	F=(matrix {{1,3},{-2,1}}) * (matrix {{w*v+v^k,y,x},{z,w,y*v+v^k}}) * (matrix {{2,2,3},{-1,2,2},{1,2,1}});
	stdio<<"INFO: Beginning Type 16-k with k="<<k<<endl;
	stderr<<"printf(\"INFO: Beginning Type 16-k with k="<<k<<"\");"<<endl;
	mu=tryFinFormula(F);
	stdio<<"INFO: Answer="<<mu<<endl;
);

stdio<<"INFO: Beginning Type 17"<<endl;
for k in {3,4,5} do (
	F=(matrix {{1,3},{0,1}}) * (matrix {{w*v+v^k,y,x},{z,w,y*v}}) * (matrix {{2,2,3},{-1,2,2},{1,2,1}});
	stdio<<"INFO: Beginning Type 17-k with k="<<k<<endl;
	stderr<<"printf(\"INFO: Beginning Type 17-k with k="<<k<<"\");"<<endl;
	mu=tryFinFormula(F);
	stdio<<"INFO: Answer="<<mu<<endl;
);

stdio<<"INFO: Beginning Type 18"<<endl;
stderr<<"printf(\"INFO: Beginning Type 18"<<"\");"<<endl;
F=(matrix {{1,3},{0,1}}) * (matrix {{w*v+v^3,y,x},{z,w,y^2+v^3}}) * (matrix {{2,2,3},{-1,2,2},{1,2,1}});
mu=tryFinFormula(F);
stdio<<"INFO: Answer="<<mu<<endl;

stdio<<"INFO: Beginning Type 19"<<endl;
stderr<<"printf(\"INFO: Beginning Type 19"<<"\");"<<endl;
F=(matrix {{1,3},{0,1}}) * (matrix {{w*v,y,x},{z,w,y^2+v^3}}) * (matrix {{2,2,3},{-1,2,2},{1,2,1}});
mu=tryFinFormula(F);
stdio<<"INFO: Answer="<<mu<<endl;

stdio<<"INFO: Beginning Type 20"<<endl;
stderr<<"printf(\"INFO: Beginning Type 20"<<"\");"<<endl;
F=(matrix {{1,3},{0,1}}) * (matrix {{w^2+v^3,y,x},{z,w,y^2+v^3}}) * (matrix {{2,2,3},{-1,2,2},{1,2,1}});
mu=tryFinFormula(F);
stdio<<"INFO: Answer="<<mu<<endl;

stdio<<"INFO: Beginning Type 21"<<endl;
for k in {2,3,4,5} do (
	F=(matrix {{1,0},{0,1}}) * (matrix {{z,y,x},{x,w,v^2+y^2+z^k}}) * (matrix {{2,2,3},{-1,2,2},{1,2,1}});
	stdio<<"INFO: Beginning Type 21-k with k="<<k<<endl;
	stderr<<"printf(\"INFO: Beginning Type 21-k with k="<<k<<"\");"<<endl;
	mu=tryFinFormula(F);
	stdio<<"INFO: Answer="<<mu<<endl;
);


stdio<<"INFO: Beginning Type 22"<<endl;
for k in {1,2,3,4} do (
	----F=(matrix {{1,0},{0,1}}) * (matrix {{z,y,x},{x,w,v^2+y*z+y^k*w}}) * (matrix {{2,2,3},{-1,2,2},{1,2,1}});
	--better:
	--F=(matrix {{-2,0},{-1,-6}}) * (matrix {{z,y,x},{x,w,v^2+y*z+y^k*w}}) * (matrix {{-1,-4,-5},{-4,-5,-5},{-6,0,-2}});
	F=(matrix {{0,-3},{2,0}}) * (matrix {{z,y,x},{x,w,v^2+y*z+y^k*w}}) * (matrix {{10,9,-2},{-8,-6,-1},{-5,0,0}});
	stdio<<"INFO: Beginning Type 22-k with k="<<k<<endl;
	stderr<<"printf(\"INFO: Beginning Type 22-k with k="<<k<<"\");"<<endl;
	mu=tryFinFormula(F);
	stdio<<"INFO: Answer="<<mu<<endl;
);

stdio<<"INFO: Beginning Type 23"<<endl;
for k in {2,3,4,5} do (
	--F=(matrix {{1,0},{0,1}}) * (matrix {{z,y,x},{x,w,v^2+y*z+y^(k+1)}}) * (matrix {{2,2,3},{-1,2,2},{1,2,1}});
	F=(matrix {{4,0},{0,-2}}) * (matrix {{z,y,x},{x,w,v^2+y*z+y^(k+1)}}) * (matrix {{-4,-4,0},{-7,8,-3},{-5,6,6}});
	stdio<<"INFO: Beginning Type 23-k with k="<<k<<endl;
	stderr<<"printf(\"INFO: Beginning Type 23-k with k="<<k<<"\");"<<endl;
	mu=tryFinFormula(F);
	stdio<<"INFO: Answer="<<mu<<endl;
);

stdio<<"INFO: Beginning Type 24"<<endl;
stderr<<"printf(\"INFO: Beginning Type 24"<<"\");"<<endl;
F=(matrix {{1,0},{0,1}}) * (matrix {{z,y,x},{x,w,v^2+y*w+z^2}}) * (matrix {{2,2,3},{-1,2,2},{1,2,1}});
mu=tryFinFormula(F);
stdio<<"INFO: Answer="<<mu<<endl;

stdio<<"INFO: Beginning Type 25"<<endl;
stderr<<"printf(\"INFO: Beginning Type 25"<<"\");"<<endl;
F=(matrix {{1,0},{0,1}}) * (matrix {{z,y,x},{x,w,v^2+y^3+z^2}}) * (matrix {{2,2,3},{-1,2,2},{1,2,1}});
mu=tryFinFormula(F);
stdio<<"INFO: Answer="<<mu<<endl;

stdio<<"INFO: Beginning Type 26"<<endl;
stderr<<"printf(\"INFO: Beginning Type 26"<<"\");"<<endl;
F=(matrix {{1,0},{0,1}}) * (matrix {{z,y,x+v^2},{x,w,v*y+z^2}}) * (matrix {{2,2,3},{-1,2,2},{1,2,1}});
mu=tryFinFormula(F);
stdio<<"INFO: Answer="<<mu<<endl;

stdio<<"INFO: Beginning Type 27"<<endl;
stderr<<"printf(\"INFO: Beginning Type 27"<<"\");"<<endl;
F=(matrix {{1,0},{0,1}}) * (matrix {{z,y,x+v^2},{x,w,v*z+y^2}}) * (matrix {{2,2,3},{-1,2,2},{1,2,1}});
mu=tryFinFormula(F);
stdio<<"INFO: Answer="<<mu<<endl;

stdio<<"INFO: Beginning Type 28"<<endl;
stderr<<"printf(\"INFO: Beginning Type 28"<<"\");"<<endl;
F=(matrix {{1,0},{0,1}}) * (matrix {{z,y,x+v^2},{x,w,y^2+z^2}}) * (matrix {{2,2,3},{-1,2,2},{1,2,1}});
mu=tryFinFormula(F);
stdio<<"INFO: Answer="<<mu<<endl;

quit; 
