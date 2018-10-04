---------------------------------------------------------------------------
---------------------------------------------------------------------------
---------------------------------------------------------------------------
---------------------------------------------------------------------------
---------------------------------------------------------------------------
-- in the following block  claculates the partial reg of ideals

restart

loadPackage "EdgeIdeals"

-- this function gives the varibles of any monomial.
-- the entries are monomials

xNum=20

monvars = (mon,RING) -> ( 
    var = first entries vars RING;
    flatten for i  to length var -1 list (
       	while mon % var_i ==0 list 
	i+1
	do 
	mon=mon//var_i
	)
    )

S = QQ[x_1..x_(xNum),T,Degrees=>{xNum:{1,0},{0,1}}];

-- the following function returns the edge ideal of a cycle of size n
-- INPUT: integer
-- OUTPUT: ideal

C = n -> (
    return ideal ((for i from 1 to n-1 list(x_i*x_(i+1)))|{x_n*x_1})
    )

-- the following computes the edge ideal of a path
-- INPUT: integer
-- OUTPUT: ideal

P = l -> (
    return ideal ((for i from 1 to l-1 list(x_i*x_(i+1))))
    )

-- the function computes the kernel of the Rees algebra of I
-- INPUT: ideal
-- OUTPUT: ideal

reesKer = I -> (
    RING := ring I;
    genI := first entries gens I;
    indYI := for i to length genI -1 list(monvars(genI_i,RING));
    l := first entries vars RING;
    xvars := l_{0..#l-2};
    yvarsI := for i to length indYI -1 list (Y_(indYI_i));
    R := QQ[X_1..X_(#xvars),yvarsI,Degrees=>{#xvars:{1,0},length yvarsI:{0,1}}];
    genAlg := xvars|T*genI;
    rees := map(S,R,genAlg);
    J := trim ker rees;
    return J
    )

-- the function to compute the x_regularity of Rees algebra
-- INPUT: ideal
-- OUTPUT: integer

xReg = I -> (
    RING := ring  reesKer(I);
    B := betti res reesKer(I);
    l := sort  keys B;        
    return max apply(l, element ->  element_1_0-element_0)
    )


for i from 2 to 12 do print (regularity P(i) - xReg(P(i)) ,i)
for i from 3 to 12 do print (regularity C(i) - xReg(C(i)) ,i)


---------------------------------------------------------------------------
---------------------------------------------------------------------------
---------------------------------------------------------------------------
---------------------------------------------------------------------------
---------------------------------------------------------------------------
-- this function gives a random sample of bipartite graphs.
-- INPUTS: A ring, lower bound for the number of vartices, upper bound for the number of vertiecs,
-- the size of random sample
-- OUTPUT: a list of graphs
samGraph = (RING , lowerBound , upperBound, samSize) -> (
    counter:= 0;
    t:=0;
    list1 := while counter<samSize list (
	print(counter,t);
	t=t+1;
    	graph  := randomGraph(RING,random(lowerBound,upperBound));
    	if isBipartite(graph) then (graph, counter = counter +1) else continue
    	);
   list1 := for i to length list1 -1 list list1_i_0;
   return  list1
    )

(R,f) = selectVariables({0..xNum-1},S)

graphList = samGraph(R,9,15,10);

idealList = unique for i to length graphList -1 list f(edgeIdeal graphList_i);

-- the following computes the conjectute
-- INPUTE: a list of ideals
-- OUTPUT: a list of binary values

conj = aList -> (
        return (apply(idealList , 
		I -> return  (regularity(I)-xReg(I)==2 , I) ));
    )


-- the following tests the conjecture
-- INPUT: a list of ideals
-- OUTPUT: a sequence 

conjTest = aList -> (
    for i to #aList-1 do (
        if regularity(aList_i)-xReg(aList_i)==2 
	then print(true , i)
	else return (false,i)
	)
    )


conjTest(idealList)
conj(idealList)