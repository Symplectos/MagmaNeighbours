/*
 * File:   Neighbour.m
 * Author: Marc-Christian Zimmermann, Michael Jürgens, Gilles Bellot
 * Date:   2014 - Eichlinghofen - Germany
 *
 * Description: "Two-Neighbours"-Algorithm of Boris Hemkemeier
 *
 * Literature:	- [BH] Algorithmische Konstruktionen von Gittern - Boris Hemkemeier
 *		- [MJ] Ph. D. Thesis - Michael Jürgens
 *
 * History:	- 30/04/2014: project now managed by GB
 *		- 05/05/2014: fixed an error - now using suitable vectors for neighbouring (see [BH] Algorithmus 1)
 *		- 06/05/2014: added optional usage of Mass
 *		- 06/05/2014: clean up
 *		- 06/05/2014: added SPeq0_Invar (see [MJ])
 *		- 06/05/2014: added a strategy to easily discard lattices at later stages of the search (1/automOrder > mass difference)
 *		- 06/05/2014: added several trivial search strategies
 *		- 06/05/2014: added orbitsOfSpaces (now using orbitsOfSpaces to get representants of the different orbits under the AutomorphismGroup)
 *		- 07/05/2014: added several strategies - the most interesting being "next lattice fewest neighbours"
 *		- 07/05/2014: added "next lattice fewest neighbour" strategy with orbit length multiplicity
 *		- 07/05/2014: added optional SuccessiveMinima support
 *		- 06/06/2014: added own neighbour construction "algorithm"
 *		- 06/06/2014: added MassRational by Ivica
 *		- 07/06/2014: fixed several errors related to SucMin and DualSucMin
 *		- 07/06/2014: added output of highest minimum found so far
 *		- 13/06/2014: added support for successive minima of partual dual lattices as additional invariant
 *		- 17/06/2014: improved output
 *		- 23/06/2014: added option support for SP0_Invar
 *		- 14/10/2014: first support for odd lattices added (not fully functional - sometimes we can't get the entire genus this way) --- well, this isn't working at all yet
 *		- 03/12/2014: improved save function
 *
 *
 * ToDo:	- add search strategies
 *		- add better save load function (I have no idea how to load a file given by a string :( )
 *		- add new invariants (elementary divisors...)
 *		- add support for odd lattices
 * 
 * Note:
 *		- while strategy 9 makes no sense, it is quite often the fastest of all the implemented search strategies
 */
 
// DEFINITIONS /////////////////////////////////////////////////////////////////////////
declare verbose TwoNeighbours,5;
declare attributes Lat : numberOfTimesVisited;
declare attributes Lat : foundBy;
 
// FUNCTIONS ///////////////////////////////////////////////////////////////////////////

// calculate the number of pairs x,y with b(x,y)=0
intrinsic SPeq0_Invar(L::Lat : MinVecsBound:=1000) -> RngIntElt
{ Computes the number of pairs x,y of shortest vectors with b(x,y) = 0. }

  shvecs := ShortestVectors(L);
  if #shvecs le MinVecsBound then
    anz := 0;			// anz counts the number of pairs x,y with b(x,y) = 0
    for x,y in shvecs do
      if (L!x,L!y) eq 0 then
	anz +:= 1;
      end if;
    end for;
    return anz;
  else
    return -1;
  end if;
end intrinsic;

// chose next lattice by strategy
intrinsic getNextLattice(~index::RngIntElt, strategy::RngIntElt, ~Gen::SeqEnum, ~Unexp::SeqEnum, useSucMin::BoolElt)
{ get the next lattice to expand - different strategies available }
  
  n := Dimension(Gen[1]);
  
  case strategy:
    
    when 0: 			// strategy 0 : take the first lattice that hasn't been expanded
      index := Unexp[1];
      return;
    
    when 1:			// strategy 1 : take the last lattice that has been found as a neighbour of the previous lattice
      index := Maximum(Unexp);
      return;
    
    when 2:			// strategy 2 : take the lattice with the largest automorphism group 
      Sort(~Unexp, func< i , j | Order(Gen[i]`AutomorphismGroup) - Order(Gen[j]`AutomorphismGroup) >);
      index := Unexp[#Unexp];
      return;
    
    when 3:			// strategy 3 : take the lattice with the smallest automorphism group 
      Sort(~Unexp, func< i , j | Order(Gen[i]`AutomorphismGroup) - Order(Gen[j]`AutomorphismGroup) >);
      index := Unexp[1];
      return;
  
    when 4:			// strategy 4 : take the lattice that has been visited the least often (random)
      Sort(~Unexp, func< i , j | Gen[i]`numberOfTimesVisited - Gen[j]`numberOfTimesVisited >);
      index := Random({i : i in Unexp | Gen[i]`numberOfTimesVisited eq Gen[Unexp[1]]`numberOfTimesVisited});
      return;
    
    when 5:			// strategy 5 : take the lattice that has been visited the least often (last first)
      Sort(~Unexp, func< i , j | Gen[i]`numberOfTimesVisited - Gen[j]`numberOfTimesVisited >);
      S := [i : i in Unexp | Gen[i]`numberOfTimesVisited eq Gen[Unexp[1]]`numberOfTimesVisited];
      index := S[#S];
      return;
    
    when 6: 			// strategy 6 : take the lattice that has been visited the least often (highest sucMin first)
      if not useSucMin then
        printf "Critical error! Strategy 6 not useable without successive minima!\n";
        exit;
      end if;
      
      Sort(~Unexp, func< i , j | Gen[i]`numberOfTimesVisited - Gen[j]`numberOfTimesVisited >);
      S := [i : i in Unexp | Gen[i]`numberOfTimesVisited eq Gen[Unexp[1]]`numberOfTimesVisited];
      Sort(~S, func< i , j | SuccessiveMinima(Gen[i])[n] - SuccessiveMinima(Gen[j])[n] >);
      index := S[#S];
      return;
    
    when 7: 			// strategy 7 : take the lattice that has been visited the least often (smallest last sucMin first)
      if not useSucMin then
        printf "Critical error! Strategy 7 not useable without successive minima!\n";
        exit;
      end if;
      
      Sort(~Unexp, func< i , j | Gen[i]`numberOfTimesVisited - Gen[j]`numberOfTimesVisited >);
      S := [i : i in Unexp | Gen[i]`numberOfTimesVisited eq Gen[Unexp[1]]`numberOfTimesVisited];
      Sort(~S, func< i , j | SuccessiveMinima(Gen[i])[n] - SuccessiveMinima(Gen[j])[n] >);
      index := S[1];
      return;
  
    when 8: 			// strategy 8 : take the lattice that has been visisted the least often (with orbit length multiplicity)
      Sort(~Unexp, func< i , j | Gen[i]`numberOfTimesVisited - Gen[j]`numberOfTimesVisited >);
      S := [i : i in Unexp | Gen[i]`numberOfTimesVisited eq Gen[Unexp[1]]`numberOfTimesVisited];
      index := S[#S];
      return;
      
    when 9:  			// strategy 9 : ultimate BVB strategy (or rather, a Sheogorath strategy) - take the lattice with the most non-isometric lattices in the same bucket
				// (until the first isometric lattice is found) - last visited first
      Sort(~Unexp, func< i , j | Gen[i]`numberOfTimesVisited - Gen[j]`numberOfTimesVisited >);
      S := [i : i in Unexp | Gen[i]`numberOfTimesVisited eq Gen[Unexp[1]]`numberOfTimesVisited];
      index := S[#S];
      return;
      
    when 10:			// strategy 10 : take the lattice that has been visited the least often (highest minima first)
      Sort(~Unexp, func< i , j | Gen[i]`numberOfTimesVisited - Gen[j]`numberOfTimesVisited >);
      S := [i : i in Unexp | Gen[i]`numberOfTimesVisited eq Gen[Unexp[1]]`numberOfTimesVisited];
      Sort(~S, func< i , j | Minimum(Gen[i]) - Minimum(Gen[j]) >);
      index := S[1];
      return;
 
  end case;
end intrinsic

intrinsic Neighbours(L::Lat, ~B::Assoc, ~Gen::SeqEnum, ~Unexp::SeqEnum, ~Exp::SeqEnum, ~massArray::[] : boundThetaSeries:=6, useSucMin:=false, useDualSucMin:=false, useSP0:=false,
countNonTrivElDiv:=false, useDecompositionAut:=false, useDecompositionIsom:=false, useNaturalAction:=false, bacherDepth:=-1, useReciprocal:=false, strategy:=9, 
discardKernel:=false, discardOdd:=false, autOrderDiv:=0, saveFile:="", testReflectivity := false) 
{ Computes 2-neighbours of L }

  // Definitions
  L:=CoordinateLattice(L);
  n:=Dimension(L);
  Aut:=ChangeRing(AutomorphismGroup(L : Decomposition:=useDecompositionAut, NaturalAction:=useNaturalAction, BacherDepth:=bacherDepth),GF(2));
  t := 0;
 
  // get representants of the different orbits under the automorphism Group
  goodVectors := OrbitsOfSpaces(Aut,1);
  vprintf TwoNeighbours, 1 : "\t\tNumber of orbits to check = %o\n" , #goodVectors;
  vprintf TwoNeighbours, 1: "-------------------------------------------------------------------------------\n\n";
  
  multiplicityIndex := 0;		// used in strategy 8 -- see above
  
  // create neighbours
  for v in goodVectors do
    foundNewNeighbour := false;		// used in save and restore
    
    if strategy eq 8 then
      multiplicityIndex +:= 1;
    end if;
   w := L!(Basis(v[2])[1]);
    
    if IsEven(L) then
      // exclude vectors that won't create an even neighbour
      if (w,w) mod 8 eq 2 or (w,w) mod 8 eq 6 then
        vprintf TwoNeighbours , 3 : "Discarding vector because of bad norm modulo 8!\n";
        continue;
      end if;
    end if;
   
    if not (w,w) mod 4  eq 0 then
     vprintf TwoNeighbours,1 : "Discarding vector %o because it has norm %o\n",w,(w,w);
    end if;

    
    if (w,w) mod 4 eq 0 then
    
      // try vectors with norm 4 modulo 8 - i. e. find a b in Basis(L) such that (v,b) = 1 mod 2 - guaranteed to work if detL = 1 mod 2
     if IsEven(L) then
        if (w,w) mod 8 eq 4 then
          norm1 := (w,w);			// needed in the case of 2 / detL - since in that case it is not guaranteed that we find a b with (v,b) = 1 mod 2
          for b in Basis(L) do
            if (w,b) mod 2 eq 1 then
              w := w+2*b;
              break;
            end if;
          end for;
          if norm1 eq (w,w) then
            vprintf TwoNeighbours, 3 : "Discarding vector since there is no basis vector such that N(v+2b) = 0 mod 8!\n";
            continue;			// bad vector -> discard
          end if;
        end if; 
      end if; // end if (w,w) mod 8 eq 4

      // exclude vectors from the kernel of L -- see [BH] p. 10     
      if discardKernel and RSpace(GF(2),n)!w in Kernel(ChangeRing(GramMatrix(L),GF(2))) then
        vprintf TwoNeighbours,3 : "Discarding vector because it lies in the kernel of the gramian!\n";
        vprintf TwoNeighbours,3 : "Lattice: %o\n", L;
        vprintf TwoNeighbours,3 : "vector: %o\n", w;
        continue;
      end if;
      

      // compute two-neighbour at w
      vprintf TwoNeighbours, 1 : "Checking two-neighbour with vector %o ...\n\n", w;
      t := Cputime();
      
      // normalize the vector
      k := Minimum([i : i in [1..n] | w[i] mod 2 ne 0]);
      
      // find x such that x * w_k = 1 mod 8
      x := InverseMod(w[k], 8);
      w := x * w - (x*w[k]-1)*Basis(L)[k];
      
      // construct basis vectors
      newBasis := ZeroMatrix(Rationals(), n,n);
     
      // find m with m not equal to k and (v, b_m) not in 2Z
      m := Minimum([i : i in [1..n] | (i ne k) and ((w,Basis(L)[i]) mod 2 ne 0)]);
     
      newBasis[k] := 1/2 * w;
      newBasis[m] := KSpace(Rationals(),n)!( 2 * Basis(L)[m]);
      
      for i:= 1 to n do
        if i ne k and i ne m then
          if (Basis(L)[i], w) mod 2 eq 0 then
            newBasis[i] := KSpace(Rationals(),n)!(Basis(L)[i]);
          else
            newBasis[i] := KSpace(Rationals(),n)!(Basis(L)[i] + Basis(L)[m]);
          end if;
        end if;
      end for;
      
      N := CoordinateLattice(LLL(LatticeWithGram(newBasis*GramMatrix(L)*Transpose(newBasis))));
     

      // discard odd lattice --- more theory needed
      if discardOdd and not IsEven(N) then 
        vprintf TwoNeighbours,3 : "%o expanded to an odd neighbour - discarding!\n",w;
        vprintf TwoNeighbours,3 : "Lattice: %o\n",L;
        vprintf TwoNeighbours,3 : "Neighbour: %o\n",N;
        continue; 
      end if;
      
      // set attribute to count how often we have seen this lattice so far to 1
      N`numberOfTimesVisited := 1;
      
      // get the automorphism group and create bucket key
      automOrder := #AutomorphismGroup(N : Decomposition:=useDecompositionAut, NaturalAction:=useNaturalAction, BacherDepth:=bacherDepth);
      
      sp0 := -1;
      if useSP0 then
        sp0 := SPeq0_Invar(N);
      end if;
      
      if not useSucMin then
        key:=<automOrder, ThetaSeries(N,boundThetaSeries), sp0>;
      else if not useDualSucMin then
        sucmin := SuccessiveMinima(N);
        key:=<automOrder, ThetaSeries(N,boundThetaSeries), sp0, sucmin>;
        else
          partialDualArray := [];
	  partialSucMinArray := [];
	  sv := SuccessiveMinima(N);
	
	  for x in Divisors(Exponent(DualQuotient(N))) do
	    if x eq 1 then
	      continue;
	    end if;
	     
	    if x eq Level(N) then
	      ND := CoordinateLattice(Dual(N));
	    else
	      ND := CoordinateLattice(PartialDual(N,x));
	    end if;
	    
	    Append(~partialDualArray, ND);
	  end for;
	
	  for x in partialDualArray do
	    svd := SuccessiveMinima(x);
	    Append(~partialSucMinArray, svd);
	  end for;
	  
	  key := <Order(AutomorphismGroup(N)), ThetaSeries(N,boundThetaSeries), sp0, sv, partialSucMinArray>;
        end if;
      end if;
      
      // new invariants -> create new bucket and insert the neighbour
      if not IsDefined(B,key) then
     
        Append(~Gen,N);
        B[key]:=[#Gen];
        Append(~Unexp, #Gen);
        foundNewNeighbour := true;
	
      // invariants exist - check for isometry
      else // end if not IsDefined(B,key)
	alreadyIn := false;
        
        // if we are close to the full Mass, we may discard lattices with small automorphism group
        if useReciprocal then
          if 1/automOrder gt massArray[1]-massArray[2] then
	    alreadyIn := true;
	    massArray[7]+:=1;
	    vprintf TwoNeighbours, 3 : "Discarded lattice because 1/automOrder = %o\nactualMass-currentMass = %o!\n",1/automOrder,massArray[2]-massArray[1];
	  end if;
	end if;
	
	// check for isometry
        if not alreadyIn then
	 for M in B[key] do
	    
	    if strategy eq 9 then
	      Gen[M]`numberOfTimesVisited+:=1;  // used in a search strategy (Sheogorath strategy)
	    end if;
	    
	    isIsom := IsIsometric(N,Gen[M] : Decomposition:=useDecompositionIsom, BacherDepth:=bacherDepth);
	    
	    if isIsom then
	     
	      if strategy ne 9 and strategy ne 8 then
		Gen[M]`numberOfTimesVisited+:=1;  // used in a search strategy (expand lattice we have seen the least often so far)
	      end if;
	      
	      if strategy eq 8 then
	        Gen[M]`numberOfTimesVisited +:= goodVectors[multiplicityIndex][1];
	      end if;
	      
	      alreadyIn := true;
	      break;
	    end if;
	  end for;
	end if;
          
        // not isometric -> add neighbour
        if not alreadyIn then
          Append(~Gen, N);
          Append(~B[key], #Gen);
          Append(~Unexp, #Gen);
          foundNewNeighbour := true;
        end if; // end if not alreadyIn
        
      end if; // end if isDefined(B,key) - else
    end if; // end if (v,v) mod 4 eq 0
    
    
    if foundNewNeighbour then
     
     if testReflectivity then
        if massArray[9] eq 1 then
          isReflective := true;
          if RootSystemPos(GramMatrix(N)) eq false then 
            massArray[9] := 0;
            isReflective := false;
          end if;
        end if;
        if massArray[9] eq 0 then
          isReflective := false;
        end if;
      end if;
     
      N`foundBy := massArray[8];
    
      if Minimum(N) gt massArray[3] then
        massArray[3] := Minimum(N);
        massArray[4] := 1;
        else if Minimum(N) eq massArray[3] then
          massArray[4] +:=1;
        end if;
      end if;

      if autOrderDiv in Divisors(Order(AutomorphismGroup(N))) then
        massArray[5] +:= 1;
      end if;
      
      if countNonTrivElDiv then
        sm,smv := SuccessiveMinima(L);
        if ElementaryDivisors(quo<L | smv>) ne [] then
          massArray[6] +:= 1;
        end if;
      end if;
                  
      vprintf TwoNeighbours,1 : "\t\tNumber of known lattices in this genus: %o\n", #Gen;
      vprintf TwoNeighbours,1 : "\t\tHighest Minimum found: %o (%o times)\n", massArray[3], massArray[4];
      if autOrderDiv ne 0 then
        vprintf TwoNeighbours,1 : "\t\tLattices with %o / #Aut: %o\n", autOrderDiv, massArray[5];
      end if;
      if countNonTrivElDiv then
        vprintf TwoNeighbours,1 : "\t\tLattices with non trivial elementary divisors: %o\n",massArray[6];
      end if;
      
      // increment the currentMass (massArray[2])
      massArray[2]+:=1/automOrder;
      vprintf TwoNeighbours,1 : "---------------------------------------------------------------------\n";
      vprintf TwoNeighbours,1 : "Actual mass: %o\nMass to achieve: %o\nDifference: %o\n", massArray[2], massArray[1], (massArray[1]-massArray[2])*1.0;
      vprintf TwoNeighbours,1 : "Percentual: %o %%\n", massArray[2]/massArray[1]*100.0;
      if testReflectivity then
      vprintf TwoNeighbours,1 : "Reflective: %o\n", isReflective;
      end if;
      vprintf TwoNeighbours,1 : "---------------------------------------------------------------------\n\n";
      if massArray[1] eq massArray[2] then
        break; 
      end if;
    end if;    
    
    // save file (if so requested)
    if saveFile ne "" and foundNewNeighbour then
      F:=Open((saveFile cat "Gen"),"r+");
      Seek(F,-2,2);
      Put(F, Sprintf(",\n%m];",N));
      delete F;
      
      F:=Open((saveFile cat "VisitedArray"),"r+");
      Seek(F,-2,2);
      Put(F, Sprintf(",\n%m];",N));
      delete F;
      
      visitedArray:=[];
      autoArray:=[];
      i:=0;
      for L in Gen do
        i +:= 1;
        visitedArray[i] := L`numberOfTimesVisited;
        autoArray[i] := L`AutomorphismGroup;
      end for;
      PrintFile((saveFile cat "VisitedArray"), Sprintf("visitedArray:=%m;",visitedArray) : Overwrite:=true);
      PrintFile((saveFile cat "AutoArray"), Sprintf("autoArray:=%\m;", autoArray) : Overwrite:=true);
    end if;
    
    t := Cputime(t);
    vprintf TwoNeighbours,1 : "\t\t\t\t\t\t\t\tdone in %os\n\n", t;
  end for; // for v in goodVectors
end intrinsic;

intrinsic TwoNeighbours(L::Lat : boundThetaSeries:=6, strategy:=9, useReciprocal:=false, useSucMin:=false, useDualSucMin:=false, usePartialDualSucMin:=false, useSP0:=false, 
countNonTrivElDiv:=false, useDecompositionAut:=false, useDecompositionIsom:=false, useNaturalAction:=false, bacherDepth:=-1, discardOdd:=false, discardKernel:=false, 
autOrderDiv:=0, saveFile:="", genusFile:="", doRecover:=false, recoverGen:=[], recoverAuto:=[], recoverUnexp:=[], recoverExp:=[], recoverVisited:=[], testReflectivity := false) -> 
SeqEnum                  
{Computes the Genus of L using the "Two-Neighbours"-Algorithm of Boris Hemkemeier.}

  printf "\n-------------------------------------------------------------------------------\n";
  printf "\t\tTwo-Neighbours in MAGMA beta_v1.9.\n";
  printf "Using the Two-Neighbour-Algorithm to compute the genus of the lattice\n\n%o\n\n",L;
  printf "Level : %o\n", Level(L);
  printf "Exponent of dual quotient : %o\n", Exponent(DualQuotient(L));
  printf "Mass  : %o\n\t\t\t~\n\t%o", MassRational(L), MassRational(L)*1.0;
  printf "\n-------------------------------------------------------------------------------\n\n";
  
  n:=Dimension(L);	// dimension
  massArray:=[];	// array with the actual Mass and the Mass of the lattice we have already found
  visitedArray:=[];	// used to save and recover the number of times we have seen a certain lattice
  autoArray:=[];	// used to save and recover the automorphism groups of the lattices in Gen
  B:=AssociativeArray();// array, indexed by a tuple (key) of #AutomorphismGroup(L), ThetaSeries(L,boundThetaSeries), number of pairs of orthogonal minimal vectors (to be extended)
			// each entry contains a list of the indices of those lattices in Gen with the appropriate invariants
 
 if not doRecover then
    L:=CoordinateLattice(L);
    Gen:=[L];		// numerated list of the lattices in the genus
    Unexp:=[1];		// lattices that have yet to be expanded
    Exp:=[];		// lattices that have already been expanded
    
    L`foundBy := 0;
    
    // set up Mass array
    orderL := #AutomorphismGroup(L : Decomposition:=useDecompositionAut, NaturalAction:=useNaturalAction, BacherDepth:=bacherDepth);
    Mass := MassRational(L);
    massArray[1] := Mass;
    massArray[2] := 1/orderL;
    massArray[3] := Minimum(L);		// highest minimum so far
    massArray[4] := 1;			// count of the highest minimum
    massArray[5] := 0;			// check for lattices with given automorphism group order
    massArray[6] := 0;			// count lattices with non trivial elementary divisors (L / sucminL)
    massArray[7] := 0;			// number of lattices L discarded because 1/Aut(L) was too big
    massArray[8] := 0;			// current index
    massArray[9] := 1;			// check for reflectivity
    
    if RootSystemPos(GramMatrix(L)) eq false then
      massArray[9] := 0;
    end if;
    
    if autOrderDiv in Divisors(orderL) then
      massArray[5] +:= 1;
    end if;
    
    if countNonTrivElDiv then
      sm,smv := SuccessiveMinima(L);
      if ElementaryDivisors(quo<L | smv>) ne [] then
        massArray[6] +:= 1;
      end if;
    end if;
    
    // set up keys
    if IsEmpty(Keys(B)) then
    
      sp0 := -1;
      if useSP0 then
        sp0 := SPeq0_Invar(L);
      end if;
    
      if not useSucMin then
        key := <orderL, ThetaSeries(L,boundThetaSeries), sp0>;
	B[key] := [1];
      else 
        if not useDualSucMin then
	  sucmin := SuccessiveMinima(L);
	  key := <orderL, ThetaSeries(L,boundThetaSeries), sp0, sucmin>;
	  B[key] := [1];
        else
	  partialDualArray := [];
	  partialSucMinArray := [];
	  sv := SuccessiveMinima(L);
	
	  for x in Divisors(Exponent(DualQuotient(L))) do
	    if x eq 1 then
	      continue;
	    end if;
	     
	    if x eq Level(L) then
	      LD := CoordinateLattice(Dual(L));
	    else
	      LD := CoordinateLattice(PartialDual(L,x));
	    end if;
	    
	    Append(~partialDualArray, LD);
	  end for;
	
	  for x in partialDualArray do
	    svd := SuccessiveMinima(x);
	    Append(~partialSucMinArray, svd);
	  end for;
	  
	  key := <orderL, ThetaSeries(L,boundThetaSeries), sp0, sv, partialSucMinArray>;
	  B[key] := [1];
        end if;
      end if;
    end if;
    
    // set up attribute to count how often we have already visited the lattice
    L`numberOfTimesVisited := 0;
  
  else
    vprintf TwoNeighbours,1 : "Restoring...";
    t := Cputime();
    
    Gen := recoverGen;
    Unexp := recoverUnexp;
    Exp := recoverExp;
    visitedArray := recoverVisited;
    autoArray := recoverAuto;
    Mass := MassRational(L);
    
    massArray[1] := Mass;
    massArray[2] := 0;
    massArray[3] := 0;			// highest minimum so far
    massArray[4] := 1;			// count of the highest minimum
    massArray[5] := 0;			// check for lattices with given automorphism group order
    massArray[6] := 0;			// count lattices with non trivial elementary divisors (L / sucminL)
    massArray[7] := 0;			// number of lattices L discarded because 1/Aut(L) was too big
    massArray[8] := 0;			// current index
    massArray[9] := 1;			// check for reflectivity
    
    i:=0;
    for L in Gen do
      i+:=1;
      Gen[i]`AutomorphismGroup := autoArray[i];
      automOrder := Order(Gen[i]`AutomorphismGroup);
      massArray[2] +:= 1/automOrder;
      Gen[i]`numberOfTimesVisited := visitedArray[i];
      
      if Minimum(L) gt massArray[3] then
        massArray[3] := Minimum(L);
        massArray[4] := 1;
        else if Minimum(L) eq massArray[3] then
          massArray[4] +:=1;
        end if;
      end if;
      
      if massArray[9] eq 1 and RootSystemPos(GramMatrix(L)) eq false  then
        massArray[9] := 0;
      end if;
      
      sm,smv := SuccessiveMinima(L);
      if ElementaryDivisors(quo<L | smv>) ne [] then
        massArray[6] +:= 1;
      end if;
   
      sp0 := -1;
      if useSP0 then
        sp0 := SPeq0_Invar(L);
      end if;
   
      if not useSucMin then
        key:=<automOrder, ThetaSeries(L,boundThetaSeries), sp0>;
      else 
        if not useDualSucMin then
          sucmin := SuccessiveMinima(L);
          key:=<automOrder, ThetaSeries(L,boundThetaSeries), sp0, sucmin>;
        else
          partialDualArray := [];
	  partialSucMinArray := [];
	  sv := SuccessiveMinima(L);
	
	  for x in Divisors(Exponent(DualQuotient(L))) do
	    if x eq 1 then continue; end if;
	    
	    if x eq Level(L) then
	      LD := CoordinateLattice(Dual(L));
	    else	    
	      LD := CoordinateLattice(PartialDual(L,x));
	    end if;
	    
	    Append(~partialDualArray, LD);
	  end for;
	
	  for x in partialDualArray do
	    svd := SuccessiveMinima(x);
	    Append(~partialSucMinArray, svd);
	  end for;
	  orderL := #AutomorphismGroup(L : Decomposition:=useDecompositionAut, NaturalAction:=useNaturalAction, BacherDepth:=bacherDepth);
	  key := <orderL, ThetaSeries(L,boundThetaSeries), sp0, sv, partialSucMinArray>;
        end if;
      end if;
        
      if not IsDefined(B,key) then
        B[key]:=[i];
      else
        Append(~B[key], i);
      end if;
    end for;
    t := Cputime(t);
    vprintf TwoNeighbours,1 :" done in %os\n\n!\n",t;
  end if;

  // create saveFile
  if saveFile ne "" then
   PrintFile((saveFile cat "Gen"), Sprintf("Gen:=%m", Gen) : Overwrite:=true);
   F:=Open((saveFile cat "Gen"),"r+");
   Seek(F,-4,2);
   //Put(F,"];");
   delete F;
   PrintFile((saveFile cat "Exp"), Sprintf("Exp:=%m;",Exp) : Overwrite:=true);
   i:=0;
   for L in Gen do
     i +:= 1;
     visitedArray[i] := L`numberOfTimesVisited;
     autoArray[i] := L`AutomorphismGroup;
   end for;
   PrintFile((saveFile cat "VisitedArray"), Sprintf("visitedArray:=%m;",visitedArray) : Overwrite:=true);
   PrintFile((saveFile cat "AutoArray"), Sprintf("autoArray:=%\m;", autoArray) : Overwrite:=true);
  end if;
  
  // enter the main loop
  while (not IsEmpty(Unexp)) and (massArray[1] ne massArray[2]) do
    
    // chose next lattice to be expanded
    index := 1;
    getNextLattice(~index, strategy, ~Gen, ~Unexp, useSucMin);
    curL := Gen[index];
    massArray[8] := index;
       
    vprintf TwoNeighbours,1 : "\n-------------------------------------------------------------------------------\n";
    vprintf TwoNeighbours,1 : "\t\tLattices already found: %o\n", #Gen;
    vprintf TwoNeighbours,1 : "\t\tLattices yet to expand: %o\n", #Unexp;
    vprintf TwoNeighbours,1 : "\t\tExpanding lattice: %o (%o)\n", #Exp+1, index;
    vprintf TwoNeighbours,1 : "\t\tHighest Minimum found: %o (%o times)\n", massArray[3], massArray[4];
    if autOrderDiv ne 0 then
      vprintf TwoNeighbours,1 : "\t\tLattices with %o / #Aut: %o\n", autOrderDiv, massArray[5];
    end if;
    if countNonTrivElDiv then
      vprintf TwoNeighbours,1 : "\t\tLattices with non trivial elementary divisors: %o\n",massArray[6];
    end if;
    vprintf TwoNeighbours,1 : "\t\tMass already achieved: %o %%\n", massArray[2]/massArray[1]*100.0;

    // compute 2-neighbours of L
    Neighbours(curL, ~B, ~Gen, ~Unexp, ~Exp, ~massArray : useReciprocal:=useReciprocal, strategy:=strategy, useSucMin:=useSucMin, useSP0:=useSP0,
useDualSucMin:=useDualSucMin, countNonTrivElDiv:=countNonTrivElDiv, boundThetaSeries:=boundThetaSeries, useDecompositionAut:=useDecompositionAut, 
useDecompositionIsom:=useDecompositionIsom, useNaturalAction:=useNaturalAction, bacherDepth:=bacherDepth, discardOdd:=discardOdd, discardKernel:=discardKernel, 
autOrderDiv:=autOrderDiv, saveFile:=saveFile, testReflectivity := testReflectivity);
  
    Append(~Exp, index);	// mark the lattice as expanded
    Exclude(~Unexp, index);	// delete the lattice from the unexpanded list
    
    if massArray[1] eq massArray[2] then 
      printf "Mass Reached!\n";
    end if;
        
    // save file (if so requested)
    if saveFile ne "" then
      F:=File(saveFile cat "Exp", "r+");
      Seek(F,-3,2);
      Put(F, "," cat IntegerToString(index) cat "];");
    end if;
  end while;
  
  // print the result
  isReflective := true;
  if massArray[9] eq 0 then
    isReflective := false;
  end if;
  
  vprintf TwoNeighbours,1 : "\n------------------------------------------------------------\n";
  vprintf TwoNeighbours,1 : "Classnumber : %o\n", #Gen;
  vprintf TwoNeighbours,1 : "Mass        : %o\n", massArray[2];
  vprintf TwoNeighbours,1 : "Reflective  : %o\n", isReflective;
  vprintf TwoNeighbours,1 : "Level : %o\n", Level(L);
  vprintf TwoNeighbours,1 : "Exponent of dual quotient : %o\n", Exponent(DualQuotient(L));
  vprintf TwoNeighbours,1 : "Highest Minimum found: %o (%o times)\n", massArray[3], massArray[4];
  if autOrderDiv ne 0 then
    vprintf TwoNeighbours,1 : "Lattices with %o / #Aut: %o\n", autOrderDiv, massArray[5];
  end if;
  if countNonTrivElDiv then
    vprintf TwoNeighbours,1 : "Lattices with non trivial elementary divisors: %o\n",massArray[6];
  end if;
  vprintf TwoNeighbours,1 : "Number of buckets: %o\n", #B;
  X:=[];
  for x in Keys(B) do
    Append(~X,x);
  end for;
  Sort(~X, func< x,y | #B[y] - #B[x]>);
  for i:=1 to #X do
    vprintf TwoNeighbours,1 : "\t%o (%o)\n",X[i], #B[X[i]];
  end for;
  
  vprintf TwoNeighbours,1: "Number of lattices discarded because of useReciprocal: %o\n", massArray[7];
  
  // sort the genus by decreasing minima and return
  Sort(~Gen, func< L1, L2 | Minimum(L2) - Minimum(L1) >);
 
 AdjM := ZeroMatrix(Integers(), #Gen, #Gen);
 for i:=1 to #Gen do
   if Gen[i]`foundBy ne 0 then
     AdjM[i][Integers()!Gen[i]`foundBy] := 1;
    end if;
  end for;
  
  fprintf "test.txt","%o\n%o\n",#Gen,AdjM;
 
  // if genusFile is set, print the result to a file on the disc
  if genusFile ne "" then
    PrintFile(genusFile, Sprintf("Classnumber  : %o\nMass         : %o\nFactorization:%o\n", #Gen, massArray[2], FactorizationOfQuotient(massArray[2])) : Overwrite := true);
    
    for L in Gen do
      fprintf genusFile, "%o\n", CoordinateLattice(L);
      fprintf genusFile, "#AutomorphismGroup: %o = %o\n", Factorization(Order(AutomorphismGroup(L))), Order(AutomorphismGroup(L));
      fprintf genusFile, "ThetaSeries: %o\n", ThetaSeries(L, boundThetaSeries); 
      if useSucMin then
        fprintf genusFile, "SuccessiveMinima: %o\n", SuccessiveMinima(L);
      end if;
      fprintf genusFile, "\n";
    end for;
  end if;
  
  return Gen;
end intrinsic;
