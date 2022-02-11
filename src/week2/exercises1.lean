
-- Include all your imports for the exercises above this line

-- Use #check below to see if you've gotten the import and namespace figured out correctly. 

/- 
 # Exercise 1: Importing something you've already done
 We (mostly) proved a handy theorem last time about all natural numbers being either even or odd. Import that file (demo1.lean) and #check if you can cite that lemma.
-/ 


/-
  # Exercise 2: Searching mathlib by name
  Here are a few lemmas by name. Import the appropriate file above, and #check to see if you got it right.

  * lemma frequently_measure_inter_ne_zero (an important result in basic ergodic theory (a part of dynamics))
  * theorem halting_problem (The theorem that says the halting problem is not computable)
  * def ideal (the definition of an ideal in a semiring)
  * theorem is_galois (a theorem that says a field is Galois iff it's separable and normal)
  * structure partition_of_unity (defines the notion of a ``partition of unity`` on a topological space)
-/


/-
  # Exercise 3: Searching through mathlib 
  Here are a few descriptions of lemmas. Try to find them, import the file, and #check your answer.

  * A lemma that says the set of neighbors of a vertex v in a subgraph G' is a subset of the vertices of the original graph G
  * A lemma that says that -1 is a square mod p if and only if p is not congruent to 3 mod 4 (this is a useful lemma to prove quadratic reciprocity)
  * A theorem that says that a linear map f has eigenvalue μ if and only if μ is a root of the minimal polynomial of f
  * A lemma that says that the tail of a list l ++ [a] is the same as the tail of l ++ [a] (i.e. tail (l ++ [a]) = tail(l) ++ [a] )
  * The Whitney embedding theorem.
  * The definition of the ``yoneda functor`` in category theory
  * A theorem that says a group G is ``nilpotent`` if and only if it has a finite ascending series
-/


/-
  # Exercise 4: Look up all your favorite mathematical objects
  Spend some time getting familiar with the layout of mathlib. Look for your favorite mathematical objects, and see if they're defined already! (If they aren't, maybe you can do it!)
-/