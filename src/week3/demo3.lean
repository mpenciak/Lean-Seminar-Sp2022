-- Lean can do single line comments

/-
It also has multi-line comments
# Comments 

## can

* **have**
* `Markdown`
* _Formatting_
* [A good guide for MD syntax](https://www.markdownguide.org/basic-syntax/). 
-/

/- 
Remember the import statements, in this case it imports the file in some directory
`something_in_leans_path/data/nat/basic.lean`. They have to be at the top of the file. 
-/
import data.nat.basic
import algebra.group.basic


/- 
Opens a namespace. Now everything in this portion of code will be accessible 
as `random_examples.thing` 
-/
namespace random_examples

-- `end random_examples` is a few lines down


/- 
Makes everything in a namespace accessible. Note, this is slightly different from namespace/end.
Nothing in this file will enter the nat namespace for example. 
-/
open nat



































/-
A quick one-line format for defining things (being purposefully vague with the word things).
Subscripts can be typed using \1 \2 \3, ..., \9, \0 
-/
def definition_name (input₁ : Sort) (input₂ : Type) : Type 0 := sorry


-- You'll see a lot of lemmas. 
lemma lemma_name {implicit assumption : Prop} 
    : ℕ :=
-- Here we begin the tactics block, where all our proofs.   
begin
  sorry
end

/- 
If something is important enough it deserves to be called a theorem!
Notice you can get pretty wild with the whitespace. 
-/
theorem theorem_name (
  same : Type
  )
  : 
  ℕ = list ℕ
  := 
  by sorry

end random_examples
































/- 
Opening a section is a good way of portioning out your code off by common assumptions. 
You can name sections which can help Lean know which section to close when you say `end`. 
-/
section

-- There's an `end` a few lines down which ends the current section. 



-- Sometimes it might be annoying to have to write out the same assumptions over multiple lemmas.
lemma lemma₁ (assumption₁ : Type) (assumption₂ : Type): Prop := sorry
lemma lemma₂ (assumption₁ : Type) (assumption₂ : Type): Prop := sorry

/-
Instead we can define variables that will persist until the end of the section and become
available in each assumption. They can be implicit or explicit. 
-/
-- variables (a : ℕ) (b : ℕ) 
variables (a b : ℕ)
/- 
Notice we didn't include `a` and `b` as variables in this lemma, but it knows they exist because
of the variables above. 
-/
lemma random_lemma (h : a = b) : a = a :=
begin
  refl
end



/- 
Lean is also smart and only includes variables in the assumptions that are actually referenced.
Check out the context by putting your cusor after `by` but before the actual proof. 
-/ 
lemma other_random_lemma : a < a + 1 := by exact lt_add_one a


/- 
Sometimes you'll see lemmas or theorems with proofs that don't have `begin` and `end`. These 
are still valid proofs, but are instead called _proof terms_. We'll talk about those next time! 
-/
lemma last_random_lemma : a ≥ b ∨ a < b := le_or_lt b a

-- This ends the un-named section
end




























/- 
Sometimes it's helpful to define constants and do local calculations to test out what works and
doesn't work, but they shouldn't be part of your theorems or proofs. 
-/
constants (pointless_constant : Type)

/- 
We've seen `#check` before, it's helpful to figure out what the type of something is to test 
things out while proving stuff. There's some tricky type theory going on with the outputs. 
-/
#check pointless_constant
#check last_random_lemma



-- Starting the section called `random-section`.
section random_section

/- 
Here we see a new kind of variable declaration using the brackets `[]` (and our old friend, 
the implicit variable declaration `{}`). This is basically saying that we're carrying around 
some un-named hypothesis that G has a way of multiplying its elements throughout. 
-/
variables {G : Type} [has_mul G] (g h : G)

#check g * h

end random_section



/- 
Actually we want to use more than just the fact that we can multiply elements. We want the
multiplication to have some properties so that we can reason about it. Below we add in the
assumption that G is a group, and all that comes along with it.
-/
section stuff_about_groups
variables {G : Type} [group G] (g h : G)
 
#check g⁻¹
#check group.inv g
#check _inst_1

-- You'll see examples often in demo documents. These are basically un-named lemmas. 
example (a b : G) : a * (a⁻¹ * b) = b :=
begin
  rw [←mul_assoc, mul_right_inv, one_mul]
end


/- 
This is something more indicative of what you'll find in mathlib. There's a lot going on in
this lemma, so lets take some time to piece it all together.

* `@[simp, to_additive]` tags the lemma with the `simp` and `to_additive` attributes. Don't worry
too much about what this means for now. The key takeaway about the `simp` attribute is that
this now lets the `simp` tactic use our lemma when it does its thing.

* The names of lemmas in mathlib are usually something crazy like `mul_eq_one_iff_inv_eq`. This is
in principle in order to make it easier to find them, but I don't find this to be the case at all.

* Here we're using a new technique to prove equalities/equivalences/inequalities. This is the 
incredibly versitile `calc` block. The format 

* This is something you won't find in mathlib, but the `library_search` tactic can be helpful.
When you can't remember the names of the lemmas you need, but they aren't too hidden for Lean 
to look up `library_search` can find them for you.
-/
@[simp, to_additive]
theorem mul_eq_one_iff_inv_eq' : g * h = 1 ↔ g⁻¹ = h :=
begin
  calc g * h = 1 ↔ g = h⁻¹ : by rw mul_eq_one_iff_eq_inv
  ...            ↔ h = g⁻¹ : by library_search -- It actually worked this time!
  ...            ↔ g⁻¹ = h : by rw eq_comm
end


example (a b c d : ℕ) (hyp : c = d*a + b) (hyp' : b = a*d) : c = 2*a*d :=
/- 
think about the sequence of moves if you start with hyp and go forward by rewriting with
hyp', mul_comm, two_mul, mul_assoc
-/
-- by rw [hyp, hyp', mul_comm, two_mul, add_mul]
begin
  calc c = d*a + b   : by exact hyp
  ...    = d*a + a*d : by rw hyp'
  ...    = a*d + a*d : by rw mul_comm
  ...    = (a + a)*d : by rw add_mul
  ...    = 2*a*d     : by rw two_mul
end

#check two_mul


example (a : ℕ) : a < a + 2 :=
calc a   < a + 1 : lt_add_one a
...  < a + 2 : lt_add_one (a + 1)

end stuff_about_groups


































/-
In lean files where new objects are defined you may see the following kinds of constructions
For now don't worry too much about the differences between `structure` and `class`. Structures 
and classes are defined in terms of providing a bunch of different fields. 
-/
structure three_numbers := 
  (num1 : ℕ)
  (num2 : ℕ)
  (num3 : ℕ)

#check three_numbers.num1

/-
Here is the _class_ of a Group together with an extra point I call step which has as one of
its hypotheses that it's not the identity.
-/
class group_with_step (G : Type) extends group G :=
    (step : G)
    (step_neq_one : step ≠ 1)

-- We'll devote a lot of time to understanding `structure` and `class` later on in the semester.




/-
You may not see this too often in mathlib, but you can define inductive datatypes (whatever 
those are) using the following kind of declaration. In this case, I'm defining a datatype with
two elements.
-/
inductive z2 : Type
| e : z2
| s : z2

-- This is exactly how nat is defined!
#check nat


open z2

/-
As you can see I can play around with it just like in any other functional programming
language.
-/
def z2_mul : z2 → z2 → z2
| e e := e
| e s := s
| s e := s
| s s := e





/-
`#eval` evaluates the function. It's kind of what you would expect form an actual programming
language (which we shuldn't forget is exactly what Lean is).
-/
#eval z2_mul s s
#eval z2_mul s e

-- Here I'm saying that z2 has multiplication.
instance : has_mul z2 := {mul := z2_mul}

/-
We can now use the `*` for our function, because that's precisely how we defined the operation.
The `*` symbol is just another alias for `has_mul.mul`. We can go back and forth between the infix
and regular notation by putting the operator in `()`. All of the following lines are doing the
exact same thing.
-/
#eval e * s
#eval has_mul.mul e s
#eval (*) e s
#eval ( * s) e 






/-
We can even make things print out nicer by telling Lean how to represent the elements of my 
structure. First we define the `z2_repr` function which has a reasonable looking type.
-/  

def z2_repr : z2 → string
| e := "e"
| s := "s"

-- Next we tell Lean that z2 has a string representation given by that function. 
instance : has_repr z2 := { repr := z2_repr}

-- Now everything shows up nicely!
#eval s * e

-- Here we'll show that it actually is a group!
instance : group z2 := { mul := _,
  mul_assoc := _,
  one := _,
  one_mul := _,
  mul_one := _,
  npow := _,
  npow_zero' := _,
  npow_succ' := _,
  inv := _,
  div := _,
  div_eq_mul_inv := _,
  zpow := _,
  zpow_zero' := _,
  zpow_succ' := _,
  zpow_neg' := _,
  mul_left_inv := _ }








































-- On second thought, maybe not...

/-
There are also a lot of keywords that you may encounter. We'll get to them eventually as well, 
but it's not super critical to understand what they're all saying for now.
-/

universes u v 

variables (T : Type u)

noncomputable theory

section 

local attribute [simp] add_assoc

end

-- And other exotic things like open_locale and stuff I'm probably forgetting to mention.


































/- 
This was all probably very overwhelming! And that's ok because this was intended to be a whirlwind
tour through Lean. A lot of the things we talked about in this demo will be touched on later in
more depth, so the goal for today was to mainly show you the highlights of what's out there.

This demo file and the associated slides can serve as a possible reference guide to notation and 
constructions we'll use later in the semester (though there are still a few things I haven't
talked about). 


Where to go from here: 


* First stop is the Lean Community website: <https://leanprover-community.github.io/index.html>.
Pretty much all of links below (and much more!) can be found at this site. In particular, there's 
a section on Undergraduate math that has not been formalized yet. Check it out and maybe you can
get inspired on a project to work on! <https://leanprover-community.github.io/undergrad.html>


Some hands-on games to play with:


* If you've completed the Natural Number Game 
<https://www.ma.imperial.ac.uk/~buzzard/xena/natural_number_game/> 
or you're finding it tedious after a point, the _Real Number Game_ may be fun for you. 
The first few ``levels'' may be a bit easy after the NNG, but it gets pretty tough!
<https://github.com/leanprover-community/tutorials>

* Another way to get hands-on with Lean is by working on the _Complex Number Game_
<https://github.com/ImperialCollegeLondon/complex-number-game>
as opposed to following the usual curriculum from an undergraduate real analysis class, you'll be
constructing the complex numbers as pairs of real numbers from scratch. 

* Finally, a great learning resource which combines video lectures, demonstrations, and exercises
(and where I'm getting a lot of the inspiration for my own demos, examples, exercises, ...) is 
the _Lean for the Curious Mathematician_ 2020 conference. 
<https://leanprover-community.github.io/lftcm2020/>


If you want to read more in then some


* _Lean Forward_ <https://lean-forward.github.io/>
  * A group of researchers and grad students at Vrije Universiteit Amsterdam
  * Have 4 semesters worth of projects <https://lean-forward.github.io/logical-verification/>
  * Textbook used in the courses is excellent (though has a distinct CS flavor to it)
  <https://github.com/blanchette/logical_verification_2021/blob/main/hitchhikers_guide.pdf>

* _Theorem proving in Lean_ <https://leanprover.github.io/theorem_proving_in_lean>. Kind of the 
canonical tome. Covers pretty much everything that goes into proving theorems in Lean. 

* _Mathematics in Lean_ <https://leanprover-community.github.io/mathematics_in_lean/basics.html>. 
Much shorter than Theorem Proving in Lean, so it doesn't go into nearly as much detail. Maybe a
good first read before tackling _Theorem Proving in Lean_


Finally there's the actual documentation:


* _Lean Reference Manual_ <https://leanprover.github.io/reference/>

* _mathlib Documentation_ <https://leanprover-community.github.io/mathlib_docs/>
-/