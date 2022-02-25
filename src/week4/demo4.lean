import data.rat
import tactic
/-
# Week 4: Proving things in Lean

This week the goal is to begin talking about the process of proving theorems in Lean. 

## Lean is a programming language

Lean is like any other programming language, thought it may not seem like it from our use-cases
so far. You can write totally functional. You can use `lean --run` in the terminal which will run
the `main` function in any Lean file. Check out `hello_world.lean` and `food_recommender.lean` to 
get a sense of the syntax, and see what the language is capable of (in principle anything, though
Lean 3 has a very limited standard library, so it may not be suitable for intricate tasks). 


If Lean is just a programming language, then what are we actually doing when we prove theorems?
The foundation for proof formalization in Lean is Lean's highly expressive **type system**. In Lean
everything has a fixed _type_. When we declare variables, we give their names and also provide a
typing judgement with `(x : t)` signifying that the variable `x` has type `t`. Everything's type
can be checked with `#check`.
-/
variables (a₁ : ℕ) (a₂ : nat) (b₁ : bool) (b₂ : bool)

#check a₁
#check a₁ + a₂
#check b₁ || b₂
-- #check b₁ + b₂

#check 3
#check 4.7

/-
As you can see above, Lean has some weird behaviour around thinking all numbers are natural numbers
An expression can be evaluated using `#eval`
-/
#eval 4.7

#check (4.7 : ℚ)
#eval (4.7 : ℚ)

-- #check -3
#check (-3 : ℤ)

/-
When I say everything has a type, I really mean EVERYTHING! Including functions! In fact, even 
if we don't tell Lean explicitly what the type of everything is, it will still try to determine it
(and throw an error if it is unable to). 
-/
def f := ( + 3)
#check f
#eval f 3


def g := (+ (3 : ℚ))
#check g
#eval g (3/2)
#eval g 9

/-
Functions with multiple inputs are handled via currying. Very briefly, the basic idea is that a
function `f₁ : X × Y → Z` is equivalent to a function `f₂ : X → (Y → Z)` via 
`f₁(x, y) = (f₂(x))(y)` (though Lean can do the same with a lot less parentheses). 

Finally, notice the notation `f : X → Y` is playing a double role, one as being the usual
mathematician's notation for functions from `X` to `Y`, but also it is a typing judgement 
that says `f` has type `X → Y`)
-/
variable h : ℕ → ℕ → ℕ
#check h

def func₁ : ℕ → ℕ → ℕ := λ x y, x + 2*y + x + y
def func₂ (x : ℕ) (y : ℕ) : ℕ := 2*x + 3*y

#check func₁
#check func₂

#check func₁ 2
#check func₂ 2 3
#reduce func₁ 





























/-
But our interest in Lean is in its ability to prove things! Be it about mathematical objects, or
simply just reason about functions defined in Lean itself.
-/
theorem func₁_eq_func₂ : func₁ = func₂ :=
begin
ext x y,
/-
Here we see a new tactic, called `ext`. If the work has been done in defining things appropriately,
`ext` reduces the goal of showing two functions are equal to the goal that the functions are equal
on all inputs.
-/
unfold func₁,
/-
Here we see a new tactic, called `unfold`. If we are trying to prove something about some named
object, we can unfold its definitions to get it in simpler terms. (Note this doesn't work on
structures, classes, and stuff. Just things defined with `def` (or `lemma` or `theorem`)!
-/
unfold func₂,
/-
At this point our goal is something very easily achievable. We could do this by hand, but we're
tired of the natural number game, so lets just use the `ring` tactic.
-/
ring
end

/-
So what were we actually doing in the above proof? Fundamentally, constructing a proof in Lean is
just a very fancy version of building a function with the appropriate inputs (hypotheses), and 
output. 

The precise version of all of this is called the Curry-Howard correspondence 
<https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence>. 
-/


/-
Tactics mode is also nothing special! It's just a useful tool built into Lean for constructing
functions. For example, we could 
-/

def max_of_list : list ℕ → ℕ :=
begin
intro l,
cases l with head tail,
exact 0, -- All functions in Lean must be total functions. So we assign `0` as the max of `list.nil`
exact max head (max_of_list tail) 
end

example : Sort   = Sort 0 := by refl
example : Prop   = Sort   := by refl
example : Type   = Sort 1 := by refl
example : Type 0 = Sort 1 := by refl

#check Type 1
#check Prop