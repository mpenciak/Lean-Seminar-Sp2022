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


/-
That's not the answer we were expecting! To get the right answer we can force any expression of 
one type into another type (**coercion**) . This will only work if Lean has some way of 
-/
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
meta def max_of_list : list ℕ → ℕ
| L :=
begin
cases L with head tail,
exact 0,
exact max head (max_of_list tail)
end

/-
What is the type of 
-/
#check func₁_eq_func₂
#check func₁ = func₂
#check 3 = 3
#check (=) -- Meta variables appear when Lean can't specify the type of a given expression. 
#check (=) (3 : ℚ )
#check @eq -- show all the implicit arguments of an expression by including an `@`. 

/-
So if we're building functions from types to types, what are all the kinds of types that are
possible?

Lean's builtin type system has only a few (infinitely many) built in types. There is one for every 
natural number `n`, these are all refered to as `Sort n`.
-/
#check Prop
#check Type
#check Sort 1
#check Sort 2


/-
There are a few synonyms, like `Sort 0 = Sort = Prop`
-/
example : Sort   = Sort 0 := by refl
example : Prop   = Sort   := by refl

/-
And `Sort 1 = Type = Type 0`
-/
example : Type   = Sort 1 := by refl
example : Type 0 = Sort 1 := by refl

/-
and `Sort k = Type (k - 1)`
-/
example : Type 1 = Sort 2 := by refl
example : Type 2 = Sort 3 := by refl
-- and so on...

/-
The fact that `Type 0 : Type 1` is similar to the issue about why there is no set of all sets.
A convenient way of making definitions and proofs as general as possible is by introducing 
_universe variables_ and defining objects independent of universe.
-/
universes u v
variables (A : Type u) (B : Type v)

#check (A → B) -- The type is a function type is always `max u v`.

#check add_comm_group -- `u_1` is playing the role of a metavariable for universe level.
#check add_comm_group B
#check add_comm_group.add
#check @add_comm_group.add 

/-
`Prop` i.e. `Sort 0` has the property that any two instances of a `Prop` are definitionally equal. 
This is called the proof irrelevance, and is a particular choice that Lean has made.
 This is not required, and alternatives like Homotopy Type Theory exist. 
-/
example {α : Type} {a b : α} (h : a = b) (h' : a = b) : h = h' := by refl



























/-
With this in mind, it's easy to see exactly how we can compare proofs of propositions with 
definitions of functions
-/
variables (P Q R : Prop)

example : (P → Q) → ((P → Q) → R) → R :=
begin
sorry
end

example : P → (P → Q) → (Q → R) → R := sorry

/-
The final pieces of the puzzle under the hood of Lean is Lean's support for **dependent types**,
which are expressions that look like `Π (x : A), B`. 
-/
#check @list.append 
#check @eq
#check @eq ℕ 
#check @list.append string
#check Π T : Type, T → T


























/-
Everything else that you will deal with is built on top of the Lean kernel as something called an
**inductive data type**. We've seen a few examples of these before 
-/
#check list
#check nat
inductive z2 : Type
| e : z2
| s : z2

/-
Even things like structures and classes are inductive data types under the hood (though there's
a lot more going on under the hood as well)
-/
#check and
#check or

#print prefix and -- `print prefix <thing>` prints everything known in the `<thing>` namespace

/-
You can handle inductive data types via tactics like `cases`, `induction`, `split`, ... 

For example, we have seen the existential quantifier `∃` in the natural number game, and it may
have seemed strange that we dealt with it via `cases` in the NNG. Well if we dig a little deeper,
we see that it is in fact implemented as an inductive data type!
-/
#check Exists
#check @Exists
#print prefix Exists

#check (∧)
#check (∨)

#check and.intro
#check exists.intro 

example {n : ℕ} (h : even n) : odd (n + 1) ∧ even (n + 2) :=
begin
apply and.intro,
{
apply exists.elim h,
intros,
apply exists.intro a, 
sorry,
},
apply exists.elim h,
intros,
apply exists.intro a, 
sorry,
end


example {n : ℕ} (h : even n) : odd (n + 1) ∧ even (n + 2) :=
begin
split,
cases h with k hk,
use k,
sorry,
sorry,
end

example {n : ℕ} (h : even n) : odd (n + 1) ∧ even (n + 2) :=
 and.intro (exists.elim h (λa h, exists.intro a (by rw h)))
           (exists.elim h (λa h, exists.intro (a + 1) (by {rw h, ring})))


















set_option pp.beta true



/-
Even equality is an inductive data type!
-/
#check @eq

/-
What about things like rewriting expressions? The `rewrite` or `rw` tactic is actually just a
smart tactic someone wrote that trys to apply the following operation on equalities
-/
#check eq.subst 
#check @eq.subst

/-
An alternative notation for this function is.
-/
#check (▸)

/-
For example consider the following proof
-/

variables (a b c : ℕ) (hyp : b = a)

-- #check @eq.subst ℕ (λk, k + c = b + c) b a hyp 

example (hyp : a = b) : a + c = b + c :=
begin
sorry
end

/-
There's also some tools built into lean that allow you to be even more precise about how you rewrite
terms using the conversion tactic. Conversion uses a way of navigating expressions with things like
`to_lhs`, `to_rhs` to enter on the left or right of a relation. `congr` to deal with all of the
arguments, and `funext` to enter inside the arguments of a function.
-/
example : a + c = c + b :=
begin
-- conv
--   begin
--   end
sorry
end



























/-
Finally, there's the final small issue about computability, and the axiom of choice. Lean has
skirted this issue by allowing the user to choose whether or not they want to work in a computable
world
-/
#print axioms

/-
The axiom of choice is about exactly what you'd expect
-/
#check @classical.choice


/-
You may also see a `quot.sound` entry in the list of axioms, and this is an important axiom 
that we'll talk about soon. In essense, another basic construction built into Lean to deal with 
quotients is `quot`
-/
#check @quot
#print prefix quot -- You can see all of what is known about quot, the key elements ar
#check quot.mk
#check quot.map
#check quot.lift






























/-
Of course the whole point of Lean is to be a proof **assistant**, not a hinderance. This talk was
just meant to be an illustration of what's happening under the hood, not how one interacts with the
proof assistant on a day to day basis.
-/

/-
The whole point of Lean is that it does a lot for you! Implicit class instantiation, tactics,
pattern matching, automatic methods created by structure and class, etc etc...
-/