import tactic

/-
The goal for next week is to introduce the last major piece of the Lean language that's used 
regularly in mathlib. This is the **type class** system. But before we do that, lets finish talking
about the underlying logic of Lean.

First recall how we got here: Proving theorems in Lean amounts to constructing terms of the right 
type. For example we prove the next example four times. But fundamentall all 4 proofs are exactly
the same
-/
lemma lemma1 {P Q : Prop} (h : P ∧ Q) : Q ∧ P := and.intro (and.elim_right h) (and.elim_left h) 

lemma lemma2 {P Q : Prop} (h : P ∧ Q) : Q ∧ P := and.intro (h.right) (h.left)

lemma lemma3 {P Q : Prop} : P ∧ Q → Q ∧ P := λh, ⟨h.2, h.1⟩

lemma lemma4 {P Q : Prop} : P ∧ Q → Q ∧ P :=
begin
intro h,
cases h with p q,
split,
exact q,
exact p,
end

#print lemma1
#print lemma2
#print lemma3
#print lemma4
/-
The expressiveness of Lean that allows it to formalize more complicated mathematics than just simple
logical puzzles like those above comes from its support for a couple of pieces of type theory:
**dependent types** and **inductive data types**. 

Lets focus on dependent types first. 
-/













/-
There are likely others, but in your daily life working on proofs in mathlib there are basically 
only two kinds of dependent types you'll run into: _dependent products_ and _dependent sums_. 

A dependent product is kind of like a function type, but the function's values map into different
places depending on the input. For example, consider the type of fixed-length lists:
-/
structure len_list (n : ℕ) :=
(carrier : list ℕ)
(len_eq_n : carrier.length = n)

#check len_list 3 -- List of natural numbers of length 3

/-
Consider the function which adds 0 to the front of a list
-/
def F (n : ℕ) : len_list n → len_list (n + 1) := λL, 
{ carrier  := 0 :: L.carrier,
  len_eq_n := by simp [L.len_eq_n] } -- Notice we actually had to prove something!

#check F
/-
Note the type of `F`. The `Π` in the output is exactly the dependent product. Think about what you
would want the type of `F` to be... It takes an input `n : ℕ` and the output is a function type
`len_list n → len_list (n + 1)`. You would expect that this means the type of `F` should be 

`ℕ → len_list n → len_list (n + 1)`

But of course this doesn't make sense because until we know the first argument, `n` has no meaning.
The way we should think about this is in terms of a _dependent product_ or _dependent function type_
In general, the dependent product is often times written as `Πα, β` in the CS literature which 
confuses me until I realize that `β` can actually depend on 

An even easier example that this shows up in is the `cons` function for lists (we usually write it
as `(::)`, for example `0 :: L.carrier` above)
-/

#check @list.cons
/-
Showing all the implicit arguments reveals that the `cons` function is a dependent type.

The way this appears in formalizing mathematics is in terms of the `∀` symbol. In fact, according
to lean `Π` and `∀` are synonyms. For example consider the following lemma
-/

example : ∀ (N : ℕ), N + 1 > N := lt_add_one
/-
The conclusion `N + 1 > N` is a type of type `Prop`, which _depends on a natural number N_. This is
exactly a _dependent function type_ of type `Πℕ, Prop`. he usual function type is just a dependent 
function type where the output type does not depend on the input.


Why do we also use the dependent product terminology? We can kind of think of a dependent product 
as a big infinite product over the input.
-/



























/-
The other kind of dependent type is the _dependent sum_ type `Σ`. In this case, coming up with a non
contrived CS example is a little tough, so I'll jump straight to the _logical_ analogue `∃`. 

Consider this example:
-/

example : ∃(M : ℕ), M > 2 := sorry

/-
Again, the type `M > 2` has type `Prop`, but it doesn't make sense unless we already have an `M : ℕ`
in context. In this case we say this example has type `Σℕ, Prop`. 

In general the dependent product of the form `Σα, β` (here `β` could depend on `α`) is the type of
pairs `(a, b)` where `a : α` and `b : β(α)`. In the above example the type is all the pairs

`(3, by norm_num)`,
`(4, _)`, 
`(5, _)`, 
...
where the underscores can be filled in with any term proving `M > 2`. 
-/

example : ∀(n : ℕ), ∃(M : ℕ), M > n := sorry




























/-
Reasoning about these quantifiers almost always boils down to the following rules:

* Have a `∀` in my goal? Use `intro` to eliminate it.
-/
example : ∀ (N : ℕ), N + 1 > N :=
begin
  sorry
end

/-
* Have a `∀` in a hypothesis `h`, and want to use it in a particular instance `x`? Use 
`specialize h x`
-/
example (f : ℕ → ℕ) (h1 : ∀(n : ℕ), f n > n) (h2 : ∀(n : ℕ), f n < n + 2) : ∀n , f n = n + 1 := 
begin
  sorry
end
/-
* Have a `∃` in a goal? Find some witness of the property `x` and `use x`:
-/
example : ∃ (z : ℤ), ∀(n : ℕ), z < n :=
begin
  sorry
end

/-
* Have a `∃` in a hypothesis? Use `cases` to split it up into the witness, and the proposition it 
satisfies.
-/
example (S : set ℕ) (h : ∃n, n ∈ S) : S.nonempty :=
begin
  sorry
end

























/-
We've already spent time talking about inductive data types and structures, but just to recall 
briefly look at the following two examples.
-/

inductive mynat
| zero : mynat
| succ : mynat → mynat

#print prefix mynat

structure bdd_func :=
(to_fun : ℕ → ℕ)
(bdd : ∃(M : ℕ), ∀(n : ℕ), to_fun n < M)

#print prefix bdd_func

variable f : bdd_func

-- #check f 3

instance : has_coe_to_fun bdd_func (λ_, ℕ → ℕ) := {
  coe := λf, f.to_fun
}

#check f.bdd


/-
If we have time, lets try to prove this more involved example:
-/
instance : has_add bdd_func := sorry