/-
The plan for this week is to tackle the typeclass system in Lean, which is the last 

We will do this by working through a few extended examples of some "real mathematics". In 
particular, we'll be talking about _monoids_ and _groups_. 
-/
import tactic

/-
If you asked a mathematican what a monoid is they'd say something like "It's a set, together with
a binary map which is associative and has two-sided identities." Before we try to implement this
definition we'll begin by making 1 modification:

Lean can talk about sets, but it is a lot more natural to define monoid structures on types instead.
Not much is lost in making this modification, and in fact there is a lot to be gained (if we go the
further step in making our types universe polymorphic)

Without further ado, we then would arrive at the following definition:
-/

#check mul_assoc

universe u

#check mul_assoc

structure mymonoid := 
(carrier : Type u)
(id' : carrier)
(mul' : carrier → carrier → carrier)
(mul_assoc' : ∀(a b c : carrier), mul' (mul' a b) c = mul' a (mul' b c))
(id_mul' : ∀a, mul' id' a = a)
(mul_id' : ∀a, mul' a id' = a)


namespace mymonoid

/- 
Writing `mul` all over the place is annoying, so we can do this. Note we're secretly doing some
typeclass stuff here
-/
instance (M : mymonoid) : has_mul M.carrier := { mul := M.mul' }
instance (M : mymonoid) : has_one M.carrier := { one := M.id' }



@[simp] lemma mul_assoc {M : mymonoid} : ∀(a b c : M.carrier), a * b * c = a * (b * c) := sorry

@[simp] lemma id_mul {M : mymonoid} : ∀(a : M.carrier), 1 * a = a := sorry

@[simp] lemma mul_id {M : mymonoid} : ∀(a : M.carrier), a * 1 = a := sorry

theorem unique_id {M : mymonoid} {e : M.carrier} (hid : ∀a, e * a = a) : e = 1 :=
begin
  specialize hid 1,
  simp at hid,
  exact hid,
end

end mymonoid

/-
The way we construct some new examples of these objects is by defining things of the appropriate
types. For example
-/

def mynat : mymonoid :=
{ carrier := ℕ,
  id' := 0,
  mul' := (+),
  mul_assoc' := add_assoc,
  id_mul' := zero_add,
  mul_id' := add_zero }




























/-
As you can see from dealing with mymonoid, we're running into some annoying issues. The first of 
which is that we have to constantly talk about the underlying type of a `M : mymonoid` by calling it
with `M.carrier`, when in principle it doesn't have any more information than a type `M` anyway.

The solution to this is to **un-bundle** the type from the structure. In some sense, we're taking
our algebraic objects and turning them into function types...
-/

structure mymonoid' (M : Type u) := 
(id' : M)
(mul' : M → M → M)
(mul_assoc' : ∀(a b c : M), mul' (mul' a b) c = mul' a (mul' b c))
(id_mul' : ∀a, mul' id' a = a)
(mul_id' : ∀a, mul' a id' = a)

/-
Of course these two constructures are equivalent to each other. 
-/

example (M : Type u) : mymonoid' M → mymonoid := λh, { carrier := M,
  id' := h.id',
  mul' := h.mul',
  mul_assoc' := h.mul_assoc',
  id_mul' := h.id_mul',
  mul_id' := h.mul_id' }

example : Π(M : mymonoid), mymonoid' M.carrier := λM, { id' := M.id', -- note the dependent type!
  mul' := M.mul',
  mul_assoc' := M.mul_assoc',
  id_mul' := M.id_mul',
  mul_id' := M.mul_id' }

/-
You may have noticed a little bit of an annoying feature in the above arguments: Because everything
was named exactly the same between the two different 

We can actually simplify the above kinds of arguments into really simple 1 or 2 line arguments:
-/

example (M : Type u) : mymonoid' M → mymonoid := λh, { carrier := M,
 ..h }

example : Π(M : mymonoid), mymonoid' M.carrier := λM, { ..M }

/-
The `..h` and `..M` say "Look at all the records defining this structure, and unfold them all and
provide." It's important that the names actually matched between the two structures, as otherwise 
this wouldn't work.

There is still something annoying about this construction, and it will become most obvious if we
want to define an extension of our object:
-/

structure mygroup' (G : Type u) extends mymonoid' G :=
(inv': G → G)
(mul_inv' : ∀g, mul' g (inv' g) = id')

def int_group' : mygroup' ℤ := { id' := 0,
  mul' := (+),
  mul_assoc' :=add_assoc,
  id_mul' := zero_add,
  mul_id' := add_zero,
  inv' := λz, -z,
  mul_inv' :=  add_neg_self }

/-
Great! We've got a `mygroup'`. But a `mygroup'` extends a `mymonoid'`... But we have no way to
access all the results we may have proven about `mymonoid'` to `int_group'`! 
-/

































/-
This problem, and many others are solved entirely by the **type class** system in Lean... You may
have seen the `[   ]` variable declarations, and these are exactly type classes! Lets see how 
groups in Lean are actually implemented:
-/

#check group






/-
That was a trip! But it was classes all the way down! has_mul, semigroup, monoid, and finally group. 
The great thing is that if we prove something about monoids, then we get the results for free for
any group because of the typeclass inheritance. 

It also solves the issue of having all those annoying structure declarations having to be explicit,
Lean has a **type class inference** system which can deduce instances of a typeclass based off 
rules available to it. Lets do some examples:
-/

class mymonoid'' (M : Type u) extends has_mul M, has_one M:= -- `extends` is not unique to classes
(mul_assoc : ∀(a b c : M), a * b * c = a * (b * c))
(id_mul : ∀a, 1 * a = a)
(mul_id : ∀a, a * 1 = a)

namespace mymonoid''

universe v

variables {M : Type u} {N : Type v} [mymonoid'' M] [mymonoid'' N]

/-
We can now provide _instances_ for the typeclass system to start inhabiting. These can be as simple
as showing previously defined structures are monoids:
-/

instance nat_is_monoid: mymonoid'' ℕ := { mul := (+),
  one := 0,
  mul_assoc := add_assoc,
  id_mul := sorry, 
  mul_id := sorry }

/-
We can even define instances in terms of other instances
-/

instance monoid_prod : mymonoid'' (M × N) := { mul := λp q, ⟨p.1 * q.1, p.2 * q.2⟩,
  one := ⟨1, 1⟩,
  mul_assoc := 
  begin
    intros a b c,
    ext,
    exact mul_assoc a.1 b.1 c.1,
    exact mul_assoc a.2 b.2 c.2,
  end,
  id_mul := sorry,
  mul_id := sorry }

variables (g h : M × N)

#check g * h

end mymonoid''

/-
This is a synonym for `class`!
-/
@[class] structure mygroup'' (G : Type u) extends mymonoid'' G, has_inv G:=
(mul_inv : ∀(g : G), g * g⁻¹ = 1)

instance int_mygroup : mygroup'' ℤ :=
{ mul := (+),
  one := 0,
  mul_assoc := add_assoc,
  id_mul := sorry,
  mul_id := sorry,
  inv := has_neg.neg,
  mul_inv := add_neg_self}

variables (G H : Type) [mygroup'' G] [mygroup'' H]
variables (g h : G × H)

#check g * h

#print instances mygroup''

































/-
Finally, let me just say a few words about where type classes are helpful in your day to day life as
a programmer. 

Typeclasses give you a way of defining polymorphic functions! 
-/

class printable (T : Type) :=
(print: T → string)

class foldable (T : Type → Type) :=
(fold (α β : Type) : (α → β → β) → β → T α → β)

#check list

instance : foldable list :=
{ fold := λα β m b L, begin
  cases L,
  exact b,
  exact m L_hd b,
end }