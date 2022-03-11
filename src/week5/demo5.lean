/-
The goal of this demo is to serve as an extended example to show the process of working with
and extending mathematical structures in Lean. A lot of this file is taken from Floris van Doorn's 
demo in LFTCM2020.

We first import a few modules we want from later to connect with later in the document.
-/
import algebra.group.defs
import category_theory.category.basic


/-
This is a long file, so we'll want to section off parts of the document to keep the local variables,
notation, and more isolated.
-/
section basic_definitions

/-
Structures are defined in the following format: 


structure structure_name :=
(field1 : ...)
(field2 : ...)
...
(fieldn : ...)


This is very similar to the inductive datatypes that we've seen before. For this demo we'll be
focusing on a simple structure called a _Pointed type_. The structure is simply some type, together
with a particular instance of said type. We can think of them as pairs of a type `T` and some 
`p : T`. 
-/
structure pointed_type :=
(type : Type*)
(point : type)

/-
Lean now recognizes this as a new type. We could have provided the type ascription to 
`pointed_type : Type (u + 1)`, but Lean does it for us.
-/
#check pointed_type

/-
Lean now recognizes this type as something we can refer to, and construct new types out of.
-/
#check ℕ → pointed_type 
#check ℕ × pointed_type
#check list pointed_type


/-
We can even provide instances of this structure. For example the natural numbers `ℕ` could be 
considered a pointed type by considering the pair `(ℕ, 0)`. The method to do this is to use
`name.mk`:
-/
def pointed_nat : pointed_type := pointed_type.mk ℕ 0
def pointed_int : pointed_type := pointed_type.mk ℤ 0

-- You can also use an "anonymous constructor" by using angle brackets `\< \>`.
def pointed_nat_with_1 : pointed_type := ⟨ℕ, 1⟩

-- We can `#check` to see if Lean recognizes them.
#check pointed_nat

/-
We can even ask Lean to `#reduce` them. This is similar to evaluation, but essentially asks Lean to 
rewrite the expression in simplest terms.
-/
#reduce pointed_nat

/-
In fact, using the `structure` keyword means that Lean has generated a ton of useful functions 
associated with our new type. 
-/
#print prefix pointed_type

/-
Some highlights are: 
* `pointed_type.mk : Π (carrier : Type u), carrier → pointed_type`
This is the `make` function. We saw above, the `Π` symbol can basically be thought of as a `λ`, so
the above type takes in a `carrier`, a `point` of the carrier, and returns a `pointed_type`. This is
exactly how we've been using it

* It also automatically provides `pointed_type.carrier` and `pointed_type.point` to
extract the components of 
-/

open pointed_type

#check type
#check point

#reduce type pointed_nat 
#reduce type pointed_int

/-
Lean also lets you use the usual `.` notation you may be familiar with in OOP. Because 
`pointed_nat_with_1` is a `pointed_type`, then we can call `pointed_type.point` by just typing:
-/
#reduce pointed_nat_with_1.point

/-
* Another useful function that is constructed when dealing with a structure is `pointed_type.rec`, 
`pointed_type.rec_on`, `pointed_type.cases_on` (a synonym). The exact type signature is not super
important, but the key takeaway is that it allows us to define things on `pointed_types` by 
-/
#print prefix pointed_type

#print pointed_type.rec
#check pointed_type.cases_on  

/-
Lets do a few more constructions of pointed types. In fact, any non-empty type is a pointed type
if we just choose some instance!
-/
noncomputable def from_nonempty {X : Type} (h : nonempty X) : pointed_type := { type := X,
  point := classical.choice h }

#check classical.choice
-- We see here we need to make this a noncomputable definition, becuase we're using choice.

/-
Actually this gives us an idea that maybe we could show that any pointed type is nonempty! Though 
when we look at the type of nonempty we see that it's expecting something in the usual `Sort` 
hierarchy. 

We can get around this by offering a **coercion** from . This is just like the coercion we have to
specficy when we want to consider `3` as an integer: `(3 : ℤ)`
-/
instance : has_coe_to_sort pointed_type (Type*) := ⟨pointed_type.type⟩

#check pointed_nat
#check (pointed_nat : Type)


/- 
Now we can prove the lemma that `pointed_type`s are nonempty by providing a witness!
-/
namespace pointed_type

lemma nonempty (X : pointed_type) : nonempty X := nonempty.intro X.point

/-
Finally, a large class of pointed types can be generated in the following way:
-/
def from_has_one (X : Type) [has_one X] : pointed_type := ⟨X, 1⟩

#reduce from_has_one ℤ

variables (G : Type) [group G] 

#reduce from_has_one G

/-
We can even define the product of pointed types.
-/
@[simps point]
def prod (A B : pointed_type) : pointed_type :=
{ type := A × B,
  point := (A.point, B.point) }

/-
Finally, a small command that I learned which is nice to remind yourself of what variables are in 
scope
-/
#where

end pointed_type
end basic_definitions

section pointed_maps

/-
Unfortunately pointed types are not super interesting to reason about, but one thing we can do is 
define maps between them! Intuitively, a good notion of a map between pointed types is one which
respects the point. This can also be encoded as a structure!
-/
structure pointed_map (A B : pointed_type) :=
(to_fun : A → B) -- The actual function
(to_fun_point : to_fun A.point = B.point) -- The property that the function respects the points

-- Just a quick example of how we can reason about this!
def pointed_coe' : pointed_map pointed_nat pointed_int := sorry

/-
Actually on second though, this is all getting a little annoying to write out all the time! Lets 
give ourselves some nice notation to work with
-/

notation `ℕ⬝` := pointed_nat
notation `ℤ⬝` := pointed_int
infix ` →⬝ `:25 := pointed_map

#check ℤ

#check ℕ.

-- Now the definition looks a lot nicer!
def pointed_coe : ℕ⬝ →⬝ ℤ⬝ := { to_fun := int.of_nat,
  to_fun_point := 
  begin
    -- Sometimes when it's not entirely clear what we're trying to prove, `dunfold` and `unfold` 
    -- can be your friend! (though it also feels sometimes that definitions aren't unfolding when
    -- they should.)
    sorry
  end }


namespace pointed_map
variables {A B C D : pointed_type}
variables {g : B →⬝ C} {f f₁ f₂ : A →⬝ B} {h : C →⬝ D}
variable (a : A)

/-
You would hope something like this would work
-/
-- #check f a
/-
But Lean rightfully complains that `f` is a `pointed_map` and not a function! In order to "apply" it 
to anything, we need to remember that one of its fields is `to_fun`
-/
#check f.to_fun a

/-
But this is annoying, so we can do better and coerce it into a function type using `has_coe_to_fun`!
-/
instance : has_coe_to_fun (A →⬝ B) (λ (h : A →⬝ B ), A → B) := ⟨pointed_map.to_fun⟩

-- And now it works
#check f a

/-
It's usually a good idea to provide a couple `simp` lemmas to help Lean unfold definitions along
the way
-/
@[simp] lemma coe_mk {f : A → B} {hf : f A.point = B.point} {x : A} :
  { pointed_map . to_fun := f, to_fun_point := hf } x = f x := by refl

@[simp] lemma coe_point : f A.point = B.point := f.to_fun_point

/-
And also prove an extensionality lemma that when two pointed maps are the same:
-/
@[ext] protected lemma ext (hf₁₂ : ∀ x, f₁ x = f₂ x) : f₁ = f₂ :=
begin
  -- It probably pays for the first step to be splitting up `f₁` and `f₂` into their constituent
  -- parts with `cases f₁`
  sorry
end

/-
We can now start prove basic things about pointed maps
-/
def comp (g : B →⬝ C) (f : A →⬝ B) : A →⬝ C :=
sorry

def id : A →⬝ A :=
sorry

lemma comp_assoc : h.comp (g.comp f) = (h.comp g).comp f :=
sorry

lemma id_comp : f.comp id = f :=
sorry

lemma comp_id : id.comp f = f :=
sorry

/-
We can define a few maps into and out of products of pointed types, and then prove properties about
them as well!
-/
def fst : A.prod B →⬝ A :=
sorry

def snd : A.prod B →⬝ B :=
sorry

def pair (f : C →⬝ A) (g : C →⬝ B) : C →⬝ A.prod B :=
sorry

lemma fst_pair (f : C →⬝ A) (g : C →⬝ B) : fst.comp (f.pair g) = f :=
sorry

lemma snd_pair (f : C →⬝ A) (g : C →⬝ B) : snd.comp (f.pair g) = g :=
sorry

lemma pair_unique (f : C →⬝ A) (g : C →⬝ B) (u : C→⬝ A.prod B) (h1u : fst.comp u = f)
  (h2u : snd.comp u = g) : u = f.pair g :=
begin
  sorry
end

end pointed_map
end pointed_maps