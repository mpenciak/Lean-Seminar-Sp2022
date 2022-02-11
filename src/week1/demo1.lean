-- Welcome to Lean! As you can tell I'm working with Lean through VS Code. Unfortunately there aren't a ton of options available for Lean-compatible editors (the other option is emacs)





-- I'll be using ``tactics'' to prove the results below, so I need to import the tactics module just as I would import a module in any other language. 
import tactic
import data.nat.basic





-- A little trick so Lean doesn't get confused between my definition of even and odd and the one already implemented in Lean.
namespace hidden






-- The syntax of Lean is very human readable. It features UTF-8 encoding, and has all of our favorite characters like ←, →, ↔, ⟨⟩, ℕ, ℤ, ℝ, ℂ   

def even (n : ℕ) := ∃(k : ℕ), 2*k = n
def odd  (n : ℕ) := ∃(k : ℕ), 2*k + 1 = n





theorem even_plus_even {n m : ℕ} (h₁ : even n) (h₂ : even m) : even (n + m) :=
-- Begin and end are used to denote the beginning and end of a proof given in tactic mode. Sorry is a tactic that automatically proves any theorem! (unfortunately, it's cheating so Lean scolds us for using it)
begin
  sorry
end














-- Lets prove an even harder theorem. This time we should think a little bit about how we would go about showing this result on pen and paper before we jump into its formalization. 
theorem even_or_odd {n : ℕ} : even n ∨ odd n :=
begin
  sorry
end

end hidden
