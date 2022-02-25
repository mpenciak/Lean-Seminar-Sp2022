import data.rat.basic
import tactic

constants (a₁ : ℕ) (a₂ : nat) (b₁ : bool) (b₂ : bool)
#check a₁
#check a₁ + a₂
#check b₁ || b₂
-- #check b₁ + b₂


#check 3
#check 4.7

#eval 4.7

#check (4.7 : ℚ)
#eval (4.7 : ℚ)

-- #check -3
#check (-3: ℤ)


def f := (+3)
#check f
#eval f 3

def g := (+ (3 : ℚ))
#check g
#eval g (3/2)
#eval g 9

constant h : ℕ → ℕ → ℕ
#check h

def func₁ : ℕ → ℕ → ℕ := λ x y, x + 2*y + x + y
def func₂ (x : ℕ) (y : ℕ) : ℕ := 2*x + 3*y

#check func₁
#check func₂

#check func₁ 2
#check func₂ 2 3
#reduce func₁ 

theorem func_eq_func : func₁ = func₂ :=
begin
  ext x y,
  unfold func₁,
  unfold func₂,
  ring, -- This is where I used a tactic, hence the import tactic at the beginning of the file!
end