import system.io
/- 
Please disregard how messed up this file is. It was the only way
I could get Lean to do what I wanted it to do...
-/
meta def get_foods : list string → io (list string)
| foods := do
  io.put_str "What else (say nothing if you're out)?\n",
  food ← io.get_line,
  if food = "nothing" then return foods
  else get_foods (food::foods)

meta def make_sandwich : list string → string
| []              := " sandwich"
| (food :: [])    := food ++ make_sandwich []
| (food :: foods) := food ++ ", " ++ make_sandwich foods

meta def main : io unit := do
  io.put_str "What food do you have (say nothing if you're out)?\n",
  food <- io.get_line,
  if food = "nothing" then io.put_str "You must be starving!\n"
  else do {
    foods <- get_foods [food],
    io.put_str $ "You you should have a " ++ (make_sandwich foods) ++ "!\n"
  }
