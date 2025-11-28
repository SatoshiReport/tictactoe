import Tictactoe

open Tictactoe

/-- Example lemma using mathlib to confirm the dependency is available. -/
lemma add_even (a b : ℤ) (ha : Even a) (hb : Even b) : Even (a + b) := by
  simpa using ha.add hb

def main : IO Unit :=
  pure ()
