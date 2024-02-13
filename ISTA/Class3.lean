import Std.Tactic.Ext
import Mathlib.Tactic.Have
import Mathlib.Tactic.Lemma

variable {α : Type}


-- # Concatenating lists

def cat : List α → List α → List α
| [ ]   , y => y
| a :: x, y => a :: cat x y

theorem cat_assoc (x y z : List α) :
    cat (cat x y) z = cat x (cat y z) := by
  sorry

theorem cat_nil (x : List α) :
    cat x [] = x := by
  sorry


-- # Reversing lists

def rev : List α → List α
| [ ]    => [ ]
| a :: x => cat (rev x) [a]

private def r : List α → List α → List α
| [ ]   , y => y
| a :: x, y => r x (a :: y)

def rf (x : List α) : List α :=
  r x []

theorem rev_eq_rf : @rev α = rf := by
  sorry
