import Std.Tactic.Ext
import Mathlib.Tactic.Have
import Mathlib.Tactic.Lemma

variable {T : Type}


-- # Concatenating lists

def cat : List T → List T → List T
| [ ]   , y => y
| a :: x, y => a :: cat x y

theorem cat_assoc (x y z : List T) :
    cat (cat x y) z = cat x (cat y z) := by
  sorry

theorem cat_nil (x : List T) :
    cat x [] = x := by
  sorry


-- # Reversing lists

def rev : List T → List T
| [ ]    => [ ]
| a :: x => cat (rev x) [a]

private def r : List T → List T → List T
| [ ]   , y => y
| a :: x, y => r x (a :: y)

def rf (x : List T) : List T := r x []

theorem rev_eq_rf : @rev T = rf := by
  sorry
