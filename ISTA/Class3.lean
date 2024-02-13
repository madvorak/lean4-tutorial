import Std.Tactic.Ext
import Mathlib.Tactic.Have
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Convert

variable {T : Type}


-- # Concatenating lists

def cat : List T → List T → List T
| [ ]   , y => y
| a :: x, y => a :: cat x y

theorem cat_assoc (x y z : List T) :
    cat (cat x y) z = cat x (cat y z) := by
  induction x with
  | nil => rfl
  | cons a l ih =>
    dsimp only [cat]
    rw [ih]

theorem cat_nil (x : List T) :
    cat x [] = x := by
  induction x <;> simp_all [cat]


-- # Reversing lists

def rev : List T → List T
| [ ]    => [ ]
| a :: x => cat (rev x) [a]

private def r : List T → List T → List T
| [ ]   , y => y
| a :: x, y => r x (a :: y)

def rf (x : List T) : List T := r x []

private lemma rev_eq_r (x y : List T) :
    r x y = cat (rev x) y := by
  revert y
  induction x with
  | nil =>
    intro
    rfl
  | cons a l ih =>
    intro k
    dsimp only [r, rev]
    rw [ih (a :: k), cat_assoc]
    rfl

theorem rev_eq_rf : @rev T = rf := by
  ext x
  unfold rf
  rw [rev_eq_r, cat_nil]
