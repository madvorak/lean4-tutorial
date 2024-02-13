import Std.Tactic.Ext
import Mathlib.Tactic.Have
import Mathlib.Tactic.Lemma

variable {α : Type}


def cat : List α → List α → List α
| [ ]   , y => y
| a :: x, y => a :: cat x y

theorem cat_assoc (x y z : List α) :
  cat (cat x y) z = cat x (cat y z) :=
by
  induction x with
  | nil => rfl
  | cons a s ih =>
    dsimp only [cat]
    exact congr_arg (a :: ·) ih

theorem cat_nil (x : List α) :
  cat x [] = x :=
by
  induction x with
  | nil => rfl
  | cons a s ih =>
    dsimp only [cat]
    exact congr_arg (a :: ·) ih



def rev : List α → List α
| [ ]    => [ ]
| a :: x => cat (rev x) [a]

private def r : List α → List α → List α
| [ ]   , y => y
| a :: x, y => r x (a :: y)

def rev' (x : List α) : List α :=
  r x []

private lemma rev_eq_r (x : List α) :
  rev x = r x [] :=
by
  -- starting by `induction x` would get us into a blind alley
  have generalized : ∀ x y : List α, cat (rev x) y = r x y
  · clear x
    intro x
    -- here `intro y` would get us into another blind alley
    induction x with
    | nil =>
      intro y
      rfl
    | cons a u ih =>
      intro y
      dsimp only [rev, r]
      specialize ih (a :: y)
      rw [cat_assoc]
      exact ih
  specialize generalized x []
  rw [cat_nil] at generalized
  exact generalized

theorem rev_eq_rev' : @rev α = rev' :=
by
  ext x
  apply rev_eq_r
