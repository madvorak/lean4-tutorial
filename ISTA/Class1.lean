import Mathlib.Data.Real.Basic


def fact : ℕ → ℕ
| 0   => 1
| n+1 => (n+1) * (fact n)

#eval fact 6


def Bound (f : ℝ → ℝ) (b : ℝ) : Prop := ∀ x : ℝ, f x ≤ b

def Bounded (f : ℝ → ℝ) : Prop := ∃ b : ℝ, Bound f b

theorem bounded_add (f g : ℝ → ℝ) : Bounded f ∧ Bounded g → Bounded (f+g) := by
  intro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  use a + b
  intro x
  exact add_le_add (ha x) (hb x)


-- for next four: `exact`, `constructor`, `left`, `right`, `intro`, `use`, `cases`, `obtain`

theorem and_swap (P Q : Prop) : P ∧ Q → Q ∧ P := by
  tauto

theorem or_swap (P Q : Prop) : P ∨ Q → Q ∨ P := by
  tauto

theorem and_distrib_or (P Q R : Prop) : P ∧ (Q ∨ R) ↔ P ∧ Q ∨ P ∧ R := by
  tauto

theorem deMorgan_all {T : Type} {R : T → Prop} : (∀ a : T, ¬ R a) ↔ ¬ (∃ a : T, R a) := by
  tauto


-- prove manually:
theorem rationals_dense (x z : ℚ) : x < z → ∃ y : ℚ, x < y ∧ y < z :=
  exists_between


theorem almostCantor (T : Type) : ¬ (∃ f : T → Set T, f.Surjective) := by
  intro ⟨f, hf⟩
  obtain ⟨x, hx⟩ := hf { e : T | e ∉ f e }
  have paradox : x ∈ f x ↔ x ∉ f x
  · exact iff_of_eq (congr_arg (x ∈ ·) hx)
  tauto
