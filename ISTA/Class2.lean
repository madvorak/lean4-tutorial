import Mathlib.Data.Nat.Basic


class Relation (A : Type) where
  rel : A → A → Prop

infix:51 " ⊑ " => Relation.rel


def Reflexiv (A : Type) [Relation A] : Prop := ∀ x : A, x ⊑ x

def Antisym (A : Type) [Relation A] : Prop := ∀ x y : A, x ⊑ y → y ⊑ x → x = y

def Transitiv (A : Type) [Relation A] : Prop := ∀ x y z : A, x ⊑ y → y ⊑ z → x ⊑ z

class Poset (A : Type) extends Relation A where
  refle : Reflexiv A
  antis : Antisym A
  trans : Transitiv A


theorem triangleless {A : Type} [Poset A] (a b c : A) :
    (a ⊑ b ∧ b ⊑ c ∧ c ⊑ a) → a = b := by
  sorry

/-
prefix:70 " ⊓ " => CompleteLattic.infim
prefix:70 " ⊔ " => CompleteLattic.supre
-/
