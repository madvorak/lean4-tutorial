import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Have


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


section posets

variable {A : Type} [Poset A]

theorem triangleless (a b c : A) :
    (a ⊑ b ∧ b ⊑ c ∧ c ⊑ a) → a = b := by
  sorry


def LowerBound (a : A) (S : Set A) : Prop :=
  ∀ x ∈ S, a ⊑ x

def UpperBound (z : A) (S : Set A) : Prop :=
  ∀ x ∈ S, x ⊑ z

def LeastUpperBound (y : A) (S : Set A) : Prop :=
  UpperBound y S ∧ ∀ z : A, UpperBound z S → y ⊑ z

def GreatLowerBound (b : A) (S : Set A) : Prop :=
  LowerBound b S ∧ ∀ a : A, LowerBound a S → a ⊑ b

class CompleteLattic (A : Type) extends Poset A where
  hasInfim : ∀ S : Set A, ∃ b : A, GreatLowerBound b S
  hasSupre : ∀ S : Set A, ∃ y : A, LeastUpperBound y S

end posets

section lattices

variable {A : Type} [CompleteLattic A]

noncomputable def infim (S : Set A) : A :=
  (CompleteLattic.hasInfim S).choose

noncomputable def supre (S : Set A) : A :=
  (CompleteLattic.hasSupre S).choose

prefix:70 " ⊓ " => infim
prefix:70 " ⊔ " => supre

end lattices
