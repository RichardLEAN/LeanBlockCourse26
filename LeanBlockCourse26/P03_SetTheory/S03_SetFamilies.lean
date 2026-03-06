/-
This section is mostly inspired by the Set Theory Game:
https://github.com/leanprover-community/lean4game
-/

import Mathlib.Data.Set.Basic
import Mathlib.Order.SetNotation
import Mathlib.Tactic.Cases

variable {α : Type*}

#check Set α  -- set with elements of type α
#check Set (Set α) -- set family of sets with elements of type α


/-
# Sets: Set Families
=====================

`S : Set (Set α)` means `S` is a set of sets (a set family) of elements of type `α`.

## Intersections of Set Families

We can use `⋂₀ S`, imported through `Mathlib.Order.SetNotation`, to
denote the intersection of a set family `S`. n element is in `⋂₀ S`
if and only if it is in every set of the family `S`.
-/

lemma mem_sInter {x : α} {S : Set (Set α)} : x ∈ ⋂₀ S ↔ ∀ t ∈ S, x ∈ t := by rfl

example (S : Set α) (F : Set (Set α)) (h₁ : S ∈ F) : ⋂₀ F ⊆ S := by
  intro x h
  rw [mem_sInter] at h
  have := h S h₁
  assumption

example (S : Set α) (F : Set (Set α)) (h₁ : S ∈ F) : ⋂₀ F ⊆ S := fun _ h => h S h₁

example (F G : Set (Set α)) (h₁ : F ⊆ G) : ⋂₀ G ⊆ ⋂₀ F := by
  intro x h₂
  rw [mem_sInter] at *
  intro t h₃
  have : t ∈ G := h₁ h₃
  have : x ∈ t := h₂ t this
  assumption

example (F G : Set (Set α)) (h₁ : F ⊆ G) : ⋂₀ G ⊆ ⋂₀ F := fun _ h₂ t h₃ => h₂ t (h₁ h₃)

/-
## Unions of Set Families

We can also use `⋃₀ S` to denote the union of a set family `S`.
An element is in `⋃₀ S` iff it is in some set of the family `S`.
-/

lemma mem_sUnion {x : α} {S : Set (Set α)} : x ∈ ⋃₀ S ↔ ∃ t ∈ S, x ∈ t := by rfl

example (S : Set α) (F : Set (Set α)) (h₁ : S ∈ F) : S ⊆ ⋃₀ F := by
  intro x xs
  rw [mem_sUnion]
  use S

example (S : Set α) (F : Set (Set α)) (h₁ : S ∈ F) : S ⊆ ⋃₀ F := fun _ xs => ⟨S, h₁, xs⟩

example (F G : Set (Set α)) (h₁ : F ⊆ G) : ⋃₀ F ⊆ ⋃₀ G := by
  intro x h
  rw [mem_sUnion] at *
  obtain ⟨t, tf, xt⟩ := h
  have tg := h₁ tf
  use t 

example (F G : Set (Set α)) (h₁ : F ⊆ G) : ⋃₀ F ⊆ ⋃₀ G :=
  fun _ ⟨t, tf, xt⟩ => ⟨t, h₁ tf, xt⟩ 

/-
## Exercise Block B01
-/

-- Exercise 1.1
example (R S : Set α) : R ∪ S = ⋃₀ {R, S} := by
  sorry

-- Exercise 1.2
example (F G : Set (Set α)) : ⋃₀ (F ∪ G) = (⋃₀ F) ∪ (⋃₀ G) := by
  sorry

-- Exercise 1.2
example (S : Set α) (F : Set (Set α)) : ⋃₀ F ⊆ S ↔ ∀ t ∈ F, t ⊆ S := by
  sorry

-- Exercise 1.3
example (S : Set α) (F : Set (Set α)) : S ∩ (⋃₀ F) = ⋃₀ {t | ∃ u ∈ F, t = S ∩ u} := by
  sorry

-- Exercise 1.4
example (R S : Set α) : R ∩ S = ⋂₀ {R, S} := by
  sorry

-- Exercise 1.5
example (F G : Set (Set α)) : ⋂₀ (F ∪ G) = (⋂₀ F) ∩ (⋂₀ G) := by
  sorry

-- Exercise 1.6
example (S : Set α) (F : Set (Set α)) : S ⊆ ⋂₀ F ↔ ∀ t ∈ F, S ⊆ t := by
  sorry

-- Exercise 1.7
example (S : Set α) (F G : Set (Set α)) (h₁ : ∀ t ∈ F, S ∪ t ∈ G) : ⋂₀ G ⊆ S ∪ (⋂₀ F) := by
  sorry

-- Exercise 1.8
example (F G H : Set (Set α)) (h₁ : ∀ t ∈ F, ∃ u ∈ G, t ∩ u ∈ H) : (⋃₀ F) ∩ (⋂₀ G) ⊆ ⋃₀ H := by
  sorry

-- Exercise 1.9
example (F : Set (Set α)) : (⋃₀ F)ᶜ = ⋂₀ {t | tᶜ ∈ F} := by
  sorry

-- Exercise 1.10
example (F : Set (Set α)) : (⋂₀ F)ᶜ = ⋃₀ {t | tᶜ ∈ F} := by
  sorry

-- Exercise 1.12
example (F G : Set (Set α)) (h₁ : ∀ t ∈ F, ∃ u ∈ G, t ⊆ u) (h₂ : ∃ t ∈ F, ∀ u ∈ G, u ⊆ t) :
    ∃ s, s ∈ F ∩ G := by
  sorry

-- Exercise 1.13
example (F G : Set (Set α)) : (⋃₀ F) ∩ (⋃₀ G)ᶜ ⊆ ⋃₀ (F ∩ Gᶜ) := by
  sorry

-- Exercise 1.14
example (F G : Set (Set α)) (h₁ : ⋃₀ (F ∩ Gᶜ) ⊆ (⋃₀ F) ∩ (⋃₀ G)ᶜ) :
    (⋃₀ F) ∩ (⋃₀ G) ⊆ ⋃₀ (F ∩ G) := by
  sorry

-- Exercise 1.15
example (F G : Set (Set α)) : (⋃₀ F) ∩ (⋂₀ G)ᶜ ⊆ ⋃₀ {t | ∃ u ∈ F, ∃ v ∈ G, t = u ∩ vᶜ} := by
  sorry

-- Exercise 1.16
example (S : Set α) (h₁ : ∀ F, (⋃₀ F = S → S ∈ F)) : ∃ x, S = {x} := by
  sorry
