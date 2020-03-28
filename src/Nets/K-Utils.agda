{-# OPTIONS --safe #-}

open import Relation.Binary.PropositionalEquality

open import Categories.Category

-- This module uses the K axiom and should only be imported in modules
-- that also allow the use of K
module Nets.K-Utils {o ℓ e} (C : Category o ℓ e) where

open import Categories.Morphism.HeterogeneousIdentity C
open Category C

-- doesn't need K
square₁ : ∀ {A B C D} (f : A ⇒ B) (g : C ⇒ D) (AC : A ≡ C) (BD : B ≡ D) →
          (subst₂ _⇒_ AC BD f ≈ g) →
          CommutativeSquare f (hid AC) (hid BD) g
square₁ f g refl refl eq = begin
  id ∘ f           ≈⟨ identityˡ ⟩
  f                ≈⟨ eq ⟩
  g                ≈˘⟨ identityʳ ⟩
  g ∘ id           ∎
  where open HomReasoning

-- doesn't need K
square₂ : ∀ {A B C D} (f : A ⇒ B) (g : C ⇒ D) (CA : C ≡ A) (DB : D ≡ B) →
          (subst₂ _⇒_ CA DB g ≈ f) →
          CommutativeSquare f (hid (sym CA)) (hid (sym DB)) g
square₂ f g refl refl eq = begin
  id ∘ f           ≈⟨ identityˡ ⟩
  f                ≈˘⟨ eq ⟩
  g                ≈˘⟨ identityʳ ⟩
  g ∘ id           ∎
  where open HomReasoning

id-triangle : ∀ {A B C} (AB : A ≡ B) (BC : B ≡ C) (AC : A ≡ C) →
              hid BC ∘ hid AB ≈ hid AC
id-triangle {A} {B} {C} refl refl refl = identityʳ

id-pentagon : ∀ {A B C D E} (AB : A ≡ B) (BC : B ≡ C)
              (CD : C ≡ D) (AE : A ≡ E) (ED : E ≡ D) →
              hid CD ∘ hid BC ∘ hid AB ≈ hid ED ∘ hid AE
id-pentagon refl refl refl refl refl = begin
  id ∘ id ∘ id     ≈⟨ identityˡ ⟩
  id ∘ id          ≈⟨ identityˡ ⟩
  id               ≈˘⟨ identityˡ ⟩
  id ∘ id          ∎
  where open HomReasoning
