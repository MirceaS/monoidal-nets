{-# OPTIONS --safe #-}

open import Relation.Binary.PropositionalEquality

open import Categories.Category
import Categories.Morphism.HeterogeneousIdentity as HI

-- This module uses the K axiom and should only be imported in modules
-- that also allow the use of K
module Nets.K-Utils {o ℓ e} (C : Category o ℓ e) where
  open Category C
  open HI C

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

  hexagon₁ : ∀ {A B C D E F} (f : C ⇒ D) (g : A ⇒ B) (h : E ⇒ F)
             (BC : B ≡ C) (AE : A ≡ E) (FD : F ≡ D) →
             subst₂ _⇒_ AE (sym FD) (f ∘ (subst (A ⇒_) BC g)) ≈ h →
             f ∘ hid BC ∘ g ≈ hid FD ∘ h ∘ hid AE
  hexagon₁ f g h refl refl refl eq = begin
    f ∘ id ∘ g       ≈⟨ refl⟩∘⟨ identityˡ ⟩
    f ∘ g            ≈⟨ eq ⟩
    h                ≈˘⟨ identityʳ ⟩
    h ∘ id           ≈˘⟨ identityˡ ⟩
    id ∘ h ∘ id      ∎
    where open HomReasoning
