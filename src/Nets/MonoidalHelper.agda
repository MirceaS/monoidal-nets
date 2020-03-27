{-# OPTIONS --safe #-}

open import Level
open import Data.Product using (_,_; curry′)
open import Relation.Binary using (Setoid)
open import Relation.Binary.PropositionalEquality

open import Categories.Category
open import Categories.Category.Monoidal
open import Categories.Functor using (Functor)
open import Categories.Functor.Bifunctor using (Bifunctor)
open import Categories.Morphism.HeterogeneousIdentity.Properties using (BF-hid)

open import Nets.Utils

module Nets.MonoidalHelper {ℓₜ ℓₜᵣ : Level} (VLabel-setoid : Setoid ℓₜ ℓₜᵣ)
                           {ℓₒ ℓₒᵣ : Level}
                           (ELabel-setoid :
                             List (Setoid.Carrier VLabel-setoid) →
                             List (Setoid.Carrier VLabel-setoid) →
                             Setoid ℓₒ ℓₒᵣ
                           ) {l : Level} where

open import Nets.Hypergraph VLabel-setoid ELabel-setoid
open Core {l}
open import Nets.Category   VLabel-setoid ELabel-setoid {l} renaming (Hypergraph-Category to HC)
open import Nets.K-Utils HC

open import Categories.Morphism HC using (_≅_; module _≅_)
open import Categories.Morphism.HeterogeneousIdentity HC

module _ (⊗ : Bifunctor HC HC HC) (unit : Category.Obj HC) where

  open HC
  open Functor ⊗

  _⊗₀_ : Obj → Obj → Obj
  _⊗₀_ = curry′ F₀

  _⊗₁_ : ∀ {X Y Z W} → X ⇒ Y → Z ⇒ W → X ⊗₀ Z ⇒ Y ⊗₀ W
  f ⊗₁ g = F₁ (f , g)

  module _ (unitl : ∀ {X} → unit ⊗₀ X ≡ X)
           (unitr : ∀ {X} → X ⊗₀ unit ≡ X)
           (assoc : ∀ {X Y Z} → (X ⊗₀ Y) ⊗₀ Z ≡ X ⊗₀ (Y ⊗₀ Z))
           (id-unit-idˡ : ∀ {X Y} {f : X ⇒ Y} → subst₂ _⇒_ unitl unitl (id {unit} ⊗₁ f) ≈ f)
           (id-unit-idʳ : ∀ {X Y} {f : X ⇒ Y} → subst₂ _⇒_ unitr unitr (f ⊗₁ id {unit}) ≈ f)
           (f-assoc : ∀ {X X′ Y Y′ Z Z′} {f : X ⇒ X′} {g : Y ⇒ Y′} {h : Z ⇒ Z′} →
             subst₂ _⇒_ assoc assoc ((f ⊗₁ g) ⊗₁ h) ≈ (f ⊗₁ (g ⊗₁ h)))
           where
    module monoidal where

      variable
        X Y Z : Obj
        f g h : X ⇒ Y

      unitorˡ : unit ⊗₀ X ≅ X
      unitorˡ = record
        { from = hid unitl
        ; to   = hid (sym unitl)
        ; iso  = record
          { isoˡ = hid-symˡ unitl
          ; isoʳ = hid-symʳ unitl
          }
        }

      unitorʳ : X ⊗₀ unit ≅ X
      unitorʳ = record
        { from = hid unitr
        ; to   = hid (sym unitr)
        ; iso  = record
          { isoˡ = hid-symˡ unitr
          ; isoʳ = hid-symʳ unitr
          }
        }

      associator : (X ⊗₀ Y) ⊗₀ Z ≅ X ⊗₀ (Y ⊗₀ Z)
      associator = record
        { from = hid assoc
        ; to   = hid (sym assoc)
        ; iso  = record
          { isoˡ = hid-symˡ assoc
          ; isoʳ = hid-symʳ assoc
          }
        }
          
      module unitorˡ {X} = _≅_ (unitorˡ {X = X})
      module unitorʳ {X} = _≅_ (unitorʳ {X = X})
      module associator {X} {Y} {Z} = _≅_ (associator {X = X} {Y = Y} {Z = Z})

      unitorˡ-commute-from : CommutativeSquare (id {unit} ⊗₁ f) unitorˡ.from unitorˡ.from f
      unitorˡ-commute-from {f = f} = square₁ (id {unit} ⊗₁ f) f unitl unitl id-unit-idˡ

      unitorˡ-commute-to : CommutativeSquare f unitorˡ.to unitorˡ.to (id {unit} ⊗₁ f)
      unitorˡ-commute-to {f = f} = square₂ f (id {unit} ⊗₁ f) unitl unitl id-unit-idˡ

      unitorʳ-commute-from : CommutativeSquare (f ⊗₁ id {unit}) unitorʳ.from unitorʳ.from f
      unitorʳ-commute-from {f = f} = square₁ (f ⊗₁ id {unit}) f unitr unitr id-unit-idʳ

      unitorʳ-commute-to : CommutativeSquare f unitorʳ.to unitorʳ.to (f ⊗₁ id {unit})
      unitorʳ-commute-to {f = f} = square₂ f (f ⊗₁ id {unit}) unitr unitr id-unit-idʳ

      assoc-commute-from : CommutativeSquare ((f ⊗₁ g) ⊗₁ h) associator.from associator.from (f ⊗₁ (g ⊗₁ h))
      assoc-commute-from {f = f} {g = g} {h = h} = square₁ ((f ⊗₁ g) ⊗₁ h) (f ⊗₁ (g ⊗₁ h)) assoc assoc f-assoc

      assoc-commute-to : CommutativeSquare (f ⊗₁ (g ⊗₁ h)) associator.to associator.to ((f ⊗₁ g) ⊗₁ h)
      assoc-commute-to {f = f} {g = g} {h = h} = square₂ (f ⊗₁ (g ⊗₁ h)) ((f ⊗₁ g) ⊗₁ h) assoc assoc f-assoc

      triangle : ∀ {X Y} → (id {Y} ⊗₁ unitorˡ.from {X}) ∘ associator.from ≈ unitorʳ.from ⊗₁ id
      triangle = begin
        _ ≈⟨ BF-hid ⊗ refl unitl ⟩∘⟨refl ⟩
        _ ≈⟨ id-triangle assoc (cong₂ _⊗₀_ refl unitl) (cong₂ _⊗₀_ unitr refl) ⟩
        _ ≈˘⟨ BF-hid ⊗ unitr refl ⟩
        _ ∎
        where open HomReasoning hiding (refl; sym; trans)

      pentagon : ∀ {X Y Z W} → (id ⊗₁ hid assoc) ∘ hid (assoc {X} {Y ⊗₀ Z}) ∘ (hid assoc ⊗₁ id {W}) ≈
                                hid assoc ∘ hid assoc
      pentagon = begin
        _ ≈⟨ BF-hid ⊗ refl assoc ⟩∘⟨ refl⟩∘⟨ BF-hid ⊗ assoc refl ⟩
        _ ≈⟨ id-pentagon (cong₂ _⊗₀_ assoc refl) assoc (cong₂ _⊗₀_ refl assoc) assoc assoc ⟩
        _ ∎
        where open HomReasoning hiding (refl; sym; trans)

    monoidal : Monoidal HC
    monoidal = record { ⊗ = ⊗; unit = unit; monoidal }
