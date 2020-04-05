{-# OPTIONS --without-K --safe #-}

open import Level
open import Data.Product using (_,_; curry′)
open import Relation.Binary using (Setoid)
open import Relation.Binary.PropositionalEquality

open import Categories.Category
open import Categories.Category.Monoidal
open import Categories.Functor using (Functor)
open import Categories.Functor.Bifunctor using (Bifunctor)

open import Nets.Utils
open import Nets.Hypergraph

module Nets.MonoidalHelper {ℓ₁ ℓ₂ ℓ₃} (HG : Hypergraph ℓ₁ ℓ₂ ℓ₃) {l} where

open import Nets.Diagram HG
open Core {l}
open import Nets.Category HG {l} renaming (Diagram-Category to DC)

open import Categories.Morphism DC using (_≅_; module _≅_)
open import Categories.Morphism.HeterogeneousIdentity DC

module _ (⊗ : Bifunctor DC DC DC) (unit : Category.Obj DC) where

  open DC
  open Functor ⊗

  private
    _⊗₀_ : Obj → Obj → Obj
    _⊗₀_ = curry′ F₀

    _⊗₁_ : ∀ {X Y Z W} → X ⇒ Y → Z ⇒ W → X ⊗₀ Z ⇒ Y ⊗₀ W
    f ⊗₁ g = F₁ (f , g)

  module monoidal (unitl : ∀ {X} → unit ⊗₀ X ≡ X)
                  (unitr : ∀ {X} → X ⊗₀ unit ≡ X)
                  (assoc : ∀ {X Y Z} → (X ⊗₀ Y) ⊗₀ Z ≡ X ⊗₀ (Y ⊗₀ Z))
                  (id-unit-idˡ : ∀ {X Y} {f : X ⇒ Y} → subst₂ _⇒_ unitl unitl (id {unit} ⊗₁ f) ≈ f)
                  (id-unit-idʳ : ∀ {X Y} {f : X ⇒ Y} → subst₂ _⇒_ unitr unitr (f ⊗₁ id {unit}) ≈ f)
                  (f-assoc : ∀ {X X′ Y Y′ Z Z′} {f : X ⇒ X′} {g : Y ⇒ Y′} {h : Z ⇒ Z′} →
                    subst₂ _⇒_ assoc assoc ((f ⊗₁ g) ⊗₁ h) ≈ (f ⊗₁ (g ⊗₁ h)))
                  where
    open hid-Utils DC

    variable
      X Y Z : Obj
      f g h : X ⇒ Y

    unitorˡ : unit ⊗₀ X ≅ X
    unitorˡ = hid-≅ unitl

    unitorʳ : X ⊗₀ unit ≅ X
    unitorʳ = hid-≅ unitr

    associator : (X ⊗₀ Y) ⊗₀ Z ≅ X ⊗₀ (Y ⊗₀ Z)
    associator = hid-≅ assoc
        
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
