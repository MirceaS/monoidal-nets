{-# OPTIONS --without-K --safe #-}

{- Here we define the closure of a relation on Diagrams -}

open import Level
open import Relation.Binary hiding (_⇒_; Symmetric)
open import Data.Product using (uncurry′)
open import Function using (id; _∘_; _$_)

open import Categories.Category
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Symmetric
open import Categories.Functor using (Functor)
open import Categories.Morphism using (_≅_)

open import Nets.Utils
open import Nets.Hypergraph
open import Nets.Diagram

module Nets.Closure {ℓ₁ ℓ₂ ℓ₃} (HG : Hypergraph ℓ₁ ℓ₂ ℓ₃) {l}
                    {ℓ} (_∼_ : ∀ {s t} → Rel (Core.Diagram HG {l} s t) ℓ) where

open Core HG {l}
open import Nets.Category HG {l}
open import Nets.Monoidal HG {l}
open import Nets.Symmetric HG {l}

infix 4 _∼⁺_

data _∼⁺_ : ∀ {s t} → Rel (Diagram s t) (suc l ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ) where
  inj : ∀ {s t} {d e : Diagram s t} → d ∼ e → d ∼⁺ e
  ≋-inj : ∀ {s t} {d e : Diagram s t} → d ≋ e → d ∼⁺ e
  ⊚-resp : ∀ {s m t} {d e : Diagram m t} {d′ e′ : Diagram s m} →
            d ∼⁺ e → d′ ∼⁺ e′ → (d ⊚ d′) ∼⁺ (e ⊚ e′)
  ⨂-resp : ∀ {s t s′ t′} {d e : Diagram s t} {d′ e′ : Diagram s′ t′} →
            d ∼⁺ e → d′ ∼⁺ e′ → (d ⨂ d′) ∼⁺ (e ⨂ e′)
  sym : ∀ {s t} {d e : Diagram s t} → d ∼⁺ e → e ∼⁺ d
  trans : ∀ {s t} {d e f : Diagram s t} → d ∼⁺ e → e ∼⁺ f → d ∼⁺ f

Category⁺ : Category ℓ₁ (suc l ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) (suc l ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ)
Category⁺ = categoryHelper record
  { Obj       = Obj
  ; _⇒_      = _⇒_
  ; _≈_       = _∼⁺_
  ; id        = cid
  ; _∘_       = _⊚_
  ; assoc     = ≋-inj assoc
  ; identityˡ  = ≋-inj identityˡ
  ; identityʳ  = ≋-inj identityʳ
  ; equiv     = record { refl = ≋-inj Equiv.refl ; sym = sym ; trans = trans }
  ; ∘-resp-≈  = ⊚-resp
  }
  where open Diagram-Category renaming (id to cid) hiding (_∘_)

Monoidal⁺ : Monoidal Category⁺
Monoidal⁺ = record
  { ⊗ = record
    { F₀ = F₀
    ; F₁ = F₁
    ; identity = ≋-inj identity
    ; homomorphism = ≋-inj homomorphism
    ; F-resp-≈ = uncurry′ ⨂-resp
    }
  ; unit = unit
  ; unitorˡ = record
    { from = unitorˡ.from
    ; to = unitorˡ.to
    ; iso = record { isoˡ = ≋-inj unitorˡ.isoˡ ; isoʳ = ≋-inj unitorˡ.isoʳ }
    }
  ; unitorʳ = record
    { from = unitorʳ.from
    ; to = unitorʳ.to
    ; iso = record { isoˡ = ≋-inj unitorʳ.isoˡ ; isoʳ = ≋-inj unitorʳ.isoʳ }
    }
  ; associator = λ {X} {Y} {Z} → record
    { from = associator.from {X} {Y} {Z}
    ; to = associator.to {X} {Y} {Z}
    ; iso = record { isoˡ = ≋-inj (associator.isoˡ {X} {Y} {Z}) ; isoʳ = ≋-inj (associator.isoʳ {X} {Y} {Z}) }
    }
  ; unitorˡ-commute-from = ≋-inj unitorˡ-commute-from
  ; unitorˡ-commute-to = ≋-inj unitorˡ-commute-to
  ; unitorʳ-commute-from = ≋-inj unitorʳ-commute-from
  ; unitorʳ-commute-to = ≋-inj unitorʳ-commute-to
  ; assoc-commute-from = λ {X} {Y} {Z} → ≋-inj (assoc-commute-from {X} {Y} {Z})
  ; assoc-commute-to = λ {X} {Y} {Z} → ≋-inj (assoc-commute-to {X} {Y} {Z})
  ; triangle = ≋-inj triangle
  ; pentagon = ≋-inj pentagon
  }
  where
    open Diagram-Category renaming (id to cid) hiding (_∘_)
    open Diagram-Monoidal hiding (unit)
    open Functor ⊗

Symmetric⁺ : Symmetric Monoidal⁺
Symmetric⁺ = symmetricHelper Monoidal⁺ record
  { braiding = record
    { F⇒G = record
      { η = braiding.⇒.η
      ; commute = ≋-inj ∘ braiding.⇒.commute
      ; sym-commute = ≋-inj ∘ braiding.⇒.sym-commute
      }
    ; F⇐G = record
      { η = braiding.⇐.η
      ; commute = ≋-inj ∘ braiding.⇐.commute
      ; sym-commute = ≋-inj ∘ braiding.⇐.sym-commute
      }
    ; iso = λ xy → record
      { isoˡ = ≋-inj (braiding.iso.isoˡ xy)
      ; isoʳ = ≋-inj (braiding.iso.isoʳ xy)
      }
    }
  ; commutative = ≋-inj commutative
  ; hexagon = ≋-inj hexagon₁
  }
  where
    open Diagram-Category renaming (id to cid) hiding (_∘_)
    open Diagram-Symmetric
