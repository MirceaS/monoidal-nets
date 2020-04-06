{-# OPTIONS --without-K --safe #-}

{- Here we define the closure of a relation on Diagrams -}

open import Level
open import Relation.Binary
open import Relation.Binary.Construct.Closure.Equivalence

open import Nets.Utils
open import Nets.Hypergraph

module Nets.Closure {ℓ₁ ℓ₂ ℓ₃} (HG : Hypergraph ℓ₁ ℓ₂ ℓ₃) {l} where

open import Nets.Diagram HG
open Core {l}

module _ {ℓ} (_~_ : ∀ {s t} → Rel (Diagram s t) ℓ) where

  data RespClosure : ∀ {s t} → Rel (Diagram s t) (suc l ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ) where
    inj : ∀ {s t} {d e : Diagram s t} → d ~ e → RespClosure d e
    ≋-inj : ∀ {s t} {d e : Diagram s t} → d ≋ e → RespClosure d e
    ⊚-resp : ∀ {s m t} {d e : Diagram m t} {d′ e′ : Diagram s m} →
              RespClosure d e → RespClosure d′ e′ → RespClosure (d ⊚ d′) (e ⊚ e′)
    ⨂-resp : ∀ {s t s′ t′} {d e : Diagram s t} {d′ e′ : Diagram s′ t′} →
              RespClosure d e → RespClosure d′ e′ → RespClosure (d ⨂ d′) (e ⨂ e′)

  FullClosure : ∀ {s t} → Rel (Diagram s t) (suc l ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ)
  FullClosure {s} {t} = EqClosure (RespClosure {s} {t})
