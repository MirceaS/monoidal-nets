{-# OPTIONS --safe #-}

open import Level
open import Relation.Binary using (Setoid)
open import Function using (id; _∘_)
open import Data.Fin using (inject+; raise; splitAt)
open import Data.Sum using (inj₁; inj₂; [_,_]; map; map₁; map₂)

open import Nets.Utils

module Nets.Traced {ℓₜ ℓₜᵣ : Level}
                   (VLabel-setoid : Setoid ℓₜ ℓₜᵣ)
                   {ℓₒ ℓₒᵣ : Level}
                   (ELabel-setoid :
                     List (Setoid.Carrier VLabel-setoid) →
                     List (Setoid.Carrier VLabel-setoid) →
                     Setoid ℓₒ ℓₒᵣ
                   ) {l : Level} where

open import Nets.Hypergraph VLabel-setoid ELabel-setoid
open Core {l} using (Hypergraph)
open import Nets.Category   VLabel-setoid ELabel-setoid {l} using (Hypergraph-Category)
open import Nets.Monoidal   VLabel-setoid ELabel-setoid {l} using (Hypergraph-Monoidal)
open import Nets.Symmetric  VLabel-setoid ELabel-setoid {l} using (Hypergraph-Symmetric)

open import Categories.Category.Monoidal.Traced Hypergraph-Monoidal

open Hypergraph-Category renaming (id to cid; _∘_ to _⊚_)
open Hypergraph-Monoidal

Hypergraph-Traced : Traced
Hypergraph-Traced = record
  { symmetric = Hypergraph-Symmetric
  ; trace = trace
  ; vanishing₁ = {!!}
  ; vanishing₂ = {!!}
  ; superposing = {!!}
  ; yanking = {!!}
  }
  where
    trace : ∀ {X A B} → A ⊗₀ X ⇒ B ⊗₀ X → A ⇒ B
    trace {X} {A} {B} f = record
      { E = f.E
      ; conns→ = {!!}
      ; conns← = {!!}
      ; type-match = {!!}
      ; bijection = {!!}
      ; o = {!!}
      }
      where
        module f = Hypergraph f

        x = len X
        a = len A
        b = len B
