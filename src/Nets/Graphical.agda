{-# OPTIONS --safe #-}

open import Level
open import Function using (id; _∘_; _$_)
open import Relation.Binary.PropositionalEquality
import Relation.Binary.Reasoning.Setoid as Setoid-Reasoning
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Data.Empty.Polymorphic
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Product.Properties hiding (,-injectiveʳ)
open import Data.Product.Properties.WithK
open import Data.Sum using (inj₁)
open import Data.Sum.Properties
open import Data.Fin renaming (zero to fzero) using ()

open import Categories.Category
open import Categories.Functor renaming (id to idF)
open import Categories.Adjoint
open import Categories.Category.Construction.Graphs hiding (refl; sym; trans)

open import Nets.Utils
open import Nets.Hypergraph

module Nets.Graphical where

module _ {o ℓ} (G : Graph o (suc o ⊔ ℓ) (suc o ⊔ ℓ)) where
  HG = toHypergraph G

  open import Nets.Diagram HG
  open Core using (Diagram; _≋_; _⊚_)
  open import Nets.Category HG {o}

  ToGraphical : Functor (Free G) Diagram-Category
  ToGraphical = Radjunct record
    { M₀ = _::[]
    ; M₁ = ⟦_⟧ ∘ ^
    ; M-resp-≈ = ⟦⟧-cong
    }
    where open Adjoint (CatF-is-Free o (suc o ⊔ ℓ) (suc o ⊔ ℓ))
