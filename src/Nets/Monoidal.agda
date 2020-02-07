open import Level renaming (zero to lzero ; suc to lsuc)
open import Agda.Builtin.Equality
open import Data.Product as Prod using (Σ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum as Sum using (_⊎_ ; inj₁ ; inj₂ ; [_,_]′)
open import Data.Nat hiding (_⊔_)
open import Data.Vec hiding (splitAt)
open import Data.Fin renaming (zero to fzero ; suc to fsuc)
open import Data.Fin.Properties using (¬Fin0)
open import Data.Empty using (⊥-elim)
open import Data.Empty.Polymorphic renaming (⊥-elim to ⊥-elim′)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Function using (_∘_ ; Inverseᵇ ; id)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning
open import Categories.Category
open import Categories.Category.Monoidal

import Nets.Properties
import Nets.Hypergraph

module Nets.Monoidal {ℓₜ ℓₜᵣ : Level} (VLabel-setoid : Setoid ℓₜ ℓₜᵣ)
                       {ℓₒ ℓₒᵣ : Level}
                       (ELabel-setoid :
                         Σ ℕ (Vec (Setoid.Carrier VLabel-setoid)) →  -- List VLabel →
                         Σ ℕ (Vec (Setoid.Carrier VLabel-setoid)) →  -- List VLabel →
                         Setoid ℓₒ ℓₒᵣ
                       ) where

open Nets.Properties VLabel-setoid ELabel-setoid
open Nets.Hypergraph VLabel-setoid ELabel-setoid


Hypergraph-Monoidal : ∀ {l} → Monoidal (Hypergraph-Category {l})
Hypergraph-Monoidal {l} = record
  { ⊗ = record
    { F₀ = Prod.uncurry _l++_
    ; F₁ = Prod.uncurry _⨂_
    ; identity = λ {AB} → record
      { α = λ {(inj₁ ())}
      ; α′ = λ ()
      ; bijection = (λ ()) , (λ {(inj₁ ())})
      ; obj-resp = λ {(inj₁ ())}
      ; conns→-resp = conns→-resp {l} {proj₁ AB} {proj₂ AB}
      }
    ; homomorphism = {!!}
    ; F-resp-≈ = {!!}
    }
  ; unit = zero , []
  ; unitorˡ = {!!}
  ; unitorʳ = {!!}
  ; associator = {!!}
  ; unitorˡ-commute-from = {!!}
  ; unitorˡ-commute-to = {!!}
  ; unitorʳ-commute-from = {!!}
  ; unitorʳ-commute-to = {!!}
  ; assoc-commute-from = {!!}
  ; assoc-commute-to = {!!}
  ; triangle = {!!}
  ; pentagon = {!!}
  }
  where
    conns→-resp : ∀ {l} {A} {B} i → i ≡ Sum.map₂ (λ {((_ , _ , (inj₁ ())) , _)}) (Hypergraph.conns→ ((⊚-id {l} {A}) ⨂ (⊚-id {l} {B})) i)
    conns→-resp (inj₁ i) = {!!}
    conns→-resp (inj₂ ((_ , _ , (inj₁ ())) , _))
