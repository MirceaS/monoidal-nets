{-# OPTIONS --without-K --safe #-}

open import Level
open import Relation.Binary using (Rel)

import Categories.Category.Monoidal.Reasoning as MonoidalReasoning

open import Nets.Utils
open import Nets.Hypergraph
open import Nets.Diagram

module Nets.DiagrammaticReasoning {ℓ₁ ℓ₂ ℓ₃} (HG : Hypergraph ℓ₁ ℓ₂ ℓ₃) {l}
                                  {ℓ} (_∼_ : ∀ {s t} → Rel (Core.Diagram HG {l} s t) ℓ) where

open Core HG {l}
open import Nets.Category HG {l}
open import Nets.Monoidal HG {l}

open import Nets.Closure HG {l} {ℓ} _∼_

module ⁺ = MonoidalReasoning Monoidal⁺
private
  module MR = MonoidalReasoning Diagram-Monoidal

open MR public hiding (begin_; _≡⟨⟩_; _∎⟨_⟩; step-≡; step-≡˘; step-≈; step-≈˘; _∎; _IsRelatedTo_)
open ⁺ public using (begin_; _≡⟨⟩_; _∎⟨_⟩; step-≡; step-≡˘; _∎; _IsRelatedTo_)
open Diagram-Category using (_⇒_)

infixr 2 step-≈ step-≈˘ step-∼ step-∼˘

step-≈ : ∀ {s t} (x : s ⇒ t) {y z : s ⇒ t} → y IsRelatedTo z → x ≋ y → x IsRelatedTo z
step-≈ x yz xy = ⁺.step-≈ x yz (≋-inj xy)
syntax step-≈ x y≈z x≈y = x ≈⟨ x≈y ⟩ y≈z

step-≈˘ : ∀ {s t} (x : s ⇒ t) {y z : s ⇒ t} → y IsRelatedTo z → y ≋ x → x IsRelatedTo z
step-≈˘ x yz yx = ⁺.step-≈˘ x yz (≋-inj yx)
syntax step-≈˘ x y≈z y≈x = x ≈˘⟨ y≈x ⟩ y≈z

⦅_⦆ : ∀ {s t} {d e : Diagram s t} → d ∼ e → d ∼⁺ e
⦅_⦆ = inj

step-∼ = ⁺.step-≈
syntax step-∼ x y≈z x∼⁺y = x ∼⟨ x∼⁺y ⟩ y≈z

step-∼˘ = ⁺.step-≈˘
syntax step-∼˘ x y≈z y∼⁺x = x ∼˘⟨ y∼⁺x ⟩ y≈z
