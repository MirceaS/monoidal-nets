{-# OPTIONS --safe #-}

open import Level
open import Data.Unit hiding (setoid)
open import Data.Fin.Patterns
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary using (Setoid)
open import Relation.Binary.PropositionalEquality

open import Nets.Utils
open patterns

module Nets.Example where

-- the box variables that we want to use along with their input/output type interfaces
data ELabel : List ⊤ → List ⊤ → Set where
  A B : ELabel 2* 1*
  C   : ELabel 1* 1*

ELabel-setoid : List ⊤ → List ⊤ → Setoid zero zero
ELabel-setoid s t = setoid (ELabel s t)

open import Nets.Diagram   ⊤ ELabel-setoid hiding (ELabel)
open Core {zero} using (Diagram)
open import Nets.Category  ⊤ ELabel-setoid {zero}
open import Nets.Monoidal  ⊤ ELabel-setoid {zero}
open import Nets.Symmetric ⊤ ELabel-setoid {zero}

{- We will be constructing the following diagram:

   D:
             0
           ╭────╮      2
      ─────┤  B │    ╭────╮      3
      ─────┤    │╲  ╱│    │    ╭────╮
           ╰────╯ ╲╱ │    ├────┤  C ├───
           ╭────╮ ╱╲ │ A  │    ╰────╯
      ─────┤  C │╱  ╲│    │
           ╰────╯    ╰────╯
             1
-}

-- First, graphically:

D-Graphical : Diagram 3* 1*
D-Graphical = record
  { E = E′ list
  ; conns→ = conns→
  ; conns← = conns←
  ; type-match = λ _ → refl
  ; bijection = bijection₁ , bijection₂
  ; o = o′ list
  }
  where
    list : List (Σ₂ _ _ ELabel)
    list = (! B :: ! C :: ! A :: ! C :: unit)

    conns→ : _
    conns→ (inp 0F) = box 0F 0F
    conns→ (inp 1F) = box 0F 1F
    conns→ (inp 2F) = box 1F 0F
    conns→ (box 0F 0F) = box 2F 1F
    conns→ (box 1F 0F) = box 2F 0F
    conns→ (box 2F 0F) = box 3F 0F
    conns→ (box 3F 0F) = oup 0F

    conns← : _
    conns← (oup 0F) = box 3F 0F
    conns← (box 3F 0F) = box 2F 0F
    conns← (box 2F 0F) = box 1F 0F
    conns← (box 2F 1F) = box 0F 0F
    conns← (box 1F 0F) = inp 2F
    conns← (box 0F 0F) = inp 0F
    conns← (box 0F 1F) = inp 1F

    bijection₂ : _
    bijection₂ (inp 0F) = refl
    bijection₂ (inp 1F) = refl
    bijection₂ (inp 2F) = refl
    bijection₂ (box 0F 0F) = refl
    bijection₂ (box 1F 0F) = refl
    bijection₂ (box 2F 0F) = refl
    bijection₂ (box 3F 0F) = refl

    bijection₁ : _
    bijection₁ (oup 0F) = refl
    bijection₁ (box 3F 0F) = refl
    bijection₁ (box 2F 0F) = refl
    bijection₁ (box 2F 1F) = refl
    bijection₁ (box 1F 0F) = refl
    bijection₁ (box 0F 0F) = refl
    bijection₁ (box 0F 1F) = refl

-- Second, compositionally:
open Diagram-Category

D-Compositional : Diagram 3* 1*
D-Compositional = ⟦ C ⟧ ∘ ⟦ A ⟧ ∘ X ∘ (⟦ B ⟧ ⊗₁ ⟦ C ⟧)
  where
    open Diagram-Symmetric
    X = braided-iso.from {1*} {1*}

same-diagram : D-Graphical ≈ D-Compositional
same-diagram = record
  { α = λ
    { (0F , refl , refl) → (inj₁ (inj₁ (inj₁ (inj₁ (refl , refl)))))
    ; (1F , refl , refl) → (inj₁ (inj₁ (inj₁ (inj₂ (refl , refl)))))
    ; (2F , refl , refl) → (inj₁ (inj₂ (refl , refl)))
    ; (3F , refl , refl) → (inj₂ (refl , refl))
    }
  ; α′ = λ
    { (inj₁ (inj₁ (inj₁ (inj₁ (refl , refl))))) → (0F , refl , refl)
    ; (inj₁ (inj₁ (inj₁ (inj₂ (refl , refl))))) → (1F , refl , refl)
    ; (inj₁ (inj₂ (refl , refl)))               → (2F , refl , refl)
    ; (inj₂ (refl , refl))                      → (3F , refl , refl)
    }
  ; bijection = (λ
    { (inj₁ (inj₁ (inj₁ (inj₁ (refl , refl))))) → refl
    ; (inj₁ (inj₁ (inj₁ (inj₂ (refl , refl))))) → refl
    ; (inj₁ (inj₂ (refl , refl)))               → refl
    ; (inj₂ (refl , refl))                      → refl
    }) , (λ
    { (0F , refl , refl) → refl
    ; (1F , refl , refl) → refl
    ; (2F , refl , refl) → refl
    ; (3F , refl , refl) → refl
    })
  ; obj-resp = λ
    { (0F , refl , refl) → refl
    ; (1F , refl , refl) → refl
    ; (2F , refl , refl) → refl
    ; (3F , refl , refl) → refl
    }
  ; conns→-resp = λ
    { (inp 0F) → refl
    ; (inp 1F) → refl
    ; (inp 2F) → refl
    ; (box 0F 0F) → refl
    ; (box 1F 0F) → refl
    ; (box 2F 0F) → refl
    ; (box 3F 0F) → refl
    }
  }
