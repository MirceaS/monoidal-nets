{-# OPTIONS --safe #-}

open import Level
open import Data.Unit hiding (setoid)
open import Data.Fin.Patterns
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary using (Setoid)
open import Relation.Binary.PropositionalEquality

open import Nets.Utils

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

           ╭────╮
      ─────┤  B │    ╭────╮
      ─────┤    │╲  ╱│    │    ╭────╮
           ╰────╯ ╲╱ │    ├────┤  C ├───
           ╭────╮ ╱╲ │ A  │    ╰────╯
      ─────┤  C │╱  ╲│    │
           ╰────╯    ╰────╯

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
    conns→ (inj₁ 0F) = inj₂ (! (0F , refl , refl) , 0F)
    conns→ (inj₁ 1F) = inj₂ (! (0F , refl , refl) , 1F)
    conns→ (inj₁ 2F) = inj₂ (! (1F , refl , refl) , 0F)
    conns→ (inj₂ ((_ , _ , (0F , refl , refl)) , 0F)) = inj₂ (! (2F , refl , refl) , 1F)
    conns→ (inj₂ ((_ , _ , (1F , refl , refl)) , 0F)) = inj₂ (! (2F , refl , refl) , 0F)
    conns→ (inj₂ ((_ , _ , (2F , refl , refl)) , 0F)) = inj₂ (! (3F , refl , refl) , 0F)
    conns→ (inj₂ ((_ , _ , (3F , refl , refl)) , 0F)) = inj₁ 0F

    conns← : _
    conns← (inj₁ 0F) = inj₂ (! (3F , refl , refl) , 0F)
    conns← (inj₂ ((_ , _ , (3F , refl , refl)) , 0F)) = inj₂ (! (2F , refl , refl) , 0F)
    conns← (inj₂ ((_ , _ , (2F , refl , refl)) , 0F)) = inj₂ (! (1F , refl , refl) , 0F)
    conns← (inj₂ ((_ , _ , (2F , refl , refl)) , 1F)) = inj₂ (! (0F , refl , refl) , 0F)
    conns← (inj₂ ((_ , _ , (1F , refl , refl)) , 0F)) = inj₁ 2F
    conns← (inj₂ ((_ , _ , (0F , refl , refl)) , 0F)) = inj₁ 0F
    conns← (inj₂ ((_ , _ , (0F , refl , refl)) , 1F)) = inj₁ 1F

    bijection₂ : _
    bijection₂ (inj₁ 0F) = refl
    bijection₂ (inj₁ 1F) = refl
    bijection₂ (inj₁ 2F) = refl
    bijection₂ (inj₂ ((_ , _ , (0F , refl , refl)) , 0F)) = refl
    bijection₂ (inj₂ ((_ , _ , (1F , refl , refl)) , 0F)) = refl
    bijection₂ (inj₂ ((_ , _ , (2F , refl , refl)) , 0F)) = refl
    bijection₂ (inj₂ ((_ , _ , (3F , refl , refl)) , 0F)) = refl

    bijection₁ : _
    bijection₁ (inj₁ 0F) = refl
    bijection₁ (inj₂ ((_ , _ , (3F , refl , refl)) , 0F)) = refl
    bijection₁ (inj₂ ((_ , _ , (2F , refl , refl)) , 0F)) = refl
    bijection₁ (inj₂ ((_ , _ , (2F , refl , refl)) , 1F)) = refl
    bijection₁ (inj₂ ((_ , _ , (1F , refl , refl)) , 0F)) = refl
    bijection₁ (inj₂ ((_ , _ , (0F , refl , refl)) , 0F)) = refl
    bijection₁ (inj₂ ((_ , _ , (0F , refl , refl)) , 1F)) = refl

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
    { (inj₁ 0F) → refl
    ; (inj₁ 1F) → refl
    ; (inj₁ 2F) → refl
    ; (inj₂ ((_ , _ , (0F , refl , refl)) , 0F)) → refl
    ; (inj₂ ((_ , _ , (1F , refl , refl)) , 0F)) → refl
    ; (inj₂ ((_ , _ , (2F , refl , refl)) , 0F)) → refl
    ; (inj₂ ((_ , _ , (3F , refl , refl)) , 0F)) → refl
    }
  }
