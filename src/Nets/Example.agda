open import Level renaming (zero to lzero)
open import Agda.Builtin.Equality
open import Data.Unit
open import Data.Unit.Properties using (≡-setoid)
open import Data.Product using (Σ ; _,_)
open import Data.Sum using (inj₁ ; inj₂)
open import Data.Nat
open import Data.Vec
open import Data.Fin using (Fin)
open import Data.Fin.Patterns


open import Nets.Hypergraph ≡-setoid

module Nets.Example where 

--shorthands for common type interfaces
0* : Σ _ (Vec ⊤)
0* = 0 , []
1* : Σ _ (Vec ⊤)
1* = 1 , (tt ∷ [])
2* : Σ _ (Vec ⊤)
2* = 2 , (tt ∷ tt ∷ [])

data Obj : Σ _ (Vec ⊤) → Σ _ (Vec ⊤) → Set where
--the objects variables that we want to use along with their input/output type interfaces
  A B : Obj 2* 2*
  C   : Obj 2* 1*

data hierarchical : Σ _ (Vec ⊤) → Σ _ (Vec ⊤) → Set₁ where
   ↓ : Hypergraph hierarchical {lzero} 2* 1* → hierarchical 1* 1*
   app : hierarchical 2* 1*
   ⊢ : {input : Σ _ (Vec ⊤)} → hierarchical input 0*

diagram : Hypergraph Obj 2* 1*
diagram = record
            { E = E
            ; o = o
            ; conns→ = conns→
            ; conns← = conns←
            ; type-match = type-match
            ; one-to-one = one-to-one
            }
            where
              E = Fin 4
              o = lookup ((_ , _ , A) ∷ (_ , _ , A) ∷ (_ , _ , B) ∷ (_ , _ , C) ∷ [])
              conns→ : _
              conns→ (inj₁ 0F) = inj₂ (0F , 1F)
              conns→ (inj₁ 1F) = inj₂ (1F , 1F)
              conns→ (inj₂ (0F , 0F)) = inj₂ (1F , 0F)
              conns→ (inj₂ (0F , 1F)) = inj₂ (2F , 0F)
              conns→ (inj₂ (1F , 0F)) = inj₂ (0F , 0F)
              conns→ (inj₂ (1F , 1F)) = inj₂ (2F , 1F)
              conns→ (inj₂ (2F , 0F)) = inj₂ (3F , 0F)
              conns→ (inj₂ (2F , 1F)) = inj₂ (3F , 1F)
              conns→ (inj₂ (3F , 0F)) = inj₁ 0F
              conns← : _
              conns← (inj₁ 0F) = inj₂ (3F , 0F)
              conns← (inj₂ (0F , 0F)) = inj₂ (1F , 0F)
              conns← (inj₂ (0F , 1F)) = inj₁ 0F
              conns← (inj₂ (1F , 0F)) = inj₂ (0F , 0F)
              conns← (inj₂ (1F , 1F)) = inj₁ 1F
              conns← (inj₂ (2F , 0F)) = inj₂ (0F , 1F)
              conns← (inj₂ (2F , 1F)) = inj₂ (1F , 1F)
              conns← (inj₂ (3F , 0F)) = inj₂ (2F , 0F)
              conns← (inj₂ (3F , 1F)) = inj₂ (2F , 1F)
              type-match : _
              type-match (inj₁ 0F) = refl
              type-match (inj₁ 1F) = refl
              type-match (inj₂ (0F , 0F)) = refl
              type-match (inj₂ (0F , 1F)) = refl
              type-match (inj₂ (1F , 0F)) = refl
              type-match (inj₂ (1F , 1F)) = refl
              type-match (inj₂ (2F , 0F)) = refl
              type-match (inj₂ (2F , 1F)) = refl
              type-match (inj₂ (3F , 0F)) = refl
              one-to-oneₗ : _
              one-to-oneₗ (inj₁ 0F) = refl
              one-to-oneₗ (inj₂ (0F , 0F)) = refl
              one-to-oneₗ (inj₂ (0F , 1F)) = refl
              one-to-oneₗ (inj₂ (1F , 0F)) = refl
              one-to-oneₗ (inj₂ (1F , 1F)) = refl
              one-to-oneₗ (inj₂ (2F , 0F)) = refl
              one-to-oneₗ (inj₂ (2F , 1F)) = refl
              one-to-oneₗ (inj₂ (3F , 0F)) = refl
              one-to-oneₗ (inj₂ (3F , 1F)) = refl
              one-to-oneᵣ : _
              one-to-oneᵣ (inj₁ 0F) = refl
              one-to-oneᵣ (inj₁ 1F) = refl
              one-to-oneᵣ (inj₂ (0F , 0F)) = refl
              one-to-oneᵣ (inj₂ (0F , 1F)) = refl
              one-to-oneᵣ (inj₂ (1F , 0F)) = refl
              one-to-oneᵣ (inj₂ (1F , 1F)) = refl
              one-to-oneᵣ (inj₂ (2F , 0F)) = refl
              one-to-oneᵣ (inj₂ (2F , 1F)) = refl
              one-to-oneᵣ (inj₂ (3F , 0F)) = refl
              one-to-one : _
              one-to-one = one-to-oneₗ , one-to-oneᵣ
