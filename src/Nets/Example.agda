open import Level
open import Agda.Builtin.Equality
open import Data.Unit
open import Data.Unit.Properties using (≡-setoid)
open import Data.Product using (Σ ; _,_)
open import Data.Nat
open import Data.Vec
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

data hierarchical : Σ _ (Vec ⊤) → Σ _ (Vec ⊤) → Set where
  ↓ : Hypergraph hierarchical 2* 1* → hierarchical 1* 1*
  app : hierarchical 2* 1*
  ⊢ : {input : Σ _ (Vec ⊤)} → hierarchical input 0*

diagram : Hypergraph Obj 2* 1*
diagram = record
            { E-size = E-size
            ; E = E
            ; conns→ = conns→
            ; conns← = conns←
            ; type-match = type-match
            ; one-to-one = one-to-one
            }
            where
              E-size = 4
              E = (_ , _ , A) ∷ (_ , _ , A) ∷ (_ , _ , B) ∷ (_ , _ , C) ∷ []
              conns→ : _
              conns→ (0F , 0F) = 1F , 1F
              conns→ (0F , 1F) = 2F , 1F
              conns→ (1F , 0F) = 2F , 0F
              conns→ (1F , 1F) = 3F , 0F
              conns→ (2F , 0F) = 1F , 0F
              conns→ (2F , 1F) = 3F , 1F
              conns→ (3F , 0F) = 4F , 0F
              conns→ (3F , 1F) = 4F , 1F
              conns→ (4F , 0F) = 0F , 0F
              conns← : _
              conns← (0F , 0F) = 4F , 0F
              conns← (1F , 0F) = 2F , 0F
              conns← (1F , 1F) = 0F , 0F
              conns← (2F , 0F) = 1F , 0F
              conns← (2F , 1F) = 0F , 1F
              conns← (3F , 0F) = 1F , 1F
              conns← (3F , 1F) = 2F , 1F
              conns← (4F , 0F) = 3F , 0F
              conns← (4F , 1F) = 3F , 1F
              type-match : _
              type-match (0F , 0F) = refl
              type-match (0F , 1F) = refl
              type-match (1F , 0F) = refl
              type-match (1F , 1F) = refl
              type-match (2F , 0F) = refl
              type-match (2F , 1F) = refl
              type-match (3F , 0F) = refl
              type-match (3F , 1F) = refl
              type-match (4F , 0F) = refl
              one-to-oneₗ : _
              one-to-oneₗ (0F , 0F) = refl , refl
              one-to-oneₗ (1F , 0F) = refl , refl
              one-to-oneₗ (1F , 1F) = refl , refl
              one-to-oneₗ (2F , 0F) = refl , refl
              one-to-oneₗ (2F , 1F) = refl , refl
              one-to-oneₗ (3F , 0F) = refl , refl
              one-to-oneₗ (3F , 1F) = refl , refl
              one-to-oneₗ (4F , 0F) = refl , refl
              one-to-oneₗ (4F , 1F) = refl , refl
              one-to-oneᵣ : _
              one-to-oneᵣ (0F , 0F) = refl , refl
              one-to-oneᵣ (0F , 1F) = refl , refl
              one-to-oneᵣ (1F , 0F) = refl , refl
              one-to-oneᵣ (1F , 1F) = refl , refl
              one-to-oneᵣ (2F , 0F) = refl , refl
              one-to-oneᵣ (2F , 1F) = refl , refl
              one-to-oneᵣ (3F , 0F) = refl , refl
              one-to-oneᵣ (3F , 1F) = refl , refl
              one-to-oneᵣ (4F , 0F) = refl , refl
              one-to-one : _
              one-to-one = one-to-oneₗ , one-to-oneᵣ
