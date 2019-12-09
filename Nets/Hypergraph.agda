open import Level renaming (zero to lzero ; suc to lsuc)
open import Agda.Builtin.Equality
open import Data.Product using (Σ ; _,_ ; ∃₂ ; proj₁ ; proj₂)
open import Data.Nat hiding (_⊔_)
open import Data.Vec
open import Data.Fin renaming (zero to fzero ; suc to fsuc)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≢_)
open import Function using (_∘_ ; Inverseᵇ)

module Nets.Hypergraph {ℓₜ ℓₜᵣ : Level} (Types-setoid : Setoid ℓₜ ℓₜᵣ) where

module T = Setoid Types-setoid
T = T.Carrier

------some technical utilities------
data ⊤ {l : Level} : Set l where
  tt : ⊤

Fin-pm : {ℓ₁ : Level} {n : ℕ} → Fin (suc n) → (A : Set ℓ₁) → (B : Fin n → Set ℓ₁) → Set ℓ₁
Fin-pm fzero A _ = A
Fin-pm (fsuc i) _ B = B i
------------------------------------

record Hypergraph {ℓₒ : Level} (input : Σ _ (Vec T)) (output : Σ _ (Vec T)) : Set (ℓₜ ⊔ ℓₜᵣ ⊔ (lsuc ℓₒ)) where
  inductive
  field
    Obj : Σ _ (Vec T) → Σ _ (Vec T) → Set ℓₒ
    E-size : ℕ
    E : Vec (∃₂ Obj) E-size

  Vec-of-Vecs : Set ℓₜ
  Vec-of-Vecs = Vec (Σ _ (Vec T)) (suc E-size)

  E-inputs :  Vec-of-Vecs
  E-inputs  = output ∷ (map  proj₁          E)
  
  E-outputs : Vec-of-Vecs
  E-outputs = input  ∷ (map (proj₁ ∘ proj₂) E)

  index-pair : Vec-of-Vecs → Set
  index-pair v = Σ (Fin (suc E-size)) (λ i → Fin (proj₁ (lookup v i)))

  index-eq : (v : Vec-of-Vecs) → Rel (index-pair v) lzero
  index-eq v = λ {(i , j) (i' , j') → Σ (i ≡ i') (λ {refl → j ≡ j'})}
  
  lookup² : (v : Vec-of-Vecs) → index-pair v → T
  lookup² v = λ {(i , j) → lookup (proj₂ (lookup v i)) j}
  
  field
    conns→ : index-pair E-outputs → index-pair E-inputs
    conns← : index-pair E-inputs → index-pair E-outputs
    type-match : (ij : index-pair E-outputs) → lookup² E-outputs ij T.≈ lookup² E-inputs (conns→ ij)
    one-to-one : Inverseᵇ (index-eq E-outputs) (index-eq E-inputs) conns→ conns←



record SimpleHypergraph {ℓₒ ℓᵣ : Level} (input : Σ _ (Vec T)) (output : Σ _ (Vec T)) : Set (ℓₜ ⊔ ℓₜᵣ ⊔ (lsuc ℓᵣ) ⊔ (lsuc ℓₒ)) where
  field
    hg : Hypergraph {ℓₒ} input output

  open Hypergraph hg public

  field
    _≲_ : Rel (Fin E-size) ℓᵣ
    partial_order : IsPartialOrder _≡_ _≲_
    conns-resp-≲     : (i : Fin E-size) → (j : Fin (proj₁ (lookup E-outputs (fsuc i)))) →
                       (Fin-pm (proj₁ (conns→ ((fsuc i) , j))) ⊤ (i ≲_))
    conns-resp-≲-neq : (i : Fin E-size) → (j : Fin (proj₁ (lookup E-outputs (fsuc i)))) →
                       (Fin-pm (proj₁ (conns→ ((fsuc i) , j))) ⊤ (i ≢_))
    


--Use Example:
module _ (t : T) where
  
  2* : Σ _ (Vec T)
  2* = 2 , (t ∷ t ∷ [])
  1* : Σ _ (Vec T)
  1* = 1 , (t ∷ [])
  
  data Obj : Σ _ (Vec T) → Σ _ (Vec T) → Set where
    A B : Obj 2* 2*
    C   : Obj 2* 1*

  input = 2*
  output = 1*

  diagram : Hypergraph input output
  diagram = record
              { Obj = Obj
              ; E-size = E-size
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
                conns→ (fzero , fzero)                                = (# 1) , (# 1)
                conns→ (fzero , fsuc fzero)                           = (# 2) , (# 1)
                conns→ (fsuc fzero , fzero)                           = (# 2) , (# 0)
                conns→ (fsuc fzero , fsuc fzero)                      = (# 3) , (# 0)
                conns→ (fsuc (fsuc fzero) , fzero)                    = (# 1) , (# 0)
                conns→ (fsuc (fsuc fzero) , fsuc fzero)               = (# 3) , (# 1)
                conns→ (fsuc (fsuc (fsuc fzero)) , fzero)             = (# 4) , (# 0)
                conns→ (fsuc (fsuc (fsuc fzero)) , fsuc fzero)        = (# 4) , (# 1)
                conns→ (fsuc (fsuc (fsuc (fsuc fzero))) , fzero)      = (# 0) , (# 0)
                conns← : _
                conns← (fzero , fzero)                                = (# 4) , (# 0)
                conns← (fsuc fzero , fzero)                           = (# 2) , (# 0)
                conns← (fsuc fzero , fsuc fzero)                      = (# 0) , (# 0)
                conns← (fsuc (fsuc fzero) , fzero)                    = (# 1) , (# 0)
                conns← (fsuc (fsuc fzero) , fsuc fzero)               = (# 0) , (# 1)
                conns← (fsuc (fsuc (fsuc fzero)) , fzero)             = (# 1) , (# 1)
                conns← (fsuc (fsuc (fsuc fzero)) , fsuc fzero)        = (# 2) , (# 1)
                conns← (fsuc (fsuc (fsuc (fsuc fzero))) , fzero)      = (# 3) , (# 0)
                conns← (fsuc (fsuc (fsuc (fsuc fzero))) , fsuc fzero) = (# 3) , (# 1)
                type-match : _
                type-match (fzero , fzero)                                = T.refl
                type-match (fzero , fsuc fzero)                           = T.refl
                type-match (fsuc fzero , fzero)                           = T.refl
                type-match (fsuc fzero , fsuc fzero)                      = T.refl
                type-match (fsuc (fsuc fzero) , fzero)                    = T.refl
                type-match (fsuc (fsuc fzero) , fsuc fzero)               = T.refl
                type-match (fsuc (fsuc (fsuc fzero)) , fzero)             = T.refl
                type-match (fsuc (fsuc (fsuc fzero)) , fsuc fzero)        = T.refl
                type-match (fsuc (fsuc (fsuc (fsuc fzero))) , fzero)      = T.refl
                one-to-oneₗ : _
                one-to-oneₗ (fzero , fzero)                                = refl , refl
                one-to-oneₗ (fsuc fzero , fzero)                           = refl , refl
                one-to-oneₗ (fsuc fzero , fsuc fzero)                      = refl , refl
                one-to-oneₗ (fsuc (fsuc fzero) , fzero)                    = refl , refl
                one-to-oneₗ (fsuc (fsuc fzero) , fsuc fzero)               = refl , refl
                one-to-oneₗ (fsuc (fsuc (fsuc fzero)) , fzero)             = refl , refl
                one-to-oneₗ (fsuc (fsuc (fsuc fzero)) , fsuc fzero)        = refl , refl
                one-to-oneₗ (fsuc (fsuc (fsuc (fsuc fzero))) , fzero)      = refl , refl
                one-to-oneₗ (fsuc (fsuc (fsuc (fsuc fzero))) , fsuc fzero) = refl , refl
                one-to-oneᵣ : _
                one-to-oneᵣ (fzero , fzero)                                = refl , refl
                one-to-oneᵣ (fzero , fsuc fzero)                           = refl , refl
                one-to-oneᵣ (fsuc fzero , fzero)                           = refl , refl
                one-to-oneᵣ (fsuc fzero , fsuc fzero)                      = refl , refl
                one-to-oneᵣ (fsuc (fsuc fzero) , fzero)                    = refl , refl
                one-to-oneᵣ (fsuc (fsuc fzero) , fsuc fzero)               = refl , refl
                one-to-oneᵣ (fsuc (fsuc (fsuc fzero)) , fzero)             = refl , refl
                one-to-oneᵣ (fsuc (fsuc (fsuc fzero)) , fsuc fzero)        = refl , refl
                one-to-oneᵣ (fsuc (fsuc (fsuc (fsuc fzero))) , fzero)      = refl , refl
                one-to-one : _
                one-to-one = one-to-oneₗ , one-to-oneᵣ
