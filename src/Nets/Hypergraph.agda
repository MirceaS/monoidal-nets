open import Level renaming (zero to lzero ; suc to lsuc)
open import Agda.Builtin.Equality
open import Data.Product using (Σ ; _,_ ; ∃₂ ; proj₁ ; proj₂ ; map₁ ; map₂) renaming (map to pair-map)
open import Data.Sum hiding (map ; map₁ ; map₂)
open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties using (+-suc)
open import Data.Vec hiding (splitAt)
open import Data.Vec.Properties using (lookup-map)
open import Data.Fin renaming (zero to fzero ; suc to fsuc ; _+_ to _+f_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≢_ ; cong ; sym ; trans)
open import Function using (_∘_ ; Inverseᵇ ; id)

module Nets.Hypergraph {ℓₜ ℓₜᵣ : Level} (Types-setoid : Setoid ℓₜ ℓₜᵣ) {ℓₒ : Level} (Obj : Σ _ (Vec (Setoid.Carrier Types-setoid)) → Σ _ (Vec (Setoid.Carrier Types-setoid)) → Set ℓₒ) where

module T = Setoid Types-setoid
T = T.Carrier

------some technical utilities------
data ⊤' {l : Level} : Set l where
  tt : ⊤'

Fin-pm : {ℓ₁ : Level} {n : ℕ} → Fin (suc n) → (A : Set ℓ₁) → (B : Fin n → Set ℓ₁) → Set ℓ₁
Fin-pm fzero A _ = A
Fin-pm (fsuc i) _ B = B i

--lemma1 : ((na , A) : Σ _ (Vec T)) → ((nb , B) : Σ _ (Vec T)) → (i : Fin na) → lookup i A ≡ lookup (inject+ nb i) (A ++ B)
--lemma1 (na , A) (zero , []) = 
------------------------------------

record Hypergraph (input : Σ _ (Vec T)) (output : Σ _ (Vec T)) : Set (ℓₜ ⊔ ℓₜᵣ ⊔ ℓₒ) where
  field
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



record SimpleHypergraph {ℓᵣ : Level} (input : Σ _ (Vec T)) (output : Σ _ (Vec T)) : Set (ℓₜ ⊔ ℓₜᵣ ⊔ (lsuc ℓᵣ) ⊔ (lsuc ℓₒ)) where
  field
    hg : Hypergraph input output

  open Hypergraph hg public

  field
    _≲_ : Rel (Fin E-size) ℓᵣ
    partial_order : IsPartialOrder _≡_ _≲_
    conns-resp-≲     : (i : Fin E-size) → (j : Fin (proj₁ (lookup E-outputs (fsuc i)))) →
                       (Fin-pm (proj₁ (conns→ ((fsuc i) , j))) ⊤' (i ≲_))
    conns-resp-≲-neq : (i : Fin E-size) → (j : Fin (proj₁ (lookup E-outputs (fsuc i)))) →
                       (Fin-pm (proj₁ (conns→ ((fsuc i) , j))) ⊤' (i ≢_))
    

record _≋_ {A B : Σ _ (Vec T)} (G H : Hypergraph A B) : Set (ℓₜ ⊔ ℓₜᵣ ⊔ (lsuc ℓₒ)) where
  module G = Hypergraph G
  module H = Hypergraph H
  field
    same-size : G.E-size ≡ H.E-size
    α  : Fin G.E-size → Fin H.E-size
    α' : Fin H.E-size → Fin G.E-size
    
    one-to-one : Inverseᵇ _≡_ _≡_ α α'
    obj-resp : {i : Fin G.E-size} → lookup G.E i ≡ lookup H.E (α i)

  β : Fin (suc G.E-size) → Fin (suc H.E-size)
  β = λ {fzero → fzero ; (fsuc i) → fsuc (α i)}

  γ : (f : ∃₂ Obj → Σ _ (Vec T)) (spl : Σ _ (Vec T)) (i : Fin (suc G.E-size)) → Fin (proj₁ (lookup (spl ∷ (map f G.E)) i)) → Fin (proj₁ (lookup (spl ∷ (map f H.E)) (β i)))
  γ = λ f _ → λ {fzero → id ; (fsuc j) → cast (cong proj₁ (trans
                                                               (trans
                                                                    (lookup-map    j  f G.E)
                                                                    (cong f obj-resp))
                                                               (sym (lookup-map (α j) f H.E))))}

  field
    conns-resp : {ij : G.index-pair G.E-outputs} → H.index-eq H.E-inputs
                                                        (pair-map β (λ {i} → γ proj₁ B i) (G.conns→ ij))
                                                        (H.conns→ (pair-map β (λ {i} → γ (proj₁ ∘ proj₂) A i) ij))

-- _⊚_ : {A B C : Σ _ (Vec T)} → Hypergraph B C → Hypergraph A B → Hypergraph A C
-- _⊚_ {A} {B} {C} BC AB = record
--                                                  { E-size = E-size
--                                                  ; E = E
--                                                  ; conns→ = {!!} --conns→
--                                                  ; conns← = {!!}
--                                                  ; type-match = {!!}
--                                                  ; one-to-one = {!!}
--                                                  }
--                                                  where
--                                                  module AB = Hypergraph AB
--                                                  module BC = Hypergraph BC
--                                                  E-size = AB.E-size + BC.E-size
--                                                  E = AB.E ++ BC.E
--                                                  conns→ : Σ (Fin (suc E-size)) (λ i → Fin (proj₁ (lookup (A ∷ (map (proj₁ ∘ proj₂) E)) i))) → Σ (Fin (suc E-size)) (λ i → Fin (proj₁ (lookup (C ∷ (map proj₁ E)) i)))
--                                                  conns→ (i , j) with splitAt (suc AB.E-size) i
--                                                  conns→ (i , j)    | (inj₁ i') with AB.conns→ (i' , cast {!!} j)
--                                                  conns→ (i , j)    | (inj₁ i')    | (fzero , j') with BC.conns→ (fzero , j')
--                                                  conns→ (i , j)    | (inj₁ i')    | (fzero , j')    | (fzero , j'') = fzero , j''
--                                                  conns→ (i , j)    | (inj₁ i')    | (fzero , j')    | ((fsuc i'') , j'') = (cast (+-suc AB.E-size BC.E-size) (raise AB.E-size (fsuc i''))) , cast {!!} j''
--                                                  conns→ (i , j)    | (inj₁ i')    | ((fsuc i'') , j') = (inject+ BC.E-size (fsuc i'')) , cast {!!} j'
