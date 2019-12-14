open import Level renaming (zero to lzero ; suc to lsuc)
open import Agda.Builtin.Equality
open import Data.Product using (Σ ; _,_ ; ∃₂ ; proj₁ ; proj₂ ; map₁ ; map₂) renaming (map to pair-map)
open import Data.Sum hiding (map ; map₁ ; map₂)
open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties using (+-suc)
open import Data.Vec hiding (splitAt) renaming (lookup to _at_)
open import Data.Vec.Properties using (lookup-map)
open import Data.Fin renaming (zero to fzero ; suc to fsuc ; _+_ to _+f_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Function using (_∘_ ; Inverseᵇ ; id)

module Nets.Hypergraph {ℓₜ ℓₜᵣ : Level} (Types-setoid : Setoid ℓₜ ℓₜᵣ) {ℓₒ : Level} (Obj : Σ _ (Vec (Setoid.Carrier Types-setoid)) → Σ _ (Vec (Setoid.Carrier Types-setoid)) → Set ℓₒ) where

module T = Setoid Types-setoid
T = T.Carrier

------some technical utilities------
data ⊤' {l : Level} : Set l where
  tt : ⊤'

_⟩⟨_ = cong
infix 0 ⟩⟨

Fin-pm : {ℓ₁ : Level} {n : ℕ} → Fin (suc n) → (A : Set ℓ₁) → (B : Fin n → Set ℓ₁) → Set ℓ₁
Fin-pm fzero A _ = A
Fin-pm (fsuc i) _ B = B i

splitAt-lemma : ∀ {l} {X : Set l} (na nb : ℕ) (A : Vec X na) (B : Vec X nb) (i : Fin (na + nb)) →
                [ (λ i₁ → (A ++ B) at i ≡ A at i₁) , (λ i₂ → (A ++ B) at i ≡ B at i₂) ]′ (splitAt na i)
splitAt-lemma zero     nb []      B i = refl
splitAt-lemma (suc na) nb (_ ∷ A) B fzero = refl
splitAt-lemma (suc na) nb (_ ∷ A) B (fsuc i) with splitAt na i | inspect (splitAt na) i
splitAt-lemma (suc na) nb (_ ∷ A) B (fsuc i)    | inj₁ i₁      | [ split=i₁ ] = subst id (cong [ _ , _ ]′ split=i₁) (splitAt-lemma na nb A B i)
splitAt-lemma (suc na) nb (_ ∷ A) B (fsuc i)    | inj₂ i₂      | [ split=i₂ ] = subst id (cong [ _ , _ ]′ split=i₂) (splitAt-lemma na nb A B i)

map-++-commute : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) {n m : ℕ} (xs : Vec A n) (ys : Vec A m) →
                 map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++-commute f []       ys = refl
map-++-commute f (x ∷ xs) ys =
  cong ((f x) ∷_) (map-++-commute f xs ys)
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
  index-pair v = Σ (Fin (suc E-size)) (λ i → Fin (proj₁ (v at i)))

  index-eq : (v : Vec-of-Vecs) → Rel (index-pair v) lzero
  index-eq v = λ {(i , j) (i' , j') → Σ (i ≡ i') (λ {refl → j ≡ j'})}
  
  lookup² : (v : Vec-of-Vecs) → index-pair v → T
  lookup² v = λ {(i , j) → (proj₂ (v at i)) at j}
  
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
    conns-resp-≲     : (i : Fin E-size) → (j : Fin (proj₁ (E-outputs at (fsuc i)))) →
                       (Fin-pm (proj₁ (conns→ ((fsuc i) , j))) ⊤' (i ≲_))
    conns-resp-≲-neq : (i : Fin E-size) → (j : Fin (proj₁ (E-outputs at (fsuc i)))) →
                       (Fin-pm (proj₁ (conns→ ((fsuc i) , j))) ⊤' (i ≢_))


record _≋_ {A B : Σ _ (Vec T)} (G H : Hypergraph A B) : Set (ℓₜ ⊔ ℓₜᵣ ⊔ (lsuc ℓₒ)) where
  module G = Hypergraph G
  module H = Hypergraph H
  field
    same-size : G.E-size ≡ H.E-size
    α  : Fin G.E-size → Fin H.E-size
    α' : Fin H.E-size → Fin G.E-size
    
    one-to-one : Inverseᵇ _≡_ _≡_ α α'
    obj-resp : {i : Fin G.E-size} → G.E at i ≡ H.E at (α i)

  β : Fin (suc G.E-size) → Fin (suc H.E-size)
  β = λ {fzero → fzero ; (fsuc i) → fsuc (α i)}

  γ : (f : ∃₂ Obj → Σ _ (Vec T)) (spl : Σ _ (Vec T)) (i : Fin (suc G.E-size)) → Fin (proj₁ ((spl ∷ (map f G.E)) at i)) → Fin (proj₁ ((spl ∷ (map f H.E)) at (β i)))
  γ = λ f _ → λ {fzero → id ; (fsuc j) → cast (cong proj₁ (trans
                                                               (trans
                                                                    (lookup-map    j  f G.E)
                                                                    (cong f obj-resp))
                                                               (sym (lookup-map (α j) f H.E))))}

  field
    conns-resp : {ij : G.index-pair G.E-outputs} → H.index-eq H.E-inputs
                                                        (pair-map β (λ {i} → γ proj₁ B i) (G.conns→ ij))
                                                        (H.conns→ (pair-map β (λ {i} → γ (proj₁ ∘ proj₂) A i) ij))

_⊚_ : {A B C : Σ _ (Vec T)} → Hypergraph B C → Hypergraph A B → Hypergraph A C
_⊚_ {A} {B} {C} BC AB = record
                                                 { E-size = E-size
                                                 ; E = E
                                                 ; conns→ = {!!} --conns→
                                                 ; conns← = {!!}
                                                 ; type-match = {!!}
                                                 ; one-to-one = {!!}
                                                 }
                                                 where
                                                 module AB = Hypergraph AB
                                                 module BC = Hypergraph BC
                                                 E-size = AB.E-size + BC.E-size
                                                 E = AB.E ++ BC.E
                                                 {-open ≡-Reasoning
                                                 conns→ : Σ (Fin (suc E-size)) (λ i → Fin (proj₁ ((A ∷ (map (proj₁ ∘ proj₂) E)) at i))) → Σ (Fin (suc E-size)) (λ i → Fin (proj₁ ((C ∷ (map proj₁ E)) at i)))
                                                 conns→ (i , j) with splitAt (suc AB.E-size) i
                                                 conns→ (i , j)    | inj₁ i' with AB.conns→ (i' , cast (begin
                                                     _ ≡⟨ cong (proj₁ ∘ (_at i) ∘ (A ∷_)) (map-++-commute _ AB.E BC.E) ⟩
                                                     _ ≡⟨ cong proj₁ (splitAt-lemma _ _ (A ∷ (map (proj₁ ∘ proj₂) AB.E)) (map (proj₁ ∘ proj₂) BC.E) i) ⟩
                                                     _ ∎
                                                   ) j)
                                                 conns→ (i , j)    | inj₁ i'    | fzero , j' with BC.conns→ (fzero , j')
                                                 conns→ (i , j)    | inj₁ i'    | fzero , j'    | fzero , j'' = fzero , j''
                                                 conns→ (i , j)    | inj₁ i'    | fzero , j'    | (fsuc i'') , j'' = (cast (+-suc AB.E-size BC.E-size) (raise AB.E-size (fsuc i''))) , cast {!!} j''
                                                 conns→ (i , j)    | inj₁ i'    | (fsuc i'') , j' = (inject+ BC.E-size (fsuc i'')) , cast {!!} j' -}
