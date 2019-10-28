open import Level
open import Agda.Builtin.Sigma
open import Agda.Builtin.Equality
open import Data.Product using (_×_ ; map)
open import Data.Fin using (Fin)
open import Data.Fin.Properties renaming (setoid to Fin-setoid)
open import Data.Nat using (ℕ)
open import Data.Empty
open import Function using (_∘_ ; IsBijection ; _on_ ; id)
open import Relation.Binary

open import Nets.Utils

module Nets.Hypergraph where


record Hypergraph (ℓₑ ℓ₁ ℓ₂ ℓᵥ ℓ₃ ℓ₄ ℓ₅ : Level) : Set (suc (ℓₑ ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓᵥ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅)) where
  field
    E-poset : Poset ℓₑ ℓ₁ ℓ₂
    V-setoid : Setoid ℓᵥ ℓ₃

  open TOSubsets V-setoid
  module E = Poset E-poset
  E = E.Carrier
  module V = Setoid V-setoid
  V = V.Carrier

  field
    V-size : ℕ
    E-size : ℕ
    V-fin : V → Fin V-size
    E-fin : E → Fin E-size
    V-fin-bij : IsBijection V._≈_ _≡_ V-fin
    E-fin-bij : IsBijection E._≈_ _≡_ E-fin
    V-fin-resp : V._≈_ =[ V-fin ]⇒ _≡_
    E-fin-resp : E._≈_ =[ E-fin ]⇒ _≡_

    s : E → totally_ordered_subsets {ℓ₄} {ℓ₅}
    t : E → totally_ordered_subsets {ℓ₄} {ℓ₅}
    s-resp : E._≈_ =[ s ]⇒ _≋_
    t-resp : E._≈_ =[ t ]⇒ _≋_
    
    I : E
    O : E
    I-min : Minimum E._≤_ I
    O-max : Maximum E._≤_ O
    
    ηᵢ :      (v : V) →          Σ E (λ e → fst (s e) v)
    ηᵢ-uniq : (v : V) → (e-con : Σ E (λ e → fst (s e) v)) → (fst e-con) E.≈ (fst (ηᵢ v))
    ηᵢ-resp : V._≈_ =[ fst ∘ ηᵢ ]⇒ E._≈_
    
    ηₒ :      (v : V) →          Σ E (λ e → fst (t e) v)
    ηₒ-uniq : (v : V) → (e-con : Σ E (λ e → fst (t e) v)) → (fst (ηₒ v) E.≈ (fst e-con))
    ηₒ-resp : V._≈_ =[ fst ∘ ηₒ ]⇒ E._≈_
    
    γ :   (v : V) → fst (ηₒ v) E.≤ fst (ηᵢ v)
    γ-≉ : (v : V) → fst (ηₒ v) E.≈ fst (ηᵢ v) → ⊥

  _∈_ : (v : V) → totally_ordered_subsets {ℓ₄} {ℓ₅} → Set _
  v ∈ s = fst s v

  _∉_ : (v : V) → totally_ordered_subsets {ℓ₄} {ℓ₅} → Set _
  v ∉ s = (v ∈ s) → ⊥

  lemma1ᵢ : ∀ v → v ∉ s I
  lemma1ᵢ v p = γ-≉ v ηₒv=ηᵢv
    where
      ηₒv : E
      ηₒv = fst (ηₒ v)
      ηᵢv : E
      ηᵢv = fst (ηᵢ v)
      ηₒv≤ηᵢv : ηₒv E.≤ ηᵢv
      ηₒv≤ηᵢv = γ v
      I=ηᵢv : I E.≈ ηᵢv
      I=ηᵢv = ηᵢ-uniq v (I , p)
      ηₒv≤I : ηₒv E.≤ I
      ηₒv≤I = E.≤-respʳ-≈ (E.Eq.sym I=ηᵢv) ηₒv≤ηᵢv
      I≤ηₒv : I E.≤ ηₒv
      I≤ηₒv = I-min ηₒv
      ηₒv=I : ηₒv E.≈ I
      ηₒv=I = E.antisym ηₒv≤I I≤ηₒv
      ηₒv=ηᵢv : ηₒv E.≈ ηᵢv
      ηₒv=ηᵢv = E.Eq.trans ηₒv=I I=ηᵢv
    
  
  lemma1ₒ : ∀ v → v ∉ t O
  lemma1ₒ v p = γ-≉ v ηₒv=ηᵢv
    where
      ηₒv : E
      ηₒv = fst (ηₒ v)
      ηᵢv : E
      ηᵢv = fst (ηᵢ v)
      ηₒv≤ηᵢv : ηₒv E.≤ ηᵢv
      ηₒv≤ηᵢv = γ v
      ηₒv=O : ηₒv E.≈ O
      ηₒv=O = ηₒ-uniq v (O , p)
      O≤ηᵢv : O E.≤ ηᵢv
      O≤ηᵢv = E.≤-respˡ-≈ ηₒv=O ηₒv≤ηᵢv
      ηᵢv≤O : ηᵢv E.≤ O
      ηᵢv≤O = O-max ηᵢv
      O=ηᵢv : O E.≈ ηᵢv
      O=ηᵢv = E.antisym O≤ηᵢv ηᵢv≤O
      ηₒv=ηᵢv : ηₒv E.≈ ηᵢv
      ηₒv=ηᵢv = E.Eq.trans ηₒv=O O=ηᵢv

record HypergraphMorphism (ℓₑ ℓ₁ ℓ₂ ℓᵥ ℓ₃ ℓ₄ ℓ₅ ℓₑ' ℓ₁' ℓ₂' ℓᵥ' ℓ₃' ℓ₄' ℓ₅' : Level) (A : Hypergraph ℓₑ ℓ₁ ℓ₂ ℓᵥ ℓ₃ ℓ₄ ℓ₅) (B : Hypergraph ℓₑ' ℓ₁' ℓ₂' ℓᵥ' ℓ₃' ℓ₄' ℓ₅') : Set (ℓₑ ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓᵥ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅ ⊔ ℓₑ' ⊔ ℓ₁' ⊔ ℓ₂' ⊔ ℓᵥ' ⊔ ℓ₃' ⊔ ℓ₄' ⊔ ℓ₅') where
  module A = Hypergraph A
  module B = Hypergraph B
  module A-tos = TOSubsets A.V-setoid
  module B-tos = TOSubsets B.V-setoid
  field
    V-hom : A.V → B.V
    E-hom : A.E → B.E
  
  -- map_totally_ordered_subsets : ∀ {b1 b2 a1 a2} → B-tos.totally_ordered_subsets {b1} {b2} → A-tos.totally_ordered_subsets {a1} {a2}
  -- map_totally_ordered_subsets (pred , rel , total) = (pred ∘ V-hom , rel on (map V-hom id) , ?)

  -- field
  --   s-coherence : ∀ {e} → (B.s E-hom e) () 
