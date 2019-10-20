open import Level
open import Agda.Builtin.Sigma
open import Data.Product using (_×_)
open import Function.Core using (_∘_)
open import Relation.Binary
open import Data.Empty

open import Nets.Utils

module Nets.Hypergraph where


record Hypergraph (ℓₑ ℓ₁ ℓ₂ ℓᵥ ℓ₃ ℓ₄ ℓ₅ : Level) : Set (suc (ℓₑ ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓᵥ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅)) where
  field
    E-poset : Poset ℓₑ ℓ₁ ℓ₂
    V-setoid : Setoid ℓᵥ ℓ₃

  module E = Poset E-poset
  E = E.Carrier
  module V = Setoid V-setoid
  V = V.Carrier

  field
    -- we omit the constraint on E and V to be finite for now as working with
    -- finite types in Agda is a huge hassle and I don't feel like having
    -- them finite would add enough value to this formalisation to be worth it
    s : E → totally_ordered_subsets {_} {_} {ℓ₄} {ℓ₅} V-setoid
    t : E → totally_ordered_subsets {_} {_} {ℓ₄} {ℓ₅} V-setoid
    -- missing: s and t respect edge equality
    -- ^ turns out to be very difficult to write down as there is no simple
    -- notion of equality of Total Orders.
    -- On that note, should we make the equality on E propositional?
    
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

  _∈_ : (v : V) → totally_ordered_subsets {_} {_} {ℓ₄} {ℓ₅} V-setoid → Set _
  v ∈ s = fst s v

  _∉_ : (v : V) → totally_ordered_subsets {_} {_} {ℓ₄} {ℓ₅} V-setoid → Set _
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
      
      
