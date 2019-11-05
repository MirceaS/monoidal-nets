open import Level
open import Agda.Builtin.Sigma
open import Agda.Builtin.Equality
open import Data.Product using (_×_ ; map)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Fin using (Fin)
open import Data.Fin.Properties renaming (setoid to Fin-setoid)
open import Data.Nat using (ℕ)
open import Data.Empty
open import Function using (_∘_ ; IsBijection ; _on_ ; id)
open import Relation.Binary

open import Nets.Utils

module Nets.Hypergraph {ℓₜ ℓₜᵣ : Level} (Types-setoid : Setoid ℓₜ ℓₜᵣ) where

module T = Setoid Types-setoid
T = T.Carrier

record Hypergraph (ℓₑ ℓ₁ ℓ₂ ℓᵥ ℓ₃ ℓ₄ ℓ₅ : Level) : Set (suc (ℓₑ ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓᵥ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅ ⊔ ℓₜ ⊔ ℓₜᵣ)) where
  field
    E-poset : Poset ℓₑ ℓ₁ ℓ₂
    V-setoid : Setoid ℓᵥ ℓ₃

  open TOSubsets V-setoid
  module E = Poset E-poset
  E = E.Carrier
  module V = Setoid V-setoid
  V = V.Carrier

  field
    {-
    V-size : ℕ
    E-size : ℕ
    V-fin : V → Fin V-size
    E-fin : E → Fin E-size
    V-fin-bij : IsBijection V._≈_ _≡_ V-fin
    E-fin-bij : IsBijection E._≈_ _≡_ E-fin
    V-fin-resp : V._≈_ =[ V-fin ]⇒ _≡_
    E-fin-resp : E._≈_ =[ E-fin ]⇒ _≡_
    -}

    type : V → T

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

  E-setoid : Setoid ℓₑ ℓ₁
  E-setoid = record { Carrier = E ; _≈_ = E._≈_ ; isEquivalence = E.isEquivalence }

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

bij-type : ∀ {ℓₑ ℓ₁ ℓ₂ ℓᵥ ℓ₃ ℓ₄ ℓ₅} → (A B : Hypergraph ℓₑ ℓ₁ ℓ₂ ℓᵥ ℓ₃ ℓ₄ ℓ₅) → Set (ℓₜᵣ ⊔ ℓᵥ ⊔ ℓ₃ ⊔ ℓ₄)
bij-type A B = Σ (Bij (subset-setoid A.V-setoid (fst (A.t A.O))) (subset-setoid B.V-setoid (fst (B.s B.I)))) (λ bij → (∀ x → (A.type (fst x)) T.≈ (B.type (fst (Bij.from bij x)))))
  where
    module A = Hypergraph A
    module B = Hypergraph B

comp : ∀ {ℓₑ ℓ₁ ℓ₂ ℓᵥ ℓ₃ ℓ₄ ℓ₅} → (A B : Hypergraph ℓₑ ℓ₁ ℓ₂ ℓᵥ ℓ₃ ℓ₄ ℓ₅) → bij-type A B → Hypergraph _ _ _ _ _ _ _
comp A B (bij , types-match) = record
                                 { E-poset = record { Carrier = (A.E-setoid − A.O) ⊎ (B.E-setoid − B.I) ; _≈_ = _E-≈_ ; _≤_ = _E-≤_ ; isPartialOrder = record { isPreorder = record { isEquivalence = {!!} ; reflexive = reflexive ; trans = trans } ; antisym = antisym } }
                                 ; V-setoid = {!!}
                                 ; type = {!!}
                                 ; s = {!!}
                                 ; t = {!!}
                                 ; s-resp = {!!}
                                 ; t-resp = {!!}
                                 ; I = {!!}
                                 ; O = {!!}
                                 ; I-min = {!!}
                                 ; O-max = {!!}
                                 ; ηᵢ = {!!}
                                 ; ηᵢ-uniq = {!!}
                                 ; ηᵢ-resp = {!!}
                                 ; ηₒ = {!!}
                                 ; ηₒ-uniq = {!!}
                                 ; ηₒ-resp = {!!}
                                 ; γ = {!!}
                                 ; γ-≉ = {!!}
                                 }
                                 where
                                 module A = Hypergraph A
                                 module B = Hypergraph B
                                 _E-≈_ : Rel ((A.E-setoid − A.O) ⊎ (B.E-setoid − B.I)) _
                                 (inj₁ (x , _)) E-≈ (inj₁ (y , _)) = x A.E.≈ y
                                 (inj₂ (x , _)) E-≈ (inj₂ (y , _)) = x B.E.≈ y
                                 (inj₁ (x , _)) E-≈ (inj₂ (y , _)) = ⊥'
                                 (inj₂ (x , _)) E-≈ (inj₁ (y , _)) = ⊥'
                                 _E-≤_ : Rel ((A.E-setoid − A.O) ⊎ (B.E-setoid − B.I)) _
                                 (inj₁ (x , _)) E-≤ (inj₁ (y , _)) = x A.E.≤ y
                                 (inj₂ (x , _)) E-≤ (inj₂ (y , _)) = x B.E.≤ y
                                 (inj₁ (x , _)) E-≤ (inj₂ (y , _)) = ⊤'
                                 (inj₂ (x , _)) E-≤ (inj₁ (y , _)) = ⊥'
                                 antisym : Antisymmetric _E-≈_ _E-≤_
                                 antisym {inj₁ _} {inj₁ _} = A.E.antisym
                                 antisym {inj₂ _} {inj₂ _} = B.E.antisym
                                 antisym {inj₁ _} {inj₂ _} _ ()
                                 antisym {inj₂ _} {inj₁ _} ()
                                 reflexive : _E-≈_ ⇒ _E-≤_
                                 reflexive {inj₁ _} {inj₁ _} = A.E.reflexive
                                 reflexive {inj₂ _} {inj₂ _} = B.E.reflexive
                                 reflexive {inj₁ _} {inj₂ _} ()
                                 reflexive {inj₂ _} {inj₁ _} ()
                                 trans : Transitive _E-≤_
                                 trans {inj₁ _} {inj₁ _} {inj₁ _} = A.E.trans
                                 trans {inj₂ _} {inj₂ _} {inj₂ _} = B.E.trans
                                 trans {inj₁ _} {_} {inj₂ _} _ _ = tt
                                 trans {_} {inj₂ _} {inj₁ _} _ ()
                                 trans {inj₂ _} {inj₁ _} ()
                                 
                                 
                                 
                                 
                                 
                                 
                                 

{-
record HypergraphMorphism (ℓₑ ℓ₁ ℓ₂ ℓᵥ ℓ₃ ℓ₄ ℓ₅ ℓₑ' ℓ₁' ℓ₂' ℓᵥ' ℓ₃' ℓ₄' ℓ₅' : Level) (A : Hypergraph ℓₑ ℓ₁ ℓ₂ ℓᵥ ℓ₃ ℓ₄ ℓ₅) (B : Hypergraph ℓₑ' ℓ₁' ℓ₂' ℓᵥ' ℓ₃' ℓ₄' ℓ₅') : Set (ℓₑ ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓᵥ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅ ⊔ ℓₑ' ⊔ ℓ₁' ⊔ ℓ₂' ⊔ ℓᵥ' ⊔ ℓ₃' ⊔ ℓ₄' ⊔ ℓ₅') where
  module A = Hypergraph A
  module B = Hypergraph B
  module A-tos = TOSubsets A.V-setoid
  module B-tos = TOSubsets B.V-setoid
  field
    V-hom : A.V → B.V
    E-hom : A.E → B.E
  
  map_totally_ordered_subsets : ∀ {l1 l2} → B-tos.totally_ordered_subsets {l1} {l2} → A-tos.totally_ordered_subsets {l1} {l2}
  map_totally_ordered_subsets (pred , rel , totalOrd) = (pred ∘ V-hom , (rel on V-hom-pair) , record
    { isPartialOrder = record
      { isPreorder = {!!}
      ; antisym = λ {x} {y} → antisym {map V-hom id x} {map V-hom id y}
      }
    ; total = λ x y → total (V-hom-pair x) (V-hom-pair y)
    })
    where
      V-hom-pair : Σ A.V (pred ∘ V-hom) → Σ B.V pred
      V-hom-pair = map V-hom id
      open IsTotalOrder totalOrd
      -- antisym' : ∀ {i j} → rel (V-hom-pair i) (V-hom-pair j) → rel (V-hom-pair j) (V-hom-pair i) → _
      

  -- field
  --   s-coherence : ∀ {e} → (B.s E-hom e) () 
-}
