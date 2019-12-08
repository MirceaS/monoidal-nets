open import Level
open import Agda.Builtin.Sigma
open import Agda.Builtin.Equality
open import Data.Product using (_×_ ; ∃)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Fin using (Fin)
open import Data.Fin.Properties renaming (setoid to Fin-setoid)
open import Data.Nat using (ℕ)
open import Data.Empty
open import Data.List
open import Function using (_∘_ ; IsBijection ; _on_ ; id)
open import Relation.Binary

open import Nets.Utils

module Nets.Hypergraph {ℓₜ ℓₜᵣ : Level} (Types-setoid : Setoid ℓₜ ℓₜᵣ) where
open ListOfUniques Types-setoid using () renaming (same-list to _T≈_) public

module T = Setoid Types-setoid
T = T.Carrier

record Hypergraph {ℓₑ ℓ₁ ℓᵥ ℓ₃ ℓ₄ ℓ₅ : Level} : Set (suc (ℓₑ ⊔ ℓ₁ ⊔ ℓᵥ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅ ⊔ ℓₜ ⊔ ℓₜᵣ)) where
  field
    E-setoid : Setoid ℓₑ ℓ₁
    V-setoid : Setoid ℓᵥ ℓ₃

  open ListOfUniques V-setoid public
  
  open Setoid E-setoid public
  E = Carrier
  module V = Setoid V-setoid
  V = V.Carrier

  field
    type : V → T
    
    I : E
    O : E

    s+uniq : E → list-of-uniques
    t+uniq : E → list-of-uniques

  s = fst ∘ s+uniq
  t = fst ∘ t+uniq
  wtns = fst         -- The witness of an existential statement (defined for clarity)
  
  field
    ηₛ :      (v : V) →          ∃ (λ e → v ∈ (s e))
    ηₜ :      (v : V) →          ∃ (λ e → v ∈ (t e))
    -- Properties
    ηₛ-uniq : (v : V) → (e-con : ∃ (λ e → v ∈ (s e))) → (wtns e-con) ≈ (wtns (ηₛ v))
    ηₜ-uniq : (v : V) → (e-con : ∃ (λ e → v ∈ (t e))) → (wtns (ηₜ v) ≈ (wtns e-con))
    ηₛ-resp : V._≈_ =[ wtns ∘ ηₛ ]⇒ _≈_
    ηₜ-resp : V._≈_ =[ wtns ∘ ηₜ ]⇒ _≈_
    s-resp : _≈_ =[ s+uniq ]⇒ _≋_
    t-resp : _≈_ =[ t+uniq ]⇒ _≋_


record IsDirectedHypergraph (hg : Hypergraph) (IT : List T) (OT : List T) : Set _ where
  open Hypergraph hg hiding (reflexive) public
  field
    input-match :   IT T≈ (map type (t I))
    output-match :  (map type (s O)) T≈ OT

    partial-order : Σ (Rel E _) (IsPartialOrder _≈_)

  _≤_ = fst partial-order
  open IsPartialOrder (snd partial-order) hiding (refl) public

  field
    I-min : Minimum _≤_ I
    O-max : Maximum _≤_ O
    
    γ :   (v : V) → wtns (ηₜ v) ≤ wtns (ηₛ v)
    γ-≉ : (v : V) → wtns (ηₜ v) ≉ wtns (ηₛ v)

  lemma1ᵢ : ∀ v → v ∉ s I
  lemma1ᵢ v p = γ-≉ v ηₜv=ηₛv
    where
      ηₜv : E
      ηₜv = wtns (ηₜ v)
      ηₛv : E
      ηₛv = wtns (ηₛ v)
      ηₜv≤ηₛv : ηₜv ≤ ηₛv
      ηₜv≤ηₛv = γ v
      I=ηₛv : I ≈ ηₛv
      I=ηₛv = ηₛ-uniq v (I , p)
      ηₜv≤I : ηₜv ≤ I
      ηₜv≤I = ≤-respʳ-≈ (Eq.sym I=ηₛv) ηₜv≤ηₛv
      I≤ηₜv : I ≤ ηₜv
      I≤ηₜv = I-min ηₜv
      ηₜv=I : ηₜv ≈ I
      ηₜv=I = antisym ηₜv≤I I≤ηₜv
      ηₜv=ηₛv : ηₜv ≈ ηₛv
      ηₜv=ηₛv = Eq.trans ηₜv=I I=ηₛv
    
  
  lemma1ₒ : ∀ v → v ∉ t O
  lemma1ₒ v p = γ-≉ v ηₜv=ηₛv
    where
      ηₜv : E
      ηₜv = wtns (ηₜ v)
      ηₛv : E
      ηₛv = wtns (ηₛ v)
      ηₜv≤ηₛv : ηₜv ≤ ηₛv
      ηₜv≤ηₛv = γ v
      ηₜv=O : ηₜv ≈ O
      ηₜv=O = ηₜ-uniq v (O , p)
      O≤ηₛv : O ≤ ηₛv
      O≤ηₛv = ≤-respˡ-≈ ηₜv=O ηₜv≤ηₛv
      ηₛv≤O : ηₛv ≤ O
      ηₛv≤O = O-max ηₛv
      O=ηₛv : O ≈ ηₛv
      O=ηₛv = antisym O≤ηₛv ηₛv≤O
      ηₜv=ηₛv : ηₜv ≈ ηₛv
      ηₜv=ηₛv = Eq.trans ηₜv=O O=ηₛv


DirectedHypergraph = Σ Hypergraph IsDirectedHypergraph

    {-   --finiteness
    V-size : ℕ
    E-size : ℕ
    V-fin : V → Fin V-size
    E-fin : E → Fin E-size
    V-fin-bij : IsBijection V._≈_ _≡_ V-fin
    E-fin-bij : IsBijection E._≈_ _≡_ E-fin
    V-fin-resp : V._≈_ =[ V-fin ]⇒ _≡_
    E-fin-resp : E._≈_ =[ E-fin ]⇒ _≡_
    -}


{-
bij-type : ∀ {ℓₑ ℓ₁ ℓ₂ ℓᵥ ℓ₃ ℓ₄ ℓ₅} → (A B : DirectedHypergraph ℓₑ ℓ₁ ℓ₂ ℓᵥ ℓ₃ ℓ₄ ℓ₅) → Set (ℓₜᵣ ⊔ ℓᵥ ⊔ ℓ₃ ⊔ ℓ₄)
bij-type A B = Σ (Bij (subset-setoid A.V-setoid (fst (A.t A.O))) (subset-setoid B.V-setoid (fst (B.s B.I)))) (λ bij → (∀ x → (A.type (fst x)) T.≈ (B.type (fst (Bij.from bij x)))))
  where
    module A = DirectedHypergraph A
    module B = DirectedHypergraph B -}

-- (A.E-setoid − A.O) ⊎ (B.E-setoid − B.I)
comp : {X Y Z : List T} → DirectedHypergraph Y Z → DirectedHypergraph X Y → DirectedHypergraph X Z
comp A B (bij , types-match) = ?
                                 where
                                 module A = IsDirectedHypergraph (snd A)
                                 module B = IsDirectedHypergraph (snd B)
                                 _E-≈_ : Rel ((A.E-setoid − A.O) ⊎ (B.E-setoid − B.I)) _
                                 (inj₁ (x , _)) E-≈ (inj₁ (y , _)) = x A.≈ y
                                 (inj₂ (x , _)) E-≈ (inj₂ (y , _)) = x B.≈ y
                                 (inj₁ (x , _)) E-≈ (inj₂ (y , _)) = ⊥'
                                 (inj₂ (x , _)) E-≈ (inj₁ (y , _)) = ⊥'
                                 _E-≤_ : Rel ((A.E-setoid − A.O) ⊎ (B.E-setoid − B.I)) _
                                 (inj₁ (x , _)) E-≤ (inj₁ (y , _)) = x A.≤ y
                                 (inj₂ (x , _)) E-≤ (inj₂ (y , _)) = x B.≤ y
                                 (inj₁ (x , _)) E-≤ (inj₂ (y , _)) = ⊤'
                                 (inj₂ (x , _)) E-≤ (inj₁ (y , _)) = ⊥'
                                 antisym : Antisymmetric _E-≈_ _E-≤_
                                 antisym {inj₁ _} {inj₁ _} = A.antisym
                                 antisym {inj₂ _} {inj₂ _} = B.antisym
                                 antisym {inj₁ _} {inj₂ _} _ ()
                                 antisym {inj₂ _} {inj₁ _} ()
                                 reflexive : _E-≈_ ⇒ _E-≤_
                                 reflexive {inj₁ _} {inj₁ _} = A.reflexive
                                 reflexive {inj₂ _} {inj₂ _} = B.reflexive
                                 reflexive {inj₁ _} {inj₂ _} ()
                                 reflexive {inj₂ _} {inj₁ _} ()
                                 trans : Transitive _E-≤_
                                 trans {inj₁ _} {inj₁ _} {inj₁ _} = A.trans
                                 trans {inj₂ _} {inj₂ _} {inj₂ _} = B.trans
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
