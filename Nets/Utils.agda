open import Level
open import Agda.Builtin.Sigma
open import Relation.Binary
open import Relation.Unary using (Pred ; _⊆_)
open import Function.Core using (_on_)
open import Data.Maybe
open import Data.List
open import Data.Nat hiding (_⊔_)
open import Data.Product using (_×_ ; map₂)
open import Data.Empty

module Nets.Utils where

data ⊥' {l : Level} : Set l where

data ⊤' {l : Level} : Set l where
  tt : ⊤'

_P≈_ : {a ℓ₁ ℓ₂ : Level} {A : Set a} → Pred A ℓ₁ → Pred A ℓ₂ → Set _
P P≈ Q = P ⊆ Q × Q ⊆ P

_−_ : {a l : Level} → (A : Setoid a l) → (x : Setoid.Carrier A) → Set _
A − x = Σ A.Carrier (x ≉_)
  where
    module A = Setoid A
    _≉_ = λ x y → (x A.≈ y) → ⊥

subset-setoid : {ℓ₁ ℓ₂ ℓ₃ : Level} → (A-setoid : Setoid ℓ₁ ℓ₂) → Pred (Setoid.Carrier A-setoid) ℓ₃ → Setoid (ℓ₁ ⊔ ℓ₃) ℓ₂
subset-setoid A-setoid pred = record
  { Carrier = Σ A pred
  ; _≈_ = A._≈_ on fst
  ; isEquivalence = record
    { refl = refl
    ; sym = sym
    ; trans = trans
    }
  }
  where
    module A = Setoid A-setoid
    A = A.Carrier
    open IsEquivalence A.isEquivalence
    

module TOSubsets {a ℓ : Level} (A : Setoid a ℓ) where

  totally_ordered_subsets : {ℓ₁ ℓ₂ : Level} → Set _
  totally_ordered_subsets {ℓ₁} {ℓ₂} = Σ (Pred C ℓ₁) (λ p → Σ (Rel (Σ C p) ℓ₂) (IsTotalOrder (_≡_ on fst)))
    where
      module A = Setoid A
      C = A.Carrier
      _≡_ = A._≈_

  _≋_ : {ℓ₁ ℓ₂ : Level} → Rel (totally_ordered_subsets {ℓ₁} {ℓ₂}) _
  (pred₁ , rel₁ , _) ≋ (pred₂ , rel₂ , _) = Σ (pred₁ P≈ pred₂) (λ {(p , q) → (rel₁ =[ map₂ p ]⇒ rel₂) × (rel₂ =[ map₂ q ]⇒ rel₁)})


  -- _≋_ is equivalence

-- find in list of list gives us a function from A to Nat

record Bij {ℓ₁ ℓ₂ : Level} (A-setoid B-setoid : Setoid ℓ₁ ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  module A = Setoid A-setoid
  A = A.Carrier
  module B = Setoid B-setoid
  B = B.Carrier
  field
    from : A → B
    to : B → A
    conv₁ : ∀ x → to (from x) A.≈ x
    conv₂ : ∀ x → from (to x) B.≈ x

-- list_to_TotalOrder : {l₁ l₂ l₃ : Level} → (A : DecSetoid l₁ l₂) → (List (DecSetoid.Carrier A)) → Maybe (Σ (Rel (DecSetoid.Carrier A) l₃) (IsTotalOrder (DecSetoid._≈_ A)))
-- list_to_TotalOrder A [] = just ((λ _ _ → ⊥) , )
--   where
--     open DecSetoid A


