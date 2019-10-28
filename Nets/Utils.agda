open import Level
open import Agda.Builtin.Sigma
open import Relation.Binary
open import Relation.Unary using (Pred ; _⊆_)
open import Function.Core using (_on_)
open import Data.Maybe
open import Data.List
open import Data.Nat
open import Data.Product using (_×_ ; map₂)

module Nets.Utils where

_P≈_ : {a ℓ₁ ℓ₂ : Level} {A : Set a} → Pred A ℓ₁ → Pred A ℓ₂ → Set _
P P≈ Q = P ⊆ Q × Q ⊆ P

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


-- list_to_TotalOrder : {l₁ l₂ l₃ : Level} → (A : DecSetoid l₁ l₂) → (List (DecSetoid.Carrier A)) → Maybe (Σ (Rel (DecSetoid.Carrier A) l₃) (IsTotalOrder (DecSetoid._≈_ A)))
-- list_to_TotalOrder A [] = just ((λ _ _ → ⊥) , )
--   where
--     open DecSetoid A


