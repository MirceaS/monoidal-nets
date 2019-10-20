open import Level
open import Agda.Builtin.Sigma
open import Relation.Binary
open import Relation.Unary using (Pred)
open import Data.Maybe
open import Function.Core using (_on_ ; _∘_)

module Nets.Utils where

totally_ordered_subsets : {a ℓ ℓ₁ ℓ₂ : Level} → (Setoid a ℓ) → Set _
totally_ordered_subsets {a} {ℓ} {ℓ₁} {ℓ₂} A = Σ (Pred C ℓ₁) (λ p → Σ (Rel (Σ C p) ℓ₂) (IsTotalOrder (_≡_ on fst)))
  where
    module A = Setoid A
    C = A.Carrier
    _≡_ = A._≈_


data List {l : Level} (A : Set l) : Set (suc l) where
  [] : List A
  a ∷ as : A → List A → List A

-- list_to_TotalOrder : {l₁ l₂ l₃ : Level} → (A : DecSetoid l₁ l₂) → (List (DecSetoid.Carrier A)) → Maybe (Σ (Rel (DecSetoid.Carrier A) l₃) (IsTotalOrder (DecSetoid._≈_ A)))
-- list_to_TotalOrder A [] = just ((λ _ _ → ⊥) , )
--   where
--     open DecSetoid A
