{-# OPTIONS --without-K --safe #-}

open import Level renaming (zero to lzero; suc to lsuc)
open import Data.Unit
open import Data.Product using (Σ; _,_; proj₁; proj₂; zip)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Fin renaming (zero to fzero; suc to fsuc; _+_ to _f+_)
open import Data.Vec using (Vec; _++_; []; _∷_; replicate)
open import Relation.Binary.PropositionalEquality
open import Function using (id ; _∘_)

module Nets.Utils where

-- convinient way to represent lists as Vectors along with their size
List : ∀ {l} → Set l → Set l
List A = Σ ℕ (Vec A)

len         = proj₁
vec-of-list = proj₂

-- the singleton list
_∷[] : ∀ {l} {A : Set l} → A → List A
a ∷[] = suc zero , a ∷ []

-- converter from natural numbers to lists of units
_* : ℕ → List ⊤
n * = n , replicate tt

0* = 0 *
1* = 1 *
2* = 2 *
3* = 3 *
4* = 4 *

-- general utilities
Σ₂ : ∀ {a} {b} {c} (A : Set a) (B : Set b)
     (C : A → B → Set c) → Set (a ⊔ b ⊔ c)
Σ₂ A B C = Σ A λ a → Σ B λ b → C a b


-- list concatenation
_⊕_ : ∀ {l} {A : Set l} → (xs ys : List A) → List A
_⊕_ = zip _+_ _++_


-- some properties of list concatenation
⊕-identityʳ : ∀ {a} {A : Set a} (X : List A) → X ⊕ (zero , []) ≡ X
⊕-identityʳ (zero , []) = refl
⊕-identityʳ ((suc n) , (x ∷ xs)) = cong ((suc zero , x ∷ []) ⊕_) (⊕-identityʳ (n , xs))

⊕-assoc : ∀ {a} {A : Set a} (X Y Z : List A) → ((X ⊕ Y) ⊕ Z) ≡ (X ⊕ (Y ⊕ Z))
⊕-assoc (zero , []) Y Z = refl
⊕-assoc ((suc n) , (x ∷ xs)) Y Z = cong ((suc zero , x ∷ []) ⊕_) (⊕-assoc (n , xs) Y Z)


-- some other useful properties
fsuc-subst : ∀ {l} {A : Set l} {a b : List A} (eq : a ≡ b) x {a′} →
             fsuc (subst (Fin ∘ len) eq x) ≡ subst (Fin ∘ len) (cong ((suc zero , a′) ⊕_) eq) (fsuc x)
fsuc-subst refl x = refl

0-subst : ∀ {l} {A : Set l} {a b : List A} (eq : a ≡ b) {a′} →
          fzero ≡ subst (Fin ∘ len) (cong ((suc zero , a′) ⊕_) eq) fzero
0-subst refl = refl
