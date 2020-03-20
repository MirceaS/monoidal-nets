{-# OPTIONS --without-K --safe #-}

open import Level renaming (zero to lzero; suc to lsuc)
open import Data.Unit
open import Data.Unit.Properties using (≡-setoid)
open import Data.Product as Prod using (Σ; _,_; proj₁; proj₂; uncurry)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Vec using (_∷_; [])
open import Relation.Binary using (Rel; Setoid)
open import Relation.Binary.PropositionalEquality

open import Nets.Utils

module Nets.Hierarchical where

open import Nets.Hypergraph ≡-setoid
open Core
open import Nets.Category ≡-setoid

data hierarchical :   (l : ℕ) → (s t : List ⊤) → Set₁
eq :                  (l : ℕ) → (s t : List ⊤) → Rel (hierarchical l s t) (lsuc lzero) -- (G H : hierarchical l s t) → Set₁
hierarchical-setoid : (l : ℕ) → (s t : List ⊤) → Setoid (lsuc lzero) (lsuc lzero)
-- eq-refl :             (l : ℕ) → (s t : List ⊤) → {x : hierarchical l s t} → eq l s t x x
-- eq-sym :              (l : ℕ) → (s t : List ⊤) → {x y : hierarchical l s t} → eq l s t x y → eq l s t y x
-- eq-trans :            (l : ℕ) → (s t : List ⊤) → {x y z : hierarchical l s t} →
--                      eq l s t x y → eq l s t y z → eq l s t x z

data hierarchical where
  lambda : {l : ℕ} → (s : List ⊤) →
           Hypergraph (hierarchical-setoid l) {lzero} ((tt ∷[]) ⊕ s) 1* →
           hierarchical (suc l) s 1*
  app :    {l : ℕ} →
           hierarchical l 2* 1*

{- data eq where
  lambda-eq : {l : ℕ} →
              (H₁ H₂ : Hypergraph (hierarchical-setoid l) {lzero} 2* 1*) →
              _≋_ (hierarchical-setoid l) H₁ H₂ →
              eq (suc l) 1* 1* (lambda H₁) (lambda H₂)
  app-eq :    {l : ℕ} →
              eq l 2* 1* app app -}

eq (suc l) (le , TS) 1* (lambda .(le , TS) H₁) (lambda .(le , TS) H₂) = _≋_ (hierarchical-setoid l) H₁ H₂
eq _ 2* 1* x y = x ≡ y

module HC l = Hypergraph-Category (hierarchical-setoid l) {lzero}

hierarchical-setoid level s t = record
  { Carrier = hierarchical level s t
  ; _≈_ = eq level s t
  ; isEquivalence = record { refl = {!!} ; sym = eq-sym level s t ; trans = {!!} } -- eq-isEquivalence level s t
  }
  where
    eq-sym : (l : ℕ) → (s t : List ⊤) → {x y : hierarchical l s t} → eq l s t x y → eq l s t y x
    eq-sym (suc l) s 1* {lambda .s x} {lambda .s y} = HC.Equiv.sym l
    eq-sym _ 2* 1* {app} {app} eq = eq 

--eq-refl (suc l) s 1* {lambda .s x} = HC.Equiv.refl l
--eq-refl _ 2* 1* {app} = refl

-- eq-sym (suc l) s t {lambda x} {lambda y} (lambda-eq x y x=y) = lambda-eq y x (Hypergraph-Category.Equiv.sym (hierarchical-setoid l) {lzero} x=y)
-- eq-sym l s t {app} {app} _ = app-eq

{- eq-trans (suc l) s t {lambda x} {lambda y} {lambda z} (lambda-eq x y x=y) (lambda-eq y z y=z) =
  lambda-eq x z (HC.Equiv.trans l x=y y=z)
eq-trans l s t {app} {app} {app} _ _ = app-eq -}

    {- eq-isEquivalence : (l : ℕ) → (s t : List ⊤) → IsEquivalence (eq l s t)
    eq-isEquivalence l s t = record
      { refl = eq-refl l s t
      ; sym = eq-sym l s t
      ; trans = eq-trans l s t
      }
    -}
