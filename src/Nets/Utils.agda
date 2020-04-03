{-# OPTIONS --without-K --safe #-}

open import Level renaming (zero to lzero; suc to lsuc)
open import Data.Unit
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_; zip)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Fin renaming (zero to fzero; suc to fsuc; _+_ to _f+_)
open import Data.Fin.Properties using (inject+-raise-splitAt)
open import Data.Vec using (Vec; []; _∷_; _++_; lookup; replicate)
open import Data.Sum using (inj₁; inj₂; [_,_]′; map; map₁; map₂)
open import Data.Sum.Properties
open import Relation.Binary.PropositionalEquality
open import Relation.Binary using (Rel)
open import Function using (id ; _∘_)

module Nets.Utils where

-- general utilities
Σ₂ : ∀ {a b c} (A : Set a) (B : Set b)
     (C : A → B → Set c) → Set (a ⊔ b ⊔ c)
Σ₂ A B C = Σ A λ a → Σ B λ b → C a b

-- convinient way to represent lists as Vectors along with their size
List : ∀ {l} → Set l → Set l
List A = Σ ℕ (Vec A)

len         = proj₁
vec-of-list = proj₂

module _ {l lₛ lₜ} {S : Set lₛ} {T : Set lₜ} {E : S → T → Set l} where
  -- selectors for the source and target of abstract Edges
  s : Σ₂ S T E → S
  s = proj₁

  t : Σ₂ S T E → T
  t = proj₁ ∘ proj₂

  ! : ∀ {s t} → E s t → Σ₂ S T E
  ! {s = s} {t} e = s , t , e

  E′ : List (Σ₂ S T E) → S → T → Set (lₛ ⊔ lₜ)
  E′ list s′ t′ = Σ (Fin (len list)) (λ i → (s (lu i) ≡ s′) × (t (lu i) ≡ t′))
    where lu = lookup (vec-of-list list)

  label′ : (list : List (Σ₂ S T E)) → ∀ {s t} → E′ list s t → E s t
  label′ list {s} {t} (i , refl , refl) = proj₂ (proj₂ (lookup (vec-of-list list) i))

  module patterns where
    pattern box e i = (inj₂ ((_ , _ , (e , refl , refl)) , i))
    pattern inp i = inj₁ i
    pattern oup i = inj₁ i

unit : ∀ {l} {A : Set l} → List A
unit = zero , []

infixr 3 _::_

_::_ : ∀ {l} {A : Set l} → A → List A → List A
a :: (l , as) = suc l , a ∷ as

-- the singleton list
_::[] : ∀ {l} {A : Set l} → A → List A
a ::[] = a :: unit

inject::[] : ∀ {a} {A : Set a} {x y : A} → x ::[] ≡ y ::[] → x ≡ y
inject::[] refl = refl

-- converter from natural numbers to lists of units
_* : ℕ → List ⊤
n * = n , replicate tt

0* = 0 *
1* = 1 *
2* = 2 *
3* = 3 *
4* = 4 *

-- list concatenation
infixr 10 _⊕_

_⊕_ : ∀ {l} {A : Set l} → (xs ys : List A) → List A
_⊕_ = zip _+_ _++_

-- some properties of list concatenation
⊕-identityʳ : ∀ {a} {A : Set a} (X : List A) → X ⊕ unit ≡ X
⊕-identityʳ (zero , []) = refl
⊕-identityʳ ((suc n) , (x ∷ xs)) = cong (x ::[] ⊕_) (⊕-identityʳ (n , xs))

⊕-assoc : ∀ {a} {A : Set a} (X Y Z : List A) → ((X ⊕ Y) ⊕ Z) ≡ (X ⊕ (Y ⊕ Z))
⊕-assoc (zero , []) Y Z = refl
⊕-assoc ((suc n) , (x ∷ xs)) Y Z = cong (x ::[] ⊕_) (⊕-assoc (n , xs) Y Z)


-- some other useful properties
subF : ∀ {a} {A : Set a} {X Y : List A} → X ≡ Y → Fin (len X) → Fin (len Y)
subF = subst (Fin ∘ len)

subF′ : ∀ {a} {A : Set a} {X Y : List A} → X ≡ Y → Fin (len X) → Fin (len Y)
subF′ eq = cast (cong len eq)

subF≗subF′ : ∀ {a} {A : Set a} {X Y : List A} → (eq : X ≡ Y) → (i : Fin (len X)) → subF eq i ≡ subF′ eq i
subF≗subF′ refl fzero = refl
subF≗subF′ {X = suc l , X ∷ XS} refl (fsuc i) = cong fsuc (subF≗subF′ {X = l , XS} refl i)


0-subst : ∀ {l} {A : Set l} {a b : List A} (eq : a ≡ b) {a′} →
          fzero ≡ subF (cong (a′ ::[] ⊕_) eq) fzero
0-subst refl = refl

fsuc-subst : ∀ {l} {A : Set l} {a b : List A} (eq : a ≡ b) x {a′} →
             fsuc (subF eq x) ≡ subF (cong (a′ ::[] ⊕_) eq) (fsuc x)
fsuc-subst refl x = refl


open ≡-Reasoning

splitAt-assoc : ∀ {a} {A : Set a} {X Y Z : List A} i → splitAt (len X) (subF (⊕-assoc X Y Z) i) ≡
                [ (map₂ (inject+ (len Z))) ∘ (splitAt (len X)) , inj₂ ∘ (raise (len Y)) ]′ (splitAt (len X + len Y) i)
splitAt-assoc {X = zero , []} {Y} {Z} i = begin
  _ ≡˘⟨ cong inj₂ (inject+-raise-splitAt (len Y) (len Z) i) ⟩
  _ ≡⟨ [,]-∘-distr inj₂ (splitAt (len Y) i) ⟩
  _ ∎
splitAt-assoc {X = suc l , X ∷ XS} {Y} {Z} fzero =
  cong (splitAt (suc l)) (subF≗subF′ (⊕-assoc (suc l , X ∷ XS) Y Z) fzero)
splitAt-assoc {X = suc l , X ∷ XS} {Y} {Z} (fsuc i) = begin
  _ ≡⟨ cong (splitAt (suc l)) (subF≗subF′ (⊕-assoc (suc l , X ∷ XS) Y Z) (fsuc i)) ⟩
  _ ≡˘⟨ cong ((map₁ fsuc) ∘ (splitAt l)) (subF≗subF′ _ i) ⟩
  _ ≡⟨ cong (map₁ fsuc) (splitAt-assoc {X = l , XS} {Y} {Z} i) ⟩
  _ ≡⟨ [,]-∘-distr (map₁ fsuc) (splitAt (l + len Y) i) ⟩
  _ ≡⟨ [,]-cong (map₁₂-commute ∘ (splitAt l)) (λ _ → refl) (splitAt (l + len Y) i) ⟩
  _ ≡˘⟨ [,]-map-commute (splitAt (l + len Y) i) ⟩
  _ ∎

splitAt-sym-assoc : ∀ {a} {A : Set a} {X Y Z : List A} i → splitAt (len X + len Y) (subF (sym (⊕-assoc X Y Z)) i) ≡
                    [ inj₁ ∘ (inject+ (len Y)) , (map₁ (raise (len X))) ∘ (splitAt (len Y)) ]′ (splitAt (len X) i)
splitAt-sym-assoc {X = zero , []} {Y} i with splitAt (len Y) i
splitAt-sym-assoc {X = zero , []} {Y} i    | inj₁ _ = refl
splitAt-sym-assoc {X = zero , []} {Y} i    | inj₂ _ = refl
splitAt-sym-assoc {X = suc l , X ∷ XS} {Y} {Z} fzero =
  cong (splitAt ((suc l) + (len Y))) (subF≗subF′ (sym (⊕-assoc (suc l , X ∷ XS) Y Z)) fzero)
splitAt-sym-assoc {X = suc l , X ∷ XS} {Y} {Z} (fsuc i) = begin
  _ ≡⟨ cong (splitAt ((suc l) + (len Y))) (subF≗subF′ (sym (⊕-assoc (suc l , X ∷ XS) Y Z)) (fsuc i)) ⟩
  _ ≡˘⟨ cong ((map₁ fsuc) ∘ (splitAt (l + (len Y)))) (subF≗subF′ _ i) ⟩
  _ ≡⟨ cong (map₁ fsuc) (splitAt-sym-assoc {X = l , XS} {Y} {Z} i) ⟩
  _ ≡⟨ [,]-∘-distr (map₁ fsuc) (splitAt l i) ⟩
  _ ≡⟨ [,]-cong (λ _ → refl) (map-commute ∘ (splitAt (len Y))) (splitAt l i) ⟩
  _ ≡˘⟨ [,]-map-commute (splitAt l i) ⟩
  _ ∎

assoc-raise : ∀ {a} {A : Set a} {X Y Z : List A} i →
              subF (⊕-assoc X Y Z) (raise (len X + len Y) i) ≡ raise (len X) (raise (len Y) i)
assoc-raise {X = zero , []} i = refl
assoc-raise {X = suc l , X ∷ XS} {Y} {Z} i = begin
  _ ≡⟨ subF≗subF′ _ (fsuc (raise (l + len Y) i)) ⟩
  _ ≡˘⟨ cong fsuc (subF≗subF′ _ (raise (l + len Y) i)) ⟩
  _ ≡⟨ cong fsuc (assoc-raise {X = l , XS} {Y} {Z} i) ⟩
  _ ∎

assoc-inject+ : ∀ {a} {A : Set a} {X Y Z : List A} i →
                subF (⊕-assoc X Y Z) (inject+ (len Z) i) ≡
                [ inject+ (len Y + len Z) , (raise (len X)) ∘ (inject+ (len Z)) ]′ (splitAt (len X) i)
assoc-inject+ {X = zero , []} i = refl
assoc-inject+ {X = suc l , X ∷ XS} {Y} {Z} fzero = subF≗subF′ (⊕-assoc (suc l , X ∷ XS) Y Z) fzero
assoc-inject+ {X = suc l , X ∷ XS} {Y} {Z} (fsuc i) = begin
  _ ≡⟨ subF≗subF′ _ (fsuc (inject+ (len Z) i)) ⟩
  _ ≡˘⟨ cong fsuc (subF≗subF′ _ (inject+ (len Z) i)) ⟩
  _ ≡⟨ cong fsuc (assoc-inject+ {X = l , XS} {Y} {Z} i) ⟩
  _ ≡⟨ [,]-∘-distr fsuc (splitAt l i) ⟩
  _ ≡˘⟨ [,]-map-commute (splitAt l i) ⟩
  _ ∎
