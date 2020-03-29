{-# OPTIONS --without-K --safe #-}

open import Level renaming (zero to lzero; suc to lsuc)
open import Data.Unit
open import Data.Product using (Σ; _,_; proj₁; proj₂; zip)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Fin renaming (zero to fzero; suc to fsuc; _+_ to _f+_)
open import Data.Fin.Properties using (inject+-raise-splitAt)
open import Data.Vec using (Vec; _++_; []; _∷_; replicate)
open import Data.Sum using (inj₁; inj₂; [_,_]′; map; map₁; map₂)
open import Data.Sum.Properties
open import Relation.Binary.PropositionalEquality
open import Function using (id ; _∘_)

module Nets.Utils where

-- general utilities
Σ₂ : ∀ {a} {b} {c} (A : Set a) (B : Set b)
     (C : A → B → Set c) → Set (a ⊔ b ⊔ c)
Σ₂ A B C = Σ A λ a → Σ B λ b → C a b

-- selectors for the source and target of abstract Edges
s : ∀ {l lₛ lₜ} {S : Set lₛ} {T : Set lₜ} {E : S → T → Set l} → Σ₂ S T E → S
s = proj₁

t : ∀ {l lₛ lₜ} {S : Set lₛ} {T : Set lₜ} {E : S → T → Set l} → Σ₂ S T E → T
t = proj₁ ∘ proj₂


-- convinient way to represent lists as Vectors along with their size
List : ∀ {l} → Set l → Set l
List A = Σ ℕ (Vec A)

len         = proj₁
vec-of-list = proj₂

subF : ∀ {a} {A : Set a} {X Y : List A} → X ≡ Y → Fin (len X) → Fin (len Y)
subF = subst (Fin ∘ len)

subF′ : ∀ {a} {A : Set a} {X Y : List A} → X ≡ Y → Fin (len X) → Fin (len Y)
subF′ eq = cast (cong len eq)

subF≗subF′ : ∀ {a} {A : Set a} {X Y : List A} → (eq : X ≡ Y) → (i : Fin (len X)) → subF eq i ≡ subF′ eq i
subF≗subF′ refl fzero = refl
subF≗subF′ {X = suc l , X ∷ XS} refl (fsuc i) = cong fsuc (subF≗subF′ {X = l , XS} refl i)

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

-- list concatenation
_⊕_ : ∀ {l} {A : Set l} → (xs ys : List A) → List A
_⊕_ = zip _+_ _++_

-- some properties of list concatenation
⊕-identityʳ : ∀ {a} {A : Set a} (X : List A) → X ⊕ (zero , []) ≡ X
⊕-identityʳ (zero , []) = refl
⊕-identityʳ ((suc n) , (x ∷ xs)) = cong (x ∷[] ⊕_) (⊕-identityʳ (n , xs))

⊕-assoc : ∀ {a} {A : Set a} (X Y Z : List A) → ((X ⊕ Y) ⊕ Z) ≡ (X ⊕ (Y ⊕ Z))
⊕-assoc (zero , []) Y Z = refl
⊕-assoc ((suc n) , (x ∷ xs)) Y Z = cong (x ∷[] ⊕_) (⊕-assoc (n , xs) Y Z)

-- some other useful properties
0-subst : ∀ {l} {A : Set l} {a b : List A} (eq : a ≡ b) {a′} →
          fzero ≡ subF (cong (a′ ∷[] ⊕_) eq) fzero
0-subst refl = refl

fsuc-subst : ∀ {l} {A : Set l} {a b : List A} (eq : a ≡ b) x {a′} →
             fsuc (subF eq x) ≡ subF (cong (a′ ∷[] ⊕_) eq) (fsuc x)
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
