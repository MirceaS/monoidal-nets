open import Level renaming (zero to lzero ; suc to lsuc)
open import Agda.Builtin.Equality
open import Data.Unit
open import Data.Unit.Properties using (≡-setoid)
open import Data.Product using (Σ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum using (inj₁ ; inj₂)
open import Data.Nat
open import Data.Vec
open import Data.Fin using (Fin)
open import Data.Fin.Patterns
open import Data.Empty
open import Relation.Binary hiding (_⇒_)


import Nets.Hypergraph ≡-setoid as HGBase
open import Nets.Properties ≡-setoid using (Hypergraph-Category)

module Nets.Example where 

--shorthands for common type interfaces
0* : Σ _ (Vec ⊤)
0* = 0 , []
1* : Σ _ (Vec ⊤)
1* = 1 , (tt ∷ [])
2* : Σ _ (Vec ⊤)
2* = 2 , (tt ∷ tt ∷ [])

data Obj : Σ _ (Vec ⊤) → Σ _ (Vec ⊤) → Set where
--the objects variables that we want to use along with their input/output type interfaces
  A B : Obj 2* 2*
  C   : Obj 2* 1*


data hierarchical :   (l : ℕ) → (s t : Σ _ (Vec ⊤)) → Set₁
data eq :             (l : ℕ) → (s t : Σ _ (Vec ⊤)) → Rel (hierarchical l s t) (lsuc lzero) -- (G H : hierarchical l s t) → Set₁
hierarchical-setoid : (l : ℕ) → (s t : Σ _ (Vec ⊤)) → Setoid (lsuc lzero) (lsuc lzero)

{-# NO_POSITIVITY_CHECK #-}
data hierarchical where
  lambda : {l : ℕ} →
           HGBase.Hypergraph (hierarchical-setoid l) {lzero} 2* 1* →
           hierarchical (suc l) 1* 1*
  app :    {l : ℕ} →
           hierarchical l 2* 1*

data eq where
  lambda-eq : {l : ℕ} →
              (H₁ H₂ : HGBase.Hypergraph (hierarchical-setoid l) {lzero} 2* 1*) →
              HGBase._≋_ (hierarchical-setoid l) H₁ H₂ →
              eq (suc l) 1* 1* (lambda H₁) (lambda H₂)
  app-eq :    {l : ℕ} →
              eq l 2* 1* app app

hierarchical-setoid level s t = record
  { Carrier = hierarchical level s t
  ; _≈_ = eq level s t
  ; isEquivalence = eq-isEquivalence level s t
  }
  where
    module HC l = Hypergraph-Category (hierarchical-setoid l) {lzero}

    eq-refl : (l : ℕ) → (s t : Σ _ (Vec ⊤)) → {x : hierarchical l s t} → eq l s t x x
    eq-refl (suc l) s t {lambda x} = lambda-eq x x (HC.Equiv.refl l)
    eq-refl l s t {app} = app-eq

    eq-sym : (l : ℕ) → (s t : Σ _ (Vec ⊤)) → {x y : hierarchical l s t} → eq l s t x y → eq l s t y x
    eq-sym (suc l) s t {lambda x} {lambda y} (lambda-eq x y x=y) = lambda-eq y x (HC.Equiv.sym l x=y)
    eq-sym l s t {app} {app} _ = app-eq

    eq-trans : (l : ℕ) → (s t : Σ _ (Vec ⊤)) → {x y z : hierarchical l s t} →
               eq l s t x y → eq l s t y z → eq l s t x z
    eq-trans (suc l) s t {lambda x} {lambda y} {lambda z} (lambda-eq x y x=y) (lambda-eq y z y=z) =
      lambda-eq x z (HC.Equiv.trans l x=y y=z)
    eq-trans l s t {app} {app} {app} _ _ = app-eq

    eq-isEquivalence : (l : ℕ) → (s t : Σ _ (Vec ⊤)) → IsEquivalence (eq l s t)
    eq-isEquivalence l s t = record
      { refl = eq-refl l s t
      ; sym = eq-sym l s t
      ; trans = eq-trans l s t
      }


liftHG : ∀ {l s t} → HGBase.Hypergraph (hierarchical-setoid l      ) {lzero} s t →
                      HGBase.Hypergraph (hierarchical-setoid (suc l)) {lzero} s t
liftHG {l} {s} {t} h = record
  { E = h.E
  ; conns→ = h.conns→
  ; conns← = h.conns←
  ; type-match = h.type-match
  ; bijection = h.bijection
  ; o = o
  }
  where
    module h = HGBase.Hypergraph (hierarchical-setoid l) h

    o : ∀ {input output} → h.E input output → hierarchical (suc l) input output
    o e with (h.o e)
    o e    | (lambda x) = lambda (liftHG x)
    o e    | app = app


module HG l = HGBase (hierarchical-setoid l)
module HC l = Hypergraph-Category (hierarchical-setoid l) {lzero}

module pop l where
  open HC (suc l)
  open HG (suc l)
  _⇒′_ = HG.Hypergraph l {lzero}

  LHS : 2* ⇒′ 1* → 2* ⇒ 1*
  LHS h = ⟦ app ⟧ ∘ ((id {1*}) ⨂ ⟦ lambda h ⟧)

  RHS : 2* ⇒′ 1* → 2* ⇒ 1*
  RHS = liftHG


data _~_ : ∀ {l s t} → Rel (HG.Hypergraph l {lzero} s t) (lsuc lzero) where
  -- maybe do this via a relation union or other construct?
  -- ≋→~ : ∀ {l s t} → (g h : HG.Hypergraph l {lzero} s t) → HG._≋_ l g h → g ~ h
  pop : ∀ {l} → (h : HG.Hypergraph l {lzero} 2* 1*) →
           _~_ {suc l} {2*} {1*} (pop.LHS l h) (pop.RHS l h)

{-
    level' : ℕ
    level' = level
      
    _~_ : Rel (hierarchical level s t) _
    _~_ with level
    _~_    | zero = ?
    _~_    | (suc l) = ? -}

-- diagram : Hypergraph Obj 2* 1*
-- diagram = record
--             { E = E
--             ; o = o
--             ; conns→ = conns→
--             ; conns← = conns←
--             ; type-match = type-match
--             ; one-to-one = one-to-one
--             }
--             where
--               E = Fin 4
--               o = lookup ((_ , _ , A) ∷ (_ , _ , A) ∷ (_ , _ , B) ∷ (_ , _ , C) ∷ [])
--               conns→ : _
--               conns→ (inj₁ 0F) = inj₂ (0F , 1F)
--               conns→ (inj₁ 1F) = inj₂ (1F , 1F)
--               conns→ (inj₂ (0F , 0F)) = inj₂ (1F , 0F)
--               conns→ (inj₂ (0F , 1F)) = inj₂ (2F , 0F)
--               conns→ (inj₂ (1F , 0F)) = inj₂ (0F , 0F)
--               conns→ (inj₂ (1F , 1F)) = inj₂ (2F , 1F)
--               conns→ (inj₂ (2F , 0F)) = inj₂ (3F , 0F)
--               conns→ (inj₂ (2F , 1F)) = inj₂ (3F , 1F)
--               conns→ (inj₂ (3F , 0F)) = inj₁ 0F
--               conns← : _
--               conns← (inj₁ 0F) = inj₂ (3F , 0F)
--               conns← (inj₂ (0F , 0F)) = inj₂ (1F , 0F)
--               conns← (inj₂ (0F , 1F)) = inj₁ 0F
--               conns← (inj₂ (1F , 0F)) = inj₂ (0F , 0F)
--               conns← (inj₂ (1F , 1F)) = inj₁ 1F
--               conns← (inj₂ (2F , 0F)) = inj₂ (0F , 1F)
--               conns← (inj₂ (2F , 1F)) = inj₂ (1F , 1F)
--               conns← (inj₂ (3F , 0F)) = inj₂ (2F , 0F)
--               conns← (inj₂ (3F , 1F)) = inj₂ (2F , 1F)
--               type-match : _
--               type-match (inj₁ 0F) = refl
--               type-match (inj₁ 1F) = refl
--               type-match (inj₂ (0F , 0F)) = refl
--               type-match (inj₂ (0F , 1F)) = refl
--               type-match (inj₂ (1F , 0F)) = refl
--               type-match (inj₂ (1F , 1F)) = refl
--               type-match (inj₂ (2F , 0F)) = refl
--               type-match (inj₂ (2F , 1F)) = refl
--               type-match (inj₂ (3F , 0F)) = refl
--               one-to-oneₗ : _
--               one-to-oneₗ (inj₁ 0F) = refl
--               one-to-oneₗ (inj₂ (0F , 0F)) = refl
--               one-to-oneₗ (inj₂ (0F , 1F)) = refl
--               one-to-oneₗ (inj₂ (1F , 0F)) = refl
--               one-to-oneₗ (inj₂ (1F , 1F)) = refl
--               one-to-oneₗ (inj₂ (2F , 0F)) = refl
--               one-to-oneₗ (inj₂ (2F , 1F)) = refl
--               one-to-oneₗ (inj₂ (3F , 0F)) = refl
--               one-to-oneₗ (inj₂ (3F , 1F)) = refl
--               one-to-oneᵣ : _
--               one-to-oneᵣ (inj₁ 0F) = refl
--               one-to-oneᵣ (inj₁ 1F) = refl
--               one-to-oneᵣ (inj₂ (0F , 0F)) = refl
--               one-to-oneᵣ (inj₂ (0F , 1F)) = refl
--               one-to-oneᵣ (inj₂ (1F , 0F)) = refl
--               one-to-oneᵣ (inj₂ (1F , 1F)) = refl
--               one-to-oneᵣ (inj₂ (2F , 0F)) = refl
--               one-to-oneᵣ (inj₂ (2F , 1F)) = refl
--               one-to-oneᵣ (inj₂ (3F , 0F)) = refl
--               one-to-one : _
--               one-to-one = one-to-oneₗ , one-to-oneᵣ
