{-# OPTIONS --without-K --safe #-}

{- This is the main file of this library and it 
 - formalises the idea of a String Diagram.
 -
 - ~ Octavian-Mircea Sebe, 2020
 -}


open import Level renaming (zero to lzero; suc to lsuc)
open import Agda.Builtin.Equality
open import Data.Product as Prod using (Σ; _,_; proj₁; proj₂; ∃; _×_)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Sum.Properties
open import Data.Nat hiding (_⊔_)
open import Data.Vec hiding (splitAt)
open import Data.Vec.Properties using (lookup-splitAt; lookup-++ˡ; lookup-++ʳ)
open import Data.Fin renaming (zero to fzero; suc to fsuc; _+_ to _f+_)
open import Data.Fin.Properties using (splitAt-inject+; splitAt-raise; inject+-raise-splitAt)
open import Data.Empty.Polymorphic
open import Data.Unit.Polymorphic
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Function using (_∘_; _$_; Inverseᵇ; id)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open import Nets.Utils
open import Nets.Hypergraph

module Nets.Diagram {ℓ₁ ℓ₂ ℓ₃} (HG : Hypergraph ℓ₁ ℓ₂ ℓ₃) where

private
  module E = Hypergraph HG
  open E renaming (V to VLabel; E to ELabel) using ()

module Core {l : Level} where

  infix 4 _≋[_][_]_ _≋_
  infixr 9 _⊚[_]_ _⊚_
  infixr 10 _⨂_

  record Diagram (input : List VLabel) (output : List VLabel) : Set (lsuc l ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) where
    field
      E : List VLabel → List VLabel → Set l

    -- to be accessed from the outside when the input or
    -- output are not so easy to deduce
    inp = input
    oup = output

    -- type representing the ports that arrows go into
    in-index  = (Fin (len output)) ⊎ (Σ (Σ₂ _ _ E) (Fin ∘ len ∘ s))
    -- type representing the ports that arrows go out of
    out-index = (Fin (len input))  ⊎ (Σ (Σ₂ _ _ E) (Fin ∘ len ∘ t))

    in-lookup  : in-index  → VLabel
    in-lookup  = [ lookup (vec-of-list output) , (λ {((s , _ , e) , i) → lookup (vec-of-list s) i})]′

    out-lookup : out-index → VLabel
    out-lookup = [ lookup (vec-of-list input)  , (λ {((_ , t , e) , i) → lookup (vec-of-list t) i})]′

    field
      conns→ : out-index → in-index
      conns← : in-index → out-index
      type-match : (i : out-index) → out-lookup i ≡ in-lookup (conns→ i)
      bijection : Inverseᵇ _≡_ _≡_ conns→ conns←

    bijection₁ = proj₁ bijection
    bijection₂ = proj₂ bijection

    field
      -- the label associated with each box
      o : ∀ {input output} → E input output → ELabel input output

    ↑ : {E′ : List VLabel → List VLabel → Set l} → (f : ∀ {s t} → E s t → E′ s t) →
        Σ (Σ₂ _ _ E) (Fin ∘ len ∘ s) → Σ (Σ₂ _ _ E′) (Fin ∘ len ∘ s)
    ↑ f ((s , t , e) , i) = ((s , t , f e) , i)

    ↑′ : {E′ : List VLabel → List VLabel → Set l} → (f : ∀ {s t} → E s t → E′ s t) →
        Σ (Σ₂ _ _ E) (Fin ∘ len ∘ t) → Σ (Σ₂ _ _ E′) (Fin ∘ len ∘ t)
    ↑′ f ((s , t , e) , i) = ((s , t , f e) , i)


  -- diagram isomorphism

  -- defining the isomorphism heterogenously saves us a lot of trouble later on
  record _≋[_][_]_ {A B A′ B′ : List VLabel} (LHS : Diagram A B) (A≡A′ : A ≡ A′) (B≡B′ : B ≡ B′)
                   (RHS : Diagram A′ B′) : Set (l ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) where
    module LHS = Diagram LHS
    module RHS = Diagram RHS
    field
      α : ∀ {input output} → LHS.E input output → RHS.E input output
      α′ : ∀ {input output} → RHS.E input output → LHS.E input output

      bijection : ∀ {input output} → Inverseᵇ _≡_ _≡_ (α {input} {output}) (α′)
      obj-resp : ∀ {input output} → (e : LHS.E input output) → (LHS.o e) E.≈ (RHS.o (α e))

    α-in-index :  LHS.in-index  → RHS.in-index
    α-in-index  = Sum.map (subF B≡B′) (LHS.↑ α)
    α-out-index : LHS.out-index → RHS.out-index
    α-out-index = Sum.map (subF A≡A′) (LHS.↑′ α)

    field
      conns→-resp : (i : LHS.out-index) →
                     RHS.conns→ (α-out-index i) ≡ α-in-index (LHS.conns→ i)
 
    conns←-resp : (i : LHS.in-index) →
                   RHS.conns← (α-in-index i) ≡ α-out-index (LHS.conns← i)
    conns←-resp i = let open ≡-Reasoning in begin
      _ ≡˘⟨ cong (RHS.conns← ∘ α-in-index) (LHS.bijection₁ i) ⟩
      _ ≡˘⟨ cong RHS.conns← (conns→-resp (LHS.conns← i)) ⟩
      _ ≡⟨ RHS.bijection₂ (α-out-index (LHS.conns← i)) ⟩
      _ ∎

  -- the homogenous version of the diagram isomorphism
  _≋_ : ∀ {A B} → Rel (Diagram A B) (l ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
  _≋_ = _≋[ refl ][ refl ]_

  module _≋_ = _≋[_][_]_

  ≋[][]→≋ : ∀ {A B A′ B′ : List VLabel} {LHS : Diagram A B} {A≡A′ : A ≡ A′} {B≡B′ : B ≡ B′} {RHS : Diagram A′ B′} →
             LHS ≋[ A≡A′ ][ B≡B′ ] RHS → subst₂ Diagram A≡A′ B≡B′ LHS ≋ RHS
  ≋[][]→≋ {A≡A′ = refl} {refl} l=r = l=r


  -- heterogenous diagram composition
  _⊚[_]_ : ∀ {A B C D : List VLabel} → Diagram C D → B ≡ C → Diagram A B → Diagram A D
  _⊚[_]_ {A} {B} {C} {D} CD BC AB = record
    { E = E
    ; conns→ = conns→
    ; conns← = conns←
    ; type-match = type-match
    ; bijection = bijection
    ; o = [ AB.o , CD.o ]′
    }
    where
      module AB = Diagram AB
      module CD = Diagram CD

      open ≡-Reasoning

      sub = subF BC
      sub′ = subF (sym BC)

      lemma : ∀ j → lookup (vec-of-list B) j ≡ lookup (vec-of-list C) (sub j)
      lemma _ rewrite BC = refl

      E : _
      E input output = (AB.E input output) ⊎ (CD.E input output)

      conns→ : _
      conns→ (inj₁ i) =
        [ (λ j → Sum.map₂ (CD.↑ inj₂) (CD.conns→ (inj₁ (sub j))))
        , inj₂ ∘ (AB.↑ inj₁)
        ]′ (AB.conns→ (inj₁ i))
      conns→ (inj₂ ((_ , _ , inj₁ e) , i)) =
        [ (λ j → Sum.map₂ (CD.↑ inj₂) (CD.conns→ (inj₁ (sub j))))
        , inj₂ ∘ (AB.↑ inj₁)
        ]′ (AB.conns→ (inj₂ ((_ , _ , e) , i)))
      conns→ (inj₂ ((_ , _ , inj₂ e) , j)) =
        Sum.map₂ (CD.↑ inj₂) (CD.conns→ (inj₂ ((_ , _ , e) , j)))

      conns← : _
      conns← (inj₁ i) =
        [ (λ j → Sum.map₂ (AB.↑′ inj₁) (AB.conns← (inj₁ (sub′ j))))
        , inj₂ ∘ (CD.↑′ inj₂)
        ]′ (CD.conns← (inj₁ i))
      conns← (inj₂ ((_ , _ , inj₁ e) , j)) =
        Sum.map₂ (AB.↑′ inj₁) (AB.conns← (inj₂ ((_ , _ , e) , j)))
      conns← (inj₂ ((_ , _ , inj₂ e) , i)) =
        [ (λ j → Sum.map₂ (AB.↑′ inj₁) (AB.conns← (inj₁ (sub′ j))))
        , inj₂ ∘ (CD.↑′ inj₂)
        ]′ (CD.conns← (inj₂ ((_ , _ , e) , i)))

      type-match : _
      type-match (inj₁ i) with (AB.conns→ (inj₁ i)) | (inspect AB.conns→ (inj₁ i))
      type-match (inj₁ i) | (inj₁ j) | [ i→j ] with (CD.conns→ (inj₁ (sub j))) | (inspect CD.conns→ (inj₁ (sub j)))
      type-match (inj₁ i) | (inj₁ j) | [ i→j ] | (inj₁ _) | [ j→k ] = begin
        _ ≡⟨ AB.type-match (inj₁ i) ⟩
        _ ≡⟨ cong [ _ , _ ]′ i→j ⟩
        _ ≡⟨ lemma j ⟩
        _ ≡⟨ CD.type-match (inj₁ (sub j)) ⟩
        _ ≡⟨ cong [ _ , _ ]′ j→k ⟩
        _ ∎
      type-match (inj₁ i) | (inj₁ j) | [ i→j ] | (inj₂ _) | [ j→k ] = begin
        _ ≡⟨ AB.type-match (inj₁ i) ⟩
        _ ≡⟨ cong [ _ , _ ]′ i→j ⟩
        _ ≡⟨ lemma j ⟩
        _ ≡⟨ CD.type-match (inj₁ (sub j)) ⟩
        _ ≡⟨ cong [ _ , _ ]′ j→k ⟩
        _ ∎
      type-match (inj₁ i) | (inj₂ _) | [ i→j ] = begin
        _ ≡⟨ AB.type-match (inj₁ i) ⟩
        _ ≡⟨ cong [ _ , _ ]′ i→j ⟩
        _ ∎
      type-match (inj₂ ((_ , _ , inj₁ e) , i)) with (AB.conns→ (inj₂ ((_ , _ , e) , i))) | (inspect AB.conns→ (inj₂ ((_ , _ , e) , i)))
      type-match (inj₂ ((_ , _ , inj₁ e) , i)) | (inj₁ j) | [ i→j ] with (CD.conns→ (inj₁ (sub j))) | (inspect CD.conns→ (inj₁ (sub j)))
      type-match (inj₂ ((_ , _ , inj₁ e) , i)) | (inj₁ j) | [ i→j ] | (inj₁ _) | [ j→k ] = begin
        _ ≡⟨ AB.type-match (inj₂ ((_ , _ , e) , i)) ⟩
        _ ≡⟨ cong [ _ , _ ]′ i→j ⟩
        _ ≡⟨ lemma j ⟩
        _ ≡⟨ CD.type-match (inj₁ (sub j)) ⟩
        _ ≡⟨ cong [ _ , _ ]′ j→k ⟩
        _ ∎
      type-match (inj₂ ((_ , _ , inj₁ e) , i)) | (inj₁ j) | [ i→j ] | (inj₂ _) | [ j→k ] = begin
        _ ≡⟨ AB.type-match (inj₂ ((_ , _ , e) , i)) ⟩
        _ ≡⟨ cong [ _ , _ ]′ i→j ⟩
        _ ≡⟨ lemma j ⟩
        _ ≡⟨ CD.type-match (inj₁ (sub j)) ⟩
        _ ≡⟨ cong [ _ , _ ]′ j→k ⟩
        _ ∎
      type-match (inj₂ ((_ , _ , inj₁ e) , i)) | (inj₂ _) | [ i→j ] = begin
        _ ≡⟨ AB.type-match (inj₂ ((_ , _ , e) , i)) ⟩
        _ ≡⟨ cong [ _ , _ ]′ i→j ⟩
        _ ∎
      type-match (inj₂ ((_ , _ , inj₂ e) , i)) with (CD.conns→ (inj₂ ((_ , _ , e) , i))) | (inspect CD.conns→ (inj₂ ((_ , _ , e) , i)))
      type-match (inj₂ ((_ , _ , inj₂ e) , i)) | (inj₁ _) | [ i→j ] = begin
        _ ≡⟨ CD.type-match (inj₂ ((_ , _ , e) , i)) ⟩
        _ ≡⟨ cong [ _ , _ ]′ i→j ⟩
        _ ∎
      type-match (inj₂ ((_ , _ , inj₂ e) , i)) | (inj₂ _) | [ i→j ] = begin
        _ ≡⟨ CD.type-match (inj₂ ((_ , _ , e) , i)) ⟩
        _ ≡⟨ cong [ _ , _ ]′ i→j ⟩
        _ ∎

      bijection₁ : _
      bijection₁ (inj₁ i) with (CD.conns← (inj₁ i)) | (inspect CD.conns← (inj₁ i))
      bijection₁ (inj₁ i) | (inj₁ j) | [ i→j ] with (AB.conns← (inj₁ (sub′ j))) | (inspect AB.conns← (inj₁ (sub′ j)))
      bijection₁ (inj₁ i) | (inj₁ j) | [ i→j ] | (inj₁ _) | [ j→k ] = begin
          _ ≡˘⟨ cong [ _ , _ ]′   (cong AB.conns→ j→k) ⟩
          _ ≡⟨  cong [ _ , _ ]′   (AB.bijection₁ (inj₁ (sub′ j))) ⟩
          _ ≡⟨  cong (Sum.map₂ _) (cong (CD.conns→ ∘ inj₁) (subst-subst-sym BC)) ⟩
          _ ≡˘⟨ cong (Sum.map₂ _) (cong CD.conns→ i→j) ⟩
          _ ≡⟨  cong (Sum.map₂ _) (CD.bijection₁ (inj₁ i)) ⟩
          _ ∎
      bijection₁ (inj₁ i) | (inj₁ j) | [ i→j ] | (inj₂ _) | [ j→k ] = begin
          _ ≡˘⟨ cong [ _ , _ ]′   (cong AB.conns→ j→k) ⟩
          _ ≡⟨  cong [ _ , _ ]′   (AB.bijection₁ (inj₁ (sub′ j))) ⟩
          _ ≡⟨  cong (Sum.map₂ _) (cong (CD.conns→ ∘ inj₁) (subst-subst-sym BC)) ⟩
          _ ≡˘⟨ cong (Sum.map₂ _) (cong CD.conns→ i→j) ⟩
          _ ≡⟨  cong (Sum.map₂ _) (CD.bijection₁ (inj₁ i)) ⟩
          _ ∎
      bijection₁ (inj₁ i) | (inj₂ _) | [ i→j ] = cong (Sum.map₂ _) (begin
          _ ≡˘⟨ cong CD.conns→ i→j ⟩
          _ ≡⟨ CD.bijection₁ (inj₁ i) ⟩
          _ ∎)
      bijection₁ (inj₂ ((_ , _ , inj₁ e) , i)) with (AB.conns← (inj₂ ((_ , _ , e) , i))) | (inspect AB.conns← (inj₂ ((_ , _ , e) , i)))
      bijection₁ (inj₂ ((_ , _ , inj₁ e) , i)) | (inj₁ _) | [ i→j ] = cong [ _ , _ ]′ (begin
          _ ≡˘⟨ cong AB.conns→ i→j ⟩
          _ ≡⟨ AB.bijection₁ (inj₂ ((_ , _ , e) , i)) ⟩
          _ ∎)
      bijection₁ (inj₂ ((_ , _ , inj₁ e) , i)) | (inj₂ _) | [ i→j ] = cong [ _ , _ ]′ (begin
          _ ≡˘⟨ cong AB.conns→ i→j ⟩
          _ ≡⟨ AB.bijection₁ (inj₂ ((_ , _ , e) , i)) ⟩
          _ ∎)
      bijection₁ (inj₂ ((_ , _ , inj₂ e) , i)) with (CD.conns← (inj₂ ((_ , _ , e) , i))) | (inspect CD.conns← (inj₂ ((_ , _ , e) , i)))
      bijection₁ (inj₂ ((_ , _ , inj₂ e) , i)) | (inj₁ j) | [ i→j ] with (AB.conns← (inj₁ (sub′ j))) | (inspect AB.conns← (inj₁ (sub′ j)))
      bijection₁ (inj₂ ((_ , _ , inj₂ e) , i)) | (inj₁ j) | [ i→j ] | (inj₁ _) | [ j→k ] = begin
          _ ≡˘⟨ cong [ _ , _ ]′   (cong AB.conns→ j→k) ⟩
          _ ≡⟨  cong [ _ , _ ]′   (AB.bijection₁ (inj₁ (sub′ j))) ⟩
          _ ≡⟨  cong (Sum.map₂ _) (cong (CD.conns→ ∘ inj₁) (subst-subst-sym BC)) ⟩
          _ ≡˘⟨ cong (Sum.map₂ _) (cong CD.conns→ i→j) ⟩
          _ ≡⟨  cong (Sum.map₂ _) (CD.bijection₁ (inj₂ ((_ , _ , e) , i))) ⟩
          _ ∎
      bijection₁ (inj₂ ((_ , _ , inj₂ e) , i)) | (inj₁ j) | [ i→j ] | (inj₂ _) | [ j→k ] = begin
          _ ≡˘⟨ cong [ _ , _ ]′   (cong AB.conns→ j→k) ⟩
          _ ≡⟨  cong [ _ , _ ]′   (AB.bijection₁ (inj₁ (sub′ j))) ⟩
          _ ≡⟨  cong (Sum.map₂ _) (cong (CD.conns→ ∘ inj₁) (subst-subst-sym BC)) ⟩
          _ ≡˘⟨ cong (Sum.map₂ _) (cong CD.conns→ i→j) ⟩
          _ ≡⟨  cong (Sum.map₂ _) (CD.bijection₁ (inj₂ ((_ , _ , e) , i))) ⟩
          _ ∎
      bijection₁ (inj₂ ((_ , _ , inj₂ e) , i)) | (inj₂ _) | [ i→j ] = cong (Sum.map₂ _) (begin
          _ ≡˘⟨ cong CD.conns→ i→j ⟩
          _ ≡⟨ CD.bijection₁ (inj₂ ((_ , _ , e) , i)) ⟩
          _ ∎)

      bijection₂ : _
      bijection₂ (inj₁ i) with (AB.conns→ (inj₁ i)) | (inspect AB.conns→ (inj₁ i))
      bijection₂ (inj₁ i) | (inj₁ j) | [ i→j ] with (CD.conns→ (inj₁ (sub j))) | (inspect CD.conns→ (inj₁ (sub j)))
      bijection₂ (inj₁ i) | (inj₁ j) | [ i→j ] | (inj₁ _) | [ j→k ] = begin
          _ ≡˘⟨ cong [ _ , _ ]′   (cong CD.conns← j→k) ⟩
          _ ≡⟨  cong [ _ , _ ]′   (CD.bijection₂ (inj₁ (sub j))) ⟩
          _ ≡⟨  cong (Sum.map₂ _) (cong (AB.conns← ∘ inj₁) (subst-sym-subst BC)) ⟩
          _ ≡˘⟨ cong (Sum.map₂ _) (cong AB.conns← i→j) ⟩
          _ ≡⟨  cong (Sum.map₂ _) (AB.bijection₂ (inj₁ i)) ⟩
          _ ∎
      bijection₂ (inj₁ i) | (inj₁ j) | [ i→j ] | (inj₂ _) | [ j→k ] = begin
          _ ≡˘⟨ cong [ _ , _ ]′   (cong CD.conns← j→k) ⟩
          _ ≡⟨  cong [ _ , _ ]′   (CD.bijection₂ (inj₁ (sub j))) ⟩
          _ ≡⟨  cong (Sum.map₂ _) (cong (AB.conns← ∘ inj₁) (subst-sym-subst BC)) ⟩
          _ ≡˘⟨ cong (Sum.map₂ _) (cong AB.conns← i→j) ⟩
          _ ≡⟨  cong (Sum.map₂ _) (AB.bijection₂ (inj₁ i)) ⟩
          _ ∎
      bijection₂ (inj₁ i) | (inj₂ _) | [ i→j ] = cong (Sum.map₂ _) (begin
          _ ≡˘⟨ cong AB.conns← i→j ⟩
          _ ≡⟨ AB.bijection₂ (inj₁ i) ⟩
          _ ∎)
      bijection₂ (inj₂ ((_ , _ , inj₁ e) , i)) with (AB.conns→ (inj₂ ((_ , _ , e) , i))) | (inspect AB.conns→ (inj₂ ((_ , _ , e) , i)))
      bijection₂ (inj₂ ((_ , _ , inj₁ e) , i)) | (inj₁ j) | [ i→j ] with (CD.conns→ (inj₁ (sub j))) | (inspect CD.conns→ (inj₁ (sub j)))
      bijection₂ (inj₂ ((_ , _ , inj₁ e) , i)) | (inj₁ j) | [ i→j ] | (inj₁ _) | [ j→k ] = begin
          _ ≡˘⟨ cong [ _ , _ ]′   (cong CD.conns← j→k) ⟩
          _ ≡⟨  cong [ _ , _ ]′   (CD.bijection₂ (inj₁ (sub j))) ⟩
          _ ≡⟨  cong (Sum.map₂ _) (cong (AB.conns← ∘ inj₁) (subst-sym-subst BC)) ⟩
          _ ≡˘⟨ cong (Sum.map₂ _) (cong AB.conns← i→j) ⟩
          _ ≡⟨  cong (Sum.map₂ _) (AB.bijection₂ (inj₂ ((_ , _ , e) , i))) ⟩
          _ ∎
      bijection₂ (inj₂ ((_ , _ , inj₁ e) , i)) | (inj₁ j) | [ i→j ] | (inj₂ _) | [ j→k ] = begin
          _ ≡˘⟨ cong [ _ , _ ]′   (cong CD.conns← j→k) ⟩
          _ ≡⟨  cong [ _ , _ ]′   (CD.bijection₂ (inj₁ (sub j))) ⟩
          _ ≡⟨  cong (Sum.map₂ _) (cong (AB.conns← ∘ inj₁) (subst-sym-subst BC)) ⟩
          _ ≡˘⟨ cong (Sum.map₂ _) (cong AB.conns← i→j) ⟩
          _ ≡⟨  cong (Sum.map₂ _) (AB.bijection₂ (inj₂ ((_ , _ , e) , i))) ⟩
          _ ∎
      bijection₂ (inj₂ ((_ , _ , inj₁ e) , i)) | (inj₂ _) | [ i→j ] = cong (Sum.map₂ _) (begin
          _ ≡˘⟨ cong AB.conns← i→j ⟩
          _ ≡⟨ AB.bijection₂ (inj₂ ((_ , _ , e) , i)) ⟩
          _ ∎)
      bijection₂ (inj₂ ((_ , _ , inj₂ e) , i)) with (CD.conns→ (inj₂ ((_ , _ , e) , i))) | (inspect CD.conns→ (inj₂ ((_ , _ , e) , i)))
      bijection₂ (inj₂ ((_ , _ , inj₂ e) , i)) | (inj₁ _) | [ i→j ] = cong [ _ , _ ]′ (begin
          _ ≡˘⟨ cong CD.conns← i→j ⟩
          _ ≡⟨ CD.bijection₂ (inj₂ ((_ , _ , e) , i)) ⟩
          _ ∎)
      bijection₂ (inj₂ ((_ , _ , inj₂ e) , i)) | (inj₂ _) | [ i→j ] = cong [ _ , _ ]′ (begin
          _ ≡˘⟨ cong CD.conns← i→j ⟩
          _ ≡⟨ CD.bijection₂ (inj₂ ((_ , _ , e) , i)) ⟩
          _ ∎)

      bijection : _
      bijection = bijection₁ , bijection₂

  -- homogenous diagram composition
  _⊚_ : ∀ {A B C} → Diagram B C → Diagram A B → Diagram A C
  _⊚_ = _⊚[ refl ]_

  ⊚[]≡⊚ : ∀ {A B C D : List VLabel} → {f : Diagram C D} → {BC : B ≡ C} → {g : Diagram A B} → f ⊚[ BC ] g ≡ f ⊚ (subst (Diagram A) BC g)
  ⊚[]≡⊚ {BC = refl} = refl


  -- Diagram tensor product
  _⨂_ : ∀ {A B C D : List VLabel} → Diagram A B → Diagram C D → Diagram (A ⊕ C) (B ⊕ D)
  _⨂_ {A} {B} {C} {D} AB CD = record
    { E = E
    ; conns→ = conns→
    ; conns← = conns←
    ; type-match = type-match
    ; bijection = bijection
    ; o = [ AB.o , CD.o ]′
    }
    where
      module AB = Diagram AB
      module CD = Diagram CD

      open ≡-Reasoning

      E : _
      E input output = (AB.E input output) ⊎ (CD.E input output)

      conns→ : _
      conns→ (inj₁ i) = [ ((Sum.map (inject+ (len D)) (AB.↑ inj₁)) ∘ AB.conns→ ∘ inj₁)
                         , ((Sum.map (raise   (len B)) (CD.↑ inj₂)) ∘ CD.conns→ ∘ inj₁)
                         ]′ (splitAt (len A) i)
      conns→ (inj₂ ((_ , _ , inj₁ e) , i)) = Sum.map (inject+ (len D)) (AB.↑ inj₁) (AB.conns→ (inj₂ ((_ , _ , e) , i)))
      conns→ (inj₂ ((_ , _ , inj₂ e) , i)) = Sum.map (raise   (len B)) (CD.↑ inj₂) (CD.conns→ (inj₂ ((_ , _ , e) , i)))
      conns← : _
      conns← (inj₁ i) = [ ((Sum.map (inject+ (len C)) (AB.↑′ inj₁)) ∘ AB.conns← ∘ inj₁)
                         , ((Sum.map (raise   (len A)) (CD.↑′ inj₂)) ∘ CD.conns← ∘ inj₁)
                         ]′ (splitAt (len B) i)
      conns← (inj₂ ((_ , _ , inj₁ e) , i)) = Sum.map (inject+ (len C)) (AB.↑′ inj₁) (AB.conns← (inj₂ ((_ , _ , e) , i)))
      conns← (inj₂ ((_ , _ , inj₂ e) , i)) = Sum.map (raise   (len A)) (CD.↑′ inj₂) (CD.conns← (inj₂ ((_ , _ , e) , i)))

      type-match : _
      type-match (inj₁ i) with (splitAt (len A) i) | (inspect (splitAt (len A)) i)
      type-match (inj₁ i)    | (inj₁ i₁) | [ i=i₁ ] with (AB.conns→ (inj₁ i₁)) | (inspect AB.conns→ (inj₁ i₁))
      type-match (inj₁ i)    | (inj₁ i₁) | [ i=i₁ ]    | (inj₁ j) | [ i=j ] = begin
        _ ≡⟨ lookup-splitAt (len A) (vec-of-list A) (vec-of-list C) i ⟩
        _ ≡⟨ cong [ _ , _ ]′ i=i₁ ⟩
        _ ≡⟨ AB.type-match (inj₁ i₁) ⟩
        _ ≡⟨ cong [ _ , _ ]′ i=j ⟩
        _ ≡˘⟨ lookup-++ˡ (vec-of-list B) (vec-of-list D) j ⟩
        _ ∎
      type-match (inj₁ i)    | (inj₁ i₁) | [ i=i₁ ]    | (inj₂ _) | [ i=j ] = begin
        _ ≡⟨ lookup-splitAt (len A) (vec-of-list A) (vec-of-list C) i ⟩
        _ ≡⟨ cong [ _ , _ ]′ i=i₁ ⟩
        _ ≡⟨ AB.type-match (inj₁ i₁) ⟩
        _ ≡⟨ cong [ _ , _ ]′ i=j ⟩
        _ ∎
      type-match (inj₁ i)    | (inj₂ i₂) | [ i=i₂ ] with (CD.conns→ (inj₁ i₂)) | (inspect CD.conns→ (inj₁ i₂))
      type-match (inj₁ i)    | (inj₂ i₂) | [ i=i₂ ]    | (inj₁ j) | [ i=j ] = begin
        _ ≡⟨ lookup-splitAt (len A) (vec-of-list A) (vec-of-list C) i ⟩
        _ ≡⟨ cong [ _ , _ ]′ i=i₂ ⟩
        _ ≡⟨ CD.type-match (inj₁ i₂) ⟩
        _ ≡⟨ cong [ _ , _ ]′ i=j ⟩
        _ ≡˘⟨ lookup-++ʳ (vec-of-list B) (vec-of-list D) j ⟩
        _ ∎
      type-match (inj₁ i)    | (inj₂ i₂) | [ i=i₂ ]    | (inj₂ _) | [ i=j ] = begin
        _ ≡⟨ lookup-splitAt (len A) (vec-of-list A) (vec-of-list C) i ⟩
        _ ≡⟨ cong [ _ , _ ]′ i=i₂ ⟩
        _ ≡⟨ CD.type-match (inj₁ i₂) ⟩
        _ ≡⟨ cong [ _ , _ ]′ i=j ⟩
        _ ∎
      type-match (inj₂ ((_ , _ , inj₁ e) , i)) with (AB.conns→ (inj₂ ((_ , _ , e) , i))) | (inspect AB.conns→ (inj₂ ((_ , _ , e) , i)))
      type-match (inj₂ ((_ , _ , inj₁ e) , i))    | (inj₁ j) | [ i=j ] = begin
        _ ≡⟨ AB.type-match (inj₂ ((_ , _ , e) , i)) ⟩
        _ ≡⟨ cong [ _ , _ ]′ i=j ⟩
        _ ≡˘⟨ lookup-++ˡ (vec-of-list B) (vec-of-list D) j ⟩
        _ ∎
      type-match (inj₂ ((_ , _ , inj₁ e) , i))    | (inj₂ _) | [ i=j ] = begin
        _ ≡⟨ AB.type-match (inj₂ ((_ , _ , e) , i)) ⟩
        _ ≡⟨ cong [ _ , _ ]′ i=j ⟩
        _ ∎
      type-match (inj₂ ((_ , _ , inj₂ e) , i)) with (CD.conns→ (inj₂ ((_ , _ , e) , i))) | (inspect CD.conns→ (inj₂ ((_ , _ , e) , i)))
      type-match (inj₂ ((_ , _ , inj₂ e) , i))    | (inj₁ j) | [ i=j ] = begin
        _ ≡⟨ CD.type-match (inj₂ ((_ , _ , e) , i)) ⟩
        _ ≡⟨ cong [ _ , _ ]′ i=j ⟩
        _ ≡˘⟨ lookup-++ʳ (vec-of-list B) (vec-of-list D) j ⟩
        _ ∎
      type-match (inj₂ ((_ , _ , inj₂ e) , i))    | (inj₂ _) | [ i=j ] = begin
        _ ≡⟨ CD.type-match (inj₂ ((_ , _ , e) , i)) ⟩
        _ ≡⟨ cong [ _ , _ ]′ i=j ⟩
        _ ∎

      bijection₁ : _
      bijection₁ (inj₁ i) with (splitAt (len B) i) | (inspect (splitAt (len B)) i)
      bijection₁ (inj₁ i)    | (inj₁ i₁) | [ i=i₁ ] with (AB.conns← (inj₁ i₁)) | (inspect AB.conns← (inj₁ i₁))
      bijection₁ (inj₁ i)    | (inj₁ i₁) | [ i=i₁ ]    | (inj₁ j) | [ i=j ]
        rewrite splitAt-inject+ (len A) (len C) j = begin
        _ ≡˘⟨ cong ((Sum.map (inject+ (len D)) (AB.↑ inj₁)) ∘ AB.conns→) i=j ⟩
        _ ≡⟨ cong (Sum.map _ _) (proj₁ AB.bijection (inj₁ i₁)) ⟩
        _ ≡˘⟨ cong (inj₁ ∘ [ _ , _ ]′) i=i₁ ⟩
        _ ≡⟨ cong inj₁ (inject+-raise-splitAt (len B) (len D) i) ⟩
        _ ∎
      bijection₁ (inj₁ i)    | (inj₁ i₁) | [ i=i₁ ]    | (inj₂ (_ , j)) | [ i=j ] = begin
        _ ≡˘⟨ cong ((Sum.map (inject+ (len D)) (AB.↑ inj₁)) ∘ AB.conns→) i=j ⟩
        _ ≡⟨ cong (Sum.map _ _) (proj₁ AB.bijection (inj₁ i₁)) ⟩
        _ ≡˘⟨ cong (inj₁ ∘ [ _ , _ ]′) i=i₁ ⟩
        _ ≡⟨ cong inj₁ (inject+-raise-splitAt (len B) (len D) i) ⟩
        _ ∎
      bijection₁ (inj₁ i)    | (inj₂ i₂) | [ i=i₂ ] with (CD.conns← (inj₁ i₂)) | (inspect CD.conns← (inj₁ i₂))
      bijection₁ (inj₁ i)    | (inj₂ i₂) | [ i=i₂ ]    | (inj₁ j) | [ i=j ]
        rewrite splitAt-raise (len A) (len C) j = begin
        _ ≡˘⟨ cong ((Sum.map (raise (len B)) (CD.↑ inj₂)) ∘ CD.conns→) i=j ⟩
        _ ≡⟨ cong (Sum.map _ _) (proj₁ CD.bijection (inj₁ i₂)) ⟩
        _ ≡˘⟨ cong (inj₁ ∘ [ _ , _ ]′) i=i₂ ⟩
        _ ≡⟨ cong inj₁ (inject+-raise-splitAt (len B) (len D) i) ⟩
        _ ∎
      bijection₁ (inj₁ i)    | (inj₂ i₂) | [ i=i₂ ]    | (inj₂ (_ , j)) | [ i=j ] = begin
        _ ≡˘⟨ cong ((Sum.map (raise (len B)) (CD.↑ inj₂)) ∘ CD.conns→) i=j ⟩
        _ ≡⟨ cong (Sum.map _ _) (proj₁ CD.bijection (inj₁ i₂)) ⟩
        _ ≡˘⟨ cong (inj₁ ∘ [ _ , _ ]′) i=i₂ ⟩
        _ ≡⟨ cong inj₁ (inject+-raise-splitAt (len B) (len D) i) ⟩
        _ ∎
      bijection₁ (inj₂ ((_ , _ , inj₁ e) , i)) with (AB.conns← (inj₂ ((_ , _ , e) , i))) | (inspect AB.conns← (inj₂ ((_ , _ , e) , i)))
      bijection₁ (inj₂ ((_ , _ , inj₁ e) , i))    | (inj₁ j) | [ i=j ]
        rewrite splitAt-inject+ (len A) (len C) j = begin
        _ ≡˘⟨ cong ((Sum.map (inject+ (len D)) (AB.↑ inj₁)) ∘ AB.conns→) i=j ⟩
        _ ≡⟨ cong (Sum.map _ _) (proj₁ AB.bijection (inj₂ ((_ , _ , e) , i))) ⟩
        _ ∎
      bijection₁ (inj₂ ((_ , _ , inj₁ e) , i))    | (inj₂ (_ , j)) | [ i=j ] = begin
        _ ≡˘⟨ cong ((Sum.map (inject+ (len D)) (AB.↑ inj₁)) ∘ AB.conns→) i=j ⟩
        _ ≡⟨ cong (Sum.map _ _) (proj₁ AB.bijection (inj₂ ((_ , _ , e) , i))) ⟩
        _ ∎
      bijection₁ (inj₂ ((_ , _ , inj₂ e) , i)) with (CD.conns← (inj₂ ((_ , _ , e) , i))) | (inspect CD.conns← (inj₂ ((_ , _ , e) , i)))
      bijection₁ (inj₂ ((_ , _ , inj₂ e) , i))    | (inj₁ j) | [ i=j ]
        rewrite splitAt-raise (len A) (len C) j = begin
        _ ≡˘⟨ cong ((Sum.map (raise (len B)) (CD.↑ inj₂)) ∘ CD.conns→) i=j ⟩
        _ ≡⟨ cong (Sum.map _ _) (proj₁ CD.bijection (inj₂ ((_ , _ , e) , i))) ⟩
        _ ∎
      bijection₁ (inj₂ ((_ , _ , inj₂ e) , i))    | (inj₂ (_ , j)) | [ i=j ] = begin
        _ ≡˘⟨ cong ((Sum.map (raise (len B)) (CD.↑ inj₂)) ∘ CD.conns→) i=j ⟩
        _ ≡⟨ cong (Sum.map _ _) (proj₁ CD.bijection (inj₂ ((_ , _ , e) , i))) ⟩
        _ ∎

      bijection₂ : _
      bijection₂ (inj₁ i) with (splitAt (len A) i) | (inspect (splitAt (len A)) i)
      bijection₂ (inj₁ i)    | (inj₁ i₁) | [ i=i₁ ] with (AB.conns→ (inj₁ i₁)) | (inspect AB.conns→ (inj₁ i₁))
      bijection₂ (inj₁ i)    | (inj₁ i₁) | [ i=i₁ ]    | (inj₁ j) | [ i=j ]
        rewrite splitAt-inject+ (len B) (len D) j = begin
        _ ≡˘⟨ cong ((Sum.map (inject+ (len C)) (AB.↑′ inj₁)) ∘ AB.conns←) i=j ⟩
        _ ≡⟨ cong (Sum.map _ _) (proj₂ AB.bijection (inj₁ i₁)) ⟩
        _ ≡˘⟨ cong (inj₁ ∘ [ _ , _ ]′) i=i₁ ⟩
        _ ≡⟨ cong inj₁ (inject+-raise-splitAt (len A) (len C) i) ⟩
        _ ∎
      bijection₂ (inj₁ i)    | (inj₁ i₁) | [ i=i₁ ]    | (inj₂ (_ , j)) | [ i=j ] = begin
        _ ≡˘⟨ cong ((Sum.map (inject+ (len C)) (AB.↑′ inj₁)) ∘ AB.conns←) i=j ⟩
        _ ≡⟨ cong (Sum.map _ _) (proj₂ AB.bijection (inj₁ i₁)) ⟩
        _ ≡˘⟨ cong (inj₁ ∘ [ _ , _ ]′) i=i₁ ⟩
        _ ≡⟨ cong inj₁ (inject+-raise-splitAt (len A) (len C) i) ⟩
        _ ∎
      bijection₂ (inj₁ i)    | (inj₂ i₂) | [ i=i₂ ] with (CD.conns→ (inj₁ i₂)) | (inspect CD.conns→ (inj₁ i₂))
      bijection₂ (inj₁ i)    | (inj₂ i₂) | [ i=i₂ ]    | (inj₁ j) | [ i=j ]
        rewrite splitAt-raise (len B) (len D) j = begin
        _ ≡˘⟨ cong ((Sum.map (raise (len A)) (CD.↑′ inj₂)) ∘ CD.conns←) i=j ⟩
        _ ≡⟨ cong (Sum.map _ _) (proj₂ CD.bijection (inj₁ i₂)) ⟩
        _ ≡˘⟨ cong (inj₁ ∘ [ _ , _ ]′) i=i₂ ⟩
        _ ≡⟨ cong inj₁ (inject+-raise-splitAt (len A) (len C) i) ⟩
        _ ∎
      bijection₂ (inj₁ i)    | (inj₂ i₂) | [ i=i₂ ]    | (inj₂ (_ , j)) | [ i=j ] = begin
        _ ≡˘⟨ cong ((Sum.map (raise (len A)) (CD.↑′ inj₂)) ∘ CD.conns←) i=j ⟩
        _ ≡⟨ cong (Sum.map _ _) (proj₂ CD.bijection (inj₁ i₂)) ⟩
        _ ≡˘⟨ cong (inj₁ ∘ [ _ , _ ]′) i=i₂ ⟩
        _ ≡⟨ cong inj₁ (inject+-raise-splitAt (len A) (len C) i) ⟩
        _ ∎
      bijection₂ (inj₂ ((_ , _ , inj₁ e) , i)) with (AB.conns→ (inj₂ ((_ , _ , e) , i))) | (inspect AB.conns→ (inj₂ ((_ , _ , e) , i)))
      bijection₂ (inj₂ ((_ , _ , inj₁ e) , i))    | (inj₁ j) | [ i=j ]
        rewrite splitAt-inject+ (len B) (len D) j = begin
        _ ≡˘⟨ cong ((Sum.map (inject+ (len C)) (AB.↑′ inj₁)) ∘ AB.conns←) i=j ⟩
        _ ≡⟨ cong (Sum.map _ _) (proj₂ AB.bijection (inj₂ ((_ , _ , e) , i))) ⟩
        _ ∎
      bijection₂ (inj₂ ((_ , _ , inj₁ e) , i))    | (inj₂ (_ , j)) | [ i=j ] = begin
        _ ≡˘⟨ cong ((Sum.map (inject+ (len C)) (AB.↑′ inj₁)) ∘ AB.conns←) i=j ⟩
        _ ≡⟨ cong (Sum.map _ _) (proj₂ AB.bijection (inj₂ ((_ , _ , e) , i))) ⟩
        _ ∎
      bijection₂ (inj₂ ((_ , _ , inj₂ e) , i)) with (CD.conns→ (inj₂ ((_ , _ , e) , i))) | (inspect CD.conns→ (inj₂ ((_ , _ , e) , i)))
      bijection₂ (inj₂ ((_ , _ , inj₂ e) , i))    | (inj₁ j) | [ i=j ]
        rewrite splitAt-raise (len B) (len D) j = begin
        _ ≡˘⟨ cong ((Sum.map (raise (len A)) (CD.↑′ inj₂)) ∘ CD.conns←) i=j ⟩
        _ ≡⟨ cong (Sum.map _ _) (proj₂ CD.bijection (inj₂ ((_ , _ , e) , i))) ⟩
        _ ∎
      bijection₂ (inj₂ ((_ , _ , inj₂ e) , i))    | (inj₂ (_ , j)) | [ i=j ] = begin
        _ ≡˘⟨ cong ((Sum.map (raise (len A)) (CD.↑′ inj₂)) ∘ CD.conns←) i=j ⟩
        _ ≡⟨ cong (Sum.map _ _) (proj₂ CD.bijection (inj₂ ((_ , _ , e) , i))) ⟩
        _ ∎

      bijection : _
      bijection = bijection₁ , bijection₂

  record SimpleDiagram (input : List VLabel) (output : List VLabel) : Set (lsuc l ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) where
    field
      diagram : Diagram input output

    open Diagram diagram public

    _≲_ : Rel (Σ₂ _ _ E) _
    e₁ ≲ e₂ = ∃ λ i₁ → ∃ λ i₂ → conns→ (inj₂ (e₁ , i₁)) ≡ inj₂ (e₂ , i₂)

    field
      partial-order : IsPartialOrder _≡_ _≲_

    module edge-order = IsPartialOrder partial-order

module _ where
  open Core {ℓ₁}

  -- the singleton diagram
  ⟦_⟧ : ∀ {s t} → ELabel s t → Diagram s t
  ⟦_⟧ {s} {t} x = record
    { E = λ s′ t′ → (s ≡ s′) × (t ≡ t′)
    ; conns→ = λ { (inj₁ i) → inj₂ ((s , t , refl , refl) , i)
                  ; (inj₂ ((_ , _ , refl , refl) , i)) → inj₁ i
                  }
    ; conns← = λ { (inj₁ i) → inj₂ ((s , t , refl , refl) , i)
                  ; (inj₂ ((_ , _ , refl , refl) , i)) → inj₁ i
                  }
    ; type-match = λ { (inj₁ i) → refl
                     ; (inj₂ ((_ , _ , refl , refl) , i)) → refl
                     }
    ; bijection = (λ
                    { (inj₁ i) → refl
                    ; (inj₂ ((_ , _ , refl , refl) , i)) → refl
                    }
                  ) , (λ
                    { (inj₁ i) → refl
                    ; (inj₂ ((_ , _ , refl , refl) , i)) → refl
                    }
                  )
    ; o = λ {(refl , refl) → x}
    }

  ⟦⟧-cong : ∀ {s t} {f g : ELabel s t} → f E.≈ g → ⟦ f ⟧ ≋ ⟦ g ⟧
  ⟦⟧-cong fg = record
    { α = id
    ; α′ = id
    ; bijection = (λ _ → refl) , (λ _ → refl)
    ; obj-resp = λ {(refl , refl) → fg}
    ; conns→-resp = λ
        { (inj₁ _) → refl
        ; (inj₂ ((_ , _ , refl , refl) , _)) → refl
        }
    }
