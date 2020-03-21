{-# OPTIONS --without-K --safe #-}

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
open import Function using (_∘_; Inverseᵇ; id)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open import Nets.Utils

module Nets.Hypergraph {ℓₜ ℓₜᵣ : Level}
                       (VLabel-setoid : Setoid ℓₜ ℓₜᵣ)
                       {ℓₒ ℓₒᵣ : Level}
                       (ELabel-setoid :
                         List (Setoid.Carrier VLabel-setoid) →
                         List (Setoid.Carrier VLabel-setoid) →
                         Setoid ℓₒ ℓₒᵣ)
                       where

-- bringing the contents of the setoids into scope as VLabel._≈_ or ELabel._≈_ etc.
module VLabel = Setoid VLabel-setoid
VLabel = VLabel.Carrier

module ELabel {input : _} {output : _} = Setoid (ELabel-setoid input output)
ELabel = ELabel.Carrier

module Core {l : Level} where

  infix 4 _≋[_][_]_

  record Hypergraph (input : List VLabel) (output : List VLabel) : Set ((lsuc l) ⊔ ℓₜ ⊔ ℓₜᵣ ⊔ ℓₒ) where
    field
      E : List VLabel → List VLabel → Set l

    Edge : Set (ℓₜ ⊔ l)
    Edge = Σ₂ (List VLabel) (List VLabel) E

    -- input of the edge (s for source)
    s : Edge → List VLabel
    s = proj₁

    -- output of the edge (t for target)
    t : Edge → List VLabel
    t = proj₁ ∘ proj₂

    -- type representing the ports that arrows go into
    in-index  = (Fin (len output)) ⊎ (Σ Edge (Fin ∘ len ∘ s))
    -- type representing the ports that arrows go out of
    out-index = (Fin (len input))  ⊎ (Σ Edge (Fin ∘ len ∘ t))

    in-lookup  : in-index  → VLabel
    in-lookup  = [ lookup (vec-of-list output) , (λ {((s , _ , e) , i) → lookup (vec-of-list s) i})]′

    out-lookup : out-index → VLabel
    out-lookup = [ lookup (vec-of-list input)  , (λ {((_ , t , e) , i) → lookup (vec-of-list t) i})]′

    field
      conns→ : out-index → in-index
      conns← : in-index → out-index
      type-match : (i : out-index) → out-lookup i VLabel.≈ in-lookup (conns→ i)
      bijection : Inverseᵇ _≡_ _≡_ conns→ conns←

    bijection₁ = proj₁ bijection
    bijection₂ = proj₂ bijection

    field
      -- the label associated with each box
      o : ∀ {input output} → E input output → ELabel {input} {output}


  -- hypergraph isomorphism

  -- defining the isomorphism heterogenously saves us a lot of trouble later on
  record _≋[_][_]_ {A B A′ B′ : List VLabel} (LHS : Hypergraph A B) (A≡A′ : A ≡ A′) (B≡B′ : B ≡ B′) (RHS : Hypergraph A′ B′) : Set (l ⊔ ℓₜ ⊔ ℓₜᵣ ⊔ ℓₒ ⊔ ℓₒᵣ) where
    module LHS = Hypergraph LHS
    module RHS = Hypergraph RHS
    field
      α : ∀ {input output} → LHS.E input output → RHS.E input output
      α′ : ∀ {input output} → RHS.E input output → LHS.E input output

      bijection : ∀ {input output} → Inverseᵇ _≡_ _≡_ (α {input} {output}) (α′)
      obj-resp : ∀ {input output} → (e : LHS.E input output) → (LHS.o e) ELabel.≈ (RHS.o (α e))

    α-in-index :  LHS.in-index  → RHS.in-index
    α-in-index  = Sum.map (subst (Fin ∘ len) B≡B′) (λ {((_ , _ , e) , i) → (_ , _ , α e) , i})
    α-out-index : LHS.out-index → RHS.out-index
    α-out-index = Sum.map (subst (Fin ∘ len) A≡A′) (λ {((_ , _ , e) , i) → (_ , _ , α e) , i})

    field
      conns→-resp : (i : LHS.out-index) →
                     RHS.conns→ (α-out-index i) ≡ α-in-index (LHS.conns→ i)
      -- this one is redundant
      -- conns←-resp : {i : LHS.in-index} →
      --                RHS.conns← (α-in-index i) ≡ α-out-index (LHS.conns← i)

  -- the homogenous version of the hypergraph isomorphism
  _≋_ : ∀ {A B : List VLabel} → Rel (Hypergraph A B) (l ⊔ ℓₜ ⊔ ℓₜᵣ ⊔ ℓₒ ⊔ ℓₒᵣ)
  _≋_ = _≋[ refl ][ refl ]_

  module _≋_ = _≋[_][_]_


  ≋[][]→≋ : ∀ {A B A′ B′ : List VLabel} {LHS : Hypergraph A B} {A≡A′ : A ≡ A′} {B≡B′ : B ≡ B′} {RHS : Hypergraph A′ B′} →
             LHS ≋[ A≡A′ ][ B≡B′ ] RHS → subst₂ Hypergraph A≡A′ B≡B′ LHS ≋ RHS
  ≋[][]→≋ {A≡A′ = refl} {refl} l=r = l=r


  -- hypergraph composition
  _⊚_ : ∀ {A B C : List VLabel} → Hypergraph B C → Hypergraph A B → Hypergraph A C
  BC ⊚ AB = record
    { E = E
    ; conns→ = conns→
    ; conns← = conns←
    ; type-match = type-match
    ; bijection = bijection
    ; o = [ AB.o , BC.o ]′
    }
    where
      module AB = Hypergraph AB
      module BC = Hypergraph BC

      E : _
      E input output = (AB.E input output) ⊎ (BC.E input output)

      -- →
      conns→ : _
      conns→ (inj₁ i) =
        [ (λ j →
            Sum.map₂
              (λ {((_ , _ , e) , k) → (_ , _ , inj₂ e) , k})
              (BC.conns→ (inj₁ j))
          )
        , (λ {((_ , _ , e) , j) → inj₂ ((_ , _ , inj₁ e) , j)})
        ]′ (AB.conns→ (inj₁ i))
      conns→ (inj₂ ((_ , _ , inj₁ e) , i)) =
        [ (λ j →
            Sum.map₂
              (λ {((_ , _ , e) , k) → (_ , _ , inj₂ e) , k})
              (BC.conns→ (inj₁ j))
          )
        , (λ {((_ , _ , e) , j) → inj₂ ((_ , _ , inj₁ e) , j)})
        ]′ (AB.conns→ (inj₂ ((_ , _ , e) , i)))
      conns→ (inj₂ ((_ , _ , inj₂ e) , j)) =
        Sum.map₂
          (λ {((_ , _ , e) , k) → (_ , _ , inj₂ e) , k})
          (BC.conns→ (inj₂ ((_ , _ , e) , j)))

      -- ←
      conns← : _
      conns← (inj₁ i) =
        [ (λ j →
            Sum.map₂
              (λ {((_ , _ , e) , k) → (_ , _ , inj₁ e) , k})
              (AB.conns← (inj₁ j))
          )
        , (λ {((_ , _ , e) , j) → inj₂ ((_ , _ , inj₂ e) , j)})
        ]′ (BC.conns← (inj₁ i))
      conns← (inj₂ ((_ , _ , inj₁ e) , j)) =
        Sum.map₂
          (λ {((_ , _ , e) , k) → (_ , _ , inj₁ e) , k})
          (AB.conns← (inj₂ ((_ , _ , e) , j)))
      conns← (inj₂ ((_ , _ , inj₂ e) , i)) =
        [ (λ j →
            Sum.map₂
              (λ {((_ , _ , e) , k) → (_ , _ , inj₁ e) , k})
              (AB.conns← (inj₁ j))
          )
        , (λ {((_ , _ , e) , j) → inj₂ ((_ , _ , inj₂ e) , j)})
        ]′ (BC.conns← (inj₂ ((_ , _ , e) , i)))

      --properties
      type-match : _
      type-match = type-match′
        where
          open SetoidReasoning VLabel-setoid
          type-match′ : _
          type-match′ (inj₁ i) with (AB.conns→ (inj₁ i)) | (inspect AB.conns→ (inj₁ i))
          type-match′ (inj₁ i) | (inj₁ j) | [ i→j ] with (BC.conns→ (inj₁ j)) | (inspect BC.conns→ (inj₁ j))
          type-match′ (inj₁ i) | (inj₁ j) | [ i→j ] | (inj₁ _) | [ j→k ] = begin
            _ ≈⟨ AB.type-match (inj₁ i) ⟩
            _ ≡⟨ cong [ _ , _ ]′ i→j ⟩
            _ ≈⟨ BC.type-match (inj₁ j) ⟩
            _ ≡⟨ cong [ _ , _ ]′ j→k ⟩
            _ ∎
          type-match′ (inj₁ i) | (inj₁ j) | [ i→j ] | (inj₂ _) | [ j→k ] = begin
            _ ≈⟨ AB.type-match (inj₁ i) ⟩
            _ ≡⟨ cong [ _ , _ ]′ i→j ⟩
            _ ≈⟨ BC.type-match (inj₁ j) ⟩
            _ ≡⟨ cong [ _ , _ ]′ j→k ⟩
            _ ∎
          type-match′ (inj₁ i) | (inj₂ _) | [ i→j ] = begin
            _ ≈⟨ AB.type-match (inj₁ i) ⟩
            _ ≡⟨ cong [ _ , _ ]′ i→j ⟩
            _ ∎
          type-match′ (inj₂ ((_ , _ , inj₁ e) , i)) with (AB.conns→ (inj₂ ((_ , _ , e) , i))) | (inspect AB.conns→ (inj₂ ((_ , _ , e) , i)))
          type-match′ (inj₂ ((_ , _ , inj₁ e) , i)) | (inj₁ j) | [ i→j ] with (BC.conns→ (inj₁ j)) | (inspect BC.conns→ (inj₁ j))
          type-match′ (inj₂ ((_ , _ , inj₁ e) , i)) | (inj₁ j) | [ i→j ] | (inj₁ _) | [ j→k ] = begin
            _ ≈⟨ AB.type-match (inj₂ ((_ , _ , e) , i)) ⟩
            _ ≡⟨ cong [ _ , _ ]′ i→j ⟩
            _ ≈⟨ BC.type-match (inj₁ j) ⟩
            _ ≡⟨ cong [ _ , _ ]′ j→k ⟩
            _ ∎
          type-match′ (inj₂ ((_ , _ , inj₁ e) , i)) | (inj₁ j) | [ i→j ] | (inj₂ _) | [ j→k ] = begin
            _ ≈⟨ AB.type-match (inj₂ ((_ , _ , e) , i)) ⟩
            _ ≡⟨ cong [ _ , _ ]′ i→j ⟩
            _ ≈⟨ BC.type-match (inj₁ j) ⟩
            _ ≡⟨ cong [ _ , _ ]′ j→k ⟩
            _ ∎
          type-match′ (inj₂ ((_ , _ , inj₁ e) , i)) | (inj₂ _) | [ i→j ] = begin
            _ ≈⟨ AB.type-match (inj₂ ((_ , _ , e) , i)) ⟩
            _ ≡⟨ cong [ _ , _ ]′ i→j ⟩
            _ ∎
          type-match′ (inj₂ ((_ , _ , inj₂ e) , i)) with (BC.conns→ (inj₂ ((_ , _ , e) , i))) | (inspect BC.conns→ (inj₂ ((_ , _ , e) , i)))
          type-match′ (inj₂ ((_ , _ , inj₂ e) , i)) | (inj₁ _) | [ i→j ] = begin
            _ ≈⟨ BC.type-match (inj₂ ((_ , _ , e) , i)) ⟩
            _ ≡⟨ cong [ _ , _ ]′ i→j ⟩
            _ ∎
          type-match′ (inj₂ ((_ , _ , inj₂ e) , i)) | (inj₂ _) | [ i→j ] = begin
            _ ≈⟨ BC.type-match (inj₂ ((_ , _ , e) , i)) ⟩
            _ ≡⟨ cong [ _ , _ ]′ i→j ⟩
            _ ∎

      bijection₁ : _
      bijection₁ = bijection₁′
        where
          open ≡-Reasoning
          bijection₁′ : _
          bijection₁′ (inj₁ i) with (BC.conns← (inj₁ i)) | (inspect BC.conns← (inj₁ i))
          bijection₁′ (inj₁ i) | (inj₁ j) | [ i→j ] with (AB.conns← (inj₁ j)) | (inspect AB.conns← (inj₁ j))
          bijection₁′ (inj₁ i) | (inj₁ j) | [ i→j ] | (inj₁ _) | [ j→k ] = trans
            (cong [ _ , _ ]′
              (begin
              _ ≡⟨ cong AB.conns→ (sym j→k) ⟩
              _ ≡⟨ AB.bijection₁ (inj₁ j) ⟩
              _ ∎))
            (cong (Sum.map₂ _)
              (begin
              _ ≡⟨ cong BC.conns→ (sym i→j) ⟩
              _ ≡⟨ BC.bijection₁ (inj₁ i) ⟩
              _ ∎))
          bijection₁′ (inj₁ i) | (inj₁ j) | [ i→j ] | (inj₂ _) | [ j→k ] = trans
            (cong [ _ , _ ]′
              (begin
              _ ≡⟨ cong AB.conns→ (sym j→k) ⟩
              _ ≡⟨ AB.bijection₁ (inj₁ j) ⟩
              _ ∎))
            (cong (Sum.map₂ _)
              (begin
              _ ≡⟨ cong BC.conns→ (sym i→j) ⟩
              _ ≡⟨ BC.bijection₁ (inj₁ i) ⟩
              _ ∎))
          bijection₁′ (inj₁ i) | (inj₂ _) | [ i→j ] =
            cong (Sum.map₂ _)
              (begin
              _ ≡⟨ cong BC.conns→ (sym i→j) ⟩
              _ ≡⟨ BC.bijection₁ (inj₁ i) ⟩
              _ ∎)
          bijection₁′ (inj₂ ((_ , _ , inj₁ e) , i)) with (AB.conns← (inj₂ ((_ , _ , e) , i))) | (inspect AB.conns← (inj₂ ((_ , _ , e) , i)))
          bijection₁′ (inj₂ ((_ , _ , inj₁ e) , i)) | (inj₁ _) | [ i→j ] =
            cong [ _ , _ ]′
              (begin
              _ ≡⟨ cong AB.conns→ (sym i→j) ⟩
              _ ≡⟨ AB.bijection₁ (inj₂ ((_ , _ , e) , i)) ⟩
              _ ∎)
          bijection₁′ (inj₂ ((_ , _ , inj₁ e) , i)) | (inj₂ _) | [ i→j ] =
            cong [ _ , _ ]′
              (begin
              _ ≡⟨ cong AB.conns→ (sym i→j) ⟩
              _ ≡⟨ AB.bijection₁ (inj₂ ((_ , _ , e) , i)) ⟩
              _ ∎)
          bijection₁′ (inj₂ ((_ , _ , inj₂ e) , i)) with (BC.conns← (inj₂ ((_ , _ , e) , i))) | (inspect BC.conns← (inj₂ ((_ , _ , e) , i)))
          bijection₁′ (inj₂ ((_ , _ , inj₂ e) , i)) | (inj₁ j) | [ i→j ] with (AB.conns← (inj₁ j)) | (inspect AB.conns← (inj₁ j))
          bijection₁′ (inj₂ ((_ , _ , inj₂ e) , i)) | (inj₁ j) | [ i→j ] | (inj₁ _) | [ j→k ] = trans
            (cong [ _ , _ ]′
              (begin
              _ ≡⟨ cong AB.conns→ (sym j→k) ⟩
              _ ≡⟨ AB.bijection₁ (inj₁ j) ⟩
              _ ∎))
            (cong (Sum.map₂ _)
              (begin
              _ ≡⟨ cong BC.conns→ (sym i→j) ⟩
              _ ≡⟨ BC.bijection₁ (inj₂ ((_ , _ , e) , i)) ⟩
              _ ∎))
          bijection₁′ (inj₂ ((_ , _ , inj₂ e) , i)) | (inj₁ j) | [ i→j ] | (inj₂ _) | [ j→k ] = trans
            (cong [ _ , _ ]′
              (begin
              _ ≡⟨ cong AB.conns→ (sym j→k) ⟩
              _ ≡⟨ AB.bijection₁ (inj₁ j) ⟩
              _ ∎))
            (cong (Sum.map₂ _)
              (begin
              _ ≡⟨ cong BC.conns→ (sym i→j) ⟩
              _ ≡⟨ BC.bijection₁ (inj₂ ((_ , _ , e) , i)) ⟩
              _ ∎))
          bijection₁′ (inj₂ ((_ , _ , inj₂ e) , i)) | (inj₂ _) | [ i→j ] =
            cong (Sum.map₂ _)
              (begin
              _ ≡⟨ cong BC.conns→ (sym i→j) ⟩
              _ ≡⟨ BC.bijection₁ (inj₂ ((_ , _ , e) , i)) ⟩
              _ ∎)

      bijection₂ : _
      bijection₂ = bijection₂′
        where
          open ≡-Reasoning
          bijection₂′ : _
          bijection₂′ (inj₁ i) with (AB.conns→ (inj₁ i)) | (inspect AB.conns→ (inj₁ i))
          bijection₂′ (inj₁ i) | (inj₁ j) | [ i→j ] with (BC.conns→ (inj₁ j)) | (inspect BC.conns→ (inj₁ j))
          bijection₂′ (inj₁ i) | (inj₁ j) | [ i→j ] | (inj₁ _) | [ j→k ] = trans
            (cong [ _ , _ ]′
              (begin
              _ ≡⟨ cong BC.conns← (sym j→k) ⟩
              _ ≡⟨ BC.bijection₂ (inj₁ j) ⟩
              _ ∎))
            (cong (Sum.map₂ _)
              (begin
              _ ≡⟨ cong AB.conns← (sym i→j) ⟩
              _ ≡⟨ AB.bijection₂ (inj₁ i) ⟩
              _ ∎))
          bijection₂′ (inj₁ i) | (inj₁ j) | [ i→j ] | (inj₂ _) | [ j→k ] = trans
            (cong [ _ , _ ]′
              (begin
              _ ≡⟨ cong BC.conns← (sym j→k) ⟩
              _ ≡⟨ BC.bijection₂ (inj₁ j) ⟩
              _ ∎))
            (cong (Sum.map₂ _)
              (begin
              _ ≡⟨ cong AB.conns← (sym i→j) ⟩
              _ ≡⟨ AB.bijection₂ (inj₁ i) ⟩
              _ ∎))
          bijection₂′ (inj₁ i) | (inj₂ _) | [ i→j ] =
            cong (Sum.map₂ _)
              (begin
              _ ≡⟨ cong AB.conns← (sym i→j) ⟩
              _ ≡⟨ AB.bijection₂ (inj₁ i) ⟩
              _ ∎)
          bijection₂′ (inj₂ ((_ , _ , inj₁ e) , i)) with (AB.conns→ (inj₂ ((_ , _ , e) , i))) | (inspect AB.conns→ (inj₂ ((_ , _ , e) , i)))
          bijection₂′ (inj₂ ((_ , _ , inj₁ e) , i)) | (inj₁ j) | [ i→j ] with (BC.conns→ (inj₁ j)) | (inspect BC.conns→ (inj₁ j))
          bijection₂′ (inj₂ ((_ , _ , inj₁ e) , i)) | (inj₁ j) | [ i→j ] | (inj₁ _) | [ j→k ] = trans
            (cong [ _ , _ ]′
              (begin
              _ ≡⟨ cong BC.conns← (sym j→k) ⟩
              _ ≡⟨ BC.bijection₂ (inj₁ j) ⟩
              _ ∎))
            (cong (Sum.map₂ _)
              (begin
              _ ≡⟨ cong AB.conns← (sym i→j) ⟩
              _ ≡⟨ AB.bijection₂ (inj₂ ((_ , _ , e) , i)) ⟩
              _ ∎))
          bijection₂′ (inj₂ ((_ , _ , inj₁ e) , i)) | (inj₁ j) | [ i→j ] | (inj₂ _) | [ j→k ] = trans
            (cong [ _ , _ ]′
              (begin
              _ ≡⟨ cong BC.conns← (sym j→k) ⟩
              _ ≡⟨ BC.bijection₂ (inj₁ j) ⟩
              _ ∎))
            (cong (Sum.map₂ _)
              (begin
              _ ≡⟨ cong AB.conns← (sym i→j) ⟩
              _ ≡⟨ AB.bijection₂ (inj₂ ((_ , _ , e) , i)) ⟩
              _ ∎))
          bijection₂′ (inj₂ ((_ , _ , inj₁ e) , i)) | (inj₂ _) | [ i→j ] =
            cong (Sum.map₂ _)
              (begin
              _ ≡⟨ cong AB.conns← (sym i→j) ⟩
              _ ≡⟨ AB.bijection₂ (inj₂ ((_ , _ , e) , i)) ⟩
              _ ∎)
          bijection₂′ (inj₂ ((_ , _ , inj₂ e) , i)) with (BC.conns→ (inj₂ ((_ , _ , e) , i))) | (inspect BC.conns→ (inj₂ ((_ , _ , e) , i)))
          bijection₂′ (inj₂ ((_ , _ , inj₂ e) , i)) | (inj₁ _) | [ i→j ] =
            cong [ _ , _ ]′
              (begin
              _ ≡⟨ cong BC.conns← (sym i→j) ⟩
              _ ≡⟨ BC.bijection₂ (inj₂ ((_ , _ , e) , i)) ⟩
              _ ∎)
          bijection₂′ (inj₂ ((_ , _ , inj₂ e) , i)) | (inj₂ _) | [ i→j ] =
            cong [ _ , _ ]′
              (begin
              _ ≡⟨ cong BC.conns← (sym i→j) ⟩
              _ ≡⟨ BC.bijection₂ (inj₂ ((_ , _ , e) , i)) ⟩
              _ ∎)
      bijection : _
      bijection = bijection₁ , bijection₂

  _⊚[_]_ : ∀ {A B C D : List VLabel} → Hypergraph C D → B ≡ C → Hypergraph A B → Hypergraph A D
  f ⊚[ eq ] g rewrite eq = f ⊚ g

  ⊚[]≡⊚ : ∀ {A B C D : List VLabel} → (f : Hypergraph C D) → (BC : B ≡ C) → (g : Hypergraph A B) → f ⊚[ BC ] g ≡ f ⊚ (subst (Hypergraph A) BC g)
  ⊚[]≡⊚ f refl g = refl

  -- Hypergraph tensor product
  _⨂_ : ∀ {A B C D : List VLabel} → Hypergraph A B → Hypergraph C D → Hypergraph (A ⊕ C) (B ⊕ D)
  _⨂_ {A} {B} {C} {D} AB CD = record
    { E = E
    ; conns→ = conns→
    ; conns← = conns←
    ; type-match = type-match
    ; bijection = bijection
    ; o = [ AB.o , CD.o ]′
    }
    where
      module AB = Hypergraph AB
      module CD = Hypergraph CD

      E : _
      E input output = (AB.E input output) ⊎ (CD.E input output)

      conns→ : _
      conns→ (inj₁ i) = [ ((Sum.map (inject+ (len D)) (λ {((_ , _ , f) , j) → (_ , _ , inj₁ f) , j})) ∘ AB.conns→ ∘ inj₁)
                         , ((Sum.map (raise   (len B)) (λ {((_ , _ , f) , j) → (_ , _ , inj₂ f) , j})) ∘ CD.conns→ ∘ inj₁)
                         ]′ (splitAt (len A) i)
      conns→ (inj₂ ((_ , _ , inj₁ e) , i)) = Sum.map (inject+ (len D)) (λ {((_ , _ , f) , j) → (_ , _ , inj₁ f) , j}) (AB.conns→ (inj₂ ((_ , _ , e) , i)))
      conns→ (inj₂ ((_ , _ , inj₂ e) , i)) = Sum.map (raise   (len B)) (λ {((_ , _ , f) , j) → (_ , _ , inj₂ f) , j}) (CD.conns→ (inj₂ ((_ , _ , e) , i)))
      conns← : _
      conns← (inj₁ i) = [ ((Sum.map (inject+ (len C)) (λ {((_ , _ , f) , j) → (_ , _ , inj₁ f) , j})) ∘ AB.conns← ∘ inj₁)
                         , ((Sum.map (raise   (len A)) (λ {((_ , _ , f) , j) → (_ , _ , inj₂ f) , j})) ∘ CD.conns← ∘ inj₁)
                         ]′ (splitAt (len B) i)
      conns← (inj₂ ((_ , _ , inj₁ e) , i)) = Sum.map (inject+ (len C)) (λ {((_ , _ , f) , j) → (_ , _ , inj₁ f) , j}) (AB.conns← (inj₂ ((_ , _ , e) , i)))
      conns← (inj₂ ((_ , _ , inj₂ e) , i)) = Sum.map (raise   (len A)) (λ {((_ , _ , f) , j) → (_ , _ , inj₂ f) , j}) (CD.conns← (inj₂ ((_ , _ , e) , i)))

      type-match : _
      type-match = type-match'
        where
          open SetoidReasoning VLabel-setoid
          type-match' : _
          type-match' (inj₁ i) with (splitAt (len A) i) | (inspect (splitAt (len A)) i)
          type-match' (inj₁ i)    | (inj₁ i₁) | [ i=i₁ ] with (AB.conns→ (inj₁ i₁)) | (inspect AB.conns→ (inj₁ i₁))
          type-match' (inj₁ i)    | (inj₁ i₁) | [ i=i₁ ]    | (inj₁ j) | [ i=j ] = begin
            _ ≡⟨ lookup-splitAt (len A) (vec-of-list A) (vec-of-list C) i ⟩
            _ ≡⟨ cong [ _ , _ ]′ i=i₁ ⟩
            _ ≈⟨ AB.type-match (inj₁ i₁) ⟩
            _ ≡⟨ cong [ _ , _ ]′ i=j ⟩
            _ ≡˘⟨ lookup-++ˡ (vec-of-list B) (vec-of-list D) j ⟩
            _ ∎
          type-match' (inj₁ i)    | (inj₁ i₁) | [ i=i₁ ]    | (inj₂ _) | [ i=j ] = begin
            _ ≡⟨ lookup-splitAt (len A) (vec-of-list A) (vec-of-list C) i ⟩
            _ ≡⟨ cong [ _ , _ ]′ i=i₁ ⟩
            _ ≈⟨ AB.type-match (inj₁ i₁) ⟩
            _ ≡⟨ cong [ _ , _ ]′ i=j ⟩
            _ ∎
          type-match' (inj₁ i)    | (inj₂ i₂) | [ i=i₂ ] with (CD.conns→ (inj₁ i₂)) | (inspect CD.conns→ (inj₁ i₂))
          type-match' (inj₁ i)    | (inj₂ i₂) | [ i=i₂ ]    | (inj₁ j) | [ i=j ] = begin
            _ ≡⟨ lookup-splitAt (len A) (vec-of-list A) (vec-of-list C) i ⟩
            _ ≡⟨ cong [ _ , _ ]′ i=i₂ ⟩
            _ ≈⟨ CD.type-match (inj₁ i₂) ⟩
            _ ≡⟨ cong [ _ , _ ]′ i=j ⟩
            _ ≡˘⟨ lookup-++ʳ (vec-of-list B) (vec-of-list D) j ⟩
            _ ∎
          type-match' (inj₁ i)    | (inj₂ i₂) | [ i=i₂ ]    | (inj₂ _) | [ i=j ] = begin
            _ ≡⟨ lookup-splitAt (len A) (vec-of-list A) (vec-of-list C) i ⟩
            _ ≡⟨ cong [ _ , _ ]′ i=i₂ ⟩
            _ ≈⟨ CD.type-match (inj₁ i₂) ⟩
            _ ≡⟨ cong [ _ , _ ]′ i=j ⟩
            _ ∎
          type-match' (inj₂ ((_ , _ , inj₁ e) , i)) with (AB.conns→ (inj₂ ((_ , _ , e) , i))) | (inspect AB.conns→ (inj₂ ((_ , _ , e) , i)))
          type-match' (inj₂ ((_ , _ , inj₁ e) , i))    | (inj₁ j) | [ i=j ] = begin
            _ ≈⟨ AB.type-match (inj₂ ((_ , _ , e) , i)) ⟩
            _ ≡⟨ cong [ _ , _ ]′ i=j ⟩
            _ ≡˘⟨ lookup-++ˡ (vec-of-list B) (vec-of-list D) j ⟩
            _ ∎
          type-match' (inj₂ ((_ , _ , inj₁ e) , i))    | (inj₂ _) | [ i=j ] = begin
            _ ≈⟨ AB.type-match (inj₂ ((_ , _ , e) , i)) ⟩
            _ ≡⟨ cong [ _ , _ ]′ i=j ⟩
            _ ∎
          type-match' (inj₂ ((_ , _ , inj₂ e) , i)) with (CD.conns→ (inj₂ ((_ , _ , e) , i))) | (inspect CD.conns→ (inj₂ ((_ , _ , e) , i)))
          type-match' (inj₂ ((_ , _ , inj₂ e) , i))    | (inj₁ j) | [ i=j ] = begin
            _ ≈⟨ CD.type-match (inj₂ ((_ , _ , e) , i)) ⟩
            _ ≡⟨ cong [ _ , _ ]′ i=j ⟩
            _ ≡˘⟨ lookup-++ʳ (vec-of-list B) (vec-of-list D) j ⟩
            _ ∎
          type-match' (inj₂ ((_ , _ , inj₂ e) , i))    | (inj₂ _) | [ i=j ] = begin
            _ ≈⟨ CD.type-match (inj₂ ((_ , _ , e) , i)) ⟩
            _ ≡⟨ cong [ _ , _ ]′ i=j ⟩
            _ ∎

      bijection : _
      bijection = bijection₁ , bijection₂
        where
          bijection₁ : _
          bijection₁ (inj₁ i) with (splitAt (len B) i) | (inspect (splitAt (len B)) i)
          bijection₁ (inj₁ i)    | (inj₁ i₁) | [ i=i₁ ] with (AB.conns← (inj₁ i₁)) | (inspect AB.conns← (inj₁ i₁))
          bijection₁ (inj₁ i)    | (inj₁ i₁) | [ i=i₁ ]    | (inj₁ j) | [ i=j ]
            rewrite splitAt-inject+ (len A) (len C) j = begin
            _ ≡˘⟨ cong ((Sum.map (inject+ (len D)) (λ { ((_ , _ , f) , j) → (_ , _ , inj₁ f) , j })) ∘ AB.conns→) i=j ⟩
            _ ≡⟨ cong (Sum.map _ _) (proj₁ AB.bijection (inj₁ i₁)) ⟩
            _ ≡˘⟨ cong (inj₁ ∘ [ _ , _ ]′) i=i₁ ⟩
            _ ≡⟨ cong inj₁ (inject+-raise-splitAt (len B) (len D) i) ⟩
            _ ∎
            where open ≡-Reasoning
          bijection₁ (inj₁ i)    | (inj₁ i₁) | [ i=i₁ ]    | (inj₂ (_ , j)) | [ i=j ] = begin
            _ ≡˘⟨ cong ((Sum.map (inject+ (len D)) (λ { ((_ , _ , f) , j) → (_ , _ , inj₁ f) , j })) ∘ AB.conns→) i=j ⟩
            _ ≡⟨ cong (Sum.map _ _) (proj₁ AB.bijection (inj₁ i₁)) ⟩
            _ ≡˘⟨ cong (inj₁ ∘ [ _ , _ ]′) i=i₁ ⟩
            _ ≡⟨ cong inj₁ (inject+-raise-splitAt (len B) (len D) i) ⟩
            _ ∎
            where open ≡-Reasoning
          bijection₁ (inj₁ i)    | (inj₂ i₂) | [ i=i₂ ] with (CD.conns← (inj₁ i₂)) | (inspect CD.conns← (inj₁ i₂))
          bijection₁ (inj₁ i)    | (inj₂ i₂) | [ i=i₂ ]    | (inj₁ j) | [ i=j ]
            rewrite splitAt-raise (len A) (len C) j = begin
            _ ≡˘⟨ cong ((Sum.map (raise (len B)) (λ { ((_ , _ , f) , j) → (_ , _ , inj₂ f) , j })) ∘ CD.conns→) i=j ⟩
            _ ≡⟨ cong (Sum.map _ _) (proj₁ CD.bijection (inj₁ i₂)) ⟩
            _ ≡˘⟨ cong (inj₁ ∘ [ _ , _ ]′) i=i₂ ⟩
            _ ≡⟨ cong inj₁ (inject+-raise-splitAt (len B) (len D) i) ⟩
            _ ∎
            where open ≡-Reasoning
          bijection₁ (inj₁ i)    | (inj₂ i₂) | [ i=i₂ ]    | (inj₂ (_ , j)) | [ i=j ] = begin
            _ ≡˘⟨ cong ((Sum.map (raise (len B)) (λ { ((_ , _ , f) , j) → (_ , _ , inj₂ f) , j })) ∘ CD.conns→) i=j ⟩
            _ ≡⟨ cong (Sum.map _ _) (proj₁ CD.bijection (inj₁ i₂)) ⟩
            _ ≡˘⟨ cong (inj₁ ∘ [ _ , _ ]′) i=i₂ ⟩
            _ ≡⟨ cong inj₁ (inject+-raise-splitAt (len B) (len D) i) ⟩
            _ ∎
            where open ≡-Reasoning
          bijection₁ (inj₂ ((_ , _ , inj₁ e) , i)) with (AB.conns← (inj₂ ((_ , _ , e) , i))) | (inspect AB.conns← (inj₂ ((_ , _ , e) , i)))
          bijection₁ (inj₂ ((_ , _ , inj₁ e) , i))    | (inj₁ j) | [ i=j ]
            rewrite splitAt-inject+ (len A) (len C) j = begin
            _ ≡˘⟨ cong ((Sum.map (inject+ (len D)) (λ { ((_ , _ , f) , j) → (_ , _ , inj₁ f) , j })) ∘ AB.conns→) i=j ⟩
            _ ≡⟨ cong (Sum.map _ _) (proj₁ AB.bijection (inj₂ ((_ , _ , e) , i))) ⟩
            _ ∎
            where open ≡-Reasoning
          bijection₁ (inj₂ ((_ , _ , inj₁ e) , i))    | (inj₂ (_ , j)) | [ i=j ] = begin
            _ ≡˘⟨ cong ((Sum.map (inject+ (len D)) (λ { ((_ , _ , f) , j) → (_ , _ , inj₁ f) , j })) ∘ AB.conns→) i=j ⟩
            _ ≡⟨ cong (Sum.map _ _) (proj₁ AB.bijection (inj₂ ((_ , _ , e) , i))) ⟩
            _ ∎
            where open ≡-Reasoning
          bijection₁ (inj₂ ((_ , _ , inj₂ e) , i)) with (CD.conns← (inj₂ ((_ , _ , e) , i))) | (inspect CD.conns← (inj₂ ((_ , _ , e) , i)))
          bijection₁ (inj₂ ((_ , _ , inj₂ e) , i))    | (inj₁ j) | [ i=j ]
            rewrite splitAt-raise (len A) (len C) j = begin
            _ ≡˘⟨ cong ((Sum.map (raise (len B)) (λ { ((_ , _ , f) , j) → (_ , _ , inj₂ f) , j })) ∘ CD.conns→) i=j ⟩
            _ ≡⟨ cong (Sum.map _ _) (proj₁ CD.bijection (inj₂ ((_ , _ , e) , i))) ⟩
            _ ∎
            where open ≡-Reasoning
          bijection₁ (inj₂ ((_ , _ , inj₂ e) , i))    | (inj₂ (_ , j)) | [ i=j ] = begin
            _ ≡˘⟨ cong ((Sum.map (raise (len B)) (λ { ((_ , _ , f) , j) → (_ , _ , inj₂ f) , j })) ∘ CD.conns→) i=j ⟩
            _ ≡⟨ cong (Sum.map _ _) (proj₁ CD.bijection (inj₂ ((_ , _ , e) , i))) ⟩
            _ ∎
            where open ≡-Reasoning

          bijection₂ : _
          bijection₂ (inj₁ i) with (splitAt (len A) i) | (inspect (splitAt (len A)) i)
          bijection₂ (inj₁ i)    | (inj₁ i₁) | [ i=i₁ ] with (AB.conns→ (inj₁ i₁)) | (inspect AB.conns→ (inj₁ i₁))
          bijection₂ (inj₁ i)    | (inj₁ i₁) | [ i=i₁ ]    | (inj₁ j) | [ i=j ]
            rewrite splitAt-inject+ (len B) (len D) j = begin
            _ ≡˘⟨ cong ((Sum.map (inject+ (len C)) (λ { ((_ , _ , f) , j) → (_ , _ , inj₁ f) , j })) ∘ AB.conns←) i=j ⟩
            _ ≡⟨ cong (Sum.map _ _) (proj₂ AB.bijection (inj₁ i₁)) ⟩
            _ ≡˘⟨ cong (inj₁ ∘ [ _ , _ ]′) i=i₁ ⟩
            _ ≡⟨ cong inj₁ (inject+-raise-splitAt (len A) (len C) i) ⟩
            _ ∎
            where open ≡-Reasoning
          bijection₂ (inj₁ i)    | (inj₁ i₁) | [ i=i₁ ]    | (inj₂ (_ , j)) | [ i=j ] = begin
            _ ≡˘⟨ cong ((Sum.map (inject+ (len C)) (λ { ((_ , _ , f) , j) → (_ , _ , inj₁ f) , j })) ∘ AB.conns←) i=j ⟩
            _ ≡⟨ cong (Sum.map _ _) (proj₂ AB.bijection (inj₁ i₁)) ⟩
            _ ≡˘⟨ cong (inj₁ ∘ [ _ , _ ]′) i=i₁ ⟩
            _ ≡⟨ cong inj₁ (inject+-raise-splitAt (len A) (len C) i) ⟩
            _ ∎
            where open ≡-Reasoning
          bijection₂ (inj₁ i)    | (inj₂ i₂) | [ i=i₂ ] with (CD.conns→ (inj₁ i₂)) | (inspect CD.conns→ (inj₁ i₂))
          bijection₂ (inj₁ i)    | (inj₂ i₂) | [ i=i₂ ]    | (inj₁ j) | [ i=j ]
            rewrite splitAt-raise (len B) (len D) j = begin
            _ ≡˘⟨ cong ((Sum.map (raise (len A)) (λ { ((_ , _ , f) , j) → (_ , _ , inj₂ f) , j })) ∘ CD.conns←) i=j ⟩
            _ ≡⟨ cong (Sum.map _ _) (proj₂ CD.bijection (inj₁ i₂)) ⟩
            _ ≡˘⟨ cong (inj₁ ∘ [ _ , _ ]′) i=i₂ ⟩
            _ ≡⟨ cong inj₁ (inject+-raise-splitAt (len A) (len C) i) ⟩
            _ ∎
            where open ≡-Reasoning
          bijection₂ (inj₁ i)    | (inj₂ i₂) | [ i=i₂ ]    | (inj₂ (_ , j)) | [ i=j ] = begin
            _ ≡˘⟨ cong ((Sum.map (raise (len A)) (λ { ((_ , _ , f) , j) → (_ , _ , inj₂ f) , j })) ∘ CD.conns←) i=j ⟩
            _ ≡⟨ cong (Sum.map _ _) (proj₂ CD.bijection (inj₁ i₂)) ⟩
            _ ≡˘⟨ cong (inj₁ ∘ [ _ , _ ]′) i=i₂ ⟩
            _ ≡⟨ cong inj₁ (inject+-raise-splitAt (len A) (len C) i) ⟩
            _ ∎
            where open ≡-Reasoning
          bijection₂ (inj₂ ((_ , _ , inj₁ e) , i)) with (AB.conns→ (inj₂ ((_ , _ , e) , i))) | (inspect AB.conns→ (inj₂ ((_ , _ , e) , i)))
          bijection₂ (inj₂ ((_ , _ , inj₁ e) , i))    | (inj₁ j) | [ i=j ]
            rewrite splitAt-inject+ (len B) (len D) j = begin
            _ ≡˘⟨ cong ((Sum.map (inject+ (len C)) (λ { ((_ , _ , f) , j) → (_ , _ , inj₁ f) , j })) ∘ AB.conns←) i=j ⟩
            _ ≡⟨ cong (Sum.map _ _) (proj₂ AB.bijection (inj₂ ((_ , _ , e) , i))) ⟩
            _ ∎
            where open ≡-Reasoning
          bijection₂ (inj₂ ((_ , _ , inj₁ e) , i))    | (inj₂ (_ , j)) | [ i=j ] = begin
            _ ≡˘⟨ cong ((Sum.map (inject+ (len C)) (λ { ((_ , _ , f) , j) → (_ , _ , inj₁ f) , j })) ∘ AB.conns←) i=j ⟩
            _ ≡⟨ cong (Sum.map _ _) (proj₂ AB.bijection (inj₂ ((_ , _ , e) , i))) ⟩
            _ ∎
            where open ≡-Reasoning
          bijection₂ (inj₂ ((_ , _ , inj₂ e) , i)) with (CD.conns→ (inj₂ ((_ , _ , e) , i))) | (inspect CD.conns→ (inj₂ ((_ , _ , e) , i)))
          bijection₂ (inj₂ ((_ , _ , inj₂ e) , i))    | (inj₁ j) | [ i=j ]
            rewrite splitAt-raise (len B) (len D) j = begin
            _ ≡˘⟨ cong ((Sum.map (raise (len A)) (λ { ((_ , _ , f) , j) → (_ , _ , inj₂ f) , j })) ∘ CD.conns←) i=j ⟩
            _ ≡⟨ cong (Sum.map _ _) (proj₂ CD.bijection (inj₂ ((_ , _ , e) , i))) ⟩
            _ ∎
            where open ≡-Reasoning
          bijection₂ (inj₂ ((_ , _ , inj₂ e) , i))    | (inj₂ (_ , j)) | [ i=j ] = begin
            _ ≡˘⟨ cong ((Sum.map (raise (len A)) (λ { ((_ , _ , f) , j) → (_ , _ , inj₂ f) , j })) ∘ CD.conns←) i=j ⟩
            _ ≡⟨ cong (Sum.map _ _) (proj₂ CD.bijection (inj₂ ((_ , _ , e) , i))) ⟩
            _ ∎
            where open ≡-Reasoning


  record SimpleHypergraph (input : List VLabel) (output : List VLabel) : Set ((lsuc l) ⊔ ℓₜ ⊔ ℓₜᵣ ⊔ ℓₒ) where
    field
      hypergraph : Hypergraph input output

    open Hypergraph hypergraph public

    _≲_ : Rel Edge _
    e₁ ≲ e₂ = ∃ λ i₁ → ∃ λ i₂ → conns→ (inj₂ (e₁ , i₁)) ≡ inj₂ (e₂ , i₂)

    field
      partial-order : IsPartialOrder _≡_ _≲_

    module edge-order = IsPartialOrder partial-order


-- the singleton hypergraph
⟦_⟧ : ∀ {s t} → ELabel {s} {t} → Core.Hypergraph {ℓₜ} s t
⟦_⟧ {s} {t} x = record
  { E = λ s′ t′ → (s ≡ s′) × (t ≡ t′)
  ; conns→ = λ { (inj₁ i) → inj₂ ((s , t , refl , refl) , i)
                ; (inj₂ ((_ , _ , refl , refl) , i)) → inj₁ i
                }
  ; conns← = λ { (inj₁ i) → inj₂ ((s , t , refl , refl) , i)
                ; (inj₂ ((_ , _ , refl , refl) , i)) → inj₁ i
                }
  ; type-match = λ { (inj₁ i) → VLabel.refl
                   ; (inj₂ ((_ , _ , refl , refl) , i)) → VLabel.refl
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
