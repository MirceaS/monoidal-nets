{-# OPTIONS --without-K --safe #-}

{- This is a generalisation of Graph from Categories.Category.Construction.Graphs
 - that uses Lists of vertices as the end-vertices of edges
 -}

open import Level
open import Relation.Binary hiding (_⇒_)

open import Categories.Category.Construction.Graphs hiding (setoid)

open import Nets.Utils

module Nets.Hypergraph where

record Hypergraph o ℓ e : Set (suc (o ⊔ ℓ ⊔ e)) where
  infix 4 _≈_ E

  field
    V : Set o
    E : Rel (List V) ℓ
    _≈_ : ∀ {A B} → Rel (E A B) e
    equiv : ∀ {A B} → IsEquivalence (_≈_ {A} {B})

  setoid : {A B : List V} → Setoid _ _
  setoid {A} {B} = record
    { Carrier       = E A B
    ; _≈_           = _≈_
    ; isEquivalence = equiv
    }

  module Equiv {A} {B} = IsEquivalence (equiv {A} {B})

toGraph : ∀ {o ℓ e} → Hypergraph o ℓ e → Graph o ℓ e
toGraph h = record
  { Obj = List V
  ; _⇒_ = E
  ; _≈_ = _≈_
  ; equiv = equiv
  }
  where open Hypergraph h

module _ {o ℓ e} (g : Graph o ℓ e) where
  open Graph g
  data E-inj : Rel (List Obj) (o ⊔ ℓ) where
    ^ : ∀ {x y} → x ⇒ y → E-inj (x ::[]) (y ::[])

toHypergraph : ∀ {o ℓ e} → Graph o ℓ e → Hypergraph o (o ⊔ ℓ) e
toHypergraph g = record
  { V = Obj
  ; E = E-inj g
  ; _≈_ = _≈-inj_
  ; equiv = record
    { refl = λ {x} → refl-inj {_} {_} {x}
    ; sym = λ {x} → sym-inj {_} {_} {x}
    ; trans = λ {x} → trans-inj {_} {_} {x}
    }
  }
  where
    open Graph g

    _≈-inj_ : ∀ {x y} → Rel (E-inj g x y) _
    (^ x) ≈-inj (^ y) = x ≈ y

    refl-inj : ∀ {x y} → (Reflexive (_≈-inj_ {x} {y}))
    refl-inj {_} {_} {^ _} = Equiv.refl

    sym-inj : ∀ {x y} → (Symmetric (_≈-inj_ {x} {y}))
    sym-inj {_} {_} {^ _} {^ _} = Equiv.sym

    trans-inj : ∀ {x y} → (Transitive (_≈-inj_ {x} {y}))
    trans-inj {_} {_} {^ _} {^ _} {^ _} = Equiv.trans
