{-# OPTIONS --without-K --safe #-}

open import Level
open import Relation.Binary using (Rel; Setoid; Reflexive; Symmetric; Transitive)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Function using (_∘_)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Fin renaming (zero to fzero; suc to fsuc)
open import Data.Empty.Polymorphic

open import Categories.Functor
open import Categories.Adjoint
open import Categories.Category.Construction.Graphs hiding (refl; sym; trans)

open import Nets.Utils

module Nets.Graphical {o ℓ e} (G : Graph o (suc o ⊔ ℓ) (suc o ⊔ ℓ ⊔ e)) where

open Graph G
open Adjoint (CatF-is-Free o (suc o ⊔ ℓ) (suc o ⊔ ℓ ⊔ e)) using (Radjunct)


data ELabel : List Obj → List Obj → Set (suc o ⊔ ℓ) where
  * : ∀ {A B} → A ⇒ B → ELabel (A ∷[]) (B ∷[])

ELabel-setoid : List Obj → List Obj → Setoid _ _
ELabel-setoid s t = record
  { Carrier = ELabel s t
  ; _≈_ = _E≈_
  ; isEquivalence = record
    { refl  = λ {x} → Erefl {x}
    ; sym   = λ {x} → Esym {x}
    ; trans = λ {x} → Etrans {x}
    }
  }
  where
      _E≈_ : Rel (ELabel s t) _
      (* f) E≈ (* g) = f ≈ g
      Erefl : Reflexive _E≈_
      Erefl {* _} = Equiv.refl
      Esym : Symmetric _E≈_
      Esym {* _} {* _} = Equiv.sym
      Etrans : Transitive _E≈_
      Etrans {* _} {* _} {* _} = Equiv.trans

open import Nets.Diagram Obj ELabel-setoid using (module Core; ⟦_⟧; ⟦⟧-cong)
open Core {o} using (_≋_)
open import Nets.Category Obj ELabel-setoid {o}


ToGraphical : Functor (Free G) Diagram-Category
ToGraphical = Radjunct record
  { M₀ = _∷[]
  ; M₁ = ⟦_⟧ ∘ *
  ; M-resp-≈ = ⟦⟧-cong
  }
