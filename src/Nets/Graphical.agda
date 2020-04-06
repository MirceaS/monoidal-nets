{-# OPTIONS --without-K --safe #-}

open import Level
open import Function using (id; _∘_; _$_)

open import Categories.Category
open import Categories.Functor renaming (id to idF)
open import Categories.Adjoint
open import Categories.Category.Construction.Graphs hiding (refl; sym; trans)

open import Nets.Utils
open import Nets.Hypergraph

module Nets.Graphical where

module _ {o ℓ} (G : Graph o (suc o ⊔ ℓ) (suc o ⊔ ℓ)) where
  HG = toHypergraph G

  open import Nets.Diagram HG
  open Core using (Diagram; _≋_; _⊚_)
  open import Nets.Category HG {o}

  ToGraphical : Functor (Free G) Diagram-Category
  ToGraphical = Radjunct record
    { M₀ = _::[]
    ; M₁ = ⟦_⟧ ∘ ^
    ; M-resp-≈ = ⟦⟧-cong
    }
    where open Adjoint (CatF-is-Free o (suc o ⊔ ℓ) (suc o ⊔ ℓ))

{- The following assumption can be proved but the proof is quite involved
 - and falls outside the scope of this project at the moment. This is why,
 - for now, we assume it to be true in order to proceed but, if proved in
 - the future, this module declaration can be removed.
 -}
module _ (ToGraphicalIsFaithful : ∀ {o ℓ} (G : Graph o (suc o ⊔ ℓ) (suc o ⊔ ℓ)) →
                                  Faithful (ToGraphical {o} {ℓ} G)) where

  module _ {o ℓ} (C : Category o (suc o ⊔ ℓ) (suc o ⊔ ℓ)) where

    G = Underlying₀ C
    FC = Free G
    open import Nets.Category (toHypergraph G) {o} renaming (Diagram-Category to DC)
    toDC = Functor.₁ (ToGraphical {o} {ℓ} G)
    module eval = Functor (Adjoint.counit.η (CatF-is-Free o (suc o ⊔ ℓ) (suc o ⊔ ℓ)) C)

    Coherence : ∀ {s t} → (f g : FC [ s , t ]) → DC [ toDC f ≈ toDC g ] → C [ eval.₁ f ≈ eval.₁ g ]
    Coherence f g f≋g = eval.F-resp-≈ (ToGraphicalIsFaithful {o} {ℓ} G f g f≋g)

    {- The definition of Coherence from above may appear innocuous but
     - what it's actually showing is that if 2 diagrams, each representing
     - a combination of terms in some Category, are isomorphic, then we
     - can produce a proof that the 2 terms themselves are equivalent when
     - evaluated inside the Category. We can therefore use our toolkit of
     - graphical reasoning tools to prove things about arbitrary
     - Categories, which is quite significant.
     -
     - The thing to note here is that the only "hard" bit is to prove that
     - the canonical Functor from the Free Category to Diagram-Category is
     - faithful. This is not at all a common thing and it shows us that
     - Diagram-Category, although not a Free category itself, is
     - "Free-like".
     -
     - The process of showing that the Coherence property holds for
     - Categories with additional structure is analogous to the above,
     - with the analogous requirement that the canonical Free Functor to
     - the corresponding Diagram Category of the right type is faithful.
     -
     - For Monoidal and Symmetric Categories, we can show more than that.
     - We can show that Diagram-Monoidal and Diagram-Symmetric are the
     - Free Monoidal Category and the Free Symmetric Category
     - respectively, but this is a difficult proof that is outside our
     - scope at this time.
     -}
