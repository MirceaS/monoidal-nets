{-# OPTIONS --without-K --safe #-}

{- This is an example of a definition of graphical rewrite rules
 - along with a derivation that 2 diagrams are equivalent under
 - those rules. All the diagrams are built using combinators
 - for simplicity.
 -}

open import Level
open import Relation.Binary using (Rel)
open import Data.Unit hiding (setoid)

open import Nets.Utils
open import Nets.Hypergraph

module Nets.ReasoningExample where

data ELabel : List ⊤ → List ⊤ → Set where
  A     : ELabel 2* 1*
  B C D : ELabel 1* 1*

HG = basic ELabel

open import Nets.Diagram HG
open Core {zero} using (Diagram)
open import Nets.Category HG {zero}
open import Nets.Monoidal HG {zero}
open import Nets.Symmetric HG {zero}

open Diagram-Category
open Diagram-Symmetric

infix 4 _∼_

{- Rewrite rules:

   one-to-two:           
         
      ╭────╮                      ╭────╮   ╭────╮
   ───┤    │   ╭────╮          ───┤  B ├───┤    │
      │    ├───┤  C ├───   ⇒     ╰────╯   │    ├───
      │ A  │   ╰────╯             ╭────╮   │ A  │ 
   ───┤    │                   ───┤  B ├───┤    │
      ╰────╯                      ╰────╯   ╰────╯

   BC-to-nil:

      ╭────╮   ╭────╮
   ───┤  C ├───┤  B ├──    ⇒      ─────────────
      ╰────╯   ╰────╯  
-}

data _∼_ : ∀ {s t} → Rel (Diagram s t) (suc zero) where
  one-to-two : ⟦ C ⟧ ∘ ⟦ A ⟧ ∼ ⟦ A ⟧ ∘ ⟦ B ⟧ ⊗₁ ⟦ B ⟧
  BC-to-nil : ⟦ B ⟧ ∘ ⟦ C ⟧ ∼ id

open import Nets.Closure HG {zero} _∼_
open import Nets.DiagrammaticReasoning HG {zero} _∼_

{-

   derivation:
             
         
      ╭────╮   ╭────╮  ╭────╮                      ╭────╮   ╭────╮
   ───┤  D ├───┤  B ├───┤    │   ╭────╮          ───┤  D ├───┤    │
      ╰────╯   ╰────╯   │    ├───┤  B ├───   ∼⁺     ╰────╯   │    ├───
      ╭────╮            │ A  │   ╰────╯                      │ A  │
   ───┤  B ├────────────┤    │                   ────────────┤    │
      ╰────╯            ╰────╯                               ╰────╯
-}

derivation : ⟦ B ⟧ ∘ ⟦ A ⟧ ∘ ⟦ B ⟧ ⊗₁ id ∘ ⟦ D ⟧ ⊗₁ ⟦ B ⟧ ∼⁺
             ⟦ A ⟧ ∘ ⟦ D ⟧ ⊗₁ id
derivation = begin
  _ ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ split₁ˡ ⟩
  _ ≈⟨ refl⟩∘⟨ refl⟩∘⟨ split₁ʳ ⟩
  _ ≈˘⟨ refl⟩∘⟨ assoc ⟩
  _ ∼˘⟨ ⁺.refl⟩∘⟨ ⦅ one-to-two ⦆ ⁺.⟩∘⟨refl ⟩
  _ ≈˘⟨ assoc ⟩
  _ ≈˘⟨ assoc ⟩∘⟨refl ⟩
  _ ∼⟨ ⦅ BC-to-nil ⦆ ⁺.⟩∘⟨refl ⁺.⟩∘⟨refl ⟩
  _ ≈⟨ identityˡ ⟩∘⟨refl ⟩
  _ ∎
