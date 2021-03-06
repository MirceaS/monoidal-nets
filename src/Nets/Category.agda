{-# OPTIONS --without-K --safe #-}

open import Level renaming (zero to lzero ; suc to lsuc)
open import Agda.Builtin.Equality
open import Data.Product as Prod using (Σ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum as Sum using (_⊎_ ; inj₁ ; inj₂ ; [_,_]′)
open import Data.Nat hiding (_⊔_)
open import Data.Vec hiding (splitAt)
open import Data.Fin renaming (zero to fzero ; suc to fsuc)
open import Data.Fin.Properties using (¬Fin0)
open import Data.Empty using (⊥-elim)
open import Data.Empty.Polymorphic hiding (⊥-elim)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Function using (_∘_ ; Inverseᵇ ; id)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open import Categories.Category

open import Nets.Utils
open import Nets.Hypergraph

module Nets.Category {ℓ₁ ℓ₂ ℓ₃} (HG : Hypergraph ℓ₁ ℓ₂ ℓ₃) {l} where

open import Nets.Diagram HG
open Core {l}

private
  module E = Hypergraph HG
  open E renaming (V to VLabel; E to ELabel) using ()

Diagram-Category : Category ℓ₁ (lsuc l ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) (l ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
Diagram-Category = categoryHelper record
  { Obj       = List VLabel
  ; _⇒_      = Diagram
  ; _≈_       = _≋_
  ; id        = ⊚-id
  ; _∘_       = _⊚_
  ; assoc     = ⊚-assoc
  ; identityˡ  = ⊚-identityˡ
  ; identityʳ  = ⊚-identityʳ
  ; equiv     = ≋-equiv
  ; ∘-resp-≈  = ⊚-resp-≋
  }
  where
    ⊚-assoc : {A B C D : List VLabel} {f : Diagram A B}
              {g : Diagram B C} {h : Diagram C D} →
              ((h ⊚ g) ⊚ f) ≋ (h ⊚ (g ⊚ f))
    ⊚-assoc {f = f} {g} {h} = record
      { α = λ
        { (inj₁ x)        → inj₁ (inj₁ x)
        ; (inj₂ (inj₁ x)) → inj₁ (inj₂ x)
        ; (inj₂ (inj₂ x)) → inj₂ x
        }
      ; α′ = λ
        { (inj₁ (inj₁ x)) → inj₁ x
        ; (inj₁ (inj₂ x)) → inj₂ (inj₁ x)
        ; (inj₂ x)        → inj₂ (inj₂ x)
        }
      ; bijection = (λ
          { (inj₁ (inj₁ x)) → refl
          ; (inj₁ (inj₂ x)) → refl
          ; (inj₂ x)        → refl
          }
        ) , (λ
          { (inj₁ x)        → refl
          ; (inj₂ (inj₁ x)) → refl
          ; (inj₂ (inj₂ x)) → refl
          }
        )
      ; label-resp = λ
        { (inj₁ x)        → E.Equiv.refl
        ; (inj₂ (inj₁ x)) → E.Equiv.refl
        ; (inj₂ (inj₂ x)) → E.Equiv.refl
        }
      ; conns→-resp = conns→-resp
      }
      where
        module f = Diagram f
        module g = Diagram g
        module h = Diagram h

        conns→-resp : _
        conns→-resp (inj₁ i) with (f.conns→ (inj₁ i))
        conns→-resp (inj₁ i)    | (inj₁ j) with (g.conns→ (inj₁ j))
        conns→-resp (inj₁ i)    | (inj₁ j)    | (inj₁ k) with (h.conns→ (inj₁ k))
        conns→-resp (inj₁ i)    | (inj₁ j)    | (inj₁ k)    | (inj₁ _) = refl
        conns→-resp (inj₁ i)    | (inj₁ j)    | (inj₁ k)    | (inj₂ _) = refl
        conns→-resp (inj₁ i)    | (inj₁ j)    | (inj₂ _)               = refl
        conns→-resp (inj₁ i)    | (inj₂ _)                             = refl
        conns→-resp (inj₂ ((_ , _ , inj₁ e) , i)) with (f.conns→ (inj₂ ((_ , _ , e) , i)))
        conns→-resp (inj₂ ((_ , _ , inj₁ e) , i))    | (inj₁ j) with (g.conns→ (inj₁ j))
        conns→-resp (inj₂ ((_ , _ , inj₁ e) , i))    | (inj₁ j)    | (inj₁ k) with (h.conns→ (inj₁ k))
        conns→-resp (inj₂ ((_ , _ , inj₁ e) , i))    | (inj₁ j)    | (inj₁ k)    | (inj₁ _) = refl
        conns→-resp (inj₂ ((_ , _ , inj₁ e) , i))    | (inj₁ j)    | (inj₁ k)    | (inj₂ _) = refl
        conns→-resp (inj₂ ((_ , _ , inj₁ e) , i))    | (inj₁ j)    | (inj₂ _)               = refl
        conns→-resp (inj₂ ((_ , _ , inj₁ e) , i))    | (inj₂ _)                             = refl
        conns→-resp (inj₂ ((_ , _ , inj₂ (inj₁ e)) , i)) with (g.conns→ (inj₂ ((_ , _ , e) , i)))
        conns→-resp (inj₂ ((_ , _ , inj₂ (inj₁ e)) , i))    | (inj₁ j) with (h.conns→ (inj₁ j))
        conns→-resp (inj₂ ((_ , _ , inj₂ (inj₁ e)) , i))    | (inj₁ j)    | (inj₁ _) = refl
        conns→-resp (inj₂ ((_ , _ , inj₂ (inj₁ e)) , i))    | (inj₁ j)    | (inj₂ _) = refl
        conns→-resp (inj₂ ((_ , _ , inj₂ (inj₁ e)) , i))    | (inj₂ _)               = refl
        conns→-resp (inj₂ ((_ , _ , inj₂ (inj₂ e)) , i)) with (h.conns→ (inj₂ ((_ , _ , e) , i)))
        conns→-resp (inj₂ ((_ , _ , inj₂ (inj₂ e)) , i))    | (inj₁ _) = refl
        conns→-resp (inj₂ ((_ , _ , inj₂ (inj₂ e)) , i))    | (inj₂ _) = refl


    ⊚-id : ∀ {A} → Diagram A A
    ⊚-id = record
      { E = λ _ _ → ⊥
      ; conns→ = λ {(inj₁ x) → inj₁ x}
      ; conns← = λ {(inj₁ x) → inj₁ x}
      ; VLabel-resp = λ {(inj₁ _) → refl}
      ; bijection = (λ {(inj₁ _) → refl}) ,
                     (λ {(inj₁ _) → refl})
      ; label = λ ()
      }


    ≋-equiv : ∀ {A B} → IsEquivalence (_≋_ {A} {B})
    ≋-equiv = record
      { refl = ≋-refl
      ; sym = ≋-sym
      ; trans = ≋-trans
      }
      where
        ≋-refl : Reflexive _≋_
        ≋-refl {f} = record
          { α = id
          ; α′ = id
          ; bijection = (λ _ → refl) , (λ _ → refl)
          ; label-resp = λ _ → E.Equiv.refl
          ; conns→-resp = conns→-resp
          }
          where
            module f = Diagram f
            conns→-resp : _
            conns→-resp (inj₁ i) with (f.conns→ (inj₁ i))
            conns→-resp (inj₁ i) | (inj₁ _) = refl
            conns→-resp (inj₁ i) | (inj₂ _) = refl
            conns→-resp (inj₂ ei) with (f.conns→ (inj₂ ei))
            conns→-resp (inj₂ ei) | (inj₁ _) = refl
            conns→-resp (inj₂ ei) | (inj₂ _) = refl

        ≋-sym : Symmetric _≋_
        ≋-sym f≋g = record
          { α = fg.α′
          ; α′ = fg.α
          ; bijection = bijection
          ; label-resp = label-resp
          ; conns→-resp = conns→-resp
          }
          where
            module fg = _≋_ f≋g

            bijection : ∀ {input output} → Inverseᵇ _≡_ _≡_ (fg.α′ {input} {output}) (fg.α)
            bijection {input} {output} = Prod.swap (fg.bijection {input} {output})
  
            label-resp : ∀ {input output} → (e : fg.RHS.E input output) → fg.RHS.label e E.≈ fg.LHS.label (fg.α′ e)
            label-resp {input} {output} e = begin
              _ ≡˘⟨ cong fg.RHS.label (proj₁ fg.bijection e) ⟩
              _ ≈˘⟨ fg.label-resp (fg.α′ e) ⟩
              _ ∎
              where open SetoidReasoning E.setoid

            conns→-resp : _
            conns→-resp (inj₁ i) with (fg.LHS.conns→ (inj₁ i))
                             | (inspect fg.LHS.conns→ (inj₁ i))
            conns→-resp (inj₁ i)    | (inj₁ j) | [ gj ] = begin
              _ ≡˘⟨ cong ((Sum.map₂ _) ∘ (Sum.map₂ _)) gj ⟩
              _ ≡˘⟨ cong (Sum.map₂ _) (fg.conns→-resp (inj₁ i)) ⟩
              _ ∎
              where open ≡-Reasoning
            conns→-resp (inj₁ i)    | (inj₂ ((_ , _ , e′) , j)) | [ gj ] = begin
              _ ≡˘⟨ cong (λ x → inj₂ ((_ , _ , x) , j)) (proj₂ fg.bijection e′) ⟩
              _ ≡˘⟨ cong ((Sum.map₂ _) ∘ (Sum.map₂ _)) gj ⟩
              _ ≡˘⟨ cong (Sum.map₂ _) (fg.conns→-resp (inj₁ i)) ⟩
              _ ∎
              where open ≡-Reasoning
            conns→-resp (inj₂ ((_ , _ , e) , i)) with (fg.LHS.conns→ (inj₂ ((_ , _ , fg.α′ e) , i)))
                                             | (inspect fg.LHS.conns→ (inj₂ ((_ , _ , fg.α′ e) , i)))
            conns→-resp (inj₂ ((_ , _ , e) , i))    | (inj₁ j) | [ gj ] = begin
              _ ≡˘⟨ cong ((Sum.map₂ _) ∘ (Sum.map₂ _)) gj ⟩
              _ ≡˘⟨ cong (Sum.map₂ _) (fg.conns→-resp (inj₂ ((_ , _ , fg.α′ e) , i))) ⟩
              _ ≡⟨ cong (λ x → Sum.map₂ _ (fg.RHS.conns→ (inj₂ ((_ , _ , x) , i)))) (proj₁ fg.bijection e) ⟩
              _ ∎
              where open ≡-Reasoning
            conns→-resp (inj₂ ((_ , _ , e) , i))    | (inj₂ ((_ , _ , e′) , j)) | [ gj ] = begin
              _ ≡˘⟨ cong (λ x → inj₂ ((_ , _ , x) , j)) (proj₂ fg.bijection e′) ⟩
              _ ≡˘⟨ cong ((Sum.map₂ _) ∘ (Sum.map₂ _)) gj ⟩
              _ ≡˘⟨ cong (Sum.map₂ _) (fg.conns→-resp (inj₂ ((_ , _ , fg.α′ e) , i))) ⟩
              _ ≡⟨ cong (λ x → Sum.map₂ _ (fg.RHS.conns→ (inj₂ ((_ , _ , x) , i)))) (proj₁ fg.bijection e) ⟩
              _ ∎
              where open ≡-Reasoning

        ≋-trans : Transitive _≋_
        ≋-trans f≋g g≋h = record
          { α = gh.α ∘ fg.α
          ; α′ = fg.α′ ∘ gh.α′
          ; bijection = bijection
          ; label-resp = label-resp
          ; conns→-resp = conns→-resp
          }
          where
            module fg = _≋_ f≋g
            module gh = _≋_ g≋h

            bijection : ∀ {input output} → Inverseᵇ _≡_ _≡_ ((gh.α {_} {output}) ∘ (fg.α {input})) (fg.α′ ∘ gh.α′)
            bijection {input} {output} =
              (λ x → trans (cong gh.α (proj₁ fg.bijection (gh.α′ x))) (proj₁ gh.bijection x)) ,
              (λ x → trans (cong fg.α′ (proj₂ gh.bijection (fg.α x))) (proj₂ fg.bijection x))

            label-resp : ∀ {input output} → (e : fg.LHS.E input output) → fg.LHS.label e E.≈ gh.RHS.label (gh.α (fg.α e))
            label-resp {input} {output} e = E.Equiv.trans (fg.label-resp e) (gh.label-resp (fg.α e))

            conns→-resp : _
            conns→-resp (inj₁ i) with (fg.LHS.conns→ (inj₁ i))
                             | (inspect fg.LHS.conns→ (inj₁ i))
            conns→-resp (inj₁ i)    | (inj₁ _) | [ gj ] = begin
              _ ≡⟨ gh.conns→-resp (inj₁ i) ⟩
              _ ≡⟨ cong (Sum.map₂ _) (fg.conns→-resp (inj₁ i)) ⟩
              _ ≡⟨ cong ((Sum.map₂ _) ∘ (Sum.map₂ _)) gj ⟩
              _ ∎
              where open ≡-Reasoning
            conns→-resp (inj₁ i)    | (inj₂ _) | [ gj ] = begin
              _ ≡⟨ gh.conns→-resp (inj₁ i) ⟩
              _ ≡⟨ cong (Sum.map₂ _) (fg.conns→-resp (inj₁ i)) ⟩
              _ ≡⟨ cong ((Sum.map₂ _) ∘ (Sum.map₂ _)) gj ⟩
              _ ∎
              where open ≡-Reasoning
            conns→-resp (inj₂ ((_ , _ , e) , i)) with (fg.LHS.conns→ (inj₂ ((_ , _ , e) , i)))
                                             | (inspect fg.LHS.conns→ (inj₂ ((_ , _ , e) , i)))
            conns→-resp (inj₂ ((_ , _ , e) , i))    | (inj₁ _) | [ gj ] = begin
              _ ≡⟨ gh.conns→-resp (inj₂ ((_ , _ , fg.α e) , i)) ⟩
              _ ≡⟨ cong (Sum.map₂ _) (fg.conns→-resp (inj₂ ((_ , _ , e) , i))) ⟩
              _ ≡⟨ cong ((Sum.map₂ _) ∘ (Sum.map₂ _)) gj ⟩
              _ ∎
              where open ≡-Reasoning
            conns→-resp (inj₂ ((_ , _ , e) , i))    | (inj₂ _) | [ gj ] = begin
              _ ≡⟨ gh.conns→-resp (inj₂ ((_ , _ , fg.α e) , i)) ⟩
              _ ≡⟨ cong (Sum.map₂ _) (fg.conns→-resp (inj₂ ((_ , _ , e) , i))) ⟩
              _ ≡⟨ cong ((Sum.map₂ _) ∘ (Sum.map₂ _)) gj ⟩
              _ ∎
              where open ≡-Reasoning


    ⊚-identityˡ : ∀ {A B : List VLabel} {f : Diagram A B} → (⊚-id ⊚ f) ≋ f
    ⊚-identityˡ {A} {B} {f} = record
      { α = λ {(inj₁ e) → e}
      ; α′ = inj₁
      ; bijection = (λ _ → refl) ,
                    (λ {(inj₁ _) → refl})
      ; label-resp = λ {(inj₁ _) → E.Equiv.refl}
      ; conns→-resp = conns→-resp
      }
      where
        module f = Diagram f
        conns→-resp : _
        conns→-resp (inj₁ i) with (f.conns→ (inj₁ i))
        conns→-resp (inj₁ i)    | (inj₁ _) = refl
        conns→-resp (inj₁ i)    | (inj₂ _) = refl
        conns→-resp (inj₂ ((_ , _ , inj₁ e) , i)) with (f.conns→ (inj₂ ((_ , _ , e) , i)))
        conns→-resp (inj₂ ((_ , _ , inj₁ e) , i))    | (inj₁ _) = refl
        conns→-resp (inj₂ ((_ , _ , inj₁ e) , i))    | (inj₂ _) = refl


    ⊚-identityʳ : ∀ {A B : List VLabel} {f : Diagram A B} → (f ⊚ ⊚-id) ≋ f
    ⊚-identityʳ {A} {B} {f} = record
      { α = λ {(inj₂ e) → e}
      ; α′ = inj₂
      ; bijection = (λ _ → refl) ,
                    (λ {(inj₂ _) → refl})
      ; label-resp = λ {(inj₂ _) → E.Equiv.refl}
      ; conns→-resp = conns→-resp
      }
      where
        module f = Diagram f
        conns→-resp : _
        conns→-resp (inj₁ i) with (f.conns→ (inj₁ i))
        conns→-resp (inj₁ i)    | (inj₁ _) = refl
        conns→-resp (inj₁ i)    | (inj₂ _) = refl
        conns→-resp (inj₂ ((_ , _ , inj₂ e) , i)) with (f.conns→ (inj₂ ((_ , _ , e) , i)))
        conns→-resp (inj₂ ((_ , _ , inj₂ e) , i))    | (inj₁ _) = refl
        conns→-resp (inj₂ ((_ , _ , inj₂ e) , i))    | (inj₂ _) = refl


    ⊚-resp-≋ : ∀ {A B C : List VLabel} {f h : Diagram B C} {g i : Diagram A B} →
                f ≋ h → g ≋ i → (f ⊚ g) ≋ (h ⊚ i)
    ⊚-resp-≋ f≋h g≋i = record
      { α = Sum.map gi.α fh.α
      ; α′ = Sum.map gi.α′ fh.α′
      ; bijection = (λ { (inj₁ e) → cong inj₁ (proj₁ gi.bijection e)
                       ; (inj₂ e) → cong inj₂ (proj₁ fh.bijection e) }) ,
                    (λ { (inj₁ e) → cong inj₁ (proj₂ gi.bijection e)
                       ; (inj₂ e) → cong inj₂ (proj₂ fh.bijection e) })
      ; label-resp = λ { (inj₁ e) → gi.label-resp e
                     ; (inj₂ e) → fh.label-resp e }
      ; conns→-resp = conns→-resp
      }
      where
        module fh = _≋_ f≋h
        module gi = _≋_ g≋i
        open ≡-Reasoning
        conns→-resp : _
        conns→-resp (inj₁ i) with (gi.LHS.conns→ (inj₁ i)) | (inspect gi.LHS.conns→ (inj₁ i))
        conns→-resp (inj₁ i)    | (inj₁ j) | [ i→j ] with (fh.LHS.conns→ (inj₁ j)) | (inspect fh.LHS.conns→ (inj₁ j))
        conns→-resp (inj₁ i)    | (inj₁ j) | [ i→j ]    | (inj₁ _) | [ j→k ] = begin
          _ ≡⟨ cong [ _ , _ ]′ (gi.conns→-resp (inj₁ i)) ⟩
          _ ≡⟨ cong ([ _ , _ ]′ ∘ (Sum.map₂ _)) i→j ⟩
          _ ≡⟨ cong (Sum.map₂ _) (fh.conns→-resp (inj₁ j)) ⟩
          _ ≡⟨ cong ((Sum.map₂ _) ∘ (Sum.map₂ _)) j→k ⟩
          _ ∎
        conns→-resp (inj₁ i)    | (inj₁ j) | [ i→j ]    | (inj₂ _) | [ j→k ] = begin
          _ ≡⟨ cong [ _ , _ ]′ (gi.conns→-resp (inj₁ i)) ⟩
          _ ≡⟨ cong ([ _ , _ ]′ ∘ (Sum.map₂ _)) i→j ⟩
          _ ≡⟨ cong (Sum.map₂ _) (fh.conns→-resp (inj₁ j)) ⟩
          _ ≡⟨ cong ((Sum.map₂ _) ∘ (Sum.map₂ _)) j→k ⟩
          _ ∎
        conns→-resp (inj₁ i)    | (inj₂ _) | [ i→j ] = begin
          _ ≡⟨ cong [ _ , _ ]′ (gi.conns→-resp (inj₁ i)) ⟩
          _ ≡⟨ cong ([ _ , _ ]′ ∘ (Sum.map₂ _)) i→j ⟩
          _ ∎
        conns→-resp (inj₂ ((_ , _ , inj₁ e) , i)) with (gi.LHS.conns→ (inj₂ ((_ , _ , e) , i)))
                                              | (inspect gi.LHS.conns→ (inj₂ ((_ , _ , e) , i)))
        conns→-resp (inj₂ ((_ , _ , inj₁ e) , i))    | (inj₁ j) | [ i→j ] with (fh.LHS.conns→ (inj₁ j)) | (inspect fh.LHS.conns→ (inj₁ j))
        conns→-resp (inj₂ ((_ , _ , inj₁ e) , i))    | (inj₁ j) | [ i→j ]    | (inj₁ _) | [ j→k ] = begin
          _ ≡⟨ cong [ _ , _ ]′ (gi.conns→-resp (inj₂ ((_ , _ , e) , i))) ⟩
          _ ≡⟨ cong ([ _ , _ ]′ ∘ (Sum.map₂ _)) i→j ⟩
          _ ≡⟨ cong (Sum.map₂ _) (fh.conns→-resp (inj₁ j)) ⟩
          _ ≡⟨ cong ((Sum.map₂ _) ∘ (Sum.map₂ _)) j→k ⟩
          _ ∎
        conns→-resp (inj₂ ((_ , _ , inj₁ e) , i))    | (inj₁ j) | [ i→j ]    | (inj₂ _) | [ j→k ] = begin
          _ ≡⟨ cong [ _ , _ ]′ (gi.conns→-resp (inj₂ ((_ , _ , e) , i))) ⟩
          _ ≡⟨ cong ([ _ , _ ]′ ∘ (Sum.map₂ _)) i→j ⟩
          _ ≡⟨ cong (Sum.map₂ _) (fh.conns→-resp (inj₁ j)) ⟩
          _ ≡⟨ cong ((Sum.map₂ _) ∘ (Sum.map₂ _)) j→k ⟩
          _ ∎
        conns→-resp (inj₂ ((_ , _ , inj₁ e) , i))    | (inj₂ _) | [ i→j ] = begin
          _ ≡⟨ cong [ _ , _ ]′ (gi.conns→-resp (inj₂ ((_ , _ , e) , i))) ⟩
          _ ≡⟨ cong ([ _ , _ ]′ ∘ (Sum.map₂ _)) i→j ⟩
          _ ∎
        conns→-resp (inj₂ ((_ , _ , inj₂ e) , i)) with (fh.LHS.conns→ (inj₂ ((_ , _ , e) , i)))
                                              | (inspect fh.LHS.conns→ (inj₂ ((_ , _ , e) , i)))
        conns→-resp (inj₂ ((_ , _ , inj₂ e) , i))    | (inj₁ _) | [ i→j ] = begin
          _ ≡⟨ cong (Sum.map₂ _) (fh.conns→-resp (inj₂ ((_ , _ , e) , i))) ⟩
          _ ≡⟨ cong ((Sum.map₂ _) ∘ (Sum.map₂ _)) i→j ⟩
          _ ∎
        conns→-resp (inj₂ ((_ , _ , inj₂ e) , i))    | (inj₂ _) | [ i→j ] = begin
          _ ≡⟨ cong (Sum.map₂ _) (fh.conns→-resp (inj₂ ((_ , _ , e) , i))) ⟩
          _ ≡⟨ cong ((Sum.map₂ _) ∘ (Sum.map₂ _)) i→j ⟩
          _ ∎

module Diagram-Category = Category Diagram-Category
