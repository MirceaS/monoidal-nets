{-# OPTIONS --safe #-}

open import Level
open import Data.Product as Prod using (Σ; _,_; proj₁; proj₂; uncurry)
open import Data.Sum as Sum using (inj₁; inj₂; [_,_])
open import Data.Sum.Properties
open import Data.Nat using (ℕ; _+_)
open import Data.Vec using (Vec; _++_; lookup)
open import Data.Vec.Properties using (lookup-++ˡ; lookup-++ʳ; lookup-splitAt)
open import Data.Fin renaming (zero to fzero; suc to fsuc; _+_ to _f+_)
open import Data.Fin.Properties using (splitAt-inject+; splitAt-raise; inject+-raise-splitAt)
open import Data.Empty.Polymorphic
open import Function using (id; _∘_; flip)
open import Relation.Binary using (Setoid)
import      Relation.Binary.Reasoning.Setoid as Setoid-Reasoning
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Categories.Category.Monoidal.Symmetric using (Symmetric)

open import Nets.Utils

module Nets.Symmetric {ℓₜ ℓₜᵣ : Level}
                      (VLabel-setoid : Setoid ℓₜ ℓₜᵣ)
                      {ℓₒ ℓₒᵣ : Level}
                      (ELabel-setoid :
                        List (Setoid.Carrier VLabel-setoid) →
                        List (Setoid.Carrier VLabel-setoid) →
                        Setoid ℓₒ ℓₒᵣ
                      ) {l : Level} where

open import Nets.Hypergraph VLabel-setoid ELabel-setoid
open Core {l} using (Hypergraph; _≋[_][_]_; ≋[][]→≋; _⊚[_]_; ⊚[]≡⊚)
open import Nets.Category   VLabel-setoid ELabel-setoid {l} using (Hypergraph-Category)
open import Nets.Monoidal   VLabel-setoid ELabel-setoid {l} using (Hypergraph-Monoidal)
import Nets.K-Utils Hypergraph-Category as K-Utils


Hypergraph-Symmetric : Symmetric Hypergraph-Monoidal
Hypergraph-Symmetric = record
  { braided = record
    { braiding = record
      { F⇒G = record
        { η = uncurry braid
        ; commute = uncurry braid-comm
        }
      ; F⇐G = record
        { η = uncurry (flip braid)
        ; commute = uncurry (flip braid-comm)
        }
      ; iso = λ AB → record
        { isoˡ = uncurry braid-iso AB
        ; isoʳ = uncurry (flip braid-iso) AB
        }
      }
    ; hexagon₁ = λ {X} {Y} {Z} → hexagon₁ X Y Z
    ; hexagon₂ = {!!}
    }
  ; commutative = λ {X} {Y} → braid-iso Y X
  }
  where
    open Hypergraph-Category renaming (_∘_ to _⊚_; id to cid)
    open Hypergraph-Monoidal

    braid : ∀ A B → A ⊗₀ B ⇒ B ⊗₀ A
    braid A B = record
      { E = λ _ _ → ⊥
      ; conns→ = λ {(inj₁ i) → inj₁ ([ raise b , inject+ a ] (splitAt a i))}
      ; conns← = λ {(inj₁ i) → inj₁ ([ raise a , inject+ b ] (splitAt b i))}
      ; type-match = type-match
      ; bijection = bijection₁ , bijection₂
      ; o = λ ()
      }
      where
        a = len A
        b = len B
        va = vec-of-list A
        vb = vec-of-list B

        type-match : _
        type-match (inj₁ i) = begin
          _ ≡⟨ lookup-splitAt a va vb i ⟩
          _ ≡˘⟨ [,]-cong (lookup-++ʳ vb va) (lookup-++ˡ vb va) (splitAt a i) ⟩
          _ ≡˘⟨ [,]-∘-distr {f = lookup (vb ++ va)} (splitAt a i) ⟩
          _ ∎
          where open Setoid-Reasoning VLabel-setoid

        bijection₁ : _
        bijection₁ (inj₁ i) = cong inj₁ (begin
          _ ≡⟨ cong [ _ , _ ] ([,]-∘-distr {f = splitAt a} (splitAt b i)) ⟩
          _ ≡⟨ cong [ _ , _ ] ([,]-cong (splitAt-raise a b) (splitAt-inject+ a b) (splitAt b i)) ⟩
          _ ≡⟨ [,]-∘-distr {f = [ _ , _ ]} (splitAt b i) ⟩
          _ ≡⟨ inject+-raise-splitAt b a i ⟩
          _ ∎)
          where open ≡-Reasoning

        bijection₂ : _
        bijection₂ (inj₁ i) = cong inj₁ (begin
          _ ≡⟨ cong [ _ , _ ] ([,]-∘-distr {f = splitAt b} (splitAt a i)) ⟩
          _ ≡⟨ cong [ _ , _ ] ([,]-cong (splitAt-raise b a) (splitAt-inject+ b a) (splitAt a i)) ⟩
          _ ≡⟨ [,]-∘-distr {f = [ _ , _ ]} (splitAt a i) ⟩
          _ ≡⟨ inject+-raise-splitAt a b i ⟩
          _ ∎)
          where open ≡-Reasoning
        
    braid-comm : ∀ {A B C D} → (f : A ⇒ B) → (g : C ⇒ D) → CommutativeSquare (f ⊗₁ g) (braid A C) (braid B D) (g ⊗₁ f)
    braid-comm {A} {B} {C} {D} f g = record
      { α = α
      ; α′ = λ
          { (inj₂ (inj₁ e)) → inj₁ (inj₂ e)
          ; (inj₂ (inj₂ e)) → inj₁ (inj₁ e)
          }
      ; bijection = (λ
          { (inj₂ (inj₁ e)) → refl
          ; (inj₂ (inj₂ e)) → refl
          }) , (λ
          { (inj₁ (inj₁ e)) → refl
          ; (inj₁ (inj₂ e)) → refl
          })
      ; obj-resp = λ
          { (inj₁ (inj₁ e)) → ELabel.refl
          ; (inj₁ (inj₂ e)) → ELabel.refl
          }
      ; conns→-resp = conns→-resp
      }
      where
        open ≡-Reasoning
        module f = Hypergraph f
        module g = Hypergraph g
        module LHS = Hypergraph ((braid B D) ⊚ (f ⊗₁ g))
        module RHS = Hypergraph ((g ⊗₁ f) ⊚ (braid A C))

        a = len A
        b = len B
        c = len C
        d = len D

        α : ∀ {input output} → LHS.E input output → RHS.E input output
        α (inj₁ (inj₁ e)) = inj₂ (inj₂ e)
        α (inj₁ (inj₂ e)) = inj₂ (inj₁ e)

        α-in-index :  LHS.in-index  → RHS.in-index
        α-in-index  = Sum.map₂ (λ {((_ , _ , e) , i) → (_ , _ , α e) , i})
        α-out-index : LHS.out-index → RHS.out-index
        α-out-index = Sum.map₂ (λ {((_ , _ , e) , i) → (_ , _ , α e) , i})
        
        conns→-resp : (i : LHS.out-index) →
                       RHS.conns→ (α-out-index i) ≡ α-in-index (LHS.conns→ i)
        conns→-resp (inj₁ i) = begin
          _ ≡⟨ cong ((Sum.map₂ _) ∘ [ _ , _ ]) ([,]-∘-distr {f = splitAt c} (splitAt a i)) ⟩
          _ ≡⟨ cong ((Sum.map₂ _) ∘ [ _ , _ ]) ([,]-cong (splitAt-raise c a) (splitAt-inject+ c a) (splitAt a i)) ⟩
          _ ≡⟨ cong (Sum.map₂ _) ([,]-∘-distr {f = [ _ , _ ]} (splitAt a i)) ⟩
          _ ≡⟨ [,]-∘-distr {f = Sum.map₂ _} (splitAt a i) ⟩
          _ ≡⟨ [,]-cong (λ x → begin
            _ ≡⟨ map-commute (f.conns→ (inj₁ x)) ⟩
            _ ≡˘⟨ [,]-cong ((cong (inj₁ ∘ [ _ , _ ])) ∘ (splitAt-inject+ b d)) (λ _ → refl) (f.conns→ (inj₁ x)) ⟩
            _ ≡˘⟨ [,]-∘-distr {f = Sum.map₂ _} (f.conns→ (inj₁ x)) ⟩
            _ ∎) (λ x → begin
            _ ≡⟨ map-commute (g.conns→ (inj₁ x)) ⟩
            _ ≡˘⟨ [,]-cong ((cong (inj₁ ∘ [ _ , _ ])) ∘ (splitAt-raise b d)) (λ _ → refl) (g.conns→ (inj₁ x)) ⟩
            _ ≡˘⟨ [,]-∘-distr {f = Sum.map₂ _} (g.conns→ (inj₁ x)) ⟩
            _ ∎) (splitAt a i) ⟩
          _ ≡˘⟨ [,]-∘-distr {f = Sum.map₂ _} (splitAt a i) ⟩
          _ ≡˘⟨ cong (Sum.map₂ _) ([,]-cong ([,]-map-commute ∘ f.conns→ ∘ inj₁) ([,]-map-commute ∘ g.conns→ ∘ inj₁) (splitAt a i)) ⟩
          _ ≡˘⟨ cong (Sum.map₂ _) ([,]-∘-distr {f = [ _ , _ ]} (splitAt a i)) ⟩
          _ ∎
        conns→-resp (inj₂ ((_ , _ , inj₁ (inj₁ e)) , i)) = begin
          _ ≡⟨ map-commute (f.conns→ (inj₂ ((_ , _ , e) , i))) ⟩
          _ ≡˘⟨ [,]-∘-distr {f = α-in-index} (f.conns→ (inj₂ ((_ , _ , e) , i))) ⟩
          _ ≡˘⟨ cong α-in-index ([,]-cong ((cong (inj₁ ∘ [ _ , _ ])) ∘ (splitAt-inject+ b d)) (λ _ → refl) (f.conns→ (inj₂ ((_ , _ , e) , i)))) ⟩
          _ ≡˘⟨ cong α-in-index ([,]-map-commute (f.conns→ (inj₂ ((_ , _ , e) , i)))) ⟩
          _ ∎
        conns→-resp (inj₂ ((_ , _ , inj₁ (inj₂ e)) , i)) = begin
          _ ≡⟨ map-commute (g.conns→ (inj₂ ((_ , _ , e) , i))) ⟩
          _ ≡˘⟨ [,]-∘-distr {f = α-in-index} (g.conns→ (inj₂ ((_ , _ , e) , i))) ⟩
          _ ≡˘⟨ cong α-in-index ([,]-cong ((cong (inj₁ ∘ [ _ , _ ])) ∘ (splitAt-raise b d)) (λ _ → refl) (g.conns→ (inj₂ ((_ , _ , e) , i)))) ⟩
          _ ≡˘⟨ cong α-in-index ([,]-map-commute (g.conns→ (inj₂ ((_ , _ , e) , i)))) ⟩
          _ ∎

    braid-iso : ∀ A B → braid B A ⊚ braid A B ≈ cid
    braid-iso A B = record
      { α = λ {(inj₁ ())}
      ; α′ = λ ()
      ; bijection = (λ ()) , (λ {(inj₁ ())})
      ; obj-resp = λ {(inj₁ ())}
      ; conns→-resp = λ {(inj₁ i) → cong inj₁ (begin
          _ ≡˘⟨ inject+-raise-splitAt a b i ⟩
          _ ≡˘⟨ [,]-∘-distr {f = [ _ , _ ]} (splitAt a i) ⟩
          _ ≡˘⟨ cong [ _ , _ ] ([,]-cong (splitAt-raise b a) (splitAt-inject+ b a) (splitAt a i)) ⟩
          _ ≡˘⟨ cong [ _ , _ ] ([,]-∘-distr {f = splitAt b} (splitAt a i)) ⟩
          _ ∎)
          ; (inj₂ ((_ , _ , inj₁ ()) , _))}
      }
      where
        open ≡-Reasoning

        a = len A
        b = len B

    open Commutation

    hexagon₁ : ∀ X Y Z →
               [ (X ⊗₀ Y) ⊗₀ Z ⇒ Y ⊗₀ Z ⊗₀ X ]⟨
                 (braid X Y) ⊗₁ cid {Z}          ⇒⟨ (Y ⊗₀ X) ⊗₀ Z ⟩
                 associator.from {Y} {X} {Z}      ⇒⟨ Y ⊗₀ X ⊗₀ Z ⟩
                 cid {Y} ⊗₁ (braid X Z)
               ≈ associator.from {X} {Y} {Z}      ⇒⟨ X ⊗₀ Y ⊗₀ Z ⟩
                 braid X (Y ⊗₀ Z)                ⇒⟨ (Y ⊗₀ Z) ⊗₀ X ⟩
                 associator.from {Y} {Z} {X}
               ⟩
    hexagon₁ X Y Z = K-Utils.hexagon₁ f g h
      (⊕-assoc Y X Z) (⊕-assoc X Y Z) (⊕-assoc Y Z X) {!!} -- (≋[][]→≋ hex)
      where
        f = cid {Y} ⊗₁ (braid X Z)
        g = (braid X Y) ⊗₁ cid {Z}
        h = braid X (Y ⊗₀ Z)

        hex : f ⊚[ ⊕-assoc Y X Z ] g ≋[ ⊕-assoc X Y Z ][ sym (⊕-assoc Y Z X) ] h
        hex = record
          { α = λ {(inj₁ ())} ; α′ = {!!} ; bijection = {!!} ; obj-resp = {!!} ; conns→-resp = {!!} }
