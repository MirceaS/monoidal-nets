{-# OPTIONS --safe #-}

open import Level
open import Data.Product as Prod using (Σ; _,_; proj₁; proj₂; uncurry)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂; [_,_]; map; map₁; map₂)
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

open import Categories.Morphism Hypergraph-Category using (_≅_; module ≅)
open import Categories.Morphism.HeterogeneousIdentity Hypergraph-Category
open import Categories.Morphism.Properties Hypergraph-Category using (Iso-≈; Iso-∘)
open import Categories.Category.Monoidal.Utilities Hypergraph-Monoidal using (_⊗ᵢ_)


Hypergraph-Symmetric : Symmetric Hypergraph-Monoidal
Hypergraph-Symmetric = record
  { braided = record
    { braiding = record
      { F⇒G = record
        { η = uncurry braid
        ; commute = uncurry braid-comm
        ; sym-commute = λ (x , y) → Equiv.sym (braid-comm x y)
        }
      ; F⇐G = record
        { η = uncurry (flip braid)
        ; commute = uncurry (flip braid-comm)
        ; sym-commute = λ (x , y) → Equiv.sym (braid-comm y x)
        }
      ; iso = λ (x , y) → _≅_.iso (braid-≅ x y)
      }
    ; hexagon₁ = λ {X} {Y} {Z} → hexagon₁ X Y Z
    ; hexagon₂ = λ {X} {Y} {Z} → hexagon₂ X Y Z
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
          _ ≡˘⟨ [,]-∘-distr (lookup (vb ++ va)) (splitAt a i) ⟩
          _ ∎
          where open Setoid-Reasoning VLabel-setoid

        bijection₁ : _
        bijection₁ (inj₁ i) = cong inj₁ (begin
          _ ≡⟨ cong [ _ , _ ] ([,]-∘-distr (splitAt a) (splitAt b i)) ⟩
          _ ≡⟨ cong [ _ , _ ] ([,]-cong (splitAt-raise a b) (splitAt-inject+ a b) (splitAt b i)) ⟩
          _ ≡⟨ [,]-∘-distr [ _ , _ ] (splitAt b i) ⟩
          _ ≡⟨ inject+-raise-splitAt b a i ⟩
          _ ∎)
          where open ≡-Reasoning

        bijection₂ : _
        bijection₂ (inj₁ i) = cong inj₁ (begin
          _ ≡⟨ cong [ _ , _ ] ([,]-∘-distr (splitAt b) (splitAt a i)) ⟩
          _ ≡⟨ cong [ _ , _ ] ([,]-cong (splitAt-raise b a) (splitAt-inject+ b a) (splitAt a i)) ⟩
          _ ≡⟨ [,]-∘-distr [ _ , _ ] (splitAt a i) ⟩
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
        α-in-index  = map₂ (λ {((_ , _ , e) , i) → (_ , _ , α e) , i})
        α-out-index : LHS.out-index → RHS.out-index
        α-out-index = map₂ (λ {((_ , _ , e) , i) → (_ , _ , α e) , i})
        
        conns→-resp : (i : LHS.out-index) →
                       RHS.conns→ (α-out-index i) ≡ α-in-index (LHS.conns→ i)
        conns→-resp (inj₁ i) = begin
          _ ≡⟨ cong ((map₂ _) ∘ [ _ , _ ]) ([,]-∘-distr (splitAt c) (splitAt a i)) ⟩
          _ ≡⟨ cong ((map₂ _) ∘ [ _ , _ ]) ([,]-cong (splitAt-raise c a) (splitAt-inject+ c a) (splitAt a i)) ⟩
          _ ≡⟨ cong (map₂ _) ([,]-∘-distr [ _ , _ ] (splitAt a i)) ⟩
          _ ≡⟨ [,]-∘-distr (map₂ _) (splitAt a i) ⟩
          _ ≡⟨ [,]-cong (λ x → begin
            _ ≡⟨ map-commute (f.conns→ (inj₁ x)) ⟩
            _ ≡˘⟨ [,]-cong ((cong (inj₁ ∘ [ _ , _ ])) ∘ (splitAt-inject+ b d)) (λ _ → refl) (f.conns→ (inj₁ x)) ⟩
            _ ≡˘⟨ [,]-∘-distr (map₂ _) (f.conns→ (inj₁ x)) ⟩
            _ ∎) (λ x → begin
            _ ≡⟨ map-commute (g.conns→ (inj₁ x)) ⟩
            _ ≡˘⟨ [,]-cong ((cong (inj₁ ∘ [ _ , _ ])) ∘ (splitAt-raise b d)) (λ _ → refl) (g.conns→ (inj₁ x)) ⟩
            _ ≡˘⟨ [,]-∘-distr (map₂ _) (g.conns→ (inj₁ x)) ⟩
            _ ∎) (splitAt a i) ⟩
          _ ≡˘⟨ [,]-∘-distr (map₂ _) (splitAt a i) ⟩
          _ ≡˘⟨ cong (map₂ _) ([,]-cong ([,]-map-commute ∘ f.conns→ ∘ inj₁) ([,]-map-commute ∘ g.conns→ ∘ inj₁) (splitAt a i)) ⟩
          _ ≡˘⟨ cong (map₂ _) ([,]-∘-distr [ _ , _ ] (splitAt a i)) ⟩
          _ ∎
        conns→-resp (inj₂ ((_ , _ , inj₁ (inj₁ e)) , i)) = begin
          _ ≡⟨ map-commute (f.conns→ (inj₂ ((_ , _ , e) , i))) ⟩
          _ ≡˘⟨ [,]-∘-distr α-in-index (f.conns→ (inj₂ ((_ , _ , e) , i))) ⟩
          _ ≡˘⟨ cong α-in-index ([,]-cong ((cong (inj₁ ∘ [ _ , _ ])) ∘ (splitAt-inject+ b d)) (λ _ → refl) (f.conns→ (inj₂ ((_ , _ , e) , i)))) ⟩
          _ ≡˘⟨ cong α-in-index ([,]-map-commute (f.conns→ (inj₂ ((_ , _ , e) , i)))) ⟩
          _ ∎
        conns→-resp (inj₂ ((_ , _ , inj₁ (inj₂ e)) , i)) = begin
          _ ≡⟨ map-commute (g.conns→ (inj₂ ((_ , _ , e) , i))) ⟩
          _ ≡˘⟨ [,]-∘-distr α-in-index (g.conns→ (inj₂ ((_ , _ , e) , i))) ⟩
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
          _ ≡˘⟨ [,]-∘-distr [ _ , _ ] (splitAt a i) ⟩
          _ ≡˘⟨ cong [ _ , _ ] ([,]-cong (splitAt-raise b a) (splitAt-inject+ b a) (splitAt a i)) ⟩
          _ ≡˘⟨ cong [ _ , _ ] ([,]-∘-distr (splitAt b) (splitAt a i)) ⟩
          _ ∎)
          ; (inj₂ ((_ , _ , inj₁ ()) , _))}
      }
      where
        open ≡-Reasoning
        a = len A
        b = len B

    braid-≅ : ∀ A B → A ⊗₀ B ≅ B ⊗₀ A
    braid-≅ A B = record
      { from = braid A B
      ; to = braid B A
      ; iso = record
        { isoˡ = braid-iso A B
        ; isoʳ = braid-iso B A
        }
      }

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
    hexagon₁ X Y Z = let open HomReasoning hiding (refl; sym; trans) in begin
      _ ≈˘⟨ refl⟩∘⟨ hid-subst-cod g (⊕-assoc Y X Z) ⟩
      _ ≡˘⟨ ⊚[]≡⊚ {f = f} {⊕-assoc Y X Z} {g} ⟩
      _ ≈˘⟨ ≋[][]→≋ hex ⟩
      _ ≈⟨ hid-subst₂ (sym (⊕-assoc X Y Z)) (⊕-assoc Y Z X) h ⟩
      _ ≈⟨ refl⟩∘⟨ refl⟩∘⟨ hid-sym-sym (⊕-assoc X Y Z) ⟩
      _ ∎
      where
        f = cid {Y} ⊗₁ (braid X Z)
        g = (braid X Y) ⊗₁ cid {Z}
        h = braid X (Y ⊗₀ Z)

        x = len X
        y = len Y
        z = len Z

        sub = subF (sym (⊕-assoc X Y Z))

        T1 : Fin y ⊎ Fin (x + z) → _
        T1 = [ inject+ (z + x) , (raise y) ∘ [ raise z , inject+ x ] ∘ (splitAt x) ]
        T2 = (splitAt y) ∘ (subF (⊕-assoc Y X Z)) ∘ (inject+ z) ∘ [ raise y , inject+ x ] ∘ (splitAt x)
        T3 = (splitAt y) ∘ (subF (⊕-assoc Y X Z)) ∘ (raise (y + x))

        hex : h ≋[ sym (⊕-assoc X Y Z) ][ ⊕-assoc Y Z X ] f ⊚[ ⊕-assoc Y X Z ] g
        hex = let open ≡-Reasoning in record
          { α = λ ()
          ; α′ = λ
            { (inj₁ (inj₁ ()))
            ; (inj₂ (inj₁ ()))
            }
          ; bijection = (λ
            { (inj₁ (inj₁ ()))
            ; (inj₂ (inj₁ ()))
            }) , (λ ())
          ; obj-resp = λ ()
          ; conns→-resp = λ {(inj₁ i) → begin
              _ ≡⟨ [,]-∘-distr [ _ , _ ] (splitAt (x + y) (sub i)) ⟩
              _ ≡˘⟨ [,]-cong ((cong (map₂ _)) ∘ ([,]-∘-distr inj₁) ∘ T2) ((cong (map₂ _)) ∘ ([,]-∘-distr inj₁) ∘ T3) (splitAt (x + y) (sub i)) ⟩
              _ ≡˘⟨ [,]-∘-distr inj₁ (splitAt (x + y) (sub i)) ⟩
              _ ≡⟨ cong inj₁ (begin
                _ ≡⟨ cong [ _ , _ ] (splitAt-sym-assoc {X = X} {Y} {Z} i) ⟩
                _ ≡⟨ [,]-∘-distr [ _ , _ ] (splitAt x i) ⟩
                _ ≡⟨ [,]-cong (λ j → begin
                  _ ≡⟨ cong (T1 ∘ (splitAt y) ∘ (subF (⊕-assoc Y X Z)) ∘ (inject+ z) ∘ [ raise y , inject+ x ]) (splitAt-inject+ x y j) ⟩
                  _ ≡⟨ cong T1 (splitAt-assoc (inject+ z (raise y j))) ⟩
                  _ ≡⟨ cong ([ _ , _ ] ∘ [ _ , _ ]) (splitAt-inject+ (y + x) z (raise y j)) ⟩
                  _ ≡⟨ [,]-map-commute (splitAt y (raise y j)) ⟩
                  _ ≡⟨ cong [ _ , _ ] (splitAt-raise y _ j) ⟩
                  _ ≡⟨ cong ((raise y) ∘ [ _ , _ ]) (splitAt-inject+ x z j) ⟩
                  _ ∎) (λ j → begin
                  _ ≡⟨ [,]-map-commute (splitAt y j) ⟩
                  _ ≡⟨ [,]-cong (λ k → begin
                    _ ≡⟨ cong (T1 ∘ (splitAt y) ∘ (subF (⊕-assoc Y X Z)) ∘ (inject+ z) ∘ [ _ , _ ]) (splitAt-raise x _ k) ⟩
                    _ ≡⟨ cong T1 (splitAt-assoc (inject+ z (inject+ x k))) ⟩
                    _ ≡⟨ cong (T1 ∘ [ _ , _ ]) (splitAt-inject+ (y + x) z (inject+ x k)) ⟩
                    _ ≡⟨ cong (T1 ∘ (map₂ _)) (splitAt-inject+ y x k) ⟩
                    _ ∎) (λ k → begin
                    _ ≡⟨ cong T1 (splitAt-assoc (raise (y + x) k)) ⟩
                    _ ≡⟨ cong (T1 ∘ [ _ , _ ]) (splitAt-raise (y + x) _ k) ⟩
                    _ ≡⟨ cong ((raise y) ∘ [ _ , _ ]) (splitAt-raise x _ k) ⟩
                    _ ∎) (splitAt y j) ⟩
                  _ ∎) (splitAt x i) ⟩
                _ ≡˘⟨ [,]-cong (assoc-raise {X = Y} {Z} {X}) (assoc-inject+ {X = Y} {Z} {X}) (splitAt x i) ⟩
                _ ≡˘⟨ [,]-∘-distr (subF (⊕-assoc Y Z X)) (splitAt x i) ⟩
                _ ∎) ⟩
              _ ∎}
          }


    hexagon₂ : ∀ X Y Z →
               [ X ⊗₀ Y ⊗₀ Z ⇒ (Z ⊗₀ X) ⊗₀ Y ]⟨
                 cid {X} ⊗₁ (braid Y Z)          ⇒⟨ X ⊗₀ Z ⊗₀ Y ⟩
                 (associator.to {X} {Z} {Y}       ⇒⟨ (X ⊗₀ Z) ⊗₀ Y ⟩
                 (braid X Z) ⊗₁ cid {Y})
               ≈ associator.to {X} {Y} {Z}        ⇒⟨ (X ⊗₀ Y) ⊗₀ Z ⟩
                 (braid (X ⊗₀ Y) Z               ⇒⟨ Z ⊗₀ X ⊗₀ Y ⟩
                 associator.to {Z} {X} {Y})
               ⟩
    hexagon₂ X Y Z = Iso-≈ (hexagon₁ Z X Y) (Iso-∘ (Iso-∘
                       (_≅_.iso ((braid-≅ Z X) ⊗ᵢ ≅.refl))
                       (hid-iso (⊕-assoc X Z Y)))
                       (_≅_.iso (≅.refl ⊗ᵢ (braid-≅ Z Y)))
                     ) (Iso-∘ (Iso-∘
                       (hid-iso (⊕-assoc Z X Y))
                       (_≅_.iso (braid-≅ Z (X ⊗₀ Y))))
                       (hid-iso (⊕-assoc X Y Z))
                     )

