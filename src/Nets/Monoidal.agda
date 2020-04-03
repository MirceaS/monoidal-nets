{-# OPTIONS --safe #-}

open import Level renaming (zero to lzero; suc to lsuc)
open import Data.Product as Prod using (Σ; _,_; proj₁; proj₂)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Sum.Properties
open import Data.Nat hiding (_⊔_)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Fin renaming (zero to fzero; suc to fsuc; _+_ to _f+_)
open import Data.Fin.Properties using (inject+-raise-splitAt; splitAt-inject+; splitAt-raise)
open import Relation.Binary using (Setoid)
open import Relation.Binary.PropositionalEquality
open import Function using (_∘_ ; id; Inverseᵇ)

open import Categories.Functor.Bifunctor using (Bifunctor)
open import Categories.Category
open import Categories.Category.Product
open import Categories.Category.Monoidal using (Monoidal)

open import Nets.Utils
open import Nets.Hypergraph

module Nets.Monoidal {ℓ₁ ℓ₂ ℓ₃} (HG : Hypergraph ℓ₁ ℓ₂ ℓ₃) {l} where

open import Nets.Diagram HG
open Core {l}
open import Nets.Category HG {l}
open import Nets.MonoidalHelper HG {l}

private
  module E = Hypergraph HG
  open E renaming (V to VLabel; E to ELabel) using ()

Diagram-Monoidal : Monoidal Diagram-Category
Diagram-Monoidal = monoidal ⊗ unit refl (λ {x} → ⊕-identityʳ x) (λ {x y z} → ⊕-assoc x y z)
                               id-unit⨂- (≋[][]→≋ -⨂id-unit) (≋[][]→≋ assoc)
  where
    module HC = Diagram-Category
    HC = Diagram-Category

    module homomorphism {X₁} {X₂} {Y₁} {Y₂} {Z₁} {Z₂}
                        {f₁ : Diagram X₁ Y₁} {f₂ : Diagram X₂ Y₂}
                        {g₁ : Diagram Y₁ Z₁} {g₂ : Diagram Y₂ Z₂} where
    
      module LHS = Diagram ((g₁ HC.∘ f₁) ⨂ (g₂ HC.∘ f₂))
      module RHS = Diagram ((g₁ ⨂ g₂) HC.∘ (f₁ ⨂ f₂))
      module f₁ = Diagram f₁
      module f₂ = Diagram f₂
      module g₁ = Diagram g₁
      module g₂ = Diagram g₂
      
      α : ∀ {input output} → LHS.E input output → RHS.E input output
      α (inj₁ (inj₁ e)) = (inj₁ (inj₁ e))
      α (inj₁ (inj₂ e)) = (inj₂ (inj₁ e))
      α (inj₂ (inj₁ e)) = (inj₁ (inj₂ e))
      α (inj₂ (inj₂ e)) = (inj₂ (inj₂ e))
      
      α′ : ∀ {input output} → RHS.E input output → LHS.E input output
      α′ (inj₁ (inj₁ e)) = (inj₁ (inj₁ e))
      α′ (inj₁ (inj₂ e)) = (inj₂ (inj₁ e))
      α′ (inj₂ (inj₁ e)) = (inj₁ (inj₂ e))
      α′ (inj₂ (inj₂ e)) = (inj₂ (inj₂ e))

      bijection₁ : ∀ {input output} → ((x : RHS.E input output) → α (α′ x) ≡ x)
      bijection₁ (inj₁ (inj₁ e)) = refl
      bijection₁ (inj₁ (inj₂ e)) = refl
      bijection₁ (inj₂ (inj₁ e)) = refl
      bijection₁ (inj₂ (inj₂ e)) = refl

      bijection₂ : ∀ {input output} → ((x : LHS.E input output) → α′ (α x) ≡ x)
      bijection₂ (inj₁ (inj₁ e)) = refl
      bijection₂ (inj₁ (inj₂ e)) = refl
      bijection₂ (inj₂ (inj₁ e)) = refl
      bijection₂ (inj₂ (inj₂ e)) = refl
      
      bijection : ∀ {input output} → Inverseᵇ _≡_ _≡_ (α {input} {output}) (α′)
      bijection = bijection₁ , bijection₂
      
      obj-resp : ∀ {input output} → (e : LHS.E input output) → (LHS.o e) E.≈ (RHS.o (α e))
      obj-resp (inj₁ (inj₁ e)) = E.Equiv.refl
      obj-resp (inj₁ (inj₂ e)) = E.Equiv.refl
      obj-resp (inj₂ (inj₁ e)) = E.Equiv.refl
      obj-resp (inj₂ (inj₂ e)) = E.Equiv.refl

      α-in-index :  LHS.in-index  → RHS.in-index
      α-in-index  = Sum.map₂ (Prod.map (λ {(_ , _ , e) → _ , _ , α e}) id)
      α-out-index : LHS.out-index → RHS.out-index
      α-out-index = Sum.map₂ (Prod.map (λ {(_ , _ , e) → _ , _ , α e}) id)
      
      conns→-resp : (i : LHS.out-index) →
                     RHS.conns→ (α-out-index i) ≡ α-in-index (LHS.conns→ i)
      conns→-resp (inj₁ i) with (splitAt (len X₁) i)
      conns→-resp (inj₁ i)    | (inj₁ i₁) with (f₁.conns→ (inj₁ i₁))
      conns→-resp (inj₁ i)    | (inj₁ i₁)    | (inj₁ j) rewrite (splitAt-inject+ (len Y₁) (len Y₂) j)
                                                         with (g₁.conns→ (inj₁ j))
      conns→-resp (inj₁ i)    | (inj₁ i₁)    | (inj₁ j)    | (inj₁ _) = refl
      conns→-resp (inj₁ i)    | (inj₁ i₁)    | (inj₁ j)    | (inj₂ _) = refl
      conns→-resp (inj₁ i)    | (inj₁ i₁)    | (inj₂ _) = refl
      conns→-resp (inj₁ i)    | (inj₂ i₂) with (f₂.conns→ (inj₁ i₂))
      conns→-resp (inj₁ i)    | (inj₂ i₂)    | (inj₁ j) rewrite (splitAt-raise (len Y₁) (len Y₂) j)
                                                         with (g₂.conns→ (inj₁ j))
      conns→-resp (inj₁ i)    | (inj₂ i₂)    | (inj₁ j)    | (inj₁ _) = refl
      conns→-resp (inj₁ i)    | (inj₂ i₂)    | (inj₁ j)    | (inj₂ _) = refl
      conns→-resp (inj₁ i)    | (inj₂ i₂)    | (inj₂ _) = refl
      conns→-resp (inj₂ ((_ , _ , inj₁ (inj₁ e)) , i)) with (f₁.conns→ (inj₂ ((_ , _ , e) , i)))
      conns→-resp (inj₂ ((_ , _ , inj₁ (inj₁ e)) , i))    | (inj₁ j) rewrite (splitAt-inject+ (len Y₁) (len Y₂) j)
                                                                      with (g₁.conns→ (inj₁ j))
      conns→-resp (inj₂ ((_ , _ , inj₁ (inj₁ e)) , i))    | (inj₁ j)    | (inj₁ _) = refl
      conns→-resp (inj₂ ((_ , _ , inj₁ (inj₁ e)) , i))    | (inj₁ j)    | (inj₂ _) = refl
      conns→-resp (inj₂ ((_ , _ , inj₁ (inj₁ e)) , i))    | (inj₂ _) = refl
      conns→-resp (inj₂ ((_ , _ , inj₁ (inj₂ e)) , i)) with (g₁.conns→ (inj₂ ((_ , _ , e) , i)))
      conns→-resp (inj₂ ((_ , _ , inj₁ (inj₂ e)) , i))    | (inj₁ _) = refl
      conns→-resp (inj₂ ((_ , _ , inj₁ (inj₂ e)) , i))    | (inj₂ _) = refl
      conns→-resp (inj₂ ((_ , _ , inj₂ (inj₁ e)) , i)) with (f₂.conns→ (inj₂ ((_ , _ , e) , i)))
      conns→-resp (inj₂ ((_ , _ , inj₂ (inj₁ e)) , i))    | (inj₁ j) rewrite (splitAt-raise (len Y₁) (len Y₂) j)
                                                                      with (g₂.conns→ (inj₁ j))
      conns→-resp (inj₂ ((_ , _ , inj₂ (inj₁ e)) , i))    | (inj₁ j)    | (inj₁ _) = refl
      conns→-resp (inj₂ ((_ , _ , inj₂ (inj₁ e)) , i))    | (inj₁ j)    | (inj₂ _) = refl
      conns→-resp (inj₂ ((_ , _ , inj₂ (inj₁ e)) , i))    | (inj₂ _) = refl
      conns→-resp (inj₂ ((_ , _ , inj₂ (inj₂ e)) , i)) with (g₂.conns→ (inj₂ ((_ , _ , e) , i)))
      conns→-resp (inj₂ ((_ , _ , inj₂ (inj₂ e)) , i))    | (inj₁ _) = refl
      conns→-resp (inj₂ ((_ , _ , inj₂ (inj₂ e)) , i))    | (inj₂ _) = refl



    module F-resp-≈ {A} {B} {C} {D}
                    {f₁ f₂ : Diagram A B}
                    {g₁ g₂ : Diagram C D}
                    (f₁=f₂ : (f₁ ≋ f₂))
                    (g₁=g₂ : (g₁ ≋ g₂)) where
      module LHS = Diagram (f₁ ⨂ g₁)
      module RHS = Diagram (f₂ ⨂ g₂)
      module ff = _≋_ f₁=f₂
      module gg = _≋_ g₁=g₂
      
      α : ∀ {input output} → LHS.E input output → RHS.E input output
      α = Sum.map ff.α gg.α
      α′ : ∀ {input output} → RHS.E input output → LHS.E input output
      α′ = Sum.map ff.α′ gg.α′

      bijection : ∀ {input output} → Inverseᵇ _≡_ _≡_ (α {input} {output}) (α′)
      bijection = (λ { (inj₁ e) → cong inj₁ (proj₁ ff.bijection e)
                     ; (inj₂ e) → cong inj₂ (proj₁ gg.bijection e)})
                , (λ { (inj₁ e) → cong inj₁ (proj₂ ff.bijection e)
                     ; (inj₂ e) → cong inj₂ (proj₂ gg.bijection e)})
      obj-resp : ∀ {input output} → (e : LHS.E input output) → (LHS.o e) E.≈ (RHS.o (α e))
      obj-resp (inj₁ e) = ff.obj-resp e
      obj-resp (inj₂ e) = gg.obj-resp e

      α-in-index :  LHS.in-index  → RHS.in-index
      α-in-index  = Sum.map₂ (Prod.map (λ {(_ , _ , e) → _ , _ , α e}) id)
      α-out-index : LHS.out-index → RHS.out-index
      α-out-index = Sum.map₂ (Prod.map (λ {(_ , _ , e) → _ , _ , α e}) id)
      
      conns→-resp : (i : LHS.out-index) →
                     RHS.conns→ (α-out-index i) ≡ α-in-index (LHS.conns→ i)
      conns→-resp (inj₁ i) with (splitAt (len A) i)
      conns→-resp (inj₁ i)    | (inj₁ _) = let open ≡-Reasoning in begin
        _ ≡⟨ cong [ _ , _ ]′ (ff.conns→-resp _) ⟩
        _ ≡⟨  [,]-map-commute (ff.LHS.conns→ _) ⟩
        _ ≡˘⟨ [,]-map-commute (ff.LHS.conns→ _) ⟩
        _ ∎
      conns→-resp (inj₁ i)    | (inj₂ _) = let open ≡-Reasoning in begin
        _ ≡⟨ cong [ _ , _ ]′ (gg.conns→-resp _) ⟩
        _ ≡⟨  [,]-map-commute (gg.LHS.conns→ _) ⟩
        _ ≡˘⟨ [,]-map-commute (gg.LHS.conns→ _) ⟩
        _ ∎
      conns→-resp (inj₂ ((_ , _ , inj₁ e) , i)) = let open ≡-Reasoning in begin
        _ ≡⟨ cong [ _ , _ ]′ (ff.conns→-resp _) ⟩
        _ ≡⟨  [,]-map-commute (ff.LHS.conns→ _) ⟩
        _ ≡˘⟨ [,]-map-commute (ff.LHS.conns→ _) ⟩
        _ ∎
      conns→-resp (inj₂ ((_ , _ , inj₂ e) , i)) = let open ≡-Reasoning in begin
        _ ≡⟨ cong [ _ , _ ]′ (gg.conns→-resp _) ⟩
        _ ≡⟨  [,]-map-commute (gg.LHS.conns→ _) ⟩
        _ ≡˘⟨ [,]-map-commute (gg.LHS.conns→ _) ⟩
        _ ∎



    ⊗ : Bifunctor HC HC HC
    ⊗ = record
      { F₀ = Prod.uncurry _⊕_
      ; F₁ = Prod.uncurry _⨂_
      ; identity = λ {AB} → record
        { α = λ {(inj₁ ())}
        ; α′ = λ ()
        ; bijection = (λ ()) , (λ {(inj₁ ())})
        ; obj-resp = λ {(inj₁ ())}
        ; conns→-resp = let open ≡-Reasoning in λ where
            (inj₁ i) → begin
              _ ≡˘⟨ cong inj₁ (inject+-raise-splitAt (len (proj₁ AB)) (len (proj₂ AB)) i) ⟩
              _ ≡⟨ cong (Sum.map₂ _) ([,]-∘-distr inj₁ (splitAt (len (proj₁ AB)) i)) ⟩
              _ ∎
            (inj₂ ((_ , _ , (inj₁ ())) , _))
        }
      ; homomorphism = λ {X} {Y} {Z} {f} {g} → record {
          homomorphism {proj₁ X} {proj₂ X} {proj₁ Y} {proj₂ Y}
                       {proj₁ Z} {proj₂ Z} {proj₁ f} {proj₂ f}
                       {proj₁ g} {proj₂ g} }
      ; F-resp-≈ = λ {A} {B} {fg₁} {fg₂} f=f,g=g → record {
          F-resp-≈ {proj₁ A}   {proj₁ B}   {proj₂ A}   {proj₂ B}
                   {proj₁ fg₁} {proj₁ fg₂} {proj₂ fg₁} {proj₂ fg₂}
                   (proj₁ f=f,g=g) (proj₂ f=f,g=g) } 
      }



    id-unit⨂- : ∀ {A B} {f : A HC.⇒ B} → (HC.id {unit} ⨂ f) ≋ f
    id-unit⨂- {A} {B} {f} = record
      { α = λ {(inj₂ e) → e}
      ; α′ = inj₂
      ; bijection = (λ e → refl)
                  , (λ {(inj₂ e) → refl})
      ; obj-resp = λ {(inj₂ e) → E.Equiv.refl}
      ; conns→-resp = λ
          { (inj₁ i) → begin
              _ ≡˘⟨ map-id (f.conns→ _) ⟩
              _ ≡˘⟨ map-commute (f.conns→ _) ⟩
              _ ∎
          ; (inj₂ ((_ , _ , inj₂ e) , i)) → begin
              _ ≡˘⟨ map-id (f.conns→ _) ⟩
              _ ≡˘⟨ map-commute (f.conns→ _) ⟩
              _ ∎
          }
      }
      where
        module f = Diagram f
        open ≡-Reasoning



    -⨂id-unit : ∀ {A B} {f : A HC.⇒ B} → (f ⨂ (HC.id {unit})) ≋[ ⊕-identityʳ A ][ ⊕-identityʳ B ] f
    -⨂id-unit {A} {B} {f} = record
      { α = α
      ; α′ = inj₁
      ; bijection = (λ e → refl)
                  , (λ {(inj₁ e) → refl})
      ; obj-resp = λ {(inj₁ e) → E.Equiv.refl}
      ; conns→-resp = conns→-resp
      }
      where
        open ≡-Reasoning

        module LHS = Diagram (f ⨂ (HC.id {unit}))
        module RHS = Diagram f

        α : ∀ {s t} → LHS.E s t → RHS.E s t
        α (inj₁ e) = e

        α-in-index :  LHS.in-index  → RHS.in-index
        α-in-index  = Sum.map (subF (⊕-identityʳ B)) (λ {((_ , _ , e) , i) → (_ , _ , α e) , i})
        α-out-index : LHS.out-index → RHS.out-index
        α-out-index = Sum.map (subF (⊕-identityʳ A)) (λ {((_ , _ , e) , i) → (_ , _ , α e) , i})

        lemma : ∀ {A : List VLabel} → (i : Fin ((len A) + zero)) →
                splitAt (len A) i ≡ inj₁ (subF (⊕-identityʳ A) i)
        lemma {suc l , A ∷ AS} fzero = cong inj₁ (0-subst (⊕-identityʳ (l , AS)))
        lemma {suc l , A ∷ AS} (fsuc i) = begin
          _ ≡⟨ cong (Sum.map fsuc id) (lemma {l , AS} i) ⟩
          _ ≡⟨ cong inj₁ (fsuc-subst (⊕-identityʳ (l , AS)) i) ⟩
          _ ∎

        lemma2 : ∀ {B : List VLabel} → (i : Fin (len B)) → i ≡ subF (⊕-identityʳ B) (inject+ zero i)
        lemma2 {B} i = inj₁-injective (begin
          _ ≡˘⟨ splitAt-inject+ (len B) zero i ⟩
          _ ≡⟨ lemma ((inject+ zero) i) ⟩
          _ ∎)

        conns→-resp : (i : LHS.out-index) → RHS.conns→ (α-out-index i) ≡ α-in-index (LHS.conns→ i)
        conns→-resp (inj₁ i) = begin
          _ ≡˘⟨ map-id (RHS.conns→ (α-out-index (inj₁ i))) ⟩
          _ ≡⟨ map-cong lemma2 (λ _ → refl) (RHS.conns→ (α-out-index (inj₁ i))) ⟩
          _ ≡˘⟨ map-commute (RHS.conns→ (α-out-index (inj₁ i))) ⟩
          _ ≡˘⟨ cong ([ _ , _ ]′ ∘ [ _ , _ ]′) (lemma {A} i) ⟩
          _ ∎
        conns→-resp (inj₂ (( _ , _ , inj₁ e) , i)) with RHS.conns→ (inj₂ (( _ , _ , e) , i))
        conns→-resp (inj₂ (( _ , _ , inj₁ e) , i))    | (inj₁ j) = cong inj₁ (lemma2 j)
        conns→-resp (inj₂ (( _ , _ , inj₁ e) , i))    | (inj₂ _) = refl



    assoc : ∀ {A A′ A′′ B B′ B′′} {f : A HC.⇒ B} {g : A′ HC.⇒ B′} {h : A′′ HC.⇒ B′′} →
            ((f ⨂ g) ⨂ h) ≋[ ⊕-assoc A A′ A′′ ][ ⊕-assoc B B′ B′′ ] (f ⨂ (g ⨂ h))
    assoc {A} {A′} {A′′} {B} {B′} {B′′} {f} {g} {h} = record
      { α = α
      ; α′ = λ
        { (inj₁ e) → inj₁ (inj₁ e)
        ; (inj₂ (inj₁ e)) → inj₁ (inj₂ e)
        ; (inj₂ (inj₂ e)) → inj₂ e
        }
      ; bijection = (λ
        { (inj₁ e) → refl
        ; (inj₂ (inj₁ e)) → refl
        ; (inj₂ (inj₂ e)) → refl
        }) , (λ
        { (inj₁ (inj₁ e)) → refl
        ; (inj₁ (inj₂ e)) → refl
        ; (inj₂ e) → refl
        })
      ; obj-resp = λ
        { (inj₁ (inj₁ e)) → E.Equiv.refl
        ; (inj₁ (inj₂ e)) → E.Equiv.refl
        ; (inj₂ e) → E.Equiv.refl
        }
      ; conns→-resp = conns→-resp
      }
      where
        open ≡-Reasoning

        module LHS = Diagram ((f ⨂ g) ⨂ h)
        module RHS = Diagram (f ⨂ (g ⨂ h))
        module f = Diagram f
        module g = Diagram g
        module h = Diagram h

        α : ∀ {s t} → LHS.E s t → RHS.E s t
        α (inj₁ (inj₁ e)) = inj₁ e
        α (inj₁ (inj₂ e)) = inj₂ (inj₁ e)
        α (inj₂ e) = inj₂ (inj₂ e)

        α-in-index :  LHS.in-index  → RHS.in-index
        α-in-index  = Sum.map (subF (⊕-assoc B B′ B′′)) (λ {((_ , _ , e) , i) → (_ , _ , α e) , i})
        α-out-index : LHS.out-index → RHS.out-index
        α-out-index = Sum.map (subF (⊕-assoc A A′ A′′)) (λ {((_ , _ , e) , i) → (_ , _ , α e) , i})

        lemma : ∀ {l} {S : Set l} {A B C} {f : Fin (len A) → S} {g : Fin (len B) → S} {h : Fin (len C) → S} →
                (i : Fin ((len A + len B) + len C)) →
                [ [ f , g ]′ ∘ (splitAt (len A)) , h ]′ (splitAt (len A + len B) i) ≡
                [ f , [ g , h ]′ ∘ (splitAt (len B)) ]′ (splitAt (len A) (subF (⊕-assoc {A = VLabel} A B C) i))
        lemma {A = zero , []} _ = refl
        lemma {A = suc l , A ∷ AS} fzero = cong ([ _ , _ ]′ ∘ (splitAt (suc l))) (0-subst (⊕-assoc (l , AS) _ _))
        lemma {A = suc l , A ∷ AS} {B} {C} {f} {g} {h} (fsuc i) = begin
          _ ≡⟨ [,]-map-commute (splitAt (l + len B) i) ⟩
          _ ≡⟨ [,]-cong ([,]-map-commute ∘ (splitAt l)) (λ _ → refl) (splitAt (l + len B) i) ⟩
          _ ≡⟨ lemma {A = l , AS} {B} {C} {f ∘ fsuc} {g} {h} i ⟩
          _ ≡˘⟨ [,]-map-commute (splitAt l (subF (⊕-assoc (l , AS) B C) i)) ⟩
          _ ≡⟨ cong ([ _ , _ ]′ ∘ (splitAt (suc l))) (fsuc-subst (⊕-assoc (l , AS) B C) i) ⟩
          _ ∎

        inject+-inject+ : ∀ {A B C : List VLabel} → (i : Fin (len A)) →
                          inject+ ((len B) + (len C)) i ≡
                          subF (⊕-assoc A B C) (inject+ (len C) (inject+ (len B) i))
        inject+-inject+ {suc l , _ ∷ AS} fzero = 0-subst (⊕-assoc (l , AS) _ _)
        inject+-inject+ {suc l , _ ∷ AS} (fsuc i) = begin
          _ ≡⟨ cong fsuc (inject+-inject+ {l , AS} i) ⟩
          _ ≡⟨ fsuc-subst (⊕-assoc (l , AS) _ _) _ ⟩
          _ ∎

        raise-inject+ : ∀ {A B C : List VLabel} → (i : Fin (len B)) →
                        raise (len A) (inject+ (len C) i) ≡
                        subF (⊕-assoc A B C) (inject+ (len C) (raise (len A) i))
        raise-inject+ {zero , []} i = refl
        raise-inject+ {suc l , _ ∷ AS} {B} {C} i = begin
          _ ≡⟨ cong fsuc (raise-inject+ {l , AS} {B} {C} i) ⟩
          _ ≡⟨ fsuc-subst (⊕-assoc (l , AS) B C) _ ⟩
          _ ∎

        raise-raise : ∀ {A B C : List VLabel} → (i : Fin (len C)) →
                      raise (len A) (raise (len B) i) ≡
                      subF (⊕-assoc A B C) (raise ((len A) + (len B)) i)
        raise-raise {zero , []} i = refl
        raise-raise {suc l , A ∷ AS} {B} {C} i = begin
          _ ≡⟨ cong fsuc (raise-raise {l , AS} {B} {C} i) ⟩
          _ ≡⟨ fsuc-subst (⊕-assoc (l , AS) B C) _ ⟩
          _ ∎

        conns→-resp : (i : LHS.out-index) → RHS.conns→ (α-out-index i) ≡ α-in-index (LHS.conns→ i)
        conns→-resp (inj₁ i) = begin
          _ ≡⟨ [,]-cong (λ _ → refl) (([,]-∘-distr (Sum.map _ _)) ∘ (splitAt (len A′)))
               (splitAt (len A) (subF (⊕-assoc A A′ A′′) i)) ⟩
          _ ≡˘⟨ lemma {f = (Sum.map _ _) ∘ f.conns→ ∘ inj₁} i ⟩
          _ ≡⟨ [,]-cong (λ x → begin
            _ ≡⟨ [,]-cong (λ y → begin
              _ ≡⟨ map-cong (inject+-inject+ {B}) (λ _ → refl) (f.conns→ (inj₁ y)) ⟩
              _ ≡˘⟨ map-commute (f.conns→ (inj₁ y)) ⟩
              _ ∎) (λ y → begin
              _ ≡⟨ map-commute (g.conns→ (inj₁ y)) ⟩
              _ ≡⟨ map-cong (raise-inject+ {B}) (λ _ → refl) (g.conns→ (inj₁ y)) ⟩
              _ ≡˘⟨ map-commute (g.conns→ (inj₁ y)) ⟩
              _ ∎) (splitAt (len A) x) ⟩
            _ ≡˘⟨ [,]-∘-distr (Sum.map _ _) (splitAt (len A) x) ⟩
            _ ≡˘⟨ map-commute ([ _ , _ ]′ (splitAt (len A) x)) ⟩
            _ ∎) (λ x → begin
            _ ≡⟨ map-commute (h.conns→ (inj₁ x)) ⟩
            _ ≡⟨ map-cong (raise-raise {B}) (λ _ → refl) (h.conns→ (inj₁ x)) ⟩
            _ ≡˘⟨ map-commute (h.conns→ (inj₁ x)) ⟩
            _ ∎) (splitAt (len A + len A′) i) ⟩
          _ ≡˘⟨ [,]-∘-distr α-in-index (splitAt (len A + len A′) i) ⟩
          _ ∎
        conns→-resp (inj₂ ((_ , _ , inj₁ (inj₁ e)) , i)) with f.conns→ (inj₂ ((_ , _ , e) , i))
        conns→-resp (inj₂ ((_ , _ , inj₁ (inj₁ e)) , i))    | (inj₁ j) = cong inj₁ (inject+-inject+ {B} j)
        conns→-resp (inj₂ ((_ , _ , inj₁ (inj₁ e)) , i))    | (inj₂ _) = refl
        conns→-resp (inj₂ ((_ , _ , inj₁ (inj₂ e)) , i)) with g.conns→ (inj₂ ((_ , _ , e) , i))
        conns→-resp (inj₂ ((_ , _ , inj₁ (inj₂ e)) , i))    | (inj₁ j) = cong inj₁ (raise-inject+ {B} j)
        conns→-resp (inj₂ ((_ , _ , inj₁ (inj₂ e)) , i))    | (inj₂ _) = refl
        conns→-resp (inj₂ ((_ , _ , inj₂ e) , i)) with h.conns→ (inj₂ ((_ , _ , e) , i))
        conns→-resp (inj₂ ((_ , _ , inj₂ e) , i))    | (inj₁ j) = cong inj₁ (raise-raise {B} j)
        conns→-resp (inj₂ ((_ , _ , inj₂ e) , i))    | (inj₂ _) = refl


module Diagram-Monoidal = Monoidal Diagram-Monoidal
