--{-# OPTIONS --without-K --safe #-}

open import Level renaming (zero to lzero ; suc to lsuc)
open import Agda.Builtin.Equality
open import Data.Product as Prod using (Σ ; _,_ ; proj₁ ; proj₂ ; _×_)
open import Data.Sum as Sum using (_⊎_ ; inj₁ ; inj₂ ; [_,_]′)
open import Data.Sum.Properties using ([,]-∘-distr ; [,]-map-commute ; map-commute ; map-cong)
open import Data.Nat hiding (_⊔_)
open import Data.Vec hiding (splitAt)
open import Data.Fin renaming (zero to fzero ; suc to fsuc ; _+_ to _f+_)
open import Data.Fin.Properties using (¬Fin0 ; inject+-raise-splitAt ; splitAt-inject+ ; splitAt-raise)
open import Data.Empty using (⊥-elim)
open import Data.Empty.Polymorphic renaming (⊥-elim to ⊥-elim′)
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality
open import Function using (_∘_ ; Inverseᵇ ; id ; case_of_)
open import Categories.Functor.Bifunctor using (Bifunctor)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning
open import Categories.Category
open import Categories.Category.Product
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Simple
open import Categories.Morphism using (Iso)

import Nets.Properties
import Nets.Hypergraph

module Nets.Monoidal {ℓₜ ℓₜᵣ : Level} (VLabel-setoid : Setoid ℓₜ ℓₜᵣ)
                       {ℓₒ ℓₒᵣ : Level}
                       (ELabel-setoid :
                         Σ ℕ (Vec (Setoid.Carrier VLabel-setoid)) →  -- List VLabel →
                         Σ ℕ (Vec (Setoid.Carrier VLabel-setoid)) →  -- List VLabel →
                         Setoid ℓₒ ℓₒᵣ
                       ) where

open Nets.Properties VLabel-setoid ELabel-setoid
open Nets.Hypergraph VLabel-setoid ELabel-setoid

l++-identityʳ : ∀ {a} {A : Set a} (X : List A) → X l++ (zero , []) ≡ X
l++-identityʳ (zero , []) = refl
l++-identityʳ ((suc n) , (x ∷ xs)) = cong ((suc zero , x ∷ []) l++_) (l++-identityʳ (n , xs))

l++-assoc : ∀ {a} {A : Set a} (X Y Z : List A) → ((X l++ Y) l++ Z) ≡ (X l++ (Y l++ Z))
l++-assoc (zero , []) Y Z = refl
l++-assoc ((suc n) , (x ∷ xs)) Y Z = cong ((suc zero , x ∷ []) l++_) (l++-assoc (n , xs) Y Z)

map-id : ∀ {a b} {A : Set a} {B : Set b} → (Sum.map (id {a} {A}) (id {b} {B})) ≗ id
map-id (inj₁ _) = refl
map-id (inj₂ _) = refl

lemma : ∀ {a b c} {A : Set a} {B : Rel A b} (sel : ∀ {z z′} → B z z′ → Set c) →
          {x y x′ y′ : A} → (f : B x x′) → (eq₁ : x ≡ y) → (eq₂ : x′ ≡ y′) →
          sel (subst (λ w → B w y′) eq₁ (subst (B x) eq₂ f)) → sel f
lemma _ _ refl refl e = e

lemma′ : ∀ {a b c} {A : Set a} {B : Rel A b} (sel : ∀ {z z′} → B z z′ → Set c) →
          {x y x′ y′ : A} → (f : B x x′) → (eq₁ : x ≡ y) → (eq₂ : x′ ≡ y′) →
          sel f → sel (subst (λ w → B w y′) eq₁ (subst (B x) eq₂ f))
lemma′ _ _ refl refl e = e

lemma2 : ∀ {a b c d} {A : Set a} {B : Rel A b} {D : Set d} (sel : ∀ {z z′} → B z z′ → Set c) →
           (sel′ : ∀ {z z′} → (h : B z z′) → sel h → D) →
           {x y x′ y′ : A} → (f : B x x′) → (eq₁ : x ≡ y) → (eq₂ : x′ ≡ y′) →
           (e : sel (subst (λ w → B w y′) eq₁ (subst (B x) eq₂ f))) →
           sel′ (subst (λ w → B w y′) eq₁ (subst (B x) eq₂ f)) e ≡ sel′ f (lemma sel f eq₁ eq₂ e)
lemma2 _ _ _ refl refl _ = refl

lemma3 : ∀ {a b c d} {A : Set a} {B : Rel A b} (sel : ∀ {z z′} → B z z′ → Rel A c) →
           {D : A → Set d} →
           (sel′ : ∀ {z z′} → (h : B z z′) → (D z) ⊎ (Σ (Σ₂ A A (sel h)) (D ∘ proj₁ ∘ proj₂)) → (D z′) ⊎ (Σ (Σ₂ A A (sel h)) (D ∘ proj₁))) →
           {x y x′ y′ : A} → (f : B x x′) → (eq₁ : x ≡ y) → (eq₂ : x′ ≡ y′) →
           (e : (D y) ⊎ (Σ (Σ₂ A A (sel (subst (λ w → B w y′) eq₁ (subst (B x) eq₂ f)))) (D ∘ proj₁ ∘ proj₂))) →
           Sum.map (subst D (sym eq₂)) (λ {((s , t , ee) , i) → (s , t , lemma (λ xx → sel xx s t) f eq₁ eq₂ ee) , i}) (sel′ (subst (λ w → B w y′) eq₁ (subst (B x) eq₂ f)) e) ≡
           sel′ f (Sum.map (subst D (sym eq₁)) (λ {((s , t , ee) , i) → (s , t , lemma (λ xx → sel xx s t) f eq₁ eq₂ ee) , i}) e)
lemma3 _ sel′ f refl refl (inj₁ i) with (sel′ f (inj₁ i))
lemma3 _ sel′ f refl refl (inj₁ i)    | (inj₁ _) = refl
lemma3 _ sel′ f refl refl (inj₁ i)    | (inj₂ _) = refl
lemma3 _ sel′ f refl refl (inj₂ i) with (sel′ f (inj₂ i))
lemma3 _ sel′ f refl refl (inj₂ i)    | (inj₁ _) = refl
lemma3 _ sel′ f refl refl (inj₂ i)    | (inj₂ _) = refl

lemma∘lemma′≡id : ∀ {a b c} {A : Set a} {B : Rel A b} (sel : ∀ {z z′} → B z z′ → Set c) →
                  {x y x′ y′ : A} → (f : B x x′) → (eq₁ : x ≡ y) → (eq₂ : x′ ≡ y′) →
                  (e : sel f) → lemma {B = B} sel f eq₁ eq₂ (lemma′ {B = B} sel f eq₁ eq₂ e) ≡ e
lemma∘lemma′≡id _ _ refl refl e = refl

lemma′∘lemma≡id : ∀ {a b c} {A : Set a} {B : Rel A b} (sel : ∀ {z z′} → B z z′ → Set c) →
                  {x y x′ y′ : A} → (f : B x x′) → (eq₁ : x ≡ y) → (eq₂ : x′ ≡ y′) →
                  (e : sel (subst (λ w → B w y′) eq₁ (subst (B x) eq₂ f))) → lemma′ {B = B} sel f eq₁ eq₂ (lemma {B = B} sel f eq₁ eq₂ e) ≡ e
lemma′∘lemma≡id _ _ refl refl e = refl

Hypergraph-Monoidal : ∀ {l} → Monoidal (Hypergraph-Category {l})
Hypergraph-Monoidal {l} = monoidal ⊗ unit refl (λ {x} → l++-identityʳ x) (λ {x y z} → l++-assoc x y z) id-unit⨂- -⨂id-unit assoc
  where
    module HC = Hypergraph-Category {l}
    HC = Hypergraph-Category {l}

    module homomorphism {X₁} {X₂} {Y₁} {Y₂} {Z₁} {Z₂}
                        {f₁ : Hypergraph {l} X₁ Y₁} {f₂ : Hypergraph {l} X₂ Y₂}
                        {g₁ : Hypergraph {l} Y₁ Z₁} {g₂ : Hypergraph {l} Y₂ Z₂} where
    
      module LHS = Hypergraph ((g₁ HC.∘ f₁) ⨂ (g₂ HC.∘ f₂))
      module RHS = Hypergraph ((g₁ ⨂ g₂) HC.∘ (f₁ ⨂ f₂))
      module f₁ = Hypergraph f₁
      module f₂ = Hypergraph f₂
      module g₁ = Hypergraph g₁
      module g₂ = Hypergraph g₂
      
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
      
      obj-resp : ∀ {input output} → (e : LHS.E input output) → (LHS.o e) ELabel.≈ (RHS.o (α e))
      obj-resp (inj₁ (inj₁ e)) = ELabel.refl
      obj-resp (inj₁ (inj₂ e)) = ELabel.refl
      obj-resp (inj₂ (inj₁ e)) = ELabel.refl
      obj-resp (inj₂ (inj₂ e)) = ELabel.refl

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
                    {f₁ f₂ : Hypergraph {l} A B}
                    {g₁ g₂ : Hypergraph {l} C D}
                    (f₁=f₂,g₁=g₂ : (f₁ ≋ f₂) × (g₁ ≋ g₂)) where
      module LHS = Hypergraph (f₁ ⨂ g₁)
      module RHS = Hypergraph (f₂ ⨂ g₂)
      module ff = _≋_ (proj₁ f₁=f₂,g₁=g₂)
      module gg = _≋_ (proj₂ f₁=f₂,g₁=g₂)
      
      α : ∀ {input output} → LHS.E input output → RHS.E input output
      α = Sum.map ff.α gg.α
      α′ : ∀ {input output} → RHS.E input output → LHS.E input output
      α′ = Sum.map ff.α′ gg.α′

      bijection : ∀ {input output} → Inverseᵇ _≡_ _≡_ (α {input} {output}) (α′)
      bijection = (λ { (inj₁ e) → cong inj₁ (proj₁ ff.bijection e)
                     ; (inj₂ e) → cong inj₂ (proj₁ gg.bijection e)})
                , (λ { (inj₁ e) → cong inj₁ (proj₂ ff.bijection e)
                     ; (inj₂ e) → cong inj₂ (proj₂ gg.bijection e)})
      obj-resp : ∀ {input output} → (e : LHS.E input output) → (LHS.o e) ELabel.≈ (RHS.o (α e))
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
      { F₀ = Prod.uncurry _l++_
      ; F₁ = Prod.uncurry _⨂_
      ; identity = λ {AB} → record
        { α = λ {(inj₁ ())}
        ; α′ = λ ()
        ; bijection = (λ ()) , (λ {(inj₁ ())})
        ; obj-resp = λ {(inj₁ ())}
        ; conns→-resp = let open ≡-Reasoning in λ where
            (inj₁ i) → begin
              _ ≡˘⟨ cong inj₁ (inject+-raise-splitAt (len (proj₁ AB)) (len (proj₂ AB)) i) ⟩
              _ ≡⟨ cong (Sum.map₂ _) ([,]-∘-distr {f = inj₁} (splitAt (len (proj₁ AB)) i)) ⟩
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
                   f=f,g=g } 
      }

    unit = zero , []

    id-unit⨂- : ∀ {A B} {f : A HC.⇒ B} → (HC.id {unit} ⨂ f) ≋ f
    id-unit⨂- {A} {B} {f} = record
      { α = λ {(inj₂ e) → e}
      ; α′ = inj₂
      ; bijection = (λ e → refl)
                  , (λ {(inj₂ e) → refl})
      ; obj-resp = λ {(inj₂ e) → ELabel.refl}
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
        module f = Hypergraph f
        open ≡-Reasoning

    -⨂id-unit : ∀ {A B} {f : A HC.⇒ B} → subst (HC._⇒ _) (l++-identityʳ A) (subst (_ HC.⇒_) (l++-identityʳ B) (f ⨂ (HC.id {unit}))) ≋ f
    -⨂id-unit {A} {B} {f} = record
      { α = α₁ ∘ α₂
      ; α′ = α₁′ ∘ α₂′
      ; bijection = α₁α₂α₁′α₂′≡id
                  , α₁′α₂′α₁α₂≡id
      ; obj-resp = obj-resp
      ; conns→-resp = {!!}
      }
      where
        f′ = f ⨂ (HC.id {unit})
        substf′ = subst (HC._⇒ B) (l++-identityʳ A) (subst ((A l++ unit) HC.⇒_) (l++-identityʳ B) f′)

        module f′ = Hypergraph f′
        module LHS = Hypergraph substf′
        module RHS = Hypergraph f

        module _ {input} {output} where
          sel = λ {z} {z′} h → Hypergraph.E {l} {z} {z′} h input output
          sel′ = λ {z} {z′} h → Hypergraph.o {l} {z} {z′} h {input} {output}

          α₁ : f′.E input output → RHS.E input output
          α₁ (inj₁ e) = e

          α₂ : LHS.E input output → f′.E input output
          α₂ = lemma sel f′ (l++-identityʳ A) (l++-identityʳ B)

          α₁′ : f′.E input output → LHS.E input output
          α₁′ = lemma′ sel f′ (l++-identityʳ A) (l++-identityʳ B)

          α₂′ : RHS.E input output → f′.E input output
          α₂′ = inj₁

          α₂′α₁≡id : ∀ e → α₂′ (α₁ e) ≡ e
          α₂′α₁≡id (inj₁ e) = refl

          α₁α₂α₁′α₂′≡id : ∀ e → α₁ (α₂ (α₁′ (α₂′ e))) ≡ e
          α₁α₂α₁′α₂′≡id e = cong α₁ (lemma∘lemma′≡id sel f′ (l++-identityʳ A) (l++-identityʳ B) (α₂′ e))

          α₁′α₂′α₁α₂≡id : ∀ e → α₁′ (α₂′ (α₁ (α₂ e))) ≡ e
          α₁′α₂′α₁α₂≡id e = trans (cong α₁′ (α₂′α₁≡id (α₂ e))) (lemma′∘lemma≡id sel f′ (l++-identityʳ A) (l++-identityʳ B) e)

          obj-resp : (e : LHS.E input output) → (LHS.o e) ELabel.≈ (RHS.o (α₁ (α₂ e)))
          obj-resp e = begin
            _ ≡⟨ lemma2 sel sel′ f′ (l++-identityʳ A) (l++-identityʳ B) e ⟩
            _ ≡⟨ f′α₁≡f (α₂ e) ⟩
            _ ∎
            where
              open SetoidReasoning (ELabel-setoid _ _)
              f′α₁≡f : ∀ e → f′.o e ≡ RHS.o (α₁ e)
              f′α₁≡f (inj₁ e) = refl


    assoc : ∀ {A B A′ B′ A′′ B′′} {f : A HC.⇒ B} {f′ : A′ HC.⇒ B′} {f′′ : A′′ HC.⇒ B′′} →
            subst (HC._⇒ (B l++ (B′ l++ B′′))) (l++-assoc A A′ A′′) (subst (((A l++ A′) l++ A′′) HC.⇒_) (l++-assoc B B′ B′′) ((f ⨂ f′) ⨂ f′′)) ≋ (f ⨂ (f′ ⨂ f′′))
    assoc {A} {B} {A′} {B′} {A′′} {B′′} {g} {g′} {g′′} = record
      { α = α₁ ∘ α₂
      ; α′ = α₁′ ∘ α₂′
      ; bijection = α₁α₂α₁′α₂′≡id
                  , α₁′α₂′α₁α₂≡id
      ; obj-resp = obj-resp
      ; conns→-resp = conns→-resp
      }
      where
        eq₁ = l++-assoc A A′ A′′
        eq₂ = l++-assoc B B′ B′′

        f = g ⨂ (g′ ⨂ g′′)
        f′ = (g ⨂ g′) ⨂ g′′
        substf′ = subst (HC._⇒ (B l++ (B′ l++ B′′))) eq₁ (subst (((A l++ A′) l++ A′′) HC.⇒_) eq₂ f′)

        module f′ = Hypergraph f′
        module LHS = Hypergraph substf′
        module RHS = Hypergraph f

        module _ {input} {output} where
          sel = λ {z} {z′} h → Hypergraph.E {l} {z} {z′} h input output
          sel′ = λ {z} {z′} h → Hypergraph.o {l} {z} {z′} h {input} {output}

          α₁ : f′.E input output → RHS.E input output
          α₁ (inj₁ (inj₁ i)) = inj₁ i
          α₁ (inj₁ (inj₂ i)) = inj₂ (inj₁ i)
          α₁ (inj₂ i) = inj₂ (inj₂ i)

          α₂ : LHS.E input output → f′.E input output
          α₂ = lemma {B = Hypergraph {l}} sel f′ eq₁ eq₂

          α₁′ : f′.E input output → LHS.E input output
          α₁′ = lemma′ {B = Hypergraph {l}} sel f′ eq₁ eq₂

          α₂′ : RHS.E input output → f′.E input output
          α₂′ (inj₁ i) = inj₁ (inj₁ i)
          α₂′ (inj₂ (inj₁ i)) = inj₁ (inj₂ i)
          α₂′ (inj₂ (inj₂ i)) = inj₂ i

          α₂′α₁≡id : ∀ e → α₂′ (α₁ e) ≡ e
          α₂′α₁≡id (inj₁ (inj₁ i)) = refl
          α₂′α₁≡id (inj₁ (inj₂ i)) = refl
          α₂′α₁≡id (inj₂ i) = refl

          α₁α₂α₁′α₂′≡id : ∀ e → α₁ (α₂ (α₁′ (α₂′ e))) ≡ e
          α₁α₂α₁′α₂′≡id (inj₁ i) = cong α₁ (lemma∘lemma′≡id sel f′ eq₁ eq₂ (inj₁ (inj₁ i)))
          α₁α₂α₁′α₂′≡id (inj₂ (inj₁ i)) = cong α₁ (lemma∘lemma′≡id sel f′ eq₁ eq₂ (inj₁ (inj₂ i)))
          α₁α₂α₁′α₂′≡id (inj₂ (inj₂ i)) = cong α₁ (lemma∘lemma′≡id sel f′ eq₁ eq₂ (inj₂ i))

          α₁′α₂′α₁α₂≡id : ∀ e → α₁′ (α₂′ (α₁ (α₂ e))) ≡ e
          α₁′α₂′α₁α₂≡id e = trans (cong α₁′ (α₂′α₁≡id (α₂ e))) (lemma′∘lemma≡id sel f′ eq₁ eq₂ e)

          obj-resp : (e : LHS.E input output) → (LHS.o e) ELabel.≈ (RHS.o (α₁ (α₂ e)))
          obj-resp e = begin
            _ ≡⟨ lemma2 sel sel′ f′ eq₁ eq₂ e ⟩
            _ ≡⟨ f′α₁≡f (α₂ e) ⟩
            _ ∎
            where
              open SetoidReasoning (ELabel-setoid _ _)
              f′α₁≡f : ∀ e → f′.o e ≡ RHS.o (α₁ e)
              f′α₁≡f (inj₁ (inj₁ i)) = refl
              f′α₁≡f (inj₁ (inj₂ i)) = refl
              f′α₁≡f (inj₂ i) = refl

        α-in-index :  LHS.in-index  → RHS.in-index
        α-in-index  = Sum.map₂ (λ {((s , t , e) , i) → (s , t , α₁ (α₂ e)) , i})
        α-out-index : LHS.out-index → RHS.out-index
        α-out-index = Sum.map₂ (λ {((s , t , e) , i) → (s , t , α₁ (α₂ e)) , i})

        lemma3′ : (i : LHS.out-index) → (Sum.map (subst (Fin ∘ len) (sym eq₂)) (λ {((s , t , e) , j) → (s , t , α₂ e) , j}) (LHS.conns→ i)) ≡
                                         (f′.conns→ (Sum.map (subst (Fin ∘ len) (sym eq₁)) (λ {((s , t , e) , j) → (s , t , α₂ e) , j}) i))
        lemma3′ = lemma3 (Hypergraph.E {l}) (Hypergraph.conns→ {l}) f′ eq₁ eq₂

        conns→-resp : (i : LHS.out-index) →
                       RHS.conns→ (α-out-index i) ≡ α-in-index (LHS.conns→ i)
        conns→-resp i = begin
          RHS.conns→ (α-out-index i)                  ≡⟨ {!!} ⟩
          α₁-index₂ (f′.conns→ (α₂-index₁ i))         ≡˘⟨ cong α₁-index₂ (lemma3′ i) ⟩
          α₁-index₂ (α₂-index₂ (LHS.conns→ i))        ≡⟨ map-commute (LHS.conns→ i) ⟩
          Sum.map ((subst (Fin ∘ len) eq₂) ∘ (subst (Fin ∘ len) (sym eq₂))) (λ {((s , t , e) , j) → (s , t , α₁ (α₂ e)) , j}) (LHS.conns→ i)
                                                       ≡⟨ map-cong (λ p → subst-subst-sym eq₂ {p}) (λ _ → refl) (LHS.conns→ i) ⟩
          α-in-index (LHS.conns→ i) ∎
          where
            open ≡-Reasoning
            α₁-index₁ = Sum.map (subst (Fin ∘ len)      eq₁ ) (λ {((s , t , e) , j) → (s , t , α₁ e) , j})
            α₁-index₂ = Sum.map (subst (Fin ∘ len)      eq₂ ) (λ {((s , t , e) , j) → (s , t , α₁ e) , j})
            α₂-index₁ = Sum.map (subst (Fin ∘ len) (sym eq₁)) (λ {((s , t , e) , j) → (s , t , α₂ e) , j})
            α₂-index₂ = Sum.map (subst (Fin ∘ len) (sym eq₂)) (λ {((s , t , e) , j) → (s , t , α₂ e) , j})

            fα₁≡α₁f′ : ∀ e → RHS.conns→ (α₁-index₁ e) ≡ α₁-index₂ (f′.conns→ e)
            fα₁≡α₁f′ (inj₁ i) = {!!}
            fα₁≡α₁f′ (inj₂ ((s , t , inj₁ (inj₁ e)) , i)) with (Hypergraph.conns→ g (inj₂ ((s , t , e) , i)))
            fα₁≡α₁f′ (inj₂ ((s , t , inj₁ (inj₁ e)) , i))    | (inj₁ j) = cong inj₁ {!!}
            fα₁≡α₁f′ (inj₂ ((s , t , inj₁ (inj₁ e)) , i))    | (inj₂ _) = refl
            fα₁≡α₁f′ (inj₂ ((s , t , inj₁ (inj₂ e)) , i)) with (Hypergraph.conns→ g′ (inj₂ ((s , t , e) , i)))
            fα₁≡α₁f′ (inj₂ ((s , t , inj₁ (inj₂ e)) , i))    | (inj₁ j) = cong inj₁ {!!}
            fα₁≡α₁f′ (inj₂ ((s , t , inj₁ (inj₂ e)) , i))    | (inj₂ _) = refl
            fα₁≡α₁f′ (inj₂ ((s , t , inj₂ e) , i)) with (Hypergraph.conns→ g′′ (inj₂ ((s , t , e) , i)))
            fα₁≡α₁f′ (inj₂ ((s , t , inj₂ e) , i))    | (inj₁ j) = cong inj₁ {!!}
            fα₁≡α₁f′ (inj₂ ((s , t , inj₂ e) , i))    | (inj₂ _) = refl
              where
                fsuc-subst : ∀ {a b : ℕ} (eq₁ : a ≡ b) x → fsuc (subst Fin eq₁ x) ≡ subst Fin (cong suc eq₁) (fsuc x)
                fsuc-subst refl x = refl

                inject+-inject+ : ∀ {X Y Z : List VLabel} → (i : Fin (len X)) →
                                  inject+ ((len Y) + (len Z)) i ≡ subst (Fin ∘ len) (l++-assoc X Y Z) (inject+ (len Z) (inject+ (len Y) i))
                inject+-inject+ {zero , []} {Y} {Z} ()
                inject+-inject+ {suc l , X ∷ XS} {Y} {Z} (fsuc i) = begin
                  -- _ ≡⟨ cong fsuc (inject+-inject+ {l , XS} {Y} {Z} i) ⟩
                  _ ≡⟨ {!!} ⟩
                  _ ∎
                  where open ≡-Reasoning

                raise-inject+ : ∀ {X Y Z : List VLabel} → (i : Fin (len Y)) →
                                raise (len X) (inject+ (len Z) i) ≡ subst (Fin ∘ len) (l++-assoc X Y Z) (inject+ (len Z) (raise (len X) i))
                raise-inject+ {zero , []} {Y} {Z} i = refl
                raise-inject+ {suc l , X ∷ XS} {Y} {Z} i = begin
                  _ ≡⟨ cong fsuc (raise-inject+ {l , XS} {Y} {Z} i) ⟩
                  _ ≡⟨ cong fsuc (subst-∘ {P = Fin} {len} (l++-assoc (l , XS) Y Z)) ⟩
                  _ ≡⟨ fsuc-subst (cong len (l++-assoc (l , XS) Y Z)) (inject+ (len Z) (raise l i)) ⟩
                  _ ≡⟨ cong₂ (subst Fin) {u = fsuc (inject+ (len Z) (raise l i))} (begin
                    _ ≡˘⟨ cong-∘ {f = suc} {len} (l++-assoc (l , XS) Y Z)⟩
                    _ ≡⟨ cong-∘ {f = len} (l++-assoc (l , XS) Y Z)⟩
                    _ ∎) refl ⟩
                  _ ≡˘⟨ subst-∘ {P = Fin} {len} (l++-assoc (suc l , X ∷ XS) Y Z) ⟩
                  _ ∎
                  where open ≡-Reasoning
