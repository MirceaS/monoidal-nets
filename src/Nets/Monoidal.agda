open import Level renaming (zero to lzero ; suc to lsuc)
open import Agda.Builtin.Equality
open import Data.Product as Prod using (Σ ; _,_ ; proj₁ ; proj₂ ; _×_)
open import Data.Sum as Sum using (_⊎_ ; inj₁ ; inj₂ ; [_,_]′)
open import Data.Sum.Properties using ([,]-∘-distr ; [,]-map-commute)
open import Data.Nat hiding (_⊔_)
open import Data.Vec hiding (splitAt)
open import Data.Fin renaming (zero to fzero ; suc to fsuc)
open import Data.Fin.Properties using (¬Fin0 ; inject+-raise-splitAt ; splitAt-inject+ ; splitAt-raise)
open import Data.Empty using (⊥-elim)
open import Data.Empty.Polymorphic renaming (⊥-elim to ⊥-elim′)
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality
open import Function using (_∘_ ; Inverseᵇ ; id)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning
open import Categories.Category
open import Categories.Category.Product
open import Categories.Category.Monoidal

import Nets.Properties
import Nets.Hypergraph hiding (_⊚_)

module Nets.Monoidal {ℓₜ ℓₜᵣ : Level} (VLabel-setoid : Setoid ℓₜ ℓₜᵣ)
                       {ℓₒ ℓₒᵣ : Level}
                       (ELabel-setoid :
                         Σ ℕ (Vec (Setoid.Carrier VLabel-setoid)) →  -- List VLabel →
                         Σ ℕ (Vec (Setoid.Carrier VLabel-setoid)) →  -- List VLabel →
                         Setoid ℓₒ ℓₒᵣ
                       ) where

open Nets.Properties VLabel-setoid ELabel-setoid
open Nets.Hypergraph VLabel-setoid ELabel-setoid

l++-identityʳ : ∀ {l} {A : Set l} (xs : Σ _ (Vec A)) → xs ≡ xs l++ (zero , [])
l++-identityʳ (zero , []) = refl
l++-identityʳ ((suc n) , (x ∷ xs)) = cong ((suc zero , x ∷ []) l++_) (l++-identityʳ (n , xs))

Hypergraph-Monoidal : ∀ {l} → Monoidal (Hypergraph-Category {l})
Hypergraph-Monoidal {l} = record
  { ⊗ = record
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
        hom {proj₁ X} {proj₂ X} {proj₁ Y} {proj₂ Y}
            {proj₁ Z} {proj₂ Z} {proj₁ f} {proj₂ f}
            {proj₁ g} {proj₂ g} }
    ; F-resp-≈ = λ {A} {B} {fg₁} {fg₂} f=f,g=g → record {
        F-resp-≈ {proj₁ A}   {proj₁ B}   {proj₂ A}   {proj₂ B}
                 {proj₁ fg₁} {proj₁ fg₂} {proj₂ fg₁} {proj₂ fg₂}
                 f=f,g=g } 
    }
  ; unit = zero , []
  ; unitorˡ = record { from = HC.id; to = HC.id ; iso = record
                       { isoˡ = HC.identityˡ {f = HC.id}
                       ; isoʳ = HC.identityˡ {f = HC.id}
                       }
                     }
  ; unitorʳ = λ {X} → record
    { from = subst (HC._⇒ X) (l++-identityʳ X) HC.id
    ; to = subst (X HC.⇒_) (l++-identityʳ X) HC.id
    ; iso = {!!} -- record { isoˡ = {!unitorʳ-isoˡ!} {- unitorʳ-isoˡ -} ; isoʳ = {!!} }
    }
  ; associator = {!!}
  ; unitorˡ-commute-from = {!!}
  ; unitorˡ-commute-to = {!!}
  ; unitorʳ-commute-from = {!!}
  ; unitorʳ-commute-to = {!!}
  ; assoc-commute-from = {!!}
  ; assoc-commute-to = {!!}
  ; triangle = {!!}
  ; pentagon = {!!}
  }
  where
    module HC = Category (Hypergraph-Category {l})
    module hom {X₁} {X₂} {Y₁} {Y₂} {Z₁} {Z₂}
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
      conns→-resp (inj₁ i)    | (inj₁ i₁)    | (inj₁ j) with (g₁.conns→ (inj₁ j)) | (inspect (g₁.conns→) (inj₁ j))
      conns→-resp (inj₁ i)    | (inj₁ i₁)    | (inj₁ j)    | (inj₁ _) | [ j=k ] = begin
        _ ≡⟨ cong ([ _ , _ ]′ ∘ [ _ , _ ]′) (splitAt-inject+ (len Y₁) (len Y₂) j) ⟩
        _ ≡⟨ cong ([ _ , _ ]′ ∘ [ _ , _ ]′) j=k ⟩
        _ ∎
        where open ≡-Reasoning
      conns→-resp (inj₁ i)    | (inj₁ i₁)    | (inj₁ j)    | (inj₂ _) | [ j=k ] = begin
        _ ≡⟨ cong ([ _ , _ ]′ ∘ [ _ , _ ]′) (splitAt-inject+ (len Y₁) (len Y₂) j) ⟩
        _ ≡⟨ cong ([ _ , _ ]′ ∘ [ _ , _ ]′) j=k ⟩
        _ ∎
        where open ≡-Reasoning
      conns→-resp (inj₁ i)    | (inj₁ i₁)    | (inj₂ _) = refl
      conns→-resp (inj₁ i)    | (inj₂ i₂) with (f₂.conns→ (inj₁ i₂))
      conns→-resp (inj₁ i)    | (inj₂ i₂)    | (inj₁ j) with (g₂.conns→ (inj₁ j)) | (inspect (g₂.conns→) (inj₁ j))
      conns→-resp (inj₁ i)    | (inj₂ i₂)    | (inj₁ j)    | (inj₁ _) | [ j=k ] = begin
        _ ≡⟨ cong ([ _ , _ ]′ ∘ [ _ , _ ]′) (splitAt-raise (len Y₁) (len Y₂) j) ⟩
        _ ≡⟨ cong ([ _ , _ ]′ ∘ [ _ , _ ]′) j=k ⟩
        _ ∎
        where open ≡-Reasoning
      conns→-resp (inj₁ i)    | (inj₂ i₂)    | (inj₁ j)    | (inj₂ _) | [ j=k ] = begin
        _ ≡⟨ cong ([ _ , _ ]′ ∘ [ _ , _ ]′) (splitAt-raise (len Y₁) (len Y₂) j) ⟩
        _ ≡⟨ cong ([ _ , _ ]′ ∘ [ _ , _ ]′) j=k ⟩
        _ ∎
        where open ≡-Reasoning
      conns→-resp (inj₁ i)    | (inj₂ i₂)    | (inj₂ _) = refl
      conns→-resp (inj₂ ((_ , _ , inj₁ (inj₁ e)) , i)) with (f₁.conns→ (inj₂ ((_ , _ , e) , i)))
      conns→-resp (inj₂ ((_ , _ , inj₁ (inj₁ e)) , i))    | (inj₁ j) with (g₁.conns→ (inj₁ j)) | (inspect (g₁.conns→) (inj₁ j))
      conns→-resp (inj₂ ((_ , _ , inj₁ (inj₁ e)) , i))    | (inj₁ j)    | (inj₁ _) | [ j=k ] = begin
        _ ≡⟨ cong ([ _ , _ ]′ ∘ [ _ , _ ]′) (splitAt-inject+ (len Y₁) (len Y₂) j) ⟩
        _ ≡⟨ cong ([ _ , _ ]′ ∘ [ _ , _ ]′) j=k ⟩
        _ ∎
        where open ≡-Reasoning
      conns→-resp (inj₂ ((_ , _ , inj₁ (inj₁ e)) , i))    | (inj₁ j)    | (inj₂ _) | [ j=k ] = begin
        _ ≡⟨ cong ([ _ , _ ]′ ∘ [ _ , _ ]′) (splitAt-inject+ (len Y₁) (len Y₂) j) ⟩
        _ ≡⟨ cong ([ _ , _ ]′ ∘ [ _ , _ ]′) j=k ⟩
        _ ∎
        where open ≡-Reasoning
      conns→-resp (inj₂ ((_ , _ , inj₁ (inj₁ e)) , i))    | (inj₂ _) = refl
      conns→-resp (inj₂ ((_ , _ , inj₁ (inj₂ e)) , i)) with (g₁.conns→ (inj₂ ((_ , _ , e) , i)))
      conns→-resp (inj₂ ((_ , _ , inj₁ (inj₂ e)) , i))    | (inj₁ _) = refl
      conns→-resp (inj₂ ((_ , _ , inj₁ (inj₂ e)) , i))    | (inj₂ _) = refl
      conns→-resp (inj₂ ((_ , _ , inj₂ (inj₁ e)) , i)) with (f₂.conns→ (inj₂ ((_ , _ , e) , i)))
      conns→-resp (inj₂ ((_ , _ , inj₂ (inj₁ e)) , i))    | (inj₁ j) with (g₂.conns→ (inj₁ j)) | (inspect (g₂.conns→) (inj₁ j))
      conns→-resp (inj₂ ((_ , _ , inj₂ (inj₁ e)) , i))    | (inj₁ j)    | (inj₁ _) | [ j=k ] = begin
        _ ≡⟨ cong ([ _ , _ ]′ ∘ [ _ , _ ]′) (splitAt-raise (len Y₁) (len Y₂) j) ⟩
        _ ≡⟨ cong ([ _ , _ ]′ ∘ [ _ , _ ]′) j=k ⟩
        _ ∎
        where open ≡-Reasoning
      conns→-resp (inj₂ ((_ , _ , inj₂ (inj₁ e)) , i))    | (inj₁ j)    | (inj₂ _) | [ j=k ] = begin
        _ ≡⟨ cong ([ _ , _ ]′ ∘ [ _ , _ ]′) (splitAt-raise (len Y₁) (len Y₂) j) ⟩
        _ ≡⟨ cong ([ _ , _ ]′ ∘ [ _ , _ ]′) j=k ⟩
        _ ∎
        where open ≡-Reasoning
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
      conns→-resp (inj₁ i)    | (inj₁ _) = begin
        _ ≡⟨ cong [ _ , _ ]′ (ff.conns→-resp _) ⟩
        _ ≡⟨  [,]-map-commute (ff.LHS.conns→ _) ⟩
        _ ≡˘⟨ [,]-map-commute (ff.LHS.conns→ _) ⟩
        _ ∎
        where open ≡-Reasoning
      conns→-resp (inj₁ i)    | (inj₂ _) = begin
        _ ≡⟨ cong [ _ , _ ]′ (gg.conns→-resp _) ⟩
        _ ≡⟨  [,]-map-commute (gg.LHS.conns→ _) ⟩
        _ ≡˘⟨ [,]-map-commute (gg.LHS.conns→ _) ⟩
        _ ∎
        where open ≡-Reasoning
      conns→-resp (inj₂ ((_ , _ , inj₁ e) , i)) = begin
        _ ≡⟨ cong [ _ , _ ]′ (ff.conns→-resp _) ⟩
        _ ≡⟨  [,]-map-commute (ff.LHS.conns→ _) ⟩
        _ ≡˘⟨ [,]-map-commute (ff.LHS.conns→ _) ⟩
        _ ∎
        where open ≡-Reasoning
      conns→-resp (inj₂ ((_ , _ , inj₂ e) , i)) = begin
        _ ≡⟨ cong [ _ , _ ]′ (gg.conns→-resp _) ⟩
        _ ≡⟨  [,]-map-commute (gg.LHS.conns→ _) ⟩
        _ ≡˘⟨ [,]-map-commute (gg.LHS.conns→ _) ⟩
        _ ∎
        where open ≡-Reasoning

    {- unitorʳ-isoˡ : (Hypergraph-Category Category.≈ (Hypergraph-Category Category.∘ subst (λ section → Hypergraph _ section) (l++-identityʳ _) ⊚-id) (subst (λ section → Hypergraph section _) (l++-identityʳ _) ⊚-id)) (Category.id Hypergraph-Category)
    unitorʳ-isoˡ = HC.Equiv.trans {!!} (HC.identityˡ {f = HC.id}) -}
