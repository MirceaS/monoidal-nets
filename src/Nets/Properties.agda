open import Level renaming (zero to lzero ; suc to lsuc)
open import Agda.Builtin.Equality
open import Data.Product as Prod using (Σ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum as Sum using (_⊎_ ; inj₁ ; inj₂ ; [_,_]′)
open import Data.Nat hiding (_⊔_)
open import Data.Vec hiding (splitAt)
open import Data.Fin renaming (zero to fzero ; suc to fsuc)
open import Data.Empty.Polymorphic
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Function using (_∘_ ; Inverseᵇ ; id)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning
open import Categories.Category

import Nets.Hypergraph

module Nets.Properties {ℓₜ ℓₜᵣ : Level} (Types-setoid : Setoid ℓₜ ℓₜᵣ)
                       {ℓₒ ℓₒᵣ : Level}
                       (Obj-setoid :
                         Σ ℕ (Vec (Setoid.Carrier Types-setoid)) →  -- List T →
                         Σ ℕ (Vec (Setoid.Carrier Types-setoid)) →  -- List T →
                         Setoid ℓₒ ℓₒᵣ
                       ) where

open Nets.Hypergraph Types-setoid Obj-setoid



⊚-assoc : {l : Level}
          {A B C D : List T} {f : Hypergraph {l} A B}
          {g : Hypergraph {l} B C} {h : Hypergraph {l} C D} →
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
  ; one-to-one = (λ
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
  ; obj-resp = λ
    { (inj₁ x)        → Obj.refl
    ; (inj₂ (inj₁ x)) → Obj.refl
    ; (inj₂ (inj₂ x)) → Obj.refl
    }
  ; conns→-resp = conns→-resp
  }
  where
    module f = Hypergraph f
    module g = Hypergraph g
    module h = Hypergraph h
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

⊚-id : ∀ {l} {A} → Hypergraph {l} A A
⊚-id = record
  { E = λ _ _ → ⊥
  ; conns→ = λ {(inj₁ x) → inj₁ x}
  ; conns← = λ {(inj₁ x) → inj₁ x}
  ; type-match = λ {(inj₁ _) → T.refl}
  ; one-to-one = (λ {(inj₁ _) → refl}) ,
                 (λ {(inj₁ _) → refl})
  ; o = λ ()
  }


≋-equiv : ∀ {l A B} → IsEquivalence (_≋_ {l} {A} {B})
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
      ; one-to-one = (λ _ → refl) , (λ _ → refl)
      ; obj-resp = λ _ → Obj.refl
      ; conns→-resp = conns→-resp
      }
      where
        module f = Hypergraph f
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
      ; one-to-one = one-to-one
      ; obj-resp = obj-resp
      ; conns→-resp = conns→-resp
      }
      where
        module fg = _≋_ f≋g
        one-to-one : ∀ {input output} → Inverseᵇ _≡_ _≡_ (fg.α′ {input} {output}) (fg.α)
        one-to-one {input} {output} = Prod.swap (fg.one-to-one {input} {output})
        obj-resp : ∀ {input output} → (e : fg.H.E input output) → fg.H.o e Obj.≈ fg.G.o (fg.α′ e)
        obj-resp {input} {output} e = begin
          _ ≡˘⟨ cong fg.H.o (proj₁ fg.one-to-one e) ⟩
          _ ≈˘⟨ fg.obj-resp (fg.α′ e) ⟩
          _ ∎
          where open SetoidReasoning (Obj-setoid input output)
        conns→-resp : _
        conns→-resp (inj₁ i) with (fg.G.conns→ (inj₁ i))
                         | (inspect fg.G.conns→ (inj₁ i))
        conns→-resp (inj₁ i)    | (inj₁ j) | [ gj ] = begin
          _ ≡˘⟨ cong ((Sum.map₂ _) ∘ (Sum.map₂ _)) gj ⟩
          _ ≡˘⟨ cong (Sum.map₂ _) (fg.conns→-resp (inj₁ i)) ⟩
          _ ∎
          where open ≡-Reasoning
        conns→-resp (inj₁ i)    | (inj₂ ((_ , _ , e′) , j)) | [ gj ] = begin
          _ ≡˘⟨ cong (λ x → inj₂ ((_ , _ , x) , j)) (proj₂ fg.one-to-one e′) ⟩
          _ ≡˘⟨ cong ((Sum.map₂ _) ∘ (Sum.map₂ _)) gj ⟩
          _ ≡˘⟨ cong (Sum.map₂ _) (fg.conns→-resp (inj₁ i)) ⟩
          _ ∎
          where open ≡-Reasoning
        conns→-resp (inj₂ ((_ , _ , e) , i)) with (fg.G.conns→ (inj₂ ((_ , _ , fg.α′ e) , i)))
                                         | (inspect fg.G.conns→ (inj₂ ((_ , _ , fg.α′ e) , i)))
        conns→-resp (inj₂ ((_ , _ , e) , i))    | (inj₁ j) | [ gj ] = begin
          _ ≡˘⟨ cong ((Sum.map₂ _) ∘ (Sum.map₂ _)) gj ⟩
          _ ≡˘⟨ cong (Sum.map₂ _) (fg.conns→-resp (inj₂ ((_ , _ , fg.α′ e) , i))) ⟩
          _ ≡⟨ cong (λ x → Sum.map₂ _ (fg.H.conns→ (inj₂ ((_ , _ , x) , i)))) (proj₁ fg.one-to-one e) ⟩
          _ ∎
          where open ≡-Reasoning
        conns→-resp (inj₂ ((_ , _ , e) , i))    | (inj₂ ((_ , _ , e′) , j)) | [ gj ] = begin
          _ ≡˘⟨ cong (λ x → inj₂ ((_ , _ , x) , j)) (proj₂ fg.one-to-one e′) ⟩
          _ ≡˘⟨ cong ((Sum.map₂ _) ∘ (Sum.map₂ _)) gj ⟩
          _ ≡˘⟨ cong (Sum.map₂ _) (fg.conns→-resp (inj₂ ((_ , _ , fg.α′ e) , i))) ⟩
          _ ≡⟨ cong (λ x → Sum.map₂ _ (fg.H.conns→ (inj₂ ((_ , _ , x) , i)))) (proj₁ fg.one-to-one e) ⟩
          _ ∎
          where open ≡-Reasoning
    ≋-trans : Transitive _≋_
    ≋-trans f≋g g≋h = record
      { α = gh.α ∘ fg.α
      ; α′ = fg.α′ ∘ gh.α′
      ; one-to-one = one-to-one
      ; obj-resp = obj-resp
      ; conns→-resp = conns→-resp
      }
      where
        module fg = _≋_ f≋g
        module gh = _≋_ g≋h
        one-to-one : ∀ {input output} → Inverseᵇ _≡_ _≡_ ((gh.α {_} {output}) ∘ (fg.α {input})) (fg.α′ ∘ gh.α′)
        one-to-one {input} {output} =
          (λ x → trans (cong gh.α (proj₁ fg.one-to-one (gh.α′ x))) (proj₁ gh.one-to-one x)) ,
          (λ x → trans (cong fg.α′ (proj₂ gh.one-to-one (fg.α x))) (proj₂ fg.one-to-one x))
        obj-resp : ∀ {input output} → (e : fg.G.E input output) → fg.G.o e Obj.≈ gh.H.o (gh.α (fg.α e))
        obj-resp {input} {output} e = Obj.trans (fg.obj-resp e) (gh.obj-resp (fg.α e))
        conns→-resp : _
        conns→-resp (inj₁ i) with (fg.G.conns→ (inj₁ i))
                         | (inspect fg.G.conns→ (inj₁ i))
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
        conns→-resp (inj₂ ((_ , _ , e) , i)) with (fg.G.conns→ (inj₂ ((_ , _ , e) , i)))
                                         | (inspect fg.G.conns→ (inj₂ ((_ , _ , e) , i)))
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


⊚-identityˡ : ∀ {l} {A B : List T} {f : Hypergraph {l} A B} → (⊚-id ⊚ f) ≋ f
⊚-identityˡ {l} {A} {B} {f} = record
  { α = λ {(inj₁ e) → e}
  ; α′ = inj₁
  ; one-to-one = (λ _ → refl) ,
                 (λ {(inj₁ _) → refl})
  ; obj-resp = λ {(inj₁ _) → Obj.refl}
  ; conns→-resp = conns→-resp
  }
  where
    module f = Hypergraph f
    conns→-resp : _
    conns→-resp (inj₁ i) with (f.conns→ (inj₁ i))
    conns→-resp (inj₁ i)    | (inj₁ _) = refl
    conns→-resp (inj₁ i)    | (inj₂ _) = refl
    conns→-resp (inj₂ ((_ , _ , inj₁ e) , i)) with (f.conns→ (inj₂ ((_ , _ , e) , i)))
    conns→-resp (inj₂ ((_ , _ , inj₁ e) , i))    | (inj₁ _) = refl
    conns→-resp (inj₂ ((_ , _ , inj₁ e) , i))    | (inj₂ _) = refl

⊚-identityʳ : ∀ {l} {A B : List T} {f : Hypergraph {l} A B} → (f ⊚ ⊚-id) ≋ f
⊚-identityʳ {l} {A} {B} {f} = record
  { α = λ {(inj₂ e) → e}
  ; α′ = inj₂
  ; one-to-one = (λ _ → refl) ,
                 (λ {(inj₂ _) → refl})
  ; obj-resp = λ {(inj₂ _) → Obj.refl}
  ; conns→-resp = conns→-resp
  }
  where
    module f = Hypergraph f
    conns→-resp : _
    conns→-resp (inj₁ i) with (f.conns→ (inj₁ i))
    conns→-resp (inj₁ i)    | (inj₁ _) = refl
    conns→-resp (inj₁ i)    | (inj₂ _) = refl
    conns→-resp (inj₂ ((_ , _ , inj₂ e) , i)) with (f.conns→ (inj₂ ((_ , _ , e) , i)))
    conns→-resp (inj₂ ((_ , _ , inj₂ e) , i))    | (inj₁ _) = refl
    conns→-resp (inj₂ ((_ , _ , inj₂ e) , i))    | (inj₂ _) = refl


⊚-resp-≋ : ∀ {l} {A B C : List T} {f h : Hypergraph {l} B C} {g i : Hypergraph {l} A B} →
            f ≋ h → g ≋ i → (f ⊚ g) ≋ (h ⊚ i)
⊚-resp-≋ f≋h g≋i = record
  { α = Sum.map gi.α fh.α
  ; α′ = Sum.map gi.α′ fh.α′
  ; one-to-one = (λ { (inj₁ e) → cong inj₁ (proj₁ gi.one-to-one e)
                    ; (inj₂ e) → cong inj₂ (proj₁ fh.one-to-one e) }) ,
                 (λ { (inj₁ e) → cong inj₁ (proj₂ gi.one-to-one e)
                    ; (inj₂ e) → cong inj₂ (proj₂ fh.one-to-one e) })
  ; obj-resp = λ { (inj₁ e) → gi.obj-resp e
                 ; (inj₂ e) → fh.obj-resp e }
  ; conns→-resp = conns→-resp
  }
  where
    module fh = _≋_ f≋h
    module gi = _≋_ g≋i
    conns→-resp : _
    conns→-resp = {!!}

Hypergraph-Category : ∀ {l} → Category ℓₜ ((lsuc l) ⊔ ℓₜ ⊔ ℓₜᵣ ⊔ ℓₒ) (l ⊔ ℓₜ ⊔ ℓₜᵣ ⊔ ℓₒ ⊔ ℓₒᵣ)
Hypergraph-Category {l} = record
  { Obj = List T
  ; _⇒_ = Hypergraph {l}
  ; _≈_ = _≋_
  ; id = ⊚-id
  ; _∘_ = _⊚_
  ; assoc = ⊚-assoc
  ; sym-assoc = ≋-equiv.sym ⊚-assoc
  ; identityˡ = ⊚-identityˡ
  ; identityʳ = ⊚-identityʳ
  ; equiv = ≋-equiv
  ; ∘-resp-≈ = ⊚-resp-≋
  }
  where
    module ≋-equiv {A} {B} = IsEquivalence (≋-equiv {l} {A} {B})
