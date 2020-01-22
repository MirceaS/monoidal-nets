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
open import Categories.Category
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

module Nets.Hypergraph {ℓₜ ℓₜᵣ : Level} (Types-setoid : Setoid ℓₜ ℓₜᵣ)
                       {ℓₒ ℓₒᵣ : Level}
                       (Obj-setoid :
                         Σ ℕ (Vec (Setoid.Carrier Types-setoid)) →  -- List T →
                         Σ ℕ (Vec (Setoid.Carrier Types-setoid)) →  -- List T →
                         Setoid ℓₒ ℓₒᵣ
                       ) where


--convinient way to represent lists as Vectors along with their size
List : ∀ {l} → Set l → Set l
List A = Σ ℕ (Vec A)

len         = proj₁
vec-of-list = proj₂


--bringing the contents of the setoids into scope as T._≈_ or Obj._≈_ etc.
module T = Setoid Types-setoid
T = T.Carrier

module Obj {input : _} {output : _} where
  open Setoid (Obj-setoid input output) public
Obj = Obj.Carrier


--utilities
Σ₂ : ∀ {a} {b} {c} (A : Set a) (B : Set b)
     (C : A → B → Set c) → Set (a ⊔ b ⊔ c)
Σ₂ A B C = Σ A λ a → Σ B λ b → C a b



record Hypergraph {l : Level} (input : List T) (output : List T) : Set ((lsuc l) ⊔ ℓₜ ⊔ ℓₜᵣ ⊔ ℓₒ) where
  field
    E : List T → List T → Set l

  Edge : Set (ℓₜ ⊔ l)
  Edge = Σ₂ (List T) (List T) E

  --input of the edge (s for source)
  s : Edge → List T
  s = proj₁

  --output of the edge (t for target)
  t : Edge → List T
  t = proj₁ ∘ proj₂

  -- type representing the ports that arrows go into
  in-index  = (Fin (len output)) ⊎ (Σ Edge (Fin ∘ len ∘ s))
  -- type representing the ports that arrows go out of
  out-index = (Fin (len input))  ⊎ (Σ Edge (Fin ∘ len ∘ t))

  in-lookup  : in-index  → T
  in-lookup  = [ lookup (vec-of-list output) , (λ {((s , _ , e) , i) → lookup (vec-of-list s) i})]′

  out-lookup : out-index → T
  out-lookup = [ lookup (vec-of-list input)  , (λ {((_ , t , e) , i) → lookup (vec-of-list t) i})]′

  field
    conns→ : out-index → in-index
    conns← : in-index → out-index
    type-match : (i : out-index) → out-lookup i T.≈ in-lookup (conns→ i)
    one-to-one : Inverseᵇ _≡_ _≡_ conns→ conns←    -- TODO replace with a newly defined edge equality?

  one-to-one₁ = proj₁ one-to-one
  one-to-one₂ = proj₂ one-to-one

  field
    --the label associated with each box
    o : ∀ {input output} → E input output → Obj {input} {output}

--hypergraph composition
_⊚_ : ∀ {l} {A B C : List T} → Hypergraph {l} B C → Hypergraph {l} A B → Hypergraph {l} A C
_⊚_ BC AB = record
  { E = E
  ; conns→ = conns→
  ; conns← = conns←
  ; type-match = type-match
  ; one-to-one = one-to-one
  ; o = [ AB.o , BC.o ]′
  }
  where
    module AB = Hypergraph AB
    module BC = Hypergraph BC
    E : _
    E input output = (AB.E input output) ⊎ (BC.E input output)

    -- →
    conns→ : _
    conns→ (inj₁ i) =
      [ (λ j →
          Sum.map₂
            (λ {((_ , _ , e) , k) → (_ , _ , inj₂ e) , k})
            (BC.conns→ (inj₁ j))
        )
      , (λ {((_ , _ , e) , j) → inj₂ ((_ , _ , inj₁ e) , j)})
      ]′ (AB.conns→ (inj₁ i))
    conns→ (inj₂ ((_ , _ , inj₁ e) , i)) =
      [ (λ j →
          Sum.map₂
            (λ {((_ , _ , e) , k) → (_ , _ , inj₂ e) , k})
            (BC.conns→ (inj₁ j))
        )
      , (λ {((_ , _ , e) , j) → inj₂ ((_ , _ , inj₁ e) , j)})
      ]′ (AB.conns→ (inj₂ ((_ , _ , e) , i)))
    conns→ (inj₂ ((_ , _ , inj₂ e) , j)) =
      Sum.map₂
        (λ {((_ , _ , e) , k) → (_ , _ , inj₂ e) , k})
        (BC.conns→ (inj₂ ((_ , _ , e) , j)))

    -- ←
    conns← : _
    conns← (inj₁ i) =
      [ (λ j →
          Sum.map₂
            (λ {((_ , _ , e) , k) → (_ , _ , inj₁ e) , k})
            (AB.conns← (inj₁ j))
        )
      , (λ {((_ , _ , e) , j) → inj₂ ((_ , _ , inj₂ e) , j)})
      ]′ (BC.conns← (inj₁ i))
    conns← (inj₂ ((_ , _ , inj₁ e) , j)) =
      Sum.map₂
        (λ {((_ , _ , e) , k) → (_ , _ , inj₁ e) , k})
        (AB.conns← (inj₂ ((_ , _ , e) , j)))
    conns← (inj₂ ((_ , _ , inj₂ e) , i)) =
      [ (λ j →
          Sum.map₂
            (λ {((_ , _ , e) , k) → (_ , _ , inj₁ e) , k})
            (AB.conns← (inj₁ j))
        )
      , (λ {((_ , _ , e) , j) → inj₂ ((_ , _ , inj₂ e) , j)})
      ]′ (BC.conns← (inj₂ ((_ , _ , e) , i)))

    --properties
    type-match : _
    type-match = {!!}
    one-to-one = {!!}
--                                   type-match : _
--                                   type-match = type-match′
--                                     where
--                                       open SetoidReasoning Types-setoid
--                                       type-match′ : _
--                                       type-match′ (inj₁ i) with (AB.conns→ (inj₁ i)) | (inspect AB.conns→ (inj₁ i))
--                                       type-match′ (inj₁ i) | (inj₁ j) | [ i→j ] with (BC.conns→ (inj₁ j)) | (inspect BC.conns→ (inj₁ j))
--                                       type-match′ (inj₁ i) | (inj₁ j) | [ i→j ] | (inj₁ _) | [ j→k ] = begin
--                                         _ ≈⟨ AB.type-match (inj₁ i) ⟩
--                                         _ ≡⟨ cong [ _ , _ ]′ i→j ⟩
--                                         _ ≈⟨ BC.type-match (inj₁ j) ⟩
--                                         _ ≡⟨ cong [ _ , _ ]′ j→k ⟩
--                                         _ ∎
--                                       type-match′ (inj₁ i) | (inj₁ j) | [ i→j ] | (inj₂ _) | [ j→k ] = begin
--                                         _ ≈⟨ AB.type-match (inj₁ i) ⟩
--                                         _ ≡⟨ cong [ _ , _ ]′ i→j ⟩
--                                         _ ≈⟨ BC.type-match (inj₁ j) ⟩
--                                         _ ≡⟨ cong [ _ , _ ]′ j→k ⟩
--                                         _ ∎
--                                       type-match′ (inj₁ i) | (inj₂ _) | [ i→j ] = begin
--                                         _ ≈⟨ AB.type-match (inj₁ i) ⟩
--                                         _ ≡⟨ cong [ _ , _ ]′ i→j ⟩
--                                         _ ∎
--                                       type-match′ (inj₂ ((inj₁ e) , i)) with (AB.conns→ (inj₂ (e , i))) | (inspect AB.conns→ (inj₂ (e , i)))
--                                       type-match′ (inj₂ ((inj₁ e) , i)) | (inj₁ j) | [ i→j ] with (BC.conns→ (inj₁ j)) | (inspect BC.conns→ (inj₁ j))
--                                       type-match′ (inj₂ ((inj₁ e) , i)) | (inj₁ j) | [ i→j ] | (inj₁ _) | [ j→k ] = begin
--                                         _ ≈⟨ AB.type-match (inj₂ (e , i)) ⟩
--                                         _ ≡⟨ cong [ _ , _ ]′ i→j ⟩
--                                         _ ≈⟨ BC.type-match (inj₁ j) ⟩
--                                         _ ≡⟨ cong [ _ , _ ]′ j→k ⟩
--                                         _ ∎
--                                       type-match′ (inj₂ ((inj₁ e) , i)) | (inj₁ j) | [ i→j ] | (inj₂ _) | [ j→k ] = begin
--                                         _ ≈⟨ AB.type-match (inj₂ (e , i)) ⟩
--                                         _ ≡⟨ cong [ _ , _ ]′ i→j ⟩
--                                         _ ≈⟨ BC.type-match (inj₁ j) ⟩
--                                         _ ≡⟨ cong [ _ , _ ]′ j→k ⟩
--                                         _ ∎
--                                       type-match′ (inj₂ ((inj₁ e) , i)) | (inj₂ _) | [ i→j ] = begin
--                                         _ ≈⟨ AB.type-match (inj₂ (e , i)) ⟩
--                                         _ ≡⟨ cong [ _ , _ ]′ i→j ⟩
--                                         _ ∎
--                                       type-match′ (inj₂ ((inj₂ e) , i)) with (BC.conns→ (inj₂ (e , i))) | (inspect BC.conns→ (inj₂ (e , i)))
--                                       type-match′ (inj₂ ((inj₂ e) , i)) | (inj₁ _) | [ i→j ] = begin
--                                         _ ≈⟨ BC.type-match (inj₂ (e , i)) ⟩
--                                         _ ≡⟨ cong [ _ , _ ]′ i→j ⟩
--                                         _ ∎
--                                       type-match′ (inj₂ ((inj₂ e) , i)) | (inj₂ _) | [ i→j ] = begin
--                                         _ ≈⟨ BC.type-match (inj₂ (e , i)) ⟩
--                                         _ ≡⟨ cong [ _ , _ ]′ i→j ⟩
--                                         _ ∎
--                                   one-to-one₁ : _
--                                   one-to-one₁ = one-to-one₁′
--                                     where
--                                       open ≡-Reasoning
--                                       one-to-one₁′ : _
--                                       one-to-one₁′ (inj₁ i) with (BC.conns← (inj₁ i)) | (inspect BC.conns← (inj₁ i))
--                                       one-to-one₁′ (inj₁ i) | (inj₁ j) | [ i→j ] with (AB.conns← (inj₁ j)) | (inspect AB.conns← (inj₁ j))
--                                       one-to-one₁′ (inj₁ i) | (inj₁ j) | [ i→j ] | (inj₁ _) | [ j→k ] = trans
--                                         (cong [ _ , _ ]′
--                                           (begin
--                                           _ ≡⟨ cong AB.conns→ (sym j→k) ⟩
--                                           _ ≡⟨ AB.one-to-one₁ (inj₁ j) ⟩
--                                           _ ∎))
--                                         (cong (Sum.map₂ _)
--                                           (begin
--                                           _ ≡⟨ cong BC.conns→ (sym i→j) ⟩
--                                           _ ≡⟨ BC.one-to-one₁ (inj₁ i) ⟩
--                                           _ ∎))
--                                       one-to-one₁′ (inj₁ i) | (inj₁ j) | [ i→j ] | (inj₂ _) | [ j→k ] = trans
--                                         (cong [ _ , _ ]′
--                                           (begin
--                                           _ ≡⟨ cong AB.conns→ (sym j→k) ⟩
--                                           _ ≡⟨ AB.one-to-one₁ (inj₁ j) ⟩
--                                           _ ∎))
--                                         (cong (Sum.map₂ _)
--                                           (begin
--                                           _ ≡⟨ cong BC.conns→ (sym i→j) ⟩
--                                           _ ≡⟨ BC.one-to-one₁ (inj₁ i) ⟩
--                                           _ ∎))
--                                       one-to-one₁′ (inj₁ i) | (inj₂ _) | [ i→j ] =
--                                         cong (Sum.map₂ _)
--                                           (begin
--                                           _ ≡⟨ cong BC.conns→ (sym i→j) ⟩
--                                           _ ≡⟨ BC.one-to-one₁ (inj₁ i) ⟩
--                                           _ ∎)
--                                       one-to-one₁′ (inj₂ (inj₁ e , i)) with (AB.conns← (inj₂ (e , i))) | (inspect AB.conns← (inj₂ (e , i)))
--                                       one-to-one₁′ (inj₂ (inj₁ e , i)) | (inj₁ _) | [ i→j ] =
--                                         cong [ _ , _ ]′
--                                           (begin
--                                           _ ≡⟨ cong AB.conns→ (sym i→j) ⟩
--                                           _ ≡⟨ AB.one-to-one₁ (inj₂ (e , i)) ⟩
--                                           _ ∎)
--                                       one-to-one₁′ (inj₂ (inj₁ e , i)) | (inj₂ _) | [ i→j ] =
--                                         cong [ _ , _ ]′
--                                           (begin
--                                           _ ≡⟨ cong AB.conns→ (sym i→j) ⟩
--                                           _ ≡⟨ AB.one-to-one₁ (inj₂ (e , i)) ⟩
--                                           _ ∎)
--                                       one-to-one₁′ (inj₂ (inj₂ e , i)) with (BC.conns← (inj₂ (e , i))) | (inspect BC.conns← (inj₂ (e , i)))
--                                       one-to-one₁′ (inj₂ (inj₂ e , i)) | (inj₁ j) | [ i→j ] with (AB.conns← (inj₁ j)) | (inspect AB.conns← (inj₁ j))
--                                       one-to-one₁′ (inj₂ (inj₂ e , i)) | (inj₁ j) | [ i→j ] | (inj₁ _) | [ j→k ] = trans
--                                         (cong [ _ , _ ]′
--                                           (begin
--                                           _ ≡⟨ cong AB.conns→ (sym j→k) ⟩
--                                           _ ≡⟨ AB.one-to-one₁ (inj₁ j) ⟩
--                                           _ ∎))
--                                         (cong (Sum.map₂ _)
--                                           (begin
--                                           _ ≡⟨ cong BC.conns→ (sym i→j) ⟩
--                                           _ ≡⟨ BC.one-to-one₁ (inj₂ (e , i)) ⟩
--                                           _ ∎))
--                                       one-to-one₁′ (inj₂ (inj₂ e , i)) | (inj₁ j) | [ i→j ] | (inj₂ _) | [ j→k ] = trans
--                                         (cong [ _ , _ ]′
--                                           (begin
--                                           _ ≡⟨ cong AB.conns→ (sym j→k) ⟩
--                                           _ ≡⟨ AB.one-to-one₁ (inj₁ j) ⟩
--                                           _ ∎))
--                                         (cong (Sum.map₂ _)
--                                           (begin
--                                           _ ≡⟨ cong BC.conns→ (sym i→j) ⟩
--                                           _ ≡⟨ BC.one-to-one₁ (inj₂ (e , i)) ⟩
--                                           _ ∎))
--                                       one-to-one₁′ (inj₂ (inj₂ e , i)) | (inj₂ _) | [ i→j ] =
--                                         cong (Sum.map₂ _)
--                                           (begin
--                                           _ ≡⟨ cong BC.conns→ (sym i→j) ⟩
--                                           _ ≡⟨ BC.one-to-one₁ (inj₂ (e , i)) ⟩
--                                           _ ∎)
--                                   one-to-one₂ : _
--                                   one-to-one₂ = one-to-one₂′
--                                     where
--                                       open ≡-Reasoning
--                                       one-to-one₂′ : _
--                                       one-to-one₂′ (inj₁ i) with (AB.conns→ (inj₁ i)) | (inspect AB.conns→ (inj₁ i))
--                                       one-to-one₂′ (inj₁ i) | (inj₁ j) | [ i→j ] with (BC.conns→ (inj₁ j)) | (inspect BC.conns→ (inj₁ j))
--                                       one-to-one₂′ (inj₁ i) | (inj₁ j) | [ i→j ] | (inj₁ _) | [ j→k ] = trans
--                                         (cong [ _ , _ ]′
--                                           (begin
--                                           _ ≡⟨ cong BC.conns← (sym j→k) ⟩
--                                           _ ≡⟨ BC.one-to-one₂ (inj₁ j) ⟩
--                                           _ ∎))
--                                         (cong (Sum.map₂ _)
--                                           (begin
--                                           _ ≡⟨ cong AB.conns← (sym i→j) ⟩
--                                           _ ≡⟨ AB.one-to-one₂ (inj₁ i) ⟩
--                                           _ ∎))
--                                       one-to-one₂′ (inj₁ i) | (inj₁ j) | [ i→j ] | (inj₂ _) | [ j→k ] = trans
--                                         (cong [ _ , _ ]′
--                                           (begin
--                                           _ ≡⟨ cong BC.conns← (sym j→k) ⟩
--                                           _ ≡⟨ BC.one-to-one₂ (inj₁ j) ⟩
--                                           _ ∎))
--                                         (cong (Sum.map₂ _)
--                                           (begin
--                                           _ ≡⟨ cong AB.conns← (sym i→j) ⟩
--                                           _ ≡⟨ AB.one-to-one₂ (inj₁ i) ⟩
--                                           _ ∎))
--                                       one-to-one₂′ (inj₁ i) | (inj₂ _) | [ i→j ] =
--                                         cong (Sum.map₂ _)
--                                           (begin
--                                           _ ≡⟨ cong AB.conns← (sym i→j) ⟩
--                                           _ ≡⟨ AB.one-to-one₂ (inj₁ i) ⟩
--                                           _ ∎)
--                                       one-to-one₂′ (inj₂ (inj₁ e , i)) with (AB.conns→ (inj₂ (e , i))) | (inspect AB.conns→ (inj₂ (e , i)))
--                                       one-to-one₂′ (inj₂ (inj₁ e , i)) | (inj₁ j) | [ i→j ] with (BC.conns→ (inj₁ j)) | (inspect BC.conns→ (inj₁ j))
--                                       one-to-one₂′ (inj₂ (inj₁ e , i)) | (inj₁ j) | [ i→j ] | (inj₁ _) | [ j→k ] = trans
--                                         (cong [ _ , _ ]′
--                                           (begin
--                                           _ ≡⟨ cong BC.conns← (sym j→k) ⟩
--                                           _ ≡⟨ BC.one-to-one₂ (inj₁ j) ⟩
--                                           _ ∎))
--                                         (cong (Sum.map₂ _)
--                                           (begin
--                                           _ ≡⟨ cong AB.conns← (sym i→j) ⟩
--                                           _ ≡⟨ AB.one-to-one₂ (inj₂ (e , i)) ⟩
--                                           _ ∎))
--                                       one-to-one₂′ (inj₂ (inj₁ e , i)) | (inj₁ j) | [ i→j ] | (inj₂ _) | [ j→k ] = trans
--                                         (cong [ _ , _ ]′
--                                           (begin
--                                           _ ≡⟨ cong BC.conns← (sym j→k) ⟩
--                                           _ ≡⟨ BC.one-to-one₂ (inj₁ j) ⟩
--                                           _ ∎))
--                                         (cong (Sum.map₂ _)
--                                           (begin
--                                           _ ≡⟨ cong AB.conns← (sym i→j) ⟩
--                                           _ ≡⟨ AB.one-to-one₂ (inj₂ (e , i)) ⟩
--                                           _ ∎))
--                                       one-to-one₂′ (inj₂ (inj₁ e , i)) | (inj₂ _) | [ i→j ] =
--                                         cong (Sum.map₂ _)
--                                           (begin
--                                           _ ≡⟨ cong AB.conns← (sym i→j) ⟩
--                                           _ ≡⟨ AB.one-to-one₂ (inj₂ (e , i)) ⟩
--                                           _ ∎)
--                                       one-to-one₂′ (inj₂ (inj₂ e , i)) with (BC.conns→ (inj₂ (e , i))) | (inspect BC.conns→ (inj₂ (e , i)))
--                                       one-to-one₂′ (inj₂ (inj₂ e , i)) | (inj₁ _) | [ i→j ] =
--                                         cong [ _ , _ ]′
--                                           (begin
--                                           _ ≡⟨ cong BC.conns← (sym i→j) ⟩
--                                           _ ≡⟨ BC.one-to-one₂ (inj₂ (e , i)) ⟩
--                                           _ ∎)
--                                       one-to-one₂′ (inj₂ (inj₂ e , i)) | (inj₂ _) | [ i→j ] =
--                                         cong [ _ , _ ]′
--                                           (begin
--                                           _ ≡⟨ cong BC.conns← (sym i→j) ⟩
--                                           _ ≡⟨ BC.one-to-one₂ (inj₂ (e , i)) ⟩
--                                           _ ∎)
--                                   one-to-one : _
--                                   one-to-one = one-to-one₁ , one-to-one₂

--hypergraph equivalence
record _≋_ {l} {A B : List T} (G H : Hypergraph {l} A B) : Set (l ⊔ ℓₜ ⊔ ℓₜᵣ ⊔ ℓₒ ⊔ ℓₒᵣ) where
  module G = Hypergraph G
  module H = Hypergraph H
  field
    α : ∀ {input output} → G.E input output → H.E input output
    α′ : ∀ {input output} → H.E input output → G.E input output

    one-to-one : ∀ {input output} → Inverseᵇ _≡_ _≡_ (α {input} {output}) (α′)  -- TODO again, maybe change this to some new edge equality?
    obj-resp : ∀ {input output} → (e : G.E input output) → (G.o e) Obj.≈ (H.o (α e))

  α-in-index :  G.in-index  → H.in-index
  α-in-index  = Sum.map₂ (Prod.map (λ {(_ , _ , e) → _ , _ , α e}) id)
  α-out-index : G.out-index → H.out-index
  α-out-index = Sum.map₂ (Prod.map (λ {(_ , _ , e) → _ , _ , α e}) id)

  field
    conns→-resp : (i : G.out-index) →
                   H.conns→ (α-out-index i) ≡ α-in-index (G.conns→ i)  -- TODO again, maybe change this to some new edge equality?
    -- this one is redundant
    -- conns←-resp : {i : G.in-index} →
    --                H.conns← (α-in-index i) ≡ α-out-index (G.conns← i)


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

-- record SimpleHypergraph {ℓᵣ : Level} (input : List T) (output : List T) : Set (ℓₜ ⊔ ℓₜᵣ ⊔ (lsuc ℓᵣ) ⊔ (lsuc ℓₒ)) where
--   field
--     hg : Hypergraph input output

--   open Hypergraph hg public

--   field
--     _≲_ : Rel (Fin E-size) ℓᵣ
--     partial_order : IsPartialOrder _≡_ _≲_
--     conns-resp-≲     : (i : Fin E-size) → (j : Fin (proj₁ (E-outputs at (fsuc i)))) →
--                        (Fin-pm (proj₁ (conns→ ((fsuc i) , j))) ⊤' (i ≲_))
--     conns-resp-≲-neq : (i : Fin E-size) → (j : Fin (proj₁ (E-outputs at (fsuc i)))) →
--                        (Fin-pm (proj₁ (conns→ ((fsuc i) , j))) ⊤' (i ≢_))

Hypergraph-Category : ∀ {l} → Category ℓₜ ((lsuc l) ⊔ ℓₜ ⊔ ℓₜᵣ ⊔ ℓₒ) (l ⊔ ℓₜ ⊔ ℓₜᵣ ⊔ ℓₒ ⊔ ℓₒᵣ)
Hypergraph-Category {l} = record
  { Obj = List T
  ; _⇒_ = Hypergraph {l}
  ; _≈_ = _≋_
  ; id = ⊚-id
  ; _∘_ = _⊚_
  ; assoc = ⊚-assoc
  ; sym-assoc = {!!}
  ; identityˡ = {!!}
  ; identityʳ = {!!}
  ; equiv = {!!}
  ; ∘-resp-≈ = {!!}
  }
