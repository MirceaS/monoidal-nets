open import Level renaming (zero to lzero ; suc to lsuc)
open import Agda.Builtin.Equality
open import Data.Product as Prod using (Σ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum as Sum using (_⊎_ ; inj₁ ; inj₂ ; [_,_]′)
open import Data.Nat hiding (_⊔_)
open import Data.Vec hiding (splitAt)
open import Data.Vec.Properties using (lookup-splitAt ; lookup-++ˡ ; lookup-++ʳ)
open import Data.Fin renaming (zero to fzero ; suc to fsuc ; _+_ to _f+_)
open import Data.Fin.Properties using (splitAt-inject+ ; splitAt-raise ; inject+-raise-splitAt)
open import Data.Empty.Polymorphic
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Function using (_∘_ ; Inverseᵇ ; id)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

module Nets.Hypergraph {ℓₜ ℓₜᵣ : Level} (VLabel-setoid : Setoid ℓₜ ℓₜᵣ)
                       {ℓₒ ℓₒᵣ : Level}
                       (ELabel-setoid :
                         Σ ℕ (Vec (Setoid.Carrier VLabel-setoid)) →  -- List VLabel →
                         Σ ℕ (Vec (Setoid.Carrier VLabel-setoid)) →  -- List VLabel →
                         Setoid ℓₒ ℓₒᵣ
                       ) where


--convinient way to represent lists as Vectors along with their size
List : ∀ {l} → Set l → Set l
List A = Σ ℕ (Vec A)

len         = proj₁
vec-of-list = proj₂


--bringing the contents of the setoids into scope as VLabel._≈_ or ELabel._≈_ etc.
module VLabel = Setoid VLabel-setoid
VLabel = VLabel.Carrier

module ELabel {input : _} {output : _} = Setoid (ELabel-setoid input output)
ELabel = ELabel.Carrier


--utilities
Σ₂ : ∀ {a} {b} {c} (A : Set a) (B : Set b)
     (C : A → B → Set c) → Set (a ⊔ b ⊔ c)
Σ₂ A B C = Σ A λ a → Σ B λ b → C a b

_l++_ : ∀ {l} {A : Set l} → (xs ys : List A) → List A
_l++_ = Prod.zip _+_ _++_


record Hypergraph {l : Level} (input : List VLabel) (output : List VLabel) : Set ((lsuc l) ⊔ ℓₜ ⊔ ℓₜᵣ ⊔ ℓₒ) where
  field
    E : List VLabel → List VLabel → Set l

  Edge : Set (ℓₜ ⊔ l)
  Edge = Σ₂ (List VLabel) (List VLabel) E

  --input of the edge (s for source)
  s : Edge → List VLabel
  s = proj₁

  --output of the edge (t for target)
  t : Edge → List VLabel
  t = proj₁ ∘ proj₂

  -- type representing the ports that arrows go into
  in-index  = (Fin (len output)) ⊎ (Σ Edge (Fin ∘ len ∘ s))
  -- type representing the ports that arrows go out of
  out-index = (Fin (len input))  ⊎ (Σ Edge (Fin ∘ len ∘ t))

  in-lookup  : in-index  → VLabel
  in-lookup  = [ lookup (vec-of-list output) , (λ {((s , _ , e) , i) → lookup (vec-of-list s) i})]′

  out-lookup : out-index → VLabel
  out-lookup = [ lookup (vec-of-list input)  , (λ {((_ , t , e) , i) → lookup (vec-of-list t) i})]′

  field
    conns→ : out-index → in-index
    conns← : in-index → out-index
    type-match : (i : out-index) → out-lookup i VLabel.≈ in-lookup (conns→ i)
    bijection : Inverseᵇ _≡_ _≡_ conns→ conns←    -- TODO replace with a newly defined edge equality?

  bijection₁ = proj₁ bijection
  bijection₂ = proj₂ bijection

  field
    --the label associated with each box
    o : ∀ {input output} → E input output → ELabel {input} {output}




--hypergraph equivalence
record _≋_ {l} {A B : List VLabel} (G H : Hypergraph {l} A B) : Set (l ⊔ ℓₜ ⊔ ℓₜᵣ ⊔ ℓₒ ⊔ ℓₒᵣ) where
  module G = Hypergraph G
  module H = Hypergraph H
  field
    α : ∀ {input output} → G.E input output → H.E input output
    α′ : ∀ {input output} → H.E input output → G.E input output

    bijection : ∀ {input output} → Inverseᵇ _≡_ _≡_ (α {input} {output}) (α′)  -- TODO again, maybe change this to some new edge equality?
    obj-resp : ∀ {input output} → (e : G.E input output) → (G.o e) ELabel.≈ (H.o (α e))

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





--hypergraph composition
_⊚_ : ∀ {l} {A B C : List VLabel} → Hypergraph {l} B C → Hypergraph {l} A B → Hypergraph {l} A C
_⊚_ BC AB = record
  { E = E
  ; conns→ = conns→
  ; conns← = conns←
  ; type-match = type-match
  ; bijection = bijection
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
    type-match = type-match′
      where
        open SetoidReasoning VLabel-setoid
        type-match′ : _
        type-match′ (inj₁ i) with (AB.conns→ (inj₁ i)) | (inspect AB.conns→ (inj₁ i))
        type-match′ (inj₁ i) | (inj₁ j) | [ i→j ] with (BC.conns→ (inj₁ j)) | (inspect BC.conns→ (inj₁ j))
        type-match′ (inj₁ i) | (inj₁ j) | [ i→j ] | (inj₁ _) | [ j→k ] = begin
          _ ≈⟨ AB.type-match (inj₁ i) ⟩
          _ ≡⟨ cong [ _ , _ ]′ i→j ⟩
          _ ≈⟨ BC.type-match (inj₁ j) ⟩
          _ ≡⟨ cong [ _ , _ ]′ j→k ⟩
          _ ∎
        type-match′ (inj₁ i) | (inj₁ j) | [ i→j ] | (inj₂ _) | [ j→k ] = begin
          _ ≈⟨ AB.type-match (inj₁ i) ⟩
          _ ≡⟨ cong [ _ , _ ]′ i→j ⟩
          _ ≈⟨ BC.type-match (inj₁ j) ⟩
          _ ≡⟨ cong [ _ , _ ]′ j→k ⟩
          _ ∎
        type-match′ (inj₁ i) | (inj₂ _) | [ i→j ] = begin
          _ ≈⟨ AB.type-match (inj₁ i) ⟩
          _ ≡⟨ cong [ _ , _ ]′ i→j ⟩
          _ ∎
        type-match′ (inj₂ ((_ , _ , inj₁ e) , i)) with (AB.conns→ (inj₂ ((_ , _ , e) , i))) | (inspect AB.conns→ (inj₂ ((_ , _ , e) , i)))
        type-match′ (inj₂ ((_ , _ , inj₁ e) , i)) | (inj₁ j) | [ i→j ] with (BC.conns→ (inj₁ j)) | (inspect BC.conns→ (inj₁ j))
        type-match′ (inj₂ ((_ , _ , inj₁ e) , i)) | (inj₁ j) | [ i→j ] | (inj₁ _) | [ j→k ] = begin
          _ ≈⟨ AB.type-match (inj₂ ((_ , _ , e) , i)) ⟩
          _ ≡⟨ cong [ _ , _ ]′ i→j ⟩
          _ ≈⟨ BC.type-match (inj₁ j) ⟩
          _ ≡⟨ cong [ _ , _ ]′ j→k ⟩
          _ ∎
        type-match′ (inj₂ ((_ , _ , inj₁ e) , i)) | (inj₁ j) | [ i→j ] | (inj₂ _) | [ j→k ] = begin
          _ ≈⟨ AB.type-match (inj₂ ((_ , _ , e) , i)) ⟩
          _ ≡⟨ cong [ _ , _ ]′ i→j ⟩
          _ ≈⟨ BC.type-match (inj₁ j) ⟩
          _ ≡⟨ cong [ _ , _ ]′ j→k ⟩
          _ ∎
        type-match′ (inj₂ ((_ , _ , inj₁ e) , i)) | (inj₂ _) | [ i→j ] = begin
          _ ≈⟨ AB.type-match (inj₂ ((_ , _ , e) , i)) ⟩
          _ ≡⟨ cong [ _ , _ ]′ i→j ⟩
          _ ∎
        type-match′ (inj₂ ((_ , _ , inj₂ e) , i)) with (BC.conns→ (inj₂ ((_ , _ , e) , i))) | (inspect BC.conns→ (inj₂ ((_ , _ , e) , i)))
        type-match′ (inj₂ ((_ , _ , inj₂ e) , i)) | (inj₁ _) | [ i→j ] = begin
          _ ≈⟨ BC.type-match (inj₂ ((_ , _ , e) , i)) ⟩
          _ ≡⟨ cong [ _ , _ ]′ i→j ⟩
          _ ∎
        type-match′ (inj₂ ((_ , _ , inj₂ e) , i)) | (inj₂ _) | [ i→j ] = begin
          _ ≈⟨ BC.type-match (inj₂ ((_ , _ , e) , i)) ⟩
          _ ≡⟨ cong [ _ , _ ]′ i→j ⟩
          _ ∎
    bijection₁ : _
    bijection₁ = bijection₁′
      where
        open ≡-Reasoning
        bijection₁′ : _
        bijection₁′ (inj₁ i) with (BC.conns← (inj₁ i)) | (inspect BC.conns← (inj₁ i))
        bijection₁′ (inj₁ i) | (inj₁ j) | [ i→j ] with (AB.conns← (inj₁ j)) | (inspect AB.conns← (inj₁ j))
        bijection₁′ (inj₁ i) | (inj₁ j) | [ i→j ] | (inj₁ _) | [ j→k ] = trans
          (cong [ _ , _ ]′
            (begin
            _ ≡⟨ cong AB.conns→ (sym j→k) ⟩
            _ ≡⟨ AB.bijection₁ (inj₁ j) ⟩
            _ ∎))
          (cong (Sum.map₂ _)
            (begin
            _ ≡⟨ cong BC.conns→ (sym i→j) ⟩
            _ ≡⟨ BC.bijection₁ (inj₁ i) ⟩
            _ ∎))
        bijection₁′ (inj₁ i) | (inj₁ j) | [ i→j ] | (inj₂ _) | [ j→k ] = trans
          (cong [ _ , _ ]′
            (begin
            _ ≡⟨ cong AB.conns→ (sym j→k) ⟩
            _ ≡⟨ AB.bijection₁ (inj₁ j) ⟩
            _ ∎))
          (cong (Sum.map₂ _)
            (begin
            _ ≡⟨ cong BC.conns→ (sym i→j) ⟩
            _ ≡⟨ BC.bijection₁ (inj₁ i) ⟩
            _ ∎))
        bijection₁′ (inj₁ i) | (inj₂ _) | [ i→j ] =
          cong (Sum.map₂ _)
            (begin
            _ ≡⟨ cong BC.conns→ (sym i→j) ⟩
            _ ≡⟨ BC.bijection₁ (inj₁ i) ⟩
            _ ∎)
        bijection₁′ (inj₂ ((_ , _ , inj₁ e) , i)) with (AB.conns← (inj₂ ((_ , _ , e) , i))) | (inspect AB.conns← (inj₂ ((_ , _ , e) , i)))
        bijection₁′ (inj₂ ((_ , _ , inj₁ e) , i)) | (inj₁ _) | [ i→j ] =
          cong [ _ , _ ]′
            (begin
            _ ≡⟨ cong AB.conns→ (sym i→j) ⟩
            _ ≡⟨ AB.bijection₁ (inj₂ ((_ , _ , e) , i)) ⟩
            _ ∎)
        bijection₁′ (inj₂ ((_ , _ , inj₁ e) , i)) | (inj₂ _) | [ i→j ] =
          cong [ _ , _ ]′
            (begin
            _ ≡⟨ cong AB.conns→ (sym i→j) ⟩
            _ ≡⟨ AB.bijection₁ (inj₂ ((_ , _ , e) , i)) ⟩
            _ ∎)
        bijection₁′ (inj₂ ((_ , _ , inj₂ e) , i)) with (BC.conns← (inj₂ ((_ , _ , e) , i))) | (inspect BC.conns← (inj₂ ((_ , _ , e) , i)))
        bijection₁′ (inj₂ ((_ , _ , inj₂ e) , i)) | (inj₁ j) | [ i→j ] with (AB.conns← (inj₁ j)) | (inspect AB.conns← (inj₁ j))
        bijection₁′ (inj₂ ((_ , _ , inj₂ e) , i)) | (inj₁ j) | [ i→j ] | (inj₁ _) | [ j→k ] = trans
          (cong [ _ , _ ]′
            (begin
            _ ≡⟨ cong AB.conns→ (sym j→k) ⟩
            _ ≡⟨ AB.bijection₁ (inj₁ j) ⟩
            _ ∎))
          (cong (Sum.map₂ _)
            (begin
            _ ≡⟨ cong BC.conns→ (sym i→j) ⟩
            _ ≡⟨ BC.bijection₁ (inj₂ ((_ , _ , e) , i)) ⟩
            _ ∎))
        bijection₁′ (inj₂ ((_ , _ , inj₂ e) , i)) | (inj₁ j) | [ i→j ] | (inj₂ _) | [ j→k ] = trans
          (cong [ _ , _ ]′
            (begin
            _ ≡⟨ cong AB.conns→ (sym j→k) ⟩
            _ ≡⟨ AB.bijection₁ (inj₁ j) ⟩
            _ ∎))
          (cong (Sum.map₂ _)
            (begin
            _ ≡⟨ cong BC.conns→ (sym i→j) ⟩
            _ ≡⟨ BC.bijection₁ (inj₂ ((_ , _ , e) , i)) ⟩
            _ ∎))
        bijection₁′ (inj₂ ((_ , _ , inj₂ e) , i)) | (inj₂ _) | [ i→j ] =
          cong (Sum.map₂ _)
            (begin
            _ ≡⟨ cong BC.conns→ (sym i→j) ⟩
            _ ≡⟨ BC.bijection₁ (inj₂ ((_ , _ , e) , i)) ⟩
            _ ∎)
    bijection₂ : _
    bijection₂ = bijection₂′
      where
        open ≡-Reasoning
        bijection₂′ : _
        bijection₂′ (inj₁ i) with (AB.conns→ (inj₁ i)) | (inspect AB.conns→ (inj₁ i))
        bijection₂′ (inj₁ i) | (inj₁ j) | [ i→j ] with (BC.conns→ (inj₁ j)) | (inspect BC.conns→ (inj₁ j))
        bijection₂′ (inj₁ i) | (inj₁ j) | [ i→j ] | (inj₁ _) | [ j→k ] = trans
          (cong [ _ , _ ]′
            (begin
            _ ≡⟨ cong BC.conns← (sym j→k) ⟩
            _ ≡⟨ BC.bijection₂ (inj₁ j) ⟩
            _ ∎))
          (cong (Sum.map₂ _)
            (begin
            _ ≡⟨ cong AB.conns← (sym i→j) ⟩
            _ ≡⟨ AB.bijection₂ (inj₁ i) ⟩
            _ ∎))
        bijection₂′ (inj₁ i) | (inj₁ j) | [ i→j ] | (inj₂ _) | [ j→k ] = trans
          (cong [ _ , _ ]′
            (begin
            _ ≡⟨ cong BC.conns← (sym j→k) ⟩
            _ ≡⟨ BC.bijection₂ (inj₁ j) ⟩
            _ ∎))
          (cong (Sum.map₂ _)
            (begin
            _ ≡⟨ cong AB.conns← (sym i→j) ⟩
            _ ≡⟨ AB.bijection₂ (inj₁ i) ⟩
            _ ∎))
        bijection₂′ (inj₁ i) | (inj₂ _) | [ i→j ] =
          cong (Sum.map₂ _)
            (begin
            _ ≡⟨ cong AB.conns← (sym i→j) ⟩
            _ ≡⟨ AB.bijection₂ (inj₁ i) ⟩
            _ ∎)
        bijection₂′ (inj₂ ((_ , _ , inj₁ e) , i)) with (AB.conns→ (inj₂ ((_ , _ , e) , i))) | (inspect AB.conns→ (inj₂ ((_ , _ , e) , i)))
        bijection₂′ (inj₂ ((_ , _ , inj₁ e) , i)) | (inj₁ j) | [ i→j ] with (BC.conns→ (inj₁ j)) | (inspect BC.conns→ (inj₁ j))
        bijection₂′ (inj₂ ((_ , _ , inj₁ e) , i)) | (inj₁ j) | [ i→j ] | (inj₁ _) | [ j→k ] = trans
          (cong [ _ , _ ]′
            (begin
            _ ≡⟨ cong BC.conns← (sym j→k) ⟩
            _ ≡⟨ BC.bijection₂ (inj₁ j) ⟩
            _ ∎))
          (cong (Sum.map₂ _)
            (begin
            _ ≡⟨ cong AB.conns← (sym i→j) ⟩
            _ ≡⟨ AB.bijection₂ (inj₂ ((_ , _ , e) , i)) ⟩
            _ ∎))
        bijection₂′ (inj₂ ((_ , _ , inj₁ e) , i)) | (inj₁ j) | [ i→j ] | (inj₂ _) | [ j→k ] = trans
          (cong [ _ , _ ]′
            (begin
            _ ≡⟨ cong BC.conns← (sym j→k) ⟩
            _ ≡⟨ BC.bijection₂ (inj₁ j) ⟩
            _ ∎))
          (cong (Sum.map₂ _)
            (begin
            _ ≡⟨ cong AB.conns← (sym i→j) ⟩
            _ ≡⟨ AB.bijection₂ (inj₂ ((_ , _ , e) , i)) ⟩
            _ ∎))
        bijection₂′ (inj₂ ((_ , _ , inj₁ e) , i)) | (inj₂ _) | [ i→j ] =
          cong (Sum.map₂ _)
            (begin
            _ ≡⟨ cong AB.conns← (sym i→j) ⟩
            _ ≡⟨ AB.bijection₂ (inj₂ ((_ , _ , e) , i)) ⟩
            _ ∎)
        bijection₂′ (inj₂ ((_ , _ , inj₂ e) , i)) with (BC.conns→ (inj₂ ((_ , _ , e) , i))) | (inspect BC.conns→ (inj₂ ((_ , _ , e) , i)))
        bijection₂′ (inj₂ ((_ , _ , inj₂ e) , i)) | (inj₁ _) | [ i→j ] =
          cong [ _ , _ ]′
            (begin
            _ ≡⟨ cong BC.conns← (sym i→j) ⟩
            _ ≡⟨ BC.bijection₂ (inj₂ ((_ , _ , e) , i)) ⟩
            _ ∎)
        bijection₂′ (inj₂ ((_ , _ , inj₂ e) , i)) | (inj₂ _) | [ i→j ] =
          cong [ _ , _ ]′
            (begin
            _ ≡⟨ cong BC.conns← (sym i→j) ⟩
            _ ≡⟨ BC.bijection₂ (inj₂ ((_ , _ , e) , i)) ⟩
            _ ∎)
    bijection : _
    bijection = bijection₁ , bijection₂



-- Hypergraph tensor product
_⨂_ : ∀ {l} {A B C D : List VLabel} → Hypergraph {l} A B → Hypergraph {l} C D → Hypergraph {l} (A l++ C) (B l++ D)
_⨂_ {_} {A} {B} {C} {D} AB CD = record
  { E = E
  ; conns→ = conns→
  ; conns← = conns←
  ; type-match = type-match
  ; bijection = bijection
  ; o = [ AB.o , CD.o ]′
  }
  where
    module AB = Hypergraph AB
    module CD = Hypergraph CD
    E : _
    E input output = (AB.E input output) ⊎ (CD.E input output)
    conns→ : _
    conns→ (inj₁ i) with (splitAt (len A) i)
    conns→ (inj₁ i)    | (inj₁ i₁)       = Sum.map (inject+ (len D)) (λ {((_ , _ , f) , j) → (_ , _ , inj₁ f) , j}) (AB.conns→ (inj₁ i₁))
    conns→ (inj₁ i)    | (inj₂ i₂)       = Sum.map (raise   (len B)) (λ {((_ , _ , f) , j) → (_ , _ , inj₂ f) , j}) (CD.conns→ (inj₁ i₂))
    conns→ (inj₂ ((_ , _ , inj₁ e) , i)) = Sum.map (inject+ (len D)) (λ {((_ , _ , f) , j) → (_ , _ , inj₁ f) , j}) (AB.conns→ (inj₂ ((_ , _ , e) , i)))
    conns→ (inj₂ ((_ , _ , inj₂ e) , i)) = Sum.map (raise   (len B)) (λ {((_ , _ , f) , j) → (_ , _ , inj₂ f) , j}) (CD.conns→ (inj₂ ((_ , _ , e) , i)))
    conns← : _
    conns← (inj₁ i) with (splitAt (len B) i)
    conns← (inj₁ i)    | (inj₁ i₁)       = Sum.map (inject+ (len C)) (λ {((_ , _ , f) , j) → (_ , _ , inj₁ f) , j}) (AB.conns← (inj₁ i₁))
    conns← (inj₁ i)    | (inj₂ i₂)       = Sum.map (raise   (len A)) (λ {((_ , _ , f) , j) → (_ , _ , inj₂ f) , j}) (CD.conns← (inj₁ i₂))
    conns← (inj₂ ((_ , _ , inj₁ e) , i)) = Sum.map (inject+ (len C)) (λ {((_ , _ , f) , j) → (_ , _ , inj₁ f) , j}) (AB.conns← (inj₂ ((_ , _ , e) , i)))
    conns← (inj₂ ((_ , _ , inj₂ e) , i)) = Sum.map (raise   (len A)) (λ {((_ , _ , f) , j) → (_ , _ , inj₂ f) , j}) (CD.conns← (inj₂ ((_ , _ , e) , i)))
    type-match : _
    type-match = type-match'
      where
        open SetoidReasoning VLabel-setoid
        type-match' : _
        type-match' (inj₁ i) with (splitAt (len A) i) | (inspect (splitAt (len A)) i)
        type-match' (inj₁ i)    | (inj₁ i₁) | [ i=i₁ ] with (AB.conns→ (inj₁ i₁)) | (inspect AB.conns→ (inj₁ i₁))
        type-match' (inj₁ i)    | (inj₁ i₁) | [ i=i₁ ]    | (inj₁ j) | [ i=j ] = begin
          _ ≡⟨ lookup-splitAt (len A) (vec-of-list A) (vec-of-list C) i ⟩
          _ ≡⟨ cong [ _ , _ ]′ i=i₁ ⟩
          _ ≈⟨ AB.type-match (inj₁ i₁) ⟩
          _ ≡⟨ cong [ _ , _ ]′ i=j ⟩
          _ ≡˘⟨ lookup-++ˡ (vec-of-list B) (vec-of-list D) j ⟩
          _ ∎
        type-match' (inj₁ i)    | (inj₁ i₁) | [ i=i₁ ]    | (inj₂ _) | [ i=j ] = begin
          _ ≡⟨ lookup-splitAt (len A) (vec-of-list A) (vec-of-list C) i ⟩
          _ ≡⟨ cong [ _ , _ ]′ i=i₁ ⟩
          _ ≈⟨ AB.type-match (inj₁ i₁) ⟩
          _ ≡⟨ cong [ _ , _ ]′ i=j ⟩
          _ ∎
        type-match' (inj₁ i)    | (inj₂ i₂) | [ i=i₂ ] with (CD.conns→ (inj₁ i₂)) | (inspect CD.conns→ (inj₁ i₂))
        type-match' (inj₁ i)    | (inj₂ i₂) | [ i=i₂ ]    | (inj₁ j) | [ i=j ] = begin
          _ ≡⟨ lookup-splitAt (len A) (vec-of-list A) (vec-of-list C) i ⟩
          _ ≡⟨ cong [ _ , _ ]′ i=i₂ ⟩
          _ ≈⟨ CD.type-match (inj₁ i₂) ⟩
          _ ≡⟨ cong [ _ , _ ]′ i=j ⟩
          _ ≡˘⟨ lookup-++ʳ (vec-of-list B) (vec-of-list D) j ⟩
          _ ∎
        type-match' (inj₁ i)    | (inj₂ i₂) | [ i=i₂ ]    | (inj₂ _) | [ i=j ] = begin
          _ ≡⟨ lookup-splitAt (len A) (vec-of-list A) (vec-of-list C) i ⟩
          _ ≡⟨ cong [ _ , _ ]′ i=i₂ ⟩
          _ ≈⟨ CD.type-match (inj₁ i₂) ⟩
          _ ≡⟨ cong [ _ , _ ]′ i=j ⟩
          _ ∎
        type-match' (inj₂ ((_ , _ , inj₁ e) , i)) with (AB.conns→ (inj₂ ((_ , _ , e) , i))) | (inspect AB.conns→ (inj₂ ((_ , _ , e) , i)))
        type-match' (inj₂ ((_ , _ , inj₁ e) , i))    | (inj₁ j) | [ i=j ] = begin
          _ ≈⟨ AB.type-match (inj₂ ((_ , _ , e) , i)) ⟩
          _ ≡⟨ cong [ _ , _ ]′ i=j ⟩
          _ ≡˘⟨ lookup-++ˡ (vec-of-list B) (vec-of-list D) j ⟩
          _ ∎
        type-match' (inj₂ ((_ , _ , inj₁ e) , i))    | (inj₂ _) | [ i=j ] = begin
          _ ≈⟨ AB.type-match (inj₂ ((_ , _ , e) , i)) ⟩
          _ ≡⟨ cong [ _ , _ ]′ i=j ⟩
          _ ∎
        type-match' (inj₂ ((_ , _ , inj₂ e) , i)) with (CD.conns→ (inj₂ ((_ , _ , e) , i))) | (inspect CD.conns→ (inj₂ ((_ , _ , e) , i)))
        type-match' (inj₂ ((_ , _ , inj₂ e) , i))    | (inj₁ j) | [ i=j ] = begin
          _ ≈⟨ CD.type-match (inj₂ ((_ , _ , e) , i)) ⟩
          _ ≡⟨ cong [ _ , _ ]′ i=j ⟩
          _ ≡˘⟨ lookup-++ʳ (vec-of-list B) (vec-of-list D) j ⟩
          _ ∎
        type-match' (inj₂ ((_ , _ , inj₂ e) , i))    | (inj₂ _) | [ i=j ] = begin
          _ ≈⟨ CD.type-match (inj₂ ((_ , _ , e) , i)) ⟩
          _ ≡⟨ cong [ _ , _ ]′ i=j ⟩
          _ ∎
    bijection : _
    bijection = bijection₁ , bijection₂
      where
        bijection₁ : _
        bijection₁ (inj₁ i) with (splitAt (len B) i) | (inspect (splitAt (len B)) i)
        bijection₁ (inj₁ i)    | (inj₁ i₁) | [ i=i₁ ] with (AB.conns← (inj₁ i₁)) | (inspect AB.conns← (inj₁ i₁))
        bijection₁ (inj₁ i)    | (inj₁ i₁) | [ i=i₁ ]    | (inj₁ j) | [ i=j ]
          rewrite splitAt-inject+ (len A) (len C) j = begin
          _ ≡˘⟨ cong ((Sum.map (inject+ (len D)) (λ { ((_ , _ , f) , j) → (_ , _ , inj₁ f) , j })) ∘ AB.conns→) i=j ⟩
          _ ≡⟨ cong (Sum.map _ _) (proj₁ AB.bijection (inj₁ i₁)) ⟩
          _ ≡˘⟨ cong (inj₁ ∘ [ _ , _ ]′) i=i₁ ⟩
          _ ≡⟨ cong inj₁ (inject+-raise-splitAt (len B) (len D) i) ⟩
          _ ∎
          where open ≡-Reasoning
        bijection₁ (inj₁ i)    | (inj₁ i₁) | [ i=i₁ ]    | (inj₂ (_ , j)) | [ i=j ] = begin
          _ ≡˘⟨ cong ((Sum.map (inject+ (len D)) (λ { ((_ , _ , f) , j) → (_ , _ , inj₁ f) , j })) ∘ AB.conns→) i=j ⟩
          _ ≡⟨ cong (Sum.map _ _) (proj₁ AB.bijection (inj₁ i₁)) ⟩
          _ ≡˘⟨ cong (inj₁ ∘ [ _ , _ ]′) i=i₁ ⟩
          _ ≡⟨ cong inj₁ (inject+-raise-splitAt (len B) (len D) i) ⟩
          _ ∎
          where open ≡-Reasoning
        bijection₁ (inj₁ i)    | (inj₂ i₂) | [ i=i₂ ] with (CD.conns← (inj₁ i₂)) | (inspect CD.conns← (inj₁ i₂))
        bijection₁ (inj₁ i)    | (inj₂ i₂) | [ i=i₂ ]    | (inj₁ j) | [ i=j ]
          rewrite splitAt-raise (len A) (len C) j = begin
          _ ≡˘⟨ cong ((Sum.map (raise (len B)) (λ { ((_ , _ , f) , j) → (_ , _ , inj₂ f) , j })) ∘ CD.conns→) i=j ⟩
          _ ≡⟨ cong (Sum.map _ _) (proj₁ CD.bijection (inj₁ i₂)) ⟩
          _ ≡˘⟨ cong (inj₁ ∘ [ _ , _ ]′) i=i₂ ⟩
          _ ≡⟨ cong inj₁ (inject+-raise-splitAt (len B) (len D) i) ⟩
          _ ∎
          where open ≡-Reasoning
        bijection₁ (inj₁ i)    | (inj₂ i₂) | [ i=i₂ ]    | (inj₂ (_ , j)) | [ i=j ] = begin
          _ ≡˘⟨ cong ((Sum.map (raise (len B)) (λ { ((_ , _ , f) , j) → (_ , _ , inj₂ f) , j })) ∘ CD.conns→) i=j ⟩
          _ ≡⟨ cong (Sum.map _ _) (proj₁ CD.bijection (inj₁ i₂)) ⟩
          _ ≡˘⟨ cong (inj₁ ∘ [ _ , _ ]′) i=i₂ ⟩
          _ ≡⟨ cong inj₁ (inject+-raise-splitAt (len B) (len D) i) ⟩
          _ ∎
          where open ≡-Reasoning
        bijection₁ (inj₂ ((_ , _ , inj₁ e) , i)) with (AB.conns← (inj₂ ((_ , _ , e) , i))) | (inspect AB.conns← (inj₂ ((_ , _ , e) , i)))
        bijection₁ (inj₂ ((_ , _ , inj₁ e) , i))    | (inj₁ j) | [ i=j ]
          rewrite splitAt-inject+ (len A) (len C) j = begin
          _ ≡˘⟨ cong ((Sum.map (inject+ (len D)) (λ { ((_ , _ , f) , j) → (_ , _ , inj₁ f) , j })) ∘ AB.conns→) i=j ⟩
          _ ≡⟨ cong (Sum.map _ _) (proj₁ AB.bijection (inj₂ ((_ , _ , e) , i))) ⟩
          _ ∎
          where open ≡-Reasoning
        bijection₁ (inj₂ ((_ , _ , inj₁ e) , i))    | (inj₂ (_ , j)) | [ i=j ] = begin
          _ ≡˘⟨ cong ((Sum.map (inject+ (len D)) (λ { ((_ , _ , f) , j) → (_ , _ , inj₁ f) , j })) ∘ AB.conns→) i=j ⟩
          _ ≡⟨ cong (Sum.map _ _) (proj₁ AB.bijection (inj₂ ((_ , _ , e) , i))) ⟩
          _ ∎
          where open ≡-Reasoning
        bijection₁ (inj₂ ((_ , _ , inj₂ e) , i)) with (CD.conns← (inj₂ ((_ , _ , e) , i))) | (inspect CD.conns← (inj₂ ((_ , _ , e) , i)))
        bijection₁ (inj₂ ((_ , _ , inj₂ e) , i))    | (inj₁ j) | [ i=j ]
          rewrite splitAt-raise (len A) (len C) j = begin
          _ ≡˘⟨ cong ((Sum.map (raise (len B)) (λ { ((_ , _ , f) , j) → (_ , _ , inj₂ f) , j })) ∘ CD.conns→) i=j ⟩
          _ ≡⟨ cong (Sum.map _ _) (proj₁ CD.bijection (inj₂ ((_ , _ , e) , i))) ⟩
          _ ∎
          where open ≡-Reasoning
        bijection₁ (inj₂ ((_ , _ , inj₂ e) , i))    | (inj₂ (_ , j)) | [ i=j ] = begin
          _ ≡˘⟨ cong ((Sum.map (raise (len B)) (λ { ((_ , _ , f) , j) → (_ , _ , inj₂ f) , j })) ∘ CD.conns→) i=j ⟩
          _ ≡⟨ cong (Sum.map _ _) (proj₁ CD.bijection (inj₂ ((_ , _ , e) , i))) ⟩
          _ ∎
          where open ≡-Reasoning
        bijection₂ : _
        bijection₂ (inj₁ i) with (splitAt (len A) i) | (inspect (splitAt (len A)) i)
        bijection₂ (inj₁ i)    | (inj₁ i₁) | [ i=i₁ ] with (AB.conns→ (inj₁ i₁)) | (inspect AB.conns→ (inj₁ i₁))
        bijection₂ (inj₁ i)    | (inj₁ i₁) | [ i=i₁ ]    | (inj₁ j) | [ i=j ]
          rewrite splitAt-inject+ (len B) (len D) j = begin
          _ ≡˘⟨ cong ((Sum.map (inject+ (len C)) (λ { ((_ , _ , f) , j) → (_ , _ , inj₁ f) , j })) ∘ AB.conns←) i=j ⟩
          _ ≡⟨ cong (Sum.map _ _) (proj₂ AB.bijection (inj₁ i₁)) ⟩
          _ ≡˘⟨ cong (inj₁ ∘ [ _ , _ ]′) i=i₁ ⟩
          _ ≡⟨ cong inj₁ (inject+-raise-splitAt (len A) (len C) i) ⟩
          _ ∎
          where open ≡-Reasoning
        bijection₂ (inj₁ i)    | (inj₁ i₁) | [ i=i₁ ]    | (inj₂ (_ , j)) | [ i=j ] = begin
          _ ≡˘⟨ cong ((Sum.map (inject+ (len C)) (λ { ((_ , _ , f) , j) → (_ , _ , inj₁ f) , j })) ∘ AB.conns←) i=j ⟩
          _ ≡⟨ cong (Sum.map _ _) (proj₂ AB.bijection (inj₁ i₁)) ⟩
          _ ≡˘⟨ cong (inj₁ ∘ [ _ , _ ]′) i=i₁ ⟩
          _ ≡⟨ cong inj₁ (inject+-raise-splitAt (len A) (len C) i) ⟩
          _ ∎
          where open ≡-Reasoning
        bijection₂ (inj₁ i)    | (inj₂ i₂) | [ i=i₂ ] with (CD.conns→ (inj₁ i₂)) | (inspect CD.conns→ (inj₁ i₂))
        bijection₂ (inj₁ i)    | (inj₂ i₂) | [ i=i₂ ]    | (inj₁ j) | [ i=j ]
          rewrite splitAt-raise (len B) (len D) j = begin
          _ ≡˘⟨ cong ((Sum.map (raise (len A)) (λ { ((_ , _ , f) , j) → (_ , _ , inj₂ f) , j })) ∘ CD.conns←) i=j ⟩
          _ ≡⟨ cong (Sum.map _ _) (proj₂ CD.bijection (inj₁ i₂)) ⟩
          _ ≡˘⟨ cong (inj₁ ∘ [ _ , _ ]′) i=i₂ ⟩
          _ ≡⟨ cong inj₁ (inject+-raise-splitAt (len A) (len C) i) ⟩
          _ ∎
          where open ≡-Reasoning
        bijection₂ (inj₁ i)    | (inj₂ i₂) | [ i=i₂ ]    | (inj₂ (_ , j)) | [ i=j ] = begin
          _ ≡˘⟨ cong ((Sum.map (raise (len A)) (λ { ((_ , _ , f) , j) → (_ , _ , inj₂ f) , j })) ∘ CD.conns←) i=j ⟩
          _ ≡⟨ cong (Sum.map _ _) (proj₂ CD.bijection (inj₁ i₂)) ⟩
          _ ≡˘⟨ cong (inj₁ ∘ [ _ , _ ]′) i=i₂ ⟩
          _ ≡⟨ cong inj₁ (inject+-raise-splitAt (len A) (len C) i) ⟩
          _ ∎
          where open ≡-Reasoning
        bijection₂ (inj₂ ((_ , _ , inj₁ e) , i)) with (AB.conns→ (inj₂ ((_ , _ , e) , i))) | (inspect AB.conns→ (inj₂ ((_ , _ , e) , i)))
        bijection₂ (inj₂ ((_ , _ , inj₁ e) , i))    | (inj₁ j) | [ i=j ]
          rewrite splitAt-inject+ (len B) (len D) j = begin
          _ ≡˘⟨ cong ((Sum.map (inject+ (len C)) (λ { ((_ , _ , f) , j) → (_ , _ , inj₁ f) , j })) ∘ AB.conns←) i=j ⟩
          _ ≡⟨ cong (Sum.map _ _) (proj₂ AB.bijection (inj₂ ((_ , _ , e) , i))) ⟩
          _ ∎
          where open ≡-Reasoning
        bijection₂ (inj₂ ((_ , _ , inj₁ e) , i))    | (inj₂ (_ , j)) | [ i=j ] = begin
          _ ≡˘⟨ cong ((Sum.map (inject+ (len C)) (λ { ((_ , _ , f) , j) → (_ , _ , inj₁ f) , j })) ∘ AB.conns←) i=j ⟩
          _ ≡⟨ cong (Sum.map _ _) (proj₂ AB.bijection (inj₂ ((_ , _ , e) , i))) ⟩
          _ ∎
          where open ≡-Reasoning
        bijection₂ (inj₂ ((_ , _ , inj₂ e) , i)) with (CD.conns→ (inj₂ ((_ , _ , e) , i))) | (inspect CD.conns→ (inj₂ ((_ , _ , e) , i)))
        bijection₂ (inj₂ ((_ , _ , inj₂ e) , i))    | (inj₁ j) | [ i=j ]
          rewrite splitAt-raise (len B) (len D) j = begin
          _ ≡˘⟨ cong ((Sum.map (raise (len A)) (λ { ((_ , _ , f) , j) → (_ , _ , inj₂ f) , j })) ∘ CD.conns←) i=j ⟩
          _ ≡⟨ cong (Sum.map _ _) (proj₂ CD.bijection (inj₂ ((_ , _ , e) , i))) ⟩
          _ ∎
          where open ≡-Reasoning
        bijection₂ (inj₂ ((_ , _ , inj₂ e) , i))    | (inj₂ (_ , j)) | [ i=j ] = begin
          _ ≡˘⟨ cong ((Sum.map (raise (len A)) (λ { ((_ , _ , f) , j) → (_ , _ , inj₂ f) , j })) ∘ CD.conns←) i=j ⟩
          _ ≡⟨ cong (Sum.map _ _) (proj₂ CD.bijection (inj₂ ((_ , _ , e) , i))) ⟩
          _ ∎
          where open ≡-Reasoning

-- record SimpleHypergraph {ℓᵣ : Level} (input : List VLabel) (output : List VLabel) : Set (ℓₜ ⊔ ℓₜᵣ ⊔ (lsuc ℓᵣ) ⊔ (lsuc ℓₒ)) where
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




