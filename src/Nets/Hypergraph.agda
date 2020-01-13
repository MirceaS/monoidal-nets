open import Level renaming (zero to lzero ; suc to lsuc)
open import Agda.Builtin.Equality
open import Data.Product as Prod using (Σ ; _,_ ; ∃₂ ; proj₁ ; proj₂)
open import Data.Sum as Sum using (_⊎_ ; inj₁ ; inj₂ ; [_,_]′)
open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties using (+-suc)
open import Data.Vec hiding (splitAt)
open import Data.Vec.Properties using (lookup-map)
open import Data.Fin renaming (zero to fzero ; suc to fsuc ; _+_ to _+f_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Function using (_∘_ ; Inverseᵇ ; id)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

module Nets.Hypergraph {ℓₜ ℓₜᵣ : Level} (Types-setoid : Setoid ℓₜ ℓₜᵣ)
                       {ℓₒ : Level} (Obj :
                         Σ _ (Vec (Setoid.Carrier Types-setoid)) →
                         Σ _ (Vec (Setoid.Carrier Types-setoid)) →
                         Set ℓₒ
                       ) where

module T = Setoid Types-setoid
T = T.Carrier

{------some technical utilities------
data ⊤' {l : Level} : Set l where
  tt : ⊤'

_⟩⟨_ = cong
infix 0 ⟩⟨

Fin-pm : {ℓ₁ : Level} {n : ℕ} → Fin (suc n) → (A : Set ℓ₁) → (B : Fin n → Set ℓ₁) → Set ℓ₁
Fin-pm fzero A _ = A
Fin-pm (fsuc i) _ B = B i

map-++-commute : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) {n m : ℕ} (xs : Vec A n) (ys : Vec A m) →
                 map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++-commute f []       ys = refl
map-++-commute f (x ∷ xs) ys =
  cong ((f x) ∷_) (map-++-commute f xs ys)
------------------------------------}

record Hypergraph {l : Level} (input : Σ _ (Vec T)) (output : Σ _ (Vec T)) : Set ((lsuc l) ⊔ ℓₜ ⊔ ℓₜᵣ ⊔ ℓₒ) where
  field
    E : Set l
    o : E → ∃₂ Obj

  len = proj₁
  vec = proj₂

  s : E → Σ _ (Vec T) 
  s = proj₁         ∘ o
  
  t : E → Σ _ (Vec T)
  t = proj₁ ∘ proj₂ ∘ o

  in-index  = (Fin (len output)) ⊎ (Σ E (Fin ∘ len ∘ s))
  out-index = (Fin (len input))  ⊎ (Σ E (Fin ∘ len ∘ t))

  in-lookup  : in-index  → T
  in-lookup  = [ lookup (vec output) , (λ {(e , i) → lookup (vec (s e)) i})]′

  out-lookup : out-index → T
  out-lookup = [ lookup (vec input)  , (λ {(e , i) → lookup (vec (t e)) i})]′

  field
    conns→ : out-index → in-index
    conns← : in-index → out-index
    type-match : (i : out-index) → out-lookup i T.≈ in-lookup (conns→ i)
    one-to-one : Inverseᵇ _≡_ _≡_ conns→ conns←

  one-to-one₁ = proj₁ one-to-one
  one-to-one₂ = proj₂ one-to-one

_⊚_ : ∀ {l₁ l₂} {A B C : Σ _ (Vec T)} → Hypergraph {l₁} B C → Hypergraph {l₂} A B → Hypergraph {l₁ ⊔ l₂} A C
_⊚_ {_} {_} {na , A} {nb , B} {nc , C} BC AB = record
                                  { E = E
                                  ; o = o
                                  ; conns→ = conns→
                                  ; conns← = conns←
                                  ; type-match = type-match
                                  ; one-to-one = one-to-one
                                  }
                                where
                                  module AB = Hypergraph AB
                                  module BC = Hypergraph BC
                                  E = AB.E ⊎ BC.E
                                  o = [ AB.o , BC.o ]′
                                  conns→ : _
                                  conns→ (inj₁ i) = [
                                      (λ j → Sum.map₂ (Prod.map inj₂ id) (BC.conns→ (inj₁ j))) ,
                                      inj₂ ∘ (Prod.map inj₁ id)
                                    ]′ (AB.conns→ (inj₁ i))
                                  conns→ (inj₂ ((inj₁ e) , i)) = [
                                      (λ j → Sum.map₂ (Prod.map inj₂ id) (BC.conns→ (inj₁ j))) ,
                                      inj₂ ∘ (Prod.map inj₁ id)
                                    ]′ (AB.conns→ (inj₂ (e , i)))
                                  conns→ (inj₂ ((inj₂ e) , i)) = Sum.map₂
                                      (Prod.map inj₂ id)
                                    (BC.conns→ (inj₂ (e , i)))
                                  conns← : _
                                  conns← (inj₁ i) = [
                                      (λ j → Sum.map₂ (Prod.map inj₁ id) (AB.conns← (inj₁ j))) ,
                                      inj₂ ∘ (Prod.map inj₂ id)
                                    ]′ (BC.conns← (inj₁ i))
                                  conns← (inj₂ ((inj₁ e) , i)) = Sum.map₂
                                      (Prod.map inj₁ id)
                                    (AB.conns← (inj₂ (e , i)))
                                  conns← (inj₂ ((inj₂ e) , i)) = [
                                      (λ j → Sum.map₂ (Prod.map inj₁ id) (AB.conns← (inj₁ j))) ,
                                      inj₂ ∘ (Prod.map inj₂ id)
                                    ]′ (BC.conns← (inj₂ (e , i)))
                                  type-match : _
                                  type-match = type-match′
                                    where
                                      open SetoidReasoning Types-setoid
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
                                      type-match′ (inj₂ ((inj₁ e) , i)) with (AB.conns→ (inj₂ (e , i))) | (inspect AB.conns→ (inj₂ (e , i)))
                                      type-match′ (inj₂ ((inj₁ e) , i)) | (inj₁ j) | [ i→j ] with (BC.conns→ (inj₁ j)) | (inspect BC.conns→ (inj₁ j))
                                      type-match′ (inj₂ ((inj₁ e) , i)) | (inj₁ j) | [ i→j ] | (inj₁ _) | [ j→k ] = begin
                                        _ ≈⟨ AB.type-match (inj₂ (e , i)) ⟩
                                        _ ≡⟨ cong [ _ , _ ]′ i→j ⟩
                                        _ ≈⟨ BC.type-match (inj₁ j) ⟩
                                        _ ≡⟨ cong [ _ , _ ]′ j→k ⟩
                                        _ ∎
                                      type-match′ (inj₂ ((inj₁ e) , i)) | (inj₁ j) | [ i→j ] | (inj₂ _) | [ j→k ] = begin
                                        _ ≈⟨ AB.type-match (inj₂ (e , i)) ⟩
                                        _ ≡⟨ cong [ _ , _ ]′ i→j ⟩
                                        _ ≈⟨ BC.type-match (inj₁ j) ⟩
                                        _ ≡⟨ cong [ _ , _ ]′ j→k ⟩
                                        _ ∎
                                      type-match′ (inj₂ ((inj₁ e) , i)) | (inj₂ _) | [ i→j ] = begin
                                        _ ≈⟨ AB.type-match (inj₂ (e , i)) ⟩
                                        _ ≡⟨ cong [ _ , _ ]′ i→j ⟩
                                        _ ∎
                                      type-match′ (inj₂ ((inj₂ e) , i)) with (BC.conns→ (inj₂ (e , i))) | (inspect BC.conns→ (inj₂ (e , i)))
                                      type-match′ (inj₂ ((inj₂ e) , i)) | (inj₁ _) | [ i→j ] = begin
                                        _ ≈⟨ BC.type-match (inj₂ (e , i)) ⟩
                                        _ ≡⟨ cong [ _ , _ ]′ i→j ⟩
                                        _ ∎
                                      type-match′ (inj₂ ((inj₂ e) , i)) | (inj₂ _) | [ i→j ] = begin
                                        _ ≈⟨ BC.type-match (inj₂ (e , i)) ⟩
                                        _ ≡⟨ cong [ _ , _ ]′ i→j ⟩
                                        _ ∎
                                  one-to-one₁ : _
                                  one-to-one₁ = one-to-one₁′
                                    where
                                      open ≡-Reasoning
                                      one-to-one₁′ : _
                                      one-to-one₁′ (inj₁ i) with (BC.conns← (inj₁ i)) | (inspect BC.conns← (inj₁ i))
                                      one-to-one₁′ (inj₁ i) | (inj₁ j) | [ i→j ] with (AB.conns← (inj₁ j)) | (inspect AB.conns← (inj₁ j))
                                      one-to-one₁′ (inj₁ i) | (inj₁ j) | [ i→j ] | (inj₁ _) | [ j→k ] = trans
                                        (cong [ _ , _ ]′
                                          (begin
                                          _ ≡⟨ cong AB.conns→ (sym j→k) ⟩
                                          _ ≡⟨ AB.one-to-one₁ (inj₁ j) ⟩
                                          _ ∎))
                                        (cong (Sum.map₂ _)
                                          (begin
                                          _ ≡⟨ cong BC.conns→ (sym i→j) ⟩
                                          _ ≡⟨ BC.one-to-one₁ (inj₁ i) ⟩
                                          _ ∎))
                                      one-to-one₁′ (inj₁ i) | (inj₁ j) | [ i→j ] | (inj₂ _) | [ j→k ] = trans
                                        (cong [ _ , _ ]′
                                          (begin
                                          _ ≡⟨ cong AB.conns→ (sym j→k) ⟩
                                          _ ≡⟨ AB.one-to-one₁ (inj₁ j) ⟩
                                          _ ∎))
                                        (cong (Sum.map₂ _)
                                          (begin
                                          _ ≡⟨ cong BC.conns→ (sym i→j) ⟩
                                          _ ≡⟨ BC.one-to-one₁ (inj₁ i) ⟩
                                          _ ∎))
                                      one-to-one₁′ (inj₁ i) | (inj₂ _) | [ i→j ] =
                                        cong (Sum.map₂ _)
                                          (begin
                                          _ ≡⟨ cong BC.conns→ (sym i→j) ⟩
                                          _ ≡⟨ BC.one-to-one₁ (inj₁ i) ⟩
                                          _ ∎)
                                      one-to-one₁′ (inj₂ (inj₁ e , i)) with (AB.conns← (inj₂ (e , i))) | (inspect AB.conns← (inj₂ (e , i)))
                                      one-to-one₁′ (inj₂ (inj₁ e , i)) | (inj₁ _) | [ i→j ] =
                                        cong [ _ , _ ]′
                                          (begin
                                          _ ≡⟨ cong AB.conns→ (sym i→j) ⟩
                                          _ ≡⟨ AB.one-to-one₁ (inj₂ (e , i)) ⟩
                                          _ ∎)
                                      one-to-one₁′ (inj₂ (inj₁ e , i)) | (inj₂ _) | [ i→j ] =
                                        cong [ _ , _ ]′
                                          (begin
                                          _ ≡⟨ cong AB.conns→ (sym i→j) ⟩
                                          _ ≡⟨ AB.one-to-one₁ (inj₂ (e , i)) ⟩
                                          _ ∎)
                                      one-to-one₁′ (inj₂ (inj₂ e , i)) with (BC.conns← (inj₂ (e , i))) | (inspect BC.conns← (inj₂ (e , i)))
                                      one-to-one₁′ (inj₂ (inj₂ e , i)) | (inj₁ j) | [ i→j ] with (AB.conns← (inj₁ j)) | (inspect AB.conns← (inj₁ j))
                                      one-to-one₁′ (inj₂ (inj₂ e , i)) | (inj₁ j) | [ i→j ] | (inj₁ _) | [ j→k ] = trans
                                        (cong [ _ , _ ]′
                                          (begin
                                          _ ≡⟨ cong AB.conns→ (sym j→k) ⟩
                                          _ ≡⟨ AB.one-to-one₁ (inj₁ j) ⟩
                                          _ ∎))
                                        (cong (Sum.map₂ _)
                                          (begin
                                          _ ≡⟨ cong BC.conns→ (sym i→j) ⟩
                                          _ ≡⟨ BC.one-to-one₁ (inj₂ (e , i)) ⟩
                                          _ ∎))
                                      one-to-one₁′ (inj₂ (inj₂ e , i)) | (inj₁ j) | [ i→j ] | (inj₂ _) | [ j→k ] = trans
                                        (cong [ _ , _ ]′
                                          (begin
                                          _ ≡⟨ cong AB.conns→ (sym j→k) ⟩
                                          _ ≡⟨ AB.one-to-one₁ (inj₁ j) ⟩
                                          _ ∎))
                                        (cong (Sum.map₂ _)
                                          (begin
                                          _ ≡⟨ cong BC.conns→ (sym i→j) ⟩
                                          _ ≡⟨ BC.one-to-one₁ (inj₂ (e , i)) ⟩
                                          _ ∎))
                                      one-to-one₁′ (inj₂ (inj₂ e , i)) | (inj₂ _) | [ i→j ] =
                                        cong (Sum.map₂ _)
                                          (begin
                                          _ ≡⟨ cong BC.conns→ (sym i→j) ⟩
                                          _ ≡⟨ BC.one-to-one₁ (inj₂ (e , i)) ⟩
                                          _ ∎)
                                  one-to-one₂ : _
                                  one-to-one₂ = one-to-one₂′
                                    where
                                      open ≡-Reasoning
                                      one-to-one₂′ : _
                                      one-to-one₂′ (inj₁ i) with (AB.conns→ (inj₁ i)) | (inspect AB.conns→ (inj₁ i))
                                      one-to-one₂′ (inj₁ i) | (inj₁ j) | [ i→j ] with (BC.conns→ (inj₁ j)) | (inspect BC.conns→ (inj₁ j))
                                      one-to-one₂′ (inj₁ i) | (inj₁ j) | [ i→j ] | (inj₁ _) | [ j→k ] = trans
                                        (cong [ _ , _ ]′
                                          (begin
                                          _ ≡⟨ cong BC.conns← (sym j→k) ⟩
                                          _ ≡⟨ BC.one-to-one₂ (inj₁ j) ⟩
                                          _ ∎))
                                        (cong (Sum.map₂ _)
                                          (begin
                                          _ ≡⟨ cong AB.conns← (sym i→j) ⟩
                                          _ ≡⟨ AB.one-to-one₂ (inj₁ i) ⟩
                                          _ ∎))
                                      one-to-one₂′ (inj₁ i) | (inj₁ j) | [ i→j ] | (inj₂ _) | [ j→k ] = trans
                                        (cong [ _ , _ ]′
                                          (begin
                                          _ ≡⟨ cong BC.conns← (sym j→k) ⟩
                                          _ ≡⟨ BC.one-to-one₂ (inj₁ j) ⟩
                                          _ ∎))
                                        (cong (Sum.map₂ _)
                                          (begin
                                          _ ≡⟨ cong AB.conns← (sym i→j) ⟩
                                          _ ≡⟨ AB.one-to-one₂ (inj₁ i) ⟩
                                          _ ∎))
                                      one-to-one₂′ (inj₁ i) | (inj₂ _) | [ i→j ] =
                                        cong (Sum.map₂ _)
                                          (begin
                                          _ ≡⟨ cong AB.conns← (sym i→j) ⟩
                                          _ ≡⟨ AB.one-to-one₂ (inj₁ i) ⟩
                                          _ ∎)
                                      one-to-one₂′ (inj₂ (inj₁ e , i)) with (AB.conns→ (inj₂ (e , i))) | (inspect AB.conns→ (inj₂ (e , i)))
                                      one-to-one₂′ (inj₂ (inj₁ e , i)) | (inj₁ j) | [ i→j ] with (BC.conns→ (inj₁ j)) | (inspect BC.conns→ (inj₁ j))
                                      one-to-one₂′ (inj₂ (inj₁ e , i)) | (inj₁ j) | [ i→j ] | (inj₁ _) | [ j→k ] = trans
                                        (cong [ _ , _ ]′
                                          (begin
                                          _ ≡⟨ cong BC.conns← (sym j→k) ⟩
                                          _ ≡⟨ BC.one-to-one₂ (inj₁ j) ⟩
                                          _ ∎))
                                        (cong (Sum.map₂ _)
                                          (begin
                                          _ ≡⟨ cong AB.conns← (sym i→j) ⟩
                                          _ ≡⟨ AB.one-to-one₂ (inj₂ (e , i)) ⟩
                                          _ ∎))
                                      one-to-one₂′ (inj₂ (inj₁ e , i)) | (inj₁ j) | [ i→j ] | (inj₂ _) | [ j→k ] = trans
                                        (cong [ _ , _ ]′
                                          (begin
                                          _ ≡⟨ cong BC.conns← (sym j→k) ⟩
                                          _ ≡⟨ BC.one-to-one₂ (inj₁ j) ⟩
                                          _ ∎))
                                        (cong (Sum.map₂ _)
                                          (begin
                                          _ ≡⟨ cong AB.conns← (sym i→j) ⟩
                                          _ ≡⟨ AB.one-to-one₂ (inj₂ (e , i)) ⟩
                                          _ ∎))
                                      one-to-one₂′ (inj₂ (inj₁ e , i)) | (inj₂ _) | [ i→j ] =
                                        cong (Sum.map₂ _)
                                          (begin
                                          _ ≡⟨ cong AB.conns← (sym i→j) ⟩
                                          _ ≡⟨ AB.one-to-one₂ (inj₂ (e , i)) ⟩
                                          _ ∎)
                                      one-to-one₂′ (inj₂ (inj₂ e , i)) with (BC.conns→ (inj₂ (e , i))) | (inspect BC.conns→ (inj₂ (e , i)))
                                      one-to-one₂′ (inj₂ (inj₂ e , i)) | (inj₁ _) | [ i→j ] =
                                        cong [ _ , _ ]′
                                          (begin
                                          _ ≡⟨ cong BC.conns← (sym i→j) ⟩
                                          _ ≡⟨ BC.one-to-one₂ (inj₂ (e , i)) ⟩
                                          _ ∎)
                                      one-to-one₂′ (inj₂ (inj₂ e , i)) | (inj₂ _) | [ i→j ] =
                                        cong [ _ , _ ]′
                                          (begin
                                          _ ≡⟨ cong BC.conns← (sym i→j) ⟩
                                          _ ≡⟨ BC.one-to-one₂ (inj₂ (e , i)) ⟩
                                          _ ∎)
                                  one-to-one : _
                                  one-to-one = one-to-one₁ , one-to-one₂

record _≋_ {l} {A B : Σ _ (Vec T)} (G H : Hypergraph {l} A B) : Set ((lsuc l) ⊔ ℓₜ ⊔ ℓₜᵣ ⊔ ℓₒ) where
  module G = Hypergraph G
  module H = Hypergraph H
  field
    α : G.E → H.E
    α′ : H.E → G.E

    one-to-one : Inverseᵇ _≡_ _≡_ α α′
    obj-resp : {e : G.E} → G.o e ≡ H.o (α e)

  α-in-index :  G.in-index  → H.in-index
  α-in-index  = Sum.map₂ (Prod.map α (cast (cong (proj₁ ∘ proj₁        ) obj-resp)))
  α-out-index : G.out-index → H.out-index
  α-out-index = Sum.map₂ (Prod.map α (cast (cong (proj₁ ∘ proj₁ ∘ proj₂) obj-resp)))

  field
    conns→-resp : {i : G.out-index} →
                   H.conns→ (α-out-index i) ≡ α-in-index (G.conns→ i)
    -- this one is redundant
    -- conns←-resp : {i : G.in-index} →
    --                H.conns← (α-in-index i) ≡ α-out-index (G.conns← i)


-- record SimpleHypergraph {ℓᵣ : Level} (input : Σ _ (Vec T)) (output : Σ _ (Vec T)) : Set (ℓₜ ⊔ ℓₜᵣ ⊔ (lsuc ℓᵣ) ⊔ (lsuc ℓₒ)) where
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
