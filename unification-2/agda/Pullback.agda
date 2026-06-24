{-# OPTIONS --safe #-}

------------------------------------------------------------------------
-- The pullback of two renamings ρ₁ : Fin a → Fin n and ρ₂ : Fin b → Fin n
-- (with a common codomain).
--
-- This corresponds to the specification's pushout judgment
--   Γ ⊢ ρ₁ ⊔ ρ₂ = i₁ ; i₂ : Γ₃
-- (which, by the variance of metavariable renamings, is a pullback in the
-- category of contexts and injective renamings: the intersection of the
-- images, with the two projections).
--
-- We build the size c of Γ₃ together with projections i₁ : Fin c → Fin a
-- and i₂ : Fin c → Fin b, and prove:
--   * commutes : ρ₁ ∘ i₁ = ρ₂ ∘ i₂
--   * complete : every p with ρ₁ p in the range of ρ₂ is in the range of i₁.
------------------------------------------------------------------------

module Pullback where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Properties using (_≟_)
open import Data.Vec.Base using (Vec; []; _∷_; lookup; map)
open import Data.Vec.Properties using (lookup-map)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Empty using (⊥-elim)

open import Renaming

------------------------------------------------------------------------
-- Deciding whether x is in the range of ρ (and producing a preimage).

findPre : ∀ {n b} (x : Fin n) (ρ : Ren n b) → Dec (x ∈ʳ ρ)
findPre x []       = no λ ()
findPre x (y ∷ ρ)  with x ≟ y
... | yes refl = yes (zero , refl)
... | no  x≢y  with findPre x ρ
...   | yes (q , e) = yes (suc q , e)
...   | no  ¬p      = no λ { (zero , e)  → x≢y (sym e)
                          ; (suc q , e) → ¬p (q , e) }

------------------------------------------------------------------------
-- The construction: size + the two projections, computed together.

pbData : ∀ {n a b} (ρ₁ : Ren n a) (ρ₂ : Ren n b) → Σ ℕ (λ c → Ren a c × Ren b c)
pbData []       ρ₂ = 0 , [] , []
pbData (x ∷ ρ₁) ρ₂ with findPre x ρ₂ | pbData ρ₁ ρ₂
... | yes (q , _) | (c , i₁ , i₂) = suc c , (zero ∷ map suc i₁) , (q ∷ i₂)
... | no  _       | (c , i₁ , i₂) = c , map suc i₁ , i₂

pbSize : ∀ {n a b} (ρ₁ : Ren n a) (ρ₂ : Ren n b) → ℕ
pbSize ρ₁ ρ₂ = proj₁ (pbData ρ₁ ρ₂)

pbι₁ : ∀ {n a b} (ρ₁ : Ren n a) (ρ₂ : Ren n b) → Ren a (pbSize ρ₁ ρ₂)
pbι₁ ρ₁ ρ₂ = proj₁ (proj₂ (pbData ρ₁ ρ₂))

pbι₂ : ∀ {n a b} (ρ₁ : Ren n a) (ρ₂ : Ren n b) → Ren b (pbSize ρ₁ ρ₂)
pbι₂ ρ₁ ρ₂ = proj₂ (proj₂ (pbData ρ₁ ρ₂))

------------------------------------------------------------------------
-- The pullback square commutes.

pbComm : ∀ {n a b} (ρ₁ : Ren n a) (ρ₂ : Ren n b) (k : Fin (pbSize ρ₁ ρ₂)) →
         app ρ₁ (app (pbι₁ ρ₁ ρ₂) k) ≡ app ρ₂ (app (pbι₂ ρ₁ ρ₂) k)
pbComm []       ρ₂ ()
pbComm (x ∷ ρ₁) ρ₂ k with findPre x ρ₂ | pbData ρ₁ ρ₂ | pbComm ρ₁ ρ₂
... | yes (q , e) | (c , i₁ , i₂) | ih = lemma k
  where
    lemma : (k : Fin (suc c)) →
            app (x ∷ ρ₁) (app (zero ∷ map suc i₁) k) ≡ app ρ₂ (app (q ∷ i₂) k)
    lemma zero     = sym e
    lemma (suc k') =
      trans (cong (app (x ∷ ρ₁)) (lookup-map k' suc i₁)) (ih k')
... | no  _       | (c , i₁ , i₂) | ih =
      trans (cong (app (x ∷ ρ₁)) (lookup-map k suc i₁)) (ih k)

pbCommVec : ∀ {n a b} (ρ₁ : Ren n a) (ρ₂ : Ren n b) →
            comp ρ₁ (pbι₁ ρ₁ ρ₂) ≡ comp ρ₂ (pbι₂ ρ₁ ρ₂)
pbCommVec ρ₁ ρ₂ = ren-ext λ k →
  trans (app-comp ρ₁ (pbι₁ ρ₁ ρ₂) k)
        (trans (pbComm ρ₁ ρ₂ k) (sym (app-comp ρ₂ (pbι₂ ρ₁ ρ₂) k)))

------------------------------------------------------------------------
-- Completeness of the first projection: any A-position whose ρ₁-image
-- lies in the range of ρ₂ is in the range of i₁.

pbComplete : ∀ {n a b} (ρ₁ : Ren n a) (ρ₂ : Ren n b) {p : Fin a} →
             app ρ₁ p ∈ʳ ρ₂ → p ∈ʳ pbι₁ ρ₁ ρ₂
pbComplete (x ∷ ρ₁) ρ₂ {zero}   mem with findPre x ρ₂ | pbData ρ₁ ρ₂
... | yes _ | (c , i₁ , i₂) = zero , refl
... | no ¬p | (c , i₁ , i₂) = ⊥-elim (¬p mem)
pbComplete (x ∷ ρ₁) ρ₂ {suc p'} mem with findPre x ρ₂ | pbData ρ₁ ρ₂ | pbComplete ρ₁ ρ₂ {p'} mem
... | yes _ | (c , i₁ , i₂) | ih = ∈ʳ-there (∈ʳ-suc i₁ ih)
... | no  _ | (c , i₁ , i₂) | ih = ∈ʳ-suc i₁ ih
