{-# OPTIONS --safe #-}

------------------------------------------------------------------------
-- The equalizer of two renamings ρ₁, ρ₂ : Fin a → Fin n  (same domain).
--
-- This corresponds to the specification's coequalizer judgment
--   Γ ⊢ ρ₁ • ρ₂ = i : Γ'
-- (which, because of the variance of metavariable renamings, is an
-- equalizer in the category of contexts and injective renamings).
--
-- We build the subcontext Γ' (its size) together with the embedding
-- i : Fin Γ' → Fin a picking out exactly the positions on which ρ₁ and ρ₂
-- agree, and prove:
--   * agree    : ρ₁ ∘ i = ρ₂ ∘ i        (the embedding lands in agreement)
--   * complete : every agreeing position is in the range of i.
------------------------------------------------------------------------

module Equalizer where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Properties using (_≟_)
open import Data.Vec.Base using (Vec; []; _∷_; lookup; map)
open import Data.Vec.Properties using (lookup-map)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
open import Data.Empty using (⊥-elim)

open import Renaming

------------------------------------------------------------------------
-- The construction:  size + embedding, computed together.

eqData : ∀ {n a} (ρ₁ ρ₂ : Ren n a) → Σ ℕ (Ren a)
eqData []        []        = 0 , []
eqData (x₁ ∷ ρ₁) (x₂ ∷ ρ₂) with x₁ ≟ x₂ | eqData ρ₁ ρ₂
... | yes _ | (s , e) = suc s , (zero ∷ map suc e)
... | no  _ | (s , e) = s , map suc e

eqSize : ∀ {n a} (ρ₁ ρ₂ : Ren n a) → ℕ
eqSize ρ₁ ρ₂ = proj₁ (eqData ρ₁ ρ₂)

eqEmb : ∀ {n a} (ρ₁ ρ₂ : Ren n a) → Ren a (eqSize ρ₁ ρ₂)
eqEmb ρ₁ ρ₂ = proj₂ (eqData ρ₁ ρ₂)

------------------------------------------------------------------------
-- The embedding lands in the agreement set.

eqAgree : ∀ {n a} (ρ₁ ρ₂ : Ren n a) (k : Fin (eqSize ρ₁ ρ₂)) →
          app ρ₁ (app (eqEmb ρ₁ ρ₂) k) ≡ app ρ₂ (app (eqEmb ρ₁ ρ₂) k)
eqAgree []        []        ()
eqAgree (x₁ ∷ ρ₁) (x₂ ∷ ρ₂) k with x₁ ≟ x₂ | eqData ρ₁ ρ₂ | eqAgree ρ₁ ρ₂
... | yes p | (s , e) | ih = lemma k
  where
    lemma : (k : Fin (suc s)) →
            app (x₁ ∷ ρ₁) (app (zero ∷ map suc e) k) ≡ app (x₂ ∷ ρ₂) (app (zero ∷ map suc e) k)
    lemma zero      = p
    lemma (suc k')  =
      trans (cong (app (x₁ ∷ ρ₁)) (lookup-map k' suc e))
            (trans (ih k') (sym (cong (app (x₂ ∷ ρ₂)) (lookup-map k' suc e))))
... | no  _ | (s , e) | ih = λ-no k
  where
    λ-no : (k : Fin s) →
           app (x₁ ∷ ρ₁) (app (map suc e) k) ≡ app (x₂ ∷ ρ₂) (app (map suc e) k)
    λ-no k =
      trans (cong (app (x₁ ∷ ρ₁)) (lookup-map k suc e))
            (trans (ih k) (sym (cong (app (x₂ ∷ ρ₂)) (lookup-map k suc e))))

-- The Vec-level statement of agreement, used for soundness.
eqAgreeVec : ∀ {n a} (ρ₁ ρ₂ : Ren n a) →
             comp ρ₁ (eqEmb ρ₁ ρ₂) ≡ comp ρ₂ (eqEmb ρ₁ ρ₂)
eqAgreeVec ρ₁ ρ₂ = ren-ext λ k →
  trans (app-comp ρ₁ (eqEmb ρ₁ ρ₂) k)
        (trans (eqAgree ρ₁ ρ₂ k) (sym (app-comp ρ₂ (eqEmb ρ₁ ρ₂) k)))

------------------------------------------------------------------------
-- Completeness: every agreeing position is in the range of the embedding.

eqComplete : ∀ {n a} (ρ₁ ρ₂ : Ren n a) {i : Fin a} →
             app ρ₁ i ≡ app ρ₂ i → i ∈ʳ eqEmb ρ₁ ρ₂
eqComplete []        []        {()}
eqComplete (x₁ ∷ ρ₁) (x₂ ∷ ρ₂) {zero}   hyp with x₁ ≟ x₂ | eqData ρ₁ ρ₂
... | yes _ | (s , e) = zero , refl
... | no ¬p | (s , e) = ⊥-elim (¬p hyp)
eqComplete (x₁ ∷ ρ₁) (x₂ ∷ ρ₂) {suc i'} hyp with x₁ ≟ x₂ | eqData ρ₁ ρ₂ | eqComplete ρ₁ ρ₂ {i'} hyp
... | yes _ | (s , e) | ih = ∈ʳ-there (∈ʳ-suc e ih)
... | no  _ | (s , e) | ih = ∈ʳ-suc e ih
