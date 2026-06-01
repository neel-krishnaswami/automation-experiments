------------------------------------------------------------------------
-- Metaweakening Θ ⊇ Θ' and metavariable removal Θ -ᵐ X ≡ Θ'.
--
-- Both are defined at the list level (operating on mlist), with the
-- MCtx records carrying distinctness automatically.
------------------------------------------------------------------------

{-# OPTIONS #-}

module MetaWeakening where

open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; subst)
open import Relation.Nullary using (¬_)

open import Base
open import Renaming
open import Term
open import Substitution

------------------------------------------------------------------------
-- Metaweakening — list-level on (Name × Ctx) entries.
------------------------------------------------------------------------

infix 4 _⊇ᴸ_
data _⊇ᴸ_ : List (Name × Ctx) → List (Name × Ctx) → Set where
  wkl-nil  : [] ⊇ᴸ []
  wkl-cons : ∀ {Θ Θ' X Γ}  → Θ ⊇ᴸ Θ' → ((X , Γ) ∷ Θ) ⊇ᴸ ((X , Γ) ∷ Θ')
  wkl-skip : ∀ {Θ Θ' X Γ}  → Θ ⊇ᴸ Θ' → ((X , Γ) ∷ Θ) ⊇ᴸ Θ'

infix 4 _⊇_
_⊇_ : MCtx → MCtx → Set
Θ ⊇ Θ' = mlist Θ ⊇ᴸ mlist Θ'

⊇ᴸ-refl : ∀ {Θ} → Θ ⊇ᴸ Θ
⊇ᴸ-refl {[]}    = wkl-nil
⊇ᴸ-refl {_ ∷ _} = wkl-cons ⊇ᴸ-refl

⊇-refl : ∀ {Θ} → Θ ⊇ Θ
⊇-refl = ⊇ᴸ-refl

⊇ᴸ-trans : ∀ {Θ₁ Θ₂ Θ₃} → Θ₁ ⊇ᴸ Θ₂ → Θ₂ ⊇ᴸ Θ₃ → Θ₁ ⊇ᴸ Θ₃
⊇ᴸ-trans wkl-nil       wkl-nil       = wkl-nil
⊇ᴸ-trans (wkl-cons w₁) (wkl-cons w₂) = wkl-cons (⊇ᴸ-trans w₁ w₂)
⊇ᴸ-trans (wkl-cons w₁) (wkl-skip w₂) = wkl-skip (⊇ᴸ-trans w₁ w₂)
⊇ᴸ-trans (wkl-skip w₁) w₂            = wkl-skip (⊇ᴸ-trans w₁ w₂)

⊇-trans : ∀ {Θ₁ Θ₂ Θ₃} → Θ₁ ⊇ Θ₂ → Θ₂ ⊇ Θ₃ → Θ₁ ⊇ Θ₃
⊇-trans = ⊇ᴸ-trans

------------------------------------------------------------------------
-- Metavariable removal — defined in Term.agda; re-imported here.
------------------------------------------------------------------------
-- Aux 5.0: metaweakening preserves membership.
------------------------------------------------------------------------

mwk-memᴸ :
  ∀ {Θ Θ' X Γ} → Θ ⊇ᴸ Θ' → X ⦂[ Γ ]∈ᴸ Θ' → X ⦂[ Γ ]∈ᴸ Θ
mwk-memᴸ (wkl-cons _) m-hereᴸ        = m-hereᴸ
mwk-memᴸ (wkl-cons w) (m-thereᴸ m)   = m-thereᴸ (mwk-memᴸ w m)
mwk-memᴸ (wkl-skip w) m              = m-thereᴸ (mwk-memᴸ w m)

mwk-mem :
  ∀ {Θ Θ' X Γ} → Θ ⊇ Θ' → X ⦂[ Γ ]∈ Θ' → X ⦂[ Γ ]∈ Θ
mwk-mem = mwk-memᴸ

------------------------------------------------------------------------
-- §5.1: metaweakening preserves term well-formedness.
------------------------------------------------------------------------

mwk-term : ∀ {Θ Θ' Γ t} → Θ ⊇ Θ' → Θ' ، Γ ⊢ t → Θ ، Γ ⊢ t
mwk-term sub (wf-var x∈)     = wf-var x∈
mwk-term sub wf-con          = wf-con
mwk-term sub (wf-fun d₁ d₂)  = wf-fun (mwk-term sub d₁) (mwk-term sub d₂)
mwk-term sub (wf-meta {Γ_X = Γ_X} m wfρ) = wf-meta (mwk-memᴸ {Γ = Γ_X} sub m) wfρ

------------------------------------------------------------------------
-- §6.1: metaweakening preserves substitution well-formedness.
------------------------------------------------------------------------

mwk-subᴸ : ∀ {Θ Θ' Θ'' σ} → Θ ⊇ Θ' → Θ' ⊢ˢᴸ σ ∶ Θ'' → Θ ⊢ˢᴸ σ ∶ Θ''
mwk-subᴸ sub sl-nil               = sl-nil
mwk-subᴸ sub (sl-cons d wf-t fresh) =
  sl-cons (mwk-subᴸ sub d) (mwk-term sub wf-t) fresh

mwk-sub : ∀ {Θ Θ' Θ'' σ} → Θ ⊇ Θ' → Θ' ⊢ˢ σ ∶ Θ'' → Θ ⊢ˢ σ ∶ Θ''
mwk-sub = mwk-subᴸ

------------------------------------------------------------------------
-- §6.4: id-sub is well-typed.
------------------------------------------------------------------------

id-sub-list-wf-aux :
  ∀ (Θ : MCtx) (suffix : List (Name × Ctx))
  → DistinctM suffix
  → (∀ {X Γ} → X ⦂[ Γ ]∈ᴸ suffix → X ⦂[ Γ ]∈ᴸ mlist Θ)
  → Θ ⊢ˢᴸ id-sub-list suffix ∶ suffix
id-sub-list-wf-aux Θ []              _                 _     = sl-nil
id-sub-list-wf-aux Θ ((X , Γ) ∷ ms) (dm-cons fresh d) embed =
  sl-cons
    (id-sub-list-wf-aux Θ ms d (λ m → embed (m-thereᴸ m)))
    (wf-meta (embed m-hereᴸ) (id-ren-wf {Γ}))
    fresh

id-sub-wf : ∀ {Θ} → Θ ⊢ˢ id-sub Θ ∶ Θ
id-sub-wf {Θ} = id-sub-list-wf-aux Θ (mlist Θ) (mnd Θ) (λ m → m)
