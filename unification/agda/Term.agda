------------------------------------------------------------------------
-- Terms, term well-formedness, and the action of renamings on terms.
--
-- We use list-level well-formedness `Θ ، Γ ⊢ t`, with metavariable
-- contexts carrying distinctness on the metavariable names.
------------------------------------------------------------------------

{-# OPTIONS #-}

module Term where

open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Data.Nat.Properties using (_≟_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; cong₂)
open import Data.Empty using (⊥-elim)

open import Base
open import Renaming

------------------------------------------------------------------------
-- Abstract function symbols and constants
------------------------------------------------------------------------

-- Concrete instantiation: symbols and constants are natural numbers.
-- (The development is parametric in these but Agda's parameter handling
-- works better with concrete witnesses.)
open import Data.Nat using (ℕ)

Sym : Set
Sym = ℕ

Con : Set
Con = ℕ

------------------------------------------------------------------------
-- Metavariable contexts as records with distinctness on the metavariable names.
------------------------------------------------------------------------

-- Membership in a list of (Name × Ctx) pairs (in the first component).
infix 4 _∈Fstᴸ_
data _∈Fstᴸ_ : Name → List (Name × Ctx) → Set where
  fst-here  : ∀ {X Γ ms}                  → X ∈Fstᴸ ((X , Γ) ∷ ms)
  fst-there : ∀ {X Y Γ ms} → X ∈Fstᴸ ms   → X ∈Fstᴸ ((Y , Γ) ∷ ms)

infix 4 _∉Fstᴸ_
_∉Fstᴸ_ : Name → List (Name × Ctx) → Set
X ∉Fstᴸ ms = ¬ (X ∈Fstᴸ ms)

data DistinctM : List (Name × Ctx) → Set where
  dm-nil  : DistinctM []
  dm-cons : ∀ {X Γ ms} → X ∉Fstᴸ ms → DistinctM ms → DistinctM ((X , Γ) ∷ ms)

record MCtx : Set where
  constructor mkMCtx
  field
    mlist : List (Name × Ctx)
    mnd   : DistinctM mlist

open MCtx public

[]ᵐ : MCtx
[]ᵐ = mkMCtx [] dm-nil

extend-M : (X : Name) (Γ : Ctx) (Θ : MCtx) → X ∉Fstᴸ mlist Θ → MCtx
extend-M X Γ Θ fresh = mkMCtx ((X , Γ) ∷ mlist Θ) (dm-cons fresh (mnd Θ))

------------------------------------------------------------------------
-- Metavariable removal — lifted up so both Substitution and
-- MetaWeakening can reference it.
------------------------------------------------------------------------

infix 4 _-ᵐᴸ_≡_
data _-ᵐᴸ_≡_ : List (Name × Ctx) → Name → List (Name × Ctx) → Set where
  rml-here  : ∀ {Θ X Γ}                                            → ((X , Γ) ∷ Θ) -ᵐᴸ X ≡ Θ
  rml-there : ∀ {Θ Θ' X Y Γ_Y}
              → X ≢ Y
              → Θ -ᵐᴸ X ≡ Θ'
              → ((Y , Γ_Y) ∷ Θ) -ᵐᴸ X ≡ ((Y , Γ_Y) ∷ Θ')

infix 4 _-ᵐ_≡_
_-ᵐ_≡_ : MCtx → Name → MCtx → Set
Θ -ᵐ X ≡ Θ' = mlist Θ -ᵐᴸ X ≡ mlist Θ'

------------------------------------------------------------------------
-- Metavariable lookup membership
------------------------------------------------------------------------

infix 4 _⦂[_]∈ᴸ_
data _⦂[_]∈ᴸ_ : Name → Ctx → List (Name × Ctx) → Set where
  m-hereᴸ  : ∀ {X Γ ms}                       → X ⦂[ Γ ]∈ᴸ ((X , Γ) ∷ ms)
  m-thereᴸ : ∀ {X Y Γ Γ' ms} → X ⦂[ Γ ]∈ᴸ ms → X ⦂[ Γ ]∈ᴸ ((Y , Γ') ∷ ms)

infix 4 _⦂[_]∈_
_⦂[_]∈_ : Name → Ctx → MCtx → Set
X ⦂[ Γ ]∈ Θ = X ⦂[ Γ ]∈ᴸ mlist Θ

------------------------------------------------------------------------
-- Terms
------------------------------------------------------------------------

data Term : Set where
  vr : Name → Term
  cn : Con  → Term
  fn : Sym  → Term → Term → Term
  mv : Name → Ren  → Term

------------------------------------------------------------------------
-- Term well-formedness (list-level: lifts to MCtx record via mlist).
------------------------------------------------------------------------

infix 4 _،_⊢_
data _،_⊢_ : MCtx → Ctx → Term → Set where
  wf-var  : ∀ {Θ Γ a}      → a ∈ Γ                          → Θ ، Γ ⊢ vr a
  wf-con  : ∀ {Θ Γ c}                                       → Θ ، Γ ⊢ cn c
  wf-fun  : ∀ {Θ Γ f t₁ t₂}
            → Θ ، Γ ⊢ t₁ → Θ ، Γ ⊢ t₂                      → Θ ، Γ ⊢ fn f t₁ t₂
  wf-meta : ∀ {Θ Γ X Γ_X ρ}
            → X ⦂[ Γ_X ]∈ Θ
            → Γ ⊢ ρ ∶ Γ_X
            → Θ ، Γ ⊢ mv X ρ

------------------------------------------------------------------------
-- Action of a renaming on a term
------------------------------------------------------------------------

infix 25 [_]_
[_]_ : Ren → Term → Term
[ ρ ] (vr a)     = vr (look ρ a)
[ ρ ] (cn c)     = cn c
[ ρ ] (fn f t u) = fn f ([ ρ ] t) ([ ρ ] u)
[ ρ ] (mv X ρ')  = mv X (ρ ⨾ ρ')

------------------------------------------------------------------------
-- §2.5: identity renaming acts trivially on well-typed terms.
------------------------------------------------------------------------

id-ren-action : ∀ {Θ Γ t} → Θ ، Γ ⊢ t → [ id-ren Γ ] t ≡ t
id-ren-action {Γ = Γ} (wf-var x∈)        = cong vr (id-ren-look {Γ} x∈)
id-ren-action          wf-con            = refl
id-ren-action          (wf-fun d₁ d₂)    =
  cong₂ (fn _) (id-ren-action d₁) (id-ren-action d₂)
id-ren-action {Γ = Γ} (wf-meta {X = X} {Γ_X = Γ_X} m wfρ) =
  cong (mv X) (id-ren-left-id-direct {Γ} {Γ_X} wfρ)
