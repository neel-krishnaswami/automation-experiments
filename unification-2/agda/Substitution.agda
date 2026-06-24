{-# OPTIONS --safe #-}

------------------------------------------------------------------------
-- Metasubstitutions  Δ ⊢ σ : Θ  (written `Sub Δ Θ`).
--
-- A metasubstitution assigns, to each metavariable X of the source
-- context Θ, a term over the target context Δ in X's dependency context.
-- We represent it as a record wrapping a *function*; equality of
-- substitutions is the pointwise relation `_≐_`, which is exactly the
-- specification's notion (two substitutions are equal iff they act
-- identically on every metavariable).  This avoids any appeal to
-- function extensionality, while keeping `Sub Δ Θ` a rigid type former.
------------------------------------------------------------------------

module Substitution where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Properties using (_≟_)
open import Data.Vec.Base using (Vec; []; _∷_; lookup)
open import Function.Base using (id)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂)
open import Data.Empty using (⊥-elim)

open import Renaming
open import Term

------------------------------------------------------------------------
-- Substitutions and their (pointwise) equality.

record Sub {N M} (Δ : MetaCtx N) (Θ : Vec ℕ M) : Set where
  constructor mkSub
  field ap : (X : Fin M) → Term Δ (lookup Θ X)
open Sub public

infix 4 _≐_
_≐_ : ∀ {N M} {Δ : MetaCtx N} {Θ : Vec ℕ M} → Sub Δ Θ → Sub Δ Θ → Set
σ ≐ τ = ∀ X → ap σ X ≡ ap τ X

≐-refl : ∀ {N M} {Δ : MetaCtx N} {Θ : Vec ℕ M} {σ : Sub Δ Θ} → σ ≐ σ
≐-refl X = refl

≐-sym : ∀ {N M} {Δ : MetaCtx N} {Θ : Vec ℕ M} {σ τ : Sub Δ Θ} → σ ≐ τ → τ ≐ σ
≐-sym e X = sym (e X)

≐-trans : ∀ {N M} {Δ : MetaCtx N} {Θ : Vec ℕ M} {σ τ ρ : Sub Δ Θ} →
          σ ≐ τ → τ ≐ ρ → σ ≐ ρ
≐-trans e e' X = trans (e X) (e' X)

------------------------------------------------------------------------
-- Application of a substitution to a term.

sub : ∀ {N M} {Δ : MetaCtx N} {Θ : Vec ℕ M} {Γ} → Sub Δ Θ → Term Θ Γ → Term Δ Γ
sub σ (var i)    = var i
sub σ con        = con
sub σ (fun s t)  = fun (sub σ s) (sub σ t)
sub σ (mvar X r) = ren r (ap σ X)

-- Metasubstitution commutes with object renaming.
sub-ren : ∀ {N M} {Δ : MetaCtx N} {Θ : Vec ℕ M} {Γ Γ'}
          (σ : Sub Δ Θ) (ρ : Ren Γ' Γ) (t : Term Θ Γ) →
          sub σ (ren ρ t) ≡ ren ρ (sub σ t)
sub-ren σ ρ (var i)    = refl
sub-ren σ ρ con        = refl
sub-ren σ ρ (fun s t)  = cong₂ fun (sub-ren σ ρ s) (sub-ren σ ρ t)
sub-ren σ ρ (mvar X r) = sym (ren-comp ρ r (ap σ X))

-- Applying a substitution respects pointwise equality.
sub-cong : ∀ {N M} {Δ : MetaCtx N} {Θ : Vec ℕ M} {Γ} {σ τ : Sub Δ Θ} → σ ≐ τ →
           (t : Term Θ Γ) → sub σ t ≡ sub τ t
sub-cong e (var i)    = refl
sub-cong e con        = refl
sub-cong e (fun s t)  = cong₂ fun (sub-cong e s) (sub-cong e t)
sub-cong e (mvar X r) = cong (ren r) (e X)

------------------------------------------------------------------------
-- Identity and composition.

idSub : ∀ {N} {Θ : MetaCtx N} → Sub Θ Θ
idSub = mkSub λ X → mvar X idR

sub-id : ∀ {N} {Θ : MetaCtx N} {Γ} (t : Term Θ Γ) → sub idSub t ≡ t
sub-id (var i)    = refl
sub-id con        = refl
sub-id (fun s t)  = cong₂ fun (sub-id s) (sub-id t)
sub-id (mvar X r) = cong (mvar X) (comp-idʳ r)

-- Composition:  (compSub σ' σ) = σ' ; σ  applies σ then σ'.
compSub : ∀ {N M L} {Δ' : MetaCtx N} {Δ : MetaCtx M} {Θ : Vec ℕ L} →
          Sub Δ' Δ → Sub Δ Θ → Sub Δ' Θ
compSub σ' σ = mkSub λ X → sub σ' (ap σ X)

sub-comp : ∀ {N M L} {Δ' : MetaCtx N} {Δ : MetaCtx M} {Θ : Vec ℕ L} {Γ}
           (σ' : Sub Δ' Δ) (σ : Sub Δ Θ) (t : Term Θ Γ) →
           sub σ' (sub σ t) ≡ sub (compSub σ' σ) t
sub-comp σ' σ (var i)    = refl
sub-comp σ' σ con        = refl
sub-comp σ' σ (fun s t)  = cong₂ fun (sub-comp σ' σ s) (sub-comp σ' σ t)
sub-comp σ' σ (mvar X r) = sub-ren σ' r (ap σ X)

-- Monoid laws for composition (pointwise).
compSub-idˡ : ∀ {N M} {Δ : MetaCtx N} {Θ : Vec ℕ M} (σ : Sub Δ Θ) → compSub idSub σ ≐ σ
compSub-idˡ σ X = sub-id (ap σ X)

compSub-idʳ : ∀ {N M} {Δ : MetaCtx N} {Θ : Vec ℕ M} (σ : Sub Δ Θ) → compSub σ idSub ≐ σ
compSub-idʳ σ X = ren-id (ap σ X)

compSub-assoc : ∀ {N M L K} {Δ₃ : MetaCtx N} {Δ₂ : MetaCtx M} {Δ₁ : MetaCtx L}
                {Θ : Vec ℕ K} (a : Sub Δ₃ Δ₂) (b : Sub Δ₂ Δ₁) (c : Sub Δ₁ Θ) →
                compSub (compSub a b) c ≐ compSub a (compSub b c)
compSub-assoc a b c X = sym (sub-comp a b (ap c X))

-- compSub respects pointwise equality in its left argument.
compSub-congˡ : ∀ {N M L} {Δ' : MetaCtx N} {Δ : MetaCtx M} {Θ : Vec ℕ L}
                {σ' τ' : Sub Δ' Δ} → σ' ≐ τ' → (σ : Sub Δ Θ) →
                compSub σ' σ ≐ compSub τ' σ
compSub-congˡ e σ X = sub-cong e (ap σ X)

------------------------------------------------------------------------
-- Updating a substitution at a single metavariable slot.
--
--   substAt X u base  acts as `u` on slot X and as `base` elsewhere.

substAt-fun : ∀ {N M} {Δ : MetaCtx N} {Θ : Vec ℕ M} →
              (X : Fin M) → Term Δ (lookup Θ X) → Sub Δ Θ →
              (W : Fin M) → Term Δ (lookup Θ W)
substAt-fun X u base W with X ≟ W
... | yes refl = u
... | no  _    = ap base W

substAt : ∀ {N M} {Δ : MetaCtx N} {Θ : Vec ℕ M} →
          (X : Fin M) → Term Δ (lookup Θ X) → Sub Δ Θ → Sub Δ Θ
substAt X u base = mkSub (substAt-fun X u base)

substAt-here : ∀ {N M} {Δ : MetaCtx N} {Θ : Vec ℕ M}
               (X : Fin M) (u : Term Δ (lookup Θ X)) (base : Sub Δ Θ) →
               ap (substAt X u base) X ≡ u
substAt-here X u base with X ≟ X
... | yes refl = refl
... | no  ¬p   = ⊥-elim (¬p refl)

substAt-there : ∀ {N M} {Δ : MetaCtx N} {Θ : Vec ℕ M}
                (X : Fin M) (u : Term Δ (lookup Θ X)) (base : Sub Δ Θ)
                {W : Fin M} → X ≢ W → ap (substAt X u base) W ≡ ap base W
substAt-there X u base {W} ¬p with X ≟ W
... | yes p  = ⊥-elim (¬p p)
... | no  _  = refl

------------------------------------------------------------------------
-- Extending a substitution by a term in a freshly *prepended* slot.
-- `consSub u σ` assigns u to metavariable `zero` and σ to the rest.
-- (Used as the most-general factoring substitution σ'' for the
-- metavariable rules, where the fresh metavariable Z sits at slot zero.)

consSub : ∀ {N M} {Δ : MetaCtx N} {Θ : Vec ℕ M} {a} →
          Term Δ a → Sub Δ Θ → Sub Δ (a ∷ Θ)
consSub u σ = mkSub λ { zero → u ; (suc W) → ap σ W }

-- The identity substitution weakened by a prepended slot:
-- maps metavariable W (of Θ) to (suc W)[id] in (a ∷ Θ).
wkId : ∀ {N} {Θ : MetaCtx N} {a} → Sub (a ∷ Θ) Θ
wkId = mkSub λ W → mvar (suc W) idR
