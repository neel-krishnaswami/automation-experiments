{-# OPTIONS --safe #-}

------------------------------------------------------------------------
-- The unification algorithm, presented as an inductive relation
--   Θ; Γ ⊢ t₁ = t₂ ↝ σ : Θ'
-- (written `Unify Θ t₁ t₂ Θ' σ`), and the proof of its correctness:
--
--   1.  σ : Sub Θ' Θ                       (by construction)
--   2.  sub σ t₁ ≡ sub σ t₂                (soundness)
--   3.  any unifier σ' factors as σ'' ; σ  (most general unifier)
--
-- Following the design notes, the number of metavariable slots is not
-- fixed: the metavariable rules introduce the fresh metavariable Z at a
-- freshly *prepended* slot (`zero`), and never remove the solved
-- metavariables (which become harmless: nothing refers to them).  This
-- keeps every lookup definitional and avoids reindexing, while proving
-- exactly the three stated properties.
------------------------------------------------------------------------

module Unification where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Properties using (_≟_)
open import Data.Vec.Base using (Vec; []; _∷_; lookup)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product.Base using (Σ; _,_; ∃; ∃-syntax; proj₁; proj₂)

open import Renaming
open import Term
open import Substitution
open import Equalizer
open import Pullback

------------------------------------------------------------------------
-- Occurrence of a metavariable in a term (the "occurs check").

data _∈ₘ_ {N} {Θ : MetaCtx N} (W : Fin N) : ∀ {Γ} → Term Θ Γ → Set where
  hereM : ∀ {Γ} {r : Ren Γ (lookup Θ W)} → W ∈ₘ mvar W r
  funMˡ : ∀ {Γ} {s t : Term Θ Γ} → W ∈ₘ s → W ∈ₘ fun s t
  funMʳ : ∀ {Γ} {s t : Term Θ Γ} → W ∈ₘ t → W ∈ₘ fun s t

-- A substitution that agrees with the identity on every metavariable
-- occurring in t fixes t.
sub-agreeId : ∀ {N} {Θ : MetaCtx N} {Γ} (σ : Sub Θ Θ) (t : Term Θ Γ) →
              (∀ {W} → W ∈ₘ t → ap σ W ≡ mvar W idR) → sub σ t ≡ t
sub-agreeId σ (var i)    h = refl
sub-agreeId σ con        h = refl
sub-agreeId σ (fun s t)  h = cong₂ fun (sub-agreeId σ s (λ m → h (funMˡ m)))
                                       (sub-agreeId σ t (λ m → h (funMʳ m)))
sub-agreeId σ (mvar X r) h = trans (cong (ren r) (h hereM)) (cong (mvar X) (comp-idʳ r))

------------------------------------------------------------------------
-- Connecting equalizer/pullback completeness to terms.

-- If [ρ₁]u = [ρ₂]u then u is covered by the equalizer embedding.
agreeCovered : ∀ {N} {Θ : MetaCtx N} {n a} (ρ₁ ρ₂ : Ren n a) (u : Term Θ a) →
               ren ρ₁ u ≡ ren ρ₂ u → Covered (eqEmb ρ₁ ρ₂) u
agreeCovered ρ₁ ρ₂ u eq mem = eqComplete ρ₁ ρ₂ (ren-fv-agree ρ₁ ρ₂ u eq mem)

-- If [ρ₁]u = [ρ₂]v then u is covered by the first pullback projection.
pbCovered : ∀ {N} {Θ : MetaCtx N} {n a b} (ρ₁ : Ren n a) (ρ₂ : Ren n b)
            (u : Term Θ a) (v : Term Θ b) →
            ren ρ₁ u ≡ ren ρ₂ v → Covered (pbι₁ ρ₁ ρ₂) u
pbCovered ρ₁ ρ₂ u v eq {p} mem =
  pbComplete ρ₁ ρ₂ (covered-ren ρ₂ v (subst (app ρ₁ p ∈fv_) eq (fv-ren ρ₁ u mem)))

------------------------------------------------------------------------
-- The unification relation.

data Unify {N} {Γ} : (Θ : MetaCtx N) (t₁ t₂ : Term Θ Γ)
                     {N' : ℕ} (Θ' : MetaCtx N') (σ : Sub Θ' Θ) → Set₁ where

  unVar : ∀ {Θ} {i : Fin Γ} → Unify Θ (var i) (var i) Θ idSub

  unCon : ∀ {Θ} → Unify Θ (con {Γ = Γ}) con Θ idSub

  unFun : ∀ {Θ s₁ s₂ t₁ t₂ N' Θ' N'' Θ''} {σ : Sub {N'} Θ' Θ} {σ' : Sub {N''} Θ'' Θ'} →
          Unify Θ s₁ s₂ Θ' σ →
          Unify Θ' (sub σ t₁) (sub σ t₂) Θ'' σ' →
          Unify Θ (fun s₁ t₁) (fun s₂ t₂) Θ'' (compSub σ' σ)

  unMetaSame : ∀ {Θ} (X : Fin N) (ρ₁ ρ₂ : Ren Γ (lookup Θ X)) →
          Unify Θ (mvar X ρ₁) (mvar X ρ₂)
                (eqSize ρ₁ ρ₂ ∷ Θ) (substAt X (mvar zero (eqEmb ρ₁ ρ₂)) wkId)

  unMetaDiff : ∀ {Θ} (X Y : Fin N) → X ≢ Y →
          (ρ₁ : Ren Γ (lookup Θ X)) (ρ₂ : Ren Γ (lookup Θ Y)) → Inj ρ₁ → Inj ρ₂ →
          Unify Θ (mvar X ρ₁) (mvar Y ρ₂)
                (pbSize ρ₁ ρ₂ ∷ Θ)
                (substAt X (mvar zero (pbι₁ ρ₁ ρ₂)) (substAt Y (mvar zero (pbι₂ ρ₁ ρ₂)) wkId))

  unMetaTm : ∀ {Θ} (X : Fin N) (ρ : Ren Γ (lookup Θ X)) (t : Term Θ Γ) →
          Inj ρ → ¬ (X ∈ₘ t) → (cov : Covered ρ t) →
          Unify Θ (mvar X ρ) t Θ (substAt X (strengthen ρ t cov) idSub)

  unTmMeta : ∀ {Θ} (X : Fin N) (ρ : Ren Γ (lookup Θ X)) (t : Term Θ Γ) →
          Inj ρ → ¬ (X ∈ₘ t) → (cov : Covered ρ t) →
          Unify Θ t (mvar X ρ) Θ (substAt X (strengthen ρ t cov) idSub)

------------------------------------------------------------------------
-- Property 2: soundness.   [σ] t₁ ≡ [σ] t₂.
-- (Property 1, Θ' ⊢ σ : Θ, holds by construction: σ is given as a Sub.)

-- The metavariable-vs-term case, shared by unMetaTm and unTmMeta.
metaTm-sound : ∀ {N} {Θ : MetaCtx N} {Γ} (X : Fin N) (ρ : Ren Γ (lookup Θ X))
               (t : Term Θ Γ) → ¬ (X ∈ₘ t) → (cov : Covered ρ t) →
               sub (substAt X (strengthen ρ t cov) idSub) (mvar X ρ)
                 ≡ sub (substAt X (strengthen ρ t cov) idSub) t
metaTm-sound {Θ = Θ} X ρ t occ cov =
  trans (cong (ren ρ) (substAt-here X (strengthen ρ t cov) idSub))
        (trans (ren-strengthen ρ t cov) (sym (sub-agreeId σ t agree)))
  where
    σ = substAt X (strengthen ρ t cov) idSub
    agree : ∀ {W} → W ∈ₘ t → ap σ W ≡ mvar W idR
    agree {W} m = substAt-there X (strengthen ρ t cov) idSub
                    (λ e → occ (subst (λ Z → Z ∈ₘ t) (sym e) m))

soundness : ∀ {N Γ} {Θ : MetaCtx N} {t₁ t₂ : Term Θ Γ} {N'} {Θ' : MetaCtx N'}
            {σ : Sub Θ' Θ} → Unify Θ t₁ t₂ Θ' σ → sub σ t₁ ≡ sub σ t₂
soundness unVar = refl
soundness unCon = refl
soundness (unFun {s₁ = s₁} {s₂} {t₁} {t₂} {σ = σ} {σ'} d₁ d₂) =
  cong₂ fun
    (trans (sym (sub-comp σ' σ s₁)) (trans (cong (sub σ') (soundness d₁)) (sub-comp σ' σ s₂)))
    (trans (sym (sub-comp σ' σ t₁)) (trans (soundness d₂) (sub-comp σ' σ t₂)))
soundness (unMetaSame X ρ₁ ρ₂) =
  trans (cong (ren ρ₁) (substAt-here X (mvar zero (eqEmb ρ₁ ρ₂)) wkId))
        (trans (cong (mvar zero) (eqAgreeVec ρ₁ ρ₂))
               (cong (ren ρ₂) (sym (substAt-here X (mvar zero (eqEmb ρ₁ ρ₂)) wkId))))
soundness (unMetaDiff X Y X≢Y ρ₁ ρ₂ inj₁ inj₂) =
  trans (cong (ren ρ₁) apσX)
        (trans (cong (mvar zero) (pbCommVec ρ₁ ρ₂)) (cong (ren ρ₂) (sym apσY)))
  where
    base = substAt Y (mvar zero (pbι₂ ρ₁ ρ₂)) wkId
    σ = substAt X (mvar zero (pbι₁ ρ₁ ρ₂)) base
    apσX : ap σ X ≡ mvar zero (pbι₁ ρ₁ ρ₂)
    apσX = substAt-here X (mvar zero (pbι₁ ρ₁ ρ₂)) base
    apσY : ap σ Y ≡ mvar zero (pbι₂ ρ₁ ρ₂)
    apσY = trans (substAt-there X (mvar zero (pbι₁ ρ₁ ρ₂)) base X≢Y)
                 (substAt-here Y (mvar zero (pbι₂ ρ₁ ρ₂)) wkId)
soundness (unMetaTm X ρ t inj occ cov) = metaTm-sound X ρ t occ cov
soundness (unTmMeta X ρ t inj occ cov) = sym (metaTm-sound X ρ t occ cov)

------------------------------------------------------------------------
-- Property 3: most general unifier.
--
-- For each rule we exhibit, for any competing unifier σ', a factoring
-- substitution σ'' with σ' ≐ σ'' ; σ.

-- The metavariable-vs-term case (σ'' = σ').
metaTm-mgu : ∀ {N Γ} (Θ : MetaCtx N) (X : Fin N) (ρ : Ren Γ (lookup Θ X)) (t : Term Θ Γ)
             (inj : Inj ρ) (cov : Covered ρ t) {N''} {Θ'' : MetaCtx N''} (σ' : Sub Θ'' Θ) →
             ren ρ (ap σ' X) ≡ sub σ' t →
             σ' ≐ compSub σ' (substAt X (strengthen ρ t cov) idSub)
metaTm-mgu Θ X ρ t inj cov σ' eq W with X ≟ W
... | yes refl = sym (ren-inj inj eq2)
  where
    eq2 : ren ρ (sub σ' (strengthen ρ t cov)) ≡ ren ρ (ap σ' X)
    eq2 = trans (sym (sub-ren σ' ρ (strengthen ρ t cov)))
                (trans (cong (sub σ') (ren-strengthen ρ t cov)) (sym eq))
... | no ¬p = sym (ren-id (ap σ' W))

-- The same-metavariable case (σ'' = consSub w σ', w the strengthening).
same-mgu : ∀ {N Γ} (Θ : MetaCtx N) (X : Fin N) (ρ₁ ρ₂ : Ren Γ (lookup Θ X))
           {N''} {Θ'' : MetaCtx N''} (σ' : Sub Θ'' Θ) →
           ren ρ₁ (ap σ' X) ≡ ren ρ₂ (ap σ' X) →
           Σ (Sub Θ'' (eqSize ρ₁ ρ₂ ∷ Θ))
             (λ σ'' → σ' ≐ compSub σ'' (substAt X (mvar zero (eqEmb ρ₁ ρ₂)) wkId))
same-mgu Θ X ρ₁ ρ₂ σ' eq = consSub w σ' , factor
  where
    u   = ap σ' X
    cov = agreeCovered ρ₁ ρ₂ u eq
    w   = strengthen (eqEmb ρ₁ ρ₂) u cov
    σ'' = consSub w σ'
    factor : σ' ≐ compSub σ'' (substAt X (mvar zero (eqEmb ρ₁ ρ₂)) wkId)
    factor W with X ≟ W
    ... | yes refl = sym (ren-strengthen (eqEmb ρ₁ ρ₂) u cov)
    ... | no ¬p    = sym (ren-id (ap σ' W))

-- The distinct-metavariables case (pullback).
diff-mgu : ∀ {N Γ} (Θ : MetaCtx N) (X Y : Fin N) (X≢Y : X ≢ Y)
           (ρ₁ : Ren Γ (lookup Θ X)) (ρ₂ : Ren Γ (lookup Θ Y)) (inj₂ : Inj ρ₂)
           {N''} {Θ'' : MetaCtx N''} (σ' : Sub Θ'' Θ) →
           ren ρ₁ (ap σ' X) ≡ ren ρ₂ (ap σ' Y) →
           Σ (Sub Θ'' (pbSize ρ₁ ρ₂ ∷ Θ))
             (λ σ'' → σ' ≐ compSub σ'' (substAt X (mvar zero (pbι₁ ρ₁ ρ₂))
                                          (substAt Y (mvar zero (pbι₂ ρ₁ ρ₂)) wkId)))
diff-mgu Θ X Y X≢Y ρ₁ ρ₂ inj₂ σ' eq = consSub w σ' , factor
  where
    u    = ap σ' X
    v    = ap σ' Y
    cov  = pbCovered ρ₁ ρ₂ u v eq
    w    = strengthen (pbι₁ ρ₁ ρ₂) u cov
    σ''  = consSub w σ'
    base = substAt Y (mvar zero (pbι₂ ρ₁ ρ₂)) wkId
    σd   = substAt X (mvar zero (pbι₁ ρ₁ ρ₂)) base
    -- ι₂ ∘ w recovers v, using ρ₂ injective and the pullback square.
    renι₂w≡v : ren (pbι₂ ρ₁ ρ₂) w ≡ v
    renι₂w≡v = ren-inj inj₂
      (trans (ren-comp ρ₂ (pbι₂ ρ₁ ρ₂) w)
      (trans (cong (λ r → ren r w) (sym (pbCommVec ρ₁ ρ₂)))
      (trans (sym (ren-comp ρ₁ (pbι₁ ρ₁ ρ₂) w))
      (trans (cong (ren ρ₁) (ren-strengthen (pbι₁ ρ₁ ρ₂) u cov)) eq))))
    factor : σ' ≐ compSub σ'' σd
    factor W with X ≟ W
    ... | yes refl = sym (ren-strengthen (pbι₁ ρ₁ ρ₂) u cov)
    ... | no ¬pX with Y ≟ W
    ...   | yes refl = sym renι₂w≡v
    ...   | no ¬pY  = sym (ren-id (ap σ' W))

-- The main theorem.
mgu : ∀ {N Γ} {Θ : MetaCtx N} {t₁ t₂ : Term Θ Γ} {N'} {Θ' : MetaCtx N'} {σ : Sub Θ' Θ} →
      Unify Θ t₁ t₂ Θ' σ →
      ∀ {N''} {Θ'' : MetaCtx N''} (σ' : Sub Θ'' Θ) → sub σ' t₁ ≡ sub σ' t₂ →
      Σ (Sub Θ'' Θ') (λ σ'' → σ' ≐ compSub σ'' σ)
mgu unVar σ' eq = σ' , λ X → sym (ren-id (ap σ' X))
mgu unCon σ' eq = σ' , λ X → sym (ren-id (ap σ' X))
mgu {Θ = Θ} (unFun {s₁ = s₁} {s₂} {t₁ = t₁} {t₂ = t₂} {σ = σa} {σ' = σb} d₁ d₂) σ' eq
  with mgu d₁ σ' (funˡ-inj eq)
... | τa , pa
  with mgu d₂ τa (trans (sub-comp τa σa t₁)
                  (trans (sym (sub-cong {Θ = Θ} pa t₁))
                  (trans (funʳ-inj eq)
                  (trans (sub-cong {Θ = Θ} pa t₂) (sym (sub-comp τa σa t₂))))))
... | τb , pb =
  τb , λ X → trans (pa X) (trans (compSub-congˡ pb σa X) (compSub-assoc τb σb σa X))
mgu {Θ = Θ} (unMetaSame X ρ₁ ρ₂) σ' eq = same-mgu Θ X ρ₁ ρ₂ σ' eq
mgu {Θ = Θ} (unMetaDiff X Y X≢Y ρ₁ ρ₂ inj₁ inj₂) σ' eq = diff-mgu Θ X Y X≢Y ρ₁ ρ₂ inj₂ σ' eq
mgu {Θ = Θ} (unMetaTm X ρ t inj occ cov) σ' eq = σ' , metaTm-mgu Θ X ρ t inj cov σ' eq
mgu {Θ = Θ} (unTmMeta X ρ t inj occ cov) σ' eq = σ' , metaTm-mgu Θ X ρ t inj cov σ' (sym eq)

------------------------------------------------------------------------
-- The three correctness properties, bundled, exactly as stated at the
-- end of unification.md:
--
--   If Θ; Γ ⊢ t₁ and Θ; Γ ⊢ t₂ and Θ; Γ ⊢ t₁ = t₂ ↝ σ : Θ' then
--     1. Θ' ⊢ σ : Θ
--     2. [σ] t₁ = [σ] t₂
--     3. for all Θ'' ⊢ σ' : Θ with [σ'] t₁ = [σ'] t₂,
--        there exists Θ'' ⊢ σ'' : Θ' such that σ' = σ'' ; σ
--
-- Property 1 (Θ' ⊢ σ : Θ) holds *by construction*: it is the very type
-- of the substitution σ produced by the relation, namely `Sub Θ' Θ`.

record Correct {N Γ} (Θ : MetaCtx N) (t₁ t₂ : Term Θ Γ)
               {N'} (Θ' : MetaCtx N') (σ : Sub Θ' Θ) : Set where
  field
    -- property 2
    sound        : sub σ t₁ ≡ sub σ t₂
    -- property 3
    most-general : ∀ {N''} {Θ'' : MetaCtx N''} (σ' : Sub Θ'' Θ) →
                   sub σ' t₁ ≡ sub σ' t₂ →
                   Σ (Sub Θ'' Θ') (λ σ'' → σ' ≐ compSub σ'' σ)

correct : ∀ {N Γ} {Θ : MetaCtx N} {t₁ t₂ : Term Θ Γ} {N'} {Θ' : MetaCtx N'}
          {σ : Sub Θ' Θ} → Unify Θ t₁ t₂ Θ' σ → Correct Θ t₁ t₂ Θ' σ
correct u = record { sound = soundness u ; most-general = mgu u }
