{-# OPTIONS --safe #-}

------------------------------------------------------------------------
-- Terms over a metavariable context Θ and an object context Γ.
--
-- The metavariable context is represented as a vector `Vec ℕ N`: there
-- are N metavariable "slots", and the arity (dependency-context size) of
-- metavariable X (an element of `Fin N`) is `lookup Θ X`.
--
-- Crucially the number of slots N is *invariant* under unification: the
-- algorithm only ever changes the arity recorded at a slot (and reuses a
-- slot for the freshly introduced metavariable), so we never reindex.
------------------------------------------------------------------------

module Term where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Properties using (_≟_)
open import Data.Vec.Base using (Vec; []; _∷_; lookup; map; tabulate)
open import Data.Vec.Properties using (lookup∘tabulate; tabulate-cong; tabulate∘lookup)
open import Function.Base using (id; _∘_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Data.Product.Base using (Σ; _,_; ∃; ∃-syntax; proj₁; proj₂)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Empty using (⊥-elim)

open import Renaming

-- A metavariable context with N slots.
MetaCtx : ℕ → Set
MetaCtx N = Vec ℕ N

------------------------------------------------------------------------
-- Terms.  t ::= a | c | f(t₁,t₂) | X[ρ]

data Term {N} (Θ : MetaCtx N) : ℕ → Set where
  var  : ∀ {Γ} → Fin Γ → Term Θ Γ
  con  : ∀ {Γ} → Term Θ Γ
  fun  : ∀ {Γ} → Term Θ Γ → Term Θ Γ → Term Θ Γ
  mvar : ∀ {Γ} (X : Fin N) → Ren Γ (lookup Θ X) → Term Θ Γ

------------------------------------------------------------------------
-- The action of an object renaming on a term:  [ρ] t.
-- ρ : Ren Δ Γ  is a map Fin Γ → Fin Δ, so it sends Term Θ Γ to Term Θ Δ.

ren : ∀ {N} {Θ : MetaCtx N} {Γ Δ} → Ren Δ Γ → Term Θ Γ → Term Θ Δ
ren ρ (var i)    = var (app ρ i)
ren ρ con        = con
ren ρ (fun s t)  = fun (ren ρ s) (ren ρ t)
ren ρ (mvar X r) = mvar X (comp ρ r)

-- Functor laws.

ren-id : ∀ {N} {Θ : MetaCtx N} {Γ} (t : Term Θ Γ) → ren idR t ≡ t
ren-id (var i)    = cong var (app-idR i)
ren-id con        = refl
ren-id (fun s t)  = cong₂ fun (ren-id s) (ren-id t)
ren-id (mvar X r) = cong (mvar X) (comp-idˡ r)

ren-comp : ∀ {N} {Θ : MetaCtx N} {Γ Δ E} (ρ : Ren E Δ) (σ : Ren Δ Γ) (t : Term Θ Γ) →
           ren ρ (ren σ t) ≡ ren (comp ρ σ) t
ren-comp ρ σ (var i)    = cong var (sym (app-comp ρ σ i))
ren-comp ρ σ con        = refl
ren-comp ρ σ (fun s t)  = cong₂ fun (ren-comp ρ σ s) (ren-comp ρ σ t)
ren-comp ρ σ (mvar X r) = cong (mvar X) (sym (comp-assoc ρ σ r))

-- Renaming respects equality of renamings.
ren-cong : ∀ {N} {Θ : MetaCtx N} {Γ Δ} {ρ ρ' : Ren Δ Γ} → ρ ≡ ρ' →
           (t : Term Θ Γ) → ren ρ t ≡ ren ρ' t
ren-cong e t = cong (λ ρ → ren ρ t) e

------------------------------------------------------------------------
-- Free (object) variables of a term.

data _∈fv_ {N} {Θ : MetaCtx N} : ∀ {Γ} → Fin Γ → Term Θ Γ → Set where
  here   : ∀ {Γ} {i : Fin Γ} → i ∈fv var i
  funˡ   : ∀ {Γ} {i : Fin Γ} {s t : Term Θ Γ} → i ∈fv s → i ∈fv fun s t
  funʳ   : ∀ {Γ} {i : Fin Γ} {s t : Term Θ Γ} → i ∈fv t → i ∈fv fun s t
  inMvar : ∀ {Γ} {i : Fin Γ} {X} {r : Ren Γ (lookup Θ X)} {k} → app r k ≡ i → i ∈fv mvar X r

-- "t is covered by ρ": every free variable of t is in the range of ρ.
Covered : ∀ {N} {Θ : MetaCtx N} {Γ m} → Ren Γ m → Term Θ Γ → Set
Covered ρ t = ∀ {i} → i ∈fv t → i ∈ʳ ρ

-- A renamed term is covered by the renaming used.
covered-ren : ∀ {N} {Θ : MetaCtx N} {Γ Δ} (ρ : Ren Δ Γ) (t : Term Θ Γ) →
              Covered ρ (ren ρ t)
covered-ren ρ (var i)    here          = i , refl
covered-ren ρ (fun s t)  (funˡ m)      = covered-ren ρ s m
covered-ren ρ (fun s t)  (funʳ m)      = covered-ren ρ t m
covered-ren ρ (mvar X r) (inMvar {k = k} e) =
  app r k , trans (sym (app-comp ρ r k)) e

------------------------------------------------------------------------
-- Strengthening:  [ρ⁻¹] t, the inverse image of t under ρ.
-- Defined for any covered term; needs no injectivity hypothesis itself.

strengthen : ∀ {N} {Θ : MetaCtx N} {Γ m} (ρ : Ren Γ m) (t : Term Θ Γ) →
             Covered ρ t → Term Θ m
strengthen ρ (var i)    cov = var (proj₁ (cov here))
strengthen ρ con        cov = con
strengthen ρ (fun s t)  cov = fun (strengthen ρ s (λ m → cov (funˡ m)))
                                  (strengthen ρ t (λ m → cov (funʳ m)))
strengthen ρ (mvar X r) cov = mvar X (tabulate (λ k → proj₁ (cov (inMvar {k = k} refl))))

-- Round trip:  [ρ] ([ρ⁻¹] t) = t.
ren-strengthen : ∀ {N} {Θ : MetaCtx N} {Γ m} (ρ : Ren Γ m) (t : Term Θ Γ)
                 (cov : Covered ρ t) → ren ρ (strengthen ρ t cov) ≡ t
ren-strengthen ρ (var i)    cov = cong var (proj₂ (cov here))
ren-strengthen ρ con        cov = refl
ren-strengthen ρ (fun s t)  cov = cong₂ fun (ren-strengthen ρ s _) (ren-strengthen ρ t _)
ren-strengthen ρ (mvar X r) cov =
  cong (mvar X) (ren-ext λ k →
    trans (app-comp ρ (tabulate _) k)
    (trans (cong (app ρ) (lookup∘tabulate _ k))
           (proj₂ (cov (inMvar {k = k} refl)))))

------------------------------------------------------------------------
-- Injectivity of [ρ] when ρ is injective.
--
-- Proven via the strengthening round trip, which avoids the (painful)
-- need to extract injectivity of the indexed `mvar` constructor.

-- Under injectivity, preimages are unique, so strengthening does not
-- depend on the covering proof.
pre-unique : ∀ {n m} {ρ : Ren n m} → Inj ρ → {v : Fin n} (p q : v ∈ʳ ρ) →
             proj₁ p ≡ proj₁ q
pre-unique inj (j , e) (j' , e') = injective inj (trans e (sym e'))

strengthen-cong : ∀ {N} {Θ : MetaCtx N} {Γ m} (ρ : Ren Γ m) → Inj ρ →
                  (t : Term Θ Γ) (cov cov' : Covered ρ t) →
                  strengthen ρ t cov ≡ strengthen ρ t cov'
strengthen-cong ρ inj (var i)    cov cov' = cong var (pre-unique inj (cov here) (cov' here))
strengthen-cong ρ inj con        cov cov' = refl
strengthen-cong ρ inj (fun s t)  cov cov' =
  cong₂ fun (strengthen-cong ρ inj s _ _) (strengthen-cong ρ inj t _ _)
strengthen-cong ρ inj (mvar X r) cov cov' =
  cong (mvar X) (tabulate-cong λ k →
    pre-unique inj (cov (inMvar {k = k} refl)) (cov' (inMvar {k = k} refl)))

strengthen-resp : ∀ {N} {Θ : MetaCtx N} {Γ m} (ρ : Ren Γ m) → Inj ρ →
                  {t t' : Term Θ Γ} → t ≡ t' →
                  (cov : Covered ρ t) (cov' : Covered ρ t') →
                  strengthen ρ t cov ≡ strengthen ρ t' cov'
strengthen-resp ρ inj refl cov cov' = strengthen-cong ρ inj _ cov cov'

-- Strengthening a renamed term gives the original term back.
strengthen-ren : ∀ {N} {Θ : MetaCtx N} {Γ m} {ρ : Ren Γ m} → Inj ρ →
                 (u : Term Θ m) (cov : Covered ρ (ren ρ u)) →
                 strengthen ρ (ren ρ u) cov ≡ u
strengthen-ren {ρ = ρ} inj (var j)    cov = cong var (injective inj (proj₂ (cov here)))
strengthen-ren         inj con        cov = refl
strengthen-ren         inj (fun s t)  cov = cong₂ fun (strengthen-ren inj s _) (strengthen-ren inj t _)
strengthen-ren {ρ = ρ} inj (mvar X r) cov =
  cong (mvar X)
    (trans (tabulate-cong λ k →
              injective inj (trans (proj₂ (cov (inMvar {k = k} refl))) (app-comp ρ r k)))
           (tabulate∘lookup r))

-- [ρ] is injective when ρ is.
ren-inj : ∀ {N} {Θ : MetaCtx N} {Γ Δ} {ρ : Ren Δ Γ} → Inj ρ →
          {u v : Term Θ Γ} → ren ρ u ≡ ren ρ v → u ≡ v
ren-inj {ρ = ρ} inj {u} {v} e =
  trans (sym (strengthen-ren inj u (covered-ren ρ u)))
        (trans (strengthen-resp ρ inj e (covered-ren ρ u) (covered-ren ρ v))
               (strengthen-ren inj v (covered-ren ρ v)))

------------------------------------------------------------------------
-- Injectivity of the term constructors.

var-inj : ∀ {N} {Θ : MetaCtx N} {Γ} {a b : Fin Γ} → var {Θ = Θ} a ≡ var b → a ≡ b
var-inj e = just-injective (cong f e)
  where f : Term _ _ → Maybe (Fin _)
        f (var i) = just i
        f _       = nothing

funˡ-inj : ∀ {N} {Θ : MetaCtx N} {Γ} {a b c d : Term Θ Γ} → fun a b ≡ fun c d → a ≡ c
funˡ-inj e = cong f e
  where f : Term _ _ → Term _ _
        f (fun s _) = s
        f _         = con

funʳ-inj : ∀ {N} {Θ : MetaCtx N} {Γ} {a b c d : Term Θ Γ} → fun a b ≡ fun c d → b ≡ d
funʳ-inj e = cong f e
  where f : Term _ _ → Term _ _
        f (fun _ t) = t
        f _         = con

private
  getR : ∀ {N} {Γ} (Θ : MetaCtx N) (X : Fin N) → Term Θ Γ → Maybe (Ren Γ (lookup Θ X))
  getR Θ X (var i)    = nothing
  getR Θ X con        = nothing
  getR Θ X (fun s t)  = nothing
  getR Θ X (mvar Y s) with X ≟ Y
  ... | yes refl = just s
  ... | no  _    = nothing

  getR-X : ∀ {N} {Γ} (Θ : MetaCtx N) (X : Fin N) (r : Ren Γ (lookup Θ X)) →
           getR Θ X (mvar X r) ≡ just r
  getR-X Θ X r with X ≟ X
  ... | yes refl = refl
  ... | no  ¬p   = ⊥-elim (¬p refl)

mvar-inj : ∀ {N} {Θ : MetaCtx N} {Γ} {X} {r₁ r₂ : Ren Γ (lookup Θ X)} →
           mvar X r₁ ≡ mvar X r₂ → r₁ ≡ r₂
mvar-inj {Θ = Θ} {X = X} {r₁} {r₂} e =
  just-injective (trans (sym (getR-X Θ X r₁)) (trans (cong (getR Θ X) e) (getR-X Θ X r₂)))

------------------------------------------------------------------------
-- Free-variable functoriality, and agreement of renamings on free vars.

-- Renaming maps a free variable i of t to the free variable (app ρ i) of [ρ]t.
fv-ren : ∀ {N} {Θ : MetaCtx N} {Γ Δ} (ρ : Ren Δ Γ) (t : Term Θ Γ) {i : Fin Γ} →
         i ∈fv t → app ρ i ∈fv ren ρ t
fv-ren ρ (var i)    here              = here
fv-ren ρ (fun s t)  (funˡ m)          = funˡ (fv-ren ρ s m)
fv-ren ρ (fun s t)  (funʳ m)          = funʳ (fv-ren ρ t m)
fv-ren ρ (mvar X r) (inMvar {k = k} refl) = inMvar {k = k} (app-comp ρ r k)

-- If [ρ₁]u = [ρ₂]u then ρ₁ and ρ₂ agree on every free variable of u.
ren-fv-agree : ∀ {N} {Θ : MetaCtx N} {n a} (ρ₁ ρ₂ : Ren n a) (u : Term Θ a) {i : Fin a} →
               ren ρ₁ u ≡ ren ρ₂ u → i ∈fv u → app ρ₁ i ≡ app ρ₂ i
ren-fv-agree ρ₁ ρ₂ (var j)    eq here       = var-inj eq
ren-fv-agree ρ₁ ρ₂ (fun s t)  eq (funˡ m)   = ren-fv-agree ρ₁ ρ₂ s (funˡ-inj eq) m
ren-fv-agree ρ₁ ρ₂ (fun s t)  eq (funʳ m)   = ren-fv-agree ρ₁ ρ₂ t (funʳ-inj eq) m
ren-fv-agree ρ₁ ρ₂ (mvar X r) eq (inMvar {k = k} refl) =
  trans (sym (app-comp ρ₁ r k)) (trans (cong (λ ρ → app ρ k) (mvar-inj eq)) (app-comp ρ₂ r k))
