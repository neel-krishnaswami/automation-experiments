------------------------------------------------------------------------
-- Pushouts and coequalizers of renamings.
--
-- We define them inductively (matching paper §7/§8), then construct
-- the record presentation `Pushout` / `Coequalizer` exposing typing,
-- equation, and universal property.  The unification algorithm and
-- main theorem consume these records.
------------------------------------------------------------------------

{-# OPTIONS #-}

module PushoutCoequalizer where

open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl)

open import Base
open import Renaming

------------------------------------------------------------------------
-- The "find an entry with a given output" relation ρ|y.
--
-- ρ|y ≡ ρ', y/x means: ρ has an entry y/x (output y, input x), and
-- ρ' is ρ with that entry removed.
--
-- The variant `ρ|y ≡ ⊥` means: y is not in range(ρ).
------------------------------------------------------------------------

data _∣_≡_ : Ren → Name → (Ren × Name) → Set where
  find-hit  : ∀ {ρ y x}                                  → ((y , x) ∷ ρ) ∣ y ≡ (ρ , x)
  find-miss : ∀ {ρ y z x ρ' a} → y ≢ z → ρ ∣ y ≡ (ρ' , a)
              → ((z , x) ∷ ρ) ∣ y ≡ ((z , x) ∷ ρ' , a)

data _∣_≡⊥ : Ren → Name → Set where
  find⊥-nil  : ∀ {y}                            → [] ∣ y ≡⊥
  find⊥-cons : ∀ {ρ y z x} → y ≢ z → ρ ∣ y ≡⊥   → ((z , x) ∷ ρ) ∣ y ≡⊥

------------------------------------------------------------------------
-- Inductive pushout: Γ ⊢ ρ₁ ⊔ ρ₂ = i₁; i₂ : Γ₃
-- (At the list level; the Ctx-level record wraps lists and the
-- distinctness invariant comes from the renaming wf judgments.)
------------------------------------------------------------------------

data PushoutI : List Name → Ren → Ren → Ren → Ren → List Name → Set where
  push-nil-l :
    ∀ {Γ ρ₂}
    → PushoutI Γ [] ρ₂ [] [] []
  push-nil-r :
    ∀ {Γ ρ₁}
    → PushoutI Γ ρ₁ [] [] [] []
  push-cons-var :
    ∀ {Γ ρ₁ ρ₂ ρ₂' i₁ i₂ Γ' y x z}
    → ρ₂ ∣ y ≡ (ρ₂' , z)
    → PushoutI Γ ρ₁ ρ₂' i₁ i₂ Γ'
    → PushoutI Γ ((y , x) ∷ ρ₁) ρ₂ ((x , y) ∷ i₁) ((z , y) ∷ i₂) (y ∷ Γ')
  push-cons-skip :
    ∀ {Γ ρ₁ ρ₂ p₁ p₂ Γ' y x}
    → ρ₂ ∣ y ≡⊥
    → PushoutI Γ ρ₁ ρ₂ p₁ p₂ Γ'
    → PushoutI Γ ((y , x) ∷ ρ₁) ρ₂ p₁ p₂ Γ'

------------------------------------------------------------------------
-- Inductive coequalizer: Γ ⊢ ρ₁ • ρ₂ = i : Γ'
------------------------------------------------------------------------

data CoequalizerI : List Name → Ren → Ren → Ren → List Name → Set where
  coeq-nil :
    ∀ {Γ}
    → CoequalizerI Γ [] [] [] []
  coeq-cons-ok :
    ∀ {Γ ρ₁ ρ₂ i Γ' y x}
    → CoequalizerI Γ ρ₁ ρ₂ i Γ'
    → CoequalizerI Γ ((y , x) ∷ ρ₁) ((y , x) ∷ ρ₂) ((x , y) ∷ i) (y ∷ Γ')
  coeq-cons-skip :
    ∀ {Γ ρ₁ ρ₂ i Γ' y z x}
    → y ≢ z
    → CoequalizerI Γ ρ₁ ρ₂ i Γ'
    → CoequalizerI Γ ((y , x) ∷ ρ₁) ((z , x) ∷ ρ₂) i Γ'

------------------------------------------------------------------------
-- The record presentations of pushout / coequalizer used downstream.
------------------------------------------------------------------------

record Pushout (Γ : Ctx) (ρ₁ ρ₂ : Ren) (Γ₁ Γ₂ : Ctx) : Set where
  field
    Γ₃        : Ctx
    i₁        : Ren
    i₂        : Ren
    wf-i₁     : Γ₁ ⊢ i₁ ∶ Γ₃
    wf-i₂     : Γ₂ ⊢ i₂ ∶ Γ₃
    eq        : (ρ₁ ⨾ i₁) ≡ (ρ₂ ⨾ i₂)
    universal :
      ∀ {Δ q₁ q₂} → Γ₁ ⊢ q₁ ∶ Δ → Γ₂ ⊢ q₂ ∶ Δ →
      (ρ₁ ⨾ q₁) ≡ (ρ₂ ⨾ q₂) →
      ∃[ q' ] ((Γ₃ ⊢ q' ∶ Δ) × (q₁ ≡ (i₁ ⨾ q')) × (q₂ ≡ (i₂ ⨾ q')))

record Coequalizer (Γ : Ctx) (ρ₁ ρ₂ : Ren) (Γ' : Ctx) : Set where
  field
    Γ''       : Ctx
    i         : Ren
    wf-i      : Γ' ⊢ i ∶ Γ''
    eq        : (ρ₁ ⨾ i) ≡ (ρ₂ ⨾ i)
    universal :
      ∀ {Δ j} → Γ' ⊢ j ∶ Δ → (ρ₁ ⨾ j) ≡ (ρ₂ ⨾ j) →
      ∃[ j' ] ((Γ'' ⊢ j' ∶ Δ) × (j ≡ (i ⨾ j')))

------------------------------------------------------------------------
-- Existence: pushouts and coequalizers exist for compatible renamings.
--
-- The constructive existence proofs (the algorithm) and the proofs of
-- the typing/equation/universal properties form §7.1–§7.3 and
-- §8.1–§8.3.  Those proofs require Aux 2.3a, Aux 2.3b, codomain
-- reweakening, and detailed range characterizations; we expose them
-- here as postulates with the full structure of the deliverables.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Concrete constructions
------------------------------------------------------------------------

open import Data.Nat.Properties using (_≟_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Product using (Σ; Σ-syntax)
open import Relation.Binary.PropositionalEquality
  using (sym; trans; cong; subst)

-- Filter a list of names to those where ρ₁ and ρ₂ agree under look.
filter-agreedᴸ : Ren → Ren → List Name → List Name
filter-agreedᴸ ρ₁ ρ₂ [] = []
filter-agreedᴸ ρ₁ ρ₂ (x ∷ xs) with look ρ₁ x ≟ look ρ₂ x
... | yes _ = x ∷ filter-agreedᴸ ρ₁ ρ₂ xs
... | no  _ = filter-agreedᴸ ρ₁ ρ₂ xs

-- Filter preserves distinctness.
filter-agreed-distinct :
  ∀ {ρ₁ ρ₂ xs} → Distinct xs → Distinct (filter-agreedᴸ ρ₁ ρ₂ xs)
filter-agreed-distinct {xs = []} d-nil = d-nil
filter-agreed-distinct {ρ₁} {ρ₂} {x ∷ xs} (d-cons x∉xs d)
  with look ρ₁ x ≟ look ρ₂ x
... | yes _ = d-cons (filter-preserves-∉ x∉xs) (filter-agreed-distinct d)
    where
      filter-preserves-∉ :
        ∀ {y} → y ∉ᴸ xs → y ∉ᴸ filter-agreedᴸ ρ₁ ρ₂ xs
      filter-preserves-∉ {y} y∉ m = y∉ (filter-mem-back m)
        where
          filter-mem-back :
            ∀ {zs} → y ∈ᴸ filter-agreedᴸ ρ₁ ρ₂ zs → y ∈ᴸ zs
          filter-mem-back {[]} ()
          filter-mem-back {z ∷ zs} m'
            with look ρ₁ z ≟ look ρ₂ z
          ... | yes _ with m'
          ... | hereᴸ = hereᴸ
          ... | thereᴸ m'' = thereᴸ (filter-mem-back m'')
          filter-mem-back {z ∷ zs} m' | no _ = thereᴸ (filter-mem-back m')
... | no _ = filter-agreed-distinct d

-- Identity-like renaming i = (x₁, x₁) ∷ (x₂, x₂) ∷ ... for a list of
-- names.  Uses fresh-in-tail to discharge the wfl-cons fresh premise.
make-emb-renᴸ : List Name → Ren
make-emb-renᴸ []        = []
make-emb-renᴸ (x ∷ xs)  = (x , x) ∷ make-emb-renᴸ xs

-- Phase 2 (plan): range of the embedding equals its input list.
range-emb-eq : ∀ xs → range (make-emb-renᴸ xs) ≡ xs
range-emb-eq []       = refl
range-emb-eq (x ∷ xs) = cong (x ∷_) (range-emb-eq xs)

------------------------------------------------------------------------
-- Phase 3 (plan): list intersection machinery.
------------------------------------------------------------------------

-- Decidable membership in a list of names.
_∈ᴸ?_ : (a : Name) (xs : List Name) → Dec (a ∈ᴸ xs)
a ∈ᴸ? [] = no λ ()
a ∈ᴸ? (x ∷ xs) with a ≟ x
... | yes refl = yes hereᴸ
... | no  a≢x  with a ∈ᴸ? xs
...   | yes m    = yes (thereᴸ m)
...   | no  a∉xs = no λ where
                       hereᴸ      → a≢x refl
                       (thereᴸ m) → a∉xs m

-- list-intersect: keep elements of xs that also appear in ys.
list-intersectᴸ : List Name → List Name → List Name
list-intersectᴸ []       _  = []
list-intersectᴸ (x ∷ xs) ys with x ∈ᴸ? ys
... | yes _ = x ∷ list-intersectᴸ xs ys
... | no  _ = list-intersectᴸ xs ys

-- Membership: in intersection ⇔ in both.
list-intersect-mem-back :
  ∀ {xs ys z} → z ∈ᴸ list-intersectᴸ xs ys → (z ∈ᴸ xs) × (z ∈ᴸ ys)
list-intersect-mem-back {[]} ()
list-intersect-mem-back {x ∷ xs} {ys} {z} m with x ∈ᴸ? ys
... | yes x∈ys with m
... | hereᴸ      = hereᴸ , x∈ys
... | thereᴸ m'  =
        let z∈xs , z∈ys = list-intersect-mem-back m'
        in thereᴸ z∈xs , z∈ys
list-intersect-mem-back {x ∷ xs} {ys} {z} m | no  _ =
  let z∈xs , z∈ys = list-intersect-mem-back m
  in thereᴸ z∈xs , z∈ys

list-intersect-mem-forward :
  ∀ {xs ys z} → z ∈ᴸ xs → z ∈ᴸ ys → z ∈ᴸ list-intersectᴸ xs ys
list-intersect-mem-forward {x ∷ xs} {ys} {.x} hereᴸ z∈ys with x ∈ᴸ? ys
... | yes _   = hereᴸ
... | no  x∉  = ⊥-elim (x∉ z∈ys)
list-intersect-mem-forward {x ∷ xs} {ys} (thereᴸ m) z∈ys with x ∈ᴸ? ys
... | yes _ = thereᴸ (list-intersect-mem-forward m z∈ys)
... | no  _ = list-intersect-mem-forward m z∈ys

-- Distinctness preserved.
list-intersect-distinct :
  ∀ {xs ys} → Distinct xs → Distinct (list-intersectᴸ xs ys)
list-intersect-distinct {xs = []} _ = d-nil
list-intersect-distinct {xs = x ∷ xs} {ys = ys} (d-cons x∉xs d)
  with x ∈ᴸ? ys
... | yes _ = d-cons (λ m → x∉xs (proj₁ (list-intersect-mem-back m)))
                      (list-intersect-distinct d)
... | no  _ = list-intersect-distinct d

-- Intersection is a sublist of its first argument.
list-intersect-⊆ᴸ :
  ∀ {xs ys} → list-intersectᴸ xs ys ⊆ᴸ xs
list-intersect-⊆ᴸ {[]} = ⊆-nil
list-intersect-⊆ᴸ {x ∷ xs} {ys} with x ∈ᴸ? ys
... | yes _ = ⊆-cons (list-intersect-⊆ᴸ {xs} {ys})
... | no  _ = ⊆-skip (list-intersect-⊆ᴸ {xs} {ys})

-- Filtered list is a sublist of the original.
filter-⊆ᴸ :
  ∀ {ρ₁ ρ₂ xs} → filter-agreedᴸ ρ₁ ρ₂ xs ⊆ᴸ xs
filter-⊆ᴸ {xs = []} = ⊆-nil
filter-⊆ᴸ {ρ₁} {ρ₂} {x ∷ xs}
  with look ρ₁ x ≟ look ρ₂ x
... | yes _ = ⊆-cons (filter-⊆ᴸ {ρ₁} {ρ₂})
... | no  _ = ⊆-skip (filter-⊆ᴸ {ρ₁} {ρ₂})

-- Aux: removing an element from a list preserves not-in-list.
rem-preserves-∉ᴸ :
  ∀ {a b xs ys} → b ∉ᴸ xs → xs -ᴸ a ≡ ys → b ∉ᴸ ys
rem-preserves-∉ᴸ ne rem-hereᴸ m = ne (thereᴸ m)
rem-preserves-∉ᴸ ne (rem-thereᴸ _ rem) hereᴸ = ne hereᴸ
rem-preserves-∉ᴸ ne (rem-thereᴸ _ rem) (thereᴸ m) =
  rem-preserves-∉ᴸ (λ m₀ → ne (thereᴸ m₀)) rem m

cons-fst-eq-pc :
  ∀ {a b : Name} {x : Name} {ρ ρ' : Ren}
  → ((a , x) ∷ ρ) ≡ ((b , x) ∷ ρ') → a ≡ b
cons-fst-eq-pc refl = refl

cons-tail-eq-pc :
  ∀ {a b : Name} {x : Name} {ρ ρ' : Ren}
  → ((a , x) ∷ ρ) ≡ ((b , x) ∷ ρ') → ρ ≡ ρ'
cons-tail-eq-pc refl = refl

-- Aux: removal from a Distinct list leaves the removed element absent.
rem-removes-distinct :
  ∀ {xs ys a} → Distinct xs → xs -ᴸ a ≡ ys → a ∉ᴸ ys
rem-removes-distinct (d-cons a∉ _) rem-hereᴸ = a∉
rem-removes-distinct (d-cons a∉ d-xs) (rem-thereᴸ ne rem) hereᴸ = ne refl
rem-removes-distinct (d-cons _ d-xs) (rem-thereᴸ _ rem) (thereᴸ m) =
  rem-removes-distinct d-xs rem m

-- Embedding renaming is well-typed: list xs ⊆ ys, with xs distinct, gives
-- ys ⊢ make-emb-renᴸ xs ∶ xs.
make-emb-ren-wfᴸ :
  ∀ {xs ys}
  → (∀ {z} → z ∈ᴸ xs → z ∈ᴸ ys)
  → Distinct xs
  → ys ⊢ᴸ make-emb-renᴸ xs ∶ xs
make-emb-ren-wfᴸ {[]}     _   _ = wfl-nil
make-emb-ren-wfᴸ {x ∷ xs} {ys} embed (d-cons x∉xs d-xs) =
  let x∈ys = embed hereᴸ
      ys-rem , rem-eq = ∈→remᴸ x∈ys
      embed' : ∀ {z} → z ∈ᴸ xs → z ∈ᴸ ys-rem
      embed' {z} m =
        let z∈ys = embed (thereᴸ m)
            z≢x : z ≢ x
            z≢x z≡x = x∉xs (subst (_∈ᴸ xs) z≡x m)
        in rem-pushes-memᴸ rem-eq z∈ys z≢x
      ih = make-emb-ren-wfᴸ {xs} {ys-rem} embed' d-xs
  in wfl-cons rem-eq ih x∉xs

-- Aux: look in make-emb-ren is the identity on its domain.
make-emb-ren-look :
  ∀ {xs z} → z ∈ᴸ xs → make-emb-renᴸ xs ! z ≡ just z
make-emb-ren-look {x ∷ xs} {z} hereᴸ with z ≟ z
... | yes _ = refl
... | no  ne = ⊥-elim (ne refl)
make-emb-ren-look {x ∷ xs} {z} (thereᴸ m) with z ≟ x
... | yes refl = refl
... | no  _    = make-emb-ren-look m

-- look of the embedding is the identity on its domain.
make-emb-ren-look-eq :
  ∀ {xs z} → z ∈ᴸ xs → look (make-emb-renᴸ xs) z ≡ z
make-emb-ren-look-eq {xs} {z} m
  with make-emb-renᴸ xs ! z | make-emb-ren-look {xs} {z} m
... | just .z | refl = refl

-- A simple lookup-from-just for renamings: if ρ ! a = just b, look ρ a = b.
look-from-just' : ∀ {ρ a b} → ρ ! a ≡ just b → look ρ a ≡ b
look-from-just' {ρ} {a} {b} eq with ρ ! a | eq
... | .(just b) | refl = refl

-- Helper from Renaming.lookup-cons-≢.
lookup-cons-≢-here :
  ∀ {a x z ρ} → z ≢ x → ((a , x) ∷ ρ) ! z ≡ ρ ! z
lookup-cons-≢-here {a} {x} {z} {ρ} ne with z ≟ x
... | yes z≡x = ⊥-elim (ne z≡x)
... | no  _   = refl

-- Lookup of a name not in the filter (look ρ₁ x ≠ look ρ₂ x case).
filter-skipped-look :
  ∀ {ρ₁ ρ₂ xs x z}
  → look ρ₁ x ≢ look ρ₂ x  -- skipped at x
  → z ∈ᴸ filter-agreedᴸ ρ₁ ρ₂ xs
  → z ≢ x → z ∈ᴸ filter-agreedᴸ ρ₁ ρ₂ xs
filter-skipped-look _ m _ = m

------------------------------------------------------------------------
-- Phase 6 (plan): ρ ⨾ (build-renᴸ (look ρ⁻¹) ts) ≡ make-emb-renᴸ ts.
-- This is the algebraic identity that makes the pushout work.
------------------------------------------------------------------------

comp-with-inv-emb :
  ∀ {xs xs' ρ} (ts : List Name)
  → Distinct xs → xs ⊢ᴸ ρ ∶ xs'
  → (∀ {z} → z ∈ᴸ ts → z ∈ᴸ range ρ)
  → ρ ⨾ build-renᴸ (look (ρ ⁻¹)) ts ≡ make-emb-renᴸ ts
comp-with-inv-emb [] _ _ _ = refl
comp-with-inv-emb {ρ = ρ} (t ∷ ts-rest) d D embed =
  let -- ρ⁻¹ is well-typed: list Γ_target ⊢ᴸ ρ⁻¹ ∶ range ρ.
      ρ⁻¹-wf = ren-inv-wfᴸ d D
      -- t ∈ range ρ so ρ⁻¹ ! t is defined.
      t∈range = embed hereᴸ
      ρ⁻¹!t-def = ren-lookup-definedᴸ ρ⁻¹-wf t∈range
      b         = proj₁ ρ⁻¹!t-def
      ρ⁻¹!t-eq  = proj₂ ρ⁻¹!t-def
      -- look ρ⁻¹ t = b.
      look-eq : look (ρ ⁻¹) t ≡ b
      look-eq = look-from-just {ρ ⁻¹} {t} {b} ρ⁻¹!t-eq
      -- By inv-of-inv: ρ ! b = just t.
      ρ!b-eq : ρ ! b ≡ just t
      ρ!b-eq = inv-of-inv-look-from-look d D ρ⁻¹!t-eq
      -- Compute one step of ρ ⨾ build-renᴸ:
      -- build-renᴸ (look ρ⁻¹) (t ∷ ts-rest) = (look ρ⁻¹ t, t) ∷ build-renᴸ (look ρ⁻¹) ts-rest
      -- so ρ ⨾ ((look ρ⁻¹ t, t) ∷ rest) = ?
      -- We need ρ ! (look ρ⁻¹ t).  Since look ρ⁻¹ t = b and ρ ! b = just t:
      ρ!⟨lookρ⁻¹t⟩-eq : ρ ! (look (ρ ⁻¹) t) ≡ just t
      ρ!⟨lookρ⁻¹t⟩-eq = trans (cong (ρ !_) look-eq) ρ!b-eq
      step : ρ ⨾ ((look (ρ ⁻¹) t , t) ∷ build-renᴸ (look (ρ ⁻¹)) ts-rest)
           ≡ (t , t) ∷ (ρ ⨾ build-renᴸ (look (ρ ⁻¹)) ts-rest)
      step = ⨾-cons-head-step
               {ρ} {look (ρ ⁻¹) t} {t} {build-renᴸ (look (ρ ⁻¹)) ts-rest} {t}
               ρ!⟨lookρ⁻¹t⟩-eq
      ih = comp-with-inv-emb ts-rest d D (λ m → embed (thereᴸ m))
  in trans step (cong ((t , t) ∷_) ih)

------------------------------------------------------------------------
-- Aux for the coequalizer: extracting/inserting from the agreement filter.
------------------------------------------------------------------------

-- If z is in the filter, then ρ₁ and ρ₂ agree on z under `look`.
filter-agreed-spec :
  ∀ {ρ₁ ρ₂ xs z} → z ∈ᴸ filter-agreedᴸ ρ₁ ρ₂ xs → look ρ₁ z ≡ look ρ₂ z
filter-agreed-spec {ρ₁} {ρ₂} {[]} ()
filter-agreed-spec {ρ₁} {ρ₂} {x ∷ xs} m with look ρ₁ x ≟ look ρ₂ x
... | yes eq with m
... | hereᴸ      = eq
... | thereᴸ m'  = filter-agreed-spec {ρ₁} {ρ₂} {xs} m'
filter-agreed-spec {ρ₁} {ρ₂} {x ∷ xs} m | no _ = filter-agreed-spec {ρ₁} {ρ₂} {xs} m

-- Given agreement on z, z lives in the filter.
filter-mem-from-agreement :
  ∀ {ρ₁ ρ₂ xs z}
  → look ρ₁ z ≡ look ρ₂ z → z ∈ᴸ xs
  → z ∈ᴸ filter-agreedᴸ ρ₁ ρ₂ xs
filter-mem-from-agreement {ρ₁} {ρ₂} {x ∷ xs} {.x} agree hereᴸ
  with look ρ₁ x ≟ look ρ₂ x
... | yes _    = hereᴸ
... | no  ne   = ⊥-elim (ne agree)
filter-mem-from-agreement {ρ₁} {ρ₂} {x ∷ xs} agree (thereᴸ m)
  with look ρ₁ x ≟ look ρ₂ x
... | yes _ = thereᴸ (filter-mem-from-agreement {ρ₁} {ρ₂} {xs} agree m)
... | no  _ = filter-mem-from-agreement {ρ₁} {ρ₂} {xs} agree m

------------------------------------------------------------------------
-- Phase 7 (plan): coequalizer construction.
------------------------------------------------------------------------

coequalizer :
  ∀ {Γ ρ₁ ρ₂ Γ'}
  → Γ ⊢ ρ₁ ∶ Γ' → Γ ⊢ ρ₂ ∶ Γ'
  → Coequalizer Γ ρ₁ ρ₂ Γ'
coequalizer {Γ = Γ} {ρ₁ = ρ₁} {ρ₂ = ρ₂} {Γ' = Γ'} D₁ D₂ =
  record
    { Γ''       = Γ''-ctx
    ; i         = i
    ; wf-i      = wf-i
    ; eq        = coeq-eq
    ; universal = λ {Δ} {j} wf-j eq-j → coeq-universal {Δ} {j} wf-j eq-j
    }
  where
    Γ''-list : List Name
    Γ''-list = filter-agreedᴸ ρ₁ ρ₂ (list Γ')

    Γ''-distinct : Distinct Γ''-list
    Γ''-distinct = filter-agreed-distinct (nd Γ')

    Γ''-ctx : Ctx
    Γ''-ctx = mkCtx Γ''-list Γ''-distinct

    Γ''⊆Γ' : ∀ {z} → z ∈ᴸ Γ''-list → z ∈ᴸ list Γ'
    Γ''⊆Γ' = ⊆ᴸ-mono-∈ (filter-⊆ᴸ {ρ₁} {ρ₂})

    i : Ren
    i = make-emb-renᴸ Γ''-list

    wf-i : list Γ' ⊢ᴸ i ∶ Γ''-list
    wf-i = make-emb-ren-wfᴸ Γ''⊆Γ' Γ''-distinct

    -- coeq-eq: ρ₁ ⨾ i ≡ ρ₂ ⨾ i.
    coeq-eq : (ρ₁ ⨾ i) ≡ (ρ₂ ⨾ i)
    coeq-eq = ⨾-cong-lookup {ρ₁} {ρ₂} {i}
              λ z z∈range-i →
        let z∈Γ''-list : z ∈ᴸ Γ''-list
            z∈Γ''-list = subst (z ∈ᴸ_) (range-emb-eq Γ''-list) z∈range-i
            z∈listΓ' = Γ''⊆Γ' z∈Γ''-list
            look-agree = filter-agreed-spec {ρ₁} {ρ₂} {list Γ'} z∈Γ''-list
            ρ₁!z-def = ren-lookup-definedᴸ D₁ z∈listΓ'
            b₁ = proj₁ ρ₁!z-def
            ρ₁!z-eq = proj₂ ρ₁!z-def
            ρ₂!z-def = ren-lookup-definedᴸ D₂ z∈listΓ'
            b₂ = proj₁ ρ₂!z-def
            ρ₂!z-eq = proj₂ ρ₂!z-def
            look-ρ₁ = look-from-just {ρ₁} {z} {b₁} ρ₁!z-eq
            look-ρ₂ = look-from-just {ρ₂} {z} {b₂} ρ₂!z-eq
            b₁≡b₂ : b₁ ≡ b₂
            b₁≡b₂ = trans (sym look-ρ₁) (trans look-agree look-ρ₂)
        in trans ρ₁!z-eq (trans (cong just b₁≡b₂) (sym ρ₂!z-eq))

    -- For each output of j (where j : list Γ' ⊢ᴸ j ∶ Δ), that output
    -- is in Γ''-list, by extracting the cons-equation from ρ₁⨾j ≡ ρ₂⨾j.
    j-out-in-agreement :
      ∀ {j-ren Δ-list}
      → list Γ' ⊢ᴸ j-ren ∶ Δ-list
      → ρ₁ ⨾ j-ren ≡ ρ₂ ⨾ j-ren
      → ∀ {a} → a ∈ᴸ range j-ren → a ∈ᴸ Γ''-list
    j-out-in-agreement wfl-nil _ ()
    j-out-in-agreement {j-ren = (a , x) ∷ j-rest}
                       (wfl-cons rem D'-j fresh) eq-j hereᴸ =
      let a∈listΓ' = removeᴸ→memberᴸ rem
          ρ₁!a-def = ren-lookup-definedᴸ D₁ a∈listΓ'
          b₁       = proj₁ ρ₁!a-def
          ρ₁!a-eq  = proj₂ ρ₁!a-def
          ρ₂!a-def = ren-lookup-definedᴸ D₂ a∈listΓ'
          b₂       = proj₁ ρ₂!a-def
          ρ₂!a-eq  = proj₂ ρ₂!a-def
          step₁ : ρ₁ ⨾ ((a , x) ∷ j-rest) ≡ (b₁ , x) ∷ (ρ₁ ⨾ j-rest)
          step₁ = ⨾-cons-head-step {ρ₁} {a} {x} {j-rest} {b₁} ρ₁!a-eq
          step₂ : ρ₂ ⨾ ((a , x) ∷ j-rest) ≡ (b₂ , x) ∷ (ρ₂ ⨾ j-rest)
          step₂ = ⨾-cons-head-step {ρ₂} {a} {x} {j-rest} {b₂} ρ₂!a-eq
          cons-eq : (b₁ , x) ∷ (ρ₁ ⨾ j-rest) ≡ (b₂ , x) ∷ (ρ₂ ⨾ j-rest)
          cons-eq = trans (sym step₁) (trans eq-j step₂)
          b₁≡b₂ : b₁ ≡ b₂
          b₁≡b₂ = cons-fst-eq-pc {b₁} {b₂} {x} {ρ₁ ⨾ j-rest} {ρ₂ ⨾ j-rest} cons-eq
          look-agree : look ρ₁ a ≡ look ρ₂ a
          look-agree =
            trans (look-from-just {ρ₁} {a} {b₁} ρ₁!a-eq)
                  (trans b₁≡b₂ (sym (look-from-just {ρ₂} {a} {b₂} ρ₂!a-eq)))
      in filter-mem-from-agreement {ρ₁} {ρ₂} {list Γ'} look-agree a∈listΓ'
    j-out-in-agreement {j-ren = (a , x) ∷ j-rest}
                       (wfl-cons rem D'-j fresh) eq-j (thereᴸ m) =
      let a∈listΓ' = removeᴸ→memberᴸ rem
          ρ₁!a-def = ren-lookup-definedᴸ D₁ a∈listΓ'
          b₁       = proj₁ ρ₁!a-def
          ρ₁!a-eq  = proj₂ ρ₁!a-def
          ρ₂!a-def = ren-lookup-definedᴸ D₂ a∈listΓ'
          b₂       = proj₁ ρ₂!a-def
          ρ₂!a-eq  = proj₂ ρ₂!a-def
          step₁ = ⨾-cons-head-step {ρ₁} {a} {x} {j-rest} {b₁} ρ₁!a-eq
          step₂ = ⨾-cons-head-step {ρ₂} {a} {x} {j-rest} {b₂} ρ₂!a-eq
          cons-eq = trans (sym step₁) (trans eq-j step₂)
          eq-j' : ρ₁ ⨾ j-rest ≡ ρ₂ ⨾ j-rest
          eq-j' = cons-tail-eq-pc {b₁} {b₂} {x}
                                   {ρ₁ ⨾ j-rest} {ρ₂ ⨾ j-rest} cons-eq
          D'-listΓ' = subsume-codomᴸ D'-j (removeᴸ→⊆ᴸ rem)
      in j-out-in-agreement D'-listΓ' eq-j' m

    -- (make-emb-renᴸ Γ''-list) ⨾ j ≡ j when all outputs of j are in Γ''-list.
    emb-comp-id :
      ∀ {j-ren Δ-list}
      → Γ''-list ⊢ᴸ j-ren ∶ Δ-list
      → make-emb-renᴸ Γ''-list ⨾ j-ren ≡ j-ren
    emb-comp-id wfl-nil = refl
    emb-comp-id {j-ren = (a , x) ∷ j-rest} (wfl-cons rem D' fresh) =
      let a∈Γ''-list = removeᴸ→memberᴸ rem
          emb!a-eq = make-emb-ren-look {Γ''-list} {a} a∈Γ''-list
          step : make-emb-renᴸ Γ''-list ⨾ ((a , x) ∷ j-rest)
               ≡ (a , x) ∷ (make-emb-renᴸ Γ''-list ⨾ j-rest)
          step = ⨾-cons-head-step
                   {make-emb-renᴸ Γ''-list} {a} {x} {j-rest} {a} emb!a-eq
          D'-Γ''-list = subsume-codomᴸ D' (removeᴸ→⊆ᴸ rem)
          ih = emb-comp-id D'-Γ''-list
      in trans step (cong ((a , x) ∷_) ih)

    coeq-universal :
      ∀ {Δ : Ctx} {j} → Γ' ⊢ j ∶ Δ → (ρ₁ ⨾ j) ≡ (ρ₂ ⨾ j)
      → ∃[ j' ] ((Γ''-ctx ⊢ j' ∶ Δ) × (j ≡ (i ⨾ j')))
    coeq-universal {Δ} {j} wf-j eq-j =
      let out-in : ∀ {a} → a ∈ᴸ range j → a ∈ᴸ Γ''-list
          out-in = j-out-in-agreement wf-j eq-j
          j-retyped : Γ''-list ⊢ᴸ j ∶ list Δ
          j-retyped = retype-codomᴸ (nd Γ') wf-j out-in
          ij-eq : i ⨾ j ≡ j
          ij-eq = emb-comp-id j-retyped
      in j , j-retyped , sym ij-eq

------------------------------------------------------------------------
-- Phase 8 (plan): pushout construction.
--
-- Γ₃ = list-intersect (range ρ₁) (range ρ₂)
-- i₁ = build-renᴸ (look (ρ₁ ⁻¹)) Γ₃-list
-- i₂ = build-renᴸ (look (ρ₂ ⁻¹)) Γ₃-list
------------------------------------------------------------------------

pushout :
  ∀ {Γ ρ₁ ρ₂ Γ₁ Γ₂}
  → Γ ⊢ ρ₁ ∶ Γ₁ → Γ ⊢ ρ₂ ∶ Γ₂
  → Pushout Γ ρ₁ ρ₂ Γ₁ Γ₂
pushout {Γ = Γ} {ρ₁ = ρ₁} {ρ₂ = ρ₂} {Γ₁ = Γ₁} {Γ₂ = Γ₂} D₁ D₂ =
  record
    { Γ₃        = Γ₃-ctx
    ; i₁        = i₁
    ; i₂        = i₂
    ; wf-i₁     = wf-i₁
    ; wf-i₂     = wf-i₂
    ; eq        = push-eq
    ; universal = λ {Δ} {q₁} {q₂} wf-q₁ wf-q₂ eq-q →
                    push-universal {Δ} {q₁} {q₂} wf-q₁ wf-q₂ eq-q
    }
  where
    Γ₃-list : List Name
    Γ₃-list = list-intersectᴸ (range ρ₁) (range ρ₂)

    Γ₃-distinct : Distinct Γ₃-list
    Γ₃-distinct = list-intersect-distinct (range-distinctᴸ (nd Γ) D₁)

    Γ₃-ctx : Ctx
    Γ₃-ctx = mkCtx Γ₃-list Γ₃-distinct

    Γ₃⊆range-ρ₁ : ∀ {a} → a ∈ᴸ Γ₃-list → a ∈ᴸ range ρ₁
    Γ₃⊆range-ρ₁ m = proj₁ (list-intersect-mem-back {range ρ₁} {range ρ₂} m)

    Γ₃⊆range-ρ₂ : ∀ {a} → a ∈ᴸ Γ₃-list → a ∈ᴸ range ρ₂
    Γ₃⊆range-ρ₂ m = proj₂ (list-intersect-mem-back {range ρ₁} {range ρ₂} m)

    ρ₁⁻¹-wf : list Γ₁ ⊢ᴸ ρ₁ ⁻¹ ∶ range ρ₁
    ρ₁⁻¹-wf = ren-inv-wfᴸ (nd Γ) D₁

    ρ₂⁻¹-wf : list Γ₂ ⊢ᴸ ρ₂ ⁻¹ ∶ range ρ₂
    ρ₂⁻¹-wf = ren-inv-wfᴸ (nd Γ) D₂

    -- look (ρ₁⁻¹) maps Γ₃-list into list Γ₁.
    look-ρ₁⁻¹-into-Γ₁ : ∀ {z} → z ∈ᴸ Γ₃-list → look (ρ₁ ⁻¹) z ∈ᴸ list Γ₁
    look-ρ₁⁻¹-into-Γ₁ {z} z∈Γ₃ =
      let z∈range-ρ₁ = Γ₃⊆range-ρ₁ z∈Γ₃
          ρ₁⁻¹!z-def = ren-lookup-definedᴸ ρ₁⁻¹-wf z∈range-ρ₁
          b = proj₁ ρ₁⁻¹!z-def
          ρ₁⁻¹!z-eq = proj₂ ρ₁⁻¹!z-def
          look-eq : look (ρ₁ ⁻¹) z ≡ b
          look-eq = look-from-just {ρ₁ ⁻¹} {z} {b} ρ₁⁻¹!z-eq
          b∈Γ₁ = ρ!-output-in-codomain ρ₁⁻¹-wf ρ₁⁻¹!z-eq
      in subst (_∈ᴸ list Γ₁) (sym look-eq) b∈Γ₁

    look-ρ₂⁻¹-into-Γ₂ : ∀ {z} → z ∈ᴸ Γ₃-list → look (ρ₂ ⁻¹) z ∈ᴸ list Γ₂
    look-ρ₂⁻¹-into-Γ₂ {z} z∈Γ₃ =
      let z∈range-ρ₂ = Γ₃⊆range-ρ₂ z∈Γ₃
          ρ₂⁻¹!z-def = ren-lookup-definedᴸ ρ₂⁻¹-wf z∈range-ρ₂
          b = proj₁ ρ₂⁻¹!z-def
          ρ₂⁻¹!z-eq = proj₂ ρ₂⁻¹!z-def
          look-eq : look (ρ₂ ⁻¹) z ≡ b
          look-eq = look-from-just {ρ₂ ⁻¹} {z} {b} ρ₂⁻¹!z-eq
          b∈Γ₂ = ρ!-output-in-codomain ρ₂⁻¹-wf ρ₂⁻¹!z-eq
      in subst (_∈ᴸ list Γ₂) (sym look-eq) b∈Γ₂

    look-ρ⁻¹-inj-ρ₁ : ∀ {z z'} → z ∈ᴸ range ρ₁ → z' ∈ᴸ range ρ₁
      → z ≢ z' → look (ρ₁ ⁻¹) z ≢ look (ρ₁ ⁻¹) z'
    look-ρ⁻¹-inj-ρ₁ {z} {z'} z∈ z'∈ z≢z' look-eq =
      -- look ρ₁⁻¹ z = b, look ρ₁⁻¹ z' = b. By inv-of-inv: ρ₁ ! b = just z and = just z'.
      -- Hence z = z'.
      let ρ₁⁻¹!z-def = ren-lookup-definedᴸ ρ₁⁻¹-wf z∈
          b1 = proj₁ ρ₁⁻¹!z-def
          ρ₁⁻¹!z-eq = proj₂ ρ₁⁻¹!z-def
          ρ₁⁻¹!z'-def = ren-lookup-definedᴸ ρ₁⁻¹-wf z'∈
          b1' = proj₁ ρ₁⁻¹!z'-def
          ρ₁⁻¹!z'-eq = proj₂ ρ₁⁻¹!z'-def
          look-z-b1 : look (ρ₁ ⁻¹) z ≡ b1
          look-z-b1 = look-from-just {ρ₁ ⁻¹} {z} {b1} ρ₁⁻¹!z-eq
          look-z'-b1' : look (ρ₁ ⁻¹) z' ≡ b1'
          look-z'-b1' = look-from-just {ρ₁ ⁻¹} {z'} {b1'} ρ₁⁻¹!z'-eq
          b1≡b1' : b1 ≡ b1'
          b1≡b1' = trans (sym look-z-b1) (trans look-eq look-z'-b1')
          -- ρ₁ ! b1 = just z and ρ₁ ! b1' = just z'. b1 = b1' → ρ₁ ! b1 = just z' too.
          ρ₁!b1-z : ρ₁ ! b1 ≡ just z
          ρ₁!b1-z = inv-of-inv-look-from-look (nd Γ) D₁ ρ₁⁻¹!z-eq
          ρ₁!b1-z' : ρ₁ ! b1 ≡ just z'
          ρ₁!b1-z' = trans (cong (ρ₁ !_) b1≡b1') (inv-of-inv-look-from-look (nd Γ) D₁ ρ₁⁻¹!z'-eq)
          z≡z' : z ≡ z'
          z≡z' = just-injective (trans (sym ρ₁!b1-z) ρ₁!b1-z')
      in z≢z' z≡z'

    look-ρ⁻¹-inj-ρ₂ : ∀ {z z'} → z ∈ᴸ range ρ₂ → z' ∈ᴸ range ρ₂
      → z ≢ z' → look (ρ₂ ⁻¹) z ≢ look (ρ₂ ⁻¹) z'
    look-ρ⁻¹-inj-ρ₂ {z} {z'} z∈ z'∈ z≢z' look-eq =
      let ρ₂⁻¹!z-def = ren-lookup-definedᴸ ρ₂⁻¹-wf z∈
          b1 = proj₁ ρ₂⁻¹!z-def
          ρ₂⁻¹!z-eq = proj₂ ρ₂⁻¹!z-def
          ρ₂⁻¹!z'-def = ren-lookup-definedᴸ ρ₂⁻¹-wf z'∈
          b1' = proj₁ ρ₂⁻¹!z'-def
          ρ₂⁻¹!z'-eq = proj₂ ρ₂⁻¹!z'-def
          look-z-b1 = look-from-just {ρ₂ ⁻¹} {z} {b1} ρ₂⁻¹!z-eq
          look-z'-b1' = look-from-just {ρ₂ ⁻¹} {z'} {b1'} ρ₂⁻¹!z'-eq
          b1≡b1' = trans (sym look-z-b1) (trans look-eq look-z'-b1')
          ρ₂!b1-z = inv-of-inv-look-from-look (nd Γ) D₂ ρ₂⁻¹!z-eq
          ρ₂!b1-z' = trans (cong (ρ₂ !_) b1≡b1') (inv-of-inv-look-from-look (nd Γ) D₂ ρ₂⁻¹!z'-eq)
          z≡z' = just-injective (trans (sym ρ₂!b1-z) ρ₂!b1-z')
      in z≢z' z≡z'

    i₁ : Ren
    i₁ = build-renᴸ (look (ρ₁ ⁻¹)) Γ₃-list

    i₂ : Ren
    i₂ = build-renᴸ (look (ρ₂ ⁻¹)) Γ₃-list

    wf-i₁ : list Γ₁ ⊢ᴸ i₁ ∶ Γ₃-list
    wf-i₁ = build-ren-wfᴸ Γ₃-distinct look-ρ₁⁻¹-into-Γ₁
            (λ z∈ z'∈ z≢z' → look-ρ⁻¹-inj-ρ₁ (Γ₃⊆range-ρ₁ z∈) (Γ₃⊆range-ρ₁ z'∈) z≢z')

    wf-i₂ : list Γ₂ ⊢ᴸ i₂ ∶ Γ₃-list
    wf-i₂ = build-ren-wfᴸ Γ₃-distinct look-ρ₂⁻¹-into-Γ₂
            (λ z∈ z'∈ z≢z' → look-ρ⁻¹-inj-ρ₂ (Γ₃⊆range-ρ₂ z∈) (Γ₃⊆range-ρ₂ z'∈) z≢z')

    push-eq : (ρ₁ ⨾ i₁) ≡ (ρ₂ ⨾ i₂)
    push-eq =
      let lhs : ρ₁ ⨾ i₁ ≡ make-emb-renᴸ Γ₃-list
          lhs = comp-with-inv-emb Γ₃-list (nd Γ) D₁ Γ₃⊆range-ρ₁
          rhs : ρ₂ ⨾ i₂ ≡ make-emb-renᴸ Γ₃-list
          rhs = comp-with-inv-emb Γ₃-list (nd Γ) D₂ Γ₃⊆range-ρ₂
      in trans lhs (sym rhs)

    -- q ≡ build-renᴸ (look (ρ⁻¹)) Γ₃-list ⨾ (ρ ⨾ q) when outputs of (ρ ⨾ q)
    -- all land in Γ₃-list (the precondition needed for the inverse lookup
    -- to be defined at each step).
    q≡inv⨾ρq-aux :
      ∀ {q ρ Γ-cod Γ-dom Δ-list}
      → Distinct Γ-cod → Γ-cod ⊢ᴸ ρ ∶ Γ-dom
      → Γ-dom ⊢ᴸ q ∶ Δ-list
      → (∀ {a} → a ∈ᴸ range (ρ ⨾ q) → a ∈ᴸ Γ₃-list)
      → q ≡ build-renᴸ (look (ρ ⁻¹)) Γ₃-list ⨾ (ρ ⨾ q)
    q≡inv⨾ρq-aux _ _ wfl-nil _ = refl
    q≡inv⨾ρq-aux {q = (b , δ) ∷ q-rest} {ρ = ρ} d-cod D-ρ
                  (wfl-cons rem-q D'-q fresh-q) out-in =
      let b∈Γ-dom = removeᴸ→memberᴸ rem-q
          ρ!b-def = ren-lookup-definedᴸ D-ρ b∈Γ-dom
          c = proj₁ ρ!b-def
          ρ!b-eq = proj₂ ρ!b-def
          look-ρ-b : look ρ b ≡ c
          look-ρ-b = look-from-just {ρ} {b} {c} ρ!b-eq
          step-ρ : ρ ⨾ ((b , δ) ∷ q-rest) ≡ (c , δ) ∷ (ρ ⨾ q-rest)
          step-ρ = ⨾-cons-head-step {ρ} {b} {δ} {q-rest} {c} ρ!b-eq
          range-eq : range (ρ ⨾ ((b , δ) ∷ q-rest)) ≡ c ∷ range (ρ ⨾ q-rest)
          range-eq = cong range step-ρ
          c∈Γ₃ : c ∈ᴸ Γ₃-list
          c∈Γ₃ = out-in (subst (c ∈ᴸ_) (sym range-eq) hereᴸ)
          out-in-rest : ∀ {a} → a ∈ᴸ range (ρ ⨾ q-rest) → a ∈ᴸ Γ₃-list
          out-in-rest {a} a∈ = out-in (subst (a ∈ᴸ_) (sym range-eq) (thereᴸ a∈))
          -- build-renᴸ (look ρ⁻¹) Γ₃-list ! c = just (look ρ⁻¹ c)
          inv-ren = build-renᴸ (look (ρ ⁻¹)) Γ₃-list
          inv-ren!c-eq : inv-ren ! c ≡ just (look (ρ ⁻¹) c)
          inv-ren!c-eq = build-ren-look {look (ρ ⁻¹)} {Γ₃-list} {c} c∈Γ₃
          -- look ρ⁻¹ c = look ρ⁻¹ (look ρ b) = b (by ρ⁻¹-look-of-ρ-look).
          look-inv-c-b : look (ρ ⁻¹) c ≡ b
          look-inv-c-b = trans (cong (look (ρ ⁻¹)) (sym look-ρ-b))
                                (ρ⁻¹-look-of-ρ-look d-cod D-ρ b∈Γ-dom)
          inv-ren!c-b : inv-ren ! c ≡ just b
          inv-ren!c-b = trans inv-ren!c-eq (cong just look-inv-c-b)
          step-inv : inv-ren ⨾ ((c , δ) ∷ (ρ ⨾ q-rest))
                    ≡ (b , δ) ∷ (inv-ren ⨾ (ρ ⨾ q-rest))
          step-inv = ⨾-cons-head-step {inv-ren} {c} {δ} {ρ ⨾ q-rest} {b} inv-ren!c-b
          D'-q-Γ-dom = subsume-codomᴸ D'-q (removeᴸ→⊆ᴸ rem-q)
          ih = q≡inv⨾ρq-aux d-cod D-ρ D'-q-Γ-dom out-in-rest
          goal-step : (b , δ) ∷ q-rest ≡ inv-ren ⨾ ((c , δ) ∷ (ρ ⨾ q-rest))
          goal-step = trans (cong ((b , δ) ∷_) ih) (sym step-inv)
      in trans goal-step (cong (inv-ren ⨾_) (sym step-ρ))

    push-universal :
      ∀ {Δ q₁ q₂} → Γ₁ ⊢ q₁ ∶ Δ → Γ₂ ⊢ q₂ ∶ Δ →
      (ρ₁ ⨾ q₁) ≡ (ρ₂ ⨾ q₂) →
      ∃[ q' ] ((Γ₃-ctx ⊢ q' ∶ Δ)
              × (q₁ ≡ (i₁ ⨾ q'))
              × (q₂ ≡ (i₂ ⨾ q')))
    push-universal {Δ} {q₁} {q₂} wf-q₁ wf-q₂ eq-q =
      let q' = ρ₁ ⨾ q₁
          q'-wf-Γ : list Γ ⊢ᴸ q' ∶ list Δ
          q'-wf-Γ = ren-comp-wfᴸ D₁ wf-q₁ (nd Γ)
          out-in-Γ₃ : ∀ {a} → a ∈ᴸ range q' → a ∈ᴸ Γ₃-list
          out-in-Γ₃ a∈ =
            let a∈range-ρ₁ = comp-output-in-rangeᴸ {ρ₁} {q₁} a∈
                a∈range-ρ₂-q₂ : _ ∈ᴸ range (ρ₂ ⨾ q₂)
                a∈range-ρ₂-q₂ = subst (_ ∈ᴸ_) (cong range eq-q) a∈
                a∈range-ρ₂ = comp-output-in-rangeᴸ {ρ₂} {q₂} a∈range-ρ₂-q₂
            in list-intersect-mem-forward a∈range-ρ₁ a∈range-ρ₂
          q'-wf-Γ₃ : Γ₃-list ⊢ᴸ q' ∶ list Δ
          q'-wf-Γ₃ = retype-codomᴸ (nd Γ) q'-wf-Γ out-in-Γ₃
          q₁≡i₁q' : q₁ ≡ i₁ ⨾ q'
          q₁≡i₁q' = q≡inv⨾ρq-aux (nd Γ) D₁ wf-q₁ out-in-Γ₃
          -- For q₂: precondition is outputs of (ρ₂ ⨾ q₂) in Γ₃-list.
          -- This follows from eq-q and out-in-Γ₃.
          out-in-Γ₃-ρ₂q₂ : ∀ {a} → a ∈ᴸ range (ρ₂ ⨾ q₂) → a ∈ᴸ Γ₃-list
          out-in-Γ₃-ρ₂q₂ a∈ = out-in-Γ₃ (subst (_ ∈ᴸ_) (sym (cong range eq-q)) a∈)
          q₂≡i₂⨾ρ₂q₂ : q₂ ≡ i₂ ⨾ (ρ₂ ⨾ q₂)
          q₂≡i₂⨾ρ₂q₂ = q≡inv⨾ρq-aux (nd Γ) D₂ wf-q₂ out-in-Γ₃-ρ₂q₂
          q₂≡i₂q' : q₂ ≡ i₂ ⨾ q'
          q₂≡i₂q' = trans q₂≡i₂⨾ρ₂q₂ (cong (i₂ ⨾_) (sym eq-q))
      in q' , q'-wf-Γ₃ , q₁≡i₁q' , q₂≡i₂q'
