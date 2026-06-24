{-# OPTIONS --safe #-}

------------------------------------------------------------------------
-- Object-level renamings.
--
-- An object context Γ is represented by its size (a natural number) and
-- an object variable is an element of `Fin Γ`.  A renaming `Γ ⊢ ρ : Γ'`
-- of the specification is a function `Fin Γ' → Fin Γ`; we represent it
-- concretely as a vector `Vec (Fin Γ) Γ'` (the i-th entry is ρ(i)).
------------------------------------------------------------------------

module Renaming where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Vec.Base using (Vec; []; _∷_; lookup; map; tabulate)
open import Data.Vec.Properties
  using (lookup-map; lookup∘tabulate; tabulate-cong; tabulate∘lookup)
open import Function.Base using (id; _∘_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)
open import Data.Product.Base using (Σ; _,_; ∃; ∃-syntax; proj₁; proj₂)

-- A renaming ρ with `Γ ⊢ ρ : Γ'`, i.e. ρ : Fin Γ' → Fin Γ.
Ren : ℕ → ℕ → Set
Ren n m = Vec (Fin n) m

-- Application: app ρ i = ρ(i).
app : ∀ {n m} → Ren n m → Fin m → Fin n
app ρ i = lookup ρ i

-- Identity renaming.
idR : ∀ {n} → Ren n n
idR = tabulate id

app-idR : ∀ {n} (i : Fin n) → app idR i ≡ i
app-idR i = lookup∘tabulate id i

-- Composition: (comp ρ ρ') i = ρ (ρ' i).
comp : ∀ {n m l} → Ren n m → Ren m l → Ren n l
comp ρ ρ' = map (app ρ) ρ'

app-comp : ∀ {n m l} (ρ : Ren n m) (ρ' : Ren m l) (i : Fin l) →
           app (comp ρ ρ') i ≡ app ρ (app ρ' i)
app-comp ρ ρ' i = lookup-map i (app ρ) ρ'

-- Extensionality of renamings: pointwise equality implies equality.
-- (This is funext for the finite domain, and is provable.)
ren-ext : ∀ {n m} {ρ ρ' : Ren n m} → (∀ i → app ρ i ≡ app ρ' i) → ρ ≡ ρ'
ren-ext {ρ = ρ} {ρ'} h =
  trans (sym (tabulate∘lookup ρ)) (trans (tabulate-cong h) (tabulate∘lookup ρ'))

------------------------------------------------------------------------
-- The category laws for renamings (proved pointwise via ren-ext).

comp-idˡ : ∀ {n m} (ρ : Ren n m) → comp idR ρ ≡ ρ
comp-idˡ ρ = ren-ext λ i → trans (app-comp idR ρ i) (app-idR (app ρ i))

comp-idʳ : ∀ {n m} (ρ : Ren n m) → comp ρ idR ≡ ρ
comp-idʳ ρ = ren-ext λ i → trans (app-comp ρ idR i) (cong (app ρ) (app-idR i))

comp-assoc : ∀ {n m l k} (ρ : Ren n m) (σ : Ren m l) (τ : Ren l k) →
             comp (comp ρ σ) τ ≡ comp ρ (comp σ τ)
comp-assoc ρ σ τ = ren-ext λ i →
  trans (app-comp (comp ρ σ) τ i)
  (trans (app-comp ρ σ (app τ i))
  (trans (sym (cong (app ρ) (app-comp σ τ i)))
         (sym (app-comp ρ (comp σ τ) i))))

------------------------------------------------------------------------
-- Injectivity and the range of a renaming.

-- ρ is injective as a function Fin m → Fin n.  We use a record (rather
-- than a plain Π-type) so that `Inj ρ` is a rigid type former from which
-- ρ can be recovered by unification.
record Inj {n m} (ρ : Ren n m) : Set where
  constructor mkInj
  field injective : ∀ {i j} → app ρ i ≡ app ρ j → i ≡ j
open Inj public

idR-inj : ∀ {n} → Inj (idR {n})
idR-inj = mkInj λ {i} {j} e → trans (sym (app-idR i)) (trans e (app-idR j))

comp-inj : ∀ {n m l} {ρ : Ren n m} {σ : Ren m l} → Inj ρ → Inj σ → Inj (comp ρ σ)
comp-inj {ρ = ρ} {σ} iρ iσ = mkInj λ {i} {j} e →
  injective iσ (injective iρ (trans (sym (app-comp ρ σ i)) (trans e (app-comp ρ σ j))))

-- Membership in the range of a renaming: v is hit by ρ.  The witness
-- `proj₁` is the preimage and `proj₂` is the proof that ρ maps it to v.
_∈ʳ_ : ∀ {n m} → Fin n → Ren n m → Set
v ∈ʳ ρ = ∃[ i ] app ρ i ≡ v

-- Membership is preserved by consing a new entry, and shifted by map suc.
∈ʳ-there : ∀ {n s} {x : Fin n} {ρ : Ren n s} {v : Fin n} → v ∈ʳ ρ → v ∈ʳ (x ∷ ρ)
∈ʳ-there (j , e) = suc j , e

∈ʳ-suc : ∀ {a s} (e : Ren a s) {i : Fin a} → i ∈ʳ e → suc i ∈ʳ map suc e
∈ʳ-suc e (j , eq) = j , trans (lookup-map j suc e) (cong suc eq)
