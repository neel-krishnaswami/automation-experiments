------------------------------------------------------------------------
-- Names, contexts (as records carrying duplicate-freeness), variable
-- membership, context removal, and the subcontext relation.
------------------------------------------------------------------------

{-# OPTIONS #-}

module Base where

open import Data.Nat using (ℕ)
open import Data.Nat.Properties using (_≟_)
open import Data.List using (List; []; _∷_)
open import Data.Product
  using (_×_; _,_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; subst)

------------------------------------------------------------------------
-- Names
------------------------------------------------------------------------

Name : Set
Name = ℕ

------------------------------------------------------------------------
-- List-level membership and distinctness (NoDup)
------------------------------------------------------------------------

infix 4 _∈ᴸ_
data _∈ᴸ_ : Name → List Name → Set where
  hereᴸ  : ∀ {x xs}             → x ∈ᴸ (x ∷ xs)
  thereᴸ : ∀ {x y xs} → x ∈ᴸ xs → x ∈ᴸ (y ∷ xs)

infix 4 _∉ᴸ_
_∉ᴸ_ : Name → List Name → Set
x ∉ᴸ xs = ¬ (x ∈ᴸ xs)

data Distinct : List Name → Set where
  d-nil  : Distinct []
  d-cons : ∀ {x xs} → x ∉ᴸ xs → Distinct xs → Distinct (x ∷ xs)

------------------------------------------------------------------------
-- Object contexts: a list with a proof of distinctness.
------------------------------------------------------------------------

record Ctx : Set where
  constructor mkCtx
  field
    list : List Name
    nd   : Distinct list

open Ctx public

[]ᶜ : Ctx
[]ᶜ = mkCtx [] d-nil

-- Smart constructor: extend a context by a fresh name.
extend : (x : Name) (Γ : Ctx) → x ∉ᴸ list Γ → Ctx
extend x Γ fresh = mkCtx (x ∷ list Γ) (d-cons fresh (nd Γ))

------------------------------------------------------------------------
-- Membership in a Ctx (wraps list membership)
------------------------------------------------------------------------

infix 4 _∈_
_∈_ : Name → Ctx → Set
x ∈ Γ = x ∈ᴸ list Γ

------------------------------------------------------------------------
-- Variable removal: Γ₀ - a ≡ Γ₁.  Carries the freshness data of both
-- endpoints automatically through `extend`.
------------------------------------------------------------------------

infix 4 _-_≡_
data _-_≡_ : Ctx → Name → Ctx → Set where
  rem-here  : ∀ {Γ a fresh}
              → extend a Γ fresh - a ≡ Γ
  rem-there : ∀ {Γ Γ' a b fresh fresh'}
              → a ≢ b
              → Γ - a ≡ Γ'
              → extend b Γ fresh - a ≡ extend b Γ' fresh'

-- §1.1
remove→member : ∀ {Γ₀ Γ₁ a} → Γ₀ - a ≡ Γ₁ → a ∈ Γ₀
remove→member rem-here          = hereᴸ
remove→member (rem-there _ rem) = thereᴸ (remove→member rem)

-- Removal preserves non-membership.
remove-preserves-∉ :
  ∀ {Γ Γ' a b} → a ∉ᴸ list Γ → Γ - b ≡ Γ' → a ∉ᴸ list Γ'
remove-preserves-∉ ne rem-here m              = ne (thereᴸ m)
remove-preserves-∉ ne (rem-there _ rem) hereᴸ = ne hereᴸ
remove-preserves-∉ ne (rem-there _ rem) (thereᴸ m) =
  remove-preserves-∉ (λ m₀ → ne (thereᴸ m₀)) rem m

-- Aux 1.2 (membership after removal) — provable with the distinctness
-- carried by the records.
member-after-remove :
  ∀ {Γ₀ Γ₁ a b} → Γ₀ - a ≡ Γ₁ → b ∈ Γ₁ → (b ∈ Γ₀) × (a ≢ b)
member-after-remove (rem-here {fresh = fresh}) m =
  thereᴸ m , λ a≡b → fresh (subst (_∈ᴸ _) (sym a≡b) m)
member-after-remove (rem-there ne rem) hereᴸ =
  hereᴸ , ne
member-after-remove (rem-there ne rem) (thereᴸ m) with member-after-remove rem m
... | m₀ , ne₀ = thereᴸ m₀ , ne₀

-- Aux 1.3 (swap of removals).
swap-remove :
  ∀ {Γ Γ₁ Γ₁₂ a₁ a₂} → Γ - a₁ ≡ Γ₁ → Γ₁ - a₂ ≡ Γ₁₂ → a₁ ≢ a₂ →
  ∃[ Γ₂ ] ((Γ - a₂ ≡ Γ₂) × (Γ₂ - a₁ ≡ Γ₁₂))
swap-remove {Γ₁₂ = Γ₁₂} (rem-here {fresh = fresh}) D₂ ne =
  let fresh' = remove-preserves-∉ fresh D₂ in
  extend _ Γ₁₂ fresh' ,
  rem-there (λ a₂≡a₁ → ne (sym a₂≡a₁)) D₂ ,
  rem-here
swap-remove (rem-there ne₁ D₁') rem-here ne =
  _ , rem-here , D₁'
swap-remove (rem-there {fresh = fresh} ne₁ D₁') (rem-there ne₂ D₂') ne with swap-remove D₁' D₂' ne
... | Γ₂′ , p₁ , p₂ =
  let fresh' = remove-preserves-∉ fresh p₁ in
  extend _ Γ₂′ fresh' , rem-there ne₂ p₁ , rem-there ne₁ p₂

------------------------------------------------------------------------
-- Subcontext (subsequence) relation Γ ⊆ Γ'
------------------------------------------------------------------------

infix 4 _⊆ᴸ_
data _⊆ᴸ_ : List Name → List Name → Set where
  ⊆-nil  : ∀ {xs}                              → [] ⊆ᴸ xs
  ⊆-cons : ∀ {xs ys x}  → xs ⊆ᴸ ys             → (x ∷ xs) ⊆ᴸ (x ∷ ys)
  ⊆-skip : ∀ {xs ys x}  → xs ⊆ᴸ ys             → xs ⊆ᴸ (x ∷ ys)

infix 4 _⊆_
_⊆_ : Ctx → Ctx → Set
Γ ⊆ Γ' = list Γ ⊆ᴸ list Γ'

⊆ᴸ-refl : ∀ {xs} → xs ⊆ᴸ xs
⊆ᴸ-refl {[]}    = ⊆-nil
⊆ᴸ-refl {_ ∷ _} = ⊆-cons ⊆ᴸ-refl

⊆-refl : ∀ {Γ} → Γ ⊆ Γ
⊆-refl = ⊆ᴸ-refl

⊆ᴸ-trans : ∀ {xs ys zs} → xs ⊆ᴸ ys → ys ⊆ᴸ zs → xs ⊆ᴸ zs
⊆ᴸ-trans ⊆-nil       ⊆-nil       = ⊆-nil
⊆ᴸ-trans ⊆-nil       (⊆-cons _)  = ⊆-nil
⊆ᴸ-trans ⊆-nil       (⊆-skip q)  = ⊆-skip (⊆ᴸ-trans ⊆-nil q)
⊆ᴸ-trans (⊆-cons p)  (⊆-cons q)  = ⊆-cons (⊆ᴸ-trans p q)
⊆ᴸ-trans (⊆-cons p)  (⊆-skip q)  = ⊆-skip (⊆ᴸ-trans (⊆-cons p) q)
⊆ᴸ-trans (⊆-skip p)  (⊆-cons q)  = ⊆-skip (⊆ᴸ-trans p q)
⊆ᴸ-trans (⊆-skip p)  (⊆-skip q)  = ⊆-skip (⊆ᴸ-trans (⊆-skip p) q)

⊆-trans : ∀ {Γ₁ Γ₂ Γ₃} → Γ₁ ⊆ Γ₂ → Γ₂ ⊆ Γ₃ → Γ₁ ⊆ Γ₃
⊆-trans = ⊆ᴸ-trans

⊆ᴸ-mono-∈ : ∀ {xs ys x} → xs ⊆ᴸ ys → x ∈ᴸ xs → x ∈ᴸ ys
⊆ᴸ-mono-∈ (⊆-cons s) hereᴸ      = hereᴸ
⊆ᴸ-mono-∈ (⊆-cons s) (thereᴸ m) = thereᴸ (⊆ᴸ-mono-∈ s m)
⊆ᴸ-mono-∈ (⊆-skip s) m          = thereᴸ (⊆ᴸ-mono-∈ s m)

⊆-mono-∈ : ∀ {Γ Γ' x} → Γ ⊆ Γ' → x ∈ Γ → x ∈ Γ'
⊆-mono-∈ = ⊆ᴸ-mono-∈

remove→⊆ : ∀ {Γ₀ Γ₁ a} → Γ₀ - a ≡ Γ₁ → Γ₁ ⊆ Γ₀
remove→⊆ rem-here          = ⊆-skip ⊆ᴸ-refl
remove→⊆ (rem-there _ rem) = ⊆-cons (remove→⊆ rem)
