------------------------------------------------------------------------
-- Renamings ρ, well-formedness, identity, composition, inverse, range.
--
-- We work with list-level well-formedness `xs ⊢ᴸ ρ ∶ᴸ xs'` and lift to
-- `Γ ⊢ ρ ∶ Γ'` for Ctx records via the underlying lists.  Distinctness
-- of the input/output lists is carried by the Ctx records' nd field.
--
-- The list-level rule for cons requires the new input to be fresh in
-- the codomain — this is exactly the "duplicate-freeness convention"
-- of the paper and ensures that the codomain list, built up by the
-- inductive rules, is automatically distinct.
--
-- Convention §0.4: `ρ ⨾ ρ'` = "apply ρ' first, then ρ".
------------------------------------------------------------------------

{-# OPTIONS #-}

module Renaming where

open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁; proj₂)
open import Data.Nat.Properties using (_≟_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Data.Empty using (⊥-elim)

open import Base

------------------------------------------------------------------------
-- Renamings as lists of (output , input) pairs.
------------------------------------------------------------------------

Ren : Set
Ren = List (Name × Name)

infix 5 _!_
_!_ : Ren → Name → Maybe Name
[] ! _ = nothing
((a , x) ∷ ρ) ! z with z ≟ x
... | yes _ = just a
... | no  _ = ρ ! z

------------------------------------------------------------------------
-- List-level well-formedness.  The cons rule requires the input `x` to
-- be fresh in the codomain (matching the paper's convention).
------------------------------------------------------------------------

-- We need a list-level removal relation paralleling Base._-_≡_.
infix 4 _-ᴸ_≡_
data _-ᴸ_≡_ : List Name → Name → List Name → Set where
  rem-hereᴸ  : ∀ {xs a}                          → (a ∷ xs) -ᴸ a ≡ xs
  rem-thereᴸ : ∀ {xs ys a b} → a ≢ b → xs -ᴸ a ≡ ys → (b ∷ xs) -ᴸ a ≡ (b ∷ ys)

-- Bridges between Ctx-level and list-level removal.
ctx-rem→list-rem : ∀ {Γ Γ' a} → Γ - a ≡ Γ' → list Γ -ᴸ a ≡ list Γ'
ctx-rem→list-rem rem-here          = rem-hereᴸ
ctx-rem→list-rem (rem-there ne D)  = rem-thereᴸ ne (ctx-rem→list-rem D)

-- List-level membership / ⊆ already in Base.

infix 4 _⊢ᴸ_∶_
data _⊢ᴸ_∶_ : List Name → Ren → List Name → Set where
  wfl-nil  : ∀ {xs}                                 → xs ⊢ᴸ [] ∶ []
  wfl-cons : ∀ {xs₀ xs₁ xs' ρ a x}
             → xs₀ -ᴸ a ≡ xs₁
             → xs₁ ⊢ᴸ ρ ∶ xs'
             → (fresh : x ∉ᴸ xs')
             → xs₀ ⊢ᴸ ((a , x) ∷ ρ) ∶ (x ∷ xs')

-- Ctx-level wf as a definition.
infix 4 _⊢_∶_
_⊢_∶_ : Ctx → Ren → Ctx → Set
Γ ⊢ ρ ∶ Γ' = list Γ ⊢ᴸ ρ ∶ list Γ'

------------------------------------------------------------------------
-- Standard operations
------------------------------------------------------------------------

id-ren-list : List Name → Ren
id-ren-list []       = []
id-ren-list (x ∷ xs) = (x , x) ∷ id-ren-list xs

id-ren : Ctx → Ren
id-ren Γ = id-ren-list (list Γ)

_⨾_ : Ren → Ren → Ren
ρ ⨾ []             = []
ρ ⨾ ((a , x) ∷ ρ') with ρ ! a
... | just b  = (b , x) ∷ (ρ ⨾ ρ')
... | nothing = ρ ⨾ ρ'

range : Ren → List Name
range []            = []
range ((a , _) ∷ ρ) = a ∷ range ρ

infix 30 _⁻¹
_⁻¹ : Ren → Ren
[] ⁻¹            = []
((a , x) ∷ ρ) ⁻¹ = (x , a) ∷ (ρ ⁻¹)

look : Ren → Name → Name
look ρ a with ρ ! a
... | just b  = b
... | nothing = a

------------------------------------------------------------------------
-- §1.1 at list level
------------------------------------------------------------------------

removeᴸ→memberᴸ : ∀ {xs ys a} → xs -ᴸ a ≡ ys → a ∈ᴸ xs
removeᴸ→memberᴸ rem-hereᴸ          = hereᴸ
removeᴸ→memberᴸ (rem-thereᴸ _ rem) = thereᴸ (removeᴸ→memberᴸ rem)

remove-preserves-∉ᴸ :
  ∀ {xs ys a b} → a ∉ᴸ xs → xs -ᴸ b ≡ ys → a ∉ᴸ ys
remove-preserves-∉ᴸ ne rem-hereᴸ m              = ne (thereᴸ m)
remove-preserves-∉ᴸ ne (rem-thereᴸ _ rem) hereᴸ = ne hereᴸ
remove-preserves-∉ᴸ ne (rem-thereᴸ _ rem) (thereᴸ m) =
  remove-preserves-∉ᴸ (λ m₀ → ne (thereᴸ m₀)) rem m

removeᴸ→⊆ᴸ : ∀ {xs ys a} → xs -ᴸ a ≡ ys → ys ⊆ᴸ xs
removeᴸ→⊆ᴸ rem-hereᴸ          = ⊆-skip ⊆ᴸ-refl
removeᴸ→⊆ᴸ (rem-thereᴸ _ rem) = ⊆-cons (removeᴸ→⊆ᴸ rem)

------------------------------------------------------------------------
-- §2.2 (identity renaming is well-formed)
------------------------------------------------------------------------

id-ren-list-wf : ∀ (xs : List Name) → Distinct xs → xs ⊢ᴸ id-ren-list xs ∶ xs
id-ren-list-wf [] _                  = wfl-nil
id-ren-list-wf (x ∷ xs) (d-cons ne d) = wfl-cons rem-hereᴸ (id-ren-list-wf xs d) ne

id-ren-wf : ∀ {Γ} → Γ ⊢ id-ren Γ ∶ Γ
id-ren-wf {Γ} = id-ren-list-wf (list Γ) (nd Γ)

------------------------------------------------------------------------
-- Aux 2.0b: id-ren lookup
------------------------------------------------------------------------

id-ren-list-lookup :
  ∀ {xs x} → x ∈ᴸ xs → id-ren-list xs ! x ≡ just x
id-ren-list-lookup {x ∷ xs} (hereᴸ {x = x}) with x ≟ x
... | yes _    = refl
... | no  ne   = ⊥-elim (ne refl)
id-ren-list-lookup {y ∷ xs} {x} (thereᴸ m) with x ≟ y
... | yes refl = refl
... | no  _    = id-ren-list-lookup m

id-ren-lookup :
  ∀ {Γ x} → x ∈ Γ → id-ren Γ ! x ≡ just x
id-ren-lookup {Γ} m = id-ren-list-lookup m

id-ren-look :
  ∀ {Γ x} → x ∈ Γ → look (id-ren Γ) x ≡ x
id-ren-look {Γ} {x} m with id-ren Γ ! x | id-ren-lookup {Γ} m
... | just .x | refl = refl
... | nothing | ()

------------------------------------------------------------------------
-- §2.1: ρ lookup lands in Γ for `x ∈ Γ'`.
------------------------------------------------------------------------

ren-output-inᴸ :
  ∀ {xs xs' ρ x} → xs ⊢ᴸ ρ ∶ xs' → x ∈ᴸ xs' → look ρ x ∈ᴸ xs
ren-output-inᴸ (wfl-cons {a = a} {x = y} rem D' _) hereᴸ with y ≟ y
... | yes _   = removeᴸ→memberᴸ rem
... | no  ne  = ⊥-elim (ne refl)
ren-output-inᴸ {x = x} (wfl-cons {a = a} {x = y} rem D' _) (thereᴸ m) with x ≟ y
... | yes refl = removeᴸ→memberᴸ rem
... | no  _    = ⊆ᴸ-mono-∈ (removeᴸ→⊆ᴸ rem) (ren-output-inᴸ D' m)

ren-output-in :
  ∀ {Γ Γ' ρ x} → Γ ⊢ ρ ∶ Γ' → x ∈ Γ' → look ρ x ∈ Γ
ren-output-in = ren-output-inᴸ

------------------------------------------------------------------------
-- Aux 2.5a: left identity for renaming composition, generalized via ⊆ᴸ.
------------------------------------------------------------------------

id-ren-left-id-list :
  ∀ {xs_a xs_b xs' ρ}
  → xs_a ⊆ᴸ xs_b → xs_a ⊢ᴸ ρ ∶ xs' → id-ren-list xs_b ⨾ ρ ≡ ρ
id-ren-left-id-list sub wfl-nil = refl
id-ren-left-id-list {xs_b = xs_b} sub (wfl-cons {a = a} {x = x} rem D' _)
  with id-ren-list xs_b ! a | id-ren-list-lookup {xs_b} (⊆ᴸ-mono-∈ sub (removeᴸ→memberᴸ rem))
... | just .a | refl = cong ((a , x) ∷_) (id-ren-left-id-list (⊆ᴸ-trans (removeᴸ→⊆ᴸ rem) sub) D')
... | nothing | ()

id-ren-left-id-direct :
  ∀ {Γ Γ' ρ} → Γ ⊢ ρ ∶ Γ' → id-ren Γ ⨾ ρ ≡ ρ
id-ren-left-id-direct {Γ} D = id-ren-left-id-list ⊆ᴸ-refl D

------------------------------------------------------------------------
-- Codomain reweakening (Aux 2.7a)
------------------------------------------------------------------------

codom-reweakenᴸ :
  ∀ {xs xs' ρ y} → xs ⊢ᴸ ρ ∶ xs' → y ∉ᴸ xs → (y ∷ xs) ⊢ᴸ ρ ∶ xs'
codom-reweakenᴸ wfl-nil _ = wfl-nil
codom-reweakenᴸ {xs' = xs'} {y = y} (wfl-cons {a = a} rem D₀ fresh) y∉xs =
  let y∉xs₁ : y ∉ᴸ _
      y∉xs₁ = remove-preserves-∉ᴸ y∉xs rem
      rem' = rem-thereᴸ (λ y≡a → y∉xs (subst (_∈ᴸ _) y≡a (removeᴸ→memberᴸ rem))) rem
  in wfl-cons rem' (codom-reweakenᴸ D₀ y∉xs₁) fresh

-- Restrict ρ's codomain to its actual range.
restrict-codom-to-rangeᴸ :
  ∀ {xs xs' ρ} → xs ⊢ᴸ ρ ∶ xs' → range ρ ⊢ᴸ ρ ∶ xs'
restrict-codom-to-rangeᴸ wfl-nil = wfl-nil
restrict-codom-to-rangeᴸ (wfl-cons _ D₀ fresh) =
  wfl-cons rem-hereᴸ (restrict-codom-to-rangeᴸ D₀) fresh

------------------------------------------------------------------------
-- List-level helpers used by linearity inversion.
------------------------------------------------------------------------

-- The removed element does not occur in the output (with distinctness).
remove-removes :
  ∀ {xs ys a} → Distinct xs → xs -ᴸ a ≡ ys → a ∉ᴸ ys
remove-removes (d-cons fresh _) rem-hereᴸ      = fresh
remove-removes (d-cons _ d) (rem-thereᴸ ne rem) hereᴸ      = ne refl
remove-removes (d-cons _ d) (rem-thereᴸ _ rem) (thereᴸ m)  =
  remove-removes d rem m

-- Removal preserves distinctness.
remove-preserves-distinct :
  ∀ {xs ys a} → Distinct xs → xs -ᴸ a ≡ ys → Distinct ys
remove-preserves-distinct (d-cons _ d)         rem-hereᴸ          = d
remove-preserves-distinct (d-cons fresh d) (rem-thereᴸ _ rem) =
  d-cons (remove-preserves-∉ᴸ fresh rem) (remove-preserves-distinct d rem)

-- Aux 1.3 at the list level (no distinctness needed).
swap-removeᴸ :
  ∀ {xs xs₁ xs₁₂ a₁ a₂} → xs -ᴸ a₁ ≡ xs₁ → xs₁ -ᴸ a₂ ≡ xs₁₂ → a₁ ≢ a₂ →
  ∃[ xs₂ ] ((xs -ᴸ a₂ ≡ xs₂) × (xs₂ -ᴸ a₁ ≡ xs₁₂))
swap-removeᴸ rem-hereᴸ                   D₂                     ne =
  _ , rem-thereᴸ (λ a₂≡a₁ → ne (sym a₂≡a₁)) D₂ , rem-hereᴸ
swap-removeᴸ (rem-thereᴸ ne₁ D₁')        rem-hereᴸ              ne =
  _ , rem-hereᴸ , D₁'
swap-removeᴸ (rem-thereᴸ ne₁ D₁')        (rem-thereᴸ ne₂ D₂')   ne with swap-removeᴸ D₁' D₂' ne
... | xs₂' , p₁ , p₂ = _ , rem-thereᴸ ne₂ p₁ , rem-thereᴸ ne₁ p₂

------------------------------------------------------------------------
-- Auxiliary lookup lemmas
------------------------------------------------------------------------

-- ρ-lookup at the head of a cons.
lookup-head : ∀ {a x ρ} → ((a , x) ∷ ρ) ! x ≡ just a
lookup-head {a} {x} with x ≟ x
... | yes _  = refl
... | no ne  = ⊥-elim (ne refl)

-- ρ-lookup at a non-matching head.
lookup-cons-≢ :
  ∀ {a x z ρ} → z ≢ x → ((a , x) ∷ ρ) ! z ≡ ρ ! z
lookup-cons-≢ {a} {x} {z} ne with z ≟ x
... | yes refl = ⊥-elim (ne refl)
... | no  _    = refl

-- Reduce `look` given a known lookup result.
look-from-just : ∀ {ρ a b} → ρ ! a ≡ just b → look ρ a ≡ b
look-from-just {ρ} {a} {b} eq with ρ ! a
look-from-just {ρ} {a} {b} refl | just .b = refl

look-from-nothing : ∀ {ρ a} → ρ ! a ≡ nothing → look ρ a ≡ a
look-from-nothing {ρ} {a} eq with ρ ! a
look-from-nothing refl | nothing = refl

-- `look ρ x` at the head of a cons (matching input).
look-head : ∀ {a x ρ} → look ((a , x) ∷ ρ) x ≡ a
look-head {a} {x} {ρ} with x ≟ x
... | yes _   = refl
... | no  ne  = ⊥-elim (ne refl)

-- `look ρ x` at a non-matching head reduces.
look-cons-≢ :
  ∀ {a x z ρ} → z ≢ x → look ((a , x) ∷ ρ) z ≡ look ρ z
look-cons-≢ {a} {x} {z} {ρ} ne with z ≟ x
... | yes refl = ⊥-elim (ne refl)
... | no  _    = refl

------------------------------------------------------------------------
-- Aux 2.3b: linearity inversion.
--
-- Given xs ⊢ ρ : xs' with y ∈ xs', we can decompose ρ into the entry
-- mapping to y plus the rest.  The rest is typed at smaller contexts
-- and agrees with ρ on the codomain minus y.
------------------------------------------------------------------------

record LinearityInversionᴸ (xs : List Name) (ρ : Ren) (xs' : List Name) (y : Name) : Set where
  field
    b              : Name
    xs_mid         : List Name
    xs'_y          : List Name
    ρ-minus-y      : Ren
    look-eq        : look ρ y ≡ b
    rem-xs         : xs -ᴸ b ≡ xs_mid
    rem-xs'        : xs' -ᴸ y ≡ xs'_y
    wf-minus       : xs_mid ⊢ᴸ ρ-minus-y ∶ xs'_y
    agree          : ∀ {z} → z ∈ᴸ xs'_y → look ρ z ≡ look ρ-minus-y z

linearity-inversionᴸ :
  ∀ {xs xs' ρ y} → xs ⊢ᴸ ρ ∶ xs' → Distinct xs → y ∈ᴸ xs'
  → LinearityInversionᴸ xs ρ xs' y
-- Case y = x (head of codomain): extract head entry (c, x).
linearity-inversionᴸ
  {ρ = (c , x) ∷ ρ_inner}
  (wfl-cons {a = .c} {x = .x} rem D fresh-x) d-xs hereᴸ =
  record
    { b           = c
    ; xs_mid      = _
    ; xs'_y       = _
    ; ρ-minus-y   = ρ_inner
    ; look-eq     = look-head {c} {x}
    ; rem-xs      = rem
    ; rem-xs'     = rem-hereᴸ
    ; wf-minus    = D
    ; agree       = λ {z} z∈ →
        look-cons-≢ {a = c} {x = x} {z = z} {ρ = ρ_inner}
                    (λ z≡x → fresh-x (subst (_∈ᴸ _) z≡x z∈))
    }
-- Case y ≠ x (deeper in codomain): recurse + swap removals.
linearity-inversionᴸ
  {ρ = (c , x) ∷ ρ_inner}
  (wfl-cons {a = .c} {x = .x} rem D fresh-x) d-xs (thereᴸ {x = y} m)
  with linearity-inversionᴸ D (remove-preserves-distinct d-xs rem) m
... | inner =
  let
    b'        = LinearityInversionᴸ.b inner
    xs_mid'   = LinearityInversionᴸ.xs_mid inner
    xs'_y'    = LinearityInversionᴸ.xs'_y inner
    ρ-rest    = LinearityInversionᴸ.ρ-minus-y inner
    eq        = LinearityInversionᴸ.look-eq inner
    rem-out   = LinearityInversionᴸ.rem-xs inner
    rem-cod   = LinearityInversionᴸ.rem-xs' inner
    wf-rest   = LinearityInversionᴸ.wf-minus inner
    agr       = LinearityInversionᴸ.agree inner
    -- c ≠ b' because c ∉ xs-outer (by remove-removes) and b' ∈ xs-outer
    -- (by ren-output-inᴸ on D applied to m).
    c∉xs-outer  = remove-removes d-xs rem
    b'∈xs-outer = subst (_∈ᴸ _) eq (ren-output-inᴸ {x = y} D m)
    c≢b'        : c ≢ b'
    c≢b'        = λ c≡b' → c∉xs-outer (subst (_∈ᴸ _) (sym c≡b') b'∈xs-outer)
    -- swap-removeᴸ on (xs -ᴸ c ≡ xs-outer) and (xs-outer -ᴸ b' ≡ xs_mid')
    swapped     = swap-removeᴸ rem rem-out c≢b'
    xs-swap     = proj₁ swapped
    rem-b'      = proj₁ (proj₂ swapped)
    rem-c-rest  = proj₂ (proj₂ swapped)
    -- y ≠ x because y ∈ xs'_inner and x ∉ xs'_inner.
    -- We don't strictly need this in the body but for the agree clause.
    y≢x         : y ≢ x
    y≢x y≡x     = fresh-x (subst (_∈ᴸ _) y≡x m)
  in
  record
    { b           = b'
    ; xs_mid      = xs-swap
    ; xs'_y       = x ∷ xs'_y'
    ; ρ-minus-y   = (c , x) ∷ ρ-rest
    ; look-eq     = trans (look-cons-≢ {a = c} {x = x} {z = y} {ρ = ρ_inner} y≢x) eq
    ; rem-xs      = rem-b'
    ; rem-xs'     = rem-thereᴸ y≢x rem-cod
    ; wf-minus    = wfl-cons rem-c-rest wf-rest
                             (remove-preserves-∉ᴸ fresh-x rem-cod)
    ; agree       = agree-aux ρ-rest y≢x agr
    }
  where
    -- Closed-over helper: builds agree for the outer record.
    agree-aux :
      ∀ (ρ-rest' : Ren)
        {y'} → y' ≢ x
      → (∀ {z'} → z' ∈ᴸ LinearityInversionᴸ.xs'_y inner → look ρ_inner z' ≡ look ρ-rest' z')
      → ∀ {z} → z ∈ᴸ (x ∷ LinearityInversionᴸ.xs'_y inner)
      → look ((c , x) ∷ ρ_inner) z ≡ look ((c , x) ∷ ρ-rest') z
    agree-aux ρ-rest' _ _ hereᴸ =
      trans (look-head {c} {x} {ρ_inner})
            (sym (look-head {c} {x} {ρ-rest'}))
    agree-aux ρ-rest' _ agr {z} (thereᴸ z∈) =
      let z∈xs'_inner = ⊆ᴸ-mono-∈ (removeᴸ→⊆ᴸ (LinearityInversionᴸ.rem-xs' inner)) z∈
          z≢x : z ≢ x
          z≢x = λ z≡x → fresh-x (subst (_∈ᴸ _) z≡x z∈xs'_inner)
      in trans (look-cons-≢ {a = c} {x = x} {z = z} {ρ = ρ_inner} z≢x)
               (trans (agr z∈)
                      (sym (look-cons-≢ {a = c} {x = x} {z = z} {ρ = ρ-rest'} z≢x)))

------------------------------------------------------------------------
-- Lookup well-definedness from typing.
------------------------------------------------------------------------

ren-lookup-definedᴸ :
  ∀ {xs xs' ρ x} → xs ⊢ᴸ ρ ∶ xs' → x ∈ᴸ xs' → ∃[ b ] (ρ ! x ≡ just b)
ren-lookup-definedᴸ (wfl-cons {a = a} {x = y} _ _ _) hereᴸ
  = a , lookup-head {a} {y}
ren-lookup-definedᴸ {ρ = (a , y) ∷ ρ-inner} {x = x}
  (wfl-cons rem D fresh) (thereᴸ m)
  with x ≟ y
... | yes refl = ⊥-elim (fresh m)
... | no  x≢y  = ren-lookup-definedᴸ D m

------------------------------------------------------------------------
-- Removal uniqueness (no Distinct needed: the rules already enforce it).
------------------------------------------------------------------------

-- xs -ᴸ a, where xs starts with a, yields the tail.
xs-rem-here-eq : ∀ {a xs ys} → (a ∷ xs) -ᴸ a ≡ ys → xs ≡ ys
xs-rem-here-eq rem-hereᴸ            = refl
xs-rem-here-eq (rem-thereᴸ ne _)    = ⊥-elim (ne refl)

removeᴸ-unique :
  ∀ {xs ys₁ ys₂ a} → xs -ᴸ a ≡ ys₁ → xs -ᴸ a ≡ ys₂ → ys₁ ≡ ys₂
removeᴸ-unique rem-hereᴸ          D₂                 = xs-rem-here-eq D₂
removeᴸ-unique (rem-thereᴸ ne _)  rem-hereᴸ          = ⊥-elim (ne refl)
removeᴸ-unique (rem-thereᴸ _ D₁)  (rem-thereᴸ _ D₂)  =
  cong (_ ∷_) (removeᴸ-unique D₁ D₂)

------------------------------------------------------------------------
-- ⨾-cong-lookup: if ρ₁ and ρ₂ agree on the lookups of all outputs of σ,
-- then ρ₁ ⨾ σ ≡ ρ₂ ⨾ σ.
------------------------------------------------------------------------

⨾-cong-lookup :
  ∀ {ρ₁ ρ₂ σ}
  → (∀ a → a ∈ᴸ range σ → ρ₁ ! a ≡ ρ₂ ! a)
  → ρ₁ ⨾ σ ≡ ρ₂ ⨾ σ
⨾-cong-lookup {σ = []} _ = refl
⨾-cong-lookup {ρ₁} {ρ₂} {σ = (a , x) ∷ σ-0} agr
  with ρ₁ ! a | ρ₂ ! a | agr a hereᴸ
... | just b₁ | just .b₁ | refl =
      cong ((b₁ , x) ∷_) (⨾-cong-lookup (λ a' m → agr a' (thereᴸ m)))
... | nothing | nothing  | refl =
      ⨾-cong-lookup (λ a' m → agr a' (thereᴸ m))

------------------------------------------------------------------------
-- Range membership at the list level: outputs of σ live in σ's
-- output context.
------------------------------------------------------------------------

ren-output-inᴸ-range :
  ∀ {xs xs' σ z} → xs ⊢ᴸ σ ∶ xs' → z ∈ᴸ range σ → z ∈ᴸ xs
ren-output-inᴸ-range (wfl-cons rem _ _) hereᴸ      = removeᴸ→memberᴸ rem
ren-output-inᴸ-range (wfl-cons rem D _) (thereᴸ m) =
  ⊆ᴸ-mono-∈ (removeᴸ→⊆ᴸ rem) (ren-output-inᴸ-range D m)

-- Convert look-equality to !-equality when both lookups are defined.
look-eq→!-eq :
  ∀ {ρa ρb z ba bb}
  → ρa ! z ≡ just ba → ρb ! z ≡ just bb
  → look ρa z ≡ look ρb z
  → ρa ! z ≡ ρb ! z
look-eq→!-eq {ρa} {ρb} {z} {ba} {bb} eq-a eq-b look-eq =
  let lo-a : look ρa z ≡ ba
      lo-a = look-from-just {ρa} {z} {ba} eq-a
      lo-b : look ρb z ≡ bb
      lo-b = look-from-just {ρb} {z} {bb} eq-b
      ba≡bb : ba ≡ bb
      ba≡bb = trans (sym lo-a) (trans look-eq lo-b)
  in trans eq-a (trans (cong just ba≡bb) (sym eq-b))

------------------------------------------------------------------------
-- §2.3: composition of well-typed renamings is well-typed.
------------------------------------------------------------------------

ren-comp-wfᴸ :
  ∀ {xs xs' xs'' ρ ρ'}
  → xs ⊢ᴸ ρ ∶ xs' → xs' ⊢ᴸ ρ' ∶ xs'' → Distinct xs
  → xs ⊢ᴸ (ρ ⨾ ρ') ∶ xs''
ren-comp-wfᴸ D wfl-nil _ = wfl-nil
ren-comp-wfᴸ {xs} {xs'} {xs''} {ρ} {(a , x) ∷ ρ'-0}
             D
             (wfl-cons {xs₁ = xs'-mid} {xs' = xs''-0} {a = .a} {x = .x}
                       rem' D'-0 fresh-x)
             d-xs
  with ren-lookup-definedᴸ D (removeᴸ→memberᴸ rem')
... | b' , ρ!a-eq
  with linearity-inversionᴸ D d-xs (removeᴸ→memberᴸ rem')
... | inv
  with ρ ! a | ρ!a-eq
... | just .b' | refl = step
  where
    inv-b      = LinearityInversionᴸ.b inv
    inv-xs_mid = LinearityInversionᴸ.xs_mid inv
    inv-xs'_y  = LinearityInversionᴸ.xs'_y inv
    inv-ρm     = LinearityInversionᴸ.ρ-minus-y inv

    b'≡inv-b : b' ≡ inv-b
    b'≡inv-b = trans (sym (look-from-just {ρ} {a} {b'} ρ!a-eq))
                      (LinearityInversionᴸ.look-eq inv)

    rem-xs-bʹ : xs -ᴸ b' ≡ inv-xs_mid
    rem-xs-bʹ = subst (λ z → xs -ᴸ z ≡ inv-xs_mid)
                      (sym b'≡inv-b) (LinearityInversionᴸ.rem-xs inv)

    xs'_y≡xs'-mid : inv-xs'_y ≡ xs'-mid
    xs'_y≡xs'-mid = removeᴸ-unique (LinearityInversionᴸ.rem-xs' inv) rem'

    ρ-minus-wf-mid : inv-xs_mid ⊢ᴸ inv-ρm ∶ xs'-mid
    ρ-minus-wf-mid = subst (inv-xs_mid ⊢ᴸ inv-ρm ∶_)
                            xs'_y≡xs'-mid (LinearityInversionᴸ.wf-minus inv)

    d-xs_mid : Distinct inv-xs_mid
    d-xs_mid = remove-preserves-distinct d-xs rem-xs-bʹ

    IH : inv-xs_mid ⊢ᴸ (inv-ρm ⨾ ρ'-0) ∶ xs''-0
    IH = ren-comp-wfᴸ ρ-minus-wf-mid D'-0 d-xs_mid

    -- The agreement at !-level on outputs of ρ'-0
    agree-! : ∀ z → z ∈ᴸ range ρ'-0 → ρ ! z ≡ inv-ρm ! z
    agree-! z z∈ =
      let z∈xs'-mid : z ∈ᴸ xs'-mid
          z∈xs'-mid = ren-output-inᴸ-range D'-0 z∈
          z∈xs'_y   : z ∈ᴸ inv-xs'_y
          z∈xs'_y   = subst (z ∈ᴸ_) (sym xs'_y≡xs'-mid) z∈xs'-mid
          look-agr  : look ρ z ≡ look inv-ρm z
          look-agr  = LinearityInversionᴸ.agree inv z∈xs'_y
          ρ-def     = ren-lookup-definedᴸ D
                        (⊆ᴸ-mono-∈ (removeᴸ→⊆ᴸ rem') z∈xs'-mid)
          ρ--def    = ren-lookup-definedᴸ ρ-minus-wf-mid z∈xs'-mid
      in look-eq→!-eq {ρa = ρ} {ρb = inv-ρm} {z = z}
                       {ba = proj₁ ρ-def} {bb = proj₁ ρ--def}
                       (proj₂ ρ-def) (proj₂ ρ--def) look-agr

    ⨾-equal : ρ ⨾ ρ'-0 ≡ inv-ρm ⨾ ρ'-0
    ⨾-equal = ⨾-cong-lookup agree-!

    goal-mid : inv-xs_mid ⊢ᴸ (ρ ⨾ ρ'-0) ∶ xs''-0
    goal-mid = subst (inv-xs_mid ⊢ᴸ_∶ xs''-0) (sym ⨾-equal) IH

    step : xs ⊢ᴸ ((b' , x) ∷ (ρ ⨾ ρ'-0)) ∶ (x ∷ xs''-0)
    step = wfl-cons rem-xs-bʹ goal-mid fresh-x

ren-comp-wf :
  ∀ {Γ Γ' Γ'' ρ ρ'} → Γ ⊢ ρ ∶ Γ' → Γ' ⊢ ρ' ∶ Γ'' → Γ ⊢ (ρ ⨾ ρ') ∶ Γ''
ren-comp-wf {Γ} D D' = ren-comp-wfᴸ D D' (nd Γ)

------------------------------------------------------------------------
-- Phase 1 (plan): codomain manipulation helpers.
--
-- ∈→remᴸ, rem-pushes-memᴸ, sub-residualᴸ, subsume-codomᴸ, retype-codomᴸ.
------------------------------------------------------------------------

-- Membership gives a concrete removal witness.
∈→remᴸ : ∀ {a xs} → a ∈ᴸ xs → ∃[ ys ] (xs -ᴸ a ≡ ys)
∈→remᴸ {a} {x ∷ xs} m with a ≟ x
... | yes refl = xs , rem-hereᴸ
... | no  a≢x  with m
... | hereᴸ          = ⊥-elim (a≢x refl)
... | thereᴸ {xs = xs} m' =
        let ys , rem = ∈→remᴸ {a} {xs} m'
        in x ∷ ys , rem-thereᴸ a≢x rem

-- Removal preserves membership for non-equal elements.
rem-pushes-memᴸ :
  ∀ {a b ws zs} → ws -ᴸ a ≡ zs → b ∈ᴸ ws → b ≢ a → b ∈ᴸ zs
rem-pushes-memᴸ rem-hereᴸ hereᴸ b≢a = ⊥-elim (b≢a refl)
rem-pushes-memᴸ rem-hereᴸ (thereᴸ m) _ = m
rem-pushes-memᴸ (rem-thereᴸ _ _) hereᴸ _ = hereᴸ
rem-pushes-memᴸ (rem-thereᴸ _ rem) (thereᴸ m) b≢a =
  thereᴸ (rem-pushes-memᴸ rem m b≢a)

-- ⊆ᴸ propagation through removal of the same element.
sub-residualᴸ :
  ∀ {xs ys xs' ys' a}
  → xs ⊆ᴸ ys → xs -ᴸ a ≡ xs' → ys -ᴸ a ≡ ys' → xs' ⊆ᴸ ys'
sub-residualᴸ ⊆-nil () _
sub-residualᴸ (⊆-cons s) rem-hereᴸ rem-hereᴸ = s
sub-residualᴸ (⊆-cons s) rem-hereᴸ (rem-thereᴸ ne _) = ⊥-elim (ne refl)
sub-residualᴸ (⊆-cons s) (rem-thereᴸ ne _) rem-hereᴸ = ⊥-elim (ne refl)
sub-residualᴸ (⊆-cons s) (rem-thereᴸ _ rem-xs) (rem-thereᴸ _ rem-ys) =
  ⊆-cons (sub-residualᴸ s rem-xs rem-ys)
sub-residualᴸ (⊆-skip s) rem rem-hereᴸ =
  ⊆ᴸ-trans (removeᴸ→⊆ᴸ rem) s
sub-residualᴸ (⊆-skip s) rem (rem-thereᴸ _ rem-ys) =
  ⊆-skip (sub-residualᴸ s rem rem-ys)

-- If xs ⊢ᴸ ρ ∶ Δ and xs ⊆ᴸ ys, then ρ also types at the larger codomain ys.
subsume-codomᴸ :
  ∀ {xs ys ρ Δ} → xs ⊢ᴸ ρ ∶ Δ → xs ⊆ᴸ ys → ys ⊢ᴸ ρ ∶ Δ
subsume-codomᴸ wfl-nil _ = wfl-nil
subsume-codomᴸ (wfl-cons {a = a} rem D' fresh) sub =
  let a∈xs = removeᴸ→memberᴸ rem
      a∈ys = ⊆ᴸ-mono-∈ sub a∈xs
      ys-rem , ys-rem-eq = ∈→remᴸ a∈ys
      sub' = sub-residualᴸ sub rem ys-rem-eq
      D'' = subsume-codomᴸ D' sub'
  in wfl-cons ys-rem-eq D'' fresh

-- Retype ρ's codomain to a list ys that contains all of ρ's outputs.
-- Requires Distinct xs (the original codomain) to ensure ρ's outputs
-- are distinct, so subsequent recursive calls operate on smaller ys.
retype-codomᴸ :
  ∀ {xs ys ρ Δ}
  → Distinct xs
  → xs ⊢ᴸ ρ ∶ Δ
  → (∀ {a} → a ∈ᴸ range ρ → a ∈ᴸ ys)
  → ys ⊢ᴸ ρ ∶ Δ
retype-codomᴸ _ wfl-nil _ = wfl-nil
retype-codomᴸ d (wfl-cons {a = a} rem D' fresh) embed =
  let a∈ys = embed hereᴸ
      ys-rem , ys-rem-eq = ∈→remᴸ a∈ys
      d-mid = remove-preserves-distinct d rem
      a∉xs-mid = remove-removes d rem
      embed' : ∀ {b} → b ∈ᴸ range _ → b ∈ᴸ ys-rem
      embed' {b} m =
        let b∈ys = embed (thereᴸ m)
            b∈xs-mid = ren-output-inᴸ-range D' m
            b≢a : b ≢ a
            b≢a b≡a = a∉xs-mid (subst (_∈ᴸ _) b≡a b∈xs-mid)
        in rem-pushes-memᴸ ys-rem-eq b∈ys b≢a
      D'' = retype-codomᴸ d-mid D' embed'
  in wfl-cons ys-rem-eq D'' fresh

------------------------------------------------------------------------
-- Phase 4 (plan): build-renᴸ — a generalisation of identity embedding
-- with a custom output function.
------------------------------------------------------------------------

build-renᴸ : (Name → Name) → List Name → Ren
build-renᴸ f []       = []
build-renᴸ f (x ∷ xs) = (f x , x) ∷ build-renᴸ f xs

-- Lookup in build-renᴸ.
build-ren-look :
  ∀ {f xs z} → z ∈ᴸ xs → (build-renᴸ f xs) ! z ≡ just (f z)
build-ren-look {f} {x ∷ xs} {.x} hereᴸ with x ≟ x
... | yes _    = refl
... | no  ne   = ⊥-elim (ne refl)
build-ren-look {f} {x ∷ xs} {z} (thereᴸ m) with z ≟ x
... | yes refl = refl
... | no  _    = build-ren-look m

-- Well-typing of build-renᴸ.
-- Requires Distinct xs (so successive entries don't repeat),
-- f maps xs into ys, and f is injective on xs.
build-ren-wfᴸ :
  ∀ {ys xs f}
  → Distinct xs
  → (∀ {z} → z ∈ᴸ xs → f z ∈ᴸ ys)
  → (∀ {z z'} → z ∈ᴸ xs → z' ∈ᴸ xs → z ≢ z' → f z ≢ f z')
  → ys ⊢ᴸ build-renᴸ f xs ∶ xs
build-ren-wfᴸ {xs = []} _ _ _ = wfl-nil
build-ren-wfᴸ {ys = ys} {xs = x ∷ xs-rest} {f = f}
              (d-cons x∉xs d-rest) f-mem f-inj =
  let fx∈ys = f-mem hereᴸ
      ys-rem , ys-rem-eq = ∈→remᴸ fx∈ys
      f-mem' : ∀ {z} → z ∈ᴸ xs-rest → f z ∈ᴸ ys-rem
      f-mem' {z} m =
        let fz∈ys = f-mem (thereᴸ m)
            z≢x : z ≢ x
            z≢x z≡x = x∉xs (subst (_∈ᴸ xs-rest) z≡x m)
            fz≢fx : f z ≢ f x
            fz≢fx = f-inj (thereᴸ m) hereᴸ z≢x
        in rem-pushes-memᴸ ys-rem-eq fz∈ys fz≢fx
      f-inj' : ∀ {z z'} → z ∈ᴸ xs-rest → z' ∈ᴸ xs-rest → z ≢ z' → f z ≢ f z'
      f-inj' z∈ z'∈ z≢z' = f-inj (thereᴸ z∈) (thereᴸ z'∈) z≢z'
      ih = build-ren-wfᴸ d-rest f-mem' f-inj'
  in wfl-cons ys-rem-eq ih x∉xs

------------------------------------------------------------------------
-- §3.1 (Aux 3.1): typing of inverse renaming.
--
-- These lemmas were previously in Properties.agda; we hoist them here
-- so that PushoutCoequalizer.agda can use them.
------------------------------------------------------------------------

ren-inv-wfᴸ :
  ∀ {xs xs' ρ} → Distinct xs → xs ⊢ᴸ ρ ∶ xs'
  → xs' ⊢ᴸ ρ ⁻¹ ∶ range ρ
ren-inv-wfᴸ _ wfl-nil = wfl-nil
ren-inv-wfᴸ d (wfl-cons {a = a} rem D fresh) =
  let d' = remove-preserves-distinct d rem
      ih = ren-inv-wfᴸ d' D
      a-not-in-xs-mid = remove-removes d rem
      a-not-in-range-ρ-inner :
        a ∉ᴸ range _
      a-not-in-range-ρ-inner a∈range =
        a-not-in-xs-mid (ren-output-inᴸ-range D a∈range)
  in wfl-cons rem-hereᴸ ih a-not-in-range-ρ-inner

range-distinctᴸ :
  ∀ {xs xs' ρ} → Distinct xs → xs ⊢ᴸ ρ ∶ xs' → Distinct (range ρ)
range-distinctᴸ _ wfl-nil = d-nil
range-distinctᴸ d (wfl-cons {a = a} rem D _) =
  let d' = remove-preserves-distinct d rem
      a-not-in-xs-mid = remove-removes d rem
      a-not-in-range :
        a ∉ᴸ range _
      a-not-in-range a∈range =
        a-not-in-xs-mid (ren-output-inᴸ-range D a∈range)
  in d-cons a-not-in-range (range-distinctᴸ d' D)

ren-inv-wf :
  ∀ {Γ Γ' ρ} → Γ ⊢ ρ ∶ Γ'
  → ∃[ Γ_inv ] ((list Γ_inv ≡ range ρ) × (Γ' ⊢ ρ ⁻¹ ∶ Γ_inv))
ren-inv-wf {Γ = Γ} {Γ' = Γ'} D =
  mkCtx (range _) (range-distinctᴸ (nd Γ) D) , refl ,
  ren-inv-wfᴸ (nd Γ) D

-- If ρ ! a ≡ just b, then b lives in ρ's codomain.
ρ!-output-in-codomain :
  ∀ {xs xs' ρ a b} → xs ⊢ᴸ ρ ∶ xs' → ρ ! a ≡ just b → b ∈ᴸ xs
ρ!-output-in-codomain wfl-nil ()
ρ!-output-in-codomain {ρ = (c , x) ∷ ρ-rest} {a = a} (wfl-cons rem D' _) eq
  with a ≟ x | eq
... | yes refl | refl = removeᴸ→memberᴸ rem
... | no a≢x | eq' =
        ⊆ᴸ-mono-∈ (removeᴸ→⊆ᴸ rem) (ρ!-output-in-codomain D' eq')

-- Inverse lookup: if ρ ! a ≡ just b, then ρ⁻¹ ! b ≡ just a.
inv-look-from-look :
  ∀ {xs xs' ρ a b} → Distinct xs → xs ⊢ᴸ ρ ∶ xs'
  → ρ ! a ≡ just b → ρ ⁻¹ ! b ≡ just a
inv-look-from-look _ wfl-nil ()
inv-look-from-look {ρ = (c , x) ∷ ρ-rest} {a = a} {b = b} d
                    (wfl-cons rem D' _) eq
  with a ≟ x | eq
... | yes refl | refl =
        lookup-head {x} {c} {ρ-rest ⁻¹}
... | no a≢x | eq' =
        let d-mid   = remove-preserves-distinct d rem
            ih      = inv-look-from-look d-mid D' eq'
            b-in-xs-mid = ρ!-output-in-codomain D' eq'
            c-not-in-xs-mid = remove-removes d rem
            b≢c : b ≢ c
            b≢c b≡c = c-not-in-xs-mid (subst (_∈ᴸ _) b≡c b-in-xs-mid)
        in trans (lookup-cons-≢ {x} {c} {b} {ρ-rest ⁻¹} b≢c) ih

-- ρ ⨾ ρ-rest is unaffected by prepending an entry to ρ whose input is
-- absent from ρ-rest's codomain.
prepend-comp-eq :
  ∀ {ρ' a₀ x₀ ρ-rest xs_mid xs'_rest}
  → xs_mid ⊢ᴸ ρ-rest ∶ xs'_rest → x₀ ∉ᴸ xs_mid
  → ((a₀ , x₀) ∷ ρ') ⨾ ρ-rest ≡ ρ' ⨾ ρ-rest
prepend-comp-eq {ρ'} {a₀} {x₀} {ρ-rest} D x₀∉xs_mid =
  ⨾-cong-lookup λ a a∈range →
    let a-in-xs_mid = ren-output-inᴸ-range D a∈range
        a≢x₀ : a ≢ x₀
        a≢x₀ a≡x₀ = x₀∉xs_mid (subst (_∈ᴸ _) a≡x₀ a-in-xs_mid)
    in lookup-cons-≢ {a₀} {x₀} {a} {ρ'} a≢x₀

-- Composition head-step using an explicit head-lookup witness.
⨾-cons-head-step :
  ∀ {ρ' c x ρ-rest b} → ρ' ! c ≡ just b
  → ρ' ⨾ ((c , x) ∷ ρ-rest) ≡ (b , x) ∷ (ρ' ⨾ ρ-rest)
⨾-cons-head-step {ρ'} {c} {x} {ρ-rest} {b} eq
  with ρ' ! c | eq
... | .(just b) | refl = refl

-- (ρ⁻¹ ⨾ ρ) ! a ≡ just a for a ∈ ρ's domain.
inv-comp-id-! :
  ∀ {xs xs' ρ a} → Distinct xs → xs ⊢ᴸ ρ ∶ xs' → a ∈ᴸ xs'
  → (ρ ⁻¹ ⨾ ρ) ! a ≡ just a
inv-comp-id-! _ wfl-nil ()
inv-comp-id-! {ρ = (c , x) ∷ ρ-rest} {a = a} d
        (wfl-cons rem D' fresh) a∈ =
  let ρ⁻¹!c-eq : ((x , c) ∷ ρ-rest ⁻¹) ! c ≡ just x
      ρ⁻¹!c-eq = lookup-head {x} {c} {ρ-rest ⁻¹}
      step-head : ((c , x) ∷ ρ-rest) ⁻¹ ⨾ ((c , x) ∷ ρ-rest)
                ≡ (x , x) ∷ (((c , x) ∷ ρ-rest) ⁻¹ ⨾ ρ-rest)
      step-head = ⨾-cons-head-step {(x , c) ∷ ρ-rest ⁻¹} {c} {x} {ρ-rest} {x} ρ⁻¹!c-eq
      d-mid       = remove-preserves-distinct d rem
      c∉xs_mid    = remove-removes d rem
      prep-eq     : ((x , c) ∷ ρ-rest ⁻¹) ⨾ ρ-rest ≡ ρ-rest ⁻¹ ⨾ ρ-rest
      prep-eq     = prepend-comp-eq {ρ-rest ⁻¹} {x} {c} {ρ-rest} D' c∉xs_mid
  in trans (cong (_! a) step-head) (lookup-step a∈)
  where
    lookup-step :
      a ∈ᴸ (x ∷ _)
      → ((x , x) ∷ (((c , x) ∷ ρ-rest) ⁻¹ ⨾ ρ-rest)) ! a ≡ just a
    lookup-step hereᴸ = lookup-head {x} {x} {((c , x) ∷ ρ-rest) ⁻¹ ⨾ ρ-rest}
    lookup-step (thereᴸ m) =
      let a≢x : a ≢ x
          a≢x a≡x = fresh (subst (_∈ᴸ _) a≡x m)
          d-mid    = remove-preserves-distinct d rem
          c∉xs_mid = remove-removes d rem
          prep-eq  : ((x , c) ∷ ρ-rest ⁻¹) ⨾ ρ-rest ≡ ρ-rest ⁻¹ ⨾ ρ-rest
          prep-eq  = prepend-comp-eq {ρ-rest ⁻¹} {x} {c} {ρ-rest} D' c∉xs_mid
          ih       = inv-comp-id-! d-mid D' m
          head-skip : ((x , x) ∷ (((c , x) ∷ ρ-rest) ⁻¹ ⨾ ρ-rest)) ! a
                    ≡ (((c , x) ∷ ρ-rest) ⁻¹ ⨾ ρ-rest) ! a
          head-skip = lookup-cons-≢ {x} {x} {a} {((c , x) ∷ ρ-rest) ⁻¹ ⨾ ρ-rest} a≢x
      in trans head-skip (trans (cong (_! a) prep-eq) ih)

-- Symmetric: (ρ ⨾ ρ⁻¹) ! z ≡ just z for z ∈ range ρ.
comp-inv-id-! :
  ∀ {xs xs' ρ z} → Distinct xs → xs ⊢ᴸ ρ ∶ xs' → z ∈ᴸ range ρ
  → (ρ ⨾ ρ ⁻¹) ! z ≡ just z
comp-inv-id-! _ wfl-nil ()
comp-inv-id-! {ρ = (c , x) ∷ ρ-rest} {z = z} d
        (wfl-cons rem D' fresh) z∈ =
  let ρ!x-eq : ((c , x) ∷ ρ-rest) ! x ≡ just c
      ρ!x-eq = lookup-head {c} {x} {ρ-rest}
      step-head : ((c , x) ∷ ρ-rest) ⨾ ((c , x) ∷ ρ-rest) ⁻¹
                ≡ (c , c) ∷ (((c , x) ∷ ρ-rest) ⨾ ρ-rest ⁻¹)
      step-head = ⨾-cons-head-step {(c , x) ∷ ρ-rest} {x} {c} {ρ-rest ⁻¹} {c} ρ!x-eq
      d-mid       = remove-preserves-distinct d rem
      c∉xs_mid    = remove-removes d rem
  in trans (cong (_! z) step-head) (lookup-step z∈)
  where
    lookup-step :
      z ∈ᴸ (c ∷ range ρ-rest)
      → ((c , c) ∷ (((c , x) ∷ ρ-rest) ⨾ ρ-rest ⁻¹)) ! z ≡ just z
    lookup-step hereᴸ = lookup-head {c} {c} {((c , x) ∷ ρ-rest) ⨾ ρ-rest ⁻¹}
    lookup-step (thereᴸ m) =
      let z∈xs_mid = ren-output-inᴸ-range D' m
          c∉xs_mid = remove-removes d rem
          z≢c : z ≢ c
          z≢c z≡c = c∉xs_mid (subst (_∈ᴸ _) z≡c z∈xs_mid)
          d-mid = remove-preserves-distinct d rem
          ih    = comp-inv-id-! d-mid D' m
          ρ-rest⁻¹-wf : _ ⊢ᴸ (ρ-rest ⁻¹) ∶ range ρ-rest
          ρ-rest⁻¹-wf = ren-inv-wfᴸ d-mid D'
          prep-eq : ((c , x) ∷ ρ-rest) ⨾ (ρ-rest ⁻¹) ≡ ρ-rest ⨾ (ρ-rest ⁻¹)
          prep-eq = prepend-comp-eq {ρ-rest} {c} {x} {ρ-rest ⁻¹} ρ-rest⁻¹-wf fresh
          head-skip : ((c , c) ∷ (((c , x) ∷ ρ-rest) ⨾ ρ-rest ⁻¹)) ! z
                    ≡ (((c , x) ∷ ρ-rest) ⨾ ρ-rest ⁻¹) ! z
          head-skip = lookup-cons-≢ {c} {c} {z} {((c , x) ∷ ρ-rest) ⨾ ρ-rest ⁻¹} z≢c
      in trans head-skip (trans (cong (_! z) prep-eq) ih)

ρ⁻¹-look-of-ρ-look :
  ∀ {xs xs' ρ a} → Distinct xs → xs ⊢ᴸ ρ ∶ xs' → a ∈ᴸ xs'
  → look (ρ ⁻¹) (look ρ a) ≡ a
ρ⁻¹-look-of-ρ-look {ρ = ρ} {a = a} d D a∈
  with ren-lookup-definedᴸ D a∈
... | b , ρ!a≡just-b =
      let ρ⁻¹!b≡just-a = inv-look-from-look d D ρ!a≡just-b
          look-ρ-eq : look ρ a ≡ b
          look-ρ-eq = look-from-just {ρ} {a} {b} ρ!a≡just-b
          look-ρ⁻¹-eq : look (ρ ⁻¹) b ≡ a
          look-ρ⁻¹-eq = look-from-just {ρ ⁻¹} {b} {a} ρ⁻¹!b≡just-a
      in trans (cong (look (ρ ⁻¹)) look-ρ-eq) look-ρ⁻¹-eq

-- If ρ ! a ≡ just b, then a lives in ρ's domain.
ρ!-input-in-domain :
  ∀ {xs xs' ρ a b} → xs ⊢ᴸ ρ ∶ xs' → ρ ! a ≡ just b → a ∈ᴸ xs'
ρ!-input-in-domain wfl-nil ()
ρ!-input-in-domain {ρ = (c , x) ∷ ρ-rest} {a = a} (wfl-cons rem D' _) eq
  with a ≟ x | eq
... | yes refl | _    = hereᴸ
... | no a≢x  | eq'  = thereᴸ (ρ!-input-in-domain D' eq')

-- If ρ⁻¹ ! z ≡ just x, then ρ ! x ≡ just z.
inv-of-inv-look-from-look :
  ∀ {xs xs' ρ z x} → Distinct xs → xs ⊢ᴸ ρ ∶ xs'
  → (ρ ⁻¹) ! z ≡ just x → ρ ! x ≡ just z
inv-of-inv-look-from-look _ wfl-nil ()
inv-of-inv-look-from-look {ρ = (c , y) ∷ ρ-rest} {z = z} {x = x} d
                          (wfl-cons rem D' fresh) eq
  with z ≟ c | eq
... | yes refl | refl =
        lookup-head {c} {y} {ρ-rest}
... | no z≢c | eq' =
        let d-mid = remove-preserves-distinct d rem
            ih = inv-of-inv-look-from-look d-mid D' eq'
            x≢y : x ≢ y
            x≢y x≡y = fresh (subst (_∈ᴸ _) x≡y (ρ!-input-in-domain D' ih))
        in trans (lookup-cons-≢ {c} {y} {x} {ρ-rest} x≢y) ih

ρ-look-of-ρ⁻¹-look :
  ∀ {xs xs' ρ z} → Distinct xs → xs ⊢ᴸ ρ ∶ xs' → z ∈ᴸ range ρ
  → look ρ (look (ρ ⁻¹) z) ≡ z
ρ-look-of-ρ⁻¹-look {ρ = ρ} {z = z} d D z∈ =
  let ρ⁻¹-wf : _ ⊢ᴸ (ρ ⁻¹) ∶ range ρ
      ρ⁻¹-wf = ren-inv-wfᴸ d D
      ρ⁻¹-def = ren-lookup-definedᴸ ρ⁻¹-wf z∈
      x = proj₁ ρ⁻¹-def
      ρ⁻¹!z≡just-x : (ρ ⁻¹) ! z ≡ just x
      ρ⁻¹!z≡just-x = proj₂ ρ⁻¹-def
      ρ!x≡just-z : ρ ! x ≡ just z
      ρ!x≡just-z = inv-of-inv-look-from-look d D ρ⁻¹!z≡just-x
      look-ρ⁻¹-eq : look (ρ ⁻¹) z ≡ x
      look-ρ⁻¹-eq = look-from-just {ρ ⁻¹} {z} {x} ρ⁻¹!z≡just-x
      look-ρ-eq : look ρ x ≡ z
      look-ρ-eq = look-from-just {ρ} {x} {z} ρ!x≡just-z
  in trans (cong (look ρ) look-ρ⁻¹-eq) look-ρ-eq

just-injective : ∀ {A : Set} {a b : A} → just a ≡ just b → a ≡ b
just-injective refl = refl

-- If ρ ! a ≡ just b, then b is in range ρ (output of an entry).
just-output-in-range :
  ∀ {ρ a b} → ρ ! a ≡ just b → b ∈ᴸ range ρ
just-output-in-range {[]} ()
just-output-in-range {(c , x) ∷ ρ-rest} {a} eq with a ≟ x | eq
... | yes refl | refl = hereᴸ
... | no  _    | eq'  = thereᴸ (just-output-in-range eq')

-- Step helpers for ρ ⨾ σ: separates the just/nothing cases.
comp-step-just :
  ∀ {ρ c x σ b}
  → ρ ! c ≡ just b
  → (ρ ⨾ ((c , x) ∷ σ)) ≡ (b , x) ∷ (ρ ⨾ σ)
comp-step-just {ρ} {c} {x} {σ} {b} eq with ρ ! c | eq
... | .(just b) | refl = refl

comp-step-nothing :
  ∀ {ρ c x σ}
  → ρ ! c ≡ nothing
  → (ρ ⨾ ((c , x) ∷ σ)) ≡ ρ ⨾ σ
comp-step-nothing {ρ} {c} {x} {σ} eq with ρ ! c | eq
... | .nothing | refl = refl

-- All outputs of ρ ⨾ σ are in range ρ.
comp-output-in-rangeᴸ :
  ∀ {ρ σ a} → a ∈ᴸ range (ρ ⨾ σ) → a ∈ᴸ range ρ
comp-output-in-rangeᴸ {σ = []} ()
comp-output-in-rangeᴸ {ρ} {(c , x) ∷ σ-rest} {a} m = aux refl m
  where
    handle-just : ∀ {b} → ρ ! c ≡ just b → a ∈ᴸ (b ∷ range (ρ ⨾ σ-rest)) → a ∈ᴸ range ρ
    handle-just eq hereᴸ      = just-output-in-range {ρ} {c} eq
    handle-just eq (thereᴸ m') = comp-output-in-rangeᴸ {ρ} {σ-rest} {a} m'

    aux : ∀ {mb} → ρ ! c ≡ mb
        → a ∈ᴸ range (ρ ⨾ ((c , x) ∷ σ-rest)) → a ∈ᴸ range ρ
    aux {just b} eq m' =
      let step : ρ ⨾ ((c , x) ∷ σ-rest) ≡ (b , x) ∷ (ρ ⨾ σ-rest)
          step = comp-step-just {ρ} {c} {x} {σ-rest} {b} eq
          m'' : a ∈ᴸ (b ∷ range (ρ ⨾ σ-rest))
          m'' = subst (a ∈ᴸ_) (cong range step) m'
      in handle-just eq m''
    aux {nothing} eq m' =
      let step : ρ ⨾ ((c , x) ∷ σ-rest) ≡ ρ ⨾ σ-rest
          step = comp-step-nothing {ρ} {c} {x} {σ-rest} eq
          m'' : a ∈ᴸ range (ρ ⨾ σ-rest)
          m'' = subst (a ∈ᴸ_) (cong range step) m'
      in comp-output-in-rangeᴸ {ρ} {σ-rest} {a} m''

-- Phase 5 (plan): look injectivity on a well-typed renaming's domain.
look-injective-on-dom :
  ∀ {xs xs' ρ a b}
  → Distinct xs → xs ⊢ᴸ ρ ∶ xs'
  → a ∈ᴸ xs' → b ∈ᴸ xs'
  → look ρ a ≡ look ρ b → a ≡ b
look-injective-on-dom {ρ = ρ} {a = a} {b = b} d D a∈ b∈ look-eq =
  let ρ!a-def = ren-lookup-definedᴸ D a∈
      c₁      = proj₁ ρ!a-def
      ρ!a-eq  = proj₂ ρ!a-def
      ρ!b-def = ren-lookup-definedᴸ D b∈
      c₂      = proj₁ ρ!b-def
      ρ!b-eq  = proj₂ ρ!b-def
      look-a-eq : look ρ a ≡ c₁
      look-a-eq = look-from-just {ρ} {a} {c₁} ρ!a-eq
      look-b-eq : look ρ b ≡ c₂
      look-b-eq = look-from-just {ρ} {b} {c₂} ρ!b-eq
      c₁≡c₂ : c₁ ≡ c₂
      c₁≡c₂ = trans (sym look-a-eq) (trans look-eq look-b-eq)
      ρ⁻¹!c₁-a : (ρ ⁻¹) ! c₁ ≡ just a
      ρ⁻¹!c₁-a = inv-look-from-look d D ρ!a-eq
      ρ⁻¹!c₁-b : (ρ ⁻¹) ! c₁ ≡ just b
      ρ⁻¹!c₁-b = trans (cong ((ρ ⁻¹) !_) c₁≡c₂) (inv-look-from-look d D ρ!b-eq)
  in just-injective (trans (sym ρ⁻¹!c₁-a) ρ⁻¹!c₁-b)

