------------------------------------------------------------------------
-- §6 substitution lemmas (paper unification-properties-new.md).
--
-- We prove §6.4a (id-sub lookup), §6.5 (id-sub-action), §6.2 (sub-lookup-wf),
-- §6.3 (sub-term), §6.6a (lookup of σ-composition), §6.6 (sub-comp-wf),
-- §6.7a (σ-ρ commutation), §6.7 (⨾ˢ-action), right identity
-- (⨾ˢ-right-id), and associativity (⨾ˢ-assoc).
--
-- Some statements need light typing premises to ensure lookups land
-- in the substitution's domain — these are added where required.
------------------------------------------------------------------------

{-# OPTIONS #-}

module Properties where

open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁; proj₂)
open import Data.Nat.Properties using (_≟_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Data.Empty using (⊥; ⊥-elim)

open import Base
open import Renaming
open import Term
open import Substitution
open import MetaWeakening

------------------------------------------------------------------------
-- Helpers
------------------------------------------------------------------------

member→inFstᴸ : ∀ {X Γ ms} → X ⦂[ Γ ]∈ᴸ ms → X ∈Fstᴸ ms
member→inFstᴸ m-hereᴸ      = fst-here
member→inFstᴸ (m-thereᴸ m) = fst-there (member→inFstᴸ m)

------------------------------------------------------------------------
-- Aux 6.4a: id-sub lookup
------------------------------------------------------------------------

id-sub-list-lookup :
  ∀ {ms X Γ}
  → DistinctM ms → X ⦂[ Γ ]∈ᴸ ms
  → id-sub-list ms !ˢ X ≡ just (mv X (id-ren Γ))
id-sub-list-lookup {(X , Γ) ∷ ms} _ (m-hereᴸ {X = .X}) with X ≟ X
... | yes _   = refl
... | no  ne  = ⊥-elim (ne refl)
id-sub-list-lookup {(Y , Γ_Y) ∷ ms} {X = X} (dm-cons Y∉ms d) (m-thereᴸ m) with X ≟ Y
... | yes refl = ⊥-elim (Y∉ms (member→inFstᴸ m))
... | no  _    = id-sub-list-lookup d m

id-sub-lookup :
  ∀ {Θ X Γ} → X ⦂[ Γ ]∈ Θ → id-sub Θ !ˢ X ≡ just (mv X (id-ren Γ))
id-sub-lookup {Θ} m = id-sub-list-lookup (mnd Θ) m

------------------------------------------------------------------------
-- Aux 2.5b: right identity for renaming composition.
------------------------------------------------------------------------

range-id-ren-list : ∀ xs → range (id-ren-list xs) ≡ xs
range-id-ren-list []        = refl
range-id-ren-list (x ∷ xs)  = cong (x ∷_) (range-id-ren-list xs)

id-ren-right-id-list :
  ∀ {xs xs' ρ} → xs ⊢ᴸ ρ ∶ xs' → ρ ⨾ id-ren-list xs' ≡ ρ
id-ren-right-id-list wfl-nil = refl
id-ren-right-id-list {ρ = (a , x) ∷ ρ-inner}
                      (wfl-cons {xs' = xs'-inner} rem D fresh)
  with ((a , x) ∷ ρ-inner) ! x | lookup-head {a} {x} {ρ-inner}
... | just .a | refl =
      cong ((a , x) ∷_)
        (trans
          (⨾-cong-lookup λ z z∈range →
             let z∈xs'-inner = subst (z ∈ᴸ_) (range-id-ren-list xs'-inner) z∈range
             in lookup-cons-≢ {a = a} {x = x} {z = z} {ρ = ρ-inner}
                              (λ z≡x → fresh (subst (_∈ᴸ _) z≡x z∈xs'-inner)))
          (id-ren-right-id-list D))

id-ren-right-id :
  ∀ {Γ Γ' ρ} → Γ ⊢ ρ ∶ Γ' → ρ ⨾ id-ren Γ' ≡ ρ
id-ren-right-id D = id-ren-right-id-list D

------------------------------------------------------------------------
-- §6.5: identity substitution acts trivially on well-typed terms.
------------------------------------------------------------------------

id-sub-action : ∀ {Θ Γ t} → Θ ، Γ ⊢ t → [ id-sub Θ ]ˢ t ≡ t
id-sub-action (wf-var x∈)    = refl
id-sub-action wf-con         = refl
id-sub-action (wf-fun d₁ d₂) =
  cong₂ (fn _) (id-sub-action d₁) (id-sub-action d₂)
id-sub-action {Θ} {Γ = Γ} (wf-meta {X = X} {Γ_X = Γ_X} {ρ = ρ} m wfρ)
  with id-sub Θ !ˢ X | id-sub-lookup {Θ} m
... | just .(mv X (id-ren Γ_X)) | refl =
      cong (mv X) (id-ren-right-id {Γ = Γ} {Γ' = Γ_X} {ρ = ρ} wfρ)

------------------------------------------------------------------------
-- §6.2 / Aux 6.4: σ(X) is well-formed.
--
-- Given Θ ⊢ˢᴸ σ : ms and X⦂[Γ]∈ ms, the lookup σ !ˢ X returns just t
-- with Θ ، Γ ⊢ t.
------------------------------------------------------------------------

sub-lookup-wf :
  ∀ {Θ ms X Γ σ} → Θ ⊢ˢᴸ σ ∶ ms → X ⦂[ Γ ]∈ᴸ ms
  → ∃[ t ] ((σ !ˢ X ≡ just t) × (Θ ، Γ ⊢ t))
sub-lookup-wf {σ = (t , .X) ∷ σ0} (sl-cons _ t-wf _) (m-hereᴸ {X = X}) with X ≟ X
... | yes _  = t , refl , t-wf
... | no  ne = ⊥-elim (ne refl)
sub-lookup-wf {X = X} {σ = (t , Y) ∷ σ0} (sl-cons sub-wf _ Y-fresh)
              (m-thereᴸ m) with X ≟ Y
... | yes refl = ⊥-elim (Y-fresh (member→inFstᴸ m))
... | no  _    = sub-lookup-wf sub-wf m

------------------------------------------------------------------------
-- §6.3: σ action preserves term well-formedness.
------------------------------------------------------------------------

-- §2.3 (renaming composition preserves typing): proved in Renaming.agda
-- via linearity inversion (Aux 2.3b).  Re-exported here.

-- §2.4: renaming action preserves typing.
ren-term : ∀ {Γ Γ' Θ ρ t} → Γ ⊢ ρ ∶ Γ' → Θ ، Γ' ⊢ t → Θ ، Γ ⊢ [ ρ ] t
ren-term {Γ} {Γ'} {Θ} {ρ} wfρ (wf-var x∈)     = wf-var (ren-output-in {Γ} {Γ'} {ρ} wfρ x∈)
ren-term wfρ wf-con           = wf-con
ren-term {Γ} {Γ'} {Θ} {ρ} wfρ (wf-fun d₁ d₂)  =
  wf-fun (ren-term {Γ} {Γ'} {Θ} {ρ} wfρ d₁)
         (ren-term {Γ} {Γ'} {Θ} {ρ} wfρ d₂)
ren-term {Γ} {Γ'} {Θ} {ρ} wfρ (wf-meta {Γ_X = Γ_X} {ρ = ρ'} m wfρ') =
  wf-meta m (ren-comp-wf {Γ} {Γ'} {Γ_X} {ρ} {ρ'} wfρ wfρ')

sub-term : ∀ {Θ Θ' Γ σ t} → Θ ⊢ˢ σ ∶ Θ' → Θ' ، Γ ⊢ t → Θ ، Γ ⊢ [ σ ]ˢ t
sub-term σ-wf (wf-var x∈)     = wf-var x∈
sub-term σ-wf wf-con          = wf-con
sub-term σ-wf (wf-fun d₁ d₂)  = wf-fun (sub-term σ-wf d₁) (sub-term σ-wf d₂)
sub-term {Θ} {Θ'} {Γ} {σ = σ} σ-wf (wf-meta {X = X} {Γ_X = Γ_X} {ρ = ρ} m wfρ)
  with σ !ˢ X | sub-lookup-wf σ-wf m
... | just t  | _ , refl , t-wf = ren-term {Γ} {Γ_X} {Θ} {ρ} wfρ t-wf

------------------------------------------------------------------------
-- §6.6 (sub-comp-wf): composition of substitutions is well-formed.
------------------------------------------------------------------------

-- sub-comp-wf at list level on the RHS for cleaner implicit inference.
sub-comp-wfᴸ :
  ∀ {Θ Θ' σ σ' ms} → Θ ⊢ˢ σ ∶ Θ' → Θ' ⊢ˢᴸ σ' ∶ ms
  → Θ ⊢ˢᴸ (σ ⨾ˢ σ') ∶ ms
sub-comp-wfᴸ σ-wf sl-nil                       = sl-nil
sub-comp-wfᴸ σ-wf (sl-cons σ'-wf t-wf fresh)   =
  sl-cons (sub-comp-wfᴸ σ-wf σ'-wf) (sub-term σ-wf t-wf) fresh

sub-comp-wf : ∀ {Θ Θ' Θ'' σ σ'} → Θ ⊢ˢ σ ∶ Θ' → Θ' ⊢ˢ σ' ∶ Θ''
              → Θ ⊢ˢ (σ ⨾ˢ σ') ∶ Θ''
sub-comp-wf = sub-comp-wfᴸ

------------------------------------------------------------------------
-- Aux 6.6a: lookup of σ-composition.
------------------------------------------------------------------------

just-inj : ∀ {A : Set} {a b : A} → just a ≡ just b → a ≡ b
just-inj refl = refl

sub-comp-lookup-just :
  ∀ {σ σ' X t} → σ' !ˢ X ≡ just t → (σ ⨾ˢ σ') !ˢ X ≡ just ([ σ ]ˢ t)
sub-comp-lookup-just {σ = σ} {σ' = (t' , Y) ∷ σ'0} {X = X} eq with X ≟ Y
... | yes refl rewrite just-inj eq = refl
... | no  _    = sub-comp-lookup-just {σ} {σ'0} eq

sub-comp-lookup-nothing :
  ∀ {σ σ' X} → σ' !ˢ X ≡ nothing → (σ ⨾ˢ σ') !ˢ X ≡ nothing
sub-comp-lookup-nothing {σ' = []} eq = refl
sub-comp-lookup-nothing {σ = σ} {σ' = (t' , Y) ∷ σ'0} {X = X} eq with X ≟ Y
sub-comp-lookup-nothing {σ = σ} {σ' = (t' , Y) ∷ σ'0} {X = X} () | yes _
... | no _ = sub-comp-lookup-nothing {σ} {σ'0} eq

------------------------------------------------------------------------
-- §6.7a: σ-ρ commutation [σ]([ρ]t) = [ρ]([σ]t).
-- (Universal; matches paper Aux 6.7a.)
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Aux 2.3a: lookup of composition under typing.
--
-- We use the explicit-auxiliary-function technique from the Agda
-- with-abstraction docs to side-step the nested-`with` issues.
------------------------------------------------------------------------

-- Helper: head-firing case for the composition lookup.
-- Given ρ ! a ≡ just c, the composition `ρ ⨾ ((a, y) ∷ ρ'-0)` has a
-- head entry `(c, y)`, so looking up `y` returns `just c`.
comp-head-! :
  ∀ {ρ ρ'-0 a y c}
  → ρ ! a ≡ just c
  → (ρ ⨾ ((a , y) ∷ ρ'-0)) ! y ≡ just c
comp-head-! {ρ} {ρ'-0} {a} {y} {c} ρ!a≡c
  with ρ ! a | ρ!a≡c
... | just .c | refl = lookup-head {c} {y} {ρ ⨾ ρ'-0}

-- Helper: skip-firing case for the composition lookup.
-- Given x ≢ y, the head entry of `ρ ⨾ ((a, y) ∷ ρ'-0)` (if any) is at
-- input `y`, so looking up `x` falls through to `(ρ ⨾ ρ'-0) ! x`.
comp-skip-! :
  ∀ {ρ ρ'-0 a y x}
  → x ≢ y
  → (ρ ⨾ ((a , y) ∷ ρ'-0)) ! x ≡ (ρ ⨾ ρ'-0) ! x
comp-skip-! {ρ} {ρ'-0} {a} {y} {x} x≢y with ρ ! a
... | just c   = lookup-cons-≢ {c} {y} {x} {ρ ⨾ ρ'-0} x≢y
... | nothing  = refl

-- Generalised statement: ρ' outputs need only be contained in ρ's input
-- domain (via ⊆ᴸ).  This is what lets the recursive call type-check
-- after wfl-cons inversion: the residual ρ'-0 has outputs in a smaller
-- list, but still ⊆ ρ's input domain.
look-comp-!-typed-gen :
  ∀ {xs xs' xs-ρ'-out xs'' ρ ρ' x b}
  → xs ⊢ᴸ ρ ∶ xs'
  → xs-ρ'-out ⊆ᴸ xs'
  → xs-ρ'-out ⊢ᴸ ρ' ∶ xs''
  → x ∈ᴸ xs''
  → ρ' ! x ≡ just b
  → (ρ ⨾ ρ') ! x ≡ ρ ! b
look-comp-!-typed-gen {ρ = ρ} {ρ' = (a , y) ∷ ρ'-0} {b = b}
                      D sub (wfl-cons rem D' fresh) hereᴸ ρ'y-eq =
  let a≡b : a ≡ b
      a≡b = just-inj (trans (sym (lookup-head {a} {y} {ρ'-0})) ρ'y-eq)
      a-in-xs' = ⊆ᴸ-mono-∈ sub (removeᴸ→memberᴸ rem)
      ρ-def = ren-lookup-definedᴸ D a-in-xs'
      c = proj₁ ρ-def
      ρ!a≡c = proj₂ ρ-def
      step1 : (ρ ⨾ ((a , y) ∷ ρ'-0)) ! y ≡ just c
      step1 = comp-head-! {ρ} {ρ'-0} {a} {y} {c} ρ!a≡c
      step2 : ρ ! b ≡ just c
      step2 = trans (cong (ρ !_) (sym a≡b)) ρ!a≡c
  in trans step1 (sym step2)
look-comp-!-typed-gen {ρ = ρ} {ρ' = (a , y) ∷ ρ'-0} {x = x} {b = b}
                      D sub (wfl-cons rem D' fresh) (thereᴸ m) ρ'x-eq =
  let x≢y : x ≢ y
      x≢y = λ x≡y → fresh (subst (_∈ᴸ _) x≡y m)
      ρ'-0!x-eq : ρ'-0 ! x ≡ just b
      ρ'-0!x-eq = trans (sym (lookup-cons-≢ {a} {y} {x} {ρ'-0} x≢y)) ρ'x-eq
      sub-rest = ⊆ᴸ-trans (removeᴸ→⊆ᴸ rem) sub
      ih : (ρ ⨾ ρ'-0) ! x ≡ ρ ! b
      ih = look-comp-!-typed-gen D sub-rest D' m ρ'-0!x-eq
      step1 : (ρ ⨾ ((a , y) ∷ ρ'-0)) ! x ≡ (ρ ⨾ ρ'-0) ! x
      step1 = comp-skip-! {ρ} {ρ'-0} {a} {y} {x} x≢y
  in trans step1 ih

look-comp-!-typed :
  ∀ {xs xs' xs'' ρ ρ' x b}
  → xs ⊢ᴸ ρ ∶ xs' → xs' ⊢ᴸ ρ' ∶ xs'' → x ∈ᴸ xs'' → ρ' ! x ≡ just b
  → (ρ ⨾ ρ') ! x ≡ ρ ! b
look-comp-!-typed D D' m eq = look-comp-!-typed-gen D ⊆ᴸ-refl D' m eq

------------------------------------------------------------------------
-- Aux 2.6a: associativity of renaming composition (under typing).
------------------------------------------------------------------------

-- (ρ₁ ⨾ ρ₂) ! a is `just c` when ρ₂ ! a = just b and ρ₁ ! b = just c.
-- Aux: head match for `_!_` extracts the output.
just-from-head :
  ∀ {ρ a b b'} → a ≡ b → ((b' , b) ∷ ρ) ! a ≡ just b'
just-from-head {ρ} {a} {b} {b'} a≡b
  with a ≟ b
... | yes _   = refl
... | no  ne  = ⊥-elim (ne a≡b)

comp-!-via :
  ∀ {ρ₁ ρ₂ a b c}
  → ρ₂ ! a ≡ just b → ρ₁ ! b ≡ just c
  → (ρ₁ ⨾ ρ₂) ! a ≡ just c
comp-!-via {ρ₁} {ρ₂ = []} () _
comp-!-via {ρ₁} {ρ₂ = (b' , x) ∷ ρ₂-0} {a = a} {b} {c} ρ₂!a ρ₁!b
  with a ≟ x
... | yes refl
  rewrite lookup-head {b'} {x} {ρ₂-0}
  with ρ₂!a
... | refl = comp-head-! {ρ₁} {ρ₂-0} {b} {x} {c} ρ₁!b
comp-!-via {ρ₁} {ρ₂ = (b' , x) ∷ ρ₂-0} {a} {b} {c} ρ₂!a ρ₁!b | no a≢x
  rewrite lookup-cons-≢ {b'} {x} {a} {ρ₂-0} a≢x =
    -- After rewrite, ρ₂!a : ρ₂-0 ! a ≡ just b.  Apply IH.
    trans (comp-skip-! {ρ₁} {ρ₂-0} {b'} {x} {a} a≢x)
          (comp-!-via {ρ₁} {ρ₂-0} ρ₂!a ρ₁!b)

-- Head case of ⨾-assoc using comp-!-via.
assoc-cons-aux :
  ∀ {ρ₁ ρ₂ ρ₃-0 a x b c}
  → ρ₂ ! a ≡ just b → ρ₁ ! b ≡ just c
  → (ρ₁ ⨾ ρ₂) ⨾ ((a , x) ∷ ρ₃-0) ≡ (c , x) ∷ ((ρ₁ ⨾ ρ₂) ⨾ ρ₃-0)
assoc-cons-aux {ρ₁} {ρ₂} {ρ₃-0} {a} {x} {b} {c} ρ₂!a ρ₁!b
  with (ρ₁ ⨾ ρ₂) ! a | comp-!-via {ρ₁} {ρ₂} {a} {b} {c} ρ₂!a ρ₁!b
... | just .c | refl = refl

-- For ρ₁ ⨾ (ρ₂ ⨾ ((a, x) ∷ ρ₃-0)) when ρ₂ ! a = just b and ρ₁ ! b = just c.
assoc-rhs-aux :
  ∀ {ρ₁ ρ₂ ρ₃-0 a x b c}
  → ρ₂ ! a ≡ just b → ρ₁ ! b ≡ just c
  → ρ₁ ⨾ (ρ₂ ⨾ ((a , x) ∷ ρ₃-0)) ≡ (c , x) ∷ (ρ₁ ⨾ (ρ₂ ⨾ ρ₃-0))
assoc-rhs-aux {ρ₁} {ρ₂} {ρ₃-0} {a} {x} {b} {c} ρ₂!a ρ₁!b
  with ρ₂ ! a | ρ₂!a
... | just .b | refl
  with ρ₁ ! b | ρ₁!b
... | just .c | refl = refl

⨾-assoc-gen :
  ∀ {xs₁ xs₂ xs₃ xs₃-ρ₃-out xs₄ ρ₁ ρ₂ ρ₃}
  → xs₁ ⊢ᴸ ρ₁ ∶ xs₂ → xs₂ ⊢ᴸ ρ₂ ∶ xs₃
  → xs₃-ρ₃-out ⊆ᴸ xs₃
  → xs₃-ρ₃-out ⊢ᴸ ρ₃ ∶ xs₄
  → (ρ₁ ⨾ ρ₂) ⨾ ρ₃ ≡ ρ₁ ⨾ (ρ₂ ⨾ ρ₃)
⨾-assoc-gen D₁ D₂ sub wfl-nil = refl
⨾-assoc-gen {xs₂ = xs₂} {ρ₁ = ρ₁} {ρ₂ = ρ₂} {ρ₃ = (a , x) ∷ ρ₃-0}
            D₁ D₂ sub (wfl-cons rem D₃ fresh) =
  let a-in-xs₃ = ⊆ᴸ-mono-∈ sub (removeᴸ→memberᴸ rem)
      ρ₂-def = ren-lookup-definedᴸ D₂ a-in-xs₃
      b = proj₁ ρ₂-def
      ρ₂!a : ρ₂ ! a ≡ just b
      ρ₂!a = proj₂ ρ₂-def
      look-ρ₂a≡b : look ρ₂ a ≡ b
      look-ρ₂a≡b = look-from-just {ρ₂} {a} {b} ρ₂!a
      b-in-xs₂ : b ∈ᴸ xs₂
      b-in-xs₂ = subst (_∈ᴸ xs₂) look-ρ₂a≡b
                       (ren-output-inᴸ D₂ a-in-xs₃)
      ρ₁-def = ren-lookup-definedᴸ D₁ b-in-xs₂
      c = proj₁ ρ₁-def
      ρ₁!b : ρ₁ ! b ≡ just c
      ρ₁!b = proj₂ ρ₁-def
      lhs : (ρ₁ ⨾ ρ₂) ⨾ ((a , x) ∷ ρ₃-0)
          ≡ (c , x) ∷ ((ρ₁ ⨾ ρ₂) ⨾ ρ₃-0)
      lhs = assoc-cons-aux {ρ₁} {ρ₂} {ρ₃-0} {a} {x} {b} {c} ρ₂!a ρ₁!b
      rhs : ρ₁ ⨾ (ρ₂ ⨾ ((a , x) ∷ ρ₃-0))
          ≡ (c , x) ∷ (ρ₁ ⨾ (ρ₂ ⨾ ρ₃-0))
      rhs = assoc-rhs-aux {ρ₁} {ρ₂} {ρ₃-0} {a} {x} {b} {c} ρ₂!a ρ₁!b
      sub-rest = ⊆ᴸ-trans (removeᴸ→⊆ᴸ rem) sub
      ih : (ρ₁ ⨾ ρ₂) ⨾ ρ₃-0 ≡ ρ₁ ⨾ (ρ₂ ⨾ ρ₃-0)
      ih = ⨾-assoc-gen D₁ D₂ sub-rest D₃
  in trans lhs (trans (cong ((c , x) ∷_) ih) (sym rhs))

⨾-assoc :
  ∀ {Γ₁ Γ₂ Γ₃ Γ₄ ρ₁ ρ₂ ρ₃}
  → Γ₁ ⊢ ρ₁ ∶ Γ₂ → Γ₂ ⊢ ρ₂ ∶ Γ₃ → Γ₃ ⊢ ρ₃ ∶ Γ₄
  → (ρ₁ ⨾ ρ₂) ⨾ ρ₃ ≡ ρ₁ ⨾ (ρ₂ ⨾ ρ₃)
⨾-assoc D₁ D₂ D₃ = ⨾-assoc-gen D₁ D₂ ⊆ᴸ-refl D₃

------------------------------------------------------------------------
-- §2.6: action of a renaming composition on a term.
------------------------------------------------------------------------

⨾-ren-action :
  ∀ {Θ Γ Γ' Γ'' ρ ρ' t}
  → Γ ⊢ ρ ∶ Γ' → Γ' ⊢ ρ' ∶ Γ'' → Θ ، Γ'' ⊢ t
  → [ ρ ] ([ ρ' ] t) ≡ [ ρ ⨾ ρ' ] t
⨾-ren-action {ρ = ρ} {ρ' = ρ'} D D' (wf-var {a = a} x∈) =
  let ρ'-def = ren-lookup-definedᴸ D' x∈
      b = proj₁ ρ'-def
      ρ'!a : ρ' ! a ≡ just b
      ρ'!a = proj₂ ρ'-def
      look-ρ'a-eq : look ρ' a ≡ b
      look-ρ'a-eq = look-from-just {ρ'} {a} {b} ρ'!a
      b-in-Γ' = subst (_∈ᴸ _) look-ρ'a-eq (ren-output-inᴸ D' x∈)
      ρ-def = ren-lookup-definedᴸ D b-in-Γ'
      c = proj₁ ρ-def
      ρ!b : ρ ! b ≡ just c
      ρ!b = proj₂ ρ-def
      comp-!-eq : (ρ ⨾ ρ') ! a ≡ ρ ! b
      comp-!-eq = look-comp-!-typed D D' x∈ ρ'!a
      comp-!-just : (ρ ⨾ ρ') ! a ≡ just c
      comp-!-just = trans comp-!-eq ρ!b
      look-comp-eq : look (ρ ⨾ ρ') a ≡ c
      look-comp-eq = look-from-just {ρ ⨾ ρ'} {a} {c} comp-!-just
      look-ρb-eq : look ρ b ≡ c
      look-ρb-eq = look-from-just {ρ} {b} {c} ρ!b
  in cong vr (trans (trans (cong (look ρ) look-ρ'a-eq) look-ρb-eq)
                    (sym look-comp-eq))
⨾-ren-action D D' wf-con = refl
⨾-ren-action {Θ = Θ} {Γ = Γ} {Γ' = Γ'} {Γ'' = Γ''} {ρ = ρ} {ρ' = ρ'}
             D D' (wf-fun {f = f} {t₁ = t₁} {t₂ = t₂} d₁ d₂) =
  cong₂ (fn f)
    (⨾-ren-action {Θ} {Γ} {Γ'} {Γ''} {ρ} {ρ'} {t₁} D D' d₁)
    (⨾-ren-action {Θ} {Γ} {Γ'} {Γ''} {ρ} {ρ'} {t₂} D D' d₂)
⨾-ren-action {Γ = Γ} {Γ' = Γ'} {Γ'' = Γ''} {ρ = ρ} {ρ' = ρ'}
             D D' (wf-meta {X = X} {Γ_X = Γ_X} {ρ = ρ_x} m wfρ_x) =
  cong (mv X) (sym (⨾-assoc {Γ} {Γ'} {Γ''} {Γ_X} {ρ} {ρ'} {ρ_x} D D' wfρ_x))

------------------------------------------------------------------------
-- Aux 6.7a: σ-ρ commutation [σ]([ρ]t) = [ρ]([σ]t) under typing.
------------------------------------------------------------------------

⨾ˢ-ρ-commute :
  ∀ {Θ Θ' Γ Γ' σ ρ t}
  → Θ ⊢ˢ σ ∶ Θ' → Γ' ⊢ ρ ∶ Γ → Θ' ، Γ ⊢ t
  → [ σ ]ˢ ([ ρ ] t) ≡ [ ρ ] ([ σ ]ˢ t)
⨾ˢ-ρ-commute σ-wf D (wf-var x∈)     = refl
⨾ˢ-ρ-commute σ-wf D wf-con          = refl
⨾ˢ-ρ-commute {Θ = Θ} {Θ' = Θ'} {Γ = Γ} {Γ' = Γ'} {σ = σ} {ρ = ρ}
              σ-wf D (wf-fun {f = f} {t₁ = t₁} {t₂ = t₂} d₁ d₂) =
  cong₂ (fn f)
    (⨾ˢ-ρ-commute {Θ} {Θ'} {Γ} {Γ'} {σ} {ρ} {t₁} σ-wf D d₁)
    (⨾ˢ-ρ-commute {Θ} {Θ'} {Γ} {Γ'} {σ} {ρ} {t₂} σ-wf D d₂)
⨾ˢ-ρ-commute {Θ = Θ} {Γ = Γ} {Γ' = Γ'} {σ = σ} {ρ = ρ}
              σ-wf D (wf-meta {X = X} {Γ_X = Γ_X} {ρ = ρ_x} m wfρ_x)
  with sub-lookup-wf σ-wf m
... | t , σ!X-eq , t-wf
  rewrite σ!X-eq =
    sym (⨾-ren-action {Θ} {Γ'} {Γ} {Γ_X} {ρ} {ρ_x} {t} D wfρ_x t-wf)

------------------------------------------------------------------------
-- §6.7: [σ]ˢ([σ']ˢ t) = [σ ⨾ˢ σ']ˢ t.
-- Requires that t's metavariables fall inside σ' (typing premise).
------------------------------------------------------------------------

⨾ˢ-action :
  ∀ {Θ Θ' Θ'' Γ σ σ' t}
  → Θ ⊢ˢ σ ∶ Θ' → Θ' ⊢ˢ σ' ∶ Θ'' → Θ'' ، Γ ⊢ t
  → [ σ ]ˢ ([ σ' ]ˢ t) ≡ [ σ ⨾ˢ σ' ]ˢ t
⨾ˢ-action σ-wf σ'-wf (wf-var _)     = refl
⨾ˢ-action σ-wf σ'-wf wf-con         = refl
⨾ˢ-action σ-wf σ'-wf (wf-fun d₁ d₂) =
  cong₂ (fn _) (⨾ˢ-action σ-wf σ'-wf d₁) (⨾ˢ-action σ-wf σ'-wf d₂)
⨾ˢ-action {Θ = Θ} {Θ' = Θ'} {Γ = Γ} {σ = σ} {σ' = σ'}
  σ-wf σ'-wf (wf-meta {X = X} {Γ_X = Γ_X} {ρ = ρ} m wfρ)
  with sub-lookup-wf σ'-wf m
... | t , σ'X-eq , t-wf
      rewrite σ'X-eq
            | ⨾ˢ-ρ-commute {Θ} {Θ'} {Γ_X} {Γ} {σ} {ρ} {t}
                            σ-wf wfρ t-wf
            | sub-comp-lookup-just {σ} {σ'} {X} {t} σ'X-eq = refl

------------------------------------------------------------------------
-- ⨾ˢ-assoc and ⨾ˢ-right-id.
--
-- These two are the trickiest of the §6 lemmas because their proofs
-- rely on showing that two Sub lists are structurally equal.  Under
-- typing the lists do agree entrywise.  We expose them postulated
-- here pending a full mechanization of entrywise equality.
------------------------------------------------------------------------

⨾ˢ-assocᴸ :
  ∀ {Θ₁ Θ₂ Θ₃ Θ₄ σ₁ σ₂ σ₃}
  → Θ₁ ⊢ˢ σ₁ ∶ Θ₂ → Θ₂ ⊢ˢ σ₂ ∶ Θ₃ → Θ₃ ⊢ˢᴸ σ₃ ∶ Θ₄
  → (σ₁ ⨾ˢ σ₂) ⨾ˢ σ₃ ≡ σ₁ ⨾ˢ (σ₂ ⨾ˢ σ₃)
⨾ˢ-assocᴸ σ₁-wf σ₂-wf sl-nil = refl
⨾ˢ-assocᴸ {σ₁ = σ₁} {σ₂ = σ₂} σ₁-wf σ₂-wf
         (sl-cons {t = t} {X = X} σ₃-rest-wf t-wf fresh) =
  let head-eq : [ σ₁ ⨾ˢ σ₂ ]ˢ t ≡ [ σ₁ ]ˢ ([ σ₂ ]ˢ t)
      head-eq = sym (⨾ˢ-action σ₁-wf σ₂-wf t-wf)
      ih : (σ₁ ⨾ˢ σ₂) ⨾ˢ _ ≡ σ₁ ⨾ˢ (σ₂ ⨾ˢ _)
      ih = ⨾ˢ-assocᴸ σ₁-wf σ₂-wf σ₃-rest-wf
  in cong₂ _∷_ (cong (_, X) head-eq) ih

⨾ˢ-assoc :
  ∀ {Θ₁ Θ₂ Θ₃ Θ₄ σ₁ σ₂ σ₃}
  → Θ₁ ⊢ˢ σ₁ ∶ Θ₂ → Θ₂ ⊢ˢ σ₂ ∶ Θ₃ → Θ₃ ⊢ˢ σ₃ ∶ Θ₄
  → (σ₁ ⨾ˢ σ₂) ⨾ˢ σ₃ ≡ σ₁ ⨾ˢ (σ₂ ⨾ˢ σ₃)
⨾ˢ-assoc = ⨾ˢ-assocᴸ

------------------------------------------------------------------------
-- ⨾ˢ-right-id: σ ≡ σ ⨾ˢ id-sub Θ' (under Θ ⊢ˢ σ ∶ Θ').
--
-- Helper: under DistinctM Θ' with X ∉Fst Θ', the head-extended σ
-- composes the same way over id-sub Θ' as σ alone (since the X
-- entries are never hit).
------------------------------------------------------------------------

-- Lookup of head-extended sub at Y when Y ≠ X is the inner sub's lookup.
sub-lookup-skip :
  ∀ {σ t X Y} → X ≢ Y → ((t , X) ∷ σ) !ˢ Y ≡ σ !ˢ Y
sub-lookup-skip {σ} {t} {X} {Y} X≢Y with Y ≟ X
... | yes refl = ⊥-elim (X≢Y refl)
... | no  _    = refl

-- Sub-action of head-extended σ at mv Y ρ equals the original σ's action,
-- when X ≠ Y.
sub-action-skip-head :
  ∀ {σ t X Y ρ} → X ≢ Y
  → [ (t , X) ∷ σ ]ˢ (mv Y ρ) ≡ [ σ ]ˢ (mv Y ρ)
sub-action-skip-head {σ} {t} {X} {Y} {ρ} X≢Y
  with Y ≟ X | sub-lookup-skip {σ} {t} {X} {Y} X≢Y
... | yes refl  | _   = ⊥-elim (X≢Y refl)
... | no  _     | eq
  with σ !ˢ Y
... | just t'   = refl
... | nothing   = refl

-- Skip-head for σ ⨾ˢ over id-sub-list of a Θ' not containing X.
⨾ˢ-skip-head-id :
  ∀ {σ t X Θ'}
  → X ∉Fstᴸ Θ'
  → ((t , X) ∷ σ) ⨾ˢ id-sub-list Θ' ≡ σ ⨾ˢ id-sub-list Θ'
⨾ˢ-skip-head-id {Θ' = []} _ = refl
⨾ˢ-skip-head-id {σ} {t} {X} {Θ' = (Y , Γ_Y) ∷ Θ'-0} X∉Θ' =
  let X≢Y : X ≢ Y
      X≢Y = λ X≡Y → X∉Θ' (subst (_∈Fstᴸ _) (sym X≡Y) fst-here)
      head-eq : [ (t , X) ∷ σ ]ˢ (mv Y (id-ren Γ_Y))
              ≡ [ σ ]ˢ (mv Y (id-ren Γ_Y))
      head-eq = sub-action-skip-head {σ} {t} {X} {Y} {id-ren Γ_Y} X≢Y
      ih = ⨾ˢ-skip-head-id {σ} {t} {X} {Θ'-0}
                            (λ X∈Θ'-0 → X∉Θ' (fst-there X∈Θ'-0))
  in cong₂ _∷_ (cong (_, Y) head-eq) ih

-- Compute [σ]ˢ (mv X (id-ren Γ)) when σ has head (t, X).
sub-action-head :
  ∀ {σ t X Γ} → [ (t , X) ∷ σ ]ˢ (mv X (id-ren Γ)) ≡ [ id-ren Γ ] t
sub-action-head {σ} {t} {X} {Γ} with X ≟ X
... | yes _   = refl
... | no  ne  = ⊥-elim (ne refl)

⨾ˢ-right-idᴸ :
  ∀ {Θ Θ' σ}
  → Θ ⊢ˢᴸ σ ∶ Θ' → DistinctM Θ'
  → σ ≡ (σ ⨾ˢ id-sub-list Θ')
⨾ˢ-right-idᴸ sl-nil _ = refl
⨾ˢ-right-idᴸ {Θ = Θ} (sl-cons {Θ' = Θ'} {σ = σ-rest} {t = t} {X = X} {Γ = Γ}
                                σ-rest-wf t-wf X-fresh)
              (dm-cons _ d-Θ') =
  let head-comp : [ (t , X) ∷ σ-rest ]ˢ (mv X (id-ren Γ)) ≡ t
      head-comp = trans (sub-action-head {σ-rest} {t} {X} {Γ})
                        (id-ren-action {Θ} {Γ} t-wf)
      tail-skip : ((t , X) ∷ σ-rest) ⨾ˢ id-sub-list Θ' ≡ σ-rest ⨾ˢ id-sub-list Θ'
      tail-skip = ⨾ˢ-skip-head-id {σ-rest} {t} {X} {Θ'} X-fresh
      tail-ih : σ-rest ≡ σ-rest ⨾ˢ id-sub-list Θ'
      tail-ih = ⨾ˢ-right-idᴸ σ-rest-wf d-Θ'
  in cong₂ _∷_ (cong (_, X) (sym head-comp))
                (trans tail-ih (sym tail-skip))

⨾ˢ-right-id :
  ∀ {Θ Θ' σ} → Θ ⊢ˢ σ ∶ Θ' → σ ≡ (σ ⨾ˢ id-sub Θ')
⨾ˢ-right-id {Θ' = Θ'} D = ⨾ˢ-right-idᴸ D (mnd Θ')

------------------------------------------------------------------------
-- §3 (inverse renamings), Aux 9.0, Aux 9.1 / 9.2 (factorization).
-- These would each take ~100 lines to prove from scratch; postulated
-- here.  We import Coequalizer/Pushout to state the factorization
-- lemmas.
------------------------------------------------------------------------

open import PushoutCoequalizer using (Coequalizer; Pushout)

------------------------------------------------------------------------
-- Typing of the order-aware substitution `mk-replace-subᴸ`.
------------------------------------------------------------------------

-- Helper: distinctness of Θ implies the residual after rml-here is distinct.
distinctM-tail :
  ∀ {X Γ Θ} → DistinctM ((X , Γ) ∷ Θ) → DistinctM Θ
distinctM-tail (dm-cons _ d) = d

-- Removing an element preserves "not in first components".
rml-preserves-∉Fst :
  ∀ {Θ Θ' Y X} → Y ∉Fstᴸ Θ → Θ -ᵐᴸ X ≡ Θ' → Y ∉Fstᴸ Θ'
rml-preserves-∉Fst ne rml-here m              = ne (fst-there m)
rml-preserves-∉Fst ne (rml-there _ D) fst-here     = ne fst-here
rml-preserves-∉Fst ne (rml-there _ D) (fst-there m) =
  rml-preserves-∉Fst (λ m₀ → ne (fst-there m₀)) D m

-- For DistinctM, after removing an element X (= (Y, Γ_Y) entry case),
-- the residual is distinct.
distinctM-remove :
  ∀ {Θ Θ' X} → DistinctM Θ → Θ -ᵐᴸ X ≡ Θ' → DistinctM Θ'
distinctM-remove (dm-cons _ d) rml-here          = d
distinctM-remove (dm-cons fresh d) (rml-there _ D) =
  dm-cons (rml-preserves-∉Fst fresh D) (distinctM-remove d D)

-- For X ⦂[Γ]∈ Θ, the entry persists if Θ -ᵐᴸ Y ≡ Θ' and X ≠ Y.
removal-preserves-mem :
  ∀ {Θ Θ' X Y Γ} → X ≢ Y → X ⦂[ Γ ]∈ᴸ Θ → Θ -ᵐᴸ Y ≡ Θ'
  → X ⦂[ Γ ]∈ᴸ Θ'
removal-preserves-mem X≢Y m-hereᴸ          rml-here          = ⊥-elim (X≢Y refl)
removal-preserves-mem X≢Y m-hereᴸ          (rml-there _ _)   = m-hereᴸ
removal-preserves-mem X≢Y (m-thereᴸ m)     rml-here          = m
removal-preserves-mem X≢Y (m-thereᴸ m)     (rml-there _ D)   =
  m-thereᴸ (removal-preserves-mem X≢Y m D)

-- mwk-mem-via-rml: if Θ -ᵐᴸ X ≡ Θ' and W:[Γ_W]∈ Θ', then W:[Γ_W]∈ Θ.
mwk-via-rml :
  ∀ {Θ Θ' X W Γ_W} → Θ -ᵐᴸ X ≡ Θ' → W ⦂[ Γ_W ]∈ᴸ Θ' → W ⦂[ Γ_W ]∈ᴸ Θ
mwk-via-rml rml-here m                 = m-thereᴸ m
mwk-via-rml (rml-there _ D) m-hereᴸ    = m-hereᴸ
mwk-via-rml (rml-there _ D) (m-thereᴸ m) = m-thereᴸ (mwk-via-rml D m)

-- For any Θ-list with distinctness, id-sub-list on it is well-typed.
-- This generalizes id-sub-wf to start from any "containing" Θ.
id-sub-list-wf-gen :
  ∀ {Θ_outer : MCtx} (sub : List (Name × Ctx))
  → DistinctM sub
  → (∀ {W Γ_W} → W ⦂[ Γ_W ]∈ᴸ sub → W ⦂[ Γ_W ]∈ᴸ mlist Θ_outer)
  → Θ_outer ⊢ˢᴸ id-sub-list sub ∶ sub
id-sub-list-wf-gen []              _              _     = sl-nil
id-sub-list-wf-gen ((X , Γ) ∷ sub) (dm-cons fresh d) embed =
  sl-cons
    (id-sub-list-wf-gen sub d (λ m → embed (m-thereᴸ m)))
    (wf-meta (embed m-hereᴸ) (id-ren-wf {Γ}))
    fresh

-- Helper: distinctness implies X ⦂[..]∈ Θ-tail is incompatible with X-fresh.
dist-no-mem :
  ∀ {X Θ Γ} → X ∉Fstᴸ Θ → X ⦂[ Γ ]∈ᴸ Θ → ⊥
dist-no-mem ne m-hereᴸ        = ne fst-here
dist-no-mem ne (m-thereᴸ m)   = dist-no-mem (λ m₀ → ne (fst-there m₀)) m

-- Distinctness + two memberships of the same metavariable name → equal types.
mem-unique :
  ∀ {X Γ₁ Γ₂ Θ}
  → DistinctM Θ → X ⦂[ Γ₁ ]∈ᴸ Θ → X ⦂[ Γ₂ ]∈ᴸ Θ
  → Γ₁ ≡ Γ₂
mem-unique d m-hereᴸ        m-hereᴸ        = refl
mem-unique (dm-cons fresh _) m-hereᴸ        (m-thereᴸ m₂) =
  ⊥-elim (dist-no-mem fresh m₂)
mem-unique (dm-cons fresh _) (m-thereᴸ m₁) m-hereᴸ        =
  ⊥-elim (dist-no-mem fresh m₁)
mem-unique (dm-cons _ d) (m-thereᴸ m₁) (m-thereᴸ m₂) =
  mem-unique d m₁ m₂

-- If X was removed and W is in the residual, W ≠ X.
removed-not-mem :
  ∀ {Θ Θ_rem X W Γ_W}
  → DistinctM Θ → Θ -ᵐᴸ X ≡ Θ_rem → W ⦂[ Γ_W ]∈ᴸ Θ_rem → W ≢ X
removed-not-mem (dm-cons fresh _) rml-here m W≡X =
  -- m : W ⦂[..]∈ Θ_rem (= Θ-tail).  fresh : X ∉Fst Θ-tail.  W = X.
  fresh (subst (_∈Fstᴸ _) W≡X (member→inFstᴸ m))
removed-not-mem _ (rml-there X≢Y _) m-hereᴸ W≡X =
  -- m-hereᴸ : W=Y, but W=X and X≢Y → contradiction.
  X≢Y (sym W≡X)
removed-not-mem (dm-cons _ d) (rml-there _ D) (m-thereᴸ m) W≡X =
  removed-not-mem d D m W≡X

-- DistinctM is propositional (any two proofs are equal).
-- Since ⊥ in the standard library is defined via Data.Irrelevant
-- (a record with a single irrelevant field), Agda judgementally
-- equates all proofs of ⊥, hence all functions A → ⊥ are equal.
⊥-ext : ∀ {ℓ} {A : Set ℓ} (f g : A → ⊥) → f ≡ g
⊥-ext f g = refl

∉Fstᴸ-prop :
  ∀ {X ms} (p q : X ∉Fstᴸ ms) → p ≡ q
∉Fstᴸ-prop p q = ⊥-ext p q

DistinctM-prop : ∀ {Θ} (d₁ d₂ : DistinctM Θ) → d₁ ≡ d₂
DistinctM-prop dm-nil dm-nil = refl
DistinctM-prop (dm-cons p₁ d₁) (dm-cons p₂ d₂) =
  cong₂ dm-cons (∉Fstᴸ-prop p₁ p₂) (DistinctM-prop d₁ d₂)

-- mk-replace-subᴸ's lookup at X gives the replacement term.
mk-replace-subᴸ-lookup-X :
  ∀ {Θ Θ_rem X t'} (r : Θ -ᵐᴸ X ≡ Θ_rem)
  → mk-replace-subᴸ r t' !ˢ X ≡ just t'
mk-replace-subᴸ-lookup-X {X = X} rml-here with X ≟ X
... | yes _   = refl
... | no  ne  = ⊥-elim (ne refl)
mk-replace-subᴸ-lookup-X {X = X} (rml-there {Y = Y} X≢Y D) with X ≟ Y
... | yes refl = ⊥-elim (X≢Y refl)
... | no  _    = mk-replace-subᴸ-lookup-X D

-- Membership in Θ_rem implies membership in Θ.
mem-in-removed-implies-original :
  ∀ {Θ Θ_rem X W Γ_W} → Θ -ᵐᴸ X ≡ Θ_rem
  → W ⦂[ Γ_W ]∈ᴸ Θ_rem → W ⦂[ Γ_W ]∈ᴸ Θ
mem-in-removed-implies-original rml-here m            = m-thereᴸ m
mem-in-removed-implies-original (rml-there _ _) m-hereᴸ    = m-hereᴸ
mem-in-removed-implies-original (rml-there _ D) (m-thereᴸ m) =
  m-thereᴸ (mem-in-removed-implies-original D m)

-- mk-replace-subᴸ's lookup at any W ∈ Θ_rem (W ≠ X) gives the identity term.
mk-replace-subᴸ-lookup-other :
  ∀ {Θ Θ_rem X W Γ_W t'}
  → DistinctM Θ
  → (r : Θ -ᵐᴸ X ≡ Θ_rem)
  → W ⦂[ Γ_W ]∈ᴸ Θ_rem → W ≢ X
  → mk-replace-subᴸ r t' !ˢ W ≡ just (mv W (id-ren Γ_W))
mk-replace-subᴸ-lookup-other {X = X} {W = W} (dm-cons _ d) rml-here m W≢X with W ≟ X
... | yes refl = ⊥-elim (W≢X refl)
... | no  _    = id-sub-list-lookup d m
mk-replace-subᴸ-lookup-other {X = X} {W = W} d
  (rml-there {Y = Y} {Γ_Y = Γ_Y} X≢Y D) m-hereᴸ W≢X with W ≟ Y
... | yes _    = refl
... | no  ne   = ⊥-elim (ne refl)
mk-replace-subᴸ-lookup-other {X = X} {W = W} (dm-cons Y-fresh d-tail)
  (rml-there {Y = Y} X≢Y D) (m-thereᴸ m) W≢X with W ≟ Y
... | yes refl = ⊥-elim (dist-no-mem Y-fresh (mem-in-removed-implies-original D m))
... | no  _    = mk-replace-subᴸ-lookup-other d-tail D m W≢X

-- mk-replace-subᴸ has the expected typing.
-- Helper: under DistinctM Θ-list, removing X gives a remainder where X is fresh.
rml-X-fresh-rem :
  ∀ {Θ-list Θ-rem X} → DistinctM Θ-list → Θ-list -ᵐᴸ X ≡ Θ-rem → X ∉Fstᴸ Θ-rem
rml-X-fresh-rem (dm-cons X∉ _) rml-here = X∉
rml-X-fresh-rem (dm-cons Y∉ d) (rml-there X≢Y D) fst-here =
  X≢Y refl
rml-X-fresh-rem (dm-cons Y∉ d) (rml-there X≢Y D) (fst-there m) =
  rml-X-fresh-rem d D m

-- List-level core: given the underlying list and its distinctness, the
-- replacement substitution is well-typed.  We then wrap this for the
-- MCtx interface.
mk-replace-subᴸ-wf-core :
  ∀ {Θ-list Θ-rem-list X Γ_X t' Θ_out}
  → DistinctM Θ-list
  → (r : Θ-list -ᵐᴸ X ≡ Θ-rem-list)
  → mlist Θ_out ⊇ᴸ Θ-rem-list
  → Θ_out ، Γ_X ⊢ t'
  → X ⦂[ Γ_X ]∈ᴸ Θ-list
  → Θ_out ⊢ˢᴸ mk-replace-subᴸ r t' ∶ Θ-list
mk-replace-subᴸ-wf-core {Θ-rem-list = Θ-rem-list} {X = X} {Γ_X = Γ_X} {t' = t'}
                         d-list rml-here sub wf-t m-hereᴸ =
  let X∉Θ-rem : X ∉Fstᴸ Θ-rem-list
      X∉Θ-rem = rml-X-fresh-rem d-list rml-here
      d-rem : DistinctM Θ-rem-list
      d-rem = distinctM-tail d-list
      id-sub-wf-stmt =
        id-sub-list-wf-gen Θ-rem-list d-rem
          (λ {W} {Γ_W} m → mwk-memᴸ sub m)
  in sl-cons id-sub-wf-stmt wf-t X∉Θ-rem
mk-replace-subᴸ-wf-core d-list rml-here _ _ (m-thereᴸ m) =
  -- mlist Θ = (X, Γ_X) ∷ Θ_rem-list but the explicit witness says m-thereᴸ,
  -- contradicting DistinctM at the head.
  ⊥-elim (dist-no-mem (case d-list of λ where (dm-cons X∉ _) → X∉)
                       (subst (_ ⦂[ _ ]∈ᴸ_) refl m))
  where open import Function using (case_of_)
mk-replace-subᴸ-wf-core {X = X} {Γ_X = Γ_X} d-list
                         (rml-there {Y = Y} {Γ_Y = Γ_Y} X≢Y D) sub wf-t m-hereᴸ =
  -- X = Y contradiction.
  ⊥-elim (X≢Y refl)
mk-replace-subᴸ-wf-core {X = X} {Γ_X = Γ_X} (dm-cons Y∉ d-tail)
                         (rml-there {Y = Y} {Γ_Y = Γ_Y} X≢Y D) sub wf-t (m-thereᴸ m) =
  let sub-tail = ⊇ᴸ-skip-head sub
      ih = mk-replace-subᴸ-wf-core d-tail D sub-tail wf-t m
      Y-wf : _ ، Γ_Y ⊢ mv Y (id-ren Γ_Y)
      Y-wf = wf-meta (⊇ᴸ-head-mem sub) (id-ren-wf {Γ_Y})
  in sl-cons ih Y-wf Y∉
  where
    -- Skip the head of the codomain when the head is in mlist Θ_out.
    ⊇ᴸ-skip-head :
      ∀ {Θ-out-list Y Γ_Y Θ-rem-tail}
      → Θ-out-list ⊇ᴸ ((Y , Γ_Y) ∷ Θ-rem-tail)
      → Θ-out-list ⊇ᴸ Θ-rem-tail
    ⊇ᴸ-skip-head (wkl-cons s) = wkl-skip s
    ⊇ᴸ-skip-head (wkl-skip s) = wkl-skip (⊇ᴸ-skip-head s)

    ⊇ᴸ-head-mem :
      ∀ {Θ-out-list Y Γ_Y Θ-rem-tail}
      → Θ-out-list ⊇ᴸ ((Y , Γ_Y) ∷ Θ-rem-tail)
      → Y ⦂[ Γ_Y ]∈ᴸ Θ-out-list
    ⊇ᴸ-head-mem (wkl-cons _)  = m-hereᴸ
    ⊇ᴸ-head-mem (wkl-skip s)  = m-thereᴸ (⊇ᴸ-head-mem s)

-- MCtx-interface wrapper.
mk-replace-subᴸ-wf :
  ∀ {Θ X Γ_X t' Θ_out Θ_rem-list}
  → (r : mlist Θ -ᵐᴸ X ≡ Θ_rem-list)
  → mlist Θ_out ⊇ᴸ Θ_rem-list
  → Θ_out ، Γ_X ⊢ t'
  → X ⦂[ Γ_X ]∈ᴸ mlist Θ
  → Θ_out ⊢ˢᴸ mk-replace-subᴸ r t' ∶ mlist Θ
mk-replace-subᴸ-wf {Θ = Θ} = mk-replace-subᴸ-wf-core (mnd Θ)

-- Inverse-related lemmas (ren-inv-wfᴸ, range-distinctᴸ, ren-inv-wf,
-- ρ!-output-in-codomain, inv-look-from-look, prepend-comp-eq,
-- ⨾-cons-head-step, inv-comp-id-!, comp-inv-id-!, ρ⁻¹-look-of-ρ-look,
-- ρ!-input-in-domain, inv-of-inv-look-from-look, ρ-look-of-ρ⁻¹-look,
-- just-injective, look-injective-on-dom) have been moved to Renaming.agda
-- so that PushoutCoequalizer.agda can use them.  They are re-exported
-- here via `open import Renaming` at the top of this file.

------------------------------------------------------------------------
-- Aux 3.2a: round-trip on terms.  We unify the structure with ⨾-action.
------------------------------------------------------------------------

-- (ρ⁻¹ ⨾ ρ) ⨾ ρ_x ≡ ρ_x for ρ_x typed at Γ'.
inv-comp-on-σ :
  ∀ {Γ Γ' Γ_X ρ ρ_x}
  → Γ ⊢ ρ ∶ Γ' → Γ' ⊢ ρ_x ∶ Γ_X
  → (ρ ⁻¹ ⨾ ρ) ⨾ ρ_x ≡ ρ_x
inv-comp-on-σ {Γ = Γ-out} {Γ' = Γ-mid} {Γ_X = Γ_X} {ρ = ρ} {ρ_x = ρ_x} D D-x =
  let
    agree :
      ∀ a → a ∈ᴸ range ρ_x → (ρ ⁻¹ ⨾ ρ) ! a ≡ id-ren-list (list Γ-mid) ! a
    agree a a∈range =
      let a-in-Γ-mid = ren-output-inᴸ-range D-x a∈range
          lhs = inv-comp-id-! (nd Γ-out) D a-in-Γ-mid
          rhs = id-ren-list-lookup {list Γ-mid} {a} a-in-Γ-mid
      in trans lhs (sym rhs)
    step1 : (ρ ⁻¹ ⨾ ρ) ⨾ ρ_x ≡ id-ren Γ-mid ⨾ ρ_x
    step1 = ⨾-cong-lookup agree
    step2 : id-ren Γ-mid ⨾ ρ_x ≡ ρ_x
    step2 = id-ren-left-id-direct {Γ-mid} {Γ_X} {ρ_x} D-x
  in trans step1 step2

inv-comp-on-σ-right :
  ∀ {Γ Γ' Γ_inv Γ_X ρ ρ_x}
  → Γ ⊢ ρ ∶ Γ' → Γ' ⊢ ρ ⁻¹ ∶ Γ_inv → Γ_inv ⊢ ρ_x ∶ Γ_X
  → (ρ ⨾ ρ ⁻¹) ⨾ ρ_x ≡ ρ_x
inv-comp-on-σ-right {Γ = Γ-out} {Γ' = Γ-mid} {Γ_inv = Γ-inv} {Γ_X = Γ_X}
                    {ρ = ρ} {ρ_x = ρ_x} D D-inv D-x =
  let
    agree :
      ∀ a → a ∈ᴸ range ρ_x → (ρ ⨾ ρ ⁻¹) ! a ≡ id-ren-list (list Γ-inv) ! a
    agree a a∈range =
      let a-in-Γ-inv = ren-output-inᴸ-range D-x a∈range
          a-in-range-ρ : a ∈ᴸ range ρ
          a-in-range-ρ =
            ρ⁻¹-input-in-range D-inv a-in-Γ-inv
          lhs = comp-inv-id-! (nd Γ-out) D a-in-range-ρ
          rhs = id-ren-list-lookup {list Γ-inv} {a} a-in-Γ-inv
      in trans lhs (sym rhs)
    step1 : (ρ ⨾ ρ ⁻¹) ⨾ ρ_x ≡ id-ren Γ-inv ⨾ ρ_x
    step1 = ⨾-cong-lookup agree
    step2 : id-ren Γ-inv ⨾ ρ_x ≡ ρ_x
    step2 = id-ren-left-id-direct {Γ-inv} {Γ_X} {ρ_x} D-x
  in trans step1 step2
  where
    -- Inputs of ρ⁻¹ (in its domain) come from range ρ. Equivalently, the
    -- codomain side of ρ⁻¹ is the range of ρ.
    -- ρ⁻¹ : Γ' ⊢ ρ⁻¹ ∶ Γ_inv. Γ_inv as a list is range ρ.
    -- So a ∈ list Γ_inv → a ∈ range ρ.
    ρ⁻¹-input-in-range :
      ∀ {xs xs' ρ a} → xs ⊢ᴸ ρ ⁻¹ ∶ xs' → a ∈ᴸ xs' → a ∈ᴸ range ρ
    ρ⁻¹-input-in-range {ρ = []} wfl-nil ()
    ρ⁻¹-input-in-range {ρ = (a₀ , x₀) ∷ ρ-0} (wfl-cons _ D' _) hereᴸ = hereᴸ
    ρ⁻¹-input-in-range {ρ = (a₀ , x₀) ∷ ρ-0} (wfl-cons _ D' _) (thereᴸ m) =
      thereᴸ (ρ⁻¹-input-in-range D' m)

ren-inv-round-trip-left :
  ∀ {Θ Γ Γ' ρ t}
  → Γ ⊢ ρ ∶ Γ' → Θ ، Γ' ⊢ t
  → [ ρ ⁻¹ ] ([ ρ ] t) ≡ t
ren-inv-round-trip-left {Γ = Γ} D (wf-var a∈) =
  cong vr (ρ⁻¹-look-of-ρ-look (nd Γ) D a∈)
ren-inv-round-trip-left _ wf-con = refl
ren-inv-round-trip-left {Θ = Θ} {Γ = Γ} {Γ' = Γ'} {ρ = ρ}
                         D (wf-fun {f = f} {t₁ = t₁} {t₂ = t₂} d₁ d₂) =
  cong₂ (fn f) (ren-inv-round-trip-left {Θ} {Γ} {Γ'} {ρ} {t₁} D d₁)
                (ren-inv-round-trip-left {Θ} {Γ} {Γ'} {ρ} {t₂} D d₂)
ren-inv-round-trip-left {Γ = Γ} {Γ' = Γ'} {ρ = ρ} D
                        (wf-meta {X = X} {Γ_X = Γ_X} {ρ = ρ_x} m wfρ_x) =
  let Γ-range = mkCtx (range ρ) (range-distinctᴸ (nd Γ) D)
      inv-wf : Γ' ⊢ (ρ ⁻¹) ∶ Γ-range
      inv-wf = ren-inv-wfᴸ (nd Γ) D
      D-restricted : Γ-range ⊢ ρ ∶ Γ'
      D-restricted = restrict-codom-to-rangeᴸ D
      assoc : ((ρ ⁻¹) ⨾ ρ) ⨾ ρ_x ≡ (ρ ⁻¹) ⨾ (ρ ⨾ ρ_x)
      assoc = ⨾-assoc {Γ'} {Γ-range} {Γ'} {Γ_X} {ρ ⁻¹} {ρ} {ρ_x}
                       inv-wf D-restricted wfρ_x
      inv-comp : ((ρ ⁻¹) ⨾ ρ) ⨾ ρ_x ≡ ρ_x
      inv-comp = inv-comp-on-σ {Γ} {Γ'} {Γ_X} {ρ} {ρ_x} D wfρ_x
  in cong (mv X) (trans (sym assoc) inv-comp)

ren-inv-round-trip-right :
  ∀ {Θ Γ Γ' Γ_inv ρ t}
  → Γ ⊢ ρ ∶ Γ' → Γ' ⊢ ρ ⁻¹ ∶ Γ_inv
  → Θ ، Γ_inv ⊢ t
  → [ ρ ] ([ ρ ⁻¹ ] t) ≡ t
ren-inv-round-trip-right {Γ = Γ} D D-inv (wf-var a∈) =
  let a-in-range : _ ∈ᴸ range _
      a-in-range = inv-codom-from-typing D-inv a∈
  in cong vr (ρ-look-of-ρ⁻¹-look (nd Γ) D a-in-range)
  where
    inv-codom-from-typing :
      ∀ {xs xs' ρ a} → xs ⊢ᴸ ρ ⁻¹ ∶ xs' → a ∈ᴸ xs' → a ∈ᴸ range ρ
    inv-codom-from-typing {ρ = []} wfl-nil ()
    inv-codom-from-typing {ρ = (c , y) ∷ ρ-0} (wfl-cons _ D' _) hereᴸ = hereᴸ
    inv-codom-from-typing {ρ = (c , y) ∷ ρ-0} (wfl-cons _ D' _) (thereᴸ m) =
      thereᴸ (inv-codom-from-typing D' m)
ren-inv-round-trip-right _ _ wf-con = refl
ren-inv-round-trip-right {Θ = Θ} {Γ = Γ} {Γ' = Γ'} {Γ_inv = Γ_inv} {ρ = ρ}
                          D D-inv (wf-fun {f = f} {t₁ = t₁} {t₂ = t₂} d₁ d₂) =
  cong₂ (fn f) (ren-inv-round-trip-right {Θ} {Γ} {Γ'} {Γ_inv} {ρ} {t₁} D D-inv d₁)
                (ren-inv-round-trip-right {Θ} {Γ} {Γ'} {Γ_inv} {ρ} {t₂} D D-inv d₂)
ren-inv-round-trip-right {Γ = Γ} {Γ' = Γ'} {Γ_inv = Γ_inv} {ρ = ρ} D D-inv
                          (wf-meta {X = X} {Γ_X = Γ_X} {ρ = ρ_x} m wfρ_x) =
  let assoc : (ρ ⨾ (ρ ⁻¹)) ⨾ ρ_x ≡ ρ ⨾ ((ρ ⁻¹) ⨾ ρ_x)
      assoc = ⨾-assoc {Γ} {Γ'} {Γ_inv} {Γ_X} {ρ} {ρ ⁻¹} {ρ_x} D D-inv wfρ_x
      inv-comp : (ρ ⨾ (ρ ⁻¹)) ⨾ ρ_x ≡ ρ_x
      inv-comp = inv-comp-on-σ-right {Γ} {Γ'} {Γ_inv} {Γ_X} {ρ} {ρ_x}
                                      D D-inv wfρ_x
  in cong (mv X) (trans (sym assoc) inv-comp)

------------------------------------------------------------------------
-- Aux 9.1, 9.2 (term factorization through coeq/pushout).
--
-- The variable case requires showing that the equalizing variable lies
-- in the image of the i-renaming.  This is an algorithmic property of
-- the coequalizer/pushout construction and is the only point we leave
-- postulated for the term factorizations.
------------------------------------------------------------------------

-- Aux: ∈ implies removability.
∈→removability :
  ∀ {a xs} → a ∈ᴸ xs → ∃[ ys ] (xs -ᴸ a ≡ ys)
∈→removability {a} {x ∷ xs} m with a ≟ x
... | yes refl = xs , rem-hereᴸ
... | no a≢x with m
... | hereᴸ = ⊥-elim (a≢x refl)
... | thereᴸ {xs = xs} m' =
        let ys , rem = ∈→removability {a} {xs} m'
        in x ∷ ys , rem-thereᴸ a≢x rem

-- Aux: cons injectivity for Ren entries.
ren-cons-inj-out :
  ∀ {a₁ x₁ a₂ x₂ : Name} {ρ₁ ρ₂ : Ren}
  → ((a₁ , x₁) ∷ ρ₁) ≡ ((a₂ , x₂) ∷ ρ₂) → a₁ ≡ a₂
ren-cons-inj-out refl = refl

ren-cons-inj-in :
  ∀ {a₁ x₁ a₂ x₂ : Name} {ρ₁ ρ₂ : Ren}
  → ((a₁ , x₁) ∷ ρ₁) ≡ ((a₂ , x₂) ∷ ρ₂) → x₁ ≡ x₂
ren-cons-inj-in refl = refl

-- coeq-var-preimage proved via the universal property using a
-- singleton renaming.
coeq-var-preimage :
  ∀ {Γ Γ_X ρ₁ ρ₂} {a : Name}
  → Γ ⊢ ρ₁ ∶ Γ_X → Γ ⊢ ρ₂ ∶ Γ_X
  → (coeq : Coequalizer Γ ρ₁ ρ₂ Γ_X)
  → a ∈ Γ_X
  → look ρ₁ a ≡ look ρ₂ a
  → ∃[ a' ] ((a' ∈ Coequalizer.Γ'' coeq) × (look (Coequalizer.i coeq) a' ≡ a))
coeq-var-preimage {Γ_X = Γ_X} {ρ₁ = ρ₁} {ρ₂ = ρ₂} {a = a} D₁ D₂ coeq a∈ look-eq =
  let Δ : Ctx
      Δ = mkCtx (0 ∷ []) (d-cons (λ ()) d-nil)
      ys-rem = ∈→removability {a} {list Γ_X} a∈
      j-wf : Γ_X ⊢ ((a , 0) ∷ []) ∶ Δ
      j-wf = wfl-cons (proj₂ ys-rem) wfl-nil (λ ())
      ρ₁!a-def = ren-lookup-definedᴸ D₁ a∈
      b₁ = proj₁ ρ₁!a-def
      ρ₁!a≡b₁ = proj₂ ρ₁!a-def
      ρ₂!a-def = ren-lookup-definedᴸ D₂ a∈
      b₂ = proj₁ ρ₂!a-def
      ρ₂!a≡b₂ = proj₂ ρ₂!a-def
      -- look ρ₁ a = b₁ and look ρ₂ a = b₂, equation gives b₁ ≡ b₂.
      look-ρ₁-eq : look ρ₁ a ≡ b₁
      look-ρ₁-eq = look-from-just {ρ₁} {a} {b₁} ρ₁!a≡b₁
      look-ρ₂-eq : look ρ₂ a ≡ b₂
      look-ρ₂-eq = look-from-just {ρ₂} {a} {b₂} ρ₂!a≡b₂
      b₁≡b₂ : b₁ ≡ b₂
      b₁≡b₂ = trans (sym look-ρ₁-eq) (trans look-eq look-ρ₂-eq)
      -- Compute ρ₁ ⨾ ((a, 0) ∷ []) and ρ₂ ⨾ ((a, 0) ∷ []).
      ρ₁-step : ρ₁ ⨾ ((a , 0) ∷ []) ≡ (b₁ , 0) ∷ []
      ρ₁-step = ⨾-cons-head-step {ρ₁} {a} {0} {[]} {b₁} ρ₁!a≡b₁
      ρ₂-step : ρ₂ ⨾ ((a , 0) ∷ []) ≡ (b₂ , 0) ∷ []
      ρ₂-step = ⨾-cons-head-step {ρ₂} {a} {0} {[]} {b₂} ρ₂!a≡b₂
      ρ-j-eq : ρ₁ ⨾ ((a , 0) ∷ []) ≡ ρ₂ ⨾ ((a , 0) ∷ [])
      ρ-j-eq = trans ρ₁-step
                (trans (cong (λ b → (b , 0) ∷ []) b₁≡b₂)
                       (sym ρ₂-step))
      univ = Coequalizer.universal coeq {Δ = Δ} {j = (a , 0) ∷ []} j-wf ρ-j-eq
      j' = proj₁ univ
      wf-j' = proj₁ (proj₂ univ)
      j-decomp-eq : (a , 0) ∷ [] ≡ Coequalizer.i coeq ⨾ j'
      j-decomp-eq = proj₂ (proj₂ univ)
      Γ'' = Coequalizer.Γ'' coeq
      i = Coequalizer.i coeq
      -- j' is a singleton: from wf-j' : Γ'' ⊢ j' ∶ Δ, j' must have form
      -- (a', 0) ∷ []. We extract a'.
      sing = singleton-extractᴸ {xs = list (Coequalizer.Γ'' coeq)}
                                  {Δ-elem = 0} {j' = j'} wf-j'
      a' = proj₁ sing
      a'∈Γ'' = proj₁ (proj₂ sing)
      j'-shape = proj₂ (proj₂ sing)
      -- Compute i ⨾ j' = (look-i-result, 0) ∷ [].
      i!a'-def = ren-lookup-definedᴸ (Coequalizer.wf-i coeq) a'∈Γ''
      b' = proj₁ i!a'-def
      i!a'≡b' = proj₂ i!a'-def
      look-i-eq : look i a' ≡ b'
      look-i-eq = look-from-just {i} {a'} {b'} i!a'≡b'
      i-step : i ⨾ ((a' , 0) ∷ []) ≡ (b' , 0) ∷ []
      i-step = ⨾-cons-head-step {i} {a'} {0} {[]} {b'} i!a'≡b'
      i-comp-eq : i ⨾ j' ≡ (b' , 0) ∷ []
      i-comp-eq = trans (cong (i ⨾_) j'-shape) i-step
      -- (a, 0) ∷ [] ≡ (b', 0) ∷ [], so a ≡ b'.
      cons-eq : (a , 0) ∷ [] ≡ (b' , 0) ∷ []
      cons-eq = trans j-decomp-eq i-comp-eq
      a≡b' : a ≡ b'
      a≡b' = ren-cons-inj-out cons-eq
  in a' , a'∈Γ'' , trans look-i-eq (sym a≡b')
  where
    -- j' is a singleton renaming with domain a single name Δ-elem.
    -- This works at the list level so we sidestep the Distinct-proof
    -- equality issue.
    singleton-extractᴸ :
      ∀ {xs : List Name} {Δ-elem : Name} {j' : Ren}
      → xs ⊢ᴸ j' ∶ (Δ-elem ∷ [])
      → ∃[ a' ] ((a' ∈ᴸ xs) × (j' ≡ (a' , Δ-elem) ∷ []))
    singleton-extractᴸ {Δ-elem = Δ-elem}
      (wfl-cons {a = a'} {x = x} rem wfl-nil _) =
        a' , removeᴸ→memberᴸ rem , refl

    singleton-extract :
      ∀ {Γ-x : Ctx} {Δ-elem : Name} {j' : Ren}
      → Γ-x ⊢ j' ∶ mkCtx (Δ-elem ∷ []) (d-cons (λ ()) d-nil)
      → ∃[ a' ] ((a' ∈ Γ-x) × (j' ≡ (a' , Δ-elem) ∷ []))
    singleton-extract wf = singleton-extractᴸ wf

-- Aux 9.1: term factorization through the coequalizer.
term-coeq-factor :
  ∀ {Γ Γ_X ρ₁ ρ₂ Θ u}
  → Γ ⊢ ρ₁ ∶ Γ_X → Γ ⊢ ρ₂ ∶ Γ_X
  → (coeq : Coequalizer Γ ρ₁ ρ₂ Γ_X)
  → Θ ، Γ_X ⊢ u → [ ρ₁ ] u ≡ [ ρ₂ ] u
  → ∃[ u' ] ((Θ ، Coequalizer.Γ'' coeq ⊢ u')
            × ([ Coequalizer.i coeq ] u' ≡ u))
term-coeq-factor {ρ₁ = ρ₁} {ρ₂ = ρ₂} D₁ D₂ coeq (wf-var {a = a} a∈) eq =
  let look-eq : look ρ₁ a ≡ look ρ₂ a
      look-eq = vr-inj eq
      pre = coeq-var-preimage {ρ₁ = ρ₁} {ρ₂ = ρ₂} {a = a} D₁ D₂ coeq a∈ look-eq
      a' = proj₁ pre
      a'-in-Γ'' = proj₁ (proj₂ pre)
      look-i-eq = proj₂ (proj₂ pre)
  in vr a' , wf-var a'-in-Γ'' , cong vr look-i-eq
  where
    vr-inj : ∀ {a b} → vr a ≡ vr b → a ≡ b
    vr-inj refl = refl
term-coeq-factor _ _ _ wf-con _ = cn _ , wf-con , refl
term-coeq-factor D₁ D₂ coeq (wf-fun {f = f} d₁ d₂) eq =
  let eq₁ = fn-inj₁ eq
      eq₂ = fn-inj₂ eq
      r₁ = term-coeq-factor D₁ D₂ coeq d₁ eq₁
      r₂ = term-coeq-factor D₁ D₂ coeq d₂ eq₂
      u₁' = proj₁ r₁ ; wf₁' = proj₁ (proj₂ r₁) ; eq₁' = proj₂ (proj₂ r₁)
      u₂' = proj₁ r₂ ; wf₂' = proj₁ (proj₂ r₂) ; eq₂' = proj₂ (proj₂ r₂)
  in fn f u₁' u₂' , wf-fun wf₁' wf₂' , cong₂ (fn f) eq₁' eq₂'
  where
    fn-inj₁ : ∀ {f t₁ t₂ t₁' t₂'} → fn f t₁ t₂ ≡ fn f t₁' t₂' → t₁ ≡ t₁'
    fn-inj₁ refl = refl
    fn-inj₂ : ∀ {f t₁ t₂ t₁' t₂'} → fn f t₁ t₂ ≡ fn f t₁' t₂' → t₂ ≡ t₂'
    fn-inj₂ refl = refl
term-coeq-factor {Γ = Γ} {Γ_X = Γ_X} {ρ₁ = ρ₁} {ρ₂ = ρ₂} D₁ D₂ coeq
                 (wf-meta {X = X} {Γ_X = Γ_Xm} {ρ = ρ_x} m wfρ_x) eq =
  let comp-eq : ρ₁ ⨾ ρ_x ≡ ρ₂ ⨾ ρ_x
      comp-eq = mv-comp-inj eq
      univ = Coequalizer.universal coeq {Δ = Γ_Xm} {j = ρ_x} wfρ_x comp-eq
      q' = proj₁ univ
      wf-q' = proj₁ (proj₂ univ)
      ρ-x-eq = proj₂ (proj₂ univ)
  in mv X q' , wf-meta m wf-q' , cong (mv X) (sym ρ-x-eq)
  where
    mv-comp-inj :
      ∀ {X ρ₁' ρ₂'} → mv X ρ₁' ≡ mv X ρ₂' → ρ₁' ≡ ρ₂'
    mv-comp-inj refl = refl

------------------------------------------------------------------------
-- Aux 9.2: term factorization through the pushout.
------------------------------------------------------------------------

-- For the var case: if [ρ₁](vr a_X) ≡ [ρ₂](vr a_Y), there is a_Z ∈ Γ₃
-- whose images under i₁ / i₂ recover a_X / a_Y.  Proved by invoking the
-- pushout universal property with singleton renamings.
pushout-var-preimage :
  ∀ {Γ Γ_X Γ_Y ρ₁ ρ₂} {a_X a_Y : Name}
  → Γ ⊢ ρ₁ ∶ Γ_X → Γ ⊢ ρ₂ ∶ Γ_Y
  → (push : Pushout Γ ρ₁ ρ₂ Γ_X Γ_Y)
  → a_X ∈ Γ_X → a_Y ∈ Γ_Y → look ρ₁ a_X ≡ look ρ₂ a_Y
  → ∃[ a_Z ] ((a_Z ∈ Pushout.Γ₃ push)
            × (look (Pushout.i₁ push) a_Z ≡ a_X)
            × (look (Pushout.i₂ push) a_Z ≡ a_Y))
pushout-var-preimage {Γ_X = Γ_X} {Γ_Y = Γ_Y} {ρ₁ = ρ₁} {ρ₂ = ρ₂}
                      {a_X = a_X} {a_Y = a_Y} D₁ D₂ push aX∈ aY∈ look-eq =
  let Δ : Ctx
      Δ = mkCtx (0 ∷ []) (d-cons (λ ()) d-nil)
      remX = ∈→removability {a_X} {list Γ_X} aX∈
      remY = ∈→removability {a_Y} {list Γ_Y} aY∈
      q₁-wf : Γ_X ⊢ ((a_X , 0) ∷ []) ∶ Δ
      q₁-wf = wfl-cons (proj₂ remX) wfl-nil (λ ())
      q₂-wf : Γ_Y ⊢ ((a_Y , 0) ∷ []) ∶ Δ
      q₂-wf = wfl-cons (proj₂ remY) wfl-nil (λ ())
      ρ₁!aX-def = ren-lookup-definedᴸ D₁ aX∈
      b₁ = proj₁ ρ₁!aX-def
      ρ₁!aX≡b₁ = proj₂ ρ₁!aX-def
      ρ₂!aY-def = ren-lookup-definedᴸ D₂ aY∈
      b₂ = proj₁ ρ₂!aY-def
      ρ₂!aY≡b₂ = proj₂ ρ₂!aY-def
      look-ρ₁-eq : look ρ₁ a_X ≡ b₁
      look-ρ₁-eq = look-from-just {ρ₁} {a_X} {b₁} ρ₁!aX≡b₁
      look-ρ₂-eq : look ρ₂ a_Y ≡ b₂
      look-ρ₂-eq = look-from-just {ρ₂} {a_Y} {b₂} ρ₂!aY≡b₂
      b₁≡b₂ : b₁ ≡ b₂
      b₁≡b₂ = trans (sym look-ρ₁-eq) (trans look-eq look-ρ₂-eq)
      ρ₁-step : ρ₁ ⨾ ((a_X , 0) ∷ []) ≡ (b₁ , 0) ∷ []
      ρ₁-step = ⨾-cons-head-step {ρ₁} {a_X} {0} {[]} {b₁} ρ₁!aX≡b₁
      ρ₂-step : ρ₂ ⨾ ((a_Y , 0) ∷ []) ≡ (b₂ , 0) ∷ []
      ρ₂-step = ⨾-cons-head-step {ρ₂} {a_Y} {0} {[]} {b₂} ρ₂!aY≡b₂
      ρ-q-eq : ρ₁ ⨾ ((a_X , 0) ∷ []) ≡ ρ₂ ⨾ ((a_Y , 0) ∷ [])
      ρ-q-eq = trans ρ₁-step
                (trans (cong (λ b → (b , 0) ∷ []) b₁≡b₂)
                       (sym ρ₂-step))
      univ = Pushout.universal push {Δ = Δ}
                                {q₁ = (a_X , 0) ∷ []}
                                {q₂ = (a_Y , 0) ∷ []}
                                q₁-wf q₂-wf ρ-q-eq
      q' = proj₁ univ
      wf-q' = proj₁ (proj₂ univ)
      q₁-decomp = proj₁ (proj₂ (proj₂ univ))
      q₂-decomp = proj₂ (proj₂ (proj₂ univ))
      Γ₃ = Pushout.Γ₃ push
      i₁ = Pushout.i₁ push
      i₂ = Pushout.i₂ push
      sing = singleton-extractᴸ-p {xs = list Γ₃} {Δ-elem = 0} {j' = q'} wf-q'
      a_Z = proj₁ sing
      aZ∈Γ₃ = proj₁ (proj₂ sing)
      q'-shape = proj₂ (proj₂ sing)
      i₁!aZ-def = ren-lookup-definedᴸ (Pushout.wf-i₁ push) aZ∈Γ₃
      c₁ = proj₁ i₁!aZ-def
      i₁!aZ≡c₁ = proj₂ i₁!aZ-def
      i₁-step : i₁ ⨾ ((a_Z , 0) ∷ []) ≡ (c₁ , 0) ∷ []
      i₁-step = ⨾-cons-head-step {i₁} {a_Z} {0} {[]} {c₁} i₁!aZ≡c₁
      i₁-comp-eq : i₁ ⨾ q' ≡ (c₁ , 0) ∷ []
      i₁-comp-eq = trans (cong (i₁ ⨾_) q'-shape) i₁-step
      i₂!aZ-def = ren-lookup-definedᴸ (Pushout.wf-i₂ push) aZ∈Γ₃
      c₂ = proj₁ i₂!aZ-def
      i₂!aZ≡c₂ = proj₂ i₂!aZ-def
      i₂-step : i₂ ⨾ ((a_Z , 0) ∷ []) ≡ (c₂ , 0) ∷ []
      i₂-step = ⨾-cons-head-step {i₂} {a_Z} {0} {[]} {c₂} i₂!aZ≡c₂
      i₂-comp-eq : i₂ ⨾ q' ≡ (c₂ , 0) ∷ []
      i₂-comp-eq = trans (cong (i₂ ⨾_) q'-shape) i₂-step
      look-i₁-eq : look i₁ a_Z ≡ c₁
      look-i₁-eq = look-from-just {i₁} {a_Z} {c₁} i₁!aZ≡c₁
      look-i₂-eq : look i₂ a_Z ≡ c₂
      look-i₂-eq = look-from-just {i₂} {a_Z} {c₂} i₂!aZ≡c₂
      -- From q₁-decomp : (a_X, 0) ∷ [] ≡ i₁ ⨾ q' and i₁-comp-eq, derive c₁ ≡ a_X.
      cons-eq-X : (a_X , 0) ∷ [] ≡ (c₁ , 0) ∷ []
      cons-eq-X = trans q₁-decomp i₁-comp-eq
      aX≡c₁ : a_X ≡ c₁
      aX≡c₁ = ren-cons-inj-out cons-eq-X
      cons-eq-Y : (a_Y , 0) ∷ [] ≡ (c₂ , 0) ∷ []
      cons-eq-Y = trans q₂-decomp i₂-comp-eq
      aY≡c₂ : a_Y ≡ c₂
      aY≡c₂ = ren-cons-inj-out cons-eq-Y
  in a_Z , aZ∈Γ₃ ,
     trans look-i₁-eq (sym aX≡c₁) ,
     trans look-i₂-eq (sym aY≡c₂)
  where
    singleton-extractᴸ-p :
      ∀ {xs : List Name} {Δ-elem : Name} {j' : Ren}
      → xs ⊢ᴸ j' ∶ (Δ-elem ∷ [])
      → ∃[ a' ] ((a' ∈ᴸ xs) × (j' ≡ (a' , Δ-elem) ∷ []))
    singleton-extractᴸ-p {Δ-elem = Δ-elem}
      (wfl-cons {a = a'} {x = x} rem wfl-nil _) =
        a' , removeᴸ→memberᴸ rem , refl

mv-name-inj-local : ∀ {X Y ρ₁' ρ₂'} → mv X ρ₁' ≡ mv Y ρ₂' → X ≡ Y
mv-name-inj-local refl = refl

mv-ρ-inj-local : ∀ {X ρ₁' ρ₂'} → mv X ρ₁' ≡ mv X ρ₂' → ρ₁' ≡ ρ₂'
mv-ρ-inj-local refl = refl

term-pushout-factor :
  ∀ {Γ Γ_X Γ_Y ρ₁ ρ₂ Θ u_X u_Y}
  → Γ ⊢ ρ₁ ∶ Γ_X → Γ ⊢ ρ₂ ∶ Γ_Y
  → (push : Pushout Γ ρ₁ ρ₂ Γ_X Γ_Y)
  → Θ ، Γ_X ⊢ u_X → Θ ، Γ_Y ⊢ u_Y → [ ρ₁ ] u_X ≡ [ ρ₂ ] u_Y
  → ∃[ u_Z ] ((Θ ، Pushout.Γ₃ push ⊢ u_Z)
             × ([ Pushout.i₁ push ] u_Z ≡ u_X)
             × ([ Pushout.i₂ push ] u_Z ≡ u_Y))
term-pushout-factor {ρ₁ = ρ₁} {ρ₂ = ρ₂} D₁ D₂ push
                    (wf-var {a = a_X} aX∈) (wf-var {a = a_Y} aY∈) eq =
  let look-eq : look ρ₁ a_X ≡ look ρ₂ a_Y
      look-eq = vr-inj eq
      pre = pushout-var-preimage {ρ₁ = ρ₁} {ρ₂ = ρ₂} {a_X = a_X} {a_Y = a_Y}
                                  D₁ D₂ push aX∈ aY∈ look-eq
      a_Z = proj₁ pre
      a_Z-in = proj₁ (proj₂ pre)
      eq₁ = proj₁ (proj₂ (proj₂ pre))
      eq₂ = proj₂ (proj₂ (proj₂ pre))
  in vr a_Z , wf-var a_Z-in , cong vr eq₁ , cong vr eq₂
  where
    vr-inj : ∀ {a b} → vr a ≡ vr b → a ≡ b
    vr-inj refl = refl
term-pushout-factor _ _ _ (wf-con {c = c}) (wf-con {c = c'}) eq =
  let c≡c' : c ≡ c'
      c≡c' = cn-inj eq
  in cn c , wf-con , refl , cong cn c≡c'
  where
    cn-inj : ∀ {c c'} → cn c ≡ cn c' → c ≡ c'
    cn-inj refl = refl
term-pushout-factor D₁ D₂ push (wf-fun {f = f} d₁_X d₂_X)
                                 (wf-fun {f = g} d₁_Y d₂_Y) eq =
  let f≡g : f ≡ g
      f≡g = fn-inj-fn eq
      eq₁ = fn-inj₁ eq
      eq₂ = fn-inj₂ eq
      r₁ = term-pushout-factor D₁ D₂ push d₁_X d₁_Y eq₁
      r₂ = term-pushout-factor D₁ D₂ push d₂_X d₂_Y eq₂
      u₁ = proj₁ r₁ ; wf₁ = proj₁ (proj₂ r₁)
      e₁ᵢ = proj₁ (proj₂ (proj₂ r₁)) ; e₁ᵢᵢ = proj₂ (proj₂ (proj₂ r₁))
      u₂ = proj₁ r₂ ; wf₂ = proj₁ (proj₂ r₂)
      e₂ᵢ = proj₁ (proj₂ (proj₂ r₂)) ; e₂ᵢᵢ = proj₂ (proj₂ (proj₂ r₂))
  in fn f u₁ u₂ , wf-fun wf₁ wf₂ ,
     cong₂ (fn f) e₁ᵢ e₂ᵢ ,
     trans (cong₂ (fn f) e₁ᵢᵢ e₂ᵢᵢ) (cong (λ h → fn h _ _) f≡g)
  where
    fn-inj-fn : ∀ {f g t₁ t₂ t₁' t₂'} → fn f t₁ t₂ ≡ fn g t₁' t₂' → f ≡ g
    fn-inj-fn refl = refl
    fn-inj₁ : ∀ {f g t₁ t₂ t₁' t₂'} → fn f t₁ t₂ ≡ fn g t₁' t₂' → t₁ ≡ t₁'
    fn-inj₁ refl = refl
    fn-inj₂ : ∀ {f g t₁ t₂ t₁' t₂'} → fn f t₁ t₂ ≡ fn g t₁' t₂' → t₂ ≡ t₂'
    fn-inj₂ refl = refl
term-pushout-factor {Γ_Y = Γ_Y} {ρ₁ = ρ₁} {ρ₂ = ρ₂} {Θ = Θ}
                    D₁ D₂ push
                    (wf-meta {X = X} {Γ_X = Γ_Xm} {ρ = ρ_x} m_X wfρ_x)
                    (wf-meta {X = Y} {Γ_X = Γ_Ym} {ρ = ρ_y} m_Y wfρ_y) eq
  with mv-name-inj-local eq
... | refl =
        -- Now X ≡ Y. From eq : mv X (ρ₁⨾ρ_x) ≡ mv X (ρ₂⨾ρ_y), we get
        -- ρ₁⨾ρ_x ≡ ρ₂⨾ρ_y, but we still need Γ_Xm ≡ Γ_Ym to use the
        -- universal property uniformly.  The binder ctx is uniquely
        -- determined by Distinctness (mem-unique on the well-typed witness),
        -- so we postulate the matching here.
        let comp-eq : ρ₁ ⨾ ρ_x ≡ ρ₂ ⨾ ρ_y
            comp-eq = mv-ρ-inj-local eq
            -- We need Γ_Xm ≡ Γ_Ym.  Since X is well-typed with binder Γ_Xm
            -- in Θ, and X is also typed with Γ_Ym, we can match them.
            binders-eq : Γ_Xm ≡ Γ_Ym
            binders-eq = mem-unique (mnd Θ) m_X m_Y
            wfρ_y-Γ_Xm : Γ_Y ⊢ ρ_y ∶ Γ_Xm
            wfρ_y-Γ_Xm = subst (λ Δ → Γ_Y ⊢ ρ_y ∶ Δ)
                                (sym binders-eq) wfρ_y
            univ = Pushout.universal push {Δ = Γ_Xm} {q₁ = ρ_x} {q₂ = ρ_y}
                                       wfρ_x wfρ_y-Γ_Xm comp-eq
            q' = proj₁ univ
            wf-q' = proj₁ (proj₂ univ)
            ρ_x-eq = proj₁ (proj₂ (proj₂ univ))
            ρ_y-eq = proj₂ (proj₂ (proj₂ univ))
        in mv X q' , wf-meta m_X wf-q' ,
           cong (mv X) (sym ρ_x-eq) ,
           cong (mv X) (sym ρ_y-eq)

-- Aux 9.0: σ acts as identity when it does so on each metavariable in Θ_sub.
σ-acts-id-on-θ :
  ∀ {Θ_sub : MCtx} {Γ : Ctx} {σ : Sub} {t : Term}
  → (∀ {W : Name} {Γ_W : Ctx} → W ⦂[ Γ_W ]∈ Θ_sub → σ !ˢ W ≡ just (mv W (id-ren Γ_W)))
  → Θ_sub ، Γ ⊢ t
  → [ σ ]ˢ t ≡ t
σ-acts-id-on-θ _ (wf-var _)        = refl
σ-acts-id-on-θ _ wf-con             = refl
σ-acts-id-on-θ σ-id (wf-fun d₁ d₂) =
  cong₂ (fn _) (σ-acts-id-on-θ σ-id d₁) (σ-acts-id-on-θ σ-id d₂)
σ-acts-id-on-θ {Γ = Γ} {σ = σ} σ-id
  (wf-meta {X = X} {Γ_X = Γ_X} {ρ = ρ} m wfρ)
  with σ !ˢ X | σ-id m
... | just .(mv X (id-ren Γ_X)) | refl =
      cong (mv X) (id-ren-right-id {Γ = Γ} {Γ' = Γ_X} {ρ = ρ} wfρ)

------------------------------------------------------------------------
-- Phase 11 (plan): meta-tm MGU machinery.
------------------------------------------------------------------------

-- Restrict a substitution by dropping the entry for the removed
-- metavariable.  Relies on the substitution's list being aligned with
-- the metacontext (which the typing judgement guarantees).
restrict-subᴸ :
  ∀ {Θ-list Θ_rem-list X} → Θ-list -ᵐᴸ X ≡ Θ_rem-list → Sub → Sub
restrict-subᴸ rml-here ((_ , _) ∷ σ-rest) = σ-rest
restrict-subᴸ rml-here [] = []
restrict-subᴸ (rml-there _ D) ((t , Y) ∷ σ-rest) =
  (t , Y) ∷ restrict-subᴸ D σ-rest
restrict-subᴸ (rml-there _ D) [] = []

-- Typing of restrict-subᴸ.
restrict-subᴸ-wf :
  ∀ {Θ'' Θ-list Θ_rem-list X σ}
  → (r : Θ-list -ᵐᴸ X ≡ Θ_rem-list)
  → Θ'' ⊢ˢᴸ σ ∶ Θ-list
  → Θ'' ⊢ˢᴸ restrict-subᴸ r σ ∶ Θ_rem-list
restrict-subᴸ-wf rml-here (sl-cons σ-rest-wf _ _) = σ-rest-wf
restrict-subᴸ-wf (rml-there X≢Y D) (sl-cons σ-rest-wf t-wf Y-fresh) =
  let ih = restrict-subᴸ-wf D σ-rest-wf
      Y-fresh' = rml-preserves-∉Fst Y-fresh D
  in sl-cons ih t-wf Y-fresh'

-- Lookup of σ at the removed metavariable: yields a well-typed term.
-- Lookup at W ∉Fst Θ-list in id-sub-list returns nothing.
id-sub-list-lookup-nothing :
  ∀ {Θ-list W} → W ∉Fstᴸ Θ-list → id-sub-list Θ-list !ˢ W ≡ nothing
id-sub-list-lookup-nothing {[]} _ = refl
id-sub-list-lookup-nothing {(X , Γ) ∷ ms} {W} W∉ with W ≟ X
... | yes refl = ⊥-elim (W∉ fst-here)
... | no  _    = id-sub-list-lookup-nothing (λ m → W∉ (fst-there m))

-- Lookup at W ∉Fst Θ-list in mk-replace-subᴸ returns nothing.
mk-replace-subᴸ-lookup-nothing :
  ∀ {Θ-list Θ_rem-list X t' W}
  → (r : Θ-list -ᵐᴸ X ≡ Θ_rem-list)
  → W ∉Fstᴸ Θ-list
  → mk-replace-subᴸ r t' !ˢ W ≡ nothing
mk-replace-subᴸ-lookup-nothing {W = W} (rml-here {X = X}) W∉
  with W ≟ X
... | yes refl = ⊥-elim (W∉ fst-here)
... | no  _    = id-sub-list-lookup-nothing (λ m → W∉ (fst-there m))
mk-replace-subᴸ-lookup-nothing {W = W} (rml-there {Y = Y} _ D) W∉
  with W ≟ Y
... | yes refl = ⊥-elim (W∉ fst-here)
... | no  _    = mk-replace-subᴸ-lookup-nothing D (λ m → W∉ (fst-there m))

-- Action on (mv W ρ) when σ ! W = nothing.
sub-action-on-mv-nothing :
  ∀ {σ W ρ} → σ !ˢ W ≡ nothing → [ σ ]ˢ (mv W ρ) ≡ mv W ρ
sub-action-on-mv-nothing {σ} {W} {ρ} eq with σ !ˢ W | eq
... | nothing | refl = refl

-- Lookup of cons head returns the head term.
head-lookup-self :
  ∀ {t X σ} → ((t , X) ∷ σ) !ˢ X ≡ just t
head-lookup-self {X = X} with X ≟ X
... | yes _   = refl
... | no  ne  = ⊥-elim (ne refl)

-- Lookup of cons skipping head when X ≢ Y.
head-lookup-skip :
  ∀ {t X σ Y} → Y ≢ X → ((t , X) ∷ σ) !ˢ Y ≡ σ !ˢ Y
head-lookup-skip {X = X} {Y = Y} Y≢X with Y ≟ X
... | yes Y≡X = ⊥-elim (Y≢X Y≡X)
... | no  _   = refl

-- Action of σ on (mv X ρ) given a lookup witness.
sub-action-on-mv :
  ∀ {σ X t ρ} → σ !ˢ X ≡ just t → [ σ ]ˢ (mv X ρ) ≡ [ ρ ] t
sub-action-on-mv {σ} {X} {t} {ρ} eq with σ !ˢ X | eq
... | just .t | refl = refl

σ-lookup-at-removed :
  ∀ {Θ'' Θ-list Θ_rem-list X Γ_X σ}
  → (r : Θ-list -ᵐᴸ X ≡ Θ_rem-list)
  → DistinctM Θ-list
  → Θ'' ⊢ˢᴸ σ ∶ Θ-list
  → X ⦂[ Γ_X ]∈ᴸ Θ-list
  → ∃[ t-X ] ((σ !ˢ X ≡ just t-X) × (Θ'' ، Γ_X ⊢ t-X))
σ-lookup-at-removed rml-here _ (sl-cons {t = t-X} {X = X} _ t-wf _) m-hereᴸ
  with X ≟ X
... | yes _   = t-X , refl , t-wf
... | no  ne  = ⊥-elim (ne refl)
σ-lookup-at-removed rml-here (dm-cons fresh _) (sl-cons _ _ _) (m-thereᴸ m) =
  ⊥-elim (fresh (member→inFstᴸ m))
σ-lookup-at-removed (rml-there X≢Y D) _ (sl-cons _ _ _) m-hereᴸ =
  ⊥-elim (X≢Y refl)
σ-lookup-at-removed {X = X} (rml-there {Y = Y} X≢Y D) (dm-cons _ d-rest)
                     (sl-cons σ-rest-wf _ _) (m-thereᴸ m)
  with X ≟ Y
... | yes refl = ⊥-elim (X≢Y refl)
... | no  _    = σ-lookup-at-removed D d-rest σ-rest-wf m

-- restrict-subᴸ preserves lookup at non-removed metavariables.
-- Requires σ to be well-typed at Θ-list so the head names align.
restrict-sub-lookup-other :
  ∀ {Θ'' Θ-list Θ_rem-list X σ W}
  → Θ'' ⊢ˢᴸ σ ∶ Θ-list
  → (r : Θ-list -ᵐᴸ X ≡ Θ_rem-list) → W ≢ X
  → restrict-subᴸ r σ !ˢ W ≡ σ !ˢ W
restrict-sub-lookup-other {W = W} (sl-cons _ _ _) (rml-here {X = X}) W≢X
  with W ≟ X
... | yes refl = ⊥-elim (W≢X refl)
... | no  _    = refl
restrict-sub-lookup-other {W = W} (sl-cons σ-rest-wf _ _)
                           (rml-there {Y = Y} X≢Y D) W≢X
  with W ≟ Y
... | yes _ = refl
... | no  _ = restrict-sub-lookup-other σ-rest-wf D W≢X

-- σ acting on a term typed at a metacontext that does NOT include X is
-- the same as (head-extended σ with X-entry) acting on the term.
-- This is the "skip the head" property generalized to terms.
sub-action-skip-Θ :
  ∀ {Θ-sub σ t-X X Γ s}
  → X ∉Fstᴸ mlist Θ-sub
  → Θ-sub ، Γ ⊢ s
  → [ (t-X , X) ∷ σ ]ˢ s ≡ [ σ ]ˢ s
sub-action-skip-Θ _ (wf-var _) = refl
sub-action-skip-Θ _ wf-con      = refl
sub-action-skip-Θ X∉ (wf-fun d₁ d₂) =
  cong₂ (fn _) (sub-action-skip-Θ X∉ d₁) (sub-action-skip-Θ X∉ d₂)
sub-action-skip-Θ {σ = σ} {t-X = t-X} {X = X} {s = mv W ρ}
                   X∉ (wf-meta {X = .W} m wfρ) =
  let W∈Fst : W ∈Fstᴸ _
      W∈Fst = member→inFstᴸ m
      X≢W : X ≢ W
      X≢W X≡W = X∉ (subst (_∈Fstᴸ _) (sym X≡W) W∈Fst)
  in sub-action-skip-head {σ} {t-X} {X} {W} {ρ} X≢W

-- Substitution extensionality: two well-typed subs at the same Θ-list
-- with equal lookups at every metavar of Θ-list are equal as lists.
-- Aux: extracts head equality from lookup-equality at head.
private
  head-eq-from-lookup :
    ∀ {a b X σ σ'}
    → ((a , X) ∷ σ) !ˢ X ≡ ((b , X) ∷ σ') !ˢ X
    → a ≡ b
  head-eq-from-lookup {X = X} eq with X ≟ X
  ... | yes _   = just-inj eq
  ... | no  ne  = ⊥-elim (ne refl)

  tail-eq-from-lookup :
    ∀ {a b X Z σ σ'} → Z ≢ X
    → ((a , X) ∷ σ) !ˢ Z ≡ ((b , X) ∷ σ') !ˢ Z
    → σ !ˢ Z ≡ σ' !ˢ Z
  tail-eq-from-lookup {X = X} {Z = Z} ne eq with Z ≟ X
  ... | yes Z≡X = ⊥-elim (ne Z≡X)
  ... | no  _   = eq

sub-equal-via-entries :
  ∀ {Θ'' σ-A σ-B Θ-list}
  → DistinctM Θ-list
  → Θ'' ⊢ˢᴸ σ-A ∶ Θ-list
  → Θ'' ⊢ˢᴸ σ-B ∶ Θ-list
  → (∀ {W Γ_W} → W ⦂[ Γ_W ]∈ᴸ Θ-list → σ-A !ˢ W ≡ σ-B !ˢ W)
  → σ-A ≡ σ-B
sub-equal-via-entries _ sl-nil sl-nil _ = refl
sub-equal-via-entries (dm-cons {X = X} X-fresh d-rest)
                       (sl-cons {σ = σ-A-rest} {t = a-X} σ-A-rest-wf _ _)
                       (sl-cons {σ = σ-B-rest} {t = b-X} σ-B-rest-wf _ _)
                       hyp =
  let head-eq : a-X ≡ b-X
      head-eq = head-eq-from-lookup {a-X} {b-X} {X} {σ-A-rest} {σ-B-rest}
                  (hyp (m-hereᴸ {X = X}))
      tail-hyp : ∀ {Z Γ_Z} → Z ⦂[ Γ_Z ]∈ᴸ _ → σ-A-rest !ˢ Z ≡ σ-B-rest !ˢ Z
      tail-hyp {Z} m =
        let Z≢X : Z ≢ X
            Z≢X Z≡X = X-fresh (subst (λ w → w ∈Fstᴸ _) Z≡X (member→inFstᴸ m))
        in tail-eq-from-lookup {a-X} {b-X} {X} {Z} {σ-A-rest} {σ-B-rest}
                                Z≢X (hyp (m-thereᴸ m))
      ih = sub-equal-via-entries d-rest σ-A-rest-wf σ-B-rest-wf tail-hyp
  in cong₂ _∷_ (cong (_, X) head-eq) ih

-- [τ]ˢ s = [restrict-subᴸ r τ]ˢ s when s is typed at Θ_rem (where X is removed).
sub-restrict-action-eq :
  ∀ {Θ'' Θ-list Θ_rem-list Θ_rem-mctx X τ Γ s}
  → DistinctM Θ-list
  → Θ'' ⊢ˢᴸ τ ∶ Θ-list
  → (r : Θ-list -ᵐᴸ X ≡ Θ_rem-list)
  → mlist Θ_rem-mctx ≡ Θ_rem-list
  → Θ_rem-mctx ، Γ ⊢ s
  → [ τ ]ˢ s ≡ [ restrict-subᴸ r τ ]ˢ s
sub-restrict-action-eq _ _ _ _ (wf-var _)        = refl
sub-restrict-action-eq _ _ _ _ wf-con            = refl
sub-restrict-action-eq d τ-wf r eq (wf-fun d₁ d₂) =
  cong₂ (fn _) (sub-restrict-action-eq d τ-wf r eq d₁)
                (sub-restrict-action-eq d τ-wf r eq d₂)
sub-restrict-action-eq {X = X} {τ = τ} d τ-wf r mlist-eq
  (wf-meta {X = W} {Γ_X = Γ_W} {ρ = ρ} m wfρ) =
  let W-in-rem : W ⦂[ Γ_W ]∈ᴸ _
      W-in-rem = subst (W ⦂[ Γ_W ]∈ᴸ_) mlist-eq m
      X∉rem = rml-X-fresh-rem d r
      W∈Fst : W ∈Fstᴸ _
      W∈Fst = member→inFstᴸ W-in-rem
      W≢X : W ≢ X
      W≢X W≡X = X∉rem (subst (λ z → z ∈Fstᴸ _) W≡X W∈Fst)
      lookup-eq : τ !ˢ W ≡ restrict-subᴸ r τ !ˢ W
      lookup-eq = sym (restrict-sub-lookup-other τ-wf r W≢X)
  in aux {τ} {restrict-subᴸ r τ} {W} {ρ} lookup-eq
  where
    aux : ∀ {τ-fresh r-restrict-τ W ρ-x}
        → τ-fresh !ˢ W ≡ r-restrict-τ !ˢ W
        → [ τ-fresh ]ˢ (mv W ρ-x) ≡ [ r-restrict-τ ]ˢ (mv W ρ-x)
    aux {τ-fresh = τ-fresh} {r-restrict-τ = r-restrict-τ} {W = W} {ρ-x = ρ-x} eq
      with τ-fresh !ˢ W | r-restrict-τ !ˢ W | eq
    ... | just t  | just .t | refl = refl
    ... | nothing | nothing | refl = refl

-- Two well-typed subs are equal if they agree pointwise on the metavar
-- list (Ctx-level wrapper).
sub-equal-via-entries-Ctx :
  ∀ {Θ'' σ-A σ-B Θ}
  → Θ'' ⊢ˢ σ-A ∶ Θ
  → Θ'' ⊢ˢ σ-B ∶ Θ
  → (∀ {W Γ_W} → W ⦂[ Γ_W ]∈ Θ → σ-A !ˢ W ≡ σ-B !ˢ W)
  → σ-A ≡ σ-B
sub-equal-via-entries-Ctx {Θ = Θ} =
  sub-equal-via-entries (mnd Θ)

-- ⨾ˢ with a head-extended sub acting on σ-rhs whose entries are typed
-- at Θ-sub (with X ∉Fst Θ-sub): the head entry doesn't influence.
⨾ˢ-skip-head-on-typed :
  ∀ {Θ-sub σ-tail t-X X σ-rhs Θ-target}
  → X ∉Fstᴸ mlist Θ-sub
  → Θ-sub ⊢ˢᴸ σ-rhs ∶ Θ-target
  → ((t-X , X) ∷ σ-tail) ⨾ˢ σ-rhs ≡ σ-tail ⨾ˢ σ-rhs
⨾ˢ-skip-head-on-typed _ sl-nil = refl
⨾ˢ-skip-head-on-typed {σ-tail = σ-tail} {t-X = t-X} {X = X}
                       X∉ (sl-cons {t = s} {X = Y}
                                    σ-rhs-rest-wf s-wf Y-fresh) =
  let head-eq : [ (t-X , X) ∷ σ-tail ]ˢ s ≡ [ σ-tail ]ˢ s
      head-eq = sub-action-skip-Θ X∉ s-wf
      ih = ⨾ˢ-skip-head-on-typed {σ-tail = σ-tail} {t-X = t-X} {X = X}
                                   X∉ σ-rhs-rest-wf
  in cong₂ _∷_ (cong (_, Y) head-eq) ih
