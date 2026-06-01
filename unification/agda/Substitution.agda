------------------------------------------------------------------------
-- Metasubstitutions σ, well-formedness, identity, action, composition.
--
-- Convention §0.4: σ ⨾ˢ σ' = "apply σ' first, then σ".
------------------------------------------------------------------------

{-# OPTIONS #-}

module Substitution where

open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Data.Nat.Properties using (_≟_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong)

open import Base
open import Renaming
open import Term

------------------------------------------------------------------------
-- Substitutions as lists of (term , metavariable) entries.
------------------------------------------------------------------------

Sub : Set
Sub = List (Term × Name)

-- List-level wf: distinctness of the metavariable names is enforced
-- via a fresh-in-codomain premise on the cons rule.
infix 4 _⊢ˢᴸ_∶_
data _⊢ˢᴸ_∶_ : MCtx → Sub → List (Name × Ctx) → Set where
  sl-nil  : ∀ {Θ}                                                  → Θ ⊢ˢᴸ [] ∶ []
  sl-cons : ∀ {Θ Θ' σ t X Γ}
            → Θ ⊢ˢᴸ σ ∶ Θ'
            → Θ ، Γ ⊢ t
            → (fresh : X ∉Fstᴸ Θ')
            → Θ ⊢ˢᴸ ((t , X) ∷ σ) ∶ ((X , Γ) ∷ Θ')

infix 4 _⊢ˢ_∶_
_⊢ˢ_∶_ : MCtx → Sub → MCtx → Set
Θ ⊢ˢ σ ∶ Θ' = Θ ⊢ˢᴸ σ ∶ mlist Θ'

------------------------------------------------------------------------
-- Lookup σ(X)
------------------------------------------------------------------------

infix 5 _!ˢ_
_!ˢ_ : Sub → Name → Maybe Term
[] !ˢ _              = nothing
((t , X) ∷ σ) !ˢ Z with Z ≟ X
... | yes _ = just t
... | no  _ = σ !ˢ Z

------------------------------------------------------------------------
-- Action [σ]ˢ t
------------------------------------------------------------------------

infix 25 [_]ˢ_
[_]ˢ_ : Sub → Term → Term
[ σ ]ˢ (vr a)     = vr a
[ σ ]ˢ (cn c)     = cn c
[ σ ]ˢ (fn f t u) = fn f ([ σ ]ˢ t) ([ σ ]ˢ u)
[ σ ]ˢ (mv X ρ)   with σ !ˢ X
... | just t  = [ ρ ] t
... | nothing = mv X ρ

------------------------------------------------------------------------
-- Identity substitution and composition
------------------------------------------------------------------------

id-sub-list : List (Name × Ctx) → Sub
id-sub-list []            = []
id-sub-list ((X , Γ) ∷ Θ) = (mv X (id-ren Γ) , X) ∷ id-sub-list Θ

id-sub : MCtx → Sub
id-sub Θ = id-sub-list (mlist Θ)

_⨾ˢ_ : Sub → Sub → Sub
σ ⨾ˢ []             = []
σ ⨾ˢ ((t , X) ∷ σ') = ([ σ ]ˢ t , X) ∷ (σ ⨾ˢ σ')

------------------------------------------------------------------------
-- Build a substitution from `Θ -ᵐᴸ X ≡ Θ_rem` and a replacement term:
-- at the position of X in Θ, use the replacement; elsewhere use the
-- identity action.  The resulting σ has the same entry order as Θ.
------------------------------------------------------------------------

mk-replace-subᴸ :
  ∀ {Θ Θ_rem X} → Θ -ᵐᴸ X ≡ Θ_rem → Term → Sub
mk-replace-subᴸ {Θ_rem = Θ_rem} (rml-here {X = X}) t =
  (t , X) ∷ id-sub-list Θ_rem
mk-replace-subᴸ (rml-there {Y = Y} {Γ_Y = Γ_Y} _ D) t =
  (mv Y (id-ren Γ_Y) , Y) ∷ mk-replace-subᴸ D t
