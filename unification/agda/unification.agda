------------------------------------------------------------------------
-- Unification under a mixed prefix, for first-order terms.
--
-- Top-level aggregator module.  See the individual modules for the
-- formalization layered by topic:
--
--   * Base               — names, contexts, ∈, removal, subcontext
--   * Renaming           — renamings ρ, lookup, identity, composition
--   * Term               — terms, well-formedness Θ ، Γ ⊢ t, [ρ]_
--   * Substitution       — substitutions σ, [σ]ˢ_, identity, composition
--   * MetaWeakening      — Θ ⊇ Θ', Θ -ᵐ X ≡ Θ', and §5–§6 weakening
--   * PushoutCoequalizer — pushout and coequalizer records
--   * Properties         — the §6 lemmas used in §9 (postulated)
--   * Unification        — the unification relation and main theorem
--
-- The encoding follows `unification.md` and the proof structure follows
-- `unification-properties-new.md`.
--
-- Convention §0.4: `f ⨾ g = apply g first, then f` for renamings and
-- substitutions.
------------------------------------------------------------------------

{-# OPTIONS #-}

module unification where

open import Base                public
open import Renaming            public
open import Term                public
open import Substitution        public
open import MetaWeakening       public
open import PushoutCoequalizer  public
open import Properties          public
open import Unification         public
