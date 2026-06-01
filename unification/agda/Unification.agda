------------------------------------------------------------------------
-- The unification relation and the main correctness theorem.
--
-- Following `unification-properties-new.md` §9, the rules walk both
-- terms together.  Variable/constant equalities resolve immediately;
-- function applications recur; metavariable equations dispatch on
-- coequalizers (same metavariable on both sides), pushouts (different
-- metavariables), or inverse renamings (metavariable vs. term).
------------------------------------------------------------------------

{-# OPTIONS #-}

module Unification where

open import Data.List using ([]; _∷_)
open import Data.Product
  using (_×_; _,_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat.Properties using (_≟_)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Empty using (⊥; ⊥-elim)

open import Base
open import Renaming
open import Term
open import Substitution
open import MetaWeakening
open import PushoutCoequalizer
open import Properties

------------------------------------------------------------------------
-- The unification judgment
------------------------------------------------------------------------

infix 4 _،_⊢_≐_↝_∶_
data _،_⊢_≐_↝_∶_ : MCtx → Ctx → Term → Term → Sub → MCtx → Set where
  un-var :
      ∀ {Θ Γ a} → Θ ، Γ ⊢ vr a ≐ vr a ↝ id-sub Θ ∶ Θ
  un-con :
      ∀ {Θ Γ c} → Θ ، Γ ⊢ cn c ≐ cn c ↝ id-sub Θ ∶ Θ
  un-fun :
      ∀ {Θ Γ f t₁ t₂ t₁' t₂' σ Θ_mid σ' Θ'}
      → Θ ، Γ ⊢ t₁ ≐ t₁' ↝ σ ∶ Θ_mid
      → Θ_mid ، Γ ⊢ ([ σ ]ˢ t₂) ≐ ([ σ ]ˢ t₂') ↝ σ' ∶ Θ'
      → Θ ، Γ ⊢ fn f t₁ t₂ ≐ fn f t₁' t₂' ↝ (σ' ⨾ˢ σ) ∶ Θ'
  un-meta-same :
      ∀ {Θ Θ_rem Γ Γ_X X Z ρ₁ ρ₂}
      → (r : Θ -ᵐ X ≡ Θ_rem)
      → X ⦂[ Γ_X ]∈ Θ
      → (coeq : Coequalizer Γ ρ₁ ρ₂ Γ_X)
      → (fresh : Z ∉Fstᴸ mlist Θ_rem)
      → Θ ، Γ ⊢ mv X ρ₁ ≐ mv X ρ₂ ↝
          mk-replace-subᴸ r (mv Z (Coequalizer.i coeq)) ∶
          extend-M Z (Coequalizer.Γ'' coeq) Θ_rem fresh
  un-meta-diff :
      ∀ {Θ Θ_inter Θ_rem X Y Z Γ Γ_X Γ_Y ρ₁ ρ₂}
      → (r₁ : Θ -ᵐ X ≡ Θ_inter)
      → (r₂ : Θ_inter -ᵐ Y ≡ Θ_rem)
      → X ⦂[ Γ_X ]∈ Θ → Y ⦂[ Γ_Y ]∈ Θ_inter
      → (push : Pushout Γ ρ₁ ρ₂ Γ_X Γ_Y)
      → (fresh-Θ : Z ∉Fstᴸ mlist Θ)
      → (fresh : Z ∉Fstᴸ mlist Θ_rem)
      → Θ ، Γ ⊢ mv X ρ₁ ≐ mv Y ρ₂ ↝
          (mk-replace-subᴸ r₂ (mv Z (Pushout.i₂ push))
           ⨾ˢ mk-replace-subᴸ r₁ (mv Z (Pushout.i₁ push)))
          ∶ extend-M Z (Pushout.Γ₃ push) Θ_rem fresh
  un-meta-tm :
      ∀ {Θ Θ_rem Γ Γ_X Γ_inv X ρ t}
      → (r : Θ -ᵐ X ≡ Θ_rem)
      → X ⦂[ Γ_X ]∈ Θ                    -- X's binding in Θ
      → Γ ⊢ ρ ∶ Γ_X
      → Γ_X ⊢ ρ ⁻¹ ∶ Γ_inv               -- §3.1 inverse typing
      → Θ_rem ، Γ_inv ⊢ t                  -- paper premise: t over range(ρ)
      → Θ ، Γ ⊢ mv X ρ ≐ t ↝ mk-replace-subᴸ r ([ ρ ⁻¹ ] t) ∶ Θ_rem
  un-tm-meta :
      ∀ {Θ Θ_rem Γ Γ_X Γ_inv X ρ t}
      → (r : Θ -ᵐ X ≡ Θ_rem)
      → X ⦂[ Γ_X ]∈ Θ
      → Γ ⊢ ρ ∶ Γ_X
      → Γ_X ⊢ ρ ⁻¹ ∶ Γ_inv
      → Θ_rem ، Γ_inv ⊢ t
      → Θ ، Γ ⊢ t ≐ mv X ρ ↝ mk-replace-subᴸ r ([ ρ ⁻¹ ] t) ∶ Θ_rem

------------------------------------------------------------------------
-- The correctness specification (paper §9).
------------------------------------------------------------------------

record UnificationSpec
  {Θ Γ t₁ t₂ σ Θ'}
  (uni : Θ ، Γ ⊢ t₁ ≐ t₂ ↝ σ ∶ Θ') : Set where
  field
    sound-typing  : Θ' ⊢ˢ σ ∶ Θ
    sound-unifies : [ σ ]ˢ t₁ ≡ [ σ ]ˢ t₂
    mgu : ∀ {Θ'' τ} → Θ'' ⊢ˢ τ ∶ Θ → [ τ ]ˢ t₁ ≡ [ τ ]ˢ t₂ →
          ∃[ τ'' ] ((Θ'' ⊢ˢ τ'' ∶ Θ') × (τ ≡ (τ'' ⨾ˢ σ)))

------------------------------------------------------------------------
-- UnVar case
------------------------------------------------------------------------

unification-correct-var :
  ∀ {Θ Γ a}
  → (wf₁ : Θ ، Γ ⊢ vr a) (wf₂ : Θ ، Γ ⊢ vr a)
  → UnificationSpec (un-var {Θ} {Γ} {a})
unification-correct-var {Θ} wf₁ wf₂ = record
  { sound-typing  = id-sub-wf {Θ}
  ; sound-unifies = refl
  ; mgu = λ {Θ''} {τ} τ-wf _ →
      τ , τ-wf , ⨾ˢ-right-id {Θ' = Θ} τ-wf
  }

------------------------------------------------------------------------
-- UnCon case
------------------------------------------------------------------------

unification-correct-con :
  ∀ {Θ Γ c}
  → (wf₁ : Θ ، Γ ⊢ cn c) (wf₂ : Θ ، Γ ⊢ cn c)
  → UnificationSpec (un-con {Θ} {Γ} {c})
unification-correct-con {Θ} wf₁ wf₂ = record
  { sound-typing  = id-sub-wf {Θ}
  ; sound-unifies = refl
  ; mgu = λ {Θ''} {τ} τ-wf _ →
      τ , τ-wf , ⨾ˢ-right-id {Θ' = Θ} τ-wf
  }

------------------------------------------------------------------------
-- UnFun case (paper §9).
--
-- σ = σ' ⨾ˢ σ_mid (σ_mid handles t₁ ≐ t₁', then σ' handles the
-- σ_mid-rewritten t₂ ≐ t₂').
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Meta cases of the unification theorem.
--
-- UnMetaSame: uses Coequalizer record + Aux 9.1.
-- UnMetaDiff: uses Pushout record + Aux 9.2.
-- UnMetaTm / UnTmMeta: use inverse-renaming round-trip on terms (Aux 3.2a).
--
-- NOTE on MCtx permutation.  Paper §0.3 treats MCtx "modulo permutation
-- of entries".  Our MCtx is an explicit list, and the substitution
-- typing rule s-cons requires the head metavariable name to match.
-- The un-meta-tm rule's output substitution `([ρ⁻¹]t, X) ∷ id-sub Θ_rem`
-- assumes X is at the head of Θ; when X is removed from a position
-- other than the head (rml-there case), reconciling the two requires
-- a permutation lemma.  These postulates inhabit the spec at the
-- declared types.  Fully closing them requires either an order-
-- independent sub-typing or an explicit MCtx-permutation lemma.
------------------------------------------------------------------------

-- UnMetaSame: Θ ، Γ ⊢ mv X ρ₁ ≐ mv X ρ₂ ↝ ((mv Z (coeq.i), X) ∷ id-sub Θ_rem) ∶ extend-M Z (coeq.Γ'') Θ_rem fresh
unification-correct-meta-same :
  ∀ {Θ Θ_rem Γ Γ_X X Z ρ₁ ρ₂}
    {r : Θ -ᵐ X ≡ Θ_rem}
    {X-in-Θ : X ⦂[ Γ_X ]∈ Θ}
    {coeq : Coequalizer Γ ρ₁ ρ₂ Γ_X}
    {fresh : Z ∉Fstᴸ mlist Θ_rem}
  → Θ ، Γ ⊢ mv X ρ₁
  → Θ ، Γ ⊢ mv X ρ₂
  → UnificationSpec (un-meta-same {Θ} {Θ_rem} {Γ} {Γ_X} {X} {Z} {ρ₁} {ρ₂} r X-in-Θ coeq fresh)
unification-correct-meta-same
  {Θ = Θ} {Θ_rem = Θ_rem} {Γ = Γ} {Γ_X = Γ_X} {X = X} {Z = Z}
  {ρ₁ = ρ₁} {ρ₂ = ρ₂}
  {r = r} {X-in-Θ = X-in-Θ} {coeq = coeq} {fresh = fresh}
  (wf-meta {Γ_X = Γ_X₁} m₁ wfρ₁) (wf-meta {Γ_X = Γ_X₂} m₂ wfρ₂) =
  record
    { sound-typing  = sound-typing-proof
    ; sound-unifies = sound-unifies-proof
    ; mgu           = mgu-proof
    }
  where
    Γ'' = Coequalizer.Γ'' coeq
    i = Coequalizer.i coeq
    Θ' : MCtx
    Θ' = extend-M Z Γ'' Θ_rem fresh
    σ' : Sub
    σ' = mk-replace-subᴸ r (mv Z i)

    -- mv Z i is typed at Θ' ، Γ_X (Γ_X = Γ_eq for the coequalizer).
    mvZi-wf : Θ' ، Γ_X ⊢ mv Z i
    mvZi-wf = wf-meta m-hereᴸ (Coequalizer.wf-i coeq)

    sound-typing-proof : Θ' ⊢ˢ σ' ∶ Θ
    sound-typing-proof =
      mk-replace-subᴸ-wf {Θ = Θ} {X = X} {Γ_X = Γ_X} {Θ_out = Θ'}
                          r (wkl-skip ⊇ᴸ-refl) mvZi-wf X-in-Θ

    sound-unifies-proof : [ σ' ]ˢ (mv X ρ₁) ≡ [ σ' ]ˢ (mv X ρ₂)
    sound-unifies-proof = aux
      where
        σ-X-lookup : σ' !ˢ X ≡ just (mv Z i)
        σ-X-lookup = mk-replace-subᴸ-lookup-X r

        action-1 : [ σ' ]ˢ (mv X ρ₁) ≡ mv Z (ρ₁ ⨾ i)
        action-1 with σ' !ˢ X | σ-X-lookup
        ... | just .(mv Z i) | refl = refl

        action-2 : [ σ' ]ˢ (mv X ρ₂) ≡ mv Z (ρ₂ ⨾ i)
        action-2 with σ' !ˢ X | σ-X-lookup
        ... | just .(mv Z i) | refl = refl

        aux : [ σ' ]ˢ (mv X ρ₁) ≡ [ σ' ]ˢ (mv X ρ₂)
        aux = trans action-1
              (trans (cong (mv Z) (Coequalizer.eq coeq))
                     (sym action-2))

    -- MGU proof for meta-same: uses term-coeq-factor (Aux 9.1).
    mgu-proof : ∀ {Θ'' τ}
              → Θ'' ⊢ˢ τ ∶ Θ
              → [ τ ]ˢ (mv X ρ₁) ≡ [ τ ]ˢ (mv X ρ₂)
              → ∃[ τ'' ] ((Θ'' ⊢ˢ τ'' ∶ Θ') × (τ ≡ (τ'' ⨾ˢ σ')))
    mgu-proof {Θ''} {τ} τ-wf eq-τ =
      let τ-rest = restrict-subᴸ r τ
          τ-rest-wf : Θ'' ⊢ˢᴸ τ-rest ∶ mlist Θ_rem
          τ-rest-wf = restrict-subᴸ-wf r τ-wf
          -- Get τ_X and its typing.
          τ-X-info = σ-lookup-at-removed r (mnd Θ) τ-wf X-in-Θ
          τ_X = proj₁ τ-X-info
          τ-X-eq = proj₁ (proj₂ τ-X-info)
          τ_X-wf : Θ'' ، Γ_X ⊢ τ_X
          τ_X-wf = proj₂ (proj₂ τ-X-info)
          -- From eq-τ: [τ]ˢ (mv X ρ₁) ≡ [τ]ˢ (mv X ρ₂).
          --        ↪  [ρ₁] τ_X ≡ [ρ₂] τ_X.
          act-1 : [ τ ]ˢ (mv X ρ₁) ≡ [ ρ₁ ] τ_X
          act-1 = sub-action-on-mv {τ} {X} {τ_X} {ρ₁} τ-X-eq
          act-2 : [ τ ]ˢ (mv X ρ₂) ≡ [ ρ₂ ] τ_X
          act-2 = sub-action-on-mv {τ} {X} {τ_X} {ρ₂} τ-X-eq
          ρ-eq-on-τ_X : [ ρ₁ ] τ_X ≡ [ ρ₂ ] τ_X
          ρ-eq-on-τ_X = trans (sym act-1) (trans eq-τ act-2)
          -- The implicit Γ_X₁ from wf-meta must equal our Γ_X by mem-unique.
          Γ_X₁-eq : Γ_X₁ ≡ Γ_X
          Γ_X₁-eq = mem-unique (mnd Θ) m₁ X-in-Θ
          Γ_X₂-eq : Γ_X₂ ≡ Γ_X
          Γ_X₂-eq = mem-unique (mnd Θ) m₂ X-in-Θ
          wfρ₁' : Γ ⊢ ρ₁ ∶ Γ_X
          wfρ₁' = subst (λ G → Γ ⊢ ρ₁ ∶ G) Γ_X₁-eq wfρ₁
          wfρ₂' : Γ ⊢ ρ₂ ∶ Γ_X
          wfρ₂' = subst (λ G → Γ ⊢ ρ₂ ∶ G) Γ_X₂-eq wfρ₂
          -- Factor τ_X through the coequalizer: ∃ u' with [i] u' ≡ τ_X.
          factor-info = term-coeq-factor
                          {Γ = Γ} {Γ_X = Γ_X} {ρ₁ = ρ₁} {ρ₂ = ρ₂}
                          {Θ = Θ''} {u = τ_X}
                          wfρ₁' wfρ₂' coeq τ_X-wf ρ-eq-on-τ_X
          u' = proj₁ factor-info
          u'-wf : Θ'' ، Γ'' ⊢ u'
          u'-wf = proj₁ (proj₂ factor-info)
          [i]u'-eq : [ i ] u' ≡ τ_X
          [i]u'-eq = proj₂ (proj₂ factor-info)
          -- Construct τ'' = (u', Z) ∷ τ-rest.
          Z-fresh-in-Θ_rem : Z ∉Fstᴸ mlist Θ_rem
          Z-fresh-in-Θ_rem = fresh
          τ'' : Sub
          τ'' = (u' , Z) ∷ τ-rest
          τ''-wf : Θ'' ⊢ˢ τ'' ∶ Θ'
          τ''-wf = sl-cons τ-rest-wf u'-wf Z-fresh-in-Θ_rem
          -- Composition typing.
          comp-wf : Θ'' ⊢ˢ (τ'' ⨾ˢ σ') ∶ Θ
          comp-wf = sub-comp-wf {Θ''} {Θ'} {Θ} {τ''} {σ'} τ''-wf sound-typing-proof
          -- σ' lookups.
          σ'-lookup-X : σ' !ˢ X ≡ just (mv Z i)
          σ'-lookup-X = mk-replace-subᴸ-lookup-X r
          σ'-lookup-other-eq :
            ∀ {W Γ_W} → W ⦂[ Γ_W ]∈ Θ_rem → W ≢ X
            → σ' !ˢ W ≡ just (mv W (id-ren Γ_W))
          σ'-lookup-other-eq m W≢X =
            mk-replace-subᴸ-lookup-other (mnd Θ) r m W≢X
          -- (τ'' ⨾ˢ σ') !ˢ W computation.
          comp-lookup-X : (τ'' ⨾ˢ σ') !ˢ X ≡ just ([ τ'' ]ˢ (mv Z i))
          comp-lookup-X = sub-comp-lookup-just {τ''} {σ'} σ'-lookup-X
          -- [τ'']ˢ (mv Z i) = [i] (τ''(Z)) = [i] u' = τ_X.
          τ''-Z-eq : τ'' !ˢ Z ≡ just u'
          τ''-Z-eq = head-lookup-self {u'} {Z} {τ-rest}
          τ''-action-mv-Z : [ τ'' ]ˢ (mv Z i) ≡ [ i ] u'
          τ''-action-mv-Z = sub-action-on-mv {τ''} {Z} {u'} {i} τ''-Z-eq
          comp-X-eq-τ_X : (τ'' ⨾ˢ σ') !ˢ X ≡ just τ_X
          comp-X-eq-τ_X = trans comp-lookup-X
                                (cong just (trans τ''-action-mv-Z [i]u'-eq))
          hyp-W-eq-X :
            ∀ {W Γ_W} → W ⦂[ Γ_W ]∈ Θ → W ≡ X → τ !ˢ W ≡ (τ'' ⨾ˢ σ') !ˢ W
          hyp-W-eq-X _ W≡X =
            subst (λ z → τ !ˢ z ≡ (τ'' ⨾ˢ σ') !ˢ z) (sym W≡X)
              (trans τ-X-eq (sym comp-X-eq-τ_X))
          hyp-W-neq-X :
            ∀ {W Γ_W} → W ⦂[ Γ_W ]∈ Θ → W ≢ X → τ !ˢ W ≡ (τ'' ⨾ˢ σ') !ˢ W
          hyp-W-neq-X {W} {Γ_W} m W≢X =
            let W-in-Θ_rem : W ⦂[ Γ_W ]∈ᴸ mlist Θ_rem
                W-in-Θ_rem = removal-preserves-mem W≢X m r
                σ'-W-eq : σ' !ˢ W ≡ just (mv W (id-ren Γ_W))
                σ'-W-eq = σ'-lookup-other-eq W-in-Θ_rem W≢X
                comp-W-eq : (τ'' ⨾ˢ σ') !ˢ W
                          ≡ just ([ τ'' ]ˢ (mv W (id-ren Γ_W)))
                comp-W-eq = sub-comp-lookup-just {τ''} {σ'} σ'-W-eq
                τ-rest-W-info = sub-lookup-wf τ-rest-wf W-in-Θ_rem
                t_W = proj₁ τ-rest-W-info
                τ-rest-W-eq = proj₁ (proj₂ τ-rest-W-info)
                t_W-wf : Θ'' ، Γ_W ⊢ t_W
                t_W-wf = proj₂ (proj₂ τ-rest-W-info)
                -- τ-rest !ˢ W ≡ τ !ˢ W.
                τ-rest-eq-τ-W : τ-rest !ˢ W ≡ τ !ˢ W
                τ-rest-eq-τ-W = restrict-sub-lookup-other τ-wf r W≢X
                τ-W-eq : τ !ˢ W ≡ just t_W
                τ-W-eq = trans (sym τ-rest-eq-τ-W) τ-rest-W-eq
                -- τ'' !ˢ W: head is (u', Z), W ≠ Z (since Z ∉Fst Θ_rem and W ∈ Θ_rem).
                W≢Z : W ≢ Z
                W≢Z W≡Z = Z-fresh-in-Θ_rem
                  (subst (λ z → z ∈Fstᴸ _) W≡Z (member→inFstᴸ W-in-Θ_rem))
                τ''-W-eq : τ'' !ˢ W ≡ τ-rest !ˢ W
                τ''-W-eq = head-lookup-skip {u'} {Z} {τ-rest} {W} W≢Z
                τ''-action-mv-W : [ τ'' ]ˢ (mv W (id-ren Γ_W)) ≡ t_W
                τ''-action-mv-W =
                  trans (sub-action-on-mv {τ''} {W} {t_W} {id-ren Γ_W}
                          (trans τ''-W-eq τ-rest-W-eq))
                        (id-ren-action {Θ''} {Γ_W} t_W-wf)
            in trans τ-W-eq
                     (trans (cong just (sym τ''-action-mv-W))
                            (sym comp-W-eq))
          hyp-case-on-eq :
            ∀ {W Γ_W} (dec-eq : Dec (W ≡ X))
            → W ⦂[ Γ_W ]∈ Θ
            → τ !ˢ W ≡ (τ'' ⨾ˢ σ') !ˢ W
          hyp-case-on-eq = λ where
            (yes W≡X) m → hyp-W-eq-X m W≡X
            (no  W≢X) m → hyp-W-neq-X m W≢X
          hyp : ∀ {W Γ_W} → W ⦂[ Γ_W ]∈ Θ → τ !ˢ W ≡ (τ'' ⨾ˢ σ') !ˢ W
          hyp {W} m = hyp-case-on-eq (W ≟ X) m
          τ-eq : τ ≡ (τ'' ⨾ˢ σ')
          τ-eq = sub-equal-via-entries-Ctx {Θ = Θ} τ-wf comp-wf hyp
      in τ'' , τ''-wf , τ-eq

unification-correct-meta-diff :
  ∀ {Θ Θ_inter Θ_rem X Y Z Γ Γ_X Γ_Y ρ₁ ρ₂}
    {r₁ : Θ -ᵐ X ≡ Θ_inter} {r₂ : Θ_inter -ᵐ Y ≡ Θ_rem}
    {X-in-Θ : X ⦂[ Γ_X ]∈ Θ} {Y-in-Θ-inter : Y ⦂[ Γ_Y ]∈ Θ_inter}
    {push : Pushout Γ ρ₁ ρ₂ Γ_X Γ_Y}
    {fresh-Θ : Z ∉Fstᴸ mlist Θ}
    {fresh : Z ∉Fstᴸ mlist Θ_rem}
  → Θ ، Γ ⊢ mv X ρ₁
  → Θ ، Γ ⊢ mv Y ρ₂
  → UnificationSpec (un-meta-diff {Θ} {Θ_inter} {Θ_rem} {X} {Y} {Z} {Γ} {Γ_X} {Γ_Y} {ρ₁} {ρ₂} r₁ r₂ X-in-Θ Y-in-Θ-inter push fresh-Θ fresh)
unification-correct-meta-diff
  {Θ = Θ} {Θ_inter = Θ_inter} {Θ_rem = Θ_rem}
  {X = X} {Y = Y} {Z = Z} {Γ = Γ} {Γ_X = Γ_X} {Γ_Y = Γ_Y}
  {ρ₁ = ρ₁} {ρ₂ = ρ₂}
  {r₁ = r₁} {r₂ = r₂}
  {X-in-Θ = X-in-Θ} {Y-in-Θ-inter = Y-in-Θ-inter}
  {push = push} {fresh-Θ = fresh-Θ} {fresh = fresh}
  (wf-meta {Γ_X = Γ_X₁} m₁ wfρ₁) (wf-meta {Γ_X = Γ_Y₁} m₂ wfρ₂) =
  record
    { sound-typing  = sound-typing-proof
    ; sound-unifies = sound-unifies-proof
    ; mgu           = mgu-proof
    }
  where
    Γ₃ = Pushout.Γ₃ push
    i₁ = Pushout.i₁ push
    i₂ = Pushout.i₂ push
    Θ' : MCtx
    Θ' = extend-M Z Γ₃ Θ_rem fresh
    σ-inner = mk-replace-subᴸ r₁ (mv Z i₁)
    σ-outer = mk-replace-subᴸ r₂ (mv Z i₂)
    σ' = σ-outer ⨾ˢ σ-inner

    -- mv Z i₁ : Θ' ، Γ_X ⊢ mv Z i₁  (Z is the new head, i₁ : Γ_X ⊢ i₁ ∶ Γ₃).
    mvZi₁-wf : Θ' ، Γ_X ⊢ mv Z i₁
    mvZi₁-wf = wf-meta m-hereᴸ (Pushout.wf-i₁ push)

    mvZi₂-wf : Θ' ، Γ_Y ⊢ mv Z i₂
    mvZi₂-wf = wf-meta m-hereᴸ (Pushout.wf-i₂ push)

    -- Z is fresh in Θ_inter (from Z fresh in Θ and Θ -ᵐ X ≡ Θ_inter).
    Z-fresh-Θ_inter : Z ∉Fstᴸ mlist Θ_inter
    Z-fresh-Θ_inter = rml-preserves-∉Fst fresh-Θ r₁

    -- An "extended" σ-outer that treats Z as identity at its head;
    -- this allows clean composition with σ-inner whose terms mention Z.
    Θ-mid : MCtx
    Θ-mid = extend-M Z Γ₃ Θ_inter Z-fresh-Θ_inter

    σ-outer-ext : Sub
    σ-outer-ext = (mv Z (id-ren Γ₃) , Z) ∷ σ-outer

    σ-outer-wf : Θ' ⊢ˢ σ-outer ∶ Θ_inter
    σ-outer-wf =
      mk-replace-subᴸ-wf {Θ = Θ_inter} {X = Y} {Γ_X = Γ_Y} {Θ_out = Θ'}
                          r₂ (wkl-skip ⊇ᴸ-refl) mvZi₂-wf Y-in-Θ-inter

    mvZ-id-wf : Θ' ، Γ₃ ⊢ mv Z (id-ren Γ₃)
    mvZ-id-wf = wf-meta m-hereᴸ (id-ren-wf {Γ₃})

    σ-outer-ext-wf : Θ' ⊢ˢ σ-outer-ext ∶ Θ-mid
    σ-outer-ext-wf = sl-cons σ-outer-wf mvZ-id-wf Z-fresh-Θ_inter

    σ-inner-wf : Θ-mid ⊢ˢ σ-inner ∶ Θ
    σ-inner-wf =
      mk-replace-subᴸ-wf {Θ = Θ} {X = X} {Γ_X = Γ_X} {Θ_out = Θ-mid}
                          r₁ (wkl-skip ⊇ᴸ-refl) mvZ-mid-i₁-wf X-in-Θ
      where
        mvZ-mid-i₁-wf : Θ-mid ، Γ_X ⊢ mv Z i₁
        mvZ-mid-i₁-wf = wf-meta m-hereᴸ (Pushout.wf-i₁ push)

    -- The composition σ-outer-ext ⨾ˢ σ-inner equals σ' = σ-outer ⨾ˢ σ-inner.
    -- This follows from a per-entry argument: σ-outer-ext extends σ-outer
    -- with the identity at Z, but σ-inner's entries either (a) have form
    -- mv Z i₁ at X — for which the extension turns into [i₁]mv Z (id-ren) =
    -- mv Z (i₁ ⨾ id-ren Γ₃) = mv Z i₁ (by id-ren-right-id), matching
    -- σ-outer's "leave Z alone" behavior; or (b) have form mv W (id-ren Γ_W)
    -- with W ∈ Θ_inter, W ≠ Z — for which σ-outer-ext skips its (Z, ...)
    -- head and matches σ-outer's action.
    σ-outer-ext-comp-eq : σ-outer-ext ⨾ˢ σ-inner ≡ σ'
    σ-outer-ext-comp-eq = aux r₁ fresh-Θ
      where
        aux : ∀ {Θ-list Θ-inter-list}
            → (r : Θ-list -ᵐᴸ X ≡ Θ-inter-list)
            → Z ∉Fstᴸ Θ-list
            → σ-outer-ext ⨾ˢ mk-replace-subᴸ r (mv Z i₁)
              ≡ σ-outer ⨾ˢ mk-replace-subᴸ r (mv Z i₁)
        aux (rml-here {Θ = Θ-rest} {Γ = Γ-rest}) Z∉ =
          let Z∉rem : Z ∉Fstᴸ Θ-rest
              Z∉rem = λ m → Z∉ (fst-there m)
              lhs-Z-eq : σ-outer-ext !ˢ Z ≡ just (mv Z (id-ren Γ₃))
              lhs-Z-eq = head-lookup-self {mv Z (id-ren Γ₃)} {Z} {σ-outer}
              lhs-head : [ σ-outer-ext ]ˢ (mv Z i₁) ≡ mv Z i₁
              lhs-head =
                trans (sub-action-on-mv {σ-outer-ext} {Z} {mv Z (id-ren Γ₃)} {i₁} lhs-Z-eq)
                      (cong (mv Z) (id-ren-right-id {Γ_X} {Γ₃} {i₁} (Pushout.wf-i₁ push)))
              rhs-Z-eq : σ-outer !ˢ Z ≡ nothing
              rhs-Z-eq =
                mk-replace-subᴸ-lookup-nothing r₂ Z-fresh-Θ_inter
              rhs-head : [ σ-outer ]ˢ (mv Z i₁) ≡ mv Z i₁
              rhs-head = sub-action-on-mv-nothing {σ-outer} {Z} {i₁} rhs-Z-eq
              head-eq : [ σ-outer-ext ]ˢ (mv Z i₁) ≡ [ σ-outer ]ˢ (mv Z i₁)
              head-eq = trans lhs-head (sym rhs-head)
              tail-eq : σ-outer-ext ⨾ˢ id-sub-list Θ-rest
                      ≡ σ-outer ⨾ˢ id-sub-list Θ-rest
              tail-eq =
                ⨾ˢ-skip-head-id {σ-outer} {mv Z (id-ren Γ₃)} {Z} {Θ-rest} Z∉rem
          in cong₂ _∷_ (cong (_, X) head-eq) tail-eq
        aux (rml-there {Y = Y'} {Γ_Y = Γ_Y'} X≢Y' D) Z∉ =
          let Z-≢Y' : Z ≢ Y'
              Z-≢Y' = λ Z≡Y' →
                Z∉ (subst (_∈Fstᴸ _) (sym Z≡Y') fst-here)
              head-eq : [ σ-outer-ext ]ˢ (mv Y' (id-ren Γ_Y'))
                      ≡ [ σ-outer ]ˢ (mv Y' (id-ren Γ_Y'))
              head-eq =
                sub-action-skip-head
                  {σ-outer} {mv Z (id-ren Γ₃)} {Z} {Y'} {id-ren Γ_Y'}
                  Z-≢Y'
              tail-eq : σ-outer-ext ⨾ˢ mk-replace-subᴸ D (mv Z i₁)
                      ≡ σ-outer ⨾ˢ mk-replace-subᴸ D (mv Z i₁)
              tail-eq = aux D (λ m → Z∉ (fst-there m))
          in cong₂ _∷_ (cong (_, Y') head-eq) tail-eq

    sound-typing-proof : Θ' ⊢ˢ σ' ∶ Θ
    sound-typing-proof =
      subst (λ s → Θ' ⊢ˢ s ∶ Θ) σ-outer-ext-comp-eq
            (sub-comp-wf {Θ'} {Θ-mid} {Θ} {σ-outer-ext} {σ-inner}
                          σ-outer-ext-wf σ-inner-wf)

    -- σ' !ˢ X = just (mv Z i₁): X's slot in σ-inner has replacement (mv Z i₁),
    -- and σ-outer leaves Z alone (Z ∉ Θ_inter, so σ-outer !ˢ Z = nothing).
    σ'-X-eq : σ' !ˢ X ≡ just (mv Z i₁)
    σ'-X-eq =
      let σ-inner-X : σ-inner !ˢ X ≡ just (mv Z i₁)
          σ-inner-X = mk-replace-subᴸ-lookup-X r₁
          σ'-X-comp : σ' !ˢ X ≡ just ([ σ-outer ]ˢ (mv Z i₁))
          σ'-X-comp = sub-comp-lookup-just {σ-outer} {σ-inner} σ-inner-X
          σ-outer-Z : σ-outer !ˢ Z ≡ nothing
          σ-outer-Z = mk-replace-subᴸ-lookup-nothing r₂ Z-fresh-Θ_inter
          σ-outer-on-mvZi₁ : [ σ-outer ]ˢ (mv Z i₁) ≡ mv Z i₁
          σ-outer-on-mvZi₁ = sub-action-on-mv-nothing {σ-outer} {Z} {i₁} σ-outer-Z
      in trans σ'-X-comp (cong just σ-outer-on-mvZi₁)

    -- Y ≠ X: Y is in Θ_inter, but X is fresh in Θ_inter (by rml-X-fresh-rem).
    Y≢X : Y ≢ X
    Y≢X Y≡X =
      rml-X-fresh-rem (mnd Θ) r₁
        (subst (_∈Fstᴸ _) Y≡X (member→inFstᴸ Y-in-Θ-inter))

    -- σ' !ˢ Y = just (mv Z i₂): σ-inner !ˢ Y is the identity at Y (since
    -- Y ≠ X), and σ-outer maps Y to its replacement mv Z i₂.
    σ'-Y-eq : σ' !ˢ Y ≡ just (mv Z i₂)
    σ'-Y-eq =
      let σ-inner-Y : σ-inner !ˢ Y ≡ just (mv Y (id-ren Γ_Y))
          σ-inner-Y = mk-replace-subᴸ-lookup-other (mnd Θ) r₁ Y-in-Θ-inter Y≢X
          σ'-Y-comp : σ' !ˢ Y ≡ just ([ σ-outer ]ˢ (mv Y (id-ren Γ_Y)))
          σ'-Y-comp = sub-comp-lookup-just {σ-outer} {σ-inner} σ-inner-Y
          σ-outer-Y : σ-outer !ˢ Y ≡ just (mv Z i₂)
          σ-outer-Y = mk-replace-subᴸ-lookup-X r₂
          σ-outer-on-mvY-id : [ σ-outer ]ˢ (mv Y (id-ren Γ_Y)) ≡ mv Z i₂
          σ-outer-on-mvY-id =
            trans
              (sub-action-on-mv {σ-outer} {Y} {mv Z i₂} {id-ren Γ_Y} σ-outer-Y)
              (cong (mv Z) (id-ren-left-id-direct {Γ_Y} {Γ₃} {i₂} (Pushout.wf-i₂ push)))
      in trans σ'-Y-comp (cong just σ-outer-on-mvY-id)

    sound-unifies-proof : [ σ' ]ˢ (mv X ρ₁) ≡ [ σ' ]ˢ (mv Y ρ₂)
    sound-unifies-proof =
      let lhs-eq : [ σ' ]ˢ (mv X ρ₁) ≡ mv Z (ρ₁ ⨾ i₁)
          lhs-eq = sub-action-on-mv {σ'} {X} {mv Z i₁} {ρ₁} σ'-X-eq
          rhs-eq : [ σ' ]ˢ (mv Y ρ₂) ≡ mv Z (ρ₂ ⨾ i₂)
          rhs-eq = sub-action-on-mv {σ'} {Y} {mv Z i₂} {ρ₂} σ'-Y-eq
      in trans lhs-eq
               (trans (cong (mv Z) (Pushout.eq push)) (sym rhs-eq))

    -- Y is in Θ via mem-in-removed-implies-original (Y ∈ Θ_inter ⇒ Y ∈ Θ).
    Y-in-Θ : Y ⦂[ Γ_Y ]∈ Θ
    Y-in-Θ = mem-in-removed-implies-original r₁ Y-in-Θ-inter

    mgu-proof : ∀ {Θ'' τ}
              → Θ'' ⊢ˢ τ ∶ Θ
              → [ τ ]ˢ (mv X ρ₁) ≡ [ τ ]ˢ (mv Y ρ₂)
              → ∃[ τ'' ] ((Θ'' ⊢ˢ τ'' ∶ Θ') × (τ ≡ (τ'' ⨾ˢ σ')))
    mgu-proof {Θ''} {τ} τ-wf eq-τ =
      let τ-after-r₁ = restrict-subᴸ r₁ τ
          τ-after-r₁-wf : Θ'' ⊢ˢᴸ τ-after-r₁ ∶ mlist Θ_inter
          τ-after-r₁-wf = restrict-subᴸ-wf r₁ τ-wf
          τ-rem = restrict-subᴸ r₂ τ-after-r₁
          τ-rem-wf : Θ'' ⊢ˢᴸ τ-rem ∶ mlist Θ_rem
          τ-rem-wf = restrict-subᴸ-wf r₂ τ-after-r₁-wf
          τ-X-info = sub-lookup-wf τ-wf X-in-Θ
          t_X = proj₁ τ-X-info
          τ-X-eq = proj₁ (proj₂ τ-X-info)
          t_X-wf : Θ'' ، Γ_X ⊢ t_X
          t_X-wf = proj₂ (proj₂ τ-X-info)
          τ-Y-info = sub-lookup-wf τ-wf Y-in-Θ
          t_Y = proj₁ τ-Y-info
          τ-Y-eq = proj₁ (proj₂ τ-Y-info)
          t_Y-wf : Θ'' ، Γ_Y ⊢ t_Y
          t_Y-wf = proj₂ (proj₂ τ-Y-info)
          act-X : [ τ ]ˢ (mv X ρ₁) ≡ [ ρ₁ ] t_X
          act-X = sub-action-on-mv {τ} {X} {t_X} {ρ₁} τ-X-eq
          act-Y : [ τ ]ˢ (mv Y ρ₂) ≡ [ ρ₂ ] t_Y
          act-Y = sub-action-on-mv {τ} {Y} {t_Y} {ρ₂} τ-Y-eq
          ρ-eq : [ ρ₁ ] t_X ≡ [ ρ₂ ] t_Y
          ρ-eq = trans (sym act-X) (trans eq-τ act-Y)
          Γ_X₁-eq : Γ_X₁ ≡ Γ_X
          Γ_X₁-eq = mem-unique (mnd Θ) m₁ X-in-Θ
          Γ_Y₁-eq : Γ_Y₁ ≡ Γ_Y
          Γ_Y₁-eq = mem-unique (mnd Θ) m₂ Y-in-Θ
          wfρ₁' : Γ ⊢ ρ₁ ∶ Γ_X
          wfρ₁' = subst (λ G → Γ ⊢ ρ₁ ∶ G) Γ_X₁-eq wfρ₁
          wfρ₂' : Γ ⊢ ρ₂ ∶ Γ_Y
          wfρ₂' = subst (λ G → Γ ⊢ ρ₂ ∶ G) Γ_Y₁-eq wfρ₂
          factor-info = term-pushout-factor
                          {Γ = Γ} {Γ_X = Γ_X} {Γ_Y = Γ_Y}
                          {ρ₁ = ρ₁} {ρ₂ = ρ₂}
                          {Θ = Θ''} {u_X = t_X} {u_Y = t_Y}
                          wfρ₁' wfρ₂' push t_X-wf t_Y-wf ρ-eq
          u_Z = proj₁ factor-info
          u_Z-wf : Θ'' ، Γ₃ ⊢ u_Z
          u_Z-wf = proj₁ (proj₂ factor-info)
          [i₁]u_Z-eq : [ i₁ ] u_Z ≡ t_X
          [i₁]u_Z-eq = proj₁ (proj₂ (proj₂ factor-info))
          [i₂]u_Z-eq : [ i₂ ] u_Z ≡ t_Y
          [i₂]u_Z-eq = proj₂ (proj₂ (proj₂ factor-info))
          τ'' : Sub
          τ'' = (u_Z , Z) ∷ τ-rem
          τ''-wf : Θ'' ⊢ˢ τ'' ∶ Θ'
          τ''-wf = sl-cons τ-rem-wf u_Z-wf fresh
          comp-wf : Θ'' ⊢ˢ (τ'' ⨾ˢ σ') ∶ Θ
          comp-wf = sub-comp-wf {Θ''} {Θ'} {Θ} {τ''} {σ'}
                                 τ''-wf sound-typing-proof
          τ''-Z-lookup : τ'' !ˢ Z ≡ just u_Z
          τ''-Z-lookup = head-lookup-self {u_Z} {Z} {τ-rem}
          comp-X-eq-t_X : (τ'' ⨾ˢ σ') !ˢ X ≡ just t_X
          comp-X-eq-t_X =
            trans (sub-comp-lookup-just {τ''} {σ'} σ'-X-eq)
                  (cong just
                    (trans (sub-action-on-mv {τ''} {Z} {u_Z} {i₁} τ''-Z-lookup)
                           [i₁]u_Z-eq))
          comp-Y-eq-t_Y : (τ'' ⨾ˢ σ') !ˢ Y ≡ just t_Y
          comp-Y-eq-t_Y =
            trans (sub-comp-lookup-just {τ''} {σ'} σ'-Y-eq)
                  (cong just
                    (trans (sub-action-on-mv {τ''} {Z} {u_Z} {i₂} τ''-Z-lookup)
                           [i₂]u_Z-eq))
          hyp-W-eq-X :
            ∀ {W Γ_W} → W ⦂[ Γ_W ]∈ Θ → W ≡ X → τ !ˢ W ≡ (τ'' ⨾ˢ σ') !ˢ W
          hyp-W-eq-X _ W≡X =
            subst (λ z → τ !ˢ z ≡ (τ'' ⨾ˢ σ') !ˢ z) (sym W≡X)
              (trans τ-X-eq (sym comp-X-eq-t_X))
          hyp-W-eq-Y :
            ∀ {W Γ_W} → W ⦂[ Γ_W ]∈ Θ → W ≡ Y → τ !ˢ W ≡ (τ'' ⨾ˢ σ') !ˢ W
          hyp-W-eq-Y _ W≡Y =
            subst (λ z → τ !ˢ z ≡ (τ'' ⨾ˢ σ') !ˢ z) (sym W≡Y)
              (trans τ-Y-eq (sym comp-Y-eq-t_Y))
          hyp-W-other :
            ∀ {W Γ_W} → W ⦂[ Γ_W ]∈ Θ → W ≢ X → W ≢ Y
            → τ !ˢ W ≡ (τ'' ⨾ˢ σ') !ˢ W
          hyp-W-other {W} {Γ_W} m W≢X W≢Y =
            let W-in-Θ_inter : W ⦂[ Γ_W ]∈ᴸ mlist Θ_inter
                W-in-Θ_inter = removal-preserves-mem W≢X m r₁
                W-in-Θ_rem : W ⦂[ Γ_W ]∈ᴸ mlist Θ_rem
                W-in-Θ_rem = removal-preserves-mem W≢Y W-in-Θ_inter r₂
                W≢Z : W ≢ Z
                W≢Z W≡Z =
                  fresh (subst (_∈Fstᴸ _) W≡Z (member→inFstᴸ W-in-Θ_rem))
                σ-inner-W : σ-inner !ˢ W ≡ just (mv W (id-ren Γ_W))
                σ-inner-W =
                  mk-replace-subᴸ-lookup-other (mnd Θ) r₁ W-in-Θ_inter W≢X
                σ-outer-W : σ-outer !ˢ W ≡ just (mv W (id-ren Γ_W))
                σ-outer-W =
                  mk-replace-subᴸ-lookup-other (mnd Θ_inter) r₂ W-in-Θ_rem W≢Y
                σ-outer-action-mvW :
                  [ σ-outer ]ˢ (mv W (id-ren Γ_W)) ≡ mv W (id-ren Γ_W)
                σ-outer-action-mvW =
                  trans (sub-action-on-mv {σ-outer} {W} {mv W (id-ren Γ_W)}
                                            {id-ren Γ_W} σ-outer-W)
                        (cong (mv W) (id-ren-right-id {Γ_W} {Γ_W} {id-ren Γ_W}
                                       (id-ren-wf {Γ_W})))
                σ'-W-eq : σ' !ˢ W ≡ just (mv W (id-ren Γ_W))
                σ'-W-eq =
                  trans (sub-comp-lookup-just {σ-outer} {σ-inner} σ-inner-W)
                        (cong just σ-outer-action-mvW)
                τ''-W-via-skip : τ'' !ˢ W ≡ τ-rem !ˢ W
                τ''-W-via-skip = head-lookup-skip {u_Z} {Z} {τ-rem} {W} W≢Z
                τ-after-r₁-W : τ-after-r₁ !ˢ W ≡ τ !ˢ W
                τ-after-r₁-W = restrict-sub-lookup-other τ-wf r₁ W≢X
                τ-rem-eq-τ-W : τ-rem !ˢ W ≡ τ !ˢ W
                τ-rem-eq-τ-W =
                  trans (restrict-sub-lookup-other τ-after-r₁-wf r₂ W≢Y)
                        τ-after-r₁-W
                τ-W-info = sub-lookup-wf τ-wf m
                t_W = proj₁ τ-W-info
                τ-W-eq = proj₁ (proj₂ τ-W-info)
                t_W-wf : Θ'' ، Γ_W ⊢ t_W
                t_W-wf = proj₂ (proj₂ τ-W-info)
                τ''-W-eq : τ'' !ˢ W ≡ just t_W
                τ''-W-eq =
                  trans τ''-W-via-skip (trans τ-rem-eq-τ-W τ-W-eq)
                τ''-action-mv-W : [ τ'' ]ˢ (mv W (id-ren Γ_W)) ≡ t_W
                τ''-action-mv-W =
                  trans (sub-action-on-mv {τ''} {W} {t_W} {id-ren Γ_W}
                                            τ''-W-eq)
                        (id-ren-action t_W-wf)
                comp-W-eq : (τ'' ⨾ˢ σ') !ˢ W ≡ just t_W
                comp-W-eq =
                  trans (sub-comp-lookup-just {τ''} {σ'} σ'-W-eq)
                        (cong just τ''-action-mv-W)
            in trans τ-W-eq (sym comp-W-eq)
          hyp-dispatch :
            ∀ {W Γ_W}
            → Dec (W ≡ X) → Dec (W ≡ Y) → W ⦂[ Γ_W ]∈ Θ
            → τ !ˢ W ≡ (τ'' ⨾ˢ σ') !ˢ W
          hyp-dispatch = λ where
            (yes W≡X) _         m → hyp-W-eq-X m W≡X
            (no  W≢X) (yes W≡Y) m → hyp-W-eq-Y m W≡Y
            (no  W≢X) (no  W≢Y) m → hyp-W-other m W≢X W≢Y
          hyp : ∀ {W Γ_W} → W ⦂[ Γ_W ]∈ Θ → τ !ˢ W ≡ (τ'' ⨾ˢ σ') !ˢ W
          hyp {W} m = hyp-dispatch (W ≟ X) (W ≟ Y) m
          τ-eq : τ ≡ (τ'' ⨾ˢ σ')
          τ-eq = sub-equal-via-entries-Ctx {Θ = Θ} τ-wf comp-wf hyp
      in τ'' , τ''-wf , τ-eq

unification-correct-meta-tm :
  ∀ {Θ Θ_rem Γ Γ_X Γ_inv X ρ t}
    {r : Θ -ᵐ X ≡ Θ_rem} {X-in-Θ : X ⦂[ Γ_X ]∈ Θ}
    {wfρ : Γ ⊢ ρ ∶ Γ_X}
    {wfρ⁻¹ : Γ_X ⊢ ρ ⁻¹ ∶ Γ_inv} {t-wf : Θ_rem ، Γ_inv ⊢ t}
  → Θ ، Γ ⊢ mv X ρ
  → Θ ، Γ ⊢ t
  → UnificationSpec (un-meta-tm {Θ} {Θ_rem} {Γ} {Γ_X} {Γ_inv} {X} {ρ} {t}
                                  r X-in-Θ wfρ wfρ⁻¹ t-wf)
unification-correct-meta-tm
  {Θ = Θ} {Θ_rem = Θ_rem} {Γ = Γ} {Γ_X = Γ_X} {Γ_inv = Γ_inv}
  {X = X} {ρ = ρ} {t = t}
  {r = r} {X-in-Θ = X-in-Θ} {wfρ = wfρ} {wfρ⁻¹ = wfρ⁻¹} {t-wf = t-wf}
  _ _ =
  record
    { sound-typing  = sound-typing-proof
    ; sound-unifies = sound-unifies-proof
    ; mgu           = mgu-proof
    }
  where
    sound-typing-proof : Θ_rem ⊢ˢ mk-replace-subᴸ r ([ ρ ⁻¹ ] t) ∶ Θ
    sound-typing-proof =
      mk-replace-subᴸ-wf {Θ = Θ} {X = X} {Γ_X = Γ_X} {Θ_out = Θ_rem}
                          r ⊇ᴸ-refl [ρ⁻¹]t-wf X-in-Θ
      where
        [ρ⁻¹]t-wf : Θ_rem ، Γ_X ⊢ [ ρ ⁻¹ ] t
        [ρ⁻¹]t-wf = ren-term wfρ⁻¹ t-wf

    -- σ for short.
    σ' = mk-replace-subᴸ r ([ ρ ⁻¹ ] t)

    sound-unifies-proof : [ σ' ]ˢ (mv X ρ) ≡ [ σ' ]ˢ t
    sound-unifies-proof = sound-unifies-aux
      where
        σ-X-lookup : σ' !ˢ X ≡ just ([ ρ ⁻¹ ] t)
        σ-X-lookup = mk-replace-subᴸ-lookup-X r

        action-on-X : [ σ' ]ˢ (mv X ρ) ≡ [ ρ ] ([ ρ ⁻¹ ] t)
        action-on-X = aux
          where
            aux : [ σ' ]ˢ (mv X ρ) ≡ [ ρ ] ([ ρ ⁻¹ ] t)
            aux with σ' !ˢ X | σ-X-lookup
            ... | just .([ ρ ⁻¹ ] t) | refl = refl

        ρ-roundtrip : [ ρ ] ([ ρ ⁻¹ ] t) ≡ t
        ρ-roundtrip =
          ren-inv-round-trip-right
            {Θ = Θ_rem} {Γ = Γ} {Γ' = Γ_X} {Γ_inv = Γ_inv} {ρ = ρ} {t = t}
            wfρ wfρ⁻¹ t-wf

        -- σ acts as id on metas in Θ_rem.
        σ-id-on-Θrem :
          ∀ {W : Name} {Γ_W : Ctx} → W ⦂[ Γ_W ]∈ Θ_rem
          → σ' !ˢ W ≡ just (mv W (id-ren Γ_W))
        σ-id-on-Θrem {W} {Γ_W} m =
          mk-replace-subᴸ-lookup-other (mnd Θ) r m (removed-not-mem (mnd Θ) r m)

        action-on-t : [ σ' ]ˢ t ≡ t
        action-on-t = σ-acts-id-on-θ {σ = σ'} σ-id-on-Θrem t-wf

        sound-unifies-aux : [ σ' ]ˢ (mv X ρ) ≡ [ σ' ]ˢ t
        sound-unifies-aux = trans action-on-X (trans ρ-roundtrip (sym action-on-t))

    -- MGU proof: any unifier τ factors through σ' via the restriction.
    mgu-proof : ∀ {Θ'' τ}
              → Θ'' ⊢ˢ τ ∶ Θ
              → [ τ ]ˢ (mv X ρ) ≡ [ τ ]ˢ t
              → ∃[ τ'' ] ((Θ'' ⊢ˢ τ'' ∶ Θ_rem) × (τ ≡ (τ'' ⨾ˢ σ')))
    mgu-proof {Θ''} {τ} τ-wf eq-τ =
      let τ'' = restrict-subᴸ r τ
          τ''-wf : Θ'' ⊢ˢᴸ τ'' ∶ mlist Θ_rem
          τ''-wf = restrict-subᴸ-wf r τ-wf
          -- (1) [τ]ˢ t ≡ [τ'']ˢ t (because t is typed at Θ_rem, no X).
          τ-eq-τ''-on-t : [ τ ]ˢ t ≡ [ τ'' ]ˢ t
          τ-eq-τ''-on-t = sub-restrict-action-eq (mnd Θ) τ-wf r refl t-wf
          -- (2) τ at X: τ !ˢ X ≡ just τ_X with τ_X typed at Θ'' ، Γ_X.
          τ-X-info = σ-lookup-at-removed r (mnd Θ) τ-wf X-in-Θ
          τ_X = proj₁ τ-X-info
          τ-X-eq = proj₁ (proj₂ τ-X-info)
          τ_X-wf : Θ'' ، Γ_X ⊢ τ_X
          τ_X-wf = proj₂ (proj₂ τ-X-info)
          action-mvXρ : [ τ ]ˢ (mv X ρ) ≡ [ ρ ] τ_X
          action-mvXρ = sub-action-on-mv {τ} {X} {τ_X} {ρ} τ-X-eq
          -- (4) Derive τ_X ≡ [τ'']ˢ ([ρ⁻¹] t).
          ρ-τ_X-eq-τ''-t : [ ρ ] τ_X ≡ [ τ'' ]ˢ t
          ρ-τ_X-eq-τ''-t = trans (sym action-mvXρ) (trans eq-τ τ-eq-τ''-on-t)
          τ_X-eq-inv-t : τ_X ≡ [ ρ ⁻¹ ] ([ τ'' ]ˢ t)
          τ_X-eq-inv-t =
            trans (sym (ren-inv-round-trip-left
                          {Θ = Θ''} {Γ = Γ} {Γ' = Γ_X} {ρ = ρ} {t = τ_X}
                          wfρ τ_X-wf))
                  (cong (λ s → [ ρ ⁻¹ ] s) ρ-τ_X-eq-τ''-t)
          ⨾ˢ-commute-eq : [ ρ ⁻¹ ] ([ τ'' ]ˢ t) ≡ [ τ'' ]ˢ ([ ρ ⁻¹ ] t)
          ⨾ˢ-commute-eq = sym (⨾ˢ-ρ-commute {Θ = Θ''} {Θ' = Θ_rem}
                                              {Γ = Γ_inv} {Γ' = Γ_X}
                                              {σ = τ''} {ρ = ρ ⁻¹} {t = t}
                                              τ''-wf wfρ⁻¹ t-wf)
          τ_X-eq-final : τ_X ≡ [ τ'' ]ˢ ([ ρ ⁻¹ ] t)
          τ_X-eq-final = trans τ_X-eq-inv-t ⨾ˢ-commute-eq
          -- (5) Now τ ≡ τ'' ⨾ˢ σ' via sub-equal-via-entries-Ctx.
          comp-wf : Θ'' ⊢ˢ (τ'' ⨾ˢ σ') ∶ Θ
          comp-wf = sub-comp-wf {Θ''} {Θ_rem} {Θ} {τ''} {σ'} τ''-wf sound-typing-proof
          -- Compute lookups.
          σ'-lookup-X : σ' !ˢ X ≡ just ([ ρ ⁻¹ ] t)
          σ'-lookup-X = mk-replace-subᴸ-lookup-X r
          comp-lookup-X : (τ'' ⨾ˢ σ') !ˢ X ≡ just ([ τ'' ]ˢ ([ ρ ⁻¹ ] t))
          comp-lookup-X = sub-comp-lookup-just {τ''} {σ'} σ'-lookup-X
          σ'-lookup-other-eq :
            ∀ {W Γ_W} → W ⦂[ Γ_W ]∈ Θ_rem → W ≢ X
            → σ' !ˢ W ≡ just (mv W (id-ren Γ_W))
          σ'-lookup-other-eq m W≢X =
            mk-replace-subᴸ-lookup-other (mnd Θ) r m W≢X
          -- τ !ˢ W = (τ'' ⨾ˢ σ') !ˢ W for each W ∈ Θ.
          hyp-W-eq-X :
            ∀ {W Γ_W} → W ⦂[ Γ_W ]∈ Θ → W ≡ X → τ !ˢ W ≡ (τ'' ⨾ˢ σ') !ˢ W
          hyp-W-eq-X {W} m W≡X =
            subst (λ z → τ !ˢ z ≡ (τ'' ⨾ˢ σ') !ˢ z) (sym W≡X)
              (trans τ-X-eq
                     (trans (cong just τ_X-eq-final) (sym comp-lookup-X)))
          hyp-W-neq-X :
            ∀ {W Γ_W} → W ⦂[ Γ_W ]∈ Θ → W ≢ X → τ !ˢ W ≡ (τ'' ⨾ˢ σ') !ˢ W
          hyp-W-neq-X {W} {Γ_W} m W≢X =
            let W-in-Θ_rem = removal-preserves-mem W≢X m r
                σ'-W-eq = σ'-lookup-other-eq W-in-Θ_rem W≢X
                comp-W-eq : (τ'' ⨾ˢ σ') !ˢ W
                          ≡ just ([ τ'' ]ˢ (mv W (id-ren Γ_W)))
                comp-W-eq = sub-comp-lookup-just {τ''} {σ'} σ'-W-eq
                τ''-W-info = sub-lookup-wf τ''-wf W-in-Θ_rem
                t_W = proj₁ τ''-W-info
                τ''-W-eq = proj₁ (proj₂ τ''-W-info)
                t_W-wf = proj₂ (proj₂ τ''-W-info)
                τ''-eq-τ-W : τ'' !ˢ W ≡ τ !ˢ W
                τ''-eq-τ-W = restrict-sub-lookup-other τ-wf r W≢X
                τ-W-eq : τ !ˢ W ≡ just t_W
                τ-W-eq = trans (sym τ''-eq-τ-W) τ''-W-eq
                -- [τ'']ˢ (mv W (id-ren Γ_W)) = [id-ren Γ_W] t_W = t_W.
                action-mvW : [ τ'' ]ˢ (mv W (id-ren Γ_W)) ≡ t_W
                action-mvW =
                  trans (sub-action-on-mv {τ''} {W} {t_W} {id-ren Γ_W} τ''-W-eq)
                        (id-ren-action {Θ''} {Γ_W} t_W-wf)
            in trans τ-W-eq
                     (trans (cong just (sym action-mvW))
                            (sym comp-W-eq))
          hyp-case-on-eq :
            ∀ {W Γ_W} (dec-eq : Dec (W ≡ X))
            → W ⦂[ Γ_W ]∈ Θ
            → τ !ˢ W ≡ (τ'' ⨾ˢ σ') !ˢ W
          hyp-case-on-eq = λ where
            (yes W≡X) m → hyp-W-eq-X m W≡X
            (no  W≢X) m → hyp-W-neq-X m W≢X
          hyp : ∀ {W Γ_W} → W ⦂[ Γ_W ]∈ Θ → τ !ˢ W ≡ (τ'' ⨾ˢ σ') !ˢ W
          hyp {W} m = hyp-case-on-eq (W ≟ X) m
          τ-eq : τ ≡ (τ'' ⨾ˢ σ')
          τ-eq = sub-equal-via-entries-Ctx {Θ = Θ} τ-wf comp-wf hyp
      in τ'' , τ''-wf , τ-eq

unification-correct-tm-meta :
  ∀ {Θ Θ_rem Γ Γ_X Γ_inv X ρ t}
    {r : Θ -ᵐ X ≡ Θ_rem} {X-in-Θ : X ⦂[ Γ_X ]∈ Θ}
    {wfρ : Γ ⊢ ρ ∶ Γ_X}
    {wfρ⁻¹ : Γ_X ⊢ ρ ⁻¹ ∶ Γ_inv} {t-wf : Θ_rem ، Γ_inv ⊢ t}
  → Θ ، Γ ⊢ t
  → Θ ، Γ ⊢ mv X ρ
  → UnificationSpec (un-tm-meta {Θ} {Θ_rem} {Γ} {Γ_X} {Γ_inv} {X} {ρ} {t}
                                  r X-in-Θ wfρ wfρ⁻¹ t-wf)
unification-correct-tm-meta {r = r} {X-in-Θ = X-in-Θ} {wfρ = wfρ}
                            {wfρ⁻¹ = wfρ⁻¹} {t-wf = t-wf}
                            wf-t wf-mv =
  let sym-spec = unification-correct-meta-tm {r = r} {X-in-Θ = X-in-Θ}
                   {wfρ = wfρ} {wfρ⁻¹ = wfρ⁻¹} {t-wf = t-wf} wf-mv wf-t
  in record
       { sound-typing  = UnificationSpec.sound-typing sym-spec
       ; sound-unifies = sym (UnificationSpec.sound-unifies sym-spec)
       ; mgu = λ τ-wf eq → UnificationSpec.mgu sym-spec τ-wf (sym eq)
       }

------------------------------------------------------------------------
-- Top-level theorem, with UnVar / UnCon / UnFun proved inline by
-- structural induction on the unification derivation.
------------------------------------------------------------------------

unification-correct :
  ∀ {Θ Γ t₁ t₂ σ Θ'}
  → Θ ، Γ ⊢ t₁
  → Θ ، Γ ⊢ t₂
  → (uni : Θ ، Γ ⊢ t₁ ≐ t₂ ↝ σ ∶ Θ')
  → UnificationSpec uni
unification-correct wf₁ wf₂ un-var = unification-correct-var wf₁ wf₂
unification-correct wf₁ wf₂ un-con = unification-correct-con wf₁ wf₂
unification-correct {Θ = Θ}
  (wf-fun {t₁ = t₁}  {t₂ = t₂}  wf-t₁  wf-t₂)
  (wf-fun {t₁ = t₁'} {t₂ = t₂'} wf-t₁' wf-t₂')
  (un-fun {σ = σ_mid} {Θ_mid = Θ_mid} {σ' = σ'} {Θ' = Θ'} d₁ d₂) =
    record
      { sound-typing  = sub-comp-wf {Θ'} {Θ_mid} {Θ} σ'-wf σ_mid-wf
      ; sound-unifies = fun-unifies
      ; mgu = fun-mgu
      }
  where
    rec₁ = unification-correct wf-t₁ wf-t₁' d₁
    σ_mid-wf : Θ_mid ⊢ˢ σ_mid ∶ Θ
    σ_mid-wf = UnificationSpec.sound-typing rec₁

    [σmid]t₂-wf  = sub-term σ_mid-wf wf-t₂
    [σmid]t₂'-wf = sub-term σ_mid-wf wf-t₂'

    rec₂ = unification-correct [σmid]t₂-wf [σmid]t₂'-wf d₂
    σ'-wf : Θ' ⊢ˢ σ' ∶ Θ_mid
    σ'-wf = UnificationSpec.sound-typing rec₂

    -- sound-unifies
    fun-unifies : [ σ' ⨾ˢ σ_mid ]ˢ (fn _ t₁ t₂) ≡ [ σ' ⨾ˢ σ_mid ]ˢ (fn _ t₁' t₂')
    fun-unifies =
      let -- For t₁ / t₁':
          eq-t₁  : [ σ_mid ]ˢ t₁ ≡ [ σ_mid ]ˢ t₁'
          eq-t₁  = UnificationSpec.sound-unifies rec₁
          eq-t₁-comp : [ σ' ⨾ˢ σ_mid ]ˢ t₁ ≡ [ σ' ⨾ˢ σ_mid ]ˢ t₁'
          eq-t₁-comp = trans (sym (⨾ˢ-action σ'-wf σ_mid-wf wf-t₁))
                              (trans (cong [ σ' ]ˢ_ eq-t₁)
                                     (⨾ˢ-action σ'-wf σ_mid-wf wf-t₁'))
          -- For t₂ / t₂':
          eq-t₂  : [ σ' ]ˢ ([ σ_mid ]ˢ t₂) ≡ [ σ' ]ˢ ([ σ_mid ]ˢ t₂')
          eq-t₂  = UnificationSpec.sound-unifies rec₂
          eq-t₂-comp : [ σ' ⨾ˢ σ_mid ]ˢ t₂ ≡ [ σ' ⨾ˢ σ_mid ]ˢ t₂'
          eq-t₂-comp = trans (sym (⨾ˢ-action σ'-wf σ_mid-wf wf-t₂))
                              (trans eq-t₂
                                     (⨾ˢ-action σ'-wf σ_mid-wf wf-t₂'))
      in cong₂ (fn _) eq-t₁-comp eq-t₂-comp

    -- mgu
    fun-mgu : ∀ {Θ'' τ} → Θ'' ⊢ˢ τ ∶ Θ
            → [ τ ]ˢ (fn _ t₁ t₂) ≡ [ τ ]ˢ (fn _ t₁' t₂')
            → ∃[ τ'' ] ((Θ'' ⊢ˢ τ'' ∶ Θ') × (τ ≡ (τ'' ⨾ˢ (σ' ⨾ˢ σ_mid))))
    fun-mgu {Θ'' = Θ''} {τ = τ} τ-wf τ-unifies-fn =
      let -- Invert fn equation:
          eq-t₁ : [ τ ]ˢ t₁ ≡ [ τ ]ˢ t₁'
          eq-t₁ = fn-arg₁-eq τ-unifies-fn
          eq-t₂ : [ τ ]ˢ t₂ ≡ [ τ ]ˢ t₂'
          eq-t₂ = fn-arg₂-eq τ-unifies-fn
          -- Apply rec₁'s mgu:
          mgu₁ = UnificationSpec.mgu rec₁ τ-wf eq-t₁
          τ-a    = proj₁ mgu₁
          τ-a-wf = proj₁ (proj₂ mgu₁)
          τ≡τ-a-σmid : τ ≡ (τ-a ⨾ˢ σ_mid)
          τ≡τ-a-σmid = proj₂ (proj₂ mgu₁)
          -- Lift eq-t₂ through ⨾ˢ-action: [τ-a]ˢ([σ_mid]ˢtᵢ) ≡ [τ-a⨾ˢσ_mid]ˢtᵢ
          -- and τ-a⨾ˢσ_mid ≡ τ (from sym τ≡τ-a-σmid).
          eq-t₂-via-τ-a : [ τ-a ]ˢ ([ σ_mid ]ˢ t₂) ≡ [ τ-a ]ˢ ([ σ_mid ]ˢ t₂')
          eq-t₂-via-τ-a =
            let τ-aσmid≡τ : (τ-a ⨾ˢ σ_mid) ≡ τ
                τ-aσmid≡τ = sym τ≡τ-a-σmid
                act-t₂  = ⨾ˢ-action τ-a-wf σ_mid-wf wf-t₂
                act-t₂' = ⨾ˢ-action τ-a-wf σ_mid-wf wf-t₂'
                step2   = cong (λ s → [ s ]ˢ t₂)  τ-aσmid≡τ
                step4   = cong (λ s → [ s ]ˢ t₂') τ≡τ-a-σmid
            in trans act-t₂
                     (trans step2
                            (trans eq-t₂
                                   (trans step4 (sym act-t₂'))))
          -- Apply rec₂'s mgu:
          mgu₂ = UnificationSpec.mgu rec₂ τ-a-wf eq-t₂-via-τ-a
          τ-b    = proj₁ mgu₂
          τ-b-wf = proj₁ (proj₂ mgu₂)
          τ-a≡τ-b-σ' : τ-a ≡ (τ-b ⨾ˢ σ')
          τ-a≡τ-b-σ' = proj₂ (proj₂ mgu₂)
          -- Chain: τ ≡ τ-a ⨾ˢ σ_mid ≡ (τ-b ⨾ˢ σ') ⨾ˢ σ_mid ≡ τ-b ⨾ˢ (σ' ⨾ˢ σ_mid)
          chain : τ ≡ (τ-b ⨾ˢ (σ' ⨾ˢ σ_mid))
          chain = trans τ≡τ-a-σmid
                        (trans (cong (_⨾ˢ σ_mid) τ-a≡τ-b-σ')
                               (⨾ˢ-assoc {Θ''} {Θ'} {Θ_mid} {Θ}
                                          τ-b-wf σ'-wf σ_mid-wf))
      in τ-b , τ-b-wf , chain
      where
        -- Inversion of `fn f x y ≡ fn f x' y'` to obtain x ≡ x' and y ≡ y'.
        fn-arg₁-eq : ∀ {f x x' y y'}
                   → fn f x y ≡ fn f x' y' → x ≡ x'
        fn-arg₁-eq refl = refl
        fn-arg₂-eq : ∀ {f x x' y y'}
                   → fn f x y ≡ fn f x' y' → y ≡ y'
        fn-arg₂-eq refl = refl
unification-correct wf₁ wf₂ (un-meta-same r X-in-Θ coeq fresh) =
  unification-correct-meta-same {r = r} {X-in-Θ = X-in-Θ}
    {coeq = coeq} {fresh = fresh} wf₁ wf₂
unification-correct wf₁ wf₂ (un-meta-diff r₁ r₂ X-in-Θ Y-in-inter push fresh-Θ fresh) =
  unification-correct-meta-diff {r₁ = r₁} {r₂ = r₂}
    {X-in-Θ = X-in-Θ} {Y-in-Θ-inter = Y-in-inter}
    {push = push} {fresh-Θ = fresh-Θ} {fresh = fresh} wf₁ wf₂
unification-correct wf₁ wf₂ (un-meta-tm r X-in-Θ wfρ wfρ⁻¹ t-wf) =
  unification-correct-meta-tm {r = r} {X-in-Θ = X-in-Θ} {wfρ = wfρ}
    {wfρ⁻¹ = wfρ⁻¹} {t-wf = t-wf} wf₁ wf₂
unification-correct wf₁ wf₂ (un-tm-meta r X-in-Θ wfρ wfρ⁻¹ t-wf) =
  unification-correct-tm-meta {r = r} {X-in-Θ = X-in-Θ} {wfρ = wfρ}
    {wfρ⁻¹ = wfρ⁻¹} {t-wf = t-wf} wf₁ wf₂
