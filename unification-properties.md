# Inductive proofs for unification.md

## 0. Corrections to `unification.md`

The proofs below assume the following corrections to the rules and definitions in `unification.md`.

1. **Rule `f(t1,t2) = f(t1',t2')`.** Three problems: the first premise prints `t1 = t2` but should be `t1 = t1'`; the second premise's trailing `↝ σ'; Θ''` should be `↝ σ' : Θ''`; and the *order* of composition in the conclusion is reversed. The conclusion's substitution must take `Θ`-terms to `Θ''`-terms by applying `σ` first (which takes `Θ` to `Θ'`) and then `σ'` (which takes `Θ'` to `Θ''`). Under the file's convention `[σ_a; σ_b]t = [σ_a]([σ_b]t)` (right factor applied first), this composite is `σ'; σ`, not `σ; σ'`. Corrected rule:

   ```
   Θ; Γ ⊢ t1 = t1' ↝ σ : Θ'    Θ'; Γ ⊢ [σ]t2 = [σ]t2' ↝ σ' : Θ''
   ———————————————————————————————————————————————————————————————
   Θ; Γ ⊢ f(t1, t2) = f(t1', t2') ↝ σ'; σ : Θ''
   ```

2. **Rules `X = t` and `t = X`.** `id(θ')` has a lowercase `θ`; should be `id(Θ')`. The output substitution should be the full `id(Θ'), t/X` (which the file already writes — it is just the case typo).

3. **Rule `X = Y`.** The substitution `Z/X, Z/Y` is missing entries for the other metavariables of `Θ'`. The intended output is `id(Θ'), Z/X, Z/Y`, which has type `Θ', Z:[Γ₃] ⊢ _ : Θ', X:[Γ₁], Y:[Γ₂] = Θ`. Side condition `X ≠ Y` is implicit (the `X = X` rule handles the diagonal).

4. **Rules `X = t` and `t = X`** need the side condition `t` is not a metavariable, to avoid overlap with the `X = X` and `X = Y` cases. (The proof of MGU does not require this for soundness, but the system is not syntax-directed without it.)

5. **Metavariable contexts.** The rules `Θ ≡ Θ', X:[Γ₁], Y:[Γ₂]` and `Θ = Θ', X:[Γ']` require `X` (resp. `X`, `Y`) to be at the end of `Θ`. The proofs below treat `Θ` as a context up to permutation of its entries, i.e. as a finite map from metavariables to dependency contexts. Without this, the unification rules would be overly restrictive.

6. **Convention for composition.** `σ; σ'` means *apply σ' first, then σ*; equivalently, `[σ;σ']t = [σ]([σ']t)`. The typing reads "if `Θ ⊢ σ : Θ'` and `Θ' ⊢ σ' : Θ''` then `Θ ⊢ σ;σ' : Θ''`": `Θ'` is the *domain* (the metavariables being substituted *for*) and `Θ` the *codomain* (where the replacement terms live).

**Proof format.** Each proof is presented as numbered logical steps. Each step's justification appears in brackets, naming the rule, lemma, or hypothesis used and citing earlier line numbers `(n)` whose premises feed into it. `[IH on (n)]` means the inductive hypothesis applied to the subderivation/structure identified on line `n`. Line numbers restart at `1` within each case. `[hyp]` marks a top-level hypothesis of the theorem.

---

## 1. Weakening (`Γ ⊆ Γ'`)

### 1.1 Reflexivity: `Γ ⊆ Γ`

**Induction metric:** structure of `Γ`.

**Case `Γ = ·`:**
1. `· ⊆ ·`                                                   [WkNil]

**Case `Γ = Γ₀, a`:**
1. `Γ₀ ⊆ Γ₀`                                                 [IH on `Γ₀`]
2. `Γ₀, a ⊆ Γ₀, a`                                           [WkCons, (1)]

### 1.2 Transitivity: if `Γ ⊆ Γ'` and `Γ' ⊆ Γ''` then `Γ ⊆ Γ''`

**Induction metric:** height of `D₂ : Γ' ⊆ Γ''`. Universally quantified over `Γ` and `D₁ : Γ ⊆ Γ'`; the IH is instantiated at each strict subderivation of `D₂` with a freshly-supplied `D₁`-like derivation. Case-split on the last rule of `D₂`.

**Case `D₂` ends in WkNil** (so `Γ' = · = Γ''`):
1. `Γ ⊆ ·`                                                   [hyp `D₁`, with `Γ' = ·`]
2. The last rule of (1) must be WkNil, so `Γ = ·`            [inversion on (1)]
3. `· ⊆ ·`                                                   [WkNil]
4. `Γ ⊆ Γ''`                                                 [(2), (3)]

**Case `D₂` ends in WkCons** (so `Γ' = Γ'₀, a` and `Γ'' = Γ''₀, a`, from `D₂' : Γ'₀ ⊆ Γ''₀`).

  Case-split on the last rule of `D₁ : Γ ⊆ Γ'₀, a`:

  **Sub-case `D₁` ends in WkCons** (so `Γ = Γ₀, a`, from `D₁' : Γ₀ ⊆ Γ'₀`):
  1. `Γ₀ ⊆ Γ'₀`                                              [`D₁'`]
  2. `Γ'₀ ⊆ Γ''₀`                                            [`D₂'`]
  3. `Γ₀ ⊆ Γ''₀`                                             [IH on (2) with (1)]
  4. `Γ₀, a ⊆ Γ''₀, a`                                       [WkCons, (3)]
  5. `Γ ⊆ Γ''`                                               [(4), case shape]

  **Sub-case `D₁` ends in WkSkip** (so `D₁' : Γ ⊆ Γ'₀`):
  1. `Γ ⊆ Γ'₀`                                               [`D₁'`]
  2. `Γ'₀ ⊆ Γ''₀`                                            [`D₂'`]
  3. `Γ ⊆ Γ''₀`                                              [IH on (2) with (1)]
  4. `Γ ⊆ Γ''₀, a`                                           [WkSkip, (3)]
  5. `Γ ⊆ Γ''`                                               [(4), case shape]

  **Sub-case `D₁` ends in WkNil:** would force `Γ'₀, a = ·`, impossible.

**Case `D₂` ends in WkSkip** (so `Γ'' = Γ''₀, a`, from `D₂' : Γ' ⊆ Γ''₀`):
1. `Γ ⊆ Γ'`                                                  [hyp `D₁`]
2. `Γ' ⊆ Γ''₀`                                               [`D₂'`]
3. `Γ ⊆ Γ''₀`                                                [IH on (2) with (1)]
4. `Γ ⊆ Γ''₀, a`                                             [WkSkip, (3)]
5. `Γ ⊆ Γ''`                                                 [(4), case shape]

### 1.3 Antisymmetry: if `Γ ⊆ Γ'` and `Γ' ⊆ Γ` then `Γ = Γ'`

**Auxiliary Length Lemma.** If `Γ ⊆ Γ'` then `|Γ| ≤ |Γ'|`.

  *Induction metric:* height of `D : Γ ⊆ Γ'`.

  **Case WkNil:**
  1. `|·| = 0 ≤ 0 = |·|`                                     [arithmetic]

  **Case WkCons** (from `D' : Γ₀ ⊆ Γ'₀`):
  1. `|Γ₀| ≤ |Γ'₀|`                                          [IH on `D'`]
  2. `|Γ₀, a| = |Γ₀| + 1 ≤ |Γ'₀| + 1 = |Γ'₀, a|`             [(1), arithmetic]

  **Case WkSkip** (from `D' : Γ ⊆ Γ'₀`):
  1. `|Γ| ≤ |Γ'₀|`                                           [IH on `D'`]
  2. `|Γ| ≤ |Γ'₀| < |Γ'₀| + 1 = |Γ'₀, a|`                    [(1), arithmetic]

**Antisymmetry proof.** Induction on `D₁ : Γ ⊆ Γ'`, with `D₂ : Γ' ⊆ Γ` re-derived from the hypothesis at each recursive call.

**Case `D₁` ends in WkNil:**
1. `Γ = · = Γ'`                                              [case shape]

**Case `D₁` ends in WkCons** (so `Γ = Γ₀, a`, `Γ' = Γ'₀, a`, from `D₁' : Γ₀ ⊆ Γ'₀`).

  Case-split on the last rule of `D₂ : Γ'₀, a ⊆ Γ₀, a`:

  **Sub-case `D₂` ends in WkCons** (from `D₂' : Γ'₀ ⊆ Γ₀`):
  1. `Γ₀ ⊆ Γ'₀`                                              [`D₁'`]
  2. `Γ'₀ ⊆ Γ₀`                                              [`D₂'`]
  3. `Γ₀ = Γ'₀`                                              [IH on (1) with (2)]
  4. `Γ = Γ₀, a = Γ'₀, a = Γ'`                               [(3), case shape]

  **Sub-case `D₂` ends in WkSkip** (from `D₂' : Γ'₀, a ⊆ Γ₀`):
  1. `|Γ'₀, a| ≤ |Γ₀|`, i.e. `|Γ'₀| + 1 ≤ |Γ₀|`              [Length Lemma on `D₂'`]
  2. `|Γ₀| ≤ |Γ'₀|`                                          [Length Lemma on `D₁'`]
  3. `|Γ'₀| + 1 ≤ |Γ'₀|`                                     [(1), (2)]
  4. Contradiction; this sub-case is impossible.              [(3)]

**Case `D₁` ends in WkSkip** (so `Γ' = Γ'₀, a`, from `D₁' : Γ ⊆ Γ'₀`):
1. `|Γ| ≤ |Γ'₀|`                                             [Length Lemma on `D₁'`]
2. `|Γ'| ≤ |Γ|`, i.e. `|Γ'₀| + 1 ≤ |Γ|`                      [Length Lemma on `D₂ : Γ' ⊆ Γ`]
3. `|Γ'₀| + 1 ≤ |Γ'₀|`                                       [(1), (2)]
4. Contradiction; this case is impossible.                    [(3)]

### 1.4 Lookup preservation: if `Γ ⊆ Γ'` and `x ∈ Γ` then `x ∈ Γ'`

**Induction metric:** height of `D : Γ ⊆ Γ'`. Universally quantified over the derivation of `x ∈ Γ`.

**Case `D` ends in WkNil** (so `Γ = ·`):
1. `x ∈ ·`                                                   [hyp]
2. No rule (InHere/InThere) concludes `x ∈ ·`; vacuous.       [inversion on (1)]

**Case `D` ends in WkCons** (so `Γ = Γ₀, a`, `Γ' = Γ'₀, a`, from `D' : Γ₀ ⊆ Γ'₀`).

  Case-split on the last rule of `E : x ∈ Γ₀, a`:

  **Sub-case `E` ends in InHere** (so `x = a`):
  1. `a ∈ Γ'₀, a`                                            [InHere]
  2. `x ∈ Γ'`                                                [(1), `x = a`]

  **Sub-case `E` ends in InThere** (from `E' : x ∈ Γ₀`):
  1. `x ∈ Γ₀`                                                [`E'`]
  2. `x ∈ Γ'₀`                                               [IH on `D'` with (1)]
  3. `x ∈ Γ'₀, a`                                            [InThere, (2)]
  4. `x ∈ Γ'`                                                [(3), case shape]

**Case `D` ends in WkSkip** (so `Γ' = Γ'₀, a`, from `D' : Γ ⊆ Γ'₀`):
1. `x ∈ Γ`                                                   [hyp]
2. `x ∈ Γ'₀`                                                 [IH on `D'` with (1)]
3. `x ∈ Γ'₀, a`                                              [InThere, (2)]
4. `x ∈ Γ'`                                                  [(3), case shape]

### 1.5 Term weakening: if `Γ ⊆ Γ'` and `Θ; Γ ⊢ t` then `Θ; Γ' ⊢ t`

**Induction metric:** height of `D : Θ; Γ ⊢ t`. Universally quantified over `Γ'` and the derivation of `Γ ⊆ Γ'`.

**Case `D` ends in WfVar** (from `a ∈ Γ`):
1. `a ∈ Γ`                                                   [premise of `D`]
2. `Γ ⊆ Γ'`                                                  [hyp]
3. `a ∈ Γ'`                                                  [§1.4 on (2), (1)]
4. `Θ; Γ' ⊢ a`                                               [WfVar, (3)]

**Case `D` ends in WfCon:**
1. `Θ; Γ' ⊢ c`                                               [WfCon]

**Case `D` ends in WfFun** (from `D₁ : Θ; Γ ⊢ t1` and `D₂ : Θ; Γ ⊢ t2`):
1. `Γ ⊆ Γ'`                                                  [hyp]
2. `Θ; Γ' ⊢ t1`                                              [IH on `D₁` with (1)]
3. `Θ; Γ' ⊢ t2`                                              [IH on `D₂` with (1)]
4. `Θ; Γ' ⊢ f(t1, t2)`                                       [WfFun, (2), (3)]

**Case `D` ends in WfMeta** (from `X:[Γ_X] ∈ Θ` and `Γ_X ⊆ Γ`):
1. `X:[Γ_X] ∈ Θ`                                             [premise of `D`]
2. `Γ_X ⊆ Γ`                                                 [premise of `D`]
3. `Γ ⊆ Γ'`                                                  [hyp]
4. `Γ_X ⊆ Γ'`                                                [§1.2 on (2), (3)]
5. `Θ; Γ' ⊢ X`                                               [WfMeta, (1), (4)]

---

## 2. Lookup and Application

We assume metavariable names in `Θ` are distinct (no shadowing), so `X:[Γ] ∈ Θ` determines `Γ` uniquely. Likewise, the entries of a substitution `σ` use distinct metavariable names.

### 2.1 If `Θ ⊢ σ : Θ'` and `X:[Γ] ∈ Θ'`, then `Θ; Γ ⊢ σ(X)`

**Induction metric:** height of `D : Θ ⊢ σ : Θ'`. Universally quantified over `X` and `Γ`.

**Case `D` ends in SubNil** (so `Θ' = ·`):
1. `X:[Γ] ∈ ·`                                               [hyp]
2. No rule concludes `_:[_] ∈ ·`; vacuous.                    [inversion on (1)]

**Case `D` ends in SubCons** (so `σ = σ₀, t/X₀`, `Θ' = Θ'₀, X₀:[Γ₀]`, from `D₁ : Θ ⊢ σ₀ : Θ'₀` and `D₂ : Θ; Γ₀ ⊢ t`).

  Case-split on `X:[Γ] ∈ Θ'₀, X₀:[Γ₀]`:

  **Sub-case `X = X₀`** (so `Γ = Γ₀` by name uniqueness):
  1. `(σ₀, t/X₀)(X) = t`                                     [lookup-head]
  2. `Θ; Γ₀ ⊢ t`                                             [`D₂`]
  3. `Θ; Γ ⊢ σ(X)`                                           [(1), (2), `Γ = Γ₀`]

  **Sub-case `X ≠ X₀`** (so `X:[Γ] ∈ Θ'₀`):
  1. `X:[Γ] ∈ Θ'₀`                                           [case shape]
  2. `(σ₀, t/X₀)(X) = σ₀(X)`                                 [lookup-cons]
  3. `Θ; Γ ⊢ σ₀(X)`                                          [IH on `D₁` with (1)]
  4. `Θ; Γ ⊢ σ(X)`                                           [(2), (3)]

### 2.2 If `Θ ⊢ σ : Θ'` and `Θ'; Γ ⊢ t`, then `Θ; Γ ⊢ [σ]t`

**Induction metric:** height of `D : Θ'; Γ ⊢ t`. Universally quantified over `Γ` and the typing derivation; `σ` and `Θ ⊢ σ : Θ'` are kept fixed across the induction.

**Case `D` ends in WfVar** (from `a ∈ Γ`):
1. `[σ]a = a`                                                [substitution-on-`a`]
2. `a ∈ Γ`                                                   [premise of `D`]
3. `Θ; Γ ⊢ a`                                                [WfVar, (2)]
4. `Θ; Γ ⊢ [σ]a`                                             [(1), (3)]

**Case `D` ends in WfCon:**
1. `[σ]c = c`                                                [substitution-on-`c`]
2. `Θ; Γ ⊢ c`                                                [WfCon]
3. `Θ; Γ ⊢ [σ]c`                                             [(1), (2)]

**Case `D` ends in WfFun** (from `D₁ : Θ'; Γ ⊢ t₁` and `D₂ : Θ'; Γ ⊢ t₂`):
1. `[σ]f(t₁,t₂) = f([σ]t₁, [σ]t₂)`                           [substitution-on-`f`]
2. `Θ; Γ ⊢ [σ]t₁`                                            [IH on `D₁`]
3. `Θ; Γ ⊢ [σ]t₂`                                            [IH on `D₂`]
4. `Θ; Γ ⊢ f([σ]t₁, [σ]t₂)`                                  [WfFun, (2), (3)]
5. `Θ; Γ ⊢ [σ]f(t₁,t₂)`                                      [(1), (4)]

**Case `D` ends in WfMeta** (from `X:[Γ_X] ∈ Θ'` and `Γ_X ⊆ Γ`):
1. `[σ]X = σ(X)`                                             [substitution-on-`X`]
2. `X:[Γ_X] ∈ Θ'`                                            [premise of `D`]
3. `Γ_X ⊆ Γ`                                                 [premise of `D`]
4. `Θ; Γ_X ⊢ σ(X)`                                           [§2.1 on `Θ ⊢ σ : Θ'` and (2)]
5. `Θ; Γ ⊢ σ(X)`                                             [§1.5 on (3), (4)]
6. `Θ; Γ ⊢ [σ]X`                                             [(1), (5)]

---

## 3. Identity

### Aux 3.0 (metavariable weakening for terms)

If `Θ; Γ ⊢ t` and `Y ∉ Θ`, then `(Θ, Y:[Γ_Y]); Γ ⊢ t`.

**Induction metric:** height of `D : Θ; Γ ⊢ t`.

**Case `D` ends in WfVar** (from `a ∈ Γ`):
1. `a ∈ Γ`                                                   [premise of `D`]
2. `(Θ, Y:[Γ_Y]); Γ ⊢ a`                                     [WfVar, (1)]

**Case `D` ends in WfCon:**
1. `(Θ, Y:[Γ_Y]); Γ ⊢ c`                                     [WfCon]

**Case `D` ends in WfFun** (from `D₁ : Θ; Γ ⊢ t₁`, `D₂ : Θ; Γ ⊢ t₂`):
1. `(Θ, Y:[Γ_Y]); Γ ⊢ t₁`                                    [IH on `D₁`]
2. `(Θ, Y:[Γ_Y]); Γ ⊢ t₂`                                    [IH on `D₂`]
3. `(Θ, Y:[Γ_Y]); Γ ⊢ f(t₁, t₂)`                             [WfFun, (1), (2)]

**Case `D` ends in WfMeta** (from `X:[Γ_X] ∈ Θ` and `Γ_X ⊆ Γ`):
1. `X:[Γ_X] ∈ Θ`                                             [premise of `D`]
2. `X ≠ Y`                                                   [`Y ∉ Θ` and (1)]
3. `X:[Γ_X] ∈ Θ, Y:[Γ_Y]`                                    [InThere, (1), (2)]
4. `Γ_X ⊆ Γ`                                                 [premise of `D`]
5. `(Θ, Y:[Γ_Y]); Γ ⊢ X`                                     [WfMeta, (3), (4)]

### Aux 3.0b (metavariable weakening for substitutions)

If `Θ ⊢ σ : Θ'` and `Y ∉ Θ`, then `(Θ, Y:[Γ_Y]) ⊢ σ : Θ'`.

**Induction metric:** height of `D : Θ ⊢ σ : Θ'`.

**Case `D` ends in SubNil:**
1. `(Θ, Y:[Γ_Y]) ⊢ · : ·`                                    [SubNil]

**Case `D` ends in SubCons** (so `σ = σ₀, t/X`, `Θ' = Θ'₀, X:[Γ]`, from `D₁ : Θ ⊢ σ₀ : Θ'₀` and `D₂ : Θ; Γ ⊢ t`):
1. `(Θ, Y:[Γ_Y]) ⊢ σ₀ : Θ'₀`                                 [IH on `D₁`]
2. `(Θ, Y:[Γ_Y]); Γ ⊢ t`                                     [Aux 3.0 on `D₂`]
3. `(Θ, Y:[Γ_Y]) ⊢ (σ₀, t/X) : (Θ'₀, X:[Γ])`                 [SubCons, (1), (2)]

### Aux 3.2a (identity lookup)

If `X:[Γ_X] ∈ Θ` then `id(Θ)(X) = X`.

**Induction metric:** structure of `Θ`.

**Case `Θ = ·`:**
1. `X:[Γ_X] ∈ ·` is impossible; vacuous.

**Case `Θ = Θ₀, Y:[Γ_Y]`:**

  Case-split on `X:[Γ_X] ∈ Θ₀, Y:[Γ_Y]`:

  **Sub-case head** (`X = Y`):
  1. `id(Θ) = id(Θ₀), Y/Y`                                   [defn of `id`]
  2. `id(Θ)(Y) = Y`                                          [(1), lookup-head]
  3. `id(Θ)(X) = X`                                          [(2), `X = Y`]

  **Sub-case cons** (`X ≠ Y`, so `X:[Γ_X] ∈ Θ₀`):
  1. `X:[Γ_X] ∈ Θ₀`                                          [case shape]
  2. `id(Θ) = id(Θ₀), Y/Y`                                   [defn of `id`]
  3. `id(Θ)(X) = id(Θ₀)(X)`                                  [(2), lookup-cons, `X ≠ Y`]
  4. `id(Θ₀)(X) = X`                                         [IH on (1)]
  5. `id(Θ)(X) = X`                                          [(3), (4)]

### 3.1 `Θ ⊢ id(Θ) : Θ`

**Induction metric:** structure of `Θ`.

**Case `Θ = ·`:**
1. `id(·) = ·`                                               [defn of `id`]
2. `· ⊢ · : ·`                                               [SubNil]
3. `Θ ⊢ id(Θ) : Θ`                                           [(1), (2)]

**Case `Θ = Θ₀, X:[Γ]`** (with `X ∉ Θ₀` by name uniqueness):
1. `id(Θ) = id(Θ₀), X/X`                                     [defn of `id`]
2. `Θ₀ ⊢ id(Θ₀) : Θ₀`                                        [IH on `Θ₀`]
3. `(Θ₀, X:[Γ]) ⊢ id(Θ₀) : Θ₀`                               [Aux 3.0b on (2) with `Y := X`]
4. `Γ ⊆ Γ`                                                   [§1.1]
5. `X:[Γ] ∈ Θ₀, X:[Γ]`                                       [InHere]
6. `(Θ₀, X:[Γ]); Γ ⊢ X`                                      [WfMeta, (5), (4)]
7. `(Θ₀, X:[Γ]) ⊢ (id(Θ₀), X/X) : (Θ₀, X:[Γ])`               [SubCons, (3), (6)]
8. `Θ ⊢ id(Θ) : Θ`                                           [(1), (7)]

### 3.2 If `Θ; Γ ⊢ t` then `[id(Θ)]t = t`

**Induction metric:** height of `D : Θ; Γ ⊢ t`.

**Case `D` ends in WfVar:**
1. `[id(Θ)]a = a`                                            [substitution-on-`a`]

**Case `D` ends in WfCon:**
1. `[id(Θ)]c = c`                                            [substitution-on-`c`]

**Case `D` ends in WfFun** (from `D₁`, `D₂`):
1. `[id(Θ)]f(t₁,t₂) = f([id(Θ)]t₁, [id(Θ)]t₂)`               [substitution-on-`f`]
2. `[id(Θ)]t₁ = t₁`                                          [IH on `D₁`]
3. `[id(Θ)]t₂ = t₂`                                          [IH on `D₂`]
4. `[id(Θ)]f(t₁,t₂) = f(t₁, t₂)`                             [(1), (2), (3)]

**Case `D` ends in WfMeta** (from `X:[Γ_X] ∈ Θ` and `Γ_X ⊆ Γ`):
1. `[id(Θ)]X = id(Θ)(X)`                                     [substitution-on-`X`]
2. `X:[Γ_X] ∈ Θ`                                             [premise of `D`]
3. `id(Θ)(X) = X`                                            [Aux 3.2a on (2)]
4. `[id(Θ)]X = X`                                            [(1), (3)]

---

## 4. Composition

### 4.1 If `Θ ⊢ σ : Θ'` and `Θ' ⊢ σ' : Θ''` then `Θ ⊢ σ; σ' : Θ''`

**Induction metric:** height of `D : Θ' ⊢ σ' : Θ''`. `σ` and `Θ ⊢ σ : Θ'` are fixed across the induction.

**Case `D` ends in SubNil** (so `σ' = ·`, `Θ'' = ·`):
1. `σ; · = ·`                                                [defn of composition]
2. `Θ ⊢ · : ·`                                               [SubNil]
3. `Θ ⊢ σ; σ' : Θ''`                                         [(1), (2)]

**Case `D` ends in SubCons** (so `σ' = σ'₀, t/X`, `Θ'' = Θ''₀, X:[Γ]`, from `D₁ : Θ' ⊢ σ'₀ : Θ''₀` and `D₂ : Θ'; Γ ⊢ t`):
1. `σ; (σ'₀, t/X) = (σ; σ'₀), [σ]t/X`                        [defn of composition]
2. `Θ ⊢ σ; σ'₀ : Θ''₀`                                       [IH on `D₁`]
3. `Θ; Γ ⊢ [σ]t`                                             [§2.2 on `Θ ⊢ σ : Θ'` and `D₂`]
4. `Θ ⊢ (σ; σ'₀), [σ]t/X : (Θ''₀, X:[Γ])`                    [SubCons, (2), (3)]
5. `Θ ⊢ σ; σ' : Θ''`                                         [(1), (4)]

### Aux 4.2a (composition lookup)

For all `σ, σ'`, and all metavariables `X`: `(σ; σ')(X) = [σ](σ'(X))` (when both sides are defined).

**Induction metric:** structure of `σ'`.

**Case `σ' = ·`:**
1. `X ∉ dom(·)`; both sides undefined; vacuous.

**Case `σ' = σ'₀, t/Y`:**

  **Sub-case `X = Y`:**
  1. `σ; σ' = (σ; σ'₀), [σ]t/Y`                              [defn of composition]
  2. `(σ; σ')(Y) = [σ]t`                                     [(1), lookup-head]
  3. `σ'(Y) = t`                                             [lookup-head]
  4. `[σ](σ'(Y)) = [σ]t`                                     [(3)]
  5. `(σ; σ')(X) = [σ](σ'(X))`                               [(2), (4), `X = Y`]

  **Sub-case `X ≠ Y`:**
  1. `σ; σ' = (σ; σ'₀), [σ]t/Y`                              [defn of composition]
  2. `(σ; σ')(X) = (σ; σ'₀)(X)`                              [(1), lookup-cons]
  3. `σ'(X) = σ'₀(X)`                                        [lookup-cons]
  4. `(σ; σ'₀)(X) = [σ](σ'₀(X))`                             [IH on `σ'₀`]
  5. `(σ; σ')(X) = [σ](σ'(X))`                               [(2), (3), (4)]

### 4.2 `[σ]([σ']t) = [σ; σ']t`

Purely syntactic; no typing assumption needed.

**Induction metric:** structure of `t`.

**Case `t = a`:**
1. `[σ']a = a`                                               [substitution-on-`a`]
2. `[σ]a = a`                                                [substitution-on-`a`]
3. `[σ]([σ']a) = a`                                          [(1), (2)]
4. `[σ; σ']a = a`                                            [substitution-on-`a`]
5. `[σ]([σ']a) = [σ; σ']a`                                   [(3), (4)]

**Case `t = c`:**
1. `[σ]([σ']c) = c = [σ; σ']c`                               [substitution-on-`c` thrice]

**Case `t = f(t₁,t₂)`:**
1. `[σ']f(t₁,t₂) = f([σ']t₁, [σ']t₂)`                        [substitution-on-`f`]
2. `[σ]f([σ']t₁, [σ']t₂) = f([σ][σ']t₁, [σ][σ']t₂)`          [substitution-on-`f`]
3. `[σ][σ']t₁ = [σ; σ']t₁`                                   [IH on `t₁`]
4. `[σ][σ']t₂ = [σ; σ']t₂`                                   [IH on `t₂`]
5. `[σ]([σ']f(t₁,t₂)) = f([σ; σ']t₁, [σ; σ']t₂)`             [(1), (2), (3), (4)]
6. `[σ; σ']f(t₁,t₂) = f([σ; σ']t₁, [σ; σ']t₂)`               [substitution-on-`f`]
7. `[σ]([σ']f(t₁,t₂)) = [σ; σ']f(t₁,t₂)`                     [(5), (6)]

**Case `t = X`:**
1. `[σ']X = σ'(X)`                                           [substitution-on-`X`]
2. `[σ](σ'(X)) = (σ; σ')(X)`                                 [Aux 4.2a]
3. `(σ; σ')(X) = [σ; σ']X`                                   [substitution-on-`X`]
4. `[σ]([σ']X) = [σ; σ']X`                                   [(1), (2), (3)]

### Cor 4.3 (left identity)

For all `σ` with `Θ ⊢ σ : Θ'`: `σ; id(Θ') = σ`. (Substitutions equal entry-wise on their common domain.)

  For each `X:[Γ] ∈ Θ'`:
  1. `(σ; id(Θ'))(X) = [σ](id(Θ')(X))`                       [Aux 4.2a]
  2. `id(Θ')(X) = X`                                         [Aux 3.2a]
  3. `[σ](X) = σ(X)`                                         [substitution-on-`X`]
  4. `(σ; id(Θ'))(X) = σ(X)`                                 [(1), (2), (3)]

### Cor 4.4 (right identity)

For all `σ` with `Θ ⊢ σ : Θ'`: `id(Θ); σ = σ`.

**Induction metric:** structure of `σ`.

**Case `σ = ·`:**
1. `id(Θ); · = ·`                                            [defn of composition]

**Case `σ = σ₀, t/X`** (so `Θ' = Θ'₀, X:[Γ]`, from `D₁ : Θ ⊢ σ₀ : Θ'₀` and `D₂ : Θ; Γ ⊢ t`):
1. `id(Θ); (σ₀, t/X) = (id(Θ); σ₀), [id(Θ)]t/X`              [defn of composition]
2. `id(Θ); σ₀ = σ₀`                                          [IH on `σ₀`]
3. `[id(Θ)]t = t`                                            [§3.2 on `D₂`]
4. `id(Θ); σ = σ₀, t/X = σ`                                  [(1), (2), (3)]

### Cor 4.5 (associativity)

`(σ₁; σ₂); σ₃ = σ₁; (σ₂; σ₃)`.

**Induction metric:** structure of `σ₃`.

**Case `σ₃ = ·`:**
1. `(σ₁; σ₂); · = ·`                                         [defn of composition]
2. `σ₂; · = ·`                                               [defn of composition]
3. `σ₁; (σ₂; ·) = σ₁; · = ·`                                 [defn of composition, (2)]
4. `(σ₁; σ₂); · = σ₁; (σ₂; ·)`                               [(1), (3)]

**Case `σ₃ = σ₃', t/X`:**
1. `(σ₁; σ₂); (σ₃', t/X) = ((σ₁; σ₂); σ₃'), [σ₁; σ₂]t/X`     [defn of composition]
2. `σ₂; (σ₃', t/X) = (σ₂; σ₃'), [σ₂]t/X`                     [defn of composition]
3. `σ₁; ((σ₂; σ₃'), [σ₂]t/X) = (σ₁; (σ₂; σ₃')), [σ₁][σ₂]t/X` [defn of composition]
4. `(σ₁; σ₂); σ₃' = σ₁; (σ₂; σ₃')`                           [IH on `σ₃'`]
5. `[σ₁; σ₂]t = [σ₁]([σ₂]t)`                                 [§4.2]
6. `(σ₁; σ₂); (σ₃', t/X) = (σ₁; (σ₂; σ₃')), [σ₁][σ₂]t/X`     [(1), (4), (5)]
7. `σ₁; (σ₂; (σ₃', t/X)) = (σ₁; (σ₂; σ₃')), [σ₁][σ₂]t/X`     [(2), (3)]
8. `(σ₁; σ₂); σ₃ = σ₁; (σ₂; σ₃)`                             [(6), (7)]

---

## 5. Context intersection

**Convention.** The inductive rules for `Γ ⊆ Γ'` make `⊆` a *subsequence* relation, not a set-theoretic one — so `[a,b] ⊆ [b,a]` is not derivable. The intersection rules recurse on the first argument and emit elements in `Γ₁`'s order. For 5.3's second conjunct (`Γ₃ ⊆ Γ₂`) to hold, we assume all object contexts list their variables in a single fixed canonical order (e.g. by name) and contain no duplicates.

### Aux 5.0 (freshness)

If `x ∉ Γ₁` and `Γ₃ = Γ₁ ∩ Γ₂`, then `Γ₃ = Γ₁ ∩ (Γ₂, x)`.

**Induction metric:** height of `D : Γ₃ = Γ₁ ∩ Γ₂`.

**Case `D` ends in IntNil** (so `Γ₁ = ·`, `Γ₃ = ·`):
1. `· = · ∩ (Γ₂, x)`                                         [IntNil]

**Case `D` ends in IntKeep** (so `Γ₁ = Γ₁', y`, `Γ₃ = Γ₃', y`, from `D' : Γ₃' = Γ₁' ∩ Γ₂` and `y ∈ Γ₂`):
1. `x ≠ y` and `x ∉ Γ₁'`                                     [hyp `x ∉ Γ₁`]
2. `Γ₃' = Γ₁' ∩ (Γ₂, x)`                                     [IH on `D'` with (1)]
3. `y ∈ Γ₂`                                                  [premise of `D`]
4. `y ∈ Γ₂, x`                                               [InThere, (3)]
5. `Γ₃', y = (Γ₁', y) ∩ (Γ₂, x)`                             [IntKeep, (2), (4)]
6. `Γ₃ = Γ₁ ∩ (Γ₂, x)`                                       [(5), case shape]

**Case `D` ends in IntDrop** (so `Γ₁ = Γ₁', y`, from `D' : Γ₃ = Γ₁' ∩ Γ₂` and `y ∉ Γ₂`):
1. `x ≠ y` and `x ∉ Γ₁'`                                     [hyp `x ∉ Γ₁`]
2. `Γ₃ = Γ₁' ∩ (Γ₂, x)`                                      [IH on `D'` with (1)]
3. `y ∉ Γ₂`                                                  [premise of `D`]
4. `y ∉ Γ₂, x`                                               [(3) and `x ≠ y`]
5. `Γ₃ = (Γ₁', y) ∩ (Γ₂, x)`                                 [IntDrop, (2), (4)]
6. `Γ₃ = Γ₁ ∩ (Γ₂, x)`                                       [(5), case shape]

### Aux 5.0b (empty is minimum)

For any `Γ`: `· ⊆ Γ`.

**Induction metric:** structure of `Γ`.

**Case `Γ = ·`:**
1. `· ⊆ ·`                                                   [WkNil]

**Case `Γ = Γ₀, a`:**
1. `· ⊆ Γ₀`                                                  [IH on `Γ₀`]
2. `· ⊆ Γ₀, a`                                               [WkSkip, (1)]

### 5.1 `Γ = Γ ∩ Γ`

**Induction metric:** structure of `Γ`.

**Case `Γ = ·`:**
1. `· = · ∩ ·`                                               [IntNil]

**Case `Γ = Γ₀, x`** (with `x ∉ Γ₀` by name uniqueness):
1. `Γ₀ = Γ₀ ∩ Γ₀`                                            [IH on `Γ₀`]
2. `x ∉ Γ₀`                                                  [name uniqueness]
3. `Γ₀ = Γ₀ ∩ (Γ₀, x)`                                       [Aux 5.0 on (1), (2)]
4. `x ∈ Γ₀, x`                                               [InHere]
5. `Γ₀, x = (Γ₀, x) ∩ (Γ₀, x)`                               [IntKeep, (3), (4)]

### 5.3 If `Γ₃ = Γ₁ ∩ Γ₂` then `Γ₃ ⊆ Γ₁` and `Γ₃ ⊆ Γ₂`

(Proved before 5.2 because 5.2 uses it.)

**Induction metric:** height of `D : Γ₃ = Γ₁ ∩ Γ₂`. We prove the conjunction together.

**Case `D` ends in IntNil** (so `Γ₁ = ·`, `Γ₃ = ·`):
1. `· ⊆ ·`                                                   [§1.1]
2. `· ⊆ Γ₂`                                                  [Aux 5.0b]
3. `Γ₃ ⊆ Γ₁` and `Γ₃ ⊆ Γ₂`                                   [(1), (2)]

**Case `D` ends in IntKeep** (so `Γ₃ = Γ₃', x`, `Γ₁ = Γ₁', x`, from `D' : Γ₃' = Γ₁' ∩ Γ₂` and `x ∈ Γ₂`):
1. `Γ₃' ⊆ Γ₁'`                                               [IH on `D'`, first conjunct]
2. `Γ₃' ⊆ Γ₂`                                                [IH on `D'`, second conjunct]
3. `Γ₃', x ⊆ Γ₁', x`                                         [WkCons, (1)]
4. `x ∈ Γ₂`                                                  [premise of `D`]
5. `Γ₃', x ⊆ Γ₂`                                             [Aux 5.3a on (2), (4) — see below]
6. `Γ₃ ⊆ Γ₁` and `Γ₃ ⊆ Γ₂`                                   [(3), (5)]

**Case `D` ends in IntDrop** (so `Γ₁ = Γ₁', x`, from `D' : Γ₃ = Γ₁' ∩ Γ₂` and `x ∉ Γ₂`):
1. `Γ₃ ⊆ Γ₁'`                                                [IH on `D'`, first conjunct]
2. `Γ₃ ⊆ Γ₂`                                                 [IH on `D'`, second conjunct]
3. `Γ₃ ⊆ Γ₁', x`                                             [WkSkip, (1)]
4. `Γ₃ ⊆ Γ₁` and `Γ₃ ⊆ Γ₂`                                   [(2), (3)]

### Aux 5.3a (right extension)

Under the canonical-order convention: if `Γ ⊆ Γ'`, `x ∈ Γ'`, and every element of `Γ` precedes `x` in `Γ'`'s order, then `Γ, x ⊆ Γ'`.

  *Setup.* Decompose `Γ' = Γ'_a, x, Γ'_b` where every element of `Γ` lies in `Γ'_a`.

  1. `Γ ⊆ Γ'_a`                                              [from setup, structural inversion on `Γ ⊆ Γ'`]
  2. `Γ, x ⊆ Γ'_a, x`                                        [WkCons, (1)]
  3. For each `b ∈ Γ'_b`, repeatedly apply WkSkip to (2):
     `Γ, x ⊆ Γ'_a, x, Γ'_b = Γ'`                             [iterated WkSkip from (2)]

  In the IntKeep case of 5.3 above, the setup holds because (canonical order) every element of `Γ₃' ⊆ Γ₁'` precedes the tail `x` of `Γ₁ = Γ₁', x`, and `x ∈ Γ₂` after all elements of `Γ₃'` in `Γ₂`'s canonical order.

### 5.4 If `Γ₃ = Γ₁ ∩ Γ₂`, `Γ₄ ⊆ Γ₁`, `Γ₄ ⊆ Γ₂`, then `Γ₄ ⊆ Γ₃`

**Induction metric:** height of `D : Γ₃ = Γ₁ ∩ Γ₂`. Universally quantified over `Γ₄` and the two inclusion derivations.

**Case `D` ends in IntNil** (so `Γ₁ = ·`, `Γ₃ = ·`):
1. `Γ₄ ⊆ ·`                                                  [hyp]
2. The only rule concluding `_ ⊆ ·` is WkNil, so `Γ₄ = ·`     [inversion on (1)]
3. `· ⊆ ·`                                                   [WkNil]
4. `Γ₄ ⊆ Γ₃`                                                 [(2), (3)]

**Case `D` ends in IntKeep** (so `Γ₁ = Γ₁', x`, `Γ₃ = Γ₃', x`, from `D' : Γ₃' = Γ₁' ∩ Γ₂` and `x ∈ Γ₂`).

  Case-split on the last rule of `E : Γ₄ ⊆ Γ₁', x`:

  **Sub-case `E` ends in WkCons** (so `Γ₄ = Γ₄₀, x`, from `E' : Γ₄₀ ⊆ Γ₁'`):
  1. `Γ₄ = Γ₄₀, x ⊆ Γ₂`                                      [hyp]
  2. `Γ₄₀ ⊆ Γ₄₀, x`                                          [WkSkip, §1.1]
  3. `Γ₄₀ ⊆ Γ₂`                                              [§1.2 on (2), (1)]
  4. `Γ₄₀ ⊆ Γ₃'`                                             [IH on `D'` with `E'`, (3)]
  5. `Γ₄₀, x ⊆ Γ₃', x`                                       [WkCons, (4)]
  6. `Γ₄ ⊆ Γ₃`                                               [(5), case shape]

  **Sub-case `E` ends in WkSkip** (from `E' : Γ₄ ⊆ Γ₁'`):
  1. `Γ₄ ⊆ Γ₂`                                               [hyp]
  2. `Γ₄ ⊆ Γ₃'`                                              [IH on `D'` with `E'`, (1)]
  3. `Γ₄ ⊆ Γ₃', x`                                           [WkSkip, (2)]
  4. `Γ₄ ⊆ Γ₃`                                               [(3), case shape]

**Case `D` ends in IntDrop** (so `Γ₁ = Γ₁', x`, from `D' : Γ₃ = Γ₁' ∩ Γ₂` and `x ∉ Γ₂`).

  Case-split on the last rule of `E : Γ₄ ⊆ Γ₁', x`:

  **Sub-case `E` ends in WkCons** (so `Γ₄ = Γ₄₀, x`):
  1. `Γ₄ = Γ₄₀, x`                                           [case shape]
  2. `x ∈ Γ₄`                                                [InHere, (1)]
  3. `Γ₄ ⊆ Γ₂`                                               [hyp]
  4. `x ∈ Γ₂`                                                [§1.4 on (3), (2)]
  5. `x ∉ Γ₂`                                                [premise of `D`]
  6. Contradiction; sub-case impossible.                      [(4), (5)]

  **Sub-case `E` ends in WkSkip** (from `E' : Γ₄ ⊆ Γ₁'`):
  1. `Γ₄ ⊆ Γ₂`                                               [hyp]
  2. `Γ₄ ⊆ Γ₃`                                               [IH on `D'` with `E'`, (1)]

### 5.2 If `Γ = Γ₁ ∩ Γ₂` then `Γ = Γ₂ ∩ Γ₁`

**Setup.** The intersection algorithm is a function of its arguments (rule-by-rule case analysis shows the three rules are mutually exclusive on the first argument's shape and on `x ∈ Γ₂` vs `x ∉ Γ₂`). Let `Γ' = Γ₂ ∩ Γ₁` be the (unique) result of running it on the swapped arguments.

1. `Γ ⊆ Γ₁`                                                  [§5.3 on `Γ = Γ₁ ∩ Γ₂`, first conjunct]
2. `Γ ⊆ Γ₂`                                                  [§5.3 on `Γ = Γ₁ ∩ Γ₂`, second conjunct]
3. `Γ ⊆ Γ'`                                                  [§5.4 on `Γ' = Γ₂ ∩ Γ₁`, (2), (1)]
4. `Γ' ⊆ Γ₂`                                                 [§5.3 on `Γ' = Γ₂ ∩ Γ₁`, first conjunct]
5. `Γ' ⊆ Γ₁`                                                 [§5.3 on `Γ' = Γ₂ ∩ Γ₁`, second conjunct]
6. `Γ' ⊆ Γ`                                                  [§5.4 on `Γ = Γ₁ ∩ Γ₂`, (5), (4)]
7. `Γ = Γ'`                                                  [§1.3 on (3), (6)]
8. `Γ = Γ₂ ∩ Γ₁`                                             [(7) and defn of `Γ'`]

---

## 6. Strengthening on intersected contexts (auxiliary for §7)

### Aux 6.0 (intersection membership)

If `a ∈ Γ₁`, `a ∈ Γ₂`, and `Γ₃ = Γ₁ ∩ Γ₂`, then `a ∈ Γ₃`.

**Induction metric:** height of `D : Γ₃ = Γ₁ ∩ Γ₂`.

**Case `D` ends in IntNil** (so `Γ₁ = ·`):
1. `a ∈ ·`                                                   [hyp `a ∈ Γ₁`]
2. No rule concludes `_ ∈ ·`; vacuous.                        [inversion on (1)]

**Case `D` ends in IntKeep** (so `Γ₁ = Γ₁', x`, `Γ₃ = Γ₃', x`, from `D' : Γ₃' = Γ₁' ∩ Γ₂` and `x ∈ Γ₂`).

  Case-split on `a ∈ Γ₁', x`:

  **Sub-case head** (`a = x`):
  1. `x ∈ Γ₃', x`                                            [InHere]
  2. `a ∈ Γ₃`                                                [(1), `a = x`]

  **Sub-case cons** (`a ∈ Γ₁'`):
  1. `a ∈ Γ₁'`                                               [case shape]
  2. `a ∈ Γ₂`                                                [hyp]
  3. `a ∈ Γ₃'`                                               [IH on `D'`, (1), (2)]
  4. `a ∈ Γ₃', x`                                            [InThere, (3)]
  5. `a ∈ Γ₃`                                                [(4), case shape]

**Case `D` ends in IntDrop** (so `Γ₁ = Γ₁', x`, from `D' : Γ₃ = Γ₁' ∩ Γ₂` and `x ∉ Γ₂`).

  Case-split on `a ∈ Γ₁', x`:

  **Sub-case head** (`a = x`):
  1. `a ∈ Γ₂`                                                [hyp]
  2. `x ∉ Γ₂`                                                [premise of `D`]
  3. Contradiction; sub-case impossible.                      [(1), (2), `a = x`]

  **Sub-case cons** (`a ∈ Γ₁'`):
  1. `a ∈ Γ₁'`                                               [case shape]
  2. `a ∈ Γ₂`                                                [hyp]
  3. `a ∈ Γ₃`                                                [IH on `D'`, (1), (2)]

### Aux 6.1 (strengthening on intersection)

If `Θ; Γ₁ ⊢ t`, `Θ; Γ₂ ⊢ t`, and `Γ₃ = Γ₁ ∩ Γ₂`, then `Θ; Γ₃ ⊢ t`.

**Induction metric:** structure of `t`. Universally quantified over `Γ₁, Γ₂, Γ₃` and the two typing derivations.

**Case `t = a`:**
1. `a ∈ Γ₁`                                                  [inversion on `Θ; Γ₁ ⊢ a` (WfVar)]
2. `a ∈ Γ₂`                                                  [inversion on `Θ; Γ₂ ⊢ a` (WfVar)]
3. `a ∈ Γ₃`                                                  [Aux 6.0 on (1), (2)]
4. `Θ; Γ₃ ⊢ a`                                               [WfVar, (3)]

**Case `t = c`:**
1. `Θ; Γ₃ ⊢ c`                                               [WfCon]

**Case `t = f(t₁, t₂)`:**
1. `Θ; Γ₁ ⊢ t₁` and `Θ; Γ₁ ⊢ t₂`                             [inversion on `Θ; Γ₁ ⊢ f(t₁,t₂)` (WfFun)]
2. `Θ; Γ₂ ⊢ t₁` and `Θ; Γ₂ ⊢ t₂`                             [inversion on `Θ; Γ₂ ⊢ f(t₁,t₂)` (WfFun)]
3. `Θ; Γ₃ ⊢ t₁`                                              [IH on `t₁` from (1), (2)]
4. `Θ; Γ₃ ⊢ t₂`                                              [IH on `t₂` from (1), (2)]
5. `Θ; Γ₃ ⊢ f(t₁, t₂)`                                       [WfFun, (3), (4)]

**Case `t = X`:**
1. `X:[Γ_X] ∈ Θ` and `Γ_X ⊆ Γ₁`                              [inversion on `Θ; Γ₁ ⊢ X` (WfMeta)]
2. `Γ_X ⊆ Γ₂`                                                [inversion on `Θ; Γ₂ ⊢ X` (WfMeta), with the same `Γ_X` by name uniqueness]
3. `Γ_X ⊆ Γ₃`                                                [§5.4 on `Γ₃ = Γ₁ ∩ Γ₂`, (1), (2)]
4. `Θ; Γ₃ ⊢ X`                                               [WfMeta, (1), (3)]

---

## 7. Unification

**Theorem.** If `Θ; Γ ⊢ t1`, `Θ; Γ ⊢ t2`, and `Θ; Γ ⊢ t1 = t2 ↝ σ : Θ'`, then
- (A) `Θ' ⊢ σ : Θ`,
- (B) `[σ]t1 = [σ]t2`,
- (C) for every `Θ'' ⊢ τ : Θ` with `[τ]t1 = [τ]t2`, there exists `τ''` with `Θ'' ⊢ τ'' : Θ'` and `τ = τ''; σ`.

**Induction metric.** Height of `D : Θ; Γ ⊢ t1 = t2 ↝ σ : Θ'`. The three conclusions are proved by simultaneous induction. In clause (C), `Θ''` and `τ` are universally quantified.

### Case `D` ends in UnVar (`a = a`, `σ = id(Θ)`, `Θ' = Θ`)

**(A) Well-typedness.**
1. `Θ ⊢ id(Θ) : Θ`                                           [§3.1]

**(B) Unifies.**
1. `[id(Θ)]a = a`                                            [substitution-on-`a`]
2. `[id(Θ)]a = [id(Θ)]a`                                     [(1)]

**(C) MGU.** Given `Θ'' ⊢ τ : Θ` with `[τ]a = [τ]a`:
1. Take `τ'' := τ`                                           [choice]
2. `Θ'' ⊢ τ'' : Θ = Θ'`                                      [(1) and hyp]
3. `τ; id(Θ) = τ`                                            [Cor 4.3 on hyp]
4. `τ = τ''; σ`                                              [(1), (3)]

### Case `D` ends in UnCon (`c = c`, `σ = id(Θ)`, `Θ' = Θ`)

Identical to UnVar, replacing `[id(Θ)]a = a` with `[id(Θ)]c = c`.

### Case `D` ends in UnFun

Premises `D₁ : Θ; Γ ⊢ t1 = t1' ↝ σ_a : Θ_mid` and `D₂ : Θ_mid; Γ ⊢ [σ_a]t2 = [σ_a]t2' ↝ σ_b : Θ'`. Output: `σ = σ_b; σ_a`. (Renamed: `σ` ↦ `σ_a`, `σ'` ↦ `σ_b`, intermediate context ↦ `Θ_mid`.)

  *Setup (from hyp):* by inversion on `Θ; Γ ⊢ f(t1,t2)` (WfFun): `Θ; Γ ⊢ t1` and `Θ; Γ ⊢ t2`. Similarly `Θ; Γ ⊢ t1'` and `Θ; Γ ⊢ t2'`.

**(A) Well-typedness.**
1. `Θ_mid ⊢ σ_a : Θ`                                         [IH(A) on `D₁` with `Θ; Γ ⊢ t1`, `Θ; Γ ⊢ t1'`]
2. `Θ_mid; Γ ⊢ [σ_a]t2`                                      [§2.2 on (1), `Θ; Γ ⊢ t2`]
3. `Θ_mid; Γ ⊢ [σ_a]t2'`                                     [§2.2 on (1), `Θ; Γ ⊢ t2'`]
4. `Θ' ⊢ σ_b : Θ_mid`                                        [IH(A) on `D₂` with (2), (3)]
5. `Θ' ⊢ σ_b; σ_a : Θ`                                       [§4.1 on (4), (1)]

**(B) Unifies.**
1. `[σ_a]t1 = [σ_a]t1'`                                      [IH(B) on `D₁`]
2. `[σ_b]([σ_a]t1) = [σ_b]([σ_a]t1')`                        [apply `[σ_b]` to (1)]
3. `[σ_b; σ_a]t1 = [σ_b; σ_a]t1'`                            [§4.2 on (2), both sides]
4. `[σ_b]([σ_a]t2) = [σ_b]([σ_a]t2')`                        [IH(B) on `D₂`]
5. `[σ_b; σ_a]t2 = [σ_b; σ_a]t2'`                            [§4.2 on (4), both sides]
6. `[σ_b; σ_a]f(t1,t2) = f([σ_b; σ_a]t1, [σ_b; σ_a]t2)`      [substitution-on-`f`]
7. `[σ_b; σ_a]f(t1',t2') = f([σ_b; σ_a]t1', [σ_b; σ_a]t2')`  [substitution-on-`f`]
8. `[σ_b; σ_a]f(t1,t2) = [σ_b; σ_a]f(t1',t2')`               [(3), (5), (6), (7)]

**(C) MGU.** Given `Θ'' ⊢ τ : Θ` with `[τ]f(t1,t2) = [τ]f(t1',t2')`:
1. `f([τ]t1, [τ]t2) = f([τ]t1', [τ]t2')`                     [substitution-on-`f`, twice]
2. `[τ]t1 = [τ]t1'`                                          [inversion on (1), f injective]
3. `[τ]t2 = [τ]t2'`                                          [inversion on (1), f injective]
4. Exists `τ_a` with `Θ'' ⊢ τ_a : Θ_mid` and `τ = τ_a; σ_a`  [IH(C) on `D₁` with hyp, (2)]
5. `[τ_a]([σ_a]t2) = [τ_a; σ_a]t2 = [τ]t2`                   [§4.2 and (4)]
6. `[τ_a]([σ_a]t2') = [τ_a; σ_a]t2' = [τ]t2'`                [§4.2 and (4)]
7. `[τ_a]([σ_a]t2) = [τ_a]([σ_a]t2')`                        [(3), (5), (6)]
8. Exists `τ_b` with `Θ'' ⊢ τ_b : Θ'` and `τ_a = τ_b; σ_b`   [IH(C) on `D₂` with (4), (7)]
9. `τ = (τ_b; σ_b); σ_a`                                     [(4), (8)]
10. `τ = τ_b; (σ_b; σ_a)`                                    [Cor 4.5 on (9)]
11. Take `τ'' := τ_b`; then `Θ'' ⊢ τ'' : Θ'` and `τ = τ''; σ`  [(8), (10)]

### Case `D` ends in UnMetaSame (`X = X`, `σ = id(Θ)`, `Θ' = Θ`)

**(A)** As in UnVar (line 1: `Θ ⊢ id(Θ) : Θ` by §3.1).

**(B)** `[id(Θ)]X = [id(Θ)]X` trivially.

**(C)** As in UnVar: take `τ'' := τ`, use Cor 4.3.

### Case `D` ends in UnMetaMeta (`X = Y`, `X ≠ Y`)

Premises: `Θ = Θ_rem, X:[Γ_X], Y:[Γ_Y]`; `X ≠ Y`; `Γ_Z = Γ_X ∩ Γ_Y`; `Z ∉ Θ_rem`. Output: `σ = id(Θ_rem), Z/X, Z/Y`, `Θ' = Θ_rem, Z:[Γ_Z]`. (Renamed: `Γ₁` ↦ `Γ_X`, `Γ₂` ↦ `Γ_Y`, `Γ₃` ↦ `Γ_Z`.)

**(A) Well-typedness.**
1. `Θ_rem ⊢ id(Θ_rem) : Θ_rem`                               [§3.1]
2. `(Θ_rem, Z:[Γ_Z]) ⊢ id(Θ_rem) : Θ_rem`                    [Aux 3.0b on (1), `Z ∉ Θ_rem`]
3. `Γ_Z ⊆ Γ_X`                                               [§5.3 on `Γ_Z = Γ_X ∩ Γ_Y`, first conjunct]
4. `Z:[Γ_Z] ∈ Θ_rem, Z:[Γ_Z]`                                [InHere]
5. `(Θ_rem, Z:[Γ_Z]); Γ_X ⊢ Z`                               [WfMeta, (4), (3)]
6. `(Θ_rem, Z:[Γ_Z]) ⊢ (id(Θ_rem), Z/X) : (Θ_rem, X:[Γ_X])`  [SubCons, (2), (5)]
7. `Γ_Z ⊆ Γ_Y`                                               [§5.3 on `Γ_Z = Γ_X ∩ Γ_Y`, second conjunct]
8. `(Θ_rem, Z:[Γ_Z]); Γ_Y ⊢ Z`                               [WfMeta, (4), (7)]
9. `(Θ_rem, Z:[Γ_Z]) ⊢ σ : (Θ_rem, X:[Γ_X], Y:[Γ_Y]) = Θ`    [SubCons, (6), (8)]

**(B) Unifies.**
1. `[σ]X = σ(X) = Z`                                         [substitution-on-`X`, lookup]
2. `[σ]Y = σ(Y) = Z`                                         [substitution-on-`X`, lookup]
3. `[σ]X = [σ]Y`                                             [(1), (2)]

**(C) MGU.** Given `Θ'' ⊢ τ : Θ` with `[τ]X = [τ]Y`. Let `u := τ(X)` and `u' := τ(Y)`.
1. `[τ]X = τ(X) = u`                                         [substitution-on-`X`, lookup]
2. `[τ]Y = τ(Y) = u'`                                        [substitution-on-`X`, lookup]
3. `u = u'`                                                  [(1), (2), hyp]
4. `X:[Γ_X] ∈ Θ`                                             [case shape]
5. `Y:[Γ_Y] ∈ Θ`                                             [case shape]
6. `Θ''; Γ_X ⊢ u`                                            [§2.1 on hyp `τ`, (4)]
7. `Θ''; Γ_Y ⊢ u'`                                           [§2.1 on hyp `τ`, (5)]
8. `Θ''; Γ_Y ⊢ u`                                            [(3), (7)]
9. `Θ''; Γ_Z ⊢ u`                                            [Aux 6.1 on (6), (8), `Γ_Z = Γ_X ∩ Γ_Y`]
10. Define `τ''` on domain `Θ_rem, Z:[Γ_Z]` by:
    - `τ''(W) := τ(W)` for `W ∈ Θ_rem`
    - `τ''(Z) := u`                                          [definition]
11. For each `W:[Γ_W] ∈ Θ_rem`, `Θ''; Γ_W ⊢ τ(W)`            [§2.1 on hyp `τ` and `W:[Γ_W] ∈ Θ`]
12. `Θ'' ⊢ (τ restricted to Θ_rem) : Θ_rem`                  [SubCons, iteratively, from (11)]
13. `Θ'' ⊢ τ'' : (Θ_rem, Z:[Γ_Z]) = Θ'`                      [SubCons on (12), (9)]
14. For `W ∈ Θ_rem`: `(τ''; σ)(W) = [τ''](σ(W)) = [τ'']W = τ''(W) = τ(W)`  [Aux 4.2a; `σ(W) = W` on Θ_rem; lookup]
15. `(τ''; σ)(X) = [τ''](σ(X)) = [τ'']Z = τ''(Z) = u = τ(X)` [Aux 4.2a, σ(X) = Z, (10), (1)]
16. `(τ''; σ)(Y) = [τ''](σ(Y)) = [τ'']Z = u = u' = τ(Y)`     [Aux 4.2a, σ(Y) = Z, (10), (3), (2)]
17. `τ''; σ = τ`                                             [(14), (15), (16) — agreement on all of `dom(σ) = Θ`]

### Case `D` ends in UnMetaTm (`X = t`, `t` not a metavariable)

Premises: `Θ = Θ_rem, X:[Γ_X]`; `Γ_X ⊆ Γ`; `Θ_rem; Γ_X ⊢ t`. Output: `σ = id(Θ_rem), t/X`, `Θ' = Θ_rem`.

**(A) Well-typedness.**
1. `Θ_rem ⊢ id(Θ_rem) : Θ_rem`                               [§3.1]
2. `Θ_rem; Γ_X ⊢ t`                                          [premise of `D`]
3. `Θ_rem ⊢ (id(Θ_rem), t/X) : (Θ_rem, X:[Γ_X]) = Θ`         [SubCons, (1), (2)]

**(B) Unifies.**
1. `[σ]X = σ(X) = t`                                         [substitution-on-`X`, lookup]
2. `[σ]t = t`  (sub-derivation below)                        [—]

  *Sub-derivation for `[σ]t = t`* — note all metavariables of `t` lie in `Θ_rem` (from `Θ_rem; Γ_X ⊢ t`), and on `Θ_rem` we have `σ(W) = W` (lookup through the `id(Θ_rem)` prefix). Run §3.2's argument on `Θ_rem; Γ_X ⊢ t` with `[σ]` in place of `[id(Θ_rem)]`:
  - the WfVar, WfCon, WfFun cases are identical to §3.2;
  - the WfMeta case uses `σ(W) = id(Θ_rem)(W) = W` by lookup through `t/X` (since `W ≠ X`) and Aux 3.2a.

3. `[σ]X = [σ]t`                                             [(1), (2)]

**(C) MGU.** Given `Θ'' ⊢ τ : Θ` with `[τ]X = [τ]t`. Let `u := τ(X)`.
1. `[τ]X = u`                                                [substitution-on-`X`, lookup]
2. `u = [τ]t`                                                [(1) and hyp]
3. Define `τ''` on domain `Θ_rem` by `τ''(W) := τ(W)`        [definition]
4. For each `W:[Γ_W] ∈ Θ_rem`, `Θ''; Γ_W ⊢ τ''(W) = τ(W)`    [§2.1 on `τ`, `W:[Γ_W] ∈ Θ`]
5. `Θ'' ⊢ τ'' : Θ_rem = Θ'`                                  [SubCons iteratively, from (4)]
6. `[τ]t = [τ'']t`                                           [t's metavariables in Θ_rem; τ, τ'' agree there]
7. For `W ∈ Θ_rem`: `(τ''; σ)(W) = [τ'']W = τ''(W) = τ(W)`   [Aux 4.2a; `σ(W) = W`]
8. `(τ''; σ)(X) = [τ''](σ(X)) = [τ''](t) = [τ]t = u = τ(X)`  [Aux 4.2a, σ(X) = t, (6), (2), (1)]
9. `τ''; σ = τ`                                              [(7), (8)]

### Case `D` ends in UnTmMeta (`t = X`, `t` not a metavariable)

Symmetric to UnMetaTm. Same `σ = id(Θ_rem), t/X`, `Θ' = Θ_rem`.

**(A) Well-typedness.** Identical to UnMetaTm.

**(B) Unifies.**
1. `[σ]t = t`                                                [as in UnMetaTm (B)]
2. `[σ]X = t`                                                [as in UnMetaTm (B)]
3. `[σ]t = [σ]X`                                             [(1), (2)]

**(C) MGU.** Given `Θ'' ⊢ τ : Θ` with `[τ]t = [τ]X`. Same `u := τ(X)`, same `τ''`. The chain (1)–(9) of UnMetaTm (C) carries over verbatim with `[τ]X = [τ]t` rewritten as `[τ]t = [τ]X`. ∎
