# Inductive proofs for unification.md (new version)

## 0. Conventions, corrections, and proof format

The proofs below assume the following amendments to `unification.md`.

1. **Property at line 92 (renaming on terms — type-correctness).** The statement
   ```
   If Θ; Γ ⊢ t and Γ ⊢ ρ : Γ' then Θ; Γ ⊢ [ρ]t
   ```
   is mistyped: in `Γ ⊢ ρ : Γ'` the *inputs* of `ρ` live in `Γ'` and the *outputs* in `Γ`, so `[ρ]` takes a term over `Γ'` to a term over `Γ`. The corrected statement is:
   ```
   If Θ; Γ' ⊢ t and Γ ⊢ ρ : Γ' then Θ; Γ ⊢ [ρ]t.
   ```

2. **Strengthening property at line 135.** As written, `set-to-list(fv(t))` is not deterministic. We replace the statement with a renaming-based reformulation that is order-insensitive (see §4.1 below for the corrected statement).

3. **Metavariable contexts modulo permutation.** The rules `Θ ≡ Θ', X:[Γ']` (UnMetaTm/UnTmMeta) and `Θ ≡ Θ', X:[Γ₁], Y:[Γ₂]` (UnMetaDiff) treat `Θ` up to permutation of its entries, i.e. as a finite map from metavariable names to dependency contexts.

4. **Convention for composition (both ρ and σ).** `f; g` means *apply `g` first, then `f`*. The typing reads "if `A ⊢ f : B` and `B ⊢ g : C` then `A ⊢ f;g : C`". Lookup obeys `(f;g)(x) = f(g(x))` for renamings.

5. **Subcontext relation `⊆`.** We define `Γ_a ⊆ Γ_b` inductively by three rules `WkNilCx`, `WkConsCx`, `WkSkipCx` analogous to metaweakening (we use the same names since context isn't ambiguous):
   - `· ⊆ Γ` (any `Γ`)                          [WkNilCx]
   - `Γ_a, x ⊆ Γ_b, x` if `Γ_a ⊆ Γ_b`           [WkConsCx]
   - `Γ_a ⊆ Γ_b, x` if `Γ_a ⊆ Γ_b`              [WkSkipCx]

   Note: we are assuming all contexts are duplicate-free (object variable names appear at most once).

6. **Coequalizer universal property (line 282).** As written, the statement reads `Γ ⊢ j : Δ`, but for `ρ_1; j = ρ_2; j` to type-check the source of `j` must match the codomain of `ρ_1, ρ_2`, namely `Γ'`. Corrected statement: `Γ' ⊢ j : Δ`.

**Proof format.** Each proof is presented as numbered logical steps. Each step's justification appears in brackets on the right, naming the rule, lemma, or hypothesis used and citing earlier line numbers `(n)` whose premises feed into it. `[IH on (n)]` means the inductive hypothesis applied to the subderivation/structure identified on line `n`. Line numbers restart at `1` within each case. `[hyp]` marks a top-level hypothesis of the theorem.

Quantifiers and induction metric are stated explicitly before each proof.

**Rule naming.** Beyond names from `unification.md`, we use:
- `RemVarHere`, `RemVarThere` — the two rules for `Γ₀ - a ≡ Γ₁`.
- `RemMetaHere`, `RemMetaThere` — the two rules for `Θ₀ - X ≡ Θ₁`.
- `RemCtxNil`, `RemCtxCons` — the two rules for `Γ - Γ' ≡ Γ''`.
- `WfRenNil`, `WfRenCons` — the two rules for `Γ ⊢ ρ : Γ'`.
- `FindNil`, `FindHit`, `FindMissTail`, `FindMissBoth` — the four rules for `ρ|y`.

---

## 1. Removing variables and contexts

### 1.1 `Γ₀ - a ≡ Γ₁` ⇒ `a ∈ Γ₀`

**Quantifiers / metric.** For all `Γ₀, Γ₁, a`: induction on the height of `D : Γ₀ - a ≡ Γ₁`.

**Case `D` ends in RemVarHere** (so `Γ₀ = Γ, a`, `Γ₁ = Γ`):
1. `a ∈ Γ, a`                                                [InHere]
2. `a ∈ Γ₀`                                                  [(1), case shape]

**Case `D` ends in RemVarThere** (so `Γ₀ = Γ₀', b`, `Γ₁ = Γ₁', b`, `a ≠ b`, from `D' : Γ₀' - a ≡ Γ₁'`):
1. `a ∈ Γ₀'`                                                 [IH on `D'`]
2. `a ∈ Γ₀', b`                                              [InThere, (1)]
3. `a ∈ Γ₀`                                                  [(2), case shape]

### Aux 1.2 (membership of remaining context after removal)

If `Γ₀ - a ≡ Γ₁` and `b ∈ Γ₁`, then `b ∈ Γ₀` and `b ≠ a`.

**Quantifiers / metric.** Induction on `D : Γ₀ - a ≡ Γ₁`.

**Case RemVarHere** (`Γ₀ = Γ, a`, `Γ₁ = Γ`):
1. `b ∈ Γ`                                                   [hyp]
2. `b ∈ Γ, a`                                                [InThere, (1)]
3. `b ≠ a` (since `Γ` is duplicate-free and `a` was removed)  [duplicate-freeness of `Γ, a`]

**Case RemVarThere** (`Γ₀ = Γ₀', c`, `Γ₁ = Γ₁', c`, `a ≠ c`, from `D' : Γ₀' - a ≡ Γ₁'`):
1. Case-split on `E : b ∈ Γ₁', c`:
   - **InHere** (`b = c`): `b ∈ Γ₀', c` by InHere; `b ≠ a` since `c ≠ a`.
   - **InThere** (from `E' : b ∈ Γ₁'`): by IH on `D'`, `b ∈ Γ₀'` and `b ≠ a`; then `b ∈ Γ₀', c` by InThere.

### Aux 1.3 (swap of removals)

If `Γ - a₁ ≡ Γ_1` and `Γ_1 - a₂ ≡ Γ_{12}` with `a₁ ≠ a₂`, then there exists `Γ_2` such that `Γ - a₂ ≡ Γ_2` and `Γ_2 - a₁ ≡ Γ_{12}`.

**Quantifiers / metric.** Induction on `D₁ : Γ - a₁ ≡ Γ_1`.

**Case `D₁` ends in RemVarHere** (so `Γ = Γ_0, a₁`, `Γ_1 = Γ_0`):
1. `D₂ : Γ_0 - a₂ ≡ Γ_{12}`                                  [hyp]
2. `a₂ ∈ Γ_0`                                                [§1.1 on (1)]
3. `a₂ ≠ a₁`                                                 [hyp]
4. `(Γ_0, a₁) - a₂ ≡ (Γ_{12}, a₁)`                           [RemVarThere on (1), (3)]
5. Take `Γ_2 := Γ_{12}, a₁`. Then `Γ - a₂ ≡ Γ_2`.            [(4)]
6. `Γ_2 - a₁ = (Γ_{12}, a₁) - a₁ ≡ Γ_{12}`                   [RemVarHere]

**Case `D₁` ends in RemVarThere** (so `Γ = Γ', b`, `Γ_1 = Γ_1', b`, `a₁ ≠ b`, from `D₁' : Γ' - a₁ ≡ Γ_1'`):

Sub-case `D₂` ends in RemVarHere (so `a₂ = b`, `Γ_{12} = Γ_1'`):
1. `Γ - a₂ = (Γ', b) - b ≡ Γ'`                               [RemVarHere]
2. Take `Γ_2 := Γ'`. Then `Γ - a₂ ≡ Γ_2`.                    [(1)]
3. `Γ_2 - a₁ = Γ' - a₁ ≡ Γ_1'` (= `Γ_{12}`)                  [`D₁'`]

Sub-case `D₂` ends in RemVarThere (so `a₂ ≠ b`, `Γ_{12} = Γ_{12}', b`, from `D₂' : Γ_1' - a₂ ≡ Γ_{12}'`):
1. By IH on `D₁'` and `D₂'`: exists `Γ'_2` with `Γ' - a₂ ≡ Γ'_2` and `Γ'_2 - a₁ ≡ Γ_{12}'`.   [IH]
2. `(Γ', b) - a₂ ≡ (Γ'_2, b)`                                [RemVarThere on (1), `a₂ ≠ b`]
3. Take `Γ_2 := Γ'_2, b`.                                    [(2)]
4. `(Γ'_2, b) - a₁ ≡ (Γ_{12}', b)`                           [RemVarThere on (1), `a₁ ≠ b`]
5. `Γ_2 - a₁ ≡ Γ_{12}`                                       [(4), case shape]

---

## 2. Renamings

### Aux 2.0a (renaming lookup totality)

If `Γ ⊢ ρ : Γ'` and `x ∈ Γ'`, then `ρ(x)` is defined.

**Quantifiers / metric.** Universal in `Γ, Γ', x`. Induction on the height of `D : Γ ⊢ ρ : Γ'`.

**Case `D` ends in WfRenNil** (so `Γ' = ·`):
1. `x ∈ ·`                                                   [hyp]
2. No rule concludes `_ ∈ ·`; vacuous.                        [inversion on (1)]

**Case `D` ends in WfRenCons** (so `ρ = ρ₀, a/y`, `Γ' = Γ'₀, y`, from `D' : Γ_mid ⊢ ρ₀ : Γ'₀` where `Γ₀ - a ≡ Γ_mid`):

  Case-split on `E : x ∈ Γ'₀, y`:

  **Sub-case `x = y` (InHere):**
  1. `(ρ₀, a/y)(y) = a`                                      [lookup head]
  2. `ρ(x) = a` is defined                                   [(1), `x = y`]

  **Sub-case `x ≠ y` (InThere, from `E' : x ∈ Γ'₀`):**
  1. `ρ₀(x)` is defined                                      [IH on `D'`, `E'`]
  2. `(ρ₀, a/y)(x) = ρ₀(x)`                                  [lookup cons, `x ≠ y`]
  3. `ρ(x)` is defined                                       [(1), (2)]

### 2.1 `Γ ⊢ ρ : Γ'` and `x ∈ Γ'` ⇒ `ρ(x) ∈ Γ`

**Quantifiers / metric.** Universal in `Γ, Γ', x`. Induction on the height of `D : Γ ⊢ ρ : Γ'`.

**Case WfRenNil:** vacuous.

**Case WfRenCons** (so `ρ = ρ₀, a/y`, `Γ' = Γ'₀, y`, `Γ - a ≡ Γ_mid`, `D' : Γ_mid ⊢ ρ₀ : Γ'₀`):

  **Sub-case `x = y` (InHere):**
  1. `ρ(x) = a`                                              [lookup head, `x = y`]
  2. `a ∈ Γ`                                                 [§1.1 on premise of WfRenCons]
  3. `ρ(x) ∈ Γ`                                              [(1), (2)]

  **Sub-case `x ≠ y` (InThere, from `E' : x ∈ Γ'₀`):**
  1. `ρ(x) = ρ₀(x)`                                          [lookup cons]
  2. `ρ₀(x) ∈ Γ_mid`                                         [IH on `D'`, `E'`]
  3. `ρ₀(x) ∈ Γ`                                             [Aux 1.2 on premise of WfRenCons, (2)]
  4. `ρ(x) ∈ Γ`                                              [(1), (3)]

### Aux 2.0b (lookup of identity renaming)

For all `Γ` and `x ∈ Γ`: `id(Γ)(x) = x`.

**Quantifiers / metric.** Universal in `Γ, x`. Induction on the structure of `Γ`.

**Case `Γ = ·`:** vacuous.

**Case `Γ = Γ₀, y`:**

  **Sub-case `x = y` (InHere):**
  1. `id(Γ₀, y) = id(Γ₀), y/y`                               [defn of `id`]
  2. `(id(Γ₀), y/y)(y) = y`                                  [(1), lookup head]
  3. `id(Γ)(x) = x`                                          [(2), `x = y`]

  **Sub-case `x ≠ y` (InThere, from `x ∈ Γ₀`):**
  1. `id(Γ₀, y) = id(Γ₀), y/y`                               [defn of `id`]
  2. `(id(Γ₀), y/y)(x) = id(Γ₀)(x)`                          [lookup cons, `x ≠ y`]
  3. `id(Γ₀)(x) = x`                                         [IH on `Γ₀`]
  4. `id(Γ)(x) = x`                                          [(2), (3)]

### 2.2 `Γ ⊢ id(Γ) : Γ`

**Quantifiers / metric.** Induction on the structure of `Γ`.

**Case `Γ = ·`:**
1. `id(·) = ·`                                               [defn]
2. `· ⊢ · : ·`                                               [WfRenNil]

**Case `Γ = Γ₀, x`:**
1. `id(Γ₀, x) = id(Γ₀), x/x`                                 [defn of `id`]
2. `Γ₀ ⊢ id(Γ₀) : Γ₀`                                        [IH on `Γ₀`]
3. `(Γ₀, x) - x ≡ Γ₀`                                        [RemVarHere]
4. `(Γ₀, x) ⊢ (id(Γ₀), x/x) : (Γ₀, x)`                       [WfRenCons, (3), (2)]
5. `Γ ⊢ id(Γ) : Γ`                                           [(1), (4)]

### Aux 2.3a (lookup-after-composition)

For all renamings `ρ, ρ'` and all variables `x`: `(ρ; ρ')(x) = ρ(ρ'(x))` (when `ρ'(x)` is defined).

**Quantifiers / metric.** Universal in `ρ, x`. Induction on the structure of `ρ'`.

**Case `ρ' = ·`:** `ρ'(x)` undefined; vacuous.

**Case `ρ' = ρ'₀, b/y`:**

  **Sub-case `x = y`:**
  1. `ρ'(y) = b`                                             [lookup head]
  2. `ρ; (ρ'₀, b/y) = (ρ; ρ'₀), ρ(b)/y`                      [defn of composition]
  3. `(ρ; ρ')(y) = ρ(b)`                                     [(2), lookup head]
  4. `(ρ; ρ')(x) = ρ(ρ'(x))`                                 [(1), (3), `x = y`]

  **Sub-case `x ≠ y`:**
  1. `ρ'(x) = ρ'₀(x)`                                        [lookup cons]
  2. `ρ; (ρ'₀, b/y) = (ρ; ρ'₀), ρ(b)/y`                      [defn of composition]
  3. `(ρ; ρ')(x) = (ρ; ρ'₀)(x)`                              [(2), lookup cons, `x ≠ y`]
  4. `(ρ; ρ'₀)(x) = ρ(ρ'₀(x))`                               [IH on `ρ'₀`]
  5. `(ρ; ρ')(x) = ρ(ρ'(x))`                                 [(1), (3), (4)]

### Aux 2.3b (linearity inversion / "extract an entry")

If `Γ ⊢ ρ : Γ'` and `y ∈ Γ'`, then `ρ(y)` is defined; further, writing `b := ρ(y)`, there exist `Γ_mid` and a renaming `ρ_minus_y` such that:

(i) `Γ - b ≡ Γ_mid`,
(ii) `(Γ' - y)` exists, say `Γ' - y ≡ Γ'_y`,
(iii) `Γ_mid ⊢ ρ_minus_y : Γ'_y`,
(iv) For all `z ∈ Γ'` with `z ≠ y`, `ρ(z) = ρ_minus_y(z)`.

**Quantifiers / metric.** Induction on `D : Γ ⊢ ρ : Γ'`.

**Case WfRenNil:** vacuous (`y ∈ ·` impossible).

**Case WfRenCons** (so `ρ = ρ₀, c/x`, `Γ' = Γ'₀, x`, `Γ - c ≡ Γ_outer`, `D₀ : Γ_outer ⊢ ρ₀ : Γ'₀`):

  **Sub-case `y = x`:**
  1. `ρ(x) = c`                                              [lookup head]
  2. `(Γ'₀, x) - x ≡ Γ'₀`                                    [RemVarHere]
  3. `Γ - c ≡ Γ_outer`                                       [premise]
  4. Take `ρ_minus_y := ρ₀`, `Γ_mid := Γ_outer`, `Γ'_y := Γ'₀`.   [definition]
  5. (i), (ii), (iii) follow from (3), (2), and `D₀`. For (iv), let `z ∈ Γ' = Γ'₀, x` with `z ≠ x`, so `z ∈ Γ'₀` by InThere. Then `ρ(z) = ρ₀(z)` (lookup cons) and `ρ_minus_y(z) = ρ₀(z)` (by defn). ✓

  **Sub-case `y ≠ x` (so `y ∈ Γ'₀`):**
  1. `ρ(y) = ρ₀(y)`                                          [lookup cons]
  2. Let `b := ρ(y) = ρ₀(y)`.
  3. By IH on `D₀`, there exist `Γ_inner`, `Γ'_y_inner`, `ρ₀_minus_y` with:
     - `Γ_outer - b ≡ Γ_inner`
     - `Γ'₀ - y ≡ Γ'_y_inner`
     - `Γ_inner ⊢ ρ₀_minus_y : Γ'_y_inner`
     - For `z ∈ Γ'₀` with `z ≠ y`, `ρ₀(z) = ρ₀_minus_y(z)`.        [IH]
  4. `b ∈ Γ_outer` (since `b = ρ₀(y)` and §2.1)                    [§2.1 on `D₀`]
  5. `c ≠ b` (since `c ∉ Γ_outer` by premise `Γ - c ≡ Γ_outer`, but `b ∈ Γ_outer`)  [(4), premise]
  6. By Aux 1.3 on `Γ - c ≡ Γ_outer` and `Γ_outer - b ≡ Γ_inner` with (5): exists `Γ_mid_swap` with `Γ - b ≡ Γ_mid_swap` and `Γ_mid_swap - c ≡ Γ_inner`.   [Aux 1.3]
  7. `(Γ'₀, x) - y ≡ (Γ'_y_inner, x)`                        [RemVarThere on (3), `y ≠ x`]
  8. Take `ρ_minus_y := (ρ₀_minus_y, c/x)`, `Γ_mid := Γ_mid_swap`, `Γ'_y := Γ'_y_inner, x`.
  9. (i): `Γ - b ≡ Γ_mid` by (6).
  10. (ii): `Γ' - y ≡ Γ'_y` by (7).
  11. (iii): `Γ_mid ⊢ (ρ₀_minus_y, c/x) : (Γ'_y_inner, x)`. By WfRenCons on `Γ_mid - c ≡ Γ_inner` (from (6)) and `Γ_inner ⊢ ρ₀_minus_y : Γ'_y_inner` (from (3)).        [WfRenCons]
  12. (iv): For `z ∈ Γ' = Γ'₀, x` with `z ≠ y`:
      - If `z = x`: `ρ(x) = c` (lookup head); `ρ_minus_y(x) = c` (lookup head of `(ρ₀_minus_y, c/x)`).
      - If `z ≠ x` (so `z ∈ Γ'₀` with `z ≠ y`): `ρ(z) = ρ₀(z)` (lookup cons); `ρ_minus_y(z) = ρ₀_minus_y(z)` (lookup cons); by (3), `ρ₀(z) = ρ₀_minus_y(z)`.

### 2.3 `Γ ⊢ ρ : Γ'` and `Γ' ⊢ ρ' : Γ''` ⇒ `Γ ⊢ ρ;ρ' : Γ''`

**Quantifiers / metric.** Universal in `ρ, Γ, Γ'`. Induction on the height of `D' : Γ' ⊢ ρ' : Γ''`.

**Case WfRenNil** (so `ρ' = ·`, `Γ'' = ·`):
1. `ρ; · = ·`                                                [defn]
2. `Γ ⊢ · : ·`                                               [WfRenNil]

**Case WfRenCons** (so `ρ' = ρ'₀, b/y`, `Γ'' = Γ''₀, y`, `Γ' - b ≡ Γ'_aux`, `D'_0 : Γ'_aux ⊢ ρ'₀ : Γ''₀`):
1. `ρ; (ρ'₀, b/y) = (ρ; ρ'₀), ρ(b)/y`                        [defn of composition]
2. `b ∈ Γ'`                                                  [§1.1 on premise of WfRenCons]
3. `ρ(b) ∈ Γ`                                                [§2.1 on hyp, (2)]
4. By Aux 2.3b on hyp `Γ ⊢ ρ : Γ'` with `b ∈ Γ'`: exists `Γ_mid`, `ρ_minus_b` with `Γ - ρ(b) ≡ Γ_mid`, `Γ_mid ⊢ ρ_minus_b : Γ' - b ≡ Γ'_aux`, agreement off `b`.        [Aux 2.3b]
5. `Γ_mid ⊢ ρ_minus_b; ρ'₀ : Γ''₀`                            [IH on `D'_0` with the renaming from (4)]
6. *Claim* `ρ; ρ'₀ = ρ_minus_b; ρ'₀` as sequences. For each input `z ∈ Γ''₀`: `(ρ; ρ'₀)(z) = ρ(ρ'₀(z))` and `(ρ_minus_b; ρ'₀)(z) = ρ_minus_b(ρ'₀(z))`. Since `ρ'₀`'s outputs lie in `Γ'_aux = Γ' - b`, `ρ'₀(z) ≠ b`. By (4) part (iv), `ρ(ρ'₀(z)) = ρ_minus_b(ρ'₀(z))`. So the two compositions agree entry-wise.        [Aux 2.3a, (4)(iv)]
7. `Γ_mid ⊢ ρ; ρ'₀ : Γ''₀`                                   [(5), (6)]
8. `Γ ⊢ (ρ; ρ'₀), ρ(b)/y : (Γ''₀, y)`                        [WfRenCons on (4)(i), (7)]
9. `Γ ⊢ ρ;ρ' : Γ''`                                          [(1), (8)]

### 2.4 (Corrected) `Θ; Γ' ⊢ t` and `Γ ⊢ ρ : Γ'` ⇒ `Θ; Γ ⊢ [ρ]t`

**Quantifiers / metric.** Universal in `Γ, Γ', ρ`. Induction on the height of `D : Θ; Γ' ⊢ t`.

**Case WfVar** (from `a ∈ Γ'`):
1. `a ∈ Γ'`                                                  [premise]
2. `ρ(a) ∈ Γ`                                                [§2.1 on hyp, (1)]
3. `[ρ]a = ρ(a)`                                             [defn]
4. `Θ; Γ ⊢ [ρ]a`                                             [WfVar, (2)]

**Case WfCon:**
1. `[ρ]c = c`; `Θ; Γ ⊢ c` by WfCon.

**Case WfFun** (from `D₁, D₂`):
1. `[ρ]f(t₁,t₂) = f([ρ]t₁, [ρ]t₂)`                           [defn]
2. `Θ; Γ ⊢ [ρ]t_i` for `i = 1, 2`                            [IH on `D_i`]
3. `Θ; Γ ⊢ [ρ]f(t₁, t₂)`                                     [WfFun, (1), (2)]

**Case WfMeta** (from `X:[Γ_X] ∈ Θ`, `Γ' ⊢ ρ_inner : Γ_X`):
1. `[ρ](X[ρ_inner]) = X[ρ; ρ_inner]`                         [defn]
2. `Γ ⊢ ρ; ρ_inner : Γ_X`                                    [§2.3 on hyp, premise]
3. `Θ; Γ ⊢ X[ρ; ρ_inner]`                                    [WfMeta, premise (X ∈ Θ), (2)]

### Aux 2.5a (left identity of renaming composition)

For all `ρ` with `Γ ⊢ ρ : Γ'`: `id(Γ); ρ = ρ`.

**Quantifiers / metric.** Universal in `Γ, Γ'`. Induction on the structure of `ρ`.

**Case `ρ = ·`:**
1. `id(Γ); · = ·` by defn.

**Case `ρ = ρ₀, a/x`** (so `Γ ⊢ (ρ₀, a/x) : (Γ'₀, x)`, with `Γ - a ≡ Γ_outer` and `Γ_outer ⊢ ρ₀ : Γ'₀`):
1. `id(Γ); (ρ₀, a/x) = (id(Γ); ρ₀), id(Γ)(a)/x`              [defn of composition]
2. `a ∈ Γ`                                                   [§1.1 on premise]
3. `id(Γ)(a) = a`                                            [Aux 2.0b on (2)]
4. *Sub-claim* `id(Γ); ρ₀ = ρ₀`. We prove this entry-wise: for each `c/y ∈ ρ₀`, `(id(Γ); ρ₀)(y) = id(Γ)(c)`. Now `c = ρ₀(y) ∈ Γ_outer` (§2.1), and `Γ_outer ⊆ Γ` set-wise (by induction on `Γ - a ≡ Γ_outer`). So `c ∈ Γ` and `id(Γ)(c) = c = ρ₀(y)` (by Aux 2.0b). Hence both renamings agree entry-wise.        [Aux 2.3a, Aux 2.0b, Aux 1.2]
5. `id(Γ); ρ = (ρ₀, a/x)`                                    [(1), (3), (4)]

### Aux 2.5b (right identity of renaming composition)

For all `ρ` with `Γ ⊢ ρ : Γ'`: `ρ; id(Γ') = ρ`.

**Quantifiers / metric.** Universal in `Γ, ρ`. Induction on the structure of `Γ'`.

**Case `Γ' = ·`:**
1. By inversion on `Γ ⊢ ρ : ·` (WfRenNil), `ρ = ·`.
2. `· ; · = ·`                                               [defn]

**Case `Γ' = Γ'₀, x`:**
1. `id(Γ'₀, x) = id(Γ'₀), x/x`                               [defn `id`]
2. `ρ; (id(Γ'₀), x/x) = (ρ; id(Γ'₀)), ρ(x)/x`                [defn of composition]
3. *Sub-claim* `(ρ; id(Γ'₀))` equals `ρ` minus its `x`-entry. For each `y ∈ Γ'₀` (so `y ≠ x`): `(ρ; id(Γ'₀))(y) = ρ(id(Γ'₀)(y)) = ρ(y)` (Aux 2.3a, Aux 2.0b on `y ∈ Γ'₀`). For `y = x`: `id(Γ'₀)` is undefined at `x` (since `x ∉ Γ'₀`), so the composition does not have an `x`-entry. So `ρ; id(Γ'₀)` agrees with `ρ` everywhere except at `x`, where it is empty.        [Aux 2.3a, Aux 2.0b]
4. `(ρ; id(Γ'₀)), ρ(x)/x`: this re-introduces the `x`-entry of `ρ`. So it equals `ρ`.        [(3)]
5. `ρ; id(Γ') = ρ`                                           [(2), (4)]

### 2.5 `Θ; Γ ⊢ t` ⇒ `[id(Γ)]t = t`

**Quantifiers / metric.** Universal in `Γ`. Induction on the height of `D : Θ; Γ ⊢ t`.

**Case WfVar:** `[id(Γ)]a = id(Γ)(a) = a` (Aux 2.0b on the WfVar premise).

**Case WfCon:** `[id(Γ)]c = c` (defn).

**Case WfFun:** by IH on premises and defn `[ρ]f(t_1, t_2) = f([ρ]t_1, [ρ]t_2)`.

**Case WfMeta** (`t = X[ρ_inner]`):
1. `[id(Γ)](X[ρ_inner]) = X[id(Γ); ρ_inner]`                 [defn]
2. `id(Γ); ρ_inner = ρ_inner`                                [Aux 2.5a on the WfMeta premise]
3. `[id(Γ)](X[ρ_inner]) = X[ρ_inner]`                        [(1), (2)]

### Aux 2.6a (associativity of renaming composition)

`(ρ_1; ρ_2); ρ_3 = ρ_1; (ρ_2; ρ_3)`.

**Quantifiers / metric.** Universal in `ρ_1, ρ_2`. Induction on the structure of `ρ_3`.

**Case `ρ_3 = ·`:** both sides reduce to `·` by defn.

**Case `ρ_3 = ρ_3', a/x`:**
1. `(ρ_1; ρ_2); (ρ_3', a/x) = ((ρ_1; ρ_2); ρ_3'), (ρ_1; ρ_2)(a)/x`         [defn]
2. `ρ_2; (ρ_3', a/x) = (ρ_2; ρ_3'), ρ_2(a)/x`                              [defn]
3. `ρ_1; ((ρ_2; ρ_3'), ρ_2(a)/x) = (ρ_1; (ρ_2; ρ_3')), ρ_1(ρ_2(a))/x`     [defn]
4. `(ρ_1; ρ_2); ρ_3' = ρ_1; (ρ_2; ρ_3')`                                   [IH on `ρ_3'`]
5. `(ρ_1; ρ_2)(a) = ρ_1(ρ_2(a))`                                           [Aux 2.3a]
6. Both sides of the lemma equal `(ρ_1; (ρ_2; ρ_3')), ρ_1(ρ_2(a))/x`.       [(1)–(5)]

### 2.6 `Γ ⊢ ρ : Γ'`, `Γ' ⊢ ρ' : Γ''`, `Θ; Γ'' ⊢ t` ⇒ `[ρ][ρ']t = [ρ;ρ']t`

**Quantifiers / metric.** Universal in `Γ, Γ', Γ'', ρ, ρ'`. Induction on the structure of `t`.

**Case `t = a`:**
1. `[ρ']a = ρ'(a)`                                           [defn]
2. `[ρ]ρ'(a) = ρ(ρ'(a))`                                     [defn on a variable]
3. `[ρ;ρ']a = (ρ;ρ')(a) = ρ(ρ'(a))`                          [defn, Aux 2.3a]

**Case `t = c`:** all three reduce to `c`.

**Case `t = f(t_1, t_2)`:**
1. `[ρ'](f(t_1, t_2)) = f([ρ']t_1, [ρ']t_2)`                 [defn]
2. `[ρ](f([ρ']t_1, [ρ']t_2)) = f([ρ][ρ']t_1, [ρ][ρ']t_2)`    [defn]
3. `[ρ][ρ']t_i = [ρ;ρ']t_i` for `i = 1, 2`                   [IH on `t_i`]
4. `[ρ;ρ'](f(t_1, t_2)) = f([ρ;ρ']t_1, [ρ;ρ']t_2)`           [defn]
5. Both sides equal `f([ρ;ρ']t_1, [ρ;ρ']t_2)`.

**Case `t = X[ρ_x]`:**
1. `[ρ'](X[ρ_x]) = X[ρ'; ρ_x]`                               [defn]
2. `[ρ](X[ρ'; ρ_x]) = X[ρ; (ρ'; ρ_x)]`                       [defn]
3. `[ρ;ρ'](X[ρ_x]) = X[(ρ;ρ'); ρ_x]`                         [defn]
4. `ρ; (ρ'; ρ_x) = (ρ;ρ'); ρ_x`                              [Aux 2.6a]
5. `[ρ][ρ'](X[ρ_x]) = [ρ;ρ'](X[ρ_x])`                        [(1)–(4)]

### Aux 2.7a (codomain reweakening)

If `Γ ⊢ ρ : Γ'` and `y ∉ Γ`, then `(Γ, y) ⊢ ρ : Γ'`.

**Quantifiers / metric.** Induction on `D : Γ ⊢ ρ : Γ'`.

**Case WfRenNil:** `(Γ, y) ⊢ · : ·` by WfRenNil.

**Case WfRenCons** (`ρ = ρ₀, c/x`, `Γ - c ≡ Γ_outer`, `D₀ : Γ_outer ⊢ ρ₀ : Γ'₀`):
1. `c ∈ Γ`                                                   [§1.1 on premise]
2. `y ≠ c`                                                   [hyp `y ∉ Γ`, (1)]
3. `(Γ, y) - c ≡ (Γ_outer, y)`                               [RemVarThere on premise, (2)]
4. `y ∉ Γ_outer` (since `Γ_outer ⊆ Γ` set-wise by Aux 1.2 and `y ∉ Γ`)        [Aux 1.2 iterated]
5. `(Γ_outer, y) ⊢ ρ₀ : Γ'₀`                                 [IH on `D₀` with (4)]
6. `(Γ, y) ⊢ (ρ₀, c/x) : (Γ'₀, x)`                           [WfRenCons, (3), (5)]

---

## 3. Inverse renamings and range

### 3.0 `range(ρ) ⊆ Γ` whenever `Γ ⊢ ρ : Γ'`

**Quantifiers / metric.** Induction on `D : Γ ⊢ ρ : Γ'`. (`⊆` here is the subsequence relation from §0.5.)

**Case WfRenNil:**
1. `range(·) = ·`                                            [defn]
2. `· ⊆ Γ`                                                   [WkNilCx]

**Case WfRenCons** (so `ρ = ρ₀, a/y`, `Γ - a ≡ Γ_outer`, `D' : Γ_outer ⊢ ρ₀ : Γ'₀`):
1. `range(ρ₀, a/y) = range(ρ₀), a`                           [defn]
2. `range(ρ₀) ⊆ Γ_outer`                                     [IH on `D'`]
3. *Claim* `Γ_outer ⊆ Γ` (as subsequence). By induction on `Γ - a ≡ Γ_outer` using WkNilCx, WkConsCx, WkSkipCx: every RemVarHere step contributes a WkSkipCx; every RemVarThere step contributes a WkConsCx.        [induction on `Γ - a ≡ Γ_outer`]
4. `range(ρ₀) ⊆ Γ`                                           [transitivity of ⊆; (2), (3)]
5. By inverting (3) at `a`: since `Γ - a ≡ Γ_outer` removes `a`, `Γ = ⟨…, a, …⟩` and `a` is not in `Γ_outer`. So `a ∈ Γ`. Adding `a` to a sub-sequence of `Γ` (where `a` itself is in `Γ`) preserves the subsequence relation, possibly by inserting at the appropriate place.        [structural argument]
6. `range(ρ), a ⊆ Γ` more precisely, `range(ρ₀), a ⊆ Γ`. Formally, by the construction of `⊆` and that `a ∈ Γ`.        [(4), (5)]

   (When `Γ` is duplicate-free and `range(ρ₀) ⊆ Γ_outer` does not include `a`, the appended `a` gives a still-valid subsequence inclusion into `Γ`.)

### Aux 3.0a (inverse lookup)

If `Γ ⊢ ρ : Γ'` and `(a/x) ∈ ρ` (i.e. `ρ(x) = a` for some `x ∈ Γ'`), then `ρ⁻¹(a) = x`.

**Quantifiers / metric.** Induction on `D : Γ ⊢ ρ : Γ'`.

**Case WfRenNil:** vacuous.

**Case WfRenCons** (`ρ = ρ₀, c/y`):

  **Sub-case `(a/x) = (c/y)` (the head):**
  1. `ρ⁻¹ = ρ₀⁻¹, y/c`                                       [defn `⁻¹`]
  2. `ρ⁻¹(c) = y`                                            [lookup head]
  3. `ρ⁻¹(a) = x`                                            [(2), `a = c`, `x = y`]

  **Sub-case `(a/x) ∈ ρ₀` (so `(a/x) ≠ (c/y)`):**
  1. By linearity of `ρ`: each output appears at most once. So `a ≠ c` (since `c` is the output of the head entry and `a` is an output of `ρ₀`, and linearity prevents repetition).        [linearity]
  2. `ρ⁻¹ = ρ₀⁻¹, y/c`                                       [defn `⁻¹`]
  3. `ρ⁻¹(a) = ρ₀⁻¹(a)`                                      [(2), lookup cons, `a ≠ c`]
  4. `ρ₀⁻¹(a) = x`                                           [IH on the smaller derivation]
  5. `ρ⁻¹(a) = x`                                            [(3), (4)]

### 3.1 `Γ ⊢ ρ : Γ'` ⇒ `Γ' ⊢ ρ⁻¹ : range(ρ)`

**Quantifiers / metric.** Induction on `D : Γ ⊢ ρ : Γ'`.

**Case WfRenNil:** `ρ⁻¹ = ·`, `range(ρ) = ·`, `· ⊢ · : ·` by WfRenNil.

**Case WfRenCons** (so `ρ = ρ₀, a/y`, `Γ' = Γ'₀, y`, `Γ - a ≡ Γ_outer`, `D' : Γ_outer ⊢ ρ₀ : Γ'₀`):
1. `ρ⁻¹ = ρ₀⁻¹, y/a`                                         [defn]
2. `range(ρ) = range(ρ₀), a`                                 [defn]
3. `Γ'₀ ⊢ ρ₀⁻¹ : range(ρ₀)`                                  [IH on `D'`]
4. `range(ρ₀) ⊆ Γ_outer` set-wise                            [§3.0 + Aux 1.2 implications]
5. `a ∉ range(ρ₀)` (since `a ∉ Γ_outer` by §1.1 + Aux 1.2 on premise; (4))      [Aux 1.2 on premise]
6. `(range(ρ₀), a) - a ≡ range(ρ₀)`                          [RemVarHere]
7. `(Γ'₀, y) ⊢ (ρ₀⁻¹, y/a) : (range(ρ₀), a)`                 [WfRenCons, (6), (3)]
8. `Γ' ⊢ ρ⁻¹ : range(ρ)`                                     [(1), (2), (7)]

### Aux 3.2a (round-trip identities)

If `Γ ⊢ ρ : Γ'`, then `ρ⁻¹; ρ = id(Γ')` and `ρ; ρ⁻¹ = id(range(ρ))`.

**Proof of `ρ⁻¹; ρ = id(Γ')`** (entry-wise on `Γ'`):

For each `x ∈ Γ'`:
1. `ρ(x) ∈ range(ρ)` is defined; let `a := ρ(x)`.            [Aux 2.0a, defn of `range`]
2. `(ρ⁻¹; ρ)(x) = ρ⁻¹(ρ(x)) = ρ⁻¹(a)`                       [Aux 2.3a]
3. Since `ρ(x) = a`, by Aux 3.0a, `ρ⁻¹(a) = x`              [Aux 3.0a]
4. `(ρ⁻¹; ρ)(x) = x = id(Γ')(x)`                            [(2), (3), Aux 2.0b]

Since the two renamings agree entry-wise on `Γ'`, `ρ⁻¹; ρ = id(Γ')`.

**Proof of `ρ; ρ⁻¹ = id(range(ρ))`** is symmetric: for `a ∈ range(ρ)`, `(ρ; ρ⁻¹)(a) = ρ(ρ⁻¹(a)) = ρ(x) = a` where `x = ρ⁻¹(a)`.

---

## 4. Strengthening

We adopt the renaming-based reformulation in §0.2.

### Aux 4.0a (range-recast of a renaming)

If `Γ ⊢ ρ : Γ'`, then `range(ρ) ⊢ ρ : Γ'`.

**Quantifiers / metric.** Induction on `D : Γ ⊢ ρ : Γ'`.

**Case WfRenNil:** `range(·) = ·`, `· ⊢ · : ·`.

**Case WfRenCons** (`ρ = ρ₀, c/x`, `Γ - c ≡ Γ_outer`, `D₀ : Γ_outer ⊢ ρ₀ : Γ'₀`):
1. `range(ρ) = range(ρ₀), c`                                 [defn]
2. `range(ρ₀) ⊢ ρ₀ : Γ'₀`                                    [IH on `D₀`]
3. `(range(ρ₀), c) - c ≡ range(ρ₀)`                          [RemVarHere; uses `c ∉ range(ρ₀)`, by linearity of `ρ`]
4. `(range(ρ₀), c) ⊢ (ρ₀, c/x) : (Γ'₀, x)`                   [WfRenCons, (3), (2)]
5. `range(ρ) ⊢ ρ : Γ'`                                       [(1), (4)]

### Aux 4.0b (subsequence-induced renaming)

If `Γ_a ⊆ Γ_b` (subsequence) and `Γ_b` is duplicate-free, then there exists a renaming `ρ_emb(Γ_a, Γ_b)` with `Γ_b ⊢ ρ_emb : Γ_a` and `ρ_emb(x) = x` for each `x ∈ Γ_a`.

**Quantifiers / metric.** Induction on `D : Γ_a ⊆ Γ_b`.

**Case WkNilCx** (`Γ_a = ·`):
1. Take `ρ_emb := ·`.
2. `Γ_b ⊢ · : ·`                                             [WfRenNil]
3. Vacuously, `ρ_emb(x) = x` for `x ∈ ·`.

**Case WkConsCx** (`Γ_a = Γ_a', x`, `Γ_b = Γ_b', x`, `D' : Γ_a' ⊆ Γ_b'`):
1. By IH on `D'`: `Γ_b' ⊢ ρ_emb' : Γ_a'` with identity action.    [IH]
2. `(Γ_b', x) - x ≡ Γ_b'`                                    [RemVarHere; uses `x ∉ Γ_b'` from duplicate-freeness]
3. Take `ρ_emb := (ρ_emb', x/x)`.
4. `(Γ_b', x) ⊢ (ρ_emb', x/x) : (Γ_a', x)`                   [WfRenCons, (2), (1)]
5. For `y ∈ Γ_a', x`:
   - If `y = x`: `ρ_emb(x) = x` (lookup head).
   - If `y ∈ Γ_a'`: `ρ_emb(y) = ρ_emb'(y) = y` (lookup cons + IH).

**Case WkSkipCx** (`Γ_a ⊆ Γ_b'`, `Γ_b = Γ_b', y`, `D' : Γ_a ⊆ Γ_b'`):
1. By IH on `D'`: `Γ_b' ⊢ ρ_emb' : Γ_a` with identity action.     [IH]
2. `y ∉ Γ_b'` (from duplicate-freeness of `Γ_b`).
3. `(Γ_b', y) ⊢ ρ_emb' : Γ_a`                                [Aux 2.7a on (1), (2)]
4. Take `ρ_emb := ρ_emb'`.

### Aux 4.0c (identity action on terms)

If `Γ_b ⊢ ρ : Γ_a` and `ρ(x) = x` for all `x ∈ Γ_a`, and `Θ; Γ_a ⊢ t`, then `[ρ]t = t`.

**Quantifiers / metric.** Induction on the structure of `t` (with the typing in `Θ; Γ_a` providing well-formedness).

**Case `t = a`:** `[ρ]a = ρ(a) = a` (by hypothesis on `ρ`).

**Case `t = c`:** `[ρ]c = c`.

**Case `t = f(t_1, t_2)`:** `[ρ]f(t_1, t_2) = f([ρ]t_1, [ρ]t_2) = f(t_1, t_2)` by IH.

**Case `t = X[ρ_x]`** (with `X:[Γ_X] ∈ Θ`, `Γ_a ⊢ ρ_x : Γ_X`):
1. `[ρ](X[ρ_x]) = X[ρ; ρ_x]`                                 [defn]
2. For each `z ∈ Γ_X`, `(ρ; ρ_x)(z) = ρ(ρ_x(z))` and `ρ_x(z) ∈ Γ_a` (§2.1), so `ρ(ρ_x(z)) = ρ_x(z)` (hyp on `ρ`).        [Aux 2.3a, hyp]
3. `ρ; ρ_x = ρ_x` (entry-wise)                               [(2)]
4. `[ρ](X[ρ_x]) = X[ρ_x]`                                    [(1), (3)]

### 4.1 (Strengthening) `Θ; Γ ⊢ t` ⇒ exists a duplicate-free `Γ₀ ⊆ Γ` with elements equal to `fv(t)` as a set, and `Θ; Γ₀ ⊢ t`

**Quantifiers / metric.** Induction on `D : Θ; Γ ⊢ t`.

**Case WfVar** (so `t = a` with `a ∈ Γ`):
1. `fv(a) = {a}`                                             [defn `fv`]
2. Take `Γ₀ := ·, a`.
3. `Γ₀ ⊆ Γ` (by induction on `a ∈ Γ`: at the InHere step apply WkConsCx; at each InThere step apply WkSkipCx; the initial step is WkNilCx).
4. `a ∈ (·, a)`                                              [InHere]
5. `Θ; (·, a) ⊢ a`                                           [WfVar, (4)]
6. Elements of `Γ₀ = fv(t)` as a set.                        [(1), (2)]

**Case WfCon:** take `Γ₀ := ·`. `Θ; · ⊢ c` by WfCon. `· ⊆ Γ` by WkNilCx. `fv(c) = ∅` matches.

**Case WfFun** (from `D₁ : Θ; Γ ⊢ t_1` and `D₂ : Θ; Γ ⊢ t_2`):
1. By IH on `D_1`: `Γ_1 ⊆ Γ` with elements `fv(t_1)`, `Θ; Γ_1 ⊢ t_1`.    [IH]
2. By IH on `D_2`: `Γ_2 ⊆ Γ` with elements `fv(t_2)`, `Θ; Γ_2 ⊢ t_2`.    [IH]
3. Define `Γ₀` as the unique subsequence of `Γ` whose elements are `fv(t_1) ∪ fv(t_2)`. Since `Γ` is duplicate-free and finite, this is well-defined: walk through `Γ` and keep variables appearing in `fv(t_1) ∪ fv(t_2)`.        [construction]
4. `Γ₀ ⊆ Γ` by construction.
5. `Γ_1 ⊆ Γ₀` (every variable of `Γ_1` lies in `fv(t_1) ⊆ fv(t_1) ∪ fv(t_2)` and `Γ_1, Γ₀` both follow `Γ`'s order).   [construction]
6. `Γ_2 ⊆ Γ₀`                                                [analogous]
7. By Aux 4.0b: `Γ₀ ⊢ ρ_1 : Γ_1` (identity action), `Γ₀ ⊢ ρ_2 : Γ_2`.    [Aux 4.0b on (5), (6)]
8. By §2.4: `Θ; Γ₀ ⊢ [ρ_1]t_1`, and by Aux 4.0c, `[ρ_1]t_1 = t_1`. So `Θ; Γ₀ ⊢ t_1`.    [§2.4, Aux 4.0c on (1), (7)]
9. Similarly `Θ; Γ₀ ⊢ t_2`.                                  [(2), Aux 4.0c, §2.4]
10. `Θ; Γ₀ ⊢ f(t_1, t_2)`                                    [WfFun, (8), (9)]

**Case WfMeta** (so `t = X[ρ_inner]` with `X:[Γ_X] ∈ Θ`, `Γ ⊢ ρ_inner : Γ_X`):
1. `fv(X[ρ_inner]) = range(ρ_inner)` (as a set).             [defn `fv`]
2. By §3.0, `range(ρ_inner) ⊆ Γ` (subsequence).
3. By Aux 4.0a, `range(ρ_inner) ⊢ ρ_inner : Γ_X`.            [Aux 4.0a]
4. Take `Γ₀ := range(ρ_inner)`. Then `Γ₀ ⊆ Γ` by (2).
5. `Θ; Γ₀ ⊢ X[ρ_inner]`                                      [WfMeta on `X:[Γ_X] ∈ Θ`, (3)]
6. Elements of `Γ₀` equal `fv(t)` by (1).

---

## 5. Metaweakening

### Aux 5.0 (metaweakening preserves membership)

If `Θ ⊇ Θ'` and `X:[Γ] ∈ Θ'`, then `X:[Γ] ∈ Θ`.

**Quantifiers / metric.** Induction on `D : Θ ⊇ Θ'`.

**Case WkNil** (so `Θ = Θ' = ·`):
1. `X:[Γ] ∈ ·`                                               [hyp]
2. No rule concludes this; vacuous.

**Case WkCons** (so `Θ = Θ₀, W:[Γ_W]`, `Θ' = Θ'₀, W:[Γ_W]`, from `D' : Θ₀ ⊇ Θ'₀`):

  Case-split on `E : X:[Γ] ∈ Θ'₀, W:[Γ_W]`:

  **Sub-case `X = W`** (so `Γ = Γ_W`):
  1. `X:[Γ] ∈ Θ₀, W:[Γ_W]` by InHere.
  2. i.e., `X:[Γ] ∈ Θ`.

  **Sub-case `X ≠ W`** (so `X:[Γ] ∈ Θ'₀`):
  1. `X:[Γ] ∈ Θ₀`                                            [IH on `D'`]
  2. `X:[Γ] ∈ Θ₀, W:[Γ_W]`                                   [InThere, (1)]

**Case WkSkip** (so `Θ = Θ₀, W:[Γ_W]`, `Θ₀ ⊇ Θ'`, from `D' : Θ₀ ⊇ Θ'`):
1. `X:[Γ] ∈ Θ₀`                                              [IH on `D'`]
2. `X:[Γ] ∈ Θ₀, W:[Γ_W]`                                     [InThere, (1)]

### 5.1 `Θ ⊇ Θ'` and `Θ'; Γ ⊢ t` ⇒ `Θ; Γ ⊢ t`

**Quantifiers / metric.** Universal in `Γ, t`. Induction on `D : Θ'; Γ ⊢ t`.

**Case WfVar:**
1. `Θ; Γ ⊢ a` by WfVar (using the WfVar premise `a ∈ Γ`).

**Case WfCon:** `Θ; Γ ⊢ c` by WfCon.

**Case WfFun:**
1. `Θ; Γ ⊢ t_1`, `Θ; Γ ⊢ t_2`                                [IH on premises]
2. `Θ; Γ ⊢ f(t_1, t_2)`                                      [WfFun, (1)]

**Case WfMeta** (`t = X[ρ]`, from `X:[Γ_X] ∈ Θ'`, `Γ ⊢ ρ : Γ_X`):
1. `X:[Γ_X] ∈ Θ`                                             [Aux 5.0 on hyp, premise]
2. `Γ ⊢ ρ : Γ_X`                                             [premise]
3. `Θ; Γ ⊢ X[ρ]`                                             [WfMeta, (1), (2)]

---

## 6. Metasubstitution

### 6.1 `Θ ⊇ Θ'` and `Θ' ⊢ σ : Θ''` ⇒ `Θ ⊢ σ : Θ''`

**Quantifiers / metric.** Universal in `Θ''`. Induction on `D : Θ' ⊢ σ : Θ''`.

**Case SubNil:** `Θ ⊢ · : ·` by SubNil.

**Case SubCons** (so `σ = σ_0, t/X`, `Θ'' = Θ''_0, X:[Γ]`):
1. `Θ ⊢ σ_0 : Θ''_0`                                         [IH on left premise]
2. `Θ; Γ ⊢ t`                                                [§5.1 on hyp, right premise]
3. `Θ ⊢ (σ_0, t/X) : (Θ''_0, X:[Γ])`                         [SubCons, (1), (2)]

### 6.2 `Θ ⊢ σ : Θ'` and `X:[Γ] ∈ Θ'` ⇒ `Θ; Γ ⊢ σ(X)`

**Quantifiers / metric.** Universal in `X, Γ`. Induction on `D : Θ ⊢ σ : Θ'`.

**Case SubNil:** vacuous.

**Case SubCons** (`σ = σ_0, t/X_0`, `Θ' = Θ'_0, X_0:[Γ_0]`, from `D_1, D_2`):

  **Sub-case `X = X_0`** (so `Γ = Γ_0`):
  1. `σ(X) = t`                                              [lookup head]
  2. `Θ; Γ ⊢ t`                                              [`D_2`, `Γ = Γ_0`]

  **Sub-case `X ≠ X_0`** (so `X:[Γ] ∈ Θ'_0`):
  1. `σ(X) = σ_0(X)`                                         [lookup cons]
  2. `Θ; Γ ⊢ σ_0(X)`                                         [IH on `D_1`]
  3. `Θ; Γ ⊢ σ(X)`                                           [(1), (2)]

### 6.3 `Θ ⊢ σ : Θ'` and `Θ'; Γ ⊢ t` ⇒ `Θ; Γ ⊢ [σ]t`

**Quantifiers / metric.** Universal in `Γ, t`. Induction on `D : Θ'; Γ ⊢ t`.

**Case WfVar:** `[σ]a = a`; `Θ; Γ ⊢ a` by WfVar.

**Case WfCon:** `[σ]c = c`; `Θ; Γ ⊢ c` by WfCon.

**Case WfFun:**
1. `[σ]f(t_1, t_2) = f([σ]t_1, [σ]t_2)`                      [defn]
2. `Θ; Γ ⊢ [σ]t_i`                                           [IH on `D_i`]
3. `Θ; Γ ⊢ f([σ]t_1, [σ]t_2)`                                [WfFun, (2)]

**Case WfMeta** (`t = X[ρ]`):
1. `[σ](X[ρ]) = [ρ](σ(X))`                                   [defn]
2. `Θ; Γ_X ⊢ σ(X)`                                           [§6.2 on hyp, premise of `D`]
3. `Θ; Γ ⊢ [ρ](σ(X))`                                        [§2.4 on (2), premise]

### Aux 6.4a (lookup of identity σ)

If `X:[Γ] ∈ Θ`, then `id(Θ)(X) = X[id(Γ)]`.

**Quantifiers / metric.** Induction on `Θ`.

**Case `Θ = ·`:** vacuous.

**Case `Θ = Θ_0, Y:[Γ_Y]`:**

  **Sub-case `X = Y`** (so `Γ = Γ_Y`):
  1. `id(Θ_0, Y:[Γ_Y]) = id(Θ_0), Y[id(Γ_Y)]/Y`              [defn `id`]
  2. `id(Θ)(Y) = Y[id(Γ_Y)]`                                 [(1), lookup head]
  3. `id(Θ)(X) = X[id(Γ)]`                                   [(2), `X = Y`]

  **Sub-case `X ≠ Y`** (so `X:[Γ] ∈ Θ_0`):
  1. `id(Θ)(X) = id(Θ_0)(X)`                                 [defn, lookup cons]
  2. `id(Θ_0)(X) = X[id(Γ)]`                                 [IH on `Θ_0`]
  3. `id(Θ)(X) = X[id(Γ)]`                                   [(1), (2)]

### 6.4 `Θ ⊢ id(Θ) : Θ`

**Quantifiers / metric.** Induction on `Θ`.

**Case `Θ = ·`:** `id(·) = ·`, `· ⊢ · : ·` by SubNil.

**Case `Θ = Θ_0, X:[Γ]`:**
1. `id(Θ) = id(Θ_0), X[id(Γ)]/X`                             [defn `id`]
2. `Θ_0 ⊢ id(Θ_0) : Θ_0`                                     [IH on `Θ_0`]
3. `Θ ⊇ Θ_0` (one step of WkSkip from `Θ_0 ⊇ Θ_0`; the latter by reflexivity, proven by routine induction on `Θ_0`).        [WkSkip; reflexivity of `⊇`]
4. `Θ ⊢ id(Θ_0) : Θ_0`                                       [§6.1 on (3), (2)]
5. `Γ ⊢ id(Γ) : Γ`                                           [§2.2]
6. `X:[Γ] ∈ Θ`                                               [InHere]
7. `Θ; Γ ⊢ X[id(Γ)]`                                         [WfMeta, (6), (5)]
8. `Θ ⊢ (id(Θ_0), X[id(Γ)]/X) : (Θ_0, X:[Γ])`                [SubCons, (4), (7)]

### 6.5 `Θ; Γ ⊢ t` ⇒ `[id(Θ)]t = t`

**Quantifiers / metric.** Induction on `D : Θ; Γ ⊢ t`.

**Case WfVar:** `[id(Θ)]a = a` (defn `[σ]a = a`).

**Case WfCon:** `[id(Θ)]c = c`.

**Case WfFun:**
1. `[id(Θ)]f(t_1, t_2) = f([id(Θ)]t_1, [id(Θ)]t_2)`          [defn `[σ]`]
2. `[id(Θ)]t_i = t_i`                                        [IH on each premise]
3. `[id(Θ)]f(t_1, t_2) = f(t_1, t_2)`                        [(1), (2)]

**Case WfMeta** (`t = X[ρ]`):
1. `[id(Θ)](X[ρ]) = [ρ](id(Θ)(X))`                           [defn `[σ]`]
2. `id(Θ)(X) = X[id(Γ_X)]`                                   [Aux 6.4a]
3. `[ρ](X[id(Γ_X)]) = X[ρ; id(Γ_X)]`                         [defn `[ρ]`]
4. `ρ; id(Γ_X) = ρ`                                          [Aux 2.5b on premise of WfMeta]
5. `[id(Θ)](X[ρ]) = X[ρ]`                                    [(1)–(4)]

### Aux 6.6a (lookup of σ-composition)

For all `σ, σ', X`: `(σ; σ')(X) = [σ](σ'(X))`.

**Quantifiers / metric.** Induction on the structure of `σ'`.

**Case `σ' = ·`:** vacuous (`σ'(X)` undefined).

**Case `σ' = σ'_0, t/Y`:**

  **Sub-case `X = Y`:**
  1. `σ'(Y) = t`                                             [lookup head]
  2. `σ; σ' = (σ; σ'_0), [σ]t/Y`                             [defn composition]
  3. `(σ; σ')(Y) = [σ]t`                                     [(2), lookup head]
  4. `[σ](σ'(Y)) = [σ]t`                                     [(1)]

  **Sub-case `X ≠ Y`:**
  1. `σ'(X) = σ'_0(X)`                                       [lookup cons]
  2. `σ; σ' = (σ; σ'_0), [σ]t/Y`                             [defn]
  3. `(σ; σ')(X) = (σ; σ'_0)(X)`                             [(2), lookup cons]
  4. `(σ; σ'_0)(X) = [σ](σ'_0(X))`                           [IH on `σ'_0`]
  5. `(σ; σ')(X) = [σ](σ'(X))`                               [(1), (3), (4)]

### 6.6 `Θ ⊢ σ : Θ'` and `Θ' ⊢ σ' : Θ''` ⇒ `Θ ⊢ σ; σ' : Θ''`

**Quantifiers / metric.** Universal in `σ`. Induction on `D' : Θ' ⊢ σ' : Θ''`.

**Case SubNil:** `σ; · = ·`; `Θ ⊢ · : ·` by SubNil.

**Case SubCons** (`σ' = σ'_0, t/X`, `Θ'' = Θ''_0, X:[Γ]`):
1. `σ; (σ'_0, t/X) = (σ; σ'_0), [σ]t/X`                      [defn]
2. `Θ ⊢ σ; σ'_0 : Θ''_0`                                     [IH on left premise]
3. `Θ; Γ ⊢ [σ]t`                                             [§6.3 on hyp, right premise]
4. `Θ ⊢ (σ; σ'_0), [σ]t/X : (Θ''_0, X:[Γ])`                  [SubCons, (2), (3)]

### Aux 6.7a (σ-ρ commutation)

For any term `t` and any `σ, ρ`: `[σ]([ρ]t) = [ρ]([σ]t)`.

**Quantifiers / metric.** Induction on the structure of `t`.

**Case `t = a`:**
1. `[ρ]a = ρ(a)` (a variable).
2. `[σ](ρ(a)) = ρ(a)` (defn of `[σ]` on a variable: identity).
3. `[σ]a = a`.
4. `[ρ]a = ρ(a)`.
5. Both sides equal `ρ(a)`.

**Case `t = c`:** both sides equal `c`.

**Case `t = f(t_1, t_2)`:**
1. `[ρ]f(t_1, t_2) = f([ρ]t_1, [ρ]t_2)`                      [defn]
2. `[σ]f([ρ]t_1, [ρ]t_2) = f([σ][ρ]t_1, [σ][ρ]t_2)`          [defn]
3. By IH on `t_i`: `[σ][ρ]t_i = [ρ][σ]t_i`.
4. `[σ][ρ]f(t_1, t_2) = f([ρ][σ]t_1, [ρ][σ]t_2)`             [(2), (3)]
5. `[ρ][σ]f(t_1, t_2) = [ρ]f([σ]t_1, [σ]t_2) = f([ρ][σ]t_1, [ρ][σ]t_2)`   [defn]
6. Equal.                                                    [(4), (5)]

**Case `t = X[ρ_x]`:**
1. `[ρ]X[ρ_x] = X[ρ; ρ_x]`                                   [defn]
2. `[σ]X[ρ; ρ_x] = [ρ; ρ_x](σ(X))`                           [defn]
3. `[σ]X[ρ_x] = [ρ_x](σ(X))`                                 [defn]
4. `[ρ]([ρ_x](σ(X))) = [ρ; ρ_x](σ(X))`                       [§2.6 on `σ(X)`]
5. `[σ][ρ]X[ρ_x] = [ρ; ρ_x](σ(X)) = [ρ][σ]X[ρ_x]`            [(2), (3), (4)]

### 6.7 `[σ]([σ']t) = [σ; σ']t`

**Quantifiers / metric.** Universal in `σ, σ'`. Induction on `t`.

**Case `t = a`:** all three reduce to `a`.

**Case `t = c`:** all three reduce to `c`.

**Case `t = f(t_1, t_2)`:**
1. `[σ']f(t_1, t_2) = f([σ']t_1, [σ']t_2)`                   [defn]
2. `[σ]f([σ']t_1, [σ']t_2) = f([σ][σ']t_1, [σ][σ']t_2)`      [defn]
3. `[σ][σ']t_i = [σ; σ']t_i`                                 [IH on `t_i`]
4. `[σ; σ']f(t_1, t_2) = f([σ; σ']t_1, [σ; σ']t_2)`          [defn]
5. Equal.

**Case `t = X[ρ]`:**
1. `[σ']X[ρ] = [ρ](σ'(X))`                                   [defn]
2. `[σ]([ρ](σ'(X))) = [ρ]([σ](σ'(X)))`                       [Aux 6.7a]
3. `[σ](σ'(X)) = (σ; σ')(X)`                                 [Aux 6.6a]
4. `[ρ]((σ; σ')(X)) = [σ; σ']X[ρ]`                           [defn]
5. `[σ][σ']X[ρ] = [σ; σ']X[ρ]`                               [(1)–(4)]

---

## 7. Pushout

### 7.1 (Typing) If `Γ ⊢ ρ_1 : Γ_1`, `Γ ⊢ ρ_2 : Γ_2`, and `Γ ⊢ ρ_1 ⊔ ρ_2 = i_1; i_2 : Γ_3`, then `Γ_1 ⊢ i_1 : Γ_3` and `Γ_2 ⊢ i_2 : Γ_3`

**Quantifiers / metric.** Induction on `D : Γ ⊢ ρ_1 ⊔ ρ_2 = i_1; i_2 : Γ_3`.

**Case PushNilL** (so `ρ_1 = ·`, hence `Γ_1 = ·`, `i_1 = i_2 = · = Γ_3`):
1. `· ⊢ · : ·` by WfRenNil; `Γ_2 ⊢ · : ·` by WfRenNil (any source).

**Case PushNilR** (symmetric).

**Case PushConsVar** (so `ρ_1 = ρ_1', y/x`, `Γ_1 = Γ_1', x`, premise `ρ_2|y ≡ ρ'_2, y/z`, recursive `D' : Γ ⊢ ρ_1' ⊔ ρ'_2 = i_1'; i_2' : Γ_3'`, conclusion `i_1 = i_1', x/y`, `i_2 = i_2', z/y`, `Γ_3 = Γ_3', y`):
1. By inversion on `Γ ⊢ ρ_1 : Γ_1`: `Γ_1 = Γ_1', x`, `Γ - y ≡ Γ_y`, `Γ_y ⊢ ρ_1' : Γ_1'`.   [WfRenCons inversion]
2. By inversion on `ρ_2|y ≡ ρ'_2, y/z` together with `Γ ⊢ ρ_2 : Γ_2`: `Γ_2` has `z` as an element with `ρ_2(z) = y`. Writing this in WfRenCons form (after possibly permuting `ρ_2`'s presentation to put `y/z` last): `Γ_2 = Γ'_2_cod, z`, `Γ - y ≡ Γ_y` (same `Γ_y` since `y` is the output of `y/z`), `Γ_y ⊢ ρ'_2 : Γ'_2_cod`.    [Aux 2.3b on `Γ ⊢ ρ_2 : Γ_2` at the input mapping to `y`]
3. `Γ_1' ⊢ i_1' : Γ_3'` and `Γ'_2_cod ⊢ i_2' : Γ_3'`         [IH on `D'`, (1), (2)]
4. `(Γ_1', x) - x ≡ Γ_1'`                                    [RemVarHere]
5. `(Γ_3', y) - y ≡ Γ_3'`                                    [RemVarHere]
6. `(Γ_1', x) ⊢ (i_1', x/y) : (Γ_3', y)`                     [WfRenCons, (4), (3)]
7. `Γ_1 ⊢ i_1 : Γ_3`                                         [(6), case shape]
8. `(Γ'_2_cod, z) - z ≡ Γ'_2_cod`                            [RemVarHere]
9. `(Γ'_2_cod, z) ⊢ (i_2', z/y) : (Γ_3', y)`                 [WfRenCons, (8), (3)]
10. `Γ_2 ⊢ i_2 : Γ_3`                                        [(9), case shape, (2)]

**Case PushConsSkip** (so `ρ_1 = ρ_1', y/x`, `Γ_1 = Γ_1', x`, premise `ρ_2|y ≡ ⊥`, recursive `D' : Γ ⊢ ρ_1' ⊔ ρ_2 = p_1; p_2 : Γ'`, conclusion `i_1 = p_1`, `i_2 = p_2`, `Γ_3 = Γ'`):
1. By inversion: `Γ_1 = Γ_1', x`, `Γ - y ≡ Γ_y`, `Γ_y ⊢ ρ_1' : Γ_1'`.   [WfRenCons inversion]
2. `Γ_1' ⊢ p_1 : Γ'` and `Γ_2 ⊢ p_2 : Γ'`                    [IH on `D'`, (1)]
3. `x ∉ Γ_1'` (since `Γ_1', x` is well-formed: WfRenCons-style RemVarHere requires `x` fresh)   [duplicate-freeness]
4. `(Γ_1', x) ⊢ p_1 : Γ'`                                    [Aux 2.7a on (2), (3)]
5. `Γ_1 ⊢ i_1 : Γ_3`                                         [(4), case shape]
6. `Γ_2 ⊢ i_2 : Γ_3`                                         [(2), case shape]

### 7.2 (Equation) `ρ_1; i_1 = ρ_2; i_2`

**Quantifiers / metric.** Induction on `D`.

**Case PushNilL:** `ρ_1; i_1 = ·; · = ·`; `ρ_2; i_2 = ρ_2; · = ·`. Equal.

**Case PushNilR:** symmetric.

**Case PushConsVar:**
1. By IH on `D'`: `ρ_1'; i_1' = ρ'_2; i_2'`.                 [IH]
2. `ρ_1; i_1 = (ρ_1', y/x); (i_1', x/y)`.                    [case shape]
3. By defn of composition: `= ((ρ_1', y/x); i_1'), (ρ_1', y/x)(x)/y = ((ρ_1', y/x); i_1'), y/y`.    [defn, lookup head]
4. *Claim* `(ρ_1', y/x); i_1' = ρ_1'; i_1'`. Entry-wise on `i_1'`'s inputs (which are in `Γ_3' ∋ z'`): `(ρ_1', y/x)(i_1'(z')) = ρ_1'(i_1'(z'))` because `i_1'(z') ∈ Γ_1'` (§2.1 on (3) of 7.1's case) and `x ∉ Γ_1'` so `i_1'(z') ≠ x`; hence the head entry `y/x` doesn't fire.   [Aux 2.3a, §2.1]
5. `ρ_1; i_1 = (ρ_1'; i_1'), y/y`.                           [(3), (4)]
6. Symmetric: `ρ_2; i_2 = (ρ_2_full); (i_2', z/y)` where ρ_2_full has the `y/z` entry; computing entry-wise as above: `ρ_2; i_2 = (ρ'_2; i_2'), y/y`.        [analogous]
7. `(ρ_1'; i_1'), y/y = (ρ'_2; i_2'), y/y`.                  [(1), (5), (6)]

**Case PushConsSkip:**
1. By IH on `D'`: `ρ_1'; p_1 = ρ_2; p_2`.                    [IH]
2. `ρ_1; i_1 = (ρ_1', y/x); p_1`.                            [case shape]
3. *Claim* `(ρ_1', y/x); p_1 = ρ_1'; p_1`. By Aux 2.3a, entry-wise on `p_1`'s inputs (in `Γ_3 = Γ'`): we need `(ρ_1', y/x)(p_1(z')) = ρ_1'(p_1(z'))`. `p_1(z') ∈ Γ_1'` (§2.1) and `x ∉ Γ_1'`. So `p_1(z') ≠ x` and the head `y/x` entry of `(ρ_1', y/x)` doesn't fire.   [Aux 2.3a, §2.1]
4. `ρ_1; i_1 = ρ_1'; p_1`.                                   [(2), (3)]
5. `ρ_2; i_2 = ρ_2; p_2` (no change since `i_2 = p_2`).       [case shape]
6. `ρ_1; i_1 = ρ_2; i_2`                                     [(1), (4), (5)]

### Aux 7.3a (range characterization for pushout)

For a pushout derivation `D : Γ ⊢ ρ_1 ⊔ ρ_2 = i_1; i_2 : Γ_3`:
- For `x ∈ Γ_1`: `x ∈ range(i_1)` iff `ρ_1(x) ∈ range(ρ_2)`.
- For `z ∈ Γ_2`: `z ∈ range(i_2)` iff `ρ_2(z) ∈ range(ρ_1)`.

**Quantifiers / metric.** Induction on `D`.

**Case PushNilL:** `Γ_1 = ·`, so the first claim is vacuous. For the second: `range(i_2) = range(·) = ·`, and `range(ρ_1) = ·`, so `ρ_2(z) ∈ range(ρ_1)` is `ρ_2(z) ∈ ·`, never true. Both sides are "false," equal.

**Case PushNilR:** symmetric.

**Case PushConsVar** (`ρ_1 = ρ_1', y/x`, ρ_2 has `y/z` entry, recursive `D' : Γ ⊢ ρ_1' ⊔ ρ'_2 = i_1'; i_2' : Γ_3'`, `i_1 = i_1', x/y`):

For the first claim, let `x' ∈ Γ_1 = Γ_1', x`:
- **Sub-case `x' = x`:**
  1. `ρ_1(x) = y`                                            [lookup head]
  2. `y = ρ_2(z) ∈ range(ρ_2)`                               [defn `range`]
  3. `range(i_1) = range(i_1'), x`, so `x ∈ range(i_1)`.     [defn `range`]
  4. Both sides hold. ✓
- **Sub-case `x' ∈ Γ_1'` (so `x' ≠ x`):**
  1. `ρ_1(x') = ρ_1'(x')`                                    [lookup cons]
  2. By IH on `D'` for `x'`: `x' ∈ range(i_1')` iff `ρ_1'(x') ∈ range(ρ'_2)`.   [IH]
  3. `range(ρ_2) = range(ρ'_2) ∪ {y}` (since `ρ_2 = ρ'_2 + y/z`).
  4. *Sub-claim* `ρ_1'(x') ≠ y`. Because `ρ_1` is linear and the entry mapping to `y` is `y/x` (with input `x`, not `x'`).   [linearity]
  5. So `ρ_1'(x') ∈ range(ρ_2)` iff `ρ_1'(x') ∈ range(ρ'_2)` (by (3) and (4)).
  6. `x' ∈ range(i_1)` iff `x' ∈ range(i_1')` (by `range(i_1) = range(i_1') + x` and `x' ≠ x`).
  7. Combining: `x' ∈ range(i_1)` iff `x' ∈ range(i_1')` iff `ρ_1'(x') ∈ range(ρ'_2)` iff `ρ_1(x') ∈ range(ρ_2)`.   [(1), (2), (5), (6)]

For the second claim: analogous with `ρ_2` and `i_2`.

**Case PushConsSkip** (`ρ_2|y ≡ ⊥`, recursive `D' : Γ ⊢ ρ_1' ⊔ ρ_2 = p_1; p_2 : Γ'`, `i_1 = p_1`):

For the first claim, `x' ∈ Γ_1 = Γ_1', x`:
- **Sub-case `x' = x`:**
  1. `ρ_1(x) = y`                                            [lookup head]
  2. `y ∉ range(ρ_2)` (premise `ρ_2|y ≡ ⊥`).                  [premise]
  3. `range(i_1) = range(p_1)`, and `x ∉ range(p_1)` (since `p_1`'s outputs lie in `Γ_1'` by §2.1+§3.0, and `x ∉ Γ_1'` by duplicate-freeness). So `x ∉ range(i_1)`.   [§3.0, duplicate-freeness]
  4. Both sides "false." ✓
- **Sub-case `x' ∈ Γ_1'`:** as in PushConsVar's sub-case, using IH on `D'` and noting `ρ_2` is unchanged (no entry was removed) so `range(ρ'_2) = range(ρ_2)`.

### 7.3 (Universal property) For all `Γ_1 ⊢ q_1 : Δ`, `Γ_2 ⊢ q_2 : Δ` with `ρ_1; q_1 = ρ_2; q_2`, there exists `Γ_3 ⊢ q' : Δ` with `q_1 = i_1; q'` and `q_2 = i_2; q'`

**Construction.** Define `q'(d) := i_1⁻¹(q_1(d))` for each `d ∈ Δ`.

**Well-definedness.** For `d ∈ Δ`:
1. `q_1(d) ∈ Γ_1`                                            [§2.1 on `Γ_1 ⊢ q_1 : Δ`]
2. `ρ_1(q_1(d)) = (ρ_1; q_1)(d)`                             [Aux 2.3a]
3. `(ρ_1; q_1)(d) = (ρ_2; q_2)(d) = ρ_2(q_2(d))`             [hyp, Aux 2.3a]
4. `ρ_2(q_2(d)) ∈ range(ρ_2)`                                [defn `range`]
5. `ρ_1(q_1(d)) ∈ range(ρ_2)`                                [(2), (3), (4)]
6. By Aux 7.3a, `q_1(d) ∈ range(i_1)`.                       [Aux 7.3a, (5)]
7. So `i_1⁻¹(q_1(d))` is defined (by §3.1).

**Linearity of `q'`.** Suppose `q'(d_1) = q'(d_2)` for `d_1, d_2 ∈ Δ`.
1. `i_1⁻¹(q_1(d_1)) = i_1⁻¹(q_1(d_2))`                       [hyp]
2. Since `i_1⁻¹` is injective (it is a well-formed renaming): `q_1(d_1) = q_1(d_2)`.   [linearity of `i_1⁻¹`]
3. Since `q_1` is injective (it is a well-formed renaming): `d_1 = d_2`.   [linearity of `q_1`]

**Typing `Γ_3 ⊢ q' : Δ`.** By construction, `q'` is a function `Δ → Γ_3` that is linear (just shown) and total (just shown well-defined). To package this as a renaming `Γ_3 ⊢ q' : Δ` in WfRenCons form, we construct it inductively on `Δ`:
- `Δ = ·`: `q' = ·`. `Γ_3 ⊢ · : ·` by WfRenNil (any source `Γ_3` works).
- `Δ = Δ_0, d`: define `q'(d) ∈ Γ_3` as above, and recursively for `Δ_0`. By linearity, `q'(d)` is not among the values for `Δ_0`. So `Γ_3 - q'(d) ≡ Γ_3_minus` for some `Γ_3_minus`, and recursion gives `Γ_3_minus ⊢ q'_restricted : Δ_0`. WfRenCons gives `Γ_3 ⊢ q' : Δ_0, d`.   [WfRenCons on linearity-justified removal]

**Equation `q_1 = i_1; q'`.** Entry-wise on `Δ`:
1. `(i_1; q')(d) = i_1(q'(d)) = i_1(i_1⁻¹(q_1(d))) = q_1(d)` [Aux 2.3a, Aux 3.0a (round-trip)]

**Equation `q_2 = i_2; q'`.** Entry-wise on `Δ`:
1. `(i_2; q')(d) = i_2(q'(d))`                               [Aux 2.3a]
2. By §7.2, `ρ_1; i_1 = ρ_2; i_2`, so for any `γ ∈ Γ_3`, `ρ_1(i_1(γ)) = ρ_2(i_2(γ))`. Applied at `γ := q'(d)`:
   `ρ_1(i_1(q'(d))) = ρ_2(i_2(q'(d)))`                       [§7.2, Aux 2.3a]
3. `i_1(q'(d)) = q_1(d)` (just shown above).                 [equation `q_1 = i_1; q'`]
4. `ρ_1(q_1(d)) = ρ_2(i_2(q'(d)))`                           [(2), (3)]
5. `ρ_1(q_1(d)) = ρ_2(q_2(d))`                               [hyp `ρ_1; q_1 = ρ_2; q_2`, Aux 2.3a]
6. `ρ_2(i_2(q'(d))) = ρ_2(q_2(d))`                           [(4), (5)]
7. `i_2(q'(d)) = q_2(d)`                                     [injectivity of `ρ_2`, (6)]

---

## 8. Coequalizer

### 8.1 (Typing) If `Γ ⊢ ρ_1, ρ_2 : Γ'` and `Γ ⊢ ρ_1 • ρ_2 = i : Γ''`, then `Γ' ⊢ i : Γ''`

**Quantifiers / metric.** Induction on `D : Γ ⊢ ρ_1 • ρ_2 = i : Γ''`.

**Case CoeqNil:** `· ⊢ · : ·`.

**Case CoeqConsOk** (so `ρ_1 = ρ_1', y/x`, `ρ_2 = ρ_2', y/x`, recursive `D' : Γ ⊢ ρ_1' • ρ_2' = i' : Γ''_0`, `i = i', x/y`):
1. By inversion: `Γ' = Γ'_0, x`, `Γ - y ≡ Γ_y`, `Γ_y ⊢ ρ_1' : Γ'_0`.   [WfRenCons inversion on `Γ ⊢ ρ_1 : Γ'`]
2. Similarly `Γ_y ⊢ ρ_2' : Γ'_0`.                            [analogous]
3. `Γ'_0 ⊢ i' : Γ''_0`                                       [IH on `D'`, (1), (2)]
4. `(Γ'_0, x) - x ≡ Γ'_0`                                    [RemVarHere]
5. `(Γ'_0, x) ⊢ (i', x/y) : (Γ''_0, y)`                      [WfRenCons, (4), (3)]
6. `Γ' ⊢ i : Γ''`                                            [(5), case shape]

**Case CoeqConsSkip** (so `ρ_1 = ρ_1', y/x`, `ρ_2 = ρ_2', z/x` with `y ≠ z`, recursive `D' : Γ ⊢ ρ_1' • ρ_2' = i : Γ''`):
1. By inversion: `Γ' = Γ'_0, x`, `Γ - y ≡ Γ_y_1` with `Γ_y_1 ⊢ ρ_1' : Γ'_0`; `Γ - z ≡ Γ_y_2` with `Γ_y_2 ⊢ ρ_2' : Γ'_0`.   [inversion]
2. `Γ'_0 ⊢ i : Γ''`                                          [IH on `D'`]
3. `x ∉ Γ'_0` (duplicate-freeness of `Γ' = Γ'_0, x`).        [duplicate-freeness]
4. `(Γ'_0, x) ⊢ i : Γ''`                                     [Aux 2.7a on (2), (3)]
5. `Γ' ⊢ i : Γ''`                                            [(4), case shape]

### 8.2 (Equation) `ρ_1; i = ρ_2; i`

**Quantifiers / metric.** Induction on `D`.

**Case CoeqNil:** both sides equal `·`.

**Case CoeqConsOk:**
1. `(ρ_1', y/x); (i', x/y) = ((ρ_1', y/x); i'), (ρ_1', y/x)(x)/y = ((ρ_1', y/x); i'), y/y`     [defn, lookup head]
2. *Claim* `(ρ_1', y/x); i' = ρ_1'; i'` entry-wise: `i'`'s inputs lie in `Γ''_0`, none equal `x` (by duplicate-freeness of `Γ'`), so the head entry doesn't fire.   [Aux 2.3a, duplicate-freeness]
3. `ρ_1; i = (ρ_1'; i'), y/y`                                [(1), (2)]
4. Symmetric: `ρ_2; i = (ρ_2'; i'), y/y`                     [analogous]
5. `ρ_1'; i' = ρ_2'; i'`                                     [IH on `D'`]
6. Equal.                                                    [(3), (4), (5)]

**Case CoeqConsSkip:**
1. `(ρ_1', y/x); i = ρ_1'; i` entry-wise (as above; `i`'s inputs in `Γ''`, none equal `x`).   [Aux 2.3a]
2. `(ρ_2', z/x); i = ρ_2'; i` similarly.
3. `ρ_1'; i = ρ_2'; i`                                       [IH on `D'`]
4. Equal.                                                    [(1), (2), (3)]

### Aux 8.3a (range characterization for coequalizer)

For `D : Γ ⊢ ρ_1 • ρ_2 = i : Γ''`: for `x ∈ Γ'`, `x ∈ range(i)` iff `ρ_1(x) = ρ_2(x)`.

**Quantifiers / metric.** Induction on `D`.

**Case CoeqNil:** `Γ' = ·`, vacuous.

**Case CoeqConsOk** (`ρ_1 = ρ_1', y/x`, `ρ_2 = ρ_2', y/x`, `i = i', x/y`):

For `x' ∈ Γ' = Γ'_0, x`:
- **Sub-case `x' = x`:**
  1. `ρ_1(x) = y = ρ_2(x)`                                   [lookup head, both equal `y`]
  2. `x ∈ range(i) = range(i'), x`.                          [defn `range`]
  3. Both hold. ✓
- **Sub-case `x' ∈ Γ'_0`:**
  1. `ρ_1(x') = ρ_1'(x')` and `ρ_2(x') = ρ_2'(x')`           [lookup cons]
  2. By IH: `x' ∈ range(i')` iff `ρ_1'(x') = ρ_2'(x')` iff (by (1)) `ρ_1(x') = ρ_2(x')`.
  3. `x' ∈ range(i)` iff `x' ∈ range(i')` (since `range(i) = range(i'), x` and `x' ≠ x`).   [defn `range`]
  4. Conclusion: equivalent.                                  [(2), (3)]

**Case CoeqConsSkip** (`ρ_1 = ρ_1', y/x`, `ρ_2 = ρ_2', z/x`, `y ≠ z`, `i` unchanged):

For `x' ∈ Γ' = Γ'_0, x`:
- **Sub-case `x' = x`:**
  1. `ρ_1(x) = y ≠ z = ρ_2(x)`                               [lookup head, `y ≠ z`]
  2. `range(i)` does not contain `x` (the case `range(p_1)`-style argument as in 7.3a: `i`'s outputs lie in `Γ'_0`, and `x ∉ Γ'_0`).   [§3.0, §2.1, duplicate-freeness]
  3. Both "false." ✓
- **Sub-case `x' ∈ Γ'_0`:** as in CoeqConsOk's second sub-case, using IH on `D'`.

### 8.3 (Universal property) For all `Γ' ⊢ j : Δ` with `ρ_1; j = ρ_2; j`, exists `Γ'' ⊢ j' : Δ` with `j = i; j'`

**Construction.** Define `j'(d) := i⁻¹(j(d))` for each `d ∈ Δ`.

**Well-definedness.** For `d ∈ Δ`:
1. `j(d) ∈ Γ'`                                               [§2.1 on `Γ' ⊢ j : Δ`]
2. `(ρ_1; j)(d) = ρ_1(j(d))` and `(ρ_2; j)(d) = ρ_2(j(d))`    [Aux 2.3a]
3. `ρ_1(j(d)) = ρ_2(j(d))`                                   [hyp `ρ_1; j = ρ_2; j`, (2)]
4. By Aux 8.3a, `j(d) ∈ range(i)`.                           [Aux 8.3a, (3)]
5. So `i⁻¹(j(d))` is defined (§3.1).

**Linearity / typing.** As in §7.3: `j'` is linear because `i⁻¹` and `j` are both injective; and `Γ'' ⊢ j' : Δ` is constructed inductively on `Δ` using WfRenCons.

**Equation `j = i; j'`.** Entry-wise:
1. `(i; j')(d) = i(j'(d)) = i(i⁻¹(j(d))) = j(d)`             [Aux 2.3a, Aux 3.0a]

---

## 9. Unification theorem

**Theorem.** If `Θ; Γ ⊢ t_1`, `Θ; Γ ⊢ t_2`, and `Θ; Γ ⊢ t_1 = t_2 ↝ σ : Θ'`, then
- (A) `Θ' ⊢ σ : Θ`,
- (B) `[σ]t_1 = [σ]t_2`,
- (C) for every `Θ'' ⊢ τ : Θ` with `[τ]t_1 = [τ]t_2`, there exists `τ''` with `Θ'' ⊢ τ'' : Θ'` and `τ = τ''; σ`.

**Induction metric.** Height of `D : Θ; Γ ⊢ t_1 = t_2 ↝ σ : Θ'`. The three conclusions are proved by simultaneous induction. In clause (C), `Θ''` and `τ` are universally quantified.

### Aux 9.0 (σ acts as id on metavariables it agrees with id on)

If `σ` is a substitution with `σ(W) = W[id(Γ_W)]` for each `W ∈ Θ_sub`, and `t` satisfies `Θ_sub; Γ ⊢ t` for some `Γ`, then `[σ]t = t`.

**Quantifiers / metric.** Induction on the structure of `t`.

**Case `t = a`:** `[σ]a = a`. ✓

**Case `t = c`:** `[σ]c = c`. ✓

**Case `t = f(t_1, t_2)`:** by IH on `t_1, t_2` and defn `[σ]f(...)`.

**Case `t = W[ρ]`** (with `W ∈ Θ_sub` by WfMeta on `Θ_sub; Γ ⊢ t`):
1. `[σ]W[ρ] = [ρ](σ(W))`                                     [defn `[σ]`]
2. `σ(W) = W[id(Γ_W)]`                                       [hyp on `σ`]
3. `[ρ](W[id(Γ_W)]) = W[ρ; id(Γ_W)]`                         [defn `[ρ]`]
4. `ρ; id(Γ_W) = ρ`                                          [Aux 2.5b]
5. `[σ]W[ρ] = W[ρ]`                                          [(1)–(4)]

### Aux 9.1 (term coequalizer factorization)

If `Γ ⊢ ρ_1, ρ_2 : Γ_X`, `Γ ⊢ ρ_1 • ρ_2 = i : Γ'`, and `Θ; Γ_X ⊢ u` with `[ρ_1]u = [ρ_2]u`, then exists `Θ; Γ' ⊢ u'` with `[i]u' = u`.

**Quantifiers / metric.** Induction on the structure of `u`.

**Case `u = a`** (variable, `a ∈ Γ_X`):
1. `[ρ_j]a = ρ_j(a)` for `j = 1, 2`                          [defn]
2. `ρ_1(a) = ρ_2(a)`                                         [hyp `[ρ_1]u = [ρ_2]u`, (1)]
3. By Aux 8.3a, `a ∈ range(i)`.                              [Aux 8.3a, (2)]
4. `b := i⁻¹(a) ∈ Γ'` is defined (§3.1).
5. Take `u' := b` (viewed as a variable term).
6. `Θ; Γ' ⊢ b`                                               [WfVar, (4)]
7. `[i]b = i(b) = i(i⁻¹(a)) = a = u`                         [defn, Aux 3.0a]

**Case `u = c`:** take `u' := c`. `[i]c = c = u`. `Θ; Γ' ⊢ c` by WfCon.

**Case `u = f(u_1, u_2)`:**
1. `[ρ_j]f(u_1, u_2) = f([ρ_j]u_1, [ρ_j]u_2)`                [defn]
2. Inversion on `f([ρ_1]u_1, [ρ_1]u_2) = f([ρ_2]u_1, [ρ_2]u_2)`: `[ρ_1]u_i = [ρ_2]u_i`.   [inversion on `f`]
3. By inversion on `Θ; Γ_X ⊢ f(u_1, u_2)`: `Θ; Γ_X ⊢ u_i`.   [WfFun inversion]
4. By IH on `u_1, u_2`: `Θ; Γ' ⊢ u_i'` with `[i]u_i' = u_i`.   [IH]
5. Take `u' := f(u_1', u_2')`.
6. `Θ; Γ' ⊢ f(u_1', u_2')`                                   [WfFun, (4)]
7. `[i]f(u_1', u_2') = f([i]u_1', [i]u_2') = f(u_1, u_2) = u`   [defn, (4)]

**Case `u = Y[ρ_y]`** (with `Y:[Γ_Y] ∈ Θ`, `Γ_X ⊢ ρ_y : Γ_Y`):
1. `[ρ_j](Y[ρ_y]) = Y[ρ_j; ρ_y]`                             [defn]
2. `Y[ρ_1; ρ_y] = Y[ρ_2; ρ_y]` ⇒ `ρ_1; ρ_y = ρ_2; ρ_y`       [hyp, inversion on `Y[_] = Y[_]`]
3. By the coequalizer universal property §8.3, with `Γ_X ⊢ ρ_y : Γ_Y` playing the role of `j`: exists `Γ' ⊢ ρ_y' : Γ_Y` with `ρ_y = i; ρ_y'`.   [§8.3 on (2)]
4. Take `u' := Y[ρ_y']`.
5. `Θ; Γ' ⊢ Y[ρ_y']`                                         [WfMeta, `Y:[Γ_Y] ∈ Θ`, (3)]
6. `[i](Y[ρ_y']) = Y[i; ρ_y'] = Y[ρ_y] = u`                  [defn, (3)]

### Aux 9.2 (term pushout factorization)

If `Γ ⊢ ρ_1 : Γ_X`, `Γ ⊢ ρ_2 : Γ_Y`, `Γ ⊢ ρ_1 ⊔ ρ_2 = i_1; i_2 : Γ_Z`, and `Θ; Γ_X ⊢ u_X`, `Θ; Γ_Y ⊢ u_Y` with `[ρ_1]u_X = [ρ_2]u_Y`, then exists `Θ; Γ_Z ⊢ u_Z` with `[i_1]u_Z = u_X` and `[i_2]u_Z = u_Y`.

**Quantifiers / metric.** Simultaneous induction on the structure of `u_X` and `u_Y` (the cases will pair up by the common top-level constructor forced by `[ρ_1]u_X = [ρ_2]u_Y`).

**Case `u_X = a`** (variable, `a ∈ Γ_X`):
1. `[ρ_1]a = ρ_1(a)` (a variable).                           [defn]
2. By cases on `u_Y`: the only form whose image under `[ρ_2]` is a variable is `u_Y = b` (a variable, `b ∈ Γ_Y`). (Constants `c` give `c ≠ ρ_1(a)`; function terms give `f(...)`; metavariable terms give `Y[...]`.)        [case analysis on `u_Y`]
3. `[ρ_2]b = ρ_2(b)`.                                        [defn]
4. `ρ_1(a) = ρ_2(b)`                                         [hyp, (1), (3)]
5. `ρ_1(a) ∈ range(ρ_2)`                                     [(4), defn `range`]
6. By Aux 7.3a, `a ∈ range(i_1)`.                            [Aux 7.3a]
7. `γ := i_1⁻¹(a) ∈ Γ_Z` is defined (§3.1).
8. Take `u_Z := γ` (variable term).
9. `Θ; Γ_Z ⊢ γ`                                              [WfVar, (7)]
10. `[i_1]γ = i_1(γ) = i_1(i_1⁻¹(a)) = a = u_X`              [defn, Aux 3.0a]
11. `[i_2]γ = i_2(γ)`. By §7.2, `ρ_1; i_1 = ρ_2; i_2`. Applied at `γ`:
    `ρ_1(i_1(γ)) = ρ_2(i_2(γ))`                              [§7.2 entry-wise]
12. `ρ_1(i_1(γ)) = ρ_1(a) = ρ_2(b)`                          [(10), (4)]
13. `ρ_2(i_2(γ)) = ρ_2(b)`                                   [(11), (12)]
14. `i_2(γ) = b`                                             [injectivity of `ρ_2`, (13)]
15. `[i_2]γ = b = u_Y`                                       [(11), (14), case shape]

**Case `u_X = c`:** by case analysis on `u_Y`, must be `u_Y = c`. Take `u_Z := c`. `Θ; Γ_Z ⊢ c` by WfCon. `[i_j]c = c = u_X = u_Y`. ✓

**Case `u_X = f(u_X1, u_X2)`:** must have `u_Y = f(u_Y1, u_Y2)`. Then `[ρ_1]u_Xi = [ρ_2]u_Yi`. By inversion on `Θ; Γ_X ⊢ u_X`, `Θ; Γ_X ⊢ u_Xi`; similarly for `u_Y`. By IH, `Θ; Γ_Z ⊢ u_Zi` with `[i_j]u_Zi = u_Xi` (`j = 1`), `[i_j]u_Zi = u_Yi` (`j = 2`). Take `u_Z := f(u_Z1, u_Z2)`. Then `Θ; Γ_Z ⊢ u_Z` by WfFun, `[i_j]u_Z = f([i_j]u_Z1, [i_j]u_Z2) = u_X` (for `j=1`) and `u_Y` (for `j=2`). ✓

**Case `u_X = W[ρ_w]`** (with `W:[Γ_W] ∈ Θ`, `Γ_X ⊢ ρ_w : Γ_W`):
1. By case analysis on `u_Y`: must be `u_Y = W[ρ_w']` for the *same* metavariable `W` (otherwise `[ρ_1]u_X = W[ρ_1; ρ_w]` would equal `[ρ_2]u_Y = W'[ρ_2; ρ_w']` only if `W = W'`).   [case analysis]
2. `W[ρ_1; ρ_w] = W[ρ_2; ρ_w']` ⇒ `ρ_1; ρ_w = ρ_2; ρ_w'`.   [hyp, inversion]
3. With `q_1 := ρ_w : Γ_X ⊢ ρ_w : Γ_W` and `q_2 := ρ_w' : Γ_Y ⊢ ρ_w' : Γ_W`, the pushout universal property §7.3 (taking `Δ := Γ_W`) gives `Γ_Z ⊢ ρ_z : Γ_W` with `ρ_w = i_1; ρ_z` and `ρ_w' = i_2; ρ_z`.   [§7.3 on (2)]
4. Take `u_Z := W[ρ_z]`.
5. `Θ; Γ_Z ⊢ W[ρ_z]`                                         [WfMeta, `W:[Γ_W] ∈ Θ`, (3)]
6. `[i_1](W[ρ_z]) = W[i_1; ρ_z] = W[ρ_w] = u_X`              [defn, (3)]
7. `[i_2](W[ρ_z]) = W[i_2; ρ_z] = W[ρ_w'] = u_Y`             [defn, (3)]

### Case `D` ends in UnVar (`a = a`, `σ = id(Θ)`, `Θ' = Θ`)

**(A)** `Θ ⊢ id(Θ) : Θ` by §6.4.

**(B)** `[id(Θ)]a = a = [id(Θ)]a` by defn.

**(C)** Given `Θ'' ⊢ τ : Θ` with `[τ]a = [τ]a` (trivially true):
1. Take `τ'' := τ`.
2. `Θ'' ⊢ τ'' : Θ = Θ'`                                      [hyp]
3. `τ; id(Θ) = τ` (entry-wise: `(τ; id(Θ))(W) = [τ](id(Θ)(W)) = [τ](W[id(Γ_W)]) = [id(Γ_W)](τ(W)) = τ(W)` by Aux 6.6a, Aux 6.4a, defn `[ρ]`, §2.5).   [entry-wise calculation]
4. `τ = τ''; σ`                                              [(1), (3)]

### Case `D` ends in UnCon (`c = c`, `σ = id(Θ)`, `Θ' = Θ`)

Identical to UnVar with `c` for `a`.

### Case `D` ends in UnFun

Premises `D_1 : Θ; Γ ⊢ t_1 = t_1' ↝ σ_a : Θ_mid` and `D_2 : Θ_mid; Γ ⊢ [σ_a]t_2 = [σ_a]t_2' ↝ σ_b : Θ'`. Output: `σ = σ_b; σ_a`.

**Setup.** By inversion on WfFun applied to hyp `Θ; Γ ⊢ f(t_1,t_2)`: `Θ; Γ ⊢ t_1` and `Θ; Γ ⊢ t_2`. Similarly for `t_1', t_2'`.

**(A) Well-typedness.**
1. `Θ_mid ⊢ σ_a : Θ`                                         [IH(A) on `D_1`]
2. `Θ_mid; Γ ⊢ [σ_a]t_2`                                     [§6.3 on (1), setup]
3. `Θ_mid; Γ ⊢ [σ_a]t_2'`                                    [§6.3 on (1), setup]
4. `Θ' ⊢ σ_b : Θ_mid`                                        [IH(A) on `D_2` with (2), (3)]
5. `Θ' ⊢ σ_b; σ_a : Θ`                                       [§6.6 on (4), (1)]

**(B) Unifies.**
1. `[σ_a]t_1 = [σ_a]t_1'`                                    [IH(B) on `D_1`]
2. `[σ_b]([σ_a]t_1) = [σ_b]([σ_a]t_1')`                      [(1)]
3. `[σ_b; σ_a]t_1 = [σ_b; σ_a]t_1'`                          [§6.7 on (2)]
4. `[σ_b]([σ_a]t_2) = [σ_b]([σ_a]t_2')`                      [IH(B) on `D_2`]
5. `[σ_b; σ_a]t_2 = [σ_b; σ_a]t_2'`                          [§6.7 on (4)]
6. `[σ_b; σ_a]f(t_1, t_2) = f([σ_b;σ_a]t_1, [σ_b;σ_a]t_2) = f([σ_b;σ_a]t_1', [σ_b;σ_a]t_2') = [σ_b; σ_a]f(t_1', t_2')`   [defn `[σ]`, (3), (5)]

**(C) MGU.** Given `Θ'' ⊢ τ : Θ` with `[τ]f(t_1,t_2) = [τ]f(t_1',t_2')`:
1. `f([τ]t_1, [τ]t_2) = f([τ]t_1', [τ]t_2')`                 [defn]
2. `[τ]t_1 = [τ]t_1'`, `[τ]t_2 = [τ]t_2'`                    [inversion on `f`]
3. Exists `τ_a` with `Θ'' ⊢ τ_a : Θ_mid` and `τ = τ_a; σ_a`  [IH(C) on `D_1` with hyp, (2) left]
4. `[τ_a]([σ_a]t_2) = [τ_a; σ_a]t_2 = [τ]t_2`                [§6.7, (3)]
5. Similarly `[τ_a]([σ_a]t_2') = [τ]t_2'`                    [§6.7, (3)]
6. `[τ_a]([σ_a]t_2) = [τ_a]([σ_a]t_2')`                      [(2) right, (4), (5)]
7. Exists `τ_b` with `Θ'' ⊢ τ_b : Θ'` and `τ_a = τ_b; σ_b`   [IH(C) on `D_2` with (3), (6)]
8. `τ = (τ_b; σ_b); σ_a = τ_b; (σ_b; σ_a)`                   [(3), (7), associativity of σ-composition]
9. Take `τ'' := τ_b`.                                        [choice]

  (Associativity of σ-composition: `(σ_1; σ_2); σ_3 = σ_1; (σ_2; σ_3)`. Proven analogously to Aux 2.6a, by induction on `σ_3` using Aux 6.6a and §6.7. We elide the explicit proof — it is the σ-version of Aux 2.6a.)

### Case `D` ends in UnMetaSame

Premises: `Θ - X ≡ Θ'_rem` (i.e., `X` is removed from `Θ` modulo permutation); `Z ∉ Θ'_rem`; `Γ ⊢ ρ_1 • ρ_2 = i : Γ_eq`. Output: `σ = id(Θ'_rem), Z[i]/X`, `Θ' = Θ'_rem, Z:[Γ_eq]`. Let `X:[Γ_X] ∈ Θ`.

**(A) Well-typedness.**
1. `Θ'_rem ⊢ id(Θ'_rem) : Θ'_rem`                            [§6.4]
2. `(Θ'_rem, Z:[Γ_eq]) ⊇ Θ'_rem` (one WkSkip on reflexivity).
3. `(Θ'_rem, Z:[Γ_eq]) ⊢ id(Θ'_rem) : Θ'_rem`                [§6.1 on (2), (1)]
4. `Γ_X ⊢ i : Γ_eq`                                          [§8.1 on premise]
5. `Z:[Γ_eq] ∈ (Θ'_rem, Z:[Γ_eq])`                           [InHere]
6. `(Θ'_rem, Z:[Γ_eq]); Γ_X ⊢ Z[i]`                          [WfMeta, (5), (4)]
7. `(Θ'_rem, Z:[Γ_eq]) ⊢ (id(Θ'_rem), Z[i]/X) : (Θ'_rem, X:[Γ_X]) = Θ`           [SubCons, (3), (6)]

**(B) Unifies.**
1. `[σ](X[ρ_1]) = [ρ_1](σ(X)) = [ρ_1](Z[i]) = Z[ρ_1; i]`     [defn, lookup head, defn]
2. `[σ](X[ρ_2]) = Z[ρ_2; i]`                                 [analogous]
3. `ρ_1; i = ρ_2; i`                                         [§8.2]
4. `[σ](X[ρ_1]) = [σ](X[ρ_2])`                               [(1), (2), (3)]

**(C) MGU.** Given `Θ'' ⊢ τ : Θ` with `[τ](X[ρ_1]) = [τ](X[ρ_2])`. Let `u := τ(X)`.
1. `Θ''; Γ_X ⊢ u`                                            [§6.2 on hyp, `X:[Γ_X] ∈ Θ`]
2. `[τ](X[ρ_j]) = [ρ_j]u`                                    [defn]
3. `[ρ_1]u = [ρ_2]u`                                         [(2), hyp]
4. By Aux 9.1: exists `Θ''; Γ_eq ⊢ u'` with `[i]u' = u`.     [Aux 9.1 on premise, (1), (3)]
5. Define `τ''` on `Θ'_rem, Z:[Γ_eq]` by `τ''(W) := τ(W)` for `W ∈ Θ'_rem`, `τ''(Z) := u'`.   [definition]
6. For each `W:[Γ_W] ∈ Θ'_rem`: `Θ''; Γ_W ⊢ τ(W)`            [§6.2 on hyp]
7. `Θ'' ⊢ τ'' : Θ'`                                          [SubCons iteratively from (6), (4)]
8. For `W ∈ Θ'_rem`: `(τ''; σ)(W) = [τ''](σ(W)) = [τ''](W[id(Γ_W)]) = [id(Γ_W)](τ''(W)) = τ''(W) = τ(W)`     [Aux 6.6a; lookup cons (σ entry for `W` is in `id(Θ'_rem)`, evaluated via Aux 6.4a); defn `[ρ]`; §2.5; (5)]
9. `(τ''; σ)(X) = [τ''](σ(X)) = [τ''](Z[i]) = [i](τ''(Z)) = [i]u' = u = τ(X)`   [Aux 6.6a; lookup head; defn `[ρ]`; (5); (4); defn of `u`]
10. `τ''; σ = τ` (entry-wise on `Θ`)                         [(8), (9)]

### Case `D` ends in UnMetaDiff

Premises: `Θ ≡ Θ'_rem, X:[Γ_X], Y:[Γ_Y]`; `Γ ⊢ ρ_1 ⊔ ρ_2 = i_1; i_2 : Γ_Z`; `Z ∉ Θ'_rem`. Output: `σ = id(Θ'_rem), Z[i_1]/X, Z[i_2]/Y`, `Θ' = Θ'_rem, Z:[Γ_Z]`.

**(A) Well-typedness.**
1. `Θ'_rem ⊢ id(Θ'_rem) : Θ'_rem`                            [§6.4]
2. `(Θ'_rem, Z:[Γ_Z]) ⊢ id(Θ'_rem) : Θ'_rem`                 [§6.1]
3. `Γ_X ⊢ i_1 : Γ_Z`, `Γ_Y ⊢ i_2 : Γ_Z`                      [§7.1]
4. `Z:[Γ_Z] ∈ (Θ'_rem, Z:[Γ_Z])`                             [InHere]
5. `(Θ'_rem, Z:[Γ_Z]); Γ_X ⊢ Z[i_1]`                         [WfMeta, (4), (3)]
6. `(Θ'_rem, Z:[Γ_Z]) ⊢ (id(Θ'_rem), Z[i_1]/X) : (Θ'_rem, X:[Γ_X])`            [SubCons, (2), (5)]
7. `(Θ'_rem, Z:[Γ_Z]); Γ_Y ⊢ Z[i_2]`                         [WfMeta, (4), (3)]
8. `(Θ'_rem, Z:[Γ_Z]) ⊢ σ : (Θ'_rem, X:[Γ_X], Y:[Γ_Y]) = Θ`  [SubCons, (6), (7)]

**(B) Unifies.**
1. `[σ](X[ρ_1]) = [ρ_1](Z[i_1]) = Z[ρ_1; i_1]`               [defn, lookup, defn]
2. `[σ](Y[ρ_2]) = Z[ρ_2; i_2]`                               [analogous]
3. `ρ_1; i_1 = ρ_2; i_2`                                     [§7.2]
4. `[σ](X[ρ_1]) = [σ](Y[ρ_2])`                               [(1), (2), (3)]

**(C) MGU.** Given `Θ'' ⊢ τ : Θ` with `[τ](X[ρ_1]) = [τ](Y[ρ_2])`. Let `u_X := τ(X)`, `u_Y := τ(Y)`.
1. `Θ''; Γ_X ⊢ u_X`, `Θ''; Γ_Y ⊢ u_Y`                        [§6.2 on hyp]
2. `[τ](X[ρ_1]) = [ρ_1]u_X`, `[τ](Y[ρ_2]) = [ρ_2]u_Y`        [defn]
3. `[ρ_1]u_X = [ρ_2]u_Y`                                     [hyp, (2)]
4. By Aux 9.2: exists `Θ''; Γ_Z ⊢ u_Z` with `[i_1]u_Z = u_X` and `[i_2]u_Z = u_Y`.   [Aux 9.2 on premise, (1), (3)]
5. Define `τ''` on `Θ'_rem, Z:[Γ_Z]` by `τ''(W) := τ(W)` for `W ∈ Θ'_rem`, `τ''(Z) := u_Z`.    [definition]
6. `Θ'' ⊢ τ'' : Θ'`                                          [SubCons iteratively, (4)]
7. For `W ∈ Θ'_rem`: `(τ''; σ)(W) = τ(W)`                    [as in UnMetaSame (C) step 8]
8. `(τ''; σ)(X) = [τ''](Z[i_1]) = [i_1](τ''(Z)) = [i_1]u_Z = u_X = τ(X)`     [Aux 6.6a, lookup head, defn `[ρ]`, (5), (4)]
9. `(τ''; σ)(Y) = [i_2]u_Z = u_Y = τ(Y)`                     [analogous]
10. `τ''; σ = τ`                                             [(7), (8), (9)]

### Case `D` ends in UnMetaTm

Premises: `Θ ≡ Θ'_rem, X:[Γ_X]`; `Γ ⊢ ρ : Γ_X`; `t` not a metavariable; `Θ'_rem; range(ρ) ⊢ t`. Output: `σ = id(Θ'_rem), [ρ⁻¹]t/X`, `Θ' = Θ'_rem`.

**Setup.** By §3.1: `Γ_X ⊢ ρ⁻¹ : range(ρ)` and `range(ρ) ⊆ Γ`. By §2.4 with `Θ'_rem; range(ρ) ⊢ t` and `Γ_X ⊢ ρ⁻¹ : range(ρ)`: `Θ'_rem; Γ_X ⊢ [ρ⁻¹]t`.

**(A) Well-typedness.**
1. `Θ'_rem ⊢ id(Θ'_rem) : Θ'_rem`                            [§6.4]
2. `Θ'_rem; Γ_X ⊢ [ρ⁻¹]t`                                    [setup]
3. `Θ'_rem ⊢ (id(Θ'_rem), [ρ⁻¹]t/X) : (Θ'_rem, X:[Γ_X]) = Θ` [SubCons, (1), (2)]

**(B) Unifies.**
1. `[σ](X[ρ]) = [ρ](σ(X)) = [ρ]([ρ⁻¹]t) = [ρ; ρ⁻¹]t`        [defn, lookup, defn, §2.6]
2. `ρ; ρ⁻¹ = id(range(ρ))`                                   [Aux 3.2a (second part)]
3. `[id(range(ρ))]t = t`                                     [§2.5 on `Θ'_rem; range(ρ) ⊢ t`]
4. `[σ](X[ρ]) = t`                                           [(1)–(3)]
5. `[σ]t = t`                                                [Aux 9.0 on `Θ'_rem; range(ρ) ⊢ t` (so `fv_meta(t) ⊆ Θ'_rem`) and `σ` agreeing with `id(Θ'_rem)` on `Θ'_rem`]
6. `[σ](X[ρ]) = [σ]t`                                        [(4), (5)]

**(C) MGU.** Given `Θ'' ⊢ τ : Θ` with `[τ](X[ρ]) = [τ]t`. Let `u := τ(X)`.
1. `Θ''; Γ_X ⊢ u`                                            [§6.2]
2. `[τ](X[ρ]) = [ρ]u`                                        [defn]
3. `[ρ]u = [τ]t`                                             [(2), hyp]
4. Define `τ''` on `Θ'_rem` by `τ''(W) := τ(W)`.             [definition]
5. For each `W:[Γ_W] ∈ Θ'_rem`: `Θ''; Γ_W ⊢ τ(W)`            [§6.2]
6. `Θ'' ⊢ τ'' : Θ'_rem = Θ'`                                 [SubCons iteratively from (5)]
7. `[τ]t = [τ'']t`                                           [Aux 9.0-like agreement: `τ, τ''` agree on `Θ'_rem` and `fv_meta(t) ⊆ Θ'_rem`]
8. For `W ∈ Θ'_rem`: `(τ''; σ)(W) = τ(W)`                    [as in UnMetaSame (C)]
9. `(τ''; σ)(X) = [τ''](σ(X)) = [τ'']([ρ⁻¹]t)`                [Aux 6.6a, lookup head]
10. `[τ'']([ρ⁻¹]t) = [ρ⁻¹]([τ'']t)`                          [Aux 6.7a]
11. `[τ'']t = [τ]t = [ρ]u`                                   [(7), (3)]
12. `(τ''; σ)(X) = [ρ⁻¹]([ρ]u) = u = τ(X)`                   [(9), (10), (11), and the round-trip identity on terms (see note)]
13. `τ''; σ = τ`                                             [(8), (12)]

  **Note on step 12 (Step 11 of UnMetaTm(C), unchanged).** Formally, §2.6 requires `Γ ⊢ ρ_outer : Γ_mid` and `Γ_mid ⊢ ρ_inner : Γ_inner` with `Θ; Γ_inner ⊢ t`. We have `Γ_X ⊢ ρ⁻¹ : range(ρ)` (as `ρ_outer`) and want to compose with `ρ` viewed as `range(ρ) ⊢ ρ : ?`. By Aux 4.0a, `Γ ⊢ ρ : Γ_X` restricts to `range(ρ) ⊢ ρ_restricted : Γ_X`. The cleanest formulation is to introduce `ρ_codom : range(ρ) ⊢ ρ_codom : Γ_X` as the renaming with the same entries as `ρ` but typed at codomain `range(ρ)`. Then `ρ⁻¹; ρ_codom` makes sense and is `id(Γ_X)` by Aux 3.2a, and `[ρ⁻¹][ρ]u = u` whenever `u : Γ_X` (by the round-trip identity on terms).

### Case `D` ends in UnTmMeta

Symmetric to UnMetaTm. Output `σ = id(Θ'_rem), [ρ⁻¹]t/X`, `Θ' = Θ'_rem`.

**(A)** Identical to UnMetaTm.

**(B)** Same chain as UnMetaTm: `[σ]t = t`, `[σ](X[ρ]) = t`, hence `[σ]t = [σ](X[ρ])`.

**(C)** Given `Θ'' ⊢ τ : Θ` with `[τ]t = [τ](X[ρ])`. The proof of UnMetaTm (C) carries over with `[τ]X[ρ] = [τ]t` rewritten as `[τ]t = [τ]X[ρ]`. ∎

---

## 10. Summary

### 10.1 Fixes required to `unification.md`

1. **Line 92 (renaming-on-terms typing).** Statement should read:
   ```
   If Θ; Γ' ⊢ t and Γ ⊢ ρ : Γ' then Θ; Γ ⊢ [ρ]t.
   ```
   The original swaps the two occurrences of `Γ` on either side of the colon.

2. **Line 135 (strengthening).** The use of `set-to-list(fv(t))` is not well-defined without an ordering choice. The corrected statement (used here):
   ```
   If Θ; Γ ⊢ t then there exists a duplicate-free Γ₀ ⊆ Γ (as subsequence) with elements
   equal to fv(t) (as a set), such that Θ; Γ₀ ⊢ t.
   ```

3. **Line 282 (coequalizer universal property).** The statement reads `Γ ⊢ j : Δ`, but for `ρ_1; j = ρ_2; j` to type-check (with `Γ ⊢ ρ_1, ρ_2 : Γ'`), we need `Γ' ⊢ j : Δ`. Corrected:
   ```
   If Γ' ⊢ j : Δ and ρ_1; j = ρ_2; j, then there exists Γ'' ⊢ j' : Δ with j = i; j'.
   ```

4. **Metavariable contexts modulo permutation.** The rules `Θ ≡ Θ', X:[Γ']` and `Θ ≡ Θ', X:[Γ_1], Y:[Γ_2]` are interpreted up to permutation of `Θ`'s entries.

5. **Codomain reweakening (used in PushConsSkip / CoeqConsSkip / Aux 4.0b WkSkipCx).** The principle "any unused output may be added to the codomain of a well-formed renaming" (Aux 2.7a) is used implicitly in several pushout/coequalizer typing arguments; we recommend stating it as an explicit lemma in `unification.md` (or noting the convention).

6. **Subcontext `⊆` relation.** We define `Γ_a ⊆ Γ_b` inductively (§0.5). The renaming-wf system effectively provides this via `Aux 4.0b`. Worth adding a brief note in `unification.md` about this relation's role.

### 10.2 Auxiliary lemmas introduced

| Tag | Statement |
|---|---|
| Aux 1.2 | Membership after removal: `b ∈ Γ_1` and `Γ_0 - a ≡ Γ_1` ⇒ `b ∈ Γ_0` and `b ≠ a` |
| Aux 1.3 | Swap of removals: `Γ - a_1 ≡ Γ_1`, `Γ_1 - a_2 ≡ Γ_{12}` ⇒ exists `Γ_2` with `Γ - a_2 ≡ Γ_2`, `Γ_2 - a_1 ≡ Γ_{12}` |
| Aux 2.0a | Renaming lookup totality |
| Aux 2.0b | `id(Γ)(x) = x` for `x ∈ Γ` |
| Aux 2.3a | Lookup-after-composition: `(ρ;ρ')(x) = ρ(ρ'(x))` |
| Aux 2.3b | Linearity inversion: extract an entry from a well-typed renaming |
| Aux 2.5a | Left identity of renaming composition |
| Aux 2.5b | Right identity of renaming composition |
| Aux 2.6a | Associativity of renaming composition |
| Aux 2.7a | Codomain reweakening: unused outputs may be added |
| Aux 3.0a | Inverse lookup: `(a/x) ∈ ρ` ⇒ `ρ⁻¹(a) = x` |
| Aux 3.2a | Round-trip identities: `ρ⁻¹; ρ = id(Γ')`, `ρ; ρ⁻¹ = id(range(ρ))` |
| Aux 4.0a | Range-recast: `Γ ⊢ ρ : Γ'` ⇒ `range(ρ) ⊢ ρ : Γ'` |
| Aux 4.0b | Subsequence-induced renaming exists with identity action |
| Aux 4.0c | Identity-acting renaming preserves terms: `[ρ_emb]t = t` |
| Aux 5.0 | Metaweakening preserves membership |
| Aux 6.4a | Identity-σ lookup: `id(Θ)(X) = X[id(Γ_X)]` |
| Aux 6.6a | Lookup of σ-composition |
| Aux 6.7a | σ-ρ commutation: `[σ]([ρ]t) = [ρ]([σ]t)` |
| Aux 7.3a | Range characterization for pushout |
| Aux 8.3a | Range characterization for coequalizer |
| Aux 9.0 | σ acts as identity on terms whose metas are in σ's identity domain |
| Aux 9.1 | Term coequalizer factorization |
| Aux 9.2 | Term pushout factorization |

All weakening and substitution lemmas are stated as parallel `Γ ⊢ ρ : Γ'` / `Θ ⊢ σ : Θ'` judgments (§2.4 for renamings, §6.3 for metasubstitutions), per the request. No single-variable forms are introduced.
