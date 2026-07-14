# Monadic Rewriter Web App — Implementation Plan

## Context

`/home/nk480/notes/monad-rewriter/design.md` specifies a small single-page web app for generating equational proofs by rewriting terms in a calculus with two monads (M1, M2, with `lift : M1 A → M2 A`). The directory is greenfield: only the design doc exists. The app has three panels — signature editor, live-typechecked term editor, and an interactive proof panel where the user selects subterms and applies the 7 monad equations as rewrites, then exports the proof.

Decisions confirmed with the user:
- **General bind rule**: `Σ;Γ ⊢ e : M_i A` and `Σ;Γ, x:A ⊢ e' : M_i B` gives `do_i x <- e; e' : M_i B` — and design.md's typing rules should be **fixed** accordingly.
- **Rewrite menu ordering**: left-to-right reductions first, then deterministic right-to-left expansions, then a final "un-substitute" option that enters an occurrence-selection mode (user picks a pattern subterm and toggles which occurrences to abstract, then chooses among the beta rules applied right-to-left).
- **Nested monadic types allowed**: `return1 e : M1 A` for arbitrary `A` (the grammar's `b ::= p | (A)` permits e.g. `M1 (M2 P)`).
- **Self-contained, no build step**: vanilla JS, open `index.html` directly from the filesystem.

## Key technical decisions

- **Classic `<script>` tags, not ES modules** — ES modules are CORS-blocked under `file://`. Each file is an IIFE attaching exports to a global `MR` namespace; `index.html` loads scripts in dependency order.
- **Identifier regexes relaxed to `[A-Z][a-zA-Z_0-9]*` / `[a-z][a-zA-Z_0-9]*`** (the doc's `+` requires length ≥ 2, contradicting its own examples `x`, `y`, `p`). Reserved words: `do1 do2 let lift return1 return2 M1 M2`.
- **Panel 2 editing mechanism**: textarea + mirrored `<pre>` backdrop (transparent text, visible caret) for error highlights; hover bubbles by hit-testing mouse position against the marks' client rects. Simpler and more robust than contentEditable.
- **Panel 3 rendering**: pretty printer emits nested `<span data-path=…>` DOM directly — the DOM *is* the AST↔text map; innermost-span click selection with a widen-to-parent key.
- **Hand-coded shape matchers** for the 7 equations rather than a generic unifier.

## File layout

```
monad-rewriter/
  index.html      -- 3-panel shell, script tags in dependency order
  style.css
  js/ast.js       -- AST constructors, fv, fresh, capture-avoiding subst,
                     structural equality, getAt/replaceAt/bindersOnPath (path ops)
  js/lexer.js     -- tokenizer with char offsets; never throws (error tokens)
  js/parser.js    -- recursive descent: types, signature lines, expressions
  js/typecheck.js -- type synthesis, per-node type map, smallest-wrong-subterm errors
  js/pretty.js    -- layout-spec printer, string sink + DOM-span sink
  js/rewrite.js   -- 7 reductions, deterministic expansions, un-substitution, apply-at-path
  js/ui-editor.js -- panel 2: textarea+backdrop, error marks, hover bubbles
  js/ui-proof.js  -- panel 3: proof list, subterm selection, rewrite menu,
                     un-substitution mode state machine, export
  js/main.js      -- app state + wiring
  test.html, js/tests.js -- in-browser unit-test harness (no tooling)
```

## Core data structures

- Types: `{tag:'tbase', name}` | `{tag:'tmonad', monad:1|2, arg}`.
- Expressions (one AST type, no paren nodes; spans widened to include parens):
  `var`, `const`, `return{monad,arg}`, `lift{arg}`, `do{monad, var, rhs, body}`, `let{var, rhs, body}` — each with `span:{start,end}` into the source. Immutable; subterms addressed by **paths** (arrays of child keys) with functional `replaceAt`.
- Signature: `Map<name, Type>` + per-line errors (each signature line parsed independently — a bad line doesn't break the rest).
- Typecheck result: `types: Map<node, Type|null>` (null = poisoned) + `errors: [{span, msg}]`.
- App state: `{sigma, termAst, termErrors, proof: [{ast, rule}], frozen, selection, mode: 'normal'|'menu'|'unsub-pick'|'unsub-toggle', unsub}`.

## Key algorithms

**Typechecker (smallest wrong subterm)**: pure synthesis; a node may record an error only if none of its children are poisoned; any error or poisoned child returns null upward. Type-mismatch errors anchor on the offending *child*'s span (matching the doc's ERROR1/ERROR2 example). After a bad `do` rhs, the body is still checked with the bound variable given a distinguished `unknown` type that satisfies every constraint, so independent sibling errors all surface without cascades.

**Rewrite menu** for a selected subterm at `path` (menu order per user):
1. Reductions: do1/do2-beta, do1/do2-eta, do1/do2-assoc (with capture guard: freshen `y` against `fv(e3)`), lift-beta (`do2 x <- lift (return1 e); e' → [e/x]e'`). Note design.md's eq. 6 has a typo (`e2` twice); implement the corrected `do2 y <- e1; do2 x <- e2; e3`.
2. Deterministic expansions: eta-expansion (offered when the node's type is `M_i _` — needs the per-node type map), un-associativity (side condition `y ∉ fv(e3)`).
3. **Un-substitute** (`u`): mode machine — (a) user clicks a subterm of the selection as pattern `e`; (b) all valid occurrences highlighted (structurally equal to `e` and not capturing: `fv(e) ∩ bindersOnPath = ∅`), user toggles which to abstract; (c) on Enter, build `e''` with chosen occurrences replaced by a fresh `x`, construct the candidates `do1 x <- return1 e; e''`, `do2 x <- return2 e; e''`, `do2 x <- lift (return1 e); e''`, typecheck each in the ambient Γ (`bindersOnPath` of the selection) and offer only the ones that pass.

Applying a rewrite: `replaceAt(bottomTerm, path, result)`, re-typecheck (assert — sanity check that rewrites preserve typing), append to proof with the rule name recorded. Panel 3 tracks panel 2 only while the proof has one entry; first rewrite freezes it (add a Restart button).

**Pretty printer** (per the doc's layout spec): recursive `print(e, col, sink)`; newline after each `;`, body printed at the column of its `do`/`let` keyword; a `do/let` in rhs position is parenthesized and its own body aligns under the inner `do`. Parenthesize exactly when a complex expression occupies a simple-expression slot. Two sinks over one traversal: string (export/tests) and DOM (panel 3 spans). Property test: `parse(print(e)) ≡ e`, plus the doc's worked example byte-for-byte.

**Export**: plain-text Blob download (`<a download="proof.txt">`): signature, then the term sequence interleaved with `== { rule-name }` justifications from `proof[i].rule`.

## design.md updates (part of the work, per user request)

Fix the errors in the doc:
1. do1/do2 rules → general bind (result `M_i B`).
2. let rule → `Σ;Γ ⊢ e : A`, `Σ;Γ, x:A ⊢ e' : B` ⟹ `let x = e; e' : B` (also fix `e1/e2` vs `e/e'` mismatch).
3. Equation 6 RHS typo → `do2 y <- e1; do2 x <- e2; e3`.
4. Add the missing variable rule `x:A ∈ Γ ⟹ Σ;Γ ⊢ x : A`.
5. Identifier regexes `+` → `*`; note reserved words.
6. Formatting example typos (`do y <-` → `do1 y <-`; missing `;` after `e2)`).

Also add a **very brief** paragraph (a few lines, in the UI section) describing the rewrite choices offered for a selected subterm: left-to-right reductions listed first, then the deterministic right-to-left expansions (eta-expansion, un-associativity), then a final un-substitute option where the user selects which occurrences of a subterm to abstract before choosing among the beta rules in reverse.

## Build order & verification

Each stage verified via `test.html` (tiny assert harness, open in browser) or a manual check:

1. `ast.js` + `lexer.js` + `parser.js` + tests — parse all doc examples, span offsets, subst capture cases, `fresh`.
2. `pretty.js` (string sink) — round-trip property; doc's layout example exactly.
3. `typecheck.js` — positive examples, each error kind, the ERROR1/ERROR2 double-error case, poisoning.
4. `rewrite.js` — each of the 7 reductions, assoc capture guard, eta freshness, unassoc side condition, un-substitution candidates; every output re-typechecks.
5. `index.html` + `style.css` + panels 1–2 — manual: per-line signature errors, marks track edits, hover bubbles, backdrop/textarea alignment, scroll sync.
6. Panel 3 — manual: the doc's worked example (`do1 x <- (do1 y <- e1; e2); return1 x`) must offer exactly its two listed rewrites in order; selection widening; freeze + Restart.
7. Un-substitution mode — manual: occurrence highlighting, capture-excluded occurrences suppressed, Esc at each stage.
8. Export — file content and justifications.
9. design.md edits (independent; can be done first).
10. Final end-to-end pass: signature → ill-typed term → fix → 4-step proof including one expansion and one un-substitution → export.

Watch-items: textarea/backdrop metric mismatch (share CSS class, `pre-wrap` both layers); freshness at a rewrite site must consider all binders in scope (`bindersOnPath`), not just local `fv`.
