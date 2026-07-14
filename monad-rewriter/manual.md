# Monadic Rewriter — User Manual

The Monadic Rewriter is a single-page web app for building equational proofs
about terms in a small calculus with two monads (`M1` and `M2`, connected by
`lift : M1 A → M2 A`). You write a signature and a term, then transform the
term step by step using the monad laws; the resulting chain of terms is an
equational proof, which can be exported to a text file.

## Getting started

Open `index.html` in a browser. No server or build step is required.
(To run the test suite, open `test.html` the same way.)

The window has three panels:

| Panel | Purpose |
|---|---|
| **Signature** | Declare the constants your terms may use |
| **Term** | Write the term the proof starts from |
| **Proof** | Apply rewrites and build the proof |

## The Signature panel

Enter one constant declaration per line, in the form `c : A`:

    C : M1 P
    D : M1 Q
    E : M2 (M1 P)

Constant names start with an upper-case letter; types are propositional
letters (also upper-case), optionally under `M1` or `M2`, with parentheses
for nesting. Blank lines are ignored.

Each line is checked independently: a malformed or duplicate line is
highlighted in red (hover it for the message) without affecting the other
declarations.

## The Term panel

Write a single expression, e.g.

    do1 x <- (do1 y <- C; D); return1 x

The syntax (see `design.md` for the full grammar):

- `x` — variables (lower-case initial letter)
- `C` — constants (upper-case initial letter)
- `return1 e`, `return2 e` — monadic unit
- `do1 x <- e; e'`, `do2 x <- e; e'` — monadic bind
- `lift e` — coerce `M1 A` into `M2 A`
- `let x = e; e'` — local definition
- A `do`/`let`/`lift` expression in an argument or right-hand-side position
  must be parenthesized.

The term is parsed and typechecked as you type. Only the *smallest* ill-typed
subterms are highlighted in red — enclosing expressions that fail merely
because a subexpression inside them is wrong are not additionally flagged.
Hover a red mark to see the error message in a bubble. When the term is
well-typed, its type is shown below the editor and the term appears in the
Proof panel.

## The Proof panel

The proof is a list of terms; the first entry is your term from the Term
panel, and each later entry is obtained from the previous one by a single
equational rewrite, labelled with the rule that justifies it:

    do1 x <- (do1 y <- C; D);
    return1 x
      == { do1-eta }
    do1 y <- C;
    D

Only the **bottom** term is interactive.

### Selecting a subterm

- **Click** a subterm of the bottom term to select it (the innermost subterm
  under the cursor is chosen).
- **Click the selection again**, or press **w** / **↑**, to widen the
  selection to the enclosing expression.
- **Esc** clears the selection.

### Applying a rewrite

When a subterm is selected, the menu at the bottom lists every applicable
rewrite, in this order:

1. **Reductions (→)** — the seven equations read left to right:
   `do1-beta`, `do1-eta`, `do1-assoc`, `do2-beta`, `do2-eta`, `do2-assoc`,
   and `lift-beta` (`do2 x <- lift (return1 e); e'  ==  [e/x]e'`).
2. **Expansions (←)** — the deterministic right-to-left rules:
   eta-expansion (`e` of monadic type becomes `do_i x <- e; return_i x`) and
   reverse associativity (only offered when it introduces no variable
   capture).
3. **un-substitute…** — the beta equations read right to left (see below).

Press the **number key** shown next to an entry (or click it) to apply that
rewrite. The rewritten term is appended to the proof and becomes the new
bottom term. All rewrites are capture-avoiding; bound variables are renamed
automatically when necessary.

### Un-substitution

The beta laws read right to left turn a term `[e/x]e'` back into
`do1 x <- return1 e; e'` (and similarly for `do2` and `lift`). Since there
are many ways to un-substitute, you choose the occurrences yourself:

1. Select a subterm and press **u** (or click *un-substitute…*).
2. Click the subterm `e` you want to abstract. All occurrences of `e` that
   can legally be abstracted light up in green (occurrences that mention a
   variable bound inside the selection are excluded).
3. Click occurrences to toggle which ones will be replaced by the new
   variable; the chosen ones are shown in solid green.
4. Press **Enter**. The menu lists whichever of the three expansions
   (`do1-beta`, `do2-beta`, `lift-beta`, each in reverse) produce a
   well-typed term; pick one with a number key.

**Esc** backs out of the flow at any stage.

### Buttons

- **Undo** — remove the last proof step.
- **Restart** — discard the proof and reload the current term from the Term
  panel. (While a proof has at least one step, edits to the Signature and
  Term panels do *not* affect it; use Restart to pick them up.)
- **Export** — download the proof as `proof.txt`, containing the signature
  and the sequence of terms interleaved with their justifications.

### Keyboard reference

| Key | Effect |
|---|---|
| `1`–`9` | apply the numbered menu entry |
| `u` | start un-substitution (with a subterm selected) |
| `w` / `↑` | widen the selection |
| `Enter` | (during un-substitution) choose the expansion rule |
| `Esc` | clear the selection / cancel un-substitution |

Keys are ignored while you are typing in the Signature or Term editors.
