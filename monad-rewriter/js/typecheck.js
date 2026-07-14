// Type synthesis with "smallest wrong subterm" error reporting.
//
// infer returns the node's type, or null if the node is *poisoned* (an error
// was already reported somewhere inside it). A node may record an error only
// if none of its children are poisoned; this makes exactly the smallest wrong
// subterms carry errors. After a mismatch, bound variables get the
// distinguished UNKNOWN type, which satisfies every constraint, so independent
// errors in sibling positions still surface without cascades.
(() => {
  const MR = (globalThis.MR = globalThis.MR || {});
  const A = MR.ast;

  const UNKNOWN = { tag: 'tunknown' };
  const isUnknown = (t) => t.tag === 'tunknown';

  function infer(sigma, gamma, e, out) {
    const result = inferNode(sigma, gamma, e, out);
    out.types.set(e, result);
    return result;
  }

  function inferNode(sigma, gamma, e, out) {
    const err = (span, msg) => out.errors.push({ span, msg });
    switch (e.tag) {
      case 'var': {
        if (gamma.has(e.name)) return gamma.get(e.name);
        err(e.span, `Unbound variable '${e.name}'`);
        return null;
      }
      case 'const': {
        if (sigma.has(e.name)) return sigma.get(e.name);
        err(e.span, `Undeclared constant '${e.name}'`);
        return null;
      }
      case 'return': {
        const t = infer(sigma, gamma, e.arg, out);
        if (t === null) return null;
        return A.tmonad(e.monad, t);
      }
      case 'lift': {
        const t = infer(sigma, gamma, e.arg, out);
        if (t === null) return null;
        if (isUnknown(t)) return A.tmonad(2, UNKNOWN);
        if (t.tag === 'tmonad' && t.monad === 1) return A.tmonad(2, t.arg);
        err(e.arg.span,
          `'lift' expects an argument of type M1 _, but this has type ${A.typeToString(t)}`);
        return null;
      }
      case 'do': {
        const i = e.monad;
        const tr = infer(sigma, gamma, e.rhs, out);
        let bad = tr === null;
        let xty = UNKNOWN;
        if (tr !== null) {
          if (isUnknown(tr)) {
            xty = UNKNOWN;
          } else if (tr.tag === 'tmonad' && tr.monad === i) {
            xty = tr.arg;
          } else {
            err(e.rhs.span,
              `'do${i}' binds from a computation of type M${i} _, but this has type ${A.typeToString(tr)}`);
            bad = true;
          }
        }
        const gamma2 = new Map(gamma);
        gamma2.set(e.var, xty);
        const tb = infer(sigma, gamma2, e.body, out);
        if (tb === null) return null;
        if (bad) return null;
        if (isUnknown(tb)) return UNKNOWN;
        if (tb.tag === 'tmonad' && tb.monad === i) return tb;
        err(e.body.span,
          `The body of 'do${i}' must have type M${i} _, but this has type ${A.typeToString(tb)}`);
        return null;
      }
      case 'let': {
        const tr = infer(sigma, gamma, e.rhs, out);
        const gamma2 = new Map(gamma);
        gamma2.set(e.var, tr === null ? UNKNOWN : tr);
        const tb = infer(sigma, gamma2, e.body, out);
        if (tr === null || tb === null) return null;
        return tb;
      }
    }
  }

  // Typecheck a closed term against signature sigma.
  // Returns { type, types: Map<node, Type|null>, errors: [{span, msg}], ok }.
  function checkTerm(sigma, ast, gamma) {
    const out = { types: new Map(), errors: [] };
    const type = infer(sigma, gamma || new Map(), ast, out);
    return { type, types: out.types, errors: out.errors, ok: out.errors.length === 0 && type !== null };
  }

  // Type of expression e in an explicit context; null if ill-typed.
  function typeOfIn(sigma, gamma, e) {
    const out = { types: new Map(), errors: [] };
    const t = infer(sigma, gamma, e, out);
    return out.errors.length === 0 ? t : null;
  }

  // Context at the subterm addressed by `path` inside a well-typed root term,
  // read off the root's per-node type map.
  function gammaAt(root, path, types) {
    const gamma = new Map();
    let e = root;
    for (const k of path) {
      if ((e.tag === 'do' || e.tag === 'let') && k === 'body') {
        const rt = types.get(e.rhs);
        gamma.set(e.var, e.tag === 'do' ? rt.arg : rt);
      }
      e = e[k];
    }
    return gamma;
  }

  MR.typecheck = { checkTerm, typeOfIn, gammaAt, UNKNOWN };
})();
