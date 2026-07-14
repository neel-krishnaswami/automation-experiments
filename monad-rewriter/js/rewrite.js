// The 7 equations as rewrite rules: left-to-right reductions, deterministic
// right-to-left expansions, and un-substitution (the beta rules right-to-left,
// with user-chosen occurrences).
(() => {
  const MR = (globalThis.MR = globalThis.MR || {});
  const A = MR.ast;
  const T = MR.typecheck;

  // ---- Left-to-right reductions -------------------------------------------
  // do_i x <- return_i e; e'  -->  [e/x]e'
  const beta = (i) => (node) => {
    if (node.tag !== 'do' || node.monad !== i) return null;
    if (node.rhs.tag !== 'return' || node.rhs.monad !== i) return null;
    return A.subst(node.rhs.arg, node.var, node.body);
  };

  // do_i x <- e; return_i x  -->  e
  const eta = (i) => (node) => {
    if (node.tag !== 'do' || node.monad !== i) return null;
    const b = node.body;
    if (b.tag !== 'return' || b.monad !== i) return null;
    if (b.arg.tag !== 'var' || b.arg.name !== node.var) return null;
    return node.rhs;
  };

  // do_i x <- (do_i y <- e1; e2); e3  -->  do_i y <- e1; do_i x <- e2; e3
  // In the result y scopes over e3 as well, so rename y if e3 mentions it
  // (unless y = x, in which case the inner x shadows it and no capture occurs).
  const assoc = (i) => (node) => {
    if (node.tag !== 'do' || node.monad !== i) return null;
    if (node.rhs.tag !== 'do' || node.rhs.monad !== i) return null;
    const x = node.var, e3 = node.body;
    const inner = node.rhs;
    let y = inner.var, e2 = inner.body;
    if (y !== x && A.freeVars(e3).has(y)) {
      const y2 = A.fresh(y, new Set([...A.freeVars(e3), ...A.freeVars(e2), x]));
      e2 = A.subst(A.mkVar(y2), y, e2);
      y = y2;
    }
    return A.mkDo(i, y, inner.rhs, A.mkDo(i, x, e2, e3));
  };

  // do2 x <- lift (return1 e); e'  -->  [e/x]e'
  const liftBeta = (node) => {
    if (node.tag !== 'do' || node.monad !== 2) return null;
    if (node.rhs.tag !== 'lift') return null;
    const r = node.rhs.arg;
    if (r.tag !== 'return' || r.monad !== 1) return null;
    return A.subst(r.arg, node.var, node.body);
  };

  const REDUCTIONS = [
    { name: 'do1-beta', match: beta(1) },
    { name: 'do1-eta', match: eta(1) },
    { name: 'do1-assoc', match: assoc(1) },
    { name: 'do2-beta', match: beta(2) },
    { name: 'do2-eta', match: eta(2) },
    { name: 'do2-assoc', match: assoc(2) },
    { name: 'lift-beta', match: liftBeta },
  ];

  // ---- Deterministic right-to-left expansions -----------------------------
  // e : M_i A  -->  do_i x <- e; return_i x   (x fresh)
  const etaExpand = (i) => (node, type) => {
    if (!type || type.tag !== 'tmonad' || type.monad !== i) return null;
    const x = A.fresh('x', A.freeVars(node));
    return A.mkDo(i, x, node, A.mkReturn(i, A.mkVar(x)));
  };

  // do_i y <- e1; do_i x <- e2; e3  -->  do_i x <- (do_i y <- e1; e2); e3
  // Only when y does not occur free in e3 (there y would escape its new,
  // smaller scope); occurrences shadowed by x = y do not count.
  const unassoc = (i) => (node) => {
    if (node.tag !== 'do' || node.monad !== i) return null;
    const b = node.body;
    if (b.tag !== 'do' || b.monad !== i) return null;
    const y = node.var, x = b.var;
    if (y !== x && A.freeVars(b.body).has(y)) return null;
    return A.mkDo(i, x, A.mkDo(i, y, node.rhs, b.rhs), b.body);
  };

  const EXPANSIONS = [
    { name: 'do1-eta (expand)', match: etaExpand(1) },
    { name: 'do2-eta (expand)', match: etaExpand(2) },
    { name: 'do1-assoc (reverse)', match: unassoc(1) },
    { name: 'do2-assoc (reverse)', match: unassoc(2) },
  ];

  // Rewrites applicable to the subterm of `root` at `path`.
  // `types` is the per-node type map of the (well-typed) root term.
  // Returns { entries: [{name, dir, result}], unsubAvailable }.
  function applicableRewrites(root, path, types) {
    const node = A.getAt(root, path);
    const type = types.get(node);
    const entries = [];
    for (const r of REDUCTIONS) {
      const result = r.match(node);
      if (result) entries.push({ name: r.name, dir: 'ltr', result });
    }
    for (const r of EXPANSIONS) {
      const result = r.match(node, type);
      if (result) entries.push({ name: r.name, dir: 'rtl', result });
    }
    const unsubAvailable = !!(type && type.tag === 'tmonad');
    return { entries, unsubAvailable };
  }

  // ---- Un-substitution ----------------------------------------------------

  // Occurrences of `pattern` in `sel` that can be abstracted: alpha-equal to
  // the pattern and not under a binder that captures one of its free
  // variables. Returns paths relative to `sel`.
  function findOccurrences(sel, pattern) {
    const fvP = A.freeVars(pattern);
    const out = [];
    (function walk(e, path, bound) {
      if (A.alphaEq(e, pattern)) {
        let captured = false;
        for (const v of fvP) if (bound.has(v)) { captured = true; break; }
        if (!captured) { out.push(path); return; } // occurrences cannot nest
      }
      for (const k of A.childKeys(e)) {
        const b = (k === 'body' && (e.tag === 'do' || e.tag === 'let'))
          ? new Set(bound).add(e.var) : bound;
        walk(e[k], path.concat(k), b);
      }
    })(sel, [], new Set());
    return out;
  }

  // Candidate right-to-left beta rewrites of the subterm at `targetPath`
  // (whose value is e'), abstracting the chosen occurrences of `pattern` (e)
  // as a fresh variable x:
  //   do1 x <- return1 e; e''    do2 x <- return2 e; e''    do2 x <- lift (return1 e); e''
  // Each candidate is typechecked in the ambient context; only well-typed
  // ones are offered.
  function unsubCandidates(root, targetPath, types, sigma, pattern, chosenRelPaths) {
    const sel = A.getAt(root, targetPath);
    const x = A.fresh('x', new Set([...A.freeVars(sel), ...A.freeVars(pattern)]));
    let holed = sel;
    for (const p of chosenRelPaths) holed = A.replaceAt(holed, p, A.mkVar(x));
    const gamma = T.gammaAt(root, targetPath, types);
    const candidates = [
      { name: 'do1-beta (reverse)', result: A.mkDo(1, x, A.mkReturn(1, pattern), holed) },
      { name: 'do2-beta (reverse)', result: A.mkDo(2, x, A.mkReturn(2, pattern), holed) },
      { name: 'lift-beta (reverse)', result: A.mkDo(2, x, A.mkLift(A.mkReturn(1, pattern)), holed) },
    ];
    return candidates.filter((c) => T.typeOfIn(sigma, gamma, c.result) !== null);
  }

  MR.rewrite = { applicableRewrites, findOccurrences, unsubCandidates, REDUCTIONS, EXPANSIONS };
})();
