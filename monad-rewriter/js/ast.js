// AST for the two-monad calculus: constructors, free variables, fresh names,
// capture-avoiding substitution, alpha-equality, and path-based subterm access.
//
// Expression nodes (immutable by convention):
//   { tag: 'var',    name, span }
//   { tag: 'const',  name, span }
//   { tag: 'return', monad: 1|2, arg, span }
//   { tag: 'lift',   arg, span }
//   { tag: 'do',     monad: 1|2, var, varSpan, rhs, body, span }
//   { tag: 'let',    var, varSpan, rhs, body, span }
//
// Type nodes:
//   { tag: 'tbase', name }
//   { tag: 'tmonad', monad: 1|2, arg }
//
// Subterms are addressed by paths: arrays of child keys ('arg', 'rhs', 'body').
(() => {
  const MR = (globalThis.MR = globalThis.MR || {});

  const mkVar = (name, span) => ({ tag: 'var', name, span });
  const mkConst = (name, span) => ({ tag: 'const', name, span });
  const mkReturn = (monad, arg, span) => ({ tag: 'return', monad, arg, span });
  const mkLift = (arg, span) => ({ tag: 'lift', arg, span });
  const mkDo = (monad, v, rhs, body, span, varSpan) =>
    ({ tag: 'do', monad, var: v, varSpan, rhs, body, span });
  const mkLet = (v, rhs, body, span, varSpan) =>
    ({ tag: 'let', var: v, varSpan, rhs, body, span });

  const tbase = (name) => ({ tag: 'tbase', name });
  const tmonad = (monad, arg) => ({ tag: 'tmonad', monad, arg });

  // Child keys of a node, in source order.
  function childKeys(e) {
    switch (e.tag) {
      case 'var': case 'const': return [];
      case 'return': case 'lift': return ['arg'];
      case 'do': case 'let': return ['rhs', 'body'];
      default: throw new Error('bad tag ' + e.tag);
    }
  }

  function freeVars(e, acc, bound) {
    acc = acc || new Set();
    bound = bound || new Set();
    switch (e.tag) {
      case 'var':
        if (!bound.has(e.name)) acc.add(e.name);
        break;
      case 'const':
        break;
      case 'return': case 'lift':
        freeVars(e.arg, acc, bound);
        break;
      case 'do': case 'let': {
        freeVars(e.rhs, acc, bound);
        const shadowed = bound.has(e.var);
        bound.add(e.var);
        freeVars(e.body, acc, bound);
        if (!shadowed) bound.delete(e.var);
        break;
      }
    }
    return acc;
  }

  // fresh(y, S): y itself if y ∉ S, else y with the least numeric suffix not in S.
  function fresh(y, avoid) {
    if (!avoid.has(y)) return y;
    for (let i = 1; ; i++) {
      const cand = y + i;
      if (!avoid.has(cand)) return cand;
    }
  }

  // Capture-avoiding substitution [e/x]e'.
  function subst(e, x, ep) {
    switch (ep.tag) {
      case 'var':
        return ep.name === x ? e : ep;
      case 'const':
        return ep;
      case 'return':
        return mkReturn(ep.monad, subst(e, x, ep.arg), ep.span);
      case 'lift':
        return mkLift(subst(e, x, ep.arg), ep.span);
      case 'do': case 'let': {
        const rhs = subst(e, x, ep.rhs);
        let y = ep.var, body = ep.body;
        if (y === x) {
          // Binder shadows x: substitute only in the rhs.
          return { ...ep, rhs };
        }
        const fvE = freeVars(e);
        if (fvE.has(y)) {
          const avoid = new Set([...fvE, ...freeVars(body), x]);
          const y2 = fresh(y, avoid);
          body = subst(mkVar(y2, ep.varSpan), y, body);
          y = y2;
        }
        return { ...ep, var: y, rhs, body: subst(e, x, body) };
      }
    }
  }

  // Alpha-equality (spans ignored).
  function alphaEq(a, b, envA, envB) {
    envA = envA || new Map();
    envB = envB || new Map();
    if (a.tag !== b.tag) return false;
    switch (a.tag) {
      case 'var': {
        const ra = envA.has(a.name) ? envA.get(a.name) : null;
        const rb = envB.has(b.name) ? envB.get(b.name) : null;
        return ra === null && rb === null ? a.name === b.name : ra === rb;
      }
      case 'const':
        return a.name === b.name;
      case 'return':
        return a.monad === b.monad && alphaEq(a.arg, b.arg, envA, envB);
      case 'lift':
        return alphaEq(a.arg, b.arg, envA, envB);
      case 'do': case 'let': {
        if (a.tag === 'do' && a.monad !== b.monad) return false;
        if (!alphaEq(a.rhs, b.rhs, envA, envB)) return false;
        const envA2 = new Map(envA), envB2 = new Map(envB);
        const fresh = Symbol();
        envA2.set(a.var, fresh);
        envB2.set(b.var, fresh);
        return alphaEq(a.body, b.body, envA2, envB2);
      }
    }
  }

  function typeEq(a, b) {
    if (a.tag !== b.tag) return false;
    if (a.tag === 'tbase') return a.name === b.name;
    return a.monad === b.monad && typeEq(a.arg, b.arg);
  }

  function typeToString(t) {
    if (t.tag === 'tbase') return t.name;
    if (t.tag === 'tunknown') return '?';
    const arg = typeToString(t.arg);
    return 'M' + t.monad + ' ' + (t.arg.tag === 'tbase' || t.arg.tag === 'tunknown'
      ? arg : '(' + arg + ')');
  }

  function getAt(root, path) {
    let e = root;
    for (const k of path) e = e[k];
    return e;
  }

  // Functional replacement: rebuild the spine, sharing everything else.
  function replaceAt(root, path, sub) {
    if (path.length === 0) return sub;
    const [k, ...rest] = path;
    return { ...root, [k]: replaceAt(root[k], rest, sub) };
  }

  // Binder names introduced above (strictly enclosing) the node at `path`,
  // paired with the node that binds them. Order: outermost first.
  function bindersOnPath(root, path) {
    const out = [];
    let e = root;
    for (const k of path) {
      if ((e.tag === 'do' || e.tag === 'let') && k === 'body') {
        out.push({ name: e.var, node: e });
      }
      e = e[k];
    }
    return out;
  }

  // All subterm paths of `root`, root first, in pre-order.
  function allPaths(root) {
    const out = [];
    (function walk(e, path) {
      out.push(path);
      for (const k of childKeys(e)) walk(e[k], path.concat(k));
    })(root, []);
    return out;
  }

  MR.ast = {
    mkVar, mkConst, mkReturn, mkLift, mkDo, mkLet,
    tbase, tmonad,
    childKeys, freeVars, fresh, subst, alphaEq,
    typeEq, typeToString,
    getAt, replaceAt, bindersOnPath, allPaths,
  };
})();
