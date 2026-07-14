// Unit tests for the core logic. Run in the browser via test.html, or
// headlessly with:
//   node -e "const fs=require('fs');for(const f of ['ast','lexer','parser','typecheck','pretty','rewrite','tests'])(0,eval)(fs.readFileSync('js/'+f+'.js','utf8'))"
(() => {
  const MR = globalThis.MR;
  const A = MR.ast, P = MR.parser, T = MR.typecheck, PP = MR.pretty, R = MR.rewrite;

  const results = [];
  function test(name, fn) {
    try { fn(); results.push({ name, ok: true }); }
    catch (e) { results.push({ name, ok: false, err: e.message || String(e) }); }
  }
  function assert(cond, msg) { if (!cond) throw new Error(msg || 'assertion failed'); }
  function assertEq(got, want, msg) {
    if (got !== want) {
      throw new Error((msg ? msg + ': ' : '') +
        'expected ' + JSON.stringify(want) + ', got ' + JSON.stringify(got));
    }
  }
  const parse = (src) => {
    const r = P.parseTerm(src);
    assert(r.ast, 'parse failed: ' + (r.error && r.error.msg) + ' in: ' + src);
    return r.ast;
  };
  const sig = (src) => {
    const r = P.parseSignature(src);
    assertEq(r.errors.length, 0, 'signature errors');
    return r.sigma;
  };

  // ---- lexer / parser ----

  test('lexer: offsets and kinds', () => {
    const toks = MR.lexer.lex('do1 x <- C1; return1 x');
    assertEq(toks[0].kind, 'kw'); assertEq(toks[0].start, 0); assertEq(toks[0].end, 3);
    assertEq(toks[1].kind, 'lvar');
    assertEq(toks[2].kind, 'arrow');
    assertEq(toks[3].kind, 'uident'); assertEq(toks[3].text, 'C1');
    assertEq(toks[4].kind, 'semi');
    assertEq(toks[toks.length - 1].kind, 'eof');
  });

  test('lexer: bad character becomes error token', () => {
    const toks = MR.lexer.lex('x @ y');
    assertEq(toks[1].kind, 'error');
  });

  test('parser: doc example parses with correct shape', () => {
    const e = parse('do1 x <- (do1 y <- e1; e2); return1 x');
    assertEq(e.tag, 'do'); assertEq(e.monad, 1); assertEq(e.var, 'x');
    assertEq(e.rhs.tag, 'do'); assertEq(e.rhs.var, 'y');
    assertEq(e.body.tag, 'return');
  });

  test('parser: single-letter identifiers allowed', () => {
    assertEq(parse('x').tag, 'var');
    assertEq(parse('C').tag, 'const');
  });

  test('parser: span widened over parentheses', () => {
    const e = parse('(c)');
    assertEq(e.span.start, 0); assertEq(e.span.end, 3);
  });

  test('parser: root span covers whole term', () => {
    const src = 'do1 x <- c; return1 x';
    const e = parse(src);
    assertEq(e.span.start, 0); assertEq(e.span.end, src.length);
  });

  test('parser: trailing garbage is an error', () => {
    const r = P.parseTerm('x y');
    assert(r.error && r.ast === null);
    assertEq(r.error.span.start, 2);
  });

  test('parser: complex rhs requires parens', () => {
    assert(P.parseTerm('do1 x <- do1 y <- c; d; e').error !== null);
    assert(P.parseTerm('do1 x <- (do1 y <- c; d); e').error === null);
  });

  test('parser: error span at offending token', () => {
    const r = P.parseTerm('do1 x <- ; e');
    assert(r.error);
    assertEq(r.error.span.start, 9);
  });

  test('signature: per-line recovery and duplicates', () => {
    const r = P.parseSignature('C : M1 P\nD : M2 (M1 Q)\n\nthis is junk\nC : P');
    assert(r.sigma.has('C') && r.sigma.has('D'));
    assertEq(r.errors.length, 2); // junk line + duplicate C
    assertEq(A.typeToString(r.sigma.get('D')), 'M2 (M1 Q)');
    assertEq(A.typeToString(r.sigma.get('C')), 'P'); // later declaration wins
  });

  // ---- ast: fv, fresh, subst, alphaEq ----

  test('freeVars respects binders', () => {
    const e = parse('do1 x <- c; return1 x');
    const fv = A.freeVars(e);
    assert(fv.has('c') && !fv.has('x'));
  });

  test('fresh avoids the given set', () => {
    assertEq(A.fresh('y', new Set()), 'y');
    assertEq(A.fresh('y', new Set(['y'])), 'y1');
    assertEq(A.fresh('y', new Set(['y', 'y1'])), 'y2');
  });

  test('subst: basic replacement', () => {
    const e = A.subst(parse('C'), 'x', parse('return1 x'));
    assert(A.alphaEq(e, parse('return1 C')));
  });

  test('subst: binder shadows the substituted variable', () => {
    const e = A.subst(parse('C'), 'x', parse('do1 x <- x; return1 x'));
    assert(A.alphaEq(e, parse('do1 x <- C; return1 x')));
  });

  test('subst: capture-avoiding (binder renamed)', () => {
    // [y/x](do1 y <- C; return1 x) must not capture the substituted y.
    const e = A.subst(parse('y'), 'x', parse('do1 y <- C; return1 x'));
    assert(A.alphaEq(e, parse('do1 z <- C; return1 y')));
    assert(!A.alphaEq(e, parse('do1 z <- C; return1 z')));
  });

  test('alphaEq: renames bound variables', () => {
    assert(A.alphaEq(parse('do1 x <- c; return1 x'), parse('do1 z <- c; return1 z')));
    assert(!A.alphaEq(parse('do1 x <- c; return1 x'), parse('do1 x <- c; return1 c')));
    assert(!A.alphaEq(parse('do1 x <- c; return1 y'), parse('do1 x <- c; return1 z')));
  });

  // ---- paths ----

  test('getAt / replaceAt / bindersOnPath', () => {
    const e = parse('do1 x <- c; do2 y <- d; return2 y');
    assertEq(A.getAt(e, ['body', 'rhs']).name, 'd');
    const e2 = A.replaceAt(e, ['body', 'rhs'], A.mkVar('x'));
    assert(A.alphaEq(e2, parse('do1 x <- c; do2 y <- x; return2 y')));
    assert(A.alphaEq(e, parse('do1 x <- c; do2 y <- d; return2 y')), 'original untouched');
    const bs = A.bindersOnPath(e, ['body', 'body', 'arg']);
    assertEq(bs.map((b) => b.name).join(','), 'x,y');
    assertEq(A.bindersOnPath(e, ['body', 'rhs']).map((b) => b.name).join(','), 'x');
  });

  // ---- pretty printer ----

  test('pretty: doc layout example, byte for byte', () => {
    const e = parse('do1 x <- (do1 y <- e1; e2); e3');
    assertEq(PP.printToString(e),
      'do1 x <- (do1 y <- e1;\n' +
      '          e2);\n' +
      'e3');
  });

  test('pretty: simple do layout', () => {
    assertEq(PP.printToString(parse('do1 x <- e1; e2')), 'do1 x <- e1;\ne2');
    assertEq(PP.printToString(parse('let x = e1; e2')), 'let x = e1;\ne2');
  });

  test('pretty: lift and let need parens in simple slots', () => {
    assertEq(PP.printToString(parse('do1 x <- (lift c); return1 x')),
      'do1 x <- (lift c);\nreturn1 x');
    assertEq(PP.printToString(parse('return2 (let y = c; y)')),
      'return2 (let y = c;\n         y)');
  });

  test('pretty: round-trip parse . print = id (alpha)', () => {
    const srcs = [
      'x', 'C', 'return1 (return2 c)', 'lift (return1 c)',
      'do1 x <- (do1 y <- e1; e2); return1 x',
      'do2 x <- (lift (do1 y <- c; return1 y)); do2 z <- return2 x; return2 z',
      'let a = (do1 x <- c; return1 x); do1 y <- a; return1 y',
    ];
    for (const s of srcs) {
      const e = parse(s);
      const printed = PP.printToString(e);
      assert(A.alphaEq(parse(printed), e), 'round trip failed for: ' + s + '\n' + printed);
    }
  });

  test('pretty: inline printing', () => {
    assertEq(PP.printToInlineString(parse('do1 x <- e1; e2')), 'do1 x <- e1; e2');
  });

  // ---- typechecker ----

  const SIG = sig('C : M1 P\nD : M1 Q\nE : M2 P\nK : P\nN : M1 (M2 P)');

  test('typecheck: general bind (different result type)', () => {
    const r = T.checkTerm(SIG, parse('do1 x <- C; D'));
    assert(r.ok);
    assertEq(A.typeToString(r.type), 'M1 Q');
  });

  test('typecheck: return and nested monads', () => {
    let r = T.checkTerm(SIG, parse('return1 K'));
    assert(r.ok); assertEq(A.typeToString(r.type), 'M1 P');
    r = T.checkTerm(SIG, parse('return1 C'));
    assert(r.ok); assertEq(A.typeToString(r.type), 'M1 (M1 P)');
    r = T.checkTerm(SIG, parse('do1 x <- N; return1 x'));
    assert(r.ok); assertEq(A.typeToString(r.type), 'M1 (M2 P)');
  });

  test('typecheck: lift', () => {
    const r = T.checkTerm(SIG, parse('lift C'));
    assert(r.ok); assertEq(A.typeToString(r.type), 'M2 P');
    const bad = T.checkTerm(SIG, parse('lift K'));
    assert(!bad.ok); assertEq(bad.errors.length, 1);
  });

  test('typecheck: let extends the context', () => {
    const r = T.checkTerm(SIG, parse('let a = C; do1 x <- a; return1 x'));
    assert(r.ok); assertEq(A.typeToString(r.type), 'M1 P');
  });

  test('typecheck: unbound / undeclared', () => {
    let r = T.checkTerm(SIG, parse('nope'));
    assert(!r.ok && /Unbound/.test(r.errors[0].msg));
    r = T.checkTerm(SIG, parse('Nope'));
    assert(!r.ok && /Undeclared/.test(r.errors[0].msg));
  });

  test('typecheck: smallest wrong subterm only', () => {
    // C : M1 P cannot be bound by do2; the error sits on C, and the enclosing
    // do2 and do1 stay silent.
    const src = 'do1 x <- (do2 y <- C; return2 y); return1 x';
    const e = parse(src);
    const r = T.checkTerm(SIG, e);
    assert(!r.ok);
    assertEq(r.errors.length, 1);
    const cSpan = e.rhs.rhs.span;
    assertEq(r.errors[0].span.start, cSpan.start);
    assertEq(r.errors[0].span.end, cSpan.end);
  });

  test('typecheck: two independent errors both surface (ERROR1/ERROR2)', () => {
    const r = T.checkTerm(SIG, parse('do1 x <- Bad1; (do2 y <- Bad2; return2 y)'));
    assert(!r.ok);
    assertEq(r.errors.length, 2);
    assert(r.errors.every((e) => /Undeclared/.test(e.msg)));
  });

  test('typecheck: poisoning stops upward cascades', () => {
    const r = T.checkTerm(SIG, parse('return1 (lift Bad)'));
    assert(!r.ok);
    assertEq(r.errors.length, 1);
  });

  test('typecheck: body monad mismatch anchors on the body', () => {
    const e = parse('do1 x <- C; return2 x');
    const r = T.checkTerm(SIG, e);
    assert(!r.ok);
    assertEq(r.errors.length, 1);
    assertEq(r.errors[0].span.start, e.body.span.start);
  });

  test('typecheck: gammaAt reads binder types off the type map', () => {
    const e = parse('do1 x <- C; do1 y <- D; return1 y');
    const r = T.checkTerm(SIG, e);
    assert(r.ok);
    const gamma = T.gammaAt(e, ['body', 'body'], r.types);
    assertEq(A.typeToString(gamma.get('x')), 'P');
    assertEq(A.typeToString(gamma.get('y')), 'Q');
  });

  // ---- rewrites ----

  function rewritesFor(src, path) {
    const e = parse(src);
    const r = T.checkTerm(SIG, e);
    assert(r.ok, 'term must be well-typed: ' + src);
    return { root: e, ...R.applicableRewrites(e, path || [], r.types), types: r.types };
  }

  test('rewrite: doc worked example offers eta then assoc, then expansions', () => {
    const w = rewritesFor('do1 x <- (do1 y <- C; D); return1 x');
    const reductions = w.entries.filter((en) => en.dir === 'ltr');
    assertEq(reductions.length, 2);
    assertEq(reductions[0].name, 'do1-eta');
    assert(A.alphaEq(reductions[0].result, parse('do1 y <- C; D')));
    assertEq(reductions[1].name, 'do1-assoc');
    assert(A.alphaEq(reductions[1].result, parse('do1 y <- C; do1 x <- D; return1 x')));
    // reductions listed before expansions
    const firstRtl = w.entries.findIndex((en) => en.dir === 'rtl');
    assert(firstRtl === -1 || firstRtl >= reductions.length);
    assert(w.unsubAvailable);
  });

  test('rewrite: do1-beta substitutes', () => {
    const w = rewritesFor('do1 x <- return1 K; return1 x');
    const beta = w.entries.find((en) => en.name === 'do1-beta');
    assert(beta && A.alphaEq(beta.result, parse('return1 K')));
  });

  test('rewrite: lift-beta', () => {
    const w = rewritesFor('do2 x <- (lift (return1 K)); return2 x');
    const b = w.entries.find((en) => en.name === 'lift-beta');
    assert(b && A.alphaEq(b.result, parse('return2 K')));
  });

  test('rewrite: assoc renames to avoid capture', () => {
    // y is free in e3 (bound by the outer let), so assoc must rename the inner y.
    const e = parse('let y = K; do1 x <- (do1 y <- C; D); return1 y');
    const r = T.checkTerm(SIG, e);
    assert(r.ok);
    const w = R.applicableRewrites(e, ['body'], r.types);
    const a = w.entries.find((en) => en.name === 'do1-assoc');
    assert(a);
    assert(A.alphaEq(a.result, parse('do1 z <- C; do1 x <- D; return1 y')),
      'got: ' + PP.printToInlineString(a.result));
  });

  test('rewrite: eta-expansions offered for monadic types', () => {
    const w = rewritesFor('C');
    const ex = w.entries.find((en) => en.name === 'do1-eta (expand)');
    assert(ex && A.alphaEq(ex.result, parse('do1 x <- C; return1 x')));
    assert(!w.entries.some((en) => en.name === 'do2-eta (expand)'));
    const w2 = rewritesFor('E');
    assert(w2.entries.some((en) => en.name === 'do2-eta (expand)'));
  });

  test('rewrite: no expansions for non-monadic type', () => {
    const w = rewritesFor('K');
    assertEq(w.entries.length, 0);
    assert(!w.unsubAvailable);
  });

  test('rewrite: unassoc applies and respects its side condition', () => {
    const w = rewritesFor('do1 y <- C; do1 x <- D; return1 x');
    const u = w.entries.find((en) => en.name === 'do1-assoc (reverse)');
    assert(u && A.alphaEq(u.result, parse('do1 x <- (do1 y <- C; D); return1 x')));
    // y free in e3 blocks it:
    const w2 = rewritesFor('do1 y <- C; do1 x <- D; return1 y');
    assert(!w2.entries.some((en) => en.name === 'do1-assoc (reverse)'));
  });

  test('rewrite: all rewrite results re-typecheck', () => {
    const srcs = [
      'do1 x <- (do1 y <- C; D); return1 x',
      'do1 x <- return1 K; return1 x',
      'do2 x <- (lift (return1 K)); return2 x',
      'do1 y <- C; do1 x <- D; return1 x',
      'C', 'E',
    ];
    for (const s of srcs) {
      const e = parse(s);
      const r = T.checkTerm(SIG, e);
      assert(r.ok);
      const w = R.applicableRewrites(e, [], r.types);
      for (const en of w.entries) {
        const r2 = T.checkTerm(SIG, en.result);
        assert(r2.ok, en.name + ' produced ill-typed term for ' + s);
        assert(A.typeEq(r2.type, r.type), en.name + ' changed the type for ' + s);
      }
    }
  });

  // ---- un-substitution ----

  test('unsub: findOccurrences with capture exclusion', () => {
    const sel = parse('do1 y <- C; return1 y');
    // pattern y: its only occurrence is under the binder y -- excluded
    assertEq(R.findOccurrences(sel, A.mkVar('y')).length, 0);
    // pattern C occurs once, at the rhs
    const occ = R.findOccurrences(sel, parse('C'));
    assertEq(occ.length, 1);
    assertEq(occ[0].join('.'), 'rhs');
  });

  test('unsub: candidates filtered by typechecking', () => {
    const e = parse('return1 K');
    const r = T.checkTerm(SIG, e);
    const occ = R.findOccurrences(e, parse('K'));
    assertEq(occ.length, 1);
    const cands = R.unsubCandidates(e, [], r.types, SIG, parse('K'), occ);
    assertEq(cands.length, 1);
    assertEq(cands[0].name, 'do1-beta (reverse)');
    assert(A.alphaEq(cands[0].result, parse('do1 x <- return1 K; return1 x')));
  });

  test('unsub: works under binders using the ambient context', () => {
    const root = parse('do1 y <- C; return1 y');
    const r = T.checkTerm(SIG, root);
    const sel = A.getAt(root, ['body']); // return1 y : M1 P, with y:P ambient
    const occ = R.findOccurrences(sel, A.mkVar('y'));
    assertEq(occ.length, 1);
    const cands = R.unsubCandidates(root, ['body'], r.types, SIG, A.mkVar('y'), occ);
    assertEq(cands.length, 1);
    assert(A.alphaEq(cands[0].result, parse('do1 x <- return1 y; return1 x')));
    // applying it inside the root keeps the root well-typed
    const root2 = A.replaceAt(root, ['body'], cands[0].result);
    assert(T.checkTerm(SIG, root2).ok);
  });

  test('unsub: M2 candidates for an M2 selection', () => {
    const e = parse('return2 K');
    const r = T.checkTerm(SIG, e);
    const occ = R.findOccurrences(e, parse('K'));
    const cands = R.unsubCandidates(e, [], r.types, SIG, parse('K'), occ);
    assertEq(cands.map((c) => c.name).join(','), 'do2-beta (reverse),lift-beta (reverse)');
    for (const c of cands) {
      // beta-reducing the candidate with the inverse rule gives back the original
      const ruleName = c.name.replace(' (reverse)', '');
      const w = R.applicableRewrites(c.result, [], T.checkTerm(SIG, c.result).types);
      const red = w.entries.find((en) => en.name === ruleName);
      assert(red && A.alphaEq(red.result, e), 'inverse of ' + c.name);
    }
  });

  // ---- reporting ----

  const failed = results.filter((r) => !r.ok);
  MR.testResults = results;
  if (typeof document !== 'undefined' && document.getElementById('results')) {
    const el = document.getElementById('results');
    for (const r of results) {
      const li = document.createElement('li');
      li.className = r.ok ? 'pass' : 'fail';
      li.textContent = (r.ok ? '✓ ' : '✗ ') + r.name + (r.ok ? '' : ' — ' + r.err);
      el.appendChild(li);
    }
    document.getElementById('summary').textContent =
      failed.length === 0 ? `All ${results.length} tests passed.`
        : `${failed.length} of ${results.length} tests FAILED.`;
  } else if (typeof process !== 'undefined') {
    for (const r of results) {
      console.log((r.ok ? 'PASS' : 'FAIL') + ' ' + r.name + (r.ok ? '' : ' — ' + r.err));
    }
    console.log(failed.length === 0
      ? `All ${results.length} tests passed.`
      : `${failed.length} of ${results.length} tests FAILED.`);
    process.exitCode = failed.length === 0 ? 0 : 1;
  }
})();
