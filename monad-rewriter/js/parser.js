// Recursive-descent parsers for types, signatures, and expressions.
//
// Grammar (from design.md):
//   b ::= p | (A)          A ::= b | M1 b | M2 b
//   s ::= x | c | return1 s | return2 s | (e)
//   e ::= s | do1 x <- s; e | do2 x <- s; e | let x = s; e | lift s
//
// Parse errors are reported as { span, msg }; the parsers never throw past
// their public entry points.
(() => {
  const MR = (globalThis.MR = globalThis.MR || {});
  const { lex } = MR.lexer;
  const A = MR.ast;

  class ParseError extends Error {
    constructor(span, msg) { super(msg); this.span = span; this.msg = msg; }
  }

  class TokenStream {
    constructor(toks) { this.toks = toks; this.pos = 0; }
    peek() { return this.toks[this.pos]; }
    next() { return this.toks[this.pos++]; }
    expect(kind, what) {
      const t = this.peek();
      if (t.kind !== kind) this.fail(what);
      return this.next();
    }
    fail(what) {
      const t = this.peek();
      const found = t.kind === 'eof' ? 'end of input' : `'${t.text}'`;
      throw new ParseError({ start: t.start, end: Math.max(t.end, t.start + 1) },
        `Expected ${what}, found ${found}`);
    }
  }

  // A ::= b | M1 b | M2 b
  function parseType(ts) {
    const t = ts.peek();
    if (t.kind === 'kw' && (t.text === 'M1' || t.text === 'M2')) {
      ts.next();
      const arg = parseBaseType(ts);
      return A.tmonad(t.text === 'M1' ? 1 : 2, arg);
    }
    return parseBaseType(ts);
  }

  // b ::= p | (A)
  function parseBaseType(ts) {
    const t = ts.peek();
    if (t.kind === 'uident') { ts.next(); return A.tbase(t.text); }
    if (t.kind === 'lparen') {
      ts.next();
      const inner = parseType(ts);
      ts.expect('rparen', "')'");
      return inner;
    }
    ts.fail('a type');
  }

  // Signature: newline-separated "c : A" lines, each parsed independently so
  // one bad line does not poison the rest.
  function parseSignature(src) {
    const sigma = new Map();
    const errors = [];
    let offset = 0;
    for (const line of src.split('\n')) {
      const lineStart = offset;
      offset += line.length + 1;
      if (line.trim() === '') continue;
      const lineSpan = () => {
        const s = lineStart + line.match(/^\s*/)[0].length;
        return { start: s, end: lineStart + line.replace(/\s+$/, '').length };
      };
      try {
        const ts = new TokenStream(lex(line, lineStart));
        const c = ts.expect('uident', 'a constant name');
        ts.expect('colon', "':'");
        const ty = parseType(ts);
        ts.expect('eof', 'end of line');
        if (sigma.has(c.text)) {
          errors.push({ span: { start: c.start, end: c.end },
            msg: `Constant '${c.text}' is declared more than once` });
        }
        sigma.set(c.text, ty);
      } catch (err) {
        if (!(err instanceof ParseError)) throw err;
        errors.push({ span: err.span.start < offset - 1 ? err.span : lineSpan(), msg: err.msg });
      }
    }
    return { sigma, errors };
  }

  // e ::= s | do1 x <- s; e | do2 x <- s; e | let x = s; e | lift s
  function parseExpr(ts) {
    const t = ts.peek();
    if (t.kind === 'kw' && (t.text === 'do1' || t.text === 'do2')) {
      ts.next();
      const x = ts.expect('lvar', 'a variable name');
      ts.expect('arrow', "'<-'");
      const rhs = parseSimple(ts);
      ts.expect('semi', "';'");
      const body = parseExpr(ts);
      return A.mkDo(t.text === 'do1' ? 1 : 2, x.text, rhs, body,
        { start: t.start, end: body.span.end }, { start: x.start, end: x.end });
    }
    if (t.kind === 'kw' && t.text === 'let') {
      ts.next();
      const x = ts.expect('lvar', 'a variable name');
      ts.expect('eq', "'='");
      const rhs = parseSimple(ts);
      ts.expect('semi', "';'");
      const body = parseExpr(ts);
      return A.mkLet(x.text, rhs, body,
        { start: t.start, end: body.span.end }, { start: x.start, end: x.end });
    }
    if (t.kind === 'kw' && t.text === 'lift') {
      ts.next();
      const arg = parseSimple(ts);
      return A.mkLift(arg, { start: t.start, end: arg.span.end });
    }
    return parseSimple(ts);
  }

  // s ::= x | c | return1 s | return2 s | (e)
  function parseSimple(ts) {
    const t = ts.peek();
    if (t.kind === 'lvar') {
      ts.next();
      return A.mkVar(t.text, { start: t.start, end: t.end });
    }
    if (t.kind === 'uident') {
      ts.next();
      return A.mkConst(t.text, { start: t.start, end: t.end });
    }
    if (t.kind === 'kw' && (t.text === 'return1' || t.text === 'return2')) {
      ts.next();
      const arg = parseSimple(ts);
      return A.mkReturn(t.text === 'return1' ? 1 : 2, arg,
        { start: t.start, end: arg.span.end });
    }
    if (t.kind === 'lparen') {
      ts.next();
      const e = parseExpr(ts);
      const close = ts.expect('rparen', "')'");
      // Widen the span to cover the parentheses so highlighting includes them.
      return { ...e, span: { start: t.start, end: close.end } };
    }
    ts.fail('an expression');
  }

  // Public entry point for panel 2: parse a single term.
  function parseTerm(src) {
    try {
      const ts = new TokenStream(lex(src, 0));
      if (ts.peek().kind === 'eof') return { ast: null, error: null }; // empty input
      const ast = parseExpr(ts);
      ts.expect('eof', 'end of input');
      return { ast, error: null };
    } catch (err) {
      if (!(err instanceof ParseError)) throw err;
      return { ast: null, error: { span: err.span, msg: err.msg } };
    }
  }

  MR.parser = { parseSignature, parseTerm, parseType, TokenStream, ParseError };
})();
