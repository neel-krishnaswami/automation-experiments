// Tokenizer. Never throws: unrecognizable characters become 'error' tokens so
// live editing degrades gracefully.
//
// Token: { kind, text, start, end }  -- absolute char offsets into the source.
// Kinds: lvar uident kw lparen rparen semi colon arrow eq eof error
(() => {
  const MR = (globalThis.MR = globalThis.MR || {});

  const KEYWORDS = new Set(['do1', 'do2', 'let', 'lift', 'return1', 'return2', 'M1', 'M2']);

  const isIdentStart = (c) => /[a-zA-Z]/.test(c);
  const isIdentChar = (c) => /[a-zA-Z_0-9]/.test(c);

  // offset: added to all token positions (used when lexing a slice of a
  // larger buffer, e.g. one signature line).
  function lex(src, offset) {
    offset = offset | 0;
    const toks = [];
    let i = 0;
    const push = (kind, start, end) =>
      toks.push({ kind, text: src.slice(start, end), start: start + offset, end: end + offset });
    while (i < src.length) {
      const c = src[i];
      if (/\s/.test(c)) { i++; continue; }
      if (isIdentStart(c)) {
        const start = i;
        while (i < src.length && isIdentChar(src[i])) i++;
        const text = src.slice(start, i);
        const kind = KEYWORDS.has(text) ? 'kw'
          : /[A-Z]/.test(text[0]) ? 'uident' : 'lvar';
        push(kind, start, i);
        continue;
      }
      if (c === '(') { push('lparen', i, i + 1); i++; continue; }
      if (c === ')') { push('rparen', i, i + 1); i++; continue; }
      if (c === ';') { push('semi', i, i + 1); i++; continue; }
      if (c === ':') { push('colon', i, i + 1); i++; continue; }
      if (c === '=') { push('eq', i, i + 1); i++; continue; }
      if (c === '<' && src[i + 1] === '-') { push('arrow', i, i + 2); i += 2; continue; }
      push('error', i, i + 1);
      i++;
    }
    toks.push({ kind: 'eof', text: '', start: src.length + offset, end: src.length + offset });
    return toks;
  }

  MR.lexer = { lex, KEYWORDS };
})();
