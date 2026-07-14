// Pretty printer implementing the layout spec from design.md:
//   - a newline follows each semicolon;
//   - the body of a do/let starts at the column of the do/let keyword;
//   - a do/let in rhs position is parenthesized, and its own lines align
//     under the inner do/let.
//
// One traversal drives interchangeable sinks: a string sink (export, tests),
// an inline sink (one-line previews for the rewrite menu), and a DOM sink
// (panel 3), which emits nested <span data-path=…> elements so the DOM itself
// is the AST<->text mapping.
(() => {
  const MR = (globalThis.MR = globalThis.MR || {});

  // A complex expression in a simple-expression slot needs parentheses.
  const needsParens = (e) => e.tag === 'do' || e.tag === 'let' || e.tag === 'lift';

  function print(e, sink, path) {
    sink.enter(e, path);
    switch (e.tag) {
      case 'var': case 'const':
        sink.text(e.name);
        break;
      case 'return':
        sink.text('return' + e.monad + ' ');
        printSimpleSlot(e.arg, sink, path.concat('arg'));
        break;
      case 'lift':
        sink.text('lift ');
        printSimpleSlot(e.arg, sink, path.concat('arg'));
        break;
      case 'do': case 'let': {
        const col = sink.col;
        sink.text(e.tag === 'do'
          ? `do${e.monad} ${e.var} <- `
          : `let ${e.var} = `);
        printSimpleSlot(e.rhs, sink, path.concat('rhs'));
        sink.text(';');
        sink.newline(col);
        print(e.body, sink, path.concat('body'));
        break;
      }
    }
    sink.exit();
  }

  function printSimpleSlot(e, sink, path) {
    if (needsParens(e)) {
      sink.text('(');
      print(e, sink, path);
      sink.text(')');
    } else {
      print(e, sink, path);
    }
  }

  function makeStringSink() {
    return {
      parts: [], col: 0,
      text(s) { this.parts.push(s); this.col += s.length; },
      newline(col) { this.parts.push('\n' + ' '.repeat(col)); this.col = col; },
      enter() {}, exit() {},
      result() { return this.parts.join(''); },
    };
  }

  function makeInlineSink() {
    const s = makeStringSink();
    s.newline = function () { this.text(' '); };
    return s;
  }

  function printToString(e) {
    const sink = makeStringSink();
    print(e, sink, []);
    return sink.result();
  }

  function printToInlineString(e) {
    const sink = makeInlineSink();
    print(e, sink, []);
    return sink.result();
  }

  // DOM sink: fills `rootEl` with nested spans, one per AST node, each
  // carrying data-path (child keys joined with '.'; '' for the root).
  function makeDomSink(rootEl) {
    return {
      stack: [rootEl], col: 0,
      top() { return this.stack[this.stack.length - 1]; },
      text(s) {
        this.top().appendChild(document.createTextNode(s));
        this.col += s.length;
      },
      newline(col) {
        this.top().appendChild(document.createTextNode('\n' + ' '.repeat(col)));
        this.col = col;
      },
      enter(node, path) {
        const span = document.createElement('span');
        span.className = 'node';
        span.dataset.path = path.join('.');
        this.top().appendChild(span);
        this.stack.push(span);
      },
      exit() { this.stack.pop(); },
    };
  }

  function printToDom(e, rootEl) {
    print(e, makeDomSink(rootEl), []);
  }

  MR.pretty = { print, printToString, printToInlineString, printToDom, needsParens };
})();
