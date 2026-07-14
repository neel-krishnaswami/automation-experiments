// Wiring: editors for the signature and term panels, live re-parsing and
// typechecking, and the proof panel.
(() => {
  const MR = globalThis.MR;
  const P = MR.parser, T = MR.typecheck, A = MR.ast;

  const DEFAULT_SIG = 'C : M1 P\nD : M1 Q\nE : M2 Q\nK : P';
  const DEFAULT_TERM = 'do1 x <- (do1 y <- C; D); return1 x';

  const el = (id) => document.getElementById(id);
  const typeEl = el('term-type');

  const sigEditor = MR.uiEditor.makeEditor(el('sig-editor'), {
    initial: DEFAULT_SIG,
    onChange: () => refresh(false),
  });
  const termEditor = MR.uiEditor.makeEditor(el('term-editor'), {
    initial: DEFAULT_TERM,
    onChange: () => refresh(false),
  });

  MR.uiProof.init({
    container: el('proof'),
    statusEl: el('status'),
    menuEl: el('rewrite-menu'),
    exportBtn: el('export-btn'),
    undoBtn: el('undo-btn'),
  });
  el('restart-btn').addEventListener('click', () => refresh(true));

  // Re-parse and re-typecheck both panels. The proof panel follows the term
  // panel only while no rewrite step has been taken yet (or on Restart).
  function refresh(force) {
    const sigRes = P.parseSignature(sigEditor.getValue());
    sigEditor.setErrors(sigRes.errors);
    const sigma = sigRes.sigma;

    const { ast, error } = P.parseTerm(termEditor.getValue());
    let goodAst = null;
    if (error) {
      termEditor.setErrors([error]);
      setType('parse error', false);
    } else if (!ast) {
      termEditor.setErrors([]);
      setType('', true);
    } else {
      const check = T.checkTerm(sigma, ast);
      termEditor.setErrors(check.errors);
      if (check.ok) {
        goodAst = ast;
        setType(': ' + A.typeToString(check.type), true);
      } else {
        setType('ill-typed (hover the red marks)', false);
      }
    }

    if (force || !MR.uiProof.isFrozen()) {
      MR.uiProof.setStart(sigma, sigEditor.getValue(), goodAst);
    }
  }

  function setType(text, ok) {
    typeEl.textContent = text;
    typeEl.className = ok ? 'type ok' : 'type bad';
  }

  refresh(false);
})();
