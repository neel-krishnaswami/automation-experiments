// Panel 3: the proof. A list of pretty-printed terms; the bottom term is
// interactive. Clicking selects the innermost subterm under the cursor
// (clicking within the selection again widens it); the menu lists applicable
// rewrites, applied with number keys or by clicking. 'u' enters
// un-substitution mode: pick a pattern subterm, toggle its occurrences,
// then choose which beta rule to apply in reverse.
(() => {
  const MR = (globalThis.MR = globalThis.MR || {});
  const A = MR.ast, T = MR.typecheck, PP = MR.pretty, R = MR.rewrite;

  const S = {
    els: null,
    sigma: new Map(),
    sigText: '',
    proof: [],            // [{ ast, rule: string|null }]
    types: null,          // type map of the bottom term
    selection: null,      // path array into the bottom term
    mode: 'normal',       // normal | unsub-pick | unsub-toggle | unsub-menu
    entries: [],          // current menu entries [{name, dir, result}]
    unsubAvailable: false,
    unsub: null,          // { pattern, occurrences: [relPath], chosen: Set<str> }
    lastTermEl: null,
  };

  const pathStr = (p) => p.join('.');
  const strPath = (s) => (s === '' ? [] : s.split('.'));
  const isPrefix = (p, q) => p.length <= q.length && p.every((k, i) => k === q[i]);

  function init(els) {
    S.els = els;
    els.container.addEventListener('click', onClick);
    els.container.addEventListener('mouseover', onHover);
    els.container.addEventListener('mouseout', () => setHovered(null));
    document.addEventListener('keydown', onKey);
    els.exportBtn.addEventListener('click', exportProof);
    els.undoBtn.addEventListener('click', undo);
    render();
  }

  function isFrozen() { return S.proof.length > 1; }

  // Called by main when the panel-2 term changes (only while not frozen),
  // and by Restart (force).
  function setStart(sigma, sigText, ast) {
    S.sigma = sigma;
    S.sigText = sigText;
    S.proof = ast ? [{ ast, rule: null }] : [];
    S.selection = null;
    S.mode = 'normal';
    S.unsub = null;
    render();
  }

  function bottom() { return S.proof[S.proof.length - 1]; }

  function selectedNode() { return A.getAt(bottom().ast, S.selection); }

  // ---- rendering ----

  function render() {
    const c = S.els.container;
    c.textContent = '';
    S.lastTermEl = null;
    if (S.proof.length === 0) {
      const p = document.createElement('p');
      p.className = 'placeholder';
      p.textContent = 'Write a well-typed term in the middle panel to start a proof.';
      c.appendChild(p);
    } else {
      S.proof.forEach((entry, i) => {
        if (i > 0) {
          const rule = document.createElement('div');
          rule.className = 'step-rule';
          rule.textContent = '== { ' + entry.rule + ' }';
          c.appendChild(rule);
        }
        const pre = document.createElement('pre');
        pre.className = 'term';
        PP.printToDom(entry.ast, pre);
        c.appendChild(pre);
        if (i === S.proof.length - 1) {
          pre.classList.add('active');
          S.lastTermEl = pre;
        }
      });
      const check = T.checkTerm(S.sigma, bottom().ast);
      S.types = check.types;
      if (!check.ok) console.warn('proof term failed to re-typecheck', check.errors);
      decorate();
      c.scrollTop = c.scrollHeight;
    }
    S.els.undoBtn.disabled = !isFrozen();
    S.els.exportBtn.disabled = S.proof.length === 0;
    updateMenu();
  }

  function nodeEl(path) {
    return S.lastTermEl &&
      S.lastTermEl.querySelector(`[data-path="${pathStr(path)}"]`);
  }

  function decorate() {
    if (!S.lastTermEl) return;
    for (const el of S.lastTermEl.querySelectorAll('.node')) {
      el.classList.remove('selected', 'occ', 'occ-chosen');
    }
    if (S.selection) {
      const el = nodeEl(S.selection);
      if (el) el.classList.add('selected');
    }
    if (S.mode === 'unsub-toggle' || S.mode === 'unsub-menu') {
      for (const rel of S.unsub.occurrences) {
        const el = nodeEl(S.selection.concat(rel));
        if (el) el.classList.add(S.unsub.chosen.has(pathStr(rel)) ? 'occ-chosen' : 'occ');
      }
    }
  }

  function setStatus(msg) { S.els.statusEl.textContent = msg; }

  function updateMenu() {
    const menu = S.els.menuEl;
    menu.textContent = '';
    const addItem = (key, label, preview, onClickItem, cls) => {
      const li = document.createElement('li');
      if (cls) li.className = cls;
      const k = document.createElement('span');
      k.className = 'key';
      k.textContent = key;
      li.appendChild(k);
      const lbl = document.createElement('span');
      lbl.className = 'rule-name';
      lbl.textContent = label;
      li.appendChild(lbl);
      if (preview) {
        const pv = document.createElement('code');
        pv.textContent = preview;
        li.appendChild(pv);
      }
      if (onClickItem) li.addEventListener('click', onClickItem);
      menu.appendChild(li);
    };

    if (S.proof.length === 0) { setStatus(''); return; }

    if (S.mode === 'normal') {
      if (!S.selection) {
        setStatus('Click a subterm of the bottom term to see the applicable rewrites. '
          + 'Click it again (or press w / ↑) to widen the selection; Esc clears it.');
        return;
      }
      const { entries, unsubAvailable } = R.applicableRewrites(bottom().ast, S.selection, S.types);
      S.entries = entries;
      S.unsubAvailable = unsubAvailable;
      entries.forEach((en, i) => {
        addItem(String(i + 1),
          en.name + (en.dir === 'ltr' ? '  →' : '  ←'),
          PP.printToInlineString(en.result),
          () => applyEntry(en));
      });
      if (unsubAvailable) {
        addItem('u', 'un-substitute… (abstract occurrences of a subterm)', null,
          enterUnsubPick, 'unsub-item');
      }
      if (entries.length === 0 && !unsubAvailable) {
        setStatus('No rewrites apply to this subterm.');
      } else {
        setStatus('Press a number key (or click an item) to apply a rewrite.'
          + (unsubAvailable ? " Press 'u' to un-substitute." : ''));
      }
    } else if (S.mode === 'unsub-pick') {
      setStatus('Un-substitute: click a subterm inside the selection to abstract. Esc cancels.');
    } else if (S.mode === 'unsub-toggle') {
      setStatus(`Un-substitute: ${S.unsub.chosen.size} of ${S.unsub.occurrences.length} `
        + 'occurrence(s) chosen. Click occurrences to toggle; Enter to choose a rule; Esc cancels.');
    } else if (S.mode === 'unsub-menu') {
      S.entries.forEach((en, i) => {
        addItem(String(i + 1), en.name + '  ←',
          PP.printToInlineString(en.result),
          () => applyEntry(en));
      });
      setStatus('Choose the expansion rule to apply (number key or click). Esc goes back.');
    }
  }

  // ---- interaction ----

  function setHovered(el) {
    if (S.hoveredEl) S.hoveredEl.classList.remove('hovered');
    S.hoveredEl = el || null;
    if (el) el.classList.add('hovered');
  }

  function onHover(ev) {
    if (!S.lastTermEl) return;
    const el = ev.target.closest('.node');
    setHovered(el && S.lastTermEl.contains(el) ? el : null);
  }

  function onClick(ev) {
    if (!S.lastTermEl) return;
    const el = ev.target.closest('.node');
    if (!el || !S.lastTermEl.contains(el)) return;
    const path = strPath(el.dataset.path);
    if (S.mode === 'normal') {
      if (S.selection && pathStr(S.selection) === pathStr(path)) {
        // clicking the selected node again widens the selection
        if (S.selection.length > 0) S.selection = S.selection.slice(0, -1);
      } else {
        S.selection = path;
      }
      decorate();
      updateMenu();
    } else if (S.mode === 'unsub-pick') {
      if (!isPrefix(S.selection, path)) return;
      const rel = path.slice(S.selection.length);
      const pattern = A.getAt(bottom().ast, path);
      const occurrences = R.findOccurrences(selectedNode(), pattern);
      const relStr = pathStr(rel);
      if (!occurrences.some((o) => pathStr(o) === relStr)) {
        setStatus('That occurrence mentions a variable bound inside the selection, '
          + 'so it cannot be abstracted. Pick another subterm; Esc cancels.');
        return;
      }
      S.unsub = { pattern, occurrences, chosen: new Set([relStr]) };
      S.mode = 'unsub-toggle';
      decorate();
      updateMenu();
    } else if (S.mode === 'unsub-toggle') {
      const rel = path.slice(S.selection.length);
      const hit = S.unsub.occurrences.find((o) => isPrefix(o, rel));
      if (!hit) return;
      const key = pathStr(hit);
      if (S.unsub.chosen.has(key)) S.unsub.chosen.delete(key);
      else S.unsub.chosen.add(key);
      decorate();
      updateMenu();
    }
  }

  function enterUnsubPick() {
    if (!S.unsubAvailable) return;
    S.mode = 'unsub-pick';
    updateMenu();
  }

  function onKey(ev) {
    const t = ev.target;
    if (t && (t.tagName === 'TEXTAREA' || t.tagName === 'INPUT')) return;
    if (S.proof.length === 0) return;

    if (ev.key === 'Escape') {
      if (S.mode === 'unsub-menu') { S.mode = 'unsub-toggle'; }
      else if (S.mode !== 'normal') { S.mode = 'normal'; S.unsub = null; }
      else { S.selection = null; }
      decorate(); updateMenu();
      return;
    }
    if (S.mode === 'normal' && S.selection) {
      if (ev.key === 'u') { enterUnsubPick(); return; }
      if (ev.key === 'w' || ev.key === 'ArrowUp') {
        if (S.selection.length > 0) {
          S.selection = S.selection.slice(0, -1);
          decorate(); updateMenu();
        }
        ev.preventDefault();
        return;
      }
      const d = parseInt(ev.key, 10);
      if (d >= 1 && d <= S.entries.length) applyEntry(S.entries[d - 1]);
      return;
    }
    if (S.mode === 'unsub-toggle' && ev.key === 'Enter') {
      const chosen = [...S.unsub.chosen].map(strPath);
      const cands = R.unsubCandidates(bottom().ast, S.selection, S.types, S.sigma,
        S.unsub.pattern, chosen);
      if (cands.length === 0) {
        setStatus('No expansion rule produces a well-typed term here. '
          + 'Toggle occurrences or press Esc to cancel.');
        return;
      }
      S.entries = cands.map((c) => ({ name: c.name, dir: 'rtl', result: c.result }));
      S.mode = 'unsub-menu';
      updateMenu();
      return;
    }
    if (S.mode === 'unsub-menu') {
      const d = parseInt(ev.key, 10);
      if (d >= 1 && d <= S.entries.length) applyEntry(S.entries[d - 1]);
    }
  }

  function applyEntry(entry) {
    const newAst = A.replaceAt(bottom().ast, S.selection, entry.result);
    const check = T.checkTerm(S.sigma, newAst);
    if (!check.ok) {
      console.error('rewrite produced an ill-typed term', entry, check.errors);
      setStatus('Internal error: rewrite produced an ill-typed term (see console).');
      return;
    }
    S.proof.push({ ast: newAst, rule: entry.name });
    S.selection = null;
    S.mode = 'normal';
    S.unsub = null;
    render();
  }

  function undo() {
    if (!isFrozen()) return;
    S.proof.pop();
    S.selection = null;
    S.mode = 'normal';
    S.unsub = null;
    render();
  }

  function exportProof() {
    if (S.proof.length === 0) return;
    const parts = ['Signature', '---------', S.sigText.trim(), '', 'Proof', '-----', ''];
    S.proof.forEach((entry, i) => {
      if (i > 0) parts.push('', '  == { ' + entry.rule + ' }', '');
      parts.push(PP.printToString(entry.ast));
    });
    const blob = new Blob([parts.join('\n') + '\n'], { type: 'text/plain' });
    const url = URL.createObjectURL(blob);
    const a = document.createElement('a');
    a.href = url;
    a.download = 'proof.txt';
    document.body.appendChild(a);
    a.click();
    a.remove();
    URL.revokeObjectURL(url);
  }

  MR.uiProof = { init, setStart, isFrozen };
})();
