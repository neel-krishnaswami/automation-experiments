// Editor component for panels 1 and 2: a textarea with a mirrored <pre>
// backdrop that carries error highlights, plus hover bubbles for messages.
//
// The textarea's text is transparent-backgrounded and sits exactly on top of
// the backdrop (same font/padding/wrapping), so <mark> elements in the
// backdrop appear as highlights under the editable text. The backdrop is
// pointer-events:none; hover detection hit-tests the mouse position against
// the marks' client rects.
(() => {
  const MR = (globalThis.MR = globalThis.MR || {});

  let bubble = null;
  function showBubble(x, y, msg) {
    if (!bubble) {
      bubble = document.createElement('div');
      bubble.className = 'bubble';
      document.body.appendChild(bubble);
    }
    bubble.textContent = msg;
    bubble.style.display = 'block';
    bubble.style.left = Math.min(x + 12, window.innerWidth - 320) + 'px';
    bubble.style.top = (y + 16) + 'px';
  }
  function hideBubble() {
    if (bubble) bubble.style.display = 'none';
  }

  // makeEditor(container, { initial, onChange }) ->
  //   { getValue, setValue, setErrors }
  function makeEditor(container, opts) {
    container.classList.add('editor');
    const backdrop = document.createElement('div');
    backdrop.className = 'backdrop';
    const hl = document.createElement('pre');
    hl.className = 'editor-text hl';
    backdrop.appendChild(hl);
    const ta = document.createElement('textarea');
    ta.className = 'editor-text';
    ta.spellcheck = false;
    ta.autocapitalize = 'off';
    ta.setAttribute('autocomplete', 'off');
    container.appendChild(backdrop);
    container.appendChild(ta);

    let errors = [];
    let marks = [];

    function render() {
      const text = ta.value;
      hl.textContent = '';
      const sorted = [...errors].sort((a, b) => a.span.start - b.span.start);
      let pos = 0;
      for (const err of sorted) {
        let s = Math.max(err.span.start, pos);
        let e = Math.min(err.span.end, text.length);
        if (e <= s) {
          // zero-width span (e.g. error at end of input): mark the previous char
          if (text.length === 0) continue;
          s = Math.min(s, text.length - 1);
          e = s + 1;
          if (s < pos) continue;
        }
        hl.appendChild(document.createTextNode(text.slice(pos, s)));
        const m = document.createElement('mark');
        m.className = 'err';
        m.textContent = text.slice(s, e);
        m.dataset.msg = err.msg;
        hl.appendChild(m);
        pos = e;
      }
      hl.appendChild(document.createTextNode(text.slice(pos) + '\n'));
      marks = Array.from(hl.querySelectorAll('mark.err'));
    }

    ta.addEventListener('input', () => {
      errors = [];
      render();
      if (opts.onChange) opts.onChange(ta.value);
    });
    ta.addEventListener('scroll', () => {
      hl.style.transform = `translate(${-ta.scrollLeft}px, ${-ta.scrollTop}px)`;
    });
    ta.addEventListener('mousemove', (ev) => {
      for (const m of marks) {
        for (const r of m.getClientRects()) {
          if (ev.clientX >= r.left && ev.clientX <= r.right &&
              ev.clientY >= r.top && ev.clientY <= r.bottom) {
            showBubble(ev.clientX, ev.clientY, m.dataset.msg);
            return;
          }
        }
      }
      hideBubble();
    });
    ta.addEventListener('mouseleave', hideBubble);

    if (opts.initial) ta.value = opts.initial;
    render();

    return {
      getValue: () => ta.value,
      setValue(v) { ta.value = v; render(); },
      setErrors(errs) { errors = errs || []; render(); },
    };
  }

  MR.uiEditor = { makeEditor };
})();
