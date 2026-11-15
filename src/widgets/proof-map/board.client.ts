/**
 * Behaviour of the proof board (ProofBoard.astro). Works for any number of boards on a page.
 *
 * Board:  a card opens the popup at its step. Arrow keys move focus between visible cards and group
 *         stacks by position. Groups (<details class="pb-group">) open in place; "Show all N steps"
 *         opens or closes them all; a group opens by itself when focus returns to a card inside it.
 * Popup:  one <dialog> holds every step; one is shown at a time. Previous / Next and ← → move in
 *         reading order without closing. ✕, Esc, a click on the backdrop or the browser's Back close it,
 *         and focus returns to the card of the step last shown.
 * URL:    #step-<map>-<step> opens the popup at that step; the hash follows the step shown and is
 *         cleared on close. Opening from a card adds one history entry, so Back closes the popup.
 */

type Step = { id: string; el: HTMLElement; title: string; lane: string; n: number; card: HTMLElement | null };

function initBoard(root: HTMLElement) {
  const dialog = root.querySelector<HTMLDialogElement>('dialog.pb-dialog');
  const scroller = root.querySelector<HTMLElement>('.pb-dlg-scroll');
  if (!dialog || !scroller) return;
  const steps: Step[] = [...dialog.querySelectorAll<HTMLElement>('article.pb-step')].map((el) => ({
    id: el.id,
    el,
    title: el.dataset.title ?? '',
    lane: el.dataset.lane ?? '',
    n: Number(el.dataset.n),
    card: root.querySelector<HTMLElement>(`.pb-card[data-step="${CSS.escape(el.id)}"]`),
  }));
  const total = steps.length;
  const indexOf = (id: string) => steps.findIndex((s) => s.id === id);
  const $ = <T extends Element>(sel: string) => dialog.querySelector<T>(sel)!;
  const whereLane = $<HTMLElement>('[data-where-lane]');
  const whereN = $<HTMLElement>('[data-where-n]');
  const prevBtn = $<HTMLButtonElement>('.pb-prev');
  const nextBtn = $<HTMLButtonElement>('.pb-next');
  const live = $<HTMLElement>('[data-live]');
  const minis = [...dialog.querySelectorAll<SVGElement>('.pb-mini [data-goto]')];
  let cur = -1;

  /* Groups of steps on the board (<details class="pb-group">), and the button that opens them all. */
  const groups = [...root.querySelectorAll<HTMLDetailsElement>('details.pb-group')];
  const openGroupOf = (el: Element | null | undefined) => {
    const g = el?.closest<HTMLDetailsElement>('details.pb-group');
    if (g && !g.open) g.open = true;
  };
  const expandBtn = root.querySelector<HTMLButtonElement>('[data-expand]');
  if (expandBtn && groups.length) {
    const label = () => {
      expandBtn.textContent = (groups.every((g) => g.open) ? expandBtn.dataset.less : expandBtn.dataset.more) ?? '';
    };
    expandBtn.addEventListener('click', () => {
      const all = groups.every((g) => g.open);
      groups.forEach((g) => (g.open = !all));
      label();
    });
    groups.forEach((g) => g.addEventListener('toggle', label));
    expandBtn.hidden = false;
    label();
  }

  /* "The details": one state for every step, so a reader who checks proofs keeps them open. */
  const backs = [...dialog.querySelectorAll<HTMLDetailsElement>('details.pb-back')];
  backs.forEach((d) =>
    d.addEventListener('toggle', () => {
      backs.forEach((o) => {
        if (o !== d && o.open !== d.open) o.open = d.open;
      });
    }),
  );

  const setNav = (btn: HTMLButtonElement, s: Step | undefined, last = false) => {
    const t = btn.querySelector<HTMLElement>('[data-go-title]')!;
    btn.classList.toggle('pb-go-done', last);
    if (last) {
      btn.disabled = false;
      t.textContent = 'Back to the board';
      return;
    }
    btn.disabled = !s;
    t.textContent = s ? `${s.n} ${s.title}` : '';
  };

  /** Show step i inside the open (or opening) dialog. dir: +1 next, -1 previous, 0 jump. */
  function show(i: number, dir = 0) {
    if (i === cur) return;
    const old = steps[cur];
    const hadFocus = old?.el.contains(document.activeElement);
    old?.el.classList.remove('is-active');
    cur = i;
    const s = steps[i];
    s.el.dataset.enter = dir > 0 ? 'next' : dir < 0 ? 'prev' : '';
    s.el.classList.add('is-active');
    scroller!.scrollTop = 0;
    dialog!.setAttribute('aria-labelledby', `${s.id}-title`);
    dialog!.dataset.d = s.el.className.match(/pb-d(\d)/)?.[1] ?? '1';
    whereLane.textContent = s.lane;
    whereN.textContent = `${s.n} of ${total}`;
    minis.forEach((m) => m.classList.toggle('is-cur', m.dataset.goto === s.id));
    setNav(prevBtn, steps[i - 1]);
    setNav(nextBtn, steps[i + 1], i === total - 1);
    // Keep focus inside the dialog when the element that had it disappears or is disabled.
    const a = document.activeElement;
    if (hadFocus || (a instanceof HTMLButtonElement && a.disabled)) {
      if (a === prevBtn && prevBtn.disabled) nextBtn.focus();
      else focusTitle();
    }
  }

  const focusTitle = () => steps[cur]?.el.querySelector<HTMLElement>('.pb-step-title')?.focus({ preventScroll: true });

  const announce = (s: Step) => {
    live.textContent = '';
    window.setTimeout(() => (live.textContent = `Step ${s.n} of ${total}: ${s.title}. ${s.lane}.`), 30);
  };

  const ownsHash = () => indexOf(decodeURIComponent(location.hash.slice(1))) >= 0;
  const setHash = (id: string) => history.replaceState(history.state, '', `#${id}`);

  /** Open the popup at step i. push: add a history entry (opened from a card). */
  function open(i: number, push: boolean) {
    show(i);
    if (push) history.pushState({ pbOpen: true }, '', `#${steps[i].id}`);
    else {
      // Opened from the URL: keep the step's card behind the popup (the browser's own jump to
      // the fragment would land elsewhere, since the step lives in the dialog).
      const reveal = () => {
        openGroupOf(steps[cur]?.card);
        steps[cur]?.card?.scrollIntoView({ block: 'center' });
      };
      reveal();
      if (document.readyState !== 'complete') window.addEventListener('load', () => setTimeout(reveal), { once: true });
    }
    if (!dialog!.open) dialog!.showModal();
    focusTitle();
  }

  function go(delta: number) {
    if (cur < 0) return;
    if (delta > 0 && cur === total - 1) return closeDialog();
    const j = cur + delta;
    if (j < 0 || j >= total) return;
    show(j, delta);
    setHash(steps[j].id);
    announce(steps[j]);
  }

  let pendingFocus: HTMLElement | null = null;
  const flushFocus = () => {
    if (pendingFocus) returnTo(pendingFocus);
    pendingFocus = null;
  };
  const returnTo = (card: HTMLElement | null) => {
    if (!card) return;
    openGroupOf(card);
    card.focus();
    card.classList.remove('is-back');
    void card.offsetWidth; // restart the highlight
    card.classList.add('is-back');
    window.setTimeout(() => card.classList.remove('is-back'), 1800);
  };

  /** After the dialog closed: clear the hash and return focus to the card of the step last shown. */
  function afterClose() {
    if (cur < 0) return; // already done
    const card = steps[cur]?.card ?? null;
    steps[cur]?.el.classList.remove('is-active');
    cur = -1;
    if (ownsHash()) {
      if (history.state?.pbOpen) {
        // Undo our history entry; focus the card once the browser has restored the page.
        pendingFocus = card;
        history.back();
        window.setTimeout(flushFocus, 400); // in case popstate never comes
        return;
      }
      history.replaceState(history.state, '', location.pathname + location.search);
    }
    returnTo(card);
  }
  // Esc closes the dialog natively; every other way goes through closeDialog, which does not wait
  // for the asynchronous close event.
  dialog.addEventListener('close', afterClose);
  const closeDialog = () => {
    if (dialog!.open) dialog!.close();
    afterClose();
  };

  /** Follow the URL: open, move or close to match the hash. */
  function sync(fromNavigation: boolean) {
    let i = indexOf(decodeURIComponent(location.hash.slice(1)));
    if (i >= 0 && pendingFocus) {
      // Our own Back after a close landed on another step's URL (a link from step to step): stay closed.
      history.replaceState(history.state, '', location.pathname + location.search);
      i = -1;
    }
    if (i >= 0) {
      if (fromNavigation && !history.state) history.replaceState({ pbOpen: true }, '');
      if (!dialog!.open) open(i, false);
      else if (i !== cur) show(i), announce(steps[i]);
    } else if (dialog!.open) closeDialog();
    // After our own history.back(): the browser restores the scroll position right after popstate,
    // so focus the card in a later task.
    if (pendingFocus && i < 0) window.setTimeout(flushFocus);
  }
  window.addEventListener('popstate', () => sync(true));
  window.addEventListener('hashchange', () => sync(true));

  /* Cards open the popup. Modified clicks keep their default (new tab at the step). */
  root.addEventListener('click', (ev) => {
    const me = ev as MouseEvent;
    const card = (ev.target as Element).closest<HTMLAnchorElement>('a.pb-card');
    if (!card || me.button !== 0 || me.metaKey || me.ctrlKey || me.shiftKey || me.altKey) return;
    const i = indexOf(card.dataset.step ?? '');
    if (i < 0) return;
    ev.preventDefault();
    open(i, true);
  });

  /* Inside the popup: buttons, mini board, backdrop. */
  let downOnBackdrop = false;
  dialog.addEventListener('pointerdown', (ev) => (downOnBackdrop = ev.target === dialog));
  dialog.addEventListener('click', (ev) => {
    const t = ev.target as Element;
    if (t === dialog) {
      if (downOnBackdrop) closeDialog();
      return;
    }
    if (t.closest('[data-close]')) return closeDialog();
    const goBtn = t.closest<HTMLElement>('[data-go]');
    if (goBtn) return go(Number(goBtn.dataset.go));
    const mini = t.closest<SVGElement>('[data-goto]');
    if (mini) {
      const j = indexOf(mini.dataset.goto ?? '');
      if (j >= 0 && j !== cur) {
        show(j, j > cur ? 1 : -1);
        setHash(steps[j].id);
        announce(steps[j]);
      }
    }
  });

  dialog.addEventListener('keydown', (ev) => {
    if (ev.altKey || ev.ctrlKey || ev.metaKey || ev.shiftKey) return;
    if (ev.key !== 'ArrowLeft' && ev.key !== 'ArrowRight') return;
    const t = ev.target as HTMLElement;
    if (t.closest('input, textarea, select, [contenteditable=""], [contenteditable="true"]')) return;
    ev.preventDefault();
    go(ev.key === 'ArrowRight' ? 1 : -1);
  });

  /* Arrow keys on the board move focus to the nearest visible card or group in that direction. */
  const TARGETS = '.pb-card, .pb-group-sum';
  root.querySelector('.pb-board')?.addEventListener('keydown', (e) => {
    const ev = e as KeyboardEvent;
    const from = (ev.target as Element).closest<HTMLElement>(TARGETS);
    const cards = [...root.querySelectorAll<HTMLElement>(`.pb-board :is(${TARGETS})`)].filter(
      (el) => el.getClientRects().length > 0,
    );
    if (!from || ev.altKey || ev.ctrlKey || ev.metaKey || ev.shiftKey) return;
    let to: HTMLElement | undefined;
    if (ev.key === 'Home') to = cards[0];
    else if (ev.key === 'End') to = cards[cards.length - 1];
    else {
      const dirs: Record<string, [number, number]> = {
        ArrowUp: [0, -1],
        ArrowDown: [0, 1],
        ArrowLeft: [-1, 0],
        ArrowRight: [1, 0],
      };
      const d = dirs[ev.key];
      if (!d) return;
      const c = (el: Element) => {
        const r = el.getBoundingClientRect();
        return [r.left + r.width / 2, r.top + r.height / 2];
      };
      const [x0, y0] = c(from);
      let best = Infinity;
      for (const card of cards) {
        if (card === from) continue;
        const [x, y] = c(card);
        const along = (x - x0) * d[0] + (y - y0) * d[1];
        if (along <= 8) continue;
        const across = Math.abs((x - x0) * d[1] + (y - y0) * d[0]);
        const score = along + 2 * across;
        if (score < best) (best = score), (to = card);
      }
    }
    if (!to) return;
    ev.preventDefault();
    to.focus();
  });

  sync(false);
}

export function initBoards() {
  document.querySelectorAll<HTMLElement>('.pb').forEach((root) => {
    if (root.dataset.pbReady) return;
    root.dataset.pbReady = '1';
    initBoard(root);
  });
}
