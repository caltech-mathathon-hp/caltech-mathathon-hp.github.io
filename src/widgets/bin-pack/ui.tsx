/** @jsxImportSource preact */
/**
 * Small pieces of the folding game's interface, copied from fold-game/FoldGame.tsx (which does
 * not export them) so that both games look and behave the same. They use the fg- classes of
 * fold-game/styles.css. Keep them in step with the originals.
 */
import { useEffect, useRef, useState } from 'preact/hooks';
import type { ComponentChildren } from 'preact';

/** a key sequence as <kbd> elements ("← →" → two keys) */
export function Keys({ k }: { k: string }) {
  return (
    <span class="fg-keys">
      {k.split(' ').map((p) => (
        <kbd>{p}</kbd>
      ))}
    </span>
  );
}

export interface ChoiceOption<T> {
  value: T;
  content: ComponentChildren;
  title?: string;
  aria?: string;
  cls?: string;
}

/**
 * One choice among a few, as a group of buttons with one tab stop (roving tabindex). The arrow
 * keys move between them; Enter or Space chooses (a toolbar, as for the levels).
 */
export function Choice<T extends string | number>(props: {
  class: string;
  labelledby?: string;
  value: T;
  options: ChoiceOption<T>[];
  onChange: (v: T) => void;
}) {
  const { options, value, onChange } = props;
  const refs = useRef<(HTMLButtonElement | null)[]>([]);
  const chosen = Math.max(
    0,
    options.findIndex((o) => o.value === value),
  );
  const [focusIdx, setFocusIdx] = useState(chosen);
  useEffect(() => setFocusIdx(chosen), [chosen, options.length]);
  const onKey = (e: KeyboardEvent, i: number) => {
    const last = options.length - 1;
    const to =
      e.key === 'ArrowRight' || e.key === 'ArrowDown'
        ? i === last ? 0 : i + 1
        : e.key === 'ArrowLeft' || e.key === 'ArrowUp'
          ? i === 0 ? last : i - 1
          : e.key === 'Home'
            ? 0
            : e.key === 'End'
              ? last
              : -1;
    if (to < 0) return;
    e.preventDefault();
    e.stopPropagation();
    setFocusIdx(to);
    refs.current[to]?.focus();
  };
  return (
    <div class={props.class} role="toolbar" aria-labelledby={props.labelledby}>
      {options.map((o, i) => {
        const on = o.value === value;
        return (
          <button
            type="button"
            ref={(el) => {
              refs.current[i] = el;
            }}
            class={`fg-opt${on ? ' is-on' : ''}${o.cls ? ` ${o.cls}` : ''}`}
            aria-pressed={on}
            aria-label={o.aria}
            title={o.title}
            tabIndex={i === focusIdx ? 0 : -1}
            onClick={() => {
              setFocusIdx(i);
              onChange(o.value);
            }}
            onKeyDown={(e) => onKey(e, i)}
          >
            {o.content}
          </button>
        );
      })}
    </div>
  );
}

/** an (i) with a short explanation on hover or focus */
export function Tip({ label, children }: { label: string; children: ComponentChildren }) {
  return (
    <span class="fg-tip" tabIndex={0} aria-label={label} role="button">
      <span class="fg-tip-i" aria-hidden="true">
        i
      </span>
      <span class="fg-tip-body" role="tooltip">
        {children}
      </span>
    </span>
  );
}

export function Icon({ d, fill }: { d: string; fill?: boolean }) {
  return (
    <svg class="fg-ico" viewBox="0 0 24 24" width="16" height="16" aria-hidden="true">
      <path
        d={d}
        fill={fill ? 'currentColor' : 'none'}
        stroke="currentColor"
        stroke-width="1.8"
        stroke-linecap="round"
        stroke-linejoin="round"
      />
    </svg>
  );
}

/** icon paths used by both games */
export const ICON = {
  undo: 'M9 14 4 9l5-5M4 9h10.5a5.5 5.5 0 0 1 0 11H11',
  reset: 'M3 12a9 9 0 1 0 3-6.7L3 8M3 3v5h5',
  next: 'm9 5 7 7-7 7',
  solve: 'M4 12h3l3-7 4 14 3-7h3',
  close: 'M6 6l12 12M18 6 6 18',
  keyboard:
    'M3 7.5A1.5 1.5 0 0 1 4.5 6h15A1.5 1.5 0 0 1 21 7.5v9a1.5 1.5 0 0 1-1.5 1.5h-15A1.5 1.5 0 0 1 3 16.5zM7 10h.01M11 10h.01M15 10h.01M8 14h8',
  no: 'M12 3a9 9 0 1 0 0 18 9 9 0 0 0 0-18zM5.6 5.6l12.8 12.8',
};
