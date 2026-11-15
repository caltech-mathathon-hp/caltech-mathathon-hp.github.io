/**
 * Build-time renderer for one line of card text (a card's `caption`): KaTeX math, HP strings,
 * emphasis. Used by ProofBoard.astro, so captions need no MDX.
 *
 *   $…$ / $$…$$     KaTeX math
 *   `PHHP(PHP)^k`    an HP string: coloured letters, ^k or ^{…} as a (math) superscript
 *   *em*, **strong**
 *
 * Styles: .pb-seq, .pb-H, .pb-P, .pb-seq-exp in board.css.
 */
import katex from 'katex';

const esc = (s: string) =>
  s.replace(/[&<>"]/g, (c) => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' })[c]!);

const tex = (src: string, display = false) =>
  katex.renderToString(src, { displayMode: display, throwOnError: false, strict: false });

const emphasis = (s: string) =>
  s.replace(/\*\*([^*]+)\*\*/g, '<strong>$1</strong>').replace(/\*([^*\s][^*]*)\*/g, '<em>$1</em>');

/** An HP string: H and P coloured, ^x or ^{…} as a superscript rendered by KaTeX. */
function seq(src: string): string {
  let out = '';
  for (let i = 0; i < src.length; i++) {
    const c = src[i];
    if (c === '^') {
      let e: string;
      if (src[i + 1] === '{') {
        let depth = 0;
        let j = i + 1;
        for (; j < src.length; j++) {
          if (src[j] === '{') depth++;
          else if (src[j] === '}' && --depth === 0) break;
        }
        e = src.slice(i + 2, j);
        i = j;
      } else {
        let j = i + 1;
        if (/[0-9]/.test(src[j] ?? '')) while (/[0-9]/.test(src[j] ?? '')) j++;
        else j++;
        e = src.slice(i + 1, j);
        i = j - 1;
      }
      out += `<sup class="pb-seq-exp">${tex(e)}</sup>`;
    } else if (c === 'H' || c === 'P') out += `<span class="pb-${c}">${c}</span>`;
    else out += esc(c);
  }
  return `<span class="pb-seq">${out}</span>`;
}

/** One line of text: math, HP strings, emphasis. Returns HTML. */
export function inline(s: string): string {
  const re = /\$\$([\s\S]+?)\$\$|\$([^$]+?)\$|`([^`]+)`/g;
  let out = '';
  let last = 0;
  let m: RegExpExecArray | null;
  while ((m = re.exec(s))) {
    out += emphasis(esc(s.slice(last, m.index)));
    if (m[1] !== undefined) out += tex(m[1], true);
    else if (m[2] !== undefined) out += tex(m[2]);
    else out += seq(m[3]);
    last = re.lastIndex;
  }
  return out + emphasis(esc(s.slice(last)));
}

/** The same line as plain text (for the mini board's tooltips). */
export function plain(s: string): string {
  return s
    .replace(/\$([^$]+)\$/g, (_, t: string) => t.replace(/\\[a-zA-Z]+/g, '').replace(/[{}_^\\]/g, ''))
    .replace(/`([^`]+)`/g, '$1')
    .replace(/\*/g, '')
    .replace(/\s+/g, ' ')
    .trim();
}
