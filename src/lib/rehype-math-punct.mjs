/**
 * Keeps punctuation after inline math on the same line: "… not by $B$." could otherwise wrap
 * with the period alone at the start of the next line. Runs after rehype-katex and wraps the
 * formula and the punctuation that follows it in <span class="math-nobr">.
 */
const PUNCT = /^[.,;:!?)\]’”'"]+/;

const isInlineMath = (n) => {
  if (n?.type !== 'element') return false;
  const c = n.properties?.className;
  const list = Array.isArray(c) ? c : typeof c === 'string' ? c.split(' ') : [];
  return list.includes('katex') || list.includes('math-inline');
};

function walk(node) {
  const kids = node.children;
  if (!kids) return;
  for (let i = 0; i < kids.length; i++) {
    const n = kids[i];
    const next = kids[i + 1];
    if (isInlineMath(n) && next?.type === 'text') {
      const m = next.value.match(PUNCT);
      if (m) {
        const rest = next.value.slice(m[0].length);
        const wrap = {
          type: 'element',
          tagName: 'span',
          properties: { className: ['math-nobr'] },
          children: [n, { type: 'text', value: m[0] }],
        };
        kids.splice(i, 2, wrap, ...(rest ? [{ type: 'text', value: rest }] : []));
        continue;
      }
    }
    walk(n);
  }
}

export default function rehypeMathPunct() {
  return (tree) => walk(tree);
}
