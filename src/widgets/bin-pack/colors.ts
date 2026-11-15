/**
 * Item u of an instance is drawn in var(--item-(u mod 4 + 1)) everywhere: in the game, and in the
 * reduction viewer. These are the colours the proof figures give the running example (items 6, 2,
 * 8, 4). Instances with more than four items repeat the colours with a pattern: items 5 to 8 are
 * striped, items 9 to 12 dotted (class names bp-pat-1 and bp-pat-2, see styles.css).
 */
export const itemColor = (u: number) => `var(--item-${(u % 4) + 1})`;
export const itemPattern = (u: number) => Math.floor(u / 4) % 3;
export const PAD_COLOR = 'var(--item-pad)';
