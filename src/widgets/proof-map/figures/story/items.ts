/**
 * Drawn lengths for the item pictures. No instance is meant: labels say u₁, u₂, … and B, never
 * numbers. Bins are drawn CAP nodes long; the packing drawn is bin 1 = {u₁, u₄}, bin 2 = {u₂, u₃},
 * so that consecutive items of the string can lie in different bins.
 */
export const ITEMS = [8, 6, 6, 4];
export const CAP = 12;
export const BIN_OF = [0, 1, 1, 0];

/** Items of bin b (0-based), as indices into ITEMS, in string order. */
export const inBin = (b: number) => ITEMS.map((_, k) => k).filter((k) => BIN_OF[k] === b);

/** A bar of `size` nodes cut into dominoes of two: start and width, in nodes. */
export const domino = (size: number) => Array.from({ length: size / 2 }, (_, i) => ({ x: 2 * i, w: 2 }));
