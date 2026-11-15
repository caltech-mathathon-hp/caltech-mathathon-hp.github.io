/**
 * The running example of the whole site: items of sizes 6, 2, 8 and 4 in K = 2 bins of size
 * B = 10, packed as 6 + 4 | 2 + 8. The bin packing game's level "The running example"
 * (widgets/bin-pack/levels/running-example.json) and the explainer video use the same instance in
 * the same colours: item k is var(--item-<k+1>). For it q = 2·max(2, ⌈10^{1/3}⌉) = 6 and the cube
 * has side n = 80. Figures name an item by its size on a chip, as the game does; general
 * quantities (B, K, q, n, T) keep their letters.
 */
export const ITEMS = [6, 2, 8, 4];
export const CAP = 10;
export const BIN_OF = [0, 1, 1, 0];

/** Items of bin b (0-based), as indices into ITEMS, in string order. */
export const inBin = (b: number) => ITEMS.map((_, k) => k).filter((k) => BIN_OF[k] === b);

/** A bar of `size` nodes cut into dominoes of two: start and width, in nodes. */
export const domino = (size: number) => Array.from({ length: size / 2 }, (_, i) => ({ x: 2 * i, w: 2 }));
