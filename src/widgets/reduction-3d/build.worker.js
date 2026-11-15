/**
 * Builds a string and its fold off the main thread, so that the page stays responsive while the
 * big presets (n = 80, a few seconds) are built. reduction.client.js posts
 * { id, construction: 'bl' | 'edge', K, B, sizes, given } and gets back { id, res } or { id, error }.
 * The result is plain data (typed arrays, arrays, numbers), so it is copied as it is.
 */
import * as BLC from './construction.js';
import * as EC from './edge-construction.js';

self.onmessage = (e) => {
  const { id, construction, K, B, sizes, given } = e.data;
  const C = construction === 'edge' ? EC : BLC;
  try {
    self.postMessage({ id, res: C.build(K, B, sizes, given) });
  } catch (err) {
    self.postMessage({ id, error: String((err && err.message) || err) });
  }
};
