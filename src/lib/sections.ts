import { getCollection, type CollectionEntry } from 'astro:content';

export type Section = CollectionEntry<'sections'>;

/** All sections that are listed (everything except `hidden`), in order. */
export async function listedSections(): Promise<Section[]> {
  const all = await getCollection('sections', (s) => s.data.status !== 'hidden');
  return all.sort((a, b) => a.data.order - b.data.order);
}
