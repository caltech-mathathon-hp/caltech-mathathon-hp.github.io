/**
 * Pictures that a step card can name in its frontmatter (`figure: <key>`).
 * Add a figure: write an .astro SVG in this folder (or story/) using the pmf-* classes of fig.css
 * and the labels of notation.ts, then register it here with the props to render it with.
 * Inside a popup (the MDX body of a step) figures can also be imported directly.
 *
 * The cards of the original proof use, in board order: bl-instance (problems), bl-cube,
 * bl-string, bl-blocks (local rules), bl-skeleton, bl-edge-rods (free edges), bl-walls,
 * bl-packing, bl-face-order (frame), bl-build-walls, bl-padding (fill strips), bl-crossbar,
 * bl-linkers, bl-iff (conclusion).
 */
import Instance from './story/Instance.astro';
import Chain from './story/Chain.astro';
import Cube from './story/Cube.astro';
import Blocks from './story/Blocks.astro';
import FrontFace from './story/FrontFace.astro';
import Skeleton from './Skeleton.astro';
import EdgeRods from './EdgeRods.astro';
import Padding from './Padding.astro';
import FaceOrder from './FaceOrder.astro';
import Crossbar from './Crossbar.astro';
import Linkers from './Linkers.astro';
import RodAndRibbon from './RodAndRibbon.astro';
import SixPs from './SixPs.astro';
import BuildWalls from './BuildWalls.astro';
import Equivalence from './Equivalence.astro';

// eslint-disable-next-line @typescript-eslint/no-explicit-any
export type BoardFigure = { component: any; props?: Record<string, unknown> };

export const figures: Record<string, BoardFigure> = {
  'bl-instance': { component: Instance },
  'bl-cube': { component: Cube },
  'bl-string': { component: Chain },
  'bl-blocks': { component: Blocks },
  'bl-skeleton': { component: Skeleton },
  'bl-edge-rods': { component: EdgeRods },
  'bl-walls': { component: FrontFace },
  'bl-packing': { component: FrontFace, props: { filled: true } },
  'bl-face-order': { component: FaceOrder },
  'bl-build-walls': { component: BuildWalls },
  'bl-padding': { component: Padding },
  'bl-crossbar': { component: Crossbar },
  'bl-linkers': { component: Linkers },
  'bl-iff': { component: Equivalence },
  'bl-rod-ribbon': { component: RodAndRibbon },
  'bl-six-ps': { component: SixPs },
};
