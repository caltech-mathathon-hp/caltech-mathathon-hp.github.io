/** scene id → component. Each scene lives in its own file, so scenes can be built independently. */
import type React from 'react';
import type { SceneTime } from '../script';
import Title from './Title';
import Fold from './Fold';
import Plan from './Plan';
import CubeShape from './CubeShape';
import Local from './Local';
import Frame from './Frame';
import Walls from './Walls';
import Padding from './Padding';
import Choice from './Choice';
import Linkers from './Linkers';
import Instance from './Instance';
import StringScene from './StringScene';
import Forward from './Forward';
import Backward from './Backward';
import NoFit from './NoFit';
import End from './End';

export type SceneComponent = React.FC<{ scene: SceneTime }>;

export const SCENE_COMPONENTS: Record<string, SceneComponent> = {
  title: Title,
  fold: Fold,
  plan: Plan,
  cube: CubeShape,
  local: Local,
  frame: Frame,
  walls: Walls,
  padding: Padding,
  choice: Choice,
  linkers: Linkers,
  instance: Instance,
  string: StringScene,
  forward: Forward,
  backward: Backward,
  no: NoFit,
  end: End,
};
