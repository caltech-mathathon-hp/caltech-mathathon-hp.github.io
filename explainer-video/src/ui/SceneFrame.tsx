/** The frame every scene sits in: background, title, toy badge (part 2), caption band, captions. */
import React from 'react';
import { AbsoluteFill, useCurrentFrame } from 'remotion';
import { C } from '../theme/theme';
import { Captions, CaptionBand, SceneTitle, ToyBadge } from './Caption';
import { clamp01 } from '../lib/anim';
import { TIMELINE, type SceneTime } from '../script';

/**
 * Scenes that pick up the previous scene's last picture exactly: they cut in without a fade. Every
 * other cut dips through the background: the old picture fades out over its last frames, then the
 * new one fades in, so no picture ever vanishes in one frame.
 */
const CONTINUES = new Set(['local', 'frame', 'walls', 'padding', 'choice']);
const FADE_IN = 8;
const FADE_OUT = 8;
/** the toy badge marks the example; "instance" introduces the toy itself and "end" is about the general proof */
const hasBadge = (s?: SceneTime) => !!s && s.part === 2 && s.id !== 'instance' && s.id !== 'end';

export function SceneFrame({ scene, children, badge, band = true }: { scene: SceneTime; children?: React.ReactNode; badge?: boolean; band?: boolean }) {
  const frame = useCurrentFrame();
  const k = TIMELINE.findIndex((s) => s.id === scene.id);
  const prev = TIMELINE[k - 1];
  const next = TIMELINE[k + 1];
  /** 1 until the last FADE_OUT frames of the scene, then down to 0 on its last frame */
  const out = clamp01((scene.duration - 1 - frame) / FADE_OUT);
  const pictureIn = CONTINUES.has(scene.id) ? 1 : clamp01(frame / FADE_IN);
  const pictureOut = next && !CONTINUES.has(next.id) ? out : 1;
  // the title changes at every cut: the old one fades out, the new one fades in
  const titleO = Math.min(clamp01(frame / 12), next ? out : 1);
  const showBadge = badge ?? hasBadge(scene);
  const badgeO = Math.min(hasBadge(prev) ? 1 : clamp01(frame / 12), hasBadge(next) ? 1 : out);
  return (
    <AbsoluteFill style={{ background: C.bg, overflow: 'hidden' }}>
      <AbsoluteFill style={{ opacity: Math.min(pictureIn, pictureOut) }}>{children}</AbsoluteFill>
      {band && <CaptionBand />}
      <SceneTitle part={scene.part} title={scene.title} opacity={titleO} />
      {showBadge && <ToyBadge opacity={badgeO} />}
      <Captions cues={scene.cueTimes} />
    </AbsoluteFill>
  );
}
