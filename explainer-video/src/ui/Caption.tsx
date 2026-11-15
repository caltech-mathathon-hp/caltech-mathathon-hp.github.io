/**
 * Captions (the narration) and the frame around every scene: the scene title top left, the toy
 * badge top right in part 2, captions centred at the bottom.
 */
import React from 'react';
import { useCurrentFrame } from 'remotion';
import { C, FONT, W, H } from '../theme/theme';
import { clamp01 } from '../lib/anim';
import type { CueTime } from '../script';

const MARK: Record<string, string> = {
  h: C.h,
  p: C.p,
  bond: '#b07a10',
  i0: C.items[0],
  i1: '#b07a10',
  i2: C.items[2],
  i3: C.items[3],
  pad: '#6f6f79',
  plug: '#a08c66',
  /** the two free edges of the front face, and other things to look at */
  free: C.accent,
};

/** "[[h:H]]'s" → coloured spans */
export function Marked({ text }: { text: string }) {
  const parts: React.ReactNode[] = [];
  const re = /\[\[([a-z0-9]+):([^\]]*)\]\]/g;
  let last = 0;
  let m: RegExpExecArray | null;
  let k = 0;
  while ((m = re.exec(text))) {
    if (m.index > last) parts.push(text.slice(last, m.index));
    parts.push(
      <span key={k++} style={{ color: MARK[m[1]] ?? C.fg, fontWeight: 600 }}>
        {m[2]}
      </span>,
    );
    last = m.index + m[0].length;
  }
  if (last < text.length) parts.push(text.slice(last));
  return <>{parts}</>;
}

export const CAPTION_TOP = 900;

export function Captions({ cues }: { cues: CueTime[] }) {
  const frame = useCurrentFrame();
  const cue = cues.find((c) => frame >= c.from && frame < c.to);
  if (!cue) return null;
  const fade = 7;
  const o = clamp01(Math.min((frame - cue.from) / fade, (cue.to - 2 - frame) / fade));
  const y = (1 - clamp01((frame - cue.from) / fade)) * 10;
  return (
    <div
      style={{
        position: 'absolute',
        left: 0,
        right: 0,
        top: CAPTION_TOP,
        height: H - CAPTION_TOP,
        display: 'flex',
        alignItems: 'flex-start',
        justifyContent: 'center',
        pointerEvents: 'none',
      }}
    >
      <div
        style={{
          maxWidth: 1600,
          padding: '0 60px',
          textAlign: 'center',
          fontFamily: FONT.serif,
          fontSize: 44,
          lineHeight: 1.32,
          color: C.fg,
          opacity: o,
          transform: `translateY(${y}px)`,
          textWrap: 'balance',
        }}
      >
        <Marked text={cue.text} />
      </div>
    </div>
  );
}

/** a soft band behind the captions, so 3D content never runs under the text */
export function CaptionBand() {
  return (
    <div
      style={{
        position: 'absolute',
        left: 0,
        right: 0,
        top: CAPTION_TOP - 50,
        bottom: 0,
        background: `linear-gradient(to bottom, ${C.bg}00 0px, ${C.bg}f2 50px, ${C.bg} 100%)`,
      }}
    />
  );
}

const PART_LABEL: Record<number, string> = { 1: 'The idea', 2: 'An example', 3: 'In general' };

/**
 * The header, top left. Symbols such as ⇒ come from a fallback font with a taller line box, which
 * would push the header down a few pixels in some scenes; they get line-height 0 so every title
 * sits on the same baseline.
 */
export function SceneTitle({ part, title, opacity = 1 }: { part: number; title: string; opacity?: number }) {
  if (!title) return null;
  return (
    <div style={{ position: 'absolute', left: 64, top: 48, fontFamily: FONT.sans, opacity, display: 'flex', alignItems: 'baseline', gap: 14 }}>
      <span style={{ fontSize: 22, fontWeight: 600, color: C.accent, letterSpacing: '0.06em', textTransform: 'uppercase' }}>{PART_LABEL[part] ?? ''}</span>
      <span style={{ fontSize: 22, color: C.fgSubtle }}>·</span>
      <span style={{ fontSize: 30, fontWeight: 600, color: C.fg }}>
        {title.split(/([^\x20-\x7e’]+)/).map((t, i) => (i % 2 ? <span key={i} style={{ lineHeight: 0 }}>{t}</span> : t))}
      </span>
    </div>
  );
}

export function ToyBadge({ opacity = 1 }: { opacity?: number }) {
  return (
    <div
      style={{
        position: 'absolute',
        right: 64,
        top: 44,
        fontFamily: FONT.sans,
        fontSize: 21,
        color: C.fgMuted,
        background: C.bgElev,
        border: `1.5px solid ${C.ruleStrong}`,
        borderRadius: 8,
        padding: '8px 16px',
        opacity,
        lineHeight: 1.35,
        textAlign: 'right',
      }}
    >
      <b style={{ color: C.fg }}>Our small cube</b>: side 12, not 80
      <br />
      2 strips, not 6, so no plugs
    </div>
  );
}

export const FULL: React.CSSProperties = { position: 'absolute', left: 0, top: 0, width: W, height: H };
