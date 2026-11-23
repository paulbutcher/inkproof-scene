/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Scene.Dash
import Inkproof.Scene.DisplayList
import Inkproof.Float.RatLemmas

namespace Inkproof.Scene

inductive Theme where
  | light
  | dark
  deriving DecidableEq, Repr

/-- How a series' line is broken up; `Dash.pattern` gives the pattern `compileLine` draws it with. -/
inductive Dash where
  | solid
  | dashed
  | dotted
  deriving DecidableEq, Repr

/-- The pattern for a dash, in units of `unit` along the line (typically the line's width): none for
a solid line. -/
def Dash.pattern (unit : Rat) : Dash → Option DashPattern
  | .solid => none
  | .dashed => some ⟨4 * unit, 3 * unit⟩
  | .dotted => some ⟨unit, 2 * unit⟩

theorem Dash.pattern_solid (unit : Rat) : Dash.solid.pattern unit = none := rfl

theorem Dash.pattern_dashed (unit : Rat) : Dash.dashed.pattern unit = some ⟨4 * unit, 3 * unit⟩ := rfl

theorem Dash.pattern_dotted (unit : Rat) : Dash.dotted.pattern unit = some ⟨unit, 2 * unit⟩ := rfl

/-- Everything that tells one series from another: a series is identifiable by its marker and dash
without its colour. -/
structure SeriesStyle where
  color : Color := Color.black
  marker : MarkerShape := .circle
  dash : Dash := .solid
  deriving DecidableEq, Repr

namespace Color

private abbrev clamp01 (x : Rat) : Rat := Inkproof.Float.clamp 0 1 x

private def channel (x : Rat) : UInt8 :=
  UInt8.ofNat (((clamp01 x) * 255 + 1 / 2).floor.toNat)

private def chroma (s l : Rat) : Rat :=
  (1 - (if 2 * l - 1 < 0 then 1 - 2 * l else 2 * l - 1)) * clamp01 s

/-- The unrounded red, green and blue, each from 0 to 1, of the colour with hue `h` in degrees
(wrapped round the circle), saturation `s` and lightness `l`, the last two clamped to 0 to 1. -/
def hslChannels (h s l : Rat) : Rat × Rat × Rat :=
  let l := clamp01 l
  let c := chroma s l
  let hp := h / 60
  let f := hp - (hp.floor : Rat)
  let x := c * (if (hp.floor % 2 : Int) = 0 then f else 1 - f)
  let m := l - c / 2
  match (hp.floor % 6 : Int).toNat with
  | 0 => (c + m, x + m, m)
  | 1 => (x + m, c + m, m)
  | 2 => (m, c + m, x + m)
  | 3 => (m, x + m, c + m)
  | 4 => (x + m, m, c + m)
  | _ => (c + m, m, x + m)

/-- The colour with hue `h` in degrees, saturation `s`, lightness `l` and alpha `a`, each channel
rounded half up from its exact value; saturation, lightness and alpha are clamped to 0 to 1. -/
def ofHsl (h s l : Rat) (a : Rat := 1) : Color :=
  let (r, g, b) := hslChannels h s l
  ⟨channel r, channel g, channel b, channel a⟩

private theorem clamp01_zero : clamp01 0 = 0 := by
  rw [clamp01, Inkproof.Float.rat_clamp_eq_max_min (by grind)]; grind

private theorem clamp01_one : clamp01 1 = 1 := by
  rw [clamp01, Inkproof.Float.rat_clamp_eq_max_min (by grind)]; grind

private theorem channel_of_floor {x : Rat} {n : Nat} (h1 : (n : Rat) ≤ clamp01 x * 255 + 1 / 2)
    (h2 : clamp01 x * 255 + 1 / 2 < n + 1) : channel x = UInt8.ofNat n := by
  have a : (n : Int) ≤ (clamp01 x * 255 + 1 / 2).floor := Rat.le_floor_iff.2 (by exact_mod_cast h1)
  have b : (clamp01 x * 255 + 1 / 2).floor < (n : Int) + 1 := Rat.floor_lt_iff.2 (by exact_mod_cast h2)
  have : (clamp01 x * 255 + 1 / 2).floor.toNat = n := by omega
  simp [channel, this]

private theorem channel_zero : channel 0 = 0 :=
  channel_of_floor (n := 0) (by rw [clamp01_zero]; grind) (by rw [clamp01_zero]; grind)

private theorem channel_one : channel 1 = 255 :=
  channel_of_floor (n := 255) (by rw [clamp01_one]; grind) (by rw [clamp01_one]; grind)

private theorem chroma_zero_l (s : Rat) : chroma s 0 = 0 := by
  unfold chroma; split <;> grind

private theorem chroma_one_l (s : Rat) : chroma s 1 = 0 := by
  unfold chroma; split <;> grind

private theorem chroma_zero_s (l : Rat) : chroma 0 l = 0 := by
  unfold chroma; rw [clamp01_zero]; simp

theorem hslChannels_lightness_zero (h s : Rat) : hslChannels h s 0 = (0, 0, 0) := by
  unfold hslChannels
  simp only [clamp01_zero, chroma_zero_l]
  split <;> grind

theorem hslChannels_lightness_one (h s : Rat) : hslChannels h s 1 = (1, 1, 1) := by
  unfold hslChannels
  simp only [clamp01_one, chroma_one_l]
  split <;> grind

theorem hslChannels_saturation_zero (h l : Rat) :
    (hslChannels h 0 l).1 = (hslChannels h 0 l).2.1 ∧
      (hslChannels h 0 l).2.1 = (hslChannels h 0 l).2.2 := by
  unfold hslChannels
  simp only [chroma_zero_s]
  split <;> grind

/-- Lightness 0 is black whatever the hue and saturation. -/
theorem ofHsl_lightness_zero (h s a : Rat) :
    (ofHsl h s 0 a).r = 0 ∧ (ofHsl h s 0 a).g = 0 ∧ (ofHsl h s 0 a).b = 0 := by
  simp [ofHsl, hslChannels_lightness_zero, channel_zero]

/-- Lightness 1 is white whatever the hue and saturation. -/
theorem ofHsl_lightness_one (h s a : Rat) :
    (ofHsl h s 1 a).r = 255 ∧ (ofHsl h s 1 a).g = 255 ∧ (ofHsl h s 1 a).b = 255 := by
  simp [ofHsl, hslChannels_lightness_one, channel_one]

/-- Saturation 0 is a grey: the three colour channels agree. -/
theorem ofHsl_saturation_zero (h l a : Rat) :
    (ofHsl h 0 l a).r = (ofHsl h 0 l a).g ∧ (ofHsl h 0 l a).g = (ofHsl h 0 l a).b := by
  have := hslChannels_saturation_zero h l
  unfold ofHsl
  simp only [this.1, this.2, and_self]

/-- Each channel of `ofHsl` is the unrounded channel clamped to 0 to 1, scaled to 255 and rounded half
up; alpha likewise. -/
theorem ofHsl_eq (h s l a : Rat) :
    (ofHsl h s l a).r.toNat = ((Inkproof.Float.clamp 0 1 (hslChannels h s l).1 * 255 + 1 / 2).floor.toNat) % 256 ∧
    (ofHsl h s l a).g.toNat = ((Inkproof.Float.clamp 0 1 (hslChannels h s l).2.1 * 255 + 1 / 2).floor.toNat) % 256 ∧
    (ofHsl h s l a).b.toNat = ((Inkproof.Float.clamp 0 1 (hslChannels h s l).2.2 * 255 + 1 / 2).floor.toNat) % 256 ∧
    (ofHsl h s l a).a.toNat = ((Inkproof.Float.clamp 0 1 a * 255 + 1 / 2).floor.toNat) % 256 := by
  simp [ofHsl, channel, clamp01]

-- Contrast and luminance are Float computations (sRGB linearisation uses a real power), which Lean
-- cannot reason about, so the palettes' contrast is checked by tests instead of proved.

/-- The WCAG relative luminance of an opaque colour. -/
def luminance (c : Color) : Float :=
  let lin (v : UInt8) : Float :=
    let s := v.toNat.toFloat / 255
    if s ≤ 0.04045 then s / 12.92 else Float.pow ((s + 0.055) / 1.055) 2.4
  0.2126 * lin c.r + 0.7152 * lin c.g + 0.0722 * lin c.b

/-- The WCAG contrast ratio between two colours, from 1 (identical) to 21. -/
def contrast (a b : Color) : Float :=
  let la := a.luminance
  let lb := b.luminance
  (max la lb + 0.05) / (min la lb + 0.05)

end Color

namespace Theme

def background : Theme → Color
  | .light => ⟨255, 255, 255, 255⟩
  | .dark => ⟨18, 18, 18, 255⟩

def text : Theme → Color
  | .light => ⟨33, 33, 33, 255⟩
  | .dark => ⟨238, 238, 238, 255⟩

/-- Six series, each differing from every other in colour and, independently, in marker and dash. -/
def series : Theme → Array SeriesStyle
  | .light =>
    #[⟨⟨0, 90, 181, 255⟩, .circle, .solid⟩, ⟨⟨178, 74, 0, 255⟩, .square, .solid⟩,
      ⟨⟨0, 122, 94, 255⟩, .circle, .dashed⟩, ⟨⟨156, 39, 176, 255⟩, .square, .dashed⟩,
      ⟨⟨134, 106, 0, 255⟩, .circle, .dotted⟩, ⟨⟨198, 40, 40, 255⟩, .square, .dotted⟩]
  | .dark =>
    #[⟨⟨100, 168, 255, 255⟩, .circle, .solid⟩, ⟨⟨255, 158, 74, 255⟩, .square, .solid⟩,
      ⟨⟨64, 204, 160, 255⟩, .circle, .dashed⟩, ⟨⟨206, 147, 216, 255⟩, .square, .dashed⟩,
      ⟨⟨230, 200, 70, 255⟩, .circle, .dotted⟩, ⟨⟨255, 120, 120, 255⟩, .square, .dotted⟩]

/-- The style of the `i`th series; beyond the palette's size styles repeat. -/
def seriesStyle (t : Theme) (i : Nat) : SeriesStyle :=
  let s := t.series
  s[i % s.size]?.getD ⟨t.text, .circle, .solid⟩

theorem series_size (t : Theme) : t.series.size = 6 := by
  cases t <;> rfl

theorem seriesStyle_of_lt (t : Theme) {i : Nat} (h : i < 6) :
    t.seriesStyle i = t.series[i]'(by rw [series_size]; exact h) := by
  have hs := series_size t
  simp only [seriesStyle, hs, Nat.mod_eq_of_lt h]
  rw [Array.getElem?_eq_getElem (by rw [hs]; exact h)]
  rfl

theorem seriesStyle_add_size (t : Theme) (i : Nat) : t.seriesStyle (i + 6) = t.seriesStyle i := by
  have h : (i + 6) % 6 = i % 6 := by omega
  simp only [seriesStyle, series_size, h]

theorem background_light : Theme.light.background = ⟨255, 255, 255, 255⟩ := rfl

theorem background_dark : Theme.dark.background = ⟨18, 18, 18, 255⟩ := rfl

theorem text_light : Theme.light.text = ⟨33, 33, 33, 255⟩ := rfl

theorem text_dark : Theme.dark.text = ⟨238, 238, 238, 255⟩ := rfl

/-- WCAG 1.4.11 asks 3:1 for graphical objects, 1.4.3 asks 4.5:1 for text. -/
def meetsContrast (t : Theme) : Bool :=
  t.text.contrast t.background ≥ 4.5 &&
    t.series.all fun s => s.color.contrast t.background ≥ 3

/-- The least contrast of any series colour against the background of `t`. -/
def minSeriesContrast (t : Theme) : Float :=
  t.series.foldl (fun m s => min m (s.color.contrast t.background)) 21

/-- No two series of a theme share a colour, nor a (marker, dash) pair. -/
def Distinguishable (t : Theme) : Prop :=
  t.series.toList.Pairwise fun a b =>
    a.color ≠ b.color ∧ (a.marker ≠ b.marker ∨ a.dash ≠ b.dash)

instance (t : Theme) : Decidable t.Distinguishable := by unfold Distinguishable; infer_instance

theorem distinguishable (t : Theme) : t.Distinguishable := by
  cases t <;> decide

end Theme

end Inkproof.Scene
