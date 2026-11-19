/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Scene.Dash
import Inkproof.Scene.DisplayList

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
  color : Color
  marker : MarkerShape
  dash : Dash
  deriving DecidableEq, Repr

namespace Color

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
