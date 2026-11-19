/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Axis.Layout
import Inkproof.Axis.LabelLayout
import Inkproof.Axis.Scales
import Inkproof.Axis.Ticks
import Inkproof.Axis.TickLabels
import Inkproof.Scale.Categorical
import Inkproof.Scale.Linear
import Inkproof.Scale.Log
import Inkproof.Float.FloatValue
import Inkproof.Scene.Compile

namespace Inkproof.Scene

universe u

/-- The edge of the plot rectangle an axis lies along. Ticks point away from the plot. -/
inductive Side where
  | bottom
  | left
  | top
  | right
  deriving DecidableEq, Repr

/-- Whether the axis runs along `x`, so that ticks differ in `x` and are placed by `x`. -/
def Side.horizontal : Side → Bool
  | .bottom | .top => true
  | .left | .right => false

/-- The coordinate across the axis at which the axis line lies. -/
def Side.edge (s : Side) (r : Rect) : Rat :=
  match s with
  | .bottom => r.y1
  | .top => r.y0
  | .left => r.x0
  | .right => r.x1

/-- The coordinate across the axis at the far side of the plot. -/
def Side.far (s : Side) (r : Rect) : Rat :=
  match s with
  | .bottom => r.y0
  | .top => r.y1
  | .left => r.x1
  | .right => r.x0

/-- Moving away from the plot, as a multiplier of the distance. -/
def Side.outward : Side → Rat
  | .bottom | .right => 1
  | .top | .left => -1

/-- The point at `along` the axis and `across` it. -/
def Side.pt (s : Side) (along across : Rat) : Pt :=
  if s.horizontal then ⟨along, across⟩ else ⟨across, along⟩

/-- A point's coordinate along the axis. -/
def Side.along (s : Side) (p : Pt) : Rat :=
  if s.horizontal then p.x else p.y

theorem Side.along_pt (s : Side) (a c : Rat) : s.along (s.pt a c) = a := by
  unfold Side.along Side.pt; split <;> rfl

theorem Side.across_pt (s : Side) (a c : Rat) :
    (if s.horizontal then (s.pt a c).y else (s.pt a c).x) = c := by
  unfold Side.pt; split <;> rfl

theorem Side.horizontal_iff (s : Side) : s.horizontal = true ↔ s = .bottom ∨ s = .top := by
  cases s <;> simp [Side.horizontal]

theorem Side.edge_spec (r : Rect) :
    Side.bottom.edge r = r.y1 ∧ Side.top.edge r = r.y0 ∧
    Side.left.edge r = r.x0 ∧ Side.right.edge r = r.x1 := ⟨rfl, rfl, rfl, rfl⟩

theorem Side.far_spec (r : Rect) :
    Side.bottom.far r = r.y0 ∧ Side.top.far r = r.y1 ∧
    Side.left.far r = r.x1 ∧ Side.right.far r = r.x0 := ⟨rfl, rfl, rfl, rfl⟩

theorem Side.outward_spec :
    Side.bottom.outward = 1 ∧ Side.right.outward = 1 ∧
    Side.top.outward = -1 ∧ Side.left.outward = -1 := ⟨rfl, rfl, rfl, rfl⟩

/-- How an axis is drawn. Tick marks and the axis line are strips of the given half widths; a
gridline runs across the whole plot at each tick. A label is anchored `labelGap` beyond the end of
the tick marks. -/
structure AxisStyle where
  line : Paint
  lineHalfWidth : Rat
  tick : Paint
  tickHalfWidth : Rat
  tickLength : Rat
  grid : Option (Paint × Rat)
  labelGap : Rat

/-- A label for the host's text layer: its text, the point it is anchored at, and its turn. -/
structure PlacedLabel where
  text : String
  anchor : Pt
  rotation : Inkproof.Axis.Rotation

/-- An axis as drawn: the marks, and the labels the host's text layer places. -/
structure AxisDrawing where
  display : DisplayList
  labels : List PlacedLabel

/-- A straight mark of the given half width between two points, in the paint's layer and colour. -/
def segment (c : Paint) (halfWidth : Rat) (a b : Pt) : Command :=
  ⟨c.layer, c.color, .strip halfWidth [.val a, .val b]⟩

theorem segment_spec (c : Paint) (w : Rat) (a b : Pt) :
    (segment c w a b).layer = c.layer ∧ (segment c w a b).color = c.color ∧
    (segment c w a b).shape = .strip w [.val a, .val b] := ⟨rfl, rfl, rfl⟩

/-- An axis of `side` of the plot `r`. A tick at data value `t` lies at `proj t` along the axis, so
`proj` is the projection of the axis's scale, linear, logarithmic or banded. Each tick gets a tick
mark and, if the style has a grid, a gridline; `layout` is Axis's choice of which labelled ticks to
show and how to turn them. -/
def compileAxis {α : Type u} (side : Side) (r : Rect) (proj : α → Rat) (st : AxisStyle)
    (ticks : List α) (layout : Inkproof.Axis.Layout (α × String)) : AxisDrawing :=
  let lo := if side.horizontal then r.x0 else r.y0
  let hi := if side.horizontal then r.x1 else r.y1
  let e := side.edge r
  let tickEnd := e + side.outward * st.tickLength
  let axisLine := segment st.line st.lineHalfWidth (side.pt lo e) (side.pt hi e)
  let marks := ticks.map fun t =>
    segment st.tick st.tickHalfWidth (side.pt (proj t) e) (side.pt (proj t) tickEnd)
  let grid := match st.grid with
    | none => []
    | some (p, w) => ticks.map fun t => segment p w (side.pt (proj t) e) (side.pt (proj t) (side.far r))
  { display := (grid ++ axisLine :: marks).toArray
    labels := layout.kept.map fun l =>
      ⟨l.2, side.pt (proj l.1) (tickEnd + side.outward * st.labelGap), layout.rotation⟩ }

/-- Every tick has a tick mark whose both ends lie at the tick's projection along the axis. -/
theorem compileAxis_tick {α : Type u} (side : Side) (r : Rect) (proj : α → Rat) (st : AxisStyle)
    (ticks : List α) (layout : Inkproof.Axis.Layout (α × String)) {t : α} (h : t ∈ ticks) :
    ∃ c ∈ (compileAxis side r proj st ticks layout).display, ∃ a b,
      c.shape = .strip st.tickHalfWidth [.val a, .val b] ∧
      side.along a = proj t ∧ side.along b = proj t := by
  refine ⟨segment st.tick st.tickHalfWidth (side.pt (proj t) (side.edge r))
    (side.pt (proj t) (side.edge r + side.outward * st.tickLength)), ?_, _, _, rfl,
    Side.along_pt .., Side.along_pt ..⟩
  simp only [compileAxis, List.mem_toArray, List.mem_append, List.mem_cons]
  exact Or.inr (Or.inr (List.mem_map.2 ⟨t, h, rfl⟩))

/-- With a grid, every tick has a gridline whose both ends lie at the tick's projection. -/
theorem compileAxis_grid {α : Type u} (side : Side) (r : Rect) (proj : α → Rat) (st : AxisStyle)
    (ticks : List α) (layout : Inkproof.Axis.Layout (α × String)) {p : Paint × Rat}
    (hg : st.grid = some p) {t : α} (h : t ∈ ticks) :
    ∃ c ∈ (compileAxis side r proj st ticks layout).display, ∃ a b,
      c.shape = .strip p.2 [.val a, .val b] ∧
      side.along a = proj t ∧ side.along b = proj t := by
  refine ⟨segment p.1 p.2 (side.pt (proj t) (side.edge r)) (side.pt (proj t) (side.far r)), ?_, _, _,
    rfl, Side.along_pt .., Side.along_pt ..⟩
  simp only [compileAxis, hg, List.mem_toArray, List.mem_append]
  exact Or.inl (List.mem_map.2 ⟨t, h, rfl⟩)

/-- Every label kept by the layout is placed, with the layout's rotation, anchored at its tick's
projection along the axis. -/
theorem compileAxis_label {α : Type u} (side : Side) (r : Rect) (proj : α → Rat) (st : AxisStyle)
    (ticks : List α) (layout : Inkproof.Axis.Layout (α × String)) {l : α × String}
    (h : l ∈ layout.kept) :
    ∃ pl ∈ (compileAxis side r proj st ticks layout).labels,
      pl.text = l.2 ∧ side.along pl.anchor = proj l.1 ∧ pl.rotation = layout.rotation := by
  refine ⟨_, List.mem_map.2 ⟨l, h, rfl⟩, rfl, Side.along_pt .., rfl⟩

/-- What a scale axis needs besides its geometry: the locale tick labels are written in, roughly how
many ticks to aim for, and the least gap between neighbouring labels. -/
structure TickSpec where
  locale : Inkproof.Axis.Locale
  target : Nat
  labelGap : Float

/-- An axis whose ticks are at the given pixel positions along it, in any order. A tick whose
position is not a finite float is not drawn. Labels pair with the ticks in order, and as many are
shown as `layoutLabels` can fit. -/
def compilePixelAxis (side : Side) (r : Rect) (st : AxisStyle) (measure : String → Float × Float)
    (gap : Float) (pixels : List Float) (labels : List String) : AxisDrawing :=
  let placed := pixels.zip labels
  let layout : Inkproof.Axis.Layout (Float × String) :=
    if side.horizontal then Inkproof.Axis.layoutLabels measure gap (placed.mergeSort fun a b => a.1 ≤ b.1)
    else
      let (stride, kept) := Inkproof.Axis.layoutLabelsVertical measure gap placed
      ⟨.horizontal, stride, kept⟩
  compileAxis side r id st (pixels.filterMap Inkproof.Float.Float.toRat)
    ⟨layout.rotation, layout.stride, layout.kept.filterMap fun l =>
      (Inkproof.Float.Float.toRat l.1).map (·, l.2)⟩

theorem compilePixelAxis_tick (side : Side) (r : Rect) (st : AxisStyle)
    (measure : String → Float × Float) (gap : Float) (pixels : List Float) (labels : List String)
    {p : Float} {q : Rat} (hp : p ∈ pixels) (hq : Inkproof.Float.Float.toRat p = some q) :
    ∃ c ∈ (compilePixelAxis side r st measure gap pixels labels).display, ∃ a b,
      c.shape = .strip st.tickHalfWidth [.val a, .val b] ∧
      side.along a = q ∧ side.along b = q := by
  unfold compilePixelAxis
  exact compileAxis_tick side r id st _ _ (t := q) (List.mem_filterMap.2 ⟨p, hp, hq⟩)

/-- An axis for a linear scale: ticks where `linearScaleTicks` puts them, at the pixel the scale
maps each to. -/
def compileLinearAxis (side : Side) (r : Rect) (s : Inkproof.Scale.Linear Float) (spec : TickSpec)
    (measure : String → Float × Float) (st : AxisStyle) : AxisDrawing :=
  let ts := Inkproof.Axis.linearScaleTicks s spec.target
  compilePixelAxis side r st measure spec.labelGap (ts.map s.map)
    (Inkproof.Axis.tickLabels spec.locale ts)

/-- An axis for a logarithmic scale: ticks where `logScaleTicks` puts them, at the pixel the scale
maps each to. -/
def compileLogAxis (side : Side) (r : Rect) (s : Inkproof.Scale.Log Float) (spec : TickSpec)
    (measure : String → Float × Float) (st : AxisStyle) : AxisDrawing :=
  let ts := Inkproof.Axis.logScaleTicks s spec.target
  compilePixelAxis side r st measure spec.labelGap (ts.map (s.map Float.log))
    (Inkproof.Axis.tickLabels spec.locale ts)

/-- Every tick of a linear scale whose pixel is finite has a tick mark at the scale's own
projection of it. -/
theorem compileLinearAxis_tick (side : Side) (r : Rect) (s : Inkproof.Scale.Linear Float)
    (spec : TickSpec) (measure : String → Float × Float) (st : AxisStyle) {t : Float} {q : Rat}
    (ht : t ∈ Inkproof.Axis.linearScaleTicks s spec.target)
    (hq : Inkproof.Float.Float.toRat (s.map t) = some q) :
    ∃ c ∈ (compileLinearAxis side r s spec measure st).display, ∃ a b,
      c.shape = .strip st.tickHalfWidth [.val a, .val b] ∧
      side.along a = q ∧ side.along b = q :=
  compilePixelAxis_tick _ _ _ _ _ _ _ (List.mem_map.2 ⟨t, ht, rfl⟩) hq

/-- Every tick of a log scale whose pixel is finite has a tick mark at the scale's own projection
of it. -/
theorem compileLogAxis_tick (side : Side) (r : Rect) (s : Inkproof.Scale.Log Float)
    (spec : TickSpec) (measure : String → Float × Float) (st : AxisStyle) {t : Float} {q : Rat}
    (ht : t ∈ Inkproof.Axis.logScaleTicks s spec.target)
    (hq : Inkproof.Float.Float.toRat (s.map Float.log t) = some q) :
    ∃ c ∈ (compileLogAxis side r s spec measure st).display, ∃ a b,
      c.shape = .strip st.tickHalfWidth [.val a, .val b] ∧
      side.along a = q ∧ side.along b = q :=
  compilePixelAxis_tick _ _ _ _ _ _ _ (List.mem_map.2 ⟨t, ht, rfl⟩) hq

/-- The pixel at the centre of band `i` of a categorical scale. -/
def bandCentrePixel {κ : Type u} (s : Inkproof.Scale.Categorical κ Float) (i : Nat) : Float :=
  letI : NatCast Float := ⟨Nat.toFloat⟩
  s.bandCentre i

/-- The pixel at the centre of band `i` is its start plus half the bandwidth. -/
theorem bandCentrePixel_eq {κ : Type u} (s : Inkproof.Scale.Categorical κ Float) (i : Nat) :
    letI : NatCast Float := ⟨Nat.toFloat⟩
    bandCentrePixel s i = s.bandStart i + s.bandwidth / 2 :=
  rfl

/-- An axis for a categorical scale: a tick at the centre of each band `categoricalIndices` selects,
labelled by `name`. -/
def compileCategoricalAxis {κ : Type u} (side : Side) (r : Rect) (s : Inkproof.Scale.Categorical κ Float)
    (name : κ → String) (target : Nat) (labelGap : Float) (measure : String → Float × Float)
    (st : AxisStyle) : AxisDrawing :=
  let is := (Inkproof.Axis.categoricalIndices s.categories.size 0 s.categories.size.toFloat target).filter
    (· < s.categories.size)
  compilePixelAxis side r st measure labelGap (is.map (bandCentrePixel s))
    (is.filterMap fun i => (s.categories[i]?).map name)

/-- Every band selected for labelling whose centre is finite has a tick mark at that centre. -/
theorem compileCategoricalAxis_tick {κ : Type u} (side : Side) (r : Rect)
    (s : Inkproof.Scale.Categorical κ Float) (name : κ → String) (target : Nat) (labelGap : Float)
    (measure : String → Float × Float) (st : AxisStyle) {i : Nat} {q : Rat}
    (hi : i ∈ (Inkproof.Axis.categoricalIndices s.categories.size 0 s.categories.size.toFloat
      target).filter (· < s.categories.size))
    (hq : Inkproof.Float.Float.toRat (bandCentrePixel s i) = some q) :
    ∃ c ∈ (compileCategoricalAxis side r s name target labelGap measure st).display, ∃ a b,
      c.shape = .strip st.tickHalfWidth [.val a, .val b] ∧
      side.along a = q ∧ side.along b = q :=
  compilePixelAxis_tick _ _ _ _ _ _ _ (List.mem_map.2 ⟨i, hi, rfl⟩) hq

end Inkproof.Scene
