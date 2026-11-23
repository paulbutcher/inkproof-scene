/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Axis.Layout
import Inkproof.Axis.LabelLayout
import Inkproof.Axis.Scales
import Inkproof.Axis.Ticks
import Inkproof.Axis.TickLabels
import Inkproof.Axis.TimeLabel
import Inkproof.Scale.Categorical
import Inkproof.Scale.Linear
import Inkproof.Scale.Log
import Inkproof.Float.FloatValue
import Inkproof.Scene.Compile
import Inkproof.Scene.Text

namespace Inkproof.Scene

open Inkproof.Core

universe u v

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

/-- How an axis is drawn. Every width, half width and length is in pixels. Tick marks and the axis line are strips of the given half widths; a
gridline runs across the whole plot at each tick. A label is anchored `labelGap` beyond the end of
the tick marks. Each of the line, the tick marks and the labels can be left out; the labels are set in `labelText`; the gridlines and the labels
keep their places when the line or the tick marks are. -/
structure AxisStyle where
  line : Paint := {}
  lineHalfWidth : Rat := 1 / 2
  tick : Paint := {}
  tickHalfWidth : Rat := 1 / 2
  tickLength : Rat := 4
  grid : Option (Paint × Rat) := none
  labelGap : Rat := 2
  showLine : Bool := true
  showTicks : Bool := true
  showLabels : Bool := true
  labelText : TextStyle := {}

/-- A label for the host's text layer: its text, the point it is anchored at, its turn and how it is set. -/
structure PlacedLabel where
  text : String
  anchor : Pt
  rotation : Inkproof.Axis.Rotation
  style : TextStyle := {}

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

/-- The main gridlines: one across the whole plot at each tick, if the style has a grid. -/
def axisGridlines {α : Type u} (side : Side) (r : Rect) (proj : α → Rat) (st : AxisStyle)
    (ticks : List α) : List Command :=
  match st.grid with
  | none => []
  | some (p, w) => ticks.map fun t => segment p w (side.pt (proj t) (side.edge r)) (side.pt (proj t) (side.far r))

/-- A label at the end of each bar's value, set in `style`, with `format` turning the value into text.
A missing value has no label. -/
def barValueLabels {α : Type u} {β : Type v} [LE α] (style : TextStyle) (format : β → String)
    (proj : Projection α β) (s : Series α β) : List PlacedLabel :=
  (s.points.filterMap fun (x, v) =>
    v.map fun y => ⟨format y, ⟨proj.x x, proj.y y⟩, .horizontal, style⟩).toList

/-- The labels are those of the series' points in order, one for each present value and none for a missing one. -/
theorem barValueLabels_eq {α : Type u} {β : Type v} [LE α] (style : TextStyle) (format : β → String)
    (proj : Projection α β) (s : Series α β) :
    barValueLabels style format proj s =
      s.points.toList.filterMap fun (x, v) =>
        v.map fun y => ⟨format y, ⟨proj.x x, proj.y y⟩, .horizontal, style⟩ := by
  simp [barValueLabels]

/-- Each present value has a label anchored at its bar's end, in the given style. -/
theorem mem_barValueLabels {α : Type u} {β : Type v} [LE α] (style : TextStyle) (format : β → String)
    (proj : Projection α β) (s : Series α β) {x : α} {y : β} (h : (x, some y) ∈ s.points) :
    (⟨format y, ⟨proj.x x, proj.y y⟩, .horizontal, style⟩ : PlacedLabel) ∈
      barValueLabels style format proj s :=
  Array.mem_toList_iff.2 (Array.mem_filterMap.2 ⟨(x, some y), h, rfl⟩)

/-- An axis of `side` of the plot `r`. A tick at data value `t` lies at `proj t` along the axis, so
`proj` is the projection of the axis's scale, linear, logarithmic or banded. Each tick gets a tick
mark, unless the style omits them, and, if the style has a grid, a gridline; `layout` is Axis's choice of which labelled ticks to
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
  { display := (axisGridlines side r proj st ticks ++ (if st.showLine then [axisLine] else []) ++
      (if st.showTicks then marks else [])).toArray
    labels := if st.showLabels then layout.kept.map fun l =>
      ⟨l.2, side.pt (proj l.1) (tickEnd + side.outward * st.labelGap), layout.rotation, st.labelText⟩ else [] }

/-- The display is the gridlines, then the axis line if shown, then the tick marks if shown. -/
theorem compileAxis_display {α : Type u} (side : Side) (r : Rect) (proj : α → Rat) (st : AxisStyle)
    (ticks : List α) (layout : Inkproof.Axis.Layout (α × String)) :
    (compileAxis side r proj st ticks layout).display =
      (axisGridlines side r proj st ticks ++
        (if st.showLine then
          [segment st.line st.lineHalfWidth (side.pt (if side.horizontal then r.x0 else r.y0) (side.edge r))
            (side.pt (if side.horizontal then r.x1 else r.y1) (side.edge r))] else []) ++
        (if st.showTicks then ticks.map fun t =>
          segment st.tick st.tickHalfWidth (side.pt (proj t) (side.edge r))
            (side.pt (proj t) (side.edge r + side.outward * st.tickLength)) else [])).toArray := rfl

/-- With the line and the tick marks omitted, the display is the gridlines alone. -/
theorem compileAxis_display_bare {α : Type u} (side : Side) (r : Rect) (proj : α → Rat) (st : AxisStyle)
    (ticks : List α) (layout : Inkproof.Axis.Layout (α × String))
    (hl : st.showLine = false) (ht : st.showTicks = false) :
    (compileAxis side r proj st ticks layout).display = (axisGridlines side r proj st ticks).toArray := by
  simp [compileAxis, hl, ht]

/-- Omitting the line and the tick marks leaves the gridlines and the labels where they were. -/
theorem compileAxis_bare_keeps {α : Type u} (side : Side) (r : Rect) (proj : α → Rat) (st : AxisStyle)
    (ticks : List α) (layout : Inkproof.Axis.Layout (α × String)) :
    (compileAxis side r proj { st with showLine := false, showTicks := false } ticks layout).labels =
        (compileAxis side r proj st ticks layout).labels ∧
      (compileAxis side r proj { st with showLine := false, showTicks := false } ticks layout).display =
        (axisGridlines side r proj st ticks).toArray := ⟨rfl, by simp [compileAxis, axisGridlines]⟩

/-- The label text style changes only the labels' style: the display is unchanged, and so are the labels' text, anchors
and rotation. -/
theorem compileAxis_labelText {α : Type u} (side : Side) (r : Rect) (proj : α → Rat) (st : AxisStyle)
    (ticks : List α) (layout : Inkproof.Axis.Layout (α × String)) (t : TextStyle) :
    (compileAxis side r proj { st with labelText := t } ticks layout).display =
        (compileAxis side r proj st ticks layout).display ∧
      (compileAxis side r proj { st with labelText := t } ticks layout).labels =
        (compileAxis side r proj st ticks layout).labels.map ({ · with style := t }) := by
  refine ⟨rfl, ?_⟩
  simp only [compileAxis]
  split <;> simp [Function.comp_def]

/-- Without labels the drawing has none. -/
theorem compileAxis_no_labels {α : Type u} (side : Side) (r : Rect) (proj : α → Rat) (st : AxisStyle)
    (ticks : List α) (layout : Inkproof.Axis.Layout (α × String)) (h : st.showLabels = false) :
    (compileAxis side r proj st ticks layout).labels = [] := by
  simp [compileAxis, h]

/-- Without tick marks, the display is the gridlines and the axis line alone. -/
theorem compileAxis_no_ticks {α : Type u} (side : Side) (r : Rect) (proj : α → Rat) (st : AxisStyle)
    (ticks : List α) (layout : Inkproof.Axis.Layout (α × String)) (h : st.showTicks = false) :
    (compileAxis side r proj st ticks layout).display =
      (axisGridlines side r proj st ticks ++
        (if st.showLine then
          [segment st.line st.lineHalfWidth (side.pt (if side.horizontal then r.x0 else r.y0) (side.edge r))
            (side.pt (if side.horizontal then r.x1 else r.y1) (side.edge r))] else [])).toArray := by
  simp [compileAxis, h]

/-- Without the axis line, the display is the gridlines and the tick marks alone. -/
theorem compileAxis_no_line {α : Type u} (side : Side) (r : Rect) (proj : α → Rat) (st : AxisStyle)
    (ticks : List α) (layout : Inkproof.Axis.Layout (α × String)) (h : st.showLine = false) :
    (compileAxis side r proj st ticks layout).display =
      (axisGridlines side r proj st ticks ++
        (if st.showTicks then ticks.map fun t =>
          segment st.tick st.tickHalfWidth (side.pt (proj t) (side.edge r))
            (side.pt (proj t) (side.edge r + side.outward * st.tickLength)) else [])).toArray := by
  simp [compileAxis, h]

/-- With tick marks shown, every tick has a tick mark whose both ends lie at the tick's projection
along the axis. -/
theorem compileAxis_tick {α : Type u} (side : Side) (r : Rect) (proj : α → Rat) (st : AxisStyle)
    (ticks : List α) (layout : Inkproof.Axis.Layout (α × String)) (hs : st.showTicks = true)
    {t : α} (h : t ∈ ticks) :
    ∃ c ∈ (compileAxis side r proj st ticks layout).display, ∃ a b,
      c.shape = .strip st.tickHalfWidth [.val a, .val b] ∧
      side.along a = proj t ∧ side.along b = proj t := by
  refine ⟨segment st.tick st.tickHalfWidth (side.pt (proj t) (side.edge r))
    (side.pt (proj t) (side.edge r + side.outward * st.tickLength)), ?_, _, _, rfl,
    Side.along_pt .., Side.along_pt ..⟩
  simp only [compileAxis, hs, ite_true, List.mem_toArray, List.mem_append]
  exact Or.inr (List.mem_map.2 ⟨t, h, rfl⟩)

/-- With a grid, every tick has a gridline whose both ends lie at the tick's projection. -/
theorem compileAxis_grid {α : Type u} (side : Side) (r : Rect) (proj : α → Rat) (st : AxisStyle)
    (ticks : List α) (layout : Inkproof.Axis.Layout (α × String)) {p : Paint × Rat}
    (hg : st.grid = some p) {t : α} (h : t ∈ ticks) :
    ∃ c ∈ (compileAxis side r proj st ticks layout).display, ∃ a b,
      c.shape = .strip p.2 [.val a, .val b] ∧
      side.along a = proj t ∧ side.along b = proj t := by
  refine ⟨segment p.1 p.2 (side.pt (proj t) (side.edge r)) (side.pt (proj t) (side.far r)), ?_, _, _,
    rfl, Side.along_pt .., Side.along_pt ..⟩
  simp only [compileAxis, axisGridlines, hg, List.mem_toArray, List.mem_append]
  exact Or.inl (Or.inl (List.mem_map.2 ⟨t, h, rfl⟩))

/-- With labels shown, every label kept by the layout is placed, with the layout's rotation, anchored at its tick's
projection along the axis. -/
theorem compileAxis_label {α : Type u} (side : Side) (r : Rect) (proj : α → Rat) (st : AxisStyle)
    (ticks : List α) (layout : Inkproof.Axis.Layout (α × String)) (hs : st.showLabels = true)
    {l : α × String} (h : l ∈ layout.kept) :
    ∃ pl ∈ (compileAxis side r proj st ticks layout).labels,
      pl.text = l.2 ∧ side.along pl.anchor = proj l.1 ∧ pl.rotation = layout.rotation := by
  simp only [compileAxis, hs, ite_true]
  exact ⟨_, List.mem_map.2 ⟨l, h, rfl⟩, rfl, Side.along_pt .., rfl⟩

/-- Gridlines at `positions`, which need not be ticks, drawn with their own paint and half width. -/
structure MinorGrid (α : Type u) where
  paint : Paint
  halfWidth : Rat
  positions : List α

/-- The gridlines a `MinorGrid` adds to an axis: one across the whole plot at each position that lies
within the plot, is not drawn twice, and is not at a tick when the style has a main grid. -/
def minorGridlines {α : Type u} (side : Side) (r : Rect) (proj : α → Rat) (st : AxisStyle)
    (m : MinorGrid α) (ticks : List α) : List Command :=
  let lo := if side.horizontal then r.x0 else r.y0
  let hi := if side.horizontal then r.x1 else r.y1
  let taken := if st.grid.isSome then ticks.map proj else []
  ((m.positions.map proj).filter fun p => decide (lo ≤ p ∧ p ≤ hi ∧ p ∉ taken)).eraseDups.map fun p =>
    segment m.paint m.halfWidth (side.pt p (side.edge r)) (side.pt p (side.far r))

/-- A position inside the plot that is not at a tick drawn with a main gridline has a minor gridline
spanning the plot, at its projection. -/
theorem minorGridlines_mem {α : Type u} (side : Side) (r : Rect) (proj : α → Rat) (st : AxisStyle)
    (m : MinorGrid α) (ticks : List α) {x : α} (hx : x ∈ m.positions)
    (hlo : (if side.horizontal then r.x0 else r.y0) ≤ proj x)
    (hhi : proj x ≤ (if side.horizontal then r.x1 else r.y1))
    (ht : st.grid.isSome = true → proj x ∉ ticks.map proj) :
    segment m.paint m.halfWidth (side.pt (proj x) (side.edge r)) (side.pt (proj x) (side.far r)) ∈
      minorGridlines side r proj st m ticks := by
  unfold minorGridlines
  apply List.mem_map.2
  refine ⟨proj x, ?_, rfl⟩
  apply List.mem_eraseDups.2
  apply List.mem_filter.2
  refine ⟨List.mem_map.2 ⟨x, hx, rfl⟩, ?_⟩
  simp only [decide_eq_true_eq]
  refine ⟨hlo, hhi, ?_⟩
  split
  · rename_i h; exact ht h
  · simp

/-- Every minor gridline spans the plot at the projection of one of the positions, inside the plot. -/
theorem minorGridlines_spec {α : Type u} (side : Side) (r : Rect) (proj : α → Rat) (st : AxisStyle)
    (m : MinorGrid α) (ticks : List α) {c : Command} (hc : c ∈ minorGridlines side r proj st m ticks) :
    ∃ x ∈ m.positions,
      c = segment m.paint m.halfWidth (side.pt (proj x) (side.edge r)) (side.pt (proj x) (side.far r)) ∧
      (if side.horizontal then r.x0 else r.y0) ≤ proj x ∧
      proj x ≤ (if side.horizontal then r.x1 else r.y1) := by
  unfold minorGridlines at hc
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hc
  obtain ⟨hp, hd⟩ := List.mem_filter.1 (List.mem_eraseDups.1 hp)
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hp
  simp only [decide_eq_true_eq] at hd
  exact ⟨x, hx, rfl, hd.1, hd.2.1⟩

/-- The drawing with `lines` beneath its marks. -/
def AxisDrawing.withMinor (d : AxisDrawing) (lines : List Command) : AxisDrawing :=
  { d with display := lines.toArray ++ d.display }

theorem AxisDrawing.withMinor_display (d : AxisDrawing) (lines : List Command) :
    (d.withMinor lines).display = lines.toArray ++ d.display := rfl

theorem AxisDrawing.withMinor_labels (d : AxisDrawing) (lines : List Command) :
    (d.withMinor lines).labels = d.labels := rfl

/-- `compileAxis` with minor gridlines drawn beneath its marks. -/
def compileAxisMinor {α : Type u} (side : Side) (r : Rect) (proj : α → Rat) (st : AxisStyle)
    (minor : MinorGrid α) (ticks : List α) (layout : Inkproof.Axis.Layout (α × String)) :
    AxisDrawing :=
  (compileAxis side r proj st ticks layout).withMinor (minorGridlines side r proj st minor ticks)

/-- The labels are those of the axis without minor gridlines. -/
theorem compileAxisMinor_labels {α : Type u} (side : Side) (r : Rect) (proj : α → Rat)
    (st : AxisStyle) (minor : MinorGrid α) (ticks : List α) (layout : Inkproof.Axis.Layout (α × String)) :
    (compileAxisMinor side r proj st minor ticks layout).labels =
      (compileAxis side r proj st ticks layout).labels := rfl

/-- The display is the minor gridlines followed by the display of the axis without them, so its tick
marks, axis line and main gridlines are unchanged. -/
theorem compileAxisMinor_display {α : Type u} (side : Side) (r : Rect) (proj : α → Rat)
    (st : AxisStyle) (minor : MinorGrid α) (ticks : List α) (layout : Inkproof.Axis.Layout (α × String)) :
    (compileAxisMinor side r proj st minor ticks layout).display =
      (minorGridlines side r proj st minor ticks).toArray ++
        (compileAxis side r proj st ticks layout).display := rfl

/-- A point's coordinate across the axis. -/
def Side.across (s : Side) (p : Pt) : Rat :=
  if s.horizontal then p.y else p.x

theorem Side.across_pt' (s : Side) (a c : Rat) : s.across (s.pt a c) = c := by
  unfold Side.across Side.pt; split <;> rfl

/-- The title of the axis of `side` of the plot `r`, centred along the axis. `extent` is how far the
axis's tick labels reach beyond the plot's edge, as measured by the host; the title's anchor is
`gap` beyond that, and the text extends away from the plot from it. A title beside a vertical axis
is turned. -/
def placeAxisTitle (side : Side) (r : Rect) (extent gap : Rat) (text : String)
    (style : TextStyle := TextStyle.axisTitle) : PlacedLabel :=
  let lo := if side.horizontal then r.x0 else r.y0
  let hi := if side.horizontal then r.x1 else r.y1
  ⟨text, side.pt ((lo + hi) / 2) (side.edge r + side.outward * (extent + gap)),
    if side.horizontal then .horizontal else .vertical, style⟩

/-- The title is set in the given style. -/
theorem placeAxisTitle_style (side : Side) (r : Rect) (extent gap : Rat) (text : String) (s : TextStyle) :
    (placeAxisTitle side r extent gap text s).style = s := rfl

/-- The title is centred along the axis. -/
theorem placeAxisTitle_along (side : Side) (r : Rect) (extent gap : Rat) (text : String) :
    side.along (placeAxisTitle side r extent gap text).anchor =
      ((if side.horizontal then r.x0 else r.y0) + (if side.horizontal then r.x1 else r.y1)) / 2 :=
  Side.along_pt ..

/-- The title lies `extent + gap` beyond the plot's edge, measured away from the plot. -/
theorem placeAxisTitle_across (side : Side) (r : Rect) (extent gap : Rat) (text : String) :
    side.outward * (side.across (placeAxisTitle side r extent gap text).anchor - side.edge r) =
      extent + gap := by
  have h : side.outward * side.outward = 1 := by cases side <;> simp [Side.outward, Rat.mul_neg]
  rw [placeAxisTitle, Side.across_pt']
  have : side.edge r + side.outward * (extent + gap) - side.edge r = side.outward * (extent + gap) := by
    rw [Rat.add_comm, Rat.add_sub_cancel]
  rw [this, ← Rat.mul_assoc, h, Rat.one_mul]

/-- With a non-negative extent and a positive gap, the title lies strictly outside the plot's edge
and beyond the tick labels' extent. -/
theorem placeAxisTitle_outside (side : Side) (r : Rect) {extent gap : Rat} (hx : 0 ≤ extent)
    (hg : 0 < gap) (text : String) :
    0 < side.outward * (side.across (placeAxisTitle side r extent gap text).anchor - side.edge r) ∧
    extent < side.outward * (side.across (placeAxisTitle side r extent gap text).anchor - side.edge r) := by
  rw [placeAxisTitle_across]
  have h : extent < extent + gap := by
    have := (Rat.add_lt_add_left (a := 0) (b := gap) (c := extent)).2 hg
    rwa [Rat.add_zero] at this
  exact ⟨Rat.not_le.mp fun h' => Rat.not_le.mpr h (Rat.le_trans h' hx), h⟩

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
    (hs : st.showTicks = true) {p : Float} {q : Rat} (hp : p ∈ pixels)
    (hq : Inkproof.Float.Float.toRat p = some q) :
    ∃ c ∈ (compilePixelAxis side r st measure gap pixels labels).display, ∃ a b,
      c.shape = .strip st.tickHalfWidth [.val a, .val b] ∧
      side.along a = q ∧ side.along b = q := by
  unfold compilePixelAxis
  exact compileAxis_tick side r id st _ _ hs (t := q) (List.mem_filterMap.2 ⟨p, hp, hq⟩)

/-- `compilePixelAxis` with minor gridlines at the given pixel positions. A position that is not a
finite float is not drawn. -/
def compilePixelAxisMinor (side : Side) (r : Rect) (st : AxisStyle) (measure : String → Float × Float)
    (gap : Float) (pixels : List Float) (labels : List String) (minor : MinorGrid Float) : AxisDrawing :=
  (compilePixelAxis side r st measure gap pixels labels).withMinor
    (minorGridlines side r id st ⟨minor.paint, minor.halfWidth, minor.positions.filterMap Inkproof.Float.Float.toRat⟩
      (pixels.filterMap Inkproof.Float.Float.toRat))

/-- The labels are those of the axis without minor gridlines. -/
theorem compilePixelAxisMinor_labels (side : Side) (r : Rect) (st : AxisStyle)
    (measure : String → Float × Float) (gap : Float) (pixels : List Float) (labels : List String)
    (minor : MinorGrid Float) :
    (compilePixelAxisMinor side r st measure gap pixels labels minor).labels =
      (compilePixelAxis side r st measure gap pixels labels).labels := rfl

/-- The display is the minor gridlines followed by the display of the axis without them. -/
theorem compilePixelAxisMinor_display (side : Side) (r : Rect) (st : AxisStyle)
    (measure : String → Float × Float) (gap : Float) (pixels : List Float) (labels : List String)
    (minor : MinorGrid Float) :
    (compilePixelAxisMinor side r st measure gap pixels labels minor).display =
      (minorGridlines side r id st ⟨minor.paint, minor.halfWidth, minor.positions.filterMap Inkproof.Float.Float.toRat⟩
        (pixels.filterMap Inkproof.Float.Float.toRat)).toArray ++
        (compilePixelAxis side r st measure gap pixels labels).display := rfl

/-- A position whose pixel is a finite `q` inside the plot, and which is not at a tick drawn with a main
gridline, has a minor gridline spanning the plot at `q`. -/
theorem compilePixelAxisMinor_line (side : Side) (r : Rect) (st : AxisStyle)
    (measure : String → Float × Float) (gap : Float) (pixels : List Float) (labels : List String)
    (minor : MinorGrid Float) {p : Float} {q : Rat} (hp : p ∈ minor.positions)
    (hq : Inkproof.Float.Float.toRat p = some q)
    (hlo : (if side.horizontal then r.x0 else r.y0) ≤ q)
    (hhi : q ≤ (if side.horizontal then r.x1 else r.y1))
    (ht : st.grid.isSome = true → q ∉ pixels.filterMap Inkproof.Float.Float.toRat) :
    segment minor.paint minor.halfWidth (side.pt q (side.edge r)) (side.pt q (side.far r)) ∈
      (compilePixelAxisMinor side r st measure gap pixels labels minor).display := by
  have h := minorGridlines_mem side r id st
    ⟨minor.paint, minor.halfWidth, minor.positions.filterMap Inkproof.Float.Float.toRat⟩
    (pixels.filterMap Inkproof.Float.Float.toRat) (x := q) (List.mem_filterMap.2 ⟨p, hp, hq⟩) hlo hhi
    (by simpa using ht)
  simp only [compilePixelAxisMinor, AxisDrawing.withMinor, Array.mem_append, List.mem_toArray]
  exact Or.inl h

/-- An axis for a linear scale: ticks where `linearScaleTicks` puts them, at the pixel the scale
maps each to. -/
def compileLinearAxis (side : Side) (r : Rect) (s : Inkproof.Scale.Linear Float) (spec : TickSpec)
    (measure : String → Float × Float) (st : AxisStyle) : AxisDrawing :=
  let ts := Inkproof.Axis.linearScaleTicks s spec.target
  compilePixelAxis side r st measure spec.labelGap (ts.map s.map)
    (Inkproof.Axis.tickLabels spec.locale ts)

/-- `compileLinearAxis` with minor gridlines at the given data values. -/
def compileLinearAxisMinor (side : Side) (r : Rect) (s : Inkproof.Scale.Linear Float) (spec : TickSpec)
    (measure : String → Float × Float) (st : AxisStyle) (minor : MinorGrid Float) : AxisDrawing :=
  let ts := Inkproof.Axis.linearScaleTicks s spec.target
  compilePixelAxisMinor side r st measure spec.labelGap (ts.map s.map)
    (Inkproof.Axis.tickLabels spec.locale ts) ⟨minor.paint, minor.halfWidth, minor.positions.map s.map⟩

/-- A position of the data whose pixel is a finite `q` inside the plot, and which is not at a tick drawn
with a main gridline, has a minor gridline spanning the plot at `q`. -/
theorem compileLinearAxisMinor_line (side : Side) (r : Rect) (s : Inkproof.Scale.Linear Float) (spec : TickSpec)
    (measure : String → Float × Float) (st : AxisStyle) (minor : MinorGrid Float) {p : Float} {q : Rat}
    (hp : p ∈ minor.positions) (hq : Inkproof.Float.Float.toRat (s.map p) = some q)
    (hlo : (if side.horizontal then r.x0 else r.y0) ≤ q)
    (hhi : q ≤ (if side.horizontal then r.x1 else r.y1))
    (ht : st.grid.isSome = true → q ∉ ((Inkproof.Axis.linearScaleTicks s spec.target).map s.map).filterMap Inkproof.Float.Float.toRat) :
    segment minor.paint minor.halfWidth (side.pt q (side.edge r)) (side.pt q (side.far r)) ∈
      (compileLinearAxisMinor side r s spec measure st minor).display :=
  compilePixelAxisMinor_line _ _ _ _ _ _ _ _ (List.mem_map.2 ⟨p, hp, rfl⟩) hq hlo hhi ht

/-- An axis for a logarithmic scale: ticks where `logScaleTicks` puts them, at the pixel the scale
maps each to. -/
def compileLogAxis (side : Side) (r : Rect) (s : Inkproof.Scale.Log Float) (spec : TickSpec)
    (measure : String → Float × Float) (st : AxisStyle) : AxisDrawing :=
  let ts := Inkproof.Axis.logScaleTicks s spec.target
  compilePixelAxis side r st measure spec.labelGap (ts.map (s.map Float.log))
    (Inkproof.Axis.tickLabels spec.locale ts)

/-- `compileLogAxis` with minor gridlines at the given data values. -/
def compileLogAxisMinor (side : Side) (r : Rect) (s : Inkproof.Scale.Log Float) (spec : TickSpec)
    (measure : String → Float × Float) (st : AxisStyle) (minor : MinorGrid Float) : AxisDrawing :=
  let ts := Inkproof.Axis.logScaleTicks s spec.target
  compilePixelAxisMinor side r st measure spec.labelGap (ts.map (s.map Float.log))
    (Inkproof.Axis.tickLabels spec.locale ts) ⟨minor.paint, minor.halfWidth, minor.positions.map (s.map Float.log)⟩

/-- A position of the data whose pixel is a finite `q` inside the plot, and which is not at a tick drawn
with a main gridline, has a minor gridline spanning the plot at `q`. -/
theorem compileLogAxisMinor_line (side : Side) (r : Rect) (s : Inkproof.Scale.Log Float) (spec : TickSpec)
    (measure : String → Float × Float) (st : AxisStyle) (minor : MinorGrid Float) {p : Float} {q : Rat}
    (hp : p ∈ minor.positions) (hq : Inkproof.Float.Float.toRat (s.map Float.log p) = some q)
    (hlo : (if side.horizontal then r.x0 else r.y0) ≤ q)
    (hhi : q ≤ (if side.horizontal then r.x1 else r.y1))
    (ht : st.grid.isSome = true → q ∉ ((Inkproof.Axis.logScaleTicks s spec.target).map (s.map Float.log)).filterMap Inkproof.Float.Float.toRat) :
    segment minor.paint minor.halfWidth (side.pt q (side.edge r)) (side.pt q (side.far r)) ∈
      (compileLogAxisMinor side r s spec measure st minor).display :=
  compilePixelAxisMinor_line _ _ _ _ _ _ _ _ (List.mem_map.2 ⟨p, hp, rfl⟩) hq hlo hhi ht

/-- The labels and display of a linear axis with minor gridlines are those of the plain axis, with the
minor gridlines beneath. -/
theorem compileLinearAxisMinor_labels (side : Side) (r : Rect) (s : Inkproof.Scale.Linear Float)
    (spec : TickSpec) (measure : String → Float × Float) (st : AxisStyle) (minor : MinorGrid Float) :
    (compileLinearAxisMinor side r s spec measure st minor).labels =
      (compileLinearAxis side r s spec measure st).labels := rfl

/-- As `compileLinearAxisMinor_labels`, for a log axis. -/
theorem compileLogAxisMinor_labels (side : Side) (r : Rect) (s : Inkproof.Scale.Log Float)
    (spec : TickSpec) (measure : String → Float × Float) (st : AxisStyle) (minor : MinorGrid Float) :
    (compileLogAxisMinor side r s spec measure st minor).labels =
      (compileLogAxis side r s spec measure st).labels := rfl

/-- Every tick of a linear scale whose pixel is finite has a tick mark at the scale's own
projection of it. -/
theorem compileLinearAxis_tick (side : Side) (r : Rect) (s : Inkproof.Scale.Linear Float)
    (spec : TickSpec) (measure : String → Float × Float) (st : AxisStyle) {t : Float} {q : Rat}
    (ht : t ∈ Inkproof.Axis.linearScaleTicks s spec.target)
    (hs : st.showTicks = true) (hq : Inkproof.Float.Float.toRat (s.map t) = some q) :
    ∃ c ∈ (compileLinearAxis side r s spec measure st).display, ∃ a b,
      c.shape = .strip st.tickHalfWidth [.val a, .val b] ∧
      side.along a = q ∧ side.along b = q :=
  compilePixelAxis_tick _ _ _ _ _ _ _ hs (List.mem_map.2 ⟨t, ht, rfl⟩) hq

/-- Every tick of a log scale whose pixel is finite has a tick mark at the scale's own projection
of it. -/
theorem compileLogAxis_tick (side : Side) (r : Rect) (s : Inkproof.Scale.Log Float)
    (spec : TickSpec) (measure : String → Float × Float) (st : AxisStyle) {t : Float} {q : Rat}
    (ht : t ∈ Inkproof.Axis.logScaleTicks s spec.target)
    (hs : st.showTicks = true) (hq : Inkproof.Float.Float.toRat (s.map Float.log t) = some q) :
    ∃ c ∈ (compileLogAxis side r s spec measure st).display, ∃ a b,
      c.shape = .strip st.tickHalfWidth [.val a, .val b] ∧
      side.along a = q ∧ side.along b = q :=
  compilePixelAxis_tick _ _ _ _ _ _ _ hs (List.mem_map.2 ⟨t, ht, rfl⟩) hq

/-- An axis for a linear scale of seconds since 1970-01-01T00:00:00 UTC: ticks at the clock intervals
`durationScaleTicks` chooses, labelled in UTC with `months` as the month names. `spec.locale` is not
used. -/
def compileTimeAxis (side : Side) (r : Rect) (s : Inkproof.Scale.Linear Float) (spec : TickSpec)
    (months : List String) (measure : String → Float × Float) (st : AxisStyle) : AxisDrawing :=
  let ts := Inkproof.Axis.durationScaleTicks s spec.target
  let step := Inkproof.Axis.durationStep (s.domainEnd - s.domainStart).abs spec.target
  compilePixelAxis side r st measure spec.labelGap (ts.map s.map)
    (Inkproof.Axis.timeTickLabels months step ts)

/-- Every tick of a time scale whose pixel is finite has a tick mark at the scale's own projection
of it. -/
theorem compileTimeAxis_tick (side : Side) (r : Rect) (s : Inkproof.Scale.Linear Float)
    (spec : TickSpec) (months : List String) (measure : String → Float × Float) (st : AxisStyle)
    {t : Float} {q : Rat} (ht : t ∈ Inkproof.Axis.durationScaleTicks s spec.target)
    (hs : st.showTicks = true) (hq : Inkproof.Float.Float.toRat (s.map t) = some q) :
    ∃ c ∈ (compileTimeAxis side r s spec months measure st).display, ∃ a b,
      c.shape = .strip st.tickHalfWidth [.val a, .val b] ∧
      side.along a = q ∧ side.along b = q :=
  compilePixelAxis_tick _ _ _ _ _ _ _ hs (List.mem_map.2 ⟨t, ht, rfl⟩) hq

/-- `compileTimeAxis` with minor gridlines at the given times. -/
def compileTimeAxisMinor (side : Side) (r : Rect) (s : Inkproof.Scale.Linear Float) (spec : TickSpec)
    (months : List String) (measure : String → Float × Float) (st : AxisStyle) (minor : MinorGrid Float) :
    AxisDrawing :=
  let ts := Inkproof.Axis.durationScaleTicks s spec.target
  let step := Inkproof.Axis.durationStep (s.domainEnd - s.domainStart).abs spec.target
  compilePixelAxisMinor side r st measure spec.labelGap (ts.map s.map)
    (Inkproof.Axis.timeTickLabels months step ts) ⟨minor.paint, minor.halfWidth, minor.positions.map s.map⟩

/-- A position of the data whose pixel is a finite `q` inside the plot, and which is not at a tick drawn
with a main gridline, has a minor gridline spanning the plot at `q`. -/
theorem compileTimeAxisMinor_line (side : Side) (r : Rect) (s : Inkproof.Scale.Linear Float) (spec : TickSpec) (months : List String)
    (measure : String → Float × Float) (st : AxisStyle) (minor : MinorGrid Float) {p : Float} {q : Rat}
    (hp : p ∈ minor.positions) (hq : Inkproof.Float.Float.toRat (s.map p) = some q)
    (hlo : (if side.horizontal then r.x0 else r.y0) ≤ q)
    (hhi : q ≤ (if side.horizontal then r.x1 else r.y1))
    (ht : st.grid.isSome = true → q ∉ ((Inkproof.Axis.durationScaleTicks s spec.target).map s.map).filterMap Inkproof.Float.Float.toRat) :
    segment minor.paint minor.halfWidth (side.pt q (side.edge r)) (side.pt q (side.far r)) ∈
      (compileTimeAxisMinor side r s spec months measure st minor).display :=
  compilePixelAxisMinor_line _ _ _ _ _ _ _ _ (List.mem_map.2 ⟨p, hp, rfl⟩) hq hlo hhi ht

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
    (hs : st.showTicks = true) (hq : Inkproof.Float.Float.toRat (bandCentrePixel s i) = some q) :
    ∃ c ∈ (compileCategoricalAxis side r s name target labelGap measure st).display, ∃ a b,
      c.shape = .strip st.tickHalfWidth [.val a, .val b] ∧
      side.along a = q ∧ side.along b = q :=
  compilePixelAxis_tick _ _ _ _ _ _ _ hs (List.mem_map.2 ⟨i, hi, rfl⟩) hq

end Inkproof.Scene
