/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Axis.Layout
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

end Inkproof.Scene
