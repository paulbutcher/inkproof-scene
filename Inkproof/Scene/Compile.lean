/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Core.Segmented
import Inkproof.Scale.Linear
import Inkproof.Scene.Dash
import Inkproof.Scene.Join
import Inkproof.Scene.Reduce

namespace Inkproof.Scene

open Inkproof.Core Inkproof.Scale

universe u v w

/-- How data coordinates become grid coordinates. A chart's scales fix it; `Projection.linear` is
the one made of two linear scales. -/
structure Projection (α : Type u) (β : Type v) where
  x : α → Rat
  y : β → Rat

def Projection.linear (sx sy : Linear Rat) : Projection Rat Rat := ⟨sx.map, sy.map⟩

/-- A gradient along the plane's y axis with stops given in data units, placed by the projection. -/
def Projection.gradientY {α : Type u} {β : Type v} (proj : Projection α β) (first : β × Color)
    (rest : List (β × Color)) : Shading :=
  .gradient .y ⟨proj.y first.1, first.2⟩ (rest.map fun (v, c) => ⟨proj.y v, c⟩)

/-- A gradient along the plane's x axis with stops given in data units, placed by the projection. -/
def Projection.gradientX {α : Type u} {β : Type v} (proj : Projection α β) (first : α × Color)
    (rest : List (α × Color)) : Shading :=
  .gradient .x ⟨proj.x first.1, first.2⟩ (rest.map fun (v, c) => ⟨proj.x v, c⟩)

/-- A pixel whose centre is at the projection of a stop's value takes that stop's colour, when the
projected stops ascend. -/
theorem Projection.gradientY_at {α : Type u} {β : Type v} (proj : Projection α β)
    (first : β × Color) (rest : List (β × Color))
    (hs : (first :: rest).Pairwise fun a b => proj.y a.1 < proj.y b.1) {s : β × Color}
    (hm : s ∈ first :: rest) {px : Pixel} (hpx : (px.row : Rat) + 1 / 2 = proj.y s.1) :
    (proj.gradientY first rest).at px = s.2 := by
  have hs' : (Stop.mk (proj.y first.1) first.2 :: rest.map fun (v, c) => ⟨proj.y v, c⟩).Pairwise
      (·.pos < ·.pos) := by
    refine List.pairwise_cons.2 ⟨fun a ha => ?_, List.pairwise_map.2 (List.pairwise_cons.1 hs).2⟩
    obtain ⟨⟨v, c⟩, hm, rfl⟩ := List.mem_map.1 ha
    exact (List.pairwise_cons.1 hs).1 _ hm
  have := evalStops_at _ _ hs' ⟨proj.y s.1, s.2⟩ (by
    cases List.mem_cons.1 hm with
    | inl h => subst h; simp
    | inr h => exact List.mem_cons_of_mem _ (List.mem_map.2 ⟨s, h, rfl⟩))
  simpa [Projection.gradientY, Shading.at, hpx] using this

/-- A pixel whose centre is at the projection of a stop's value takes that stop's colour, when the
projected stops ascend. -/
theorem Projection.gradientX_at {α : Type u} {β : Type v} (proj : Projection α β)
    (first : α × Color) (rest : List (α × Color))
    (hs : (first :: rest).Pairwise fun a b => proj.x a.1 < proj.x b.1) {s : α × Color}
    (hm : s ∈ first :: rest) {px : Pixel} (hpx : (px.col : Rat) + 1 / 2 = proj.x s.1) :
    (proj.gradientX first rest).at px = s.2 := by
  have hs' : (Stop.mk (proj.x first.1) first.2 :: rest.map fun (v, c) => ⟨proj.x v, c⟩).Pairwise
      (·.pos < ·.pos) := by
    refine List.pairwise_cons.2 ⟨fun a ha => ?_, List.pairwise_map.2 (List.pairwise_cons.1 hs).2⟩
    obtain ⟨⟨v, c⟩, hm, rfl⟩ := List.mem_map.1 ha
    exact (List.pairwise_cons.1 hs).1 _ hm
  have := evalStops_at _ _ hs' ⟨proj.x s.1, s.2⟩ (by
    cases List.mem_cons.1 hm with
    | inl h => subst h; simp
    | inr h => exact List.mem_cons_of_mem _ (List.mem_map.2 ⟨s, h, rfl⟩))
  simpa [Projection.gradientX, Shading.at, hpx] using this

/-- A stepped shading along the plane's y axis with stops given in data units, placed by the
projection. -/
def Projection.stepsY {α : Type u} {β : Type v} (proj : Projection α β) (first : β × Color)
    (rest : List (β × Color)) : Shading :=
  .steps .y ⟨proj.y first.1, first.2⟩ (rest.map fun (v, c) => ⟨proj.y v, c⟩)

/-- A stepped shading along the plane's x axis with stops given in data units, placed by the
projection. -/
def Projection.stepsX {α : Type u} {β : Type v} (proj : Projection α β) (first : α × Color)
    (rest : List (α × Color)) : Shading :=
  .steps .x ⟨proj.x first.1, first.2⟩ (rest.map fun (v, c) => ⟨proj.x v, c⟩)

/-- A pixel whose centre is at the projection of a stop's value takes that stop's colour, when the
projected stops ascend. -/
theorem Projection.stepsY_at {α : Type u} {β : Type v} (proj : Projection α β)
    (first : β × Color) (rest : List (β × Color))
    (hs : (first :: rest).Pairwise fun a b => proj.y a.1 < proj.y b.1) {s : β × Color}
    (hm : s ∈ first :: rest) {px : Pixel} (hpx : (px.row : Rat) + 1 / 2 = proj.y s.1) :
    (proj.stepsY first rest).at px = s.2 := by
  have hs' : (Stop.mk (proj.y first.1) first.2 :: rest.map fun (v, c) => ⟨proj.y v, c⟩).Pairwise
      (·.pos < ·.pos) := by
    refine List.pairwise_cons.2 ⟨fun a ha => ?_, List.pairwise_map.2 (List.pairwise_cons.1 hs).2⟩
    obtain ⟨⟨v, c⟩, hm, rfl⟩ := List.mem_map.1 ha
    exact (List.pairwise_cons.1 hs).1 _ hm
  have := evalSteps_at _ _ hs' ⟨proj.y s.1, s.2⟩ (by
    cases List.mem_cons.1 hm with
    | inl h => subst h; simp
    | inr h => exact List.mem_cons_of_mem _ (List.mem_map.2 ⟨s, h, rfl⟩))
  simpa [Projection.stepsY, Shading.at, hpx] using this

/-- A pixel whose centre is at the projection of a stop's value takes that stop's colour, when the
projected stops ascend. -/
theorem Projection.stepsX_at {α : Type u} {β : Type v} (proj : Projection α β)
    (first : α × Color) (rest : List (α × Color))
    (hs : (first :: rest).Pairwise fun a b => proj.x a.1 < proj.x b.1) {s : α × Color}
    (hm : s ∈ first :: rest) {px : Pixel} (hpx : (px.col : Rat) + 1 / 2 = proj.x s.1) :
    (proj.stepsX first rest).at px = s.2 := by
  have hs' : (Stop.mk (proj.x first.1) first.2 :: rest.map fun (v, c) => ⟨proj.x v, c⟩).Pairwise
      (·.pos < ·.pos) := by
    refine List.pairwise_cons.2 ⟨fun a ha => ?_, List.pairwise_map.2 (List.pairwise_cons.1 hs).2⟩
    obtain ⟨⟨v, c⟩, hm, rfl⟩ := List.mem_map.1 ha
    exact (List.pairwise_cons.1 hs).1 _ hm
  have := evalSteps_at _ _ hs' ⟨proj.x s.1, s.2⟩ (by
    cases List.mem_cons.1 hm with
    | inl h => subst h; simp
    | inr h => exact List.mem_cons_of_mem _ (List.mem_map.2 ⟨s, h, rfl⟩))
  simpa [Projection.stepsX, Shading.at, hpx] using this

/-- The projected points of a series, a missing value staying missing. -/
def Projection.points {α : Type u} {β : Type v} [LE α] (proj : Projection α β) (s : Series α β) :
    List (Option Pt) :=
  s.points.toList.map fun (x, v) => v.map fun y => ⟨proj.x x, proj.y y⟩

/-- Splits at each missing value into the runs of present values between them. -/
def runsOf : List (Option Pt) → List (List Pt)
  | [] => []
  | none :: rest => [] :: runsOf rest
  | some p :: rest =>
    match runsOf rest with
    | [] => [[p]]
    | r :: rs => (p :: r) :: rs

private def runsStep : Option Pt → List (List Pt) → List (List Pt)
  | none, rs => [] :: rs
  | some p, [] => [[p]]
  | some p, r :: rs => (p :: r) :: rs

/-- The compiled form of `runsOf`: a fold, which the compiler runs in constant stack. -/
private def runsOfFold (l : List (Option Pt)) : List (List Pt) := l.foldr runsStep []

@[csimp] private theorem runsOf_eq_fold : @runsOf = @runsOfFold := by
  funext l
  show runsOf l = l.foldr runsStep []
  induction l with
  | nil => rfl
  | cons o rest ih =>
    rw [List.foldr_cons, ← ih]
    cases o <;> rw [runsOf]
    · rfl
    · cases runsOf rest <;> rfl

/-- The runs of a segmented series: no run spans a break between segments or a missing value, so
the points of a run are consecutive present points of one segment. -/
def Projection.runs {α : Type u} {β : Type v} [LE α] (proj : Projection α β) (g : Segmented α β) :
    List (List Pt) :=
  g.segments.toList.flatMap fun s => runsOf (proj.points s)

/-- The runs as strip items, each followed by an explicit gap. -/
def Item.ofRuns : List (List Pt) → List (Item Pt)
  | [] => []
  | r :: rs => r.map Item.val ++ Item.gap :: Item.ofRuns rs

/-- The compiled form of `Item.ofRuns`: a fold, which the compiler runs in constant stack. -/
private def Item.ofRunsFold (rs : List (List Pt)) : List (Item Pt) :=
  rs.foldr (fun r acc => r.map Item.val ++ Item.gap :: acc) []

@[csimp] private theorem Item.ofRuns_eq_fold : @Item.ofRuns = @Item.ofRunsFold := by
  funext rs
  show Item.ofRuns rs = rs.foldr _ []
  induction rs with
  | nil => rfl
  | cons r rs ih => rw [List.foldr_cons, ← ih]; rfl

/-- However a strip is drawn, its runs are drawn separately: the gap between two runs joins
nothing. -/
theorem Item.chain_ofRuns {single : Pt → Region} {join : Pt → Pt → Region}
    (rs : List (List Pt)) (p : Pt) :
    Item.chain single join (Item.ofRuns rs) p ↔
      ∃ r ∈ rs, Item.chain single join (r.map Item.val) p := by
  induction rs with
  | nil => simp [Item.ofRuns, Item.chain]
  | cons r rs ih =>
    rw [Item.ofRuns, Item.chain_append_gap, ih]
    simp

/-- Splitting a strip built from runs at its gaps gives the runs back. -/
theorem Item.runs_ofRuns (rs : List (List Pt)) : Item.runs (Item.ofRuns rs) = rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    rw [Item.ofRuns, Item.runs_append_gap, ih]

theorem runsOf_flatten (l : List (Option Pt)) : (runsOf l).flatten = l.filterMap id := by
  induction l with
  | nil => rfl
  | cons o rest ih =>
    cases o with
    | none => simpa [runsOf] using ih
    | some p =>
      simp only [runsOf]
      cases hr : runsOf rest with
      | nil =>
        rw [hr] at ih
        simp only [List.flatten_nil] at ih
        simp [← ih]
      | cons r rs =>
        rw [hr] at ih
        simp only [List.flatten_cons] at ih
        simp [← ih]

private theorem runsOf_spec (l : List (Option Pt)) :
    (∀ r ∈ runsOf l, ∀ a, a ∈ r → some a ∈ l) ∧
    (∀ r ∈ runsOf l, ∀ a b, [a, b] <:+: r → [some a, some b] <:+: l) ∧
    (∀ r rs, runsOf l = r :: rs → ∀ q r', r = q :: r' → ∃ t, l = some q :: t) := by
  induction l with
  | nil => simp [runsOf]
  | cons o rest ih =>
    obtain ⟨ih1, ih2, ih3⟩ := ih
    cases o with
    | none =>
      simp only [runsOf]
      refine ⟨?_, ?_, ?_⟩
      · intro r hr a ha
        rcases List.mem_cons.mp hr with rfl | hr
        · simp at ha
        · exact List.mem_cons_of_mem _ (ih1 r hr a ha)
      · intro r hr a b hab
        rcases List.mem_cons.mp hr with rfl | hr
        · simp at hab
        · exact List.infix_cons (ih2 r hr a b hab)
      · intro r rs h q r' hr
        simp only [List.cons.injEq] at h
        obtain ⟨rfl, -⟩ := h
        simp at hr
    | some p =>
      simp only [runsOf]
      cases hr : runsOf rest with
      | nil =>
        refine ⟨?_, ?_, ?_⟩
        · intro r hr a ha
          simp only [List.mem_singleton] at hr
          subst hr
          simp_all
        · intro r hr a b hab
          simp only [List.mem_singleton] at hr
          subst hr
          have := hab.length_le
          simp at this
        · intro r rs h q r' hq
          simp only [List.cons.injEq] at h
          obtain ⟨rfl, -⟩ := h
          simp only [List.cons.injEq] at hq
          obtain ⟨rfl, -⟩ := hq
          exact ⟨rest, rfl⟩
      | cons r0 rs0 =>
        rw [hr] at ih1 ih2 ih3
        refine ⟨?_, ?_, ?_⟩
        · intro r hr' a ha
          rcases List.mem_cons.mp hr' with rfl | hr'
          · rcases List.mem_cons.mp ha with rfl | ha
            · simp
            · exact List.mem_cons_of_mem _ (ih1 r0 (List.mem_cons_self ..) a ha)
          · exact List.mem_cons_of_mem _ (ih1 r (List.mem_cons_of_mem _ hr') a ha)
        · intro r hr' a b hab
          rcases List.mem_cons.mp hr' with rfl | hr'
          · rcases List.infix_cons_iff.mp hab with hpre | hin
            · obtain ⟨hap, t, ht⟩ := List.cons_prefix_cons.mp hpre
              have ht' : r0 = b :: t := by simpa using ht.symm
              obtain ⟨u, hu⟩ := ih3 r0 rs0 rfl b t ht'
              rw [hap, hu]
              exact ⟨[], u, by simp⟩
            · exact List.infix_cons (ih2 r0 (List.mem_cons_self ..) a b hin)
          · exact List.infix_cons (ih2 r (List.mem_cons_of_mem _ hr') a b hab)
        · intro r rs h q r' hq
          simp only [List.cons.injEq] at h
          obtain ⟨rfl, -⟩ := h
          simp only [List.cons.injEq] at hq
          obtain ⟨rfl, -⟩ := hq
          exact ⟨rest, rfl⟩

theorem Region.thicken_zero (a : Region) (p : Pt) : Region.thicken 0 a p ↔ a p := by
  constructor
  · rintro ⟨q, hq, h⟩
    simp only [Region.disc, Rat.zero_mul] at h
    have hx := mul_self_nonneg' (p.x - q.x)
    have hy := mul_self_nonneg' (p.y - q.y)
    have hx0 : (p.x - q.x) * (p.x - q.x) = 0 := by grind
    have hy0 : (p.y - q.y) * (p.y - q.y) = 0 := by grind
    have h1 : p.x - q.x = 0 := by grind
    have h2 : p.y - q.y = 0 := by grind
    have : p = q := by
      cases p; cases q; simp only [Pt.mk.injEq]; grind
    rwa [this]
  · exact fun h => Region.sub_thicken 0 a p h

theorem Region.covers_exists {α : Type} {rs : List α} {f : α → Region} {px : Pixel} :
    Region.Covers (fun p => ∃ r ∈ rs, f r p) px ↔ ∃ r ∈ rs, (f r).Covers px :=
  ⟨fun ⟨p, ⟨r, hr, h⟩, hc⟩ => ⟨r, hr, p, h, hc⟩, fun ⟨r, hr, p, h, hc⟩ => ⟨p, ⟨r, hr, h⟩, hc⟩⟩

/-- A shading and a layer: how a chart paints its marks. A `Color` is a flat shading. -/
structure Paint where
  layer : Nat
  color : Shading

/-- A line chart's style. `halfWidth` is in the projection's units (pixels for a pixel projection). `reduce` aggregates each run to the first, last, lowest and highest value
of each pixel column class, which draws the same pixels as the full data for a bare line
(`compileLine_covers_iff`); a thick line is not covered by that guarantee. A `dash` cuts each run,
after joining and reducing, into dashes (`dashRun`), each within the undashed line; `none` is solid. -/
structure LineStyle where
  paint : Paint
  halfWidth : Rat
  reduce : Bool
  dash : Option DashPattern := none
  join : Join := .straight

/-- The runs cut into dashes, or as they are when there is no pattern. -/
def dashRuns : Option DashPattern → List (List Pt) → List (List Pt)
  | none, runs => runs
  | some d, runs => runs.flatMap (dashRun d)

theorem dashRuns_none (runs : List (List Pt)) : dashRuns none runs = runs := rfl

theorem dashRuns_some (d : DashPattern) (runs : List (List Pt)) :
    dashRuns (some d) runs = runs.flatMap (dashRun d) := rfl

/-- A line chart: one strip, broken at every gap and missing value. -/
def compileLine {α : Type u} {β : Type v} [LE α] (st : LineStyle) (proj : Projection α β)
    (g : Segmented α β) : DisplayList :=
  let runs := joinRuns st.join (proj.runs g)
  let runs := if st.reduce then runs.map reducePoints else runs
  let runs := dashRuns st.dash runs
  #[⟨st.paint.layer, st.paint.color,
    .strip st.halfWidth (Item.ofRuns runs)⟩]

/-- An area chart: the area between the series and the line at `baseline`, broken at every gap and
missing value. -/
def compileArea {α : Type u} {β : Type v} [LE α] (paint : Paint) (baseline : β)
    (proj : Projection α β) (g : Segmented α β) (join : Join := .straight) : DisplayList :=
  #[⟨paint.layer, paint.color, .area (proj.y baseline) (Item.ofRuns (joinRuns join (proj.runs g)))⟩]

/-- The items of an envelope over per-column extents, `none` being an absent column: the present
columns, with one gap in place of each stretch of absent columns after a present one. The flag is
whether the last item is a gap or there is none yet. -/
def envelopeItems : Bool → List (Option Column) → List (Item Column)
  | _, [] => []
  | _, some c :: rest => .val c :: envelopeItems false rest
  | true, none :: rest => envelopeItems true rest
  | false, none :: rest => .gap :: envelopeItems true rest

/-- The compiled form of `envelopeItems`: an accumulator loop. -/
private def envelopeItemsAux : Bool → List (Item Column) → List (Option Column) → List (Item Column)
  | _, acc, [] => acc.reverse
  | _, acc, some c :: rest => envelopeItemsAux false (.val c :: acc) rest
  | true, acc, none :: rest => envelopeItemsAux true acc rest
  | false, acc, none :: rest => envelopeItemsAux true (.gap :: acc) rest

private theorem envelopeItemsAux_eq (l : List (Option Column)) :
    ∀ (b : Bool) (acc : List (Item Column)),
      envelopeItemsAux b acc l = acc.reverse ++ envelopeItems b l := by
  induction l with
  | nil => intro b acc; simp [envelopeItemsAux, envelopeItems]
  | cons o rest ih =>
    intro b acc
    cases o with
    | some c => simp [envelopeItemsAux, envelopeItems, ih]
    | none => cases b <;> simp [envelopeItemsAux, envelopeItems, ih]

private def envelopeItemsLoop (b : Bool) (l : List (Option Column)) : List (Item Column) :=
  envelopeItemsAux b [] l

@[csimp] private theorem envelopeItems_eq_loop : @envelopeItems = @envelopeItemsLoop := by
  funext b l
  simp [envelopeItemsLoop, envelopeItemsAux_eq]

/-- The projected columns of per-column extents, an absent column staying absent. Column `i` lies
at `proj.x i`. -/
def envelopeColumns {β : Type v} (proj : Projection Nat β) (cols : Array (Option (β × β))) :
    List (Option Column) :=
  cols.toList.mapIdx fun i o => o.map fun (lo, hi) => ⟨proj.x i, proj.y lo, proj.y hi⟩

/-- An envelope chart: the lowest and highest value of each column, drawn as one envelope. An absent
column is not drawn, and the columns on either side of it are not joined. -/
def compileEnvelope {β : Type v} (paint : Paint) (proj : Projection Nat β)
    (cols : Array (Option (β × β))) : DisplayList :=
  #[⟨paint.layer, paint.color, .envelope (envelopeItems true (envelopeColumns proj cols))⟩]

/-- The extents of Core's `Pyramid.columns` over `Minimum β × Maximum β` as envelope columns: a
column with no samples is absent. -/
def extentColumns {β : Type v} [LE β] [DecidableLE β] (cols : Array (Minimum β × Maximum β)) :
    Array (Option (β × β)) :=
  cols.map fun (mn, mx) => do pure (← mn.get, ← mx.get)

/-- An envelope chart drawn straight from per-column extents. -/
def compileEnvelopeOfExtents {β : Type v} [LE β] [DecidableLE β] (paint : Paint)
    (proj : Projection Nat β) (cols : Array (Minimum β × Maximum β)) : DisplayList :=
  compileEnvelope paint proj (extentColumns cols)

/-- A bar chart's style: `width` is the bar width in the projection's units (pixels for a pixel projection), not in data units; `compileStackedBarsBy` sizes bars by their spacing instead. -/
structure BarStyle where
  paint : Paint
  width : Rat

/-- A bar chart: for each present value, a bar `width` wide (in the projection's units) centred on its x, from `baseline` to the
value. A missing value has no bar. -/
def compileBars {α : Type u} {β : Type v} [LE α] (st : BarStyle) (baseline : β)
    (proj : Projection α β) (s : Series α β) : DisplayList :=
  s.points.filterMap fun (x, v) =>
    v.map fun y => ⟨st.paint.layer, st.paint.color,
      .rect ⟨proj.x x - st.width / 2, proj.y baseline, proj.x x + st.width / 2, proj.y y⟩⟩

/-- A scatter chart's style: `radius` is in the projection's units (pixels for a pixel projection). -/
structure ScatterStyle where
  paint : Paint
  shape : MarkerShape
  radius : Rat

/-- A scatter chart: a marker at each present value. -/
def compileScatter {α : Type u} {β : Type v} [LE α] (st : ScatterStyle) (proj : Projection α β)
    (s : Series α β) : DisplayList :=
  s.points.filterMap fun (x, v) =>
    v.map fun y => ⟨st.paint.layer, st.paint.color,
      .marker st.shape ⟨proj.x x, proj.y y⟩ st.radius⟩

/-- A scatter chart whose marker radius depends on the value: each present value gets `radius` of it. -/
def compileScatterBy {α : Type u} {β : Type v} [LE α] (st : ScatterStyle) (radius : β → Rat)
    (proj : Projection α β) (s : Series α β) : DisplayList :=
  s.points.filterMap fun (x, v) =>
    v.map fun y => ⟨st.paint.layer, st.paint.color,
      .marker st.shape ⟨proj.x x, proj.y y⟩ (radius y)⟩

/-- A marker at each sample a line cannot show: the runs of exactly one sample. -/
def compileIsolated {α : Type u} {β : Type v} [LE α] (st : ScatterStyle) (proj : Projection α β)
    (g : Segmented α β) : DisplayList :=
  (proj.runs g).toArray.filterMap fun
    | [p] => some ⟨st.paint.layer, st.paint.color, .marker st.shape p st.radius⟩
    | _ => none

/-- A hollow disc marker: `outline` out to `radius`, with `fill` over it out to `radius - stroke`. -/
structure RingStyle where
  layer : Nat
  outline : Color
  fill : Color
  radius : Rat
  stroke : Rat

/-- A hollow marker centred at `center`: a disc over a larger disc. -/
def compileRing (st : RingStyle) (center : Pt) : DisplayList :=
  #[⟨st.layer, st.outline, .marker .circle center st.radius⟩,
    ⟨st.layer, st.fill, .marker .circle center (st.radius - st.stroke)⟩]

/-- A heatmap cell: the rectangle from `(x0, y0)` to `(x1, y1)` and its value, if any. -/
structure Cell (α : Type u) (β : Type v) (γ : Type) where
  x0 : α
  x1 : α
  y0 : β
  y1 : β
  value : Option γ

/-- A heatmap: a rectangle for each cell with a value, coloured by `colorOf`. -/
def compileHeatmap {α : Type u} {β : Type v} {γ : Type} (layer : Nat) (colorOf : γ → Color)
    (proj : Projection α β) (cells : Array (Cell α β γ)) : DisplayList :=
  cells.filterMap fun c =>
    c.value.map fun v => ⟨layer, colorOf v,
      .rect ⟨proj.x c.x0, proj.y c.y0, proj.x c.x1, proj.y c.y1⟩⟩

section Theorems

variable {α : Type u} {β : Type v} [LE α]

private theorem covers_singleton {c : Command} {px : Pixel} :
    DisplayList.Covers #[c] px ↔ c.shape.region.Covers px := by
  simp [DisplayList.Covers, Command.Covers]

private theorem strip_covers_runs {c : Command} {hw : Rat} {rs : List (List Pt)} {px : Pixel}
    (h : c.shape = .strip hw (Item.ofRuns rs)) :
    c.Covers px ↔ ∃ r ∈ rs, (Region.thicken hw (poly r)).Covers px := by
  have : c.shape.region = fun p => ∃ r ∈ rs, Region.thicken hw (poly r) p := by
    rw [h]
    funext p
    apply propext
    simp only [Shape.region, Region.thicken, Item.chain_ofRuns]
    constructor
    · rintro ⟨q, ⟨r, hr, hq⟩, hd⟩; exact ⟨r, hr, q, hq, hd⟩
    · rintro ⟨r, hr, q, hq, hd⟩; exact ⟨q, ⟨r, hr, hq⟩, hd⟩
  simp only [Command.Covers, this]
  exact Region.covers_exists

/-- Reducing a bare line to the first, last, lowest and highest value of each pixel column class
draws exactly the pixels the full data does. The theorem holds for every series, sorted
or not: it needs no assumption about the data or the projection. -/
theorem compileLine_covers_iff (st : LineStyle) (hw : st.halfWidth = 0) (hd : st.dash = none)
    (proj : Projection α β)
    (g : Segmented α β) (px : Pixel) :
    (compileLine st proj g).Covers px ↔
      (compileLine { st with reduce := false } proj g).Covers px := by
  have key : ∀ b : Bool, (compileLine { st with reduce := b } proj g).Covers px ↔
      ∃ r ∈ (if b then (joinRuns st.join (proj.runs g)).map reducePoints
        else joinRuns st.join (proj.runs g)), (poly r).Covers px := by
    intro b
    rw [compileLine, covers_singleton]
    rw [← Command.Covers, strip_covers_runs
      (hw := st.halfWidth) (rs := if b then (joinRuns st.join (proj.runs g)).map reducePoints
        else joinRuns st.join (proj.runs g))
      (by simp [hd, dashRuns])]
    simp only [hw]
    exact ⟨fun ⟨r, hr, h⟩ => ⟨r, hr, Region.covers_congr (Region.thicken_zero _) px |>.mp h⟩,
      fun ⟨r, hr, h⟩ => ⟨r, hr, Region.covers_congr (Region.thicken_zero _) px |>.mpr h⟩⟩
  have e : { st with reduce := st.reduce } = st := rfl
  have hL := key st.reduce
  rw [e] at hL
  rw [hL, key false]
  cases hb : st.reduce
  · exact Iff.rfl
  · simp only [ite_true, List.mem_map]
    constructor
    · rintro ⟨_, ⟨r, hr, rfl⟩, h⟩
      exact ⟨r, hr, (reducePoints_covers r px).mp h⟩
    · rintro ⟨r, hr, h⟩
      exact ⟨reducePoints r, ⟨r, hr, rfl⟩, (reducePoints_covers r px).mpr h⟩

/-- No line is drawn across a gap: every point of the unreduced bare line of a segmented
series is a projected present point, or lies on the segment between two projected present points
that are adjacent in one segment, with no break and no missing value between them. -/
theorem compileLine_no_bridge (st : LineStyle) (hw : st.halfWidth = 0) (hr : st.reduce = false)
    (hd : st.dash = none) (hj : st.join = .straight) (proj : Projection α β) (g : Segmented α β)
    {c : Command} (hc : c ∈ compileLine st proj g) {p : Pt} (h : c.shape.region p) :
    ∃ s ∈ g.segments.toList, some p ∈ proj.points s ∨
      ∃ a b, [some a, some b] <:+: proj.points s ∧ Region.seg a b p := by
  have hcmd : c = ⟨st.paint.layer, st.paint.color,
      .strip st.halfWidth (Item.ofRuns (proj.runs g))⟩ := by
    simpa [compileLine, hr, hd, hj, dashRuns, joinRuns_straight] using hc
  subst hcmd
  simp only [Shape.region, hw, Region.thicken_zero, Item.chain_ofRuns] at h
  obtain ⟨r, hrun, hp⟩ := h
  change poly r p at hp
  obtain ⟨s, hs, hrs⟩ := List.mem_flatMap.mp hrun
  refine ⟨s, hs, ?_⟩
  obtain ⟨h1, h2, -⟩ := runsOf_spec (proj.points s)
  rcases poly_mem_adj hp with hm | ⟨a, b, hi, hseg⟩
  · exact Or.inl (h1 r hrs p hm)
  · exact Or.inr ⟨a, b, h2 r hrs a b hi, hseg⟩

/-- A dashed line draws nothing the same line undashed does not: its dashes lie within the undashed
strip's region, so the line is still never drawn across a gap. -/
theorem compileLine_dash_sub (st : LineStyle) (proj : Projection α β) (g : Segmented α β)
    {c : Command} (hc : c ∈ compileLine st proj g) {p : Pt} (h : c.shape.region p) :
    ∃ c' ∈ compileLine { st with dash := none } proj g, c'.shape.region p := by
  refine ⟨_, Array.mem_singleton.mpr rfl, ?_⟩
  have hcmd : c = ⟨st.paint.layer, st.paint.color, .strip st.halfWidth (Item.ofRuns
      (dashRuns st.dash (if st.reduce then (joinRuns st.join (proj.runs g)).map reducePoints else joinRuns st.join (proj.runs g))))⟩ := by
    simpa [compileLine] using hc
  subst hcmd
  simp only [Shape.region, Region.thicken, Item.chain_ofRuns] at h ⊢
  obtain ⟨q, ⟨r, hr, hq⟩, hd⟩ := h
  refine ⟨q, ?_, hd⟩
  cases hdash : st.dash with
  | none =>
    simp only [hdash, dashRuns] at hr ⊢
    exact ⟨r, hr, hq⟩
  | some d =>
    simp only [hdash, dashRuns] at hr
    obtain ⟨l, hl, hrl⟩ := List.mem_flatMap.mp hr
    exact ⟨l, by simpa [dashRuns] using hl, dashRun_sub _ _ hrl q hq⟩

/-- Whatever the join, a bare unreduced undashed line draws only along the joined runs, each run
joined on its own. -/
theorem compileLine_join_runs (st : LineStyle) (hw : st.halfWidth = 0) (hr : st.reduce = false)
    (hd : st.dash = none) (proj : Projection α β) (g : Segmented α β) {c : Command}
    (hc : c ∈ compileLine st proj g) {p : Pt} (h : c.shape.region p) :
    ∃ r ∈ proj.runs g, poly (joinRun st.join r) p := by
  have hcmd : c = ⟨st.paint.layer, st.paint.color,
      .strip st.halfWidth (Item.ofRuns (joinRuns st.join (proj.runs g)))⟩ := by
    simpa [compileLine, hr, hd, dashRuns] using hc
  subst hcmd
  simp only [Shape.region, hw, Region.thicken_zero, Item.chain_ofRuns] at h
  obtain ⟨r, hrun, hp⟩ := h
  obtain ⟨r0, hr0, rfl⟩ := List.mem_map.mp hrun
  exact ⟨r0, hr0, hp⟩

/-- An area chart's runs are filled separately, as a strip's are. -/
theorem compileArea_no_bridge (paint : Paint) (baseline : β) (proj : Projection α β)
    (g : Segmented α β) (join : Join) {c : Command}
    (hc : c ∈ compileArea paint baseline proj g join) {p : Pt} (h : c.shape.region p) :
    ∃ r ∈ proj.runs g, (Shape.area (proj.y baseline) ((joinRun join r).map Item.val)).region p := by
  have hcmd : c = ⟨paint.layer, paint.color,
      .area (proj.y baseline) (Item.ofRuns (joinRuns join (proj.runs g)))⟩ := by
    simpa [compileArea] using hc
  subst hcmd
  obtain ⟨r, hr, hp⟩ := (Item.chain_ofRuns _ _).mp h
  obtain ⟨r0, hr0, rfl⟩ := List.mem_map.mp hr
  exact ⟨r0, hr0, hp⟩

theorem mem_compileBars (st : BarStyle) (baseline : β) (proj : Projection α β) (s : Series α β)
    (c : Command) :
    c ∈ compileBars st baseline proj s ↔ ∃ x y, (x, some y) ∈ s.points ∧
      c = ⟨st.paint.layer, st.paint.color, .rect ⟨proj.x x - st.width / 2, proj.y baseline,
        proj.x x + st.width / 2, proj.y y⟩⟩ := by
  simp only [compileBars, Array.mem_filterMap]
  constructor
  · rintro ⟨⟨x, _ | y⟩, hm, h⟩
    · simp at h
    · exact ⟨x, y, hm, by simpa using h.symm⟩
  · rintro ⟨x, y, hm, rfl⟩
    exact ⟨(x, some y), hm, rfl⟩

theorem mem_compileScatter (st : ScatterStyle) (proj : Projection α β) (s : Series α β)
    (c : Command) :
    c ∈ compileScatter st proj s ↔ ∃ x y, (x, some y) ∈ s.points ∧
      c = ⟨st.paint.layer, st.paint.color, .marker st.shape ⟨proj.x x, proj.y y⟩ st.radius⟩ := by
  simp only [compileScatter, Array.mem_filterMap]
  constructor
  · rintro ⟨⟨x, _ | y⟩, hm, h⟩
    · simp at h
    · exact ⟨x, y, hm, by simpa using h.symm⟩
  · rintro ⟨x, y, hm, rfl⟩
    exact ⟨(x, some y), hm, rfl⟩

theorem mem_compileScatterBy (st : ScatterStyle) (radius : β → Rat) (proj : Projection α β)
    (s : Series α β) (c : Command) :
    c ∈ compileScatterBy st radius proj s ↔ ∃ x y, (x, some y) ∈ s.points ∧
      c = ⟨st.paint.layer, st.paint.color, .marker st.shape ⟨proj.x x, proj.y y⟩ (radius y)⟩ := by
  simp only [compileScatterBy, Array.mem_filterMap]
  constructor
  · rintro ⟨⟨x, _ | y⟩, hm, h⟩
    · simp at h
    · exact ⟨x, y, hm, by simpa using h.symm⟩
  · rintro ⟨x, y, hm, rfl⟩
    exact ⟨(x, some y), hm, rfl⟩

/-- Every present sample is drawn: a pixel containing its projected point is covered, so no
sample is lost however small the marker. -/
theorem compileScatter_covers (st : ScatterStyle) (hr : 0 ≤ st.radius) (proj : Projection α β)
    (s : Series α β) {x : α} {y : β} (hm : (x, some y) ∈ s.points) {px : Pixel}
    (hc : px.Contains ⟨proj.x x, proj.y y⟩) : (compileScatter st proj s).Covers px := by
  refine ⟨_, (mem_compileScatter st proj s _).mpr ⟨x, y, hm, rfl⟩, ⟨proj.x x, proj.y y⟩, ?_, hc⟩
  cases hs : st.shape with
  | square =>
    simp only [Shape.region, Region.box, Between]
    grind
  | circle =>
    simp only [Shape.region, Region.disc, Rat.sub_self, Rat.zero_mul, Rat.add_zero]
    exact mul_self_nonneg' _

/-- A marker is drawn for exactly the runs of one sample. -/
theorem mem_compileIsolated (st : ScatterStyle) (proj : Projection α β) (g : Segmented α β)
    (c : Command) :
    c ∈ compileIsolated st proj g ↔ ∃ p, [p] ∈ proj.runs g ∧
      c = ⟨st.paint.layer, st.paint.color, .marker st.shape p st.radius⟩ := by
  simp only [compileIsolated, Array.mem_filterMap, List.mem_toArray]
  constructor
  · rintro ⟨r, hr, h⟩
    match r, h with
    | [p], h => exact ⟨p, hr, by simpa using h.symm⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨[p], hp, rfl⟩

/-- A hollow marker lies within its outer radius and fills it: its extent is `radius`, for a stroke
no wider than the radius. -/
theorem compileRing_extent (st : RingStyle) (center : Pt) (h0 : 0 ≤ st.stroke)
    (h1 : st.stroke ≤ st.radius) (p : Pt) :
    (∃ c ∈ compileRing st center, c.shape.region p) ↔ Region.disc center st.radius p := by
  have hin : 0 ≤ st.radius - st.stroke := by grind
  have hle : st.radius - st.stroke ≤ st.radius := by grind
  simp only [compileRing, Array.mem_def, List.mem_cons, List.not_mem_nil,
    or_false]
  constructor
  · rintro ⟨c, rfl | rfl, h⟩
    · exact h
    · simp only [Shape.region, Region.disc] at h ⊢
      have : (st.radius - st.stroke) * (st.radius - st.stroke) ≤ st.radius * st.radius :=
        by
        have := Rat.mul_nonneg h0 (b := 2 * st.radius - st.stroke) (by grind)
        grind
      exact Rat.le_trans h this
  · intro h
    exact ⟨_, Or.inl rfl, h⟩

omit [LE α] in
theorem mem_compileHeatmap {γ : Type} (layer : Nat) (colorOf : γ → Color) (proj : Projection α β)
    (cells : Array (Cell α β γ)) (c : Command) :
    c ∈ compileHeatmap layer colorOf proj cells ↔ ∃ cell ∈ cells, ∃ v, cell.value = some v ∧
      c = ⟨layer, colorOf v, .rect ⟨proj.x cell.x0, proj.y cell.y0, proj.x cell.x1,
        proj.y cell.y1⟩⟩ := by
  simp only [compileHeatmap, Array.mem_filterMap]
  constructor
  · rintro ⟨cell, hm, h⟩
    cases hv : cell.value with
    | none => simp [hv] at h
    | some v => exact ⟨cell, hm, v, hv, by simpa [hv] using h.symm⟩
  · rintro ⟨cell, hm, v, hv, rfl⟩
    exact ⟨cell, hm, by simp [hv]⟩

theorem mem_envelopeItems (f : Bool) (l : List (Option Column)) (c : Column) :
    Item.val c ∈ envelopeItems f l ↔ some c ∈ l := by
  induction l generalizing f with
  | nil => simp [envelopeItems]
  | cons o rest ih =>
    cases o with
    | some d => simp [envelopeItems, ih]
    | none => cases f <;> simp [envelopeItems, ih]

/-- Nothing joins the columns either side of an absent one: a point of an envelope lies in the span
of one column, or between two columns that are adjacent in the input. -/
theorem envelopeItems_no_bridge (f : Bool) (l : List (Option Column)) {p : Pt}
    (h : Item.chain (fun c => Region.span c.x c.x c.lo c.lo c.hi c.hi)
      (fun a b => Region.span a.x b.x a.lo b.lo a.hi b.hi) (envelopeItems f l) p) :
    (∃ c, some c ∈ l ∧ Region.span c.x c.x c.lo c.lo c.hi c.hi p) ∨
      ∃ a b, [some a, some b] <:+: l ∧ Region.span a.x b.x a.lo b.lo a.hi b.hi p := by
  induction l generalizing f with
  | nil => simp [envelopeItems, Item.chain] at h
  | cons o rest ih =>
    cases o with
    | none =>
      cases f
      · simp only [envelopeItems, Item.chain] at h
        rcases ih true h with ⟨c, hc, hp⟩ | ⟨a, b, hi, hp⟩
        · exact Or.inl ⟨c, List.mem_cons_of_mem _ hc, hp⟩
        · exact Or.inr ⟨a, b, List.infix_cons hi, hp⟩
      · simp only [envelopeItems] at h
        rcases ih true h with ⟨c, hc, hp⟩ | ⟨a, b, hi, hp⟩
        · exact Or.inl ⟨c, List.mem_cons_of_mem _ hc, hp⟩
        · exact Or.inr ⟨a, b, List.infix_cons hi, hp⟩
    | some a =>
      simp only [envelopeItems, Item.chain] at h
      rcases h with h | h | h
      · exact Or.inl ⟨a, List.mem_cons_self .., h⟩
      · cases rest with
        | nil => simp [envelopeItems] at h
        | cons o' rest' =>
          cases o' with
          | none => cases rest' <;> simp [envelopeItems] at h
          | some b =>
            simp only [envelopeItems] at h
            exact Or.inr ⟨a, b, ⟨[], rest', by simp⟩, h⟩
      · rcases ih false h with ⟨c, hc, hp⟩ | ⟨a', b, hi, hp⟩
        · exact Or.inl ⟨c, List.mem_cons_of_mem _ hc, hp⟩
        · exact Or.inr ⟨a', b, List.infix_cons hi, hp⟩

theorem mem_envelopeColumns {β : Type v} (proj : Projection Nat β) (cols : Array (Option (β × β)))
    (c : Column) :
    some c ∈ envelopeColumns proj cols ↔
      ∃ i lo hi, cols[i]? = some (some (lo, hi)) ∧ c = ⟨proj.x i, proj.y lo, proj.y hi⟩ := by
  simp only [envelopeColumns, List.mem_mapIdx, Array.getElem?_eq_some_iff]
  constructor
  · rintro ⟨i, hi, h⟩
    have hi' : i < cols.size := by simpa using hi
    cases hc : cols[i] with
    | none => simp [hc] at h
    | some v =>
      obtain ⟨lo, hi2⟩ := v
      refine ⟨i, lo, hi2, ⟨hi', hc⟩, ?_⟩
      simp [hc] at h
      exact h.symm
  · rintro ⟨i, lo, hi, ⟨hlt, h⟩, rfl⟩
    refine ⟨i, by simpa using hlt, ?_⟩
    simp [h]

/-- Exactly the present columns are drawn: each at its own x, and no absent column contributes. -/
theorem mem_compileEnvelope_columns {β : Type v} (paint : Paint) (proj : Projection Nat β)
    (cols : Array (Option (β × β))) (c : Column) :
    (∃ cmd ∈ compileEnvelope paint proj cols, ∃ items, cmd.shape = .envelope items ∧
        Item.val c ∈ items) ↔
      ∃ i lo hi, cols[i]? = some (some (lo, hi)) ∧ c = ⟨proj.x i, proj.y lo, proj.y hi⟩ := by
  rw [← mem_envelopeColumns, ← mem_envelopeItems true]
  simp [compileEnvelope]

/-- No line is drawn across an absent column: every point of the envelope lies in the span of one
present column, or between two present columns that are adjacent in the input. -/
theorem compileEnvelope_no_bridge {β : Type v} (paint : Paint) (proj : Projection Nat β)
    (cols : Array (Option (β × β))) {c : Command} (hc : c ∈ compileEnvelope paint proj cols)
    {p : Pt} (h : c.shape.region p) :
    (∃ c, some c ∈ envelopeColumns proj cols ∧ Region.span c.x c.x c.lo c.lo c.hi c.hi p) ∨
      ∃ a b, [some a, some b] <:+: envelopeColumns proj cols ∧
        Region.span a.x b.x a.lo b.lo a.hi b.hi p := by
  have : c = ⟨paint.layer, paint.color, .envelope (envelopeItems true (envelopeColumns proj cols))⟩ := by
    simpa [compileEnvelope] using hc
  subst this
  exact envelopeItems_no_bridge true _ h

/-- Every present column is drawn: a pixel containing the projected lowest value of the column is
covered. -/
theorem compileEnvelope_covers {β : Type v} (paint : Paint) (proj : Projection Nat β)
    (cols : Array (Option (β × β))) {i : Nat} {lo hi : β} (h : cols[i]? = some (some (lo, hi)))
    {px : Pixel} (hc : px.Contains ⟨proj.x i, proj.y lo⟩) :
    (compileEnvelope paint proj cols).Covers px := by
  have hm : Item.val (⟨proj.x i, proj.y lo, proj.y hi⟩ : Column) ∈
      envelopeItems true (envelopeColumns proj cols) :=
    (mem_envelopeItems _ _ _).mpr ((mem_envelopeColumns ..).mpr ⟨i, lo, hi, h, rfl⟩)
  refine ⟨⟨paint.layer, paint.color, .envelope (envelopeItems true (envelopeColumns proj cols))⟩,
    by simp [compileEnvelope], ⟨proj.x i, proj.y lo⟩, ?_, hc⟩
  refine Item.single_sub_chain hm _ ⟨0, by grind, by grind, by grind, ?_⟩
  simp [Between]
  grind

/-- A column is absent exactly when it has no lowest or no highest value. -/
theorem extentColumns_getElem? {β : Type v} [LE β] [DecidableLE β]
    (cols : Array (Minimum β × Maximum β)) (i : Nat) {lo hi : β} :
    (extentColumns cols)[i]? = some (some (lo, hi)) ↔
      ∃ mn mx, cols[i]? = some (mn, mx) ∧ mn.get = some lo ∧ mx.get = some hi := by
  simp only [extentColumns, Array.getElem?_map]
  cases h : cols[i]? with
  | none => simp
  | some c =>
    obtain ⟨⟨a⟩, ⟨b⟩⟩ := c
    cases a <;> cases b <;> simp [Option.bind] <;> grind

/-- Drawing from extents is drawing the columns `extentColumns` reads from them. -/
theorem compileEnvelopeOfExtents_eq {β : Type v} [LE β] [DecidableLE β] (paint : Paint)
    (proj : Projection Nat β) (cols : Array (Minimum β × Maximum β)) :
    compileEnvelopeOfExtents paint proj cols = compileEnvelope paint proj (extentColumns cols) :=
  rfl

/-- A column with both extremes is drawn: a pixel containing the projected lowest value is covered. -/
theorem compileEnvelopeOfExtents_covers {β : Type v} [LE β] [DecidableLE β] (paint : Paint)
    (proj : Projection Nat β) (cols : Array (Minimum β × Maximum β)) {i : Nat} {mn : Minimum β}
    {mx : Maximum β} {lo hi : β} (h : cols[i]? = some (mn, mx)) (hl : mn.get = some lo)
    (hh : mx.get = some hi) {px : Pixel} (hc : px.Contains ⟨proj.x i, proj.y lo⟩) :
    (compileEnvelopeOfExtents paint proj cols).Covers px :=
  compileEnvelope_covers paint proj _ ((extentColumns_getElem? cols i).mpr ⟨mn, mx, h, hl, hh⟩) hc

/-- No sample lies outside the drawn column: when column `i` aggregates the samples `xs`, each
sample's value is between the extents drawn for it. -/
theorem extentColumns_bounds {γ : Type w} {β : Type v} [LE β] [DecidableLE β] [Std.IsLinearOrder β]
    (lo : γ → Minimum β) (up : γ → Maximum β) (xs : Array γ)
    (cols : Array (Minimum β × Maximum β)) {i : Nat}
    (hi' : cols[i]? = some (Aggregate.fold lo xs, Aggregate.fold up xs)) {l h : β}
    (hc : (extentColumns cols)[i]? = some (some (l, h))) {x : γ} (hx : x ∈ xs) :
    (∀ b, (lo x).get = some b → l ≤ b) ∧ (∀ b, (up x).get = some b → b ≤ h) := by
  obtain ⟨mn, mx, hm, hl, hh⟩ := (extentColumns_getElem? cols i).mp hc
  rw [hi'] at hm
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hm)
  exact ⟨fun b hb => ((Minimum.fold_get_eq_some lo xs l).mp hl).2 x hx b hb,
    fun b hb => ((Maximum.fold_get_eq_some up xs h).mp hh).2 x hx b hb⟩

end Theorems

end Inkproof.Scene
