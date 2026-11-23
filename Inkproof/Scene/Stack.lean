/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Core.Stack
import Inkproof.Scene.Compile

namespace Inkproof.Scene

open Inkproof.Core

universe u v

variable {α : Type u} {β : Type v} [LE α] [Add β] [Zero β] [LT β] [DecidableLT β]

/-- The band series `k` occupies at index `i` of a stack: from the stacked top below it, which is
zero when nothing of its sign lies below, to its own stacked top. `none` if its value is missing. -/
def stackSpan (ss : Array (Series α β)) (k i : Nat) : Option (β × β) :=
  (Series.valueAt ss k i).map fun v =>
    let neg := decide (v < 0)
    (Series.signSum ss i neg k, Series.signSum ss i neg (k + 1))

/-- The columns of series `k`'s band, one per point, `none` where its value is missing. -/
def stackedColumns (proj : Projection α β) (ss : Array (Series α β)) (k : Nat) :
    List (Option Column) :=
  match ss[k]? with
  | none => []
  | some s => s.xs.toList.mapIdx fun i x =>
    (stackSpan ss k i).map fun (lo, hi) => ⟨proj.x x, proj.y lo, proj.y hi⟩

/-- Stacked areas: series `k` filled, in `paint k`, between the stacked top below it and its own.
Nothing is drawn across a missing value. -/
def compileStackedAreas (paint : Nat → Paint) (proj : Projection α β) (ss : Array (Series α β)) :
    DisplayList :=
  (Array.range ss.size).map fun k =>
    ⟨(paint k).layer, (paint k).color,
      .envelope (envelopeItems true (stackedColumns proj ss k))⟩

/-- The bar of a column `width` wide, in the projection's units (pixels for a pixel projection),
centred on the column's x. -/
def barRect (c : Column) (width : Rat) : Rect := ⟨c.x - width / 2, c.lo, c.x + width / 2, c.hi⟩

/-- Stacked bars: for each present value of series `k`, a bar `width` wide, in the projection's
units (pixels for a pixel projection), centred on its x, from the stacked top below it to its own,
in `paint k`. To size bars by the spacing of the x values instead, use `compileStackedBarsBy`. -/
def compileStackedBars (paint : Nat → Paint) (width : Rat) (proj : Projection α β)
    (ss : Array (Series α β)) : DisplayList :=
  (Array.range ss.size).flatMap fun k =>
    ((stackedColumns proj ss k).filterMap id).toArray.map fun c =>
      ⟨(paint k).layer, (paint k).color, .rect (barRect c width)⟩

/-- The distance, in the projection's units, from the point at index `i` of `xs` to the next one,
or to the previous one for the last point. Zero for a lone point or an index past the end. -/
def pointSpacing (proj : Projection α β) (xs : Array α) (i : Nat) : Rat :=
  let d (a b : Rat) := if a < b then b - a else a - b
  match xs[i]?, xs[i + 1]? with
  | some x, some n => d (proj.x x) (proj.x n)
  | some x, none =>
    match i with
    | 0 => 0
    | j + 1 => (xs[j]?).elim 0 fun p => d (proj.x p) (proj.x x)
  | none, _ => 0

/-- Stacked bars sized by their spacing: each bar is `fraction` of the distance between its x and
its neighbour's (`pointSpacing`), so `fraction = 3 / 5` leaves a gap of two fifths whatever the
projection's units. Otherwise as `compileStackedBars`. -/
def compileStackedBarsBy (paint : Nat → Paint) (fraction : Rat) (proj : Projection α β)
    (ss : Array (Series α β)) : DisplayList :=
  (Array.range ss.size).flatMap fun k =>
    match ss[k]? with
    | none => #[]
    | some s =>
      (((stackedColumns proj ss k).mapIdx fun i c =>
          c.map fun c => (⟨(paint k).layer, (paint k).color,
            .rect (barRect c (fraction * pointSpacing proj s.xs i))⟩ : Command)).filterMap id).toArray

theorem stackSpan_top (ss : Array (Series α β)) (k i : Nat) :
    (stackSpan ss k i).map (·.2) = Series.stackAt ss k i := by
  simp [stackSpan, Series.stackAt, Option.map_map, Function.comp_def]

/-- A band's lower edge is the stacked top of the series below it, wherever that series has a
value of the same sign. -/
theorem stackSpan_lower (ss : Array (Series α β)) (k i : Nat) (v w : β)
    (hv : Series.valueAt ss (k + 1) i = some v) (hw : Series.valueAt ss k i = some w)
    (hs : decide (w < 0) = decide (v < 0)) :
    (stackSpan ss (k + 1) i).map (·.1) = Series.stackAt ss k i := by
  simp [stackSpan, Series.stackAt, hv, hw, hs]

theorem stackedColumns_getElem? (proj : Projection α β) (ss : Array (Series α β)) (k : Nat)
    (hk : k < ss.size) (i : Nat) (hi : i < ss[k].size) :
    (stackedColumns proj ss k)[i]? =
      some ((stackSpan ss k i).map fun (lo, hi) => ⟨proj.x ss[k].xs[i], proj.y lo, proj.y hi⟩) := by
  have hx : i < ss[k].xs.size := hi
  simp [stackedColumns, hk, hx]
  rfl

theorem compileStackedAreas_getElem? (paint : Nat → Paint) (proj : Projection α β)
    (ss : Array (Series α β)) (k : Nat) (hk : k < ss.size) :
    (compileStackedAreas paint proj ss)[k]? =
      some ⟨(paint k).layer, (paint k).color,
        .envelope (envelopeItems true (stackedColumns proj ss k))⟩ := by
  simp [compileStackedAreas, hk]

theorem mem_compileStackedBars (paint : Nat → Paint) (width : Rat) (proj : Projection α β)
    (ss : Array (Series α β)) (it : Command) :
    it ∈ compileStackedBars paint width proj ss ↔
      ∃ k < ss.size, ∃ c, some c ∈ stackedColumns proj ss k ∧
        it = ⟨(paint k).layer, (paint k).color,
          .rect (barRect c width)⟩ := by
  simp [compileStackedBars, List.mem_filterMap, eq_comm]

theorem barRect_width (c : Column) (width : Rat) :
    (barRect c width).x1 - (barRect c width).x0 = width := by
  simp [barRect]; grind

omit [LE α] [Add β] [Zero β] [LT β] [DecidableLT β] in
theorem pointSpacing_next (proj : Projection α β) (xs : Array α) (i : Nat) (x n : α)
    (hx : xs[i]? = some x) (hn : xs[i + 1]? = some n) :
    pointSpacing proj xs i = if proj.x x < proj.x n then proj.x n - proj.x x
      else proj.x x - proj.x n := by
  simp [pointSpacing, hx, hn]

omit [LE α] [Add β] [Zero β] [LT β] [DecidableLT β] in
theorem pointSpacing_last (proj : Projection α β) (xs : Array α) (j : Nat) (p x : α)
    (hp : xs[j]? = some p) (hx : xs[j + 1]? = some x) (hn : xs[j + 2]? = none) :
    pointSpacing proj xs (j + 1) = if proj.x p < proj.x x then proj.x x - proj.x p
      else proj.x p - proj.x x := by
  simp [pointSpacing, hx, hn, hp]

omit [LE α] [Add β] [Zero β] [LT β] [DecidableLT β] in
theorem pointSpacing_lone (proj : Projection α β) (xs : Array α) (x : α)
    (hx : xs[0]? = some x) (hn : xs[1]? = none) : pointSpacing proj xs 0 = 0 := by
  simp [pointSpacing, hx, hn]

omit [LE α] [Add β] [Zero β] [LT β] [DecidableLT β] in
theorem pointSpacing_none (proj : Projection α β) (xs : Array α) (i : Nat)
    (h : xs[i]? = none) : pointSpacing proj xs i = 0 := by
  simp [pointSpacing, h]

theorem mem_compileStackedBarsBy (paint : Nat → Paint) (fraction : Rat) (proj : Projection α β)
    (ss : Array (Series α β)) (it : Command) :
    it ∈ compileStackedBarsBy paint fraction proj ss ↔
      ∃ k, ∃ hk : k < ss.size, ∃ i c, (stackedColumns proj ss k)[i]? = some (some c) ∧
        it = ⟨(paint k).layer, (paint k).color,
          .rect (barRect c (fraction * pointSpacing proj ss[k].xs i))⟩ := by
  simp only [compileStackedBarsBy, Array.mem_flatMap, Array.mem_range]
  constructor
  · rintro ⟨k, hk, h⟩
    have hs : ss[k]? = some ss[k] := Array.getElem?_eq_getElem hk
    rw [hs] at h
    simp only [List.mem_toArray, List.mem_filterMap, List.mem_mapIdx, id] at h
    obtain ⟨o, ⟨i, hi, ho⟩, rfl⟩ := h
    cases hc : (stackedColumns proj ss k)[i] with
    | none => simp [hc] at ho
    | some c =>
      refine ⟨k, hk, i, c, by rw [List.getElem?_eq_getElem hi, hc], ?_⟩
      simp only [hc, Option.map_some] at ho
      exact (Option.some.inj ho).symm
  · rintro ⟨k, hk, i, c, hc, rfl⟩
    refine ⟨k, hk, ?_⟩
    have hs : ss[k]? = some ss[k] := Array.getElem?_eq_getElem hk
    rw [hs]
    have hi := (List.getElem?_eq_some_iff.mp hc).1
    simp only [List.mem_toArray, List.mem_filterMap, List.mem_mapIdx, id]
    refine ⟨_, ⟨i, hi, rfl⟩, ?_⟩
    have : (stackedColumns proj ss k)[i] = some c := by
      simpa [List.getElem?_eq_getElem hi] using hc
    simp [this]

/-- Each bar of `compileStackedBarsBy` is `fraction` of the distance from its x to the next
point's. -/
theorem compileStackedBarsBy_width (paint : Nat → Paint) (fraction : Rat) (proj : Projection α β)
    (ss : Array (Series α β)) (k : Nat) (hk : k < ss.size) (i : Nat) (x n : α) (c : Column)
    (hx : ss[k].xs[i]? = some x) (hn : ss[k].xs[i + 1]? = some n)
    (hc : (stackedColumns proj ss k)[i]? = some (some c)) :
    ∃ r, (⟨(paint k).layer, (paint k).color, .rect r⟩ : Command) ∈
        compileStackedBarsBy paint fraction proj ss ∧
      r.x1 - r.x0 = fraction * (if proj.x x < proj.x n then proj.x n - proj.x x
        else proj.x x - proj.x n) := by
  refine ⟨_, (mem_compileStackedBarsBy paint fraction proj ss _).mpr ⟨k, hk, i, c, hc, rfl⟩, ?_⟩
  rw [barRect_width, pointSpacing_next proj _ i x n hx hn]

end Inkproof.Scene
