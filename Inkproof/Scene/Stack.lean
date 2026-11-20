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

/-- Stacked bars: for each present value of series `k`, a bar of `width` grid units centred on its
x, from the stacked top below it to its own, in `paint k`. -/
def compileStackedBars (paint : Nat → Paint) (width : Rat) (proj : Projection α β)
    (ss : Array (Series α β)) : DisplayList :=
  (Array.range ss.size).flatMap fun k =>
    ((stackedColumns proj ss k).filterMap id).toArray.map fun c =>
      ⟨(paint k).layer, (paint k).color,
        .rect ⟨c.x - width / 2, c.lo, c.x + width / 2, c.hi⟩⟩

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
          .rect ⟨c.x - width / 2, c.lo, c.x + width / 2, c.hi⟩⟩ := by
  simp [compileStackedBars, List.mem_filterMap, eq_comm]

end Inkproof.Scene
