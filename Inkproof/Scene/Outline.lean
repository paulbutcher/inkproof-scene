/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Scene.Clip

namespace Inkproof.Scene

/-- Where a border of width `w` lies on a rectangle's edge: wholly inside it, or half either side. -/
inductive OutlinePlacement where
  | inside
  | centred
  deriving DecidableEq, Repr

/-- How far the border's outer edge lies beyond the rectangle's edge. -/
def OutlinePlacement.reach (w : Rat) : OutlinePlacement → Rat
  | .inside => 0
  | .centred => w / 2

theorem OutlinePlacement.reach_inside (w : Rat) : OutlinePlacement.reach w .inside = 0 := rfl

theorem OutlinePlacement.reach_centred (w : Rat) : OutlinePlacement.reach w .centred = w / 2 := rfl

/-- A border of width `w` round the rectangle, as rectangles that meet only along their edges: the
top and bottom strips across the full outer width, and the left and right strips between them.
When the border leaves no hole it is the one rectangle that the border's outer edge bounds. A
width that is not positive gives no rectangles. -/
def Rect.outline (r : Rect) (w : Rat) (pl : OutlinePlacement) : List Rect :=
  if w ≤ 0 then [] else
  let g := pl.reach w
  let ox0 := min r.x0 r.x1 - g
  let oy0 := min r.y0 r.y1 - g
  let ox1 := max r.x0 r.x1 + g
  let oy1 := max r.y0 r.y1 + g
  let ix0 := ox0 + w
  let iy0 := oy0 + w
  let ix1 := ox1 - w
  let iy1 := oy1 - w
  if ix0 < ix1 ∧ iy0 < iy1 then
    [⟨ox0, oy0, ox1, iy0⟩, ⟨ox0, iy1, ox1, oy1⟩, ⟨ox0, iy0, ix0, iy1⟩, ⟨ix1, iy0, ox1, iy1⟩]
  else [⟨ox0, oy0, ox1, oy1⟩]

/-- The rectangle's border drawn in one colour or shading on one layer. -/
def DisplayList.outline (r : Rect) (w : Rat) (pl : OutlinePlacement) (color : Shading)
    (layer : Nat) : DisplayList :=
  (r.outline w pl).toArray.map fun b => ⟨layer, color, .rect b⟩

/-- Each border rectangle is one command with the given layer and shading. -/
theorem DisplayList.outline_eq (r : Rect) (w : Rat) (pl : OutlinePlacement) (color : Shading)
    (layer : Nat) : DisplayList.outline r w pl color layer =
      ((r.outline w pl).map fun b => (⟨layer, color, .rect b⟩ : Command)).toArray := by
  simp [DisplayList.outline, List.map_toArray]

/-- A point is in the border exactly when it is in the outer rectangle and not strictly inside the
hole; a border too wide to leave a hole is the whole outer rectangle. -/
theorem Rect.outline_holds (r : Rect) (w : Rat) (pl : OutlinePlacement) (hw : 0 < w) (p : Pt) :
    (∃ b ∈ r.outline w pl, b.Holds p) ↔
      (min r.x0 r.x1 - pl.reach w ≤ p.x ∧ p.x ≤ max r.x0 r.x1 + pl.reach w ∧
        min r.y0 r.y1 - pl.reach w ≤ p.y ∧ p.y ≤ max r.y0 r.y1 + pl.reach w) ∧
      ¬ (let g := pl.reach w
         (min r.x0 r.x1 - g + w < p.x ∧ p.x < max r.x0 r.x1 + g - w ∧
          min r.y0 r.y1 - g + w < p.y ∧ p.y < max r.y0 r.y1 + g - w)) := by
  have hg : 0 ≤ pl.reach w := by cases pl <;> simp [OutlinePlacement.reach] <;> grind
  unfold Rect.outline
  have hn : ¬ w ≤ 0 := by grind
  simp only [hn, ite_false]
  generalize pl.reach w = g at *
  obtain ⟨a, b, c, d⟩ := r
  simp only [Rect.Holds, Region.box, between_iff]
  split
  · simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left]
    grind
  · simp only [List.mem_singleton, exists_eq_left]
    grind

end Inkproof.Scene
