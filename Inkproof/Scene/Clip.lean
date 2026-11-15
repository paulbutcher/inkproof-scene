/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Scene.Coverage

namespace Inkproof.Scene

/-- The point lies in the rectangle, boundary included. -/
def Rect.Holds (r : Rect) (p : Pt) : Prop := Region.box r.x0 r.y0 r.x1 r.y1 p

theorem between_iff {a b v : Rat} : Between a b v ↔ min a b ≤ v ∧ v ≤ max a b := by
  unfold Between
  grind

/-- The overlap of two rectangles, or `none` when they are disjoint. The result's corners are in
ascending order. -/
def Rect.meet (a b : Rect) : Option Rect :=
  let x0 := max (min a.x0 a.x1) (min b.x0 b.x1)
  let x1 := min (max a.x0 a.x1) (max b.x0 b.x1)
  let y0 := max (min a.y0 a.y1) (min b.y0 b.y1)
  let y1 := min (max a.y0 a.y1) (max b.y0 b.y1)
  if x0 ≤ x1 ∧ y0 ≤ y1 then some ⟨x0, y0, x1, y1⟩ else none

/-- The overlap of two rectangles is the rectangle's points that lie in both, and is `none` exactly
when there are none. -/
theorem Rect.meet_holds (a b : Rect) (p : Pt) :
    (∃ r, a.meet b = some r ∧ r.Holds p) ↔ a.Holds p ∧ b.Holds p := by
  unfold Rect.meet Rect.Holds Region.box
  simp only [between_iff]
  constructor
  · rintro ⟨r, hr, h⟩
    split at hr
    · cases hr
      simp only at h
      grind
    · simp at hr
  · intro h
    have hc : max (min a.x0 a.x1) (min b.x0 b.x1) ≤ min (max a.x0 a.x1) (max b.x0 b.x1) ∧
        max (min a.y0 a.y1) (min b.y0 b.y1) ≤ min (max a.y0 a.y1) (max b.y0 b.y1) := by grind
    simp only [hc, and_self, ite_true]
    refine ⟨_, rfl, ?_⟩
    simp only [Rat.min_def, Rat.max_def] at hc ⊢
    grind

/-- A shape restricted to the rectangle `r`, or `none` when nothing of it can lie there. Rectangles
and square markers are cut exactly; every other shape is scissored, which leaves the renderer to
discard what falls outside `r`. -/
def Shape.clip (r : Rect) : Shape → Option Shape
  | .rect b => (b.meet r).map .rect
  | .marker .square c k =>
    (Rect.meet ⟨c.x - k, c.y - k, c.x + k, c.y + k⟩ r).map .rect
  | s => some (.clipped r s)

/-- Clipping keeps exactly the points of the shape that lie in the rectangle: what remains lies
inside it, and nothing inside it is lost. -/
theorem Shape.clip_region (r : Rect) (s : Shape) (p : Pt) :
    (∃ s', s.clip r = some s' ∧ s'.region p) ↔ s.region p ∧ r.Holds p := by
  cases s with
  | rect b =>
    simp only [Shape.clip, Option.map_eq_some_iff]
    constructor
    · rintro ⟨s', ⟨m, hm, rfl⟩, h⟩
      have := (Rect.meet_holds b r p).mp ⟨m, hm, h⟩
      exact this
    · intro h
      obtain ⟨m, hm, hh⟩ := (Rect.meet_holds b r p).mpr h
      exact ⟨_, ⟨m, hm, rfl⟩, hh⟩
  | marker sh c k =>
    cases sh with
    | square =>
      simp only [Shape.clip, Option.map_eq_some_iff]
      constructor
      · rintro ⟨s', ⟨m, hm, rfl⟩, h⟩
        exact (Rect.meet_holds _ r p).mp ⟨m, hm, h⟩
      · intro h
        obtain ⟨m, hm, hh⟩ := (Rect.meet_holds ⟨c.x - k, c.y - k, c.x + k, c.y + k⟩ r p).mpr h
        exact ⟨_, ⟨m, hm, rfl⟩, hh⟩
    | circle =>
      simp only [Shape.clip, Option.some.injEq, exists_eq_left', Shape.region]
      exact and_comm
  | _ =>
    simp only [Shape.clip, Option.some.injEq, exists_eq_left', Shape.region]
    exact and_comm

/-- A command restricted to the rectangle `r`, with the same layer and colour. -/
def Command.clip (r : Rect) (c : Command) : Option Command :=
  (c.shape.clip r).map fun s => { c with shape := s }

/-- The commands of a display list restricted to the rectangle `r`, in the same order. -/
def DisplayList.clip (r : Rect) (dl : DisplayList) : DisplayList :=
  dl.filterMap (Command.clip r)

/-- A pixel is covered by the clipped list exactly when some command has a point in the rectangle
and in the pixel. -/
theorem DisplayList.clip_covers (r : Rect) (dl : DisplayList) (px : Pixel) :
    (dl.clip r).Covers px ↔ ∃ c ∈ dl, ∃ p, c.shape.region p ∧ r.Holds p ∧ px.Contains p := by
  unfold DisplayList.clip DisplayList.Covers Command.Covers Region.Covers
  simp only [Array.mem_filterMap, Command.clip, Option.map_eq_some_iff]
  constructor
  · rintro ⟨_, ⟨c, hc, s, hs, rfl⟩, p, hp, hx⟩
    obtain ⟨h1, h2⟩ := (Shape.clip_region r c.shape p).mp ⟨s, hs, hp⟩
    exact ⟨c, hc, p, h1, h2, hx⟩
  · rintro ⟨c, hc, p, h1, h2, hx⟩
    obtain ⟨s, hs, hp⟩ := (Shape.clip_region r c.shape p).mpr ⟨h1, h2⟩
    exact ⟨_, ⟨c, hc, s, hs, rfl⟩, p, hp, hx⟩

/-- Everything the clipped list covers is covered by the original. -/
theorem DisplayList.Covers.of_clip {r : Rect} {dl : DisplayList} {px : Pixel}
    (h : (dl.clip r).Covers px) : dl.Covers px :=
  match (DisplayList.clip_covers r dl px).mp h with
  | ⟨c, hc, p, h1, _, hx⟩ => ⟨c, hc, p, h1, hx⟩

/-- A pixel whose square lies in the rectangle is covered by the clipped list exactly when it is
covered by the original: nothing inside the plot area is lost. -/
theorem DisplayList.clip_covers_of_inside {r : Rect} {px : Pixel} (dl : DisplayList)
    (hin : ∀ p, px.Contains p → r.Holds p) : (dl.clip r).Covers px ↔ dl.Covers px := by
  rw [DisplayList.clip_covers]
  constructor
  · exact DisplayList.Covers.of_clip ∘ (DisplayList.clip_covers r dl px).mpr
  · rintro ⟨c, hc, p, h1, hx⟩
    exact ⟨c, hc, p, h1, hin p hx, hx⟩

/-- Every point of a clipped list lies in the rectangle, so every pixel it covers meets it. -/
theorem DisplayList.clip_inside {r : Rect} {dl : DisplayList} {px : Pixel}
    (h : (dl.clip r).Covers px) : ∃ p, r.Holds p ∧ px.Contains p :=
  match (DisplayList.clip_covers r dl px).mp h with
  | ⟨_, _, p, _, h2, hx⟩ => ⟨p, h2, hx⟩

end Inkproof.Scene
