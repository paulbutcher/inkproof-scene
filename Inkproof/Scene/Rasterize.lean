/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Scene.Meet

namespace Inkproof.Scene

theorem between_iff (a b v : Rat) : Between a b v ↔ min a b ≤ v ∧ v ≤ max a b := by
  unfold Between; grind

/-- The rectangle `Region.box` meets the window. -/
def boxMeetsB (x0 y0 x1 y1 : Rat) (w : Window) : Bool :=
  decide (w.x0 ≤ w.x1 ∧ w.y0 ≤ w.y1 ∧ min x0 x1 ≤ w.x1 ∧ w.x0 ≤ max x0 x1 ∧
    min y0 y1 ≤ w.y1 ∧ w.y0 ≤ max y0 y1)

theorem boxMeetsB_iff (x0 y0 x1 y1 : Rat) (w : Window) :
    boxMeetsB x0 y0 x1 y1 w = true ↔ (Region.box x0 y0 x1 y1).Meets w := by
  unfold boxMeetsB Region.Meets Region.box
  simp only [decide_eq_true_eq, between_iff]
  constructor
  · rintro ⟨a, b, c, d, e, f⟩
    exact ⟨⟨max w.x0 (min x0 x1), max w.y0 (min y0 y1)⟩, by simp only []; grind,
      by simp only [Window.Has]; grind⟩
  · rintro ⟨p, ⟨⟨a, b⟩, c, d⟩, e, f, g, h⟩
    grind

/-- The window of a rectangle whose corners are in either order. -/
def Rect.window (b : Rect) : Window := ⟨min b.x0 b.x1, min b.y0 b.y1, max b.x0 b.x1, max b.y0 b.y1⟩

theorem Rect.has_window (b : Rect) (p : Pt) :
    b.window.Has p ↔ Region.box b.x0 b.y0 b.x1 b.y1 p := by
  simp only [Rect.window, Window.Has, Region.box, between_iff]; grind

/-- Whether the shape has a point in the window. -/
def Shape.meetsB : Shape → Window → Bool
  | .strip hw items, w =>
    Item.anyB (fun a => discMeetsB a hw w) (fun a b => segNearB a b hw w) items
  | .envelope items, w =>
    Item.anyB (fun c => spanMeetsB c.x c.x c.lo c.lo c.hi c.hi w)
      (fun a b => spanMeetsB a.x b.x a.lo b.lo a.hi b.hi w) items
  | .area y0 items, w =>
    Item.anyB (fun a => spanMeetsB a.x a.x y0 y0 a.y a.y w)
      (fun a b => spanMeetsB a.x b.x y0 y0 a.y b.y w) items
  | .rect b, w => boxMeetsB b.x0 b.y0 b.x1 b.y1 w
  | .marker .square c r, w => boxMeetsB (c.x - r) (c.y - r) (c.x + r) (c.y + r) w
  | .marker .circle c r, w => discMeetsB c r w
  | .text b _, w => boxMeetsB b.x0 b.y0 b.x1 b.y1 w
  | .clipped b s, w => s.meetsB (w.inter b.window)

theorem Shape.meetsB_iff (s : Shape) (w : Window) :
    s.meetsB w = true ↔ s.region.Meets w := by
  induction s generalizing w with
  | strip hw items =>
    unfold meetsB region
    rw [Item.anyB_iff (M := w.Near hw) (single := Region.point) (join := Region.seg)]
    · constructor
      · rintro ⟨q, h, p, hp, hd⟩; exact ⟨p, ⟨q, h, hd⟩, hp⟩
      · rintro ⟨p, ⟨q, h, hd⟩, hp⟩; exact ⟨q, h, p, hp, hd⟩
    · intro a
      rw [discMeetsB_near_iff]
      exact ⟨fun h => ⟨a, rfl, h⟩, fun ⟨q, hq, h⟩ => by subst hq; exact h⟩
    · intro a b; exact segNearB_iff a b hw w
  | envelope items =>
    unfold meetsB region
    exact Item.anyB_iff (M := w.Has) (fun c => spanMeetsB_iff ..) (fun a b => spanMeetsB_iff ..) items
  | area y0 items =>
    unfold meetsB region
    exact Item.anyB_iff (M := w.Has) (fun c => spanMeetsB_iff ..) (fun a b => spanMeetsB_iff ..) items
  | rect b => exact boxMeetsB_iff ..
  | marker shape c r =>
    cases shape
    · exact boxMeetsB_iff ..
    · exact discMeetsB_iff ..
  | text b _ => exact boxMeetsB_iff ..
  | clipped b s ih =>
    unfold meetsB region
    rw [ih]
    constructor
    · rintro ⟨p, hp, h⟩
      rw [Window.has_inter] at h
      exact ⟨p, ⟨(Rect.has_window b p).1 h.2, hp⟩, h.1⟩
    · rintro ⟨p, ⟨hb, hp⟩, h⟩
      exact ⟨p, hp, Window.has_inter.2 ⟨h, (Rect.has_window b p).2 hb⟩⟩

theorem Command.meetsB_iff (c : Command) (px : Pixel) :
    c.shape.meetsB px.window = true ↔ c.Covers px := Shape.meetsB_iff c.shape px.window

end Inkproof.Scene
