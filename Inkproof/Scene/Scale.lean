/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Scale.Linear
import Inkproof.Scene.Coverage

namespace Inkproof.Scene

def Pt.scale (k : Rat) (p : Pt) : Pt := ⟨k * p.x, k * p.y⟩

def Rect.scale (k : Rat) (b : Rect) : Rect := ⟨k * b.x0, k * b.y0, k * b.x1, k * b.y1⟩

def Column.scale (k : Rat) (c : Column) : Column := ⟨k * c.x, k * c.lo, k * c.hi⟩

def Stop.scale (k : Rat) (s : Stop) : Stop := ⟨k * s.pos, s.color⟩

/-- Gradient stop positions scale; colours do not. -/
def Shading.scale (k : Rat) : Shading → Shading
  | .flat c => .flat c
  | .gradient a s rest => .gradient a (s.scale k) (rest.map (Stop.scale k))
  | .steps a s rest => .steps a (s.scale k) (rest.map (Stop.scale k))

def Item.map {α β : Type} (f : α → β) : Item α → Item β
  | .val a => .val (f a)
  | .gap => .gap

/-- Every coordinate, half width, radius and box scaled by `k`. -/
def Shape.scale (k : Rat) : Shape → Shape
  | .strip hw items => .strip (k * hw) (items.map (Item.map (Pt.scale k)))
  | .envelope items => .envelope (items.map (Item.map (Column.scale k)))
  | .area y0 items => .area (k * y0) (items.map (Item.map (Pt.scale k)))
  | .rect b => .rect (b.scale k)
  | .marker m c r => .marker m (c.scale k) (k * r)
  | .text b s => .text (b.scale k) s
  | .clipped b s => .clipped (b.scale k) (s.scale k)

def Command.scale (k : Rat) (c : Command) : Command :=
  ⟨c.layer, c.color.scale k, c.shape.scale k⟩

/-- The display list scaled by `k`, as when drawing at a device pixel ratio. -/
def DisplayList.scale (k : Rat) (dl : DisplayList) : DisplayList := dl.map (Command.scale k)

theorem Pt.scale_x (k : Rat) (p : Pt) : (p.scale k).x = k * p.x := rfl

theorem Pt.scale_y (k : Rat) (p : Pt) : (p.scale k).y = k * p.y := rfl

theorem Rect.scale_eq (k : Rat) (b : Rect) :
    b.scale k = ⟨k * b.x0, k * b.y0, k * b.x1, k * b.y1⟩ := rfl

theorem Column.scale_eq (k : Rat) (c : Column) : c.scale k = ⟨k * c.x, k * c.lo, k * c.hi⟩ := rfl

theorem Stop.scale_pos (k : Rat) (s : Stop) : (s.scale k).pos = k * s.pos := rfl

theorem Stop.scale_color (k : Rat) (s : Stop) : (s.scale k).color = s.color := rfl

theorem Shading.scale_flat (k : Rat) (c : Color) : (Shading.flat c).scale k = .flat c := rfl

theorem Shading.scale_gradient (k : Rat) (a s rest) :
    (Shading.gradient a s rest).scale k = .gradient a (s.scale k) (rest.map (Stop.scale k)) := rfl

theorem Shading.scale_steps (k : Rat) (a s rest) :
    (Shading.steps a s rest).scale k = .steps a (s.scale k) (rest.map (Stop.scale k)) := rfl

theorem Item.map_val {α β : Type} (f : α → β) (a : α) : (Item.val a).map f = .val (f a) := rfl

theorem Item.map_gap {α β : Type} (f : α → β) : (Item.gap : Item α).map f = .gap := rfl

theorem Command.scale_eq (k : Rat) (c : Command) :
    c.scale k = ⟨c.layer, c.color.scale k, c.shape.scale k⟩ := rfl

theorem Shape.scale_strip (k hw : Rat) (items : List (Item Pt)) :
    (Shape.strip hw items).scale k = .strip (k * hw) (items.map (Item.map (Pt.scale k))) := rfl

theorem Shape.scale_envelope (k : Rat) (items : List (Item Column)) :
    (Shape.envelope items).scale k = .envelope (items.map (Item.map (Column.scale k))) := rfl

theorem Shape.scale_area (k y0 : Rat) (items : List (Item Pt)) :
    (Shape.area y0 items).scale k = .area (k * y0) (items.map (Item.map (Pt.scale k))) := rfl

theorem Shape.scale_rect (k : Rat) (b : Rect) : (Shape.rect b).scale k = .rect (b.scale k) := rfl

theorem Shape.scale_marker (k : Rat) (m : MarkerShape) (c : Pt) (r : Rat) :
    (Shape.marker m c r).scale k = .marker m (c.scale k) (k * r) := rfl

theorem Shape.scale_text (k : Rat) (b : Rect) (s : String) :
    (Shape.text b s).scale k = .text (b.scale k) s := rfl

theorem Shape.scale_clipped (k : Rat) (b : Rect) (s : Shape) :
    (Shape.clipped b s).scale k = .clipped (b.scale k) (s.scale k) := rfl

theorem DisplayList.scale_toList (k : Rat) (dl : DisplayList) :
    (dl.scale k).toList = dl.toList.map (Command.scale k) := by
  simp [DisplayList.scale]

/-- Only the sizes in pixels scaled by `k`: strip half widths and marker radii. Coordinates, baselines,
boxes and gradient stops are in whatever units the list is in, so they stay. -/
def Shape.scaleSizes (k : Rat) : Shape → Shape
  | .strip hw items => .strip (k * hw) items
  | .marker m c r => .marker m c (k * r)
  | .clipped b s => .clipped b (s.scaleSizes k)
  | s => s

def Command.scaleSizes (k : Rat) (c : Command) : Command := ⟨c.layer, c.color, c.shape.scaleSizes k⟩

/-- The display list with its half widths and radii multiplied by `k`, as when a list in data
coordinates is drawn at a device pixel ratio. -/
def DisplayList.scaleSizes (k : Rat) (dl : DisplayList) : DisplayList :=
  dl.map (Command.scaleSizes k)

theorem Shape.scaleSizes_strip (k hw : Rat) (items : List (Item Pt)) :
    (Shape.strip hw items).scaleSizes k = .strip (k * hw) items := rfl

theorem Shape.scaleSizes_marker (k : Rat) (m : MarkerShape) (c : Pt) (r : Rat) :
    (Shape.marker m c r).scaleSizes k = .marker m c (k * r) := rfl

theorem Shape.scaleSizes_clipped (k : Rat) (b : Rect) (s : Shape) :
    (Shape.clipped b s).scaleSizes k = .clipped b (s.scaleSizes k) := rfl

theorem Shape.scaleSizes_envelope (k : Rat) (items : List (Item Column)) :
    (Shape.envelope items).scaleSizes k = .envelope items := rfl

theorem Shape.scaleSizes_area (k y0 : Rat) (items : List (Item Pt)) :
    (Shape.area y0 items).scaleSizes k = .area y0 items := rfl

theorem Shape.scaleSizes_rect (k : Rat) (b : Rect) : (Shape.rect b).scaleSizes k = .rect b := rfl

theorem Shape.scaleSizes_text (k : Rat) (b : Rect) (s : String) :
    (Shape.text b s).scaleSizes k = .text b s := rfl

theorem Command.scaleSizes_eq (k : Rat) (c : Command) :
    c.scaleSizes k = ⟨c.layer, c.color, c.shape.scaleSizes k⟩ := rfl

theorem DisplayList.scaleSizes_toList (k : Rat) (dl : DisplayList) :
    (dl.scaleSizes k).toList = dl.toList.map (Command.scaleSizes k) := by
  simp [DisplayList.scaleSizes]

theorem DisplayList.scaleSizes_size (k : Rat) (dl : DisplayList) :
    (dl.scaleSizes k).size = dl.size := by
  simp [DisplayList.scaleSizes]

/-- The pixel a view of two linear scales puts a data point at. -/
def Pt.view (sx sy : Inkproof.Scale.Linear Rat) (p : Pt) : Pt := ⟨sx.map p.x, sy.map p.y⟩

/-- A shape in data coordinates drawn under the view of `sx` and `sy`: coordinates go through the
scales and sizes, already in pixels, stay. -/
def Shape.view (sx sy : Inkproof.Scale.Linear Rat) : Shape → Shape
  | .strip hw items => .strip hw (items.map (Item.map (Pt.view sx sy)))
  | .envelope items =>
    .envelope (items.map (Item.map fun c => ⟨sx.map c.x, sy.map c.lo, sy.map c.hi⟩))
  | .area y0 items => .area (sy.map y0) (items.map (Item.map (Pt.view sx sy)))
  | .rect b => .rect ⟨sx.map b.x0, sy.map b.y0, sx.map b.x1, sy.map b.y1⟩
  | .marker m c r => .marker m (c.view sx sy) r
  | .text b s => .text ⟨sx.map b.x0, sy.map b.y0, sx.map b.x1, sy.map b.y1⟩ s
  | .clipped b s =>
    .clipped ⟨sx.map b.x0, sy.map b.y0, sx.map b.x1, sy.map b.y1⟩ (s.view sx sy)

theorem Pt.view_eq (sx sy : Inkproof.Scale.Linear Rat) (p : Pt) : p.view sx sy = ⟨sx.map p.x, sy.map p.y⟩ := rfl

theorem Shape.view_strip (sx sy : Inkproof.Scale.Linear Rat) (hw : Rat) (items : List (Item Pt)) :
    (Shape.strip hw items).view sx sy = .strip hw (items.map (Item.map (Pt.view sx sy))) := rfl

theorem Shape.view_marker (sx sy : Inkproof.Scale.Linear Rat) (m : MarkerShape) (c : Pt) (r : Rat) :
    (Shape.marker m c r).view sx sy = .marker m (c.view sx sy) r := rfl

theorem Shape.view_envelope (sx sy : Inkproof.Scale.Linear Rat) (items : List (Item Column)) :
    (Shape.envelope items).view sx sy =
      .envelope (items.map (Item.map fun c => ⟨sx.map c.x, sy.map c.lo, sy.map c.hi⟩)) := rfl

theorem Shape.view_area (sx sy : Inkproof.Scale.Linear Rat) (y0 : Rat) (items : List (Item Pt)) :
    (Shape.area y0 items).view sx sy = .area (sy.map y0) (items.map (Item.map (Pt.view sx sy))) := rfl

theorem Shape.view_rect (sx sy : Inkproof.Scale.Linear Rat) (b : Rect) :
    (Shape.rect b).view sx sy = .rect ⟨sx.map b.x0, sy.map b.y0, sx.map b.x1, sy.map b.y1⟩ := rfl

theorem Shape.view_text (sx sy : Inkproof.Scale.Linear Rat) (b : Rect) (s : String) :
    (Shape.text b s).view sx sy = .text ⟨sx.map b.x0, sy.map b.y0, sx.map b.x1, sy.map b.y1⟩ s := rfl

theorem Shape.view_clipped (sx sy : Inkproof.Scale.Linear Rat) (b : Rect) (s : Shape) :
    (Shape.clipped b s).view sx sy =
      .clipped ⟨sx.map b.x0, sy.map b.y0, sx.map b.x1, sy.map b.y1⟩ (s.view sx sy) := rfl

/-- Scaling the sizes of a list in data coordinates, then viewing it, is viewing it and then drawing
it at `k` times the pixel size: a strip's half width and a marker's radius become `k` times theirs
while the positions are the original's under the view. -/
theorem Shape.view_scaleSizes (sx sy : Inkproof.Scale.Linear Rat) (k : Rat) (s : Shape) :
    (s.scaleSizes k).view sx sy = (s.view sx sy).scaleSizes k := by
  induction s with
  | clipped b s ih => simp only [Shape.scaleSizes, Shape.view, ih]
  | _ => rfl

theorem Shape.view_scaleSizes_strip (sx sy : Inkproof.Scale.Linear Rat) (k hw : Rat) (items : List (Item Pt)) :
    ((Shape.strip hw items).scaleSizes k).view sx sy =
      .strip (k * hw) (items.map (Item.map (Pt.view sx sy))) := rfl

theorem Shape.view_scaleSizes_marker (sx sy : Inkproof.Scale.Linear Rat) (k : Rat) (m : MarkerShape) (c : Pt)
    (r : Rat) :
    ((Shape.marker m c r).scaleSizes k).view sx sy = .marker m (c.view sx sy) (k * r) := rfl

/-- The point of the original that `p` is the image of. -/
def Pt.unscale (k : Rat) (p : Pt) : Pt := ⟨p.x / k, p.y / k⟩

theorem Pt.unscale_eq (k : Rat) (p : Pt) : p.unscale k = ⟨p.x / k, p.y / k⟩ := rfl

private theorem eq_mul_iff {k x y : Rat} (hk : k ≠ 0) : x = k * y ↔ x / k = y := by
  constructor
  · rintro rfl; grind
  · rintro rfl; grind

private theorem mul_le_mul_iff {k a b : Rat} (hk : 0 < k) : k * a ≤ k * b ↔ a ≤ b := by
  constructor
  · intro h; exact Rat.le_of_mul_le_mul_left h hk
  · intro h; exact Rat.mul_le_mul_of_nonneg_left h (Rat.le_of_lt hk)

private theorem between_scale {k a b y : Rat} (hk : 0 < k) :
    Between (k * a) (k * b) y ↔ Between a b (y / k) := by
  have hy : y = k * (y / k) := by grind
  generalize y / k = v at hy ⊢
  subst hy
  unfold Between
  rw [mul_le_mul_iff hk, mul_le_mul_iff hk, mul_le_mul_iff hk, mul_le_mul_iff hk]

private theorem scale_eq {k a b t : Rat} : k * a + t * (k * b - k * a) = k * (a + t * (b - a)) := by
  grind

private theorem scale_coord {k : Rat} (hk : k ≠ 0) {x a b t : Rat} :
    x = k * a + t * (k * b - k * a) ↔ x / k = a + t * (b - a) := by
  rw [scale_eq]; exact eq_mul_iff hk

theorem Region.seg_scale {k : Rat} (hk : 0 < k) (a b p : Pt) :
    Region.seg (a.scale k) (b.scale k) p ↔ Region.seg a b (p.unscale k) := by
  have hk' : k ≠ 0 := by grind
  unfold Region.seg Pt.scale Pt.unscale
  simp only [scale_coord hk']

theorem Region.span_scale {k : Rat} (hk : 0 < k) (x0 x1 l0 l1 h0 h1 : Rat) (p : Pt) :
    Region.span (k * x0) (k * x1) (k * l0) (k * l1) (k * h0) (k * h1) p ↔
      Region.span x0 x1 l0 l1 h0 h1 (p.unscale k) := by
  have hk' : k ≠ 0 := by grind
  unfold Region.span Pt.unscale
  simp only [scale_eq, eq_mul_iff hk', between_scale hk]

theorem Region.box_scale {k : Rat} (hk : 0 < k) (x0 y0 x1 y1 : Rat) (p : Pt) :
    Region.box (k * x0) (k * y0) (k * x1) (k * y1) p ↔ Region.box x0 y0 x1 y1 (p.unscale k) := by
  unfold Region.box Pt.unscale
  rw [between_scale hk, between_scale hk]

theorem Region.disc_scale {k : Rat} (hk : 0 < k) (c : Pt) (r : Rat) (p : Pt) :
    Region.disc (c.scale k) (k * r) p ↔ Region.disc c r (p.unscale k) := by
  have hk' : k ≠ 0 := by grind
  unfold Region.disc Pt.scale Pt.unscale
  have h : ∀ u v : Rat, (u - k * v) * (u - k * v) = k * k * ((u / k - v) * (u / k - v)) := by
    intro u v
    have hu : u = k * (u / k) := by grind
    generalize u / k = w at hu ⊢
    subst hu
    grind
  simp only [h]
  rw [show k * r * (k * r) = k * k * (r * r) by grind, ← Rat.mul_add, mul_le_mul_iff (Rat.mul_pos hk hk)]

theorem unscale_scale {k : Rat} (hk : 0 < k) (p : Pt) : (p.scale k).unscale k = p := by
  have hk' : k ≠ 0 := by grind
  simp only [Pt.scale, Pt.unscale]
  have : ∀ v : Rat, k * v / k = v := by intro v; grind
  simp [this]

theorem scale_unscale {k : Rat} (hk : 0 < k) (p : Pt) : (p.unscale k).scale k = p := by
  have hk' : k ≠ 0 := by grind
  simp only [Pt.scale, Pt.unscale]
  have : ∀ v : Rat, k * (v / k) = v := by intro v; grind
  simp [this]

private theorem point_scale {k : Rat} (hk : 0 < k) (a p : Pt) :
    Region.point (a.scale k) p ↔ Region.point a (p.unscale k) := by
  unfold Region.point
  constructor
  · rintro rfl; rw [unscale_scale hk]
  · intro h; rw [← scale_unscale hk p, h]

private theorem chain_map {α β : Type} {single' : β → Region} {join' : β → β → Region}
    {single : α → Region} {join : α → α → Region} (f : α → β) (u : Pt → Pt)
    (hs : ∀ a p, single' (f a) p ↔ single a (u p))
    (hj : ∀ a b p, join' (f a) (f b) p ↔ join a b (u p)) (items : List (Item α)) (p : Pt) :
    Item.chain single' join' (items.map (Item.map f)) p ↔ Item.chain single join items (u p) := by
  induction items with
  | nil => simp [Item.chain]
  | cons i rest ih =>
    cases i with
    | gap => simpa [Item.chain, Item.map] using ih
    | val a =>
      cases rest with
      | nil => simp [Item.chain, Item.map, hs]
      | cons j rest' =>
        cases j with
        | gap => simp_all [Item.chain, Item.map]
        | val b => simp_all [Item.chain, Item.map]

theorem Shape.scale_region {k : Rat} (hk : 0 < k) (s : Shape) (p : Pt) :
    (s.scale k).region p ↔ s.region (p.unscale k) := by
  induction s generalizing p with
  | strip hw items =>
    simp only [Shape.scale, Shape.region, Region.thicken]
    have hc : ∀ q, Item.chain Region.point Region.seg (items.map (Item.map (Pt.scale k))) q ↔
        Item.chain Region.point Region.seg items (q.unscale k) :=
      chain_map (Pt.scale k) (Pt.unscale k) (point_scale hk) (Region.seg_scale hk) items
    constructor
    · rintro ⟨q, hq, hd⟩
      refine ⟨q.unscale k, (hc q).1 hq, ?_⟩
      rw [← Region.disc_scale hk, scale_unscale hk]
      exact hd
    · rintro ⟨q, hq, hd⟩
      refine ⟨q.scale k, (hc _).2 (by rw [unscale_scale hk]; exact hq), ?_⟩
      rw [Region.disc_scale hk]
      exact hd
  | envelope items =>
    simp only [Shape.scale, Shape.region]
    exact chain_map (Column.scale k) (Pt.unscale k)
      (fun a p => Region.span_scale hk a.x a.x a.lo a.lo a.hi a.hi p)
      (fun a b p => Region.span_scale hk a.x b.x a.lo b.lo a.hi b.hi p) items p
  | area y0 items =>
    simp only [Shape.scale, Shape.region]
    exact chain_map (Pt.scale k) (Pt.unscale k)
      (fun a p => Region.span_scale hk a.x a.x y0 y0 a.y a.y p)
      (fun a b p => Region.span_scale hk a.x b.x y0 y0 a.y b.y p) items p
  | rect b => exact Region.box_scale hk _ _ _ _ p
  | marker m c r =>
    cases m
    · simp only [Shape.scale, Shape.region, Pt.scale, Pt.unscale]
      have e : ∀ a : Rat, k * a - k * r = k * (a - r) := by intro a; grind
      have f : ∀ a : Rat, k * a + k * r = k * (a + r) := by intro a; grind
      rw [e, e, f, f]
      exact Region.box_scale hk ..
    · exact Region.disc_scale hk _ _ p
  | text b _ => exact Region.box_scale hk _ _ _ _ p
  | clipped b s ih => simp only [Shape.scale, Shape.region, Rect.scale, Region.box_scale hk, ih]

theorem Shape.scale_covers {k : Rat} (hk : 0 < k) (s : Shape) (px : Pixel) :
    (s.scale k).region.Covers px ↔ ∃ q, s.region q ∧ px.Contains (q.scale k) := by
  constructor
  · rintro ⟨p, hp, hc⟩
    refine ⟨p.unscale k, (Shape.scale_region hk s p).1 hp, ?_⟩
    rw [scale_unscale hk]; exact hc
  · rintro ⟨q, hq, hc⟩
    refine ⟨q.scale k, (Shape.scale_region hk s _).2 ?_, hc⟩
    rw [unscale_scale hk]; exact hq

theorem Command.scale_covers {k : Rat} (hk : 0 < k) (c : Command) (px : Pixel) :
    (c.scale k).Covers px ↔ ∃ q, c.shape.region q ∧ px.Contains (q.scale k) :=
  Shape.scale_covers hk c.shape px

/-- A pixel is covered by the scaled list exactly when some point of the original, scaled, lies in
it: the raster of the scaled list is the original's drawn at `k` times the resolution. -/
theorem DisplayList.scale_covers {k : Rat} (hk : 0 < k) (dl : DisplayList) (px : Pixel) :
    (dl.scale k).Covers px ↔ ∃ c ∈ dl, ∃ q, c.shape.region q ∧ px.Contains (q.scale k) := by
  unfold DisplayList.Covers
  simp only [DisplayList.scale, Array.mem_map]
  constructor
  · rintro ⟨_, ⟨c, hc, rfl⟩, h⟩
    exact ⟨c, hc, (Command.scale_covers hk c px).1 h⟩
  · rintro ⟨c, hc, h⟩
    exact ⟨_, ⟨c, hc, rfl⟩, (Command.scale_covers hk c px).2 h⟩

theorem DisplayList.scale_size (k : Rat) (dl : DisplayList) : (dl.scale k).size = dl.size := by
  simp [DisplayList.scale]

private theorem ratio_scale {k : Rat} (hk : 0 < k) (a b c d : Rat) :
    (k * a - k * b) / (k * c - k * d) = (a - b) / (c - d) := by
  rw [show k * a - k * b = k * (a - b) by grind, show k * c - k * d = k * (c - d) by grind]
  have hk' : k ≠ 0 := by grind
  generalize a - b = x
  generalize c - d = y
  by_cases hy : y = 0
  · subst hy; grind
  · grind

/-- The colour of the scaled stops at `k * t` is the original's at `t`. -/
theorem evalStops_scale {k : Rat} (hk : 0 < k) (rest : List Stop) (s : Stop) (t : Rat) :
    evalStops (s.scale k) (rest.map (Stop.scale k)) (k * t) = evalStops s rest t := by
  induction rest generalizing s with
  | nil => rfl
  | cons n rest ih =>
    simp only [List.map_cons, evalStops, Stop.scale, mul_le_mul_iff hk, ratio_scale hk]
    split <;> try rfl
    split <;> try rfl
    exact ih n

theorem evalSteps_scale {k : Rat} (hk : 0 < k) (rest : List Stop) (s : Stop) (t : Rat) :
    evalSteps (s.scale k) (rest.map (Stop.scale k)) (k * t) = evalSteps s rest t := by
  induction rest generalizing s with
  | nil => rfl
  | cons n rest ih =>
    simp only [List.map_cons, evalSteps, Stop.scale, mul_le_mul_iff hk]
    split <;> try rfl
    exact ih n

end Inkproof.Scene
