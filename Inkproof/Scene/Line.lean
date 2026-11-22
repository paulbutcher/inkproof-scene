/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Scene.Coverage

namespace Inkproof.Scene

/-- A triangle, boundary included. -/
structure Tri where
  a : Pt
  b : Pt
  c : Pt
  deriving DecidableEq, Repr

def Tri.region (t : Tri) : Region := fun p =>
  ∃ u v w : Rat, 0 ≤ u ∧ 0 ≤ v ∧ 0 ≤ w ∧ u + v + w = 1 ∧
    p.x = u * t.a.x + v * t.b.x + w * t.c.x ∧ p.y = u * t.a.y + v * t.b.y + w * t.c.y

/-- A parallelogram with corner `a` and edges `e` and `f` is the union of two triangles. -/
theorem parallelogram_sub_tris (a e f : Pt) (u v : Rat) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) :
    let p : Pt := ⟨a.x + u * e.x + v * f.x, a.y + u * e.y + v * f.y⟩
    (Tri.mk a ⟨a.x + e.x, a.y + e.y⟩ ⟨a.x + f.x, a.y + f.y⟩).region p ∨
    (Tri.mk ⟨a.x + e.x + f.x, a.y + e.y + f.y⟩ ⟨a.x + f.x, a.y + f.y⟩
      ⟨a.x + e.x, a.y + e.y⟩).region p := by
  intro p
  by_cases h : u + v ≤ 1
  · exact Or.inl ⟨1 - u - v, u, v, by grind, hu0, hv0, by grind, by grind, by grind⟩
  · exact Or.inr ⟨u + v - 1, 1 - u, 1 - v, by grind, by grind, by grind, by grind, by grind, by grind⟩

private theorem abs_bound {x D L h : Rat} (hx : x * x ≤ h * h * D) (hL : L * L ≤ D) (hh : 0 ≤ h)
    (hD : 0 ≤ D) : -(h * D) ≤ x * L ∧ x * L ≤ h * D := by
  have h1 : (x * L) * (x * L) ≤ (h * D) * (h * D) := by
    have h3 := Rat.mul_le_mul_of_nonneg_right hx (mul_self_nonneg' L)
    have h4 := Rat.mul_le_mul_of_nonneg_left hL (Rat.mul_nonneg (Rat.mul_nonneg hh hh) hD)
    grind
  have h2 : 0 ≤ h * D := Rat.mul_nonneg hh hD
  generalize x * L = z at h1 ⊢
  generalize h * D = c at h1 h2 ⊢
  constructor
  · by_cases hc : -c ≤ z
    · exact hc
    · have := Rat.mul_pos (a := -c - z) (b := c - z) (by grind) (by grind)
      grind
  · by_cases hc : z ≤ c
    · exact hc
    · have := Rat.mul_pos (a := z - c) (b := z + c) (by grind) (by grind)
      grind

private theorem cauchy (e1 e2 f1 f2 : Rat) :
    (e1 * f1 + e2 * f2) * (e1 * f1 + e2 * f2) ≤ (e1 * e1 + e2 * e2) * (f1 * f1 + f2 * f2) := by
  have := mul_self_nonneg' (e1 * f2 - e2 * f1)
  grind

private theorem lower_bound (x y : Rat) :
    let L := 7 / 10 * (max x (-x) + max y (-y))
    L * L ≤ x * x + y * y ∧ (0 < x * x + y * y → 0 < L) := by
  intro L
  have hx := mul_self_nonneg' x
  have hy := mul_self_nonneg' y
  have hax : 0 ≤ max x (-x) := by grind
  have hay : 0 ≤ max y (-y) := by grind
  have hsx : max x (-x) * max x (-x) = x * x := by grind
  have hsy : max y (-y) * max y (-y) = y * y := by grind
  constructor
  · have := mul_self_nonneg' (max x (-x) - max y (-y))
    grind
  · intro hD
    by_cases hp : 0 < L
    · exact hp
    · have e1 : max x (-x) = 0 := by grind
      have e2 : max y (-y) = 0 := by grind
      rw [e1] at hsx
      rw [e2] at hsy
      grind

/-- A lower bound on the length of `f`, within a factor of `√2`: the stated rectangle is a little
longer than the exact one because it uses this in place of the length. -/
def lengthBound (f : Pt) : Rat := 7 / 10 * (max f.x (-f.x) + max f.y (-f.y))

/-- The direction of a segment, or the horizontal when it has no length. -/
def Pt.dir (a b : Pt) : Pt := if a = b then ⟨1, 0⟩ else ⟨b.x - a.x, b.y - a.y⟩

theorem lengthBound_sq_le (f : Pt) : lengthBound f * lengthBound f ≤ f.x * f.x + f.y * f.y :=
  (lower_bound f.x f.y).1

theorem lengthBound_pos (f : Pt) (h : 0 < f.x * f.x + f.y * f.y) : 0 < lengthBound f :=
  (lower_bound f.x f.y).2 h

theorem Pt.dir_of_eq (a : Pt) : a.dir a = ⟨1, 0⟩ := by simp [Pt.dir]

theorem Pt.dir_of_ne (a b : Pt) (h : a ≠ b) : a.dir b = ⟨b.x - a.x, b.y - a.y⟩ := by
  simp [Pt.dir, h]

private theorem dir_sq_pos (a b : Pt) :
    0 < (a.dir b).x * (a.dir b).x + (a.dir b).y * (a.dir b).y := by
  unfold Pt.dir
  split
  · grind
  · rename_i h
    have hx := mul_self_nonneg' (b.x - a.x)
    have hy := mul_self_nonneg' (b.y - a.y)
    by_cases h0 : b.x - a.x = 0
    · by_cases h1 : b.y - a.y = 0
      · exact absurd (by cases a; cases b; simp_all; grind) h
      · simp only
        have := Rat.mul_pos (a := b.y - a.y) (b := b.y - a.y)
        by_cases hp : 0 < b.y - a.y
        · have := Rat.mul_pos hp hp; grind
        · have hn : 0 < -(b.y - a.y) := by grind
          have := Rat.mul_pos hn hn; grind
    · simp only
      by_cases hp : 0 < b.x - a.x
      · have := Rat.mul_pos hp hp; grind
      · have hn : 0 < -(b.x - a.x) := by grind
        have := Rat.mul_pos hn hn; grind

/-- The rectangle of half-width `h` about the segment from `a` along `f`, extended by the same
distance at each end and measured against `lengthBound f` rather than the exact length (which
would need a square root), as the corner `o` and the edges `e` and `g`. -/
def Pt.frame (a f : Pt) (h : Rat) : Pt × Pt × Pt :=
  let k := h / lengthBound f
  (⟨a.x - k * f.x + k * f.y, a.y - k * f.y - k * f.x⟩,
   ⟨(1 + 2 * k) * f.x, (1 + 2 * k) * f.y⟩,
   ⟨-(2 * k) * f.y, 2 * k * f.x⟩)

private theorem eq_of_mul_right {x y z : Rat} (hz : 0 < z) (h : x * z = y * z) : x = y := by
  have hz' : z ≠ 0 := by grind
  have := Rat.div_mul_cancel (a := x) hz'
  have := Rat.div_mul_cancel (a := y) hz'
  grind

/-- A disc about a point of the segment `a + t f` lies in the frame. -/
theorem frame_param (a f : Pt) (h t : Rat) (hh : 0 < h) (hD : 0 < f.x * f.x + f.y * f.y)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (p : Pt)
    (hp : Region.disc ⟨a.x + t * f.x, a.y + t * f.y⟩ h p) :
    ∃ u v : Rat, 0 ≤ u ∧ u ≤ 1 ∧ 0 ≤ v ∧ v ≤ 1 ∧
      p.x = (a.frame f h).1.x + u * (a.frame f h).2.1.x + v * (a.frame f h).2.2.x ∧
      p.y = (a.frame f h).1.y + u * (a.frame f h).2.1.y + v * (a.frame f h).2.2.y := by
  obtain ⟨hLL, hLpos⟩ := lower_bound f.x f.y
  have hL : 0 < lengthBound f := hLpos hD
  have hLL' : lengthBound f * lengthBound f ≤ f.x * f.x + f.y * f.y := hLL
  unfold Region.disc at hp
  simp only at hp
  unfold Pt.frame
  simp only
  have hk : h / lengthBound f * lengthBound f = h := Rat.div_mul_cancel (by grind)
  generalize h / lengthBound f = k at hk ⊢
  generalize lengthBound f = L at hL hLL' hk
  clear hLL hLpos
  subst hk
  have hkpos : 0 < k := by
    by_cases hc : 0 < k
    · exact hc
    · have := Rat.mul_nonneg (a := -k) (b := L) (by grind) (Rat.le_of_lt hL)
      grind
  generalize hDdef : f.x * f.x + f.y * f.y = D at hD hLL'
  have hdisc : (p.x - (a.x + t * f.x)) * (p.x - (a.x + t * f.x)) +
      (p.y - (a.y + t * f.y)) * (p.y - (a.y + t * f.y)) ≤ k * L * (k * L) := hp
  generalize hex : p.x - (a.x + t * f.x) = ex at hdisc
  generalize hey : p.y - (a.y + t * f.y) = ey at hdisc
  have hc1 : (ex * f.x + ey * f.y) * (ex * f.x + ey * f.y) ≤ k * L * (k * L) * D := by
    have h1 := cauchy ex ey f.x f.y
    rw [hDdef] at h1
    have h2 := Rat.mul_le_mul_of_nonneg_right hdisc (Rat.le_of_lt hD)
    grind
  have hc2 : (ey * f.x - ex * f.y) * (ey * f.x - ex * f.y) ≤ k * L * (k * L) * D := by
    have h1 := cauchy ex ey (-f.y) f.x
    have hD' : -f.y * -f.y + f.x * f.x = D := by grind
    rw [hD'] at h1
    have h2 := Rat.mul_le_mul_of_nonneg_right hdisc (Rat.le_of_lt hD)
    grind
  obtain ⟨b1l, b1u⟩ := abs_bound hc1 hLL' (Rat.le_of_lt hh) (Rat.le_of_lt hD)
  obtain ⟨b2l, b2u⟩ := abs_bound hc2 hLL' (Rat.le_of_lt hh) (Rat.le_of_lt hD)
  have hDL : 0 < D * L := Rat.mul_pos hD hL
  obtain ⟨A, hA⟩ : ∃ A, A * D = ex * f.x + ey * f.y := ⟨_, Rat.div_mul_cancel (by grind)⟩
  obtain ⟨B, hB⟩ : ∃ B, B * D = ey * f.x - ex * f.y := ⟨_, Rat.div_mul_cancel (by grind)⟩
  have eA : A * (D * L) = (ex * f.x + ey * f.y) * L := by rw [← hA]; grind
  have eB : B * (D * L) = (ey * f.x - ex * f.y) * L := by rw [← hB]; grind
  have hA1 : -k ≤ A := by
    refine Rat.le_of_mul_le_mul_right ?_ hDL
    rw [eA]; grind
  have hA2 : A ≤ k := by
    refine Rat.le_of_mul_le_mul_right ?_ hDL
    rw [eA]; grind
  have hB1 : -k ≤ B := by
    refine Rat.le_of_mul_le_mul_right ?_ hDL
    rw [eB]; grind
  have hB2 : B ≤ k := by
    refine Rat.le_of_mul_le_mul_right ?_ hDL
    rw [eB]; grind
  obtain ⟨u, hu⟩ : ∃ u, u * (1 + 2 * k) = t + A + k := ⟨_, Rat.div_mul_cancel (by grind)⟩
  obtain ⟨v, hv⟩ : ∃ v, v * (2 * k) = B + k := ⟨_, Rat.div_mul_cancel (by grind)⟩
  have hk1 : 0 < 1 + 2 * k := by grind
  have hk2 : 0 < 2 * k := by grind
  refine ⟨u, v, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Rat.le_of_mul_le_mul_right (by grind) hk1
  · exact Rat.le_of_mul_le_mul_right (by grind) hk1
  · exact Rat.le_of_mul_le_mul_right (by grind) hk2
  · exact Rat.le_of_mul_le_mul_right (by grind) hk2
  · apply eq_of_mul_right hD
    grind
  · apply eq_of_mul_right hD
    grind

/-- The two triangles of the rectangle about the segment from `a` to `b`, of half-width `h`. The
ends are square caps that extend by `h` at least, and there is no join geometry: where segments
meet, their rectangles overlap. -/
def segTriangles (h : Rat) (a b : Pt) : List Tri :=
  let fr := a.frame (a.dir b) h
  let o := fr.1
  let e := fr.2.1
  let g := fr.2.2
  [⟨o, ⟨o.x + e.x, o.y + e.y⟩, ⟨o.x + g.x, o.y + g.y⟩⟩,
   ⟨⟨o.x + e.x + g.x, o.y + e.y + g.y⟩, ⟨o.x + g.x, o.y + g.y⟩, ⟨o.x + e.x, o.y + e.y⟩⟩]

/-- Every point within `h` of the segment from `a` to `b`, which is everything the model says a
segment of half-width `h` occupies, lies in one of the triangles. -/
theorem thicken_seg_sub_segTriangles {h : Rat} (hh : 0 < h) (a b p : Pt)
    (hp : Region.thicken h (Region.seg a b) p) : ∃ t ∈ segTriangles h a b, t.region p := by
  obtain ⟨q, ⟨s, hs0, hs1, hqx, hqy⟩, hd⟩ := hp
  have hD := dir_sq_pos a b
  have key : ∃ t : Rat, 0 ≤ t ∧ t ≤ 1 ∧ q = ⟨a.x + t * (a.dir b).x, a.y + t * (a.dir b).y⟩ := by
    unfold Pt.dir at hD ⊢
    by_cases hab : a = b
    · subst hab
      exact ⟨0, by grind, by grind, by cases q; simp_all <;> grind⟩
    · simp only [hab, ite_false] at hD ⊢
      exact ⟨s, hs0, hs1, by cases q; simp_all⟩
  obtain ⟨t, ht0, ht1, rfl⟩ := key
  obtain ⟨u, v, hu0, hu1, hv0, hv1, hx, hy⟩ := frame_param a (a.dir b) h t hh hD ht0 ht1 p hd
  have hpe : p = ⟨(a.frame (a.dir b) h).1.x + u * (a.frame (a.dir b) h).2.1.x +
      v * (a.frame (a.dir b) h).2.2.x, (a.frame (a.dir b) h).1.y +
      u * (a.frame (a.dir b) h).2.1.y + v * (a.frame (a.dir b) h).2.2.y⟩ := by
    cases p; simp_all
  have := parallelogram_sub_tris (a.frame (a.dir b) h).1 (a.frame (a.dir b) h).2.1
    (a.frame (a.dir b) h).2.2 u v hu0 hu1 hv0 hv1
  rw [← hpe] at this
  unfold segTriangles
  rcases this with h1 | h1
  · exact ⟨_, List.mem_cons_self, h1⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, h1⟩

/-- The triangles of a strip of half-width `h`: those of each segment between adjacent values, and
of each value itself, so a value with no neighbour is still drawn. -/
def stripTriangles (h : Rat) : List (Item Pt) → List Tri
  | [] => []
  | .gap :: rest => stripTriangles h rest
  | .val a :: rest =>
    segTriangles h a a ++
      (match rest with
        | .val b :: _ => segTriangles h a b
        | _ => []) ++ stripTriangles h rest

/-- A strip of positive half-width lies within its triangles, so the triangles cover every pixel
the strip covers under the raster model. -/
theorem strip_region_sub_triangles {h : Rat} (hh : 0 < h) (items : List (Item Pt)) (p : Pt)
    (hp : (Shape.strip h items).region p) : ∃ t ∈ stripTriangles h items, t.region p := by
  obtain ⟨q, hq, hd⟩ := hp
  induction items with
  | nil => exact absurd hq id
  | cons x rest ih =>
    cases x with
    | gap => exact ih hq
    | val a =>
      rcases hq with hq | hq | hq
      · have : q = a := hq
        subst this
        obtain ⟨t, ht, hr⟩ := thicken_seg_sub_segTriangles hh q q p ⟨q, ⟨0, by grind, by grind,
          by grind, by grind⟩, hd⟩
        exact ⟨t, by simp [stripTriangles, ht], hr⟩
      · cases rest with
        | nil => exact absurd hq id
        | cons y rest' =>
          cases y with
          | gap => exact absurd hq id
          | val b =>
            obtain ⟨t, ht, hr⟩ := thicken_seg_sub_segTriangles hh a b p ⟨q, hq, hd⟩
            exact ⟨t, by simp [stripTriangles, ht], hr⟩
      · obtain ⟨t, ht, hr⟩ := ih hq
        exact ⟨t, by simp [stripTriangles, ht], hr⟩

/-- A pixel covered by a strip of positive half-width is covered by one of its triangles. -/
theorem strip_covers_triangles {h : Rat} (hh : 0 < h) (items : List (Item Pt)) (px : Pixel)
    (hc : (Shape.strip h items).region.Covers px) :
    ∃ t ∈ stripTriangles h items, t.region.Covers px :=
  match hc with
  | ⟨p, hp, hx⟩ =>
    match strip_region_sub_triangles hh items p hp with
    | ⟨t, ht, hr⟩ => ⟨t, ht, p, hr, hx⟩

end Inkproof.Scene
