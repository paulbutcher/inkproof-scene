/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Scene.Poly

namespace Inkproof.Scene

/-- A dash pattern in the projection's units (pixels for a pixel projection), measured along the line: `on` drawn, then `off` skipped, repeating
from the start of each run. A pattern whose `on` is not positive or whose `off` is negative draws
the line solid. -/
structure DashPattern where
  on : Rat
  off : Rat
  deriving DecidableEq, Repr

/-- Whether the pattern is one that dashes. -/
def DashPattern.valid (d : DashPattern) : Bool := decide (0 < d.on ∧ 0 ≤ d.off)

/-- The point `t` of the way from `a` to `b`. -/
def Pt.lerp (a b : Pt) (t : Rat) : Pt := ⟨a.x + t * (b.x - a.x), a.y + t * (b.y - a.y)⟩

/-- The length of the segment from `a` to `b` to within `1/1024`, never above the exact length. -/
def segLength (a b : Pt) : Rat :=
  let d := (b.x - a.x) * (b.x - a.x) + (b.y - a.y) * (b.y - a.y)
  (Nat.sqrt (d * (1024 * 1024)).floor.toNat : Rat) / 1024

/-- The dashes of the pattern within the segment from `a` to `b`, which starts `s` along the run: for
each dash that meets the segment, the stretch of it that does, as a pair of points. -/
def dashSeg (d : DashPattern) (s : Rat) (a b : Pt) : List (List Pt) :=
  let len := segLength a b
  let period := d.on + d.off
  if len ≤ 0 then [] else
  let k0 := (s / period).floor.toNat
  let k1 := ((s + len) / period).floor.toNat
  (List.range (k1 + 1 - k0)).filterMap fun i =>
    let start := ((k0 + i : Nat) : Rat) * period
    let lo := max s start
    let hi := min (s + len) (start + d.on)
    if lo < hi then some [a.lerp b ((lo - s) / len), a.lerp b ((hi - s) / len)] else none

/- That a dash is no longer than `on`, and that every full period holds a dash, are checked as
properties only: stating them means measuring the interpolated endpoints with `segLength`, whose
integer square root rounding does not scale with the interpolation parameter, and the proofs did not
close against that rounding. -/

/-- The dashes along the points of a run, whose first point is `s` along it. -/
def dashAlong (d : DashPattern) : Rat → List Pt → List (List Pt)
  | s, a :: b :: rest => dashSeg d s a b ++ dashAlong d (s + segLength a b) (b :: rest)
  | _, _ => []

/-- A run as dashes, each a run of its own. A run of one point has no length and stays as it is. -/
def dashRun (d : DashPattern) (r : List Pt) : List (List Pt) :=
  match r with
  | a :: b :: rest => if d.valid then dashAlong d 0 (a :: b :: rest) else [r]
  | [] => []
  | _ => [r]

theorem DashPattern.valid_iff (d : DashPattern) : d.valid = true ↔ 0 < d.on ∧ 0 ≤ d.off := by
  simp [DashPattern.valid]

theorem segLength_sq_le (a b : Pt) :
    segLength a b * segLength a b ≤
      (b.x - a.x) * (b.x - a.x) + (b.y - a.y) * (b.y - a.y) := by
  have hd : 0 ≤ (b.x - a.x) * (b.x - a.x) + (b.y - a.y) * (b.y - a.y) :=
    Rat.add_nonneg (mul_self_nonneg' _) (mul_self_nonneg' _)
  unfold segLength
  simp only
  generalize (b.x - a.x) * (b.x - a.x) + (b.y - a.y) * (b.y - a.y) = d at hd ⊢
  have h0 : (0 : Rat) ≤ d * (1024 * 1024) := Rat.mul_nonneg hd (by grind)
  have h1 : (((d * (1024 * 1024)).floor.toNat : Nat) : Rat) ≤ d * (1024 * 1024) := by
    have := Rat.floor_le (a := d * (1024 * 1024))
    have h2 : (0 : Int) ≤ (d * (1024 * 1024)).floor := by
      exact Rat.le_floor_iff.mpr (by simpa using h0)
    have h4 : (((d * (1024 * 1024)).floor.toNat : Nat) : Rat) = (((d * (1024 * 1024)).floor : Int) : Rat) := by
      have := Int.toNat_of_nonneg h2
      exact_mod_cast this
    rw [h4]; exact this
  generalize (d * (1024 * 1024)).floor.toNat = n at h1
  have h3 : ((Nat.sqrt n * Nat.sqrt n : Nat) : Rat) ≤ n := by
    exact_mod_cast Nat.sqrt_le n
  generalize Nat.sqrt n = m at h3
  push_cast at h3
  have h5 : (m : Rat) / 1024 * 1024 = m := Rat.div_mul_cancel (by grind)
  generalize (m : Rat) / 1024 = q at h5
  refine Rat.le_of_mul_le_mul_right (c := 1024 * 1024) ?_ (by grind)
  rw [← h5] at h3
  grind

/-- The length is within `1/1024` of the exact one: the exact squared length is at most the square of
the computed length plus `1/1024`. -/
theorem sq_le_segLength_add (a b : Pt) :
    (b.x - a.x) * (b.x - a.x) + (b.y - a.y) * (b.y - a.y) ≤
      (segLength a b + 1 / 1024) * (segLength a b + 1 / 1024) := by
  have hd : 0 ≤ (b.x - a.x) * (b.x - a.x) + (b.y - a.y) * (b.y - a.y) :=
    Rat.add_nonneg (mul_self_nonneg' _) (mul_self_nonneg' _)
  unfold segLength
  simp only
  generalize (b.x - a.x) * (b.x - a.x) + (b.y - a.y) * (b.y - a.y) = d at hd ⊢
  have h0 : (0 : Rat) ≤ d * (1024 * 1024) := Rat.mul_nonneg hd (by grind)
  have h2 : (0 : Int) ≤ (d * (1024 * 1024)).floor :=
    Rat.le_floor_iff.mpr (by simpa using h0)
  have h4 : (((d * (1024 * 1024)).floor.toNat : Nat) : Rat) = (((d * (1024 * 1024)).floor : Int) : Rat) := by
    have := Int.toNat_of_nonneg h2
    exact_mod_cast this
  have h1 : d * (1024 * 1024) < (((d * (1024 * 1024)).floor.toNat : Nat) : Rat) + 1 := by
    rw [h4]; have := Rat.lt_floor_add_one (d * (1024 * 1024)); push_cast at this; exact this
  generalize (d * (1024 * 1024)).floor.toNat = n at h1
  have h3 : ((n + 1 : Nat) : Rat) ≤ ((Nat.sqrt n + 1) * (Nat.sqrt n + 1) : Nat) := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.lt_succ_sqrt n)
  generalize Nat.sqrt n = m at h3
  push_cast at h3
  have h5 : ((m : Rat) / 1024 + 1 / 1024) * 1024 = m + 1 := by
    rw [Rat.add_mul, Rat.div_mul_cancel (by grind)]; grind
  generalize (m : Rat) / 1024 + 1 / 1024 = q at h5
  refine Rat.le_of_mul_le_mul_right (c := 1024 * 1024) ?_ (by grind)
  have h6 : q * q * (1024 * 1024) = (q * 1024) * (q * 1024) := by grind
  rw [h6, h5]
  grind

private theorem frac_mem {u len : Rat} (hl : 0 < len) (h0 : 0 ≤ u) (h1 : u ≤ len) :
    0 ≤ u / len ∧ u / len ≤ 1 := by
  have key : u / len * len = u := Rat.div_mul_cancel (by grind)
  generalize u / len = q at key
  constructor
  · refine Classical.byContradiction fun hc => ?_
    have := Rat.mul_pos (a := -q) (b := len) (by grind) hl
    grind
  · refine Classical.byContradiction fun hc => ?_
    have := Rat.mul_pos (a := q - 1) (b := len) (by grind) hl
    grind

/-- A point `t` of the way along a segment, for `t` from 0 to 1, lies on it. -/
theorem lerp_mem_seg (a b : Pt) {t : Rat} (h0 : 0 ≤ t) (h1 : t ≤ 1) : Region.seg a b (a.lerp b t) :=
  ⟨t, h0, h1, rfl, rfl⟩

private theorem seg_lerp_sub (a b : Pt) {t1 t2 : Rat} (h1 : 0 ≤ t1) (h1' : t1 ≤ 1) (h2 : 0 ≤ t2)
    (h2' : t2 ≤ 1) (x : Pt) (hx : Region.seg (a.lerp b t1) (a.lerp b t2) x) : Region.seg a b x := by
  obtain ⟨u, hu0, hu1, hxx, hxy⟩ := hx
  refine ⟨t1 + u * (t2 - t1), ?_, ?_, ?_, ?_⟩
  · have := Rat.mul_nonneg hu0 (a := u) (b := t1)
    have h3 : 0 ≤ (1 - u) * t1 := Rat.mul_nonneg (by grind) h1
    have h4 : 0 ≤ u * t2 := Rat.mul_nonneg hu0 h2
    grind
  · have h3 : (1 - u) * t1 ≤ (1 - u) * 1 := Rat.mul_le_mul_of_nonneg_left h1' (by grind)
    have h4 : u * t2 ≤ u * 1 := Rat.mul_le_mul_of_nonneg_left h2' hu0
    grind
  · simp only [Pt.lerp] at hxx; grind
  · simp only [Pt.lerp] at hxy; grind

/-- Every point of every dash of a segment lies on the segment. -/
theorem dashSeg_sub {d : DashPattern} {s : Rat} {a b : Pt} {r : List Pt} (hr : r ∈ dashSeg d s a b)
    (x : Pt) (hx : poly r x) : Region.seg a b x := by
  unfold dashSeg at hr
  simp only [] at hr
  split at hr
  · simp at hr
  · rename_i hlen
    simp only [List.mem_filterMap, List.mem_range] at hr
    obtain ⟨i, -, hi⟩ := hr
    split at hi
    · rename_i hlt
      simp only [Option.some.injEq] at hi
      subst hi
      have hl : 0 < segLength a b := by grind
      generalize (s / (d.on + d.off)).floor.toNat + i = k at *
      have hlo : s ≤ max s (k * (d.on + d.off)) := by grind
      have hlo2 : max s (k * (d.on + d.off)) < min (s + segLength a b) (k * (d.on + d.off) + d.on) := hlt
      have hhi : min (s + segLength a b) (k * (d.on + d.off) + d.on) ≤ s + segLength a b := by grind
      generalize max s (k * (d.on + d.off)) = lo at *
      generalize min (s + segLength a b) (k * (d.on + d.off) + d.on) = hi at *
      obtain ⟨f0, f1⟩ := frac_mem hl (u := lo - s) (by grind) (by grind)
      obtain ⟨g0, g1⟩ := frac_mem hl (u := hi - s) (by grind) (by grind)
      rcases (poly_cons_cons _ _ [] x).mp hx with h | h | h
      · subst h; exact lerp_mem_seg a b f0 f1
      · exact seg_lerp_sub a b f0 f1 g0 g1 x h
      · rw [poly_single] at h; subst h; exact lerp_mem_seg a b g0 g1
    · simp at hi

theorem dashAlong_sub (d : DashPattern) (l : List Pt) (s : Rat) {r : List Pt}
    (hr : r ∈ dashAlong d s l) (x : Pt) (hx : poly r x) : poly l x := by
  induction l generalizing s with
  | nil => simp [dashAlong] at hr
  | cons a rest ih =>
    cases rest with
    | nil => simp [dashAlong] at hr
    | cons b rest' =>
      simp only [dashAlong, List.mem_append] at hr
      rcases hr with h | h
      · exact (poly_cons_cons a b rest' x).mpr (Or.inr (Or.inl (dashSeg_sub h x hx)))
      · exact (poly_cons_cons a b rest' x).mpr (Or.inr (Or.inr (ih _ h)))

/-- Every point of every dash of a run lies on the run, so dashing never draws where the undashed
line does not. -/
theorem dashRun_sub (d : DashPattern) (l : List Pt) {r : List Pt} (hr : r ∈ dashRun d l)
    (x : Pt) (hx : poly r x) : poly l x := by
  unfold dashRun at hr
  split at hr
  · split at hr
    · exact dashAlong_sub _ _ _ hr x hx
    · simp at hr; subst hr; exact hx
  · simp at hr
  · simp at hr; subst hr; exact hx

end Inkproof.Scene
