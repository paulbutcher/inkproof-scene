/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Scene.Coverage

namespace Inkproof.Scene

/-! # Exact tests for a region meeting a window

A `Window` is a closed axis-aligned rectangle, empty when inverted; a pixel's square is one. Each test
decides, in exact rational arithmetic, whether a primitive's region has a point in a window, and
carries a proof that it agrees with the region. -/

structure Window where
  x0 : Rat
  y0 : Rat
  x1 : Rat
  y1 : Rat
  deriving DecidableEq, Repr

def Window.Has (w : Window) (p : Pt) : Prop := w.x0 ≤ p.x ∧ p.x ≤ w.x1 ∧ w.y0 ≤ p.y ∧ p.y ≤ w.y1

/-- The region has a point in the window. -/
def Region.Meets (r : Region) (w : Window) : Prop := ∃ p, r p ∧ w.Has p

def Pixel.window (px : Pixel) : Window := ⟨px.col, px.row, px.col + 1, px.row + 1⟩

theorem Region.covers_iff_meets (r : Region) (px : Pixel) : r.Covers px ↔ r.Meets px.window :=
  Iff.rfl

/-- The window where `w` and `v` overlap. -/
def Window.inter (w v : Window) : Window := ⟨max w.x0 v.x0, max w.y0 v.y0, min w.x1 v.x1, min w.y1 v.y1⟩

theorem Window.has_inter {w v : Window} {p : Pt} : (w.inter v).Has p ↔ w.Has p ∧ v.Has p := by
  simp only [Window.inter, Window.Has]
  grind

/-- The constraint `a + d * t ≤ b` on a parameter `t`. -/
structure Lin where
  a : Rat
  d : Rat
  b : Rat

def Lin.Holds (c : Lin) (t : Rat) : Prop := c.a + c.d * t ≤ c.b

/-- The parameters in `[0, 1]` satisfying the constraint, as an interval (empty when `lo > hi`). -/
def Lin.range (c : Lin) : Rat × Rat :=
  if c.d = 0 then (if c.a ≤ c.b then (0, 1) else (1, 0))
  else if 0 < c.d then (0, (c.b - c.a) / c.d) else ((c.b - c.a) / c.d, 1)

theorem mul_le_mul_right_iff {x y d : Rat} (hd : 0 < d) : x * d ≤ y * d ↔ x ≤ y := by
  constructor
  · intro h
    refine Decidable.byContradiction fun hc => ?_
    have := Rat.mul_lt_mul_of_pos_right (by grind : y < x) hd
    grind
  · intro h
    exact Rat.mul_le_mul_of_nonneg_right h (by grind)

theorem Lin.range_iff (c : Lin) {t : Rat} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    (c.range.1 ≤ t ∧ t ≤ c.range.2) ↔ c.Holds t := by
  unfold Lin.range Lin.Holds
  by_cases hd : c.d = 0
  · simp only [hd, ite_true]
    by_cases hab : c.a ≤ c.b <;> simp [hab, h0, h1] <;> grind
  · simp only [hd, ite_false]
    have hq : (c.b - c.a) / c.d * c.d = c.b - c.a := Rat.div_mul_cancel hd
    by_cases hp : 0 < c.d
    · simp only [hp, ite_true]
      have := mul_le_mul_right_iff (x := t) (y := (c.b - c.a) / c.d) hp
      constructor
      · intro h; grind
      · intro h; exact ⟨h0, this.1 (by grind)⟩
    · have hn : 0 < -c.d := by grind
      simp only [hp, ite_false]
      have := mul_le_mul_right_iff (x := (c.b - c.a) / c.d) (y := t) hn
      constructor
      · intro h; grind
      · intro h; exact ⟨this.1 (by grind), h1⟩

/-- The interval of parameters in `[0, 1]` meeting every constraint. -/
def Lin.rangeAll : List Lin → Rat × Rat
  | [] => (0, 1)
  | c :: cs =>
    let r := rangeAll cs
    (max r.1 c.range.1, min r.2 c.range.2)

theorem Lin.rangeAll_bounds (cs : List Lin) : 0 ≤ (rangeAll cs).1 ∧ (rangeAll cs).2 ≤ 1 := by
  induction cs with
  | nil => simp [rangeAll]
  | cons c cs ih =>
    simp only [rangeAll]
    grind

theorem Lin.rangeAll_iff (cs : List Lin) {t : Rat} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    ((rangeAll cs).1 ≤ t ∧ t ≤ (rangeAll cs).2) ↔ ∀ c ∈ cs, c.Holds t := by
  induction cs with
  | nil => simp [rangeAll, h0, h1]
  | cons c cs ih =>
    simp only [rangeAll, List.mem_cons, forall_eq_or_imp, ← ih, ← range_iff c h0 h1]
    grind

/-- Some parameter in `[0, 1]` meets every constraint. -/
def Lin.feasible (cs : List Lin) : Bool := (rangeAll cs).1 ≤ (rangeAll cs).2

theorem Lin.feasible_iff (cs : List Lin) :
    feasible cs = true ↔ ∃ t : Rat, 0 ≤ t ∧ t ≤ 1 ∧ ∀ c ∈ cs, c.Holds t := by
  have hb := rangeAll_bounds cs
  simp only [feasible, decide_eq_true_eq]
  constructor
  · intro h
    exact ⟨_, hb.1, by grind, (rangeAll_iff cs hb.1 (by grind)).1 ⟨Rat.le_refl, h⟩⟩
  · rintro ⟨t, h0, h1, h⟩
    exact Rat.le_trans ((rangeAll_iff cs h0 h1).2 h).1 ((rangeAll_iff cs h0 h1).2 h).2

/-- The segment from `a` to `b` meets the window. -/
def segMeetsB (a b : Pt) (w : Window) : Bool :=
  Lin.feasible [⟨a.x, b.x - a.x, w.x1⟩, ⟨-a.x, -(b.x - a.x), -w.x0⟩,
    ⟨a.y, b.y - a.y, w.y1⟩, ⟨-a.y, -(b.y - a.y), -w.y0⟩]

theorem segMeetsB_iff (a b : Pt) (w : Window) :
    segMeetsB a b w = true ↔ (Region.seg a b).Meets w := by
  unfold segMeetsB
  rw [Lin.feasible_iff]
  constructor
  · rintro ⟨t, h0, h1, h⟩
    have hx1 := h ⟨a.x, b.x - a.x, w.x1⟩ (by simp)
    have hx0 := h ⟨-a.x, -(b.x - a.x), -w.x0⟩ (by simp)
    have hy1 := h ⟨a.y, b.y - a.y, w.y1⟩ (by simp)
    have hy0 := h ⟨-a.y, -(b.y - a.y), -w.y0⟩ (by simp)
    simp only [Lin.Holds] at hx1 hx0 hy1 hy0
    exact ⟨⟨a.x + t * (b.x - a.x), a.y + t * (b.y - a.y)⟩, ⟨t, h0, h1, rfl, rfl⟩,
      by simp only [Window.Has]; grind⟩
  · rintro ⟨p, ⟨t, h0, h1, hx, hy⟩, h⟩
    refine ⟨t, h0, h1, ?_⟩
    simp only [Window.Has] at h
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl <;> simp only [Lin.Holds] <;> grind

/-- `∃ y` in `[y0, y1]` between `l` and `h`, in either order. -/
theorem exists_between (l h y0 y1 : Rat) :
    (∃ y, Between l h y ∧ y0 ≤ y ∧ y ≤ y1) ↔ y0 ≤ y1 ∧ (l ≤ y1 ∨ h ≤ y1) ∧ (y0 ≤ l ∨ y0 ≤ h) := by
  simp only [Between]
  constructor
  · rintro ⟨y, h1, h2, h3⟩; grind
  · rintro ⟨h0, h1, h2⟩
    by_cases hl : l ≤ h
    · exact ⟨max y0 l, by grind⟩
    · exact ⟨max y0 h, by grind⟩

/-- The quadrilateral swept by `Region.span` meets the window. -/
def spanMeetsB (x0 x1 l0 l1 h0 h1 : Rat) (w : Window) : Bool :=
  let base : List Lin := [⟨x0, x1 - x0, w.x1⟩, ⟨-x0, -(x1 - x0), -w.x0⟩]
  let lo1 : Lin := ⟨l0, l1 - l0, w.y1⟩
  let hi1 : Lin := ⟨h0, h1 - h0, w.y1⟩
  let lo0 : Lin := ⟨-l0, -(l1 - l0), -w.y0⟩
  let hi0 : Lin := ⟨-h0, -(h1 - h0), -w.y0⟩
  decide (w.y0 ≤ w.y1) && (Lin.feasible (base ++ [lo1, lo0]) || Lin.feasible (base ++ [lo1, hi0]) ||
    Lin.feasible (base ++ [hi1, lo0]) || Lin.feasible (base ++ [hi1, hi0]))

theorem spanMeetsB_iff (x0 x1 l0 l1 h0 h1 : Rat) (w : Window) :
    spanMeetsB x0 x1 l0 l1 h0 h1 w = true ↔ (Region.span x0 x1 l0 l1 h0 h1).Meets w := by
  unfold spanMeetsB Region.Meets Region.span
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, Lin.feasible_iff,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false, Lin.Holds, Window.Has]
  constructor
  · rintro ⟨hy, h⟩
    obtain ⟨t, h0', h1', h⟩ : ∃ t : Rat, 0 ≤ t ∧ t ≤ 1 ∧ (x0 + (x1 - x0) * t ≤ w.x1) ∧
        (-x0 + -(x1 - x0) * t ≤ -w.x0) ∧
        (l0 + (l1 - l0) * t ≤ w.y1 ∨ h0 + (h1 - h0) * t ≤ w.y1) ∧
        (-l0 + -(l1 - l0) * t ≤ -w.y0 ∨ -h0 + -(h1 - h0) * t ≤ -w.y0) := by
      rcases h with ((⟨t, a, b, c⟩ | ⟨t, a, b, c⟩) | ⟨t, a, b, c⟩) | ⟨t, a, b, c⟩
      · have e1 := c ⟨x0, x1 - x0, w.x1⟩ (by simp)
        have e2 := c ⟨-x0, -(x1 - x0), -w.x0⟩ (by simp)
        have e3 := c ⟨l0, l1 - l0, w.y1⟩ (by simp)
        have e4 := c ⟨-l0, -(l1 - l0), -w.y0⟩ (by simp)
        exact ⟨t, a, b, by grind⟩
      · have e1 := c ⟨x0, x1 - x0, w.x1⟩ (by simp)
        have e2 := c ⟨-x0, -(x1 - x0), -w.x0⟩ (by simp)
        have e3 := c ⟨l0, l1 - l0, w.y1⟩ (by simp)
        have e4 := c ⟨-h0, -(h1 - h0), -w.y0⟩ (by simp)
        exact ⟨t, a, b, by grind⟩
      · have e1 := c ⟨x0, x1 - x0, w.x1⟩ (by simp)
        have e2 := c ⟨-x0, -(x1 - x0), -w.x0⟩ (by simp)
        have e3 := c ⟨h0, h1 - h0, w.y1⟩ (by simp)
        have e4 := c ⟨-l0, -(l1 - l0), -w.y0⟩ (by simp)
        exact ⟨t, a, b, by grind⟩
      · have e1 := c ⟨x0, x1 - x0, w.x1⟩ (by simp)
        have e2 := c ⟨-x0, -(x1 - x0), -w.x0⟩ (by simp)
        have e3 := c ⟨h0, h1 - h0, w.y1⟩ (by simp)
        have e4 := c ⟨-h0, -(h1 - h0), -w.y0⟩ (by simp)
        exact ⟨t, a, b, by grind⟩
    have := (exists_between (l0 + t * (l1 - l0)) (h0 + t * (h1 - h0)) w.y0 w.y1).2
      ⟨hy, by grind, by grind⟩
    obtain ⟨y, hy'⟩ := this
    exact ⟨⟨x0 + t * (x1 - x0), y⟩, ⟨t, h0', h1', rfl, hy'.1⟩, by grind⟩
  · rintro ⟨p, ⟨t, h0', h1', hx, hb⟩, hw⟩
    have := (exists_between _ _ w.y0 w.y1).1 ⟨p.y, hb, hw.2.2.1, hw.2.2.2⟩
    refine ⟨this.1, ?_⟩
    rcases this.2.1 with a | a <;> rcases this.2.2 with b | b
    · exact Or.inl (Or.inl (Or.inl ⟨t, h0', h1', by rintro c ((rfl | rfl) | rfl | rfl) <;> grind⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨t, h0', h1', by rintro c ((rfl | rfl) | rfl | rfl) <;> grind⟩))
    · exact Or.inl (Or.inr ⟨t, h0', h1', by rintro c ((rfl | rfl) | rfl | rfl) <;> grind⟩)
    · exact Or.inr ⟨t, h0', h1', by rintro c ((rfl | rfl) | rfl | rfl) <;> grind⟩

theorem sq_le_sq_pos {a b : Rat} (h0 : 0 ≤ a) (h : a ≤ b) : a * a ≤ b * b :=
  Rat.le_trans (Rat.mul_le_mul_of_nonneg_left h h0) (Rat.mul_le_mul_of_nonneg_right h (by grind))

theorem sq_le_sq_neg {a b : Rat} (h0 : a ≤ 0) (h : b ≤ a) : a * a ≤ b * b := by
  have := sq_le_sq_pos (a := -a) (b := -b) (by grind) (by grind)
  grind

/-- `a * a ≤ ρ * ρ` bounds `a` by `ρ` in magnitude. -/
theorem abs_le_of_sq_le {a ρ : Rat} (hρ : 0 ≤ ρ) (h : a * a ≤ ρ * ρ) : -ρ ≤ a ∧ a ≤ ρ := by
  constructor
  · refine Decidable.byContradiction fun hc => ?_
    have := Rat.mul_pos (by grind : 0 < -ρ - a) (by grind : 0 < -a + ρ)
    grind
  · refine Decidable.byContradiction fun hc => ?_
    have := Rat.mul_pos (by grind : 0 < a - ρ) (by grind : 0 < a + ρ)
    grind

/-- The point of `[lo, hi]` nearest `v`. -/
def clamp (v lo hi : Rat) : Rat := max lo (min v hi)

theorem clamp_mem {v lo hi : Rat} (h : lo ≤ hi) : lo ≤ clamp v lo hi ∧ clamp v lo hi ≤ hi := by
  unfold clamp; grind

/-- The clamped point is no farther from `v` than any point of the interval. -/
theorem clamp_sq_le {v lo hi p : Rat} (h : lo ≤ p) (h' : p ≤ hi) :
    (clamp v lo hi - v) * (clamp v lo hi - v) ≤ (p - v) * (p - v) := by
  have hl : lo ≤ hi := Rat.le_trans h h'
  unfold clamp
  by_cases h1 : v ≤ lo
  · have : max lo (min v hi) = lo := by grind
    rw [this]; exact sq_le_sq_pos (by grind) (by grind)
  by_cases h2 : hi ≤ v
  · have : max lo (min v hi) = hi := by grind
    rw [this]; exact sq_le_sq_neg (by grind) (by grind)
  · have : max lo (min v hi) = v := by grind
    rw [this]; simp only [Rat.sub_self, Rat.zero_mul]; exact mul_self_nonneg' _

/-- The disc of radius `r` about `c` meets the window. -/
def discMeetsB (c : Pt) (r : Rat) (w : Window) : Bool :=
  decide (w.x0 ≤ w.x1 ∧ w.y0 ≤ w.y1) &&
    decide ((clamp c.x w.x0 w.x1 - c.x) * (clamp c.x w.x0 w.x1 - c.x) +
      (clamp c.y w.y0 w.y1 - c.y) * (clamp c.y w.y0 w.y1 - c.y) ≤ r * r)

theorem discMeetsB_iff (c : Pt) (r : Rat) (w : Window) :
    discMeetsB c r w = true ↔ (Region.disc c r).Meets w := by
  unfold discMeetsB Region.Meets Region.disc
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨hx, hy⟩, h⟩
    have a := clamp_mem (v := c.x) hx
    have b := clamp_mem (v := c.y) hy
    exact ⟨⟨clamp c.x w.x0 w.x1, clamp c.y w.y0 w.y1⟩, by grind, by simp only [Window.Has]; grind⟩
  · rintro ⟨p, hp, hw⟩
    obtain ⟨a, b, c', d⟩ := hw
    have h1 := clamp_sq_le (v := c.x) a b
    have h2 := clamp_sq_le (v := c.y) c' d
    exact ⟨⟨Rat.le_trans a b, Rat.le_trans c' d⟩, by grind⟩

theorem quad_min {D k E t0 t : Rat} (hD : 0 < D) (hq : t0 * D = -k) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    D * clamp t0 0 1 * clamp t0 0 1 + 2 * clamp t0 0 1 * k + E ≤ D * t * t + 2 * t * k + E := by
  obtain rfl : k = -(t0 * D) := by grind
  unfold clamp
  by_cases a : t0 ≤ 0
  · have e : max 0 (min t0 1) = 0 := by grind
    rw [e]
    have := Rat.mul_nonneg (Rat.mul_nonneg (by grind : (0:Rat) ≤ D) h0) (by grind : 0 ≤ t - 2 * t0)
    grind
  by_cases b : 1 ≤ t0
  · have e : max 0 (min t0 1) = 1 := by grind
    rw [e]
    have := Rat.mul_nonneg (Rat.mul_nonneg (by grind : (0:Rat) ≤ D) (by grind : 0 ≤ 1 - t)) (by grind : 0 ≤ 2 * t0 - t - 1)
    grind
  · have e : max 0 (min t0 1) = t0 := by grind
    rw [e]
    have := Rat.mul_nonneg (by grind : (0:Rat) ≤ D) (mul_self_nonneg' (t - t0))
    grind

/-- Some point of the segment from `a` to `b` lies in the disc of radius `r` about `c`. -/
def segDiscB (a b c : Pt) (r : Rat) : Bool :=
  let dx := b.x - a.x
  let dy := b.y - a.y
  let ex := a.x - c.x
  let ey := a.y - c.y
  let t := clamp (-(dx * ex + dy * ey) / (dx * dx + dy * dy)) 0 1
  decide ((ex + t * dx) * (ex + t * dx) + (ey + t * dy) * (ey + t * dy) ≤ r * r)

theorem segDiscB_iff (a b c : Pt) (r : Rat) :
    segDiscB a b c r = true ↔ ∃ q, Region.seg a b q ∧ Region.disc c r q := by
  unfold segDiscB Region.seg Region.disc
  simp only [decide_eq_true_eq]
  generalize hdx : b.x - a.x = dx
  generalize hdy : b.y - a.y = dy
  generalize hex : a.x - c.x = ex
  generalize hey : a.y - c.y = ey
  constructor
  · intro h
    have hb := clamp_mem (v := -(dx * ex + dy * ey) / (dx * dx + dy * dy)) (lo := 0) (hi := 1)
      (by grind)
    generalize clamp (-(dx * ex + dy * ey) / (dx * dx + dy * dy)) 0 1 = t at h hb
    have e1 : a.x + t * dx - c.x = ex + t * dx := by rw [← hex]; grind
    have e2 : a.y + t * dy - c.y = ey + t * dy := by rw [← hey]; grind
    exact ⟨⟨a.x + t * dx, a.y + t * dy⟩, ⟨t, hb.1, hb.2, rfl, rfl⟩,
      by simp only []; rw [e1, e2]; exact h⟩
  · rintro ⟨q, ⟨t, h0, h1, hx, hy⟩, h⟩
    have e1 : q.x - c.x = ex + t * dx := by rw [hx, ← hex]; grind
    have e2 : q.y - c.y = ey + t * dy := by rw [hy, ← hey]; grind
    have hid : (ex + t * dx) * (ex + t * dx) + (ey + t * dy) * (ey + t * dy) ≤ r * r := by
      rw [← e1, ← e2]; exact h
    by_cases hD : dx * dx + dy * dy = 0
    · have hx0 := abs_le_of_sq_le (a := dx) (ρ := 0) (Rat.le_refl) (by
        have := mul_self_nonneg' dy; have := mul_self_nonneg' dx; grind)
      have hy0 := abs_le_of_sq_le (a := dy) (ρ := 0) (Rat.le_refl) (by
        have := mul_self_nonneg' dy; have := mul_self_nonneg' dx; grind)
      have e1 : dx = 0 := by grind
      have e2 : dy = 0 := by grind
      subst e1 e2
      simp only [Rat.div_def, Rat.zero_mul, Rat.add_zero, Rat.neg_zero, Rat.mul_zero] at *
      grind
    · have hpos : 0 < dx * dx + dy * dy := by
        have := mul_self_nonneg' dy; have := mul_self_nonneg' dx; grind
      have hq : -(dx * ex + dy * ey) / (dx * dx + dy * dy) * (dx * dx + dy * dy) =
          -(dx * ex + dy * ey) := Rat.div_mul_cancel hD
      have := quad_min (E := ex * ex + ey * ey) hpos hq h0 h1
      grind

/-- A point `q` is within `|r|` of some point of the window. -/
def Window.Near (w : Window) (r : Rat) (q : Pt) : Prop := ∃ p, w.Has p ∧ Region.disc q r p

/-- A coordinate within `ρ` of `[lo, hi]` is within `ρ` of its clamp. -/
theorem clamp_sq_le_of_near {v lo hi ρ : Rat} (hl : lo ≤ hi) (hρ : 0 ≤ ρ) (a : lo - ρ ≤ v)
    (b : v ≤ hi + ρ) : (clamp v lo hi - v) * (clamp v lo hi - v) ≤ ρ * ρ := by
  unfold clamp
  by_cases h1 : v ≤ lo
  · have : max lo (min v hi) = lo := by grind
    rw [this]; exact sq_le_sq_pos (by grind) (by grind)
  by_cases h2 : hi ≤ v
  · have : max lo (min v hi) = hi := by grind
    rw [this]
    have := sq_le_sq_neg (a := hi - v) (b := -ρ) (by grind) (by grind)
    grind
  · have : max lo (min v hi) = v := by grind
    rw [this]; simp only [Rat.sub_self, Rat.zero_mul]; exact Rat.mul_nonneg hρ hρ

/-- Where a segment must reach to come within `|r|` of a nonempty window: the window widened
sideways, the window widened vertically, or a disc at one of its corners. -/
theorem Window.near_iff (w : Window) (r : Rat) (hx : w.x0 ≤ w.x1) (hy : w.y0 ≤ w.y1) (q : Pt) :
    w.Near r q ↔
      (⟨w.x0 - r.abs, w.y0, w.x1 + r.abs, w.y1⟩ : Window).Has q ∨
      (⟨w.x0, w.y0 - r.abs, w.x1, w.y1 + r.abs⟩ : Window).Has q ∨
      Region.disc ⟨w.x0, w.y0⟩ r q ∨ Region.disc ⟨w.x1, w.y0⟩ r q ∨
      Region.disc ⟨w.x0, w.y1⟩ r q ∨ Region.disc ⟨w.x1, w.y1⟩ r q := by
  have hρ : 0 ≤ r.abs := Rat.abs_nonneg
  have hρ2 : r.abs * r.abs = r * r := by
    rcases Rat.le_total (a := 0) (b := r) with h | h
    · rw [Rat.abs_of_nonneg h]
    · rw [Rat.abs_of_nonpos h]; grind
  simp only [Window.Near, Window.Has, Region.disc]
  constructor
  · rintro ⟨p, ⟨a, b, c, d⟩, h⟩
    have h1 := mul_self_nonneg' (p.x - q.x)
    have h2 := mul_self_nonneg' (p.y - q.y)
    have bx := abs_le_of_sq_le hρ (a := p.x - q.x) (by grind)
    have by' := abs_le_of_sq_le hρ (a := p.y - q.y) (by grind)
    by_cases qx0 : w.x0 ≤ q.x ∧ q.x ≤ w.x1
    · exact Or.inr (Or.inl ⟨qx0.1, qx0.2, by grind, by grind⟩)
    by_cases qy0 : w.y0 ≤ q.y ∧ q.y ≤ w.y1
    · exact Or.inl ⟨by grind, by grind, qy0.1, qy0.2⟩
    by_cases u : q.x < w.x0
    · have e1 := sq_le_sq_pos (a := w.x0 - q.x) (b := p.x - q.x) (by grind) (by grind)
      by_cases v : q.y < w.y0
      · have e2 := sq_le_sq_pos (a := w.y0 - q.y) (b := p.y - q.y) (by grind) (by grind)
        exact Or.inr (Or.inr (Or.inl (by grind)))
      · have e2 := sq_le_sq_neg (a := w.y1 - q.y) (b := p.y - q.y) (by grind) (by grind)
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by grind)))))
    · have e1 := sq_le_sq_neg (a := w.x1 - q.x) (b := p.x - q.x) (by grind) (by grind)
      by_cases v : q.y < w.y0
      · have e2 := sq_le_sq_pos (a := w.y0 - q.y) (b := p.y - q.y) (by grind) (by grind)
        exact Or.inr (Or.inr (Or.inr (Or.inl (by grind))))
      · have e2 := sq_le_sq_neg (a := w.y1 - q.y) (b := p.y - q.y) (by grind) (by grind)
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by grind)))))
  · rintro (⟨a, b, c, d⟩ | ⟨a, b, c, d⟩ | h | h | h | h)
    · have := clamp_sq_le_of_near (v := q.x) hx hρ a b
      have := clamp_mem (v := q.x) hx
      exact ⟨⟨clamp q.x w.x0 w.x1, q.y⟩, by simp only []; grind, by grind⟩
    · have := clamp_sq_le_of_near (v := q.y) hy hρ c d
      have := clamp_mem (v := q.y) hy
      exact ⟨⟨q.x, clamp q.y w.y0 w.y1⟩, by simp only []; grind, by grind⟩
    · refine ⟨⟨w.x0, w.y0⟩, ⟨Rat.le_refl, hx, Rat.le_refl, hy⟩, ?_⟩; simp only []; grind
    · refine ⟨⟨w.x1, w.y0⟩, ⟨hx, Rat.le_refl, Rat.le_refl, hy⟩, ?_⟩; simp only []; grind
    · refine ⟨⟨w.x0, w.y1⟩, ⟨Rat.le_refl, hx, hy, Rat.le_refl⟩, ?_⟩; simp only []; grind
    · refine ⟨⟨w.x1, w.y1⟩, ⟨hx, Rat.le_refl, hy, Rat.le_refl⟩, ?_⟩; simp only []; grind

/-- Some point of the segment from `a` to `b` is within `|r|` of the window. -/
def segNearB (a b : Pt) (r : Rat) (w : Window) : Bool :=
  decide (w.x0 ≤ w.x1 ∧ w.y0 ≤ w.y1) &&
    (segMeetsB a b ⟨w.x0 - r.abs, w.y0, w.x1 + r.abs, w.y1⟩ ||
      segMeetsB a b ⟨w.x0, w.y0 - r.abs, w.x1, w.y1 + r.abs⟩ ||
      segDiscB a b ⟨w.x0, w.y0⟩ r || segDiscB a b ⟨w.x1, w.y0⟩ r ||
      segDiscB a b ⟨w.x0, w.y1⟩ r || segDiscB a b ⟨w.x1, w.y1⟩ r)

theorem segNearB_iff (a b : Pt) (r : Rat) (w : Window) :
    segNearB a b r w = true ↔ ∃ q, Region.seg a b q ∧ w.Near r q := by
  unfold segNearB
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, segMeetsB_iff, segDiscB_iff]
  constructor
  · rintro ⟨⟨hx, hy⟩, h⟩
    rcases h with ((((⟨q, a1, a2⟩ | ⟨q, a1, a2⟩) | ⟨q, a1, a2⟩) | ⟨q, a1, a2⟩) | ⟨q, a1, a2⟩) |
      ⟨q, a1, a2⟩ <;>
      exact ⟨q, a1, (Window.near_iff w r hx hy q).2 (by grind)⟩
  · rintro ⟨q, hq, hn⟩
    have hx : w.x0 ≤ w.x1 := by
      obtain ⟨p, h, _⟩ := hn; exact Rat.le_trans h.1 h.2.1
    have hy : w.y0 ≤ w.y1 := by
      obtain ⟨p, h, _⟩ := hn; exact Rat.le_trans h.2.2.1 h.2.2.2
    refine ⟨⟨hx, hy⟩, ?_⟩
    rcases (Window.near_iff w r hx hy q).1 hn with h | h | h | h | h | h
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨q, hq, h⟩))))
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨q, hq, h⟩))))
    · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨q, hq, h⟩)))
    · exact Or.inl (Or.inl (Or.inr ⟨q, hq, h⟩))
    · exact Or.inl (Or.inr ⟨q, hq, h⟩)
    · exact Or.inr ⟨q, hq, h⟩

theorem discMeetsB_near_iff (a : Pt) (r : Rat) (w : Window) :
    discMeetsB a r w = true ↔ w.Near r a := by
  rw [discMeetsB_iff]
  constructor
  · rintro ⟨p, h1, h2⟩; exact ⟨p, h2, h1⟩
  · rintro ⟨p, h1, h2⟩; exact ⟨p, h2, h1⟩

namespace Item

variable {α : Type}

/-- Some value or some adjacent pair of values, with no gap between, satisfies the test. -/
def anyB (fs : α → Bool) (fj : α → α → Bool) : List (Item α) → Bool
  | [] => false
  | .gap :: rest => anyB fs fj rest
  | .val a :: rest =>
    fs a || (match rest with
      | .val b :: _ => fj a b
      | _ => false) || anyB fs fj rest

theorem anyB_iff {fs : α → Bool} {fj : α → α → Bool} {single : α → Region} {join : α → α → Region}
    {M : Pt → Prop} (hs : ∀ a, fs a = true ↔ ∃ q, single a q ∧ M q)
    (hj : ∀ a b, fj a b = true ↔ ∃ q, join a b q ∧ M q) (items : List (Item α)) :
    anyB fs fj items = true ↔ ∃ q, chain single join items q ∧ M q := by
  induction items with
  | nil => simp [anyB, chain]
  | cons x rest ih =>
    cases x with
    | gap => simpa [anyB, chain] using ih
    | val a =>
      simp only [anyB, chain, Bool.or_eq_true, hs, ih]
      constructor
      · rintro ((⟨q, h, m⟩ | h) | ⟨q, h, m⟩)
        · exact ⟨q, Or.inl h, m⟩
        · cases rest with
          | nil => simp at h
          | cons y ys =>
            cases y with
            | gap => simp at h
            | val b => obtain ⟨q, h, m⟩ := (hj a b).1 h; exact ⟨q, Or.inr (Or.inl h), m⟩
        · exact ⟨q, Or.inr (Or.inr h), m⟩
      · rintro ⟨q, h | h | h, m⟩
        · exact Or.inl (Or.inl ⟨q, h, m⟩)
        · refine Or.inl (Or.inr ?_)
          cases rest with
          | nil => simp at h
          | cons y ys =>
            cases y with
            | gap => simp at h
            | val b => exact (hj a b).2 ⟨q, h, m⟩
        · exact Or.inr ⟨q, h, m⟩

end Item

end Inkproof.Scene
