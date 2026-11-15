/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Scene.Coverage

namespace Inkproof.Scene

/-- The bare polyline through the points, in order. -/
def poly (l : List Pt) : Region := Item.chain Region.point Region.seg (l.map Item.val)

theorem poly_nil (p : Pt) : ¬ poly [] p := id

theorem poly_single (a p : Pt) : poly [a] p ↔ p = a := by
  simp [poly, Item.chain, Region.point]

theorem poly_cons_cons (a b : Pt) (l : List Pt) (p : Pt) :
    poly (a :: b :: l) p ↔ p = a ∨ Region.seg a b p ∨ poly (b :: l) p := by
  simp [poly, Item.chain, Region.point]

theorem poly_append {A B : List Pt} {a b : Pt} (hA : A.getLast? = some a) (hB : B.head? = some b)
    (p : Pt) : poly (A ++ B) p ↔ poly A p ∨ Region.seg a b p ∨ poly B p := by
  induction A with
  | nil => simp at hA
  | cons x rest ih =>
    cases rest with
    | nil =>
      simp at hA
      subst hA
      obtain ⟨B', rfl⟩ : ∃ B', B = b :: B' := by cases B <;> simp_all
      simp [poly_cons_cons, poly_single]
    | cons y rest' =>
      have hA' : (y :: rest').getLast? = some a := by simpa [List.getLast?_cons_cons] using hA
      have := ih hA'
      simp only [List.cons_append, poly_cons_cons] at this ⊢
      rw [this]
      simp only [or_assoc]

/-- Every point of a polyline lies on a segment between two of its points. -/
theorem poly_mem {l : List Pt} {q : Pt} (h : poly l q) :
    ∃ a ∈ l, ∃ b ∈ l, Region.seg a b q := by
  induction l with
  | nil => exact absurd h (poly_nil q)
  | cons x rest ih =>
    cases rest with
    | nil =>
      rw [poly_single] at h
      subst h
      exact ⟨q, by simp, q, by simp, 0, by grind, by grind, by grind, by grind⟩
    | cons y rest' =>
      rcases (poly_cons_cons x y rest' q).mp h with h | h | h
      · subst h
        exact ⟨q, by simp, q, by simp, 0, by grind, by grind, by grind, by grind⟩
      · exact ⟨x, by simp, y, by simp, h⟩
      · obtain ⟨a, ha, b, hb, hs⟩ := ih h
        exact ⟨a, List.mem_cons_of_mem _ ha, b, List.mem_cons_of_mem _ hb, hs⟩

/-- Every point of a polyline is one of its points, or lies on a segment between two points that
are adjacent in it. -/
theorem poly_mem_adj {l : List Pt} {q : Pt} (h : poly l q) :
    (q ∈ l) ∨ ∃ a b, [a, b] <:+: l ∧ Region.seg a b q := by
  induction l with
  | nil => exact absurd h (poly_nil q)
  | cons x rest ih =>
    cases rest with
    | nil =>
      rw [poly_single] at h
      subst h
      exact Or.inl (by simp)
    | cons y rest' =>
      rcases (poly_cons_cons x y rest' q).mp h with h | h | h
      · subst h; exact Or.inl (by simp)
      · exact Or.inr ⟨x, y, ⟨[], rest', by simp⟩, h⟩
      · rcases ih h with h | ⟨a, b, hi, hs⟩
        · exact Or.inl (List.mem_cons_of_mem _ h)
        · exact Or.inr ⟨a, b, List.infix_cons hi, hs⟩

theorem between_comm {a b v : Rat} (h : Between a b v) : Between b a v := by
  unfold Between at *; grind

theorem between_split {a b v y : Rat} (h : Between a v y) : Between a b y ∨ Between b v y := by
  unfold Between at *; grind

private theorem frac_bounds {t d s : Rat} (h : t * d = s)
    (hb : (0 < d ∧ 0 ≤ s ∧ s ≤ d) ∨ (d < 0 ∧ s ≤ 0 ∧ d ≤ s)) : 0 ≤ t ∧ t ≤ 1 := by
  rcases hb with ⟨hd, h0, h1⟩ | ⟨hd, h0, h1⟩
  · constructor
    · refine Classical.byContradiction fun hc => ?_
      have := Rat.mul_pos (a := -t) (b := d) (by grind) hd
      grind
    · refine Classical.byContradiction fun hc => ?_
      have := Rat.mul_pos (a := t - 1) (b := d) (by grind) hd
      grind
  · constructor
    · refine Classical.byContradiction fun hc => ?_
      have := Rat.mul_pos (a := -t) (b := -d) (by grind) (by grind)
      grind
    · refine Classical.byContradiction fun hc => ?_
      have := Rat.mul_pos (a := t - 1) (b := -d) (by grind) (by grind)
      grind

theorem seg_exists_y {a b : Pt} {y : Rat} (h : Between a.y b.y y) :
    ∃ q, Region.seg a b q ∧ q.y = y := by
  by_cases hy : a.y = b.y
  · exact ⟨a, ⟨0, by grind, by grind, by grind, by grind⟩, by unfold Between at h; grind⟩
  · have hne : b.y - a.y ≠ 0 := by grind
    have key : (y - a.y) / (b.y - a.y) * (b.y - a.y) = y - a.y := Rat.div_mul_cancel hne
    have hb := frac_bounds key (by unfold Between at h; grind)
    exact ⟨⟨a.x + (y - a.y) / (b.y - a.y) * (b.x - a.x), y⟩,
      ⟨(y - a.y) / (b.y - a.y), hb.1, hb.2, rfl, by simp only; grind⟩, rfl⟩

/-- Whatever heights two points of a polyline have, it passes through every height between them. -/
theorem poly_exists_y {l : List Pt} {u v : Pt} (hu : u ∈ l) (hv : v ∈ l) {y : Rat}
    (h : Between u.y v.y y) : ∃ q, poly l q ∧ q.y = y := by
  induction l generalizing u v with
  | nil => simp at hu
  | cons x rest ih =>
    cases rest with
    | nil =>
      have hux : u = x := by simpa using hu
      have hvx : v = x := by simpa using hv
      rw [hux, hvx] at h
      exact ⟨x, (poly_single x x).mpr rfl, by unfold Between at h; grind⟩
    | cons z zs =>
      have fromX : ∀ w ∈ z :: zs, Between x.y w.y y → ∃ q, poly (x :: z :: zs) q ∧ q.y = y := by
        intro w hw hb
        rcases between_split (b := z.y) hb with hb | hb
        · obtain ⟨q, hq, hqy⟩ := seg_exists_y hb
          exact ⟨q, (poly_cons_cons x z zs q).mpr (Or.inr (Or.inl hq)), hqy⟩
        · obtain ⟨q, hq, hqy⟩ := ih (List.mem_cons_self ..) hw hb
          exact ⟨q, (poly_cons_cons x z zs q).mpr (Or.inr (Or.inr hq)), hqy⟩
      rcases List.mem_cons.mp hu with hux | hu'
      · rcases List.mem_cons.mp hv with hvx | hv'
        · refine ⟨x, (poly_cons_cons x z zs x).mpr (Or.inl rfl), ?_⟩
          rw [hux, hvx] at h
          unfold Between at h
          grind
        · rw [hux] at h
          exact fromX v hv' h
      · rcases List.mem_cons.mp hv with hvx | hv'
        · rw [hvx] at h
          exact fromX u hu' (between_comm h)
        · obtain ⟨q, hq, hqy⟩ := ih hu' hv' h
          exact ⟨q, (poly_cons_cons x z zs q).mpr (Or.inr (Or.inr hq)), hqy⟩

end Inkproof.Scene
