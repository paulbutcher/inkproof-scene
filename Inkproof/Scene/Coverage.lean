/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Scene.DisplayList

namespace Inkproof.Scene

/-- A primitive that has a point in a pixel's square covers the pixel. -/
theorem Region.covers_of_mem {r : Region} {px : Pixel} {p : Pt} (h : r p) (hp : px.Contains p) :
    r.Covers px := ⟨p, h, hp⟩

/-- A pixel covered by a region is covered by anything that occupies at least as much. -/
theorem Region.Covers.mono {a b : Region} (hab : a.Sub b) {px : Pixel} (h : a.Covers px) :
    b.Covers px :=
  match h with | ⟨p, hp, hc⟩ => ⟨p, hab p hp, hc⟩

/-- Along one axis of extent `n`, every coordinate in `[0, n]` lies in the closed unit cell of some
index below `n`. -/
theorem exists_cell (x : Rat) (n : Nat) (h0 : 0 ≤ x) (h1 : x ≤ n) (hn : 0 < n) :
    ∃ c : Nat, c < n ∧ (c : Rat) ≤ x ∧ x ≤ c + 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hf := Rat.floor_le x
  have hl := Rat.lt_floor_add_one x
  have hnn : 0 ≤ x.floor := Rat.le_floor_iff.mpr (by exact_mod_cast h0)
  obtain ⟨k, hk⟩ : ∃ k : Nat, x.floor = k := ⟨x.floor.toNat, by omega⟩
  rw [hk] at hf hl
  push_cast at hf hl h1 ⊢
  by_cases hkn : k ≤ m
  · exact ⟨k, by omega, hf, by grind⟩
  · have : (m : Rat) + 1 ≤ k := by exact_mod_cast (by omega : m + 1 ≤ k)
    exact ⟨m, by omega, by grind, by grind⟩

/-- Every point of the grid's extent lies in some pixel of the grid. -/
theorem Grid.exists_pixel (g : Grid) (hw : 0 < g.w) (hh : 0 < g.h) {p : Pt} (hp : g.Holds p) :
    ∃ px, g.Has px ∧ px.Contains p := by
  obtain ⟨hx0, hx1, hy0, hy1⟩ := hp
  obtain ⟨c, hc, hc0, hc1⟩ := exists_cell p.x g.w hx0 hx1 hw
  obtain ⟨r, hr, hr0, hr1⟩ := exists_cell p.y g.h hy0 hy1 hh
  exact ⟨⟨c, r⟩, ⟨hc, hr⟩, hc0, hc1, hr0, hr1⟩

/-- A primitive with a point inside the grid covers a pixel of the grid: a feature of positive or
zero extent is never dropped. -/
theorem Region.exists_covered {r : Region} {g : Grid} (hw : 0 < g.w) (hh : 0 < g.h) {p : Pt}
    (h : r p) (hp : g.Holds p) : ∃ px, g.Has px ∧ r.Covers px :=
  match g.exists_pixel hw hh hp with
  | ⟨px, hpx, hc⟩ => ⟨px, hpx, Region.covers_of_mem h hc⟩

theorem mul_self_nonneg' (r : Rat) : 0 ≤ r * r := by
  have := Lean.Grind.OrderedRing.sq_nonneg (a := r)
  rwa [Lean.Grind.Semiring.pow_two] at this

/-- Thickening only adds points. -/
theorem Region.sub_thicken (r : Rat) (a : Region) : a.Sub (a.thicken r) := fun p hp =>
  ⟨p, hp, by simp only [Region.disc, Rat.sub_self, Rat.zero_mul, Rat.add_zero]; exact mul_self_nonneg' r⟩

namespace Item

variable {α : Type} {single : α → Region} {join : α → α → Region}

/-- Each value of a strip occupies its own region, so a value with no neighbour is still drawn. -/
theorem single_sub_chain {items : List (Item α)} {a : α} (h : Item.val a ∈ items) :
    (single a).Sub (chain single join items) := by
  induction items with
  | nil => simp at h
  | cons x rest ih =>
    intro p hp
    rcases List.mem_cons.mp h with rfl | hm
    · exact Or.inl hp
    · cases x with
      | gap => exact ih hm p hp
      | val b => exact Or.inr (Or.inr (ih hm p hp))

/-- A gap separates a strip: nothing joins the values on either side of it. -/
theorem chain_append_gap (xs ys : List (Item α)) (p : Pt) :
    chain single join (xs ++ .gap :: ys) p ↔ chain single join xs p ∨ chain single join ys p := by
  induction xs with
  | nil => simp [chain]
  | cons x rest ih =>
    cases x with
    | gap => simpa [chain] using ih
    | val a =>
      cases rest with
      | nil => simp [chain]
      | cons y rest' =>
        cases y <;> simp_all [chain, or_assoc]

end Item

/-- A strip's value is occupied by the strip however thin the strip, so a one-sample spike between
pixel centres is covered, by the rule that a primitive covers every pixel it touches. -/
theorem Shape.strip_region_of_val {hw : Rat} {items : List (Item Pt)} {a : Pt}
    (h : Item.val a ∈ items) : (Shape.strip hw items).region a :=
  Region.sub_thicken hw _ a (Item.single_sub_chain h a rfl)

/-- A command's own shape covers every pixel it touches: the command covers any pixel that a point
of its shape lies in. -/
theorem Command.covers_of_mem {c : Command} {px : Pixel} {p : Pt} (h : c.shape.region p)
    (hp : px.Contains p) : c.Covers px := Region.covers_of_mem h hp

/-- A display list with a command with a point inside the grid covers a pixel of the grid. -/
theorem DisplayList.exists_covered {dl : DisplayList} {g : Grid} (hw : 0 < g.w) (hh : 0 < g.h)
    {c : Command} (hc : c ∈ dl) {p : Pt} (h : c.shape.region p) (hp : g.Holds p) :
    ∃ px, g.Has px ∧ dl.Covers px :=
  match Region.exists_covered hw hh h hp with
  | ⟨px, hpx, hcov⟩ => ⟨px, hpx, c, hc, hcov⟩

/-- Coverage is monotone: adding commands never uncovers a pixel. -/
theorem DisplayList.Covers.mono {a b : DisplayList} (hab : ∀ c ∈ a, c ∈ b) {px : Pixel}
    (h : a.Covers px) : b.Covers px :=
  match h with | ⟨c, hc, hcov⟩ => ⟨c, hab c hc, hcov⟩

/-- The pixels covered by the union of two display lists are those covered by either. -/
theorem DisplayList.covers_append {a b : DisplayList} {px : Pixel} :
    (a ++ b).Covers px ↔ a.Covers px ∨ b.Covers px := by
  constructor
  · rintro ⟨c, hc, hcov⟩
    rcases Array.mem_append.mp hc with h | h
    · exact Or.inl ⟨c, h, hcov⟩
    · exact Or.inr ⟨c, h, hcov⟩
  · rintro (⟨c, hc, hcov⟩ | ⟨c, hc, hcov⟩)
    · exact ⟨c, Array.mem_append_left _ hc, hcov⟩
    · exact ⟨c, Array.mem_append_right _ hc, hcov⟩

end Inkproof.Scene
