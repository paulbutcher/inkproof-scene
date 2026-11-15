/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Scene.Rasterize

namespace Inkproof.Scene

/-- One step of choosing the command on top at a pixel. -/
def winnerStep (cov : Command → Bool) (acc : Option Command) (c : Command) : Option Command :=
  if cov c then
    match acc with
    | some a => if a.layer ≤ c.layer then some c else acc
    | none => some c
  else acc

/-- The command that ends up on top at a pixel: the covering command of greatest layer, the last
in the list among those. -/
def winner (cov : Command → Bool) (cmds : List Command) : Option Command :=
  cmds.foldl (winnerStep cov) none

theorem list_rev_induction {α : Type} {P : List α → Prop} (h0 : P [])
    (hs : ∀ l x, P l → P (l ++ [x])) : ∀ l, P l := by
  intro l
  induction hn : l.length generalizing l with
  | zero => cases l <;> simp_all
  | succ n ih =>
    obtain ⟨L, b, hl⟩ := List.eq_nil_or_concat l |>.resolve_left (by rintro rfl; simp at hn)
    rw [List.concat_eq_append] at hl
    subst hl
    exact hs L b (ih L (by simpa using hn))

theorem winner_spec (cov : Command → Bool) (cmds : List Command) :
    (winner cov cmds = none ↔ ∀ c ∈ cmds, cov c = false) ∧
    ∀ c, winner cov cmds = some c → ∃ l1 l2, cmds = l1 ++ c :: l2 ∧ cov c = true ∧
      (∀ c' ∈ l1, cov c' = true → c'.layer ≤ c.layer) ∧
      (∀ c' ∈ l2, cov c' = true → c'.layer < c.layer) := by
  induction cmds using list_rev_induction with
  | h0 => simp [winner]
  | hs l x ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hw : winner cov (l ++ [x]) = winnerStep cov (winner cov l) x := by
      simp only [winner, List.foldl_append, List.foldl_cons, List.foldl_nil]
    by_cases hx : cov x = true
    · refine ⟨?_, ?_⟩
      · constructor
        · intro h
          rw [hw] at h
          simp only [winnerStep, hx, ite_true] at h
          cases hl : winner cov l with
          | none => rw [hl] at h; exact absurd h (by simp)
          | some a =>
            rw [hl] at h
            by_cases hla : a.layer ≤ x.layer <;> simp [hla] at h
        · intro h
          have := h x (by simp)
          simp [hx] at this
      · intro c h
        rw [hw] at h
        simp only [winnerStep, hx, ite_true] at h
        cases hl : winner cov l with
        | none =>
          rw [hl] at h
          have hn := ih1.1 hl
          simp only [Option.some.injEq] at h; subst h
          refine ⟨l, [], rfl, hx, fun c' hc' h => ?_, by simp⟩
          simp [hn c' hc'] at h
        | some a =>
          rw [hl] at h
          obtain ⟨l1, l2, e, ha, h1, h2⟩ := ih2 a hl
          by_cases hla : a.layer ≤ x.layer
          · simp only [hla, ite_true, Option.some.injEq] at h; subst h
            refine ⟨l, [], rfl, hx, fun c' hc' h => ?_, by simp⟩
            rw [e] at hc'
            simp only [List.mem_append, List.mem_cons] at hc'
            rcases hc' with hc' | rfl | hc'
            · have := h1 c' hc' h; grind
            · exact hla
            · have := h2 c' hc' h; grind
          · simp only [hla, ite_false, Option.some.injEq] at h; subst h
            refine ⟨l1, l2 ++ [x], by simp [e], ha, h1, fun c' hc' h => ?_⟩
            simp only [List.mem_append, List.mem_singleton] at hc'
            rcases hc' with hc' | rfl
            · exact h2 c' hc' h
            · grind
    · have hfalse : cov x = false := by simpa using hx
      have hst : winnerStep cov (winner cov l) x = winner cov l := by simp [winnerStep, hfalse]
      rw [hw, hst]
      refine ⟨?_, fun c h => ?_⟩
      · rw [ih1]
        constructor
        · intro h c hc
          simp only [List.mem_append, List.mem_singleton] at hc
          rcases hc with hc | rfl
          · exact h c hc
          · exact hfalse
        · intro h c hc; exact h c (by simp [hc])
      · obtain ⟨l1, l2, e, ha, h1, h2⟩ := ih2 c h
        refine ⟨l1, l2 ++ [x], by simp [e], ha, h1, fun c' hc' h => ?_⟩
        simp only [List.mem_append, List.mem_singleton] at hc'
        rcases hc' with hc' | rfl
        · exact h2 c' hc' h
        · rw [hfalse] at h; simp at h

/-- A rendered picture: `width * height` colours, row by row. -/
structure Image where
  width : Nat
  height : Nat
  pixels : Array Color
  size_eq : pixels.size = width * height

/-- The colour a pixel ends up with: that of the command on top there, or `bg` when no command
covers it. A covering command replaces the colour outright; blending is not part of the model. -/
def pixelColor (dl : DisplayList) (bg : Color) (px : Pixel) : Color :=
  match winner (fun c => c.shape.meetsB px.window) dl.toList with
  | some c => c.color
  | none => bg

/-- Render the display list on the grid, starting from `bg`. -/
def render (dl : DisplayList) (g : Grid) (bg : Color) : Image where
  width := g.w
  height := g.h
  pixels := Array.ofFn (n := g.w * g.h) fun i => pixelColor dl bg ⟨i.val % g.w, i.val / g.w⟩
  size_eq := Array.size_ofFn

/-- The colour at a column and row, if they are in the image. -/
def Image.get? (img : Image) (col row : Nat) : Option Color :=
  if col < img.width ∧ row < img.height then img.pixels[row * img.width + col]? else none

theorem render_get?_out (dl : DisplayList) (g : Grid) (bg : Color) {px : Pixel} (h : ¬ g.Has px) :
    (render dl g bg).get? px.col px.row = none := by
  unfold Image.get? render Grid.Has at *
  simp [h]

theorem render_get? (dl : DisplayList) (g : Grid) (bg : Color) {px : Pixel} (h : g.Has px) :
    (render dl g bg).get? px.col px.row = some (pixelColor dl bg px) := by
  unfold Image.get? render Grid.Has at *
  · have hw : 0 < g.w := by omega
    have hlt : px.row * g.w + px.col < g.w * g.h := by
      calc px.row * g.w + px.col < px.row * g.w + g.w := by omega
        _ = (px.row + 1) * g.w := by rw [Nat.add_mul, Nat.one_mul]
        _ ≤ g.h * g.w := Nat.mul_le_mul_right _ h.2
        _ = g.w * g.h := Nat.mul_comm _ _
    simp only [h, and_self, ite_true]
    rw [Array.getElem?_eq_getElem (by simpa using hlt)]
    simp only [Array.getElem_ofFn, Option.some.injEq]
    have e1 : (px.row * g.w + px.col) % g.w = px.col := by
      rw [Nat.mul_comm, Nat.mul_add_mod]; exact Nat.mod_eq_of_lt h.1
    have e2 : (px.row * g.w + px.col) / g.w = px.row := by
      rw [Nat.mul_comm, Nat.mul_add_div hw]; simp [Nat.div_eq_of_lt h.1]
    simp [e1, e2]

theorem pixelColor_of_not_covers {dl : DisplayList} {bg : Color} {px : Pixel}
    (h : ¬ dl.Covers px) : pixelColor dl bg px = bg := by
  unfold pixelColor
  cases hw : winner (fun c => c.shape.meetsB px.window) dl.toList with
  | none => rfl
  | some c =>
    obtain ⟨l1, l2, e, hc, _⟩ := (winner_spec (fun c => c.shape.meetsB px.window) dl.toList).2 c hw
    exact absurd ⟨c, Array.mem_toList_iff.1 (by rw [e]; simp), (Command.meetsB_iff c px).1 hc⟩ h

theorem pixelColor_of_covers {dl : DisplayList} {bg : Color} {px : Pixel} (h : dl.Covers px) :
    ∃ l1 c l2, dl.toList = l1 ++ c :: l2 ∧ c.Covers px ∧ pixelColor dl bg px = c.color ∧
      (∀ c' ∈ l1, c'.Covers px → c'.layer ≤ c.layer) ∧
      (∀ c' ∈ l2, c'.Covers px → c'.layer < c.layer) := by
  obtain ⟨c0, hc0, hcov⟩ := h
  have hs := winner_spec (fun c => c.shape.meetsB px.window) dl.toList
  cases hw : winner (fun c => c.shape.meetsB px.window) dl.toList with
  | none =>
    have := hs.1.1 hw c0 (Array.mem_toList_iff.2 hc0)
    simp [(Command.meetsB_iff c0 px).2 hcov] at this
  | some c =>
    obtain ⟨l1, l2, e, hc, h1, h2⟩ := hs.2 c hw
    refine ⟨l1, c, l2, e, (Command.meetsB_iff c px).1 hc, by simp [pixelColor, hw], fun c' hc' hk => ?_,
      fun c' hc' hk => ?_⟩
    · exact h1 c' hc' ((Command.meetsB_iff c' px).2 hk)
    · exact h2 c' hc' ((Command.meetsB_iff c' px).2 hk)

/-- Every pixel covered by a command shows the colour of a covering command on that command's layer
or above. -/
theorem pixelColor_covered {dl : DisplayList} {bg : Color} {px : Pixel} {c : Command}
    (hc : c ∈ dl) (h : c.Covers px) :
    ∃ c' ∈ dl, c'.Covers px ∧ pixelColor dl bg px = c'.color ∧ c.layer ≤ c'.layer := by
  obtain ⟨l1, c', l2, e, hc', hcol, h1, h2⟩ := pixelColor_of_covers (bg := bg) (px := px) ⟨c, hc, h⟩
  have hm : c ∈ l1 ++ c' :: l2 := by rw [← e]; exact Array.mem_toList_iff.2 hc
  refine ⟨c', Array.mem_toList_iff.1 (by rw [e]; simp), hc', hcol, ?_⟩
  simp only [List.mem_append, List.mem_cons] at hm
  rcases hm with hm | rfl | hm
  · exact h1 c hm h
  · exact Nat.le_refl _
  · exact Nat.le_of_lt (h2 c hm h)

/-- A one-sample spike between pixel centres still shows: a strip's lone value paints the pixel it
lies in, whatever the half-width, even zero. -/
theorem render_spike {dl : DisplayList} {bg : Color} {c : Command} (hc : c ∈ dl) {hw : Rat}
    {items : List (Item Pt)} (hs : c.shape = .strip hw items) {a : Pt} (ha : Item.val a ∈ items)
    {px : Pixel} (hp : px.Contains a) :
    ∃ c' ∈ dl, c'.Covers px ∧ pixelColor dl bg px = c'.color ∧ c.layer ≤ c'.layer :=
  pixelColor_covered hc (Command.covers_of_mem (by rw [hs]; exact Shape.strip_region_of_val ha) hp)

end Inkproof.Scene
