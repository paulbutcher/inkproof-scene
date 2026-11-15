/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Scene.Render

namespace Inkproof.Scene

/-- The commands of a display list in the order they are painted: ascending layer, list order
within a layer. -/
def DisplayList.paintOrder (dl : DisplayList) : List Command :=
  dl.toList.mergeSort (fun a b => decide (a.layer ≤ b.layer))

private theorem layer_trans (a b c : Command) :
    decide (a.layer ≤ b.layer) = true → decide (b.layer ≤ c.layer) = true →
    decide (a.layer ≤ c.layer) = true := by
  simpa using Nat.le_trans

private theorem layer_total (a b : Command) :
    (decide (a.layer ≤ b.layer) || decide (b.layer ≤ a.layer)) = true := by
  simpa using Nat.le_total _ _

theorem DisplayList.paintOrder_perm (dl : DisplayList) : dl.paintOrder.Perm dl.toList :=
  List.mergeSort_perm _ _

theorem DisplayList.paintOrder_sorted (dl : DisplayList) :
    dl.paintOrder.Pairwise (fun a b => a.layer ≤ b.layer) := by
  have := List.pairwise_mergeSort layer_trans layer_total dl.toList
  exact this.imp (by simp)

/-- Any selection of the commands whose layers are pairwise ordered keeps its list order in the
paint order. -/
theorem DisplayList.paintOrder_filter (dl : DisplayList) (q : Command → Bool)
    (h : (dl.toList.filter q).Pairwise (fun a b => a.layer ≤ b.layer)) :
    dl.paintOrder.filter q = dl.toList.filter q := by
  have hsub : List.Sublist (dl.toList.filter q) dl.paintOrder :=
    List.sublist_mergeSort layer_trans layer_total (h.imp (by simp)) List.filter_sublist
  have h2 := hsub.filter q
  rw [List.filter_eq_self.2 (by simp)] at h2
  exact (h2.eq_of_length ((dl.paintOrder_perm.filter q).length_eq.trans rfl |>.symm)).symm

private theorem paintOrder_filter_layer (dl : DisplayList) (k : Nat) (q : Command → Bool)
    (hq : ∀ c, q c = true → c.layer = k) : dl.paintOrder.filter q = dl.toList.filter q := by
  apply dl.paintOrder_filter
  refine List.pairwise_of_forall_mem_list fun a ha b hb => ?_
  have := hq a (List.mem_filter.1 ha).2
  have := hq b (List.mem_filter.1 hb).2
  omega

/-- Within a layer the paint order keeps list order. -/
theorem DisplayList.paintOrder_layer (dl : DisplayList) (k : Nat) :
    dl.paintOrder.filter (fun c => c.layer == k) = dl.toList.filter (fun c => c.layer == k) :=
  paintOrder_filter_layer dl k _ (by simp)

/-- The colour at a pixel when commands are painted in turn, each covering command replacing what
is there. -/
def paintOver (cov : Command → Bool) (bg : Color) (cmds : List Command) : Color :=
  cmds.foldl (fun acc c => if cov c then c.color else acc) bg

theorem paintOver_eq (cov : Command → Bool) (bg : Color) (cmds : List Command) :
    paintOver cov bg cmds = match (cmds.filter cov).getLast? with
      | some c => c.color
      | none => bg := by
  induction cmds using list_rev_induction with
  | h0 => simp [paintOver]
  | hs l x ih =>
    simp only [paintOver, List.foldl_append, List.foldl_cons, List.foldl_nil] at ih ⊢
    rw [ih, List.filter_append]
    by_cases hx : cov x = true <;> simp [hx]

private theorem getLast?_of_filter_layer (F : List Command) (L : Nat) (w : Command)
    (hs : F.Pairwise (fun a b => a.layer ≤ b.layer)) (hF : ∀ c ∈ F, c.layer ≤ L)
    (hw : (F.filter (fun c => c.layer == L)).getLast? = some w) : F.getLast? = some w := by
  rcases List.eq_nil_or_concat F with rfl | ⟨F', m, rfl⟩
  · simp at hw
  · rw [List.concat_eq_append] at hs hF hw ⊢
    rw [List.pairwise_append] at hs
    by_cases hm : m.layer = L
    · simp [List.filter_append, hm] at hw
      simp [hw]
    · exfalso
      have hlt : m.layer < L := by have := hF m (by simp); omega
      have : F'.filter (fun c => c.layer == L) = [] := by
        rw [List.filter_eq_nil_iff]
        intro a ha
        have := hs.2.2 a ha m (by simp)
        simp; omega
      simp [List.filter_append, this, hm] at hw

/-- Painting the commands in paint order, each covering command replacing what is there, gives the
colour the raster model assigns. -/
theorem pixelColor_eq_paintOver (dl : DisplayList) (bg : Color) (px : Pixel) :
    pixelColor dl bg px = paintOver (fun c => c.shape.meetsB px.window) bg dl.paintOrder := by
  rw [paintOver_eq]
  have hs := winner_spec (fun c => c.shape.meetsB px.window) dl.toList
  unfold pixelColor
  cases hw : winner (fun c => c.shape.meetsB px.window) dl.toList with
  | none =>
    have h1 := hs.1.1 hw
    have : dl.paintOrder.filter (fun c => c.shape.meetsB px.window) = [] := by
      rw [List.filter_eq_nil_iff]
      intro a ha
      simpa using h1 a (dl.paintOrder_perm.subset ha)
    simp [this]
  | some w =>
    obtain ⟨l1, l2, e, hc, h1, h2⟩ := hs.2 w hw
    obtain ⟨F, hF⟩ : ∃ F, F = dl.paintOrder.filter (fun c => c.shape.meetsB px.window) := ⟨_, rfl⟩
    rw [← hF]
    have hmemF : ∀ c ∈ F, c ∈ dl.toList ∧ c.shape.meetsB px.window = true := fun c hc' => by
      rw [hF] at hc'
      exact ⟨dl.paintOrder_perm.subset (List.mem_filter.1 hc').1, by simpa using (List.mem_filter.1 hc').2⟩
    have hle : ∀ c ∈ F, c.layer ≤ w.layer := by
      intro c hc'
      obtain ⟨hm, hcov⟩ := hmemF c hc'
      rw [e] at hm
      simp only [List.mem_append, List.mem_cons] at hm
      rcases hm with hm | rfl | hm
      · exact h1 c hm hcov
      · exact Nat.le_refl _
      · exact Nat.le_of_lt (h2 c hm hcov)
    have hsorted : F.Pairwise (fun a b => a.layer ≤ b.layer) :=
      (by rw [hF]; exact dl.paintOrder_sorted.filter _)
    have hq : dl.paintOrder.filter (fun c => c.shape.meetsB px.window && c.layer == w.layer) =
        dl.toList.filter (fun c => c.shape.meetsB px.window && c.layer == w.layer) :=
      paintOrder_filter_layer dl w.layer _ (by simp)
    have hFq : F.filter (fun c => c.layer == w.layer) =
        dl.paintOrder.filter (fun c => c.shape.meetsB px.window && c.layer == w.layer) := by
      rw [hF, List.filter_filter]
      simp only [Bool.and_comm]
    have hl2 : l2.filter (fun c => c.shape.meetsB px.window && c.layer == w.layer) = [] := by
      rw [List.filter_eq_nil_iff]
      intro a ha
      have := h2 a ha
      by_cases hcv : a.shape.meetsB px.window = true
      · have := this hcv; simp; omega
      · simp [hcv]
    have hlast : (F.filter (fun c => c.layer == w.layer)).getLast? = some w := by
      rw [hFq, hq, e, List.filter_append, List.filter_cons_of_pos (by simp [hc]), hl2]
      simp
    rw [getLast?_of_filter_layer F w.layer w hsorted hle hlast]

end Inkproof.Scene
