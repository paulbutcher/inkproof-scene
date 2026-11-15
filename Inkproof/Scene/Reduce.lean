/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Core.Proofs.Aggregate
import Inkproof.Scene.Poly

namespace Inkproof.Scene

open Inkproof.Core

/-- The pixel column class of an x-coordinate: `2 * x` at an integer `x`, and `2 * ⌊x⌋ + 1` strictly
between two integers. Each class is an interval (a single integer or an open unit interval), so
the points of a class cannot be told apart by which pixel columns their x-coordinate touches. -/
def xKey (x : Rat) : Int := if x.floor = x then 2 * x.floor else 2 * x.floor + 1

/-- Splits a list into maximal runs of adjacent points in the same x class. -/
def groupByKey : List Pt → List (List Pt)
  | [] => []
  | p :: rest =>
    match groupByKey rest with
    | (q :: g) :: gs => if xKey p.x = xKey q.x then (p :: q :: g) :: gs else [p] :: (q :: g) :: gs
    | _ => [[p]]

/-- What each point contributes to the aggregates of its run: first, last, lowest and highest. -/
def measure (p : Pt) : First Pt × Last Pt × Minimum Rat × Maximum Rat :=
  (⟨some p⟩, ⟨some p⟩, ⟨some p.y⟩, ⟨some p.y⟩)

/-- The first and last points of a run, joined through its lowest and highest values at the first
point's x. Whatever lies between the first and the last point of a run is replaced by the one
vertical stroke that covers the same y-extent; see `reduceRun_covers_iff`. Empty for an empty run. -/
def reduceRun (g : List Pt) : List Pt :=
  let m := Aggregate.fold measure g.toArray
  match m.1.get, m.2.1.get, m.2.2.1.get, m.2.2.2.get with
  | some f, some l, some lo, some hi => [f, ⟨f.x, lo⟩, ⟨f.x, hi⟩, l]
  | _, _, _, _ => []

/-- The first/min/max/last reduction of a polyline's points, one run per pixel column class. -/
def reducePoints (l : List Pt) : List Pt := (groupByKey l).flatMap reduceRun

theorem xKey_cases (x : Rat) :
    (x = x.floor ∧ xKey x = 2 * x.floor) ∨
    ((x.floor : Rat) < x ∧ x < x.floor + 1 ∧ xKey x = 2 * x.floor + 1) := by
  have h1 := Rat.floor_le x
  have h2 : x < (x.floor : Rat) + 1 := by
    have := Rat.lt_floor_add_one x
    push_cast at this
    exact this
  by_cases h : x.floor = x
  · left
    exact ⟨h.symm, by simp [xKey, h]⟩
  · right
    refine ⟨by grind, h2, by simp [xKey, h]⟩

theorem xKey_mono {x y : Rat} (h : x ≤ y) : xKey x ≤ xKey y := by
  have hf : x.floor ≤ y.floor := Rat.le_floor_iff.mpr (by have := Rat.floor_le x; grind)
  rcases xKey_cases x with ⟨hx, kx⟩ | ⟨hx1, hx2, kx⟩ <;>
  rcases xKey_cases y with ⟨hy, ky⟩ | ⟨hy1, hy2, ky⟩
  · omega
  · omega
  · have : x.floor ≠ y.floor := fun e => by rw [e] at hx1; grind
    omega
  · omega

/-- Points of one class cannot be told apart by the pixel columns they touch. -/
theorem xKey_col {x y : Rat} (c : Nat) (h : xKey x = xKey y) (hx : (c : Rat) ≤ x ∧ x ≤ c + 1) :
    (c : Rat) ≤ y ∧ y ≤ c + 1 := by
  rcases xKey_cases x with ⟨hx1, kx⟩ | ⟨hx1, hx2, kx⟩ <;>
  rcases xKey_cases y with ⟨hy1, ky⟩ | ⟨hy1, hy2, ky⟩
  · have : x.floor = y.floor := by omega
    rw [this] at hx1
    grind
  · omega
  · omega
  · have hfl : x.floor = y.floor := by omega
    rw [hfl] at hx1 hx2
    have a1 : c < y.floor + 1 := by
      refine Classical.byContradiction fun hc => ?_
      have : (y.floor : Rat) + 1 ≤ c := by exact_mod_cast (by omega : y.floor + 1 ≤ (c : Int))
      grind
    have a2 : y.floor < c + 1 := by
      refine Classical.byContradiction fun hc => ?_
      have : (c : Rat) + 1 ≤ y.floor := by exact_mod_cast (by omega : (c : Int) + 1 ≤ y.floor)
      grind
    have : (c : Int) = y.floor := by omega
    have : (c : Rat) = y.floor := by exact_mod_cast this
    grind

private theorem reduceRun_fold (G : List Pt) :
    Aggregate.fold measure G.toArray =
      (Aggregate.fold (fun p : Pt => First.mk (some p)) G.toArray,
       Aggregate.fold (fun p : Pt => Last.mk (some p)) G.toArray,
       Aggregate.fold (fun p : Pt => Minimum.mk (some p.y)) G.toArray,
       Aggregate.fold (fun p : Pt => Maximum.mk (some p.y)) G.toArray) := by
  unfold measure
  rw [Aggregate.fold_prod, Aggregate.fold_prod (fun p : Pt => Last.mk (some p)), Aggregate.fold_prod]

/-- What `reduceRun` computes: the first and last points of the run joined through its lowest and
highest values. -/
theorem reduceRun_spec {G : List Pt} (hG : G ≠ []) :
    ∃ f l lo hi, G.head? = some f ∧ G.getLast? = some l ∧
      reduceRun G = [f, ⟨f.x, lo⟩, ⟨f.x, hi⟩, l] ∧
      (∃ p ∈ G, p.y = lo) ∧ (∀ p ∈ G, lo ≤ p.y) ∧ (∃ p ∈ G, p.y = hi) ∧ ∀ p ∈ G, p.y ≤ hi := by
  obtain ⟨f, g, rfl⟩ : ∃ f g, G = f :: g := by cases G <;> simp_all
  have hfirst : (Aggregate.fold (fun p : Pt => First.mk (some p)) (f :: g).toArray).get = some f := by
    rw [First.fold_get]; simp
  have hlast : (Aggregate.fold (fun p : Pt => Last.mk (some p)) (f :: g).toArray).get =
      (f :: g).getLast? := by
    rw [Last.fold_get, List.getLast?_eq_head?_reverse]
    generalize (f :: g).reverse = r
    cases r <;> simp
  have hlast' : ∃ l, (f :: g).getLast? = some l := by
    cases h : (f :: g).getLast? with
    | none => simp [List.getLast?_eq_none_iff] at h
    | some l => exact ⟨l, rfl⟩
  have hmin : (Aggregate.fold (fun p : Pt => Minimum.mk (some p.y)) (f :: g).toArray).get ≠ none := by
    intro h
    have := (Minimum.fold_get_eq_none _ _).mp h f (by simp)
    simp at this
  have hmax : (Aggregate.fold (fun p : Pt => Maximum.mk (some p.y)) (f :: g).toArray).get ≠ none := by
    intro h
    have := (Maximum.fold_get_eq_none _ _).mp h f (by simp)
    simp at this
  obtain ⟨lo, hlo⟩ := Option.ne_none_iff_exists'.mp hmin
  obtain ⟨hi, hhi⟩ := Option.ne_none_iff_exists'.mp hmax
  obtain ⟨l, hl⟩ := hlast'
  have h1 := (Minimum.fold_get_eq_some _ _ lo).mp hlo
  have h2 := (Maximum.fold_get_eq_some _ _ hi).mp hhi
  refine ⟨f, l, lo, hi, rfl, hl, ?_, ?_, ?_, ?_, ?_⟩
  · unfold reduceRun
    rw [reduceRun_fold]
    simp only [hfirst, hlast, hl, hlo, hhi]
  · obtain ⟨x, hx, hxy⟩ := h1.1
    exact ⟨x, by simpa using hx, by simpa using hxy⟩
  · intro p hp
    exact h1.2 p (by simpa using hp) p.y rfl
  · obtain ⟨x, hx, hxy⟩ := h2.1
    exact ⟨x, by simpa using hx, by simpa using hxy⟩
  · intro p hp
    exact h2.2 p (by simpa using hp) p.y rfl

/-- `groupByKey` cuts a list into runs, losing and reordering nothing, each of one x class. -/
theorem groupByKey_spec (l : List Pt) :
    (groupByKey l).flatten = l ∧
    ∀ G ∈ groupByKey l, ∃ q g, G = q :: g ∧ ∀ p ∈ G, xKey p.x = xKey q.x := by
  induction l with
  | nil => simp [groupByKey]
  | cons p rest ih =>
    obtain ⟨hflat, hgroups⟩ := ih
    unfold groupByKey
    cases hg : groupByKey rest with
    | nil =>
      simp only [hg, List.flatten_nil] at hflat
      subst hflat
      simp
    | cons G gs =>
      rw [hg] at hflat hgroups
      obtain ⟨q, g, rfl, hq⟩ := hgroups _ (List.mem_cons_self ..)
      simp only [List.flatten_cons, List.cons_append] at hflat
      by_cases hk : xKey p.x = xKey q.x
      · simp only [hk, ite_true]
        refine ⟨by simp [hflat], ?_⟩
        intro H hH
        rcases List.mem_cons.mp hH with rfl | hH
        · refine ⟨p, q :: g, rfl, ?_⟩
          intro r hr
          rcases List.mem_cons.mp hr with rfl | hr
          · rfl
          · rw [hq r hr, hk]
        · exact hgroups H (List.mem_cons_of_mem _ hH)
      · simp only [hk, ite_false]
        refine ⟨by simp [hflat], ?_⟩
        intro H hH
        rcases List.mem_cons.mp hH with rfl | hH
        · exact ⟨p, [], rfl, by simp⟩
        · exact hgroups H hH

private structure Profile (k : Int) (lo hi : Rat) (L : List Pt) : Prop where
  ne : L ≠ []
  mem : ∀ p ∈ L, xKey p.x = k ∧ lo ≤ p.y ∧ p.y ≤ hi
  atLo : ∃ p ∈ L, p.y = lo
  atHi : ∃ p ∈ L, p.y = hi

private theorem between_lerp {a b t : Rat} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    Between a b (a + t * (b - a)) := by
  unfold Between
  rcases Rat.le_total (a := a) (b := b) with h | h
  · left
    have := Rat.mul_nonneg h0 (by grind : 0 ≤ b - a)
    have := Rat.mul_nonneg (by grind : 0 ≤ 1 - t) (by grind : 0 ≤ b - a)
    grind
  · right
    have := Rat.mul_nonneg h0 (by grind : 0 ≤ a - b)
    have := Rat.mul_nonneg (by grind : 0 ≤ 1 - t) (by grind : 0 ≤ a - b)
    grind

private theorem seg_between {a b q : Pt} (h : Region.seg a b q) :
    Between a.x b.x q.x ∧ Between a.y b.y q.y := by
  obtain ⟨t, h0, h1, hx, hy⟩ := h
  rw [hx, hy]
  exact ⟨between_lerp h0 h1, between_lerp h0 h1⟩

private theorem Profile.mem_poly {k : Int} {lo hi : Rat} {L : List Pt} (hP : Profile k lo hi L) {q : Pt}
    (h : poly L q) : xKey q.x = k ∧ lo ≤ q.y ∧ q.y ≤ hi := by
  obtain ⟨a, ha, b, hb, hs⟩ := poly_mem h
  obtain ⟨hxa, hya, hya'⟩ := hP.mem a ha
  obtain ⟨hxb, hyb, hyb'⟩ := hP.mem b hb
  obtain ⟨hx, hy⟩ := seg_between hs
  refine ⟨?_, ?_⟩
  · unfold Between at hx
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have := xKey_mono h1
      have := xKey_mono h2
      omega
    · have := xKey_mono h1
      have := xKey_mono h2
      omega
  · unfold Between at hy
    grind

private theorem Profile.covers {k : Int} {lo hi : Rat} {L : List Pt} (hP : Profile k lo hi L)
    (px : Pixel) :
    (poly L).Covers px ↔
      (∃ x, xKey x = k ∧ (px.col : Rat) ≤ x ∧ x ≤ px.col + 1) ∧
      ∃ y, (px.row : Rat) ≤ y ∧ y ≤ px.row + 1 ∧ lo ≤ y ∧ y ≤ hi := by
  constructor
  · rintro ⟨q, hq, h1, h2, h3, h4⟩
    obtain ⟨hk, hl, hh⟩ := hP.mem_poly hq
    exact ⟨⟨q.x, hk, h1, h2⟩, q.y, h3, h4, hl, hh⟩
  · rintro ⟨⟨x, hk, hc1, hc2⟩, y, hy1, hy2, hlo, hhi⟩
    obtain ⟨u, hu, hul⟩ := hP.atLo
    obtain ⟨v, hv, hvh⟩ := hP.atHi
    obtain ⟨q, hq, hqy⟩ := poly_exists_y hu hv (y := y) (Or.inl ⟨by grind, by grind⟩)
    obtain ⟨hqk, -, -⟩ := hP.mem_poly hq
    obtain ⟨c1, c2⟩ := xKey_col px.col (hk.trans hqk.symm) ⟨hc1, hc2⟩
    exact ⟨q, hq, c1, c2, by grind, by grind⟩

theorem Region.covers_congr {r s : Region} (h : ∀ p, r p ↔ s p) (px : Pixel) :
    r.Covers px ↔ s.Covers px :=
  ⟨fun ⟨p, hp, hc⟩ => ⟨p, (h p).mp hp, hc⟩, fun ⟨p, hp, hc⟩ => ⟨p, (h p).mpr hp, hc⟩⟩

theorem Region.covers_or {r s : Region} {px : Pixel} :
    Region.Covers (fun p => r p ∨ s p) px ↔ r.Covers px ∨ s.Covers px :=
  ⟨fun ⟨p, hp, hc⟩ => hp.elim (fun h => Or.inl ⟨p, h, hc⟩) (fun h => Or.inr ⟨p, h, hc⟩),
   fun h => h.elim (fun ⟨p, hp, hc⟩ => ⟨p, Or.inl hp, hc⟩) (fun ⟨p, hp, hc⟩ => ⟨p, Or.inr hp, hc⟩)⟩

private def PolyEq (G H : List Pt) : Prop :=
  G.head? = H.head? ∧ G.getLast? = H.getLast? ∧ G ≠ [] ∧ H ≠ [] ∧
    ∀ px, (poly G).Covers px ↔ (poly H).Covers px

private theorem covers_append_of_eq {G H X Y : List Pt} {a b : Pt}
    (hG : G.getLast? = some a) (hH : H.getLast? = some a) (hX : X.head? = some b)
    (hY : Y.head? = some b) (hGH : ∀ px, (poly G).Covers px ↔ (poly H).Covers px)
    (hXY : ∀ px, (poly X).Covers px ↔ (poly Y).Covers px) (px : Pixel) :
    (poly (G ++ X)).Covers px ↔ (poly (H ++ Y)).Covers px := by
  rw [Region.covers_congr (poly_append hG hX) px, Region.covers_congr (poly_append hH hY) px]
  simp only [Region.covers_or]
  rw [hGH px, hXY px]

private theorem reduceRun_polyEq {G : List Pt} {k : Int} (hG : G ≠ [])
    (hk : ∀ p ∈ G, xKey p.x = k) : PolyEq G (reduceRun G) := by
  obtain ⟨f, l, lo, hi, hf, hl, hr, ⟨u, hu, hul⟩, hlo, ⟨v, hv, hvh⟩, hhi⟩ := reduceRun_spec hG
  have hfm : f ∈ G := List.mem_of_mem_head? hf
  have hlm : l ∈ G := List.mem_of_getLast? hl
  have hP : Profile k lo hi G :=
    ⟨hG, fun p hp => ⟨hk p hp, hlo p hp, hhi p hp⟩, ⟨u, hu, hul⟩, ⟨v, hv, hvh⟩⟩
  have hQ : Profile k lo hi (reduceRun G) := by
    rw [hr]
    refine ⟨by simp, ?_, ⟨⟨f.x, lo⟩, by simp, rfl⟩, ⟨⟨f.x, hi⟩, by simp, rfl⟩⟩
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact ⟨hk _ hfm, hlo _ hfm, hhi _ hfm⟩
    · exact ⟨hk f hfm, Rat.le_refl, by have := hlo f hfm; have := hhi f hfm; grind⟩
    · exact ⟨hk f hfm, by have := hlo f hfm; have := hhi f hfm; grind, Rat.le_refl⟩
    · exact ⟨hk _ hlm, hlo _ hlm, hhi _ hlm⟩
  refine ⟨?_, ?_, hG, hQ.ne, fun px => (hP.covers px).trans (hQ.covers px).symm⟩
  · rw [hr, hf]; rfl
  · rw [hr, hl]; rfl

private theorem covers_reduce_flatten (Gs : List (List Pt))
    (h : ∀ G ∈ Gs, ∃ q g, G = q :: g ∧ ∀ p ∈ G, xKey p.x = xKey q.x) :
    Gs.flatten.head? = (Gs.map reduceRun).flatten.head? ∧
      ∀ px, (poly Gs.flatten).Covers px ↔ (poly (Gs.map reduceRun).flatten).Covers px := by
  induction Gs with
  | nil => exact ⟨rfl, fun _ => Iff.rfl⟩
  | cons G Gs ih =>
    obtain ⟨q, g, rfl, hk⟩ := h _ (List.mem_cons_self ..)
    obtain ⟨ihead, icov⟩ := ih fun H hH => h H (List.mem_cons_of_mem _ hH)
    obtain ⟨hhead, hlast, hGne, hHne, hcov⟩ := reduceRun_polyEq (G := q :: g) (by simp) hk
    obtain ⟨a, ha⟩ : ∃ a, (q :: g).getLast? = some a := by
      cases h : (q :: g).getLast? with
      | none => simp [List.getLast?_eq_none_iff] at h
      | some a => exact ⟨a, rfl⟩
    obtain ⟨f, hf⟩ : ∃ f, (reduceRun (q :: g)).head? = some f := by
      cases h : reduceRun (q :: g) with
      | nil => exact absurd h hHne
      | cons f _ => exact ⟨f, rfl⟩
    simp only [List.flatten_cons, List.map_cons]
    refine ⟨?_, ?_⟩
    · rw [List.head?_append, List.head?_append]
      simp [hhead, ihead]
    · cases hb : Gs.flatten.head? with
      | none =>
        have hX : Gs.flatten = [] := by simpa [List.head?_eq_none_iff] using hb
        have hY : (Gs.map reduceRun).flatten = [] := by
          rw [← List.head?_eq_none_iff, ← ihead, hb]
        rw [hX, hY]
        simpa using hcov
      | some b =>
        intro px
        exact covers_append_of_eq ha (hlast ▸ ha) hb (ihead ▸ hb) hcov icov px

/-- The first/min/max/last reduction of any polyline touches exactly the pixels the polyline does.
Neither monotonicity of the x-coordinates nor any property of the data is assumed: a run is
reduced only where its points share an x class, and the segments between runs are kept as they
are. (For x-monotone data every class is one run, which is what makes the reduction small.) -/
theorem reducePoints_covers (l : List Pt) (px : Pixel) :
    (poly (reducePoints l)).Covers px ↔ (poly l).Covers px := by
  obtain ⟨hflat, hgroups⟩ := groupByKey_spec l
  have h1 := (covers_reduce_flatten _ hgroups).2 px
  rw [hflat] at h1
  unfold reducePoints
  rw [List.flatMap_def]
  exact h1.symm

end Inkproof.Scene
