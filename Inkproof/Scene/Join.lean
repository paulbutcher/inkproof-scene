/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Scene.Raster

namespace Inkproof.Scene

/-- How consecutive points of a run are joined. `stepAfter` holds each value until the next point's
x, then rises vertically; `stepBefore` rises at the first point's x, then runs level to the next.
`spline k` is the uniform Catmull-Rom curve, drawn as `k` straight pieces to the segment (at least
one). -/
inductive Join where
  | straight
  | stepBefore
  | stepAfter
  | spline (k : Nat)
  deriving DecidableEq, Repr

/-- The cubic Hermite curve from `a` to `b` with end tangents `ma` and `mb`, at parameter `t`. -/
def hermitePoint (a b ma mb : Pt) (t : Rat) : Pt :=
  let t2 := t * t
  let t3 := t2 * t
  let h00 := 2 * t3 - 3 * t2 + 1
  let h10 := t3 - 2 * t2 + t
  let h01 := 3 * t2 - 2 * t3
  let h11 := t3 - t2
  ⟨h00 * a.x + h10 * ma.x + h01 * b.x + h11 * mb.x,
   h00 * a.y + h10 * ma.y + h01 * b.y + h11 * mb.y⟩

/-- The points that replace the segment from `a` to `b`, `a` first and `b` not included; `p` is the
point before `a` and `n` the point after `b`, each being the end point itself where there is none. -/
def Join.emit : Join → Pt → Pt → Pt → Pt → List Pt
  | .straight, _, a, _, _ => [a]
  | .stepBefore, _, a, b, _ => [a, ⟨a.x, b.y⟩]
  | .stepAfter, _, a, b, _ => [a, ⟨b.x, a.y⟩]
  | .spline k, p, a, b, n =>
    (List.range (max k 1)).map fun (j : Nat) =>
      hermitePoint a b ⟨(b.x - p.x) / 2, (b.y - p.y) / 2⟩ ⟨(n.x - a.x) / 2, (n.y - a.y) / 2⟩
        ((j : Rat) / (max k 1 : Nat))

/-- The joined points from `a`, whose predecessor is `p`, through `rest`. -/
private def joinGo (j : Join) : Pt → Pt → List Pt → List Pt
  | _, a, [] => [a]
  | p, a, b :: rest => j.emit p a b (rest.headD b) ++ joinGo j a b rest

private def joinGoAcc (j : Join) : List Pt → Pt → Pt → List Pt → List Pt
  | acc, _, a, [] => (a :: acc).reverse
  | acc, p, a, b :: rest => joinGoAcc j ((j.emit p a b (rest.headD b)).reverse ++ acc) a b rest

private theorem joinGoAcc_eq (j : Join) (rest : List Pt) :
    ∀ (acc : List Pt) (p a : Pt), joinGoAcc j acc p a rest = acc.reverse ++ joinGo j p a rest := by
  induction rest with
  | nil => intro acc p a; simp [joinGoAcc, joinGo]
  | cons b rest ih => intro acc p a; simp [joinGoAcc, joinGo, ih]

/-- The compiled form of `joinGo`: an accumulator loop, which runs in constant stack. -/
private def joinGoFast (j : Join) (p a : Pt) (rest : List Pt) : List Pt := joinGoAcc j [] p a rest

@[csimp] private theorem joinGo_eq_fast : @joinGo = @joinGoFast := by
  funext j p a rest
  simp [joinGoFast, joinGoAcc_eq]

/-- A run with its consecutive points joined; an empty run stays empty. -/
def joinRun (j : Join) : List Pt → List Pt
  | [] => []
  | a :: rest => joinGo j a a rest

/-- Each run joined separately, so nothing is joined across a gap. -/
def joinRuns (j : Join) (rs : List (List Pt)) : List (List Pt) := rs.map (joinRun j)

theorem joinRun_straight (r : List Pt) : joinRun .straight r = r := by
  have : ∀ (rest : List Pt) (p a : Pt), joinGo .straight p a rest = a :: rest := by
    intro rest
    induction rest with
    | nil => intro p a; rfl
    | cons b rest ih => intro p a; simp [joinGo, Join.emit, ih]
  cases r with
  | nil => rfl
  | cons a rest => exact this rest a a

theorem length_joinRuns (j : Join) (rs : List (List Pt)) : (joinRuns j rs).length = rs.length := by
  simp [joinRuns]

theorem joinRuns_straight (rs : List (List Pt)) : joinRuns .straight rs = rs := by
  have : joinRun .straight = id := funext joinRun_straight
  simp [joinRuns, this]

private theorem joinGo_step_indep (j : Join) (hj : j = .stepAfter ∨ j = .stepBefore) (rest : List Pt)
    (p p' a : Pt) : joinGo j p a rest = joinGo j p' a rest := by
  cases rest <;> rcases hj with rfl | rfl <;> simp [joinGo, Join.emit]

/-- A step after the point holds its value to the next point's x, then rises there. -/
theorem joinRun_stepAfter (a b : Pt) (rest : List Pt) :
    joinRun .stepAfter (a :: b :: rest) = a :: ⟨b.x, a.y⟩ :: joinRun .stepAfter (b :: rest) := by
  simp only [joinRun, joinGo, Join.emit, List.cons_append, List.nil_append]
  rw [joinGo_step_indep _ (Or.inl rfl) rest a b b]

/-- A step before the point rises at the first point's x, then runs level to the next. -/
theorem joinRun_stepBefore (a b : Pt) (rest : List Pt) :
    joinRun .stepBefore (a :: b :: rest) = a :: ⟨a.x, b.y⟩ :: joinRun .stepBefore (b :: rest) := by
  simp only [joinRun, joinGo, Join.emit, List.cons_append, List.nil_append]
  rw [joinGo_step_indep _ (Or.inr rfl) rest a b b]

/-- A spline through two points is the Hermite curve with tangent half the chord at each end,
sampled at `j / k` for `j < k`, then the last point. -/
theorem joinRun_spline_pair (k : Nat) (a b : Pt) :
    joinRun (.spline k) [a, b] =
      (List.range (max k 1)).map (fun (j : Nat) =>
        hermitePoint a b ⟨(b.x - a.x) / 2, (b.y - a.y) / 2⟩ ⟨(b.x - a.x) / 2, (b.y - a.y) / 2⟩
          ((j : Rat) / (max k 1 : Nat))) ++ [b] := rfl

theorem hermitePoint_zero (a b ma mb : Pt) : hermitePoint a b ma mb 0 = a := by
  obtain ⟨x, y⟩ := a
  simp only [hermitePoint, Rat.sub_self, Rat.zero_add, Rat.zero_mul, Rat.add_zero, Rat.one_mul,
    Rat.mul_zero]

theorem hermitePoint_one (a b ma mb : Pt) : hermitePoint a b ma mb 1 = b := by
  obtain ⟨x, y⟩ := b
  simp only [hermitePoint]
  have h1 : ((2 : Rat) * (1 * 1 * 1) - 3 * (1 * 1) + 1) = 0 := by decide +kernel
  have h2 : ((1 : Rat) * 1 * 1 - 2 * (1 * 1) + 1) = 0 := by decide +kernel
  have h3 : ((3 : Rat) * (1 * 1) - 2 * (1 * 1 * 1)) = 1 := by decide +kernel
  have h4 : ((1 : Rat) * 1 * 1 - 1 * 1) = 0 := by decide +kernel
  rw [h1, h2, h3, h4]
  simp [Rat.zero_add, Rat.add_zero]

theorem emit_straight (p a b n : Pt) : Join.emit .straight p a b n = [a] := rfl

theorem emit_stepBefore (p a b n : Pt) : Join.emit .stepBefore p a b n = [a, ⟨a.x, b.y⟩] := rfl

theorem emit_stepAfter (p a b n : Pt) : Join.emit .stepAfter p a b n = [a, ⟨b.x, a.y⟩] := rfl

theorem emit_spline (k : Nat) (p a b n : Pt) :
    Join.emit (.spline k) p a b n =
      (List.range (max k 1)).map fun (j : Nat) =>
        hermitePoint a b ⟨(b.x - p.x) / 2, (b.y - p.y) / 2⟩ ⟨(n.x - a.x) / 2, (n.y - a.y) / 2⟩
          ((j : Rat) / (max k 1 : Nat)) := rfl

private theorem emit_head (j : Join) (p a b n : Pt) : a ∈ j.emit p a b n := by
  cases j with
  | straight => simp [Join.emit]
  | stepBefore => simp [Join.emit]
  | stepAfter => simp [Join.emit]
  | spline k =>
    simp only [Join.emit, List.mem_map]
    exact ⟨0, List.mem_range.mpr (by omega), by
      have h0 : ((0 : Nat) : Rat) / ((max k 1 : Nat) : Rat) = 0 := by
        rw [Rat.div_def]; simp
      rw [h0]; exact hermitePoint_zero a b _ _⟩

/-- The joined run passes through every point of the run, whichever the join; a spline in
particular interpolates its data. -/
theorem mem_joinRun (j : Join) (r : List Pt) {q : Pt} (h : q ∈ r) : q ∈ joinRun j r := by
  have key : ∀ (rest : List Pt) (p a : Pt), q = a ∨ q ∈ rest → q ∈ joinGo j p a rest := by
    intro rest
    induction rest with
    | nil => intro p a h; simpa [joinGo] using h
    | cons b rest ih =>
      intro p a h
      simp only [joinGo, List.mem_append]
      rcases h with rfl | h
      · exact Or.inl (emit_head j p q b _)
      · rcases List.mem_cons.mp h with rfl | h
        · exact Or.inr (ih a q (Or.inl rfl))
        · exact Or.inr (ih a b (Or.inr h))
  cases r with
  | nil => simp at h
  | cons a rest => exact key rest a a (List.mem_cons.mp h)

end Inkproof.Scene
