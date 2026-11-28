/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Scene.Raster

namespace Inkproof.Scene

/-- A colour, as 8-bit red, green, blue and alpha. -/
structure Color where
  r : UInt8
  g : UInt8
  b : UInt8
  a : UInt8
  deriving DecidableEq, Repr

/-- Opaque black. -/
def Color.black : Color := ⟨0, 0, 0, 255⟩

/-- A colour at a position along a gradient's axis, in grid coordinates. -/
structure Stop where
  pos : Rat
  color : Color
  deriving DecidableEq, Repr

/-- The coordinate a gradient varies along. -/
inductive GradientAxis where
  | x
  | y
  deriving DecidableEq, Repr

/-- The channel between `a` and `b` at fraction `w` of the way, rounded half up. -/
def lerpChannel (a b : UInt8) (w : Rat) : UInt8 :=
  UInt8.ofNat (((a.toNat : Rat) + ((b.toNat : Rat) - a.toNat) * w + 1 / 2).floor.toNat)

/-- The colour a fraction `w` of the way from `a` to `b`, each channel blended and rounded alone. -/
def Color.lerp (a b : Color) (w : Rat) : Color :=
  ⟨lerpChannel a.r b.r w, lerpChannel a.g b.g w, lerpChannel a.b b.b w, lerpChannel a.a b.a w⟩

/-- `c` with its alpha multiplied by `f`, clamped to the range 0 to 1 and rounded half up; the colour channels are unchanged. -/
def Color.scaleAlpha (c : Color) (f : Rat) : Color :=
  { c with a := lerpChannel 0 c.a (max 0 (min 1 f)) }

theorem Color.scaleAlpha_rgb (c : Color) (f : Rat) :
    (c.scaleAlpha f).r = c.r ∧ (c.scaleAlpha f).g = c.g ∧ (c.scaleAlpha f).b = c.b := by
  simp [Color.scaleAlpha]

theorem Color.scaleAlpha_a (c : Color) (f : Rat) :
    (c.scaleAlpha f).a
      = UInt8.ofNat (((c.a.toNat : Rat) * max 0 (min 1 f) + 1 / 2).floor.toNat) := by
  simp [Color.scaleAlpha, lerpChannel, Rat.zero_add, Rat.sub_eq_add_neg, Rat.neg_zero, Rat.add_zero]

/-- The channel of `s` painted over `d`, given the alpha `sa` of `s`, the alpha `da` of `d` and `k`,
255 times the combined alpha: the exact quotient, rounded half up. A fully transparent result has
no colour. -/
def overChannel (sa da k : Nat) (cs cd : UInt8) : UInt8 :=
  if k = 0 then 0
  else UInt8.ofNat ((2 * (cs.toNat * sa * 255 + cd.toNat * da * (255 - sa)) + k) / (2 * k))

/-- `s` painted over `d`, both with straight (not premultiplied) alpha: the source-over composite,
with alpha `sa + da * (1 - sa)` and each colour channel the alpha-weighted mean of the two, each
channel rounded half up once. -/
def Color.over (s d : Color) : Color :=
  let sa := s.a.toNat
  let da := d.a.toNat
  let k := 255 * sa + da * (255 - sa)
  ⟨overChannel sa da k s.r d.r, overChannel sa da k s.g d.g, overChannel sa da k s.b d.b,
    UInt8.ofNat ((k + 127) / 255)⟩

private theorem overChannel_opaque (da : Nat) (cs cd : UInt8) :
    overChannel 255 da (255 * 255 + da * (255 - 255)) cs cd = cs := by
  have h := cs.toNat_lt
  simp only [overChannel, Nat.sub_self, Nat.mul_zero, Nat.add_zero, Nat.mul_zero]
  split
  · omega
  have : (2 * (cs.toNat * 255 * 255) + 255 * 255) / (2 * (255 * 255)) = cs.toNat := by omega
  rw [this]; simp

/-- A fully opaque source hides what is under it. -/
theorem Color.over_opaque {s : Color} (h : s.a = 255) (d : Color) : s.over d = s := by
  have : s.a.toNat = 255 := by simp [h]
  simp only [Color.over, this, overChannel_opaque]
  cases s; simp_all

/-- The alpha of `s` painted over `d` is `sa + da * (1 - sa)` in 8-bit units, rounded half up. -/
theorem Color.over_a_toNat (s d : Color) :
    (s.over d).a.toNat = (255 * s.a.toNat + d.a.toNat * (255 - s.a.toNat) + 127) / 255 := by
  have hs := s.a.toNat_lt
  have hd := d.a.toNat_lt
  simp only [Color.over, UInt8.toNat_ofNat']
  apply Nat.mod_eq_of_lt
  have : d.a.toNat * (255 - s.a.toNat) ≤ 255 * (255 - s.a.toNat) :=
    Nat.mul_le_mul_right _ (by omega)
  omega

/-- A colour channel of `s` painted over `d` is the alpha-weighted mean of the two channels,
rounded half up, or zero when the result has no alpha. -/
theorem overChannel_toNat (sa da : Nat) (cs cd : UInt8) :
    (overChannel sa da (255 * sa + da * (255 - sa)) cs cd).toNat =
      if 255 * sa + da * (255 - sa) = 0 then 0
      else (2 * (cs.toNat * sa * 255 + cd.toNat * da * (255 - sa)) + (255 * sa + da * (255 - sa))) /
        (2 * (255 * sa + da * (255 - sa))) := by
  have hc := cs.toNat_lt
  have hd := cd.toNat_lt
  unfold overChannel
  split
  · simp_all
  · rename_i hk
    simp only [UInt8.toNat_ofNat']
    apply Nat.mod_eq_of_lt
    rw [Nat.div_lt_iff_lt_mul (by omega)]
    have h1 : cs.toNat * sa * 255 ≤ 255 * (sa * 255) := by
      have : cs.toNat * sa ≤ 255 * sa := Nat.mul_le_mul_right _ (by omega)
      calc cs.toNat * sa * 255 ≤ 255 * sa * 255 := Nat.mul_le_mul_right _ this
        _ = 255 * (sa * 255) := by simp only [Nat.mul_assoc]
    have h2 : cd.toNat * da * (255 - sa) ≤ 255 * (da * (255 - sa)) := by
      have : cd.toNat * da ≤ 255 * da := Nat.mul_le_mul_right _ (by omega)
      calc cd.toNat * da * (255 - sa) ≤ 255 * da * (255 - sa) := Nat.mul_le_mul_right _ this
        _ = 255 * (da * (255 - sa)) := by simp only [Nat.mul_assoc]
    have : 255 * sa = sa * 255 := Nat.mul_comm _ _
    omega

/-- The colour at `t` of the stops that follow `s`: the first stop's colour up to it, the last
stop's colour after it, and between two stops a blend in proportion to the distance along. -/
def evalStops (s : Stop) : List Stop → Rat → Color
  | [], _ => s.color
  | n :: rest, t =>
    if t ≤ s.pos then s.color
    else if t ≤ n.pos then s.color.lerp n.color ((t - s.pos) / (n.pos - s.pos))
    else evalStops n rest t

/-- The colour at `t` of the stops that follow `s`, each stop's colour holding until the next stop's
position, where the colour changes at once. -/
def evalSteps (s : Stop) : List Stop → Rat → Color
  | [], _ => s.color
  | n :: rest, t => if n.pos ≤ t then evalSteps n rest t else s.color

/-- What fills a command's shape: one colour everywhere, or a colour that varies along an axis
between stops, given by position in ascending order. -/
inductive Shading where
  | flat (c : Color)
  /-- The colour of a pixel is evaluated at its centre: before the first stop and after the last
  it is that stop's colour. -/
  | gradient (axis : GradientAxis) (first : Stop) (rest : List Stop)
  /-- As `gradient`, but a stop's colour holds up to the next stop's position, where it changes at
  once to the next stop's colour (`evalSteps`). -/
  | steps (axis : GradientAxis) (first : Stop) (rest : List Stop)
  deriving DecidableEq, Repr

instance : Coe Color Shading := ⟨Shading.flat⟩

/-- The colour a shading gives the pixel, evaluated at the pixel's centre. -/
def Shading.at : Shading → Pixel → Color
  | .flat c, _ => c
  | .gradient .x s rest, px => evalStops s rest ((px.col : Rat) + 1 / 2)
  | .gradient .y s rest, px => evalStops s rest ((px.row : Rat) + 1 / 2)
  | .steps .x s rest, px => evalSteps s rest ((px.col : Rat) + 1 / 2)
  | .steps .y s rest, px => evalSteps s rest ((px.row : Rat) + 1 / 2)

theorem Shading.at_flat (c : Color) (px : Pixel) : (Shading.flat c).at px = c := rfl

theorem Shading.at_gradient_x (s : Stop) (rest : List Stop) (px : Pixel) :
    (Shading.gradient .x s rest).at px = evalStops s rest ((px.col : Rat) + 1 / 2) := rfl

theorem Shading.at_gradient_y (s : Stop) (rest : List Stop) (px : Pixel) :
    (Shading.gradient .y s rest).at px = evalStops s rest ((px.row : Rat) + 1 / 2) := rfl

theorem Shading.at_steps_x (s : Stop) (rest : List Stop) (px : Pixel) :
    (Shading.steps .x s rest).at px = evalSteps s rest ((px.col : Rat) + 1 / 2) := rfl

theorem Shading.at_steps_y (s : Stop) (rest : List Stop) (px : Pixel) :
    (Shading.steps .y s rest).at px = evalSteps s rest ((px.row : Rat) + 1 / 2) := rfl

/-- Between two adjacent stops, the blend of their colours in proportion to the distance along. -/
theorem evalStops_between (s n : Stop) (rest : List Stop) {t : Rat} (h0 : s.pos < t)
    (h1 : t ≤ n.pos) :
    evalStops s (n :: rest) t = s.color.lerp n.color ((t - s.pos) / (n.pos - s.pos)) := by
  have : ¬ t ≤ s.pos := by grind
  simp [evalStops, this, h1]

private theorem floor_toNat_eq {x : Rat} {n : Nat} (h1 : (n : Rat) ≤ x) (h2 : x < n + 1) :
    x.floor.toNat = n := by
  have a : (n : Int) ≤ x.floor := Rat.le_floor_iff.2 (by exact_mod_cast h1)
  have b : x.floor < (n : Int) + 1 := Rat.floor_lt_iff.2 (by exact_mod_cast h2)
  omega

theorem lerpChannel_zero (a b : UInt8) : lerpChannel a b 0 = a := by
  unfold lerpChannel
  rw [floor_toNat_eq (n := a.toNat) (by grind) (by grind)]
  simp

theorem lerpChannel_one (a b : UInt8) : lerpChannel a b 1 = b := by
  unfold lerpChannel
  rw [floor_toNat_eq (n := b.toNat) (by grind) (by grind)]
  simp

theorem Color.lerp_zero (a b : Color) : a.lerp b 0 = a := by
  simp [Color.lerp, lerpChannel_zero]

theorem Color.lerp_one (a b : Color) : a.lerp b 1 = b := by
  simp [Color.lerp, lerpChannel_one]

theorem lerpChannel_toNat (a b : UInt8) {w : Rat} (h0 : 0 ≤ w) (h1 : w ≤ 1) :
    (lerpChannel a b w).toNat =
      ((a.toNat : Rat) + ((b.toNat : Rat) - a.toNat) * w + 1 / 2).floor.toNat := by
  have ha : (a.toNat : Rat) ≤ 255 := by have := a.toNat_lt; exact_mod_cast (by omega : a.toNat ≤ 255)
  have hb : (b.toNat : Rat) ≤ 255 := by have := b.toNat_lt; exact_mod_cast (by omega : b.toNat ≤ 255)
  have a0 : (0 : Rat) ≤ a.toNat := by exact_mod_cast Nat.zero_le _
  have b0 : (0 : Rat) ≤ b.toNat := by exact_mod_cast Nat.zero_le _
  have p1 : 0 ≤ (a.toNat : Rat) * (1 - w) := Rat.mul_nonneg a0 (by grind)
  have p2 : 0 ≤ (b.toNat : Rat) * w := Rat.mul_nonneg b0 h0
  have p3 : (a.toNat : Rat) * (1 - w) ≤ 255 * (1 - w) := Rat.mul_le_mul_of_nonneg_right ha (by grind)
  have p4 : (b.toNat : Rat) * w ≤ 255 * w := Rat.mul_le_mul_of_nonneg_right hb h0
  have e : (a.toNat : Rat) + ((b.toNat : Rat) - a.toNat) * w =
      (a.toNat : Rat) * (1 - w) + (b.toNat : Rat) * w := by grind
  have l1 : (0 : Int) ≤ ((a.toNat : Rat) + ((b.toNat : Rat) - a.toNat) * w + 1 / 2).floor := by
    rw [Rat.le_floor_iff]; grind
  have l2 : ((a.toNat : Rat) + ((b.toNat : Rat) - a.toNat) * w + 1 / 2).floor < 256 := by
    rw [Rat.floor_lt_iff]; grind
  simp only [lerpChannel, UInt8.toNat_ofNat']
  omega

/-- Blending from `a` up to `b` never leaves them, and rises with the fraction along. -/
theorem lerpChannel_mono (a b : UInt8) (hab : a ≤ b) {w v : Rat} (h0 : 0 ≤ w) (hwv : w ≤ v)
    (h1 : v ≤ 1) : (lerpChannel a b w).toNat ≤ (lerpChannel a b v).toNat := by
  rw [lerpChannel_toNat a b h0 (by grind), lerpChannel_toNat a b (by grind) h1]
  have hab' : (a.toNat : Rat) ≤ b.toNat := by exact_mod_cast UInt8.le_iff_toNat_le.1 hab
  have hm : ((b.toNat : Rat) - a.toNat) * w ≤ ((b.toNat : Rat) - a.toNat) * v :=
    Rat.mul_le_mul_of_nonneg_left hwv (by grind)
  have := Rat.floor_monotone (a := (a.toNat : Rat) + ((b.toNat : Rat) - a.toNat) * w + 1 / 2)
    (b := (a.toNat : Rat) + ((b.toNat : Rat) - a.toNat) * v + 1 / 2) (by grind)
  omega

private theorem lerp_div_self {a b : Rat} (h : a < b) : (b - a) / (b - a) = 1 :=
  by rw [Rat.div_def]; exact Rat.mul_inv_cancel _ (by grind)

/-- Stops in ascending order give their own colour at their own position. -/
theorem evalStops_at (s : Stop) (rest : List Stop) (hs : (s :: rest).Pairwise (·.pos < ·.pos)) :
    ∀ n ∈ s :: rest, evalStops s rest n.pos = n.color := by
  induction rest generalizing s with
  | nil => intro n hn; simp at hn; subst hn; simp [evalStops]
  | cons m rest ih =>
    intro n hn
    have hsm : s.pos < m.pos := (List.pairwise_cons.1 hs).1 m (by simp)
    have hrest := (List.pairwise_cons.1 hs).2
    simp only [List.mem_cons] at hn
    rcases hn with rfl | rfl | hn
    · simp [evalStops]
    · have : ¬ n.pos ≤ s.pos := by grind
      simp [evalStops, this, lerp_div_self hsm, Color.lerp_one]
    · have h1 : s.pos < n.pos := (List.pairwise_cons.1 hs).1 n (by simp [hn])
      have h2 : m.pos < n.pos := (List.pairwise_cons.1 hrest).1 n hn
      have a : ¬ n.pos ≤ s.pos := by grind
      have b : ¬ n.pos ≤ m.pos := by grind
      simp only [evalStops, a, b, ite_false]
      exact ih m hrest n (by simp [hn])

/-- Before the first stop, the first stop's colour. -/
theorem evalStops_before (s : Stop) (rest : List Stop) {t : Rat} (h : t ≤ s.pos) :
    evalStops s rest t = s.color := by
  cases rest <;> simp [evalStops, h]

/-- After the last of stops in ascending order, the last stop's colour. -/
theorem evalStops_after (s : Stop) (rest : List Stop) (hs : (s :: rest).Pairwise (·.pos < ·.pos))
    {t : Rat} (h : ∀ n ∈ s :: rest, n.pos ≤ t) :
    evalStops s rest t = ((s :: rest).getLast (by simp)).color := by
  induction rest generalizing s with
  | nil => simp [evalStops]
  | cons m rest ih =>
    have hsm : s.pos < m.pos := (List.pairwise_cons.1 hs).1 m (by simp)
    have hrest := (List.pairwise_cons.1 hs).2
    have a : ¬ t ≤ s.pos := by have := h m (by simp); grind
    have hm := h m (by simp)
    by_cases b : t ≤ m.pos
    · have ht : t = m.pos := by grind
      have : rest = [] := by
        cases rest with
        | nil => rfl
        | cons k rest =>
          have hmk : m.pos < k.pos := (List.pairwise_cons.1 hrest).1 k (by simp)
          have := h k (by simp); grind
      subst this ht
      simp [evalStops, a, lerp_div_self hsm, Color.lerp_one]
    · simp only [evalStops, a, b, ite_false]
      rw [ih m hrest (fun n hn => h n (by simp [hn]))]
      simp

/-- Up to the next stop's position, a stop's colour holds. -/
theorem evalSteps_before (s n : Stop) (rest : List Stop) {t : Rat} (h : t < n.pos) :
    evalSteps s (n :: rest) t = s.color := by
  have : ¬ n.pos ≤ t := by grind
  simp [evalSteps, this]

/-- Stops in ascending order give their own colour at their own position. -/
theorem evalSteps_at (s : Stop) (rest : List Stop) (hs : (s :: rest).Pairwise (·.pos < ·.pos)) :
    ∀ n ∈ s :: rest, evalSteps s rest n.pos = n.color := by
  induction rest generalizing s with
  | nil => intro n hn; simp at hn; subst hn; simp [evalSteps]
  | cons m rest ih =>
    intro n hn
    have hsm : s.pos < m.pos := (List.pairwise_cons.1 hs).1 m (by simp)
    have hrest := (List.pairwise_cons.1 hs).2
    simp only [List.mem_cons] at hn
    rcases hn with rfl | hn
    · have : ¬ m.pos ≤ n.pos := by grind
      simp [evalSteps, this]
    · have h : m.pos ≤ n.pos := by
        rcases hn with rfl | hn
        · grind
        · exact Rat.le_of_lt ((List.pairwise_cons.1 hrest).1 n hn)
      simp only [evalSteps, h, ite_true]
      exact ih m hrest n (by simpa using hn)

end Inkproof.Scene
