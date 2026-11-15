/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

namespace Inkproof.Scene

/-! # The raster model

Plane coordinates are exact rationals, so nothing here involves floating point. The pixel grid has
`w` columns and `h` rows; pixel `(col, row)` is the closed unit square `[col, col + 1] × [row, row + 1]`.
A primitive is a set of points (`Region`), and it covers a pixel when it meets that square: some
point of the primitive lies in it. Boundaries count, so a primitive that only touches a pixel's
edge or corner covers it, and a point on a shared edge covers every pixel sharing it. The rule is
deliberately generous: it never loses a feature that reaches a pixel, however thin.

Anti-aliasing and any other shading are not part of the model; a renderer may differ from it only
as documented where it is built. -/

/-- A point in the plane. -/
structure Pt where
  x : Rat
  y : Rat
  deriving DecidableEq, Repr

/-- A pixel of the grid, by column and row. -/
structure Pixel where
  col : Nat
  row : Nat
  deriving DecidableEq, Repr

/-- The pixel grid: `w` columns by `h` rows, covering `[0, w] × [0, h]`. -/
structure Grid where
  w : Nat
  h : Nat
  deriving DecidableEq, Repr

/-- The point lies in the pixel's closed square. -/
def Pixel.Contains (px : Pixel) (p : Pt) : Prop :=
  (px.col : Rat) ≤ p.x ∧ p.x ≤ px.col + 1 ∧ (px.row : Rat) ≤ p.y ∧ p.y ≤ px.row + 1

/-- The pixel is in the grid. -/
def Grid.Has (g : Grid) (px : Pixel) : Prop := px.col < g.w ∧ px.row < g.h

/-- The point lies in the grid's closed extent `[0, w] × [0, h]`. -/
def Grid.Holds (g : Grid) (p : Pt) : Prop :=
  0 ≤ p.x ∧ p.x ≤ g.w ∧ 0 ≤ p.y ∧ p.y ≤ g.h

/-- A set of points: what a primitive occupies. -/
abbrev Region := Pt → Prop

/-- `a` and `b` in either order: `v` lies between them. -/
def Between (a b v : Rat) : Prop := (a ≤ v ∧ v ≤ b) ∨ (b ≤ v ∧ v ≤ a)

/-- A region covers a pixel when it meets the pixel's closed square. -/
def Region.Covers (r : Region) (px : Pixel) : Prop := ∃ p, r p ∧ px.Contains p

/-- Everything `a` occupies, `b` occupies. -/
def Region.Sub (a b : Region) : Prop := ∀ p, a p → b p

/-- The segment from `a` to `b`, ends included. -/
def Region.seg (a b : Pt) : Region := fun p =>
  ∃ t : Rat, 0 ≤ t ∧ t ≤ 1 ∧ p.x = a.x + t * (b.x - a.x) ∧ p.y = a.y + t * (b.y - a.y)

/-- The single point `a`. -/
def Region.point (a : Pt) : Region := fun p => p = a

/-- The quadrilateral swept by a vertical segment moving linearly from `x0` to `x1`, its ends going
from `l0` to `l1` and from `h0` to `h1`; each end may be the lower or the upper. -/
def Region.span (x0 x1 l0 l1 h0 h1 : Rat) : Region := fun p =>
  ∃ t : Rat, 0 ≤ t ∧ t ≤ 1 ∧ p.x = x0 + t * (x1 - x0) ∧
    Between (l0 + t * (l1 - l0)) (h0 + t * (h1 - h0)) p.y

/-- The axis-aligned rectangle with opposite corners `(x0, y0)` and `(x1, y1)`, boundary included. -/
def Region.box (x0 y0 x1 y1 : Rat) : Region := fun p => Between x0 x1 p.x ∧ Between y0 y1 p.y

/-- The closed disc of radius `|r|` about `c`. -/
def Region.disc (c : Pt) (r : Rat) : Region := fun p =>
  (p.x - c.x) * (p.x - c.x) + (p.y - c.y) * (p.y - c.y) ≤ r * r

/-- Every point within `|r|` of `a`, in the Euclidean sense: round joins and round caps. -/
def Region.thicken (r : Rat) (a : Region) : Region := fun p =>
  ∃ q, a q ∧ Region.disc q r p

end Inkproof.Scene
