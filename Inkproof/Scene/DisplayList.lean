/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Scene.Raster

namespace Inkproof.Scene

/-- An element of a strip: a value, or an explicit gap. Nothing is drawn between the values on
either side of a gap; a gap is never inferred from the data. -/
inductive Item (α : Type) where
  | val (a : α)
  | gap
  deriving DecidableEq, Repr

/-- The region of a strip: each value occupies `single a`, and each pair of adjacent values with no
gap between them also occupies `join a b`. -/
def Item.chain {α : Type} (single : α → Region) (join : α → α → Region) : List (Item α) → Region
  | [] => fun _ => False
  | .gap :: rest => chain single join rest
  | .val a :: rest => fun p =>
    single a p ∨
    (match rest with
      | .val b :: _ => join a b p
      | _ => False) ∨
    chain single join rest p

/-- One column of a min/max envelope: the values `lo` and `hi` at `x`, in either order. -/
structure Column where
  x : Rat
  lo : Rat
  hi : Rat
  deriving DecidableEq, Repr

/-- The corners of a rectangle; the model treats either order of each pair alike. -/
structure Rect where
  x0 : Rat
  y0 : Rat
  x1 : Rat
  y1 : Rat
  deriving DecidableEq, Repr

inductive MarkerShape where
  /-- A closed square of half-extent `radius`. -/
  | square
  /-- A closed disc of radius `radius`. -/
  | circle
  deriving DecidableEq, Repr

/-- A colour, as 8-bit red, green, blue and alpha. -/
structure Color where
  r : UInt8
  g : UInt8
  b : UInt8
  a : UInt8
  deriving DecidableEq, Repr

/-- What a command draws, and where, in grid coordinates. -/
inductive Shape where
  /-- The polyline through the values, thickened by `halfWidth` (zero is the bare polyline). A value
  with no neighbour is a point, so a lone sample is never lost. -/
  | strip (halfWidth : Rat) (items : List (Item Pt))
  /-- The area swept by the segment from `lo` to `hi` as `x` moves between adjacent columns. -/
  | envelope (items : List (Item Column))
  /-- The area between the polyline through the values and the horizontal line `y = baseline`. -/
  | area (baseline : Rat) (items : List (Item Pt))
  | rect (box : Rect)
  | marker (shape : MarkerShape) (center : Pt) (radius : Rat)
  /-- Text laid out in `box`. The model fixes only the box, which the text must lie within; glyph
  shapes are the renderer's. -/
  | text (box : Rect) (content : String)
  deriving Repr

/-- A drawing command. Commands are painted in ascending `layer`, and within a layer in list order,
later over earlier; each paints `color` over the pixels it covers. -/
structure Command where
  layer : Nat
  color : Color
  shape : Shape
  deriving Repr

/-- The meaning of a display list is the commands in order. -/
abbrev DisplayList := Array Command

def Shape.region : Shape → Region
  | .strip hw items =>
    Region.thicken hw
      (Item.chain Region.point Region.seg items)
  | .envelope items =>
    Item.chain (fun c => Region.span c.x c.x c.lo c.lo c.hi c.hi)
      (fun a b => Region.span a.x b.x a.lo b.lo a.hi b.hi) items
  | .area y0 items =>
    Item.chain (fun a => Region.span a.x a.x y0 y0 a.y a.y)
      (fun a b => Region.span a.x b.x y0 y0 a.y b.y) items
  | .rect b => Region.box b.x0 b.y0 b.x1 b.y1
  | .marker .square c r => Region.box (c.x - r) (c.y - r) (c.x + r) (c.y + r)
  | .marker .circle c r => Region.disc c r
  | .text b _ => Region.box b.x0 b.y0 b.x1 b.y1

/-- A command covers a pixel when its shape does. -/
def Command.Covers (c : Command) (px : Pixel) : Prop := c.shape.region.Covers px

/-- A display list covers a pixel when some command does. -/
def DisplayList.Covers (dl : DisplayList) (px : Pixel) : Prop := ∃ c ∈ dl, c.Covers px

end Inkproof.Scene
