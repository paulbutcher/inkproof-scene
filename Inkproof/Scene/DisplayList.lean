/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Scene.Raster
import Inkproof.Scene.Shading

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

/-- The pieces of a strip in order: `piece a` for each value, and `join a b` after it for each pair
of adjacent values with no gap between them. -/
def Item.fold {α β : Type} (piece : α → β) (join : α → α → β) : List (Item α) → List β
  | [] => []
  | .gap :: rest => fold piece join rest
  | .val a :: rest =>
    piece a :: (match rest with
      | .val b :: _ => join a b :: fold piece join rest
      | _ => fold piece join rest)

/-- The runs of a strip: its values between gaps, in order. A gap ends a run, so a strip that
ends in a value ends in a run without a gap after it. -/
def Item.runs {α : Type} : List (Item α) → List (List α)
  | [] => []
  | .gap :: rest => [] :: runs rest
  | .val a :: rest =>
    match runs rest with
    | [] => [[a]]
    | r :: rs => (a :: r) :: rs

theorem Item.fold_gap {α β : Type} (piece : α → β) (join : α → α → β) (rest : List (Item α)) :
    Item.fold piece join (.gap :: rest) = Item.fold piece join rest := rfl

/-- A value is followed by its join with the next value exactly when that next item is a value. -/
theorem Item.fold_val_val {α β : Type} (piece : α → β) (join : α → α → β) (a b : α)
    (rest : List (Item α)) :
    Item.fold piece join (.val a :: .val b :: rest) =
      piece a :: join a b :: Item.fold piece join (.val b :: rest) := rfl

theorem Item.fold_val_gap {α β : Type} (piece : α → β) (join : α → α → β) (a : α)
    (rest : List (Item α)) :
    Item.fold piece join (.val a :: .gap :: rest) = piece a :: Item.fold piece join rest := rfl

theorem Item.fold_val_nil {α β : Type} (piece : α → β) (join : α → α → β) (a : α) :
    Item.fold piece join [.val a] = [piece a] := rfl

/-- A gap separates the strip into independent parts: nothing is joined across it. -/
theorem Item.fold_append_gap {α β : Type} (piece : α → β) (join : α → α → β) (r : List α)
    (t : List (Item α)) :
    Item.fold piece join (r.map Item.val ++ .gap :: t) =
      Item.fold piece join (r.map Item.val) ++ Item.fold piece join t := by
  cases r with
  | nil => simp [Item.fold]
  | cons a r =>
    suffices ∀ a, Item.fold piece join (.val a :: (r.map Item.val ++ .gap :: t)) =
        Item.fold piece join (.val a :: r.map Item.val) ++ Item.fold piece join t from this a
    induction r with
    | nil => intro a; simp [Item.fold]
    | cons b r ih => intro a; simp only [List.map_cons, List.cons_append, Item.fold, ih]

/-- The runs of a strip, flattened, are its values in order. -/
theorem Item.runs_flatten {α : Type} (items : List (Item α)) :
    (Item.runs items).flatten = items.filterMap fun | .val a => some a | .gap => none := by
  induction items with
  | nil => rfl
  | cons i rest ih =>
    cases i with
    | gap => simpa [Item.runs] using ih
    | val a =>
      simp only [Item.runs]
      cases hr : Item.runs rest with
      | nil => rw [hr] at ih; simp_all
      | cons r rs => rw [hr] at ih; simp_all

/-- A gap ends a run: the values before it form one run, and the strip after it is split afresh. -/
theorem Item.runs_append_gap {α : Type} (r : List α) (t : List (Item α)) :
    Item.runs (r.map Item.val ++ .gap :: t) = r :: Item.runs t := by
  induction r with
  | nil => simp [Item.runs]
  | cons a r ih => simp only [List.map_cons, List.cons_append, Item.runs] at ih ⊢; rw [ih]

/-- `Item.chain` is the union of the pieces of the strip. -/
theorem Item.chain_eq_fold {α : Type} (single : α → Region) (join : α → α → Region)
    (items : List (Item α)) (p : Pt) :
    Item.chain single join items p ↔ ∃ x ∈ Item.fold single join items, x p := by
  induction items with
  | nil => simp [Item.chain, Item.fold]
  | cons i rest ih =>
    cases i with
    | gap => simpa [Item.chain, Item.fold] using ih
    | val a =>
      cases rest with
      | nil => simp [Item.chain, Item.fold]
      | cons j rest' =>
        cases j <;> simp_all [Item.chain, Item.fold]

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
  /-- The part of `inner` that lies in `box`: a scissor. -/
  | clipped (box : Rect) (inner : Shape)
  deriving Repr

/-- A drawing command. Commands are painted in ascending `layer`, and within a layer in list order,
later over earlier; each paints its `color` over the pixels it covers. -/
structure Command where
  layer : Nat
  color : Shading
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
  | .clipped b s => fun p => Region.box b.x0 b.y0 b.x1 b.y1 p ∧ s.region p

/-- The colour a command gives a pixel it covers. -/
def Command.colorAt (c : Command) (px : Pixel) : Color := c.color.at px

theorem Command.colorAt_eq (c : Command) (px : Pixel) : c.colorAt px = c.color.at px := rfl

/-- A command covers a pixel when its shape does. -/
def Command.Covers (c : Command) (px : Pixel) : Prop := c.shape.region.Covers px

/-- A display list covers a pixel when some command does. -/
def DisplayList.Covers (dl : DisplayList) (px : Pixel) : Prop := ∃ c ∈ dl, c.Covers px

end Inkproof.Scene
