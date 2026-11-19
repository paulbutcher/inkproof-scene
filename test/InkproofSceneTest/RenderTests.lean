/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Scene
import InkproofTools.Test.Harness

open Inkproof.Scene InkproofTools.Test

namespace InkproofSceneTest

def bg : Color := ⟨0, 0, 0, 0⟩
def red : Color := ⟨255, 0, 0, 255⟩
def blue : Color := ⟨0, 0, 255, 255⟩

def grid : Grid := ⟨8, 6⟩

def halves (n : Nat) : Rat := (n : Rat) / 2

def at' (img : Image) (col row : Nat) : Color := (img.get? col row).getD bg

def painted (img : Image) (col row : Nat) : Bool := at' img col row != bg

def paintedPixels (img : Image) : List (Nat × Nat) :=
  (List.range img.height).flatMap fun r => (List.range img.width).filterMap fun c =>
    if painted img c r then some (c, r) else none

def cmd (layer : Nat) (color : Color) (shape : Shape) : Command := ⟨layer, color, shape⟩

def pt (x y : Rat) : Pt := ⟨x, y⟩

def draw (cmds : List Command) : Image := render cmds.toArray grid bg

/-- A random point of the grid, on half-pixel steps. -/
def genPt (g : Rng) : Pt × Rng :=
  let (x, g) := g.below 17
  let (y, g) := g.below 13
  (pt (halves x) (halves y), g)

def genRect (g : Rng) : Rect × Rng :=
  let (a, g) := genPt g
  let (b, g) := genPt g
  (⟨a.x, a.y, b.x, b.y⟩, g)

def renderTests : List TestCase := [
  .mk "an empty display list paints nothing, and the image has the grid's size" do
    let img := draw []
    check (paintedPixels img).isEmpty "painted something"
    check (img.pixels.size == grid.w * grid.h) "wrong size",

  .mk "a rectangle paints inside its bounding pixels and nothing outside" <|
    forAll 200 genRect fun r =>
      let img := draw [cmd 0 red (.rect r)]
      let cols := (paintedPixels img).map (·.1)
      let rows := (paintedPixels img).map (·.2)
      let lox := min r.x0 r.x1; let hix := max r.x0 r.x1
      let loy := min r.y0 r.y1; let hiy := max r.y0 r.y1
      check (cols.all fun c => lox ≤ (c : Rat) + 1 && (c : Rat) ≤ hix) "column outside" *>
      check (rows.all fun c => loy ≤ (c : Rat) + 1 && (c : Rat) ≤ hiy) "row outside" *>
      check (cols.length == 0 || (cols.length == (cols.eraseDups.length) * (rows.eraseDups.length)))
        "not a rectangle of pixels",

  .mk "a lone sample between pixel centres paints a pixel, with any half-width" <|
    forAll 200 genPt fun p =>
      let img := draw [cmd 0 red (.strip 0 [.val p])]
      check ((paintedPixels img).any fun (c, r) =>
        (c : Rat) ≤ p.x && p.x ≤ c + 1 && (r : Rat) ≤ p.y && p.y ≤ r + 1) "spike lost",

  .mk "a gap leaves the pixels between its sides unpainted" do
    let a := pt (1 / 4) (5 / 2)
    let b := pt (31 / 4) (5 / 2)
    let with' := draw [cmd 0 red (.strip 0 [.val a, .val b])]
    let without := draw [cmd 0 red (.strip 0 [.val a, .gap, .val b])]
    check (painted with' 4 2) "line does not reach the middle" *>
    check (!painted without 4 2) "gap was bridged" *>
    check (painted without 0 2 && painted without 7 2) "ends lost",

  .mk "later layers paint over earlier ones, whatever the list order" do
    let r : Shape := .rect ⟨1, 1, 4, 4⟩
    let img := draw [cmd 1 blue r, cmd 0 red r]
    check (at' img 2 2 == blue) "lower layer won"
    *> check (at' (draw [cmd 0 red r, cmd 0 blue r]) 2 2 == blue) "equal layers: later in the list must win",

  .mk "every pixel is the background or the command's colour" <|
    forAll 100 genRect fun r =>
      let img := draw [cmd 0 red (.rect r)]
      check ((List.range 6).all fun row => (List.range 8).all fun col =>
        at' img col row == bg || at' img col row == red) "pixel is neither background nor colour",

  .mk "a vertical gradient is flat across each row and blends between its end colours" do
    let top : Color := ⟨255, 0, 0, 255⟩
    let bottom : Color := ⟨0, 0, 255, 255⟩
    let grad : Shading := .gradient .y ⟨1, top⟩ [⟨5, bottom⟩]
    let img := draw [⟨0, grad, .rect ⟨0, 0, 8, 6⟩⟩]
    check ((List.range 6).all fun row => (List.range 8).all fun col =>
      at' img col row == at' img 0 row)
      "colour varies along x" *>
    check (at' img 0 0 == top && at' img 0 5 == bottom) "ends are not the stop colours" *>
    check ((List.range 4).all fun row =>
      (at' img 0 (row + 1)).r ≥ (at' img 0 (row + 2)).r &&
      (at' img 0 (row + 1)).b ≤ (at' img 0 (row + 2)).b) "red does not fall as blue rises",

  .mk "a clipped command paints nothing outside its scissor" <|
    forAll 100 (fun g => let (a, g) := genPt g; let (b, g) := genPt g; ((a, b), g)) fun (a, b) =>
      let img := draw [cmd 0 red (.clipped ⟨2, 1, 5, 4⟩ (.strip 1 [.val a, .val b]))]
      check ((paintedPixels img).all fun (c, r) => 1 ≤ c && c ≤ 5 && r ≤ 4)
        "outside the scissor",

  .mk "a thicker line paints every pixel a thinner one does" <|
    forAll 100 (fun g => let (a, g) := genPt g; let (b, g) := genPt g; ((a, b), g)) fun (a, b) =>
      let thin := draw [cmd 0 red (.strip (1 / 4) [.val a, .val b])]
      let thick := draw [cmd 0 red (.strip (3 / 2) [.val a, .val b])]
      check ((paintedPixels thin).all fun (c, r) => painted thick c r) "thick lost a pixel"
]

end InkproofSceneTest
