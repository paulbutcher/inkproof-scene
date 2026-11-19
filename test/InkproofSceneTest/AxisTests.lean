/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Scene
import InkproofTools.Test.Harness

namespace InkproofSceneTest.AxisTests

open InkproofTools.Test Inkproof.Scene Inkproof.Core

def paint : Paint := ⟨0, Color.mk 0 0 0 255⟩

def style : AxisStyle := ⟨paint, 1/2, paint, 1/2, 4, some (paint, 1/4), 2⟩

def plot : Rect := ⟨10, 10, 210, 110⟩

def spec : TickSpec := ⟨Inkproof.Axis.Locale.en, 6, 4⟩

def measure (s : String) : Float × Float := (6 * s.length.toFloat, 10)

def count (d : AxisDrawing) : Nat := d.display.size

/-- A vertical axis's pixel range descends, as in a plot with `y` upwards. -/
def descendingLinear : TestCase := .mk "a descending linear axis labels in the plot" <|
  forAll 100 (fun g => let (a, g) := g.below 50; let (n, g) := g.below 200; ((a, n), g)) fun (a, n) => do
    let s : Inkproof.Scale.Linear Float := ⟨a.toFloat, (a + n + 10).toFloat, 110, 10⟩
    let d := compileLinearAxis .left plot s spec measure style
    check (!d.labels.isEmpty) "no labels"
    for l in d.labels do
      check (10 ≤ l.anchor.y && l.anchor.y ≤ 110) "label outside the plot"

def logAxis : TestCase := .mk "a log axis puts a mark for each decade" <|
  let s : Inkproof.Scale.Log Float := ⟨1, 1000, 10, 210⟩
  let d := compileLogAxis .bottom plot s spec measure style
  check (d.labels.map (·.text) == ["1", "10", "100", "1,000"]) "labels differ"

def categoricalAxis : TestCase := .mk "a categorical axis labels each band at its centre" <| do
  let s : Inkproof.Scale.Categorical String Float := ⟨#["a", "b", "c", "d"], 10, 210⟩
  let d := compileCategoricalAxis .bottom plot s id 6 4 measure style
  check (d.labels.map (·.text) == ["a", "b", "c", "d"]) "labels differ"
  for (l, i) in d.labels.zip [0, 1, 2, 3] do
    check (l.anchor.x == (Inkproof.Float.Float.toRat (bandCentrePixel s i)).getD 0) "label off its band centre"

def months : List String :=
  ["Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec"]

def timeAxisClock : TestCase := .mk "a time axis over hours labels ticks as clock times" <|
  forAll 50 (fun g => let (a, g) := g.below 1000000; (a, g)) fun a => do
    let lo := (a * 3600).toFloat
    let s : Inkproof.Scale.Linear Float := ⟨lo, lo + 6 * 3600, 10, 210⟩
    let d := compileTimeAxis .bottom plot s spec months measure style
    check (!d.labels.isEmpty) "no labels"
    for l in d.labels do
      check (l.text.contains ':' || months.any (l.text.startsWith ·)) s!"not a time: {l.text}"

def timeAxisMonths : TestCase := .mk "a time axis over a year names months" <| do
  let s : Inkproof.Scale.Linear Float := ⟨0, 365 * 86400, 10, 210⟩
  let d := compileTimeAxis .bottom plot s spec months measure style
  check (!d.labels.isEmpty) "no labels"
  for l in d.labels do
    check (months.any (l.text.startsWith ·)) s!"not a month: {l.text}"

def tests : List TestCase :=
  [descendingLinear, logAxis, categoricalAxis, timeAxisClock, timeAxisMonths]

end InkproofSceneTest.AxisTests
