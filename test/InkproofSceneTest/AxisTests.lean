/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Scene
import InkproofTools.Test.Harness

namespace InkproofSceneTest.AxisTests

open InkproofTools.Test Inkproof.Scene Inkproof.Core

def paint : Paint := ⟨0, Color.mk 0 0 0 255⟩

def style : AxisStyle := ⟨paint, 1/2, paint, 1/2, 4, some (paint, 1/4), 2, true, true, true, {}⟩

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

def minorLogAxis : TestCase := .mk "a log axis draws a minor gridline at every integer multiple, none labelled" <| do
  let s : Inkproof.Scale.Log Float := ⟨1, 1000, 10, 210⟩
  let minor : MinorGrid Float := ⟨paint, 1/8, (List.range 8).map fun i => (i + 2).toFloat * 10⟩
  let plain := compileLogAxis .bottom plot s spec measure style
  let d := compileLogAxisMinor .bottom plot s spec measure style minor
  let lines := d.display.size - plain.display.size
  check (lines == 8) s!"expected 8 minor gridlines, got {lines}"
  check (d.labels.map (·.text) == plain.labels.map (·.text)) "labels changed"
  check (d.labels.length < lines) "not fewer labels than gridlines"
  for c in d.display.toList.take lines do
    match c.shape with
    | .strip w [.val a, .val b] =>
      check (w == 1/8) "wrong width"
      check (a.x == b.x && 10 ≤ a.x && a.x ≤ 210) "gridline off the plot"
    | _ => check false "not a gridline"

def omittedParts : TestCase := .mk "an axis omits its line, ticks or labels independently" <| do
  let s : Inkproof.Scale.Linear Float := ⟨0, 100, 10, 210⟩
  let full := compileLinearAxis .bottom plot s spec measure style
  let n := (Inkproof.Axis.linearScaleTicks s spec.target).length
  let d1 := compileLinearAxis .bottom plot s spec measure { style with showLine := false }
  let d2 := compileLinearAxis .bottom plot s spec measure { style with showTicks := false }
  let d3 := compileLinearAxis .bottom plot s spec measure { style with showLabels := false }
  let bare := compileLinearAxis .bottom plot s spec measure { style with showLine := false, showTicks := false }
  check (d1.display.size + 1 == full.display.size) "line not omitted alone"
  check (d2.display.size + n == full.display.size) "ticks not omitted alone"
  check (d3.display.size == full.display.size && d3.labels.isEmpty) "labels not omitted alone"
  check (bare.display.size + 1 + n == full.display.size) "bare axis keeps more than gridlines"
  check (bare.labels.map (·.anchor.x) == full.labels.map (·.anchor.x)) "labels moved"

def textStyle : TestCase := .mk "axis labels and titles take their text style, and the default changes no mark" <| do
  let s : Inkproof.Scale.Linear Float := ⟨0, 100, 10, 210⟩
  let big : TextStyle := { family := "serif", size := 20 }
  let plain := compileLinearAxis .bottom plot s spec measure style
  let styled := compileLinearAxis .bottom plot s spec measure { style with labelText := big }
  check (!styled.labels.isEmpty && styled.labels.all fun l => l.style.size == 20 && l.style.family == "serif") "labels not styled"
  check (plain.labels.all (·.style.size == 10)) "default label size changed"
  check (styled.display.size == plain.display.size) "text style changed the marks"
  check ((placeAxisTitle .left plot 20 4 "y").style.size == 12) "title default size"
  check ((placeAxisTitle .left plot 20 4 "y" big).style.size == 20) "title style ignored"

def minorSkipsOutside : TestCase := .mk "a minor gridline outside the plot or on a main gridline is not drawn" <| do
  let s : Inkproof.Scale.Linear Float := ⟨0, 100, 10, 210⟩
  let ts := Inkproof.Axis.linearScaleTicks s spec.target
  let minor : MinorGrid Float := ⟨paint, 1/8, [-50, 500] ++ ts⟩
  let d := compileLinearAxisMinor .bottom plot s spec measure style minor
  check (d.display.size == (compileLinearAxis .bottom plot s spec measure style).display.size)
    "extra gridlines drawn"

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
  [descendingLinear, logAxis, minorLogAxis, minorSkipsOutside, omittedParts, textStyle, categoricalAxis, timeAxisClock, timeAxisMonths]

end InkproofSceneTest.AxisTests
