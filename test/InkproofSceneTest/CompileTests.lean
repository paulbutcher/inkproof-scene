/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Scene
import InkproofTools.Test.Harness

/-! The reduction and the chart compilers on generated data, natively and under Lasm. That the
reduction draws the same pixels, and that no line crosses a gap, are proved; these check that the
compiled code reduces as intended and that the compilers agree with the series. -/

namespace InkproofSceneTest.CompileTests

open InkproofTools.Test Inkproof.Scene Inkproof.Core

/-- Points with non-decreasing x on a grid of eighths, so many share a pixel column. -/
def genPoints (g : Rng) : List Pt × Rng :=
  let (n, g) := g.below 120
  let (raw, g) := g.array n fun g =>
    let (a, g) := g.below 160
    let (b, g) := g.below 41
    ((a, b), g)
  let xs := (raw.map (·.1)).qsort (· < ·)
  let pts := (xs.zip (raw.map (·.2))).map fun (a, b) =>
    (⟨(a : Rat) / 8, (b : Rat) - 20⟩ : Pt)
  (pts.toList, g)

def reductionKeepsWhatMatters : TestCase := .mk "reduction keeps the first, last and extremes" <|
  forAll 300 genPoints fun pts => do
    let red := reducePoints pts
    check (red.head? == pts.head?) "first point lost"
    check (red.getLast? == pts.getLast?) "last point lost"
    let ys := pts.map (·.y)
    check (ys.foldl max (ys.headD 0) ∈ red.map (·.y) || pts.isEmpty) "highest value lost"
    check (ys.foldl min (ys.headD 0) ∈ red.map (·.y) || pts.isEmpty) "lowest value lost"
    let classes := (pts.map fun p => xKey p.x).eraseDups.length
    check (red.length ≤ 4 * classes) "more than four points per column class"

def spikeSurvives : TestCase := .mk "a one-sample spike survives reduction" <|
  forAll 300 genPoints fun pts => do
    let spike : Pt := ⟨3, 1000⟩
    let all := pts.filter (·.x < 3) ++ [spike] ++ pts.filter (·.x > 3)
    let red := reducePoints all
    check (red.any fun q => q.y == 1000) "spike dropped"

def scatterOnePerSample : TestCase := .mk "scatter has one marker per present value" <|
  forAll 300 genPoints fun pts => do
    let vals := pts.toArray.mapIdx fun i p => (p.x, if i % 3 == 0 then none else some p.y)
    let s := Series.ofUnsorted vals
    let proj : Projection Rat Rat := ⟨id, id⟩
    let dl := compileScatter ⟨⟨0, ⟨0, 0, 0, 255⟩⟩, .circle, 1⟩ proj s
    check (dl.size == (vals.filter fun v => v.2.isSome).size) "marker count differs from present values"

/-- A million points, every thousandth missing: the compilers must not recurse once per point. -/
def millionPoints : Array (Nat × Option Rat) :=
  Array.ofFn (n := 1000000) fun i => (i.val, if i.val % 1000 == 999 then none else some ((i.val % 97 : Nat) : Rat))

def millionPointsCompile : TestCase := .mk "compilers handle a million points" <|
  match Series.ofPoints? millionPoints with
  | .error _ => .error "series rejected"
  | .ok s => do
    let proj : Projection Nat Rat := ⟨fun x => (x : Rat) / 1000, id⟩
    let paint : Paint := ⟨0, ⟨0, 0, 0, 255⟩⟩
    let g := Segmented.single s
    let line := compileLine ⟨paint, 1, true⟩ proj g
    let area := compileArea paint 0 proj g
    let env := compileEnvelope paint proj (s.values.map (·.map fun y => (y, y)))
    check (line.size == 1 && area.size == 1 && env.size == 1) "a chart did not compile to one command"
    let items : Nat := match line[0]? with
      | some c => match c.shape with
        | .strip _ is => is.length
        | _ => 0
      | none => 0
    check (items != 0) "line has no items"

def tests : List TestCase :=
  [reductionKeepsWhatMatters, spikeSurvives, scatterOnePerSample, millionPointsCompile]

end InkproofSceneTest.CompileTests
