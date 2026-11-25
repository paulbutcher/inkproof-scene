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
    let dl := compileScatter ⟨⟨0, Color.mk 0 0 0 255⟩, .circle, 1⟩ proj s
    check (dl.size == (vals.filter fun v => v.2.isSome).size) "marker count differs from present values"

def scatterByRadiusPerValue : TestCase := .mk "scatterBy draws each marker at the radius of its value" <|
  forAll 300 genPoints fun pts => do
    let s := Series.ofUnsorted (pts.toArray.map fun p => (p.x, some p.y))
    let proj : Projection Rat Rat := ⟨id, id⟩
    let r := fun (y : Rat) => y.abs
    for c in compileScatterBy ⟨⟨0, Color.mk 0 0 0 255⟩, .circle, 1⟩ r proj s do
      match c.shape with
      | .marker _ p rad => check (rad == r p.y) "radius differs from the value's"
      | _ => check false "not a marker"

private def pathLength : List Pt → Rat
  | a :: b :: rest => segLength a b + pathLength (b :: rest)
  | _ => 0

def dashesStayWithinPattern : TestCase := .mk "each dash is no longer than the pattern's on length" <|
  forAll 300 genPoints fun pts => do
    let pat : DashPattern := ⟨2, 1⟩
    for r in dashRun pat pts do
      check (pathLength r ≤ 2) "dash longer than on"

def dashesCoverEveryPeriod : TestCase := .mk "a run has a dash for each full period of its length" <|
  forAll 300 genPoints fun pts => do
    let pat : DashPattern := ⟨2, 1⟩
    let full := (pathLength pts / 3).floor.toNat
    check ((dashRun pat pts).length ≥ full) "a period without a dash"

/-- A million points, every thousandth missing: the compilers must not recurse once per point. -/
def millionPoints : Array (Nat × Option Rat) :=
  Array.ofFn (n := 1000000) fun i => (i.val, if i.val % 1000 == 999 then none else some ((i.val % 97 : Nat) : Rat))

def millionPointsCompile : TestCase := .mk "compilers handle a million points" <|
  match Series.ofPoints? millionPoints with
  | .error _ => .error "series rejected"
  | .ok s => do
    let proj : Projection Nat Rat := ⟨fun x => (x : Rat) / 1000, id⟩
    let paint : Paint := ⟨0, Color.mk 0 0 0 255⟩
    let g := Segmented.single s
    let line := compileLine { paint, halfWidth := 1, reduce := true } proj g
    let area := compileArea paint 0 proj g
    let env := compileEnvelope paint proj (s.values.map (·.map fun y => (y, y)))
    check (line.size == 1 && area.size == 1 && env.size == 1) "a chart did not compile to one command"
    let items : Nat := match line[0]? with
      | some c => match c.shape with
        | .strip _ is => is.length
        | _ => 0
      | none => 0
    check (items != 0) "line has no items"
    let gaps (j : Join) : Nat := match (compileLine { paint, halfWidth := 1, reduce := false, join := j } proj g)[0]? with
      | some c => match c.shape with
        | .strip _ is => (is.filter fun | .gap => true | _ => false).length
        | _ => 0
      | none => 0
    check (gaps .stepAfter == gaps .straight && gaps (.spline 3) == gaps .straight)
      "a join changed where the line breaks"
    check ((compileArea paint 0 proj g (.spline 2)).size == 1) "joined area did not compile"

/-- Stacked bars of non-negative series: one bar per present value, and each rests on the bar
below it at the same x. -/
def stackedBarsRest : TestCase := .mk "stacked bars rest on the bar below" <|
  forAll 200 (fun g =>
    let (n, g) := g.below 12
    g.array 3 fun g => g.array n fun g =>
      let (m, g) := g.below 6
      let (v, g) := g.below 20
      (if m == 0 then none else some (v : Rat), g)) fun cols => do
    let mk (vs : Array (Option Rat)) : Option (Series Nat Rat) :=
      match Series.ofPoints? (vs.mapIdx fun i v => (i, v)) with
      | .ok s => some s
      | .error _ => none
    let ss := cols.filterMap mk
    check (ss.size == cols.size) "series rejected"
    let proj : Projection Nat Rat := ⟨fun x => (x : Rat), id⟩
    let bars := compileStackedBars (fun k => ⟨k, Color.mk 0 0 0 255⟩) 1 proj ss
    check (bars.size == (cols.toList.map fun vs => (vs.filter Option.isSome).size).sum)
      "wrong number of bars"
    let boxAt (k i : Nat) : Option Rect :=
      bars.findSome? fun c => match c.shape with
        | .rect b => if c.layer == k && b.x0 == (i : Rat) - 1 / 2 then some b else none
        | _ => none
    for k in [1:cols.size] do
      match cols[k]?, cols[k - 1]? with
      | some here, some below =>
        for i in [0:here.size] do
          if (here[i]?).any Option.isSome && (below[i]?).any Option.isSome then
            match boxAt k i, boxAt (k - 1) i with
            | some up, some low => check (up.y0 == low.y1) "bar does not rest on the one below"
            | _, _ => check false "bar missing"
      | _, _ => check false "series missing"

/-- At 40 pixels per x unit, a fraction of 3 / 5 gives bars 24 pixels wide, not the 3 / 5 of a
pixel that the same number would mean as a width. -/
def stackedBarsByFraction : TestCase := .mk "stacked bars take a fraction of the spacing" <|
  forAll 100 (fun g => g.below 20) fun n => do
    let pts : Array (Nat × Option Rat) := (Array.range (n + 2)).map fun i => (i, some (i + 1 : Rat))
    match Series.ofPoints? pts with
    | .error _ => check false "series rejected"
    | .ok s =>
      let proj : Projection Nat Rat := ⟨fun x => 40 * (x : Rat), id⟩
      let bars := compileStackedBarsBy (fun k => ⟨k, Color.mk 0 0 0 255⟩) (3 / 5) proj #[s]
      check (bars.size == n + 2) "wrong number of bars"
      for c in bars do
        match c.shape with
        | .rect b => check (b.x1 - b.x0 == 24) "bar is not 3 / 5 of the spacing"
        | _ => check false "not a rect"

/-- The border's rectangles have the area of the outer rectangle less the hole, whichever way the
border is placed and however wide it is. -/
def outlineArea : TestCase := .mk "outline pieces tile the border" <|
  forAll 200 (fun g => let (a, g) := g.below 40; let (b, g) := g.below 40; let (w, g) := g.below 12; let (k, g) := g.below 2; ((a, b, w, k), g)) fun (a, b, w, k) => do
    let r : Rect := ⟨0, 0, (a : Rat), (b : Rat)⟩
    let pl := if k == 0 then OutlinePlacement.inside else .centred
    let wr : Rat := (w : Rat) / 2
    let g : Rat := if k == 0 then 0 else wr / 2
    let ow := (a : Rat) + 2 * g
    let oh := (b : Rat) + 2 * g
    let hole := max 0 (ow - 2 * wr) * max 0 (oh - 2 * wr)
    let area := (r.outline wr pl).foldl (fun s q => s + (q.x1 - q.x0) * (q.y1 - q.y0)) 0
    if wr ≤ 0 then check (area == 0) "a zero width draws something"
    else if ow - 2 * wr > 0 ∧ oh - 2 * wr > 0 then check (area == ow * oh - hole) "wrong border area"
    else check (area == ow * oh) "a border without a hole is not the outer rectangle"

def tests : List TestCase :=
  [reductionKeepsWhatMatters, spikeSurvives, scatterOnePerSample, scatterByRadiusPerValue, dashesStayWithinPattern,
    dashesCoverEveryPeriod, millionPointsCompile, stackedBarsRest,
    stackedBarsByFraction, outlineArea]

end InkproofSceneTest.CompileTests
