/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Scene
import InkproofTools.Test.Harness

open Inkproof.Scene InkproofTools.Test

namespace InkproofSceneTest

def paletteTests : List TestCase :=
  [Theme.light, Theme.dark].flatMap fun t =>
    let name := repr t |>.pretty
    [ .mk s!"{name}: text and series colours meet WCAG contrast on the background" <|
        check t.meetsContrast s!"minimum series contrast {t.minSeriesContrast}",
      .mk s!"{name}: contrast is symmetric and at least 1" <|
        check (t.series.all fun s =>
          s.color.contrast t.background == t.background.contrast s.color &&
            s.color.contrast t.background ≥ 1) "contrast not symmetric",
      .mk s!"{name}: styles repeat after the palette is exhausted" <|
        check (t.seriesStyle 0 == t.seriesStyle t.series.size) "no wrap" ]

def hslTests : List TestCase :=
  [ .mk "ofHsl: primary hues at full saturation and half lightness" <|
      check (Color.ofHsl 0 1 (1 / 2) == ⟨255, 0, 0, 255⟩ && Color.ofHsl 120 1 (1 / 2) == ⟨0, 255, 0, 255⟩ &&
        Color.ofHsl 240 1 (1 / 2) == ⟨0, 0, 255, 255⟩) "primaries wrong",
    .mk "ofHsl: hue wraps every 360 degrees" <|
      check ((List.range 12).all fun i =>
        let h : Rat := i * 37
        Color.ofHsl h (4 / 5) (1 / 2) == Color.ofHsl (h + 720) (4 / 5) (1 / 2) &&
          Color.ofHsl h (4 / 5) (1 / 2) == Color.ofHsl (h - 360) (4 / 5) (1 / 2)) "hue not periodic",
    .mk "ofHsl: out-of-range saturation, lightness and alpha clamp" <|
      check (Color.ofHsl 200 5 (1 / 2) 3 == Color.ofHsl 200 1 (1 / 2) 1 &&
        Color.ofHsl 200 (1 / 2) (-1) == ⟨0, 0, 0, 255⟩) "no clamp",
    .mk "ofHsl: alpha 1/2 rounds half up" <|
      check ((Color.ofHsl 0 0 (1 / 2) (1 / 2)).a == 128) "alpha wrong" ]

end InkproofSceneTest
