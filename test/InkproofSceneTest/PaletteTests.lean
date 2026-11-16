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

end InkproofSceneTest
