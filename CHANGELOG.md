# Changelog

## v0.7.0

- `Theme` with contrast-checked light and dark palettes whose series differ by marker and dash as well as colour, and the WCAG `Color.luminance` and `Color.contrast` they are checked with.

## v0.6.0

- `DisplayList.paintOrder`, the stable sort of commands by layer, with proofs that it is a permutation, sorted by layer and keeps list order within a layer, and that painting in this order gives `pixelColor`.

## v0.5.0

- Took the square and clamp lemmas and `clamp` from inkproof-float; `clamp` now takes the interval first.
- Dropped the unused inkproof-axis requirement.

## v0.4.0

- Compilers from series, scales and aggregates to display lists for line, area, bar, scatter and heatmap charts.
- Proof that first/min/max/last reduction of a bare line covers the same pixels as the full data, and that no line is drawn across a gap or missing value.

## v0.3.0

- A pure-Lean reference rasterizer from a display list to a pixel buffer, proved to paint exactly the pixels the raster model covers, in layer order.

## v0.2.0

- Clipping of display lists to a rectangle, with a proof against the raster model.
- Triangle geometry for thick lines, with a proof against the raster model.

## v0.1.0

- The display list and the aliased, touch-based raster model, with proofs that a primitive covers every pixel it touches and that coverage is monotone under union.
