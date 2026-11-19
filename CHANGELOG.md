# Changelog

## v0.17.0

- `placeAxisTitle` places an axis title centred along the axis, clear of its tick labels.

## v0.16.0

- `compileTimeAxis` draws an axis for a scale of unix seconds, with ticks at clock intervals labelled in UTC.

## v0.15.0

- `Join` draws a line or area with stepped or spline joins between points, never across a gap.

## v0.14.0

- `compileScatterBy` draws a scatter with a marker radius computed from each value.

## v0.13.0

- `LineStyle.dash` draws a line dashed or dotted with a `DashPattern` in grid units, and `Dash.pattern` gives the pattern for a series theme's dash.

## v0.12.1

- `compileLine`, `compileArea` and `compileEnvelope` no longer recurse once per point, so a million points compile.

## v0.12.0

- `compileIsolated` marks the samples a line cannot show, and `compileRing` draws a hollow marker.

## v0.11.0

- `compileEnvelopeOfExtents` draws an envelope straight from a pyramid's per-column `Minimum` and `Maximum`.
- `compileLinearAxis`, `compileLogAxis` and `compileCategoricalAxis` draw an axis for a scale in one call, on any side.

## v0.10.0

- `compileAxis` draws an axis line, tick marks and gridlines and places the labels Axis keeps, on any side of the plot.

## v0.9.0

- `Item.fold` and `Item.runs` traverse a strip's pieces and joins and split it into runs at its gaps.

## v0.8.0

- `compileEnvelope` draws per-column lowest and highest values as one envelope, with a gap at each absent column.

## v0.7.1

- Lasm tests run under @lasm/cli 0.8.0.

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
