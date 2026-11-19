# Inkproof.Scene

The display list for Inkproof charts, the compilers that produce it, and a reference rasterizer that defines what it means. Part of Inkproof. Released under the Apache 2.0 license; see `LICENSE`.

## What it does

- Describe a drawing as a display list of layered, coloured shapes (rectangles, line strips, areas, envelopes, markers, text, clipped groups): `DisplayList`, `Command`, `Shape`, `Paint`, `Color`.
- Compile chart data into display-list commands through a projection from data to plane coordinates: `Projection`, `compileLine`, `compileArea`, `compileBars`, `compileScatter`, `compileIsolated`, `compileHeatmap`, `compileEnvelope`.
- Draw a line, area or envelope with gaps where data is missing, so no stroke bridges an absent value: `Item`, `runsOf`, `Item.ofRuns`, `compileEnvelope`.
- Draw an envelope straight from a pyramid's per-column `Minimum` and `Maximum`, an empty column left as a gap: `compileEnvelopeOfExtents`, `extentColumns`.
- Walk a strip's pieces and joins in order, or split it into its runs at its gaps: `Item.fold`, `Item.runs`, `Item.chain`.
- Mark the samples a line cannot show, and draw a hollow marker: `compileIsolated`, `compileRing`.
- Style bars, lines and scatter points: `BarStyle`, `LineStyle`, `ScatterStyle`, `RingStyle`, `SeriesStyle`, with `Dash` and `MarkerShape` for dashes and markers.
- Give the data a chart compiler takes: `Pt` for line and scatter points, `Cell` for heatmap cells, `Column` for envelope columns.
- Thin dense line data without changing its look: `reducePoints`, `reduceRun`, `groupByKey`.
- Clip a display list to a rectangle: `DisplayList.clip`, `Command.clip`, `Shape.clip`, `Rect.meet`.
- Find which commands paint a pixel, and in what order: `DisplayList.paintOrder`, `DisplayList.Covers`, `Command.Covers`, `winner`.
- State exactly which pixels a shape covers (the raster model a GPU renderer must match): `Shape.region`, `Region`, `Region.Covers`, `Pixel`, `Window`, `Grid`.
- Rasterize a display list to an image, the reference for any other renderer: `render`, `pixelColor`, `Image`.
- Draw an axis along a side of the plot: the axis line, a tick mark and optional gridline at each tick, and the labels Axis's `layoutLabels` keeps, placed for the host's text layer; any scale, since ticks are placed by a projection: `compileAxis`, `AxisStyle`, `Side`, `PlacedLabel`, `AxisDrawing`.
- Draw an axis for a linear or log scale in one call, choosing ticks, formatting and thinning labels: `compileLinearAxis`, `compileLogAxis`, `TickSpec`; for ticks already in pixels, `compilePixelAxis`.
- Pick colours, dash styles and markers for series in light and dark themes with checked contrast: `Theme`, `Theme.series`, `Theme.seriesStyle`, `Color.contrast`.

## Requiring it

```lean
require «inkproof-scene» from git "https://github.com/paulbutcher/inkproof-scene" @ "v0.9.0"
```

## Drawing an axis

For a scale, `compileLinearAxis side plot scale spec measure style` (or `compileLogAxis`) does all of the following. Otherwise:

```lean
-- ticks placed in pixels along the axis; layoutLabels decides which labels to keep and how to turn them
let ticks := pixelTicks.map (·.1)
let layout := Inkproof.Axis.layoutLabels measure 4 pixelTicks
let axis := compileAxis .bottom plot toPlane style ticks layout
-- axis.display is a DisplayList; axis.labels give each label's text, anchor and rotation
```

`toPlane` maps a tick's position to its plane coordinate; items of `layout` are `(position, text)`, so ticks of a log scale or band centres work the same way.
