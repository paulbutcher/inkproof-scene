# Inkproof.Scene

The display list for Inkproof charts, the compilers that produce it, and a reference rasterizer that defines what it means. Part of Inkproof. Released under the Apache 2.0 license; see `LICENSE`.

## What it does

- Describe a drawing as a display list of layered, coloured shapes (rectangles, line strips, areas, envelopes, markers, text, clipped groups): `DisplayList`, `Command`, `Shape`, `Paint`, `Color`.
- Compile chart data into display-list commands through a projection from data to plane coordinates: `Projection`, `compileLine`, `compileArea`, `compileBars`, `compileScatter`, `compileScatterBy` (radius from the value), `compileIsolated`, `compileHeatmap`, `compileEnvelope`.
- Draw a line, area or envelope with gaps where data is missing, so no stroke bridges an absent value: `Item`, `runsOf`, `Item.ofRuns`, `compileEnvelope`.
- Draw an envelope straight from a pyramid's per-column `Minimum` and `Maximum`, an empty column left as a gap: `compileEnvelopeOfExtents`, `extentColumns`.
- Walk a strip's pieces and joins in order, or split it into its runs at its gaps: `Item.fold`, `Item.runs`, `Item.chain`.
- Mark the samples a line cannot show, and draw a hollow marker, outlined in a colour or a gradient: `compileIsolated`, `compileRing`.
- Style bars, lines and scatter points: `BarStyle`, `LineStyle`, `ScatterStyle`, `RingStyle`, `SeriesStyle`, with `Dash` and `MarkerShape` for dashes and markers.
- Give the data a chart compiler takes: `Pt` for line and scatter points, `Cell` for heatmap cells, `Column` for envelope columns.
- Draw a line dashed or dotted with a stated pattern along its length, each dash within the solid line and no dash across a gap: `LineStyle.dash`, `DashPattern`, `Dash.pattern`, `dashRun`.
- Draw stacked areas or stacked bars of several series over shared x values, each band resting on the one below: `compileStackedAreas`, `compileStackedBars` (bar width in the projection's units, pixels for a pixel projection), `compileStackedBarsBy` (bar width as a fraction of the distance between neighbouring x values), `stackSpan`.
- Join a line or area's points with steps before or after each point, or a smooth spline through every point, never across a gap: `Join`, `LineStyle.join`, the `join` argument of `compileArea`, `joinRun`.
- Thin dense line data without changing its look: `reducePoints`, `reduceRun`, `groupByKey`.
- Clip a display list to a rectangle: `DisplayList.clip`, `Command.clip`, `Shape.clip`, `Rect.meet`.
- Draw a rectangle's border of a given width, inside its edge or centred on it, as rectangles that do not overlap (one filled rectangle when the border leaves no hole): `DisplayList.outline`, `Rect.outline`, `OutlinePlacement`.
- Scale a display list by a factor, e.g. to draw at a device pixel ratio: `DisplayList.scale`, `Command.scale`, `Shape.scale`, `Shading.scale`.
- Scale only the pixel sizes (strip half widths, marker radii) of a display list in data coordinates: `DisplayList.scaleSizes`, `Command.scaleSizes`, `Shape.scaleSizes`; `Shape.view` draws a shape under two linear scales.
- Find which commands paint a pixel, and in what order: `DisplayList.paintOrder`, `DisplayList.Covers`, `Command.Covers`, `winner`.
- State exactly which pixels a shape covers (the raster model a GPU renderer must match): `Shape.region`, `Region`, `Region.Covers`, `Pixel`, `Window`, `Grid`.
- Rasterize a display list to an image, the reference for any other renderer: `render`, `pixelColor`, `Image`; translucent commands composite source-over in paint order, `Color.over`.
- Draw an axis along a side of the plot: the axis line, a tick mark and optional gridline at each tick, and the labels (the line, tick marks and labels each switchable off in `AxisStyle`) Axis's `layoutLabels` keeps, placed for the host's text layer; any scale, since ticks are placed by a projection: `compileAxis`, `AxisStyle`, `Side`, `PlacedLabel`, `AxisDrawing`.
- Add lighter gridlines at positions with no tick or label, such as every integer multiple within a decade of a log axis: `MinorGrid` with `compileAxisMinor`, `compileLinearAxisMinor`, `compileLogAxisMinor`, `compileTimeAxisMinor`, `compilePixelAxisMinor`.
- Draw an axis for a linear, log or categorical scale in one call, choosing ticks, formatting and thinning labels: `compileLinearAxis`, `compileLogAxis`, `compileCategoricalAxis` (ticks at band centres, `bandCentrePixel`), `TickSpec`; for a scale of unix seconds, with ticks at clock intervals and UTC time labels, with the year or day a label begins as `PlacedLabel.context` for a second line, `compileTimeAxis`; for ticks already in pixels, `compilePixelAxis`.
- Fill or stroke a shape with a colour that varies along x or y between stops, given in data units through a projection: `Shading`, `Projection.gradientY`, `Projection.gradientX`, `Shading.at`.
- Fill or stroke a shape with a colour that changes at once at each stop instead of blending, stops in data units: `Shading.steps`, `Projection.stepsY`, `Projection.stepsX`.
- Set axis labels, axis titles and bar value labels in one text style, family, size and colour, each with a default: `TextStyle`, `AxisStyle.labelText`, `PlacedLabel.style`, `placeAxisTitle`, `barValueLabels`; every style structure (`AxisStyle`, `LineStyle`, `BarStyle`, `ScatterStyle`, `RingStyle`, `SeriesStyle`, `Paint`) has a default for each field.
- Place an axis title beside an axis, centred along it and clear of the tick labels, turned for a vertical axis: `placeAxisTitle`.
- Pick colours, dash styles and markers for series in light and dark themes with checked contrast: `Theme`, `Theme.series`, `Theme.seriesStyle`, `Color.contrast`.
- Colour an axis, its gridlines, labels, and legend and tooltip boxes for a light or dark theme: `Theme.axis`, `Theme.grid`, `Theme.border`, `Theme.legendFill`, `Theme.tooltipFill`, `Theme.applyAxis`.
- Make a colour from hue, saturation, lightness and alpha: `Color.ofHsl`.

## Requiring it

Use the latest release tag listed in `CHANGELOG.md` in place of `vX.Y.Z`; `lakefile.lean` records the versions of the dependencies this library is built against.

```lean
require «inkproof-scene» from git "https://github.com/paulbutcher/inkproof-scene" @ "vX.Y.Z"
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
