# BridgelandStabLean

BridgelandStabLean is a Lean 4 development of the structural, topological, and metric
foundations of Bridgeland stability conditions on triangulated categories.

The library treats stability conditions as a mathematical subject in its own right. Its main
themes are phase transformations, the lifted positive general linear group, triangulated
autoequivalences, Harder--Narasimhan mass, and the topology of the stability space. Geometric
applications are deliberately kept outside the core so that the abstract results remain
reusable across categories.

## What is formalized

- The lifted group `G̃L⁺(2, ℝ)`, including its integer fibre, surjective matrix projection,
  simply connected source, covering map, and topological-group structure.
- Actions on slicings, prestability conditions, and stability conditions.
- Autoequivalence actions modulo natural isomorphism, class-map-compatible actions, and the
  combined effective symmetry action.
- Connected-component transport and equivariance of central-charge and period coordinates.
- Harder--Narasimhan mass, the three-coordinate stability distance, separation, isometries,
  and comparison with the standard stability-space topology.
- The categorical and convex-geometric mass-subadditivity chain, including HN polygons,
  polygon-perimeter comparison, and the cohomological exactness bridge.
- Torsion-free lattice arithmetic and a rank-two numerical lattice model.

The remaining frontiers are tracked in GitHub milestones and issues. Near-term work completes
the unconditional mass-triangle/topology chain; later branches cover weak stability and HRS
tilting, quadratic support, and nonvacuous stability-in-families interfaces.

## Repository map

```text
BridgelandStabLean/
├── StabilityCondition/
│   ├── Phase/                         normalized shifts and phase analysis
│   ├── Symmetry/
│   │   ├── GLTilde/
│   │   │   ├── Action/                actions and continuity
│   │   │   ├── Covering/              fibre, surjectivity, topology, covering map
│   │   │   └── Topology/              topological-group structure
│   │   ├── Autoequivalence/
│   │   │   ├── Foundations/           K₀ and finite-length transport
│   │   │   ├── Slicing/               strict and quotient actions
│   │   │   └── Stability/             stability and class-map actions
│   │   └── Combined/                  topology, components, period map, quotient
│   └── Metric/
│       ├── Distance/                   definition, separation, induced topology
│       ├── Isometry/                   phase and full-distance invariance
│       └── Mass/
│           └── Subadditivity/          HN polygons, exactness, triangle chain
├── Lattice/
│   ├── Arithmetic/
│   └── Numerical/
└── ForMathlib/
    └── LinearAlgebra/Matrix/
```

The taxonomy is also the growth rule. The open weak-stability, support, and family milestones
have reserved branches rather than extending an existing leaf indefinitely:

```text
StabilityCondition/
├── Weak/
│   ├── Basic/
│   ├── ZeroCharge/
│   └── Tilting/
├── Support/
│   ├── Quadratic/
│   ├── Uniform/
│   └── Transport/
└── Families/
    ├── Charge/
    ├── Openness/
    ├── HarderNarasimhan/
    ├── Support/
    └── Boundedness/
```

A new top-level directory should represent a durable mathematical domain, not a single
milestone or paper.

## Build and audit

The Lean toolchain and every Lake dependency are pinned for reproducibility.

```bash
lake build
lake env lean scripts/Audit.lean
lake exe emit
```

The library does not use `sorry`. The audit records the accepted axiom closure, while the
emitter checks the elaborated environment and fails on `sorryAx`.

## Using the library with Mathlib

Add this repository as a Lake dependency and import `BridgelandStabLean`. Lake resolves the
pinned Mathlib-compatible environment transitively. When combining it with another Mathlib
library, align the Lean toolchain and resolved Mathlib revision before adding both dependencies.

## Project records

- GitHub milestones and issues are the source of truth for planned work and dependencies.
- `formalization.yaml` records source scope, toolchain identity, and the trust boundary.
- `registry/` contains statement-level source bindings.

Planning handoffs and narrative roadmaps are intentionally not versioned in this repository.
