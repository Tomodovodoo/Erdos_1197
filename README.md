# Erdos_1197

![Dependency graph](dependency-graph.svg)

This graph shows the local theorem work used to repair the former single gap
`bm_approx_data`.

Pink nodes are imported boundary facts not contributed as part of the repair. Gray nodes are local theorems and lemmas proved in this repo. The green node is the resolved former gap `bm_approx_data`.

The graph is theorem-focused: it shows the named local proof components that materially
feed `bm_approx_data`. Plain definitions and very small algebraic side lemmas are omitted
so the graph stays readable.

To run the project:
```powershell
lake exe cache get
lake build
```
