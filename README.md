# Erdos_1197

![Dependency graph](dependency-graph.svg)

This graph shows the verified theorem path from the PNT bridge to the former single gap
`bm_approx_data`.

Blue nodes are the upstream dependencies on that path. The green node is the resolved
`bm_approx_data` theorem itself.

The graph intentionally omits downstream consumers in `Formalization.lean` and routine
algebraic helper lemmas. It also omits the unused helper
`bm_approx_data_of_positive_flat_data`.

To run the project:
```powershell
lake exe cache get
lake build
```
