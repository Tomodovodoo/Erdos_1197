# Erdos_1197

![Dependency graph](dependency-graph.svg)

This graph shows the repair slice from the imported PNT facts to the former single gap
`bm_approx_data`.

Pink nodes are imported or preexisting boundary dependencies outside our contribution. Gray nodes are local
theorems and lemmas we contributed. The green node is the resolved former gap
`bm_approx_data`.

This completes the lean formalisation of Erdos Problem 1197, many thanks to ebarschkis for all main contributions, and co-authorship of this formalisation with ChatGPT and Aristotle.

To run the project:
```powershell
lake exe cache get
lake build
```
