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

Additionally, for simplicity of local development, the exact theorems sourced from PNT+ have been added with admits in PNTBridge.lean. These remain as sorries, but have been fully proven and solved already, thus completing the formalisation.
This is, however, unusual, but this then does not require you to also import the full PNT+ project.

chebyshev_asymptotic can be found [here](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/main/PrimeNumberTheoremAnd/Consequences.lean) in the PNT+ project

theta_pos_implies_prime_in_interval can be found [here](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/main/PrimeNumberTheoremAnd/PrimeInInterval.lean) in the PNT+ project
