# Erdos_1197

Minimal Lean workspace for the Haight / Buczolich-Mauldin counterexample formalization.

## Files kept in the repo

- `Erdos1197.lean`: public barrel
- `Formalization.lean`: final problem statement and reduction
- `RequestProject_BMCore.lean`: BM core package resolving the old `bm_approx_data` gap
- `RequestProject_TorusSeparation.lean`: torus/Kronecker infrastructure
- `PNTBridge.lean`: the two trusted PNT bridge statements
- `lakefile.lean`, `lake-manifest.json`, `lean-toolchain`: build configuration

## Build

```powershell
lake exe cache get
lake build
```

The project is pinned to Lean `4.28.0` via `lean-toolchain`.

## Trusted boundary

The only remaining trusted inputs are the two admitted external PNT-facing statements in `PNTBridge.lean`:

- `chebyshev_asymptotic`
- `theta_pos_implies_prime_in_interval`
