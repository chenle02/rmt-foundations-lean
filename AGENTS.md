# Agent contract

This file governs edits by coding agents and is the contract for all three
entrances: README, the Pages site in `docs/`, and `llms.txt`.

## Authority order

1. Lean declarations and their hypotheses.
2. `claims.yaml` and `formalization.yaml`.
3. `lean-toolchain`, `lakefile.toml` and `lake-manifest.json`.
4. This contract.
5. The guided documentation and the README.

Resolve any inconsistency in favour of the declarations.

## Claim boundary of version 0.2.0

Established: TW1/TW2 distribution functions, measures, densities, quantiles,
moments, smooth CDFs/densities and tail bounds; Painlevé II and Hastings–McLeod; TW4 function
identities, regularity and endpoints; the extended Airy kernel and its one-time
reduction to TW2; finite GUE Hermite and determinantal identities; Stieltjes,
concentration, cumulant and resolvent tools.

Not established:

- TW4 monotonicity or a TW4 probability measure
  (`TW4AiryR_monotone_iff_resolvent_sign` is an equivalence only);
- the GUE edge limit without the hypothesis `GUELimit TW2R`;
- that the finite-N density is the eigenvalue law of the GUE matrix model;
- unconditional distinct-time convergence for the multi-time Airy2 expression;
  probability limits retain explicit finite-law and coordinate-limit hypotheses;
- sharp cubic left-tail asymptotics;
- a global TW4 compact-window sign certificate.

Do not write documentation that weakens a hypothesis or moves an item across
this boundary.

## Rules for changes

- Use only `propext`, `Classical.choice` and `Quot.sound`. No `sorry`,
  `admit`, custom axioms or `native_decide`.
- Preserve theorem statements, attribution headers and dependency pins.
- A new structure needs a nondegenerate inhabitation example.
- Proof changes: run `bash scripts/verify.sh`.
- Documentation changes: run `python3 scripts/build_docs.py --check`, then the
  Jekyll preview in `docbuild/README.md`. Keep `llms.txt` and `CITATION.cff`
  byte-identical to their copies in `docs/`.
