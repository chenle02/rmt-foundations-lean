# Contributing

Keep each change focused, and say which declarations or documentation claims
it changes.

## Proofs

- Use the pinned `lean-toolchain` and dependencies.
- Proofs must be kernel-checked and use only `propext`, `Classical.choice` and
  `Quot.sound`. Do not add `sorry`, `admit`, custom axioms or `native_decide`.
- State every hypothesis explicitly. A conditional theorem stays conditional
  in the documentation.
- A new structure needs a nondegenerate inhabitation example.
- Preserve attribution and license headers.

Before requesting review, run:

```sh
lake exe cache get
lake build
bash scripts/verify.sh
```

## Documentation

Theorem statements and `claims.yaml` govern scientific claims. Keep the
README, the status page and `AGENTS.md` aligned with them.

For documentation changes, run

```sh
python3 scripts/build_docs.py --check
```

then build the site with Jekyll and check the output with
`python3 scripts/build_docs.py --site build/site`. The exact commands, and the
API build, are in [docbuild/README.md](docbuild/README.md).

Include the validation output in the pull request.
