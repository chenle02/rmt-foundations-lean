# Full API documentation

This nested Lake package pins doc-gen4 to `v4.35.0` at
`0e1ffe2e4ba5ecfdfaf15c65b8d3805dbb7134ae`, matching `lean-toolchain`.
The root package's Lean configuration is unchanged. The committed manifest
pins doc-gen4's transitive dependencies.

From a checkout with the pinned toolchain:

```sh
lake exe cache get
cd docbuild
lake -R -Kenv=dev build RMTFoundations:docs
python3 -m http.server --directory .lake/build/doc 8000
```

Open `http://localhost:8000/`. Serve the docs over HTTP so search can work.
To deliberately change the doc-gen4 dependency pin, first edit its `rev` in
`lakefile.toml`, then run `MATHLIB_NO_CACHE_ON_UPDATE=1 lake update doc-gen4`
inside this directory and review the resulting manifest diff. Normal builds
use the committed lock.

The normal doc-gen4 facet documents transitive imports, including Mathlib and
Lean core. Version 0.1.0 does not commit generated API pages or Mathlib documentation.
The guided site uses `docs/declarations.html` and `docs/modules.html` as its
lightweight source-linked reference, generated from `claims.yaml` and
`MODULES.tsv`. Full API documentation remains a local build option.

GitHub Pages uses **Deploy from a branch**, `main`, `/docs`. There is no custom
Actions Pages deployment. From the repository root, preview the guided site
separately:

```sh
cd docs
bundle install
bundle exec jekyll build --destination ../build/site
cd ..
python3 scripts/build_docs.py --site build/site
```
