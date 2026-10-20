---
layout: landing
title: Random matrices in Lean
description: Tracy–Widom distributions, Airy and Painlevé II theory, finite GUE identities and analytic random-matrix tools, formalized in Lean 4.
permalink: /index.html
---

<section class="hero">
<p class="eyebrow">Lean 4 library · version 0.2.0</p>
<h1>Random matrices, checked in Lean</h1>
<p class="lead">Tracy–Widom distributions, Airy and Painlevé II theory, finite GUE identities and analytic random-matrix tools. Every result is kernel-checked, and every hypothesis is stated in the declaration.</p>
<p class="actions"><a class="button" href="getting-started.html">Get started</a> <a class="button secondary" href="status.html">What is proved</a></p>
</section>

<h2>What version 0.2.0 proves</h2>

<ul class="capsule">
<li><strong>TW1 and TW2.</strong> Smooth, strictly increasing distribution functions; unique probability measures with smooth positive densities, unique quantiles, an exponential moment and all absolute moments; sharp right tails and linear-order left-tail bounds; Painlevé II representations.</li>
<li><strong>Hastings–McLeod.</strong> Unique real global Airy-normalized solution of Painlevé II, equal to the Fredholm response.</li>
<li><strong>TW4.</strong> Positivity, C<sup>1</sup> regularity, endpoint limits, interior levels and a closed formula.</li>
<li><strong>Airy2 and finite GUE.</strong> The extended Airy kernel with its one-time reduction to TW2; Hermite Christoffel–Darboux and the determinantal GUE density.</li>
<li><strong>Analytic tools.</strong> Airy function, Fredholm series, Stieltjes transforms, Marchenko–Pastur, semicircle moments, free convolution subordination, concentration, cumulants, resolvents and simple stochastic integrals.</li>
</ul>

<div class="boundary" role="note">
<p class="label">Not established in 0.2.0</p>
<ul>
<li>TW4 monotonicity, and hence a TW4 probability measure.</li>
<li>The GUE edge limit without the convergence hypothesis <code>GUELimit TW2R</code>.</li>
<li>Unconditional distinct-time finite-ensemble convergence to an Airy2 process; the limit-law theorems retain explicit producer hypotheses.</li>
<li>Sharp cubic left-tail asymptotics.</li>
<li>A sign certificate covering the full compact gap between the two proved TW4 tails.</li>
</ul>
<p><a href="status.html#boundary">Details and the declarations involved</a></p>
</div>

<h2>Additional foundations</h2>
<p>Hermite-to-Airy and one-time Fredholm limits, finite stationary Dyson/OU laws, conditional Airy2 probability limits, and TW4 two-tail positivity with conditional compact-window certificates. Read the <a href="tracy-widom.html">Tracy–Widom guide</a> for the precise scope and required hypotheses.</p>

<h2>Find your way</h2>

<div class="cards">
<a class="card" href="getting-started.html"><strong>Getting started</strong><span>Toolchain, cache and build.</span></a>
<a class="card" href="dependency.html"><strong>Use as a dependency</strong><span>Lake <code>require</code> at <code>v0.2.0</code>.</span></a>
<a class="card" href="status.html"><strong>Status and boundary</strong><span>Each claim with its declarations.</span></a>
<a class="card" href="modules.html"><strong>Module map</strong><span>All registered modules.</span></a>
<a class="card" href="declarations.html"><strong>Declaration index</strong><span>Curated statements with source links.</span></a>
<a class="card" href="trust.html"><strong>Trust</strong><span>Axioms, verification and limits.</span></a>
<a class="card" href="citation.html"><strong>Citation</strong><span>How to cite; acknowledgments.</span></a>
<a class="card" href="agents.html"><strong>Agents</strong><span>Authority order and rules.</span></a>
</div>
