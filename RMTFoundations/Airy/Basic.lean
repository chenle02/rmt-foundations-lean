import RMTFoundations.Airy.Kernel
import RMTFoundations.Airy.ComplexRestriction

/-!
# Abstract Airy solution layer

The production entry point exports ODE uniqueness and the constant Wronskian,
completed self-kernels and their polarization, and restriction of complex
solutions to the real axis. It does not construct Ai or Bi: use a compatible,
audited complex construction to instantiate these theorems.

The superseded real power-series construction is retained only under
`Tests/AiryLegacy/` as a nonzero regression witness. It is not imported by
this production entry point. Airy asymptotics, positivity, operator ideals,
Fredholm determinants and Tracy-Widom laws remain unproved here.
-/
