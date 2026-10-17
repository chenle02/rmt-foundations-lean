import RMTFoundations.TracyWidom.Measures
open MeasureTheory ProbabilityTheory Set
open RMTFoundations.TracyWidom

example : Monotone TW1R := monotone_TW1R
example : IsProbabilityMeasure TW2Measure := inferInstance
example (s : ℝ /- [definition] -/) : cdf TW1Measure s = TW1R s := cdf_TW1Measure s
example (s : ℝ /- [definition] -/) : TW2Measure (Iic s) = ENNReal.ofReal (TW2R s) :=
  TW2Measure_Iic s
