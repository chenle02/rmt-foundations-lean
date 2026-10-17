import RMTFoundations.TracyWidom.OrderOneMonotone


set_option autoImplicit false
namespace RMTFoundations.TracyWidom
open MeasureTheory Set
open RMTFoundations.Airy RMTFoundations.TWOneBounds RMTFoundations.TWOneMonotone
set_option maxHeartbeats 4000000 in
/-- Every closed shift cell has a kernel-checked actual first-square certificate. -/
theorem airy_closed_slab_first_square_margin
    (j : ℕ) -- [definition]
    (hj : j<270) -- [standing]
    (s : ℝ) -- [definition]
    (hs : s∈Icc ((-27/5:ℝ)+(j:ℝ)/50) ((-27/5:ℝ)+((j:ℝ)+1)/50)) -- [standing]
    : (1/10000:ℝ)≤airyAiReal s+(airyEnergy s+
      ‖airyBoundaryVector s+airyHankelShift s (airyBoundaryVector s)‖^2)/2 := by
  interval_cases j
  · have h := airy_negative_slab_certificate_0 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_1 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_2 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_3 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_4 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_5 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_6 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_7 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_8 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_9 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_10 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_11 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_12 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_13 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_14 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_15 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_16 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_17 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_18 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_19 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_20 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_21 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_22 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_23 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_24 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_25 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_26 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_27 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_28 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_29 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_30 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_31 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_32 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_33 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_34 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_35 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_36 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_37 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_38 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_39 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_40 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_41 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_42 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_43 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_44 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_45 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_46 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_47 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_48 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_49 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_50 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_51 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_52 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_53 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_54 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_55 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_56 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_57 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_58 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_59 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_60 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_61 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_62 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_63 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_64 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_65 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_66 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_67 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_68 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_69 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_70 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_71 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_72 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_73 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_74 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_75 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_76 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_77 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_78 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_79 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_80 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_81 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_82 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_83 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_84 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_85 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_86 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_87 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_88 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_89 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_90 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_91 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_92 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_93 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_94 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_95 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_96 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_97 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_98 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_99 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_100 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_101 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_102 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_103 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_104 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_105 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_106 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_107 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_108 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_109 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_110 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_111 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_112 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_113 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_114 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_115 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_116 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_117 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_118 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_119 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_120 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_121 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_122 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_123 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_124 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_125 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_126 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_127 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_128 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_129 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_130 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_131 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_132 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_133 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_134 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_135 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_136 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_137 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_138 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_139 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_140 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_141 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_142 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_143 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_144 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_145 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_146 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_147 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_148 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_149 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_150 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_151 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_152 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_153 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_154 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_155 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_156 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_157 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_158 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_159 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_160 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_161 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_162 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_163 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_164 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_165 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_166 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_167 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_168 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_169 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_170 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_171 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_172 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_173 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_174 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_175 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_176 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_177 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_178 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_179 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_180 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_181 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_182 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_183 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_184 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_185 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_186 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_187 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_188 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_189 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_190 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_191 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_192 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_193 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_194 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_195 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_196 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_197 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_198 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_199 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_200 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_201 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_202 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_203 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_204 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_205 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_206 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_207 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_208 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_209 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_210 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_211 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_212 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_213 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_214 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_215 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_216 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_217 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_218 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_219 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_220 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_221 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_222 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_223 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_224 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_225 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_226 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_227 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_228 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_229 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_230 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_231 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_232 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_233 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_234 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_235 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_236 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_237 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_238 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_239 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_240 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_241 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_242 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_243 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_244 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_245 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_246 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_247 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_248 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_249 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_250 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_251 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_252 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_253 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_254 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_255 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_256 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_257 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_258 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_259 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_260 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_261 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_262 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_263 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_264 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_265 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_266 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_267 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_268 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]
  · have h := airy_negative_slab_certificate_269 s (by norm_num at hs ⊢; exact hs)
    nlinarith only [h]

/-- Uniform retained margin on the full closed compact shift window. -/
theorem airy_first_square_margin_window
    (s : ℝ /- [definition] -/)
    (hs : s ∈ Icc (-27/5:ℝ) 0 /- [standing] -/) :
    (1/10000:ℝ) ≤ airyAiReal s+(airyEnergy s+
      ‖airyBoundaryVector s+airyHankelShift s (airyBoundaryVector s)‖^2)/2 := by
  have hm : s∈Icc (-27/5:ℝ) ((-27/5:ℝ)+(270:ℝ)*(1/50)) := by
    norm_num at hs ⊢
    exact hs
  obtain ⟨j,hj,hd⟩ := real_closed_slab_grid_cover (-27/5) (1/50) 270
    (by norm_num) (by norm_num) s hm
  have hb := abs_le.mp hd
  have hc : s∈Icc ((-27/5:ℝ)+(j:ℝ)/50) ((-27/5:ℝ)+((j:ℝ)+1)/50) := by
    constructor <;> linarith [hb.1,hb.2]
  exact airy_closed_slab_first_square_margin j (Finset.mem_range.mp hj) s hc

/-- The cell, window and actual nonzero negative row all coexist. -/
theorem strict_window_all_binder_joint_probe :
    (120:ℕ) < 270 ∧ (-3:ℝ) ∈ Icc ((-27/5:ℝ)+(120:ℝ)/50)
      ((-27/5:ℝ)+((120:ℝ)+1)/50) ∧
    (-3:ℝ) ∈ Icc (-27/5:ℝ) 0 ∧ airyBoundaryVector (-3) ≠ 0 ∧
    (1/10000:ℝ) ≤ airyAiReal (-3)+(airyEnergy (-3)+
      ‖airyBoundaryVector (-3)+airyHankelShift (-3) (airyBoundaryVector (-3))‖^2)/2 :=
  ⟨by norm_num,by norm_num,by norm_num,airyBoundaryVector_ne_zero (-3),
    airy_first_square_margin_window (-3) (by norm_num)⟩
end RMTFoundations.TracyWidom

#print axioms RMTFoundations.TracyWidom.airy_closed_slab_first_square_margin
#print axioms RMTFoundations.TracyWidom.airy_first_square_margin_window
#print axioms RMTFoundations.TracyWidom.strict_window_all_binder_joint_probe
