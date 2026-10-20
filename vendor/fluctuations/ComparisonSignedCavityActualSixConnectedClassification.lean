module

public import ComparisonSignedCavityActualLongitudinalPairing

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 6000000

theorem cut_block_ne_split_lt {S : Type*} {as : List PositiveMass}
    (T : ClockTree S as) (U : ℕ) (hU : U ≤ as.length) (a c : T.Slot)
    (h : T.cutBlock U hU a ≠ T.cutBlock U hU c) : T.splitIndex a c < U := by
  by_contra H
  exact h ((T.cutBlock_eq_iff U hU a c).mpr (by omega))

theorem fullScalarCutConnected4_cross_target_zero {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (U : ℕ) (K : ℕ→ℝ) (a c e f : T.Slot) (hU : U ≤ as.length)
    (hac : T.splitIndex a c < U) (hef : U ≤ T.splitIndex e f) :
    fullScalarCutConnected4 T U K a c e f=0 := by
  classical
  let : DecidableEq (T.CutBlock U hU) := Classical.decEq _
  have H4 : fullScalarCutMoment T U K [a,c,e,f]=0 := by
    by_contra H
    have HF : T.disorderExpect (fullWeight n) (fullFeature n) 0
        (cutFullVariance n 0 U 0 0 0 0 K)
        (fun σ=>(1:ℝ)*siteMonomial T σ [a,c,e,f]) 0 ≠ 0 := by
      rw [cut_full_monomial_eq_retained n 0 U 0 0 K T ho (fun _=>1) [a,c,e,f],
        T.cavityLeft.disorderExpect_one (restWeight_pos n) (restFeature n) ho,one_mul]
      exact H
    have HE:=cutDisorderExpect_graph_nonzero_even n 0 U (by omega : 0 < U)
      0 0 0 K T hU (fun _=>1) 0 (by intro i;rfl) (by intro i;rfl) [a,c,e,f] HF
    let B:=T.cutBlock U hU
    have hEF : B e=B f := (T.cutBlock_eq_iff U hU e f).mpr hef
    have hAC : B c ≠ B a := by
      intro H
      have := (T.cutBlock_eq_iff U hU a c).mp H.symm
      omega
    have H:=HE (B a)
    change Even ([B a,B c,B e,B f].count (B a)) at H
    rw [Nat.even_iff] at H
    simp only [List.count_cons,List.count_nil,←hEF] at H
    simp only [beq_self_eq_true,beq_eq_false_iff_ne.mpr hAC] at H
    cases hE : (B e == B a) <;> simp [hE] at H
  unfold fullScalarCutConnected4
  rw [H4,fullScalarCutGamma_cross_zero T ho U K a c hU hac]
  ring

theorem fullScalarCutConnected4_separate_pairs_zero {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (U : ℕ) (hU0 : 0 < U) (hU : U ≤ as.length) (K : ℕ→ℝ) (a c e f : T.Slot)
    (hcross : ∀ s∈[a,c],∀ t∈[e,f],T.splitIndex s t < U) :
    fullScalarCutConnected4 T U K a c e f=0 := by
  have H:=fullScalarCutMoment_factor T ho U hU0 hU K [a,c] [e,f] hcross
  simp only [List.cons_append,List.nil_append] at H
  unfold fullScalarCutConnected4 fullScalarCutGamma
  rw [H]
  ring

theorem cut_block_cross_list {S : Type*} {as : List PositiveMass}
    (T : ClockTree S as) (U : ℕ) (hU : U ≤ as.length)
    (ls rs : List T.Slot) (A B : T.CutBlock U hU)
    (hl : ∀ s∈ls,T.cutBlock U hU s=A)
    (hr : ∀ s∈rs,T.cutBlock U hU s=B) (hAB : A ≠ B) :
    ∀ s∈ls,∀ t∈rs,T.splitIndex s t < U := by
  intro s hs t ht
  apply cut_block_ne_split_lt T U hU
  rw [hl s hs,hr t ht]
  exact hAB

theorem native_six_connected_oriented_complete {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (U : ℕ) (K : ℕ→ℝ) (a z e f c d : T.Slot) (hU : U ≤ as.length)
    (haz : T.splitIndex a z < U) (hef : U ≤ T.splitIndex e f)
    (hca : T.cutBlock U hU c=T.cutBlock U hU a)
    (hdz : T.cutBlock U hU d=T.cutBlock U hU z) :
    nativeSixConnectedKernel T U K a z e f c d=
      fullScalarCutConnected4 T U K a c e f*fullScalarCutGamma T U K z d+
      fullScalarCutGamma T U K a c*fullScalarCutConnected4 T U K z d e f := by
  let B:=T.cutBlock U hU
  have hU0 : 0 < U := by omega
  have hAZ : B a ≠ B z := by
    intro H
    have := (T.cutBlock_eq_iff U hU a z).mp H
    omega
  have hEF : B e=B f := (T.cutBlock_eq_iff U hU e f).mpr hef
  by_cases hea : B e=B a
  · have hf : B f=B a := hEF.symm.trans hea
    have hcross : ∀ s∈[a,c,e,f],∀ t∈[z,d],T.splitIndex s t < U :=
      cut_block_cross_list T U hU [a,c,e,f] [z,d] (B a) (B z)
        (by intro s hs; simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
            rcases hs with rfl | rfl | rfl | rfl <;> first | rfl | assumption)
        (by intro s hs; simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
            rcases hs with rfl | rfl <;> first | rfl | exact hdz) hAZ
    have hout : ∀ s∈[z,d],∀ t∈[e,f],T.splitIndex s t < U :=
      cut_block_cross_list T U hU [z,d] [e,f] (B z) (B a)
        (by intro s hs; simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
            rcases hs with rfl | rfl <;> first | rfl | exact hdz)
        (by intro s hs; simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
            rcases hs with rfl | rfl <;> assumption) hAZ.symm
    rw [native_six_connected_left_block T ho U hU0 hU K a z e f c d hcross,
      fullScalarCutConnected4_separate_pairs_zero T ho U hU0 hU K z d e f hout,mul_zero,add_zero]
  · by_cases hez : B e=B z
    · have hf : B f=B z := hEF.symm.trans hez
      have hcross : ∀ s∈[a,c],∀ t∈[z,d,e,f],T.splitIndex s t < U :=
        cut_block_cross_list T U hU [a,c] [z,d,e,f] (B a) (B z)
          (by intro s hs; simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
              rcases hs with rfl | rfl <;> first | rfl | exact hca)
          (by intro s hs; simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
              rcases hs with rfl | rfl | rfl | rfl <;> first | rfl | assumption) hAZ
      have hout : ∀ s∈[a,c],∀ t∈[e,f],T.splitIndex s t < U :=
        fun s hs t ht=>hcross s hs t (by simp only [List.mem_cons,List.not_mem_nil,or_false] at ht ⊢; tauto)
      rw [native_six_connected_right_block T ho U hU0 hU K a z e f c d hcross,
        fullScalarCutConnected4_separate_pairs_zero T ho U hU0 hU K a c e f hout,zero_mul,zero_add]
    · have hcross₁ : ∀ s∈[a,c],∀ t∈[z,d,e,f],T.splitIndex s t < U := by
        intro s hs t ht
        have hsB : B s=B a := by
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
          rcases hs with rfl | rfl <;> first | rfl | exact hca
        apply cut_block_ne_split_lt T U hU
        change B s ≠ B t
        rw [hsB]
        simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
        rcases ht with rfl | rfl | rfl | rfl
        · exact hAZ
        · have htB : B t=B z := hdz
          rw [htB]; exact hAZ
        · exact (Ne.symm hea)
        · rw [←hEF]; exact (Ne.symm hea)
      have hcross₂ : ∀ s∈[z,d],∀ t∈[e,f],T.splitIndex s t < U := by
        intro s hs t ht
        have hsB : B s=B z := by
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
          rcases hs with rfl | rfl <;> first | rfl | exact hdz
        apply cut_block_ne_split_lt T U hU
        change B s ≠ B t
        rw [hsB]
        simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
        rcases ht with rfl | rfl
        · exact (Ne.symm hez)
        · rw [←hEF]; exact (Ne.symm hez)
      have hout : ∀ s∈[a,c],∀ t∈[e,f],T.splitIndex s t < U :=
        fun s hs t ht=>hcross₁ s hs t (by simp only [List.mem_cons,List.not_mem_nil,or_false] at ht ⊢; tauto)
      rw [native_six_connected_outside_blocks T ho U hU0 hU K a z e f c d hcross₁ hcross₂,
        fullScalarCutConnected4_separate_pairs_zero T ho U hU0 hU K a c e f hout,
        fullScalarCutConnected4_separate_pairs_zero T ho U hU0 hU K z d e f hcross₂,
        zero_mul,mul_zero,add_zero]

theorem native_nonjoining_connected_gamma_zero {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (U : ℕ) (K : ℕ→ℝ) (a z e f c d : T.Slot) (hU : U ≤ as.length)
    (hef : U ≤ T.splitIndex e f)
    (hnj : ¬joins (T.cutBlock U hU a) (T.cutBlock U hU z)
      (T.cutBlock U hU c) (T.cutBlock U hU d)) :
    fullScalarCutConnected4 T U K a c e f*fullScalarCutGamma T U K z d+
      fullScalarCutGamma T U K a c*fullScalarCutConnected4 T U K z d e f=0 := by
  by_cases hca : T.cutBlock U hU c=T.cutBlock U hU a
  · have hdz : T.cutBlock U hU d ≠ T.cutBlock U hU z := by
      intro H
      exact hnj (Or.inl ⟨hca,H⟩)
    have hzd:=cut_block_ne_split_lt T U hU z d hdz.symm
    rw [fullScalarCutGamma_cross_zero T ho U K z d hU hzd,
      fullScalarCutConnected4_cross_target_zero T ho U K z d e f hU hzd hef]
    ring
  · have hac:=cut_block_ne_split_lt T U hU a c (Ne.symm hca)
    rw [fullScalarCutGamma_cross_zero T ho U K a c hU hac,
      fullScalarCutConnected4_cross_target_zero T ho U K a c e f hU hac hef]
    ring

theorem native_six_connected_complete_allocation {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (U : ℕ) (K : ℕ→ℝ) (a z e f c d : T.Slot) (hU : U ≤ as.length)
    (haz : T.splitIndex a z < U) (hcd : T.splitIndex c d < U)
    (hef : U ≤ T.splitIndex e f) :
    nativeSixConnectedKernel T U K a z e f c d=
      fullScalarCutConnected4 T U K a c e f*fullScalarCutGamma T U K z d+
      fullScalarCutConnected4 T U K a d e f*fullScalarCutGamma T U K z c+
      fullScalarCutGamma T U K a c*fullScalarCutConnected4 T U K z d e f+
      fullScalarCutGamma T U K a d*fullScalarCutConnected4 T U K z c e f := by
  let B:=T.cutBlock U hU
  have hAZ : B a ≠ B z := by
    intro H
    have := (T.cutBlock_eq_iff U hU a z).mp H
    omega
  by_cases hj : joins (B a) (B z) (B c) (B d)
  · rcases hj with ⟨hca,hdz⟩ | ⟨hcz,hda⟩
    · have Had : T.splitIndex a d < U := cut_block_ne_split_lt T U hU a d (by
        change B a ≠ B d
        rw [hdz]; exact hAZ)
      have Hzc : T.splitIndex z c < U := cut_block_ne_split_lt T U hU z c (by
        change B z ≠ B c
        rw [hca]; exact hAZ.symm)
      rw [native_six_connected_oriented_complete T ho U K a z e f c d hU haz hef hca hdz,
        fullScalarCutGamma_cross_zero T ho U K a d hU Had,
        fullScalarCutGamma_cross_zero T ho U K z c hU Hzc]
      ring
    · have Hac : T.splitIndex a c < U := cut_block_ne_split_lt T U hU a c (by
        change B a ≠ B c
        rw [hcz]; exact hAZ)
      have Hzd : T.splitIndex z d < U := cut_block_ne_split_lt T U hU z d (by
        change B z ≠ B d
        rw [hda]; exact hAZ.symm)
      rw [native_six_connected_swap_low T U K a z e f c d,
        native_six_connected_oriented_complete T ho U K a z e f d c hU haz hef hda hcz,
        fullScalarCutGamma_cross_zero T ho U K a c hU Hac,
        fullScalarCutGamma_cross_zero T ho U K z d hU Hzd]
      ring
  · have hj' : ¬joins (B a) (B z) (B d) (B c) := by
      intro H
      apply hj
      rcases H with ⟨hda,hcz⟩ | ⟨hdz,hca⟩
      · exact Or.inr ⟨hcz,hda⟩
      · exact Or.inl ⟨hca,hdz⟩
    have H₁:=native_nonjoining_connected_gamma_zero T ho U K a z e f c d hU hef hj
    have H₂:=native_nonjoining_connected_gamma_zero T ho U K a z e f d c hU hef hj'
    rw [native_six_connected_nonjoins_zero T ho U K a z e f c d hU haz hcd hef hj]
    linarith

end OAI.SKFluctuations.Cavity
