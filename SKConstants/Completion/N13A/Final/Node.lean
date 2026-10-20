module

public import SKConstants.Completion.N13A.DiscardedTail
public import SKConstants.Completion.N13A.FiniteAssembly
public import SKConstants.Completion.N13A.PrefixTransfer

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology

namespace SKConstants.Completion.N13A
open SKConstantsOAI.ZeroTemperatureSK Blueprint Blueprint4

theorem sharpCoarseDomination_holds
    (hSJ3 : JointEndpointIdentityStatement) (hSJ7 : GrowingResidualMGFStatement)
    (hW : SharpWeightedStatement) (hG : SharpGramStatement)
    (hL : SharpLinearEnergyStatement) (hT : SharpTransportStatement) :
    SharpCoarseDominationStatement := by
  intro p hf hc Ω _ W β hβ
  have hψ : SharpRowConcentrationStatement := sharpRowConcentration_of_engine hSJ3 hSJ7
  obtain ⟨ha0, ha1, hz0, hs, hkbz, hkba, hkbb, hkbγ⟩ := coarse_exponent_margins hf hc
  have hβ0 : 0 < β := by linarith
  obtain ⟨Cw, hCw, L, hwt⟩ := hW W β hβ p hf hc
  obtain ⟨Ce, hCe, hlin⟩ := hL W β hβ p hf hc
  obtain ⟨Cp, hCp, hp⟩ := eventually_coarse_susceptibility W β hβ p hf hc
  obtain ⟨Cψ, cψ, hCψ, hcψ, hpsi⟩ := hψ W W β hβ
  obtain ⟨w, hwz, hwγ, hwgap⟩ := exists_weighted_variance_saving hc
  let m := min p.a (min w p.b)
  have hc' := hc
  rcases hc' with ⟨hb0, hbf, _, _, _, _, _, hzγ, _, _, _, hzagap, _, hzbgap, _⟩
  have hm : 2*p.z-p.sb < m :=
    lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have heZ : 1-p.sb < 1+m-2*p.z := by linarith
  have heψ : 1-p.sb < 1+p.a-2*p.z := by linarith
  have hbudget : ∀ᶠ n : ℕ in atTop,
      2*β^2*Cp*(n:ℝ)^(-p.b/2) + Cψ*(n:ℝ)^(-p.a) +
        (1+2*β)*(n:ℝ)^(-p.z) ≤ (n:ℝ)^(-p.kb) := by
    filter_upwards [constant_rpow_le_small_rpow (-p.b/2) (-p.kb) (2*β^2*Cp) (1/3)
      (by linarith) (by positivity) (by norm_num),
      constant_rpow_le_small_rpow (-p.a) (-p.kb) Cψ (1/3)
        (by linarith) hCψ (by norm_num),
      constant_rpow_le_small_rpow (-p.z) (-p.kb) (1+2*β) (1/3)
        (by linarith) (by positivity) (by norm_num)] with n h1 h2 h3
    linarith
  filter_upwards [hwt 2 (by norm_num), hG W β hβ p hf hc 2 (by norm_num), hlin,
    hT W β hβ p hf hc, eventually_coarse_lagMesh W β p hf hc, hp,
    eventually_weighted_budget_le Cw w L p hwγ,
    eventually_weighted_remainder_le Cw p.z hCw.le L p hzγ,
    eventually_exp_rate_absorb 2 (1/(6*Ce)) (1+m-2*p.z) (1-p.sb) 2
      (by norm_num) (by positivity) (by linarith) heZ (by norm_num),
    eventually_exp_rate_absorb 2 cψ (1+p.a-2*p.z) (1-p.sb) 2
      (by norm_num) hcψ (by linarith) heψ (by norm_num),
    eventually_four_failures (1-p.sb) hs, hbudget] with
      n hwtN hgramN hlinN htransN hschedN hpN hsmallN hremN hZrate hψrate hfour hbudgetN
  have hn : 0 < n := by omega
  have hn1 : 1 ≤ n := by omega
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hnR1 : 1 ≤ (n:ℝ) := by exact_mod_cast hn1
  obtain ⟨J, Jrow, hJ, hJrowM, hJrow, hrows, hinfo, hreference⟩ := htransN
  let I := sharpInformation W β hβ p n J
  let B := Cw*(n:ℝ)^(-2*p.gamma)*(Real.log (n:ℝ))^L
  let ε := 200*((paddingDepth (coarseCount p n)+1:ℕ):ℝ)*B
  let η := (n:ℝ)^(-p.z)
  let A := 2*β^2*actualParisiFullSusceptibilityExpected W β (coarseTime p n) +
    Cψ*(coarseMesh p n : ℝ) + η
  let r := Real.exp (-(2*(n:ℝ)^(1-p.sb)))
  have hI : AEMeasurable I (sharpLinkedLaw W β hβ p n) :=
    aemeasurable_information_of_observable _ I
      (fun y => linearEnergy W β hβ (sharpRows W β hβ p n y)) n β hnR.ne'
      hinfo.aemeasurable_fst
      ((measurable_linearEnergy W β hβ p n).comp (measurable_sharpRows W β hβ p n)).aemeasurable
  have h0 : (sharpLinkedLaw W β hβ p n).real
      {y | sharpRows W β hβ p n y ∉ gramGood W β hβ p n} ≤ r := by
    rw [hrows.measureReal_eq (measurableSet_gramGood W β hβ p n).compl]
    exact hgramN
  have h1 : (sharpLinkedLaw W β hβ p n).real
      {y | B < weightedSq W β hβ (sharpRows W β hβ p n y)} ≤ r := by
    rw [hrows.measureReal_eq (measurableSet_lt measurable_const (measurable_weightedSq W β hβ p n))]
    exact hwtN
  have h2 : (sharpLinkedLaw W β hβ p n).real
      {y | (sharpRows W β hβ p n y ∈ gramGood W β hβ p n ∧
        weightedSq W β hβ (sharpRows W β hβ p n y) ≤ B) ∧
          η < |sharpDiscarded W β hβ p n y|} ≤ r := by
    exact (discarded_tail_from_conditional_variance W β hβ p n hn1 Ce B w hCe hsmallN
      (fun y hy => (hlinN.1 y hy).2) hlinN.2).trans hZrate
  have h3 : (sharpLinkedLaw W β hβ p n).real
      {y | Real.log 2 - parisiPressure β + A <
        I y/n - β*linearEnergy W β hβ (sharpRows W β hβ p n y)} ≤ r := by
    rw [identDistrib_real_gt hinfo]
    have ht := hpsi (coarseMesh p n) (coarseCount p n) hschedN.2.1 Jrow hJrow
      n hn η (Real.rpow_pos_of_pos hnR _)
        (Real.rpow_le_one_of_one_le_of_nonpos hnR1 (by linarith))
    have he : cψ*n*η^2/(coarseMesh p n : ℝ) = cψ*(n:ℝ)^(1+p.a-2*p.z) := by
      rw [paperGrowingQueryMeshSize_coe]
      exact row_chernoff_exponent _ p.a p.z cψ hnR
    rw [he] at ht
    simpa only [A, r, coarseTime, readoutTime, add_assoc] using ht.trans hψrate
  have henergy : ∀ y : SharpInput p n,
      sharpRows W β hβ p n y ∈ gramGood W β hβ p n →
      weightedSq W β hβ (sharpRows W β hβ p n y) ≤ B →
      |sharpQueryEnergy W β hβ p n y - linearEnergy W β hβ (sharpRows W β hβ p n y)| ≤ ε := by
    intro y hy hw
    exact (hlinN.1 y hy).1.trans (mul_le_mul_of_nonneg_left hw (by positivity))
  obtain ⟨E, hE, hbad, hbound⟩ := sharp_event_of_four_failures W β hβ p n hn
    I B A ε η r h0 h1 h2 h3 henergy
  have hsmall : A+β*ε+β*η ≤ (n:ℝ)^(-p.kb) := by
    have h1 := mul_le_mul_of_nonneg_left hpN (show 0 ≤ 2*β^2 by positivity)
    have h2 := mul_le_mul_of_nonneg_left hremN hβ0.le
    have hδ : (coarseMesh p n : ℝ) = (n:ℝ)^(-p.a) := paperGrowingQueryMeshSize_coe p.a n
    dsimp only [A]
    rw [hδ]
    change ε ≤ η at hremN
    change β*ε ≤ β*η at h2
    dsimp only [η] at h2 ⊢
    nlinarith
  apply coarse_event_of_sharp_event W β hβ p hbf.le n I hI E hE
    (hbad.trans hfour) hreference
  intro y hy
  calc
    _ ≤ -(n:ℝ)*parisiPressure β + (n:ℝ)*(A+β*ε+β*η) := hbound y hy
    _ ≤ -(n:ℝ)*parisiPressure β + (n:ℝ)*(n:ℝ)^(-p.kb) := by gcongr
    _ = _ := by
      have he : (n:ℝ)*(n:ℝ)^(-p.kb) = (n:ℝ)^(1-p.kb) := by
        calc
          _ = (n:ℝ)^(1:ℝ)*(n:ℝ)^(-p.kb) := by rw [Real.rpow_one]
          _ = _ := by
            simpa only [sub_eq_add_neg] using (Real.rpow_add hnR (1:ℝ) (-p.kb)).symm
      rw [he]

end SKConstants.Completion.N13A
