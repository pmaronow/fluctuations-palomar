module

public import SKConstants.Completion.Blueprint.Nodes
public import SKConstants.Completion.Blueprint.ExperimentMeasurable

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set InformationTheory
open scoped NNReal ENNReal Topology unitInterval
set_option backward.isDefEq.respectTransparency false

namespace SKConstants.Blueprint
open SKConstantsOAI.ZeroTemperatureSK GaussianProposal

variable {Ω : Type*} [MeasurableSpace Ω]

attribute [local irreducible] runMag

theorem selectedEnlargedBoundary_subset_excludedSet (β : ℝ) (p : Parameters) (n : ℕ)
    (G : Prim n)
    (hP : primitiveGOEPressure n β G ≤ (n : ℝ) * parisiPressure β + (n : ℝ) ^ (1 - p.zP)) :
    selectedEnlargedBoundary β ((n : ℝ) ^ (-p.d)) (Real.exp (-((n : ℝ) ^ (1 - p.q)))) 12
        (hammingRadius p n) (physical n G) ⊆ excludedSet β p n G := by
  unfold excludedSet pressureSelectedSparseBoundary
  rw [ite_eq_left_iff.mpr (fun h => absurd hP h)]
  unfold selectedSparseBoundary selectedEnlargedBoundary
  cases h : selectedLowFlowCutWithinNorm β ((n : ℝ) ^ (-p.d))
      (Real.exp (-((n : ℝ) ^ (1 - p.q)))) 12 (physical n G) with
  | none => simp
  | some S =>
    intro x hx
    simp only [Option.elim_some] at hx ⊢
    exact Finset.mem_union_left _ hx

theorem endpoint_masses_of_klDiv (n : ℕ) (β : ℝ) (G : Prim n) (ν : Measure (Spin n))
    [IsProbabilityMeasure ν] (t : ℝ) (ht : 0 ≤ t)
    (hKL : klDiv (primitiveGibbsSpinKernel n β (1 / Real.sqrt (2 * (n : ℝ))) G) ν ≤
      ENNReal.ofReal t) :
    (∀ x, 0 < ν.real {x}) ∧
      finiteKL (gibbsProbability β (physical n G)) (fun x => ν.real {x}) ≤ t := by
  let μ := primitiveGibbsSpinKernel n β (1 / Real.sqrt (2 * (n : ℝ))) G
  have hac : μ ≪ ν := (klDiv_ne_top_iff.mp (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hKL)).1
  have hp : ∀ x, 0 < μ.real {x} := fun x =>
    ENNReal.toReal_pos (primitiveGibbsSpinKernel_pos_singleton n β _ G x) (measure_ne_top _ _)
  have hq : ∀ x, 0 < ν.real {x} := by
    intro x
    apply ENNReal.toReal_pos _ (measure_ne_top _ _)
    intro hx
    exact primitiveGibbsSpinKernel_pos_singleton n β _ G x (hac hx)
  refine ⟨hq, ?_⟩
  have h := finite_endpoint_KL_le μ ν id measurable_id (fun v => by simpa using hp v)
    (fun v => by simpa using hq v) t ht hKL
  have hμ : (fun v => μ.real (id ⁻¹' {v})) = gibbsProbability β (physical n G) := by
    funext v
    simp only [Set.preimage_id, measureReal_def, μ, primitiveGibbsSpinKernel_singleton]
    exact ENNReal.toReal_ofReal (gibbsProbability_pos _ _ _).le
  have hν : (fun v => ν.real (id ⁻¹' {v})) = fun x => ν.real {x} := by
    funext v
    simp
  rw [hμ, hν] at h
  exact h

theorem gridAngle_zero (p : Parameters) (n : ℕ) : gridAngle p n 0 = 0 := by
  simp [gridAngle]

theorem crossing_lower_bound (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (p : Parameters)
    (n : ℕ) (hn : 0 < n) (o : Outer n)
    (hWit : physical n o.1 ∈ lowFlowWitnessEvent β ((n : ℝ) ^ (-p.d))
      (Real.exp (-((n : ℝ) ^ (1 - p.q)))) 12)
    (hP : primitiveGOEPressure n β o.1 ≤ (n : ℝ) * parisiPressure β + (n : ℝ) ^ (1 - p.zP))
    (t : ℝ) (ht : 0 ≤ t)
    (hKL : actualProposalOriginalTargetKL n β (fineProposal W β hβ p n) (smoothing p n) o ≤
      ENNReal.ofReal t)
    (hind : IndepFun (fun ω => pathSpin W β hβ p n o ω 0)
        (fun ω => pathSpin W β hβ p n o ω (gridSize p n + 2)) (internalLaw W p n))
    (hX : ∀ x, (internalLaw W p n).real {ω | pathSpin W β hβ p n o ω 0 = x} =
        (endpointKernel W β hβ p n (baseMatrix p n o)).real {x})
    (hY : ∀ x, (internalLaw W p n).real {ω | pathSpin W β hβ p n o ω (gridSize p n + 2) = x} =
        (endpointKernel W β hβ p n (baseMatrix p n o)).real {x}) :
    Real.exp (-2 * (t + Real.log 2) / (n : ℝ) ^ (-p.d)) ≤
      (internalLaw W p n).real (goodEvent W β hβ p n o)ᶜ := by
  have hε : 0 < (n : ℝ) ^ (-p.d) := Real.rpow_pos_of_pos (by exact_mod_cast hn) _
  obtain ⟨hq, hfin⟩ := endpoint_masses_of_klDiv n β o.1
    (endpointKernel W β hβ p n (baseMatrix p n o)) t ht hKL
  have hsum : ∑ x, (endpointKernel W β hβ p n (baseMatrix p n o)).real {x} = 1 := by
    have h := finite_endpoint_probability_sum
      (endpointKernel W β hβ p n (baseMatrix p n o)) id measurable_id
    simpa only [Set.preimage_id] using h
  have hmain := probability_selectedLowFlowCut_coarse_avoidance_bad_mass (internalLaw W p n) β
    ((n : ℝ) ^ (-p.d)) (Real.exp (-((n : ℝ) ^ (1 - p.q)))) 12 (physical n o.1) hWit
    (fun x => (endpointKernel W β hβ p n (baseMatrix p n o)).real {x})
    (pathSpin W β hβ p n o) (fun _ i => 1 ≤ i ∧ i ≤ gridSize p n + 1)
    (goodEvent W β hβ p n o) (gridSize p n + 2) (hammingRadius p n) t hε hq hsum hfin
    (measurable_pathSpin_internal W β hβ p n o 0)
    (measurable_pathSpin_internal W β hβ p n o _) hind hX hY
    (measurableSet_goodEvent W β hβ p n o)
    (fun ω hω i hi => hω.1 i hi)
    (fun ω _ i hi => by omega)
    (fun ω hω i hi hc => by
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      intro hmem
      exact hω.2 j (by omega) (selectedEnlargedBoundary_subset_excludedSet β p n o.1 hP hmem))
  exact hmain.1

theorem outer_measureReal_le_of_pointwise (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (T : Set (Outer n)) (hT : MeasurableSet T) (c : ℝ)
    (hpt : ∀ o ∈ T, Real.exp (-c) ≤ (internalLaw W p n).real (goodEvent W β hβ p n o)ᶜ) :
    (outerLaw n).real T ≤
      Real.exp c * (experimentLaw W p n).real {z | z.2 ∉ goodEvent W β hβ p n z.1} := by
  set Bad := {z : Outer n × Internal p n | z.2 ∉ goodEvent W β hβ p n z.1}
  have hBad : MeasurableSet Bad := (measurableSet_goodEvent_joint W β hβ p n).compl
  have hprod : experimentLaw W p n Bad =
      ∫⁻ o, internalLaw W p n (goodEvent W β hβ p n o)ᶜ ∂outerLaw n := by
    rw [experimentLaw, Measure.prod_apply hBad]
    rfl
  have hle : ENNReal.ofReal (Real.exp (-c)) * outerLaw n T ≤ experimentLaw W p n Bad := by
    rw [hprod, ← setLIntegral_const]
    calc ∫⁻ _ in T, ENNReal.ofReal (Real.exp (-c)) ∂outerLaw n
        ≤ ∫⁻ o in T, internalLaw W p n (goodEvent W β hβ p n o)ᶜ ∂outerLaw n := by
          apply setLIntegral_mono' hT
          intro o ho
          rw [ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)]
          exact hpt o ho
      _ ≤ ∫⁻ o, internalLaw W p n (goodEvent W β hβ p n o)ᶜ ∂outerLaw n :=
          setLIntegral_le_lintegral _ _
  have hreal : Real.exp (-c) * (outerLaw n).real T ≤ (experimentLaw W p n).real Bad := by
    have h := ENNReal.toReal_mono (measure_ne_top _ _) hle
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le] at h
    exact h
  have he : Real.exp c * Real.exp (-c) = 1 := by rw [← Real.exp_add]; simp
  calc (outerLaw n).real T = Real.exp c * (Real.exp (-c) * (outerLaw n).real T) := by
        rw [← mul_assoc, he, one_mul]
    _ ≤ Real.exp c * (experimentLaw W p n).real Bad :=
        mul_le_mul_of_nonneg_left hreal (Real.exp_pos _).le

theorem tendsto_natCast_rpow_zero (x : ℝ) (hx : x < 0) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ x) atTop (𝓝 0) := by
  have h := (tendsto_rpow_neg_atTop (show 0 < -x by linarith)).comp tendsto_natCast_atTop_atTop
  simpa only [Function.comp_def, neg_neg] using h

theorem crossing_exponent_eventually (uE d s : ℝ) (h1 : 1 - uE + d < 1 - s) (h2 : d < 1 - s) :
    ∀ᶠ n : ℕ in atTop, 2 * ((n : ℝ) ^ (1 - uE) + Real.log 2) / (n : ℝ) ^ (-d) -
      (n : ℝ) ^ (1 - s) ≤ -(1 / 2) * (n : ℝ) ^ (1 - s) := by
  filter_upwards [two_rpow_le_small_rpow (1 - uE + d) d (1 - s) 2 (2 * Real.log 2) (1 / 2) h1 h2
    (by norm_num) (by positivity) (by norm_num), eventually_ge_atTop 1] with n h hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have he : 2 * ((n : ℝ) ^ (1 - uE) + Real.log 2) / (n : ℝ) ^ (-d) =
      2 * (n : ℝ) ^ (1 - uE + d) + 2 * Real.log 2 * (n : ℝ) ^ d := by
    rw [Real.rpow_neg hnR.le, div_inv_eq_mul, Real.rpow_add hnR]
    ring
  rw [he]
  linarith

theorem coverage_bound_le (β D uE kf Cp : ℝ) (hCp : 0 ≤ Cp) (n : ℕ) (hn : 1 ≤ n) :
    ((n : ℝ) ^ (-D) * (β ^ 2 * ((n : ℝ) - 1) / 2) + Cp * (n : ℝ) ^ (1 - kf) / (n : ℝ) ^ (-D)) /
        (n : ℝ) ^ (1 - uE) ≤
      β ^ 2 / 2 * (n : ℝ) ^ (uE - D) + Cp * (n : ℝ) ^ (uE - kf + D) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have ht : 0 < (n : ℝ) ^ (1 - uE) := Real.rpow_pos_of_pos hnR _
  have h1 : (n : ℝ) ^ (-D) * (β ^ 2 * ((n : ℝ) - 1) / 2) ≤
      (n : ℝ) ^ (-D) * (β ^ 2 * (n : ℝ) / 2) := by
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hnR.le _)
    have := sq_nonneg β
    nlinarith
  have e1 : (n : ℝ) ^ (-D) * (β ^ 2 * (n : ℝ) / 2) / (n : ℝ) ^ (1 - uE) =
      β ^ 2 / 2 * (n : ℝ) ^ (uE - D) := by
    have : (n : ℝ) ^ (uE - D) = (n : ℝ) ^ (-D) * (n : ℝ) ^ (1 : ℝ) / (n : ℝ) ^ (1 - uE) := by
      rw [← Real.rpow_add hnR, ← Real.rpow_sub hnR]
      congr 1
      ring
    rw [this, Real.rpow_one]
    ring
  have e2 : Cp * (n : ℝ) ^ (1 - kf) / (n : ℝ) ^ (-D) / (n : ℝ) ^ (1 - uE) =
      Cp * (n : ℝ) ^ (uE - kf + D) := by
    have : (n : ℝ) ^ (uE - kf + D) = (n : ℝ) ^ (1 - kf) / (n : ℝ) ^ (-D) / (n : ℝ) ^ (1 - uE) := by
      rw [← Real.rpow_sub hnR, ← Real.rpow_sub hnR]
      congr 1
      ring
    rw [this]
    ring
  rw [add_div, e2]
  have := div_le_div_of_nonneg_right h1 ht.le
  rw [e1] at this
  linarith

theorem measurable_primitiveGOEPressure (n : ℕ) (β : ℝ) :
    Measurable (primitiveGOEPressure n β) :=
  (((continuous_gibbsPartition β).comp (continuous_goeMatrix _)).log
    (fun z => (gibbsPartition_pos β _).ne')).measurable

theorem witness_decay_of_top_nodes (p : Parameters) (sseq : ℝ)
    (hFine : FineKLStatement) (hEnd : EndpointLawStatement) (hSeq : SequenceGoodStatement)
    (hfe : FineExponents p) (hce : CoarseExponents p) (hbe : BoundaryExponents p)
    (hse : SequenceExponents p sseq) (hcov : CoverageExponents p sseq)
    {Ω : Type} [MeasurableSpace Ω] (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) :
    Tendsto (fun n : ℕ => (skDisorderLaw n).real (lowFlowWitnessEvent β ((n : ℝ) ^ (-p.d))
      (Real.exp (-((n : ℝ) ^ (1 - p.q)))) 12)) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := hFine p hfe W β hβ
  have hE := hEnd p W β hβ
  have hS := hSeq p sseq hfe hce hbe hse W β hβ
  obtain ⟨hd, heu, huD, hukf, hse', hds⟩ := hcov
  have hzP : p.zP < 1 / 2 := hse.2.2.2.2.2.2.2.2.2.2.1
  have hD : 0 < p.D := hse.2.2.2.2.2.2.2.2.2.2.2
  set Cp := max C 0 with hCp_def
  have hCp : 0 ≤ Cp := le_max_right _ _
  let b1 : ℕ → ℝ := fun n => β ^ 2 / 2 * (n : ℝ) ^ (p.uEnt - p.D) +
    Cp * (n : ℝ) ^ (p.uEnt - p.kf + p.D)
  let b2 : ℕ → ℝ := fun n => (primLaw n).real (parisiPressureUpperEvent n β p.zP)
  let b3 : ℕ → ℝ := fun n => Real.exp (-(1 / 2) * (n : ℝ) ^ (1 - sseq))
  have hb1 : Tendsto b1 atTop (𝓝 0) := by
    have h1 := tendsto_natCast_rpow_zero (p.uEnt - p.D) (by linarith)
    have h2 := tendsto_natCast_rpow_zero (p.uEnt - p.kf + p.D) (by linarith)
    simpa using (h1.const_mul (β ^ 2 / 2)).add (h2.const_mul Cp)
  have hb2 : Tendsto b2 atTop (𝓝 0) :=
    parisiPressureUpperEvent_probability_tendsto_zero β p.zP (by linarith) hzP
  have hb3 : Tendsto b3 atTop (𝓝 0) := by
    have h := (polynomial_stretched_decay (1 - sseq) 0 (1 / 2) (by linarith) (by norm_num)).comp
      tendsto_natCast_atTop_atTop
    simpa only [Function.comp_def, Real.rpow_zero, one_mul, b3, neg_mul] using h
  have hlim : Tendsto (fun n => b1 n + b2 n + b3 n) atTop (𝓝 0) := by
    simpa using (hb1.add hb2).add hb3
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _ hlim
  filter_upwards [hC, hE, hS, eventually_ge_atTop 2,
    crossing_exponent_eventually p.uEnt p.d sseq (by linarith) hds] with n hCn hEn hSn hn2 hcross
  obtain ⟨hspin, hgauss, hkl⟩ := hCn
  have hn : 0 < n := by omega
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn2
  have hn0R : (0 : ℝ) < n := by linarith
  set t : ℝ := (n : ℝ) ^ (1 - p.uEnt) with ht_def
  have ht : 0 < t := Real.rpow_pos_of_pos hn0R _
  set K : ℝ := Cp * (n : ℝ) ^ (1 - p.kf) with hK_def
  have hK : 0 ≤ K := mul_nonneg hCp (Real.rpow_nonneg hn0R.le _)
  have hforward : klDiv (fineProposal W β hβ p n)
      ((primitiveJointGibbsLaw n β (1 / Real.sqrt (2 * (n : ℝ)))).map Prod.swap) ≤
      ENNReal.ofReal K := hkl.trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hn0R.le _)))
  have hδval : ((smoothing p n : ℝ≥0) : ℝ) = (n : ℝ) ^ (-p.D) := by
    unfold smoothing
    exact Real.coe_toNNReal _ (Real.rpow_nonneg hn0R.le _)
  have hδ0 : smoothing p n ≠ 0 := by
    intro h
    have := congrArg (fun x : ℝ≥0 => (x : ℝ)) h
    simp only [hδval, NNReal.coe_zero] at this
    exact (Real.rpow_pos_of_pos hn0R (-p.D)).ne' this
  have hδ1 : smoothing p n < 1 := by
    rw [← NNReal.coe_lt_coe, hδval, NNReal.coe_one]
    exact Real.rpow_lt_one_of_one_lt_of_neg hnR (by linarith)
  let Wit : Set (Prim n) := {G | physical n G ∈ lowFlowWitnessEvent β ((n : ℝ) ^ (-p.d))
    (Real.exp (-((n : ℝ) ^ (1 - p.q)))) 12}
  have hWit : MeasurableSet Wit :=
    (measurableSet_lowFlowWitnessEvent _ _ _ _).preimage (continuous_goeMatrix _).measurable
  let Pg : Set (Prim n) := {G | primitiveGOEPressure n β G ≤
    (n : ℝ) * parisiPressure β + (n : ℝ) ^ (1 - p.zP)}
  have hPg : MeasurableSet Pg :=
    measurableSet_le (measurable_primitiveGOEPressure n β) measurable_const
  let KLbad : Set (Outer n) := {o | ENNReal.ofReal t ≤
    actualProposalOriginalTargetKL n β (fineProposal W β hβ p n) (smoothing p n) o}
  let T : Set (Outer n) := {o | o.1 ∈ Wit ∧ o.1 ∈ Pg ∧
    actualProposalOriginalTargetKL n β (fineProposal W β hβ p n) (smoothing p n) o ≤
      ENNReal.ofReal t}
  have hKLm := measurable_actualProposalOriginalTargetKL n β (fineProposal W β hβ p n)
    (smoothing p n)
  have hT : MeasurableSet T :=
    (hWit.preimage measurable_fst).inter ((hPg.preimage measurable_fst).inter
      (measurableSet_le hKLm measurable_const))
  have hwit_eq : (skDisorderLaw n).real (lowFlowWitnessEvent β ((n : ℝ) ^ (-p.d))
      (Real.exp (-((n : ℝ) ^ (1 - p.q)))) 12) = (outerLaw n).real (Wit ×ˢ univ) := by
    rw [measureReal_def, measureReal_def, outerLaw, Measure.prod_prod, measure_univ, mul_one]
    unfold skDisorderLaw
    rw [Nat.cast_ofNat, Measure.map_apply (continuous_goeMatrix _).measurable
      (measurableSet_lowFlowWitnessEvent _ _ _ _)]
    rfl
  have hcover : Wit ×ˢ (univ : Set (Prim n)) ⊆ KLbad ∪ (Pgᶜ ×ˢ univ) ∪ T := by
    intro o ho
    by_cases h1 : ENNReal.ofReal t ≤
        actualProposalOriginalTargetKL n β (fineProposal W β hβ p n) (smoothing p n) o
    · exact Or.inl (Or.inl h1)
    · by_cases h2 : o.1 ∈ Pg
      · exact Or.inr ⟨ho.1, h2, (lt_of_not_ge h1).le⟩
      · exact Or.inl (Or.inr ⟨h2, trivial⟩)
  have hterm1 : (outerLaw n).real KLbad ≤ b1 n := by
    have h := actualProposal_original_target_KL_tail hn β (fineProposal W β hβ p n) hspin hgauss
      (smoothing p n) hδ0 hδ1 K hK hforward t ht
    have hA : 0 ≤ (smoothing p n : ℝ) * (β ^ 2 * ((n : ℝ) - 1) / 2) +
        K / (smoothing p n : ℝ) := by
      have : (0 : ℝ) ≤ (n : ℝ) - 1 := by linarith
      positivity
    have hreal := ENNReal.toReal_mono (ENNReal.div_ne_top ENNReal.ofReal_ne_top
      (ENNReal.ofReal_ne_zero_iff.mpr ht)) h
    rw [ENNReal.toReal_div, ENNReal.toReal_ofReal hA, ENNReal.toReal_ofReal ht.le] at hreal
    refine hreal.trans ?_
    rw [hδval]
    exact coverage_bound_le β p.D p.uEnt p.kf Cp hCp n (by omega)
  have hterm2 : (outerLaw n).real (Pgᶜ ×ˢ univ) ≤ b2 n := by
    rw [measureReal_def, outerLaw, Measure.prod_prod, measure_univ, mul_one]
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono
    intro G hG
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le, Pg] at hG
    exact hG.le
  have hterm3 : (outerLaw n).real T ≤ b3 n := by
    have hpt : ∀ o ∈ T, Real.exp (-(2 * (t + Real.log 2) / (n : ℝ) ^ (-p.d))) ≤
        (internalLaw W p n).real (goodEvent W β hβ p n o)ᶜ := by
      intro o ho
      obtain ⟨hind, hX, hY⟩ := hEn o
      have h := crossing_lower_bound W β hβ p n hn o ho.1 ho.2.1 t ht.le ho.2.2 hind hX hY
      convert h using 2
      ring
    have h := outer_measureReal_le_of_pointwise W β hβ p n T hT _ hpt
    refine h.trans ?_
    calc Real.exp (2 * (t + Real.log 2) / (n : ℝ) ^ (-p.d)) *
          (experimentLaw W p n).real {z | z.2 ∉ goodEvent W β hβ p n z.1}
        ≤ Real.exp (2 * (t + Real.log 2) / (n : ℝ) ^ (-p.d)) *
          Real.exp (-((n : ℝ) ^ (1 - sseq))) :=
          mul_le_mul_of_nonneg_left hSn (Real.exp_pos _).le
      _ = Real.exp (2 * (t + Real.log 2) / (n : ℝ) ^ (-p.d) - (n : ℝ) ^ (1 - sseq)) := by
          rw [← Real.exp_add]
          ring_nf
      _ ≤ b3 n := Real.exp_le_exp.mpr hcross
  rw [hwit_eq]
  calc (outerLaw n).real (Wit ×ˢ univ)
      ≤ (outerLaw n).real (KLbad ∪ (Pgᶜ ×ˢ univ) ∪ T) := measureReal_mono hcover
    _ ≤ (outerLaw n).real (KLbad ∪ (Pgᶜ ×ˢ univ)) + (outerLaw n).real T :=
        measureReal_union_le _ _
    _ ≤ (outerLaw n).real KLbad + (outerLaw n).real (Pgᶜ ×ˢ univ) + (outerLaw n).real T := by
        gcongr
        exact measureReal_union_le _ _
    _ ≤ b1 n + b2 n + b3 n := by linarith

end SKConstants.Blueprint
