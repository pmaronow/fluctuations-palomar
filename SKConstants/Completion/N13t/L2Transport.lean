module

public import SKConstants.Completion.LC4a.ReplayDIntegral

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace SKConstants.Completion.N13t

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

def IsL2Limit (μ : Measure X) (S : ℕ → X → ℝ) (J : X → ℝ) : Prop :=
  Measurable J ∧ MemLp J 2 μ ∧
    (∀ l, Integrable (fun x => (S l x - J x) ^ 2) μ) ∧
    Tendsto (fun l => ∫ x, (S l x - J x) ^ 2 ∂μ) atTop (𝓝 0)

theorem IsL2Limit.comp_hasLaw {μ : Measure X} {ν : Measure Y} {R : X → Y}
    (hR : HasLaw R ν μ) (hRm : Measurable R) {S : ℕ → Y → ℝ} {J : Y → ℝ}
    (hJ : IsL2Limit ν S J) :
    IsL2Limit μ (fun l x => S l (R x)) (fun x => J (R x)) := by
  refine ⟨hJ.1.comp hRm, hR.memLp_fun_comp hJ.2.1, ?_, ?_⟩
  · intro l
    exact hR.integrable_comp (hJ.2.2.1 l)
  · have he (l : ℕ) : (∫ x, (S l (R x) - J (R x)) ^ 2 ∂μ) =
        ∫ y, (S l y - J y) ^ 2 ∂ν :=
      hR.integral_comp (hJ.2.2.1 l).aestronglyMeasurable
    simp_rw [he]
    exact hJ.2.2.2

theorem IsL2Limit.unique {μ : Measure X} [IsFiniteMeasure μ]
    {S : ℕ → X → ℝ} {I J : X → ℝ}
    (hI : IsL2Limit μ S I) (hJ : IsL2Limit μ S J) : I =ᵐ[μ] J :=
  tendstoInMeasure_ae_unique
    (tendstoInMeasure_of_tendsto_integral_sq hI.2.2.1 hI.2.2.2)
    (tendstoInMeasure_of_tendsto_integral_sq hJ.2.2.1 hJ.2.2.2)

theorem IsL2Limit.congr_sums {μ : Measure X} {S T : ℕ → X → ℝ} {J : X → ℝ}
    (hJ : IsL2Limit μ S J) (hST : ∀ l, S l =ᵐ[μ] T l) : IsL2Limit μ T J := by
  have he (l : ℕ) : (fun x => (S l x - J x) ^ 2) =ᵐ[μ]
      fun x => (T l x - J x) ^ 2 :=
    (hST l).mono (fun x h => by change (S l x - J x) ^ 2 = (T l x - J x) ^ 2; rw [h])
  exact ⟨hJ.1, hJ.2.1, fun l => (hJ.2.2.1 l).congr (he l),
    hJ.2.2.2.congr' (Eventually.of_forall fun l => integral_congr_ae (he l))⟩

theorem IsL2Limit.change_sums {μ : Measure X} {S T : ℕ → X → ℝ} {J : X → ℝ}
    (hJ : IsL2Limit μ S J) (hSm : ∀ l, Measurable (S l)) (hTm : ∀ l, Measurable (T l))
    (hSTi : ∀ l, Integrable (fun x => (S l x - T l x) ^ 2) μ)
    (hST : Tendsto (fun l => ∫ x, (S l x - T l x) ^ 2 ∂μ) atTop (𝓝 0)) :
    IsL2Limit μ T J := by
  have he (l : ℕ) : (fun x => (T l x - J x) ^ 2) =
      fun x => ((S l x - J x) - (S l x - T l x)) ^ 2 := by
    funext x
    ring
  refine ⟨hJ.1, hJ.2.1, ?_, ?_⟩
  · intro l
    rw [he]
    exact integrable_sq_sub ((hSm l).sub hJ.1).aemeasurable
      ((hSm l).sub (hTm l)).aemeasurable (hJ.2.2.1 l) (hSTi l)
  · simp_rw [he]
    exact tendsto_integral_sq_sub
      (fun l => ((hSm l).sub hJ.1).aemeasurable)
      (fun l => ((hSm l).sub (hTm l)).aemeasurable)
      hJ.2.2.1 hSTi hJ.2.2.2 hST

theorem exists_isL2Limit_of_hasLaw
    {μ : Measure X} {ν : Measure Y} {R : X → Y} (hR : HasLaw R ν μ)
    (S : ℕ → Y → ℝ) (hSm : ∀ l, Measurable (S l))
    (I : X → ℝ) (hI : IsL2Limit μ (fun l x => S l (R x)) I) :
    ∃ J, IsL2Limit ν S J := by
  have hmemPull (l : ℕ) : MemLp (fun x => S l (R x)) 2 μ := by
    have hdiff : MemLp (fun x => S l (R x) - I x) 2 μ :=
      (memLp_two_iff_integrable_sq
        (((hSm l).aemeasurable.comp_aemeasurable hR.aemeasurable).sub
          hI.1.aemeasurable).aestronglyMeasurable).mpr (hI.2.2.1 l)
    convert hdiff.add hI.2.1 using 1
    ext x
    simp
  have hmem (l : ℕ) : MemLp (S l) 2 ν := by
    rw [← hR.map_eq]
    exact (memLp_map_measure_iff (hSm l).aestronglyMeasurable hR.aemeasurable).mpr (hmemPull l)
  let F : ℕ → Lp ℝ 2 ν := fun l => (hmem l).toLp (S l)
  have hnorm (l m : ℕ) : dist (F l) (F m) =
      dist ((hmemPull l).toLp (fun x => S l (R x)))
        ((hmemPull m).toLp (fun x => S m (R x))) := by
    have he := hR.integral_comp (((hSm l).sub (hSm m)).pow_const 2).aestronglyMeasurable
    have hsq : dist (F l) (F m) ^ 2 =
        dist ((hmemPull l).toLp (fun x => S l (R x)))
          ((hmemPull m).toLp (fun x => S m (R x))) ^ 2 := by
      simp only [dist_eq_norm]
      rw [norm_toLp_difference_sq_eq_integral (hmem l) (hmem m),
        norm_toLp_difference_sq_eq_integral (hmemPull l) (hmemPull m)]
      exact he.symm
    nlinarith [dist_nonneg (x := F l) (y := F m),
      dist_nonneg (x := (hmemPull l).toLp (fun x => S l (R x)))
        (y := (hmemPull m).toLp (fun x => S m (R x)))]
  have hlim : Tendsto (fun l => (hmemPull l).toLp (fun x => S l (R x))) atTop
      (𝓝 (hI.2.1.toLp I)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hs := hI.2.2.2
    have he (l : ℕ) : ‖(hmemPull l).toLp (fun x => S l (R x)) - hI.2.1.toLp I‖ ^ 2 =
        ∫ x, (S l (R x) - I x) ^ 2 ∂μ :=
      norm_toLp_difference_sq_eq_integral (hmemPull l) hI.2.1
    have hh : Tendsto (fun l => ‖(hmemPull l).toLp (fun x => S l (R x)) - hI.2.1.toLp I‖ ^ 2)
        atTop (𝓝 0) := hs.congr' (Eventually.of_forall fun l => (he l).symm)
    simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hh
  have hc : CauchySeq F := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hlim.cauchySeq ε hε
    exact ⟨N, fun l hl m hm => by rw [hnorm]; exact hN l hl m hm⟩
  obtain ⟨J, hJ⟩ := cauchySeq_tendsto_of_complete hc
  let K := (Lp.memLp J).aestronglyMeasurable.mk (fun y => J y)
  have hJK : (fun y => J y) =ᵐ[ν] K := (Lp.memLp J).aestronglyMeasurable.ae_eq_mk
  refine ⟨K, (Lp.memLp J).aestronglyMeasurable.measurable_mk,
    (Lp.memLp J).ae_eq hJK, ?_, ?_⟩
  · intro l
    exact (((hmem l).sub (Lp.memLp J)).integrable_sq).congr
      (hJK.mono (fun y hy => by
        change J y = K y at hy
        dsimp only [Pi.sub_apply]
        rw [hy]))
  · have hn : Tendsto (fun l => ‖F l - J‖ ^ 2) atTop (𝓝 0) := by
      simpa using ((hJ.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => J) atTop (𝓝 J))).norm).pow 2
    convert hn using 1
    funext l
    calc
      _ = ∫ y, (S l y - J y) ^ 2 ∂ν :=
        integral_congr_ae (hJK.mono (fun y hy => by
          change J y = K y at hy
          change (S l y - K y) ^ 2 = (S l y - J y) ^ 2
          rw [hy]))
      _ = _ := (norm_toLp_sub_sq_eq_integral (hmem l) J).symm

end SKConstants.Completion.N13t
