module

public import SKConstants.GaussianProposalConditionalEntropy

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal NNReal Topology Classical
set_option backward.isDefEq.respectTransparency false

namespace SKConstants

theorem klDiv_map_prod_swap {E X : Type*} [MeasurableSpace E] [MeasurableSpace X]
    (R S : Measure (E × X)) [IsProbabilityMeasure R] [IsProbabilityMeasure S] :
    klDiv (R.map Prod.swap) (S.map Prod.swap) = klDiv R S := by
  exact klDiv_map_measurableEquiv R S MeasurableEquiv.prodComm

theorem klDiv_joint_product_decomposition {E X : Type*}
    [MeasurableSpace E] [MeasurableSpace X] [StandardBorelSpace E] [Nonempty E]
    (R : Measure (E × X)) [IsProbabilityMeasure R]
    (ν : Measure X) [IsProbabilityMeasure ν] :
    klDiv R (R.fst.prod ν) = klDiv R (R.fst.prod R.snd) + klDiv R.snd ν := by
  let σ := (R.map Prod.swap).condKernel
  have hr : R.snd ⊗ₘ σ = R.map Prod.swap := by
    have h := Measure.disintegrate (R.map Prod.swap) (R.map Prod.swap).condKernel
    simpa only [Measure.fst_map_swap] using h
  have h := klDiv_compProd_eq_add R.snd ν σ (Kernel.const X R.fst)
  rw [hr, Measure.compProd_const, Measure.compProd_const] at h
  have hl : klDiv (R.map Prod.swap) (ν.prod R.fst) = klDiv R (R.fst.prod ν) := by
    rw [← Measure.prod_swap]
    exact klDiv_map_prod_swap _ _
  have hh : klDiv (R.map Prod.swap) (R.snd.prod R.fst) =
      klDiv R (R.fst.prod R.snd) := by
    rw [← Measure.prod_swap]
    exact klDiv_map_prod_swap _ _
  rw [hl, hh] at h
  exact h.trans (add_comm _ _)

theorem finiteMeasure_absolutelyContinuous_of_pos_singleton
    {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (μ ν : Measure X) (hν : ∀ x, ν {x} ≠ 0) : μ ≪ ν := by
  apply Measure.AbsolutelyContinuous.mk
  intro A _hA hnull
  have he : A = ∅ := by
    ext x
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hx
    have hle : ν {x} ≤ ν A := measure_mono (show ({x} : Set X) ⊆ A by simpa)
    rw [hnull] at hle
    exact hν x (le_zero_iff.mp hle)
  simp [he]

theorem kernel_mixture_pos_singleton {E X : Type*}
    [MeasurableSpace E] [MeasurableSpace X] [MeasurableSingletonClass X]
    (μ : Measure E) [IsProbabilityMeasure μ] (σ : Kernel E X) [IsMarkovKernel σ]
    (hσ : ∀ z x, σ z {x} ≠ 0) (x : X) : (σ ∘ₘ μ) {x} ≠ 0 := by
  rw [Measure.bind_apply (measurableSet_singleton x) σ.aemeasurable]
  apply ne_of_gt
  rw [lintegral_pos_iff_support (σ.measurable_coe (measurableSet_singleton x))]
  have hs : Function.support (fun z => σ z {x}) = univ := by
    ext z
    simp [Function.mem_support, hσ z x]
  rw [hs, measure_univ]
  norm_num

theorem measurable_klDiv_positive_finite_kernel {E X : Type*}
    [MeasurableSpace E] [MeasurableSpace X] [Fintype X]
    [MeasurableSingletonClass X]
    (σ ν : Kernel E X) [IsMarkovKernel σ] [IsMarkovKernel ν]
    (hσ : ∀ z x, σ z {x} ≠ 0) :
    Measurable (fun z => klDiv (σ z) (ν z)) := by
  classical
  let S : Set E := {z | ∀ x, ν z {x} ≠ 0}
  have hS : MeasurableSet S := by
    change MeasurableSet {z | ∀ x, ν z {x} ≠ 0}
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun x =>
      (measurableSet_eq_fun (ν.measurable_coe (measurableSet_singleton x))
        measurable_zero).compl
  let F : E → ℝ≥0∞ := fun z => ∫⁻ x,
    ENNReal.ofReal (klFun (σ.rnDeriv ν z x).toReal) ∂ν z
  have hF : Measurable F := by
    apply Measurable.lintegral_kernel_prod_right
    exact (continuous_klFun.measurable.comp (σ.measurable_rnDeriv ν).ennreal_toReal).ennreal_ofReal
  have hEq : (fun z => klDiv (σ z) (ν z)) = S.piecewise F (fun _ => ⊤) := by
    funext z
    by_cases hz : z ∈ S
    · rw [Set.piecewise_eq_of_mem S F _ hz,
        klDiv_eq_lintegral_klFun_of_ac
          (finiteMeasure_absolutelyContinuous_of_pos_singleton _ _ hz)]
      apply lintegral_congr_ae
      filter_upwards [Kernel.rnDeriv_eq_rnDeriv_measure (κ := σ) (η := ν) (a := z)]
        with x hx
      rw [hx]
    · rw [Set.piecewise_eq_of_notMem S F _ hz]
      apply klDiv_of_not_ac
      intro hac
      apply hz
      intro x hx
      exact hσ z x (hac hx)
  rw [hEq]
  exact hF.piecewise hS measurable_const

theorem klDiv_kernel_average_decomposition {E X : Type*}
    [MeasurableSpace E] [MeasurableSpace X] [StandardBorelSpace E] [Nonempty E]
    [MeasurableSpace.CountableOrCountablyGenerated E X]
    (μ : Measure E) [IsProbabilityMeasure μ] (σ : Kernel E X) [IsMarkovKernel σ]
    (ν : Measure X) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ z ∂μ, σ z ≪ ν) (hmix : ∀ᵐ z ∂μ, σ z ≪ σ ∘ₘ μ) :
    (∫⁻ z, klDiv (σ z) ν ∂μ) =
      (∫⁻ z, klDiv (σ z) (σ ∘ₘ μ) ∂μ) + klDiv (σ ∘ₘ μ) ν := by
  have h := klDiv_joint_product_decomposition (μ ⊗ₘ σ) ν
  rw [Measure.fst_compProd, Measure.snd_compProd, ← Measure.compProd_const,
    ← Measure.compProd_const,
    klDiv_compProd_same_left_eq_lintegral_ae μ σ (Kernel.const E ν) hν,
    klDiv_compProd_same_left_eq_lintegral_ae μ σ (Kernel.const E (σ ∘ₘ μ)) hmix] at h
  exact h

theorem klDiv_kernel_average_le_comparison_add {E X : Type*}
    [MeasurableSpace E] [MeasurableSpace X] [StandardBorelSpace E] [Nonempty E]
    [MeasurableSpace.CountableOrCountablyGenerated E X]
    (μ : Measure E) [IsProbabilityMeasure μ] (σ : Kernel E X) [IsMarkovKernel σ]
    (ν θ : Measure X) [IsProbabilityMeasure ν] [IsProbabilityMeasure θ]
    (hν : ∀ᵐ z ∂μ, σ z ≪ ν) (hθ : ∀ᵐ z ∂μ, σ z ≪ θ)
    (hmix : ∀ᵐ z ∂μ, σ z ≪ σ ∘ₘ μ) :
    (∫⁻ z, klDiv (σ z) ν ∂μ) ≤
      (∫⁻ z, klDiv (σ z) θ ∂μ) + klDiv (σ ∘ₘ μ) ν := by
  rw [klDiv_kernel_average_decomposition μ σ ν hν hmix]
  have hm : (∫⁻ z, klDiv (σ z) (σ ∘ₘ μ) ∂μ) ≤ ∫⁻ z, klDiv (σ z) θ ∂μ := by
    rw [klDiv_kernel_average_decomposition μ σ θ hθ hmix]
    exact le_add_right le_rfl
  gcongr

theorem reversibleKernel_lintegral_swap {E : Type*} [MeasurableSpace E]
    (γ : Measure E) [IsProbabilityMeasure γ] (κ : Kernel E E) [IsMarkovKernel κ]
    (hrev : (γ ⊗ₘ κ).map Prod.swap = γ ⊗ₘ κ)
    (F : E × E → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ p, F p ∂(γ ⊗ₘ κ)) = ∫⁻ base, ∫⁻ target, F (target, base) ∂κ base ∂γ := by
  calc
    _ = ∫⁻ p, F p.swap ∂(γ ⊗ₘ κ) := by
      rw [← lintegral_map hF measurable_swap, hrev]
    _ = _ := Measure.lintegral_compProd (hF.comp measurable_swap)

theorem reversibleKernel_original_target_KL_le {E X : Type*}
    [MeasurableSpace E] [MeasurableSpace X] [StandardBorelSpace E] [Nonempty E]
    [Fintype X] [MeasurableSingletonClass X]
    (γ : Measure E) [IsProbabilityMeasure γ] (κ : Kernel E E) [IsMarkovKernel κ]
    (hrev : (γ ⊗ₘ κ).map Prod.swap = γ ⊗ₘ κ)
    (σ ν : Kernel E X) [IsMarkovKernel σ] [IsMarkovKernel ν]
    (hσ : ∀ z x, σ z {x} ≠ 0) :
    (∫⁻ p, klDiv (σ p.1) (ν p.2) ∂(γ ⊗ₘ κ)) ≤
      (∫⁻ p, klDiv (σ p.1) (σ p.2) ∂(γ ⊗ₘ κ)) +
        klDiv (γ ⊗ₘ (σ ∘ₖ κ)) (γ ⊗ₘ ν) := by
  by_cases hD : klDiv (γ ⊗ₘ (σ ∘ₖ κ)) (γ ⊗ₘ ν) = ⊤
  · rw [hD, add_top]
    exact le_top
  have hac := (klDiv_ne_top_iff.mp hD).1.kernel_of_compProd
  have hbar : ∀ base x, (σ ∘ₖ κ) base {x} ≠ 0 := by
    intro base x
    exact kernel_mixture_pos_singleton (κ base) σ hσ x
  have htarget : Measurable (fun p : E × E => klDiv (σ p.1) (ν p.2)) :=
    measurable_klDiv_positive_finite_kernel
      (σ.comap Prod.fst measurable_fst) (ν.comap Prod.snd measurable_snd)
      (fun p x => hσ p.1 x)
  have hcompare : Measurable (fun p : E × E => klDiv (σ p.1) (σ p.2)) :=
    measurable_klDiv_positive_finite_kernel
      (σ.comap Prod.fst measurable_fst) (σ.comap Prod.snd measurable_snd)
      (fun p x => hσ p.1 x)
  rw [reversibleKernel_lintegral_swap γ κ hrev _ htarget,
    reversibleKernel_lintegral_swap γ κ hrev _ hcompare,
    klDiv_compProd_same_left_eq_lintegral_ae γ (σ ∘ₖ κ) ν hac]
  have hle : (∫⁻ base, ∫⁻ target, klDiv (σ target) (ν base) ∂κ base ∂γ) ≤
      ∫⁻ base, (∫⁻ target, klDiv (σ target) (σ base) ∂κ base) +
        klDiv ((σ ∘ₖ κ) base) (ν base) ∂γ := by
    apply lintegral_mono_ae
    filter_upwards [hac] with base hb
    have hn : ∀ x, ν base {x} ≠ 0 := by
      intro x hx
      exact hbar base x (hb hx)
    exact klDiv_kernel_average_le_comparison_add (κ base) σ (ν base) (σ base)
      (ae_of_all _ fun z => finiteMeasure_absolutelyContinuous_of_pos_singleton _ _ hn)
      (ae_of_all _ fun z => finiteMeasure_absolutelyContinuous_of_pos_singleton _ _ (hσ base))
      (ae_of_all _ fun z => finiteMeasure_absolutelyContinuous_of_pos_singleton _ _ (hbar base))
  have hcm : Measurable (fun base => ∫⁻ target, klDiv (σ target) (σ base) ∂κ base) :=
    (show Measurable (fun p : E × E => klDiv (σ p.2) (σ p.1)) from
      hcompare.comp measurable_swap).lintegral_kernel_prod_right'
  rw [lintegral_add_left hcm] at hle
  exact hle

end SKConstants
