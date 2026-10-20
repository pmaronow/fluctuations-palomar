module

public import SKConstants.Completion.N13A.Regularity
public import SKConstants.Completion.N13A.Disintegration
public import SKConstants.Completion.Blueprint.ExperimentMeasurable

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology

namespace SKConstants.Completion.N13A
open SKConstantsOAI.ZeroTemperatureSK GaussianProposal Blueprint Blueprint4

variable {Ω : Type} [MeasurableSpace Ω]

attribute [local irreducible] baseField sharpField actualParisiFullMagnetization
  actualParisiGrowingReplayField runMag

def thresholdToSharp (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (y : N13a.CoarseRunInput p n) : SharpInput p n :=
  (thresholdSpin (fun i => actualParisiFullMagnetization β (coarseTime p n)
    (baseField W β hβ p n (coarseTime p n) (y.1,y.2.1) i)) y.2.2, y.1,y.2.1)

theorem measurable_thresholdToSharp (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) : Measurable (thresholdToSharp W β hβ p n) := by
  have hY : Measurable (fun y : N13a.CoarseRunInput p n =>
      baseField W β hβ p n (coarseTime p n) (y.1,y.2.1)) :=
    (measurable_baseField W β hβ p n (coarseTime p n)).comp
    (measurable_fst.prodMk measurable_snd.fst)
  have hM : Measurable (fun y : N13a.CoarseRunInput p n => fun i =>
      actualParisiFullMagnetization β (coarseTime p n)
        (baseField W β hβ p n (coarseTime p n) (y.1,y.2.1) i)) :=
    Measurable.of_eval (fun i => ((continuous_actualParisiFullMagnetization β).measurable.comp
      ((measurable_const (a := (coarseTime p n : ℝ))).prodMk ((measurable_pi_apply i).comp hY))))
  exact ((measurable_thresholdSpin n).comp (hM.prodMk measurable_snd.snd)).prodMk
    (measurable_fst.prodMk measurable_snd.fst)

theorem thresholdToSharp_law (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) :
    ((primLaw n).prod ((replayAuxLaw W (coarseMesh p n) (coarseRank p n) (coarseCount p n)).prod
      (thresholdLaw n))).map (thresholdToSharp W β hβ p n) = sharpLinkedLaw W β hβ p n := by
  rw [← Measure.prodAssoc_prod, Measure.map_map (measurable_thresholdToSharp W β hβ p n)
    MeasurableEquiv.prodAssoc.measurable, sharpLinkedLaw_eq_terminal]
  exact NReplay.threshold_terminalLinkedLaw β (coarseTime p n) _ _
    (measurable_baseField W β hβ p n (coarseTime p n))

def runToSharp (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (hq : coarseCount p n ≤ queryCount p.a p.f n) :
    RunInput p n → SharpInput p n :=
  thresholdToSharp W β hβ p n ∘ N13a.coarsePrefix_runInput p n hq

theorem measurable_runToSharp (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (hq : coarseCount p n ≤ queryCount p.a p.f n) :
    Measurable (runToSharp W β hβ p n hq) :=
  (measurable_thresholdToSharp W β hβ p n).comp (N13a.coarsePrefix_runInput_measurable p n hq)

theorem runToSharp_spin (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (hq : coarseCount p n ≤ queryCount p.a p.f n)
    (y : RunInput p n) :
    (runToSharp W β hβ p n hq y).1 = coarseSpin W β hβ p n y.1 y.2.1 y.2.2 := by
  rw [N13a.coarsePrefix_coarseSpin W β hβ p n hq]
  unfold runToSharp thresholdToSharp N13a.coarsePrefix_runInput baseField sharpField
    sharpReplayInput replaySpinGen replayMag
  rfl

theorem runToSharp_law (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (hq : coarseCount p n ≤ queryCount p.a p.f n) :
    (runLaw W p n).map (runToSharp W β hβ p n hq) = sharpLinkedLaw W β hβ p n := by
  rw [runToSharp, ← Measure.map_map (measurable_thresholdToSharp W β hβ p n)
    (N13a.coarsePrefix_runInput_measurable p n hq), N13a.coarsePrefix_runLaw W p n hq,
    thresholdToSharp_law]

theorem coarse_event_of_sharp_event (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (hbf : p.b ≤ p.f) (n : ℕ)
    (I : SharpInput p n → ℝ) (hI : AEMeasurable I (sharpLinkedLaw W β hβ p n))
    (E : Set (SharpInput p n)) (hE : MeasurableSet E)
    (hbad : (sharpLinkedLaw W β hβ p n).real Eᶜ ≤ Real.exp (-((n:ℝ)^(1-p.sb))))
    (hR : ((sharpLinkedLaw W β hβ p n).withDensity
      (fun y => ENNReal.ofReal (Real.exp (-I y)))).map (fun y => (y.1,y.2.1)) =
        unlinkedPrimitiveSpinFirstLaw n)
    (hbound : ∀ y ∈ E, I y - (n:ℝ)*Real.log 2 -
      β * goeSpinHamiltonian (1 / Real.sqrt (2*(n:ℝ))) y.1 y.2.1 ≤
        -(n:ℝ)*parisiPressure β + (n:ℝ)^(1-p.kb)) :
    ∃ F : Set (RunInput p n), MeasurableSet F ∧
      (runLaw W p n).real Fᶜ ≤ Real.exp (-((n:ℝ)^(1-p.sb))) ∧
      ∀ᵐ g ∂primLaw n, ∀ x : Spin n,
        ((fineAuxLaw W p n).prod (thresholdLaw n)).real
          {u | (g,u) ∈ F ∧ coarseSpin W β hβ p n g u.1 u.2 = x} ≤
            Real.exp (-(n:ℝ)*parisiPressure β + (n:ℝ)^(1-p.kb) +
              β * goeSpinHamiltonian (1 / Real.sqrt (2*(n:ℝ))) x g) := by
  let hq := N13a.coarsePrefix_queryCount p.a p.b p.f hbf n
  let T := runToSharp W β hβ p n hq
  have hT : Measurable T := measurable_runToSharp W β hβ p n hq
  have hTl : (runLaw W p n).map T = sharpLinkedLaw W β hβ p n := runToSharp_law W β hβ p n hq
  refine ⟨T ⁻¹' E, hT hE, ?_, ?_⟩
  · rw [← hTl, measureReal_def, Measure.map_apply hT hE.compl] at hbad
    simpa only [preimage_compl, measureReal_def] using hbad
  · have hdom := intrinsic_restricted_endpoint_domination n β
      (-(n:ℝ)*parisiPressure β + (n:ℝ)^(1-p.kb))
      (sharpLinkedLaw W β hβ p n) I hI (fun y => (y.1,y.2.1))
      (measurable_fst.prodMk measurable_snd.fst) hR E hE hbound
    have hmap : ((runLaw W p n).restrict (T ⁻¹' E)).map
        (fun y => (coarseSpin W β hβ p n y.1 y.2.1 y.2.2,y.1)) =
        ((sharpLinkedLaw W β hβ p n).restrict E).map (fun y => (y.1,y.2.1)) := by
      rw [← hTl, Measure.restrict_map hT hE,
        Measure.map_map (measurable_fst.prodMk measurable_snd.fst) hT]
      congr 1
      funext y
      exact Prod.ext (runToSharp_spin W β hβ p n hq y).symm rfl
    have hF : Measurable (fun y : RunInput p n => coarseSpin W β hβ p n y.1 y.2.1 y.2.2) := by
      convert hT.fst using 1
      funext y
      exact (runToSharp_spin W β hβ p n hq y).symm
    apply intrinsic_kernel_of_endpoint_domination n β
      (-(n:ℝ)*parisiPressure β + (n:ℝ)^(1-p.kb))
      ((fineAuxLaw W p n).prod (thresholdLaw n))
      (fun y => coarseSpin W β hβ p n y.1 y.2.1 y.2.2)
      hF (T ⁻¹' E) (hT hE)
    rw [show (primLaw n).prod ((fineAuxLaw W p n).prod (thresholdLaw n)) = runLaw W p n from rfl,
      hmap]
    exact hdom

end SKConstants.Completion.N13A
