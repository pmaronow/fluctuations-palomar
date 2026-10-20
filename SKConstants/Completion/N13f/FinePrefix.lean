module

public import SKConstants.Completion.N13a.Node
public import SKConstants.Completion.N13f.RestrictedKernel

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set
open scoped NNReal unitInterval

namespace SKConstants.Completion.N13f
open SKConstantsOAI.ZeroTemperatureSK GaussianProposal Blueprint N13a
variable {Ω : Type*} [MeasurableSpace Ω]

def coarseReadout (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (p : Parameters) (n : ℕ)
    (u : CoarseRunInput p n) : Spin n :=
  replaySpinGen W β hβ (meshSize p.a n) (rankCount p.a p.b n) (queryCount p.a p.b n)
    (rankCount_add p.a p.b n) u.1 u.2.1 u.2.2

theorem measurable_coarseReadout (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) : Measurable (coarseReadout W β hβ p n) := by
  let r := rankCount p.a p.b n
  let k := queryCount p.a p.b n
  have hdim : r+k=n := rankCount_add p.a p.b n
  have hM : Measurable (fun u : CoarseRunInput p n => castMatrix hdim (physical n u.1)) := by
    have hc : Measurable (castMatrix hdim) := by unfold castMatrix; fun_prop
    exact hc.comp ((continuous_goeMatrix (1/Real.sqrt (2*(n : ℝ)))).measurable.comp measurable_fst)
  have hm := (measurable_castVec hdim).comp
    ((measurable_replayMag W β hβ (meshSize p.a n) r k
      (scalarGrowingSourceHorizon (meshSize p.a n) k)).comp
      (hM.prodMk measurable_snd.fst))
  exact (measurable_thresholdSpin n).comp (hm.prodMk measurable_snd.snd)

theorem coarsePrefix_auxThreshold_law (W : BrownianSystem Ω) (p : Parameters) (n : ℕ)
    (hq : queryCount p.a p.b n ≤ queryCount p.a p.f n) :
    (((fineAuxLaw W p n).prod (thresholdLaw n)).map
      (Prod.map (coarsePrefix_fineAux p n hq) id)) =
      (replayAuxLaw W (meshSize p.a n) (rankCount p.a p.b n) (queryCount p.a p.b n)).prod
        (thresholdLaw n) := by
  rw [← Measure.map_prod_map _ _ (coarsePrefix_fineAux_measurable p n hq) measurable_id,
    Measure.map_id, coarsePrefix_fineAux_law W p n hq]

theorem coarsePrefix_event_compl_eq (W : BrownianSystem Ω) (p : Parameters) (n : ℕ)
    (hq : queryCount p.a p.b n ≤ queryCount p.a p.f n)
    (E : Set (CoarseRunInput p n)) (hE : MeasurableSet E) :
    (runLaw W p n).real ((coarsePrefix_runInput p n hq) ⁻¹' E)ᶜ =
      ((primLaw n).prod ((replayAuxLaw W (meshSize p.a n) (rankCount p.a p.b n)
        (queryCount p.a p.b n)).prod (thresholdLaw n))).real Eᶜ := by
  rw [← coarsePrefix_runLaw W p n hq]
  simp only [Measure.real]
  rw [Measure.map_apply (coarsePrefix_runInput_measurable p n hq) hE.compl]
  rfl

theorem coarsePrefix_restrictedKernel_eq
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (p : Parameters) (n : ℕ)
    (hq : queryCount p.a p.b n ≤ queryCount p.a p.f n)
    (E : Set (CoarseRunInput p n)) (hE : MeasurableSet E) (g : Prim n) (x : Spin n) :
    restrictedKernel W β hβ p n ((coarsePrefix_runInput p n hq) ⁻¹' E) g x =
      ((replayAuxLaw W (meshSize p.a n) (rankCount p.a p.b n) (queryCount p.a p.b n)).prod
        (thresholdLaw n)).real {u | (g,u) ∈ E ∧ coarseReadout W β hβ p n (g,u) = x} := by
  have hm : Measurable (Prod.map (coarsePrefix_fineAux p n hq)
      (id : (Fin n → I) → (Fin n → I))) :=
    (coarsePrefix_fineAux_measurable p n hq).prodMap measurable_id
  have hset : MeasurableSet {u | (g,u) ∈ E ∧ coarseReadout W β hβ p n (g,u) = x} :=
    (hE.preimage measurable_prodMk_left).inter
      (((measurable_coarseReadout W β hβ p n).comp measurable_prodMk_left) (measurableSet_singleton x))
  rw [← coarsePrefix_auxThreshold_law W p n hq, Measure.real, Measure.map_apply hm hset]
  unfold restrictedKernel Measure.real
  congr 2
  ext u
  simp only [mem_ofPred_eq, mem_preimage, coarsePrefix_runInput]
  rw [coarsePrefix_coarseSpin W β hβ p n hq]
  rfl

end SKConstants.Completion.N13f
