module

public import SKConstants.Completion.N13a.FieldPrefix
public import SKConstants.Completion.N13a.AuxRestriction

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open SKConstantsOAI.ZeroTemperatureSK
open scoped NNReal unitInterval
namespace SKConstants.N13a
open GaussianProposal Blueprint
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
variable {Ω : Type*} [MeasurableSpace Ω]

attribute [local irreducible] runMag actualParisiGrowingReplayField
  actualParisiFullScalarDrift actualParisiFullMagnetization
  actualParisiFullSusceptibilitySquareExpected actualParisiNegativeRhoStieltjes
  actualParisiSigmaStieltjes

theorem coarsePrefix_queryCount (a b f : ℝ) (hbf : b ≤ f) (n : ℕ) :
    queryCount a b n ≤ queryCount a f n := by
  have hs : stopIndex a b n ≤ stopIndex a f n := by
    by_cases hn : 0 < n
    · simp only [stopIndex, dite_eq_left hn]
      have hH : paperGrowingQueryHorizon b n ≤ paperGrowingQueryHorizon f n :=
        Real.toNNReal_mono (mul_le_mul_of_nonneg_right hbf
          (Real.log_nonneg (by exact_mod_cast hn)))
      unfold paperGrowingQueryStop growingQueryStop
      exact Nat.find_mono (fun j hj => hH.trans hj)
    · simp [stopIndex, hn]
  exact min_le_min (Nat.sub_le_sub_right hs 1) le_rfl

theorem coarsePrefix_replayMag (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (rf qf rb qb : ℕ) (hdim : rf+qf=rb+qb) (hq : qb ≤ qf)
    (M : Matrix (Fin (rf+qf)) (Fin (rf+qf)) ℝ) (a : ReplayAux δ rf qf)
    (t : ℝ≥0) (ht : t ≤ scalarGrowingSourceHorizon δ qb) :
    replayMag W β hβ δ rb qb t (castMatrix hdim.symm M)
      (coarsePrefix_replayAux δ rf qf rb qb hdim hq a) =
      fun i => replayMag W β hβ δ rf qf t M a (Fin.cast hdim.symm i) := by
  have he := coarsePrefix_replayField W β hβ δ rf qf rb qb hdim hq (replayInput M a) t ht
  rw [coarsePrefix_input_replayInput] at he
  funext i
  exact congrArg (actualParisiFullMagnetization β t) (congrFun he i)

theorem coarsePrefix_dimension (p : Parameters) (n : ℕ) :
    rankCount p.a p.f n + queryCount p.a p.f n =
      rankCount p.a p.b n + queryCount p.a p.b n :=
  (rankCount_add p.a p.f n).trans (rankCount_add p.a p.b n).symm

abbrev CoarseAux (p : Parameters) (n : ℕ) :=
  ReplayAux (meshSize p.a n) (rankCount p.a p.b n) (queryCount p.a p.b n)

def coarsePrefix_fineAux (p : Parameters) (n : ℕ)
    (hq : queryCount p.a p.b n ≤ queryCount p.a p.f n) : FineAux p n → CoarseAux p n :=
  coarsePrefix_replayAux (meshSize p.a n) (rankCount p.a p.f n) (queryCount p.a p.f n)
    (rankCount p.a p.b n) (queryCount p.a p.b n) (coarsePrefix_dimension p n) hq

theorem coarsePrefix_fineAux_measurable (p : Parameters) (n : ℕ)
    (hq : queryCount p.a p.b n ≤ queryCount p.a p.f n) :
    Measurable (coarsePrefix_fineAux p n hq) :=
  coarsePrefix_replayAux_measurable _ _ _ _ _ _ _

theorem coarsePrefix_fineAux_law (W : BrownianSystem Ω) (p : Parameters) (n : ℕ)
    (hq : queryCount p.a p.b n ≤ queryCount p.a p.f n) :
    (fineAuxLaw W p n).map (coarsePrefix_fineAux p n hq) =
      replayAuxLaw W (meshSize p.a n) (rankCount p.a p.b n) (queryCount p.a p.b n) :=
  coarsePrefix_replayAux_law W _ _ _ _ _ _ _

abbrev CoarseRunInput (p : Parameters) (n : ℕ) := Prim n × CoarseAux p n × (Fin n → I)

def coarsePrefix_runInput (p : Parameters) (n : ℕ)
    (hq : queryCount p.a p.b n ≤ queryCount p.a p.f n) : RunInput p n → CoarseRunInput p n :=
  fun y => (y.1,coarsePrefix_fineAux p n hq y.2.1,y.2.2)

theorem coarsePrefix_runInput_measurable (p : Parameters) (n : ℕ)
    (hq : queryCount p.a p.b n ≤ queryCount p.a p.f n) :
    Measurable (coarsePrefix_runInput p n hq) :=
  measurable_fst.prodMk (((coarsePrefix_fineAux_measurable p n hq).comp
    measurable_snd.fst).prodMk measurable_snd.snd)

theorem coarsePrefix_runLaw (W : BrownianSystem Ω) (p : Parameters) (n : ℕ)
    (hq : queryCount p.a p.b n ≤ queryCount p.a p.f n) :
    (runLaw W p n).map (coarsePrefix_runInput p n hq) =
      (primLaw n).prod ((replayAuxLaw W (meshSize p.a n)
        (rankCount p.a p.b n) (queryCount p.a p.b n)).prod (thresholdLaw n)) := by
  change ((primLaw n).prod ((fineAuxLaw W p n).prod (thresholdLaw n))).map
    (Prod.map id (Prod.map (coarsePrefix_fineAux p n hq) id)) = _
  rw [← Measure.map_prod_map _ _ measurable_id
    ((coarsePrefix_fineAux_measurable p n hq).prodMap measurable_id),
    ← Measure.map_prod_map _ _ (coarsePrefix_fineAux_measurable p n hq) measurable_id,
    Measure.map_id, Measure.map_id, coarsePrefix_fineAux_law W p n hq]

theorem coarsePrefix_runMag (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (hq : queryCount p.a p.b n ≤ queryCount p.a p.f n)
    (g : Prim n) (a : FineAux p n) (t : ℝ≥0) (ht : t ≤ readoutTime p.a p.b n) :
    runMag W β hβ p n t g a =
      castVec (rankCount_add p.a p.b n)
        (replayMag W β hβ (meshSize p.a n) (rankCount p.a p.b n) (queryCount p.a p.b n) t
          (castMatrix (rankCount_add p.a p.b n) (physical n g)) (coarsePrefix_fineAux p n hq a)) := by
  have he := coarsePrefix_replayMag W β hβ (meshSize p.a n)
    (rankCount p.a p.f n) (queryCount p.a p.f n)
    (rankCount p.a p.b n) (queryCount p.a p.b n) (coarsePrefix_dimension p n) hq
    (castMatrix (rankCount_add p.a p.f n) (physical n g)) a t ht
  have hM : castMatrix (coarsePrefix_dimension p n).symm
      (castMatrix (rankCount_add p.a p.f n) (physical n g)) =
      castMatrix (rankCount_add p.a p.b n) (physical n g) := rfl
  rw [hM] at he
  unfold runMag
  funext i
  dsimp only [castVec, coarsePrefix_fineAux]
  exact (congrFun he (Fin.cast (rankCount_add p.a p.b n).symm i)).symm

theorem coarsePrefix_coarseSpin (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (hq : queryCount p.a p.b n ≤ queryCount p.a p.f n)
    (g : Prim n) (a : FineAux p n) (U : Fin n → I) :
    coarseSpin W β hβ p n g a U =
      replaySpinGen W β hβ (meshSize p.a n) (rankCount p.a p.b n) (queryCount p.a p.b n)
        (rankCount_add p.a p.b n) g (coarsePrefix_fineAux p n hq a) U := by
  unfold coarseSpin coarseMag replaySpinGen
  rw [coarsePrefix_runMag W β hβ p n hq g a (readoutTime p.a p.b n) le_rfl]
  rfl

end SKConstants.N13a
