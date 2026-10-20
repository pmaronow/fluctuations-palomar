module

public import SKConstants.Completion.N13a.RunPrefix
public import SKConstants.Completion.N13a.Restriction

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open SKConstantsOAI.ZeroTemperatureSK
open scoped NNReal
namespace SKConstants.N13a
open GaussianProposal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
variable {Ω : Type*} [MeasurableSpace Ω]

def coarsePrefix_field (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r q n : ℕ) (hn : r+q=n) (t : ℝ≥0) (x : PrefixInput δ n q) : Fin n → ℝ :=
  fun i => actualParisiGrowingReplayField W β hβ δ r q t
    (coarsePrefix_castInput δ q hn.symm x) (Fin.cast hn.symm i)

theorem coarsePrefix_field_eq_run (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r q n : ℕ) (hn : r+q=n) (t : ℝ≥0) (x : PrefixInput δ n q) :
    coarsePrefix_field W β hβ δ r q n hn t x =
      fun i => scalarMeshPaperObservation (actualParisiFullScalarDrift β)
        (actualParisiNegativeRhoStieltjes W β hβ) (actualParisiSigmaStieltjes W β hβ)
        (continuous_actualParisiNegativeRhoStieltjes W β hβ)
        (continuous_actualParisiSigmaStieltjes W β hβ)
        (scalarGrowingSourceHorizon δ q) (growingQueryDuration δ) (growingQueryTime δ) n
        (paperMatrixQueryRun r n (n : ℝ)
          (scalarGrowingPaperTarget (actualParisiFullScalarDrift β)
            (actualParisiNegativeRhoStieltjes W β hβ) (actualParisiSigmaStieltjes W β hβ)
            (continuous_actualParisiNegativeRhoStieltjes W β hβ)
            (continuous_actualParisiSigmaStieltjes W β hβ)
            (actualParisiFullMagnetization β) (actualParisiFullSusceptibilitySquareExpected W β)
            (scalarGrowingSourceHorizon δ q) δ n q)
          (scalarGrowingPaperUpdate (scalarGrowingSourceHorizon δ q) δ n q) q
          (scalarGrowingPaperInitialState (scalarGrowingSourceHorizon δ q) δ n (x.2,x.1.1),
            coarsePrefix_rows hn.symm (1 : Matrix (Fin n) (Fin n) ℝ))
          (paperCompletionReplayNoise n q x.1.2.2) x.1.2.1) i
        (projIcc 0 (scalarGrowingSourceHorizon δ q : ℝ)
          (scalarGrowingSourceHorizon δ q).coe_nonneg t) := by
  subst n
  simp only [Nat.cast_add]
  rfl

attribute [local irreducible] actualParisiFullScalarDrift actualParisiFullMagnetization
  actualParisiFullSusceptibilitySquareExpected actualParisiNegativeRhoStieltjes
  actualParisiSigmaStieltjes

theorem coarsePrefix_initial (δ : ℝ≥0) (n qb qf : ℕ) (hq : qb ≤ qf)
    (x : PrefixInput δ n qf) :
    coarsePrefix_past (scalarGrowingSourceHorizon δ qf) (scalarGrowingSourceHorizon δ qb)
      (M1.growingQueryTime_monotone δ (by omega))
      (growingQueryDuration δ) (growingQueryTime δ) n
      (scalarGrowingPaperInitialState (scalarGrowingSourceHorizon δ qf) δ n (x.2,x.1.1)) =
    scalarGrowingPaperInitialState (scalarGrowingSourceHorizon δ qb) δ n
      ((coarsePrefix_input δ n qb qf hq x).2,(coarsePrefix_input δ n qb qf hq x).1.1) := by
  apply Prod.ext
  · rfl
  · funext i
    apply ContinuousMap.ext
    intro t
    rfl

theorem coarsePrefix_field_same_dimension (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (rf qf rb qb n : ℕ) (hfN : rf+qf=n) (hbN : rb+qb=n)
    (hq : qb ≤ qf) (x : PrefixInput δ n qf) (t : ℝ≥0)
    (ht : t ≤ scalarGrowingSourceHorizon δ qb) :
    coarsePrefix_field W β hβ δ rf qf n hfN t x =
      coarsePrefix_field W β hβ δ rb qb n hbN t (coarsePrefix_input δ n qb qf hq x) := by
  obtain ⟨d, hd⟩ : ∃ d, qf = d+qb := ⟨qf-qb, by omega⟩
  have hrb : rb=rf+d := by omega
  subst qf
  subst rb
  let H := scalarGrowingSourceHorizon δ (d+qb)
  let h := scalarGrowingSourceHorizon δ qb
  have hh : h ≤ H := M1.growingQueryTime_monotone δ (by omega)
  let b := actualParisiFullScalarDrift β
  let f := actualParisiNegativeRhoStieltjes W β hβ
  let g := actualParisiSigmaStieltjes W β hβ
  let hf := continuous_actualParisiNegativeRhoStieltjes W β hβ
  let hg := continuous_actualParisiSigmaStieltjes W β hβ
  let m := actualParisiFullMagnetization β
  let scale := scalarMeshPaperIncrementScale
    (actualParisiFullSusceptibilitySquareExpected W β) (growingQueryTime δ)
  let s := scalarGrowingPaperInitialState H δ n (x.2,x.1.1)
  let E := coarsePrefix_rows hfN.symm (1 : Matrix (Fin n) (Fin n) ℝ)
  let v := paperMatrixQueryRun rf n (n : ℝ)
    (scalarMeshPaperTarget b f g hf hg m scale H (growingQueryDuration δ) (growingQueryTime δ) n (d+qb))
    (scalarMeshPaperUpdate H (growingQueryDuration δ) (growingQueryTime δ) n (d+qb))
    (d+qb) (s,E) (paperCompletionReplayNoise n (d+qb) x.1.2.2) x.1.2.1
  have hrun := coarsePrefix_run b f g hf hg m scale H h hh
    (growingQueryDuration δ) (growingQueryTime δ) (M1.growingQueryTime_monotone δ)
    rf n qb d qb (n : ℝ) (M1.growingQueryTime_monotone δ (by omega)) le_rfl
    s E x.1.2.2 x.1.2.1
  have hE : coarsePrefix_rows (Nat.add_assoc rf d qb).symm E =
      coarsePrefix_rows hbN.symm (1 : Matrix (Fin n) (Fin n) ℝ) := by
    rfl
  rw [hE, coarsePrefix_initial δ n qb (d+qb) hq x] at hrun
  have hobs := coarsePrefix_observation b f g hf hg H h hh
    (growingQueryDuration δ) (growingQueryTime δ) n v
  rw [coarsePrefix_field_eq_run, coarsePrefix_field_eq_run]
  funext i
  have hhobs := hobs i
  change scalarInitialAuxiliaryRestriction H h hh
    (scalarMeshPaperObservation b f g hf hg H (growingQueryDuration δ) (growingQueryTime δ) n v i) =
      scalarMeshPaperObservation b f g hf hg h (growingQueryDuration δ) (growingQueryTime δ) n
        (coarsePrefix_past H h hh (growingQueryDuration δ) (growingQueryTime δ) n v) i at hhobs
  change coarsePrefix_past H h hh (growingQueryDuration δ) (growingQueryTime δ) n v = _ at hrun
  rw [hrun] at hhobs
  have hth : (t : ℝ) ∈ Icc (0 : ℝ) (h : ℝ) := ⟨t.coe_nonneg,ht⟩
  have htH : (t : ℝ) ∈ Icc (0 : ℝ) (H : ℝ) := ⟨t.coe_nonneg,ht.trans hh⟩
  rw [projIcc_of_mem _ hth, projIcc_of_mem _ htH]
  exact congrFun (congrArg DFunLike.coe hhobs) ⟨t,t.coe_nonneg,ht⟩

theorem coarsePrefix_replayField (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (rf qf rb qb : ℕ) (hdim : rf+qf=rb+qb) (hq : qb ≤ qf)
    (v : M1.ReplayInput δ rf qf) (t : ℝ≥0) (ht : t ≤ scalarGrowingSourceHorizon δ qb) :
    actualParisiGrowingReplayField W β hβ δ rb qb t
      (coarsePrefix_replayInput δ rf qf rb qb hdim hq v) =
      fun i => actualParisiGrowingReplayField W β hβ δ rf qf t v (Fin.cast hdim.symm i) := by
  have he := coarsePrefix_field_same_dimension W β hβ δ rf qf rb qb (rf+qf)
    rfl hdim.symm hq v t ht
  funext i
  exact (congrFun he (Fin.cast hdim.symm i)).symm

end SKConstants.N13a
