module

public import SKConstants.Completion.NT3.PrimitiveLift

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology

namespace SKConstants.Completion.NT3
open SKConstantsOAI.ZeroTemperatureSK GaussianProposal LC4a LM3 Blueprint Blueprint4 N13A

variable {Ω : Type} [MeasurableSpace Ω]

theorem sharpDBracket_eq_path (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (y : SharpInput p n) :
    sharpDBracket W β hβ p n y =
      pathDBracket W β hβ (coarseMesh p n) (coarseRank p n) (coarseCount p n)
        (T0.sharpToReplay p n y) := by
  unfold sharpDBracket pathDBracket
  rw [← (finCongr (rankCount_add p.a p.b n)).sum_comp]
  apply Finset.sum_congr rfl
  intro i _
  unfold N13t.fullHistoryDBracket historyDBracket
  simp only [Function.comp_apply]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le (coarseTime p n).coe_nonneg] at ht
  dsimp only [sharpDCoefficient, sharpField, castVec, historyDCoefficient,
    historyPathAt, N13t.observationDProjection, T0.sharpToReplay]
  rw [Real.coe_toNNReal t ht.1]
  congr 3
  simp only [actualParisiGrowingReplayField, scalarGrowingReplayField, M1.ReplayHistories,
    Real.coe_toNNReal t ht.1]
  rfl

theorem measurable_sharpDBracket (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) : Measurable (sharpDBracket W β hβ p n) := by
  have he : sharpDBracket W β hβ p n =
      pathDBracket W β hβ (coarseMesh p n) (coarseRank p n) (coarseCount p n) ∘
        T0.sharpToReplay p n := funext (sharpDBracket_eq_path W β hβ p n)
  rw [he]
  exact (measurable_pathDBracket W β hβ _ _ _).comp (T0.measurable_sharpToReplay p n)

theorem measurable_sharpLink (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) : Measurable (sharpLink W β hβ p n) := by
  have he : sharpLink W β hβ p n =
      M1.TerminalDensity β (coarseTime p n)
        (actualParisiGrowingReplayField W β hβ (coarseMesh p n) (coarseRank p n)
          (coarseCount p n) (coarseTime p n)) ∘ T0.sharpToReplay p n :=
    funext (T0.sharpLink_eq_path W β hβ p n)
  rw [he]
  exact (M1.measurable_terminalDensity _ _ _ (M1.measurable_ReplayField W β hβ _ _ _ _)).comp
    (T0.measurable_sharpToReplay p n)

theorem sharpLink_pos (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (y : SharpInput p n) : 0 < sharpLink W β hβ p n y :=
  Finset.prod_pos fun _ _ => actualParisiSpinLinkDensity_pos _ _ _ _

theorem sharpLinkedLaw_inverse_information (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (J : SharpInput p n → ℝ) (hJ : Measurable J) :
    (sharpLinkedLaw W β hβ p n).withDensity
      (fun y => ENNReal.ofReal (Real.exp (-sharpInformation W β hβ p n J y))) =
      (sharpUnlinkedLaw W p n).withDensity
        (fun y => ENNReal.ofReal (Real.exp (J y - sharpDBracket W β hβ p n y / 2))) := by
  have hinfo : Measurable (sharpInformation W β hβ p n J) :=
    (((measurable_sharpLink W β hβ p n).log.sub hJ).add
      ((measurable_sharpDBracket W β hβ p n).div_const 2))
  have hinv : Measurable (fun y => ENNReal.ofReal
      (Real.exp (-sharpInformation W β hβ p n J y))) := hinfo.neg.exp.ennreal_ofReal
  unfold sharpLinkedLaw
  rw [← withDensity_mul _ (measurable_sharpLink W β hβ p n).ennreal_ofReal
    hinv]
  apply withDensity_congr_ae
  filter_upwards [] with y
  change ENNReal.ofReal (sharpLink W β hβ p n y) *
    ENNReal.ofReal (Real.exp (-sharpInformation W β hβ p n J y)) = _
  rw [← ENNReal.ofReal_mul (sharpLink_pos W β hβ p n y).le]
  congr 1
  rw [show sharpLink W β hβ p n y = Real.exp (Real.log (sharpLink W β hβ p n y)) from
    (Real.exp_log (sharpLink_pos W β hβ p n y)).symm, ← Real.exp_add]
  congr 1
  unfold sharpInformation
  ring

theorem sharp_inverse_information_primitive_spin_marginal
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (p : Parameters) (n : ℕ)
    (hn : 0 < n) (J : SharpInput p n → ℝ) (hJ : IsSharpDIntegral W β hβ p n J) :
    ((sharpLinkedLaw W β hβ p n).withDensity
      (fun y => ENNReal.ofReal (Real.exp (-sharpInformation W β hβ p n J y)))).map
        (fun y => (y.1, y.2.1)) = unlinkedPrimitiveSpinFirstLaw n := by
  have hδ := paperGrowingQueryMeshSize_pos p.a n hn
  obtain ⟨K, hK⟩ := T0.replayPathDIntegral_exists W β hβ (coarseMesh p n) hδ
    (coarseRank p n) (coarseCount p n)
  have he := T0.isSharpDIntegral_unique W β hβ p n J (K ∘ T0.sharpToReplay p n) hJ
    (T0.isSharpDIntegral_of_path W β hβ p n K hK)
  rw [sharpLinkedLaw_inverse_information W β hβ p n J hJ.1]
  have hd : (fun y => ENNReal.ofReal (Real.exp (J y - sharpDBracket W β hβ p n y / 2))) =ᵐ[
      sharpUnlinkedLaw W p n]
      pathReferenceDensity W β hβ (coarseMesh p n) (coarseRank p n) (coarseCount p n) K ∘
        T0.sharpToReplay p n := by
    filter_upwards [he] with y hy
    rw [hy, sharpDBracket_eq_path W β hβ p n y]
    rfl
  rw [withDensity_congr_ae hd]
  exact primitiveReference_of_path_integral W β hβ p n hδ K hK

def SharpPrimitiveEndpointStatement : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters), FineExponents p → CoarseExponents4 p →
    ∀ᶠ n : ℕ in atTop, ∀ J : SharpInput p n → ℝ, IsSharpDIntegral W β hβ p n J →
      ((sharpLinkedLaw W β hβ p n).withDensity
        (fun y => ENNReal.ofReal (Real.exp (-sharpInformation W β hβ p n J y)))).map
          (fun y => (y.1, y.2.1)) = unlinkedPrimitiveSpinFirstLaw n

theorem sharpPrimitiveEndpoint_holds : SharpPrimitiveEndpointStatement := by
  intro Ω _ W β hβ p _ _
  filter_upwards [eventually_gt_atTop 0] with n hn J hJ
  exact sharp_inverse_information_primitive_spin_marginal W β hβ p n hn J hJ

def SharpRowTransportStatement : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters), FineExponents p → CoarseExponents4 p →
    ∀ᶠ n : ℕ in atTop,
      ∃ (J : SharpInput p n → ℝ) (Jrow : (Bool × Ω) × Ω → ℝ),
        IsSharpDIntegral W β hβ p n J ∧ Measurable Jrow ∧
        LM4b.IsActualRowDIntegral W W β hβ (coarseTime p n) Jrow ∧
        HasLaw (sharpRows W β hβ p n) (canonicalArrayLaw W β hβ p n)
          (sharpLinkedLaw W β hβ p n) ∧
        IdentDistrib
          (fun y => sharpInformation W β hβ p n J y / n -
            β * linearEnergy W β hβ (sharpRows W β hβ p n y))
          (fun ω : Fin n → (Bool × Ω) × Ω =>
            (∑ i, (rowInformationV W β (coarseTime p n) Jrow (ω i) -
              β * LJ.actualFiniteRow W W β hβ (growingQueryTime (coarseMesh p n))
                (coarseCount p n) (ω i))) / n)
          (sharpLinkedLaw W β hβ p n)
          (Measure.pi fun _ : Fin n => actualParisiFullQuerySpinLaw W W β (coarseTime p n))

theorem sharpTransport_holds (hT2 : SharpRowTransportStatement) : SharpTransportStatement := by
  intro Ω _ W β hβ p hf hc
  filter_upwards [hT2 W β hβ p hf hc, sharpPrimitiveEndpoint_holds W β hβ p hf hc]
    with n hrows hend
  obtain ⟨J, Jrow, hJ, hJm, hJrow, hlaw, hident⟩ := hrows
  exact ⟨J, Jrow, hJ, hJm, hJrow, hlaw, hident, hend J hJ⟩

end SKConstants.Completion.NT3
