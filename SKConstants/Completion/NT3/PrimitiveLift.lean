module

public import SKConstants.Completion.NT3.PathReference

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

def auxiliaryStaticLaw (W : BrownianSystem Ω) (δ : ℝ≥0) (n : ℕ) :
    Measure (ScalarGrowingReplayAuxData δ n) :=
  (Measure.pi fun _ : Fin n => scalarPrimitiveBrownianPathLaw W (growingQueryDuration δ 0)).prod
    (Measure.infinitePi fun j : ℕ => Measure.pi fun _ : Fin n =>
      scalarPrimitiveBridgePathLaw W (growingQueryDuration δ j))

instance auxiliaryStaticLaw_probability (W : BrownianSystem Ω) (δ : ℝ≥0) (n : ℕ) :
    IsProbabilityMeasure (auxiliaryStaticLaw W δ n) := by
  unfold auxiliaryStaticLaw
  infer_instance

abbrev PrimitiveStatic (p : Parameters) (n : ℕ) :=
  (Spin n × Prim n) × (ScalarGrowingReplayAuxData (coarseMesh p n)
    (coarseRank p n + coarseCount p n) ×
    PaperCompletionNoise (coarseRank p n + coarseCount p n) (coarseCount p n))

def primitiveStaticLaw (W : BrownianSystem Ω) (p : Parameters) (n : ℕ) :
    Measure (PrimitiveStatic p n) :=
  ((uniformSpinLaw n).prod (primLaw n)).prod
    ((auxiliaryStaticLaw W (coarseMesh p n) (coarseRank p n + coarseCount p n)).prod
      (paperCompletionNoiseLaw (coarseRank p n + coarseCount p n) (coarseCount p n)))

instance primitiveStaticLaw_probability (W : BrownianSystem Ω) (p : Parameters) (n : ℕ) :
    IsProbabilityMeasure (primitiveStaticLaw W p n) := by
  unfold primitiveStaticLaw
  infer_instance

abbrev DPaths (δ : ℝ≥0) (n q : ℕ) := Fin n → ScalarContinuousPath (scalarGrowingSourceHorizon δ q)

def dPathLaw (W : BrownianSystem Ω) (δ : ℝ≥0) (n q : ℕ) : Measure (DPaths δ n q) :=
  Measure.pi fun _ : Fin n => scalarPrimitiveBrownianPathLaw W (scalarGrowingSourceHorizon δ q)

instance dPathLaw_probability (W : BrownianSystem Ω) (δ : ℝ≥0) (n q : ℕ) :
    IsProbabilityMeasure (dPathLaw W δ n q) := by
  unfold dPathLaw
  infer_instance

def sharpSplit (p : Parameters) (n : ℕ) (y : SharpInput p n) :
    PrimitiveStatic p n × DPaths (coarseMesh p n) (coarseRank p n + coarseCount p n)
      (coarseCount p n) :=
  (((y.1, y.2.1), (y.2.2.1, y.2.2.2.1)), y.2.2.2.2)

def sharpJoin (p : Parameters) (n : ℕ)
    (u : PrimitiveStatic p n × DPaths (coarseMesh p n) (coarseRank p n + coarseCount p n)
      (coarseCount p n)) : SharpInput p n :=
  (u.1.1.1, u.1.1.2, (u.1.2.1, u.1.2.2, u.2))

theorem measurable_sharpSplit (p : Parameters) (n : ℕ) : Measurable (sharpSplit p n) := by
  unfold sharpSplit
  fun_prop

theorem measurable_sharpJoin (p : Parameters) (n : ℕ) : Measurable (sharpJoin p n) := by
  unfold sharpJoin
  fun_prop

theorem sharpSplit_law (W : BrownianSystem Ω) (p : Parameters) (n : ℕ) :
    (sharpUnlinkedLaw W p n).map (sharpSplit p n) =
      (primitiveStaticLaw W p n).prod
        (dPathLaw W (coarseMesh p n) (coarseRank p n + coarseCount p n) (coarseCount p n)) := by
  let S := uniformSpinLaw n
  let M := primLaw n
  let A := auxiliaryStaticLaw W (coarseMesh p n) (coarseRank p n + coarseCount p n)
  let C := paperCompletionNoiseLaw (coarseRank p n + coarseCount p n) (coarseCount p n)
  let D := dPathLaw W (coarseMesh p n) (coarseRank p n + coarseCount p n) (coarseCount p n)
  have h0 := (measurePreserving_prodAssoc S M (A.prod (C.prod D))).symm
  have h1 := (MeasurePreserving.id (S.prod M)).prod (measurePreserving_prodAssoc A C D).symm
  have h2 := (measurePreserving_prodAssoc (S.prod M) (A.prod C) D).symm
  exact (h2.comp (h1.comp h0)).map_eq

theorem sharpJoin_law (W : BrownianSystem Ω) (p : Parameters) (n : ℕ) :
    ((primitiveStaticLaw W p n).prod
      (dPathLaw W (coarseMesh p n) (coarseRank p n + coarseCount p n) (coarseCount p n))).map
        (sharpJoin p n) = sharpUnlinkedLaw W p n := by
  rw [← sharpSplit_law W p n,
    Measure.map_map (measurable_sharpJoin p n) (measurable_sharpSplit p n)]
  change (sharpUnlinkedLaw W p n).map id = _
  exact Measure.map_id

def pathSplit (δ : ℝ≥0) (r q : ℕ) (u : PathInput δ r q) :
    ParisiGrowingReplaySpinStatic δ (r + q) q × DPaths δ (r + q) q :=
  ((u.2.1, u.1), u.2.2)

theorem measurable_pathSplit (δ : ℝ≥0) (r q : ℕ) : Measurable (pathSplit δ r q) :=
  (measurable_snd.fst.prodMk measurable_fst).prodMk measurable_snd.snd

theorem pathSplit_law (W : BrownianSystem Ω) (δ : ℝ≥0) (r q : ℕ) :
    ((M1.spinPrior (r + q)).prod (M1.ReplayLaw W δ r q)).map (pathSplit δ r q) =
      (parisiGrowingReplaySpinStaticLaw W δ (r + q) q).prod (dPathLaw W δ (r + q) q) := by
  let S := M1.spinPrior (r + q)
  let P := scalarGrowingReplayStaticLaw W δ (r + q) q
  let D := dPathLaw W δ (r + q) q
  have h0 := (measurePreserving_prodAssoc S P D).symm
  have h1 := (Measure.measurePreserving_swap (μ := S) (ν := P)).prod (MeasurePreserving.id D)
  exact (h1.comp h0).map_eq

def primitiveStaticMap (p : Parameters) (n : ℕ) (u : PrimitiveStatic p n) :
    ParisiGrowingReplaySpinStatic (coarseMesh p n) (coarseRank p n + coarseCount p n)
      (coarseCount p n) :=
  ((u.2.1, (castMatrix (rankCount_add p.a p.b n) (physical n u.1.2), u.2.2)),
    fun i => u.1.1 (Fin.cast (rankCount_add p.a p.b n) i))

theorem measurable_primitiveStaticMap (p : Parameters) (n : ℕ) :
    Measurable (primitiveStaticMap p n) := by
  have hm : Measurable (fun u : PrimitiveStatic p n =>
      castMatrix (rankCount_add p.a p.b n) (physical n u.1.2)) :=
    (continuous_castMatrix _).measurable.comp
      ((continuous_goeMatrix _).measurable.comp measurable_fst.snd)
  exact (measurable_snd.fst.prodMk (hm.prodMk measurable_snd.snd)).prodMk
    (Measurable.of_eval fun i => (measurable_pi_apply _).comp measurable_fst.fst)

theorem primitiveStaticMap_law (W : BrownianSystem Ω) (p : Parameters) (n : ℕ) :
    (primitiveStaticLaw W p n).map (primitiveStaticMap p n) =
      parisiGrowingReplaySpinStaticLaw W (coarseMesh p n)
        (coarseRank p n + coarseCount p n) (coarseCount p n) := by
  have h := congrArg (fun μ => μ.map (pathSplit (coarseMesh p n) (coarseRank p n) (coarseCount p n)))
    (T0.sharpToReplay_unlinked_law W p n)
  rw [← sharpJoin_law W p n,
    Measure.map_map (T0.measurable_sharpToReplay p n) (measurable_sharpJoin p n),
    Measure.map_map (measurable_pathSplit _ _ _)
      ((T0.measurable_sharpToReplay p n).comp (measurable_sharpJoin p n)),
    pathSplit_law] at h
  change (((primitiveStaticLaw W p n).prod
    (dPathLaw W (coarseMesh p n) (coarseRank p n + coarseCount p n) (coarseCount p n))).map
      (Prod.map (primitiveStaticMap p n) id)) = _ at h
  rw [← Measure.map_prod_map _ _ (measurable_primitiveStaticMap p n) measurable_id,
    Measure.map_id] at h
  have hf := congrArg (fun μ => μ.map Prod.fst) h
  simpa only [Measure.map_fst_prod, measure_univ, one_smul] using hf

def splitReferenceDensity (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r q : ℕ) (J : PathInput δ r q → ℝ)
    (u : ParisiGrowingReplaySpinStatic δ (r + q) q × DPaths δ (r + q) q) : ℝ≥0∞ :=
  pathReferenceDensity W β hβ δ r q J (u.1.2, (u.1.1, u.2))

theorem splitReference_static_marginal (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r q : ℕ) (J : PathInput δ r q → ℝ)
    (hJ : N13t.IsL2Limit ((M1.spinPrior (r + q)).prod (M1.ReplayLaw W δ r q))
      (T0.replayPathDLeftSum W β hβ δ r q) J) :
    (((parisiGrowingReplaySpinStaticLaw W δ (r + q) q).prod (dPathLaw W δ (r + q) q)).withDensity
      (splitReferenceDensity W β hβ δ r q J)).map Prod.fst =
      parisiGrowingReplaySpinStaticLaw W δ (r + q) q := by
  have hg : Measurable (splitReferenceDensity W β hβ δ r q J) :=
    (measurable_pathReferenceDensity W β hβ δ r q J hJ.1).comp
      (measurable_fst.snd.prodMk (measurable_fst.fst.prodMk measurable_snd))
  have hmap : (((M1.spinPrior (r + q)).prod (M1.ReplayLaw W δ r q)).withDensity
      (pathReferenceDensity W β hβ δ r q J)).map (pathSplit δ r q) =
      ((parisiGrowingReplaySpinStaticLaw W δ (r + q) q).prod (dPathLaw W δ (r + q) q)).withDensity
        (splitReferenceDensity W β hβ δ r q J) := by
    change (((M1.spinPrior (r + q)).prod (M1.ReplayLaw W δ r q)).withDensity
      (splitReferenceDensity W β hβ δ r q J ∘ pathSplit δ r q)).map _ = _
    rw [map_withDensity_comp _ _ (measurable_pathSplit _ _ _) _ hg, pathSplit_law]
  rw [← hmap, Measure.map_map measurable_fst (measurable_pathSplit _ _ _)]
  exact pathReference_static_marginal W β hβ δ hδ r q J hJ

theorem primitiveReference_of_path_integral (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (hδ : 0 < coarseMesh p n)
    (J : PathInput (coarseMesh p n) (coarseRank p n) (coarseCount p n) → ℝ)
    (hJ : N13t.IsL2Limit ((M1.spinPrior (coarseRank p n + coarseCount p n)).prod
      (M1.ReplayLaw W (coarseMesh p n) (coarseRank p n) (coarseCount p n)))
      (T0.replayPathDLeftSum W β hβ (coarseMesh p n) (coarseRank p n) (coarseCount p n)) J) :
    ((sharpUnlinkedLaw W p n).withDensity
      (pathReferenceDensity W β hβ (coarseMesh p n) (coarseRank p n) (coarseCount p n) J ∘
        T0.sharpToReplay p n)).map (fun y => (y.1, y.2.1)) = unlinkedPrimitiveSpinFirstLaw n := by
  let g := splitReferenceDensity W β hβ (coarseMesh p n) (coarseRank p n) (coarseCount p n) J
  have hg : Measurable g :=
    (measurable_pathReferenceDensity W β hβ _ _ _ J hJ.1).comp
      (measurable_fst.snd.prodMk (measurable_fst.fst.prodMk measurable_snd))
  have hstatic := withDensity_static_pullback (primitiveStaticLaw W p n)
    (parisiGrowingReplaySpinStaticLaw W (coarseMesh p n)
      (coarseRank p n + coarseCount p n) (coarseCount p n))
    (dPathLaw W (coarseMesh p n) (coarseRank p n + coarseCount p n) (coarseCount p n))
    (primitiveStaticMap p n) (measurable_primitiveStaticMap p n) (primitiveStaticMap_law W p n)
    g hg (splitReference_static_marginal W β hβ _ hδ _ _ J hJ)
  have hm : Measurable (pathReferenceDensity W β hβ (coarseMesh p n) (coarseRank p n)
      (coarseCount p n) J ∘ T0.sharpToReplay p n) :=
    (measurable_pathReferenceDensity W β hβ _ _ _ J hJ.1).comp (T0.measurable_sharpToReplay p n)
  have hmap := map_withDensity_comp
    ((primitiveStaticLaw W p n).prod
      (dPathLaw W (coarseMesh p n) (coarseRank p n + coarseCount p n) (coarseCount p n)))
    (sharpJoin p n) (measurable_sharpJoin p n) _ hm
  rw [sharpJoin_law] at hmap
  rw [← hmap, Measure.map_map (measurable_fst.prodMk measurable_snd.fst)
    (measurable_sharpJoin p n)]
  change (((primitiveStaticLaw W p n).prod
    (dPathLaw W (coarseMesh p n) (coarseRank p n + coarseCount p n) (coarseCount p n))).withDensity
      (fun u => g (primitiveStaticMap p n u.1, u.2))).map (Prod.fst ∘ Prod.fst) = _
  rw [← Measure.map_map measurable_fst measurable_fst, hstatic]
  change (((uniformSpinLaw n).prod (primLaw n)).prod _).map Prod.fst = _
  rw [Measure.map_fst_prod]
  simp only [measure_univ, one_smul]
  rfl

end SKConstants.Completion.NT3
