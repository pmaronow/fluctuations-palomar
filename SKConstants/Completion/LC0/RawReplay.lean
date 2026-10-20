module
public import SKConstants.Completion.LC0.SourceReplay
public import SKConstants.ParisiGrowingReplayDReference

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open SKConstantsOAI.ZeroTemperatureSK
open scoped NNReal BigOperators
namespace SKConstants.M1
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω]

abbrev RawReplayInput (Ω : Type*) (δ : ℝ≥0) (r₀ q : ℕ) :=
  ParisiGrowingReplaySpinStatic δ (Size r₀ q) q × (Fin (Size r₀ q) → Ω)

def RawReplayLaw (W : BrownianSystem Ω) (δ : ℝ≥0) (r₀ q : ℕ) : Measure (RawReplayInput Ω δ r₀ q) :=
  (parisiGrowingReplaySpinStaticLaw W δ (Size r₀ q) q).prod
    (Measure.pi (fun _ : Fin (Size r₀ q) => W.law))

instance RawReplayLaw_probability (W : BrownianSystem Ω) (δ : ℝ≥0) (r₀ q : ℕ) :
    IsProbabilityMeasure (RawReplayLaw W δ r₀ q) := by
  let := W.isProbability
  unfold RawReplayLaw
  infer_instance

def RawToReplay (W : BrownianSystem Ω) (δ : ℝ≥0) (r₀ q : ℕ)
    (u : RawReplayInput Ω δ r₀ q) : (Fin (Size r₀ q) → Bool) × ReplayInput δ r₀ q :=
  (u.1.2,(u.1.1,fun i => scalarPrimitiveBrownianPathVersion W (Horizon δ q) (u.2 i)))

theorem measurable_RawToReplay (W : BrownianSystem Ω) (δ : ℝ≥0) (r₀ q : ℕ) :
    Measurable (RawToReplay W δ r₀ q) :=
  measurable_fst.snd.prodMk (measurable_fst.fst.prodMk
    (Measurable.of_eval fun i => (measurable_scalarPrimitiveBrownianPathVersion W _).comp
      ((measurable_pi_apply i).comp measurable_snd)))

theorem rawToReplay_unlinked_law (W : BrownianSystem Ω) (δ : ℝ≥0) (r₀ q : ℕ) :
    (RawReplayLaw W δ r₀ q).map (RawToReplay W δ r₀ q) =
      (spinPrior (Size r₀ q)).prod (ReplayLaw W δ r₀ q) := by
  let := W.isProbability
  let P := scalarGrowingReplayStaticLaw W δ (Size r₀ q) q
  let S := spinPrior (Size r₀ q)
  let D := Measure.pi (fun _ : Fin (Size r₀ q) => W.law)
  let B := Measure.pi (fun _ : Fin (Size r₀ q) => scalarPrimitiveBrownianPathLaw W (Horizon δ q))
  let F : (Fin (Size r₀ q) → Ω) → Fin (Size r₀ q) → ScalarContinuousPath (Horizon δ q) :=
    fun ω i => scalarPrimitiveBrownianPathVersion W (Horizon δ q) (ω i)
  have hF : Measurable F := Measurable.of_eval fun i =>
    (measurable_scalarPrimitiveBrownianPathVersion W _).comp (measurable_pi_apply i)
  have hD : D.map F = B := scalarPrimitiveBrownianVectorPathVersion_law W _ _
  let shuffle : (ParisiGrowingReplaySpinStatic δ (Size r₀ q) q ×
      (Fin (Size r₀ q) → ScalarContinuousPath (Horizon δ q))) →
      (Fin (Size r₀ q) → Bool) × ReplayInput δ r₀ q :=
    fun u => (u.1.2,(u.1.1,u.2))
  have hs : Measurable shuffle := measurable_fst.snd.prodMk (measurable_fst.fst.prodMk measurable_snd)
  have hmap : ((P.prod S).prod D).map (Prod.map id F) = (P.prod S).prod B := by
    rw [← Measure.map_prod_map _ _ measurable_id hF, Measure.map_id, hD]
  change ((P.prod S).prod D).map (shuffle ∘ Prod.map id F) = S.prod (P.prod B)
  rw [← Measure.map_map hs (measurable_id.prodMap hF), hmap]
  change ((P.prod S).prod B).map
    (MeasurableEquiv.prodAssoc ∘ Prod.map Prod.swap id) = _
  rw [← Measure.map_map MeasurableEquiv.prodAssoc.measurable (measurable_swap.prodMap measurable_id),
    ← Measure.map_prod_map _ _ measurable_swap measurable_id,
    Measure.prod_swap, Measure.map_id, Measure.prodAssoc_prod]

def RawReplayDensity (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r₀ q : ℕ) (u : RawReplayInput Ω δ r₀ q) : ℝ :=
  TerminalDensity β (Horizon δ q)
    (actualParisiGrowingReplayField W β hβ δ r₀ q (Horizon δ q)) (RawToReplay W δ r₀ q u)

def RawLinkedLaw (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (r₀ q : ℕ) :=
  (RawReplayLaw W δ r₀ q).withDensity
    (fun u => ENNReal.ofReal (RawReplayDensity W β hβ δ r₀ q u))

theorem rawReplayDensity_pos (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r₀ q : ℕ) (u : RawReplayInput Ω δ r₀ q) :
    0 < RawReplayDensity W β hβ δ r₀ q u := terminalDensity_pos _ _ _ _

theorem measurable_RawReplayDensity (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r₀ q : ℕ) : Measurable (RawReplayDensity W β hβ δ r₀ q) :=
  (measurable_terminalDensity _ _ _ (measurable_ReplayField W β hβ δ r₀ q _)).comp
    (measurable_RawToReplay W δ r₀ q)

theorem rawLinked_toReplay_law (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r₀ q : ℕ) :
    (RawLinkedLaw W β hβ δ r₀ q).map (RawToReplay W δ r₀ q) =
      ReplayLinkedLaw W β hβ δ r₀ q := by
  let g := fun u => ENNReal.ofReal (TerminalDensity β (Horizon δ q)
    (actualParisiGrowingReplayField W β hβ δ r₀ q (Horizon δ q)) u)
  have hg : Measurable g :=
    (measurable_terminalDensity _ _ _ (measurable_ReplayField W β hβ δ r₀ q _)).ennreal_ofReal
  have hF := measurable_RawToReplay W δ r₀ q
  have hm : ((RawReplayLaw W δ r₀ q).withDensity (g ∘ RawToReplay W δ r₀ q)).map
      (RawToReplay W δ r₀ q) = ((RawReplayLaw W δ r₀ q).map
        (RawToReplay W δ r₀ q)).withDensity g := by
    ext s hs
    rw [Measure.map_apply hF hs, withDensity_apply _ (hF hs), withDensity_apply _ hs,
      setLIntegral_map hs hg hF]
    rfl
  change ((RawReplayLaw W δ r₀ q).withDensity (g ∘ RawToReplay W δ r₀ q)).map _ = _
  rw [hm, rawToReplay_unlinked_law W δ r₀ q]
  rfl

instance RawLinkedLaw_probability (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r₀ q : ℕ) : IsProbabilityMeasure (RawLinkedLaw W β hβ δ r₀ q) := by
  have hm := rawLinked_toReplay_law W β hβ δ r₀ q
  refine ⟨?_⟩
  have he := congrArg (fun ν => ν Set.univ) hm
  rw [Measure.map_apply (measurable_RawToReplay W δ r₀ q) MeasurableSet.univ] at he
  simpa using he

theorem rawReplayDensity_eq_pastCallback_ae (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r₀ q : ℕ) :
    ∀ᵐ u ∂ RawReplayLaw W δ r₀ q, RawReplayDensity W β hβ δ r₀ q u =
      ∏ i : Fin (Size r₀ q), actualParisiSpinLinkDensity β (u.1.2 i) (Horizon δ q)
        (actualParisiGrowingSpinReplayFieldPast W β hβ δ hδ r₀ q (Horizon δ q)
          (u.1,brownianVectorFullPast W.B (Horizon δ q) u.2) i) := by
  let := W.isProbability
  filter_upwards [(measurePreserving_snd (μ := parisiGrowingReplaySpinStaticLaw W δ (Size r₀ q) q)
    (ν := Measure.pi (fun _ : Fin (Size r₀ q) => W.law))).quasiMeasurePreserving.ae
      (actualParisiGrowingReplayPastCallback_brownian_ae W β hβ δ hδ r₀ q)] with u hu
  unfold RawReplayDensity TerminalDensity RawToReplay
  apply Finset.prod_congr rfl
  intro i _
  exact congrArg (actualParisiSpinLinkDensity β (u.1.2 i) (Horizon δ q))
    (congrFun (hu u.1.1 (Horizon δ q)) i).symm

end SKConstants.M1
