module

public import SKConstants.Completion.N13a.Statement

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open SKConstantsOAI.ZeroTemperatureSK
open scoped NNReal
namespace SKConstants.N13a
open GaussianProposal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

theorem coarsePrefix_weightedPath (f : StieltjesFunction ℝ) (hf : Continuous f)
    (H h : ℝ≥0) (hh : h ≤ H) (B : ScalarContinuousPath H) :
    scalarInitialAuxiliaryRestriction H h hh (scalarStieltjesWeightedPath f hf H B) =
      scalarStieltjesWeightedPath f hf h (scalarInitialAuxiliaryRestriction H h hh B) := by
  ext t
  change f t * B _ - _ = f t * B _ - _
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  have hs0 : 0 ≤ s := by simpa only [min_eq_left t.property.1] using hs.1
  have hst : s ≤ t := by simpa only [max_eq_right t.property.1] using hs.2
  have hsh : s ∈ Icc (0 : ℝ) (h : ℝ) := ⟨hs0, hst.trans t.property.2⟩
  have hsH : s ∈ Icc (0 : ℝ) (H : ℝ) := ⟨hs0, hsh.2.trans hh⟩
  simp only [IccExtend, Function.comp_apply, scalarInitialAuxiliaryRestriction,
    ContinuousMap.coe_mk, projIcc_of_mem _ hsh, projIcc_of_mem _ hsH]

theorem coarsePrefix_twoDriverPath (f g : StieltjesFunction ℝ)
    (hf : Continuous f) (hg : Continuous g) (H h : ℝ≥0) (hh : h ≤ H)
    (B D : ScalarContinuousPath H) :
    scalarInitialAuxiliaryRestriction H h hh (scalarTwoDriverWeightedPath f g hf hg H (B,D)) =
      scalarTwoDriverWeightedPath f g hf hg h
        (scalarInitialAuxiliaryRestriction H h hh B,
          scalarInitialAuxiliaryRestriction H h hh D) := by
  ext t
  exact congrArg₂ (fun x y : ℝ => -x + y)
    (congrFun (congrArg DFunLike.coe (coarsePrefix_weightedPath f hf H h hh B)) t)
    (congrFun (congrArg DFunLike.coe (coarsePrefix_weightedPath g hg H h hh D)) t)

theorem coarsePrefix_forwardPicard (b : BoundedLipschitzDrift)
    (H h : ℝ≥0) (hh : h ≤ H) (z : ℝ) (B : ScalarContinuousPath H) :
    scalarInitialAuxiliaryRestriction H h hh (scalarForwardPicardPath b H (z,B)) =
      scalarForwardPicardPath b h (z, scalarInitialAuxiliaryRestriction H h hh B) := by
  ext t
  apply solution_congr_prefix b (scalarContinuousSeedDriver H) (scalarContinuousSeedDriver h)
    (z,B) (z,scalarInitialAuxiliaryRestriction H h hh B) h _
    (⟨t,t.property.1⟩ : ℝ≥0) t.property.2
  intro s hs
  change z + B (projIcc 0 (H : ℝ) H.coe_nonneg s) =
    z + scalarInitialAuxiliaryRestriction H h hh B (projIcc 0 (h : ℝ) h.coe_nonneg s)
  have hsh : (s : ℝ) ∈ Icc (0 : ℝ) (h : ℝ) := ⟨s.coe_nonneg, hs⟩
  have hsH : (s : ℝ) ∈ Icc (0 : ℝ) (H : ℝ) := ⟨s.coe_nonneg, hs.trans hh⟩
  simp only [projIcc_of_mem _ hsh, projIcc_of_mem _ hsH,
    scalarInitialAuxiliaryRestriction, ContinuousMap.coe_mk]

theorem coarsePrefix_twoDriverPicard (b : BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (H h : ℝ≥0) (hh : h ≤ H) (z : ℝ) (B D : ScalarContinuousPath H) :
    scalarInitialAuxiliaryRestriction H h hh (scalarTwoDriverPicardPath b f g hf hg H (z,(B,D))) =
      scalarTwoDriverPicardPath b f g hf hg h
        (z,(scalarInitialAuxiliaryRestriction H h hh B,
          scalarInitialAuxiliaryRestriction H h hh D)) := by
  unfold scalarTwoDriverPicardPath
  rw [coarsePrefix_forwardPicard, coarsePrefix_twoDriverPath]

def coarsePrefix_past (H h : ℝ≥0) (hh : h ≤ H) (δ τ : ℕ → ℝ≥0) (n : ℕ)
    (s : ScalarMeshPaperPast H δ τ n) : ScalarMeshPaperPast h δ τ n :=
  ((s.1.1, (fun i => scalarInitialAuxiliaryRestriction H h hh (s.1.2.1 i), s.1.2.2)),
    fun i => scalarInitialAuxiliaryRestriction H h hh (s.2 i))

theorem coarsePrefix_observation (b : BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (H h : ℝ≥0) (hh : h ≤ H) (δ τ : ℕ → ℝ≥0) (n : ℕ)
    (s : ScalarMeshPaperPast H δ τ n) (i : Fin n) :
    scalarInitialAuxiliaryRestriction H h hh (scalarMeshPaperObservation b f g hf hg H δ τ n s i) =
      scalarMeshPaperObservation b f g hf hg h δ τ n (coarsePrefix_past H h hh δ τ n s) i :=
  coarsePrefix_twoDriverPicard b f g hf hg H h hh (s.1.1 i) (s.2 i) (s.1.2.1 i)

theorem coarsePrefix_append (H h a : ℝ≥0) (hh : h ≤ H) (d : ℝ≥0)
    (B : ScalarContinuousPath H) (z : ℝ × ScalarContinuousPath d) :
    scalarInitialAuxiliaryRestriction H h hh (scalarAppendQueryInterval H d a (B,z)) =
      scalarAppendQueryInterval h d a (scalarInitialAuxiliaryRestriction H h hh B,z) := by
  ext t
  have hm : min (t : ℝ) a ∈ Icc (0 : ℝ) (h : ℝ) :=
    ⟨le_min t.property.1 a.coe_nonneg, (min_le_left _ _).trans t.property.2⟩
  have hmH : min (t : ℝ) a ∈ Icc (0 : ℝ) (H : ℝ) := ⟨hm.1, hm.2.trans hh⟩
  simp only [scalarInitialAuxiliaryRestriction, scalarAppendQueryInterval, ContinuousMap.coe_mk,
    projIcc_of_mem _ hm, projIcc_of_mem _ hmH]

theorem coarsePrefix_update (H h : ℝ≥0) (hh : h ≤ H) (δ τ : ℕ → ℝ≥0)
    (n qf kf qb kb : ℕ) (hk : qf - kf = qb - kb)
    (s : ScalarMeshPaperPast H δ τ n) (z : EuclideanSpace ℝ (Fin n ⊕ Unit)) :
    coarsePrefix_past H h hh δ τ n (scalarMeshPaperUpdate H δ τ n qf kf s z) =
      scalarMeshPaperUpdate h δ τ n qb kb (coarsePrefix_past H h hh δ τ n s) z := by
  apply Prod.ext
  · rfl
  · funext i
    simp only [scalarMeshPaperUpdate, coarsePrefix_past, scalarMeshPaperQueryTime]
    have hc (j : ℕ) := coarsePrefix_append H h (τ j) hh (δ j) (s.2 i)
      (z (.inl i),s.1.2.2 j i)
    exact (hc (qf-kf)).trans (congrArg (fun j =>
      scalarAppendQueryInterval h (δ j) (τ j)
        (scalarInitialAuxiliaryRestriction H h hh (s.2 i),z (.inl i),s.1.2.2 j i)) hk)

theorem coarsePrefix_target (b : BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (m : ℝ → ℝ → ℝ) (scale : ℕ → ℝ)
    (H h : ℝ≥0) (hh : h ≤ H) (δ τ : ℕ → ℝ≥0)
    (n qf kf qb kb : ℕ) (hk : qf - kf = qb - kb)
    (hk' : qf - (kf+1) = qb - (kb+1))
    (ht : τ (qb-kb) ≤ h) (ha : τ (qb-(kb+1)) ≤ h)
    (s : ScalarMeshPaperPast H δ τ n) :
    scalarMeshPaperTarget b f g hf hg m scale H δ τ n qf kf s =
      scalarMeshPaperTarget b f g hf hg m scale h δ τ n qb kb
        (coarsePrefix_past H h hh δ τ n s) := by
  funext i
  simp only [scalarMeshPaperTarget, scalarMeshPaperQueryTime, hk, hk']
  have hth : (τ (qb-kb) : ℝ) ∈ Icc (0 : ℝ) (h : ℝ) := ⟨(τ _).coe_nonneg, ht⟩
  have hah : (τ (qb-(kb+1)) : ℝ) ∈ Icc (0 : ℝ) (h : ℝ) := ⟨(τ _).coe_nonneg, ha⟩
  have htH : (τ (qb-kb) : ℝ) ∈ Icc (0 : ℝ) (H : ℝ) := ⟨hth.1, hth.2.trans hh⟩
  have haH : (τ (qb-(kb+1)) : ℝ) ∈ Icc (0 : ℝ) (H : ℝ) := ⟨hah.1, hah.2.trans hh⟩
  rw [projIcc_of_mem _ hth, projIcc_of_mem _ hah,
    projIcc_of_mem _ htH, projIcc_of_mem _ haH]
  rw [← coarsePrefix_observation b f g hf hg H h hh δ τ n s i]
  rfl

end SKConstants.N13a
