module

public import WholePathPhysicalTrace

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

theorem massCellSum_nonneg {a : ℝ} (as : List PositiveMass) (ha : MassOrdered a as)
    (f : ℕ → ℝ) (hf : ∀ j < as.length, 0 ≤ f j) : 0 ≤ massCellSum as a f := by
  have h := massCellSum_mono as ha (f := fun _ => 0) (g := f) hf
  simpa only [massCellSum_const,mul_zero] using h

theorem massCellSum_sqrt_square_le {a : ℝ} (as : List PositiveMass) (ha : MassOrdered a as)
    (f : ℕ → ℝ) (hf : ∀ j < as.length, 0 ≤ f j) :
    (massCellSum as a (fun j => Real.sqrt (f j)))^2 ≤
      (partitionEnd a as-a)*massCellSum as a f := by
  induction as generalizing a f with
  | nil => simp [massCellSum,partitionEnd]
  | cons b bs ih =>
    have hf0 : 0 ≤ f 0 := hf 0 (by simp)
    have hft : ∀ j < bs.length, 0 ≤ f (j+1) := fun j hj => hf (j+1) (by simp; omega)
    let w := b.val-a
    let v := partitionEnd b.val bs-b.val
    let L := massCellSum bs b.val (fun j => Real.sqrt (f (j+1)))
    let R := massCellSum bs b.val (fun j => f (j+1))
    have hw : 0 ≤ w := sub_nonneg.mpr ha.2.1
    have hv : 0 ≤ v := sub_nonneg.mpr (massOrdered_start_le_end bs ha.2.2)
    have hR : 0 ≤ R := massCellSum_nonneg bs ha.2.2 _ hft
    have hL : L^2 ≤ v*R := ih ha.2.2 _ hft
    have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.univ : Finset (Fin 2))
      (r := ![w*Real.sqrt (f 0),L]) (f := ![w,v]) (g := ![w*f 0,R])
      (by intro i _; fin_cases i
          · change 0 ≤ w; exact hw
          · change 0 ≤ v; exact hv)
      (by intro i _; fin_cases i
          · change 0 ≤ w*f 0; exact mul_nonneg hw hf0
          · change 0 ≤ R; exact hR)
      (by intro i _; fin_cases i
          · change (w*Real.sqrt (f 0))^2 ≤ w*(w*f 0)
            rw [mul_pow,Real.sq_sqrt hf0]
            nlinarith
          · change L^2 ≤ v*R; exact hL)
    simp only [Fin.sum_univ_two] at h
    change (w*Real.sqrt (f 0)+L)^2 ≤ (w+v)*(w*f 0+R) at h
    change (w*Real.sqrt (f 0)+L)^2 ≤ (partitionEnd b.val bs-a)*(w*f 0+R)
    have he : partitionEnd b.val bs-a=w+v := by dsimp [w,v]; ring
    rwa [he]

theorem massCellSum_sqrt_le_of_unit_bound (as : List PositiveMass) (ha : MassOrdered 0 as)
    (f : ℕ → ℝ) (hf : ∀ j < as.length, 0 ≤ f j) {B : ℝ}
    (hB : massCellSum as 0 f ≤ B) :
    massCellSum as 0 (fun j => Real.sqrt (f j)) ≤ Real.sqrt B := by
  apply Real.le_sqrt_of_sq_le
  have hCS := massCellSum_sqrt_square_le as ha f hf
  have hnon := massCellSum_nonneg as ha f hf
  have he : partitionEnd 0 as-0 ≤ 1 := by simpa using ha.end_bounds.2
  exact hCS.trans ((mul_le_mul_of_nonneg_right he hnon).trans (by simpa using hB))

theorem completedSampledWholePath_sqrtTrace_le (n dim : ℕ)
    (e : Fin (dim+1) ≃ FeatureIndex (n+1))
    (b h : ℝ → ℝ≥0) {g mesh : ℝ} (hg : 0 < g) (hmesh0 : 0 ≤ mesh)
    (as : List PositiveMass) (ha : MassOrdered 0 as)
    (hmesh : ∀ w ∈ sampleMassDurations 0 as, (w:ℝ) ≤ mesh)
    (hgap : ∀ u ∈ Icc (0:ℝ) 1, ∀ v ∈ Icc (0:ℝ) 1, u ≤ v →
      g*(v-u) ≤ (h v:ℝ)-(h u:ℝ)) :
    let q := completedPathClock (n+1) b h
    let steps := sampleClockSteps q 0 as
    massCellSum as 0 (fun j => Real.sqrt
      (∫ p, physicalCutSourceSquareTrace (n+1) steps id j p
        ∂rootedHierarchyPathLaw (uniformWeight (n+1)) (finiteFeature (n+1)) (q 0) steps)) ≤
      Real.sqrt (2/((n+1:ℝ)*g)+2*mesh) := by
  dsimp only
  apply massCellSum_sqrt_le_of_unit_bound as ha
  · intro j _
    exact integral_nonneg fun p => (physicalCutSourceSquareTrace_mem_Icc (n+1) _
      (sampleClockSteps_ordered _ _ ha) id j p).1
  · exact completedSampledWholePath_trace_le n dim e b h hg hmesh0 as ha hmesh hgap

end OAI.SKFluctuations.LaplaceWindowFormalization
