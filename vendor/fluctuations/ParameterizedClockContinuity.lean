module

public import PhysicalCapEnergyConcatenation

@[expose] public section

namespace OAI.SKFluctuations.LaplaceWindowFormalization
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Hierarchy GaussianCalculus
open scoped Topology NNReal BigOperators
variable {ι P : Type*} [Fintype ι] [TopologicalSpace P] [FirstCountableTopology P]

theorem parameter_testedPartition_continuous {F A : P → (ι → ℝ) → ℝ} {C : ℝ≥0} {K : ℝ}
    (hF : ∀ r, LipschitzWith C (F r))
    (hcF : Continuous (fun p : P × (ι → ℝ) => F p.1 p.2))
    (hcA : Continuous (fun p : P × (ι → ℝ) => A p.1 p.2))
    (hb : ∀ r y, |A r y| ≤ K) (m : ℝ) (x : ι → ℝ) :
    Continuous (fun p : ℝ × P => ∫ z, A p.2 (x+Real.sqrt p.1 • z)*Real.exp (m*F p.2 (x+Real.sqrt p.1 • z))
      ∂Measure.pi fun _ : ι => gaussianReal 0 1) := by
  let ν := Measure.pi fun _ : ι => gaussianReal 0 1
  have hν : ExponentialIncrement ν := exponentialIncrement_gaussian (fun _ => 1)
  apply continuous_iff_continuousAt.mpr
  intro p
  let B := |F p.2 x|+1
  let Q := Real.sqrt p.1+1
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hcbase : Continuous (fun q : ℝ × P => F q.2 x) := hcF.comp (continuous_snd.prodMk continuous_const)
  have hbase : ∀ᶠ q in 𝓝 p, |F q.2 x| < B := hcbase.abs.continuousAt.eventually
    (eventually_lt_nhds (by dsimp [B]; linarith))
  have hscale : ∀ᶠ q in 𝓝 p, Real.sqrt q.1 < Q :=
    (Real.continuous_sqrt.comp continuous_fst).continuousAt.eventually
      (eventually_lt_nhds (by dsimp [Q]; linarith))
  apply continuousAt_of_dominated
    (bound := fun z => K*Real.exp (|m| *B)*Real.exp (|m| *C*Q*‖z‖))
  · exact Eventually.of_forall fun q => by
      have hmap : Continuous (fun z : ι → ℝ => (q.2,x+Real.sqrt q.1 • z)) := by fun_prop
      exact ((hcA.comp hmap).mul (((hcF.comp hmap).const_mul m).rexp)).aestronglyMeasurable
  · filter_upwards [hbase,hscale] with q hq hq'
    exact Eventually.of_forall fun z => by
      have hK : 0 ≤ K := (abs_nonneg (A q.2 x)).trans (hb q.2 x)
      have hdiff : |F q.2 (x+Real.sqrt q.1 • z)-F q.2 x| ≤ (C:ℝ)*Real.sqrt q.1*‖z‖ := by
        simpa only [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,
          abs_of_nonneg (Real.sqrt_nonneg _),mul_assoc] using (hF q.2).dist_le_mul (x+Real.sqrt q.1 • z) x
      have hale : |F q.2 (x+Real.sqrt q.1 • z)| ≤ B+(C:ℝ)*Q*‖z‖ := by
        have hh := abs_add_le (F q.2 (x+Real.sqrt q.1 • z)-F q.2 x) (F q.2 x)
        rw [sub_add_cancel] at hh
        have hcomp : (C:ℝ)*Real.sqrt q.1*‖z‖ ≤ (C:ℝ)*Q*‖z‖ := by gcongr
        linarith
      have hexp : Real.exp (m*F q.2 (x+Real.sqrt q.1 • z)) ≤
          Real.exp (|m| *B)*Real.exp (|m| *C*Q*‖z‖) := by
        rw [← Real.exp_add,Real.exp_le_exp]
        have h1 := (le_abs_self (m*F q.2 (x+Real.sqrt q.1 • z))).trans_eq (abs_mul m _)
        have h2 := mul_le_mul_of_nonneg_left hale (abs_nonneg m)
        nlinarith
      change |A q.2 (x+Real.sqrt q.1 • z)*Real.exp (m*F q.2 (x+Real.sqrt q.1 • z))| ≤ _
      rw [abs_mul,abs_of_pos (Real.exp_pos _)]
      exact (mul_le_mul (hb q.2 _) hexp (Real.exp_nonneg _) hK).trans_eq (by ring)
  · exact (hν (|m| *C*Q)).const_mul _
  · exact Eventually.of_forall fun z => by
      have hmap : Continuous (fun q : ℝ × P => (q.2,x+Real.sqrt q.1 • z)) :=
        continuous_snd.prodMk (continuous_const.add ((Real.continuous_sqrt.comp continuous_fst).smul continuous_const))
      exact ((hcA.comp hmap).mul (((hcF.comp hmap).const_mul m).rexp)).continuousAt

 theorem parameter_clockTest_continuous {F A : P → (ι → ℝ) → ℝ} {C : ℝ≥0} {K : ℝ}
    (hF : ∀ r, LipschitzWith C (F r))
    (hcF : Continuous (fun p : P × (ι → ℝ) => F p.1 p.2))
    (hcA : Continuous (fun p : P × (ι → ℝ) => A p.1 p.2))
    (hb : ∀ r y, |A r y| ≤ K) (m : ℝ) (x : ι → ℝ) :
    Continuous (fun p : ℝ × P => clockTest m (F p.2) (A p.2) p.1 x) := by
  have hn := parameter_testedPartition_continuous hF hcF hcA hb m x
  have hd := parameter_testedPartition_continuous (A := fun _ _ => 1) hF hcF continuous_const
    (fun _ _ => le_refl |(1:ℝ)|) m x
  simp only [one_mul] at hd
  have hh := hn.div hd (fun p => (partition_pos m
    ((ExpNormBounded.exp_lipschitz (hF p.2) m).affine_integrable (exponentialIncrement_gaussian (fun _ : ι => 1)) x _)).ne')
  exact hh.congr fun p => (clockTest_eq_all (hF p.2).continuous
    (hcA.comp (continuous_const.prodMk continuous_id)) m p.1 x).symm

theorem parameter_clockContinuation_continuous {F : P → (ι → ℝ) → ℝ} {C : ℝ≥0}
    (hF : ∀ r, LipschitzWith C (F r))
    (hcF : Continuous (fun p : P × (ι → ℝ) => F p.1 p.2))
    (m : ℝ) (x : ι → ℝ) :
    Continuous (fun p : ℝ × P => clockContinuation m (F p.2) p.1 x) := by
  have hd := parameter_testedPartition_continuous (A := fun _ _ => 1) hF hcF
    continuous_const (fun _ _ => le_refl |(1 : ℝ)|) m x
  simp only [one_mul] at hd
  have hlog := hd.log (fun p => (partition_pos m
    ((ExpNormBounded.exp_lipschitz (hF p.2) m).affine_integrable
      (exponentialIncrement_gaussian (fun _ : ι => 1)) x _)).ne')
  exact (hlog.div_const m).congr (fun p => (clockContinuation_eq_all (hF p.2).continuous m p.1 x).symm)

theorem parameter_clockGradient_continuous {F G A B : P → (ι → ℝ) → ℝ} {C : ℝ≥0}
    (hF : ∀ r, LipschitzWith C (F r))
    (hcF : Continuous (fun p : P × (ι → ℝ) => F p.1 p.2))
    (hcG : Continuous (fun p : P × (ι → ℝ) => G p.1 p.2))
    (hcA : Continuous (fun p : P × (ι → ℝ) => A p.1 p.2))
    (hcB : Continuous (fun p : P × (ι → ℝ) => B p.1 p.2))
    (hbG : AbsBounded (fun p : P × (ι → ℝ) => G p.1 p.2))
    (hbA : AbsBounded (fun p : P × (ι → ℝ) => A p.1 p.2))
    (hbB : AbsBounded (fun p : P × (ι → ℝ) => B p.1 p.2)) (m : ℝ) (x : ι → ℝ) :
    Continuous (fun p : ℝ × P => clockGradient m (F p.2) (G p.2) (A p.2) (B p.2) p.1 x) := by
  have hbM := hbA.mul hbG
  obtain ⟨KA, _, bA⟩ := hbA
  obtain ⟨KG, _, bG⟩ := hbG
  obtain ⟨KB, _, bB⟩ := hbB
  obtain ⟨KM, _, bM⟩ := hbM
  exact (parameter_clockTest_continuous hF hcF hcB (fun r y => bB (r,y)) m x).add
    (((parameter_clockTest_continuous hF hcF (hcA.mul hcG) (fun r y => bM (r,y)) m x).sub
      ((parameter_clockTest_continuous hF hcF hcA (fun r y => bA (r,y)) m x).mul
        (parameter_clockTest_continuous hF hcF hcG (fun r y => bG (r,y)) m x))).const_mul m)

end
end OAI.SKFluctuations.LaplaceWindowFormalization
