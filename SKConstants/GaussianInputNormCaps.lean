module
public import SKConstants.GaussianHamiltonian
public import SKConstants.GaussianProposalIndependentCompletions
import Mathlib.Tactic
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal Topology
namespace SKConstants.GaussianProposal
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma primitiveGaussian_coordinate_tail (i : ι) (R : ℝ) (hR : 0<R) :
    (primitiveGaussian ι).real {z | R≤|z i|} ≤2*Real.exp (-R^2/2) := by
  have hv : Var[fun z : EuclideanSpace ℝ ι=>z i;primitiveGaussian ι]=1 := by
    rw [← covariance_self (coordinate_gaussian i).aemeasurable,
      coordinate_covariance,if_pos rfl]
  simpa using gaussian_centered_two_sided_tail _ _ (coordinate_gaussian i)
    (coordinate_mean i) 1 R (by norm_num) hR hv

theorem primitiveGaussian_coordinate_max_tail (R : ℝ) (hR : 0<R) :
    (primitiveGaussian ι).real {z | ∃ i : ι,R≤|z i|} ≤
      2*(Fintype.card ι:ℝ)*Real.exp (-R^2/2) := by
  calc
    _ = (primitiveGaussian ι).real (⋃ i : ι,{z | R≤|z i|}) := by
      congr 1
      ext z
      simp
    _ ≤ ∑ i : ι,(primitiveGaussian ι).real {z | R≤|z i|} :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _i : ι,2*Real.exp (-R^2/2) :=
      Finset.sum_le_sum (fun i _=>primitiveGaussian_coordinate_tail i R hR)
    _ = 2*(Fintype.card ι:ℝ)*Real.exp (-R^2/2) := by simp; ring

lemma norm_sq_le_of_coordinate_cap (R : ℝ) (hR : 0≤R)
    (z : EuclideanSpace ℝ ι) (hz : ∀ i,|z i|≤R) :
    ‖z‖^2 ≤ (Fintype.card ι:ℝ)*R^2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  calc
    _ ≤ ∑ _i : ι,R^2 := Finset.sum_le_sum (fun i _ => by
      have h:=pow_le_pow_left₀ (abs_nonneg (z i)) (hz i) 2
      simpa only [sq_abs] using h)
    _ = _ := by simp

theorem primitiveGaussian_norm_sq_tail (R : ℝ) (hR : 0<R) :
    (primitiveGaussian ι).real {z | (Fintype.card ι:ℝ)*R^2<‖z‖^2} ≤
      2*(Fintype.card ι:ℝ)*Real.exp (-R^2/2) := by
  calc
    _ ≤ (primitiveGaussian ι).real {z | ∃ i : ι,R≤|z i|} := by
      apply measureReal_mono (h₂ := measure_ne_top (primitiveGaussian ι) _)
      intro z hz
      by_contra h
      change ¬(∃ i : ι,R≤|z i|) at h
      push_neg at h
      have he:=norm_sq_le_of_coordinate_cap R hR.le z (fun i=>(h i).le)
      exact (not_lt_of_ge he) hz
    _ ≤ _ := primitiveGaussian_coordinate_max_tail R hR

def paperCompletionNormCap (n : ℕ) (R : ℝ) :
    (q : ℕ) → PaperCompletionNoise n q → Prop
  | 0,_ => True
  | q+1,p => ‖p.1‖^2≤(n:ℝ)*R^2 ∧ paperCompletionNormCap n R q p.2

lemma measurableSet_paperCompletionNormCap (n : ℕ) (R : ℝ) :
    ∀ q,MeasurableSet {p | paperCompletionNormCap n R q p} := by
  intro q
  induction q with
  | zero => exact MeasurableSet.univ
  | succ q ih =>
    change MeasurableSet ({p | ‖p.1‖^2≤(n:ℝ)*R^2} ∩
      Prod.snd ⁻¹' {p | paperCompletionNormCap n R q p})
    exact (measurableSet_le (by fun_prop) measurable_const).inter
      (measurable_snd ih)

theorem paperCompletionNoiseLaw_norm_tail (n q : ℕ) (R : ℝ) (hR : 0<R) :
    (paperCompletionNoiseLaw n q).real {p | ¬paperCompletionNormCap n R q p} ≤
      2*(n:ℝ)*(q:ℝ)*Real.exp (-R^2/2) := by
  induction q with
  | zero => simp [paperCompletionNormCap]
  | succ q ih =>
    let μ := primitiveGaussian (Fin n)
    let ν := paperCompletionNoiseLaw n q
    have h1 : MeasurableSet {z : EuclideanSpace ℝ (Fin n) | (n:ℝ)*R^2<‖z‖^2} :=
      measurableSet_lt measurable_const (by fun_prop)
    have h2 : MeasurableSet {p | ¬paperCompletionNormCap n R q p} :=
      (measurableSet_paperCompletionNormCap n R q).compl
    have hp1 : (μ.prod ν).real (Prod.fst ⁻¹' {z | (n:ℝ)*R^2<‖z‖^2}) =
        μ.real {z | (n:ℝ)*R^2<‖z‖^2} := by
      rw [← map_measureReal_apply measurable_fst h1,Measure.map_fst_prod]
      simp
    have hp2 : (μ.prod ν).real (Prod.snd ⁻¹' {p | ¬paperCompletionNormCap n R q p}) =
        ν.real {p | ¬paperCompletionNormCap n R q p} := by
      rw [← map_measureReal_apply measurable_snd h2,Measure.map_snd_prod]
      simp
    change (μ.prod ν).real {p : EuclideanSpace ℝ (Fin n) × PaperCompletionNoise n q |
      ¬(‖p.1‖^2≤(n:ℝ)*R^2 ∧ paperCompletionNormCap n R q p.2)} ≤_
    have he : {p : EuclideanSpace ℝ (Fin n) × PaperCompletionNoise n q |
        ¬(‖p.1‖^2≤(n:ℝ)*R^2 ∧ paperCompletionNormCap n R q p.2)} =
      (Prod.fst ⁻¹' {z | (n:ℝ)*R^2<‖z‖^2}) ∪
      (Prod.snd ⁻¹' {p | ¬paperCompletionNormCap n R q p}) := by
      ext p
      change ¬(‖p.1‖^2≤(n:ℝ)*R^2 ∧ paperCompletionNormCap n R q p.2) ↔
        (n:ℝ)*R^2<‖p.1‖^2 ∨ ¬paperCompletionNormCap n R q p.2
      rw [not_and_or,not_le]
    rw [he]
    calc
      _ ≤ _ := measureReal_union_le _ _
      _ = μ.real {z | (n:ℝ)*R^2<‖z‖^2}+
          ν.real {p | ¬paperCompletionNormCap n R q p} := by rw [hp1,hp2]
      _ ≤ 2*(n:ℝ)*Real.exp (-R^2/2)+2*(n:ℝ)*(q:ℝ)*Real.exp (-R^2/2) :=
        add_le_add (by simpa using primitiveGaussian_norm_sq_tail (ι:=Fin n) R hR) ih
      _ = _ := by push_cast; ring

lemma goeMatrix_coordinate_cap (σ R : ℝ) (hR : 0≤R)
    (z : EuclideanSpace ℝ (ι×ι)) (hz : ∀ i,|z i|≤R) :
    ∀ i j,|goeMatrix σ z i j|≤2*|σ| *R := by
  intro i j
  rw [goeMatrix,abs_mul]
  have h:=abs_add_le (z (i,j)) (z (j,i))
  have he : |z (i,j)+z (j,i)|≤2*R := by linarith [hz (i,j),hz (j,i)]
  nlinarith [abs_nonneg σ]

theorem skDisorderLaw_entry_cap_tail (n : ℕ) (R : ℝ) (hR : 0<R) :
    (skDisorderLaw n).real {W | ¬∀ i j,
      |W i j|≤2*|1/Real.sqrt (2*(n:ℝ))| *R} ≤
      2*(n:ℝ)^2*Real.exp (-R^2/2) := by
  have hs : MeasurableSet {W : Matrix (Fin n) (Fin n) ℝ | ¬∀ i j,
      |W i j|≤2*|1/Real.sqrt (2*(n:ℝ))| *R} := by
    apply MeasurableSet.compl
    have he : MeasurableSet (⋂ i : Fin n,⋂ j : Fin n,
        {W : Matrix (Fin n) (Fin n) ℝ | |W i j|≤2*|1/Real.sqrt (2*(n:ℝ))| *R}) :=
      .iInter (fun i=>.iInter (fun j=>measurableSet_le
        (show Measurable (fun W : Matrix (Fin n) (Fin n) ℝ=>|W i j|) from
          ((measurable_pi_apply j).comp (measurable_pi_apply i)).abs) measurable_const))
    convert he using 1
    ext W
    simp only [Set.mem_iInter,Set.mem_ofPred_eq]
    rfl
  rw [skDisorderLaw,map_measureReal_apply (continuous_goeMatrix _).measurable hs]
  calc
    _ ≤ (primitiveGaussian (Fin n×Fin n)).real {z | ∃ i,R≤|z i|} := by
      apply measureReal_mono (h₂:=measure_ne_top (primitiveGaussian (Fin n×Fin n)) _)
      intro z hz
      by_contra h
      change ¬(∃ i : Fin n×Fin n,R≤|z i|) at h
      push_neg at h
      exact hz (goeMatrix_coordinate_cap _ R hR.le z (fun i=>(h i).le))
    _ ≤ _ := by
      simpa [Fintype.card_prod,pow_two] using
        primitiveGaussian_coordinate_max_tail (ι:=Fin n×Fin n) R hR

end SKConstants.GaussianProposal
