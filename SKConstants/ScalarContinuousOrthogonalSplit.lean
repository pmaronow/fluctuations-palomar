module

public import SKConstants.ScalarOrthogonalBlockSplit
public import SKConstants.ScalarStieltjesRiemann
import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal BigOperators
namespace SKConstants
set_option backward.isDefEq.respectTransparency false

theorem scalarBrownianAffineTime_step_sub (a h : ℝ≥0) (k : ℕ) :
    scalarBrownianAffineTime a h (k+1)-scalarBrownianAffineTime a h k=h := by
  apply NNReal.eq
  rw [NNReal.coe_sub ((scalarBrownianAffineTime_mono a h) (by omega))]
  simp only [scalarBrownianAffineTime,NNReal.coe_add,NNReal.coe_mul,NNReal.coe_natCast,
    Nat.cast_add,Nat.cast_one,NNReal.coe_one]
  ring

theorem scalarBrownianAffineTime_dyadic_block (a h : ℝ≥0) (l k i : ℕ) :
    (scalarBrownianAffineTime a (h/(2 : ℝ≥0)^l) (i+2^l*k) : ℝ) =
      scalarStieltjesDyadicIntervalTime (scalarBrownianAffineTime a h k)
        (scalarBrownianAffineTime a h (k+1)) l i := by
  rw [scalarStieltjesDyadicIntervalTime,scalarBrownianAffineTime_step_sub]
  simp only [scalarBrownianAffineTime,scalarStieltjesDyadicTime,NNReal.coe_add,
    NNReal.coe_mul,NNReal.coe_div,NNReal.coe_pow,NNReal.coe_ofNat,NNReal.coe_natCast,
    Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  field_simp
  ring

theorem scalarBrownianAffineTime_dyadic_end (a h : ℝ≥0) (d l : ℕ) :
    scalarBrownianAffineTime a (h/(2 : ℝ≥0)^l) (d*2^l) = scalarBrownianAffineTime a h d := by
  apply NNReal.eq
  simp only [scalarBrownianAffineTime,NNReal.coe_add,NNReal.coe_mul,NNReal.coe_div,
    NNReal.coe_pow,NNReal.coe_ofNat,NNReal.coe_natCast,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  field_simp

variable {Ω : Type*}

theorem scalarBrownianWeightedBlockSum_eq_interval {d : ℕ}
    (f : StieltjesFunction ℝ) (B : ℝ≥0 → Ω → ℝ) (a h : ℝ≥0) (k : Fin d)
    (F : ScalarContinuousPath (scalarBrownianAffineTime a h d)) (ω : Ω)
    (hF : ∀ t : Icc (0 : ℝ) (scalarBrownianAffineTime a h d : ℝ),
      F t = B ⟨t,t.property.1⟩ ω) (l : ℕ) :
    (∑ j : Fin (d*2^l),
      (if j.divNat=k then f (scalarBrownianAffineTime a (h/(2 : ℝ≥0)^l) j : ℝ) else 0)*
        brownianMeshIncrement B (scalarBrownianAffineTime a (h/(2 : ℝ≥0)^l)) j ω) =
      scalarStieltjesDyadicIntervalSum f (scalarBrownianAffineTime a h d) F
        (scalarBrownianAffineTime a h k) (scalarBrownianAffineTime a h (k+1)) l := by
  rw [scalarBlockSelected_sum]
  unfold scalarStieltjesDyadicIntervalSum scalarStieltjesMeshSum
  have hp (i : Fin (2^l)) : (finProdFinEquiv (k,i)).val=i.val+2^l*k.val := rfl
  simp only [brownianMeshIncrement,hp]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ =>
    f (scalarBrownianAffineTime a (h/(2 : ℝ≥0)^l) (i+2^l*k) : ℝ)*
      (B (scalarBrownianAffineTime a (h/(2 : ℝ≥0)^l) (i+2^l*k+1)) ω-
        B (scalarBrownianAffineTime a (h/(2 : ℝ≥0)^l) (i+2^l*k)) ω))]
  apply Finset.sum_congr rfl
  intro i hi
  have he (j : ℕ) (hj : j ≤ 2^l) :
      IccExtend (scalarBrownianAffineTime a h d).coe_nonneg F
        (scalarStieltjesDyadicIntervalTime (scalarBrownianAffineTime a h k)
          (scalarBrownianAffineTime a h (k+1)) l j) =
        B (scalarBrownianAffineTime a (h/(2 : ℝ≥0)^l) (j+2^l*k)) ω := by
    let q := scalarBrownianAffineTime a (h/(2 : ℝ≥0)^l)
    have hindex : j+2^l*k.val ≤ d*2^l := by nlinarith [k.isLt]
    have hle : q (j+2^l*k.val) ≤ scalarBrownianAffineTime a h d := by
      rw [← scalarBrownianAffineTime_dyadic_end a h d l]
      exact scalarBrownianAffineTime_mono _ _ hindex
    have hm : scalarStieltjesDyadicIntervalTime (scalarBrownianAffineTime a h k)
        (scalarBrownianAffineTime a h (k+1)) l j ∈
        Icc (0 : ℝ) (scalarBrownianAffineTime a h d : ℝ) := by
      rw [← scalarBrownianAffineTime_dyadic_block]
      exact ⟨(q _).coe_nonneg,hle⟩
    simp only [IccExtend,Function.comp_apply,projIcc_of_mem _ hm]
    have hq : (⟨_,hm.1⟩ : ℝ≥0) = q (j+2^l*k.val) := by
      apply NNReal.eq
      exact (scalarBrownianAffineTime_dyadic_block a h l k j).symm
    simpa only [hq] using hF ⟨_,hm⟩
  rw [scalarBrownianAffineTime_dyadic_block]
  rw [he i (Finset.mem_range.mp hi).le,he (i+1) (Finset.mem_range.mp hi)]
  simp only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

def scalarOrthogonalWeightedAuxPath (f g : StieltjesFunction ℝ)
    (hf : Continuous f) (hg : Continuous g) (H : ℝ≥0)
    (p : ScalarContinuousPath H × ScalarContinuousPath H) : ScalarContinuousPath H :=
  scalarStieltjesWeightedPath g hg H p.1 + scalarStieltjesWeightedPath f hf H p.2

theorem measurable_scalarOrthogonalWeightedAuxPath (f g : StieltjesFunction ℝ)
    (hf : Continuous f) (hg : Continuous g) (H : ℝ≥0) :
    Measurable (scalarOrthogonalWeightedAuxPath f g hf hg H) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  exact (((ContinuousMap.measurable_eval t).comp
    (measurable_scalarStieltjesWeightedPath g hg H)).comp measurable_fst).add
      (((ContinuousMap.measurable_eval t).comp
        (measurable_scalarStieltjesWeightedPath f hf H)).comp measurable_snd)

def scalarUniformPathBlockIncrement {d : ℕ} (a h : ℝ≥0)
    (X : ScalarContinuousPath (scalarBrownianAffineTime a h d)) (k : Fin d) : ℝ :=
  X ⟨scalarBrownianAffineTime a h (k+1), (scalarBrownianAffineTime a h (k+1)).coe_nonneg,
      scalarBrownianAffineTime_mono a h (by omega)⟩ -
    X ⟨scalarBrownianAffineTime a h k, (scalarBrownianAffineTime a h k).coe_nonneg,
      scalarBrownianAffineTime_mono a h k.isLt.le⟩

def scalarOrthogonalUniformBlockIncrements {d : ℕ} (f g : StieltjesFunction ℝ)
    (hf : Continuous f) (hg : Continuous g) (a h : ℝ≥0)
    (p : ScalarContinuousPath (scalarBrownianAffineTime a h d) ×
      ScalarContinuousPath (scalarBrownianAffineTime a h d)) : (Fin d ⊕ Fin d) → ℝ :=
  Sum.elim
    (fun k => scalarUniformPathBlockIncrement a h
      (scalarTwoDriverWeightedPath f g hf hg _ p) k)
    (fun k => scalarUniformPathBlockIncrement a h
      (scalarOrthogonalWeightedAuxPath f g hf hg _ p) k)

theorem measurable_scalarOrthogonalUniformBlockIncrements {d : ℕ}
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g) (a h : ℝ≥0) :
    Measurable (scalarOrthogonalUniformBlockIncrements (d := d) f g hf hg a h) := by
  apply Measurable.of_eval
  intro k
  cases k with
  | inl k =>
    exact ((ContinuousMap.measurable_eval _).comp
      (measurable_scalarTwoDriverWeightedPath f g hf hg _)).sub
      ((ContinuousMap.measurable_eval _).comp (measurable_scalarTwoDriverWeightedPath f g hf hg _))
  | inr k =>
    exact ((ContinuousMap.measurable_eval _).comp
      (measurable_scalarOrthogonalWeightedAuxPath f g hf hg _)).sub
      ((ContinuousMap.measurable_eval _).comp (measurable_scalarOrthogonalWeightedAuxPath f g hf hg _))

theorem scalarOrthogonalDyadicBlocks_pathwise_limit {d : ℕ}
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g) (a h : ℝ≥0)
    (F G : ScalarContinuousPath (scalarBrownianAffineTime a h d)) :
    Tendsto (fun l => Sum.elim
      (fun k : Fin d => -scalarStieltjesDyadicIntervalSum f _ F
        (scalarBrownianAffineTime a h k) (scalarBrownianAffineTime a h (k+1)) l +
        scalarStieltjesDyadicIntervalSum g _ G
          (scalarBrownianAffineTime a h k) (scalarBrownianAffineTime a h (k+1)) l)
      (fun k : Fin d => scalarStieltjesDyadicIntervalSum g _ F
        (scalarBrownianAffineTime a h k) (scalarBrownianAffineTime a h (k+1)) l +
        scalarStieltjesDyadicIntervalSum f _ G
          (scalarBrownianAffineTime a h k) (scalarBrownianAffineTime a h (k+1)) l)) atTop
      (nhds (scalarOrthogonalUniformBlockIncrements f g hf hg a h (F,G))) := by
  apply tendsto_pi_nhds.mpr
  intro k
  have ht (k : Fin d) : scalarBrownianAffineTime a h (k+1) ≤ scalarBrownianAffineTime a h d :=
    scalarBrownianAffineTime_mono a h (by omega)
  have hs (k : Fin d) : scalarBrownianAffineTime a h k ≤ scalarBrownianAffineTime a h (k+1) :=
    scalarBrownianAffineTime_mono a h (by omega)
  cases k with
  | inl k =>
    have hl := (scalarStieltjesDyadicIntervalSum_tendsto f hf _ _ _ (hs k) (ht k) F).neg.add
      (scalarStieltjesDyadicIntervalSum_tendsto g hg _ _ _ (hs k) (ht k) G)
    have he : scalarOrthogonalUniformBlockIncrements f g hf hg a h (F,G) (.inl k) =
        -((scalarStieltjesWeightedPath f hf _ F) ⟨_,(scalarBrownianAffineTime a h (k+1)).coe_nonneg,ht k⟩-
          (scalarStieltjesWeightedPath f hf _ F) ⟨_,(scalarBrownianAffineTime a h k).coe_nonneg,(hs k).trans (ht k)⟩)+
        ((scalarStieltjesWeightedPath g hg _ G) ⟨_,(scalarBrownianAffineTime a h (k+1)).coe_nonneg,ht k⟩-
          (scalarStieltjesWeightedPath g hg _ G) ⟨_,(scalarBrownianAffineTime a h k).coe_nonneg,(hs k).trans (ht k)⟩) := by
      simp only [scalarOrthogonalUniformBlockIncrements,Sum.elim_inl]
      dsimp [scalarUniformPathBlockIncrement,scalarTwoDriverWeightedPath]
      ring
    rw [he]
    exact hl
  | inr k =>
    have hl := (scalarStieltjesDyadicIntervalSum_tendsto g hg _ _ _ (hs k) (ht k) F).add
      (scalarStieltjesDyadicIntervalSum_tendsto f hf _ _ _ (hs k) (ht k) G)
    have he : scalarOrthogonalUniformBlockIncrements f g hf hg a h (F,G) (.inr k) =
        ((scalarStieltjesWeightedPath g hg _ F) ⟨_,(scalarBrownianAffineTime a h (k+1)).coe_nonneg,ht k⟩-
          (scalarStieltjesWeightedPath g hg _ F) ⟨_,(scalarBrownianAffineTime a h k).coe_nonneg,(hs k).trans (ht k)⟩)+
        ((scalarStieltjesWeightedPath f hf _ G) ⟨_,(scalarBrownianAffineTime a h (k+1)).coe_nonneg,ht k⟩-
          (scalarStieltjesWeightedPath f hf _ G) ⟨_,(scalarBrownianAffineTime a h k).coe_nonneg,(hs k).trans (ht k)⟩) := by
      simp only [scalarOrthogonalUniformBlockIncrements,Sum.elim_inr]
      dsimp [scalarUniformPathBlockIncrement,scalarOrthogonalWeightedAuxPath]
      ring
    rw [he]
    exact hl

theorem scalarOrthogonalDyadicBlocks_eq_pathSums {d : ℕ}
    (f g : StieltjesFunction ℝ) (B : ℝ≥0 → Ω → ℝ) {A : Type*} (C : ℝ≥0 → A → ℝ)
    (a h : ℝ≥0) (F G : ScalarContinuousPath (scalarBrownianAffineTime a h d))
    (u : Ω × A)
    (hF : ∀ t : Icc (0 : ℝ) (scalarBrownianAffineTime a h d : ℝ), F t=B ⟨t,t.property.1⟩ u.1)
    (hG : ∀ t : Icc (0 : ℝ) (scalarBrownianAffineTime a h d : ℝ), G t=C ⟨t,t.property.1⟩ u.2)
    (l : ℕ) :
    (fun k => ∑ j, scalarBlockSplitCoefficients
      (fun i : Fin (d*2^l) => -f (scalarBrownianAffineTime a (h/(2 : ℝ≥0)^l) i : ℝ))
      (fun i : Fin (d*2^l) => g (scalarBrownianAffineTime a (h/(2 : ℝ≥0)^l) i : ℝ)) k j*
        scalarTwoBrownianMeshFamily B C (scalarBrownianAffineTime a (h/(2 : ℝ≥0)^l)) (d*2^l) u j) =
    Sum.elim
      (fun k : Fin d => -scalarStieltjesDyadicIntervalSum f _ F
        (scalarBrownianAffineTime a h k) (scalarBrownianAffineTime a h (k+1)) l +
        scalarStieltjesDyadicIntervalSum g _ G
          (scalarBrownianAffineTime a h k) (scalarBrownianAffineTime a h (k+1)) l)
      (fun k : Fin d => scalarStieltjesDyadicIntervalSum g _ F
        (scalarBrownianAffineTime a h k) (scalarBrownianAffineTime a h (k+1)) l +
        scalarStieltjesDyadicIntervalSum f _ G
          (scalarBrownianAffineTime a h k) (scalarBrownianAffineTime a h (k+1)) l) := by
  funext k
  cases k with
  | inl k =>
    simp only [scalarBlockSplitCoefficients,scalarTwoBrownianMeshFamily,Fintype.sum_sum_type,
      Sum.elim_inl,Sum.elim_inr]
    have hn : (∑ j : Fin (d*2^l),
        (if j.divNat=k then -f (scalarBrownianAffineTime a (h/(2 : ℝ≥0)^l) j : ℝ) else 0)*
          brownianMeshIncrement B (scalarBrownianAffineTime a (h/(2 : ℝ≥0)^l)) j u.1) =
        -(∑ j : Fin (d*2^l),
          (if j.divNat=k then f (scalarBrownianAffineTime a (h/(2 : ℝ≥0)^l) j : ℝ) else 0)*
            brownianMeshIncrement B (scalarBrownianAffineTime a (h/(2 : ℝ≥0)^l)) j u.1) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j.divNat=k <;> simp [hj]
    rw [hn,scalarBrownianWeightedBlockSum_eq_interval f B a h k F u.1 hF,
      scalarBrownianWeightedBlockSum_eq_interval g C a h k G u.2 hG]
  | inr k =>
    simp only [scalarBlockSplitCoefficients,scalarTwoBrownianMeshFamily,Fintype.sum_sum_type,
      Sum.elim_inl,Sum.elim_inr,neg_neg]
    rw [scalarBrownianWeightedBlockSum_eq_interval g B a h k F u.1 hF,
      scalarBrownianWeightedBlockSum_eq_interval f C a h k G u.2 hG]

variable [MeasurableSpace Ω] {A : Type*} [MeasurableSpace A]

theorem scalarOrthogonalUniformBlockIncrements_hasLaw {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (Q : Measure A) [IsProbabilityMeasure Q]
    (B : ℝ≥0 → Ω → ℝ) (C : ℝ≥0 → A → ℝ)
    (hB : IsPreBrownianReal B P) (hC : IsPreBrownianReal C Q)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g) (a h : ℝ≥0)
    (hunit : ∀ s ∈ Icc (0 : ℝ) (scalarBrownianAffineTime a h d : ℝ), (f s)^2+(g s)^2=1)
    (F : Ω → ScalarContinuousPath (scalarBrownianAffineTime a h d))
    (G : A → ScalarContinuousPath (scalarBrownianAffineTime a h d))
    (hFm : Measurable F) (hGm : Measurable G)
    (hF : ∀ᵐ ω ∂P, ∀ t : Icc (0 : ℝ) (scalarBrownianAffineTime a h d : ℝ), F ω t=B ⟨t,t.property.1⟩ ω)
    (hG : ∀ᵐ ω ∂Q, ∀ t : Icc (0 : ℝ) (scalarBrownianAffineTime a h d : ℝ), G ω t=C ⟨t,t.property.1⟩ ω) :
    HasLaw (fun u : Ω × A => scalarOrthogonalUniformBlockIncrements f g hf hg a h (F u.1,G u.2))
      (Measure.pi (fun _ : Fin d ⊕ Fin d => gaussianReal 0 h)) (P.prod Q) := by
  let X : ℕ → Ω × A → (Fin d ⊕ Fin d) → ℝ := fun l u k =>
    ∑ j, scalarBlockSplitCoefficients
      (fun i : Fin (d*2^l) => -f (scalarBrownianAffineTime a (h/(2 : ℝ≥0)^l) i : ℝ))
      (fun i : Fin (d*2^l) => g (scalarBrownianAffineTime a (h/(2 : ℝ≥0)^l) i : ℝ)) k j*
        scalarTwoBrownianMeshFamily B C (scalarBrownianAffineTime a (h/(2 : ℝ≥0)^l)) (d*2^l) u j
  have hl (l : ℕ) : HasLaw (X l) (Measure.pi (fun _ : Fin d ⊕ Fin d => gaussianReal 0 h)) (P.prod Q) := by
    have hc (j : Fin (d*2^l)) :
        (scalarBrownianAffineTime a (h/(2 : ℝ≥0)^l) j : ℝ) ∈
          Icc (0 : ℝ) (scalarBrownianAffineTime a h d : ℝ) := by
      constructor
      · exact (scalarBrownianAffineTime _ _ j).coe_nonneg
      · rw [← scalarBrownianAffineTime_dyadic_end a h d l]
        exact scalarBrownianAffineTime_mono _ _ j.isLt.le
    have hl := scalarOrthogonalRefiningBlocks_hasLaw P Q B C hB hC a (h/(2 : ℝ≥0)^l)
      (fun i : Fin (d*2^l) => -f (scalarBrownianAffineTime a (h/(2 : ℝ≥0)^l) i : ℝ))
      (fun i : Fin (d*2^l) => g (scalarBrownianAffineTime a (h/(2 : ℝ≥0)^l) i : ℝ))
      (fun j => by simpa only [neg_sq] using hunit _ (hc j))
    have hv : ((2^l : ℕ) : ℝ≥0)*(h/(2 : ℝ≥0)^l)=h := by
      simp only [Nat.cast_pow,Nat.cast_ofNat]
      field_simp
    simpa only [hv] using hl
  have hm : Measurable (fun u : Ω × A =>
      scalarOrthogonalUniformBlockIncrements f g hf hg a h (F u.1,G u.2)) :=
    (measurable_scalarOrthogonalUniformBlockIncrements f g hf hg a h).comp (hFm.prodMap hGm)
  apply scalarHasLaw_borel_of_ae_tendsto (P.prod Q) _ X _ hl hm.aemeasurable
  filter_upwards [(measurePreserving_fst (μ := P) (ν := Q)).quasiMeasurePreserving.ae hF,
    (measurePreserving_snd (μ := P) (ν := Q)).quasiMeasurePreserving.ae hG] with u huF huG
  have he (l : ℕ) := scalarOrthogonalDyadicBlocks_eq_pathSums f g B C a h (F u.1) (G u.2) u huF huG l
  change Tendsto (fun l => X l u) atTop _
  simp_rw [show ∀ l, X l u = _ from he]
  exact scalarOrthogonalDyadicBlocks_pathwise_limit f g hf hg a h (F u.1) (G u.2)

end SKConstants
