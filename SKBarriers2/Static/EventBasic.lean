module

public import SKBarriers2.Interfaces
public import OAI.Probability.SKBarriers.Replicas.MatrixMassUnion
public import OAI.Probability.SKBarriers.Replicas.OverlapCode

@[expose] public section

noncomputable section
open scoped BigOperators Topology
open Classical MeasureTheory ProbabilityTheory Filter Set
open OAI OAI.SK OAI.SK.Analytic

namespace SKBarriers2

theorem constrainedPartition_eq_restrictedPartition (n d : ℕ) (β : ℝ)
    (D : Fin d → Fin d → ℝ) (J : Disorder n) :
    constrainedPartition n d β D J = restrictedPartition β (matrixReplicaSet n d D) J := by
  unfold constrainedPartition restrictedPartition replicaEnergy
  conv_rhs => rw [← Finset.sum_coe_sort]
  exact (matrixReplicaEquiv n d D).sum_comp
    (fun s => Real.exp (β * ∑ a, hamiltonian J (s.val a)))

theorem restrictedPartition_rpow_integrable {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    (β s : ℝ) {T : Finset (ReplicaConfig n d)} (hT : T.Nonempty) :
    Integrable (fun J => restrictedPartition β T J ^ s) (disorderLaw n) := by
  let M := ∫ J, restrictedLogPartition β T J ∂disorderLaw n
  have h := ((restrictedLogPartition_subGaussian hn hd β hT).integrable_exp_mul s).mul_const
    (Real.exp (s * M))
  apply h.congr
  filter_upwards [] with J
  rw [← Real.exp_add, Real.rpow_def_of_pos (restrictedPartition_pos β hT J)]
  congr 1
  dsimp only [restrictedLogPartition, M]
  ring

theorem fractionalPressure_upper_tail {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    (β s U t : ℝ) (hs : 0 < s) (D : Fin d → Fin d → ℝ)
    (hD : Nonempty (MatrixStates n d D))
    (hgap : fractionalPressure n d β s D ≤ U) :
    (disorderLaw n).real {J | (n : ℝ) * (U + t) <
      restrictedLogPartition β (matrixReplicaSet n d D) J} ≤
      Real.exp (-(n : ℝ) * s * t) := by
  have hT := (matrixReplicaSet_nonempty_iff D).mpr hD
  have hint := restrictedPartition_rpow_integrable hn hd β s hT
  have hpos : 0 < ∫ J, restrictedPartition β (matrixReplicaSet n d D) J ^ s
      ∂disorderLaw n := by
    apply integral_pos_iff_support_of_nonneg (fun J => Real.rpow_nonneg
      (restrictedPartition_pos β hT J).le s) hint |>.mpr
    simp only [Function.support, ne_eq, Real.rpow_pos_of_pos
      (restrictedPartition_pos β hT _) s |>.ne', not_false_eq_true, ofPred_true,
      measure_univ]
    norm_num
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hi : (∫ J, restrictedPartition β (matrixReplicaSet n d D) J ^ s ∂disorderLaw n) ≤
      Real.exp ((n : ℝ) * s * U) := by
    apply (Real.log_le_iff_le_exp hpos).mp
    unfold fractionalPressure at hgap
    simp_rw [constrainedPartition_eq_restrictedPartition] at hgap
    exact (div_le_iff₀ (mul_pos hn' hs)).mp hgap |>.trans_eq (by ring)
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all _ (fun J => Real.rpow_nonneg (restrictedPartition_pos β hT J).le s))
    hint (Real.exp ((n : ℝ) * s * (U + t)))
  have hsub : {J | (n : ℝ) * (U + t) <
      restrictedLogPartition β (matrixReplicaSet n d D) J} ⊆
      {J | Real.exp ((n : ℝ) * s * (U + t)) ≤
        restrictedPartition β (matrixReplicaSet n d D) J ^ s} := by
    intro J hJ
    change (n : ℝ) * (U + t) < Real.log (restrictedPartition β (matrixReplicaSet n d D) J) at hJ
    change Real.exp _ ≤ _
    rw [Real.rpow_def_of_pos (restrictedPartition_pos β hT J)]
    apply Real.exp_le_exp.mpr
    exact (by nlinarith only [mul_lt_mul_of_pos_left hJ hs] :
      (n : ℝ) * s * (U + t) ≤
        Real.log (restrictedPartition β (matrixReplicaSet n d D) J) * s)
  calc
    _ ≤ (disorderLaw n).real {J | Real.exp ((n : ℝ) * s * (U + t)) ≤
        restrictedPartition β (matrixReplicaSet n d D) J ^ s} := measureReal_mono hsub
    _ ≤ Real.exp ((n : ℝ) * s * U) / Real.exp ((n : ℝ) * s * (U + t)) :=
      (le_div_iff₀ (Real.exp_pos _)).mpr (by nlinarith only [hmark, hi])
    _ = _ := by rw [← Real.exp_sub]; congr 1; ring

def staticCodeSlice {n d : ℕ} {C : Type*} [Fintype C]
    (code : ReplicaConfig n d → C) (T : Finset (ReplicaConfig n d)) (c : C) :
    Finset (ReplicaConfig n d) := T.filter (fun s => code s = c)

def staticNumeratorEvent {n d : ℕ} {C : Type*} [Fintype C]
    (β : ℝ) (code : ReplicaConfig n d → C) (T : Finset (ReplicaConfig n d)) (U : ℝ) :
    Set (Disorder n) :=
  {J | ∀ c, (staticCodeSlice code T c).Nonempty →
    restrictedLogPartition β (staticCodeSlice code T c) J ≤ (n : ℝ) * U}

theorem measurableSet_staticNumeratorEvent {n d : ℕ} {C : Type*} [Fintype C]
    (β : ℝ) (code : ReplicaConfig n d → C) (T : Finset (ReplicaConfig n d)) (U : ℝ) :
    MeasurableSet (staticNumeratorEvent β code T U) := by
  simp only [staticNumeratorEvent, ofPred_forall]
  apply MeasurableSet.iInter
  intro c
  apply MeasurableSet.iInter
  intro hc
  exact isClosed_le (continuous_restrictedLogPartition β hc) continuous_const |>.measurableSet

theorem staticNumeratorEvent_failure_le {n d : ℕ} {C : Type*} [Fintype C]
    (β : ℝ) (code : ReplicaConfig n d → C) (T : Finset (ReplicaConfig n d))
    (U e : ℝ) (he : 0 ≤ e)
    (htail : ∀ c, (staticCodeSlice code T c).Nonempty →
      (disorderLaw n).real {J | (n : ℝ) * U <
        restrictedLogPartition β (staticCodeSlice code T c) J} ≤ e) :
    (disorderLaw n).real (staticNumeratorEvent β code T U)ᶜ ≤ (Fintype.card C : ℝ) * e := by
  let A (c : C) : Set (Disorder n) :=
    if (staticCodeSlice code T c).Nonempty then
      {J | (n : ℝ) * U < restrictedLogPartition β (staticCodeSlice code T c) J}
    else ∅
  have hsub : (staticNumeratorEvent β code T U)ᶜ ⊆ ⋃ c, A c := by
    intro J hJ
    change ¬ ∀ c, (staticCodeSlice code T c).Nonempty →
      restrictedLogPartition β (staticCodeSlice code T c) J ≤ (n : ℝ) * U at hJ
    push Not at hJ
    obtain ⟨c, hc, h⟩ := hJ
    apply Set.mem_iUnion.mpr
    refine ⟨c, ?_⟩
    simpa only [A, ite_eq_left hc, Set.mem_ofPred_eq] using h
  calc
    _ ≤ (disorderLaw n).real (⋃ c, A c) := measureReal_mono hsub
    _ ≤ ∑ c, (disorderLaw n).real (A c) := measureReal_iUnion_fintype_le A
    _ ≤ ∑ _c : C, e := by
      apply Finset.sum_le_sum
      intro c _
      by_cases hc : (staticCodeSlice code T c).Nonempty
      · simpa only [A, ite_eq_left hc] using htail c hc
      · simpa only [A, ite_eq_right hc, measureReal_empty] using he
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem staticNumeratorEvent_mass_le {n d : ℕ} {C : Type*} [Fintype C]
    (β : ℝ) (code : ReplicaConfig n d → C) (T : Finset (ReplicaConfig n d))
    (U V : ℝ) (J : Disorder n)
    (hJ : J ∈ staticNumeratorEvent β code T U)
    (hden : (n : ℝ) * V ≤ logPartition β J) :
    replicaGibbsMass β J T ≤ (Fintype.card C : ℝ) *
      Real.exp ((n : ℝ) * (U - (d : ℝ) * V)) := by
  have heq : replicaGibbsMass β J T =
      ∑ c, replicaGibbsMass β J (staticCodeSlice code T c) :=
    (Finset.sum_fiberwise T code (fun s => ∏ a, gibbs β J (s a))).symm
  rw [heq]
  calc
    _ ≤ ∑ _c : C, Real.exp ((n : ℝ) * (U - (d : ℝ) * V)) := by
      apply Finset.sum_le_sum
      intro c _
      by_cases hc : (staticCodeSlice code T c).Nonempty
      · rw [replicaGibbsMass_eq_exp β J hc]
        apply Real.exp_le_exp.mpr
        have hnum := hJ c hc
        have hd := mul_le_mul_of_nonneg_left hden (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
        nlinarith only [hnum, hd]
      · rw [Finset.not_nonempty_iff_eq_empty.mp hc]
        exact (Real.exp_pos _).le
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

private theorem staticCodeSlice_subset_matrix {n d : ℕ} {C : Type*} [Fintype C]
    (code : ReplicaConfig n d → C)
    (hcode : ∀ s t, code s = code t → replicaGram s = replicaGram t)
    (T : Finset (ReplicaConfig n d)) {c : C} {s : ReplicaConfig n d}
    (hs : s ∈ staticCodeSlice code T c) :
    staticCodeSlice code T c ⊆ matrixReplicaSet n d (replicaGram s) := by
  intro t ht
  exact (mem_matrixReplicaSet _ _).mpr (hcode t s
    ((Finset.mem_filter.mp ht).2.trans (Finset.mem_filter.mp hs).2.symm))

theorem staticNumeratorEvent_gaussian_failure_le {n d : ℕ} {C : Type*} [Fintype C]
    (hn : 0 < n) (hd : 0 < d) {β : ℝ} (hβ : β ≠ 0)
    (code : ReplicaConfig n d → C)
    (hcode : ∀ s t, code s = code t → replicaGram s = replicaGram t)
    (T : Finset (ReplicaConfig n d)) (z : ℝ) (hz : 0 ≤ z)
    (hgap : ∀ s ∈ T, matrixConstrainedPressure n d β (replicaGram s) ≤
      (d : ℝ) * finiteParisiInf β - z) :
    (disorderLaw n).real
      (staticNumeratorEvent β code T ((d : ℝ) * finiteParisiInf β - z / 2))ᶜ ≤
      (Fintype.card C : ℝ) *
        Real.exp (-(4 * (z / 2) ^ 2 / (Real.pi ^ 2 * β ^ 2 * (d : ℝ) ^ 2)) * n) := by
  apply staticNumeratorEvent_failure_le β code T _ _ (Real.exp_pos _).le
  intro c hc
  obtain ⟨s, hs⟩ := hc
  have hp := (restrictedPressure_mono hn hd β ⟨s, hs⟩
    (staticCodeSlice_subset_matrix code hcode T hs)).trans
      (by simpa only [restrictedPressure_matrixReplicaSet] using hgap s (Finset.mem_filter.mp hs).1)
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hp' := (div_le_iff₀ hn').mp hp
  have hsub : {J | (n : ℝ) * ((d : ℝ) * finiteParisiInf β - z / 2) <
      restrictedLogPartition β (staticCodeSlice code T c) J} ⊆
      {J | (z / 2) * (n : ℝ) ≤ restrictedLogPartition β (staticCodeSlice code T c) J -
        ∫ K, restrictedLogPartition β (staticCodeSlice code T c) K ∂disorderLaw n} := by
    intro J hJ
    change (n : ℝ) * _ < _ at hJ
    change (z / 2) * (n : ℝ) ≤ restrictedLogPartition β (staticCodeSlice code T c) J -
      ∫ K, restrictedLogPartition β (staticCodeSlice code T c) K ∂disorderLaw n
    nlinarith only [hJ, hp']
  exact (measureReal_mono hsub).trans
    (restrictedLogPartition_upper_tail_linear hn hd hβ (by linarith : 0 ≤ z / 2) ⟨s, hs⟩)

theorem staticNumeratorEvent_fractional_failure_le {n d : ℕ} {C : Type*} [Fintype C]
    (hn : 0 < n) (hd : 0 < d) (β s U t : ℝ) (hs : 0 < s)
    (code : ReplicaConfig n d → C)
    (hcode : ∀ x y, code x = code y → replicaGram x = replicaGram y)
    (T : Finset (ReplicaConfig n d))
    (hgap : ∀ x ∈ T, fractionalPressure n d β s (replicaGram x) ≤ U) :
    (disorderLaw n).real (staticNumeratorEvent β code T (U + t))ᶜ ≤
      (Fintype.card C : ℝ) * Real.exp (-(n : ℝ) * s * t) := by
  apply staticNumeratorEvent_failure_le β code T _ _ (Real.exp_pos _).le
  intro c hc
  obtain ⟨x, hx⟩ := hc
  have hsub := staticCodeSlice_subset_matrix code hcode T hx
  have hfull : (matrixReplicaSet n d (replicaGram x)).Nonempty := ⟨x, hsub hx⟩
  have hlog (J : Disorder n) : restrictedLogPartition β (staticCodeSlice code T c) J ≤
      restrictedLogPartition β (matrixReplicaSet n d (replicaGram x)) J := by
    apply Real.log_le_log (restrictedPartition_pos β ⟨x, hx⟩ J)
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun y _ _ => (Real.exp_pos _).le)
  apply (measureReal_mono (fun J hJ => lt_of_lt_of_le hJ (hlog J))).trans
  exact fractionalPressure_upper_tail hn hd β s U t hs (replicaGram x)
    ((matrixReplicaSet_nonempty_iff _).mp hfull) (hgap x (Finset.mem_filter.mp hx).1)

def staticDenominatorEvent (n : ℕ) (β e : ℝ) : Set (Disorder n) :=
  {J | (n : ℝ) * (finiteParisiInf β - e) ≤ logPartition β J}

theorem measurableSet_staticDenominatorEvent (n : ℕ) (β e : ℝ) :
    MeasurableSet (staticDenominatorEvent n β e) :=
  isClosed_le continuous_const (continuous_logPartition β) |>.measurableSet

theorem staticDenominatorEvent_failure_le {n : ℕ} (hn : 0 < n) (β e b : ℝ)
    (hb : 0 < b)
    (hbias : finiteParisiInf β - quenchedPressure β n ≤ e - b) :
    (disorderLaw n).real (staticDenominatorEvent n β e)ᶜ ≤
      variance (fun J : Disorder n => logPartition β J) (disorderLaw n) /
        ((n : ℝ) * b) ^ 2 := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hlp : MemLp (fun J : Disorder n => logPartition β J) 2 (disorderLaw n) := by
    have h0 := (logPartition_subGaussian hn β).memLp 2
    norm_num only [ENNReal.coe_ofNat] at h0
    have h := h0.add
      (memLp_const (∫ J, logPartition β J ∂disorderLaw n))
    convert h using 1
    funext J
    exact (sub_add_cancel _ _).symm
  have hcheb := meas_ge_le_variance_div_sq hlp (mul_pos hn' hb)
  have hcheb' : (disorderLaw n).real
      {J | (n : ℝ) * b ≤ |logPartition β J - ∫ K, logPartition β K ∂disorderLaw n|} ≤
      variance (fun J : Disorder n => logPartition β J) (disorderLaw n) /
        ((n : ℝ) * b) ^ 2 := by
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hcheb).trans_eq
      (ENNReal.toReal_ofReal (div_nonneg (variance_nonneg _ _) (sq_nonneg _)))
  apply (measureReal_mono ?_).trans hcheb'
  intro J hJ
  have hJ' : logPartition β J < (n : ℝ) * (finiteParisiInf β - e) := not_le.mp hJ
  have hmean : (n : ℝ) * (finiteParisiInf β - (e - b)) ≤
      ∫ K, logPartition β K ∂disorderLaw n := by
    have h := (le_div_iff₀ hn').mp (show finiteParisiInf β - (e - b) ≤
      quenchedPressure β n by linarith only [hbias])
    nlinarith only [h]
  change _ ≤ |logPartition β J - _|
  exact (by linarith only [hJ', hmean] : (n : ℝ) * b ≤
    -(logPartition β J - ∫ K, logPartition β K ∂disorderLaw n)).trans (neg_le_abs _)

end SKBarriers2
