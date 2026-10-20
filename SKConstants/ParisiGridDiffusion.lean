module
public import SKConstants.ParisiGridFeedback
public import SKConstants.ParisiPicardStability
public import SKConstants.ParisiCDFDiffusion

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace SKConstants.ParisiFullSupport
open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.ZeroTemperatureSK.Heat SKConstantsOAI.SK.Analytic

def gridCDFCoefficient (α : ℝ → ℝ) (h : ℝ≥0) (i : ℕ) : ℝ≥0 :=
  Real.toNNReal (α ((i:ℝ)*h))

lemma exists_grid_cell {h : ℝ≥0} (hh : 0 < h) {N : ℕ}
    (hN : (N:ℝ≥0)*h=1) {r : ℝ} (hr : r ∈ Ico (0:ℝ) 1) :
    ∃ i : ℕ, i < N ∧ ∃ δ : ℝ≥0, δ < h ∧ r=(i:ℝ)*h+δ := by
  let i : ℕ := ⌊r/(h:ℝ)⌋₊
  have hhR : 0 < (h:ℝ) := by exact_mod_cast hh
  have hrh : 0 ≤ r/(h:ℝ) := div_nonneg hr.1 hhR.le
  have hNh : (N:ℝ)*(h:ℝ)=1 := by exact_mod_cast hN
  have hi : i < N := (Nat.floor_lt hrh).mpr ((div_lt_iff₀ hhR).mpr (by simpa only [hNh] using hr.2))
  have hleft : (i:ℝ)*(h:ℝ) ≤ r := (le_div_iff₀ hhR).mp (Nat.floor_le hrh)
  have hright : r < ((i:ℝ)+1)*(h:ℝ) := (div_lt_iff₀ hhR).mp (Nat.lt_floor_add_one (r/(h:ℝ)))
  let δ : ℝ≥0 := Real.toNNReal (r-(i:ℝ)*h)
  have hδ : (δ:ℝ)=r-(i:ℝ)*h := Real.coe_toNNReal _ (sub_nonneg.mpr hleft)
  refine ⟨i,hi,δ,?_,?_⟩
  · rw [←NNReal.coe_lt_coe,hδ]; linarith
  · rw [hδ]; ring

lemma gridCDF_one (α : ℝ → ℝ) (h : ℝ≥0) (hh : 0 < h) (N : ℕ)
    (hN : (N:ℝ≥0)*h=1) : gridCDF α h 1 = α 1 := by
  have hNh : (N:ℝ)*(h:ℝ)=1 := by exact_mod_cast hN
  rw [gridCDF_eq_cell α (by exact_mod_cast hh) N
    ⟨hNh.le,by push_cast; linarith [h.coe_pos.mpr hh]⟩,hNh]

theorem finiteValue_grid_eq_scalarCDFValue
    (α : ℝ → ℝ) (hα : Monotone α) (ha : ∀ r, α r ∈ Icc (0:ℝ) 1)
    (β : ℝ) (h : ℝ≥0) (hh : 0 < h) (N : ℕ) (hN : (N:ℝ≥0)*h=1)
    {r : ℝ} (hr : r ∈ Ico (0:ℝ) 1) :
    finiteValue (gridCDFCoefficient α h) (Real.toNNReal (β^2)*h)
      (softAbs 1) N 0 (β^2*r) = scalarCDFValue β (gridCDF α h) r (Real.toNNReal (1-r)) := by
  obtain ⟨i,hi,δ,hδ,he⟩ := exists_grid_cell hh hN hr
  have hf := regularDatum_softAbs (by norm_num : (1:ℝ) ≠ 0)
  have hLip := softAbs_lipschitz (by norm_num : (1:ℝ) ≠ 0)
  have hterminal : softAbs 1 = scalarSpinTerminal := by funext x; simp [softAbs,scalarSpinTerminal]
  have hfb : BoundedDerivs (softAbs 1) := hterminal ▸ scalarSpinTerminal_regular
  have H := finiteValue_eq_gridCDFOperator_cell α hα ha hf hfb hLip β h hh N i hi hN.le δ hδ.le
  have hdur : ((N-i:ℕ):ℝ≥0)*h-δ = Real.toNNReal (1-r) := by
    ext
    have hδNi : δ ≤ ((N-i:ℕ):ℝ≥0)*h := by
      have hge : (1:ℝ≥0) ≤ (N-i:ℕ) := by exact_mod_cast (show 1 ≤ N-i by omega)
      exact hδ.le.trans (by nlinarith)
    rw [NNReal.coe_sub hδNi,Real.coe_toNNReal _ (by linarith [hr.2])]
    rw [NNReal.coe_mul,NNReal.coe_natCast,Nat.cast_sub hi.le]
    have hNh : (N:ℝ)*(h:ℝ)=1 := by exact_mod_cast hN
    rw [he]
    nlinarith
  rw [hdur,←he,Real.coe_toNNReal _ (sq_nonneg β)] at H
  rw [hterminal] at H
  rw [hterminal]
  exact H

theorem finiteFeedback_grid_drift_eq
    (α : ℝ → ℝ) (hα : Monotone α) (ha : ∀ r, α r ∈ Icc (0:ℝ) 1)
    (β : ℝ) (hβ : β ≠ 0) (h : ℝ≥0) (hh : 0 < h) (N : ℕ) (hN : (N:ℝ≥0)*h=1)
    {r : ℝ} (hr : r ∈ Ico (0:ℝ) 1) (x : ℝ) :
    (finiteFeedback (regularDatum_softAbs (by norm_num : (1:ℝ) ≠ 0))
      (softAbs_lipschitz (by norm_num : (1:ℝ) ≠ 0))
      (gridCDFCoefficient α h) (Real.toNNReal (β^2)*h) N 0).f (β^2*r) x =
      gridCDF α h r * scalarCDFGradient β (gridCDF α h) r (Real.toNNReal (1-r)) x := by
  obtain ⟨i,hi,δ,hδ,he⟩ := exists_grid_cell hh hN hr
  let c := gridCDFCoefficient α h
  let H : ℝ≥0 := Real.toNNReal (β^2)*h
  let d : ℝ≥0 := Real.toNNReal (β^2)*δ
  have hstart : β^2*r=(i:ℝ)*H+d := by
    simp only [H,d,NNReal.coe_mul,Real.coe_toNNReal _ (sq_nonneg β)]
    rw [he]
    ring
  have hdH : (d:ℝ) < H := by
    apply NNReal.coe_lt_coe.mpr
    exact mul_lt_mul_of_pos_left hδ (Real.toNNReal_pos.mpr (sq_pos_of_ne_zero hβ))
  have hcoeff : rightCoeff c H N 0 (β^2*r) = gridCDF α h r := by
    rw [hstart,rightCoeff_shift c H hi.le 0 d.coe_nonneg]
    have hiN : N-i = (N-(i+1))+1 := by omega
    simp only [Nat.zero_add,hiN,rightCoeff,ite_eq_left hdH]
    change (Real.toNNReal (α ((i:ℝ)*h)):ℝ) = _
    rw [Real.coe_toNNReal _ (ha _).1,gridCDF_eq_cell α (by exact_mod_cast hh) i]
    rw [he]; constructor
    · exact le_add_of_nonneg_right δ.coe_nonneg
    · push_cast
      have hhδ : (δ:ℝ)<h := by exact_mod_cast hδ
      linarith
  change rightCoeff c H N 0 (β^2*r)*deriv (finiteValue c H (softAbs 1) N 0 (β^2*r)) x = _
  rw [hcoeff,finiteValue_grid_eq_scalarCDFValue α hα ha β h hh N hN hr]
  congr 1
  exact (scalarCDFValue_hasDerivAt β (show ∀ z, gridCDF α h z ∈ Icc (0:ℝ) 1 from fun z => ha _)
    (gridCDF_mono hα (by exact_mod_cast hh)) r _
    (by rw [Real.toNNReal_le_iff_le_coe]; simpa using sub_le_self (1:ℝ) hr.1) x).deriv

end SKConstants.ParisiFullSupport
