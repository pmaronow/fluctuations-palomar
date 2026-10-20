module
public import SKConstants.ParisiGridCDF
public import SKConstants.ParisiFiniteFeedbackLaw

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace SKConstants.ParisiFullSupport
open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.ZeroTemperatureSK.Heat SKConstantsOAI.SK.Analytic

def uniformGridChain (α : ℝ → ℝ) (h : ℝ≥0) (N i : ℕ) : List (ℝ × ℝ≥0) :=
  List.ofFn (fun k : Fin N => (α (((i+k:ℕ):ℝ)*h),h))

lemma uniformGridChain_cons (α : ℝ → ℝ) (h : ℝ≥0) (N i : ℕ) :
    uniformGridChain α h (N+1) i = (α ((i:ℝ)*h),h)::uniformGridChain α h N (i+1) := by
  unfold uniformGridChain
  rw [List.ofFn_succ]
  simp only [Fin.val_zero, Nat.add_zero]
  congr 1
  congr 1
  funext k
  apply Prod.ext
  · apply congrArg α
    congr 1
    change ((i+(k.val+1):ℕ):ℝ) = (((i+1)+k.val:ℕ):ℝ)
    congr 1
    omega
  · rfl

lemma uniformGridChain_duration (α : ℝ → ℝ) (h : ℝ≥0) (N i : ℕ) :
    chainDuration (uniformGridChain α h N i) = (N:ℝ≥0)*h := by
  induction N generalizing i with
  | zero => simp [uniformGridChain, chainDuration]
  | succ N ih => rw [uniformGridChain_cons,chainDuration_cons,ih]; push_cast; ring

lemma uniformGridChain_mass (α : ℝ → ℝ) (ha : ∀ r, α r ∈ Icc (0:ℝ) 1)
    (h : ℝ≥0) (N i : ℕ) : ∀ p ∈ uniformGridChain α h N i, p.1 ∈ Icc (0:ℝ) 1 := by
  intro p hp
  obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hp
  exact ha _

lemma uniformGridChain_models (α : ℝ → ℝ) (h : ℝ≥0) (hh : 0 < h) (N i : ℕ) :
    TimeChainModels (gridCDF α h) ((i:ℝ)*h) (uniformGridChain α h N i) := by
  induction N generalizing i with
  | zero => trivial
  | succ N ih =>
    rw [uniformGridChain_cons]
    constructor
    · intro r hr
      apply gridCDF_eq_cell α (by exact_mod_cast hh) i
      convert hr using 1 <;> push_cast <;> ring
    · convert ih (i+1) using 1 <;> push_cast <;> ring

lemma uniformGridChain_eq_cascade (α : ℝ → ℝ) (ha : ∀ r, α r ∈ Icc (0:ℝ) 1)
    {f : ℝ → ℝ} (hf : RegularDatum f) (hLip : LipschitzWith 1 f)
    (β : ℝ) (h : ℝ≥0) (N i : ℕ) :
    scalarTimeChain β (uniformGridChain α h N i) f =
      cascade (fun k => Real.toNNReal (α ((k:ℝ)*h))) (Real.toNNReal (β^2)*h) f N i := by
  rw [← scalarTimeChain_uniform_eq_cascade hf hLip]
  congr 1
  unfold uniformGridChain
  congr 1
  funext k
  simp only [Real.coe_toNNReal _ (ha _).1]

theorem finiteValue_eq_gridCDFOperator_cell
    (α : ℝ → ℝ) (hα : Monotone α) (ha : ∀ r, α r ∈ Icc (0:ℝ) 1)
    {f : ℝ → ℝ} (hf : RegularDatum f) (hfb : BoundedDerivs f) (hLip : LipschitzWith 1 f)
    (β : ℝ) (h : ℝ≥0) (hh : 0 < h) (N i : ℕ) (hi : i < N)
    (hN : (N:ℝ≥0)*h ≤ 1) (δ : ℝ≥0) (hδ : δ ≤ h) :
    finiteValue (fun k => Real.toNNReal (α ((k:ℝ)*h))) (Real.toNNReal (β^2)*h)
      f N 0 ((Real.toNNReal (β^2):ℝ)*((i:ℝ)*h+δ)) =
      scalarCDFOperator β (gridCDF α h) ((i:ℝ)*h+δ) (((N-i:ℕ):ℝ≥0)*h-δ) f := by
  let c : ℕ → ℝ≥0 := fun k => Real.toNNReal (α ((k:ℝ)*h))
  let H : ℝ≥0 := Real.toNNReal (β^2)*h
  let d : ℝ≥0 := Real.toNNReal (β^2)*δ
  let l := (α ((i:ℝ)*h),h-δ)::uniformGridChain α h (N-(i+1)) (i+1)
  have hiN : N-i = (N-(i+1))+1 := by omega
  have hδNi : δ ≤ ((N-i:ℕ):ℝ≥0)*h := by
    exact hδ.trans (by rw [hiN]; push_cast; nlinarith [(Nat.cast_nonneg (α:=ℝ≥0) (N-(i+1)))])
  have hdur : chainDuration l = ((N-i:ℕ):ℝ≥0)*h-δ := by
    dsimp [l]
    rw [uniformGridChain_duration,hiN]
    ext
    simp only [NNReal.coe_add, NNReal.coe_mul]
    rw [NNReal.coe_sub hδ,NNReal.coe_sub (by rw [← hiN]; exact hδNi)]
    push_cast
    ring
  have hm : ∀ p ∈ l, p.1 ∈ Icc (0:ℝ) 1 := by
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ha _
    · exact uniformGridChain_mass α ha h _ _ p hp
  have hmodel : TimeChainModels (gridCDF α h) ((i:ℝ)*h+δ) l := by
    constructor
    · intro r hr
      apply gridCDF_eq_cell α (by exact_mod_cast hh) i
      rw [NNReal.coe_sub hδ] at hr
      constructor
      · exact (le_add_of_nonneg_right δ.coe_nonneg).trans hr.1
      · have H := hr.2
        push_cast
        linarith
    · have he : (i:ℝ)*h+δ+((h-δ:ℝ≥0):ℝ) = ((i+1:ℕ):ℝ)*h := by
        rw [NNReal.coe_sub hδ]; push_cast; ring
      rw [he]
      exact uniformGridChain_models α h hh _ _
  have ht : (((N-i:ℕ):ℝ≥0)*h-δ) ≤ 1 :=
    (tsub_le_self).trans ((mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le N i) h.coe_nonneg).trans hN)
  have he := scalarCDFOperator_eq_chain hfb hLip β
    (show ∀ r, gridCDF α h r ∈ Icc (0:ℝ) 1 from fun r => ha _) (gridCDF_mono hα (by exact_mod_cast hh)) l hm
    ((i:ℝ)*h+δ) _ ht hdur hmodel
  have hstart : (Real.toNNReal (β^2):ℝ)*((i:ℝ)*h+δ) = (i:ℝ)*H+d := by
    dsimp [H,d]; push_cast; ring
  rw [hstart,finiteValue_shift hf hLip c H hi.le 0 d.coe_nonneg]
  simp only [Nat.zero_add]
  conv_lhs => rw [hiN,finiteValue_head f c H _ i
    (show (d:ℝ) ≤ H from NNReal.coe_le_coe.mpr
      (mul_le_mul_of_nonneg_left hδ (Real.toNNReal (β^2)).coe_nonneg))]
  funext x
  calc
    _ = scalarTimeChain β l f x := by
      change varianceLogHeat (c i) ((H:ℝ)-d) (cascade c H f (N-(i+1)) (i+1)) x = _
      dsimp only [l,scalarTimeChain]
      rw [uniformGridChain_eq_cascade α ha hf hLip]
      rw [scalarTimeStep_eq_logSemigroup (cascade_regular hf hLip c H _ _).smooth.continuous.measurable]
      rw [varianceLogHeat_eq_logSemigroup_toNNReal (cascade_regular hf hLip c H _ _).smooth.continuous.measurable]
      congr 2
      · dsimp [c]; exact max_eq_left (ha _).1
      · have hdH : d ≤ H := mul_le_mul_of_nonneg_left hδ (Real.toNNReal (β^2)).coe_nonneg
        rw [← NNReal.coe_sub hdH,Real.toNNReal_coe]
        dsimp [H,d]
        rw [mul_tsub]
    _ = _ := (he x).symm

end SKConstants.ParisiFullSupport
