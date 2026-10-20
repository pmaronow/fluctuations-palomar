module

public import Mathlib

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory Filter Set
open scoped Topology NNReal BigOperators

local instance : Nonempty (Icc (0:ℝ) 1) := ⟨⟨0, by constructor <;> norm_num⟩⟩

def scalarUnitClamp (x : ℝ) : ℝ := max 0 (min 1 x)

theorem scalarUnitClamp_mem (x : ℝ) : scalarUnitClamp x ∈ Icc (0:ℝ) 1 := by
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

theorem scalarUnitClamp_monotone : Monotone scalarUnitClamp := by
  intro x y hxy
  unfold scalarUnitClamp
  gcongr

theorem scalarUnitClamp_lipschitz : LipschitzWith 1 scalarUnitClamp :=
  (LipschitzWith.id.const_min 1).const_max 0

theorem scalarUnitClamp_zero_of_nonpos {x : ℝ} (hx : x ≤ 0) :
    scalarUnitClamp x = 0 := by
  unfold scalarUnitClamp
  rw [min_eq_right (by linarith), max_eq_left hx]

theorem scalarUnitClamp_one_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    scalarUnitClamp x = 1 := by
  simp [scalarUnitClamp, min_eq_left hx]

theorem scalarAffine_lipschitz (L c : ℝ) (hL : 0 ≤ L) :
    LipschitzWith L.toNNReal (fun x : ℝ => L*x+c) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hL,
    show L*x+c-(L*y+c)=L*(x-y) by ring, abs_mul, abs_of_nonneg hL]

def scalarCDFRamp (α : ℝ → ℝ) (L : ℝ) (t : Icc (0:ℝ) 1) (x : ℝ) : ℝ :=
  min (α t) (scalarUnitClamp (L*(x-t)))

def scalarCDFRampEnvelope (α : ℝ → ℝ) (L x : ℝ) : ℝ :=
  ⨆ t : Icc (0:ℝ) 1, scalarCDFRamp α L t x

def scalarLipschitzCDF (α : ℝ → ℝ) (L x : ℝ) : ℝ :=
  max (scalarCDFRampEnvelope α L x) (scalarUnitClamp (1+L*(x-1)))

theorem scalarCDFRamp_mem (α : ℝ → ℝ)
    (hb : ∀ t ∈ Icc (0:ℝ) 1, α t ∈ Icc (0:ℝ) 1)
    (L : ℝ) (t : Icc (0:ℝ) 1) (x : ℝ) : scalarCDFRamp α L t x ∈ Icc (0:ℝ) 1 :=
  ⟨le_min (hb t t.property).1 (scalarUnitClamp_mem _).1,
    (min_le_left _ _).trans (hb t t.property).2⟩

theorem scalarCDFRamp_bddAbove (α : ℝ → ℝ)
    (hb : ∀ t ∈ Icc (0:ℝ) 1, α t ∈ Icc (0:ℝ) 1) (L x : ℝ) :
    BddAbove (range fun t : Icc (0:ℝ) 1 => scalarCDFRamp α L t x) := by
  exact ⟨1, fun y hy => by obtain ⟨t,rfl⟩ := hy; exact (scalarCDFRamp_mem α hb L t x).2⟩

theorem scalarCDFRampEnvelope_mem (α : ℝ → ℝ)
    (hb : ∀ t ∈ Icc (0:ℝ) 1, α t ∈ Icc (0:ℝ) 1) (L x : ℝ) :
    scalarCDFRampEnvelope α L x ∈ Icc (0:ℝ) 1 := by
  constructor
  · exact (scalarCDFRamp_mem α hb L ⟨0,by constructor <;> norm_num⟩ x).1.trans
      (le_ciSup (scalarCDFRamp_bddAbove α hb L x) ⟨0,by constructor <;> norm_num⟩)
  · exact ciSup_le fun t => (scalarCDFRamp_mem α hb L t x).2

theorem scalarCDFRamp_monotone (α : ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (t : Icc (0:ℝ) 1) : Monotone (scalarCDFRamp α L t) := by
  intro x y hxy
  unfold scalarCDFRamp
  apply min_le_min_left
  apply scalarUnitClamp_monotone
  gcongr

theorem scalarCDFRamp_lipschitz (α : ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (t : Icc (0:ℝ) 1) : LipschitzWith L.toNNReal (scalarCDFRamp α L t) := by
  change LipschitzWith L.toNNReal (fun x => min (α t) (scalarUnitClamp (L*(x-t))))
  have ha := scalarAffine_lipschitz L (-L*t) hL
  have hc := (scalarUnitClamp_lipschitz.comp ha).const_min (α t)
  simpa only [one_mul, Function.comp_def,
    show (fun x : ℝ => L*x+(-L*t)) = (fun x => L*(x-t)) by funext x; ring]
    using hc

theorem scalarCDFRampEnvelope_monotone (α : ℝ → ℝ)
    (hb : ∀ t ∈ Icc (0:ℝ) 1, α t ∈ Icc (0:ℝ) 1) (L : ℝ) (hL : 0 ≤ L) :
    Monotone (scalarCDFRampEnvelope α L) := by
  intro x y hxy
  exact ciSup_mono (scalarCDFRamp_bddAbove α hb L y)
    (fun t => scalarCDFRamp_monotone α L hL t hxy)

theorem scalarCDFRampEnvelope_lipschitz (α : ℝ → ℝ)
    (hb : ∀ t ∈ Icc (0:ℝ) 1, α t ∈ Icc (0:ℝ) 1) (L : ℝ) (hL : 0 ≤ L) :
    LipschitzWith L.toNNReal (scalarCDFRampEnvelope α L) := by
  have hdir (x y : ℝ) : scalarCDFRampEnvelope α L x ≤
      scalarCDFRampEnvelope α L y+L*|x-y| := by
    apply ciSup_le
    intro t
    have h := (scalarCDFRamp_lipschitz α L hL t).dist_le_mul x y
    simp only [Real.dist_eq, Real.coe_toNNReal _ hL] at h
    have ht := le_ciSup (scalarCDFRamp_bddAbove α hb L y) t
    change scalarCDFRamp α L t y ≤ scalarCDFRampEnvelope α L y at ht
    linarith [le_abs_self (scalarCDFRamp α L t x-scalarCDFRamp α L t y)]
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hL]
  apply abs_le.mpr
  have hxy := hdir x y
  have hyx := hdir y x
  rw [abs_sub_comm y x] at hyx
  constructor <;> linarith

theorem scalarLipschitzCDF_mem (α : ℝ → ℝ)
    (hb : ∀ t ∈ Icc (0:ℝ) 1, α t ∈ Icc (0:ℝ) 1) (L x : ℝ) :
    scalarLipschitzCDF α L x ∈ Icc (0:ℝ) 1 :=
  ⟨(scalarCDFRampEnvelope_mem α hb L x).1.trans (le_max_left _ _),
    max_le (scalarCDFRampEnvelope_mem α hb L x).2 (scalarUnitClamp_mem _).2⟩

theorem scalarLipschitzCDF_monotone (α : ℝ → ℝ)
    (hb : ∀ t ∈ Icc (0:ℝ) 1, α t ∈ Icc (0:ℝ) 1) (L : ℝ) (hL : 0 ≤ L) :
    Monotone (scalarLipschitzCDF α L) := by
  intro x y hxy
  apply max_le_max (scalarCDFRampEnvelope_monotone α hb L hL hxy)
  apply scalarUnitClamp_monotone
  gcongr

theorem scalarLipschitzCDF_lipschitz (α : ℝ → ℝ)
    (hb : ∀ t ∈ Icc (0:ℝ) 1, α t ∈ Icc (0:ℝ) 1) (L : ℝ) (hL : 0 ≤ L) :
    LipschitzWith L.toNNReal (scalarLipschitzCDF α L) := by
  change LipschitzWith L.toNNReal (fun x =>
    max (scalarCDFRampEnvelope α L x) (scalarUnitClamp (1+L*(x-1))))
  have hterminal := scalarUnitClamp_lipschitz.comp (scalarAffine_lipschitz L (1-L) hL)
  have hterminal' : LipschitzWith L.toNNReal (fun x : ℝ => scalarUnitClamp (1+L*(x-1))) := by
    simpa only [one_mul, Function.comp_def,
      show (fun x : ℝ => L*x+(1-L)) = (fun x => 1+L*(x-1)) by funext x; ring]
      using hterminal
  simpa only [max_self] using
    (scalarCDFRampEnvelope_lipschitz α hb L hL).max hterminal'

theorem scalarLipschitzCDF_zero (α : ℝ → ℝ)
    (hb : ∀ t ∈ Icc (0:ℝ) 1, α t ∈ Icc (0:ℝ) 1) {L : ℝ} (hL : 1 ≤ L) :
    scalarLipschitzCDF α L 0 = 0 := by
  have he : scalarCDFRampEnvelope α L 0=0 := by
    apply le_antisymm
    · apply ciSup_le
      intro t
      unfold scalarCDFRamp
      rw [scalarUnitClamp_zero_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith [t.property.1]))]
      exact min_le_right _ _
    · exact (scalarCDFRampEnvelope_mem α hb L 0).1
  unfold scalarLipschitzCDF
  rw [he,scalarUnitClamp_zero_of_nonpos (by linarith)]
  exact max_self 0

theorem scalarLipschitzCDF_one (α : ℝ → ℝ)
    (hb : ∀ t ∈ Icc (0:ℝ) 1, α t ∈ Icc (0:ℝ) 1) (L : ℝ) :
    scalarLipschitzCDF α L 1 = 1 := by
  unfold scalarLipschitzCDF
  rw [show 1+L*((1:ℝ)-1)=1 by ring,scalarUnitClamp_one_of_one_le le_rfl]
  exact max_eq_right (scalarCDFRampEnvelope_mem α hb L 1).2

theorem scalarLipschitzCDF_le_profile (α : ℝ → ℝ)
    (hm : MonotoneOn α (Icc (0:ℝ) 1))
    (hb : ∀ t ∈ Icc (0:ℝ) 1, α t ∈ Icc (0:ℝ) 1)
    {L x : ℝ} (hL : 0 < L) (hx : x ∈ Icc (0:ℝ) 1)
    (hterminal : 1/L ≤ 1-x) : scalarLipschitzCDF α L x ≤ α x := by
  apply max_le
  · apply ciSup_le
    intro t
    by_cases htx : (t:ℝ) ≤ x
    · exact (min_le_left _ _).trans (hm t.property hx htx)
    · unfold scalarCDFRamp
      rw [scalarUnitClamp_zero_of_nonpos
        (mul_nonpos_of_nonneg_of_nonpos hL.le (by linarith))]
      exact (min_le_right _ _).trans (hb x hx).1
  · have hprod : 1 ≤ (1-x)*L := (div_le_iff₀ hL).mp hterminal
    rw [scalarUnitClamp_zero_of_nonpos (by nlinarith)]
    exact (hb x hx).1

theorem scalarProfile_shift_le_LipschitzCDF (α : ℝ → ℝ)
    (hb : ∀ t ∈ Icc (0:ℝ) 1, α t ∈ Icc (0:ℝ) 1)
    {L x : ℝ} (hL : 0 < L) (hx : x ∈ Icc (0:ℝ) 1) (hstart : 1/L ≤ x) :
    α (x-1/L) ≤ scalarLipschitzCDF α L x := by
  let t : Icc (0:ℝ) 1 := ⟨x-1/L, by
    constructor
    · linarith
    · linarith [hx.2, one_div_nonneg.mpr hL.le]⟩
  have he : scalarCDFRamp α L t x = α (x-1/L) := by
    unfold scalarCDFRamp
    have hz : L*(x-(t:ℝ))=1 := by
      dsimp [t]
      field_simp
      ring
    rw [hz,scalarUnitClamp_one_of_one_le le_rfl,min_eq_left (hb t t.property).2]
  rw [← he]
  exact (le_ciSup (scalarCDFRamp_bddAbove α hb L x) t).trans (le_max_left _ _)

theorem scalarLipschitzCDF_tendsto_at_continuity (α : ℝ → ℝ)
    (hm : MonotoneOn α (Icc (0:ℝ) 1))
    (hb : ∀ t ∈ Icc (0:ℝ) 1, α t ∈ Icc (0:ℝ) 1)
    {x : ℝ} (hx : x ∈ Ioo (0:ℝ) 1) (hc : ContinuousAt α x) :
    Tendsto (fun n : ℕ => scalarLipschitzCDF α ((n+1:ℕ):ℝ) x) atTop (𝓝 (α x)) := by
  have hd : Tendsto (fun n : ℕ => (1:ℝ)/((n+1:ℕ):ℝ)) atTop (𝓝 0) := by
    simpa only [Nat.cast_add,Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hlow : Tendsto (fun n : ℕ => α (x-1/((n+1:ℕ):ℝ))) atTop (𝓝 (α x)) := by
    have hshift : Tendsto (fun n : ℕ => x-1/((n+1:ℕ):ℝ)) atTop (𝓝 x) := by
      simpa only [sub_zero] using
        ((tendsto_const_nhds : Tendsto (fun _ : ℕ => x) atTop (𝓝 x)).sub hd)
    exact hc.tendsto.comp hshift
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds
  · filter_upwards [hd.eventually (gt_mem_nhds hx.1)] with n hn
    exact scalarProfile_shift_le_LipschitzCDF α hb (by positivity) ⟨hx.1.le,hx.2.le⟩ hn.le
  · filter_upwards [hd.eventually (gt_mem_nhds (sub_pos.mpr hx.2))] with n hn
    exact scalarLipschitzCDF_le_profile α hm hb (by positivity) ⟨hx.1.le,hx.2.le⟩ hn.le

theorem scalarLipschitzCDF_l1_tendsto (α : ℝ → ℝ) (hm : Monotone α)
    (hb : ∀ t ∈ Icc (0:ℝ) 1, α t ∈ Icc (0:ℝ) 1) :
    Tendsto (fun n : ℕ => ∫ x in (0:ℝ)..1,
      |scalarLipschitzCDF α ((n+1:ℕ):ℝ) x-α x|) atTop (𝓝 0) := by
  have ht := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (Ioo (0:ℝ) 1))
    (F := fun n x => |scalarLipschitzCDF α ((n+1:ℕ):ℝ) x-α x|)
    (f := fun _ => (0:ℝ)) (fun _ => (1:ℝ))
    (fun n => (((scalarLipschitzCDF_lipschitz α hb ((n+1:ℕ):ℝ)
      (by positivity)).continuous.measurable.sub hm.measurable).abs).aestronglyMeasurable)
    (integrable_const 1) ?_ ?_
  · simpa only [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),
      integral_Ioc_eq_integral_Ioo,integral_zero] using ht
  · intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hg := scalarLipschitzCDF_mem α hb ((n+1:ℕ):ℝ) x
    have ha := hb x ⟨hx.1.le,hx.2.le⟩
    rw [Real.norm_eq_abs,abs_abs]
    apply abs_le.mpr
    constructor <;> linarith [hg.1,hg.2,ha.1,ha.2]
  · have ha := ae_restrict_of_ae (s := Ioo (0:ℝ) 1)
      (hm.countable_not_continuousAt.ae_notMem volume)
    filter_upwards [ae_restrict_mem measurableSet_Ioo,ha] with x hx hc
    have hcx : ContinuousAt α x := by simpa only [mem_ofPred_eq,not_not] using hc
    have hxlim := scalarLipschitzCDF_tendsto_at_continuity α (hm.monotoneOn _) hb hx hcx
    simpa only [sub_self,abs_zero] using
      (hxlim.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => α x) atTop (𝓝 (α x)))).abs

theorem exists_scalarLipschitzCDF_approximation (α : ℝ → ℝ) (hm : Monotone α)
    (hb : ∀ t ∈ Icc (0:ℝ) 1, α t ∈ Icc (0:ℝ) 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ (G : ℝ → ℝ) (K : ℝ≥0), Monotone G ∧ LipschitzWith K G ∧
      G 0=0 ∧ G 1=1 ∧ (∀ x, G x ∈ Icc (0:ℝ) 1) ∧
      (∫ x in (0:ℝ)..1, |G x-α x|)<ε := by
  obtain ⟨n,hn⟩ := ((scalarLipschitzCDF_l1_tendsto α hm hb).eventually (gt_mem_nhds hε)).exists
  refine ⟨scalarLipschitzCDF α ((n+1:ℕ):ℝ), ((n+1:ℕ):ℝ).toNNReal,
    scalarLipschitzCDF_monotone α hb _ (by positivity),
    scalarLipschitzCDF_lipschitz α hb _ (by positivity),
    scalarLipschitzCDF_zero α hb (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)),
    scalarLipschitzCDF_one α hb _, scalarLipschitzCDF_mem α hb _,hn⟩

theorem scalarUnitClamp_eq_of_mem {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) :
    scalarUnitClamp x=x := by
  rw [scalarUnitClamp,min_eq_right hx.2,max_eq_right hx.1]

theorem exists_scalarLipschitzCDF_approximation_on (α : ℝ → ℝ)
    (hm : MonotoneOn α (Icc (0:ℝ) 1))
    (hb : ∀ t ∈ Icc (0:ℝ) 1, α t ∈ Icc (0:ℝ) 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ (G : ℝ → ℝ) (K : ℝ≥0), Monotone G ∧ LipschitzWith K G ∧
      G 0=0 ∧ G 1=1 ∧ (∀ x, G x ∈ Icc (0:ℝ) 1) ∧
      (∫ x in (0:ℝ)..1, |G x-α x|)<ε := by
  let α' := fun x => α (scalarUnitClamp x)
  have hm' : Monotone α' := fun x y hxy =>
    hm (scalarUnitClamp_mem x) (scalarUnitClamp_mem y) (scalarUnitClamp_monotone hxy)
  have hb' : ∀ t ∈ Icc (0:ℝ) 1, α' t ∈ Icc (0:ℝ) 1 :=
    fun t _ => hb (scalarUnitClamp t) (scalarUnitClamp_mem t)
  obtain ⟨G,K,hGm,hGl,hG0,hG1,hGb,herr⟩ := exists_scalarLipschitzCDF_approximation α' hm' hb' hε
  refine ⟨G,K,hGm,hGl,hG0,hG1,hGb,?_⟩
  have he : (∫ x in (0:ℝ)..1, |G x-α x|) = ∫ x in (0:ℝ)..1, |G x-α' x| := by
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num : (0:ℝ)≤1)
    intro x hx
    dsimp [α']
    rw [scalarUnitClamp_eq_of_mem ⟨hx.1.le,hx.2.le⟩]
  rwa [he]

end OAI.SKFluctuations.LaplaceWindowFormalization
