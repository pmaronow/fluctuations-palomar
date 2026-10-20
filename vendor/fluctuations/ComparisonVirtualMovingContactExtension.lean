module

public import ComparisonVirtualPotentialCompactness

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 2500000

theorem virtual_contact_clamp_lipschitz
    {a b ref : ℝ} {C : ℝ≥0} (href : ref ≤ b) (H : ℝ→ℝ)
    (hLip : LipschitzOnWith C H (Icc ref b)) :
    LipschitzWith C (fun t : Icc a b=>H (max ref t.val)) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  have hs : max ref s.val∈Icc ref b := ⟨le_max_left _ _,max_le href s.property.2⟩
  have ht : max ref t.val∈Icc ref b := ⟨le_max_left _ _,max_le href t.property.2⟩
  have hh := hLip.dist_le_mul (max ref s.val) hs (max ref t.val) ht
  have hm := (LipschitzWith.id.const_max ref).dist_le_mul s.val t.val
  have hm1 : dist (max ref s.val) (max ref t.val) ≤ dist s.val t.val := by simpa using hm
  exact hh.trans (by simpa only [Subtype.dist_eq] using mul_le_mul_of_nonneg_left hm1 C.coe_nonneg)

theorem virtual_contact_clamp_abs_bound
    {a b ref : ℝ} {C : ℝ≥0} (hrefLower : a-1 ≤ ref) (href : ref ≤ b)
    (H : ℝ→ℝ) (hLip : LipschitzOnWith C H (Icc ref b)) (hzero : H ref=0)
    (t : Icc a b) : |H (max ref t.val)| ≤ (C:ℝ)*(b-a+1) := by
  have ht : max ref t.val∈Icc ref b := ⟨le_max_left _ _,max_le href t.property.2⟩
  have hh := hLip.dist_le_mul (max ref t.val) ht ref ⟨le_rfl,href⟩
  rw [Real.dist_eq,hzero,sub_zero,Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr ht.1)] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (by linarith [ht.2]) C.coe_nonneg)

def virtualMovingContactPotential
    {a b ref : ℝ} {C : ℝ≥0} (href : ref ≤ b) (H : ℝ→ℝ)
    (hLip : LipschitzOnWith C H (Icc ref b)) : BoundedContinuousFunction (Icc a b) ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun t=>H (max ref t.val),(virtual_contact_clamp_lipschitz href H hLip).continuous⟩

theorem virtual_contact_clamp_at_left_bound
    {a b ref : ℝ} {C : ℝ≥0} (hab : a ≤ b) (href : ref ≤ b)
    (H : ℝ→ℝ) (hLip : LipschitzOnWith C H (Icc ref b)) (hzero : H ref=0) :
    |H (max ref a)| ≤ (C:ℝ)*|a-ref| := by
  have ha : max ref a∈Icc ref b := ⟨le_max_left _ _,max_le href hab⟩
  have hh := hLip.dist_le_mul (max ref a) ha ref ⟨le_rfl,href⟩
  have hm := (LipschitzWith.id.const_max ref).dist_le_mul a ref
  simp only [id_eq,max_self,NNReal.coe_one,one_mul,Real.dist_eq] at hm
  rw [Real.dist_eq,hzero,sub_zero,Real.dist_eq] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left hm C.coe_nonneg)

theorem virtual_moving_contact_potentials_exists_uniform_subseq
    {a b : ℝ} {C : ℝ≥0} (hab : a ≤ b) (refs : ℕ→ℝ) (H : ℕ→ℝ→ℝ)
    (hrefLower : ∀n,a-1 ≤ refs n) (hrefUpper : ∀n,refs n ≤ b)
    (hrefLim : Tendsto refs atTop (𝓝 a)) (hzero : ∀n,H n (refs n)=0)
    (hLip : ∀n,LipschitzOnWith C (H n) (Icc (refs n) b)) :
    ∃p : BoundedContinuousFunction (Icc a b) ℝ,∃phi : ℕ→ℕ,StrictMono phi ∧
      Tendsto (fun n=>virtualMovingContactPotential (a:=a) (hrefUpper (phi n))
        (H (phi n)) (hLip (phi n))) atTop (𝓝 p) ∧
      p ⟨a,⟨le_rfl,hab⟩⟩=0 ∧ LipschitzWith C p := by
  let P : ℕ→BoundedContinuousFunction (Icc a b) ℝ := fun n=>
    virtualMovingContactPotential (a:=a) (hrefUpper n) (H n) (hLip n)
  have hPLip n : LipschitzWith (C:ℝ).toNNReal (P n) := by
    rw [Real.toNNReal_coe]
    change LipschitzWith C (fun t : Icc a b=>H n (max (refs n) t.val))
    exact virtual_contact_clamp_lipschitz (a:=a) (hrefUpper n) (H n) (hLip n)
  have hPBound n t : P n t∈Icc (-((C:ℝ)*(b-a+1))) ((C:ℝ)*(b-a+1)) :=
    abs_le.mp (virtual_contact_clamp_abs_bound (hrefLower n) (hrefUpper n) (H n) (hLip n) (hzero n) t)
  obtain ⟨p,phi,hphi,hlim⟩ := virtual_potentials_exists_uniform_subseq C.coe_nonneg P hPLip hPBound
  have hleft : Tendsto (fun n=>P n ⟨a,⟨le_rfl,hab⟩⟩) atTop (𝓝 0) := by
    have he : Tendsto (fun n=>(C:ℝ)*|a-refs n|) atTop (𝓝 0) := by
      simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℕ=>a) atTop (𝓝 a)).sub hrefLim).abs.const_mul (C:ℝ)
    apply squeeze_zero_norm _ he
    intro n
    simpa only [P,virtualMovingContactPotential,BoundedContinuousFunction.mkOfCompact_apply,
      ContinuousMap.coe_mk,Real.norm_eq_abs] using
      virtual_contact_clamp_at_left_bound hab (hrefUpper n) (H n) (hLip n) (hzero n)
  have hleftSub := hleft.comp hphi.tendsto_atTop
  have hleftEval := (BoundedContinuousFunction.lipschitz_eval_const ⟨a,⟨le_rfl,hab⟩⟩).continuous.tendsto p |>.comp hlim
  refine ⟨p,phi,hphi,hlim,tendsto_nhds_unique hleftEval hleftSub,?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro s t
  have hs := (BoundedContinuousFunction.lipschitz_eval_const s).continuous.tendsto p |>.comp hlim
  have ht := (BoundedContinuousFunction.lipschitz_eval_const t).continuous.tendsto p |>.comp hlim
  have hd := hs.dist ht
  exact le_of_tendsto hd (Eventually.of_forall fun n=>by
    simpa only [P,Function.comp_def,Real.toNNReal_coe] using (hPLip (phi n)).dist_le_mul s t)

theorem virtual_native_negative_excursion_bound
    {a b x Jref T B : ℝ} (ha : 0 ≤ a) (_hab : a ≤ b) (hx : 0 < x)
    (hJref : 0 < Jref) (hT : 0 < T) (hB : 0 ≤ B) (H : ℝ→ℝ)
    (hend : x*b+2*T ≤ 1) (hH : ContinuousOn H (Icc (0:ℝ) 1))
    (htravel : ∀l z : ℝ,0 ≤ l→z ≤ 1→l ≤ z→
      (∀t∈Ioo l z,H t < 0)→z-l ≤ T)
    (hLip : LipschitzOnWith B.toNNReal (comparisonVirtualScaledPotential x Jref H)
      (Icc a (b+2*T/x))) :
    ∀t∈Icc a b,-2*B*T/x ≤ comparisonVirtualScaledPotential x Jref H t := by
  intro t ht
  by_cases hn : H (x*t) < 0
  · have hr : 0 ≤ x*t := mul_nonneg hx.le (ha.trans ht.1)
    obtain ⟨z,hz,hHz⟩ := virtual_negative_point_near_zero hT hr
      (by nlinarith [ht.2]) hH hn htravel
    have hzt : t ≤ z/x := (le_div_iff₀ hx).mpr (by simpa only [mul_comm] using hz.1)
    have hzb : z/x ≤ b+2*T/x := by
      apply (div_le_iff₀ hx).mpr
      have hc : (b+2*T/x)*x=b*x+2*T := by field_simp
      rw [hc]
      nlinarith [hz.2,ht.2]
    have htBig : t∈Icc a (b+2*T/x) := ⟨ht.1,ht.2.trans (le_add_of_nonneg_right (by positivity : 0 ≤ 2*T/x))⟩
    have hzBig : z/x∈Icc a (b+2*T/x) := ⟨ht.1.trans hzt,hzb⟩
    have hscaledZero : comparisonVirtualScaledPotential x Jref H (z/x)=0 := by
      unfold comparisonVirtualScaledPotential
      rw [mul_div_cancel₀ z hx.ne',hHz,zero_div]
    have hh := hLip.dist_le_mul t htBig (z/x) hzBig
    rw [Real.dist_eq,hscaledZero,sub_zero,Real.dist_eq,abs_sub_comm,
      abs_of_nonneg (sub_nonneg.mpr hzt),Real.coe_toNNReal _ hB] at hh
    have hdist : z/x-t ≤ 2*T/x := by
      apply (le_div_iff₀ hx).mpr
      have he : (z/x-t)*x=z-t*x := by field_simp
      rw [he]
      nlinarith [hz.2]
    have hbnd := hh.trans (mul_le_mul_of_nonneg_left hdist hB)
    have he : B*(2*T/x)=2*B*T/x := by ring
    rw [he] at hbnd
    have heNeg : -2*B*T/x=-(2*B*T/x) := by ring
    rw [heNeg]
    exact (abs_le.mp hbnd).1
  · have hnon : 0 ≤ comparisonVirtualScaledPotential x Jref H t :=
      div_nonneg (not_lt.mp hn) (mul_pos (pow_pos hx 4) hJref).le
    have heNeg : -2*B*T/x=-(2*B*T/x) := by ring
    rw [heNeg]
    exact (neg_nonpos.mpr (by positivity : 0 ≤ 2*B*T/x)).trans hnon

theorem virtual_uniform_potential_primitive_identified_eventually
    {a b : ℝ} (P : ℕ→BoundedContinuousFunction (Icc a b) ℝ)
    (p : BoundedContinuousFunction (Icc a b) ℝ) (F : ℕ→ℝ→ℝ) (f : ℝ→ℝ)
    (hP : Tendsto P atTop (𝓝 p)) (s t : Icc a b) (hst : s.val ≤ t.val)
    (hFi : ∀n,IntegrableOn (F n) (Icc s.val t.val))
    (hfi : IntegrableOn f (Icc s.val t.val))
    (hL1 : Tendsto (fun n=>∫r in Icc s.val t.val,|F n r-f r|) atTop (𝓝 0))
    (hPrimitive : ∀ᶠ n in atTop,P n t-P n s=∫r in s.val..t.val,F n r) :
    p t-p s=∫r in s.val..t.val,f r := by
  have hsub : Ioc s.val t.val⊆Icc s.val t.val := Ioc_subset_Icc_self
  have hL1sub : Tendsto (fun n=>∫r in Ioc s.val t.val,|F n r-f r|) atTop (𝓝 0) := by
    apply squeeze_zero (fun n=>integral_nonneg fun _=>abs_nonneg _) _ hL1
    intro n
    exact setIntegral_mono_set ((hFi n).sub hfi).abs
      (Eventually.of_forall fun _=>abs_nonneg _) (Eventually.of_forall fun r hr=>hsub hr)
  have hILim := virtual_integrals_tendsto_of_L1 (volume.restrict (Ioc s.val t.val)) F f
    (fun n=>(hFi n).mono_set hsub) (hfi.mono_set hsub) hL1sub
  have hInterval : Tendsto (fun n=>∫r in s.val..t.val,F n r) atTop
      (𝓝 (∫r in s.val..t.val,f r)) := by
    simpa only [intervalIntegral.integral_of_le hst] using hILim
  have he : (fun n=>∫r in s.val..t.val,F n r)=ᶠ[atTop](fun n=>P n t-P n s) :=
    hPrimitive.mono fun _ hn=>hn.symm
  have hDiffI := hInterval.congr' he
  have hDiff := ((BoundedContinuousFunction.lipschitz_eval_const t).continuous.tendsto p |>.comp hP).sub
    ((BoundedContinuousFunction.lipschitz_eval_const s).continuous.tendsto p |>.comp hP)
  exact tendsto_nhds_unique hDiff hDiffI

theorem virtual_local_primitives_extend_to_endpoints
    {a b : ℝ} (hab : a < b) (H f : ℝ→ℝ)
    (hH : ContinuousOn H (Icc a b)) (hfi : IntegrableOn f (Icc a b))
    (hPrimitive : ∀s∈Ioo a b,∀t∈Ioo a b,s ≤ t→H t-H s=∫r in s..t,f r) :
    ∀s∈Icc a b,∀t∈Icc a b,s ≤ t→H t-H s=∫r in s..t,f r := by
  let primitive := fun r=>∫u in a..r,f u
  let F := fun r=>H r-primitive r
  have hi : IntervalIntegrable f volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab.le).mpr hfi
  have hAC := hi.absolutelyContinuousOnInterval_intervalIntegral (c:=a) (by rw [uIcc_of_le hab.le];exact ⟨le_rfl,hab.le⟩)
  have hPC : ContinuousOn primitive (Icc a b) := by
    simpa only [uIcc_of_le hab.le] using hAC.continuousOn
  have hFC : ContinuousOn F (Icc a b) := hH.sub hPC
  let mid := (a+b)/2
  have hmid : mid∈Ioo a b := by dsimp only [mid];constructor <;> linarith
  have hir r (hr : r∈Icc a b) : IntervalIntegrable f volume a r :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hr.1).mpr
      (hfi.mono_set (Icc_subset_Icc le_rfl hr.2))
  have hconst : ∀r∈Ioo a b,F r=F mid := by
    intro r hr
    rcases le_total r mid with hrm|hmr
    · have hp := hPrimitive r hr mid hmid hrm
      have hint := intervalIntegral.integral_interval_sub_left (hir mid ⟨hmid.1.le,hmid.2.le⟩)
        (hir r ⟨hr.1.le,hr.2.le⟩)
      dsimp only [F,primitive]
      linarith
    · have hp := hPrimitive mid hmid r hr hmr
      have hint := intervalIntegral.integral_interval_sub_left (hir r ⟨hr.1.le,hr.2.le⟩)
        (hir mid ⟨hmid.1.le,hmid.2.le⟩)
      dsimp only [F,primitive]
      linarith
  have hclosed : IsClosed {r | r∈Icc a b ∧ F r=F mid} :=
    isClosed_Icc.isClosed_eq hFC continuousOn_const
  have hsubset : Ioo a b⊆{r | r∈Icc a b ∧ F r=F mid} :=
    fun r hr=>⟨⟨hr.1.le,hr.2.le⟩,hconst r hr⟩
  have hclosure := closure_minimal hsubset hclosed
  rw [closure_Ioo hab.ne] at hclosure
  intro s hs t ht hst
  have hsF := (hclosure hs).2
  have htF := (hclosure ht).2
  have hint := intervalIntegral.integral_interval_sub_left (hir t ht) (hir s hs)
  dsimp only [F,primitive] at hsF htF
  linarith

end OAI.SKFluctuations.LaplaceWindowFormalization
