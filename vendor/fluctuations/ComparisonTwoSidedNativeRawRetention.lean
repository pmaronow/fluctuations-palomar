module

public import SKFluctuationsOAI.Probability.SKFluctuations.ComparisonMinimumRegularRawRatio

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 1000000

namespace RawFutureCutFamily

def retainExtra {xs B μ u₀ : ℝ} {u : PositiveMass}
    (cuts : RawFutureCutFamily xs B μ u₀ u)
    (extra : List PositiveMass) (hextra : ∀v∈extra,v.val≤1) :
    RawFutureCutFamily xs B μ u₀ u where
  bands := cuts.bands
  p := cuts.p
  q := cuts.q
  t := cuts.t
  retained := cuts.retained++extra
  observation_mem := List.mem_append_left _ cuts.observation_mem
  retained_le_one := by
    intro v hv
    rcases List.mem_append.mp hv with hv|hv
    · exact cuts.retained_le_one v hv
    · exact hextra v hv
  band_bounds := cuts.band_bounds
  mass_values := cuts.mass_values
  cut_order := by
    intro v hv
    have h := cuts.cut_order v hv
    exact ⟨List.mem_append_left _ h.1,List.mem_append_left _ h.2.1,h.2.2⟩
  cover := cuts.cover

end RawFutureCutFamily

 theorem eventually_comparison_minimum_raw_ratio_regular_retaining
    (ℓ : ℕ) (Bclock : ℝ) {m δ B cl cu Az Ca K R C μ F κ₀ C₀ Ct D : ℝ}
    (hm₀ : 0 < m) (hδ : 0 < δ) (hδm : δ < 3*m)
    (hB : 2 ≤ B) (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hBcu : cu ≤ B) (hBA : 2*cu*Az < B) (hCa : 0 < Ca) (hCaB : B/cl ≤ Ca)
    (hK : 1 ≤ K) (hKcu : 2*cu/cl ≤ K)
    (hR : 0 < R) (hR1 : R ≤ 1) (hKR : 2*K*R ≤ 1) (hcuR : 2*cu*R ≤ 1)
    (hC : 3*B/cl+1 < C) (hC1 : 1 ≤ C) (hmacro : 1 ≤ C*μ)
    (hμ : 0 < μ) (hμR : Ca*μ ≤ R) (hμB : 3*B*μ ≤ 1)
    (hFmass : 1+2*cu ≤ F) (hFradius : 1+1/R ≤ F)
    (hκ₀ : 0 < κ₀) (hC₀ : 0 < C₀) (hCt : 0 ≤ Ct) :
    ∀ᶠ n : ℕ in atTop, ∀ {E d r₀ u₀ : ℝ}
    (hn : 0 < n) (hE : 0 < E) (hd : 0 < d)
    (hr₀ : r₀ ∈ Icc (0:ℝ) (1/4)) (hu₀ : u₀ ∈ Icc (0:ℝ) (1/4)) (g : ℝ → ℝ),
    let N := (n:ℝ)
    let U := comparisonSmallMass N E
    let L := comparisonConstraintLength N E d
    let hN : 0 < N := by dsimp only [N]; exact_mod_cast hn
    let hU := comparisonSmallMass_pos hN hE
    let hL := comparisonConstraintLength_pos hN hE hd
    let k := comparisonFloor N δ U
    let M := comparisonCap N δ U L E d
    let c := k 1
    let hr : r₀ ≤ 1 := le_trans hr₀.2 (by norm_num)
    let hu : u₀ ∈ Icc (0:ℝ) 1 := ⟨hu₀.1,le_trans hu₀.2 (by norm_num)⟩
    let hc : 0 < c := comparisonFloor_pos hN hU (by norm_num)
    let hk := comparisonFloor_continuousOn (δ:=δ) hN hU hr₀.1
    let hkc := fun r (hri : r ∈ Icc r₀ 1) => comparisonFloor_lower_on (δ:=δ) hN hU hr₀.1 hri
    let hm := comparisonCap_monotoneOn (δ:=δ) hN hU.le hL hE hd.le
    let hM := comparisonCap_nonneg (δ:=δ) hN hU.le hL hE hd.le (show (0:ℝ) ≤ 1 by norm_num)
    ∀ (α : inverseIntegralConstraints r₀ u₀ k M)
    (hg : ContDiff ℝ 1 g)
    (hgpos : ∀ r ∈ Icc r₀ 1, 0<g r)
    (hp : ∀ r ∈ Ioc r₀ 1, comparisonLogSlope g r ∈ Icc (0:ℝ) 1)
    (b h : ℝ → ℝ)
    (hb : ∀ β : inverseIntegralConstraints r₀ u₀ k M,
      MonotoneOn (fun u => b u-omittedExtension hu.2
        (constrainedCoefficient hr hc hk hkc hm hM g hg.continuous β) u) (Icc (0:ℝ) 1))
    (hh : ∀ β : inverseIntegralConstraints r₀ u₀ k M,
      MonotoneOn (fun u => h u+omittedExtension hu.2
        (constrainedCoefficient hr hc hk hkc hm hM (fun r => g r*r)
          (hg.continuous.mul continuous_id) β) u) (Icc (0:ℝ) 1))
    (hbn : ∀ β : inverseIntegralConstraints r₀ u₀ k M,
      0 ≤ b 0-omittedExtension hu.2 (constrainedCoefficient hr hc hk hkc hm hM g hg.continuous β) 0)
    (hhn : ∀ β : inverseIntegralConstraints r₀ u₀ k M,
      0 ≤ h 0+omittedExtension hu.2 (constrainedCoefficient hr hc hk hkc hm hM (fun r => g r*r)
        (hg.continuous.mul continuous_id) β) 0)
    (hmin : ∀ β : inverseIntegralConstraints r₀ u₀ k M,
      inverseCompensatedPressure hr hu.2 hc hk hkc hm hM g hg.continuous n b h 0 α ≤
      inverseCompensatedPressure hr hu.2 hc hk hkc hm hM g hg.continuous n b h 0 β),
    let b' := fun u => (b u-omittedExtension hu.2
      (constrainedCoefficient hr hc hk hkc hm hM g hg.continuous α) u).toNNReal
    let h' := fun u => (h u+omittedExtension hu.2
      (constrainedCoefficient hr hc hk hkc hm hM (fun r => g r*r)
        (hg.continuous.mul continuous_id) α) u).toNNReal
    ∀ (u : PositiveMass) (huobs : u.val ≤ 1)
    (extra : List PositiveMass) (hextra : ∀v∈extra,v.val≤1) (xs z : ℝ),
      0 < xs → comparisonLowerScale n E d ≤ xs → u₀ ≤ xs → r₀ ≤ U →
      z ∈ Icc r₀ 1 → z ≤ Az*xs → d ≤ D →
      Real.sqrt (n:ℝ)*E ≤ d^2 → (n:ℝ)^(-(2:ℝ)/3+m)*d ≤ C₀*E →
      (n:ℝ)*E^2 ≤ Ct*g xs*xs^2 →
      (∀ r ∈ Icc z 1, cl*r ≤ α.val.val r ∧ α.val.val r ≤ cu*r) →
      (∀ r ∈ Icc z 1, κ₀/Real.log (n:ℝ) ≤ 1-comparisonLogSlope g r) →
      MonotoneOn h (Icc u₀ 1) → (h' 1:ℝ)-(h' 0:ℝ) ≤ Bclock →
      ∃ us : List PositiveMass, (∀ v ∈ us, v.val ≤ 1) ∧ u ∈ us ∧
        (∀v∈extra,v∈us) ∧ ∀ᶠ j : ℕ in atTop,
          (physicalRawRatio n (ℓ+1) (sampleClockSteps (completedPathClock n b' h') 0 (finiteCutMasses us j))
            0 xs (Measure.pi fun i => gaussianReal 0 (completedPathClock n b' h' 0 i)) id measurable_id)^2 ≤ 2*C := by
  have hlog : ∀ᶠ n : ℕ in atTop, 0 < Real.log (n:ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_gt_atTop 0)
  have hpow : ∀ᶠ n : ℕ in atTop, 2 ≤ (n:ℝ)^δ :=
    ((tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 2)
  filter_upwards [eventually_comparison_minimum_raw_ratio_of_finite_margins ℓ Bclock,
    eventually_comparison_regular_band_margins (F:=F) (D:=D) ℓ hm₀ hδ.le hδm hB hcl hcu hAz hBcu hBA hCa hCaB
      hK hKcu hR hR1 hKR hcuR hC hμ hμR hκ₀ hC₀ hCt,hlog,hpow] with n hnraw hnmargin hnlog hnq
  intro E d r₀ u₀ hn hE hd hr₀ hu₀ g
  dsimp only
  intro α hg hgpos hp b h hb hh hbn hhn hmin
  let N := (n:ℝ)
  let U := comparisonSmallMass N E
  let L := comparisonConstraintLength N E d
  have hN : 0 < N := by dsimp only [N]; exact_mod_cast hn
  have hU := comparisonSmallMass_pos hN hE
  have hL := comparisonConstraintLength_pos hN hE hd
  let k := comparisonFloor N δ U
  let M := comparisonCap N δ U L E d
  let c := k 1
  let hr : r₀ ≤ 1 := le_trans hr₀.2 (by norm_num)
  let hu : u₀ ≤ 1 := le_trans hu₀.2 (by norm_num)
  let hc : 0 < c := comparisonFloor_pos hN hU (by norm_num)
  let hk := comparisonFloor_continuousOn (δ:=δ) hN hU hr₀.1
  let hkc := fun r (hri : r ∈ Icc r₀ 1) => comparisonFloor_lower_on (δ:=δ) hN hU hr₀.1 hri
  let hm := comparisonCap_monotoneOn (δ:=δ) hN hU.le hL hE hd.le
  let hM := comparisonCap_nonneg (δ:=δ) hN hU.le hL hE hd.le (show (0:ℝ) ≤ 1 by norm_num)
  let b' := fun w => (b w-omittedExtension hu
    (constrainedCoefficient hr hc hk hkc hm hM g hg.continuous α) w).toNNReal
  let h' := fun w => (h w+omittedExtension hu
    (constrainedCoefficient hr hc hk hkc hm hM (fun r => g r*r)
      (hg.continuous.mul continuous_id) α) w).toNNReal
  intro u huobs extra hextra xs z hxs has hu₀xs hr₀U hz hzxs hdD hupper hlower htest hreg hslow hbare hBclock
  classical
  let base := Classical.choice (rawFutureCutFamily_nonempty u hxs hB hμ hμB hu₀xs huobs)
  let cuts := base.retainExtra extra hextra
  let Q := constrainedQuantile hr hc hk hkc hm hM α
  let p (v : ℝ) (hv : v ∈ cuts.bands) : Icc u₀ 1 :=
    ⟨(cuts.p v).val,(cuts.cut_order v hv).2.2.1.le,
      (cuts.cut_order v hv).2.2.2.1.le.trans
        ((cuts.cut_order v hv).2.2.2.2.1.le.trans (cuts.cut_order v hv).2.2.2.2.2.1)⟩
  let q (v : ℝ) (hv : v ∈ cuts.bands) : Icc u₀ 1 :=
    ⟨(cuts.q v).val,(cuts.cut_order v hv).2.2.1.le.trans (cuts.cut_order v hv).2.2.2.1.le,
      (cuts.cut_order v hv).2.2.2.2.1.le.trans (cuts.cut_order v hv).2.2.2.2.2.1⟩
  let t (v : ℝ) (hv : v ∈ cuts.bands) : Icc u₀ 1 :=
    ⟨(cuts.t v).val,(cuts.cut_order v hv).2.2.1.le.trans
      ((cuts.cut_order v hv).2.2.2.1.le.trans (cuts.cut_order v hv).2.2.2.2.1.le),
      (cuts.cut_order v hv).2.2.2.2.2.1⟩
  have hcert := fun v (hv : v ∈ cuts.bands) => hnmargin E d xs v r₀ z
    (Q (p v hv)).val (Q (q v hv)).val (Q (t v hv)).val hE hd hdD hxs has
    (cuts.band_bounds v hv).1 (cuts.band_bounds v hv).2 hupper hlower hr₀U hz hzxs
    (Q (p v hv)).property (Q (q v hv)).property (Q (t v hv)).property α.val.val g α.val.property.2
    (by simpa only [p,(cuts.mass_values v hv).1] using constrainedQuantile_spec hr hc hk hkc hm hM α (p v hv))
    (by simpa only [q,(cuts.mass_values v hv).2.1] using constrainedQuantile_spec hr hc hk hkc hm hM α (q v hv))
    (by simpa only [t,(cuts.mass_values v hv).2.2] using constrainedQuantile_spec hr hc hk hkc hm hM α (t v hv))
    hreg hg hgpos hp hslow htest
  choose! η J hcert using hcert
  have hcuts : ∀ v ∈ cuts.bands, cuts.p v ∈ cuts.retained ∧ cuts.q v ∈ cuts.retained ∧
      u₀ < (cuts.p v).val ∧ (cuts.p v).val < (cuts.q v).val ∧ (cuts.q v).val < (cuts.t v).val ∧
      (cuts.t v).val ≤ 1 ∧ 2*v ≤ (cuts.p v).val ∧ 1 ≤ J v := by
    intro v hv
    obtain ⟨hp,hq,hp₀,hpq,hqt,ht₁,h2v⟩ := cuts.cut_order v hv
    exact ⟨hp,hq,hp₀,hpq,hqt,ht₁,h2v,(hcert v hv).1⟩
  refine ⟨cuts.retained,cuts.retained_le_one,cuts.observation_mem,?_,?_⟩
  · intro v hv
    exact List.mem_append_right _ hv
  
  apply hnraw hN hU hL (min_le_left _ _) hE hd.le hnq hr₀ hu₀ hn g α hg hgpos hp
    b h hb hh hbn hhn hmin cuts.retained cuts.retained_le_one u cuts.observation_mem
    xs C μ cl cu R F (κ₀/Real.log (n:ℝ)) K Ca hxs hC1 hmacro hcl hcu.le hR
    (div_pos hκ₀ hnlog) hK hCa hFmass hFradius hbare hBclock
    cuts.bands cuts.p cuts.q cuts.t η J cuts.cover hcuts
  intro v hv
  dsimp only
  have hpv := (cuts.mass_values v hv).1
  have hqv := (cuts.mass_values v hv).2.1
  have htv := (cuts.mass_values v hv).2.2
  have hdiff : (cuts.q v).val-(cuts.p v).val=B*v := by rw [hpv,hqv]; ring
  have hdiff' : (cuts.t v).val-(cuts.q v).val=B*v := by rw [hqv,htv]; ring
  simpa only [p,q,t,Q,N,hpv,hqv,htv,
    show (2:ℝ)*B*v-B*v=B*v by ring,
    show (3:ℝ)*B*v-2*B*v=B*v by ring] using (hcert v hv).2

 theorem comparison_minimum_finite_raw_ratio_retaining
    (ℓ : ℕ) (Bclock : ℝ) {m δ cl cu Az κ₀ C₀ Ct D : ℝ}
    (hm₀ : 0 < m) (hδ : 0 < δ) (hδm : δ < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hκ₀ : 0 < κ₀) (hC₀ : 0 < C₀) (hCt : 0 ≤ Ct) :
    ∃ C : ℝ, 0 < C ∧
    ∀ᶠ n : ℕ in atTop, ∀ {E d r₀ u₀ : ℝ}
    (hn : 0 < n) (hE : 0 < E) (hd : 0 < d)
    (hr₀ : r₀ ∈ Icc (0:ℝ) (1/4)) (hu₀ : u₀ ∈ Icc (0:ℝ) (1/4)) (g : ℝ → ℝ),
    let N := (n:ℝ)
    let U := comparisonSmallMass N E
    let L := comparisonConstraintLength N E d
    let hN : 0 < N := by dsimp only [N]; exact_mod_cast hn
    let hU := comparisonSmallMass_pos hN hE
    let hL := comparisonConstraintLength_pos hN hE hd
    let k := comparisonFloor N δ U
    let M := comparisonCap N δ U L E d
    let c := k 1
    let hr : r₀ ≤ 1 := le_trans hr₀.2 (by norm_num)
    let hu : u₀ ∈ Icc (0:ℝ) 1 := ⟨hu₀.1,le_trans hu₀.2 (by norm_num)⟩
    let hc : 0 < c := comparisonFloor_pos hN hU (by norm_num)
    let hk := comparisonFloor_continuousOn (δ:=δ) hN hU hr₀.1
    let hkc := fun r (hri : r ∈ Icc r₀ 1) => comparisonFloor_lower_on (δ:=δ) hN hU hr₀.1 hri
    let hm := comparisonCap_monotoneOn (δ:=δ) hN hU.le hL hE hd.le
    let hM := comparisonCap_nonneg (δ:=δ) hN hU.le hL hE hd.le (show (0:ℝ) ≤ 1 by norm_num)
    ∀ (α : inverseIntegralConstraints r₀ u₀ k M)
    (hg : ContDiff ℝ 1 g)
    (hgpos : ∀ r ∈ Icc r₀ 1, 0<g r)
    (hp : ∀ r ∈ Ioc r₀ 1, comparisonLogSlope g r ∈ Icc (0:ℝ) 1)
    (b h : ℝ → ℝ)
    (hb : ∀ β : inverseIntegralConstraints r₀ u₀ k M,
      MonotoneOn (fun u => b u-omittedExtension hu.2
        (constrainedCoefficient hr hc hk hkc hm hM g hg.continuous β) u) (Icc (0:ℝ) 1))
    (hh : ∀ β : inverseIntegralConstraints r₀ u₀ k M,
      MonotoneOn (fun u => h u+omittedExtension hu.2
        (constrainedCoefficient hr hc hk hkc hm hM (fun r => g r*r)
          (hg.continuous.mul continuous_id) β) u) (Icc (0:ℝ) 1))
    (hbn : ∀ β : inverseIntegralConstraints r₀ u₀ k M,
      0 ≤ b 0-omittedExtension hu.2 (constrainedCoefficient hr hc hk hkc hm hM g hg.continuous β) 0)
    (hhn : ∀ β : inverseIntegralConstraints r₀ u₀ k M,
      0 ≤ h 0+omittedExtension hu.2 (constrainedCoefficient hr hc hk hkc hm hM (fun r => g r*r)
        (hg.continuous.mul continuous_id) β) 0)
    (hmin : ∀ β : inverseIntegralConstraints r₀ u₀ k M,
      inverseCompensatedPressure hr hu.2 hc hk hkc hm hM g hg.continuous n b h 0 α ≤
      inverseCompensatedPressure hr hu.2 hc hk hkc hm hM g hg.continuous n b h 0 β),
    let b' := fun u => (b u-omittedExtension hu.2
      (constrainedCoefficient hr hc hk hkc hm hM g hg.continuous α) u).toNNReal
    let h' := fun u => (h u+omittedExtension hu.2
      (constrainedCoefficient hr hc hk hkc hm hM (fun r => g r*r)
        (hg.continuous.mul continuous_id) α) u).toNNReal
    ∀ (u : PositiveMass) (huobs : u.val ≤ 1)
    (extra : List PositiveMass) (hextra : ∀v∈extra,v.val≤1) (xs z : ℝ),
      0 < xs → comparisonLowerScale n E d ≤ xs → u₀ ≤ xs → r₀ ≤ U →
      z ∈ Icc r₀ 1 → z ≤ Az*xs → d ≤ D →
      Real.sqrt (n:ℝ)*E ≤ d^2 → (n:ℝ)^(-(2:ℝ)/3+m)*d ≤ C₀*E →
      (n:ℝ)*E^2 ≤ Ct*g xs*xs^2 →
      (∀ r ∈ Icc z 1, cl*r ≤ α.val.val r ∧ α.val.val r ≤ cu*r) →
      (∀ r ∈ Icc z 1, κ₀/Real.log (n:ℝ) ≤ 1-comparisonLogSlope g r) →
      MonotoneOn h (Icc u₀ 1) → (h' 1:ℝ)-(h' 0:ℝ) ≤ Bclock →
      ∃ us : List PositiveMass, (∀ v ∈ us, v.val ≤ 1) ∧ u ∈ us ∧
        (∀v∈extra,v∈us) ∧ ∀ᶠ j : ℕ in atTop,
          (physicalRawRatio n (ℓ+1) (sampleClockSteps (completedPathClock n b' h') 0 (finiteCutMasses us j))
            0 xs (Measure.pi fun i => gaussianReal 0 (completedPathClock n b' h' 0 i)) id measurable_id)^2 ≤ 2*C := by
  obtain ⟨B,Ca,K,R,C,μ,F,hB,hBcu,hBA,hCa,hCaB,hK,hKcu,hR,hR1,hKR,hcuR,
    hC,hC1,hmacro,hμ,hμR,hμB,hFmass,hFradius⟩ := exists_raw_regular_constants hcl hcu hAz
  exact ⟨C,zero_lt_one.trans_le hC1,
    eventually_comparison_minimum_raw_ratio_regular_retaining ℓ Bclock hm₀ hδ hδm
      hB hcl hcu hAz hBcu hBA hCa hCaB hK hKcu hR hR1 hKR hcuR hC hC1 hmacro
      hμ hμR hμB hFmass hFradius hκ₀ hC₀ hCt⟩

end OAI.SKFluctuations
