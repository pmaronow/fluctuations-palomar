module

public import SKBarriers2.Static.FloorCost
public import SKBarriers2.Overshoot.TrialBound
public import SKBarriers2.Overshoot.ScheduleParisi
public import SKBarriers2.Overshoot.FloorResponse

@[expose] public section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
open OAI.SK.Analytic

namespace SKBarriers2

def HomogeneousFloorResponse (β : ℝ) : Prop :=
  ∀ K H : ℝ≥0, ∃ C : ℝ, 0 ≤ C ∧
    ∀ (α γ : ℝ → ℝ),
      (∀ z, α z ∈ Icc (0 : ℝ) 1) → Monotone α →
      (∀ z, γ z ∈ Icc (0 : ℝ) 1) → Monotone γ →
      ∀ (F V : ℝ → ℝ), BoundedDerivs F → BoundedDerivs V →
      LipschitzWith K F → LipschitzWith H (deriv F) →
      ∀ ε L : ℝ, 0 ≤ ε → 0 ≤ L → ε + L ≤ 1 →
      (∀ z, |V z| ≤ ε) → (∀ z, |deriv V z| ≤ L) →
      ∀ t : ℝ≥0, t ≤ 1 →
      |(scalarCDFOperator β (fun z => γ z / 3) 0 t (fun z => F z + V z) 0 -
          scalarCDFOperator β (fun z => γ z / 3) 0 t F 0) -
        (scalarCDFOperator β (fun z => α z / 3) 0 t (fun z => F z + V z) 0 -
          scalarCDFOperator β (fun z => α z / 3) 0 t F 0)| ≤
        C * (ε + L) * (∫ z in Icc (0 : ℝ) (t : ℝ), |γ z - α z|)

def LocalWindowGeometry (α : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ∃ a d₀ : ℝ, 0 < a ∧ 0 < d₀ ∧
    ∀ r ∈ I, ∀ d : ℝ, 0 < d → d ≤ d₀ →
      a ≤ r - 2 * d ∧ r + 6 * d ≤ 1 ∧ α (r + d) / 2 ≤ α r

def LocalBoundaryControl (β : ℝ) (α : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ∃ d₀ B : ℝ, ∃ K H : ℝ≥0, 0 < d₀ ∧ 0 ≤ B ∧
    ∀ r ∈ I, ∀ d δ : ℝ, 0 < d → d ≤ d₀ → |δ| ≤ d →
      ∀ N : ℕ, 0 < N →
      LipschitzWith K (OW.boundary β α (1 / 2) (r - 2 * d) (2 * d) 0 N) ∧
      LipschitzWith H (deriv (OW.boundary β α (1 / 2) (r - 2 * d) (2 * d) 0 N)) ∧
      ∀ z : ℝ,
        |OW.boundary β α (1 / 2) (r - 2 * d) (2 * d) (δ / (2 * d)) N z -
          OW.boundary β α (1 / 2) (r - 2 * d) (2 * d) 0 N z| ≤ B * δ ^ 2 / d

def ZeroTiltParisiLimit (β : ℝ) (α : ℝ → ℝ) : Prop :=
  ∀ γ : ℝ → ℝ, (∀ z, γ z ∈ Icc (0 : ℝ) 1) → Monotone γ →
    ∀ r d : ℝ, 0 < d → 0 ≤ r - 2 * d → r + 6 * d ≤ 1 →
      (∀ t ∈ Icc (r - 2 * d) 1, γ t = α t) →
      Tendsto (fun N : ℕ => OW.trialValue β γ α r d 0 N) atTop
        (𝓝 (3 * scalarCDFParisi β γ))

private theorem relativeGridProfile_tendsto {α : ℝ → ℝ} {a len x : ℝ}
    (hlen : 0 < len) (hax : a ≤ x) (hx : ContinuousAt α x) :
    Tendsto (fun N : ℕ => OW.relativeGridProfile α a len (N + 1) x) atTop (𝓝 (α x)) := by
  let p := fun N : ℕ => a + len *
    (⌊(x - a) * ((N + 1 : ℕ) : ℝ) / len⌋₊ : ℝ) / ((N + 1 : ℕ) : ℝ)
  have herr (N : ℕ) : 0 ≤ x - p N ∧ x - p N ≤ len / ((N + 1 : ℕ) : ℝ) := by
    have hN : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
    let u : ℝ := (x - a) * ((N + 1 : ℕ) : ℝ) / len
    have hu : 0 ≤ u := div_nonneg (mul_nonneg (sub_nonneg.mpr hax) hN.le) hlen.le
    have hlo := mul_le_mul_of_nonneg_right (Nat.floor_le hu) hlen.le
    have hhi := mul_lt_mul_of_pos_right (Nat.lt_floor_add_one u) hlen
    have he : u * len = (x - a) * ((N + 1 : ℕ) : ℝ) := div_mul_cancel₀ _ hlen.ne'
    rw [he] at hlo hhi
    have hp : (p N - a) * ((N + 1 : ℕ) : ℝ) = len * (⌊u⌋₊ : ℝ) := by
      dsimp only [p, u]
      field_simp
      ring
    have hdiv : (len / ((N + 1 : ℕ) : ℝ)) * ((N + 1 : ℕ) : ℝ) = len :=
      div_mul_cancel₀ _ hN.ne'
    constructor
    · nlinarith only [hlo, hp, hN]
    · nlinarith only [hhi, hp, hdiv, hN]
  have hz : Tendsto (fun N : ℕ => len / ((N + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have he := squeeze_zero (fun N => (herr N).1) (fun N => (herr N).2) hz
  have hp : Tendsto p atTop (𝓝 x) := by
    simpa only [sub_zero, sub_sub_cancel] using (tendsto_const_nhds (x := x)).sub he
  exact hx.tendsto.comp hp

private theorem relativeWindowProfile_tendsto {α : ℝ → ℝ} {p s h x : ℝ}
    (hh : 0 < h) (hp : p ∈ Ioo (0 : ℝ) 1) (hx : ContinuousAt α x) :
    Tendsto (fun N : ℕ => OW.relativeWindowProfile α p s h (N + 1) x) atTop (𝓝 (α x)) := by
  by_cases h₀ : x < s
  · simpa only [OW.relativeWindowProfile, ite_eq_left h₀] using
      (tendsto_const_nhds : Tendsto (fun _N : ℕ => α x) atTop (𝓝 (α x)))
  by_cases h₁ : x < s + h
  · simpa only [OW.relativeWindowProfile, ite_eq_right h₀, ite_eq_left h₁] using
      relativeGridProfile_tendsto hh (le_of_not_gt h₀) hx
  by_cases h₂ : x < s + (1 + p) * h
  · simpa only [OW.relativeWindowProfile, ite_eq_right h₀, ite_eq_right h₁, ite_eq_left h₂] using
      relativeGridProfile_tendsto (mul_pos hp.1 hh) (le_of_not_gt h₁) hx
  by_cases h₃ : x < s + 2 * h
  · simpa only [OW.relativeWindowProfile, ite_eq_right h₀, ite_eq_right h₁, ite_eq_right h₂, ite_eq_left h₃] using
      relativeGridProfile_tendsto (mul_pos (sub_pos.mpr hp.2) hh) (le_of_not_gt h₂) hx
  by_cases h₄ : x < s + 4 * h
  · simpa only [OW.relativeWindowProfile, ite_eq_right h₀, ite_eq_right h₁, ite_eq_right h₂, ite_eq_right h₃,
      ite_eq_left h₄] using relativeGridProfile_tendsto (by positivity : 0 < 2 * h)
        (le_of_not_gt h₃) hx
  · simpa only [OW.relativeWindowProfile, ite_eq_right h₀, ite_eq_right h₁, ite_eq_right h₂, ite_eq_right h₃,
      ite_eq_right h₄] using
      (tendsto_const_nhds : Tendsto (fun _N : ℕ => α x) atTop (𝓝 (α x)))

theorem zeroTiltParisiLimit_of_monotone {β : ℝ} {α : ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0 : ℝ) 1) (hαm : Monotone α) :
    ZeroTiltParisiLimit β α := by
  intro γ hγ hγm r d hd hs hT heq
  let A := fun N : ℕ => OW.joinedWindowProfile γ α (1 / 2) (r - 2 * d) (2 * d) (N + 1)
  have hh : 0 < 2 * d := by positivity
  have hp : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := by constructor <;> norm_num
  have hjoin : γ (r - 2 * d) ≤ α (r - 2 * d) :=
    (heq _ ⟨le_rfl, by linarith⟩).le
  have hbA (N : ℕ) (x : ℝ) : A N x ∈ Icc (0 : ℝ) 1 :=
    OW.joinedWindowProfile_bounds γ α hγ hα _ _ _ _ x
  have hmA (N : ℕ) : Monotone (A N) :=
    OW.joinedWindowProfile_monotone γ α hγm hαm _ _ _ (Nat.succ_pos N) hh hp hjoin
  have hc : ∀ᵐ x : ℝ, ContinuousAt α x := by
    filter_upwards [hαm.countable_not_continuousAt.ae_notMem volume] with x hx
    exact not_not.mp hx
  have hpoint : ∀ᵐ x ∂volume.restrict (Icc (0 : ℝ) 1),
      Tendsto (fun N => |A N x - γ x|) atTop (𝓝 0) := by
    filter_upwards [ae_restrict_of_ae hc, ae_restrict_mem measurableSet_Icc] with x hx hmem
    have hval : Tendsto (fun N => A N x) atTop (𝓝 (γ x)) := by
      by_cases hxs : x < r - 2 * d
      · simpa only [A, OW.joinedWindowProfile, ite_eq_left hxs] using
          (tendsto_const_nhds : Tendsto (fun _N : ℕ => γ x) atTop (𝓝 (γ x)))
      · have hxα := relativeWindowProfile_tendsto (s := r - 2 * d) hh hp hx
        rw [← heq x ⟨le_of_not_gt hxs, hmem.2⟩] at hxα
        simpa only [A, OW.joinedWindowProfile, ite_eq_right hxs] using hxα
    simpa only [sub_self, abs_zero] using (hval.sub_const (γ x)).abs
  have hdist : Tendsto (fun N => ∫ x in Icc (0 : ℝ) 1, |A N x - γ x|) atTop (𝓝 0) := by
    have H := tendsto_integral_of_dominated_convergence
      (μ := volume.restrict (Icc (0 : ℝ) 1))
      (F := fun N x => |A N x - γ x|) (f := fun _ => (0 : ℝ)) (fun _ => (1 : ℝ))
      (fun N => ((hmA N).measurable.sub hγm.measurable).abs.aestronglyMeasurable)
      (integrable_const 1) (fun N => ae_of_all _ (fun x => by
        rw [Real.norm_eq_abs, abs_abs]
        apply abs_le.mpr
        constructor <;> linarith [(hbA N x).1, (hbA N x).2, (hγ x).1, (hγ x).2])) hpoint
    simpa only [integral_zero] using H
  have hpar := scalarCDFParisi_tendsto_of_L1 β hγ hγm hbA hmA hdist
  have htrial : Tendsto (fun N : ℕ => OW.trialValue β γ α r d 0 (N + 1)) atTop
      (𝓝 (3 * scalarCDFParisi β γ)) := by
    have he (N : ℕ) : OW.trialValue β γ α r d 0 (N + 1) =
        3 * scalarCDFParisi β (A N) :=
      OW.trialValue_zero_parisi β γ α hγ hγm hα hαm r d (Nat.succ_pos N) hd hs
        (by linarith) hjoin
    simpa only [he] using hpar.const_mul 3
  exact (tendsto_add_atTop_iff_nat 1).mp htrial

private theorem trial_response_identity (β : ℝ) (γ α : ℝ → ℝ)
    (r d δ : ℝ) (N : ℕ) :
    (OW.trialValue β γ α r d δ N - OW.trialValue β γ α r d 0 N) -
        (OW.trialValue β α α r d δ N - OW.trialValue β α α r d 0 N) =
      (scalarCDFOperator β (fun z => γ z / 3) 0 (Real.toNNReal (r - 2 * d))
          (OW.boundary β α (1 / 2) (r - 2 * d) (2 * d) (δ / (2 * d)) N) 0 -
        scalarCDFOperator β (fun z => γ z / 3) 0 (Real.toNNReal (r - 2 * d))
          (OW.boundary β α (1 / 2) (r - 2 * d) (2 * d) 0 N) 0) -
      (scalarCDFOperator β (fun z => α z / 3) 0 (Real.toNNReal (r - 2 * d))
          (OW.boundary β α (1 / 2) (r - 2 * d) (2 * d) (δ / (2 * d)) N) 0 -
        scalarCDFOperator β (fun z => α z / 3) 0 (Real.toNNReal (r - 2 * d))
          (OW.boundary β α (1 / 2) (r - 2 * d) (2 * d) 0 N) 0) := by
  unfold OW.trialValue OW.penalty
  simp only [zero_div]
  ring

theorem trialValue_floor_transfer {β : ℝ} {α γ : ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0 : ℝ) 1) (hαm : Monotone α)
    (_hγ : ∀ z, γ z ∈ Icc (0 : ℝ) 1) (hγm : Monotone γ)
    {K H : ℝ≥0} {C : ℝ} (hC : 0 ≤ C)
    (hresp : ∀ (F V : ℝ → ℝ), BoundedDerivs F → BoundedDerivs V →
      LipschitzWith K F → LipschitzWith H (deriv F) →
      ∀ ε L : ℝ, 0 ≤ ε → 0 ≤ L → ε + L ≤ 1 →
      (∀ z, |V z| ≤ ε) → (∀ z, |deriv V z| ≤ L) →
      ∀ t : ℝ≥0, t ≤ 1 →
      |(scalarCDFOperator β (fun z => γ z / 3) 0 t (fun z => F z + V z) 0 -
          scalarCDFOperator β (fun z => γ z / 3) 0 t F 0) -
        (scalarCDFOperator β (fun z => α z / 3) 0 t (fun z => F z + V z) 0 -
          scalarCDFOperator β (fun z => α z / 3) 0 t F 0)| ≤
        C * (ε + L) * (∫ z in Icc (0 : ℝ) (t : ℝ), |γ z - α z|))
    {r d δ ε L D : ℝ} {N : ℕ}
    (hd : 0 < d) (hs : 0 ≤ r - 2 * d) (hT : r + 6 * d ≤ 1)
    (hFK : LipschitzWith K (OW.boundary β α (1 / 2) (r - 2 * d) (2 * d) 0 N))
    (hFH : LipschitzWith H (deriv (OW.boundary β α (1 / 2) (r - 2 * d) (2 * d) 0 N)))
    (hε : 0 ≤ ε) (hL : 0 ≤ L) (hsmall : ε + L ≤ 1)
    (hV : ∀ z, |OW.boundary β α (1 / 2) (r - 2 * d) (2 * d) (δ / (2 * d)) N z -
      OW.boundary β α (1 / 2) (r - 2 * d) (2 * d) 0 N z| ≤ ε)
    (hV' : ∀ z, |deriv (fun z =>
      OW.boundary β α (1 / 2) (r - 2 * d) (2 * d) (δ / (2 * d)) N z -
      OW.boundary β α (1 / 2) (r - 2 * d) (2 * d) 0 N z) z| ≤ L)
    (hD : (∫ z in Icc (0 : ℝ) 1, |γ z - α z|) ≤ D) :
    OW.trialValue β γ α r d δ N ≤ OW.trialValue β α α r d δ N +
      (OW.trialValue β γ α r d 0 N - OW.trialValue β α α r d 0 N) + C * (ε + L) * D := by
  let F := OW.boundary β α (1 / 2) (r - 2 * d) (2 * d) 0 N
  let V := fun z => OW.boundary β α (1 / 2) (r - 2 * d) (2 * d) (δ / (2 * d)) N z - F z
  have ht : r - 2 * d + 4 * (2 * d) ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hF : BoundedDerivs F := OW.boundary_regular β α hα hαm _ _ _ _ N ht
  have hG : BoundedDerivs (OW.boundary β α (1 / 2) (r - 2 * d) (2 * d)
      (δ / (2 * d)) N) := OW.boundary_regular β α hα hαm _ _ _ _ N ht
  have he : (fun z => F z + V z) =
      OW.boundary β α (1 / 2) (r - 2 * d) (2 * d) (δ / (2 * d)) N := by
    funext z
    dsimp only [F, V]
    ring
  have hVreg : BoundedDerivs V := by
    simpa only [V, sub_eq_add_neg, neg_one_mul] using hG.add (hF.const_mul (-1))
  have Hresp := hresp F V hF hVreg hFK hFH ε L hε hL hsmall hV hV'
    (Real.toNNReal (r - 2 * d)) (Real.toNNReal_le_one.mpr (by linarith))
  rw [he, Real.coe_toNNReal _ hs] at Hresp
  have hi : IntegrableOn (fun z => |γ z - α z|) (Icc (0 : ℝ) 1) :=
    ((hγm.monotoneOn _).integrableOn_isCompact isCompact_Icc |>.sub
      ((hαm.monotoneOn _).integrableOn_isCompact isCompact_Icc)).abs
  have hsub : Icc (0 : ℝ) (r - 2 * d) ⊆ Icc (0 : ℝ) 1 :=
    Icc_subset_Icc le_rfl (by linarith)
  have hdist : (∫ z in Icc (0 : ℝ) (r - 2 * d), |γ z - α z|) ≤ D :=
    (setIntegral_mono_set hi (ae_of_all _ (fun z => abs_nonneg _))
      (Filter.Eventually.of_forall (fun _ hz => hsub hz))).trans hD
  have H := Hresp.trans (mul_le_mul_of_nonneg_left hdist
    (mul_nonneg hC (add_nonneg hε hL)))
  rw [← trial_response_identity β γ α r d δ N] at H
  linarith [le_abs_self ((OW.trialValue β γ α r d δ N - OW.trialValue β γ α r d 0 N) -
    (OW.trialValue β α α r d δ N - OW.trialValue β α α r d 0 N))]

private theorem band_ratio_le {ρ E d δ : ℝ} (hρ : 0 < ρ) (hE : 0 < E)
    (hρd : ρ ≤ d) (hδ : |δ| ≤ 2 * E * ρ) :
    δ ^ 2 / d ≤ 4 * E ^ 2 * ρ := by
  have hd : 0 < d := hρ.trans_le hρd
  have hsq : δ ^ 2 ≤ (2 * E * ρ) ^ 2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg δ) (by positivity : 0 ≤ 2 * E * ρ)).mpr hδ
  apply (div_le_iff₀ hd).mpr
  nlinarith [mul_le_mul_of_nonneg_left hρd (show 0 ≤ 4 * E ^ 2 * ρ by positivity)]

private theorem band_gain_le {ρ E d δ : ℝ} (hρ : 0 < ρ) (hE : 0 < E)
    (hρd : ρ ≤ d) (hδ : E * ρ ≤ |δ|) :
    E ^ 2 * ρ ^ 3 ≤ δ ^ 2 * d := by
  have hsq : (E * ρ) ^ 2 ≤ δ ^ 2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (by positivity : 0 ≤ E * ρ) (abs_nonneg δ)).mpr hδ
  nlinarith [mul_le_mul_of_nonneg_right hsq hρ.le,
    mul_le_mul_of_nonneg_left hρd (sq_nonneg δ)]

theorem localFractionalGap_of_cubicGap {β : ℝ} {α : ℝ → ℝ} {I : Set ℝ}
    {ρ : ℕ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0 : ℝ) 1) (hαm : Monotone α)
    (hmin : scalarCDFParisi β α = finiteParisiInf β)
    (hcubic : LocalCubicGap β α I) (hfloor : FloorTrial β α 3)
    (hresp : HomogeneousFloorResponse β)
    (hgeometry : LocalWindowGeometry α I)
    (hboundary : LocalBoundaryControl β α I)
    (hρlim : Tendsto ρ atTop (𝓝 0)) (hρpos : ∀ᶠ n : ℕ in atTop, 0 < ρ n) :
    ∃ E₀ : ℝ, 0 < E₀ ∧ ∀ E ∈ Ioc (0 : ℝ) E₀,
      ∃ g₀ : ℝ, 0 < g₀ ∧ ∀ g ∈ Ioo (0 : ℝ) g₀,
        ∃ S₀ : ℝ, 0 < S₀ ∧ ∀ S ∈ Ioc (0 : ℝ) S₀,
          LocalFractionalGap β I ρ S E g := by
  have hbaseline : ZeroTiltParisiLimit β α := zeroTiltParisiLimit_of_monotone hα hαm
  obtain ⟨dc, κ, gc, Cd, hdc, hκ, hgc, hCd, hgap⟩ := hcubic
  obtain ⟨Cf, sf, hCf, hsf, hfl⟩ := hfloor
  obtain ⟨a, dg, ha, hdg, hgeom⟩ := hgeometry
  obtain ⟨db, B, K, H, hdb, hB, hbd⟩ := hboundary
  obtain ⟨Cr, hCr, hrsp⟩ := hresp K H
  refine ⟨min (κ / 2) (1 / 2), lt_min (by positivity) (by norm_num), ?_⟩
  intro E hE
  have hEκ : 2 * E ≤ κ := by linarith [(le_min_iff.mp hE.2).1]
  have hE1 : 2 * E ≤ 1 := by linarith [(le_min_iff.mp hE.2).2]
  refine ⟨gc * E ^ 2, mul_pos hgc (sq_pos_of_pos hE.1), ?_⟩
  intro g hg
  let A : ℝ := 3 * Cf + 4 * Cr * Cf * (B + Cd) * E ^ 2
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  obtain ⟨s₁, hs₁, hs₁margin⟩ := exists_pos_mul_lt (sub_pos.mpr hg.2) A
  refine ⟨min 1 s₁, lt_min zero_lt_one hs₁, ?_⟩
  intro S hS
  have hS1 : S ≤ 1 := (le_min_iff.mp hS.2).1
  have hSs₁ : S ≤ s₁ := (le_min_iff.mp hS.2).2
  have hS2 : S ^ 2 ≤ S := by nlinarith [hS.1]
  have hS3 : S ^ 3 ≤ S := by nlinarith [mul_le_mul_of_nonneg_left hS2 hS.1.le]
  have hmargin : 3 * Cf * S ^ 3 + 4 * Cr * Cf * (B + Cd) * E ^ 2 * S ^ 2 <
      gc * E ^ 2 - g := by
    calc
      _ ≤ A * S := by
        dsimp only [A]
        nlinarith [mul_le_mul_of_nonneg_left hS3 (show 0 ≤ 3 * Cf by positivity),
          mul_le_mul_of_nonneg_left hS2
            (show 0 ≤ 4 * Cr * Cf * (B + Cd) * E ^ 2 by positivity)]
      _ ≤ A * s₁ := mul_le_mul_of_nonneg_left hSs₁ hA
      _ < _ := hs₁margin
  let d₀ : ℝ := min dc (min dg db)
  have hd₀ : 0 < d₀ := lt_min hdc (lt_min hdg hdb)
  refine ⟨d₀, hd₀, ?_⟩
  have hsmall_s : ∀ᶠ n : ℕ in atTop, S * ρ n ≤ sf :=
    (hρlim.const_mul S).eventually (eventually_le_nhds (by simpa using hsf))
  have hsmall_mass : ∀ᶠ n : ℕ in atTop, 3 * (S * ρ n) ≤ 1 :=
    ((hρlim.const_mul S).const_mul 3).eventually
      (eventually_le_nhds (by norm_num))
  have hsmall_support : ∀ᶠ n : ℕ in atTop, Cf * (S * ρ n) ≤ a :=
    ((hρlim.const_mul S).const_mul Cf).eventually
      (eventually_le_nhds (by simpa using ha))
  have hsmall_C1 : ∀ᶠ n : ℕ in atTop, (B + Cd) * (4 * E ^ 2 * ρ n) ≤ 1 :=
    ((hρlim.const_mul (4 * E ^ 2)).const_mul (B + Cd)).eventually
      (eventually_le_nhds (by norm_num))
  filter_upwards [hρpos, hsmall_s, hsmall_mass, hsmall_support, hsmall_C1,
    eventually_gt_atTop (0 : ℕ)] with n hρ hsfloor hmass hsupp hC1 hn
  intro r hr δ q hρd hdmax hδlo hδhi hD
  let d := q - r
  have hd : 0 < d := hρ.trans_le hρd
  have hdc' : d ≤ dc := hdmax.trans (min_le_left _ _)
  have hdg' : d ≤ dg := hdmax.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hdb' : d ≤ db := hdmax.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hprefix, hT, hsep⟩ := hgeom r hr d hd hdg'
  have hs : 0 ≤ r - 2 * d := ha.le.trans hprefix
  have hδd : |δ| ≤ d := hδhi.trans
    ((mul_le_of_le_one_left hρ.le hE1).trans hρd)
  have hδκ : |δ| ≤ κ * d := hδhi.trans (by
    calc
      2 * E * ρ n ≤ κ * ρ n := mul_le_mul_of_nonneg_right hEκ hρ.le
      _ ≤ κ * d := mul_le_mul_of_nonneg_left hρd hκ.le)
  have hδpos : 0 < |δ| := (mul_pos hE.1 hρ).trans_le hδlo
  obtain ⟨hgapN, hderiv⟩ := hgap r hr d δ hd hdc' hδpos hδκ
  let σ := S * ρ n
  let γ := fun t => max (α t) (3 * σ)
  have hσ : 0 < σ := mul_pos hS.1 hρ
  obtain ⟨hcost, heq, hdist⟩ := hfl σ ⟨hσ, hsfloor⟩
  have hγ : ∀ t, γ t ∈ Icc (0 : ℝ) 1 := by
    intro t
    exact ⟨(hα t).1.trans (le_max_left _ _), max_le (hα t).2 hmass⟩
  have hγmass : ∀ t, γ t ∈ Icc (3 * σ) 1 := by
    intro t
    exact ⟨le_max_right _ _, (hγ t).2⟩
  have hγm : Monotone γ := hαm.max monotone_const
  have heq_window : ∀ t ∈ Icc (r - 2 * d) 1, γ t = α t := by
    intro t ht
    exact heq t (hsupp.trans (hprefix.trans ht.1))
  have hratio := band_ratio_le hρ hE.1 hρd hδhi
  have hsmall : B * δ ^ 2 / d + Cd * δ ^ 2 / d ≤ 1 := by
    calc
      _ = (B + Cd) * (δ ^ 2 / d) := by ring
      _ ≤ (B + Cd) * (4 * E ^ 2 * ρ n) :=
        mul_le_mul_of_nonneg_left hratio (add_nonneg hB hCd)
      _ ≤ 1 := hC1
  let R : ℝ := Cr * ((B + Cd) * δ ^ 2 / d) * (Cf * σ ^ 2)
  have hfixed : ∀ᶠ M : ℕ in atTop,
      fractionalPressure n 3 β σ (tripleGram r δ q) ≤
        3 * finiteParisiInf β - gc * δ ^ 2 * d +
          (OW.trialValue β γ α r d 0 M - OW.trialValue β α α r d 0 M) + R := by
    filter_upwards [hgapN, eventually_gt_atTop (0 : ℕ)] with M hMgap hM
    obtain ⟨hFK, hFH, hV⟩ := hbd r hr d δ hd hdb' hδd M hM
    have htransfer := trialValue_floor_transfer hα hαm hγ hγm hCr
      (hrsp α γ hα hαm hγ hγm) hd hs hT hFK hFH
      (by positivity : 0 ≤ B * δ ^ 2 / d) (by positivity : 0 ≤ Cd * δ ^ 2 / d)
      hsmall hV (hderiv M hM) hdist
    have hk : |δ / (2 * d)| ≤ (1 / 2 : ℝ) := by
      rw [abs_div, abs_of_pos (by positivity : 0 < 2 * d)]
      apply (div_le_iff₀ (by positivity : 0 < 2 * d)).mpr
      linarith
    have hD' : Nonempty (MatrixStates n 3 (tripleGram r δ (r + d))) := by
      simpa only [d, add_sub_cancel] using hD
    have htrial := OW.fractionalPressure_le_trialValue hn hM β σ hσ γ α hγmass hγm
      hα hαm r d δ hd hs hT hk hsep heq_window hD'
    have hq : r + d = q := by dsimp only [d]; ring
    rw [hq] at htrial
    have hR : Cr * (B * δ ^ 2 / d + Cd * δ ^ 2 / d) * (Cf * σ ^ 2) = R := by
      dsimp only [R]
      ring
    rw [hR] at htransfer
    linarith
  have hlimγ := hbaseline γ hγ hγm r d hd hs hT heq_window
  have hlimα := hbaseline α hα hαm r d hd hs hT (fun _ _ => rfl)
  have hlim := (((hlimγ.sub hlimα).const_add
    (3 * finiteParisiInf β - gc * δ ^ 2 * d)).add_const R)
  have hpressure := ge_of_tendsto hlim hfixed
  rw [hmin] at hpressure
  have hcost' : scalarCDFParisi β γ - finiteParisiInf β ≤ Cf * σ ^ (3 : ℕ) := by
    simpa only [Real.rpow_ofNat] using hcost
  have hRbound : R ≤ 4 * Cr * Cf * (B + Cd) * E ^ 2 * S ^ 2 * ρ n ^ 3 := by
    calc
      R = Cr * (B + Cd) * (δ ^ 2 / d) * (Cf * σ ^ 2) := by dsimp only [R]; ring
      _ ≤ Cr * (B + Cd) * (4 * E ^ 2 * ρ n) * (Cf * σ ^ 2) := by
        gcongr
      _ = _ := by dsimp only [σ]; ring
  have hgain := mul_le_mul_of_nonneg_left (band_gain_le hρ hE.1 hρd hδlo) hgc.le
  change gc * (E ^ 2 * ρ n ^ 3) ≤ gc * (δ ^ 2 * d) at hgain
  have hmargin' := mul_le_mul_of_nonneg_right hmargin.le (show 0 ≤ ρ n ^ 3 by positivity)
  have hcostscale : σ ^ (3 : ℕ) = S ^ 3 * ρ n ^ 3 := by dsimp only [σ]; ring
  rw [hcostscale] at hcost'
  change fractionalPressure n 3 β σ (tripleGram r δ q) ≤ _
  nlinarith only [hpressure, hcost', hRbound, hgain, hmargin']

theorem ScalarData.localFractionalGap_of_cubicGap {β : ℝ} (D : ScalarData β)
    {I : Set ℝ} {ρ : ℕ → ℝ}
    (hcubic : LocalCubicGap β (cdf (D.μ : Measure ℝ)) I)
    (hresp : HomogeneousFloorResponse β)
    (hgeometry : LocalWindowGeometry (cdf (D.μ : Measure ℝ)) I)
    (hboundary : LocalBoundaryControl β (cdf (D.μ : Measure ℝ)) I)
    (hρlim : Tendsto ρ atTop (𝓝 0)) (hρpos : ∀ᶠ n : ℕ in atTop, 0 < ρ n) :
    ∃ E₀ : ℝ, 0 < E₀ ∧ ∀ E ∈ Ioc (0 : ℝ) E₀,
      ∃ g₀ : ℝ, 0 < g₀ ∧ ∀ g ∈ Ioo (0 : ℝ) g₀,
        ∃ S₀ : ℝ, 0 < S₀ ∧ ∀ S ∈ Ioc (0 : ℝ) S₀,
          LocalFractionalGap β I ρ S E g :=
  SKBarriers2.localFractionalGap_of_cubicGap
    (fun z => ⟨cdf_nonneg _ z, cdf_le_one _ z⟩) (cdf (D.μ : Measure ℝ)).mono
    D.minimizer hcubic D.floorTrial hresp hgeometry hboundary hρlim hρpos

theorem localFractionalGap_of_cubicGap_uniform {β : ℝ} {α : ℝ → ℝ} {I : Set ℝ}
    (hα : ∀ z, α z ∈ Icc (0 : ℝ) 1) (hαm : Monotone α)
    (hmin : scalarCDFParisi β α = finiteParisiInf β)
    (hcubic : LocalCubicGap β α I) (hfloor : FloorTrial β α 3)
    (hresp : HomogeneousFloorResponse β)
    (hgeometry : LocalWindowGeometry α I)
    (hboundary : LocalBoundaryControl β α I) :
    ∃ E₀ : ℝ, 0 < E₀ ∧ ∀ E ∈ Ioc (0 : ℝ) E₀,
      ∃ g₀ : ℝ, 0 < g₀ ∧ ∀ g ∈ Ioo (0 : ℝ) g₀,
        ∃ S₀ : ℝ, 0 < S₀ ∧ ∀ S ∈ Ioc (0 : ℝ) S₀,
          ∀ ρ : ℕ → ℝ, Tendsto ρ atTop (𝓝 0) →
            (∀ᶠ n : ℕ in atTop, 0 < ρ n) → LocalFractionalGap β I ρ S E g := by
  have hbaseline : ZeroTiltParisiLimit β α := zeroTiltParisiLimit_of_monotone hα hαm
  obtain ⟨dc, κ, gc, Cd, hdc, hκ, hgc, hCd, hgap⟩ := hcubic
  obtain ⟨Cf, sf, hCf, hsf, hfl⟩ := hfloor
  obtain ⟨a, dg, ha, hdg, hgeom⟩ := hgeometry
  obtain ⟨db, B, K, H, hdb, hB, hbd⟩ := hboundary
  obtain ⟨Cr, hCr, hrsp⟩ := hresp K H
  refine ⟨min (κ / 2) (1 / 2), lt_min (by positivity) (by norm_num), ?_⟩
  intro E hE
  have hEκ : 2 * E ≤ κ := by linarith [(le_min_iff.mp hE.2).1]
  have hE1 : 2 * E ≤ 1 := by linarith [(le_min_iff.mp hE.2).2]
  refine ⟨gc * E ^ 2, mul_pos hgc (sq_pos_of_pos hE.1), ?_⟩
  intro g hg
  let A : ℝ := 3 * Cf + 4 * Cr * Cf * (B + Cd) * E ^ 2
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  obtain ⟨s₁, hs₁, hs₁margin⟩ := exists_pos_mul_lt (sub_pos.mpr hg.2) A
  refine ⟨min 1 s₁, lt_min zero_lt_one hs₁, ?_⟩
  intro S hS ρ hρlim hρpos
  have hS1 : S ≤ 1 := (le_min_iff.mp hS.2).1
  have hSs₁ : S ≤ s₁ := (le_min_iff.mp hS.2).2
  have hS2 : S ^ 2 ≤ S := by nlinarith [hS.1]
  have hS3 : S ^ 3 ≤ S := by nlinarith [mul_le_mul_of_nonneg_left hS2 hS.1.le]
  have hmargin : 3 * Cf * S ^ 3 + 4 * Cr * Cf * (B + Cd) * E ^ 2 * S ^ 2 <
      gc * E ^ 2 - g := by
    calc
      _ ≤ A * S := by
        dsimp only [A]
        nlinarith [mul_le_mul_of_nonneg_left hS3 (show 0 ≤ 3 * Cf by positivity),
          mul_le_mul_of_nonneg_left hS2
            (show 0 ≤ 4 * Cr * Cf * (B + Cd) * E ^ 2 by positivity)]
      _ ≤ A * s₁ := mul_le_mul_of_nonneg_left hSs₁ hA
      _ < _ := hs₁margin
  let d₀ : ℝ := min dc (min dg db)
  have hd₀ : 0 < d₀ := lt_min hdc (lt_min hdg hdb)
  refine ⟨d₀, hd₀, ?_⟩
  have hsmall_s : ∀ᶠ n : ℕ in atTop, S * ρ n ≤ sf :=
    (hρlim.const_mul S).eventually (eventually_le_nhds (by simpa using hsf))
  have hsmall_mass : ∀ᶠ n : ℕ in atTop, 3 * (S * ρ n) ≤ 1 :=
    ((hρlim.const_mul S).const_mul 3).eventually
      (eventually_le_nhds (by norm_num))
  have hsmall_support : ∀ᶠ n : ℕ in atTop, Cf * (S * ρ n) ≤ a :=
    ((hρlim.const_mul S).const_mul Cf).eventually
      (eventually_le_nhds (by simpa using ha))
  have hsmall_C1 : ∀ᶠ n : ℕ in atTop, (B + Cd) * (4 * E ^ 2 * ρ n) ≤ 1 :=
    ((hρlim.const_mul (4 * E ^ 2)).const_mul (B + Cd)).eventually
      (eventually_le_nhds (by norm_num))
  filter_upwards [hρpos, hsmall_s, hsmall_mass, hsmall_support, hsmall_C1,
    eventually_gt_atTop (0 : ℕ)] with n hρ hsfloor hmass hsupp hC1 hn
  intro r hr δ q hρd hdmax hδlo hδhi hD
  let d := q - r
  have hd : 0 < d := hρ.trans_le hρd
  have hdc' : d ≤ dc := hdmax.trans (min_le_left _ _)
  have hdg' : d ≤ dg := hdmax.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hdb' : d ≤ db := hdmax.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hprefix, hT, hsep⟩ := hgeom r hr d hd hdg'
  have hs : 0 ≤ r - 2 * d := ha.le.trans hprefix
  have hδd : |δ| ≤ d := hδhi.trans
    ((mul_le_of_le_one_left hρ.le hE1).trans hρd)
  have hδκ : |δ| ≤ κ * d := hδhi.trans (by
    calc
      2 * E * ρ n ≤ κ * ρ n := mul_le_mul_of_nonneg_right hEκ hρ.le
      _ ≤ κ * d := mul_le_mul_of_nonneg_left hρd hκ.le)
  have hδpos : 0 < |δ| := (mul_pos hE.1 hρ).trans_le hδlo
  obtain ⟨hgapN, hderiv⟩ := hgap r hr d δ hd hdc' hδpos hδκ
  let σ := S * ρ n
  let γ := fun t => max (α t) (3 * σ)
  have hσ : 0 < σ := mul_pos hS.1 hρ
  obtain ⟨hcost, heq, hdist⟩ := hfl σ ⟨hσ, hsfloor⟩
  have hγ : ∀ t, γ t ∈ Icc (0 : ℝ) 1 := by
    intro t
    exact ⟨(hα t).1.trans (le_max_left _ _), max_le (hα t).2 hmass⟩
  have hγmass : ∀ t, γ t ∈ Icc (3 * σ) 1 := by
    intro t
    exact ⟨le_max_right _ _, (hγ t).2⟩
  have hγm : Monotone γ := hαm.max monotone_const
  have heq_window : ∀ t ∈ Icc (r - 2 * d) 1, γ t = α t := by
    intro t ht
    exact heq t (hsupp.trans (hprefix.trans ht.1))
  have hratio := band_ratio_le hρ hE.1 hρd hδhi
  have hsmall : B * δ ^ 2 / d + Cd * δ ^ 2 / d ≤ 1 := by
    calc
      _ = (B + Cd) * (δ ^ 2 / d) := by ring
      _ ≤ (B + Cd) * (4 * E ^ 2 * ρ n) :=
        mul_le_mul_of_nonneg_left hratio (add_nonneg hB hCd)
      _ ≤ 1 := hC1
  let R : ℝ := Cr * ((B + Cd) * δ ^ 2 / d) * (Cf * σ ^ 2)
  have hfixed : ∀ᶠ M : ℕ in atTop,
      fractionalPressure n 3 β σ (tripleGram r δ q) ≤
        3 * finiteParisiInf β - gc * δ ^ 2 * d +
          (OW.trialValue β γ α r d 0 M - OW.trialValue β α α r d 0 M) + R := by
    filter_upwards [hgapN, eventually_gt_atTop (0 : ℕ)] with M hMgap hM
    obtain ⟨hFK, hFH, hV⟩ := hbd r hr d δ hd hdb' hδd M hM
    have htransfer := trialValue_floor_transfer hα hαm hγ hγm hCr
      (hrsp α γ hα hαm hγ hγm) hd hs hT hFK hFH
      (by positivity : 0 ≤ B * δ ^ 2 / d) (by positivity : 0 ≤ Cd * δ ^ 2 / d)
      hsmall hV (hderiv M hM) hdist
    have hk : |δ / (2 * d)| ≤ (1 / 2 : ℝ) := by
      rw [abs_div, abs_of_pos (by positivity : 0 < 2 * d)]
      apply (div_le_iff₀ (by positivity : 0 < 2 * d)).mpr
      linarith
    have hD' : Nonempty (MatrixStates n 3 (tripleGram r δ (r + d))) := by
      simpa only [d, add_sub_cancel] using hD
    have htrial := OW.fractionalPressure_le_trialValue hn hM β σ hσ γ α hγmass hγm
      hα hαm r d δ hd hs hT hk hsep heq_window hD'
    have hq : r + d = q := by dsimp only [d]; ring
    rw [hq] at htrial
    have hR : Cr * (B * δ ^ 2 / d + Cd * δ ^ 2 / d) * (Cf * σ ^ 2) = R := by
      dsimp only [R]
      ring
    rw [hR] at htransfer
    linarith
  have hlimγ := hbaseline γ hγ hγm r d hd hs hT heq_window
  have hlimα := hbaseline α hα hαm r d hd hs hT (fun _ _ => rfl)
  have hlim := (((hlimγ.sub hlimα).const_add
    (3 * finiteParisiInf β - gc * δ ^ 2 * d)).add_const R)
  have hpressure := ge_of_tendsto hlim hfixed
  rw [hmin] at hpressure
  have hcost' : scalarCDFParisi β γ - finiteParisiInf β ≤ Cf * σ ^ (3 : ℕ) := by
    simpa only [Real.rpow_ofNat] using hcost
  have hRbound : R ≤ 4 * Cr * Cf * (B + Cd) * E ^ 2 * S ^ 2 * ρ n ^ 3 := by
    calc
      R = Cr * (B + Cd) * (δ ^ 2 / d) * (Cf * σ ^ 2) := by dsimp only [R]; ring
      _ ≤ Cr * (B + Cd) * (4 * E ^ 2 * ρ n) * (Cf * σ ^ 2) := by
        gcongr
      _ = _ := by dsimp only [σ]; ring
  have hgain := mul_le_mul_of_nonneg_left (band_gain_le hρ hE.1 hρd hδlo) hgc.le
  change gc * (E ^ 2 * ρ n ^ 3) ≤ gc * (δ ^ 2 * d) at hgain
  have hmargin' := mul_le_mul_of_nonneg_right hmargin.le (show 0 ≤ ρ n ^ 3 by positivity)
  have hcostscale : σ ^ (3 : ℕ) = S ^ 3 * ρ n ^ 3 := by dsimp only [σ]; ring
  rw [hcostscale] at hcost'
  change fractionalPressure n 3 β σ (tripleGram r δ q) ≤ _
  nlinarith only [hpressure, hcost', hRbound, hgain, hmargin']

end SKBarriers2
