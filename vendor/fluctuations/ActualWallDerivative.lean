module

public import ActualWallMinimum
public import WallSweepIntegration

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal

def wallMatrixVelocity (T ε s u : ℝ) : ℝ :=
  if u < s then -wallLowStrength T ε else 0

def wallFieldVelocity (T ε s τ d rmin u : ℝ) : ℝ :=
  if u < s then wallLowStrength T ε*wallLowRadius d rmin ε*wallPsi s τ u else 0

theorem wallMatrixVelocity_intervalIntegrable (T ε : ℝ) {s : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) :
    IntervalIntegrable (wallMatrixVelocity T ε s) volume 0 1 := by
  have ha : IntervalIntegrable (wallMatrixVelocity T ε s) volume 0 s := by
    apply (intervalIntegrable_const (c := -wallLowStrength T ε)).congr_uIoo
    intro u hu
    rw [uIoo_of_le hs.le] at hu
    simp [wallMatrixVelocity, hu.2]
  have hb : IntervalIntegrable (wallMatrixVelocity T ε s) volume s 1 := by
    apply (intervalIntegrable_const (c := (0 : ℝ))).congr_uIoo
    intro u hu
    rw [uIoo_of_le hs1] at hu
    simp [wallMatrixVelocity, not_lt.mpr hu.1.le]
  exact ha.trans hb

theorem wallFieldVelocity_intervalIntegrable (T ε d rmin : ℝ) {s τ : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hτ : 0 < τ) :
    IntervalIntegrable (wallFieldVelocity T ε s τ d rmin) volume 0 1 := by
  have ha : IntervalIntegrable (wallFieldVelocity T ε s τ d rmin) volume 0 s := by
    have hcont : ContinuousOn (fun u => wallLowStrength T ε*wallLowRadius d rmin ε*wallPsi s τ u) (uIcc 0 s) := by
      simpa only [uIcc_of_le hs.le] using (wallPsi_continuousOn hs hτ).const_mul
        (wallLowStrength T ε*wallLowRadius d rmin ε)
    apply hcont.intervalIntegrable.congr_uIoo
    intro u hu
    rw [uIoo_of_le hs.le] at hu
    simp [wallFieldVelocity, hu.2]
  have hb : IntervalIntegrable (wallFieldVelocity T ε s τ d rmin) volume s 1 := by
    apply (intervalIntegrable_const (c := (0 : ℝ))).congr_uIoo
    intro u hu
    rw [uIoo_of_le hs1] at hu
    simp [wallFieldVelocity, not_lt.mpr hu.1.le]
  exact ha.trans hb

theorem integral_below_wall {f : ℝ → ℝ} {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (hf : IntervalIntegrable f volume 0 s) :
    (∫ u in (0 : ℝ)..1, if u < s then f u else 0) = ∫ u in (0 : ℝ)..s, f u := by
  have ha : IntervalIntegrable (fun u => if u < s then f u else 0) volume 0 s := by
    apply hf.congr_uIoo
    intro u hu
    rw [uIoo_of_le hs.le] at hu
    simp [hu.2]
  have hb : IntervalIntegrable (fun u => if u < s then f u else 0) volume s 1 := by
    apply (intervalIntegrable_const (c := (0 : ℝ))).congr_uIoo
    intro u hu
    rw [uIoo_of_le hs1] at hu
    simp [not_lt.mpr hu.1.le]
  rw [← intervalIntegral.integral_add_adjacent_intervals ha hb]
  have heq : (∫ u in (0 : ℝ)..s, if u < s then f u else 0) = ∫ u in (0 : ℝ)..s, f u := by
    apply intervalIntegral.integral_congr_Ioo_of_le hs.le
    intro u hu
    simp [hu.2]
  rw [heq]
  have hzero : (∫ u in s..1, if u < s then f u else 0) = 0 := by
    calc
      _ = ∫ _u in s..1, (0 : ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le hs1
        intro u hu
        simp [not_lt.mpr hu.1.le]
      _ = 0 := by simp
  simp only [hzero, add_zero]

theorem wallPsi_pair_intervalIntegrable (n : ℕ) (hn : 0 < n)
    (b h : ℝ → ℝ≥0) (hb : MonotoneOn b (Icc (0 : ℝ) 1))
    (hh : MonotoneOn h (Icc (0 : ℝ) 1)) (P : Spin n → Spin n → ℝ)
    {s τ : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (hτ : 0 < τ) :
    IntervalIntegrable (fun u => wallPsi s τ u * orderedPathPair n b h P u) volume 0 s := by
  let p : C(Icc (0 : ℝ) s, ℝ) :=
    ⟨fun u => wallPsi s τ u, (wallPsi_continuousOn hs hτ).domRestrict⟩
  have hp : Continuous (IccExtend hs.le p) := p.continuous.Icc_extend'
  have hi := orderedPathPair_mul_integrable n hn b h hb hh P
    (IccExtend hs.le p) (hp.intervalIntegrable 0 1)
  have hi' : IntervalIntegrable (fun u => IccExtend hs.le p u * orderedPathPair n b h P u)
      volume 0 s := hi.mono_set (by
    rw [uIcc_of_le hs.le, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_subset_Icc le_rfl hs1)
  apply hi'.congr
  intro u hu
  have hu' : u ∈ Icc (0 : ℝ) s := by
    rw [uIoc_of_le hs.le] at hu
    exact ⟨hu.1.le, hu.2⟩
  dsimp only
  rw [IccExtend_of_mem hs.le p hu']
  rfl

section
variable {rmin s c : ℝ} {k M : ℝ → ℝ}
variable (hr : rmin ≤ 1) (hs1 : s ≤ 1) (hc : 0 < c)
variable (hk : ContinuousOn k (Icc rmin 1))
variable (hkc : ∀ t ∈ Icc rmin 1, c ≤ k t)
variable (hm : MonotoneOn M (Icc (0 : ℝ) 1)) (hM : 0 ≤ M 1)
variable (g : ℝ → ℝ) (hg : Continuous g)

def wallPressureDerivative (T ε θ τ d : ℝ) (n : ℕ)
    (α : inverseIntegralConstraints rmin s k M) : ℝ :=
  -(1/4 : ℝ) * (∫ u in (0 : ℝ)..1,
    wallMatrixVelocity T ε s u * orderedPathB n
      (fun v => (wallChangedMatrix hr hs1 hc hk hkc hm hM g hg T ε θ α v).toNNReal)
      (fun v => (wallChangedField hr hs1 hc hk hkc hm hM g hg T ε θ τ d α v).toNNReal) u) -
  (1/2 : ℝ) * (∫ u in (0 : ℝ)..1,
    wallFieldVelocity T ε s τ d rmin u * orderedPathS n
      (fun v => (wallChangedMatrix hr hs1 hc hk hkc hm hM g hg T ε θ α v).toNNReal)
      (fun v => (wallChangedField hr hs1 hc hk hkc hm hM g hg T ε θ τ d α v).toNNReal) u)

theorem wallPressure_hasDerivAt_shift {T ε θ τ d : ℝ}
    (hs : 0 < s) (hτ : 0 < τ) (hrmin : 0 ≤ rmin)
    (hε : ε ∈ Ioo 0 T) (hθ : θ ∈ Ioo (0 : ℝ) 1)
    (hdepsilon : d^2 ≤ ε) (hginitial : g rmin = d^2)
    (hganti : AntitoneOn g (Icc rmin 1))
    (hgrmono : MonotoneOn (fun r => g r*r) (Icc rmin 1))
    (hgbound : ∀ r ∈ Icc rmin 1, g r ≤ d^2)
    (n : ℕ) (hn : 0 < n) (α : inverseIntegralConstraints rmin s k M) :
    HasDerivAt (fun t => realOrderedSKPathPressure n
      (wallChangedMatrix hr hs1 hc hk hkc hm hM g hg T ε (θ+t) α)
      (wallChangedField hr hs1 hc hk hkc hm hM g hg T ε (θ+t) τ d α) 0)
      (wallPressureDerivative hr hs1 hc hk hkc hm hM g hg T ε θ τ d n α) 0 := by
  have ha := wall_changed_clocks_admissible hr hs1 hc hk hkc hm hM g hg
    hs hτ hrmin hε ⟨hθ.1.le, hθ.2.le⟩ hdepsilon hginitial hganti hgrmono hgbound α
  have hevent : ∀ᶠ t : ℝ in 𝓝 0, θ+t ∈ Icc (0 : ℝ) 1 := by
    have ht : Tendsto (fun t : ℝ => θ+t) (𝓝 0) (𝓝 θ) := by
      simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℝ => θ) (𝓝 0) (𝓝 θ)).add
        (tendsto_id : Tendsto (fun t : ℝ => t) (𝓝 0) (𝓝 0)))
    filter_upwards [ht.eventually (Ioo_mem_nhds hθ.1 hθ.2)] with t ht
    exact ⟨ht.1.le, ht.2.le⟩
  have hevent' := hevent.filter_mono
    (show 𝓝[(Set.univ : Set ℝ) \ {0}] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have hadm := hevent'.mono fun t ht =>
    wall_changed_clocks_admissible hr hs1 hc hk hkc hm hM g hg
      hs hτ hrmin hε ht hdepsilon hginitial hganti hgrmono hgbound α
  have hb0n : ∀ u ∈ Icc (0 : ℝ) 1,
      0 ≤ wallChangedMatrix hr hs1 hc hk hkc hm hM g hg T ε θ α u := by
    intro u hu
    exact ha.2.2.1.trans (ha.1 (by norm_num) hu hu.1)
  have hh0n : ∀ u ∈ Icc (0 : ℝ) 1,
      0 ≤ wallChangedField hr hs1 hc hk hkc hm hM g hg T ε θ τ d α u := by
    intro u hu
    exact ha.2.2.2.trans (ha.2.1 (by norm_num) hu hu.1)
  have hd := realOrderedSKPathPressure_hasDerivWithinAt_curve n hn
    (fun t => wallChangedMatrix hr hs1 hc hk hkc hm hM g hg T ε (θ+t) α)
    (fun t => wallChangedField hr hs1 hc hk hkc hm hM g hg T ε (θ+t) τ d α)
    (wallMatrixVelocity T ε s) (wallFieldVelocity T ε s τ d rmin)
    (wallLowStrength T ε) (wallLowStrength T ε*wallLowRadius d rmin ε) Set.univ
    (by simpa using ha.1) (by simpa using ha.2.1)
    (by simpa using hb0n) (by simpa using hh0n)
    (hadm.mono fun _ ht => ht.1) (hadm.mono fun _ ht => ht.2.1)
    (hadm.mono fun _ ht => by
      intro u hu
      exact ht.2.2.1.trans (ht.1 (by norm_num) hu hu.1))
    (hadm.mono fun _ ht => by
      intro u hu
      exact ht.2.2.2.trans (ht.2.1 (by norm_num) hu hu.1))
    (Filter.Eventually.of_forall fun t u _ => by
      simpa using wallChangedMatrix_theta_bound hr hs1 hc hk hkc hm hM g hg
        (θ := θ+t) (θ' := θ) hε α u)
    (Filter.Eventually.of_forall fun t u hu => by
      simpa [mul_assoc] using wallChangedField_theta_bound hr hs1 hc hk hkc hm hM g hg
        (θ := θ+t) (θ' := θ) hε hs hτ hrmin α hu)
    (wallMatrixVelocity_intervalIntegrable T ε hs hs1)
    (wallFieldVelocity_intervalIntegrable T ε d rmin hs hs1 hτ)
    (Filter.Eventually.of_forall fun u _ => by
      by_cases hus : u < s
      · simp only [wallChangedMatrix, wallBareMatrix, ite_eq_left hus, wallMatrixVelocity]
        simpa only [ite_eq_left hus, one_mul, id_eq] using
          (((hasDerivAt_id (0 : ℝ)).const_add θ).mul_const (wallLowStrength T ε)).const_sub
            (T-ε) |>.sub_const
              (wallHighCoefficient hr hs1 hc hk hkc hm hM g hg α u) |>.hasDerivWithinAt
      · simp only [wallChangedMatrix, wallBareMatrix, ite_eq_right hus, wallMatrixVelocity]
        simpa only [ite_eq_right hus] using
          (hasDerivAt_const (0 : ℝ)
            (T-wallHighCoefficient hr hs1 hc hk hkc hm hM g hg α u)).hasDerivWithinAt)
    (Filter.Eventually.of_forall fun u _ => by
      by_cases hus : u < s
      · simp only [wallChangedField, wallBareField, ite_eq_left hus, wallFieldVelocity]
        simpa only [ite_eq_left hus, one_mul, id_eq] using
          (((((hasDerivAt_id (0 : ℝ)).const_add θ).mul_const
            (wallLowStrength T ε)).mul_const (wallLowRadius d rmin ε)).mul_const
            (wallPsi s τ u)).add_const
              (wallHighCoefficient hr hs1 hc hk hkc hm hM (fun r => g r*r)
                (hg.mul continuous_id) α u) |>.hasDerivWithinAt
      · simp only [wallChangedField, wallBareField, ite_eq_right hus, zero_add, wallFieldVelocity]
        simpa only [ite_eq_right hus] using
          (hasDerivAt_const (0 : ℝ)
            (wallHighCoefficient hr hs1 hc hk hkc hm hM (fun r => g r*r)
              (hg.mul continuous_id) α u)).hasDerivWithinAt)
  simpa only [hasDerivWithinAt_univ, add_zero, wallPressureDerivative] using hd

theorem wallPressure_hasDerivAt {T ε θ τ d : ℝ}
    (hs : 0 < s) (hτ : 0 < τ) (hrmin : 0 ≤ rmin)
    (hε : ε ∈ Ioo 0 T) (hθ : θ ∈ Ioo (0 : ℝ) 1)
    (hdepsilon : d^2 ≤ ε) (hginitial : g rmin = d^2)
    (hganti : AntitoneOn g (Icc rmin 1))
    (hgrmono : MonotoneOn (fun r => g r*r) (Icc rmin 1))
    (hgbound : ∀ r ∈ Icc rmin 1, g r ≤ d^2)
    (n : ℕ) (hn : 0 < n) (α : inverseIntegralConstraints rmin s k M) :
    HasDerivAt (fun t => realOrderedSKPathPressure n
      (wallChangedMatrix hr hs1 hc hk hkc hm hM g hg T ε t α)
      (wallChangedField hr hs1 hc hk hkc hm hM g hg T ε t τ d α) 0)
      (wallPressureDerivative hr hs1 hc hk hkc hm hM g hg T ε θ τ d n α) θ := by
  have hd := wallPressure_hasDerivAt_shift hr hs1 hc hk hkc hm hM g hg
    hs hτ hrmin hε hθ hdepsilon hginitial hganti hgrmono hgbound n hn α
  have hd' : HasDerivAt (fun t => realOrderedSKPathPressure n
      (wallChangedMatrix hr hs1 hc hk hkc hm hM g hg T ε (θ+t) α)
      (wallChangedField hr hs1 hc hk hkc hm hM g hg T ε (θ+t) τ d α) 0)
      (wallPressureDerivative hr hs1 hc hk hkc hm hM g hg T ε θ τ d n α) (θ-θ) := by
    simpa only [sub_self] using hd
  simpa only [← add_sub_assoc, add_sub_cancel_left] using hd'.comp_sub_const θ θ

def wallObjectiveDerivative (T ε θ τ d : ℝ) (n : ℕ)
    (α : inverseIntegralConstraints rmin s k M) : ℝ :=
  wallPressureDerivative hr hs1 hc hk hkc hm hM g hg T ε θ τ d n α +
    wallLowStrength T ε/4 *
      (∫ u in (0 : ℝ)..s, (wallLowRadius d rmin ε)^2*(wallPsi s τ u)^2)

theorem wallObjective_hasDerivAt {T ε θ τ d : ℝ}
    (hs : 0 < s) (hτ : 0 < τ) (hrmin : 0 ≤ rmin)
    (hε : ε ∈ Ioo 0 T) (hθ : θ ∈ Ioo (0 : ℝ) 1)
    (hdepsilon : d^2 ≤ ε) (hginitial : g rmin = d^2)
    (hganti : AntitoneOn g (Icc rmin 1))
    (hgrmono : MonotoneOn (fun r => g r*r) (Icc rmin 1))
    (hgbound : ∀ r ∈ Icc rmin 1, g r ≤ d^2)
    (n : ℕ) (hn : 0 < n) (α : inverseIntegralConstraints rmin s k M) :
    HasDerivAt (fun t => wallObjective hr hs1 hc hk hkc hm hM g hg T ε t τ d n 0 α)
      (wallObjectiveDerivative hr hs1 hc hk hkc hm hM g hg T ε θ τ d n α) θ := by
  have hd := wallPressure_hasDerivAt hr hs1 hc hk hkc hm hM g hg
    hs hτ hrmin hε hθ hdepsilon hginitial hganti hgrmono hgbound n hn α
  convert (hd.add_const ((1/4 : ℝ) * (∫ u in (0 : ℝ)..1,
      wallHighCoefficient hr hs1 hc hk hkc hm hM
        (fun r => g r*r^2) (hg.mul (continuous_id.pow 2)) α u))).add
    ((hasDerivAt_id θ).mul_const (wallLowStrength T ε/4 *
      (∫ u in (0 : ℝ)..s, (wallLowRadius d rmin ε)^2*(wallPsi s τ u)^2))) using 1
  · funext t
    rw [wallObjective_eq hr hs1 hc hk hkc hm hM g hg]
    dsimp only [Pi.add_apply, id_eq]
    ring
  · simp [wallObjectiveDerivative]

theorem wallObjectiveDerivative_eq_low_loss {T ε θ τ d : ℝ}
    (hs : 0 < s) (hτ : 0 < τ) (hrmin : 0 ≤ rmin)
    (hε : ε ∈ Ioo 0 T) (hθ : θ ∈ Icc (0 : ℝ) 1)
    (hdepsilon : d^2 ≤ ε) (hginitial : g rmin = d^2)
    (hganti : AntitoneOn g (Icc rmin 1))
    (hgrmono : MonotoneOn (fun r => g r*r) (Icc rmin 1))
    (hgbound : ∀ r ∈ Icc rmin 1, g r ≤ d^2)
    (n : ℕ) (hn : 0 < n) (α : inverseIntegralConstraints rmin s k M) :
    wallObjectiveDerivative hr hs1 hc hk hkc hm hM g hg T ε θ τ d n α =
      wallLowStrength T ε/4 * (∫ u in (0 : ℝ)..s,
        orderedPathB n
          (fun v => (wallChangedMatrix hr hs1 hc hk hkc hm hM g hg T ε θ α v).toNNReal)
          (fun v => (wallChangedField hr hs1 hc hk hkc hm hM g hg T ε θ τ d α v).toNNReal) u -
        2*wallLowRadius d rmin ε*wallPsi s τ u*orderedPathS n
          (fun v => (wallChangedMatrix hr hs1 hc hk hkc hm hM g hg T ε θ α v).toNNReal)
          (fun v => (wallChangedField hr hs1 hc hk hkc hm hM g hg T ε θ τ d α v).toNNReal) u +
        (wallLowRadius d rmin ε)^2*(wallPsi s τ u)^2) := by
  let b := fun v => (wallChangedMatrix hr hs1 hc hk hkc hm hM g hg T ε θ α v).toNNReal
  let h := fun v => (wallChangedField hr hs1 hc hk hkc hm hM g hg T ε θ τ d α v).toNNReal
  have ha := wall_changed_clocks_admissible hr hs1 hc hk hkc hm hM g hg
    hs hτ hrmin hε hθ hdepsilon hginitial hganti hgrmono hgbound α
  have hb : MonotoneOn b (Icc (0 : ℝ) 1) :=
    fun u hu v hv huv => Real.toNNReal_mono (ha.1 hu hv huv)
  have hh : MonotoneOn h (Icc (0 : ℝ) 1) :=
    fun u hu v hv huv => Real.toNNReal_mono (ha.2.1 hu hv huv)
  have hsub : uIcc (0 : ℝ) s ⊆ uIcc (0 : ℝ) 1 := by
    rw [uIcc_of_le hs.le, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_subset_Icc le_rfl hs1
  have hiB : IntervalIntegrable (orderedPathB n b h) volume 0 s := by
    have hi := orderedPathPair_mul_integrable n hn b h hb hh
      (fun σ ρ => (orderedOverlap n σ ρ)^2) (fun _ => 1) intervalIntegrable_const
    simpa only [one_mul, orderedPathB] using hi.mono_set hsub
  have hiS : IntervalIntegrable (fun u => wallPsi s τ u*orderedPathS n b h u) volume 0 s :=
    wallPsi_pair_intervalIntegrable n hn b h hb hh (orderedOverlap n) hs hs1 hτ
  have hip : IntervalIntegrable
      (fun u => (wallLowRadius d rmin ε)^2*(wallPsi s τ u)^2) volume 0 s := by
    have hcpsi : ContinuousOn (wallPsi s τ) (uIcc (0 : ℝ) s) := by
      simpa only [uIcc_of_le hs.le] using wallPsi_continuousOn hs hτ
    exact ((hcpsi.pow 2).const_mul _).intervalIntegrable
  have hmB : (∫ u in (0 : ℝ)..1, wallMatrixVelocity T ε s u*orderedPathB n b h u) =
      -wallLowStrength T ε*(∫ u in (0 : ℝ)..s, orderedPathB n b h u) := by
    have heq : (fun u => wallMatrixVelocity T ε s u*orderedPathB n b h u) =
        fun u => if u < s then -wallLowStrength T ε*orderedPathB n b h u else 0 := by
      funext u
      by_cases hu : u < s <;> simp [wallMatrixVelocity, hu]
    rw [heq, integral_below_wall hs hs1 (hiB.const_mul _), intervalIntegral.integral_const_mul]
  have hmS : (∫ u in (0 : ℝ)..1, wallFieldVelocity T ε s τ d rmin u*orderedPathS n b h u) =
      wallLowStrength T ε*wallLowRadius d rmin ε*
        (∫ u in (0 : ℝ)..s, wallPsi s τ u*orderedPathS n b h u) := by
    have heq : (fun u => wallFieldVelocity T ε s τ d rmin u*orderedPathS n b h u) =
        fun u => if u < s then wallLowStrength T ε*wallLowRadius d rmin ε*
          (wallPsi s τ u*orderedPathS n b h u) else 0 := by
      funext u
      by_cases hu : u < s <;> simp [wallFieldVelocity, hu, mul_assoc]
    rw [heq, integral_below_wall hs hs1 (hiS.const_mul _), intervalIntegral.integral_const_mul]
  change -(1/4 : ℝ)*(∫ u in (0 : ℝ)..1, wallMatrixVelocity T ε s u*orderedPathB n b h u)-
    (1/2 : ℝ)*(∫ u in (0 : ℝ)..1, wallFieldVelocity T ε s τ d rmin u*orderedPathS n b h u)+
    wallLowStrength T ε/4*(∫ u in (0 : ℝ)..s,
      (wallLowRadius d rmin ε)^2*(wallPsi s τ u)^2) = _
  rw [hmB, hmS]
  have his : IntervalIntegrable
      (fun u => 2*wallLowRadius d rmin ε*wallPsi s τ u*orderedPathS n b h u) volume 0 s := by
    simpa only [mul_assoc] using hiS.const_mul (2*wallLowRadius d rmin ε)
  rw [intervalIntegral.integral_add (hiB.sub his) hip,
    intervalIntegral.integral_sub hiB his]
  have heq : (fun u => 2*wallLowRadius d rmin ε*wallPsi s τ u*orderedPathS n b h u) =
      fun u => (2*wallLowRadius d rmin ε)*(wallPsi s τ u*orderedPathS n b h u) := by
    funext u
    ring
  rw [heq]
  simp_rw [intervalIntegral.integral_const_mul]
  ring

theorem wallLowPenalty_le_mass {s τ d rmin ε : ℝ}
    (hs : 0 < s) (hτ : 0 < τ) :
    (∫ u in (0 : ℝ)..s, (wallLowRadius d rmin ε)^2*(wallPsi s τ u)^2) ≤
      s*(wallLowRadius d rmin ε)^2 := by
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := s) (C := (wallLowRadius d rmin ε)^2)
    (f := fun u => (wallLowRadius d rmin ε)^2*(wallPsi s τ u)^2) (fun u hu => by
      have hu' : u ∈ Ioc (0 : ℝ) s := by simpa only [uIoc_of_le hs.le] using hu
      have hp := wallPsi_mem hs hτ ⟨hu'.1.le, hu'.2⟩
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
      apply mul_le_of_le_one_right (sq_nonneg _)
      nlinarith [hp.1, hp.2])
  rw [Real.norm_eq_abs, sub_zero, abs_of_pos hs] at hh
  exact (le_abs_self _).trans (hh.trans_eq (mul_comm _ _))

theorem wallObjectiveDerivative_le_low_cost {T ε θ τ d C : ℝ}
    (hs : 0 < s) (hτ : 0 < τ) (hrmin : 0 ≤ rmin)
    (hε : ε ∈ Ioo 0 T) (hθ : θ ∈ Icc (0 : ℝ) 1)
    (hdepsilon : d^2 ≤ ε) (hginitial : g rmin = d^2)
    (hganti : AntitoneOn g (Icc rmin 1))
    (hgrmono : MonotoneOn (fun r => g r*r) (Icc rmin 1))
    (hgbound : ∀ r ∈ Icc rmin 1, g r ≤ d^2)
    (n : ℕ) (hn : 0 < n) (α : inverseIntegralConstraints rmin s k M)
    (hcost : (∫ u in (0 : ℝ)..s, orderedPathB n
      (fun v => (wallChangedMatrix hr hs1 hc hk hkc hm hM g hg T ε θ α v).toNNReal)
      (fun v => (wallChangedField hr hs1 hc hk hkc hm hM g hg T ε θ τ d α v).toNNReal) u) ≤ C) :
    wallObjectiveDerivative hr hs1 hc hk hkc hm hM g hg T ε θ τ d n α ≤
      wallLowStrength T ε/4*(C+s*(wallLowRadius d rmin ε)^2) := by
  let b := fun v => (wallChangedMatrix hr hs1 hc hk hkc hm hM g hg T ε θ α v).toNNReal
  let h := fun v => (wallChangedField hr hs1 hc hk hkc hm hM g hg T ε θ τ d α v).toNNReal
  have ha := wall_changed_clocks_admissible hr hs1 hc hk hkc hm hM g hg
    hs hτ hrmin hε hθ hdepsilon hginitial hganti hgrmono hgbound α
  have hb : MonotoneOn b (Icc (0 : ℝ) 1) :=
    fun u hu v hv huv => Real.toNNReal_mono (ha.1 hu hv huv)
  have hh : MonotoneOn h (Icc (0 : ℝ) 1) :=
    fun u hu v hv huv => Real.toNNReal_mono (ha.2.1 hu hv huv)
  have hsub : uIcc (0 : ℝ) s ⊆ uIcc (0 : ℝ) 1 := by
    rw [uIcc_of_le hs.le, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_subset_Icc le_rfl hs1
  have hiB : IntervalIntegrable (orderedPathB n b h) volume 0 s := by
    have hi := orderedPathPair_mul_integrable n hn b h hb hh
      (fun σ ρ => (orderedOverlap n σ ρ)^2) (fun _ => 1) intervalIntegrable_const
    simpa only [one_mul, orderedPathB] using hi.mono_set hsub
  have hiS : IntervalIntegrable (fun u => wallPsi s τ u*orderedPathS n b h u) volume 0 s :=
    wallPsi_pair_intervalIntegrable n hn b h hb hh (orderedOverlap n) hs hs1 hτ
  have hip : IntervalIntegrable
      (fun u => (wallLowRadius d rmin ε)^2*(wallPsi s τ u)^2) volume 0 s := by
    have hcpsi : ContinuousOn (wallPsi s τ) (uIcc (0 : ℝ) s) := by
      simpa only [uIcc_of_le hs.le] using wallPsi_continuousOn hs hτ
    exact ((hcpsi.pow 2).const_mul _).intervalIntegrable
  have hiS0 : 0 ≤ ∫ u in (0 : ℝ)..s, wallPsi s τ u*orderedPathS n b h u := by
    apply intervalIntegral.integral_nonneg_of_ae_restrict hs.le
    change ∀ᵐ u ∂volume.restrict (Icc (0 : ℝ) s), 0 ≤ wallPsi s τ u*orderedPathS n b h u
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [show ∀ᵐ u : ℝ, u ≠ 0 from by simp [ae_iff]] with u hune hu
    have hui : u ∈ Ioc (0 : ℝ) 1 :=
      ⟨lt_of_le_of_ne hu.1 (Ne.symm hune), hu.2.trans hs1⟩
    exact mul_nonneg (wallPsi_mem hs hτ hu).1 (orderedPath_SK_bounds n hn b h hb hh hui).1
  have hr0 : 0 ≤ wallLowRadius d rmin ε :=
    div_nonneg (mul_nonneg (sq_nonneg d) hrmin) (by linarith [hε.1])
  have hc0 := (wallLowStrength_bounds hε).1
  rw [wallObjectiveDerivative_eq_low_loss hr hs1 hc hk hkc hm hM g hg
    hs hτ hrmin hε hθ hdepsilon hginitial hganti hgrmono hgbound n hn α]
  change wallLowStrength T ε/4*(∫ u in (0 : ℝ)..s,
    orderedPathB n b h u-2*wallLowRadius d rmin ε*wallPsi s τ u*orderedPathS n b h u+
      (wallLowRadius d rmin ε)^2*(wallPsi s τ u)^2) ≤ _
  have his : IntervalIntegrable
      (fun u => 2*wallLowRadius d rmin ε*wallPsi s τ u*orderedPathS n b h u) volume 0 s := by
    simpa only [mul_assoc] using hiS.const_mul (2*wallLowRadius d rmin ε)
  rw [intervalIntegral.integral_add (hiB.sub his) hip,
    intervalIntegral.integral_sub hiB his]
  have heq : (fun u => 2*wallLowRadius d rmin ε*wallPsi s τ u*orderedPathS n b h u) =
      fun u => (2*wallLowRadius d rmin ε)*(wallPsi s τ u*orderedPathS n b h u) := by
    funext u
    ring
  rw [heq, intervalIntegral.integral_const_mul]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hpen := wallLowPenalty_le_mass (d := d) (rmin := rmin) (ε := ε) hs hτ
  dsimp only [b, h] at hiS0
  nlinarith [mul_nonneg hr0 hiS0]

theorem wallMinimumValue_sweep_logarithmic_bound {T ε τ d cutoff A B : ℝ}
    (hs : 0 < s) (hτ : 0 < τ) (hrmin : 0 ≤ rmin)
    (hε : ε ∈ Ioo 0 T) (hdepsilon : d^2 ≤ ε) (hginitial : g rmin = d^2)
    (hganti : AntitoneOn g (Icc rmin 1))
    (hgrmono : MonotoneOn (fun r => g r*r) (Icc rmin 1))
    (hgbound : ∀ r ∈ Icc rmin 1, g r ≤ d^2)
    (hMc : Continuous M) (hne : (inverseIntegralConstraints rmin s k M).Nonempty)
    (n : ℕ) (hn : 0 < n) (hcutoff : 0 < cutoff) (hcutoff1 : cutoff ≤ 1) (hA : 0 ≤ A)
    (hcost : ∀ θ ∈ Ioo cutoff 1, ∀ α : inverseIntegralConstraints rmin s k M,
      wallObjective hr hs1 hc hk hkc hm hM g hg T ε θ τ d n 0 α =
        wallMinimumValue hr hs1 hc hk hkc hm hM g hg T ε τ d n 0 θ →
      wallObjectiveDerivative hr hs1 hc hk hkc hm hM g hg T ε θ τ d n α ≤ A+B*θ⁻¹) :
    wallMinimumValue hr hs1 hc hk hkc hm hM g hg T ε τ d n 0 1-
      wallMinimumValue hr hs1 hc hk hkc hm hM g hg T ε τ d n 0 0 ≤
      A+B*(-Real.log cutoff)+wallLipschitzConstant T ε d rmin*cutoff := by
  have hlip := wallMinimumValue_lipschitzOn hr hs1 hc hk hkc hm hM g hg
    hs hτ hrmin hε hdepsilon hginitial hganti hgrmono hgbound hMc hne n hn 0
  have hh := WallSweep.minimum_sweep_logarithmic_bound
    (fun θ α => wallObjective hr hs1 hc hk hkc hm hM g hg T ε θ τ d n 0 α)
    (wallMinimumValue hr hs1 hc hk hkc hm hM g hg T ε τ d n 0)
    hcutoff hcutoff1 hA
    (by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hlip) (by
      intro θ hθ
      have hθ0 : θ ∈ Ioo (0 : ℝ) 1 := ⟨hcutoff.trans hθ.1, hθ.2⟩
      obtain ⟨α, hα, hmin⟩ := wallMinimumValue_minimum hr hs1 hc hk hkc hm hM g hg
        hs hτ hrmin hε ⟨hθ0.1.le, hθ0.2.le⟩ hdepsilon hginitial hganti hgrmono
        hgbound hMc hne n hn 0
      refine ⟨α, hα, ?_, wallObjectiveDerivative hr hs1 hc hk hkc hm hM g hg T ε θ τ d n α,
        wallObjective_hasDerivAt hr hs1 hc hk hkc hm hM g hg
          hs hτ hrmin hε hθ0 hdepsilon hginitial hganti hgrmono hgbound n hn α,
        hcost θ hθ α hα⟩
      filter_upwards [Ioo_mem_nhds hθ0.1 hθ0.2] with t ht
      obtain ⟨β, hβ, hb⟩ := wallMinimumValue_minimum hr hs1 hc hk hkc hm hM g hg
        hs hτ hrmin hε ⟨ht.1.le, ht.2.le⟩ hdepsilon hginitial hganti hgrmono
        hgbound hMc hne n hn 0
      exact hb α)
  simpa only [Real.coe_toNNReal _ (wallLipschitzConstant_nonneg (d := d) hε hrmin)] using hh

end
end OAI.SKFluctuations.LaplaceWindowFormalization
