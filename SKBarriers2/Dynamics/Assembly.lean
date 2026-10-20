module

public import SKBarriers2.Dynamics.Banks
public import SKBarriers2.Dynamics.Count
public import SKBarriers2.Dynamics.Endpoint
public import OAI.Probability.SKBarriers.Dynamics.BankPool
public import OAI.Probability.SKBarriers.Dynamics.PathEndpoint
public import OAI.Probability.SKBarriers.Coverage.HighProbability

@[expose] public section

noncomputable section

open scoped BigOperators Topology
open Classical MeasureTheory ProbabilityTheory Filter Set
open OAI.SK OAI.SK.Analytic
open SKBarriers2.Dynamics

namespace SKBarriers2

structure AssemblyData where
  I : Set ℝ
  B : ℕ
  H : ℕ
  M : ℕ → ℕ
  L : ℕ → ℝ
  ρ : ℕ → ℝ
  η : ℕ → ℝ
  E : ℝ
  tLo : ℝ
  tHi : ℝ
  C : ℝ
  b : ℝ
  bPrime : ℝ
  qStar : ℝ
  S : ℕ → ℝ
  offset : ℕ → ℕ → ℝ
  width : ℕ → ℝ

namespace AssemblyData

def scales (D : AssemblyData) (n : ℕ) : AnchorScales :=
  ⟨D.tLo, D.tHi, D.C, D.b, D.bPrime, D.qStar, D.ρ n, D.E * D.ρ n,
    2 * D.η n, 2 / (n : ℝ), D.S n⟩

def p (D : AssemblyData) (n : ℕ) : ℕ := D.B * D.M n

def bad (D : AssemblyData) (n : ℕ) : Finset (ReplicaConfig n 3) :=
  forbiddenSet n D.I (D.ρ n) (D.E * D.ρ n) (D.η n) D.qStar D.b D.bPrime

def crossingError (D : AssemblyData) (n : ℕ) : ℝ :=
  ((clockAttemptCutoff n (D.L n) : ℝ) + 1) * (3 * Real.exp (-4 * D.L n))

end AssemblyData

structure AssemblyCoverage (β : ℝ) (D : AssemblyData) (c : ℕ → ℝ)
    (U : ℕ → (n : ℕ) → Set (Disorder n)) : Prop where
  nonneg : ∀ j, 0 ≤ c j
  measurable : ∀ j n, MeasurableSet (U j n)
  typical : ∀ j, Tendsto (fun n => (disorderLaw n).real (U j n)) atTop (𝓝 1)
  coverage : ∀ j n J, J ∈ U j n → ∀ E : Config n → Prop,
    (gibbsFiniteLaw β J).prob (fun x => E x ∧
      (gibbsFiniteLaw β J).prob (fun y => E y ∧ D.qStar ≤ |overlap x y|) <
        Real.exp (-c j * D.L n)) ≤ Real.exp (-(bankPrefix c j + 5) * D.L n)

structure AssemblyNumerics (D : AssemblyData) (c : ℕ → ℝ) (n : ℕ) : Prop where
  blocks_pos : 1 ≤ D.M n
  block_size : D.H + 2 ≤ D.B
  anchor : AnchorNumerics (D.scales n)
  b_pos : 0 < D.b
  cell_nonneg : 0 ≤ D.C
  gram_margin : D.C < D.b ^ 2 / 2
  packing_budget : ⌈2 / D.b ^ 2⌉₊ ≤ D.H
  center_band : ∀ t ∈ Icc D.tLo D.tHi, ∀ r,
    |r - t| ≤ (D.scales n).centerRadius → r ∈ D.I
  width_pos : 0 < D.width n
  range : ∀ i < D.p n, D.tLo ≤ D.offset n i ∧
    D.offset n i + D.width n ≤ D.tHi
  separation : ∀ i a, i < a → a < D.p n →
    D.S n ≤ D.offset n a - (D.offset n i + D.width n)
  marker_count : ((clockAttemptCutoff n (D.L n) : ℝ) + 1) *
    (2 * (D.scales n).T0 / D.width n) ^ D.M n < 1
  scale_large : 5 ≤ D.L n
  levels_budget : (D.p n : ℝ) ≤ Real.exp (D.L n)
  coverage_budget : (bankPrefix c D.B + 5) * D.L n ≤ Real.exp (D.L n)

def StaticEventBadMassLimitsStatement : Prop :=
  ∀ (β : ℝ), 1 < β → ∀ (D : AssemblyData) (c : ℕ → ℝ)
    (U : ℕ → (n : ℕ) → Set (Disorder n))
    (Q : (n : ℕ) → Set (Disorder n)) (qn : ℕ → ℝ),
    QuenchedStaticEvent β D.bad Q qn → AssemblyCoverage β D c U →
    (∀ᶠ n : ℕ in atTop, AssemblyNumerics D c n) →
    (∀ᶠ n : ℕ in atTop, qn n ≤ Real.exp (-(3 * bankPrefix c D.B + 20) * D.L n)) →
    Tendsto D.crossingError atTop (𝓝 0) →
    ∀ A κ : ℝ, (∀ᶠ n : ℕ in atTop, A * (n : ℝ) ^ κ ≤ D.L n) →
    ∀ τ : ℝ, 0 < τ → τ < (1 / 2 : ℝ) →
      Tendsto (OAI.SK.Strengthened.continuousBadMass β A κ τ) atTop (𝓝 1) ∧
      Tendsto (OAI.SK.Strengthened.discreteBadMass β A κ τ) atTop (𝓝 1)

private lemma signed_locking_bound {n : ℕ} (v x y : Config n) (h b η : ℝ)
    (hq : h ≤ overlap x y) (hx : |overlap v x| ≤ b) (hy : |overlap v y| ≤ b)
    (havoid : (![v, x, y] : ReplicaConfig n 3) ∉ signedLockingSetη n h b η) :
    |overlap v x - overlap v y| ≤ 2 * η := by
  by_contra H
  apply havoid
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq, hx, hy, lt_of_not_ge H⟩

private lemma magnitude_locking_bound {n : ℕ} (v x y : Config n) (h b η : ℝ)
    (hq : h ≤ |overlap x y|) (hx : |overlap v x| ≤ b) (hy : |overlap v y| ≤ b)
    (havoid : (![v, x, y] : ReplicaConfig n 3) ∉ signedLockingSetη n h b η)
    (havoid' : (![v, x, flip y] : ReplicaConfig n 3) ∉ signedLockingSetη n h b η) :
    abs (|overlap v x| - |overlap v y|) ≤ 2 * η := by
  by_cases hp : 0 ≤ overlap x y
  · exact (abs_abs_sub_abs_le_abs_sub _ _).trans
      (signed_locking_bound v x y h b η
        (by simpa only [abs_of_nonneg hp] using hq) hx hy havoid)
  · have H : |overlap v x - overlap v (flip y)| ≤ 2 * η :=
      signed_locking_bound v x (flip y) h b η
        (by simpa only [overlap_flip_right, abs_of_neg (lt_of_not_ge hp)] using hq)
        hx (by simpa only [overlap_flip_right, abs_neg] using hy) havoid'
    simpa only [overlap_flip_right, abs_neg] using
      (abs_abs_sub_abs_le_abs_sub _ _).trans H

private lemma narrow_mem_bad (D : AssemblyData) (n : ℕ) (v x w : Config n)
    (hc : (overlap v x + overlap v w) / 2 ∈ D.I)
    (hδlo : D.E * D.ρ n ≤ |(overlap v x - overlap v w) / 2|)
    (hδhi : |(overlap v x - overlap v w) / 2| ≤ 2 * (D.E * D.ρ n))
    (hgap : D.ρ n ≤ overlap w x - (overlap v x + overlap v w) / 2) :
    (![v, x, w] : ReplicaConfig n 3) ∈ D.bad n := by
  apply Finset.mem_union.mpr
  apply Or.inl
  apply Finset.mem_union.mpr
  apply Or.inl
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, hc, hδlo, hδhi, ?_⟩
  change (overlap v x + overlap v w) / 2 + D.ρ n ≤ overlap x w
  rw [overlap_comm x w]
  linarith only [hgap]

private def assemblyAnchorData (D : AssemblyData) {n : ℕ}
    (K : Fin (D.p n) → ℕ) (hK : ∀ j, 0 < K j)
    (z : BankIndex K → Config n) (x : ℕ → Config n) (m : ℕ) : AnchorData n where
  B := D.B
  H := D.H
  M := D.M n
  m := m
  scales := D.scales n
  pool := natBankPool K z
  fallback := natBankDefault K hK z
  x := x

private def assemblyBadVertex (D : AssemblyData) {n : ℕ}
    (K : Fin (D.p n) → ℕ) (z : BankIndex K → Config n) (x : Config n) : Prop :=
  bankCoverageBad K (blockPrior (D.p n) D.B) (D.C / 3) D.qStar z x ∨
    bankVertexBad (fun i : BankIndex K => i.1.val) (D.bad n) z x

private lemma pool_mem {n p : ℕ} (K : Fin p → ℕ) (z : BankIndex K → Config n)
    {i : ℕ} (hi : i < p) {v : Config n} (hv : v ∈ natBankPool K z i) :
    v ∈ orientedBankPool K z ⟨i, hi⟩ := by
  simpa only [natBankPool, dite_eq_left hi] using hv

private lemma vertex_narrow_avoid (D : AssemblyData) {n : ℕ}
    (K : Fin (D.p n) → ℕ) (z : BankIndex K → Config n)
    {i a : ℕ} (hia : i < a) (ha : a < D.p n) {v w x : Config n}
    (hv : v ∈ natBankPool K z i) (hw : w ∈ natBankPool K z a)
    (hx : ¬assemblyBadVertex D K z x) :
    (![v, x, w] : ReplicaConfig n 3) ∉ D.bad n := by
  have H := bank_pool_no_vertex K z (D.bad n) x (fun h => hx (Or.inr h))
    ⟨i, hia.trans ha⟩ ⟨a, ha⟩
    (fun he => (Nat.ne_of_lt hia) (congrArg Fin.val he))
    v w (pool_mem K z (hia.trans ha) hv) (pool_mem K z ha hw) (Equiv.swap 1 2)
  have he : ((![v, w, x] : ReplicaConfig n 3) ∘ Equiv.swap (1 : Fin 3) 2) =
      (![v, x, w] : ReplicaConfig n 3) := by
    funext j
    fin_cases j <;> simp [Equiv.swap_apply_def]
  rw [he] at H
  exact H

private theorem anchor_hypotheses_of_bank (D : AssemblyData) {n : ℕ}
    (hn : 0 < n) {c : ℕ → ℝ} (G : AssemblyNumerics D c n)
    (K : Fin (D.p n) → ℕ) (hK : ∀ j, 0 < K j) (z : BankIndex K → Config n)
    (hz : ¬bankTripleBad (fun i : BankIndex K => i.1.val) (D.bad n) z)
    (x : ℕ → Config n) (m : ℕ)
    (hjump : ∀ v k, k < m → |overlap v (x (k + 1)) - overlap v (x k)| ≤ 2 / (n : ℝ))
    (hgood : ∀ k ≤ m, ¬assemblyBadVertex D K z (x k)) :
    AnchorHypotheses (assemblyAnchorData D K hK z x m) := by
  have hcell : 3 * (D.C / 3) = D.C := by ring
  refine ⟨hn, G.blocks_pos, G.block_size, G.anchor, ?_, ?_, hjump, ?_, ?_, ?_, ?_, ?_⟩
  · intro j _
    exact natBankDefault_mem K hK z j
  · intro j hj v hv
    change j < D.p n at hj
    change flip v ∈ natBankPool K z j
    rw [natBankPool, dite_eq_left hj]
    exact flip_mem_orientedBankPool K z ⟨j, hj⟩ (pool_mem K z hj hv)
  · intro j hj v hv u hu hc
    have H := bank_pool_coverage K D.B z (D.C / 3) D.qStar (x u)
      (fun h => hgood u hu (Or.inl h)) j hj v hv
    simp only [hcell] at H
    exact H hc
  · intro i j hij hj v hv w hw u hu hq hvw hvx
    have H := bank_pool_no_vertex K z (D.bad n) (x u)
      (fun h => hgood u hu (Or.inr h)) ⟨i, hij.trans hj⟩ ⟨j, hj⟩
      (fun he => (Nat.ne_of_lt hij) (congrArg Fin.val he))
      v w (pool_mem K z (hij.trans hj) hv) (pool_mem K z hj hw) (Equiv.refl _)
    apply signed_locking_bound v w (x u) D.qStar D.b (D.η n) hq hvw hvx
    intro hs
    apply H
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr hs)))
  · intro i a j hia haj hj v hv u hu w hw hconf huv huw
    have Hi := pool_mem K z (hia.trans (haj.trans hj)) hv
    have Ha := pool_mem K z (haj.trans hj) hu
    have Hj := pool_mem K z hj hw
    have hai : (⟨a, haj.trans hj⟩ : Fin (D.p n)) ≠ ⟨i, hia.trans (haj.trans hj)⟩ := by
      intro he
      exact (Nat.ne_of_lt hia) (congrArg Fin.val he).symm
    have haj' : (⟨a, haj.trans hj⟩ : Fin (D.p n)) ≠ ⟨j, hj⟩ := by
      intro he
      exact (Nat.ne_of_lt haj) (congrArg Fin.val he)
    have hij' : (⟨i, hia.trans (haj.trans hj)⟩ : Fin (D.p n)) ≠ ⟨j, hj⟩ := by
      intro he
      exact (Nat.ne_of_lt (hia.trans haj)) (congrArg Fin.val he)
    apply magnitude_locking_bound u v w D.b D.bPrime (D.η n) hconf.le huv huw
    · intro hs
      exact bank_pool_no_triple K z (D.bad n) hz _ _ _ hai haj' hij' u v w Ha Hi Hj
        (Finset.mem_union.mpr (Or.inr hs))
    · intro hs
      exact bank_pool_no_triple K z (D.bad n) hz _ _ _ hai haj' hij' u v (flip w)
        Ha Hi (flip_mem_orientedBankPool K z _ Hj) (Finset.mem_union.mpr (Or.inr hs))
  · exact packing_from_gram hn G.b_pos G.cell_nonneg G.gram_margin G.packing_budget
  · refine ⟨{
      centerRegion := D.I
      localDomain := fun r δ q => r ∈ D.I ∧ D.E * D.ρ n ≤ |δ| ∧
        |δ| ≤ 2 * (D.E * D.ρ n) ∧ D.ρ n ≤ q - r
      remoteDomain := fun _ _ _ => False
      excludedPair := fun _ _ => False
      forbidden := fun v y w => (![v, y, w] : ReplicaConfig n 3) ∈ D.bad n
      center_band := G.center_band
      cover := ?_
      local_forbidden := ?_
      remote_forbidden := ?_
      pair_forbidden := ?_
      avoid := ?_ }⟩
    · dsimp only
      intro i a _ _ v _ w _ k _ hc hlo hhi hgap
      exact Or.inl ⟨hc, hlo, hhi, hgap⟩
    · intro v y w h
      exact narrow_mem_bad D n v y w h.1 h.2.1 h.2.2.1 h.2.2.2
    · intro _ _ _ h
      exact False.elim h
    · intro _ _ _ h
      exact False.elim h
    · intro i a hia ha v hv w hw k hk
      exact vertex_narrow_avoid D K z hia ha hv hw (hgood k hk)

private theorem bank_positive_endpoint (D : AssemblyData) {n : ℕ}
    (hn : 0 < n) {c : ℕ → ℝ} (G : AssemblyNumerics D c n)
    (K : Fin (D.p n) → ℕ) (hK : ∀ j, 0 < K j) (z : BankIndex K → Config n)
    (hz : ¬bankTripleBad (fun i : BankIndex K => i.1.val) (D.bad n) z)
    (x : ℕ → Config n) {m : ℕ} (hm : m ≤ clockAttemptCutoff n (D.L n))
    (hjump : ∀ v k, k < m → |overlap v (x (k + 1)) - overlap v (x k)| ≤ 2 / (n : ℝ))
    (hgood : ∀ k ≤ m, ¬assemblyBadVertex D K z (x k)) :
    0 < overlap (initialBankReference (natBankPool K z) (natBankDefault K hK z)
      D.B (D.C / 3) D.qStar (x 0)) (x m) := by
  let A := assemblyAnchorData D K hK z x m
  have hA : AnchorHypotheses A := anchor_hypotheses_of_bank D hn G K hK z hz x m hjump hgood
  have g : ThresholdIntervalGeometry A (D.offset n) (D.width n) :=
    ⟨G.width_pos, G.range, G.separation⟩
  have hT0 : 0 ≤ (D.scales n).T0 := by
    dsimp only [AnchorScales.T0]
    linarith only [G.anchor.epsilon_pos, G.anchor.transfer_nonneg, G.anchor.jump_nonneg]
  have hcount : ((A.m : ℝ) + 1) *
      (2 * A.scales.T0 / D.width n) ^ A.M < 1 := by
    change ((m : ℝ) + 1) * (2 * (D.scales n).T0 / D.width n) ^ D.M n < 1
    refine lt_of_le_of_lt ?_ G.marker_count
    exact mul_le_mul_of_nonneg_right (add_le_add (Nat.cast_le.mpr hm) (le_refl (1 : ℝ)))
      (pow_nonneg (div_nonneg (mul_nonneg (by norm_num) hT0) G.width_pos.le) _)
  rw [initialBankReference_path]
  have H : 0 < overlap (A.pick 0 A.fallback 0) (A.x A.m) :=
    positive_endpoint_of_marker_count hA g hcount
  simpa only [A, assemblyAnchorData, AnchorData.pick, AssemblyData.scales] using H

private theorem bank_stationary_crossing_bound (D : AssemblyData) {n : ℕ}
    (hn : 0 < n) (β : ℝ) (J : Disorder n) {c : ℕ → ℝ}
    (G : AssemblyNumerics D c n) (K : Fin (D.p n) → ℕ) (hK : ∀ j, 0 < K j)
    (z : BankIndex K → Config n)
    (hz : ¬bankTripleBad (fun i : BankIndex K => i.1.val) (D.bad n) z)
    {m : ℕ} (hm : m ≤ clockAttemptCutoff n (D.L n)) :
    (∑ x, gibbs β J x * kernelEvent β J (fun y =>
      overlap (initialBankReference (natBankPool K z) (natBankDefault K hK z)
        D.B (D.C / 3) D.qStar x) y ≤ 0) m x) ≤
      ((m : ℝ) + 1) * (gibbsFiniteLaw β J).prob (assemblyBadVertex D K z) := by
  apply stationary_sign_crossing_bound hn β J m _ (assemblyBadVertex D K z)
  intro path hpath hg
  have H := bank_positive_endpoint D hn G K hK z hz (extendPath path) hm
    (extendPath_jump hn β J path hpath)
    (fun k hk => by
      simpa only [extendPath, dite_eq_left hk] using hg ⟨k, by omega⟩)
  have hz0 : (⟨0, show 0 < m + 1 by omega⟩ : Fin (m + 1)) = 0 := Fin.ext rfl
  simpa only [extendPath, dite_eq_left (show 0 ≤ m by omega),
    dite_eq_left le_rfl, hz0, Fin.last] using H

private lemma bank_error_lt_one {L : ℝ} (hL : 5 ≤ L) :
    3 * Real.exp (-4 * L) < 1 := by
  have he : 3 < Real.exp (4 * L) := by
    linarith only [Real.add_one_le_exp (4 * L), hL]
  rw [show -4 * L = -(4 * L) by ring, Real.exp_neg, mul_inv_lt_iff₀ (Real.exp_pos _)]
  simpa only [one_mul] using he

private theorem exists_reference_crossing_bound (D : AssemblyData) {n : ℕ}
    (hn : 0 < n) (β : ℝ) (J : Disorder n) (c : ℕ → ℝ)
    (hc : ∀ j, 0 ≤ c j) (G : AssemblyNumerics D c n)
    (hcov : ∀ j < D.B, ∀ E : Config n → Prop,
      (gibbsFiniteLaw β J).prob (fun x => E x ∧
        (gibbsFiniteLaw β J).prob (fun y => E y ∧ D.qStar ≤ |overlap x y|) <
          Real.exp (-c j * D.L n)) ≤ Real.exp (-(bankPrefix c j + 5) * D.L n))
    (hv : replicaGibbsMass β J (D.bad n) ≤
      Real.exp (-(3 * bankPrefix c D.B + 20) * D.L n)) :
    ∃ v : Config n → Config n, ∀ k ≤ clockAttemptCutoff n (D.L n),
      (∑ x, gibbs β J x * kernelEvent β J (fun y => overlap (v x) y ≤ 0) k x) ≤
        D.crossingError n := by
  have hB : 0 < D.B := by have := G.block_size; omega
  let K : Fin (D.p n) → ℕ := scheduledBankSize c D.B (D.L n)
  have hK : ∀ j, 0 < K j := scheduledBankSize_pos c D.B (D.L n)
  obtain ⟨z, hz, hmass⟩ := SKBarriers2.exists_fixed_good_bank (p := D.p n) hB β J D.I
    (D.ρ n) (D.E * D.ρ n) (D.η n) D.qStar D.b D.bPrime (D.C / 3) (D.L n)
    c hc hcov hv G.scale_large G.levels_budget G.coverage_budget
    (bank_error_lt_one G.scale_large)
  refine ⟨initialBankReference (natBankPool K z) (natBankDefault K hK z)
    D.B (D.C / 3) D.qStar, ?_⟩
  intro k hk
  refine (bank_stationary_crossing_bound D hn β J G K hK z hz hk).trans ?_
  exact mul_le_mul (add_le_add (Nat.cast_le.mpr hk) (le_refl (1 : ℝ))) hmass
    ((gibbsFiniteLaw β J).prob_nonneg _) (by positivity)

def assemblyGoodEvent (D : AssemblyData)
    (U : ℕ → (n : ℕ) → Set (Disorder n)) (Q : (n : ℕ) → Set (Disorder n))
    (n : ℕ) : Set (Disorder n) := Q n ∩ finiteGoodEvent U D.B n

theorem quenched_crossing_bounds_of_static_event (β : ℝ) (D : AssemblyData)
    (c : ℕ → ℝ) (U : ℕ → (n : ℕ) → Set (Disorder n))
    (Q : (n : ℕ) → Set (Disorder n)) (qn : ℕ → ℝ)
    (hstatic : QuenchedStaticEvent β D.bad Q qn)
    (hcoverage : AssemblyCoverage β D c U)
    (hscale : ∀ᶠ n : ℕ in atTop, AssemblyNumerics D c n)
    (hqn : ∀ᶠ n : ℕ in atTop,
      qn n ≤ Real.exp (-(3 * bankPrefix c D.B + 20) * D.L n)) :
    ∀ᶠ n : ℕ in atTop, ∀ J ∈ assemblyGoodEvent D U Q n,
      ∃ v : Config n → Config n, ∀ k ≤ clockAttemptCutoff n (D.L n),
        (∑ x, gibbs β J x * kernelEvent β J (fun y => overlap (v x) y ≤ 0) k x) ≤
          D.crossingError n := by
  filter_upwards [hstatic.2.2, hscale, hqn, eventually_gt_atTop (0 : ℕ)] with n hs G hq hn J hJ
  apply exists_reference_crossing_bound D hn β J c hcoverage.nonneg G
  · intro j hj E
    exact hcoverage.coverage j n J ((finiteGoodEvent_mem U D.B n J).mp hJ.2 j hj) E
  · exact (hs J hJ.1).trans hq

private lemma assemblyGoodEvent_measurable (β : ℝ) (D : AssemblyData) (c : ℕ → ℝ)
    (U : ℕ → (n : ℕ) → Set (Disorder n)) (Q : (n : ℕ) → Set (Disorder n))
    (qn : ℕ → ℝ) (hs : QuenchedStaticEvent β D.bad Q qn)
    (hc : AssemblyCoverage β D c U) (n : ℕ) :
    MeasurableSet (assemblyGoodEvent D U Q n) := by
  exact (hs.1 n).inter (finiteGoodEvent_measurable U hc.measurable D.B n)

private lemma assemblyGoodEvent_typical (β : ℝ) (D : AssemblyData) (c : ℕ → ℝ)
    (U : ℕ → (n : ℕ) → Set (Disorder n)) (Q : (n : ℕ) → Set (Disorder n))
    (qn : ℕ → ℝ) (hs : QuenchedStaticEvent β D.bad Q qn)
    (hc : AssemblyCoverage β D c U) :
    Tendsto (fun n => (disorderLaw n).real (assemblyGoodEvent D U Q n)) atTop (𝓝 1) := by
  exact high_probability_inter Q (finiteGoodEvent U D.B)
    (finiteGoodEvent_measurable U hc.measurable D.B) hs.2.1
    (finiteGoodEvent_tendsto U hc.measurable hc.typical D.B)

theorem bad_mass_limits_of_static_event (β : ℝ) (_hβ : 1 < β) (D : AssemblyData)
    (c : ℕ → ℝ) (U : ℕ → (n : ℕ) → Set (Disorder n))
    (Q : (n : ℕ) → Set (Disorder n)) (qn : ℕ → ℝ)
    (hstatic : QuenchedStaticEvent β D.bad Q qn)
    (hcoverage : AssemblyCoverage β D c U)
    (hscale : ∀ᶠ n : ℕ in atTop, AssemblyNumerics D c n)
    (hqn : ∀ᶠ n : ℕ in atTop,
      qn n ≤ Real.exp (-(3 * bankPrefix c D.B + 20) * D.L n))
    (herror : Tendsto D.crossingError atTop (𝓝 0))
    (A κ : ℝ) (horizon : ∀ᶠ n : ℕ in atTop, A * (n : ℝ) ^ κ ≤ D.L n) :
    ∀ τ : ℝ, 0 < τ → τ < (1 / 2 : ℝ) →
      Tendsto (OAI.SK.Strengthened.continuousBadMass β A κ τ) atTop (𝓝 1) ∧
      Tendsto (OAI.SK.Strengthened.discreteBadMass β A κ τ) atTop (𝓝 1) := by
  intro τ _hτ hτ
  exact badMass_limits_of_quenched_crossing_bounds β D.L (assemblyGoodEvent D U Q)
    (assemblyGoodEvent_measurable β D c U Q qn hstatic hcoverage)
    (assemblyGoodEvent_typical β D c U Q qn hstatic hcoverage)
    D.crossingError (fun n => by unfold AssemblyData.crossingError; positivity) herror
    (quenched_crossing_bounds_of_static_event β D c U Q qn hstatic hcoverage hscale hqn)
    τ hτ A κ horizon

theorem bad_mass_limits_of_static_event_all_horizons (β : ℝ) (_hβ : 1 < β)
    (D : AssemblyData) (c : ℕ → ℝ) (U : ℕ → (n : ℕ) → Set (Disorder n))
    (Q : (n : ℕ) → Set (Disorder n)) (qn : ℕ → ℝ)
    (hstatic : QuenchedStaticEvent β D.bad Q qn)
    (hcoverage : AssemblyCoverage β D c U)
    (hscale : ∀ᶠ n : ℕ in atTop, AssemblyNumerics D c n)
    (hqn : ∀ᶠ n : ℕ in atTop,
      qn n ≤ Real.exp (-(3 * bankPrefix c D.B + 20) * D.L n))
    (herror : Tendsto D.crossingError atTop (𝓝 0)) :
    ∀ τ : ℝ, 0 < τ → τ < (1 / 2 : ℝ) → ∀ (t : ℕ → ℝ) (k : ℕ → ℕ),
      (∀ᶠ n : ℕ in atTop,
        0 ≤ t n ∧ t n ≤ Real.exp (D.L n) ∧ k n ≤ ⌊Real.exp (D.L n)⌋₊) →
      Tendsto (fun n => continuousBadMassAt β τ n (t n)) atTop (𝓝 1) ∧
      Tendsto (fun n => discreteBadMassAt β τ n (k n)) atTop (𝓝 1) := by
  intro τ _hτ hτ
  exact main_of_quenched_crossing_bounds β D.L (assemblyGoodEvent D U Q)
    (assemblyGoodEvent_measurable β D c U Q qn hstatic hcoverage)
    (assemblyGoodEvent_typical β D c U Q qn hstatic hcoverage)
    D.crossingError (fun n => by unfold AssemblyData.crossingError; positivity) herror
    (quenched_crossing_bounds_of_static_event β D c U Q qn hstatic hcoverage hscale hqn)
    τ hτ

theorem staticEventBadMassLimitsStatement : StaticEventBadMassLimitsStatement := by
  exact bad_mass_limits_of_static_event

end SKBarriers2
