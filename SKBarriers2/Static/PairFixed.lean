module

public import SKBarriers2.Interfaces
public import OAI.Probability.SKBarriers.Replicas.PairGibbsGap
public import OAI.Probability.SKBarriers.Replicas.TripleContinuumGap
public import OAI.Probability.SKBarriers.Replicas.ReplicaEventSplit
public import OAI.Probability.SKBarriers.Replicas.ReplicaMarginal

@[expose] public section

noncomputable section
open scoped BigOperators Topology
open Classical MeasureTheory ProbabilityTheory Filter Set OAI.SK OAI.SK.Analytic

namespace SKBarriers2

def orientReplica {n d : ℕ} (e : Equiv.Perm (Fin d)) (ε : Fin d → Bool)
    (s : ReplicaConfig n d) : ReplicaConfig n d :=
  fun a => if ε a then flip (s (e a)) else s (e a)

def orientGram {d : ℕ} (e : Equiv.Perm (Fin d)) (ε : Fin d → Bool)
    (D : Fin d → Fin d → ℝ) : Fin d → Fin d → ℝ :=
  fun a b => (if ε a then (-1 : ℝ) else 1) * (if ε b then (-1 : ℝ) else 1) * D (e a) (e b)

private theorem overlap_flip_left {n : ℕ} (x y : Config n) :
    overlap (flip x) y = -overlap x y := by
  rw [overlap_comm, overlap_flip_right, overlap_comm y x]

theorem replicaGram_orient {n d : ℕ} (e : Equiv.Perm (Fin d)) (ε : Fin d → Bool)
    (s : ReplicaConfig n d) :
    replicaGram (orientReplica e ε s) = orientGram e ε (replicaGram s) := by
  funext a b
  cases ha : ε a <;> cases hb : ε b <;>
    simp [replicaGram, orientReplica, orientGram, ha, hb, overlap_flip_left]

private def orientEquiv {n d : ℕ} (e : Equiv.Perm (Fin d)) (ε : Fin d → Bool) :
    ReplicaConfig n d ≃ ReplicaConfig n d where
  toFun := orientReplica e ε
  invFun := orientReplica e.symm (fun a => ε (e.symm a))
  left_inv s := by
    funext a
    simp only [orientReplica, Equiv.apply_symm_apply]
    by_cases hε : ε (e.symm a) = true <;> simp [hε]
  right_inv s := by
    funext a
    simp only [orientReplica, Equiv.symm_apply_apply]
    by_cases hε : ε a = true <;> simp [hε]

private theorem orientGram_injective {d : ℕ} (e : Equiv.Perm (Fin d)) (ε : Fin d → Bool) :
    Function.Injective (orientGram e ε) := by
  intro D D' h
  funext a b
  have hab := congrFun (congrFun h (e.symm a)) (e.symm b)
  dsimp only [orientGram] at hab
  simp only [Equiv.apply_symm_apply] at hab
  by_cases ha : ε (e.symm a) = true <;> by_cases hb : ε (e.symm b) = true <;>
    simpa [ha, hb] using hab

private def orientedMatrixEquiv {n d : ℕ} (e : Equiv.Perm (Fin d)) (ε : Fin d → Bool)
    (D : Fin d → Fin d → ℝ) :
    {s : ReplicaConfig n d // s ∈ matrixReplicaSet n d D} ≃
      {s : ReplicaConfig n d // s ∈ matrixReplicaSet n d (orientGram e ε D)} :=
  (orientEquiv e ε).subtypeEquiv (fun s => by
    rw [mem_matrixReplicaSet, mem_matrixReplicaSet]
    change replicaGram s = D ↔ replicaGram (orientReplica e ε s) = orientGram e ε D
    rw [replicaGram_orient]
    exact ⟨congrArg (orientGram e ε), fun h => orientGram_injective e ε h⟩)

theorem matrixStates_orient_nonempty {n d : ℕ} (e : Equiv.Perm (Fin d)) (ε : Fin d → Bool)
    {D : Fin d → Fin d → ℝ} (hD : Nonempty (MatrixStates n d D)) :
    Nonempty (MatrixStates n d (orientGram e ε D)) := by
  exact (matrixReplicaEquiv n d (orientGram e ε D)).nonempty_congr.mpr
    ((orientedMatrixEquiv e ε D).nonempty_congr.mp
      ((matrixReplicaEquiv n d D).nonempty_congr.mp hD))

theorem matrixPressure_orient {n d : ℕ} (β : ℝ) (e : Equiv.Perm (Fin d)) (ε : Fin d → Bool)
    (D : Fin d → Fin d → ℝ) :
    matrixConstrainedPressure n d β (orientGram e ε D) = matrixConstrainedPressure n d β D := by
  rw [← restrictedPressure_matrixReplicaSet, ← restrictedPressure_matrixReplicaSet]
  unfold restrictedPressure
  congr 1
  apply integral_congr_ae
  filter_upwards [] with J
  unfold restrictedLogPartition restrictedPartition
  congr 1
  conv_lhs => rw [← Finset.sum_coe_sort]
  conv_rhs => rw [← Finset.sum_coe_sort]
  apply ((orientedMatrixEquiv e ε D).sum_comp
    (fun s => Real.exp (β * replicaEnergy J s.val))).symm.trans
  apply Finset.sum_congr rfl
  intro s _
  congr 2
  change (∑ a, hamiltonian J (orientReplica e ε s.val a)) = ∑ a, hamiltonian J (s.val a)
  simp only [orientReplica, apply_ite, hamiltonian_flip, ite_self]
  exact Equiv.sum_comp e (fun a => hamiltonian J (s.val a))

theorem replicaGibbsMass_orient {n d : ℕ} (β : ℝ) (J : Disorder n)
    (e : Equiv.Perm (Fin d)) (ε : Fin d → Bool) (S : Finset (ReplicaConfig n d)) :
    replicaGibbsMass β J (S.image (orientReplica e ε)) = replicaGibbsMass β J S := by
  unfold replicaGibbsMass
  have hinj : Function.Injective (@orientReplica n d e ε) := (orientEquiv e ε).injective
  rw [Finset.sum_image hinj.injOn]
  apply Finset.sum_congr rfl
  intro s _
  simp only [orientReplica, apply_ite, gibbs_flip, ite_self]
  exact Equiv.prod_comp e (fun a => gibbs β J (s a))

private theorem orient_pair (q : ℝ) :
    orientGram (Equiv.refl _) (fun a : Fin 2 => a == 0) (pairMatrix 1 q) = pairMatrix 1 (-q) := by
  funext a b
  fin_cases a <;> fin_cases b <;> norm_num [orientGram, pairMatrix]

private theorem orient_triple (r δ q : ℝ) :
    orientGram (Equiv.refl _) (fun a : Fin 3 => a == 0) (tripleGram r δ q) = tripleGram (-r) (-δ) q := by
  funext a b
  fin_cases a <;> fin_cases b <;> simp [orientGram, tripleGram] <;> ring

theorem pair_pressure_gap {N : ℕ} (hN : 0 < N) (β : ℝ)
    (α : StieltjesFunction ℝ) (hα : ∀ z, α z ∈ Icc (0 : ℝ) 1) (hα1 : α 1 = 1)
    (hmin : scalarCDFParisi β α = finiteParisiInf β)
    {q : ℝ} (hq : q ∈ Icc (-1 : ℝ) 1)
    (hD : Nonempty (MatrixStates N 2 (pairMatrix 1 q))) :
    matrixConstrainedPressure N 2 β (pairMatrix 1 q) ≤
      2 * finiteParisiInf β - (|q| - scalarCDFOverlap β α |q|) ^ 2 / 2 := by
  have habs : |q| ∈ Icc (0 : ℝ) 1 := ⟨abs_nonneg _, abs_le.mpr hq⟩
  by_cases hq0 : 0 ≤ q
  · have hp := pairConstrainedPressure_continuum hN β α hα hα1 ⟨hq0, hq.2⟩ hD
    rw [hmin] at hp
    rw [abs_of_nonneg hq0]
    nlinarith only [hp]
  · have hf := matrixStates_orient_nonempty (Equiv.refl _) (fun a : Fin 2 => a == 0) hD
    rw [orient_pair] at hf
    have hp := pairConstrainedPressure_continuum hN β α hα hα1
      (q := -q) ⟨by linarith, by linarith [hq.1]⟩ hf
    have he := matrixPressure_orient (n := N) β (Equiv.refl _) (fun a : Fin 2 => a == 0) (pairMatrix 1 q)
    rw [orient_pair] at he
    rw [hmin, he] at hp
    rw [abs_of_neg (lt_of_not_ge hq0)]
    nlinarith only [hp]

theorem pair_pressure_gap_of_mismatch {N : ℕ} (hN : 0 < N) (β : ℝ)
    (α : StieltjesFunction ℝ) (hα : ∀ z, α z ∈ Icc (0 : ℝ) 1) (hα1 : α 1 = 1)
    (hmin : scalarCDFParisi β α = finiteParisiInf β)
    {q η : ℝ} (hq : q ∈ Icc (-1 : ℝ) 1) (hη : 0 ≤ η)
    (hdev : η ≤ abs (|q| - scalarCDFOverlap β α |q|))
    (hD : Nonempty (MatrixStates N 2 (pairMatrix 1 q))) :
    matrixConstrainedPressure N 2 β (pairMatrix 1 q) ≤ 2 * finiteParisiInf β - η ^ 2 / 2 := by
  have hp := pair_pressure_gap hN β α hα hα1 hmin hq hD
  have hs := pow_le_pow_left₀ hη hdev 2
  rw [sq_abs] at hs
  linarith

theorem fixed_pressure_gap_of_unique_minimizer {β h : ℝ} (hβ : 0 < β)
    (hh : 0 < h) (hh1 : h ≤ 1) (μ : ProbabilityMeasure ℝ)
    (hunique : ∀ ν : ProbabilityMeasure ℝ, (ν : Measure ℝ) (Icc (0 : ℝ) 1) = 1 →
      scalarCDFParisi β (cdf (ν : Measure ℝ)) = finiteParisiInf β → ν = μ) :
    ∃ b τ c : ℝ, 0 < b ∧ 0 < τ ∧ 0 < c ∧
      ∀ N : ℕ, 0 < N → ∀ r δ q : ℝ,
        |r + δ| ≤ b → |r - δ| ≤ b → q ∈ Icc h 1 →
        |q - scalarCDFOverlap β (cdf (μ : Measure ℝ)) q| ≤ τ →
        Nonempty (MatrixStates N 3 (tripleGram r δ q)) →
        matrixConstrainedPressure N 3 β (tripleGram r δ q) ≤ 3 * finiteParisiInf β - c * δ ^ 2 := by
  obtain ⟨ν, hν, hmin, τ, r₀, δ₀, c, hτ, hr₀, hδ₀, hc, hgap⟩ :=
    exists_tripleConstrainedPressure_gap hβ hh hh1
  obtain rfl := hunique ν hν hmin
  refine ⟨min r₀ δ₀, τ, c, lt_min hr₀ hδ₀, hτ, hc, ?_⟩
  intro N hN r δ q hx hy hq hdev hD
  have hr : |r| ≤ r₀ := by
    rw [abs_le] at hx hy ⊢
    have hb := min_le_left r₀ δ₀
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  have hd : |δ| ≤ δ₀ := by
    rw [abs_le] at hx hy ⊢
    have hb := min_le_right r₀ δ₀
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  by_cases hr0 : 0 ≤ r
  · exact hgap N hN r δ q ⟨hr0, (le_abs_self r).trans hr⟩ hd hq hdev hD
  · have hf := matrixStates_orient_nonempty (Equiv.refl _) (fun a : Fin 3 => a == 0) hD
    rw [orient_triple] at hf
    have hp := hgap N hN (-r) (-δ) q ⟨by linarith, (neg_le_abs r).trans hr⟩
      (by simpa only [abs_neg] using hd) hq hdev hf
    have he := matrixPressure_orient (n := N) β (Equiv.refl _) (fun a : Fin 3 => a == 0) (tripleGram r δ q)
    rw [orient_triple] at he
    simpa only [he, neg_sq] using hp

def orientedLockingSetη (n : ℕ) (β : ℝ) (α : ℝ → ℝ) (h b τ η : ℝ) :
    Finset (ReplicaConfig n 3) :=
  Finset.univ.filter (fun s => tripleQ s ∈ Icc h 1 ∧
    0 ≤ tripleR s ∧
    |overlap (s 0) (s 1)| ≤ b ∧ |overlap (s 0) (s 2)| ≤ b ∧
    η ≤ |tripleDelta s| ∧ |tripleQ s - scalarCDFOverlap β α (tripleQ s)| ≤ τ)

theorem signedLockingSetη_split {n : ℕ} (β h b τ η : ℝ) (hh : 0 ≤ h)
    (α : ℝ → ℝ) {s : ReplicaConfig n 3} (hs : s ∈ signedLockingSetη n h b η) :
    s ∈ orientedLockingSetη n β α h b τ η ∨
      replicaFlip 0 s ∈ orientedLockingSetη n β α h b τ η ∨
      Fin.tail s ∈ pairMismatchSet n β α τ := by
  obtain ⟨hq, hx, hy, hd⟩ := (Finset.mem_filter.mp hs).2
  have hq1 := (abs_le.mp (abs_overlap_le_one (s 1) (s 2))).2
  have hδ : η ≤ |tripleDelta s| := by
    dsimp only [tripleDelta]
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith only [hd]
  by_cases hg : |tripleQ s - scalarCDFOverlap β α (tripleQ s)| ≤ τ
  · by_cases hr : 0 ≤ tripleR s
    · left
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨⟨hq, hq1⟩, hr, hx, hy, hδ, hg⟩⟩
    · right; left
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      simp only [tripleQ_flip, tripleR_flip, tripleDelta_flip, abs_neg]
      have hx' : |overlap (replicaFlip 0 s 0) (replicaFlip 0 s 1)| ≤ b := by
        simpa [replicaFlip, overlap_flip_left] using hx
      have hy' : |overlap (replicaFlip 0 s 0) (replicaFlip 0 s 2)| ≤ b := by
        simpa [replicaFlip, overlap_flip_left] using hy
      exact ⟨⟨hq, hq1⟩, by linarith, hx', hy', hδ, hg⟩
  · right; right
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hh.trans hq, (not_le.mp hg).le⟩⟩

theorem signedLockingSetη_mass_le {n : ℕ} (β h b τ η : ℝ) (hh : 0 ≤ h)
    (α : ℝ → ℝ) (J : Disorder n) :
    replicaGibbsMass β J (signedLockingSetη n h b η) ≤
      2 * replicaGibbsMass β J (orientedLockingSetη n β α h b τ η) +
        replicaGibbsMass β J (pairMismatchSet n β α τ) := by
  have hs := replicaGibbsMass_le_or_or_flip (0 : Fin 3) β J
    (signedLockingSetη n h b η) (orientedLockingSetη n β α h b τ η)
    (Finset.univ.filter (fun s : ReplicaConfig n 3 => Fin.tail s ∈ pairMismatchSet n β α τ))
    (fun s hs => by
      rcases signedLockingSetη_split β h b τ η hh α hs with ht | ht | ht
      · exact Or.inl ht
      · exact Or.inr (Or.inl ht)
      · exact Or.inr (Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩)))
  simpa only [replicaGibbsMass_tail] using hs

theorem signedLockingSetη_pressure_gap {β h : ℝ} (hβ : 0 < β)
    (hh : 0 < h) (hh1 : h ≤ 1) (μ : ProbabilityMeasure ℝ)
    (hunique : ∀ ν : ProbabilityMeasure ℝ, (ν : Measure ℝ) (Icc (0 : ℝ) 1) = 1 →
      scalarCDFParisi β (cdf (ν : Measure ℝ)) = finiteParisiInf β → ν = μ) :
    ∃ b τ c : ℝ, 0 < b ∧ 0 < τ ∧ 0 < c ∧
      ∀ N : ℕ, 0 < N → ∀ η : ℝ, 0 ≤ η → ∀ s ∈ signedLockingSetη N h b η,
        matrixConstrainedPressure N 3 β (replicaGram s) ≤ 3 * finiteParisiInf β - c * η ^ 2 ∨
          Fin.tail s ∈ pairMismatchSet N β (cdf (μ : Measure ℝ)) τ := by
  obtain ⟨b, τ, c, hb, hτ, hc, hgap⟩ := fixed_pressure_gap_of_unique_minimizer hβ hh hh1 μ hunique
  refine ⟨b, τ, c, hb, hτ, hc, ?_⟩
  intro N hN η hη s hs
  obtain ⟨hq, hx, hy, hd⟩ := (Finset.mem_filter.mp hs).2
  by_cases hdev : |tripleQ s - scalarCDFOverlap β (cdf (μ : Measure ℝ)) (tripleQ s)| ≤ τ
  · left
    have hfeas := replicaGram_feasible s
    rw [replicaGram_triple_overlap hN] at hfeas ⊢
    have hx' : tripleR s + tripleDelta s = overlap (s 0) (s 1) := by unfold tripleR tripleDelta; ring
    have hy' : tripleR s - tripleDelta s = overlap (s 0) (s 2) := by unfold tripleR tripleDelta; ring
    have hp := hgap N hN (tripleR s) (tripleDelta s) (tripleQ s)
      (by simpa only [hx'] using hx) (by simpa only [hy'] using hy)
      ⟨hq, (abs_le.mp (abs_overlap_le_one (s 1) (s 2))).2⟩ hdev hfeas
    have hδ : η ≤ |tripleDelta s| := by
      dsimp only [tripleDelta]
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith only [hd]
    have hsq := pow_le_pow_left₀ hη hδ 2
    rw [sq_abs] at hsq
    nlinarith only [hp, mul_le_mul_of_nonneg_left hsq hc.le]
  · right
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hh.le.trans hq, (not_le.mp hdev).le⟩⟩

end SKBarriers2
