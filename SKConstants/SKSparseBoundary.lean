module

public import SKConstants.SKFieldEnergy

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set WithLp
open scoped ENNReal NNReal Topology BigOperators RealInnerProductSpace Classical Matrix Matrix.Norms.L2Operator
set_option backward.isDefEq.respectTransparency false

namespace SKConstants

theorem spinHammingEnlargement_filtered_gibbs_mass_le {n : ℕ} (beta L : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (B : Finset (Spin n)) (r : ℕ)
    (Good : Spin n → Prop)
    (henergy : ∀ b ∈ B, ∀ x, Good x → hammingDist b x ≤ r →
      |quadraticHamiltonian W x - quadraticHamiltonian W b| ≤ L) :
    cutMass (gibbsProbability beta W) ((spinHammingEnlargement B r).filter Good) ≤
      (((r + 1) * (n + 1)^r : ℕ) : ℝ) * Real.exp (|beta| * L) *
        cutMass (gibbsProbability beta W) B := by
  have hset : (spinHammingEnlargement B r).filter Good =
      B.biUnion (fun b => (spinHammingBall b r).filter Good) := by
    ext x
    simp only [spinHammingEnlargement, Finset.mem_filter, Finset.mem_biUnion]
    tauto
  rw [hset]
  have hb (b) (hb : b ∈ B) :
      cutMass (gibbsProbability beta W) ((spinHammingBall b r).filter Good) ≤
      (((r + 1) * (n + 1)^r : ℕ) : ℝ) * Real.exp (|beta| * L) * gibbsProbability beta W b := by
    have hc (x) (hx : x ∈ (spinHammingBall b r).filter Good) :
        gibbsProbability beta W x ≤ Real.exp (|beta| * L) * gibbsProbability beta W b := by
      obtain ⟨hx, hg⟩ := Finset.mem_filter.mp hx
      exact gibbsProbability_spin_comparison beta L W x b
        (henergy b hb x hg (Finset.mem_filter.mp hx).2)
    calc
      _ ≤ ∑ _x ∈ (spinHammingBall b r).filter Good,
          Real.exp (|beta| * L) * gibbsProbability beta W b := Finset.sum_le_sum hc
      _ = (((spinHammingBall b r).filter Good).card : ℝ) *
          (Real.exp (|beta| * L) * gibbsProbability beta W b) := by simp
      _ ≤ (((r + 1) * (n + 1)^r : ℕ) : ℝ) *
          (Real.exp (|beta| * L) * gibbsProbability beta W b) := by
        apply mul_le_mul_of_nonneg_right _
          (mul_nonneg (Real.exp_pos _).le (gibbsProbability_pos beta W b).le)
        exact_mod_cast (Finset.card_filter_le _ _).trans (spinHammingBall_card_le_pow b r)
      _ = _ := by ring
  calc
    _ ≤ ∑ b ∈ B, cutMass (gibbsProbability beta W) ((spinHammingBall b r).filter Good) :=
      cutMass_biUnion_le _ (fun x => (gibbsProbability_pos beta W x).le) _ _
    _ ≤ ∑ b ∈ B, (((r + 1) * (n + 1)^r : ℕ) : ℝ) *
        Real.exp (|beta| * L) * gibbsProbability beta W b := Finset.sum_le_sum hb
    _ = _ := by rw [← Finset.mul_sum]; rfl

def sparseFieldExcludedSet {n : ℕ} (S : Finset (Spin n)) (r : ℕ) (A : ℝ)
    (z : EuclideanSpace ℝ (Fin n × Fin n)) : Finset (Spin n) :=
  spinHammingEnlargement (spinBoundary S) r ∪
    Finset.univ.filter (fun x => z ∈ sparseFieldBadSet x r A)

theorem sparseFieldExcludedSet_gibbs_mass_le {n r : ℕ} (hn : 0 < n) (beta A : ℝ)
    (S : Finset (Spin n)) (z : EuclideanSpace ℝ (Fin n × Fin n)) :
    let W := GaussianProposal.goeMatrix (1 / Real.sqrt (2 * (n : ℝ))) z
    cutMass (gibbsProbability beta W) (sparseFieldExcludedSet S r A z) ≤
      (((r + 1) * (n + 1)^r : ℕ) : ℝ) *
        Real.exp (|beta| * (2 * A + 2 * ‖W‖ * (r : ℝ))) *
          (2 * cutFlow (continuousHeatBathEdgeFlow beta W) S Sᶜ /
            heatBathMinimumRate beta (2 * Real.sqrt (n : ℝ) * ‖W‖)) +
      cutMass (gibbsProbability beta W)
        (Finset.univ.filter (fun x => z ∈ sparseFieldBadSet x r A)) := by
  let W := GaussianProposal.goeMatrix (1 / Real.sqrt (2 * (n : ℝ))) z
  let Good := fun x : Spin n => z ∉ sparseFieldBadSet x r A
  let E := spinHammingEnlargement (spinBoundary S) r
  let Bad := Finset.univ.filter (fun x : Spin n => z ∈ sparseFieldBadSet x r A)
  have hset : sparseFieldExcludedSet S r A z = E.filter Good ∪ Bad := by
    ext x
    simp only [sparseFieldExcludedSet, E, Good, Bad, Finset.mem_union,
      Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  have he := spinHammingEnlargement_filtered_gibbs_mass_le beta
    (2 * A + 2 * ‖W‖ * (r : ℝ)) W (spinBoundary S) r Good
    (fun b hb x hx hbx => by
      have hxb : hammingDist x b ≤ r := by simpa only [hammingDist_comm] using hbx
      simpa only [abs_sub_comm] using
        sk_energy_difference_outside_sparseFieldBadSet x b hxb A z hx)
  have hf := heatBath_boundary_mass_le_opNorm hn beta W S
  have hu := Finset.sum_union_inter (s₁ := E.filter Good) (s₂ := Bad)
    (f := gibbsProbability beta W)
  have hi := cutMass_nonneg (gibbsProbability beta W) (E.filter Good ∩ Bad)
    (fun x => (gibbsProbability_pos beta W x).le)
  rw [hset]
  have hmass : cutMass (gibbsProbability beta W) (E.filter Good ∪ Bad) ≤
      cutMass (gibbsProbability beta W) (E.filter Good) + cutMass (gibbsProbability beta W) Bad := by
    unfold cutMass at *
    linarith
  apply hmass.trans
  apply add_le_add _ le_rfl
  convert he.trans (mul_le_mul_of_nonneg_left hf (by positivity)) using 1
  congr 1
  ext x
  simp only [E, Finset.mem_filter]

end SKConstants
