module
public import SKConstants.ParisiSpinPinning
public import SKConstants.SpinGeometry

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SKConstants
open SKConstantsOAI.ZeroTemperatureSK
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

theorem spinHamming_pinning_triangle {n : ℕ} (x y : Spin n)
    (m m' : EuclideanSpace ℝ (Fin n)) :
    4*(hammingDist x y:ℝ) ≤ 3*(‖spinEuclidean x-m‖^2+‖m-m'‖^2+‖m'-spinEuclidean y‖^2) := by
  have he : spinEuclidean x-spinEuclidean y =
      (spinEuclidean x-m)+(m-m')+(m'-spinEuclidean y) := by abel
  have hn : ‖spinEuclidean x-spinEuclidean y‖ ≤
      ‖spinEuclidean x-m‖+‖m-m'‖+‖m'-spinEuclidean y‖ := by
    rw [he]
    calc
      _ ≤ ‖(spinEuclidean x-m)+(m-m')‖+‖m'-spinEuclidean y‖ := norm_add_le _ _
      _ ≤ _ := by linarith [norm_add_le (spinEuclidean x-m) (m-m')]
  rw [← spinEuclidean_distance_sq]
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hn 2
  nlinarith [sq_nonneg (‖spinEuclidean x-m‖-‖m-m'‖),
    sq_nonneg (‖spinEuclidean x-m‖-‖m'-spinEuclidean y‖),
    sq_nonneg (‖m-m'‖-‖m'-spinEuclidean y‖)]

def actualParisiRowsTerminalSpin {Ω : Type*} {n : ℕ} (ω : Fin n → Bool × Ω) : Spin n :=
  fun i => (ω i).1

def actualParisiRowsPosteriorMean {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (W : BrownianSystem Ω) (β : ℝ) (S : ℝ≥0) (ω : Fin n → Bool × Ω) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => actualParisiFullPosteriorMean W β S (ω i).2)

theorem actualParisiRows_pinning_norm_sq {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (W : BrownianSystem Ω) (β : ℝ) (S : ℝ≥0) (ω : Fin n → Bool × Ω) :
    ‖spinEuclidean (actualParisiRowsTerminalSpin ω)-actualParisiRowsPosteriorMean W β S ω‖^2 =
      ∑ i : Fin n,actualParisiPinningError W β S (ω i) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i hi
  rfl

theorem actualParisiRows_Hamming_of_pinning {Ω Ξ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ] {n : ℕ}
    (W : BrownianSystem Ω) (Z : BrownianSystem Ξ) (β : ℝ) (S R : ℝ≥0)
    (ω : Fin n → Bool × Ω) (ζ : Fin n → Bool × Ξ) (a b c : ℝ)
    (ha : (∑ i : Fin n,actualParisiPinningError W β S (ω i))≤a)
    (hb : ‖actualParisiRowsPosteriorMean W β S ω-actualParisiRowsPosteriorMean Z β R ζ‖^2≤b)
    (hc : (∑ i : Fin n,actualParisiPinningError Z β R (ζ i))≤c) :
    (hammingDist (actualParisiRowsTerminalSpin ω) (actualParisiRowsTerminalSpin ζ):ℝ)≤
      (3/4:ℝ)*(a+b+c) := by
  have ht := spinHamming_pinning_triangle (actualParisiRowsTerminalSpin ω)
    (actualParisiRowsTerminalSpin ζ) (actualParisiRowsPosteriorMean W β S ω)
    (actualParisiRowsPosteriorMean Z β R ζ)
  rw [actualParisiRows_pinning_norm_sq,
    norm_sub_rev (actualParisiRowsPosteriorMean Z β R ζ) (spinEuclidean (actualParisiRowsTerminalSpin ζ)),
    actualParisiRows_pinning_norm_sq] at ht
  linarith

end SKConstants
