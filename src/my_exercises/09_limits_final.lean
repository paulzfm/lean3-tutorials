import tuto_lib

set_option pp.beta true
set_option pp.coercions false

/-
This is the final file in the series. Here we use everything covered
in previous files to prove a couple of famous theorems from 
elementary real analysis. Of course they all have more general versions
in mathlib.

As usual, keep in mind the following:

  abs_le (x y : ℝ) : |x| ≤ y ↔ -y ≤ x ∧ x ≤ y

  ge_max_iff (p q r) : r ≥ max p q  ↔ r ≥ p ∧ r ≥ q

  le_max_left p q : p ≤ max p q

  le_max_right p q : q ≤ max p q

as well as a lemma from the previous file:

  le_of_le_add_all : (∀ ε > 0, y ≤ x + ε) →  y ≤ x

Let's start with a variation on a known exercise.
-/

-- 0071
lemma le_lim {x y : ℝ} {u : ℕ → ℝ} (hu : seq_limit u x)
  (ineg : ∃ N, ∀ n ≥ N, y ≤ u n) : y ≤ x :=
begin
  apply le_of_le_add_all,
  intros ε hε,
  cases hu ε hε with N hN,
  cases ineg with N' hN',
  specialize hN (max N N') (by apply le_max_left),
  rw abs_le at hN,
  linarith [hN' (max N N') (by apply le_max_right)],
end

/-
Let's now return to the result proved in the `00_` file of this series, 
and prove again the sequential characterization of upper bounds (with a slighly
different proof).

For this, and other exercises below, we'll need many things that we proved in previous files,
and a couple of extras.

From the 5th file:

  limit_const (x : ℝ) : seq_limit (λ n, x) x


  squeeze (lim_u : seq_limit u l) (lim_w : seq_limit w l)
    (hu : ∀ n, u n ≤ v n) (hw : ∀ n, v n ≤ w n)  : seq_limit v l

From the 8th:

  def upper_bound (A : set ℝ) (x : ℝ) := ∀ a ∈ A, a ≤ x

  def is_sup (A : set ℝ) (x : ℝ) := upper_bound A x ∧ ∀ y, upper_bound A y → x ≤ y

  lt_sup (hx : is_sup A x) : ∀ y, y < x → ∃ a ∈ A, y < a :=

You can also use:

  nat.one_div_pos_of_nat {n : ℕ} : 0 < 1 / (n + 1 : ℝ)

  inv_succ_le_all :  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, 1/(n + 1 : ℝ) ≤ ε

and their easy consequences:

  limit_of_sub_le_inv_succ (h : ∀ n, |u n - x| ≤ 1/(n+1)) : seq_limit u x

  limit_const_add_inv_succ (x : ℝ) : seq_limit (λ n, x + 1/(n+1)) x

  limit_const_sub_inv_succ (x : ℝ) : seq_limit (λ n, x - 1/(n+1)) x

The structure of the proof is offered. It features a new tactic: 
`choose` which invokes the axiom of choice (observing the tactic state before and
after using it should be enough to understand everything). 
-/

-- 0072
lemma is_sup_iff (A : set ℝ) (x : ℝ) :
(is_sup A x) ↔ (upper_bound A x ∧ ∃ u : ℕ → ℝ, seq_limit u x ∧ ∀ n, u n ∈ A ) :=
begin
  split,
  { intro h,
    split,
    {
      exact h.1,
    },
    { have : ∀ n : ℕ, ∃ a ∈ A, x - 1/(n+1) < a,
      { intros n,
        have : 1/(n+1 : ℝ) > 0,
          exact nat.one_div_pos_of_nat,
        exact lt_sup h (x - 1/(n+1)) (by linarith),
      },
      choose u hu using this,
      use u, split,
      { apply limit_of_sub_le_inv_succ, intro n,
        rw abs_le, split,
        { linarith [(hu n).2], },
        { suffices : u n - x < 1 / (n + 1), by linarith,
          calc u n - x ≤ 0           : by linarith [h.1 _ ((hu n).1)]
                   ... < 1 / (n + 1) : nat.one_div_pos_of_nat,
        },
      },
      { intro n, exact (hu n).1, }
  } },
  { rintro ⟨maj, u, limu, u_in⟩,
    split,
    { exact maj, },
    { intros y ub,
      apply le_of_le_add_all,
      intros ε hε,
      cases limu ε hε with N hN,
      specialize hN N (by linarith),
      rw abs_le at hN,
      linarith [ub _ (u_in N)],
    }
  },
end

/-- Continuity of a function at a point  -/
def continuous_at_pt (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε

variables {f : ℝ → ℝ} {x₀ : ℝ} {u : ℕ → ℝ}

-- 0073
lemma seq_continuous_of_continuous (hf : continuous_at_pt f x₀)
  (hu : seq_limit u x₀) : seq_limit (f ∘ u) (f x₀) :=
begin
  intros ε hε,
  rcases hf ε hε with ⟨δ, hδ, hf⟩,
  cases hu δ hδ with N hN,
  use N, intros n hn,
  apply hf,
  apply hN,
  exact hn,
end

-- 0074
example :
  (∀ u : ℕ → ℝ, seq_limit u x₀ → seq_limit (f ∘ u) (f x₀)) →
  continuous_at_pt f x₀ :=
begin
  contrapose!,
  intro hf,
  unfold continuous_at_pt at hf,
  push_neg at hf,
  rcases hf with ⟨ε, hε, hf⟩,
  have H : ∀ n : ℕ, ∃ x, |x - x₀| ≤ 1/(n+1) ∧ ε < |f x - f x₀|,
    intro n,
    apply hf,
    exact nat.one_div_pos_of_nat,
  clear hf,
  choose u hu using H,
  use u, split,
  { intros η hη,
    cases inv_succ_le_all η hη with N hN,
    use N, intros n hn,
    linarith [(hu n).1, hN n hn],
  },
  { unfold seq_limit,
    push_neg,
    use ε, split,
    { exact hε, },
    { intros N, 
      use N,
      exact ⟨by linarith, (hu N).2⟩,
    }
  }
end

/-
Recall from the 6th file:


  def extraction (φ : ℕ → ℕ) := ∀ n m, n < m → φ n < φ m

  def cluster_point (u : ℕ → ℝ) (a : ℝ) :=
    ∃ φ, extraction φ ∧ seq_limit (u ∘ φ) a


  id_le_extraction : extraction φ → ∀ n, n ≤ φ n

and from the 8th file:

  def tendsto_infinity (u : ℕ → ℝ) := ∀ A, ∃ N, ∀ n ≥ N, u n ≥ A

  not_seq_limit_of_tendstoinfinity : tendsto_infinity u → ∀ l, ¬ seq_limit u l
-/

variables {φ : ℕ → ℕ}


-- 0075
lemma subseq_tendstoinfinity
  (h : tendsto_infinity u) (hφ : extraction φ) :
tendsto_infinity (u ∘ φ) :=
begin
  intro a,
  cases h a with N hN,
  use N,
  intros n hn,
  apply hN,
  linarith [id_le_extraction hφ n],
end

-- 0076
lemma squeeze_infinity {u v : ℕ → ℝ} (hu : tendsto_infinity u)
(huv : ∀ n, u n ≤ v n) : tendsto_infinity v :=
begin
  intro a,
  cases hu a with N hN,
  use N,
  intros n hn,
  linarith [huv n, hN n hn],
end

/-
We will use segments: Icc a b := { x | a ≤ x ∧ x ≤ b }
The notation stands for Interval-closed-closed. Variations exist with
o or i instead of c, where o stands for open and i for infinity.

We will use the following version of Bolzano-Weierstrass

  bolzano_weierstrass (h : ∀ n, u n ∈ [a, b]) :
    ∃ c ∈ [a, b], cluster_point u c

as well as the obvious

  seq_limit_id : tendsto_infinity (λ n, n)
-/
open set


-- 0077
lemma bdd_above_segment {f : ℝ → ℝ} {a b : ℝ} (hf : ∀ x ∈ Icc a b, continuous_at_pt f x) :
∃ M, ∀ x ∈ Icc a b, f x ≤ M :=
begin
  by_contradiction H,
  push_neg at H,
  have H' : ∀ n : ℕ, ∃ x, x ∈ Icc a b ∧ f x > n, from (λ n, H n),
  clear H,
  choose u hu using H',
  rcases bolzano_weierstrass (λ n, (hu n).1) with ⟨c, hc, ⟨φ, hφ, hlim⟩⟩,
  -- on the one hand
  have has_limit : seq_limit (f ∘ (u ∘ φ)) (f c),
    from seq_continuous_of_continuous (hf c hc) hlim,
  -- on the other hand
  have tendsto_inf₁ : tendsto_infinity (f ∘ u),
    from squeeze_infinity seq_limit_id (λ n, by linarith [(hu n).2]),
  have tendsto_inf : tendsto_infinity (f ∘ (u ∘ φ)),
    from subseq_tendstoinfinity tendsto_inf₁ hφ,
  -- therefore
  exact not_seq_limit_of_tendstoinfinity tendsto_inf _ has_limit,
end

/-
In the next exercise, we can use:

  abs_neg x : |-x| = |x|
-/

-- 0078
lemma continuous_opposite {f : ℝ → ℝ} {x₀ : ℝ} (h : continuous_at_pt f x₀) :
  continuous_at_pt (λ x, -f x) x₀ :=
begin
  intros ε hε,
  rcases h ε hε with ⟨δ, hδ, h⟩,
  use [δ, hδ],
  intros x hx,
  have : -f x - -f x₀ = -(f x - f x₀), by ring,
  rw [this, abs_neg],
  apply h, exact hx,
end

/-
Now let's combine the two exercises above
-/

-- 0079
lemma bdd_below_segment {f : ℝ → ℝ} {a b : ℝ} (hf : ∀ x ∈ Icc a b, continuous_at_pt f x) :
∃ m, ∀ x ∈ Icc a b, m ≤ f x :=
begin
  have : ∃ M, ∀ x ∈ Icc a b, -f x ≤ M,
  { apply bdd_above_segment,
    intros x hx,
    apply continuous_opposite,
    exact hf x hx,
  },
  cases this with M hM,
  use -M,
  intros x hx,
  linarith [hM x hx],
end

/-
Remember from the 5th file:

 unique_limit : seq_limit u l → seq_limit u l' → l = l'

and from the 6th one:

  subseq_tendsto_of_tendsto (h : seq_limit u l) (hφ : extraction φ) :
    seq_limit (u ∘ φ) l

We now admit the following version of the least upper bound theorem
(that cannot be proved without discussing the construction of real numbers
or admitting another strong theorem).

sup_segment {a b : ℝ} {A : set ℝ} (hnonvide : ∃ x, x ∈ A) (h : A ⊆ Icc a b) :
  ∃ x ∈ Icc a b, is_sup A x

In the next exercise, it can be useful to prove inclusions of sets of real number.
By definition, A ⊆ B means : ∀ x, x ∈ A → x ∈ B.
Hence one can start a proof of A ⊆ B by `intros x x_in`,
which brings `x : ℝ` and `x_in : x ∈ A` in the local context,
and then prove `x ∈ B`.

Note also the use of 
  {x | P x}
which denotes the set of x satisfying predicate P.

Hence `x' ∈ { x | P x} ↔ P x'`, by definition.
-/

-- 0080
example {a b : ℝ} (hab : a ≤ b) (hf : ∀ x ∈ Icc a b, continuous_at_pt f x) :
∃ x₀ ∈ Icc a b, ∀ x ∈ Icc a b, f x ≤ f x₀ :=
begin
  cases bdd_above_segment hf with M hM,
  cases bdd_below_segment hf with m hm,
  let A := {y | ∃ x ∈ Icc a b, y = f x},
  have A_nonempty : ∃ e, e ∈ A,
  { use f a, use a,
    exact ⟨⟨by linarith, by linarith⟩, by ring⟩,
  },
  have A_inc : A ⊆ Icc m M,
  { rintros a ⟨x, hx, rfl⟩,
    exact ⟨hm x hx, hM x hx⟩,
  },
  rcases sup_segment A_nonempty A_inc with ⟨y, hy, hsup⟩,
  rw is_sup_iff at hsup,
  rcases hsup with ⟨hub, u, ⟨lim_u, hu⟩⟩,
  choose v hv using hu,
  rcases bolzano_weierstrass (λ n, (hv n).1) with ⟨c, hc, ⟨φ, hφ, lim_vφ⟩⟩,
  use [c, hc], intros x hx,
  have lim_fvφ : seq_limit ((f ∘ v) ∘ φ) (f c),
    from seq_continuous_of_continuous (hf c hc) lim_vφ,
  clear lim_vφ,
  have lim_uφ := subseq_tendsto_of_tendsto lim_u hφ,
  have u_fv : u = f ∘ v, from funext (λ n, (hv n).2),
  rw ← u_fv at lim_fvφ,
  rw unique_limit lim_fvφ lim_uφ,
  apply hub,
  use x, exact ⟨hx, rfl⟩,
end

lemma stupid {a b x : ℝ} (h : x ∈ Icc a b) (h' : x ≠ b) : x < b :=
lt_of_le_of_ne h.right h'

/-
And now the final boss...
-/

def I := (Icc 0 1 : set ℝ) -- the type ascription makes sure 0 and 1 are real numbers here

-- 0081
example (f : ℝ → ℝ) (hf : ∀ x, continuous_at_pt f x) (h₀ : f 0 < 0) (h₁ : f 1 > 0) :
∃ x₀ ∈ I, f x₀ = 0 :=
begin
  let A := { x | x ∈ I ∧ f x < 0},
  have ex_x₀ : ∃ x₀ ∈ I, is_sup A x₀,
  { apply sup_segment,
    { use 0, exact ⟨⟨by linarith, by linarith⟩, h₀⟩, },
    { intros a h, exact h.1, },
  },
  rcases ex_x₀ with ⟨x₀, x₀_in, x₀_sup⟩,
  use [x₀, x₀_in],
  have : f x₀ ≤ 0,
  { rw is_sup_iff at x₀_sup,
    rcases x₀_sup with ⟨_, u, lim_u, hu⟩,
    have lim_fu := seq_continuous_of_continuous (hf x₀) lim_u,
    have hfu : ∀ n, f (u n) ≤ 0, from λ n, by linarith [(hu n).2],
    exact lim_le lim_fu hfu,
  },
  have x₀_1: x₀ < 1,
  { apply stupid x₀_in,
    intro H,
    rw H at this,
    linarith,
  },
  have : f x₀ ≥ 0,
  { have in_I : ∃ N : ℕ, ∀ n ≥ N, x₀ + 1/(n+1) ∈ I,
    { have : ∃ N : ℕ, ∀ n≥ N, 1/(n+1 : ℝ) ≤ 1-x₀,
        from inv_succ_le_all _ (by linarith),
      cases this with N hN,
      use N, intros n hn,
      have : 1 / (n + 1 : ℝ) > 0, from nat.one_div_pos_of_nat,
      exact ⟨by linarith [x₀_in.1], by linarith [hN n hn]⟩,
    },
    have not_in : ∀ n : ℕ, x₀ + 1/(n+1) ∉ A,
    -- By definition, x ∉ A means ¬ (x ∈ A).
    { intros n hn,
      have := x₀_sup.1 _ hn,
      have : 1 / (n + 1 : ℝ) > 0, from nat.one_div_pos_of_nat,
      linarith,
    },
    dsimp [A] at not_in,
    push_neg at not_in,
    cases in_I with N in_I,
    have lim_f := seq_continuous_of_continuous (hf x₀) (limit_const_add_inv_succ _),
    exact le_lim lim_f ⟨N, (λ n hn, not_in n (in_I n hn))⟩,
  },
  linarith,
end

-- In fact, a more general case is:
example (f : ℝ → ℝ) (hf : ∀ x, continuous_at_pt f x) (a b : ℝ) (hab : a ≤ b)
  (h₀ : f a < 0) (h₁ : f b > 0) :
∃ x₀ ∈ Icc a b, f x₀ = 0 :=
begin
  let A := { x | x ∈ Icc a b ∧ f x < 0},
  have ex_x₀ : ∃ x₀ ∈ Icc a b, is_sup A x₀,
  { apply sup_segment,
    { use a, exact ⟨⟨by linarith, hab⟩, h₀⟩, },
    { intros a h, exact h.1, },
  },
  rcases ex_x₀ with ⟨x₀, x₀_in, x₀_sup⟩,
  use [x₀, x₀_in],
  have : f x₀ ≤ 0,
  { rw is_sup_iff at x₀_sup,
    rcases x₀_sup with ⟨_, u, lim_u, hu⟩,
    have lim_fu := seq_continuous_of_continuous (hf x₀) lim_u,
    have hfu : ∀ n, f (u n) ≤ 0, from λ n, by linarith [(hu n).2],
    exact lim_le lim_fu hfu,
  },
  have x₀_1: x₀ < b,
  { apply stupid x₀_in,
    intro H,
    rw H at this,
    linarith,
  },
  have : f x₀ ≥ 0,
  { have in_I : ∃ N : ℕ, ∀ n ≥ N, x₀ + 1/(n+1) ∈ Icc a b,
    { have : ∃ N : ℕ, ∀ n≥ N, 1/(n+1 : ℝ) ≤ b-x₀,
        from inv_succ_le_all _ (by linarith),
      cases this with N hN,
      use N, intros n hn,
      have : 1 / (n + 1 : ℝ) > 0, from nat.one_div_pos_of_nat,
      exact ⟨by linarith [x₀_in.1], by linarith [hN n hn]⟩,
    },
    have not_in : ∀ n : ℕ, x₀ + 1/(n+1) ∉ A,
    -- By definition, x ∉ A means ¬ (x ∈ A).
    { intros n hn,
      have := x₀_sup.1 _ hn,
      have : 1 / (n + 1 : ℝ) > 0, from nat.one_div_pos_of_nat,
      linarith,
    },
    dsimp [A] at not_in,
    push_neg at not_in,
    cases in_I with N in_I,
    have lim_f := seq_continuous_of_continuous (hf x₀) (limit_const_add_inv_succ _),
    exact le_lim lim_f ⟨N, (λ n hn, not_in n (in_I n hn))⟩,
  },
  linarith,
end

