import data.set.finite
import crec

noncomputable theory

section ramsey
  local attribute [instance, priority 10] classical.prop_decidable
  open set

  lemma infinite_of_inj_on {α β : Type*} (f : α → β) (s : set α) (t : set β) (hs : set.infinite s) 
    (hf : ∀ x ∈ s, f x ∈ t) (inj : ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂)
  : set.infinite t :=
  begin
    intro, apply hs, constructor, haveI: fintype t := set.finite.fintype a, 
    apply @fintype.of_injective s t _ _ _, intro x, exact ⟨f x.1, hf x.1 x.2⟩, 
    rintros ⟨x, hx⟩ ⟨y, hy⟩ t, injection t with t _, simp only [subtype.mk_eq_mk], apply inj x hx y hy t
  end

  lemma infinite_pigeonhole {α β : Type*} (f : α → set β) (s : set α) (ha : set.finite s) (hb : set.infinite (bind s f)) :
    ∃ a ∈ s, set.infinite (f a) :=
  begin
    by_contra, apply hb, apply set.finite_bind ha, intros t ht, by_contra, apply a, exact ⟨t, ht, a_1⟩
  end

  @[reducible] def rset' (r : ℕ) {α : Type*} (m : set α) : set (finset α) := {x : finset α | x.card = r ∧ ∀ t ∈ x, t ∈ m}
  local notation r`-edges_of `X := rset' r X
  local notation `edges_of `X := rset' 2 X

  def colour_neighbour_in (M : set ℕ) (i : ℕ) (c : finset ℕ → ℕ) (col : ℕ) : set ℕ := 
    {j ∈ M | i ≠ j ∧ c {i,j} = col}

  lemma colour_neighbour_sub (M : set ℕ) (i : ℕ) (c : finset ℕ → ℕ) (col : ℕ) : colour_neighbour_in M i c col ⊆ M :=
  sep_subset _ _

  lemma all_colours_is_all {V K : set ℕ} (hk : set.finite K) {c : finset ℕ → ℕ} (h : ∀ (e : finset ℕ), e.card = 2 → c e ∈ K) {v : ℕ} (hv : v ∈ V) :
    bind K (colour_neighbour_in V v c) = {x ∈ V | x ≠ v} :=
  begin
    ext, simp [colour_neighbour_in, -ne.def], split, rintro ⟨_, _, xV, xv, _⟩, refine ⟨xV, xv.symm⟩,
    rintro ⟨xV, xv⟩, refine ⟨_, _, xV, xv.symm, rfl⟩, apply h, rw finset.card_insert_of_not_mem, rw finset.card_singleton, rwa finset.not_mem_singleton
  end

  lemma infinite_erase {V : set ℕ} (hV : set.infinite V) (x : ℕ) : set.infinite {t ∈ V | t ≠ x} :=
  begin
    intro a, apply hV, by_cases (x ∈ V),
      convert set.finite_insert x a, ext t, simp, split, intro q, by_cases (t = x), rw h, simp [h], right, exact ⟨‹_›, ‹_›⟩, 
      rintro (rfl | _), exact h, exact a_1.1,
    convert a, ext, simp, split; intro p, refine ⟨p, _⟩, rintro rfl, apply h p,
    exact p.1
  end

  lemma get_pair {e : finset ℕ} (he : finset.card e = 2) : ∃ (x y : ℕ), x ≠ y ∧ e = {x,y} :=
  begin
    rw finset.card_eq_succ at he, rcases he with ⟨x, i, notin, rfl, hi⟩, 
    rw finset.card_eq_one at hi, rcases hi with ⟨y, rfl⟩, 
    refine ⟨y, x, _, rfl⟩, rw finset.not_mem_singleton at notin, apply notin.symm
  end

  set_option pp.all false
  set_option trace.check true

  theorem ramsey (k : ℕ) (c : finset ℕ → ℕ) (h : ∀ (e : finset ℕ), e.card = 2 → c e < k) : ∃ (M : set ℕ), set.infinite M ∧ 
    ∃ (col : ℕ), ∀ i ∈ edges_of M, c i = col := 
  begin
    have: ∃ (f : ℕ → (ℕ × set ℕ × ℕ)), (∀ i, (∀ v ∈ (f i).2.1, c {(f i).1, v} = (f i).2.2)) ∧ 
                                       (∀ i, set.infinite ((f i).2.1)) ∧ 
                                       (∀ i, (f i).2.2 < k) ∧
                                       (∀ i j : ℕ, i < j → (f i).1 < (f j).1 ∧ (f j).1 ∈ (f i).2.1 ∧ (f j).2.1 ⊆ (f i).2.1), 
    { obtain ⟨g, hg⟩ : {g : ℕ → { z : ℕ × set ℕ × ℕ // (∀ v ∈ z.2.1, c {z.1, v} = z.2.2) ∧ set.infinite z.2.1 ∧ z.2.2 < k} 
                                // ∀ i j, i < j → (g i).1.1 < (g j).1.1 ∧ (g j).1.1 ∈ (g i).1.2.1 ∧ (g j).1.2.1 ⊆ (g i).1.2.1} := 
                       crec' nat.lt_wf (λ _ _ _ (x y : { z : ℕ × set ℕ × ℕ // (∀ v ∈ z.2.1, c {z.1, v} = z.2.2) ∧ set.infinite z.2.1 ∧ z.2.2 < k}), x.1.1 < y.1.1 ∧ y.1.1 ∈ x.1.2.1 ∧ y.1.2.1 ⊆ x.1.2.1) _,
      exact ⟨λ i, (g i).1, λ i, (g i).2.1, λ i, (g i).2.2.1, λ i, (g i).2.2.2, hg⟩,
      rintros i ⟨If, IH⟩,
      cases i,
      { set v : ℕ := 0,
        have := infinite_pigeonhole (colour_neighbour_in univ v c) {i : ℕ | i < k} (finite_lt_nat k) _, 
          swap, rw all_colours_is_all (finite_lt_nat k) h (mem_univ v), apply infinite_erase, apply infinite_univ_nat,
        rcases classical.indefinite_description _ this with ⟨red, red_prop⟩,
        rcases classical.indefinite_description _ red_prop with ⟨red_lt_2, inf_red_edges⟩,
        refine ⟨⟨⟨v, colour_neighbour_in univ v c red, red⟩, _, inf_red_edges, red_lt_2⟩, λ i hi, (not_lt_of_le (zero_le i) hi).elim⟩, 
          intros v hv, convert hv.2.2 },
      set If' := (If i (nat.lt_succ_self i)),
      rcases If'.2 with ⟨q, infBi, validCi⟩, 
      obtain ⟨v, hv₁, hv₂⟩ := classical.indefinite_description _ (exists_mem_of_infinite _ (infinite_above_of_infinite _ infBi If'.1.1)),
      have := infinite_pigeonhole (colour_neighbour_in (If'.1.2.1) v c) {i : ℕ | i < k} (finite_lt_nat k) _, 
        swap, rw all_colours_is_all (finite_lt_nat k) h hv₁, apply infinite_erase infBi, 
      rcases classical.indefinite_description _ this with ⟨red, red_prop⟩,
      rcases classical.indefinite_description _ red_prop with ⟨red_lt_k, inf_red_edges⟩,
      refine ⟨⟨⟨v, colour_neighbour_in If'.1.2.1 v c red, red⟩, _, inf_red_edges, red_lt_k⟩, _⟩, 
        intros v hv, convert hv.2.2,
      intros j hj, 
      rcases eq_or_lt_of_le (nat.le_of_lt_succ hj) with rfl | ji, 
        refine ⟨hv₂, hv₁, colour_neighbour_sub _ _ _ _⟩,
      specialize IH j i hj (nat.lt_succ_self _) ji, 
      refine ⟨trans IH.1 hv₂, IH.2.2 hv₁, trans (colour_neighbour_sub _ _ _ _) IH.2.2⟩ },
    rcases this with ⟨f, col, inf, validcol, lt'⟩,
    set a := λ i, (f i).1,
    set C := λ i, (f i).2.2,
    obtain ⟨col', colltk, inft⟩ := infinite_pigeonhole (λ col, {i : ℕ | C i = col}) {x | x < k} (finite_lt_nat _) _,
      swap, convert infinite_univ_nat, ext t, simp, apply validcol, 
    simp at colltk inft, 
    refine ⟨a '' {i : ℕ | C i = col'}, _, col', _⟩, 
      intro, apply inft, apply finite_of_finite_image _ a_1, 
      intros i j hi hj, apply strict_mono.injective, 
      intros x y r, apply (lt' x y r).1, 
    rintros e ⟨he₁, he₂⟩, simp at he₂, 
    obtain ⟨x, y, xney, rfl⟩ := get_pair he₁, 
    obtain ⟨i, Ci, rfl⟩ := he₂ x (by simp), obtain ⟨j, Cj, rfl⟩ := he₂ y (by simp), 
    rcases lt_trichotomy i j with lt | rfl | gt,
    swap, exfalso, apply xney rfl, 
    rw ← Ci, apply col, 
    apply (lt' i j lt).2.1,
    suffices: c {a j, a i} = col', 
      convert this using 2, ext, simp, rw or_comm,
    rw ← Cj, apply col, 
    apply (lt' j i gt).2.1,
  end

  lemma ramsey' {k : ℕ} {M₁ : set ℕ} (hM₁ : set.infinite M₁) (c : finset ℕ → ℕ) (h : ∀ (e : finset ℕ), e.card = 2 ∧ (∀ x ∈ e, x ∈ M₁) → c e < k) :
    ∃ (M₂ ⊆ M₁), set.infinite M₂ ∧ ∃ (col : ℕ), ∀ i ∈ edges_of M₂, c i = col :=
  begin
    obtain ⟨f, hf⟩ := has_sequence_of_infinite M₁ hM₁,
    have mono_f: strict_mono f := hf.2, 
    have inj_f: function.injective f := mono_f.injective,
    set c' : finset ℕ → ℕ := λ e, c (e.image f),
    obtain ⟨M₂', infM₂', col, monoc⟩ := ramsey k c' _, 
      refine ⟨f '' M₂', λ t ht, _, _, col, _⟩, rw mem_image at ht, rcases ht with ⟨_, _, rfl⟩, apply hf.1,
        rw set.infinite, rw finite_image_iff_on, exact infM₂', intros x y _ _, apply inj_f, 
      rintros i ⟨hi₁, hi₂⟩, 
      set i' := finset.preimage i (inj_on_of_injective _ inj_f), 
      have: i = finset.image f i',
        ext, simp, split, intro ha, specialize hi₂ a ha, simp at hi₂, rcases hi₂ with ⟨z, hz, rfl⟩, refine ⟨z, ha, rfl⟩, 
        rintro ⟨_, q, rfl⟩, exact q,
      convert monoc i' _, split, rwa [this, finset.card_image_of_injective _ inj_f] at hi₁, 
      intros t th, rw finset.mem_preimage at th, specialize hi₂ _ th, rwa mem_image_of_injective inj_f at hi₂, 
    intros e he, apply h, split, rwa finset.card_image_of_injective _ inj_f, 
    simp, rintros _ _ _ rfl, apply hf.1, 
  end
end ramsey