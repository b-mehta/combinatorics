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

  lemma all_colours_is_all' {V K : set ℕ} (hk : set.finite K) {c : finset ℕ → ℕ} 
    (h : ∀ (e : finset ℕ), e.card = 2 ∧ (∀ x ∈ e, x ∈ V) → c e ∈ K) {v : ℕ} (hv : v ∈ V) :
    bind K (colour_neighbour_in V v c) = {x ∈ V | x ≠ v} :=
  begin
    ext, simp [colour_neighbour_in, -ne.def], split, rintro ⟨_, _, xV, xv, _⟩, refine ⟨xV, xv.symm⟩,
    rintro ⟨xV, xv⟩, refine ⟨_, _, xV, xv.symm, rfl⟩, apply h, split, rw finset.card_insert_of_not_mem, rw finset.card_singleton, 
    rwa finset.not_mem_singleton, simp, rintro t (rfl | rfl); assumption
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

  theorem ramsey_r {r k : ℕ} {M₁ : set ℕ} (hM₁ : set.infinite M₁) (c : finset ℕ → ℕ) (h : ∀ e ∈ (r-edges_of M₁), c e < k) :
    ∃ (M₂ ⊆ M₁), set.infinite M₂ ∧ ∃ (col < k), ∀ i ∈ rset' r M₂, c i = col :=
  begin
    induction r with r ih generalizing M₁ c,
      refine ⟨M₁, subset.refl _, hM₁, c ∅, _, _⟩, apply h, exact ⟨rfl, λ _, false.elim⟩,
      rintros i ⟨hi₁, hi₂⟩, rw finset.card_eq_zero at hi₁, rw hi₁, 
    have: ∃ (f : ℕ → (ℕ × set ℕ × ℕ)), (∀ i, (∀ v ∈ rset' r (f i).2.1, c (insert (f i).1 v) = (f i).2.2)) ∧ 
                                       (∀ i, set.infinite ((f i).2.1)) ∧ 
                                       (∀ i, (f i).2.2 < k) ∧
                                       (∀ i, (f i).2.1 ⊆ M₁) ∧
                                       (∀ i, (f i).1 ∈ M₁) ∧
                                       (∀ i j : ℕ, i < j → (f i).1 < (f j).1 ∧ (f j).1 ∈ (f i).2.1 ∧ (f j).2.1 ⊆ (f i).2.1), 
    { obtain ⟨g, hg⟩ : {g : ℕ → { z : ℕ × set ℕ × ℕ // (∀ v ∈ rset' r z.2.1, c (insert z.1 v) = z.2.2) ∧ set.infinite z.2.1 ∧ z.2.2 < k ∧ z.2.1 ⊆ M₁ ∧ z.1 ∈ M₁} 
                                // ∀ i j, i < j → (g i).1.1 < (g j).1.1 ∧ (g j).1.1 ∈ (g i).1.2.1 ∧ (g j).1.2.1 ⊆ (g i).1.2.1} := 
                       crec' nat.lt_wf (λ _ _ _ (x y : { z : ℕ × set ℕ × ℕ // (∀ v ∈ rset' r z.2.1, c (insert z.1 v) = z.2.2) ∧ set.infinite z.2.1 ∧ z.2.2 < k ∧ z.2.1 ⊆ M₁ ∧ z.1 ∈ M₁}), x.1.1 < y.1.1 ∧ y.1.1 ∈ x.1.2.1 ∧ y.1.2.1 ⊆ x.1.2.1) _,
      exact ⟨λ i, (g i).1, λ i, (g i).2.1, λ i, (g i).2.2.1, λ i, (g i).2.2.2.1, λ i, (g i).2.2.2.2.1, λ i, (g i).2.2.2.2.2, hg⟩,
      rintros i ⟨If, IH⟩,
      cases i, 
      { obtain ⟨v, hv⟩ := classical.indefinite_description _ (exists_mem_of_infinite _ hM₁),
        set c' : finset ℕ → ℕ := λ F, c (insert v F),
        specialize @ih {x ∈ M₁ | x ≠ v} c' (infinite_erase hM₁ _) _, swap, intros e he, apply h, split, rw finset.card_insert_of_not_mem, rw he.1, 
        intro t, exact (he.2 v t).2 rfl, intros t ht, rw finset.mem_insert at ht, rcases ht with rfl | _, exact hv, exact (he.2 t ht).1, 
        obtain ⟨B₁, Bp⟩ := classical.indefinite_description _ ih, 
        obtain ⟨B₁sub, B₁inf, colp⟩ := classical.indefinite_description _ Bp, clear Bp,
        obtain ⟨col, colp2⟩ := classical.indefinite_description _ colp, clear colp,
        obtain ⟨colk, mono⟩ := classical.indefinite_description _ colp2, clear colp2,
        refine ⟨⟨⟨v, B₁, col⟩, mono, B₁inf, colk, λ t ht, (B₁sub ht).1, hv⟩, λ i hi, (not_lt_of_le (zero_le i) hi).elim⟩ },
      set If' := (If i (nat.lt_succ_self i)),
      set ai := If'.1.1,
      set Bi := If'.1.2.1,
      set ci := If'.1.2.2,
      rcases If'.2 with ⟨mono, infBi, colk, subM, memM⟩, 
      obtain ⟨v, hv₁, hv₂⟩ := classical.indefinite_description _ (exists_mem_of_infinite _ (infinite_above_of_infinite _ infBi ai)),
      set c' : finset ℕ → ℕ := λ F, c (insert v F),
      specialize @ih {x ∈ Bi | x ≠ v} c' (infinite_erase infBi _) _, swap, intros e he, apply h, split, rw finset.card_insert_of_not_mem, rw he.1, 
      intro t, exact (he.2 v t).2 rfl, intros t ht, rw finset.mem_insert at ht, rcases ht with rfl | _, exact subM hv₁, exact subM (he.2 t ht).1, 
      obtain ⟨Bi₂, Bp⟩ := classical.indefinite_description _ ih, 
      obtain ⟨Bi₂sub, Bi₂inf, colp⟩ := classical.indefinite_description _ Bp, clear Bp,
      obtain ⟨col, colp2⟩ := classical.indefinite_description _ colp, clear colp,
      obtain ⟨colk₂, mono₂⟩ := classical.indefinite_description _ colp2, clear colp2,
      refine ⟨⟨⟨v, Bi₂, col⟩, mono₂, Bi₂inf, colk₂, λ t ht, subM (Bi₂sub ht).1, subM hv₁⟩, _⟩, 
      intros j hj, 
      rcases eq_or_lt_of_le (nat.le_of_lt_succ hj) with rfl | ji,
        exact ⟨hv₂, hv₁, trans Bi₂sub (set.sep_subset _ _)⟩, 
      specialize IH j i hj (nat.lt_succ_self _) ji, 
      refine ⟨trans IH.1 hv₂, IH.2.2 hv₁, trans Bi₂sub (trans (set.sep_subset _ _) IH.2.2)⟩ }, 
    rcases this with ⟨f, col, inf, validcol, subM, memM, lt'⟩,
    set a := λ i, (f i).1,
    set C := λ i, (f i).2.2,
    obtain ⟨col', colltk, inft⟩ := infinite_pigeonhole (λ col, {i : ℕ | C i = col}) {x | x < k} (finite_lt_nat _) _,
      swap, convert infinite_univ_nat, ext t, simp, apply validcol, 
    have mono_a : strict_mono a, intros x y r, exact (lt' x y r).1,
    refine ⟨a '' {i : ℕ | C i = col'}, _, _, col', colltk, _⟩, 
      apply mem_image_elim, intros x hx, exact memM x,
      intro, apply inft, apply finite_of_finite_image _ a_1, 
      apply inj_on_of_injective, apply strict_mono.injective mono_a, 
    rintros e ⟨he₁, he₂⟩, 
    have he: e ≠ ∅, intro a_1, rw [a_1, finset.card_empty] at he₁, apply nat.succ_ne_zero _ he₁.symm, 
    set e₁ := finset.min' e he,
    have := he₂ e₁ (finset.min'_mem _ _), rcases this with ⟨i₁, h₁, h₂⟩, 
    specialize col i₁ (finset.erase e e₁) _, convert col, 
    rw ← h₂, rw finset.insert_erase, 
    convert (finset.min'_mem _ _), exact h₁.symm,
    split, rw finset.card_erase_of_mem, rw he₁, refl, apply finset.min'_mem, 
    intros t ht, simp [-ne.def] at ht, rcases he₂ t ht.2 with ⟨_, _, rfl⟩, 
    have: e₁ < a w, apply lt_of_le_of_ne _ ht.1.symm, apply finset.min'_le _ _ _ ht.2, 
    apply (lt' _ _ _).2.1, 
    rwa [← strict_mono.lt_iff_lt mono_a, h₂], 
  end

end ramsey