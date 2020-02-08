import data.set.finite
import crec

noncomputable theory

section ramsey
  local attribute [instance, priority 10] classical.prop_decidable
  open set

  lemma infinite_pigeonhole {α β : Type*} (f : α → set β) (s : set α) (ha : set.finite s) (hb : set.infinite (bind s f)) :
    ∃ a ∈ s, set.infinite (f a) :=
  begin
    by_contra, apply hb, apply set.finite_bind ha, intros t ht, by_contra, apply a, exact ⟨t, ht, a_1⟩
  end

  @[reducible] def rset' (r : ℕ) {α : Type*} (m : set α) : set (finset α) := {x : finset α | x.card = r ∧ ∀ t ∈ x, t ∈ m}
  local notation r`-edges_of `X := rset' r X
  local notation `edges_of `X := rset' 2 X

  lemma infinite_erase {α : Type*} {V : set α} (hV : set.infinite V) (x : α) : set.infinite {t ∈ V | t ≠ x} :=
  begin
    intro a, apply hV, by_cases (x ∈ V),
      convert set.finite_insert x a, ext t, simp, split, intro q, by_cases (t = x), rw h, simp [h], right, exact ⟨‹_›, ‹_›⟩, 
      rintro (rfl | _), exact h, exact a_1.1,
    convert a, ext, simp, split; intro p, refine ⟨p, _⟩, rintro rfl, apply h p,
    exact p.1
  end

  theorem ramsey_r {α : Type} (K : finset α) {r : ℕ} {M₁ : set ℕ} (hM₁ : set.infinite M₁) 
    (c : finset ℕ → α) (h : ∀ e ∈ (r-edges_of M₁), c e ∈ K) :
    ∃ (M₂ ⊆ M₁), set.infinite M₂ ∧ ∃ (col ∈ K), ∀ i ∈ (r-edges_of M₂), c i = col :=
  begin
    induction r with r ih generalizing M₁ c,
      refine ⟨M₁, subset.refl _, hM₁, c ∅, _, _⟩, apply h, exact ⟨rfl, λ _, false.elim⟩,
      rintros i ⟨hi₁, hi₂⟩, rw finset.card_eq_zero at hi₁, rw hi₁, 
    have: ∃ (f : ℕ → (ℕ × set ℕ × α)), 
            (∀ i, (∀ v ∈ rset' r (f i).2.1, c (insert (f i).1 v) = (f i).2.2) ∧ 
                  set.infinite ((f i).2.1) ∧ 
                  (f i).2.2 ∈ K ∧ (f i).2.1 ⊆ M₁ ∧ (f i).1 ∈ M₁) ∧
            (∀ i j, i < j → (f i).1 < (f j).1 ∧ (f j).1 ∈ (f i).2.1 ∧ (f j).2.1 ⊆ (f i).2.1), 
    { obtain ⟨g, hg⟩ := crec' nat.lt_wf 
          (λ _ _ _ (x y : { z : ℕ × set ℕ × α // (∀ v ∈ rset' r z.2.1, c (insert z.1 v) = z.2.2) ∧ 
                                                  set.infinite z.2.1 ∧ z.2.2 ∈ K ∧ z.2.1 ⊆ M₁ ∧ z.1 ∈ M₁}), 
                            x.1.1 < y.1.1 ∧ y.1.1 ∈ x.1.2.1 ∧ y.1.2.1 ⊆ x.1.2.1) _,
      exact ⟨λ i, (g i).1, λ i, (g i).2, hg⟩,
      rintros i ⟨If, IH⟩,
      cases i, 
      { obtain ⟨v, hv⟩ := classical.indefinite_description _ (exists_mem_of_infinite _ hM₁),
        set c' : finset ℕ → α := λ F, c (insert v F),
        specialize ih c' (infinite_erase hM₁ v) _, swap, 
        { intros e he, apply h, split, rw [finset.card_insert_of_not_mem (λ t, (he.2 v t).2 rfl), he.1],
          rw finset.forall_mem_insert, exact ⟨hv, λ t ht, (he.2 t ht).1⟩ },
        obtain ⟨B₁, Bp⟩ := classical.indefinite_description _ ih, 
        obtain ⟨B₁sub, B₁inf, colp⟩ := classical.indefinite_description _ Bp, clear Bp,
        obtain ⟨col, colp2⟩ := classical.indefinite_description _ colp, clear colp,
        obtain ⟨colk, mono⟩ := classical.indefinite_description _ colp2, clear colp2,
        refine ⟨⟨⟨v, B₁, col⟩, mono, B₁inf, colk, λ t ht, (B₁sub ht).1, hv⟩, λ i hi, (not_lt_of_le (zero_le i) hi).elim⟩ },
      set If' := (If i (nat.lt_succ_self i)),
      set ai := If'.1.1,
      set Bi := If'.1.2.1,
      rcases If'.2 with ⟨mono, infBi, colk, subM, memM⟩, 
      obtain ⟨v, hv₁, hv₂⟩ := classical.indefinite_description _ (exists_mem_of_infinite _ (infinite_above_of_infinite _ infBi ai)),
      set c' : finset ℕ → α := λ F, c (insert v F),
      specialize ih c' (infinite_erase infBi v) _, swap, 
      { intros e he, apply h, split, rw [finset.card_insert_of_not_mem (λ t, (he.2 v t).2 rfl), he.1], 
        rw finset.forall_mem_insert, exact ⟨subM hv₁, λ t ht, subM (he.2 t ht).1⟩ }, 
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
    rcases this with ⟨f, f', lt'⟩, 
    set a := λ i, (f i).1,
    obtain ⟨col', colltk, inft⟩ := infinite_pigeonhole (λ (col : α), {i : ℕ | (f i).2.2 = col}) {x | x ∈ K} (finite_mem_finset K) _,
      swap, convert infinite_univ_nat, ext t, simp, apply (f' t).2.2.1,
    have mono_a : strict_mono a, intros x y r, exact (lt' x y r).1,
    refine ⟨a '' {i : ℕ | (f i).2.2 = col'}, _, _, col', colltk, _⟩, 
      apply mem_image_elim, intros x hx, exact (f' x).2.2.2.2,
      intro, apply inft, apply finite_of_finite_image _ a_1, 
      apply inj_on_of_injective, apply strict_mono.injective mono_a, 
    rintros e ⟨he₁, he₂⟩, 
    have he: e ≠ ∅, intro a_1, rw [a_1, finset.card_empty] at he₁, apply nat.succ_ne_zero _ he₁.symm, 
    set e₁ := finset.min' e he,
    have := he₂ e₁ (finset.min'_mem _ _), rcases this with ⟨i₁, h₁, h₂⟩, 
    convert (f' i₁).1 (finset.erase e e₁) _, 
    rw ← h₂, rw finset.insert_erase, 
    convert (finset.min'_mem _ _), exact h₁.symm,
    split, rw finset.card_erase_of_mem, rw he₁, refl, apply finset.min'_mem, 
    intros t ht, simp [-ne.def] at ht, rcases he₂ t ht.2 with ⟨_, _, rfl⟩, 
    have: e₁ < a w, apply lt_of_le_of_ne _ ht.1.symm, apply finset.min'_le _ _ _ ht.2, 
    apply (lt' _ _ _).2.1, 
    rwa [← strict_mono.lt_iff_lt mono_a, h₂], 
  end

end ramsey