import algebra.geom_sum
import data.finset
import data.fintype
import tactic
import to_mathlib
import basic
import shadows
import colex

open fintype
open finset
open nat

variable {α : Type*}
variables [decidable_eq α] -- [decidable_linear_order α]

variables {n : ℕ}
local notation `X` := fin n

namespace UV
section 
  variables (U V : finset X)
  
  -- We'll only use this when |U| = |V| and U ∩ V = ∅
  def compress (U V : finset α) (A : finset α) :=
  if disjoint U A ∧ (V ⊆ A)
    then (A ∪ U) \ V
    else A

  lemma compress_size (U V : finset α) (A : finset α) (h₁ : U.card = V.card) : (compress U V A).card = A.card :=
  begin
    rw compress, split_ifs, 
      rw [card_sdiff (subset.trans h.2 (subset_union_left _ _)), card_disjoint_union h.1.symm, h₁, nat.add_sub_cancel], 
    refl
  end

  lemma compress_idem (U V : finset α) (A : finset α) : compress U V (compress U V A) = compress U V A :=
  begin
    simp only [compress], 
    split_ifs,
      suffices: U = ∅,
        rw [this, union_empty, union_empty, sdiff_idem],
      have: U \ V = U := sdiff_eq_self_of_disjoint (disjoint_of_subset_right h.2 h.1),
      rw ← disjoint_self_iff_empty,
      apply disjoint_of_subset_right (subset_union_right (A\V) _),
      rw [union_sdiff_distrib_right, ‹U \ V = U›] at h_1,
    all_goals { tauto }
  end

  @[reducible]
  def compress_remains (U V : finset α) (𝒜 : finset (finset α)) : finset (finset α) := 𝒜.filter (λ A, compress U V A ∈ 𝒜)
  @[reducible]
  def compress_motion (U V : finset α) (𝒜 : finset (finset α)) : finset (finset α) := (𝒜.filter (λ A, compress U V A ∉ 𝒜)).image (λ A, compress U V A)

  def compress_family (U V : finset α) (𝒜 : finset (finset α)) : finset (finset α) :=
  compress_motion U V 𝒜 ∪ compress_remains U V 𝒜

  lemma mem_compress_remains  {𝒜 : finset (finset α)} (U V : finset α) (A : finset α) : A ∈ compress_remains U V 𝒜 ↔ A ∈ 𝒜 ∧ compress U V A ∈ 𝒜 :=
  by rw mem_filter

  lemma mem_compress_motion {𝒜 : finset (finset α)} (U V : finset α) (A : finset α) : A ∈ compress_motion U V 𝒜 ↔ A ∉ 𝒜 ∧ (∃ B ∈ 𝒜, compress U V B = A) :=
  begin
    simp [compress_motion], 
    split; rintro ⟨p, q, r⟩,
      exact ⟨r ▸ q.2, p, ⟨q.1, r⟩⟩,
    exact ⟨q, ⟨r.1, r.2.symm ▸ p⟩, r.2⟩, 
  end

  @[reducible]
  def is_compressed (U V : finset α) (𝒜 : finset (finset α)) : Prop := compress_family U V 𝒜 = 𝒜

  lemma is_compressed_empty (𝒜 : finset (finset α)) : is_compressed ∅ ∅ 𝒜 := 
  begin
    have q: ∀ (A : finset α), compress ∅ ∅ A = A,
      simp [compress],
    simp [is_compressed, compress_family, ext, q]
  end

  lemma mem_compress {𝒜 : finset (finset α)} (U V : finset α) {A : finset α} : 
    A ∈ compress_family U V 𝒜 ↔ (A ∉ 𝒜 ∧ (∃ B ∈ 𝒜, compress U V B = A)) ∨ (A ∈ 𝒜 ∧ compress U V A ∈ 𝒜) :=
  by rw [compress_family, mem_union, mem_compress_remains, mem_compress_motion]

  lemma compress_family_size (r : ℕ) (𝒜 : finset (finset α)) (U V : finset α) (h₁ : U.card = V.card) (h₂ : all_sized 𝒜 r) : 
    all_sized (compress_family U V 𝒜) r :=
  begin
    intros A HA,
    rw mem_compress at HA, 
    rcases HA with ⟨_, _, z₁, rfl⟩ | ⟨z₁, _⟩,
      rw compress_size _ _ _ h₁, 
    all_goals {apply h₂ _ z₁}
  end

  lemma compress_family_idempotent (U V : finset α) (𝒜 : finset (finset α)) : compress_family U V (compress_family U V 𝒜) = compress_family U V 𝒜 :=
  begin
    have: ∀ A ∈ compress_family U V 𝒜, compress U V A ∈ compress_family U V 𝒜,
      intros A HA,
      rw mem_compress at HA ⊢,
      simp [compress_idem], 
      rcases HA with ⟨_, B, _, rfl⟩ | ⟨_, _⟩,
        left, refine ⟨_, B, ‹_›, _⟩; rwa compress_idem,
      right, assumption,
    have: filter (λ A, compress U V A ∉ compress_family U V 𝒜) (compress_family U V 𝒜) = ∅,
      rw ← filter_false (compress_family U V 𝒜),
      apply filter_congr,
      simpa,
    rw [compress_family, compress_motion, this, image_empty, union_comm, compress_remains, ← this],
    apply filter_union_filter_neg_eq (compress_family U V 𝒜)
  end

  lemma compress_disjoint {𝒜 : finset (finset α)} (U V : finset α) : disjoint (compress_motion U V 𝒜) (compress_remains U V 𝒜) :=
  begin
    rw disjoint_left,
    intros A HA HB,
    rw mem_compress_remains at HB,
    rw mem_compress_motion at HA,
    exact HA.1 HB.1
  end

  lemma inj_ish {U V : finset α} {A B : finset α} (hA : disjoint U A ∧ V ⊆ A) (hB : disjoint U B ∧ V ⊆ B)
    (Z : (A ∪ U) \ V = (B ∪ U) \ V) : A = B :=
  begin
    ext x, split,
    all_goals {
      intro p,
      by_cases h₁: (x ∈ V), { exact hB.2 h₁ <|> exact hA.2 h₁ },
      have := mem_sdiff.2 ⟨mem_union_left U ‹_›, h₁⟩,
      rw Z at this <|> rw ← Z at this,
      rw [mem_sdiff, mem_union] at this,
      suffices: x ∉ U, tauto,
      apply disjoint_right.1 ‹disjoint _ _ ∧ _›.1 p }
  end

  lemma compressed_size {𝒜 : finset (finset α)} (U V : finset α) : (compress_family U V 𝒜).card = 𝒜.card :=
  begin
    rw [compress_family, card_disjoint_union (compress_disjoint _ _), card_image_of_inj_on],
      rw [← card_disjoint_union, union_comm, filter_union_filter_neg_eq],
      rw [disjoint_iff_inter_eq_empty, inter_comm],
      apply filter_inter_filter_neg_eq,
    intros A HA B HB Z,
    rw mem_filter at HA HB,
    rw compress at HA Z,
    split_ifs at HA Z,
      rw compress at HB Z,
      split_ifs at HB Z,
        exact inj_ish h h_1 Z,
      tauto,
    tauto
  end

  lemma compress_held {𝒜 : finset (finset α)} {U V : finset α} {A : finset α} (h₁ : A ∈ compress_family U V 𝒜) (h₂ : V ⊆ A) (h₃ : U.card = V.card) : A ∈ 𝒜 :=
  begin
    rw mem_compress at h₁,
    rcases h₁ with ⟨_, B, H, HB⟩ | _,
      rw compress at HB,
      split_ifs at HB,
        have: V = ∅,
          apply eq_empty_of_forall_not_mem,
          intros x xV, replace h₂ := h₂ xV, 
          rw [← HB, mem_sdiff] at h₂, exact h₂.2 xV,
        have: U = ∅,
          rwa [← card_eq_zero, h₃, card_eq_zero],
        rw [‹U = ∅›, ‹V = ∅›, union_empty, sdiff_empty] at HB,
        rwa ← HB, 
      rwa ← HB,
    tauto,
  end

  lemma compress_moved {𝒜 : finset (finset α)} {U V : finset α} {A : finset α} (h₁ : A ∈ compress_family U V 𝒜) (h₂ : A ∉ 𝒜) : U ⊆ A ∧ disjoint V A ∧ (A ∪ V) \ U ∈ 𝒜 :=
  begin
    rw mem_compress at h₁,
    rcases h₁ with ⟨_, B, H, HB⟩ | _,
    { rw compress at HB,
      split_ifs at HB, { 
        rw ← HB at *,
        refine ⟨_, disjoint_sdiff, _⟩,
          have: disjoint U V := disjoint_of_subset_right h.2 h.1,
          rw union_sdiff_distrib_right, rw sdiff_eq_self_of_disjoint this, apply subset_union_right _ _,
        rwa [sdiff_union_of_subset, union_sdiff_self, sdiff_eq_self_of_disjoint h.1.symm],
        apply trans h.2 (subset_union_left _ _)},
      { rw HB at *, tauto } },
    tauto
  end

  lemma uncompressed_was_already_there {𝒜 : finset (finset α)} {U V : finset α} {A : finset α} (h₁ : A ∈ compress_family U V 𝒜) (h₂ : V ⊆ A) (h₃ : disjoint U A) : (A ∪ U) \ V ∈ 𝒜 :=
  begin
    rw mem_compress at h₁,
    have: disjoint U A ∧ V ⊆ A := ⟨h₃, h₂⟩,
    rcases h₁ with ⟨_, B, B_in_A, cB_eq_A⟩ | ⟨_, cA_in_A⟩,
    { by_cases a: (A ∪ U) \ V = A,
        have: U \ V = U := sdiff_eq_self_of_disjoint (disjoint_of_subset_right h₂ h₃),
        have: U = ∅,
          rw ← disjoint_self_iff_empty,
          suffices: disjoint U (U \ V), rw ‹U \ V = U› at this, assumption,
          apply disjoint_of_subset_right (subset_union_right (A\V) _),
          rwa [← union_sdiff_distrib_right, a],
        have: V = ∅,
          rw ← disjoint_self_iff_empty, apply disjoint_of_subset_right h₂,
          rw ← a, apply disjoint_sdiff,
        simpa [a, cB_eq_A.symm, compress, ‹U = ∅›, ‹V = ∅›],
      have: compress U V A = (A ∪ U) \ V,
        rw compress, split_ifs, refl,
      exfalso,
      apply a,
      rw [← this, ← cB_eq_A, compress_idem] },
    { rw compress at cA_in_A,
      split_ifs at cA_in_A,
      assumption }
  end

  lemma compression_reduces_shadow {𝒜 : finset (finset α)} {U V : finset α} (h₁ : ∀ x ∈ U, ∃ y ∈ V, is_compressed (erase U x) (erase V y) 𝒜) (h₂ : U.card = V.card) : 
    (∂ compress_family U V 𝒜).card ≤ (∂𝒜).card := 
  begin
    set 𝒜' := compress_family U V 𝒜,
    suffices: (∂𝒜' \ ∂𝒜).card ≤ (∂𝒜 \ ∂𝒜').card,
      suffices z: card (∂𝒜' \ ∂𝒜 ∪ ∂𝒜' ∩ ∂𝒜) ≤ card (∂𝒜 \ ∂𝒜' ∪ ∂𝒜 ∩ ∂𝒜'),
        rwa [sdiff_union_inter, sdiff_union_inter] at z,
      rw [card_disjoint_union, card_disjoint_union, inter_comm],
      apply add_le_add_right ‹_›,
      any_goals { apply sdiff_inter_inter },
    
    have q₁: ∀ B ∈ ∂𝒜' \ ∂𝒜, U ⊆ B ∧ disjoint V B ∧ (B ∪ V) \ U ∈ ∂𝒜 \ ∂𝒜',
      intros B HB,
      obtain ⟨k, k'⟩: B ∈ ∂𝒜' ∧ B ∉ ∂𝒜 := mem_sdiff.1 HB,
      have m: ∀ y ∉ B, insert y B ∉ 𝒜 := λ y H a, k' (mem_shadow'.2 ⟨y, H, a⟩),
      rcases mem_shadow'.1 k with ⟨x, _, _⟩,
      have q := compress_moved ‹insert x B ∈ 𝒜'› (m _ ‹x ∉ B›),
      have: disjoint V B := (disjoint_insert_right.1 q.2.1).2,
      have: disjoint V U := disjoint_of_subset_right q.1 q.2.1,
      have: V \ U = V := sdiff_eq_self_of_disjoint ‹_›,
      have: x ∉ U,
        intro a, 
        rcases h₁ x ‹x ∈ U› with ⟨y, Hy, xy_comp⟩,
        apply m y (disjoint_left.1 ‹disjoint V B› Hy),
        rw is_compressed at xy_comp,
        have: (insert x B ∪ V) \ U ∈ compress_family (erase U x) (erase V y) 𝒜, rw xy_comp, exact q.2.2,
        have: ((insert x B ∪ V) \ U ∪ erase U x) \ erase V y ∈ 𝒜,
          apply uncompressed_was_already_there this _ (disjoint_of_subset_left (erase_subset _ _) disjoint_sdiff),
            rw [union_sdiff_distrib_right, ‹V \ U = V›],
            apply subset.trans (erase_subset _ _) (subset_union_right _ _), 
        suffices: ((insert x B ∪ V) \ U ∪ erase U x) \ erase V y = insert y B,
          rwa ← this,
        have: x ∉ B ∪ V := λ z, disjoint_left.1 ‹disjoint V U› (or.resolve_left (mem_union.1 z) ‹x ∉ B›) ‹x ∈ U›,
        have: erase U x ⊆ insert x B ∪ V := (trans (erase_subset x _) (trans q.1 (subset_union_left _ V))),
        by calc (((insert x B ∪ V) \ U) ∪ erase U x) \ erase V y 
            = (((insert x B ∪ V) \ finset.singleton x ∪ erase U x) ∩ ((insert x B ∪ V) \ erase U x ∪ erase U x)) \ erase V y : 
                                  by rw [← union_distrib_right, ← sdiff_union_distrib_left, union_singleton_eq_insert, insert_erase a]
        ... = (B ∪ V) \ erase V y : 
                                  by rw [sdiff_union_of_subset ‹erase U x ⊆ _›, sdiff_singleton_eq_erase, insert_union, erase_insert ‹x ∉ B ∪ V›, ← union_singleton_eq_insert, union_comm, ← union_distrib_right, inter_singleton_of_not_mem (not_mem_erase _ _), empty_union]
        ... = (insert y B ∪ erase V y) \ erase V y :  
                                  by rw [← union_singleton_eq_insert, union_comm _ B, union_assoc, union_singleton_eq_insert, insert_erase ‹y ∈ V›]
        ... = insert y B : 
                                  begin rw [union_sdiff_self, sdiff_eq_self_iff_disjoint, disjoint_insert_left], refine ⟨not_mem_erase _ _, disjoint_of_subset_right (erase_subset _ _) ‹disjoint V B›.symm⟩ end,                 
      have: U ⊆ B, rw [← erase_eq_of_not_mem ‹x ∉ U›, ← subset_insert_iff], exact q.1,
      refine ⟨‹_›, ‹_›, _⟩,
      rw mem_sdiff,
      have: x ∉ V := disjoint_right.1 q.2.1 (mem_insert_self _ _),
      split,
        rw mem_shadow',
        refine ⟨x, _, _⟩,
        { simp [mem_sdiff, mem_union], tauto! },
        convert q.2.2,
        rw [← union_singleton_eq_insert, ← union_singleton_eq_insert, union_assoc, union_sdiff_distrib_right _ (B ∪ V), sdiff_eq_self_of_disjoint (singleton_disjoint.2 ‹x ∉ U›)], 
      rw mem_shadow',
      rintro ⟨w, _, _⟩,
      by_cases (w ∈ U),
        rcases h₁ w ‹w ∈ U› with ⟨z, Hz, xy_comp⟩,
        apply m z (disjoint_left.1 ‹disjoint V B› Hz),
        have: insert w ((B ∪ V) \ U) ∈ 𝒜, {
          apply compress_held a_h_h _ h₂, 
          apply subset.trans _ (subset_insert _ _),
          rw union_sdiff_distrib_right, rw ‹V \ U = V›, apply subset_union_right },
        have: (insert w ((B ∪ V) \ U) ∪ erase U w) \ erase V z ∈ 𝒜,
          refine uncompressed_was_already_there _ _ _, 
              rw is_compressed at xy_comp,
              rwa xy_comp,
            apply subset.trans (erase_subset _ _),
            apply subset.trans _ (subset_insert _ _),
            rw union_sdiff_distrib_right,
            rw ‹V \ U = V›,
            apply subset_union_right,
          rw disjoint_insert_right,
          split, apply not_mem_erase,
          apply disjoint_of_subset_left (erase_subset _ _),
          apply disjoint_sdiff,
        have: (insert w ((B ∪ V) \ U) ∪ erase U w) \ erase V z = insert z B,
        by calc (insert w ((B ∪ V) \ U) ∪ erase U w) \ erase V z = (((B ∪ V) \ U) ∪ (finset.singleton w ∪ erase U w)) \ erase V z : begin rw [← union_singleton_eq_insert, union_left_comm, union_assoc] end
        ... = (((B ∪ V) \ U) ∪ U) \ erase V z : begin congr, rw union_singleton_eq_insert, rw insert_erase h end
        ... = (B ∪ V) \ erase V z : begin rw sdiff_union_of_subset, apply subset.trans ‹U ⊆ B› (subset_union_left _ _) end
        ... = B \ erase V z ∪ V \ erase V z : begin rw union_sdiff_distrib_right end
        ... = B ∪ V \ erase V z : begin congr, rw sdiff_eq_self_iff_disjoint, apply disjoint_of_subset_right (erase_subset _ _) ‹disjoint V B›.symm end
        ... = B ∪ finset.singleton z : begin congr, ext, simp, split, intro p, by_contra, exact p.2 ‹_› p.1, intro p, rw p, tauto end
        ... = insert z B : begin rw [union_comm, union_singleton_eq_insert] end,
        rwa ← this,
      rw [mem_sdiff, ← not_imp, not_not] at a_h_w,
      have: w ∉ V := h ∘ a_h_w ∘ mem_union_right _,
      have: w ∉ B := h ∘ a_h_w ∘ mem_union_left _,
      apply m w this,
      
      have: (insert w ((B ∪ V) \ U) ∪ U) \ V ∈ 𝒜, 
        refine uncompressed_was_already_there ‹insert w ((B ∪ V) \ U) ∈ 𝒜'› (trans _ (subset_insert _ _)) _,
          rw [union_sdiff_distrib_right, ‹V \ U = V›], apply subset_union_right,
          rw disjoint_insert_right,
          exact ⟨‹_›, disjoint_sdiff⟩,
      convert this,
      rw [insert_union, sdiff_union_of_subset (trans ‹U ⊆ B› (subset_union_left _ _)), ← insert_union, union_sdiff_self], symmetry,
      rw [sdiff_eq_self_iff_disjoint, disjoint_insert_left],
      split, assumption,
      rwa disjoint.comm,
    apply card_le_card_of_inj_on (λ B, (B ∪ V) \ U) (λ B HB, (q₁ B HB).2.2),
    intros B₁ HB₁ B₂ HB₂ k,
    exact inj_ish ⟨(q₁ B₁ HB₁).2.1, (q₁ B₁ HB₁).1⟩ ⟨(q₁ B₂ HB₂).2.1, (q₁ B₂ HB₂).1⟩ k
  end

  instance thing (A B : finset X) : decidable (A <ᶜ B) := by apply_instance

  lemma compression_reduces_set [decidable_linear_order α] {U V : finset α} {hU : U ≠ ∅} {hV : V ≠ ∅} (A : finset α) (h : max' U hU < max' V hV): 
    compress U V A ≠ A → compress U V A <ᶜ A :=
  begin
    rw compress, split_ifs with h₁; intro h₂, any_goals {exfalso, apply h₂, refl}, 
    refine ⟨max' V hV, _, not_mem_sdiff_of_mem_right (max'_mem _ _), h₁.2 (max'_mem _ _)⟩, 
    intros x hx, 
    have xV: x ∉ V := λ z, not_le_of_lt hx (le_max' _ _ _ z),
    have xU: x ∉ U := λ z, not_le_of_lt hx (trans (le_max' _ _ _ z) (le_of_lt h)), 
    simp [xU, xV]
  end

  lemma binary_sum_nat {k : ℕ} {A : finset ℕ} (h₁ : ∀ {x}, x ∈ A → x < k) : A.sum (pow 2) < 2^k :=
  begin
    apply lt_of_le_of_lt (sum_le_sum_of_subset (λ t, mem_range.2 ∘ h₁)),
    have z := geom_sum_mul_add 1 k, rw [geom_series, mul_one] at z, 
    simp only [nat.pow_eq_pow] at z, rw ← z, apply nat.lt_succ_self
  end
  lemma binary_iff (A B : finset ℕ) : A.sum (pow 2) < B.sum (pow 2) ↔ A <ᶜ B:=
  begin
    have z: ∀ (A B : finset ℕ), A <ᶜ B → A.sum (pow 2) < B.sum (pow 2),
      rintro A B ⟨k, maxi, notinA, inB⟩,
      have AeqB: A.filter (λ x, ¬(x ≤ k)) = B.filter (λ x, ¬(x ≤ k)),
      { ext t, by_cases h: (k < t); simp [h], apply maxi h },
      have Alt: (A.filter (λ x, x ≤ k)).sum (pow 2) < pow 2 k :=
        binary_sum_nat (λ _, (λ th, lt_of_le_of_ne (and.right th) (ne_of_mem_of_not_mem th.left notinA)) ∘ mem_filter.1), 
      have leB: pow 2 k ≤ (B.filter (λ x, x ≤ k)).sum (pow 2),
      { apply single_le_sum (λ _ _, nat.zero_le _) (mem_filter.2 ⟨inB, _⟩), refl },
      have := add_lt_add_right (lt_of_lt_of_le Alt leB) ((filter (λ x, ¬(x ≤ k)) A).sum (pow 2)),
      rwa [← sum_union, filter_union_filter_neg_eq, AeqB, ← sum_union, filter_union_filter_neg_eq] at this, 
      any_goals { rw disjoint_iff_inter_eq_empty, apply filter_inter_filter_neg_eq },
    refine ⟨λ h, (trichotomous A B).resolve_right (λ h₁, h₁.elim _ (λ q, not_lt_of_gt h (z _ _ q))), z A B⟩, 
    rintro rfl, apply irrefl _ h
  end
  def family_measure_fin (𝒜 : finset (finset (fin n))) : ℕ := 𝒜.sum (λ A, (A.image fin.val).sum (pow 2))

  lemma compression_reduces_family {U V : finset (fin n)} {hU : U ≠ ∅} {hV : V ≠ ∅} (h : max' U hU < max' V hV) (𝒜 : finset (finset (fin n))) : 
    compress_family U V 𝒜 ≠ 𝒜 → family_measure_fin (compress_family U V 𝒜) < family_measure_fin 𝒜 :=
  begin
    rw [compress_family], 
    have q: ∀ Q ∈ filter (λ A, compress U V A ∉ 𝒜) 𝒜, compress U V Q ≠ Q,
      intros Q HQ, rw mem_filter at HQ, apply (ne_of_mem_of_not_mem HQ.1 HQ.2).symm, 
    intro,
    set CA₁ := filter (λ A, compress U V A ∈ 𝒜) 𝒜,
    have uA: CA₁ ∪ filter (λ A, compress U V A ∉ 𝒜) 𝒜 = 𝒜 := filter_union_filter_neg_eq _, 
    have ne₂: filter (λ A, compress U V A ∉ 𝒜) 𝒜 ≠ ∅, intro z, rw [compress_motion, z, image_empty, empty_union] at a, rw [z, union_empty] at uA, exact a uA,
    rw [family_measure_fin, family_measure_fin, sum_union (compress_disjoint U V)], 
    conv_rhs {rw ← uA}, 
    rw [sum_union, add_comm, add_lt_add_iff_left, sum_image], 
    apply sum_lt_sum ne₂, 
    intros A hA, 
    rw binary_iff, 
    rw colex_hom_fin,
    apply compression_reduces_set A h (q _ hA), 
    intros x Hx y Hy k,
    have cx := q x Hx, 
    have cy := q y Hy, 
    rw compress at k cx, split_ifs at k cx, 
      rw compress at k cy, split_ifs at k cy,
        exact inj_ish h_1 h_2 k, 
      exfalso, apply cy rfl,
    exfalso, apply cx rfl, 
    rw disjoint_iff_inter_eq_empty,
    apply filter_inter_filter_neg_eq
  end

  def gamma [decidable_linear_order α] : rel (finset α) (finset α) := (λ U V, ∃ (HU : U ≠ ∅), ∃ (HV : V ≠ ∅), disjoint U V ∧ finset.card U = finset.card V ∧ max' U HU < max' V HV)

  lemma min_ne_max_of_card [decidable_linear_order α] {U : finset α} (h₁ : U ≠ ∅) (h₂ : 1 < card U) : min' U h₁ ≠ max' U h₁ := 
  begin
    intro,
    apply not_le_of_lt h₂, 
    apply le_of_eq, 
    rw card_eq_one,
    use max' U h₁,
    rw eq_singleton_iff_unique_mem,
    exact ⟨max'_mem _ _, λ t Ht, le_antisymm (le_max' U h₁ t Ht) (a ▸ min'_le U h₁ t Ht)⟩
  end

  lemma compression_improved {r : ℕ} (U V : finset (fin n)) (𝒜 : finset (finset (fin n))) (h : all_sized 𝒜 r) (h₁ : gamma U V) 
    (h₂ : ∀ U₁ V₁, gamma U₁ V₁ ∧ U₁.card < U.card → is_compressed U₁ V₁ 𝒜) (h₃ : ¬ is_compressed U V 𝒜): 
    family_measure_fin (compress_family U V 𝒜) < family_measure_fin 𝒜 ∧ (compress_family U V 𝒜).card = 𝒜.card ∧ all_sized (compress_family U V 𝒜) r ∧ (∂ compress_family U V 𝒜).card ≤ (∂𝒜).card := 
  begin
    rcases h₁ with ⟨Uh, Vh, UVd, same_size, max_lt⟩,
    refine ⟨compression_reduces_family max_lt _ h₃, compressed_size _ _, _, _⟩,
    apply compress_family_size _ _ _ _ same_size h, 
    apply compression_reduces_shadow _ same_size,
    intros x Hx, refine ⟨min' V Vh, min'_mem _ _, _⟩,
    cases lt_or_le 1 U.card with p p,
    { apply h₂,
      refine ⟨⟨_, _, _, _, _⟩, card_erase_lt_of_mem Hx⟩,
      { rwa [← card_pos, card_erase_of_mem Hx, nat.lt_pred_iff] },
      { rwa [← card_pos, card_erase_of_mem (min'_mem _ _), ← same_size, nat.lt_pred_iff] },
      { apply disjoint_of_subset_left (erase_subset _ _), apply disjoint_of_subset_right (erase_subset _ _), assumption },
      { rw [card_erase_of_mem (min'_mem _ _), card_erase_of_mem Hx, same_size] },
      { apply lt_of_le_of_lt (max'_le (erase U x) _ _ (λ y, le_max' U Uh y ∘ mem_of_mem_erase)), 
        apply lt_of_lt_of_le max_lt (le_max' _ _ _ _),
        rw mem_erase, refine ⟨(min_ne_max_of_card _ _).symm, max'_mem _ _⟩, 
        rwa ← same_size } },
    rw ← card_pos at Uh,
    replace p: card U = 1 := le_antisymm p Uh,
    rw p at same_size,
    have: erase U x = ∅,
      rw [← card_eq_zero, card_erase_of_mem Hx, p], refl,
    have: erase V (min' V Vh) = ∅,
      rw [← card_eq_zero, card_erase_of_mem (min'_mem _ _), ← same_size], refl,
    rw [‹erase U x = ∅›, ‹erase V (min' V Vh) = ∅›],
    apply is_compressed_empty
  end

  instance thing2 [decidable_linear_order α] (U V : finset α) : decidable (gamma U V) := by rw gamma; apply_instance
  -- instance thing2 (U V : finset ℕ) (A : finset (finset ℕ)) : decidable (is_compressed U V A) := by rw is_compressed; apply_instance

  lemma kruskal_katona_helper (r : ℕ) (𝒜 : finset (finset (fin n))) (h : all_sized 𝒜 r) : 
    ∃ (ℬ : finset (finset (fin n))), (∂ℬ).card ≤ (∂𝒜).card ∧ 𝒜.card = ℬ.card ∧ all_sized ℬ r ∧ (∀ U V, gamma U V → is_compressed U V ℬ) := 
  begin
    refine @well_founded.recursion _ _ (measure_wf family_measure_fin) (λ (A : finset (finset (fin n))), all_sized A r → ∃ B, (∂B).card ≤ (∂A).card ∧ A.card = B.card ∧ all_sized B r ∧ ∀ (U V : finset X), gamma U V → is_compressed U V B) _ _ h,
    intros A ih z,
    set usable: finset (finset (fin n) × finset (fin n)) := filter (λ t, gamma t.1 t.2 ∧ ¬ is_compressed t.1 t.2 A) ((powerset univ).product (powerset univ)), 
    by_cases (usable = ∅),
      refine ⟨A, le_refl _, rfl, z, _⟩, intros U V k,
      rw eq_empty_iff_forall_not_mem at h,
      by_contra,
      apply h ⟨U,V⟩,
      simp [a, k], exact ⟨subset_univ _, subset_univ _⟩,
    rcases exists_min usable (λ t, t.1.card) ((nonempty_iff_ne_empty _).2 h) with ⟨⟨U,V⟩, uvh, t⟩, rw mem_filter at uvh,
    have h₂: ∀ U₁ V₁, gamma U₁ V₁ ∧ U₁.card < U.card → is_compressed U₁ V₁ A,
      intros U₁ V₁ h, by_contra, 
      apply not_le_of_gt h.2 (t ⟨U₁, V₁⟩ _),
      simp [h, a], exact ⟨subset_univ _, subset_univ _⟩,
    obtain ⟨small_measure, p2, layered, p1⟩ := compression_improved U V A z uvh.2.1 h₂ uvh.2.2, 
    rw [measure, inv_image] at ih, 
    rcases ih (compress_family U V A) small_measure layered with ⟨B, q1, q2, q3, q4⟩,
    exact ⟨B, trans q1 p1, trans p2.symm q2, q3, q4⟩
  end

  def is_init_seg_of_colex [has_lt α] (𝒜 : finset (finset α)) (r : ℕ) : Prop := all_sized 𝒜 r ∧ (∀ A ∈ 𝒜, ∀ B, B <ᶜ A ∧ B.card = r → B ∈ 𝒜)

  lemma init_seg_total [decidable_linear_order α] (𝒜₁ 𝒜₂ : finset (finset α)) (r : ℕ) (h₁ : is_init_seg_of_colex 𝒜₁ r) (h₂ : is_init_seg_of_colex 𝒜₂ r) : 𝒜₁ ⊆ 𝒜₂ ∨ 𝒜₂ ⊆ 𝒜₁ :=
  begin
    rw ← sdiff_eq_empty_iff_subset, rw ← sdiff_eq_empty_iff_subset,
    by_contra a, rw not_or_distrib at a, simp [exists_mem_iff_ne_empty.symm, exists_mem_iff_ne_empty.symm] at a,
    rcases a with ⟨⟨A, Ah₁, Ah₂⟩, ⟨B, Bh₁, Bh₂⟩⟩,
    rcases trichotomous_of (<ᶜ) A B with lt | eq | gt,
      { exact Ah₂ (h₂.2 B Bh₁ A ⟨lt, h₁.1 A Ah₁⟩) },
      { rw eq at Ah₁, exact Bh₂ Ah₁ },
      { exact Bh₂ (h₁.2 A Ah₁ B ⟨gt, h₂.1 B Bh₁⟩) },
  end

  lemma init_seg_of_compressed [decidable_linear_order α] (ℬ : finset (finset α)) (r : ℕ) (h₁ : all_sized ℬ r) (h₂ : ∀ U V, gamma U V → is_compressed U V ℬ): 
    is_init_seg_of_colex ℬ r := 
  begin
    refine ⟨h₁, _⟩,
    rintros B Bh A ⟨A_lt_B, sizeA⟩,
    by_contra a,
    set U := A \ B,
    set V := B \ A,
    have: A ≠ B, intro t, rw t at a, exact a Bh,
    have: disjoint U B ∧ V ⊆ B := ⟨sdiff_disjoint, sdiff_subset_left _ _⟩,
    have: disjoint V A ∧ U ⊆ A := ⟨sdiff_disjoint, sdiff_subset_left _ _⟩,
    have cB_eq_A: compress U V B = A,
    { rw compress, split_ifs, rw [union_sdiff_self_eq_union, union_sdiff_distrib_right, sdiff_eq_self_of_disjoint disjoint_sdiff, union_comm], 
      apply union_eq_left_of_subset,
      intro t, simp only [and_imp, not_and, mem_sdiff, not_not], exact (λ x y, y x) },
    have cA_eq_B: compress V U A = B,
    { rw compress, split_ifs, rw [union_sdiff_self_eq_union, union_sdiff_distrib_right, sdiff_eq_self_of_disjoint disjoint_sdiff, union_comm], 
      apply union_eq_left_of_subset,
      intro t, simp only [and_imp, not_and, mem_sdiff, not_not], exact (λ x y, y x) },
    have: card A = card B := trans sizeA (h₁ B Bh).symm,
    have hU: U ≠ ∅,
      { intro t, rw sdiff_eq_empty_iff_subset at t, have: A = B := eq_of_subset_of_card_le t (ge_of_eq ‹_›), rw this at a, exact a Bh },
    have hV: V ≠ ∅,
      { intro t, rw sdiff_eq_empty_iff_subset at t, have: B = A := eq_of_subset_of_card_le t (le_of_eq ‹_›), rw ← this at a, exact a Bh },
    have disj: disjoint U V,
      { exact disjoint_of_subset_left (sdiff_subset_left _ _) disjoint_sdiff },
    have smaller: max' U hU < max' V hV,
      { rcases lt_trichotomy (max' U hU) (max' V hV) with lt | eq | gt,
        { assumption },
        { exfalso, have: max' U hU ∈ U := max'_mem _ _, apply disjoint_left.1 disj this, rw eq, exact max'_mem _ _ },
        { exfalso, have z := compression_reduces_set A gt, rw cA_eq_B at z,
          apply asymm A_lt_B (z ‹A ≠ B›.symm) } },
    have: gamma U V,
    { refine ⟨hU, hV, disj, _, smaller⟩,
      have: card (A \ B ∪ A ∩ B) = card (B \ A ∪ B ∩ A),
        rwa [sdiff_union_inter, sdiff_union_inter],
      rwa [card_disjoint_union (sdiff_inter_inter _ _), card_disjoint_union (sdiff_inter_inter _ _), inter_comm, add_right_inj] at this
    },
    have Bcomp := h₂ U V this, rw is_compressed at Bcomp,
    suffices: compress U V B ∈ compress_family U V ℬ,
      rw [Bcomp, cB_eq_A] at this, exact a this,
    rw mem_compress, left, refine ⟨_, B, Bh, rfl⟩, rwa cB_eq_A, 
  end

  def all_under (A : finset ℕ) : finset (finset ℕ) := A.bind (λ k, filter (λ B, card A = card B) (image (λ B, B ∪ A.filter (λ x, x > k)) (powerset (range k))))
  def all_up_to (A : finset ℕ) : finset (finset ℕ) := all_under A ∪ finset.singleton A

  lemma mem_all_under (A : finset ℕ) (B : finset ℕ) : B ∈ all_under A ↔ card A = card B ∧ B <ᶜ A :=
  begin
    simp [all_under, colex_order], split,
      rintro ⟨k, kinA, ⟨lows, lows_small, rfl⟩, cards⟩,
      refine ⟨cards, k, _, _, kinA⟩, intros x hx, simp [hx], 
        convert false_or _, simp only [eq_iff_iff, iff_false], intro, apply not_lt_of_gt hx, rw ← mem_range, apply lows_small a,
      simp [kinA, not_or_distrib, le_refl], 
      intro, have := lows_small a, apply not_mem_range_self this, 
    rintro ⟨cards, k, z, knotinB, kinA⟩, 
    refine ⟨k, kinA, ⟨filter (λ x, x < k) B, _, _⟩, cards⟩, 
    intro, simp,
    ext, simp, split, 
      rintro (⟨a1l, a1r⟩ | ⟨a2l, a2r⟩), rwa z a1r, 
      exact a2l,
    intro, rcases (lt_or_gt_of_ne (ne_of_mem_of_not_mem a_1 knotinB)), 
      right, exact ⟨‹_›, h⟩, 
    left, rw ← z h, exact ⟨a_1, h⟩
  end

  lemma mem_all_up_to (A : finset ℕ) (B : finset ℕ) : B ∈ all_up_to A ↔ (card A = card B ∧ B <ᶜ A) ∨ B = A :=
  by simp [all_up_to, mem_all_under]; tauto

  def everything_up_to (A : finset X) : finset (finset X) := filter (λ (B : finset X), (A.card = B.card ∧ B <ᶜ A) ∨ A = B) (powerset univ)

  lemma mem_everything_up_to (A : finset X) (B : finset X) : B ∈ everything_up_to A ↔ (A.card = B.card ∧ B <ᶜ A) ∨ A = B :=
  begin
    rw everything_up_to, rw mem_filter, rw mem_powerset, split, tauto, 
    intro a, refine ⟨subset_univ _, a⟩,
  end
  lemma mem_everything_up_to' (A : finset X) (B : finset X) : B ∈ everything_up_to A ↔ A.card = B.card ∧ sum (B.image fin.val) (pow 2) ≤ sum (A.image fin.val) (pow 2) :=
  begin
    rw mem_everything_up_to, split, rintro (_ | _), split, exact a.1, apply le_of_lt, rw binary_iff, rw colex_hom_fin, exact a.2,
    rw a, simp,
    intro, rcases trichotomous_of (<ᶜ) A B with lt|rfl|gt,
    exfalso, apply not_lt_of_ge a.2, rw binary_iff, rwa colex_hom_fin,
    right, refl,
    left, exact ⟨a.1, gt⟩
  end

  lemma cast_under (A : finset X) : all_up_to (image fin.val A) = image (image fin.val) (everything_up_to A) := 
  begin
    ext B, simp [mem_everything_up_to, mem_all_up_to], split,
      rintro (_ | rfl),
      have z := a.2, rw colex_order at z, 
      have: ∀ x ∈ image fin.val A, x < n, simp, rintros x y _ rfl, exact y.2,
      have r := max_colex _ a.2 this,
      set B' := @attach_fin B n r, 
      have q: image fin.val B' = B, ext, simp, split, rintro ⟨x, _, rfl⟩, assumption, intro, refine ⟨⟨a_1, r _ a_2⟩, _⟩, simpa, 
      refine ⟨B', _, _⟩, left, split, rw card_attach_fin, rw card_image_of_inj_on at a, exact a.1, {intros _ _ _ _, apply fin.eq_of_veq},
      rw ← q at a, rw colex_hom_fin at a, exact a.2, assumption, 
      use A, split, right, refl, refl,
    rintro ⟨C, ⟨_, _⟩ | rfl, rfl⟩, 
      left, rw [card_image_of_inj_on, card_image_of_inj_on, colex_hom_fin], exact ⟨‹_›, ‹_›⟩,
      any_goals {intros _ _ _ _, apply fin.eq_of_veq},
    right, refl
  end

  lemma IS_iff_le_max (𝒜 : finset (finset X)) (r : ℕ) : 𝒜 ≠ ∅ ∧ is_init_seg_of_colex 𝒜 r ↔ ∃ (A : finset X), A ∈ 𝒜 ∧ A.card = r ∧ 𝒜 = everything_up_to A := 
  begin
    rw is_init_seg_of_colex, split, 
    { rintro ⟨ne, layer, IS⟩,
      rcases exists_max 𝒜 (λ A, sum (A.image fin.val) (pow 2)) ne with ⟨A, Ah, Ap⟩,
      refine ⟨A, Ah, layer A Ah, _⟩,
      ext B, split, intro p, rw mem_everything_up_to', 
        refine ⟨_, _⟩,
          convert layer A Ah, apply layer B p, 
        apply Ap _ p, 
      rw mem_everything_up_to, rintro (_ | rfl), 
        apply IS A Ah B ⟨a.2, _⟩, rw ← a.1, apply layer _ Ah, 
      exact Ah },
    { rintro ⟨A, Ah, Ac, rfl⟩,
      refine ⟨ne_empty_of_mem Ah, _, _⟩,
        intros B Bh, rw [mem_everything_up_to'] at Bh, rwa ← Bh.1, 
      intros B₁ Bh₁ B₂ Bh₂, rw mem_everything_up_to', split, convert Ac, exact Bh₂.2,
      rw mem_everything_up_to' at Bh₁, apply trans _ Bh₁.2, apply le_of_lt, rw binary_iff, rw colex_hom_fin, exact Bh₂.1 }
  end

  lemma up_to_is_IS {A : finset X} {r : ℕ} (h₁ : A.card = r) : is_init_seg_of_colex (everything_up_to A) r := 
  and.right $ (IS_iff_le_max _ _).2 
  (by refine ⟨A, _, h₁, rfl⟩; simp [mem_everything_up_to])

  lemma shadow_of_everything_up_to (A : finset X) (hA : A ≠ ∅) : ∂ (everything_up_to A) = everything_up_to (erase A (min' A hA)) :=
  begin
    ext B, simp [mem_shadow', mem_everything_up_to], split,
      rintro ⟨i, ih, ⟨p, ⟨k, z, _, _⟩⟩ | h⟩,
      { rw [card_insert_of_not_mem ih] at p,
        have cards: card (erase A (min' A hA)) = card B,
          rw [card_erase_of_mem (min'_mem _ _), p], refl,
        simp [cards], have: k ≠ i, rintro rfl, exact ‹k ∉ insert k B› (mem_insert_self _ _), 
        cases lt_or_gt_of_ne this, 
        { left, refine ⟨i, λ x hx, _, ih, _⟩, 
          { split; intro p, apply mem_erase_of_ne_of_mem, apply ne_of_gt (trans hx (lt_of_le_of_lt (min'_le _ _ _ ‹_›) h)), 
              rw ← z (trans h hx), apply mem_insert_of_mem p, 
            apply mem_of_mem_insert_of_ne _ (ne_of_gt hx), rw z (trans h hx), apply mem_of_mem_erase p },
          apply mem_erase_of_ne_of_mem, apply ne_of_gt (lt_of_le_of_lt _ h), apply min'_le, assumption,
          rw ← z h, apply mem_insert_self }, 
        { rcases lt_or_eq_of_le (min'_le _ hA _ ‹k ∈ A›) with h₁ | rfl,
            left, refine ⟨k, λ x hx, _, ‹k ∉ insert i B› ∘ mem_insert_of_mem, mem_erase_of_ne_of_mem (ne_of_gt h₁) ‹_›⟩, 
            simp [ne_of_gt (trans hx h₁)], rw ← z hx, rw mem_insert, simp [ne_of_gt (trans hx h)], 
          right, apply eq_of_subset_of_card_le _ (ge_of_eq cards), intros t ht, 
          rw [mem_erase] at ht, have: t ≠ i := ne_of_gt (lt_of_lt_of_le h (min'_le _ _ _ ht.2)), 
          rw ← z _ at ht, apply mem_of_mem_insert_of_ne ht.2 ‹t ≠ i›, apply lt_of_le_of_ne (min'_le _ _ _ ht.2), 
          symmetry, exact ht.1 } },
      { by_cases q: (i = min' A hA), 
          right, rw ← q, rw h, rw erase_insert ih, 
        left, split, rw card_erase_of_mem (min'_mem _ _), rw h, rw card_insert_of_not_mem ih, rw [add_comm, pred_one_add], 
        refine ⟨i, λ x hx, _, ih, mem_erase_of_ne_of_mem q (h.symm ▸ mem_insert_self _ _)⟩, rw mem_erase, split,
        intro, split, apply ne_of_gt, apply lt_of_le_of_lt _ hx, apply min'_le, rw h, apply mem_insert_self,
        rw h, apply mem_insert_of_mem a, rintro ⟨a, b⟩, rw h at b, apply mem_of_mem_insert_of_ne b (ne_of_gt hx) },
    rintro (⟨_, k, z, _, _⟩ | rfl), set j := min' (univ \ B) (ne_empty_of_mem (mem_sdiff.2 ⟨complete _, ‹_›⟩)), 
    have r: j ≤ k := min'_le _ _ _ _, 
    have: j ∉ B, have: j ∈ univ \ B := min'_mem _ _, rw mem_sdiff at this, exact this.2,
    have cards: card A = card (insert j B),
    { rw [card_insert_of_not_mem ‹j ∉ B›, ← ‹_ = card B›, card_erase_of_mem (min'_mem _ _), nat.pred_eq_sub_one, nat.sub_add_cancel], 
    apply nat.pos_of_ne_zero, rw ne, rw card_eq_zero, exact hA },
    refine ⟨j, ‹_›, _⟩, 
    rcases (lt_or_eq_of_le r) with r | r₁, 
    left, refine ⟨cards, _⟩,
    refine ⟨k, _, mt (λ t, mem_of_mem_insert_of_ne t (ne_of_gt r)) ‹k ∉ B›, mem_of_mem_erase ‹_›⟩, intros x hx, 
    rw mem_insert, rw z hx, simp [ne_of_gt (trans hx r), ne_of_gt (lt_of_le_of_lt (min'_le _ _ _ (mem_of_mem_erase ‹_›)) hx)], 
    right, apply eq_of_subset_of_card_le, intros t th, rcases lt_trichotomy k t with lt|eq|gt,
    { apply mem_insert_of_mem, rw z lt, apply mem_erase_of_ne_of_mem _ th, apply ne_of_gt (lt_of_le_of_lt _ lt), apply min'_le _ _ _ (mem_of_mem_erase ‹_›) },
    { rw [← eq, r₁], apply mem_insert_self },
    { apply mem_insert_of_mem, rw ← r₁ at gt, by_contra, apply not_lt_of_le (min'_le (univ \ B) _ t _) gt, rw mem_sdiff, exact ⟨complete _, a⟩ },
    apply ge_of_eq cards, rw mem_sdiff, exact ⟨complete _, ‹_›⟩, 
    refine ⟨min' A hA, not_mem_erase _ _, or.inr (insert_erase (min'_mem _ _)).symm⟩, 
  end

  lemma shadow_of_IS {𝒜 : finset (finset X)} (r : ℕ) (h₁ : is_init_seg_of_colex 𝒜 r) : is_init_seg_of_colex (∂𝒜) (r - 1) :=
  begin
    rcases nat.eq_zero_or_pos r with rfl | hr,
      have: 𝒜 ⊆ finset.singleton ∅,
        intros A hA, rw mem_singleton, rw ← card_eq_zero, apply h₁.1 A hA,  
      have := shadow_monotone this,
      squeeze_simp [all_removals, shadow, subset_empty] at this,
      simp [shadow, this, is_init_seg_of_colex, all_sized],
    by_cases h₂: 𝒜 = ∅,
      rw h₂, rw shadow_empty, rw is_init_seg_of_colex, rw all_sized, 
      squeeze_simp,
    replace h₁ := and.intro h₂ h₁,
    rw IS_iff_le_max at h₁,
    rcases h₁ with ⟨B, _, rfl, rfl⟩, 
    rw shadow_of_everything_up_to, 
      apply up_to_is_IS,
      rw card_erase_of_mem (min'_mem _ _), refl,
    rwa ← card_pos
  end
end
end UV

section KK
  theorem kruskal_katona (r : ℕ) (𝒜 𝒞 : finset (finset X)) : 
    all_sized 𝒜 r ∧ all_sized 𝒞 r ∧ 𝒜.card = 𝒞.card ∧ UV.is_init_seg_of_colex 𝒞 r 
  → (∂𝒞).card ≤ (∂𝒜).card :=
  begin
    rintros ⟨layerA, layerC, h₃, h₄⟩,
    rcases UV.kruskal_katona_helper r 𝒜 layerA with ⟨ℬ, _, t, layerB, fully_comp⟩,
    have: UV.is_init_seg_of_colex ℬ r := UV.init_seg_of_compressed ℬ r layerB fully_comp,
    suffices: 𝒞 = ℬ,
      rwa this at *,
    have z: card ℬ = card 𝒞 := t.symm.trans h₃,
    cases UV.init_seg_total ℬ 𝒞 r this h₄ with BC CB,
      symmetry, apply eq_of_subset_of_card_le BC (ge_of_eq z),
    apply eq_of_subset_of_card_le CB (le_of_eq z)
  end

  theorem strengthened (r : ℕ) (𝒜 𝒞 : finset (finset X)) : 
    all_sized 𝒜 r ∧ all_sized 𝒞 r ∧ 𝒞.card ≤ 𝒜.card ∧ UV.is_init_seg_of_colex 𝒞 r 
  → (∂𝒞).card ≤ (∂𝒜).card :=
  begin
    rintros ⟨Ar, Cr, cards, colex⟩,
    rcases exists_smaller_set 𝒜 𝒞.card cards with ⟨𝒜', prop, size⟩,
    have := kruskal_katona r 𝒜' 𝒞 ⟨λ A hA, Ar _ (prop hA), Cr, size, colex⟩,
    transitivity, exact this, apply card_le_of_subset, rw [shadow, shadow], apply shadow_monotone prop
  end

  theorem iterated (r k : ℕ) (𝒜 𝒞 : finset (finset X)) : 
    all_sized 𝒜 r ∧ all_sized 𝒞 r ∧ 𝒞.card ≤ 𝒜.card ∧ UV.is_init_seg_of_colex 𝒞 r 
  → (shadow^[k] 𝒞).card ≤ (shadow^[k] 𝒜).card :=
  begin
    revert r 𝒜 𝒞, induction k,
      intros, simp, exact a.2.2.1,
    rintros r A C ⟨z₁, z₂, z₃, z₄⟩, simp, apply k_ih (r-1), refine ⟨shadow_layer z₁, shadow_layer z₂, _, _⟩,
    apply strengthened r _ _ ⟨z₁, z₂, z₃, z₄⟩, 
    apply UV.shadow_of_IS _ z₄
  end

  theorem lovasz_form {r k i : ℕ} {𝒜 : finset (finset X)} (hir : i ≤ r) (hrk : r ≤ k) (hkn : k ≤ n) (h₁ : all_sized 𝒜 r) (h₂ : nat.choose k r ≤ 𝒜.card) : 
    nat.choose k (r-i) ≤ (shadow^[i] 𝒜).card :=
  begin
    set range'k : finset X := attach_fin (range k) (λ m, by rw mem_range; apply forall_lt_iff_le.2 hkn),
    set 𝒞 : finset (finset X) := powerset_len r (range'k),
    have Ccard: 𝒞.card = nat.choose k r,
      rw [card_powerset_len, card_attach_fin, card_range], 
    have: all_sized 𝒞 r, intros A HA, rw mem_powerset_len at HA, exact HA.2,
    suffices this: (shadow^[i] 𝒞).card = nat.choose k (r-i),
    { rw ← this, apply iterated r _ _ _ ⟨h₁, ‹all_sized 𝒞 r›, _, _⟩, 
      rwa Ccard, 
      refine ⟨‹_›, _⟩, rintros A HA B ⟨HB₁, HB₂⟩, 
      rw mem_powerset_len, refine ⟨_, ‹_›⟩, 
      intros t th, rw mem_attach_fin, rw mem_range, 
      have: image fin.val B <ᶜ image fin.val A, rwa colex_hom_fin,
      apply max_colex k this _ t.val _, intros x hx, rw mem_image at hx, rw mem_powerset_len at HA, rcases hx with ⟨a, ha, q⟩, rw ← q, rw ← mem_range, have := HA.1 ha, rwa mem_attach_fin at this, 
      rw mem_image, refine ⟨t, th, rfl⟩ },
    suffices: (shadow^[i] 𝒞) = powerset_len (r-i) range'k,
      rw [this, card_powerset_len, card_attach_fin, card_range], 
    ext B, rw mem_powerset_len, rw sub_iff_shadow_iter, 
    split, 
      rintro ⟨A, Ah, BsubA, card_sdiff_i⟩,
      rw mem_powerset_len at Ah, refine ⟨trans BsubA Ah.1, _⟩, symmetry,
      rw nat.sub_eq_iff_eq_add, 
      rw ← Ah.2, rw ← card_sdiff_i, rw ← card_disjoint_union, rw union_sdiff_of_subset BsubA,  apply disjoint_sdiff,
      apply hir,
    rintro ⟨_, _⟩,
    rcases exists_intermediate_set _ _ i _ a_left with ⟨C, BsubC, Csubrange, cards⟩, 
    rw [a_right, ← nat.add_sub_assoc hir, nat.add_sub_cancel_left] at cards, 
    refine ⟨C, _, BsubC, _⟩,
    rw mem_powerset_len, exact ⟨Csubrange, cards⟩, 
    rw card_sdiff BsubC, rw cards, rw a_right, rw nat.sub_sub_self hir, 
    rw a_right, rw card_attach_fin, rw card_range, rw ← nat.add_sub_assoc hir, rwa nat.add_sub_cancel_left, 
  end
end KK

def intersecting (𝒜 : finset (finset X)) : Prop := ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, ¬ disjoint A B

theorem intersecting_all {𝒜 : finset (finset X)} (h : intersecting 𝒜) : 𝒜.card ≤ 2^(n-1) :=
begin
  cases nat.eq_zero_or_pos n with b hn,
    convert nat.zero_le _,
    rw [card_eq_zero, eq_empty_iff_forall_not_mem],
    intros A HA, apply h A HA A HA, rw disjoint_self_iff_empty, 
    rw eq_empty_iff_forall_not_mem, intro x, rw b at x, exact (fin.elim0 ‹_›),
  set f : finset X → finset (finset X) := λ A, insert (univ \ A) (finset.singleton A),
  have disjs: ∀ x ∈ 𝒜, ∀ y ∈ 𝒜, x ≠ y → disjoint (f x) (f y),
    intros A hA B hB k,
    simp [not_or_distrib, and_assoc], refine ⟨_, _, _, _⟩,
      { intro z, apply k, ext a, simp [ext] at z, replace z := z a, tauto },
      intro a, rw ← a at hA, apply h _ hB _ hA disjoint_sdiff, 
      intro a, rw ← a at hB, apply h _ hB _ hA sdiff_disjoint, 
      exact k.symm, 
  have: 𝒜.bind f ⊆ powerset univ,
    intros A hA, rw mem_powerset, apply subset_univ,
  have q := card_le_of_subset this, rw [card_powerset, card_univ, card_fin] at q, 
  rw card_bind disjs at q, dsimp at q,
  have: ∀ u ∈ 𝒜, card (f u) = 2,
    intros u _, rw card_insert_of_not_mem, rw card_singleton, rw mem_singleton, intro, simp [ext] at a, apply a, exact ⟨0, hn⟩,
  rw sum_const_nat this at q,
  rw ← nat.le_div_iff_mul_le' zero_lt_two at q, 
  conv_rhs at q {rw ← nat.sub_add_cancel hn},
  rw nat.pow_add at q, simp at q, assumption,
end

def extremal_intersecting (hn : 1 ≤ n) : finset (finset X) :=
(powerset univ).filter (λ A, (⟨0, hn⟩: X) ∈ A)

theorem EKR {𝒜 : finset (finset X)} {r : ℕ} (h₁ : intersecting 𝒜) (h₂ : all_sized 𝒜 r) (h₃ : r < n/2) : 𝒜.card ≤ nat.choose (n-1) (r-1) :=
begin
  cases nat.eq_zero_or_pos r with b h1r,
    convert nat.zero_le _,
    rw [card_eq_zero, eq_empty_iff_forall_not_mem],
    intros A HA, apply h₁ A HA A HA, rw disjoint_self_iff_empty, 
    rw ← card_eq_zero, rw ← b, apply h₂ _ HA,
  by_contra size, replace size := lt_of_not_ge size,
  set 𝒜bar := 𝒜.image (λ A, univ \ A),
  have: disjoint 𝒜 (shadow^[n-2*r] 𝒜bar),
    rw disjoint_right, intros A hAbar hA, 
    simp [sub_iff_shadow_iter, mem_image] at hAbar,
    rcases hAbar with ⟨_, ⟨C, hC, rfl⟩, AsubnotC, _⟩, 
    apply h₁ A hA C hC (disjoint_of_subset_left AsubnotC sdiff_disjoint),
  have: r ≤ n := trans (le_of_lt h₃) (nat.div_le_self n 2), 
  have: 1 ≤ n := trans ‹1 ≤ r› ‹r ≤ n›,
  have z: 𝒜bar.card > nat.choose (n-1) (n-r),
    convert size using 1, rw card_image_of_inj_on, intros A _ B _ k, replace k := sdiff_partially_injective k,
      simp [ext] at k, rwa ext,
    apply choose_symm', rw [← nat.add_sub_assoc ‹r ≥ 1›, nat.sub_add_cancel ‹r ≤ n›],
  have: all_sized 𝒜bar (n - r),
    intro A, rw mem_image, rintro ⟨B, Bz, rfl⟩, rw card_univ_diff, rw card_fin, rw h₂ _ Bz, 
  have: n - 2 * r ≤ n - r, rw nat.sub_le_sub_left_iff ‹r ≤ n›, apply nat.le_mul_of_pos_left zero_lt_two,
  have kk := lovasz_form ‹n - 2 * r ≤ n - r› (by rwa nat.sub_le_sub_left_iff (trans h1r ‹r ≤ n›)) (nat.sub_le_self _ _) ‹all_sized 𝒜bar (n - r)› (le_of_lt z), 
  have q: n - r - (n - 2 * r) = r, rw [nat.sub.right_comm, nat.sub_sub_self, two_mul], apply nat.add_sub_cancel,
    rw [mul_comm, ← nat.le_div_iff_mul_le' zero_lt_two], apply le_of_lt ‹_›, 
  rw q at kk, 
  have: nat.choose n r < card (𝒜 ∪ (shadow^[n - 2 * r] 𝒜bar)),
    rw card_disjoint_union ‹_›, 
    convert lt_of_le_of_lt (nat.add_le_add_left kk _) (nat.add_lt_add_right size _),
    convert nat.choose_succ_succ _ _, any_goals {rwa [nat.sub_one, nat.succ_pred_eq_of_pos]}, 
  apply not_le_of_lt this,
  convert size_in_layer _, rw card_fin,
  rw ← union_layer, refine ⟨‹_›, _⟩,
  intros B hB, rw sub_iff_shadow_iter at hB, 
  rcases hB with ⟨A, hA, _, cards⟩, rw [card_sdiff ‹B ⊆ A›, ‹all_sized 𝒜bar (n - r)› _ ‹A ∈ _›] at cards, 
  rw [← q, ← cards, nat.sub_sub_self], 
  rw ← ‹all_sized 𝒜bar (n - r)› _ ‹A ∈ _›, apply card_le_of_subset ‹B ⊆ A›
end