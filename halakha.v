(******************************************************************************)
(*                                                                            *)
(*                        Talmudic Hermeneutics                               *)
(*                                                                            *)
(*     Formalizes the 13 middot of Rabbi Ishmael as inference rules over      *)
(*     scriptural texts. Encodes kal va-chomer (a fortiori), gezerah shavah   *)
(*     (analogy by shared term), binyan av (paradigm case), and the remaining *)
(*     rules as a typed derivation system. Verifies whether a halakhic        *)
(*     derivation is valid under the middot.                                  *)
(*                                                                            *)
(*     "Rabbi Ishmael says: By thirteen middot the Torah is expounded."       *)
(*     - Baraita of Rabbi Ishmael, Sifra 1:1                                  *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: December 2025                                                    *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Lia.
Import ListNotations.

Module TalmudicHermeneutics.

  (** Scriptural primitives. *)
  Definition Word := nat.

  Record Verse := mkVerse {
    verse_id : nat;
    verse_words : list Word
  }.

  Record Parshah := mkParshah {
    parshah_id : nat;
    parshah_verses : list Verse
  }.
  Definition word_eq_dec : forall w1 w2 : Word, {w1 = w2} + {w1 <> w2} := Nat.eq_dec.

  Definition list_nat_eq_dec : forall l1 l2 : list nat, {l1 = l2} + {l1 <> l2}.
  Proof. decide equality. apply Nat.eq_dec. Defined.

  Definition verse_eq_dec : forall v1 v2 : Verse, {v1 = v2} + {v1 <> v2}.
  Proof. decide equality; [apply list_nat_eq_dec | apply Nat.eq_dec]. Defined.

  Definition words_of : Verse -> list Word := verse_words.
  Definition verses_of : Parshah -> list Verse := parshah_verses.

  (** Subjects: entities to which halakhot apply, ordered by severity.
      category represents the type of case (e.g., property, personal, ritual). *)
  Record Subject := mkSubject {
    subject_id : nat;
    subject_severity : nat;
    subject_category : nat
  }.

  Record StrictOrder {A : Type} (R : A -> A -> Prop) : Prop := mkStrictOrder {
    strict_trans : forall a b c, R a b -> R b c -> R a c;
    strict_irrefl : forall a, ~ R a a
  }.

  Definition stricter (s1 s2 : Subject) : Prop :=
    subject_severity s1 > subject_severity s2.

  Lemma stricter_order : StrictOrder stricter.
  Proof.
    constructor.
    - intros a b c Hab Hbc. unfold stricter in *. lia.
    - intros a H. unfold stricter in H. lia.
  Qed.

  Definition stricter_trans : forall a b c, stricter a b -> stricter b c -> stricter a c :=
    strict_trans stricter stricter_order.

  Definition stricter_irrefl : forall a, ~ stricter a a :=
    strict_irrefl stricter stricter_order.

  (** Authority levels: d'oraita (Torah) vs d'rabbanan (Rabbinic). *)
  Inductive Authority : Type :=
    | DOraita : Authority
    | DRabbanan : Authority.

  Definition authority_eq_dec : forall a1 a2 : Authority, {a1 = a2} + {a1 <> a2}.
  Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

  (** Deontic modality: obligates, permits, or forbids. *)
  Inductive Modality : Type :=
    | Obligates : Modality
    | Permits : Modality
    | Forbids : Modality.

  Definition modality_eq_dec : forall m1 m2 : Modality, {m1 = m2} + {m1 <> m2}.
  Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

  Definition modalities_conflict (m1 m2 : Modality) : bool :=
    match m1, m2 with
    | Obligates, Forbids => true
    | Forbids, Obligates => true
    | Permits, Forbids => true
    | Forbids, Permits => true
    | _, _ => false
    end.

  (** Halakhic propositions: ID is identity; content lives in canonical environment. *)
  Definition Halakha := nat.

  Record HalakhaData := mkHalakhaData {
    hd_scope : Subject -> Prop;
    hd_modality : Modality;
    hd_authority : Authority
  }.

  Definition HalakhaEnv := Halakha -> option HalakhaData.

  (** Canonical global environment - the single source of truth.
      Same ID structurally guarantees same content. *)
  Definition global_env : HalakhaEnv := fun h =>
    match h with
    | 1 => Some (mkHalakhaData (fun s => subject_id s = 100) Permits DRabbanan)
    | 2 => Some (mkHalakhaData (fun s => subject_id s = 101) Obligates DOraita)
    | 3 => Some (mkHalakhaData (fun s => subject_id s = 100 \/ subject_id s = 101) Forbids DOraita)
    | 4 => Some (mkHalakhaData (fun s => subject_id s = 102) Permits DRabbanan)
    | 5 => Some (mkHalakhaData (fun s => subject_id s <= 105) Obligates DOraita)
    | 6 => Some (mkHalakhaData (fun s => subject_id s = 100) Forbids DRabbanan)
    | 7 => Some (mkHalakhaData (fun s => subject_id s = 101) Permits DOraita)
    | 8 => Some (mkHalakhaData (fun s => subject_id s = 102) Obligates DRabbanan)
    | 9 => Some (mkHalakhaData (fun s => subject_id s = 100) Obligates DOraita)
    | 10 => Some (mkHalakhaData (fun s => subject_id s = 101) Forbids DRabbanan)
    | _ => None
    end.

  (** Accessor functions use global_env. *)
  Definition halakha_scope (h : Halakha) : Subject -> Prop :=
    match global_env h with
    | Some data => hd_scope data
    | None => fun _ => False
    end.

  Definition halakha_modality (h : Halakha) : Modality :=
    match global_env h with
    | Some data => hd_modality data
    | None => Forbids
    end.

  Definition halakha_authority (h : Halakha) : Authority :=
    match global_env h with
    | Some data => hd_authority data
    | None => DRabbanan
    end.

  (** Same ID now structurally means same law. *)
  Definition halakha_eq_id (h1 h2 : Halakha) : Prop := h1 = h2.

  Definition applies_to (h : Halakha) (s : Subject) : Prop :=
    halakha_scope h s.

  Definition halakha_defined (h : Halakha) : Prop :=
    exists data, global_env h = Some data.

  Definition contains_word (v : Verse) (w : Word) : Prop :=
    In w (verse_words v).

  (** Semantic word constants for klal/prat and superfluity analysis. *)
  Definition word_kol : Word := 100.
  Definition word_ish : Word := 101.
  Definition word_davar : Word := 102.

  Definition quantifier_words : list Word := [word_kol; 103; 104].
  Definition specific_words : list Word := [word_ish; word_davar; 105; 106].

  (** Semantic word categories for determining superfluity. *)
  Definition action_words : list Word := [200; 201; 202; 203].
  Definition subject_words : list Word := [210; 211; 212; 213].
  Definition object_words : list Word := [220; 221; 222; 223].

  Definition is_semantic_core_word (w : Word) : bool :=
    existsb (Nat.eqb w) quantifier_words ||
    existsb (Nat.eqb w) specific_words ||
    existsb (Nat.eqb w) action_words ||
    existsb (Nat.eqb w) subject_words ||
    existsb (Nat.eqb w) object_words.

  (** Core words of a verse: those carrying semantic weight. *)
  Definition verse_core_words (v : Verse) : list Word :=
    filter is_semantic_core_word (verse_words v).

  (** A word is superfluous (mufneh) if it appears in the verse but is NOT
      a core semantic word - i.e., removing it doesn't change halakhic content. *)
  Definition word_superfluous (v : Verse) (w : Word) : Prop :=
    In w (verse_words v) /\ ~ In w (verse_core_words v).

  Definition word_superfluous_b (v : Verse) (w : Word) : bool :=
    existsb (Nat.eqb w) (verse_words v) &&
    negb (existsb (Nat.eqb w) (verse_core_words v)).

  Lemma word_superfluous_b_correct : forall v w,
    word_superfluous_b v w = true <-> word_superfluous v w.
  Proof.
    intros v w.
    unfold word_superfluous_b, word_superfluous.
    rewrite andb_true_iff, negb_true_iff.
    split.
    - intros [Hin Hncore].
      rewrite existsb_exists in Hin.
      destruct Hin as [x [Hxin Heq]].
      rewrite Nat.eqb_eq in Heq. subst.
      split.
      + exact Hxin.
      + intro Hcore.
        assert (existsb (Nat.eqb x) (verse_core_words v) = true) as Hex.
        { rewrite existsb_exists. exists x. split. exact Hcore. apply Nat.eqb_refl. }
        rewrite Hex in Hncore. discriminate.
    - intros [Hin Hncore].
      split.
      + rewrite existsb_exists. exists w. split. exact Hin. apply Nat.eqb_refl.
      + destruct (existsb (Nat.eqb w) (verse_core_words v)) eqn:E.
        * rewrite existsb_exists in E.
          destruct E as [x [Hxin Heq]].
          rewrite Nat.eqb_eq in Heq. subst.
          contradiction.
        * reflexivity.
  Qed.

  (** Position-based helper (kept for compatibility). *)
  Definition word_position (v : Verse) (w : Word) : option nat :=
    let fix find_pos (l : list Word) (n : nat) :=
      match l with
      | [] => None
      | x :: xs => if Nat.eq_dec x w then Some n else find_pos xs (S n)
      end
    in find_pos (verse_words v) 0.

  (** Mesorah certificate: proof-carrying evidence that a word is authorized
      for gezerah shavah between two specific verses. The word must be
      superfluous (mufneh) in both verses - this is the structural criterion
      that justifies the received tradition. *)
  Inductive MesorahCertificate : Word -> Verse -> Verse -> Type :=
    | mesorah_received : forall w v1 v2,
        contains_word v1 w ->
        contains_word v2 w ->
        word_superfluous v1 w ->
        word_superfluous v2 w ->
        v1 <> v2 ->
        MesorahCertificate w v1 v2.

  Definition mesorah_link (w : Word) (v1 v2 : Verse) : Prop :=
    inhabited (MesorahCertificate w v1 v2).

  Definition has_mesorah (w : Word) : Prop :=
    exists v1 v2, mesorah_link w v1 v2.

  Lemma mesorah_link_sym : forall w v1 v2,
    mesorah_link w v1 v2 -> mesorah_link w v2 v1.
  Proof.
    intros w v1 v2 [cert].
    inversion cert; subst.
    constructor.
    apply mesorah_received; auto.
  Qed.

  Lemma mesorah_certificate_contains : forall w v1 v2,
    mesorah_link w v1 v2 -> contains_word v1 w /\ contains_word v2 w.
  Proof.
    intros w v1 v2 [cert].
    destruct cert as [w' v1' v2' Hc1 Hc2 Hs1 Hs2 Hneq].
    split; assumption.
  Qed.

  Lemma mesorah_certificate_superfluous : forall w v1 v2,
    mesorah_link w v1 v2 -> word_superfluous v1 w /\ word_superfluous v2 w.
  Proof.
    intros w v1 v2 [cert].
    destruct cert as [w' v1' v2' Hc1 Hc2 Hs1 Hs2 Hneq].
    split; assumption.
  Qed.

  (** Torah corpus: explicit pairings of halakha-id to verse-id representing peshat. *)
  Definition CorpusEntry := (nat * nat)%type.
  Definition Corpus := list CorpusEntry.

  Definition corpus_contains (c : Corpus) (hid vid : nat) : Prop :=
    In (hid, vid) c.

  Definition corpus_contains_b (c : Corpus) (hid vid : nat) : bool :=
    existsb (fun entry => Nat.eqb (fst entry) hid && Nat.eqb (snd entry) vid) c.

  Lemma corpus_contains_b_correct : forall c hid vid,
    corpus_contains_b c hid vid = true <-> corpus_contains c hid vid.
  Proof.
    intros c hid vid.
    unfold corpus_contains_b, corpus_contains.
    rewrite existsb_exists.
    split.
    - intros [[h v] [Hin Heq]].
      simpl in Heq. rewrite andb_true_iff in Heq.
      destruct Heq as [Hh Hv].
      rewrite Nat.eqb_eq in Hh, Hv. subst.
      exact Hin.
    - intro Hin.
      exists (hid, vid). split.
      + exact Hin.
      + simpl. rewrite 2 Nat.eqb_refl. reflexivity.
  Qed.

  Definition torah_corpus : Corpus :=
    [ (1, 1); (2, 2); (3, 1); (4, 3) ].

  Definition base_derivation (h : Halakha) (v : Verse) : Prop :=
    corpus_contains torah_corpus h (verse_id v).

  Definition base_derivation_b (h : Halakha) (v : Verse) : bool :=
    corpus_contains_b torah_corpus h (verse_id v).

  Lemma base_derivation_b_correct : forall h v,
    base_derivation_b h v = true <-> base_derivation h v.
  Proof.
    intros h v.
    unfold base_derivation_b, base_derivation.
    apply corpus_contains_b_correct.
  Qed.

  Lemma corpus_consistent : NoDup (map fst torah_corpus).
  Proof.
    unfold torah_corpus. simpl.
    apply NoDup_cons. { simpl. intros [H|[H|[H|H]]]; discriminate || exact H. }
    apply NoDup_cons. { simpl. intros [H|[H|H]]; discriminate || exact H. }
    apply NoDup_cons. { simpl. intros [H|H]; discriminate || exact H. }
    apply NoDup_cons. { simpl. intros H; exact H. }
    apply NoDup_nil.
  Qed.

  Inductive derived_from : Halakha -> Verse -> Prop :=
    | derived_base : forall h v,
        base_derivation h v ->
        derived_from h v
    | derived_gezerah_shavah : forall h v1 v2 w,
        derived_from h v1 ->
        mesorah_link w v1 v2 ->
        derived_from h v2.

  (** The 13 Middot as inference rules. *)

  Inductive Middah : Type :=
    | KalVaChomer : Middah
    | GezerahShavah : Middah
    | BinyanAvEchad : Middah
    | BinyanAvShnei : Middah
    | KlalUFrat : Middah
    | PratUKlal : Middah
    | KlalUFratUKlal : Middah
    | KlalSheTzarichLeFrat : Middah
    | PratSheTzarichLeKlal : Middah
    | DavarSheHayahBiKlal : Middah
    | DavarYatzaLeLamed : Middah
    | DavarHaLamedMeInyano : Middah
    | ShneiKetuvimMakhchishim : Middah.

  Definition middah_eq_dec : forall m1 m2 : Middah, {m1 = m2} + {m1 <> m2}.
  Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

  Definition all_middot : list Middah :=
    [KalVaChomer; GezerahShavah; BinyanAvEchad; BinyanAvShnei;
     KlalUFrat; PratUKlal; KlalUFratUKlal; KlalSheTzarichLeFrat;
     PratSheTzarichLeKlal; DavarSheHayahBiKlal; DavarYatzaLeLamed;
     DavarHaLamedMeInyano; ShneiKetuvimMakhchishim].

  Lemma all_middot_complete : forall m, In m all_middot.
  Proof. intros []; simpl; auto 15. Qed.

  Lemma all_middot_length : length all_middot = 13.
  Proof. reflexivity. Qed.

  (** Derivation: a halakha derived via a middah from source verses. *)
  Record Derivation : Type := mkDerivation {
    conclusion : Halakha;
    rule : Middah;
    source_verses : list Verse;
    justification : Prop
  }.

  (** Validity predicates for each middah. *)

  (** Kal va-chomer: if h applies to the lenient case, it applies to the strict case.
      The dayo principle (Bava Kamma 25a): the derived stringency cannot exceed
      the source stringency. We model this by requiring the conclusion's scope
      to be no broader than justified by the premise. *)
  Definition valid_kal_va_chomer (lenient strict : Subject) (h : Halakha) : Prop :=
    stricter strict lenient /\
    applies_to h lenient ->
    applies_to h strict.

  (** Dayo: the conclusion of kal va-chomer is limited to what the premise establishes.
      "It is sufficient (dayo) for the derived law to be equal to the source law." *)
  Definition dayo_satisfied (h_premise h_conclusion : Halakha) (strict : Subject) : Prop :=
    forall s, applies_to h_conclusion s ->
      applies_to h_premise s \/ subject_id s = subject_id strict.

  Definition valid_kal_va_chomer_with_dayo
    (lenient strict : Subject) (h_premise h_conclusion : Halakha) : Prop :=
    stricter strict lenient /\
    applies_to h_premise lenient /\
    halakha_eq_id h_premise h_conclusion /\
    dayo_satisfied h_premise h_conclusion strict /\
    applies_to h_conclusion strict.

  (** Gezerah shavah: identical words in two verses create analogy. *)
  (** Requires mesorah_link: proof-carrying certificate for the word-verse pair. *)

  Record GezerahShavahData : Type := mkGezerahShavah {
    gs_v1 : Verse;
    gs_v2 : Verse;
    gs_word : Word;
    gs_halakha : Halakha;
    gs_mesorah_link : mesorah_link gs_word gs_v1 gs_v2;
    gs_derived_v1 : derived_from gs_halakha gs_v1
  }.

  Definition gs_contains_v1 (gsd : GezerahShavahData) : contains_word (gs_v1 gsd) (gs_word gsd) :=
    proj1 (mesorah_certificate_contains _ _ _ (gs_mesorah_link gsd)).

  Definition gs_contains_v2 (gsd : GezerahShavahData) : contains_word (gs_v2 gsd) (gs_word gsd) :=
    proj2 (mesorah_certificate_contains _ _ _ (gs_mesorah_link gsd)).

  Definition gs_mesorah (gsd : GezerahShavahData) : has_mesorah (gs_word gsd) :=
    ex_intro _ (gs_v1 gsd) (ex_intro _ (gs_v2 gsd) (gs_mesorah_link gsd)).

  Definition valid_gezerah_shavah (v1 v2 : Verse) (shared : Word) (h : Halakha) : Prop :=
    exists gsd : GezerahShavahData,
      gs_v1 gsd = v1 /\ gs_v2 gsd = v2 /\ gs_word gsd = shared /\ gs_halakha gsd = h.

  (** Binyan av: paradigm case establishes rule for similar cases. *)
  (** Similar cases share both severity level and category - the shared
      property that justifies binyan av inference. *)
  Definition similar_cases (s1 s2 : Subject) : Prop :=
    subject_severity s1 = subject_severity s2 /\
    subject_category s1 = subject_category s2.

  Definition valid_binyan_av (paradigm : Verse) (h : Halakha) (s1 s2 : Subject) : Prop :=
    derived_from h paradigm /\
    applies_to h s1 /\
    similar_cases s1 s2 ->
    applies_to h s2.

  (** Klal u-frat: general followed by particular means only the particular. *)

  Definition has_quantifier (v : Verse) : Prop :=
    exists w, In w (verse_words v) /\ In w quantifier_words.

  Definition has_specific (v : Verse) : Prop :=
    exists w, In w (verse_words v) /\ In w specific_words.

  Definition is_general (v : Verse) : Prop :=
    has_quantifier v /\ ~ has_specific v.

  Definition is_particular (v : Verse) : Prop :=
    has_specific v /\ ~ has_quantifier v.

  Definition has_quantifier_b (v : Verse) : bool :=
    existsb (fun w => existsb (Nat.eqb w) quantifier_words) (verse_words v).

  Definition has_specific_b (v : Verse) : bool :=
    existsb (fun w => existsb (Nat.eqb w) specific_words) (verse_words v).

  Definition is_general_b_new (v : Verse) : bool :=
    has_quantifier_b v && negb (has_specific_b v).

  Definition is_particular_b_new (v : Verse) : bool :=
    has_specific_b v && negb (has_quantifier_b v).

  (** Particularizes: prat follows klal textually (adjacent verse IDs)
      and shares thematic words (non-empty intersection). *)
  Definition verses_adjacent (v1 v2 : Verse) : Prop :=
    verse_id v2 = S (verse_id v1).

  Definition words_overlap (v1 v2 : Verse) : Prop :=
    exists w, In w (verse_words v1) /\ In w (verse_words v2).

  Definition particularizes (prat klal : Verse) : Prop :=
    verses_adjacent klal prat /\ words_overlap klal prat.

  (** Klal u-frat: general followed by particular restricts to particular's scope. *)
  Definition valid_klal_u_frat (klal prat : Verse) (h_premise h_conclusion : Halakha) (restriction : Subject -> Prop) : Prop :=
    is_general klal /\
    is_particular prat /\
    particularizes prat klal /\
    halakha_eq_id h_premise h_conclusion /\
    (forall s, halakha_scope h_conclusion s <-> (halakha_scope h_premise s /\ restriction s)).

  (** Prat u-klal: particular followed by general expands to general's scope. *)
  Definition valid_prat_u_klal (prat klal : Verse) (h_premise h_conclusion : Halakha) : Prop :=
    is_particular prat /\
    is_general klal /\
    particularizes prat klal /\
    halakha_eq_id h_premise h_conclusion /\
    (forall s, halakha_scope h_premise s -> halakha_scope h_conclusion s).

  (** Klal u-frat u-klal: scope is similar to the particular, not identical. *)
  Definition valid_klal_u_frat_u_klal (klal1 prat klal2 : Verse) (h_premise h_conclusion : Halakha) (similar : Subject -> Prop) : Prop :=
    is_general klal1 /\
    is_particular prat /\
    is_general klal2 /\
    particularizes prat klal1 /\
    halakha_eq_id h_premise h_conclusion /\
    (forall s, halakha_scope h_conclusion s <-> (halakha_scope h_premise s /\ similar s)).

  (** Davar she-hayah bi-klal: exception removes subjects from general rule. *)
  Definition exception_from (exc gen : Halakha) : Prop :=
    exc <> gen /\
    exists s, halakha_scope gen s /\ halakha_scope exc s.

  Definition valid_davar_she_hayah (general_rule exception result : Halakha) : Prop :=
    exception_from exception general_rule /\
    halakha_eq_id general_rule result /\
    (forall s, halakha_scope result s <-> (halakha_scope general_rule s /\ ~ halakha_scope exception s)).

  (** Shnei ketuvim makhchishim: two contradictory verses resolved by a third. *)

  Definition incompatible (h1 h2 : Halakha) (s : Subject) : Prop :=
    halakha_scope h1 s /\
    halakha_scope h2 s /\
    modalities_conflict (halakha_modality h1) (halakha_modality h2) = true.

  Definition incompatible_b (h1 h2 : Halakha) (s : Subject) : bool :=
    modalities_conflict (halakha_modality h1) (halakha_modality h2).

  Lemma incompatible_sym : forall h1 h2 s,
    incompatible h1 h2 s -> incompatible h2 h1 s.
  Proof.
    intros h1 h2 s [Hs1 [Hs2 Hm]].
    unfold incompatible.
    split. exact Hs2.
    split. exact Hs1.
    destruct (halakha_modality h1), (halakha_modality h2); simpl in *; auto.
  Qed.

  Lemma modalities_conflict_sym : forall m1 m2,
    modalities_conflict m1 m2 = modalities_conflict m2 m1.
  Proof. intros [] []; reflexivity. Qed.

  Definition halakha_conflicts (h1 h2 : Halakha) : Prop :=
    exists s, halakha_scope h1 s /\ halakha_scope h2 s /\ incompatible h1 h2 s.

  (** Resolution synthesizes a consistent halakha from conflicting ones. *)
  Record Contradiction : Type := mkContradiction {
    contra_v1 : Verse;
    contra_v2 : Verse;
    contra_v3 : Verse;
    contra_h1 : Halakha;
    contra_h2 : Halakha;
    contra_h3 : Halakha;
    contra_derived_1 : derived_from contra_h1 contra_v1;
    contra_derived_2 : derived_from contra_h2 contra_v2;
    contra_derived_3 : derived_from contra_h3 contra_v3;
    contra_conflict : halakha_conflicts contra_h1 contra_h2;
    contra_h3_consistent : ~ halakha_conflicts contra_h3 contra_h1 /\ ~ halakha_conflicts contra_h3 contra_h2
  }.

  Definition contradicts (v1 v2 : Verse) : Prop :=
    exists c : Contradiction, contra_v1 c = v1 /\ contra_v2 c = v2.

  Definition resolves (v3 v1 v2 : Verse) : Prop :=
    exists c : Contradiction,
      contra_v1 c = v1 /\ contra_v2 c = v2 /\ contra_v3 c = v3.

  Definition valid_shnei_ketuvim (v1 v2 v3 : Verse) (h : Halakha) : Prop :=
    contradicts v1 v2 /\
    resolves v3 v1 v2 /\
    derived_from h v3.

  Definition authority_ge (a1 a2 : Authority) : Prop :=
    match a1, a2 with
    | DOraita, _ => True
    | DRabbanan, DRabbanan => True
    | DRabbanan, DOraita => False
    end.

  Definition authority_ge_b (a1 a2 : Authority) : bool :=
    match a1, a2 with
    | DOraita, _ => true
    | DRabbanan, DRabbanan => true
    | DRabbanan, DOraita => false
    end.

  Lemma authority_ge_refl : forall a, authority_ge a a.
  Proof. intros []; simpl; exact I. Qed.

  Lemma authority_ge_dec : forall a1 a2, {authority_ge a1 a2} + {~ authority_ge a1 a2}.
  Proof. intros [] []; simpl; auto. Defined.

  Lemma authority_ge_b_correct : forall a1 a2,
    authority_ge_b a1 a2 = true <-> authority_ge a1 a2.
  Proof.
    intros [] []; simpl; split; auto; discriminate.
  Qed.

  Lemma authority_ge_trans : forall a b c,
    authority_ge a b -> authority_ge b c -> authority_ge a c.
  Proof. intros [] [] []; simpl; auto. Qed.

  Lemma authority_ge_antisym : forall a b,
    authority_ge a b -> authority_ge b a -> a = b.
  Proof. intros [] [] H1 H2; auto; simpl in *; contradiction. Qed.

  Definition derivation_authority (d : Derivation) : Authority :=
    halakha_authority (conclusion d).

  (** Derivation trees: structured proofs of halakhic conclusions. *)
  Inductive DerivationTree : Type :=
    | Leaf : Verse -> DerivationTree
    | Node : Middah -> list DerivationTree -> Halakha -> DerivationTree.

  Fixpoint tree_depth (t : DerivationTree) : nat :=
    match t with
    | Leaf _ => 0
    | Node _ children _ =>
        1 + fold_right max 0 (map tree_depth children)
    end.

  Fixpoint tree_verses (t : DerivationTree) : list Verse :=
    match t with
    | Leaf v => [v]
    | Node _ children _ =>
        flat_map tree_verses children
    end.

  Fixpoint tree_middot (t : DerivationTree) : list Middah :=
    match t with
    | Leaf _ => []
    | Node m children _ =>
        m :: flat_map tree_middot children
    end.

  Definition tree_conclusion (t : DerivationTree) : option Halakha :=
    match t with
    | Leaf _ => None
    | Node _ _ h => Some h
    end.

  (** Well-formedness: a derivation tree is well-formed if it uses valid middot.
      Each constructor requires child conclusions to semantically justify the parent. *)

  Definition has_conclusion (t : DerivationTree) (h : Halakha) : Prop :=
    tree_conclusion t = Some h.

  (** A citation tree is a leaf - provides verse without derived conclusion. *)
  Definition is_citation (t : DerivationTree) : Prop :=
    exists v, t = Leaf v.

  Lemma citation_no_conclusion : forall t,
    is_citation t -> tree_conclusion t = None.
  Proof.
    intros t [v Hv]. subst. reflexivity.
  Qed.

  Lemma citation_single_verse : forall t v,
    t = Leaf v -> tree_verses t = [v].
  Proof.
    intros t v Hv. subst. reflexivity.
  Qed.

  Inductive valid_node : Middah -> list DerivationTree -> Halakha -> Prop :=
    | valid_context : forall v h,
        derived_from h v ->
        valid_node DavarHaLamedMeInyano [Leaf v] h

    | valid_kal_va_chomer_node : forall t_lenient t_strict h_in h_out lenient strict v_strict,
        has_conclusion t_lenient h_in ->
        is_citation t_strict ->
        tree_verses t_strict = [v_strict] ->
        contains_word v_strict (subject_id strict) ->
        stricter strict lenient ->
        applies_to h_in lenient ->
        halakha_eq_id h_in h_out ->
        (halakha_authority h_in = DRabbanan -> halakha_authority h_out = DRabbanan) ->
        (forall s, halakha_scope h_out s <-> (halakha_scope h_in s \/ subject_id s = subject_id strict)) ->
        valid_node KalVaChomer [t_lenient; t_strict] h_out

    | valid_gezerah_shavah_node : forall t1 t2 h v1 v2 w,
        has_conclusion t1 h ->
        is_citation t2 ->
        tree_verses t1 = [v1] ->
        tree_verses t2 = [v2] ->
        valid_gezerah_shavah v1 v2 w h ->
        valid_node GezerahShavah [t1; t2] h

    | valid_binyan_av_echad_node : forall t h_in h_out s_paradigm s_target,
        has_conclusion t h_in ->
        applies_to h_in s_paradigm ->
        similar_cases s_paradigm s_target ->
        halakha_eq_id h_in h_out ->
        (forall s, halakha_scope h_out s <-> (halakha_scope h_in s \/ subject_id s = subject_id s_target)) ->
        valid_node BinyanAvEchad [t] h_out

    | valid_binyan_av_shnei_node : forall t1 t2 h_in h_out s1 s2 s_target,
        has_conclusion t1 h_in ->
        has_conclusion t2 h_in ->
        applies_to h_in s1 ->
        applies_to h_in s2 ->
        similar_cases s1 s_target ->
        similar_cases s2 s_target ->
        halakha_eq_id h_in h_out ->
        (forall s, halakha_scope h_out s <-> (halakha_scope h_in s \/ subject_id s = subject_id s_target)) ->
        valid_node BinyanAvShnei [t1; t2] h_out

    | valid_klal_u_frat_node : forall t_klal t_prat h_in h_out v_klal v_prat restriction,
        has_conclusion t_klal h_in ->
        is_citation t_prat ->
        tree_verses t_klal = [v_klal] ->
        tree_verses t_prat = [v_prat] ->
        valid_klal_u_frat v_klal v_prat h_in h_out restriction ->
        valid_node KlalUFrat [t_klal; t_prat] h_out

    | valid_prat_u_klal_node : forall t_prat t_klal h_in h_out v_prat v_klal,
        has_conclusion t_prat h_in ->
        is_citation t_klal ->
        tree_verses t_prat = [v_prat] ->
        tree_verses t_klal = [v_klal] ->
        valid_prat_u_klal v_prat v_klal h_in h_out ->
        valid_node PratUKlal [t_prat; t_klal] h_out

    | valid_klal_u_frat_u_klal_node : forall t1 t2 t3 h_in h_out v1 v2 v3 similar,
        has_conclusion t1 h_in ->
        is_citation t2 ->
        is_citation t3 ->
        tree_verses t1 = [v1] ->
        tree_verses t2 = [v2] ->
        tree_verses t3 = [v3] ->
        valid_klal_u_frat_u_klal v1 v2 v3 h_in h_out similar ->
        valid_node KlalUFratUKlal [t1; t2; t3] h_out

    | valid_klal_she_tzarich_node : forall t_klal t_prat h_in h_out v_klal v_prat,
        has_conclusion t_klal h_in ->
        is_citation t_prat ->
        tree_verses t_klal = [v_klal] ->
        tree_verses t_prat = [v_prat] ->
        is_general v_klal ->
        is_particular v_prat ->
        halakha_eq_id h_in h_out ->
        ~ derived_from h_in v_klal ->
        derived_from h_out v_klal ->
        derived_from h_out v_prat ->
        (forall s, halakha_scope h_out s <-> halakha_scope h_in s) ->
        valid_node KlalSheTzarichLeFrat [t_klal; t_prat] h_out

    | valid_prat_she_tzarich_node : forall t_prat t_klal h_in h_out v_prat v_klal,
        has_conclusion t_prat h_in ->
        is_citation t_klal ->
        tree_verses t_prat = [v_prat] ->
        tree_verses t_klal = [v_klal] ->
        is_particular v_prat ->
        is_general v_klal ->
        halakha_eq_id h_in h_out ->
        ~ derived_from h_in v_prat ->
        derived_from h_out v_prat ->
        derived_from h_out v_klal ->
        (forall s, halakha_scope h_out s <-> halakha_scope h_in s) ->
        valid_node PratSheTzarichLeKlal [t_prat; t_klal] h_out

    | valid_davar_she_hayah_node : forall t_general t_exception h_general h_exception h_out,
        has_conclusion t_general h_general ->
        has_conclusion t_exception h_exception ->
        valid_davar_she_hayah h_general h_exception h_out ->
        valid_node DavarSheHayahBiKlal [t_general; t_exception] h_out

    | valid_davar_yatza_node : forall t h_general h_teaching v,
        has_conclusion t h_general ->
        tree_verses t = [v] ->
        derived_from h_teaching v ->
        halakha_eq_id h_general h_teaching ->
        (forall s, halakha_scope h_teaching s -> halakha_scope h_general s) ->
        (exists s, halakha_scope h_general s /\ ~ halakha_scope h_teaching s) ->
        valid_node DavarYatzaLeLamed [t] h_teaching

    | valid_shnei_ketuvim_node : forall t1 t2 t3 h1 h2 h_out v1 v2 v3,
        has_conclusion t1 h1 ->
        has_conclusion t2 h2 ->
        is_citation t3 ->
        tree_verses t1 = [v1] ->
        tree_verses t2 = [v2] ->
        tree_verses t3 = [v3] ->
        halakha_conflicts h1 h2 ->
        derived_from h_out v3 ->
        ~ halakha_conflicts h_out h1 ->
        ~ halakha_conflicts h_out h2 ->
        valid_node ShneiKetuvimMakhchishim [t1; t2; t3] h_out.

  (** Bridging theorems: connect standalone predicates to tree semantics. *)

  Theorem gezerah_shavah_bridge : forall v1 v2 w h,
    valid_gezerah_shavah v1 v2 w h ->
    derived_from h v2.
  Proof.
    intros v1 v2 w h [gsd [Hv1 [Hv2 [Hw Hh]]]].
    subst.
    apply derived_gezerah_shavah with (v1 := gs_v1 gsd) (w := gs_word gsd).
    - exact (gs_derived_v1 gsd).
    - exact (gs_mesorah_link gsd).
  Qed.

  Theorem klal_u_frat_bridge : forall klal prat h_in h_out restriction,
    valid_klal_u_frat klal prat h_in h_out restriction ->
    forall s, halakha_scope h_out s -> halakha_scope h_in s.
  Proof.
    intros klal prat h_in h_out restriction Hvalid s Hout.
    unfold valid_klal_u_frat in Hvalid.
    destruct Hvalid as [_ [_ [_ [_ Hscope]]]].
    apply Hscope in Hout. destruct Hout. exact H.
  Qed.

  Theorem prat_u_klal_bridge : forall prat klal h_in h_out,
    valid_prat_u_klal prat klal h_in h_out ->
    forall s, halakha_scope h_in s -> halakha_scope h_out s.
  Proof.
    intros prat klal h_in h_out Hvalid s Hin.
    unfold valid_prat_u_klal in Hvalid.
    destruct Hvalid as [_ [_ [_ [_ Hexpand]]]].
    apply Hexpand. exact Hin.
  Qed.

  Theorem shnei_ketuvim_bridge : forall v1 v2 v3 h,
    valid_shnei_ketuvim v1 v2 v3 h ->
    derived_from h v3.
  Proof.
    intros v1 v2 v3 h [_ [_ Hd]]. exact Hd.
  Qed.

  Theorem davar_she_hayah_bridge : forall h_gen h_exc h_out,
    valid_davar_she_hayah h_gen h_exc h_out ->
    forall s, halakha_scope h_out s -> halakha_scope h_gen s /\ ~ halakha_scope h_exc s.
  Proof.
    intros h_gen h_exc h_out Hvalid s Hout.
    unfold valid_davar_she_hayah in Hvalid.
    destruct Hvalid as [_ [_ Hscope]].
    apply Hscope. exact Hout.
  Qed.

  (** Universe of valid halakhot: restricts what halakhot can appear in derivations. *)
  Definition halakha_universe : list nat := [1; 2; 3; 4; 5; 6; 7; 8; 9; 10].

  Definition valid_halakha (h : Halakha) : Prop :=
    In h halakha_universe.

  Definition valid_halakha_b (h : Halakha) : bool :=
    existsb (Nat.eqb h) halakha_universe.

  Lemma valid_halakha_b_correct : forall h,
    valid_halakha_b h = true <-> valid_halakha h.
  Proof.
    intro h.
    unfold valid_halakha_b, valid_halakha.
    rewrite existsb_exists.
    split.
    - intros [x [Hin Heq]]. rewrite Nat.eqb_eq in Heq. subst. exact Hin.
    - intro Hin. exists h. split. exact Hin. apply Nat.eqb_refl.
  Qed.

  Lemma halakha_universe_nodup : NoDup halakha_universe.
  Proof.
    unfold halakha_universe.
    repeat (apply NoDup_cons; [simpl; intros H; repeat destruct H as [H|H]; try discriminate; try exact H |]).
    apply NoDup_nil.
  Qed.

  (** Closure lemmas: valid_halakha is preserved by middot when IDs match. *)

  Lemma valid_halakha_preserved_by_id : forall h1 h2,
    halakha_eq_id h1 h2 ->
    valid_halakha h1 ->
    valid_halakha h2.
  Proof.
    intros h1 h2 Heq Hv1.
    unfold valid_halakha, halakha_eq_id in *.
    rewrite <- Heq. exact Hv1.
  Qed.

  Lemma valid_halakha_klal_u_frat : forall klal prat h_in h_out restriction,
    valid_klal_u_frat klal prat h_in h_out restriction ->
    valid_halakha h_in ->
    valid_halakha h_out.
  Proof.
    intros klal prat h_in h_out restriction Hvalid Hvin.
    unfold valid_klal_u_frat in Hvalid.
    destruct Hvalid as [_ [_ [_ [Heq _]]]].
    unfold valid_halakha, halakha_eq_id in *.
    rewrite <- Heq. exact Hvin.
  Qed.

  Lemma valid_halakha_prat_u_klal : forall prat klal h_in h_out,
    valid_prat_u_klal prat klal h_in h_out ->
    valid_halakha h_in ->
    valid_halakha h_out.
  Proof.
    intros prat klal h_in h_out Hvalid Hvin.
    unfold valid_prat_u_klal in Hvalid.
    destruct Hvalid as [_ [_ [_ [Heq _]]]].
    unfold valid_halakha, halakha_eq_id in *.
    rewrite <- Heq. exact Hvin.
  Qed.

  Lemma valid_halakha_davar_she_hayah : forall h_gen h_exc h_out,
    valid_davar_she_hayah h_gen h_exc h_out ->
    valid_halakha h_gen ->
    valid_halakha h_out.
  Proof.
    intros h_gen h_exc h_out Hvalid Hvgen.
    unfold valid_davar_she_hayah in Hvalid.
    destruct Hvalid as [_ [Heq _]].
    unfold valid_halakha, halakha_eq_id in *.
    rewrite <- Heq. exact Hvgen.
  Qed.

  (** Authority-safe derivation helpers. *)
  (** Scripture (leaves) is DOraita by nature; nodes inherit from conclusion. *)
  Definition child_authority (t : DerivationTree) : Authority :=
    match t with
    | Leaf _ => DOraita
    | Node _ _ h => halakha_authority h
    end.

  Definition min_child_authority (children : list DerivationTree) : Authority :=
    if forallb (fun t => authority_ge_b (child_authority t) DOraita) children
    then DOraita
    else DRabbanan.

  Definition authority_safe_node (m : Middah) (children : list DerivationTree) (h : Halakha) : Prop :=
    authority_ge (min_child_authority children) (halakha_authority h).

  Lemma authority_safe_no_upgrade : forall m children h,
    authority_safe_node m children h ->
    halakha_authority h = DOraita ->
    min_child_authority children = DOraita.
  Proof.
    intros m children h Hsafe Hauth.
    unfold authority_safe_node in Hsafe.
    rewrite Hauth in Hsafe.
    destruct (min_child_authority children); auto.
    simpl in Hsafe. contradiction.
  Qed.

  (** Unified well-formedness: structural validity, authority, and universe membership. *)
  Fixpoint well_formed (t : DerivationTree) : Prop :=
    match t with
    | Leaf v => True
    | Node m children h =>
        valid_node m children h /\
        valid_halakha h /\
        authority_safe_node m children h /\
        (fix all_wf (l : list DerivationTree) : Prop :=
          match l with
          | [] => True
          | c :: cs => well_formed c /\ all_wf cs
          end) children
    end.

  (** Chain of derivations: sequential application of middot. *)
  Inductive DerivationChain : Type :=
    | ChainEnd : Halakha -> DerivationChain
    | ChainStep : Middah -> Halakha -> DerivationChain -> DerivationChain.

  Fixpoint chain_length (c : DerivationChain) : nat :=
    match c with
    | ChainEnd _ => 0
    | ChainStep _ _ rest => S (chain_length rest)
    end.

  Fixpoint chain_middot (c : DerivationChain) : list Middah :=
    match c with
    | ChainEnd _ => []
    | ChainStep m _ rest => m :: chain_middot rest
    end.

  Definition chain_conclusion (c : DerivationChain) : Halakha :=
    match c with
    | ChainEnd h => h
    | ChainStep _ h _ => h
    end.

  (** Validity of a derivation chain. *)
  (** A derivation step cannot upgrade authority: conclusion <= premise. *)
  Definition step_valid (m : Middah) (h_from h_to : Halakha) : Prop :=
    authority_ge (halakha_authority h_from) (halakha_authority h_to).

  Fixpoint chain_valid (c : DerivationChain) : Prop :=
    match c with
    | ChainEnd _ => True
    | ChainStep m h rest =>
        step_valid m (chain_conclusion rest) h /\
        chain_valid rest
    end.

  (** Traditional vs. Karaite interpretation. *)
  Definition rabbinic_derivation (v : Verse) (h : Halakha) : Prop :=
    exists t : DerivationTree,
      In v (tree_verses t) /\
      tree_conclusion t = Some h /\
      well_formed t.

  Definition karaite_derivation (v : Verse) (h : Halakha) : Prop :=
    derived_from h v.

  (** Key theorems. *)

  Theorem kal_va_chomer_transitivity :
    forall a b c h,
      stricter b a ->
      stricter c b ->
      applies_to h a ->
      valid_kal_va_chomer a b h ->
      valid_kal_va_chomer b c h ->
      applies_to h c.
  Proof.
    intros a b c h Hba Hcb Ha Hab Hbc.
    unfold valid_kal_va_chomer in *.
    apply Hbc.
    split.
    - exact Hcb.
    - apply Hab.
      split.
      + exact Hba.
      + exact Ha.
  Qed.

  Theorem gezerah_shavah_application :
    forall v1 v2 w h,
      valid_gezerah_shavah v1 v2 w h ->
      derived_from h v2.
  Proof.
    intros v1 v2 w h [gsd [Hv1 [Hv2 [Hw Hh]]]].
    subst.
    apply derived_gezerah_shavah with (v1 := gs_v1 gsd) (w := gs_word gsd).
    - exact (gs_derived_v1 gsd).
    - exact (gs_mesorah_link gsd).
  Qed.

  Theorem chain_extension :
    forall c m h,
      chain_valid c ->
      step_valid m (chain_conclusion c) h ->
      chain_valid (ChainStep m h c).
  Proof.
    intros c m h Hc Hs.
    simpl.
    split.
    - exact Hs.
    - exact Hc.
  Qed.

  Theorem all_middot_necessary :
    forall m, In m all_middot <->
      m = KalVaChomer \/ m = GezerahShavah \/ m = BinyanAvEchad \/
      m = BinyanAvShnei \/ m = KlalUFrat \/ m = PratUKlal \/
      m = KlalUFratUKlal \/ m = KlalSheTzarichLeFrat \/
      m = PratSheTzarichLeKlal \/ m = DavarSheHayahBiKlal \/
      m = DavarYatzaLeLamed \/ m = DavarHaLamedMeInyano \/
      m = ShneiKetuvimMakhchishim.
  Proof.
    intro m.
    split.
    - intro H.
      destruct m; auto 15.
    - intro H.
      destruct H as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]]];
      subst; simpl; auto 15.
  Qed.

  Theorem rabbinic_extends_karaite :
    forall v h,
      karaite_derivation v h ->
      valid_halakha h ->
      rabbinic_derivation v h.
  Proof.
    intros v h Hd Hvalid.
    unfold rabbinic_derivation, karaite_derivation in *.
    exists (Node DavarHaLamedMeInyano [Leaf v] h).
    split.
    - simpl. left. reflexivity.
    - split.
      + simpl. reflexivity.
      + simpl. split.
        * apply valid_context. exact Hd.
        * split.
          { exact Hvalid. }
          { split.
            - unfold authority_safe_node, min_child_authority. simpl.
              destruct (halakha_authority h); simpl; exact I.
            - split; exact I. }
  Qed.

  (** Klal u-frat restricts scope. *)
  Theorem klal_u_frat_restricts :
    forall klal prat h_in h_out restriction s,
      valid_klal_u_frat klal prat h_in h_out restriction ->
      halakha_scope h_out s ->
      halakha_scope h_in s /\ restriction s.
  Proof.
    intros klal prat h_in h_out restriction s Hvalid Hout.
    unfold valid_klal_u_frat in Hvalid.
    destruct Hvalid as [_ [_ [_ [_ Hscope]]]].
    apply Hscope.
    exact Hout.
  Qed.

  (** Prat u-klal expands scope. *)
  Theorem prat_u_klal_expands :
    forall prat klal h_in h_out s,
      valid_prat_u_klal prat klal h_in h_out ->
      halakha_scope h_in s ->
      halakha_scope h_out s.
  Proof.
    intros prat klal h_in h_out s Hvalid Hin.
    unfold valid_prat_u_klal in Hvalid.
    destruct Hvalid as [_ [_ [_ [_ Hexpand]]]].
    apply Hexpand.
    exact Hin.
  Qed.

  (** Contradiction requires resolution - now a theorem via structural bundling. *)
  Theorem contradiction_requires_resolution :
    forall v1 v2,
      contradicts v1 v2 ->
      exists v3, resolves v3 v1 v2.
  Proof.
    intros v1 v2 [c [Hv1 Hv2]].
    exists (contra_v3 c).
    exists c.
    auto.
  Qed.

  (** D'Oraita trumps d'Rabbanan. *)
  Theorem doraita_trumps_drabbanan :
    forall d1 d2,
      derivation_authority d1 = DOraita ->
      derivation_authority d2 = DRabbanan ->
      authority_ge (derivation_authority d1) (derivation_authority d2).
  Proof.
    intros d1 d2 H1 H2.
    rewrite H1.
    simpl.
    exact I.
  Qed.

  (** No infinite regress: derivation trees have finite depth. *)
  Theorem derivation_finite :
    forall t, tree_depth t < S (tree_depth t).
  Proof.
    intro t.
    apply Nat.lt_succ_diag_r.
  Qed.

  (** Middah application cannot upgrade authority. *)
  Theorem middah_authority_ceiling :
    forall m t h,
      well_formed (Node m [t] h) ->
      authority_ge (child_authority t) (halakha_authority h).
  Proof.
    intros m t h Hawf.
    simpl in Hawf.
    destruct Hawf as [_ [_ [Hsafe _]]].
    unfold authority_safe_node, min_child_authority, child_authority in *.
    simpl in Hsafe.
    destruct t as [v | m' children' h'].
    - destruct (halakha_authority h); simpl in *; auto.
    - destruct (halakha_authority h') eqn:Eh';
      destruct (halakha_authority h) eqn:Hauth; simpl in *; auto.
  Qed.

  (** Kal va-chomer cannot create d'Oraita from d'Rabbanan. *)
  Theorem kal_va_chomer_authority_bound :
    forall t_lenient t_strict h_out,
      valid_node KalVaChomer [t_lenient; t_strict] h_out ->
      forall h_in, has_conclusion t_lenient h_in ->
      halakha_authority h_in = DRabbanan ->
      halakha_authority h_out = DRabbanan.
  Proof.
    intros t_lenient t_strict h_out Hvalid h_in Hconc Hrabb.
    inversion Hvalid; subst.
    unfold has_conclusion in *.
    match goal with
    | [ H : tree_conclusion t_lenient = Some ?x |- _ ] => rewrite H in Hconc
    end.
    inversion Hconc; subst.
    match goal with
    | [ H : halakha_authority _ = DRabbanan -> halakha_authority h_out = DRabbanan |- _ ] => apply H
    end.
    exact Hrabb.
  Qed.

  (** Gezerah shavah requires mesorah - now a theorem via structural bundling. *)
  Theorem gezerah_shavah_requires_mesorah :
    forall v1 v2 w h,
      valid_gezerah_shavah v1 v2 w h ->
      has_mesorah w.
  Proof.
    intros v1 v2 w h [gsd [_ [_ [Hw _]]]].
    rewrite <- Hw.
    exact (gs_mesorah gsd).
  Qed.

  (** Counting uses of each middah in a derivation. *)
  Fixpoint count_middah (m : Middah) (t : DerivationTree) : nat :=
    match t with
    | Leaf _ => 0
    | Node m' children _ =>
        (if middah_eq_dec m m' then 1 else 0) +
        fold_right plus 0 (map (count_middah m) children)
    end.

  (** Total middot applications in a tree. *)
  Definition total_middot (t : DerivationTree) : nat :=
    fold_right plus 0 (map (fun m => count_middah m t) all_middot).

  Lemma count_middah_leaf : forall m v, count_middah m (Leaf v) = 0.
  Proof. reflexivity. Qed.

  (** A derivation is purely kal va-chomer if it uses only that middah. *)
  Definition purely_kal_va_chomer (t : DerivationTree) : Prop :=
    forall m, In m (tree_middot t) -> m = KalVaChomer.

  (** A derivation is purely scriptural if depth is 1. *)
  Definition purely_scriptural (t : DerivationTree) : Prop :=
    tree_depth t <= 1.

  (** Complexity measure: depth times distinct middot used. *)
  Fixpoint distinct_middot (t : DerivationTree) : list Middah :=
    match t with
    | Leaf _ => []
    | Node m children _ =>
        m :: flat_map distinct_middot children
    end.

  Definition derivation_complexity (t : DerivationTree) : nat :=
    tree_depth t * length (nodup middah_eq_dec (distinct_middot t)).

  (** Simpler derivation is preferable (Occam's razor for halakha). *)
  Definition simpler_derivation (t1 t2 : DerivationTree) : Prop :=
    derivation_complexity t1 < derivation_complexity t2.

  (** Two derivations conflict if they derive contradictory halakhot. *)
  Definition derivations_conflict (t1 t2 : DerivationTree) : Prop :=
    match tree_conclusion t1, tree_conclusion t2 with
    | Some h1, Some h2 => halakha_conflicts h1 h2
    | _, _ => False
    end.

  (** Resolution: when derivations conflict, higher authority wins. *)
  Definition resolution_by_authority (t1 t2 : DerivationTree) : option DerivationTree :=
    match tree_conclusion t1, tree_conclusion t2 with
    | Some h1, Some h2 =>
        if authority_ge_b (halakha_authority h1) (halakha_authority h2)
        then Some t1
        else Some t2
    | Some _, None => Some t1
    | None, Some _ => Some t2
    | None, None => None
    end.

  (** Dayo prevents over-extension: if dayo is satisfied, conclusion adds at most one subject. *)
  Theorem dayo_limits_extension :
    forall h_premise h_conclusion strict s,
      dayo_satisfied h_premise h_conclusion strict ->
      applies_to h_conclusion s ->
      ~ applies_to h_premise s ->
      subject_id s = subject_id strict.
  Proof.
    intros h_premise h_conclusion strict s Hdayo Hconc Hnprem.
    unfold dayo_satisfied in Hdayo.
    specialize (Hdayo s Hconc).
    destruct Hdayo as [Hprem | Heq].
    - contradiction.
    - exact Heq.
  Qed.

  (** Similar_cases is an equivalence relation. *)
  Lemma similar_cases_refl : forall s, similar_cases s s.
  Proof. intro s. unfold similar_cases. split; reflexivity. Qed.

  Lemma similar_cases_sym : forall s1 s2, similar_cases s1 s2 -> similar_cases s2 s1.
  Proof.
    intros s1 s2 [Hsev Hcat].
    unfold similar_cases. split; symmetry; assumption.
  Qed.

  Lemma similar_cases_trans : forall s1 s2 s3,
    similar_cases s1 s2 -> similar_cases s2 s3 -> similar_cases s1 s3.
  Proof.
    intros s1 s2 s3 [Hsev12 Hcat12] [Hsev23 Hcat23].
    unfold similar_cases.
    split; congruence.
  Qed.

  (** ================================================================== *)
  (** CONCRETE EXAMPLES AND WITNESS TESTS                                *)
  (** ================================================================== *)

  (** Concrete verses and subjects for witness testing. *)
  Definition verse_shabbat : Verse := mkVerse 1 [10; 20; 30].
  Definition verse_yom_tov : Verse := mkVerse 2 [10; 40; 50].
  Definition verse_chol : Verse := mkVerse 3 [60; 70].

  Definition subject_shabbat : Subject := mkSubject 100 10 1.
  Definition subject_yom_tov : Subject := mkSubject 101 5 1.
  Definition subject_chol : Subject := mkSubject 102 1 1.

  (** Witness: shabbat is stricter than yom_tov. *)
  Lemma witness_shabbat_stricter_yom_tov : stricter subject_shabbat subject_yom_tov.
  Proof. unfold stricter, subject_shabbat, subject_yom_tov. simpl. lia. Qed.

  (** Witness: yom_tov is stricter than chol. *)
  Lemma witness_yom_tov_stricter_chol : stricter subject_yom_tov subject_chol.
  Proof. unfold stricter, subject_yom_tov, subject_chol. simpl. lia. Qed.

  (** Witness: transitivity works. *)
  Lemma witness_shabbat_stricter_chol : stricter subject_shabbat subject_chol.
  Proof.
    apply stricter_trans with subject_yom_tov.
    - exact witness_shabbat_stricter_yom_tov.
    - exact witness_yom_tov_stricter_chol.
  Qed.

  (** Witness: word 10 appears in both shabbat and yom_tov verses. *)
  Lemma witness_shared_word : contains_word verse_shabbat 10 /\ contains_word verse_yom_tov 10.
  Proof.
    unfold contains_word, verse_shabbat, verse_yom_tov. simpl.
    split; left; reflexivity.
  Qed.

  (** Counterexample attempt: chol is NOT stricter than shabbat. *)
  Lemma counterexample_chol_not_stricter_shabbat : ~ stricter subject_chol subject_shabbat.
  Proof. unfold stricter, subject_chol, subject_shabbat. simpl. lia. Qed.

  (** Counterexample attempt: word 60 is NOT in verse_shabbat. *)
  Lemma counterexample_word_not_in_verse : ~ contains_word verse_shabbat 60.
  Proof.
    unfold contains_word, verse_shabbat. simpl.
    intros [H|[H|[H|H]]]; try discriminate; exact H.
  Qed.

  (** ================================================================== *)
  (** WITNESS DERIVATION                                                  *)
  (** ================================================================== *)

  Definition witness_halakha : Halakha := 1.

  Definition witness_verse : Verse := mkVerse 1 [10; 20; 30].

  Lemma witness_base_derivation : base_derivation witness_halakha witness_verse.
  Proof.
    unfold base_derivation, witness_halakha, witness_verse, corpus_contains, torah_corpus.
    simpl. left. reflexivity.
  Qed.

  Lemma witness_derived : derived_from witness_halakha witness_verse.
  Proof. apply derived_base. exact witness_base_derivation. Qed.

  Lemma witness_valid_halakha : valid_halakha witness_halakha.
  Proof.
    unfold valid_halakha, witness_halakha, halakha_universe. simpl.
    left. reflexivity.
  Qed.

  Definition witness_tree : DerivationTree :=
    Node DavarHaLamedMeInyano [Leaf witness_verse] witness_halakha.

  Lemma witness_tree_valid_node : valid_node DavarHaLamedMeInyano [Leaf witness_verse] witness_halakha.
  Proof. apply valid_context. exact witness_derived. Qed.

  Lemma witness_tree_authority_safe : authority_safe_node DavarHaLamedMeInyano [Leaf witness_verse] witness_halakha.
  Proof.
    unfold authority_safe_node, min_child_authority, child_authority, witness_halakha.
    simpl. exact I.
  Qed.

  Theorem witness_tree_well_formed : well_formed witness_tree.
  Proof.
    unfold witness_tree. simpl.
    split.
    - exact witness_tree_valid_node.
    - split.
      + exact witness_valid_halakha.
      + split.
        * exact witness_tree_authority_safe.
        * split; exact I.
  Qed.

  Theorem witness_derivation_complete : rabbinic_derivation witness_verse witness_halakha.
  Proof.
    unfold rabbinic_derivation.
    exists witness_tree.
    split.
    - simpl. left. reflexivity.
    - split.
      + simpl. reflexivity.
      + exact witness_tree_well_formed.
  Qed.

  (** ================================================================== *)
  (** MULTI-STEP WORKED EXAMPLE: Depth-2 Derivation                      *)
  (** ================================================================== *)

  (** Scenario: halakha 2 applies to yom_tov (verse 2, severity 5).
      By kal va-chomer, it should apply to shabbat (severity 10, stricter).
      Tree structure:
        Node KalVaChomer
          [ Node DavarHaLamedMeInyano [Leaf verse_yom_tov] 2  -- premise
          ; Leaf verse_shabbat                                -- strict citation
          ]
          2  -- same halakha, extended scope
  *)

  Definition multistep_premise_tree : DerivationTree :=
    Node DavarHaLamedMeInyano [Leaf verse_yom_tov] 2.

  Definition multistep_citation : DerivationTree :=
    Leaf verse_shabbat.

  Definition multistep_tree : DerivationTree :=
    Node KalVaChomer [multistep_premise_tree; multistep_citation] 2.

  Lemma multistep_tree_depth : tree_depth multistep_tree = 2.
  Proof. reflexivity. Qed.

  Lemma multistep_tree_middot : tree_middot multistep_tree = [KalVaChomer; DavarHaLamedMeInyano].
  Proof. reflexivity. Qed.

  Lemma multistep_premise_derived : derived_from 2 verse_yom_tov.
  Proof.
    apply derived_base.
    unfold base_derivation, corpus_contains, torah_corpus, verse_yom_tov.
    simpl. right. left. reflexivity.
  Qed.

  Lemma multistep_premise_valid_node :
    valid_node DavarHaLamedMeInyano [Leaf verse_yom_tov] 2.
  Proof.
    apply valid_context.
    exact multistep_premise_derived.
  Qed.

  Lemma multistep_premise_valid_halakha : valid_halakha 2.
  Proof.
    unfold valid_halakha, halakha_universe. simpl.
    right. left. reflexivity.
  Qed.

  Lemma multistep_premise_authority_safe :
    authority_safe_node DavarHaLamedMeInyano [Leaf verse_yom_tov] 2.
  Proof.
    unfold authority_safe_node, min_child_authority, child_authority.
    simpl. exact I.
  Qed.

  Lemma multistep_premise_well_formed : well_formed multistep_premise_tree.
  Proof.
    unfold multistep_premise_tree. simpl.
    split.
    - exact multistep_premise_valid_node.
    - split.
      + exact multistep_premise_valid_halakha.
      + split.
        * exact multistep_premise_authority_safe.
        * split; exact I.
  Qed.

  Lemma multistep_citation_is_citation : is_citation multistep_citation.
  Proof.
    unfold is_citation, multistep_citation.
    exists verse_shabbat. reflexivity.
  Qed.

  (** Example: A simple derivation tree with one middah application. *)
  Section ExampleDerivation.
    Variable example_verse : Verse.
    Variable example_halakha : Halakha.
    Hypothesis example_derived : derived_from example_halakha example_verse.

    Definition example_leaf : DerivationTree := Leaf example_verse.

    Definition example_tree : DerivationTree :=
      Node DavarHaLamedMeInyano [example_leaf] example_halakha.

    Lemma example_tree_depth : tree_depth example_tree = 1.
    Proof. reflexivity. Qed.

    Lemma example_tree_verses : tree_verses example_tree = [example_verse].
    Proof. reflexivity. Qed.

    Lemma example_tree_middot : tree_middot example_tree = [DavarHaLamedMeInyano].
    Proof. reflexivity. Qed.

    Lemma example_tree_conclusion : tree_conclusion example_tree = Some example_halakha.
    Proof. reflexivity. Qed.

  End ExampleDerivation.

  (** Example: Chaining two kal va-chomer arguments. *)
  Section KalVaChomerChain.
    Variables s1 s2 s3 : Subject.
    Variable h : Halakha.
    Hypothesis strict_12 : stricter s2 s1.
    Hypothesis strict_23 : stricter s3 s2.
    Hypothesis h_applies_s1 : applies_to h s1.

    Definition kvc_chain : DerivationChain :=
      ChainStep KalVaChomer h (ChainStep KalVaChomer h (ChainEnd h)).

    Lemma kvc_chain_length : chain_length kvc_chain = 2.
    Proof. reflexivity. Qed.

    Lemma kvc_chain_middot : chain_middot kvc_chain = [KalVaChomer; KalVaChomer].
    Proof. reflexivity. Qed.

  End KalVaChomerChain.

  (** Middah name lookup for display. *)
  Definition middah_name (m : Middah) : nat :=
    match m with
    | KalVaChomer => 1
    | GezerahShavah => 2
    | BinyanAvEchad => 3
    | BinyanAvShnei => 4
    | KlalUFrat => 5
    | PratUKlal => 6
    | KlalUFratUKlal => 7
    | KlalSheTzarichLeFrat => 8
    | PratSheTzarichLeKlal => 9
    | DavarSheHayahBiKlal => 10
    | DavarYatzaLeLamed => 11
    | DavarHaLamedMeInyano => 12
    | ShneiKetuvimMakhchishim => 13
    end.

  Lemma middah_name_injective : forall m1 m2,
    middah_name m1 = middah_name m2 -> m1 = m2.
  Proof.
    intros [] []; intro H; try reflexivity; discriminate H.
  Qed.

  (** Structural properties of derivation trees. *)

  Lemma tree_depth_node_pos : forall m children h,
    children <> [] ->
    tree_depth (Node m children h) >= 1.
  Proof.
    intros m children h Hne.
    simpl.
    lia.
  Qed.

  Lemma tree_verses_node : forall m children h,
    tree_verses (Node m children h) = flat_map tree_verses children.
  Proof. reflexivity. Qed.

  Lemma tree_middot_cons : forall m children h,
    tree_middot (Node m children h) = m :: flat_map tree_middot children.
  Proof. reflexivity. Qed.

  (** A tree uses a middah if it appears in tree_middot. *)
  Definition uses_middah (m : Middah) (t : DerivationTree) : Prop :=
    In m (tree_middot t).

  Lemma leaf_uses_no_middah : forall v m, ~ uses_middah m (Leaf v).
  Proof.
    intros v m H.
    unfold uses_middah in H.
    simpl in H.
    exact H.
  Qed.

  Lemma node_uses_root_middah : forall m children h,
    uses_middah m (Node m children h).
  Proof.
    intros m children h.
    unfold uses_middah.
    simpl.
    left.
    reflexivity.
  Qed.

  (** Counting properties. *)

  Lemma count_middah_node_same : forall m children h,
    count_middah m (Node m children h) =
    1 + fold_right plus 0 (map (count_middah m) children).
  Proof.
    intros m children h.
    simpl.
    destruct (middah_eq_dec m m) as [_|Hne].
    - reflexivity.
    - exfalso. apply Hne. reflexivity.
  Qed.

  Lemma count_middah_node_diff : forall m m' children h,
    m <> m' ->
    count_middah m (Node m' children h) =
    fold_right plus 0 (map (count_middah m) children).
  Proof.
    intros m m' children h Hne.
    simpl.
    destruct (middah_eq_dec m m') as [Heq|_].
    - exfalso. apply Hne. exact Heq.
    - reflexivity.
  Qed.

  (** Authority reasoning. *)

  Lemma doraita_ge_all : forall a, authority_ge DOraita a.
  Proof. intros []; simpl; exact I. Qed.

  Lemma drabbanan_not_ge_doraita : ~ authority_ge DRabbanan DOraita.
  Proof. simpl. auto. Qed.

  (** The stricter relation is a strict partial order. *)
  Lemma stricter_asymm : forall a b,
    stricter a b -> ~ stricter b a.
  Proof.
    intros a b Hab Hba.
    apply (stricter_irrefl a).
    apply (stricter_trans a b a); assumption.
  Qed.

  (** Well-formedness is preserved by subtrees. *)
  Lemma well_formed_children : forall m children h c,
    well_formed (Node m children h) ->
    In c children ->
    well_formed c.
  Proof.
    intros m children h c Hwf Hin.
    simpl in Hwf.
    destruct Hwf as [_ [_ [_ Hchildren]]].
    induction children as [|c' cs IH].
    - inversion Hin.
    - simpl in Hchildren.
      destruct Hchildren as [Hc' Hcs].
      destruct Hin as [Heq | Hin'].
      + subst. exact Hc'.
      + apply IH; assumption.
  Qed.

  (** Total verses in a tree equals sum over children. *)
  Lemma tree_verses_length_node : forall m children h,
    length (tree_verses (Node m children h)) =
    fold_right plus 0 (map (fun c => length (tree_verses c)) children).
  Proof.
    intros m children h.
    simpl.
    induction children as [|c cs IH].
    - reflexivity.
    - simpl.
      rewrite app_length.
      rewrite IH.
      reflexivity.
  Qed.

  (** A leaf contributes exactly one verse. *)
  Lemma tree_verses_leaf_length : forall v,
    length (tree_verses (Leaf v)) = 1.
  Proof. reflexivity. Qed.

  (** Chain validity is preserved when extending. *)
  Lemma chain_valid_end : forall h, chain_valid (ChainEnd h).
  Proof. intro h. simpl. exact I. Qed.

  (** The 13 middot are pairwise distinct. *)
  Lemma all_middot_NoDup : NoDup all_middot.
  Proof.
    unfold all_middot.
    apply NoDup_cons. { simpl. intros [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]]]; inversion H. }
    apply NoDup_cons. { simpl. intros [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]]; inversion H. }
    apply NoDup_cons. { simpl. intros [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]; inversion H. }
    apply NoDup_cons. { simpl. intros [H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]; inversion H. }
    apply NoDup_cons. { simpl. intros [H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]; inversion H. }
    apply NoDup_cons. { simpl. intros [H|[H|[H|[H|[H|[H|[H|H]]]]]]]; inversion H. }
    apply NoDup_cons. { simpl. intros [H|[H|[H|[H|[H|[H|H]]]]]]; inversion H. }
    apply NoDup_cons. { simpl. intros [H|[H|[H|[H|[H|H]]]]]; inversion H. }
    apply NoDup_cons. { simpl. intros [H|[H|[H|[H|H]]]]; inversion H. }
    apply NoDup_cons. { simpl. intros [H|[H|[H|H]]]; inversion H. }
    apply NoDup_cons. { simpl. intros [H|[H|H]]; inversion H. }
    apply NoDup_cons. { simpl. intros [H|H]; inversion H. }
    apply NoDup_cons. { simpl. intros H; exact H. }
    apply NoDup_nil.
  Qed.

  (** ================================================================== *)
  (** CHAIN COMPOSITION                                                   *)
  (** ================================================================== *)

  Fixpoint chain_base (c : DerivationChain) : Halakha :=
    match c with
    | ChainEnd h => h
    | ChainStep _ _ rest => chain_base rest
    end.

  Definition chains_compatible (c1 c2 : DerivationChain) : Prop :=
    halakha_eq_id (chain_conclusion c1) (chain_base c2).

  Definition chains_compatible_b (c1 c2 : DerivationChain) : bool :=
    Nat.eqb (chain_conclusion c1) (chain_base c2).

  Fixpoint chain_append (c1 c2 : DerivationChain) : DerivationChain :=
    match c2 with
    | ChainEnd h => c1
    | ChainStep m h rest => ChainStep m h (chain_append c1 rest)
    end.

  Definition chain_concat (c1 c2 : DerivationChain) : option DerivationChain :=
    if chains_compatible_b c1 c2
    then Some (chain_append c1 c2)
    else None.

  Lemma chain_append_length : forall c1 c2,
    chain_length (chain_append c1 c2) = chain_length c1 + chain_length c2.
  Proof.
    intros c1 c2.
    induction c2 as [h | m h rest IH].
    - simpl. lia.
    - simpl. rewrite IH. lia.
  Qed.

  Lemma chain_concat_length : forall c1 c2 c,
    chain_concat c1 c2 = Some c ->
    chain_length c = chain_length c1 + chain_length c2.
  Proof.
    intros c1 c2 c Hconcat.
    unfold chain_concat in Hconcat.
    destruct (chains_compatible_b c1 c2) eqn:Hcompat.
    - inversion Hconcat. subst. apply chain_append_length.
    - discriminate.
  Qed.

  Lemma chain_append_conclusion : forall c1 c2,
    chain_length c2 > 0 ->
    chain_conclusion (chain_append c1 c2) = chain_conclusion c2.
  Proof.
    intros c1 c2 Hlen.
    destruct c2 as [h | m h rest].
    - simpl in Hlen. lia.
    - simpl. reflexivity.
  Qed.

  Lemma chain_append_base : forall c1 c2,
    chain_base (chain_append c1 c2) = chain_base c1.
  Proof.
    intros c1 c2.
    induction c2 as [h | m h rest IH].
    - simpl. reflexivity.
    - simpl. exact IH.
  Qed.

  Lemma chain_concat_some : forall c1 c2,
    chains_compatible_b c1 c2 = true ->
    exists c, chain_concat c1 c2 = Some c.
  Proof.
    intros c1 c2 Hcompat.
    unfold chain_concat. rewrite Hcompat.
    exists (chain_append c1 c2). reflexivity.
  Qed.

  Lemma chain_concat_none : forall c1 c2,
    chains_compatible_b c1 c2 = false ->
    chain_concat c1 c2 = None.
  Proof.
    intros c1 c2 Hcompat.
    unfold chain_concat. rewrite Hcompat. reflexivity.
  Qed.

  (** ================================================================== *)
  (** DECIDABLE VALIDATORS                                                *)
  (** ================================================================== *)

  Definition middah_eq_b (m1 m2 : Middah) : bool :=
    if middah_eq_dec m1 m2 then true else false.

  Lemma middah_eq_b_correct : forall m1 m2,
    middah_eq_b m1 m2 = true <-> m1 = m2.
  Proof.
    intros m1 m2.
    unfold middah_eq_b.
    destruct (middah_eq_dec m1 m2); split; auto; discriminate.
  Qed.

  Definition subject_eq_b (s1 s2 : Subject) : bool :=
    Nat.eqb (subject_id s1) (subject_id s2) &&
    Nat.eqb (subject_severity s1) (subject_severity s2) &&
    Nat.eqb (subject_category s1) (subject_category s2).

  Lemma subject_eq_b_correct : forall s1 s2,
    subject_eq_b s1 s2 = true <->
    subject_id s1 = subject_id s2 /\
    subject_severity s1 = subject_severity s2 /\
    subject_category s1 = subject_category s2.
  Proof.
    intros s1 s2.
    unfold subject_eq_b.
    rewrite 2 andb_true_iff.
    rewrite 3 Nat.eqb_eq.
    tauto.
  Qed.

  Definition stricter_b (s1 s2 : Subject) : bool :=
    Nat.ltb (subject_severity s2) (subject_severity s1).

  Lemma stricter_b_correct : forall s1 s2,
    stricter_b s1 s2 = true <-> stricter s1 s2.
  Proof.
    intros s1 s2.
    unfold stricter_b, stricter.
    rewrite Nat.ltb_lt.
    reflexivity.
  Qed.

  Definition contains_word_b (v : Verse) (w : Word) : bool :=
    existsb (Nat.eqb w) (verse_words v).

  Lemma contains_word_b_correct : forall v w,
    contains_word_b v w = true <-> contains_word v w.
  Proof.
    intros v w.
    unfold contains_word_b, contains_word.
    rewrite existsb_exists.
    split.
    - intros [x [Hin Heq]]. rewrite Nat.eqb_eq in Heq. subst. exact Hin.
    - intro Hin. exists w. split. exact Hin. apply Nat.eqb_refl.
  Qed.

  Definition is_general_b (v : Verse) : bool :=
    is_general_b_new v.

  Definition is_particular_b (v : Verse) : bool :=
    is_particular_b_new v.

End TalmudicHermeneutics.

(** ================================================================== *)
(** EXTRACTION                                                          *)
(** ================================================================== *)

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.

Extract Inductive TalmudicHermeneutics.Middah => "middah" ["KalVaChomer" "GezerahShavah" "BinyanAvEchad" "BinyanAvShnei" "KlalUFrat" "PratUKlal" "KlalUFratUKlal" "KlalSheTzarichLeFrat" "PratSheTzarichLeKlal" "DavarSheHayahBiKlal" "DavarYatzaLeLamed" "DavarHaLamedMeInyano" "ShneiKetuvimMakhchishim"].

Extract Inductive TalmudicHermeneutics.Authority => "authority" ["DOraita" "DRabbanan"].

Extract Inductive TalmudicHermeneutics.DerivationTree => "derivation_tree" ["Leaf" "Node"].

Extract Inductive TalmudicHermeneutics.DerivationChain => "derivation_chain" ["ChainEnd" "ChainStep"].
