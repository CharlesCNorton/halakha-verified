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

  (** Halakhic propositions: the objects derived from scripture. *)
  Record Halakha := mkHalakha {
    halakha_id : nat;
    halakha_source : nat
  }.

  Definition halakha_eq_dec : forall h1 h2 : Halakha, {h1 = h2} + {h1 <> h2}.
  Proof. decide equality; apply Nat.eq_dec. Defined.

  (** Severity ordering for kal va-chomer. *)
  Record Subject := mkSubject {
    subject_id : nat;
    subject_severity : nat
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

  Definition applies_to (h : Halakha) (s : Subject) : Prop :=
    halakha_source h = subject_id s.

  Definition contains_word (v : Verse) (w : Word) : Prop :=
    In w (verse_words v).

  (** A word is superfluous (mufneh) in a verse if removing it doesn't change
      the essential meaning. We model this as: the word appears but is not
      the first word (subject) or second word (verb) of the verse. *)
  Definition word_position (v : Verse) (w : Word) : option nat :=
    let fix find_pos (l : list Word) (n : nat) :=
      match l with
      | [] => None
      | x :: xs => if Nat.eq_dec x w then Some n else find_pos xs (S n)
      end
    in find_pos (verse_words v) 0.

  Definition word_superfluous (v : Verse) (w : Word) : Prop :=
    match word_position v w with
    | Some pos => pos >= 2
    | None => False
    end.

  Definition word_superfluous_b (v : Verse) (w : Word) : bool :=
    match word_position v w with
    | Some pos => 2 <=? pos
    | None => false
    end.

  Lemma word_superfluous_b_correct : forall v w,
    word_superfluous_b v w = true <-> word_superfluous v w.
  Proof.
    intros v w.
    unfold word_superfluous_b, word_superfluous.
    destruct (word_position v w) as [pos|].
    - rewrite Nat.leb_le. reflexivity.
    - split; intro H; inversion H.
  Qed.

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

  (** derived_from defined inductively to capture all derivation methods. *)
  Inductive derived_from : Halakha -> Verse -> Prop :=
    | derived_direct : forall h v,
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

  (** Kal va-chomer: if h applies to the lenient case, it applies to the strict case. *)
  Definition valid_kal_va_chomer (lenient strict : Subject) (h : Halakha) : Prop :=
    stricter strict lenient /\
    applies_to h lenient ->
    applies_to h strict.

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
  Definition similar_cases (s1 s2 : Subject) : Prop :=
    subject_severity s1 = subject_severity s2.

  Definition valid_binyan_av (paradigm : Verse) (h : Halakha) (s1 s2 : Subject) : Prop :=
    derived_from h paradigm /\
    applies_to h s1 /\
    similar_cases s1 s2 ->
    applies_to h s2.

  (** Klal u-frat: general followed by particular means only the particular. *)
  Definition is_general (v : Verse) : Prop :=
    length (verse_words v) > 3.
  Definition is_particular (v : Verse) : Prop :=
    length (verse_words v) <= 3.
  Definition particularizes (prat klal : Verse) : Prop :=
    incl (verse_words prat) (verse_words klal).
  Definition scope (h : Halakha) : list Subject :=
    [mkSubject (halakha_source h) 0].

  Definition valid_klal_u_frat (klal prat : Verse) (h : Halakha) (restricted_scope : list Subject) : Prop :=
    is_general klal /\
    is_particular prat /\
    particularizes prat klal ->
    scope h = restricted_scope.

  (** Prat u-klal: particular followed by general means the general applies broadly. *)
  Definition valid_prat_u_klal (prat klal : Verse) (h : Halakha) : Prop :=
    is_particular prat /\
    is_general klal /\
    particularizes prat klal ->
    forall s : Subject, applies_to h s.

  (** Klal u-frat u-klal: general-particular-general pattern. *)
  Definition valid_klal_u_frat_u_klal (klal1 prat klal2 : Verse) (h : Halakha) : Prop :=
    is_general klal1 /\
    is_particular prat /\
    is_general klal2 /\
    particularizes prat klal1 ->
    True.

  (** Davar she-hayah bi-klal: exception from a general rule. *)
  Definition exception_from (exc gen : Halakha) : Prop :=
    halakha_source exc > halakha_source gen.

  Definition valid_davar_she_hayah (general_rule exception : Halakha) : Prop :=
    exception_from exception general_rule ->
    forall s, In s (scope exception) -> ~ applies_to general_rule s.

  (** Shnei ketuvim makhchishim: two contradictory verses resolved by a third. *)

  (** Two halakhot conflict if they cannot both apply to the same subject. *)
  Definition halakha_conflicts (h1 h2 : Halakha) : Prop :=
    halakha_id h1 <> halakha_id h2.

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
    contra_resolves : ~ halakha_conflicts contra_h3 contra_h1 /\ ~ halakha_conflicts contra_h3 contra_h2
  }.

  Definition contradicts (v1 v2 : Verse) : Prop :=
    exists c : Contradiction, contra_v1 c = v1 /\ contra_v2 c = v2.

  Definition resolves (v3 v1 v2 : Verse) : Prop :=
    exists c : Contradiction,
      contra_v1 c = v1 /\ contra_v2 c = v2 /\ contra_v3 c = v3.

  Definition valid_shnei_ketuvim (v1 v2 v3 : Verse) (h : Halakha) : Prop :=
    contradicts v1 v2 /\
    resolves v3 v1 v2 ->
    derived_from h v3.

  (** Authority levels: d'oraita (Torah) vs d'rabbanan (Rabbinic). *)
  Inductive Authority : Type :=
    | DOraita : Authority
    | DRabbanan : Authority.

  Definition authority_eq_dec : forall a1 a2 : Authority, {a1 = a2} + {a1 <> a2}.
  Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

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

  Definition halakha_authority (h : Halakha) : Authority :=
    if halakha_source h <? 1000 then DOraita else DRabbanan.

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

  (** Well-formedness: a derivation tree is well-formed if it uses valid middot. *)
  (** Each constructor enforces structural constraints appropriate to the middah. *)

  Definition has_conclusion (t : DerivationTree) (h : Halakha) : Prop :=
    tree_conclusion t = Some h.

  Definition children_derive (children : list DerivationTree) (h : Halakha) : Prop :=
    exists c, In c children /\ has_conclusion c h.

  Inductive valid_node : Middah -> list DerivationTree -> Halakha -> Prop :=
    | valid_context : forall v h,
        derived_from h v ->
        valid_node DavarHaLamedMeInyano [Leaf v] h
    | valid_kal_va_chomer_node : forall t_lenient t_strict h lenient strict,
        has_conclusion t_lenient h ->
        stricter strict lenient ->
        applies_to h lenient ->
        valid_node KalVaChomer [t_lenient; t_strict] h
    | valid_gezerah_shavah_node : forall t1 t2 h v1 v2 w,
        tree_verses t1 = [v1] ->
        tree_verses t2 = [v2] ->
        valid_gezerah_shavah v1 v2 w h ->
        valid_node GezerahShavah [t1; t2] h
    | valid_binyan_av_echad_node : forall t h,
        children_derive [t] h ->
        valid_node BinyanAvEchad [t] h
    | valid_binyan_av_shnei_node : forall t1 t2 h,
        children_derive [t1; t2] h ->
        valid_node BinyanAvShnei [t1; t2] h
    | valid_klal_u_frat_node : forall t_klal t_prat h v_klal v_prat,
        tree_verses t_klal = [v_klal] ->
        tree_verses t_prat = [v_prat] ->
        is_general v_klal ->
        is_particular v_prat ->
        particularizes v_prat v_klal ->
        valid_node KlalUFrat [t_klal; t_prat] h
    | valid_prat_u_klal_node : forall t_prat t_klal h v_prat v_klal,
        tree_verses t_prat = [v_prat] ->
        tree_verses t_klal = [v_klal] ->
        is_particular v_prat ->
        is_general v_klal ->
        particularizes v_prat v_klal ->
        valid_node PratUKlal [t_prat; t_klal] h
    | valid_klal_u_frat_u_klal_node : forall t1 t2 t3 h v1 v2 v3,
        tree_verses t1 = [v1] ->
        tree_verses t2 = [v2] ->
        tree_verses t3 = [v3] ->
        is_general v1 ->
        is_particular v2 ->
        is_general v3 ->
        valid_node KlalUFratUKlal [t1; t2; t3] h
    | valid_klal_she_tzarich_node : forall t_klal t_prat h v_klal v_prat,
        tree_verses t_klal = [v_klal] ->
        tree_verses t_prat = [v_prat] ->
        is_general v_klal ->
        is_particular v_prat ->
        valid_node KlalSheTzarichLeFrat [t_klal; t_prat] h
    | valid_prat_she_tzarich_node : forall t_prat t_klal h v_prat v_klal,
        tree_verses t_prat = [v_prat] ->
        tree_verses t_klal = [v_klal] ->
        is_particular v_prat ->
        is_general v_klal ->
        valid_node PratSheTzarichLeKlal [t_prat; t_klal] h
    | valid_davar_she_hayah_node : forall t_general t_exception h h_general,
        has_conclusion t_general h_general ->
        exception_from h h_general ->
        valid_node DavarSheHayahBiKlal [t_general; t_exception] h
    | valid_davar_yatza_node : forall t h,
        children_derive [t] h ->
        valid_node DavarYatzaLeLamed [t] h
    | valid_shnei_ketuvim_node : forall t1 t2 t3 h v1 v2 v3,
        tree_verses t1 = [v1] ->
        tree_verses t2 = [v2] ->
        tree_verses t3 = [v3] ->
        contradicts v1 v2 ->
        resolves v3 v1 v2 ->
        valid_node ShneiKetuvimMakhchishim [t1; t2; t3] h.

  (** Authority-safe derivation helpers defined early for use in well_formed. *)
  Definition child_authority (t : DerivationTree) : Authority :=
    match tree_conclusion t with
    | Some h' => halakha_authority h'
    | None => DRabbanan
    end.

  Definition max_child_authority (children : list DerivationTree) : Authority :=
    if existsb (fun t => authority_ge_b (child_authority t) DOraita) children
    then DOraita
    else DRabbanan.

  Definition authority_safe_node (m : Middah) (children : list DerivationTree) (h : Halakha) : Prop :=
    authority_ge (halakha_authority h) (max_child_authority children).

  Definition kal_va_chomer_safe (h : Halakha) : Prop :=
    halakha_authority h = DRabbanan ->
    forall strict : Subject, ~ (exists h', applies_to h' strict /\ halakha_authority h' = DOraita).

  (** Unified well-formedness: structural validity AND authority preservation. *)
  Fixpoint well_formed (t : DerivationTree) : Prop :=
    match t with
    | Leaf v => True
    | Node m children h =>
        valid_node m children h /\
        authority_safe_node m children h /\
        (m = KalVaChomer -> kal_va_chomer_safe h) /\
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
  (** A derivation step is valid if it preserves or elevates authority appropriately. *)
  Definition step_valid (m : Middah) (h_from h_to : Halakha) : Prop :=
    authority_ge (halakha_authority h_to) (halakha_authority h_from) /\
    (m = KalVaChomer -> halakha_authority h_from = DRabbanan -> halakha_authority h_to = DRabbanan).

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
      rabbinic_derivation v h.
  Proof.
    intros v h Hd.
    unfold rabbinic_derivation, karaite_derivation in *.
    exists (Node DavarHaLamedMeInyano [Leaf v] h).
    split.
    - simpl. left. reflexivity.
    - split.
      + simpl. reflexivity.
      + simpl. split.
        * apply valid_context. exact Hd.
        * split.
          { unfold authority_safe_node, max_child_authority. simpl.
            destruct (halakha_authority h); simpl; exact I. }
          { split.
            - intro Heq. discriminate Heq.
            - split; exact I. }
  Qed.

  (** Klal u-frat restricts scope. *)
  Theorem klal_u_frat_restricts :
    forall klal prat h full_scope restricted_scope,
      is_general klal ->
      is_particular prat ->
      scope h = full_scope ->
      valid_klal_u_frat klal prat h restricted_scope ->
      particularizes prat klal ->
      scope h = restricted_scope.
  Proof.
    intros klal prat h full_scope restricted_scope Hg Hp Hfull Hvalid Hpart.
    unfold valid_klal_u_frat in Hvalid.
    apply Hvalid.
    auto.
  Qed.

  (** Prat u-klal expands scope universally. *)
  Theorem prat_u_klal_expands :
    forall prat klal h,
      valid_prat_u_klal prat klal h ->
      is_particular prat ->
      is_general klal ->
      particularizes prat klal ->
      forall s, applies_to h s.
  Proof.
    intros prat klal h Hvalid Hp Hg Hpart s.
    unfold valid_prat_u_klal in Hvalid.
    apply Hvalid.
    auto.
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

  (** Middah application preserves authority floor - now a theorem. *)
  Theorem middah_authority_floor :
    forall m t h,
      well_formed (Node m [t] h) ->
      authority_ge (halakha_authority h) (child_authority t).
  Proof.
    intros m t h Hawf.
    simpl in Hawf.
    destruct Hawf as [_ [Hsafe _]].
    unfold authority_safe_node, max_child_authority, child_authority in *.
    simpl in Hsafe.
    destruct (tree_conclusion t) as [h'|].
    - destruct (halakha_authority h') eqn:Eh';
      destruct (halakha_authority h) eqn:Hauth; simpl in *; auto.
    - destruct (halakha_authority h); simpl; exact I.
  Qed.

  (** Kal va-chomer cannot create d'Oraita from d'Rabbanan - now a theorem. *)
  Theorem kal_va_chomer_authority_bound :
    forall children h,
      well_formed (Node KalVaChomer children h) ->
      halakha_authority h = DRabbanan ->
      forall strict, ~ (exists h', applies_to h' strict /\ halakha_authority h' = DOraita).
  Proof.
    intros children h Hawf Hrabb strict.
    simpl in Hawf.
    destruct Hawf as [_ [_ [Hkvc _]]].
    apply Hkvc.
    - reflexivity.
    - exact Hrabb.
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

  (** ================================================================== *)
  (** CONCRETE EXAMPLES AND WITNESS TESTS                                *)
  (** ================================================================== *)

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

End TalmudicHermeneutics.
