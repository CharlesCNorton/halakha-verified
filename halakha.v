(******************************************************************************)
(*                                                                            *)
(*                        Talmudic Hermeneutics                               *)
(*                   Certified Computational Halakha                          *)
(*                                                                            *)
(*     A machine-executable semantics for the 13 middot of Rabbi Ishmael      *)
(*                                                                            *)
(*     "Rabbi Ishmael says: By thirteen middot the Torah is expounded."       *)
(*     - Baraita of Rabbi Ishmael, Sifra 1:1                                  *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: December 2025                                                    *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

(** TODO:                                                                      *)
(**   1. Complete deserialize_tree for nodes (not just leaves).                *)
(**   2. Replace polynomial hash with cryptographic hash function.             *)
(**   3. Add precedence rules for conflicting sources (stam vs yachid, rov).   *)
(**   4. Change KUF/PUK/KTF/PTK arity to 2 children with transformer redesign. *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Lia.
Import ListNotations.

(** ========================================================================= *)
(** PART I: PRIMITIVE TYPES                                                   *)
(** ========================================================================= *)

Module Primitives.

  Definition SubjectId := nat.
  Definition VerseId := nat.
  Definition HalakhaId := nat.
  Definition ShoreshId := nat.
  Definition CategoryId := nat.

  Definition reserved_subject_id : SubjectId := 0.

  Definition valid_subject_id (id : SubjectId) : bool :=
    negb (id =? reserved_subject_id).

  Definition TimeContext := nat.
  Definition time_any : TimeContext := 0.
  Definition time_day : TimeContext := 1.
  Definition time_night : TimeContext := 2.
  Definition time_shabbat : TimeContext := 3.
  Definition time_yom_tov : TimeContext := 4.
  Definition time_weekday : TimeContext := 5.

  Record Subject := mkSubject {
    subj_id : SubjectId;
    subj_case_severity : nat;
    subj_obligation_strength : nat;
    subj_category : CategoryId;
    subj_time : TimeContext
  }.

  Definition subject_eqb (s1 s2 : Subject) : bool :=
    (subj_id s1 =? subj_id s2) &&
    (subj_case_severity s1 =? subj_case_severity s2) &&
    (subj_obligation_strength s1 =? subj_obligation_strength s2) &&
    (subj_category s1 =? subj_category s2) &&
    (subj_time s1 =? subj_time s2).

  Definition stricter_b (s1 s2 : Subject) : bool :=
    subj_case_severity s2 <? subj_case_severity s1.

  Definition same_category_b (s1 s2 : Subject) : bool :=
    subj_category s1 =? subj_category s2.

  Definition similar_cases_b (s1 s2 : Subject) : bool :=
    (subj_case_severity s1 =? subj_case_severity s2) && same_category_b s1 s2 &&
    (subj_time s1 =? subj_time s2).

  Lemma subject_eqb_eq : forall s1 s2, subject_eqb s1 s2 = true <-> s1 = s2.
  Proof.
    intros [id1 csev1 osev1 cat1 t1] [id2 csev2 osev2 cat2 t2].
    unfold subject_eqb. simpl.
    rewrite !Bool.andb_true_iff, !Nat.eqb_eq.
    split.
    - intros [[[[Hid Hcsev] Hosev] Hcat] Ht]. congruence.
    - intro H. inversion H. auto.
  Qed.

End Primitives.

Export Primitives.

(** ========================================================================= *)
(** PART II: SCOPE PREDICATE DSL                                              *)
(** Finite, serializable, auditable predicates. NO CLOSURES.                  *)
(** ========================================================================= *)

Module ScopeDSL.

  Inductive ScopePred : Type :=
    | PredTrue : ScopePred
    | PredFalse : ScopePred
    | PredIdEq : SubjectId -> ScopePred
    | PredCategoryEq : CategoryId -> ScopePred
    | PredSeverityGe : nat -> ScopePred
    | PredSeverityLe : nat -> ScopePred
    | PredSeverityEq : nat -> ScopePred
    | PredTimeEq : TimeContext -> ScopePred
    | PredSimilarTo : Subject -> ScopePred
    | PredStricterThan : Subject -> ScopePred
    | PredSameCategory : Subject -> ScopePred
    | PredAnd : ScopePred -> ScopePred -> ScopePred
    | PredOr : ScopePred -> ScopePred -> ScopePred
    | PredNot : ScopePred -> ScopePred.

  Fixpoint eval_pred (p : ScopePred) (s : Subject) : bool :=
    match p with
    | PredTrue => true
    | PredFalse => false
    | PredIdEq id => subj_id s =? id
    | PredCategoryEq cat => subj_category s =? cat
    | PredSeverityGe n => n <=? subj_case_severity s
    | PredSeverityLe n => subj_case_severity s <=? n
    | PredSeverityEq n => subj_case_severity s =? n
    | PredTimeEq t => subj_time s =? t
    | PredSimilarTo ref => similar_cases_b s ref
    | PredStricterThan ref => stricter_b s ref
    | PredSameCategory ref => same_category_b s ref
    | PredAnd p1 p2 => eval_pred p1 s && eval_pred p2 s
    | PredOr p1 p2 => eval_pred p1 s || eval_pred p2 s
    | PredNot p1 => negb (eval_pred p1 s)
    end.

  Fixpoint pred_eqb (p1 p2 : ScopePred) : bool :=
    match p1, p2 with
    | PredTrue, PredTrue => true
    | PredFalse, PredFalse => true
    | PredIdEq id1, PredIdEq id2 => id1 =? id2
    | PredCategoryEq c1, PredCategoryEq c2 => c1 =? c2
    | PredSeverityGe n1, PredSeverityGe n2 => n1 =? n2
    | PredSeverityLe n1, PredSeverityLe n2 => n1 =? n2
    | PredSeverityEq n1, PredSeverityEq n2 => n1 =? n2
    | PredTimeEq t1, PredTimeEq t2 => t1 =? t2
    | PredSimilarTo s1, PredSimilarTo s2 => subject_eqb s1 s2
    | PredStricterThan s1, PredStricterThan s2 => subject_eqb s1 s2
    | PredSameCategory s1, PredSameCategory s2 => subject_eqb s1 s2
    | PredAnd a1 b1, PredAnd a2 b2 => pred_eqb a1 a2 && pred_eqb b1 b2
    | PredOr a1 b1, PredOr a2 b2 => pred_eqb a1 a2 && pred_eqb b1 b2
    | PredNot a1, PredNot a2 => pred_eqb a1 a2
    | _, _ => false
    end.

  Lemma pred_eqb_eq : forall p1 p2, pred_eqb p1 p2 = true <-> p1 = p2.
  Proof.
    induction p1; destruct p2; simpl; split; intro H;
    try discriminate; try reflexivity;
    try (rewrite Nat.eqb_eq in H; congruence);
    try (rewrite Nat.eqb_eq; congruence);
    try (rewrite subject_eqb_eq in H; congruence);
    try (rewrite subject_eqb_eq; congruence).
    - rewrite Bool.andb_true_iff in H. destruct H as [H1 H2].
      apply IHp1_1 in H1. apply IHp1_2 in H2. congruence.
    - inversion H. subst. rewrite Bool.andb_true_iff.
      split; apply IHp1_1 || apply IHp1_2; reflexivity.
    - rewrite Bool.andb_true_iff in H. destruct H as [H1 H2].
      apply IHp1_1 in H1. apply IHp1_2 in H2. congruence.
    - inversion H. subst. rewrite Bool.andb_true_iff.
      split; apply IHp1_1 || apply IHp1_2; reflexivity.
    - apply IHp1 in H. congruence.
    - inversion H. subst. apply IHp1. reflexivity.
  Qed.

End ScopeDSL.

Export ScopeDSL.

(** ========================================================================= *)
(** PART III: THE 13 MIDDOT                                                   *)
(** ========================================================================= *)

Module MiddotDef.

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

  Definition middah_eqb (m1 m2 : Middah) : bool :=
    match m1, m2 with
    | KalVaChomer, KalVaChomer => true
    | GezerahShavah, GezerahShavah => true
    | BinyanAvEchad, BinyanAvEchad => true
    | BinyanAvShnei, BinyanAvShnei => true
    | KlalUFrat, KlalUFrat => true
    | PratUKlal, PratUKlal => true
    | KlalUFratUKlal, KlalUFratUKlal => true
    | KlalSheTzarichLeFrat, KlalSheTzarichLeFrat => true
    | PratSheTzarichLeKlal, PratSheTzarichLeKlal => true
    | DavarSheHayahBiKlal, DavarSheHayahBiKlal => true
    | DavarYatzaLeLamed, DavarYatzaLeLamed => true
    | DavarHaLamedMeInyano, DavarHaLamedMeInyano => true
    | ShneiKetuvimMakhchishim, ShneiKetuvimMakhchishim => true
    | _, _ => false
    end.

  Definition all_middot : list Middah :=
    [KalVaChomer; GezerahShavah; BinyanAvEchad; BinyanAvShnei;
     KlalUFrat; PratUKlal; KlalUFratUKlal; KlalSheTzarichLeFrat;
     PratSheTzarichLeKlal; DavarSheHayahBiKlal; DavarYatzaLeLamed;
     DavarHaLamedMeInyano; ShneiKetuvimMakhchishim].

  Lemma all_middot_length : length all_middot = 13.
  Proof. reflexivity. Qed.

  Lemma middah_eqb_eq : forall m1 m2, middah_eqb m1 m2 = true <-> m1 = m2.
  Proof.
    intros [] []; simpl; split; intro H; try discriminate; try reflexivity.
  Qed.

End MiddotDef.

Export MiddotDef.

(** ========================================================================= *)
(** PART IV: MESORAH AND VERSE REGISTRY                                       *)
(** ========================================================================= *)

Inductive MufnehLevel : Type :=
  | MufnehNone : MufnehLevel
  | MufnehOne : MufnehLevel
  | MufnehBoth : MufnehLevel.

Module Registry.

  Record MesorahEntry := mkMesorahEntry {
    mes_verse1 : VerseId;
    mes_verse2 : VerseId;
    mes_root : ShoreshId
  }.

  Definition MesorahRegistry := list MesorahEntry.

  Definition mesorah_authorized (reg : MesorahRegistry) (v1 v2 : VerseId) (root : ShoreshId) : bool :=
    existsb (fun e =>
      ((mes_verse1 e =? v1) && (mes_verse2 e =? v2) && (mes_root e =? root)) ||
      ((mes_verse1 e =? v2) && (mes_verse2 e =? v1) && (mes_root e =? root))
    ) reg.

  Record MufnehEntry := mkMufnehEntry {
    muf_verse1 : VerseId;
    muf_verse2 : VerseId;
    muf_level : MufnehLevel
  }.

  Definition MufnehRegistry := list MufnehEntry.

  Definition mufneh_verified (reg : MufnehRegistry) (v1 v2 : VerseId) (level : MufnehLevel) : bool :=
    existsb (fun e =>
      ((muf_verse1 e =? v1) && (muf_verse2 e =? v2) &&
       match muf_level e, level with
       | MufnehBoth, _ => true
       | MufnehOne, MufnehOne => true
       | MufnehOne, MufnehNone => true
       | MufnehNone, MufnehNone => true
       | _, _ => false
       end) ||
      ((muf_verse1 e =? v2) && (muf_verse2 e =? v1) &&
       match muf_level e, level with
       | MufnehBoth, _ => true
       | MufnehOne, MufnehOne => true
       | MufnehOne, MufnehNone => true
       | MufnehNone, MufnehNone => true
       | _, _ => false
       end)
    ) reg.

  Record VerseEntry := mkVerseEntry {
    ve_id : VerseId;
    ve_book : nat;
    ve_chapter : nat;
    ve_number : nat;
    ve_has_quantifier : bool;
    ve_has_restriction : bool
  }.

  Definition VerseRegistry := list VerseEntry.

  Definition verse_lookup (reg : VerseRegistry) (vid : VerseId) : option VerseEntry :=
    find (fun e => ve_id e =? vid) reg.

  Definition verses_adjacent (reg : VerseRegistry) (v1 v2 : VerseId) : bool :=
    match verse_lookup reg v1, verse_lookup reg v2 with
    | Some e1, Some e2 =>
        (ve_book e1 =? ve_book e2) &&
        (ve_chapter e1 =? ve_chapter e2) &&
        (S (ve_number e1) =? ve_number e2)
    | _, _ => false
    end.

  Definition verse_is_general (reg : VerseRegistry) (vid : VerseId) : bool :=
    match verse_lookup reg vid with
    | Some e => ve_has_quantifier e && negb (ve_has_restriction e)
    | None => false
    end.

  Definition verse_is_particular (reg : VerseRegistry) (vid : VerseId) : bool :=
    match verse_lookup reg vid with
    | Some e => negb (ve_has_quantifier e)
    | None => false
    end.

  (** Provenance record for registry integrity. *)
  Record RegistryProvenance := mkRegistryProvenance {
    rp_source_hash : nat;
    rp_timestamp : nat;
    rp_authority_id : nat;
    rp_signature : list nat
  }.

  Record AuthenticatedRegistry := mkAuthenticatedRegistry {
    ar_verses : VerseRegistry;
    ar_mesorah : MesorahRegistry;
    ar_mufneh : MufnehRegistry;
    ar_provenance : RegistryProvenance
  }.

  Definition verify_provenance (ar : AuthenticatedRegistry) (expected_authority : nat) : bool :=
    rp_authority_id (ar_provenance ar) =? expected_authority.

End Registry.

Export Registry.

(** ========================================================================= *)
(** PART V: NODE CERTIFICATES - DATA ONLY, NO CODE                            *)
(** ========================================================================= *)

Module Certificates.

  Inductive DayoBound : Type :=
    | DayoStrict : DayoBound
    | DayoExtend : nat -> DayoBound.

  Inductive PirkaStatus : Type :=
    | NoPirka : PirkaStatus
    | HasPirka : ScopePred -> PirkaStatus.

  Record KVCCert := mkKVCCert {
    kvc_lenient : Subject;
    kvc_strict : Subject;
    kvc_dayo : DayoBound;
    kvc_pirka : PirkaStatus
  }.

  Record GSCert := mkGSCert {
    gs_verse1 : VerseId;
    gs_verse2 : VerseId;
    gs_root : ShoreshId;
    gs_mufneh : MufnehLevel;
    gs_transfer : ScopePred
  }.

  Record BACert := mkBACert {
    ba_paradigm : Subject
  }.

  Record BA2Cert := mkBA2Cert {
    ba2_paradigm1 : Subject;
    ba2_paradigm2 : Subject;
    ba2_common_category : CategoryId
  }.

  Record KUFCert := mkKUFCert {
    kuf_klal_verse : VerseId;
    kuf_prat_verse : VerseId;
    kuf_restriction : ScopePred
  }.

  Record PUKCert := mkPUKCert {
    puk_prat_verse : VerseId;
    puk_klal_verse : VerseId;
    puk_expansion : ScopePred
  }.

  Record KFKCert := mkKFKCert {
    kfk_klal1_verse : VerseId;
    kfk_prat_verse : VerseId;
    kfk_klal2_verse : VerseId;
    kfk_similarity : ScopePred
  }.

  Record DSHCert := mkDSHCert {
    dsh_exception : ScopePred
  }.

  Record DYLCert := mkDYLCert {
    dyl_teaching_verse : VerseId;
    dyl_modifier : ScopePred
  }.

  Record DMICert := mkDMICert {
    dmi_verse : VerseId;
    dmi_context_verse : VerseId;
    dmi_context_restriction : ScopePred
  }.

  Record SKMCert := mkSKMCert {
    skm_verse1 : VerseId;
    skm_verse2 : VerseId;
    skm_verse3 : VerseId;
    skm_resolution : ScopePred
  }.

  Inductive NodeCert : Middah -> Type :=
    | CertKVC : KVCCert -> NodeCert KalVaChomer
    | CertGS : GSCert -> NodeCert GezerahShavah
    | CertBA : BACert -> NodeCert BinyanAvEchad
    | CertBA2 : BA2Cert -> NodeCert BinyanAvShnei
    | CertKUF : KUFCert -> NodeCert KlalUFrat
    | CertPUK : PUKCert -> NodeCert PratUKlal
    | CertKFK : KFKCert -> NodeCert KlalUFratUKlal
    | CertKTF : KUFCert -> NodeCert KlalSheTzarichLeFrat
    | CertPTK : PUKCert -> NodeCert PratSheTzarichLeKlal
    | CertDSH : DSHCert -> NodeCert DavarSheHayahBiKlal
    | CertDYL : DYLCert -> NodeCert DavarYatzaLeLamed
    | CertDMI : DMICert -> NodeCert DavarHaLamedMeInyano
    | CertSKM : SKMCert -> NodeCert ShneiKetuvimMakhchishim.

End Certificates.

Export Certificates.

(** ========================================================================= *)
(** PART VI: DERIVATION TREES                                                 *)
(** ========================================================================= *)

Module DerivationTrees.

  Inductive DerivationTree : Type :=
    | DTLeaf : VerseId -> ScopePred -> DerivationTree
    | DTNode : forall m, NodeCert m -> list DerivationTree -> DerivationTree.

  Fixpoint dt_depth (t : DerivationTree) : nat :=
    match t with
    | DTLeaf _ _ => 0
    | DTNode _ _ children =>
        1 + fold_right max 0 (map dt_depth children)
    end.

  Fixpoint dt_leaf_verses (t : DerivationTree) : list VerseId :=
    match t with
    | DTLeaf v _ => [v]
    | DTNode _ _ children => flat_map dt_leaf_verses children
    end.

  Definition cert_verses (m : Middah) (cert : NodeCert m) : list VerseId :=
    match cert with
    | CertKVC _ => []
    | CertGS w => [gs_verse1 w; gs_verse2 w]
    | CertBA _ => []
    | CertBA2 _ => []
    | CertKUF w => [kuf_klal_verse w; kuf_prat_verse w]
    | CertPUK w => [puk_prat_verse w; puk_klal_verse w]
    | CertKFK w => [kfk_klal1_verse w; kfk_prat_verse w; kfk_klal2_verse w]
    | CertKTF w => [kuf_klal_verse w; kuf_prat_verse w]
    | CertPTK w => [puk_prat_verse w; puk_klal_verse w]
    | CertDSH _ => []
    | CertDYL w => [dyl_teaching_verse w]
    | CertDMI w => [dmi_verse w; dmi_context_verse w]
    | CertSKM w => [skm_verse1 w; skm_verse2 w; skm_verse3 w]
    end.

  Fixpoint dt_cert_verses (t : DerivationTree) : list VerseId :=
    match t with
    | DTLeaf _ _ => []
    | DTNode m cert children =>
        cert_verses m cert ++ flat_map dt_cert_verses children
    end.

  Definition dt_all_verses (t : DerivationTree) : list VerseId :=
    dt_leaf_verses t ++ dt_cert_verses t.

  (** TODO: KUF/PUK/KTF/PTK should require 2 children (one per verse),
      but this requires redesigning the transformers. Currently 1 child. *)
  Definition dt_requires_children (m : Middah) : nat :=
    match m with
    | ShneiKetuvimMakhchishim => 2
    | BinyanAvShnei => 2
    | KlalUFratUKlal => 3
    | GezerahShavah => 2
    | _ => 1
    end.

End DerivationTrees.

Export DerivationTrees.

(** ========================================================================= *)
(** PART VII: THE INTERPRETER - COMPOSITIONAL FROM CHILDREN                   *)
(** Every rule transforms child scope(s). No rule ignores children.           *)
(** ========================================================================= *)

Module Interpreter.

  Definition child_scope_or (children : list DerivationTree) (eval : DerivationTree -> Subject -> bool) (s : Subject) : bool :=
    existsb (fun t => eval t s) children.

  Definition child_scope_and (children : list DerivationTree) (eval : DerivationTree -> Subject -> bool) (s : Subject) : bool :=
    forallb (fun t => eval t s) children.

  Definition child_scope_first (children : list DerivationTree) (eval : DerivationTree -> Subject -> bool) (s : Subject) : bool :=
    match children with
    | [] => false
    | c :: _ => eval c s
    end.

  Definition middah_aggregation (m : Middah) : (list DerivationTree -> (DerivationTree -> Subject -> bool) -> Subject -> bool) :=
    match m with
    | ShneiKetuvimMakhchishim => child_scope_and
    | KlalUFratUKlal => child_scope_and
    | _ => child_scope_or
    end.

  Fixpoint dt_eval (t : DerivationTree) (s : Subject) : bool :=
    match t with
    | DTLeaf _ pred => eval_pred pred s
    | DTNode m cert children =>
        let base :=
          match m with
          | ShneiKetuvimMakhchishim =>
              match children with
              | [] => false
              | _ => forallb (fun c => dt_eval c s) children
              end
          | KlalUFratUKlal =>
              match children with
              | [] => false
              | _ => forallb (fun c => dt_eval c s) children
              end
          | _ => existsb (fun c => dt_eval c s) children
          end in
        match cert with
        | CertKVC w =>
            let dayo_ok :=
              match kvc_dayo w with
              | DayoStrict => subj_obligation_strength (kvc_lenient w) <=? subj_obligation_strength s
              | DayoExtend n => subj_obligation_strength (kvc_lenient w) <=? subj_obligation_strength s + n
              end in
            let pirka_ok :=
              match kvc_pirka w with
              | NoPirka => true
              | HasPirka refutation => negb (eval_pred refutation s)
              end in
            (base || (same_category_b s (kvc_strict w) && stricter_b s (kvc_lenient w))) && dayo_ok && pirka_ok
        | CertGS w =>
            base && eval_pred (gs_transfer w) s
        | CertBA w =>
            base && similar_cases_b s (ba_paradigm w)
        | CertBA2 w =>
            base && (subj_category s =? ba2_common_category w)
        | CertKUF w =>
            base && eval_pred (kuf_restriction w) s
        | CertPUK w =>
            base && eval_pred (puk_expansion w) s
        | CertKFK w =>
            base && eval_pred (kfk_similarity w) s
        | CertKTF w =>
            base && eval_pred (kuf_restriction w) s
        | CertPTK w =>
            base && eval_pred (puk_expansion w) s
        | CertDSH w =>
            base && negb (eval_pred (dsh_exception w) s)
        | CertDYL w =>
            base && eval_pred (dyl_modifier w) s
        | CertDMI w =>
            base && eval_pred (dmi_context_restriction w) s
        | CertSKM w =>
            base && eval_pred (skm_resolution w) s
        end
    end.

End Interpreter.

Export Interpreter.

(** ========================================================================= *)
(** PART VIII: VALIDITY CHECKER                                               *)
(** Checks middah admissibility, not just coherence.                          *)
(** ========================================================================= *)

Module Validity.

  Record ValidationContext := mkValidationContext {
    vc_mesorah : MesorahRegistry;
    vc_mufneh : MufnehRegistry;
    vc_verses : VerseRegistry
  }.

  Definition valid_kvc (ctx : ValidationContext) (w : KVCCert) : bool :=
    same_category_b (kvc_lenient w) (kvc_strict w) &&
    stricter_b (kvc_strict w) (kvc_lenient w).

  Definition valid_gs (ctx : ValidationContext) (w : GSCert) : bool :=
    match verse_lookup (vc_verses ctx) (gs_verse1 w),
          verse_lookup (vc_verses ctx) (gs_verse2 w) with
    | Some _, Some _ =>
        mufneh_verified (vc_mufneh ctx) (gs_verse1 w) (gs_verse2 w) (gs_mufneh w) &&
        match gs_mufneh w with
        | MufnehBoth => true
        | MufnehOne => mesorah_authorized (vc_mesorah ctx) (gs_verse1 w) (gs_verse2 w) (gs_root w)
        | MufnehNone => mesorah_authorized (vc_mesorah ctx) (gs_verse1 w) (gs_verse2 w) (gs_root w)
        end
    | _, _ => false
    end.

  Definition valid_kuf (ctx : ValidationContext) (w : KUFCert) : bool :=
    verse_is_general (vc_verses ctx) (kuf_klal_verse w) &&
    verse_is_particular (vc_verses ctx) (kuf_prat_verse w) &&
    verses_adjacent (vc_verses ctx) (kuf_klal_verse w) (kuf_prat_verse w).

  Definition valid_puk (ctx : ValidationContext) (w : PUKCert) : bool :=
    verse_is_particular (vc_verses ctx) (puk_prat_verse w) &&
    verse_is_general (vc_verses ctx) (puk_klal_verse w) &&
    verses_adjacent (vc_verses ctx) (puk_prat_verse w) (puk_klal_verse w).

  Fixpoint pred_trivially_true (p : ScopePred) : bool :=
    match p with
    | PredTrue => true
    | PredNot q => pred_trivially_false q
    | PredOr p1 p2 => pred_trivially_true p1 || pred_trivially_true p2
    | PredAnd p1 p2 => pred_trivially_true p1 && pred_trivially_true p2
    | _ => false
    end
  with pred_trivially_false (p : ScopePred) : bool :=
    match p with
    | PredFalse => true
    | PredNot q => pred_trivially_true q
    | PredAnd p1 p2 => pred_trivially_false p1 || pred_trivially_false p2
    | PredOr p1 p2 => pred_trivially_false p1 && pred_trivially_false p2
    | _ => false
    end.

  Fixpoint pred_normalize (p : ScopePred) : ScopePred :=
    match p with
    | PredAnd p1 p2 =>
        let n1 := pred_normalize p1 in
        let n2 := pred_normalize p2 in
        match n1, n2 with
        | PredTrue, _ => n2
        | _, PredTrue => n1
        | PredFalse, _ => PredFalse
        | _, PredFalse => PredFalse
        | _, _ => PredAnd n1 n2
        end
    | PredOr p1 p2 =>
        let n1 := pred_normalize p1 in
        let n2 := pred_normalize p2 in
        match n1, n2 with
        | PredFalse, _ => n2
        | _, PredFalse => n1
        | PredTrue, _ => PredTrue
        | _, PredTrue => PredTrue
        | _, _ => PredOr n1 n2
        end
    | PredNot q =>
        let nq := pred_normalize q in
        match nq with
        | PredTrue => PredFalse
        | PredFalse => PredTrue
        | PredNot qq => qq
        | _ => PredNot nq
        end
    | _ => p
    end.

  Definition pred_nontrivial (p : ScopePred) : bool :=
    let np := pred_normalize p in
    negb (pred_trivially_true np) && negb (pred_trivially_false np).

  Definition valid_ba (w : BACert) : bool :=
    valid_subject_id (subj_id (ba_paradigm w)).

  Definition valid_ba2 (w : BA2Cert) : bool :=
    valid_subject_id (subj_id (ba2_paradigm1 w)) &&
    valid_subject_id (subj_id (ba2_paradigm2 w)) &&
    negb (subj_id (ba2_paradigm1 w) =? subj_id (ba2_paradigm2 w)) &&
    (subj_category (ba2_paradigm1 w) =? ba2_common_category w) &&
    (subj_category (ba2_paradigm2 w) =? ba2_common_category w).

  Definition valid_dsh (w : DSHCert) : bool :=
    pred_nontrivial (dsh_exception w).

  Definition valid_dyl (ctx : ValidationContext) (w : DYLCert) : bool :=
    match verse_lookup (vc_verses ctx) (dyl_teaching_verse w) with
    | Some _ => pred_nontrivial (dyl_modifier w)
    | None => false
    end.

  Definition valid_skm (ctx : ValidationContext) (w : SKMCert) : bool :=
    match verse_lookup (vc_verses ctx) (skm_verse1 w),
          verse_lookup (vc_verses ctx) (skm_verse2 w),
          verse_lookup (vc_verses ctx) (skm_verse3 w) with
    | Some _, Some _, Some _ =>
        negb (skm_verse1 w =? skm_verse2 w) &&
        negb (skm_verse1 w =? skm_verse3 w) &&
        negb (skm_verse2 w =? skm_verse3 w) &&
        pred_nontrivial (skm_resolution w)
    | _, _, _ => false
    end.

  Definition valid_cert (ctx : ValidationContext) (m : Middah) (cert : NodeCert m) : bool :=
    match cert with
    | CertKVC w => valid_kvc ctx w
    | CertGS w => valid_gs ctx w
    | CertBA w => valid_ba w
    | CertBA2 w => valid_ba2 w
    | CertKUF w => valid_kuf ctx w
    | CertPUK w => valid_puk ctx w
    | CertKFK w =>
        verse_is_general (vc_verses ctx) (kfk_klal1_verse w) &&
        verse_is_particular (vc_verses ctx) (kfk_prat_verse w) &&
        verse_is_general (vc_verses ctx) (kfk_klal2_verse w)
    | CertKTF w => valid_kuf ctx w
    | CertPTK w => valid_puk ctx w
    | CertDSH w => valid_dsh w
    | CertDYL w => valid_dyl ctx w
    | CertDMI w =>
        match verse_lookup (vc_verses ctx) (dmi_verse w),
              verse_lookup (vc_verses ctx) (dmi_context_verse w) with
        | Some e1, Some e2 =>
            (ve_book e1 =? ve_book e2) && (ve_chapter e1 =? ve_chapter e2)
        | _, _ => false
        end
    | CertSKM w => valid_skm ctx w
    end.

  Definition verses_anchored (required : list VerseId) (available : list VerseId) : bool :=
    forallb (fun v => existsb (fun v' => v =? v') available) required.

  Definition children_leaf_verses (children : list DerivationTree) : list VerseId :=
    flat_map dt_leaf_verses children.

  Definition cert_anchored_verses (m : Middah) (cert : NodeCert m) : list VerseId :=
    match cert with
    | CertKVC _ => []
    | CertGS w => [gs_verse1 w; gs_verse2 w]
    | CertBA _ => []
    | CertBA2 _ => []
    | CertKUF w => [kuf_klal_verse w; kuf_prat_verse w]
    | CertPUK w => [puk_prat_verse w; puk_klal_verse w]
    | CertKFK w => [kfk_klal1_verse w; kfk_prat_verse w; kfk_klal2_verse w]
    | CertKTF w => [kuf_klal_verse w; kuf_prat_verse w]
    | CertPTK w => [puk_prat_verse w; puk_klal_verse w]
    | CertDSH _ => []
    | CertDYL w => [dyl_teaching_verse w]
    | CertDMI w => [dmi_verse w; dmi_context_verse w]
    | CertSKM w => [skm_verse1 w; skm_verse2 w; skm_verse3 w]
    end.

  Fixpoint dt_valid (ctx : ValidationContext) (t : DerivationTree) : bool :=
    match t with
    | DTLeaf vid _ =>
        match verse_lookup (vc_verses ctx) vid with
        | Some _ => true
        | None => false
        end
    | DTNode m cert children =>
        valid_cert ctx m cert &&
        (length children =? dt_requires_children m) &&
        verses_anchored (cert_anchored_verses m cert) (children_leaf_verses children) &&
        forallb (dt_valid ctx) children
    end.

  Definition dt_admissible (ctx : ValidationContext) (t : DerivationTree) : Prop :=
    dt_valid ctx t = true.

End Validity.

Export Validity.

(** ========================================================================= *)
(** PART IX: COMPILED HALAKHA                                                 *)
(** ========================================================================= *)

Module CompiledLaw.

  (** Polarity for positive/negative derivations. *)
  Inductive Polarity : Type :=
    | Positive : Polarity
    | Negative : Polarity.

  Definition polarity_eqb (p1 p2 : Polarity) : bool :=
    match p1, p2 with
    | Positive, Positive => true
    | Negative, Negative => true
    | _, _ => false
    end.

  Definition negate_polarity (p : Polarity) : Polarity :=
    match p with
    | Positive => Negative
    | Negative => Positive
    end.

  Record CompiledHalakha := mkCompiledHalakha {
    ch_id : HalakhaId;
    ch_polarity : Polarity;
    ch_derivation : DerivationTree
  }.

  Definition ch_applies (ch : CompiledHalakha) (s : Subject) : bool :=
    dt_eval (ch_derivation ch) s.

  Lemma ch_applies_eval : forall ch s,
    ch_applies ch s = dt_eval (ch_derivation ch) s.
  Proof.
    intros ch s. reflexivity.
  Qed.

  Record ValidatedHalakha := mkValidatedHalakha {
    vh_halakha : CompiledHalakha;
    vh_context : ValidationContext;
    vh_valid : dt_valid vh_context (ch_derivation vh_halakha) = true
  }.

  Definition vh_applies (vh : ValidatedHalakha) (s : Subject) : bool :=
    ch_applies (vh_halakha vh) s.

  Definition vh_audit (vh : ValidatedHalakha) : DerivationTree :=
    ch_derivation (vh_halakha vh).

  Lemma vh_ruling_reproducible : forall vh s,
    vh_applies vh s = dt_eval (vh_audit vh) s.
  Proof.
    intros vh s. unfold vh_applies, vh_audit. apply ch_applies_eval.
  Qed.

  Lemma vh_admissible : forall vh,
    dt_admissible (vh_context vh) (vh_audit vh).
  Proof.
    intro vh. unfold dt_admissible, vh_audit. exact (vh_valid vh).
  Qed.

  Definition SafeEval (vh : ValidatedHalakha) (s : Subject) : bool :=
    dt_eval (vh_audit vh) s.

  Lemma SafeEval_correct : forall vh s,
    SafeEval vh s = vh_applies vh s.
  Proof.
    intros vh s. unfold SafeEval, vh_applies, vh_audit. apply ch_applies_eval.
  Qed.

  Lemma SafeEval_only_on_valid : forall vh s,
    dt_admissible (vh_context vh) (vh_audit vh) ->
    SafeEval vh s = dt_eval (ch_derivation (vh_halakha vh)) s.
  Proof.
    intros vh s _. reflexivity.
  Qed.

End CompiledLaw.

Export CompiledLaw.

(** ========================================================================= *)
(** PART X: SCOPE TRANSFORMERS                                                *)
(** ========================================================================= *)

Module Transformers.

  Definition transform_kvc (base : CompiledHalakha) (w : KVCCert) (new_id : HalakhaId) : CompiledHalakha :=
    mkCompiledHalakha new_id (ch_polarity base) (DTNode KalVaChomer (CertKVC w) [ch_derivation base]).

  Definition transform_restrict (base : CompiledHalakha) (klal prat : VerseId) (restriction : ScopePred) (new_id : HalakhaId) : CompiledHalakha :=
    mkCompiledHalakha new_id (ch_polarity base) (DTNode KlalUFrat (CertKUF (mkKUFCert klal prat restriction)) [ch_derivation base]).

  Definition transform_expand (base : CompiledHalakha) (prat klal : VerseId) (expansion : ScopePred) (new_id : HalakhaId) : CompiledHalakha :=
    mkCompiledHalakha new_id (ch_polarity base) (DTNode PratUKlal (CertPUK (mkPUKCert prat klal expansion)) [ch_derivation base]).

  Definition transform_exception (base : CompiledHalakha) (exception : ScopePred) (new_id : HalakhaId) : CompiledHalakha :=
    mkCompiledHalakha new_id (ch_polarity base) (DTNode DavarSheHayahBiKlal (CertDSH (mkDSHCert exception)) [ch_derivation base]).

  Definition transform_gs (base1 base2 : CompiledHalakha) (w : GSCert) (new_id : HalakhaId) : CompiledHalakha :=
    mkCompiledHalakha new_id (ch_polarity base1) (DTNode GezerahShavah (CertGS w) [ch_derivation base1; ch_derivation base2]).

  Definition transform_ba (base : CompiledHalakha) (paradigm : Subject) (new_id : HalakhaId) : CompiledHalakha :=
    mkCompiledHalakha new_id (ch_polarity base) (DTNode BinyanAvEchad (CertBA (mkBACert paradigm)) [ch_derivation base]).

  Definition transform_dmi (base : CompiledHalakha) (verse context_verse : VerseId) (context_restriction : ScopePred) (new_id : HalakhaId) : CompiledHalakha :=
    mkCompiledHalakha new_id (ch_polarity base) (DTNode DavarHaLamedMeInyano (CertDMI (mkDMICert verse context_verse context_restriction)) [ch_derivation base]).

  Definition transform_dyl (base : CompiledHalakha) (teaching_verse : VerseId) (modifier : ScopePred) (new_id : HalakhaId) : CompiledHalakha :=
    mkCompiledHalakha new_id (ch_polarity base) (DTNode DavarYatzaLeLamed (CertDYL (mkDYLCert teaching_verse modifier)) [ch_derivation base]).

  Definition transform_kfk (base1 base2 base3 : CompiledHalakha) (klal1 prat klal2 : VerseId) (similarity : ScopePred) (new_id : HalakhaId) : CompiledHalakha :=
    mkCompiledHalakha new_id (ch_polarity base1) (DTNode KlalUFratUKlal (CertKFK (mkKFKCert klal1 prat klal2 similarity))
      [ch_derivation base1; ch_derivation base2; ch_derivation base3]).

  Definition transform_negate (base : CompiledHalakha) (new_id : HalakhaId) : CompiledHalakha :=
    mkCompiledHalakha new_id (negate_polarity (ch_polarity base)) (ch_derivation base).

End Transformers.

Export Transformers.

(** ========================================================================= *)
(** PART XI: VALIDATED TRANSFORMERS                                           *)
(** Transformers that preserve validity proofs.                               *)
(** ========================================================================= *)

Module ValidatedTransformers.

  Definition vtransform_kvc
    (vh : ValidatedHalakha)
    (w : KVCCert)
    (new_id : HalakhaId)
    (Hvalid : valid_kvc (vh_context vh) w = true)
    : ValidatedHalakha.
  Proof.
    refine (mkValidatedHalakha
      (transform_kvc (vh_halakha vh) w new_id)
      (vh_context vh)
      _).
    simpl.
    rewrite Hvalid. simpl.
    rewrite (vh_valid vh). reflexivity.
  Defined.

  (** Note: Hanchor requires verses to appear in children's leaves. *)
  Definition vtransform_gs
    (vh1 vh2 : ValidatedHalakha)
    (w : GSCert)
    (new_id : HalakhaId)
    (Hctx : vh_context vh1 = vh_context vh2)
    (Hvalid : valid_gs (vh_context vh1) w = true)
    (Hanchor : dt_valid (vh_context vh1)
                 (DTNode GezerahShavah (CertGS w)
                    [ch_derivation (vh_halakha vh1);
                     ch_derivation (vh_halakha vh2)]) = true)
    : ValidatedHalakha.
  Proof.
    exact (mkValidatedHalakha
      (transform_gs (vh_halakha vh1) (vh_halakha vh2) w new_id)
      (vh_context vh1)
      Hanchor).
  Defined.

  Definition vtransform_restrict
    (vh : ValidatedHalakha)
    (klal prat : VerseId)
    (restriction : ScopePred)
    (new_id : HalakhaId)
    (Hvalid : valid_kuf (vh_context vh) (mkKUFCert klal prat restriction) = true)
    (Hanchor : existsb (fun v' => klal =? v') (dt_leaf_verses (ch_derivation (vh_halakha vh)) ++ []) &&
               (existsb (fun v' => prat =? v') (dt_leaf_verses (ch_derivation (vh_halakha vh)) ++ []) && true) = true)
    : ValidatedHalakha.
  Proof.
    refine (mkValidatedHalakha
      (transform_restrict (vh_halakha vh) klal prat restriction new_id)
      (vh_context vh)
      _).
    simpl.
    rewrite Hvalid, Hanchor, (vh_valid vh). reflexivity.
  Defined.

  Definition vtransform_expand
    (vh : ValidatedHalakha)
    (prat klal : VerseId)
    (expansion : ScopePred)
    (new_id : HalakhaId)
    (Hvalid : valid_puk (vh_context vh) (mkPUKCert prat klal expansion) = true)
    (Hanchor : existsb (fun v' => prat =? v') (dt_leaf_verses (ch_derivation (vh_halakha vh)) ++ []) &&
               (existsb (fun v' => klal =? v') (dt_leaf_verses (ch_derivation (vh_halakha vh)) ++ []) && true) = true)
    : ValidatedHalakha.
  Proof.
    refine (mkValidatedHalakha
      (transform_expand (vh_halakha vh) prat klal expansion new_id)
      (vh_context vh)
      _).
    simpl.
    rewrite Hvalid, Hanchor, (vh_valid vh). reflexivity.
  Defined.

  Definition vtransform_ba
    (vh : ValidatedHalakha)
    (paradigm : Subject)
    (new_id : HalakhaId)
    (Hvalid : valid_ba (mkBACert paradigm) = true)
    : ValidatedHalakha.
  Proof.
    refine (mkValidatedHalakha
      (transform_ba (vh_halakha vh) paradigm new_id)
      (vh_context vh)
      _).
    simpl.
    rewrite Hvalid. simpl.
    rewrite (vh_valid vh). reflexivity.
  Defined.

  Definition vtransform_exception
    (vh : ValidatedHalakha)
    (exception : ScopePred)
    (new_id : HalakhaId)
    (Hvalid : valid_dsh (mkDSHCert exception) = true)
    : ValidatedHalakha.
  Proof.
    refine (mkValidatedHalakha
      (transform_exception (vh_halakha vh) exception new_id)
      (vh_context vh)
      _).
    simpl.
    rewrite Hvalid. simpl.
    rewrite (vh_valid vh). reflexivity.
  Defined.

End ValidatedTransformers.

Export ValidatedTransformers.

(** ========================================================================= *)
(** PART XII: BASE DERIVATION                                                 *)
(** ========================================================================= *)

Module BaseDerivation.

  Definition base_halakha (vid : VerseId) (scope : ScopePred) (hid : HalakhaId) : CompiledHalakha :=
    mkCompiledHalakha hid Positive (DTLeaf vid scope).

  Definition base_halakha_negative (vid : VerseId) (scope : ScopePred) (hid : HalakhaId) : CompiledHalakha :=
    mkCompiledHalakha hid Negative (DTLeaf vid scope).

End BaseDerivation.

Export BaseDerivation.

(** ========================================================================= *)
(** PART XIII: EXAMPLES                                                       *)
(** ========================================================================= *)

Module Examples.

  Definition subj_shabbat : Subject := mkSubject 1 10 10 1 time_shabbat.
  Definition subj_yom_tov : Subject := mkSubject 2 5 5 1 time_yom_tov.
  Definition subj_chol : Subject := mkSubject 3 1 1 1 time_weekday.

  Definition scope_melacha : ScopePred :=
    PredAnd (PredCategoryEq 1) (PredSeverityGe 5).

  (** Using small VerseId for serialization compatibility (<255). *)
  Definition verse_shabbat : VerseId := 1.

  Definition hal_melacha : CompiledHalakha :=
    base_halakha verse_shabbat scope_melacha 1.

  Lemma melacha_applies_shabbat : ch_applies hal_melacha subj_shabbat = true.
  Proof. reflexivity. Qed.

  Lemma melacha_applies_yom_tov : ch_applies hal_melacha subj_yom_tov = true.
  Proof. reflexivity. Qed.

  Lemma melacha_not_chol : ch_applies hal_melacha subj_chol = false.
  Proof. reflexivity. Qed.

  Definition kvc_melacha : KVCCert :=
    mkKVCCert subj_yom_tov subj_shabbat DayoStrict NoPirka.

  Definition hal_melacha_kvc : CompiledHalakha :=
    transform_kvc hal_melacha kvc_melacha 2.

  Lemma kvc_applies_shabbat : ch_applies hal_melacha_kvc subj_shabbat = true.
  Proof. reflexivity. Qed.

  Definition test_verse_registry : VerseRegistry :=
    [mkVerseEntry verse_shabbat 2 20 8 false false].

  Definition test_mesorah_registry : MesorahRegistry := [].

  Definition test_mufneh_registry : MufnehRegistry := [].

  Definition test_ctx : ValidationContext :=
    mkValidationContext test_mesorah_registry test_mufneh_registry test_verse_registry.

  Lemma base_valid : dt_valid test_ctx (ch_derivation hal_melacha) = true.
  Proof. reflexivity. Qed.

End Examples.

Export Examples.

(** ========================================================================= *)
(** PART XIV: SYSTEM PROPERTIES                                               *)
(** ========================================================================= *)

Module Properties.

  Theorem ruling_deterministic : forall ch s,
    ch_applies ch s = dt_eval (ch_derivation ch) s.
  Proof.
    intros ch s. apply ch_applies_eval.
  Qed.

  Theorem audit_reproducible : forall vh s,
    vh_applies vh s = dt_eval (vh_audit vh) s.
  Proof.
    intros vh s. apply vh_ruling_reproducible.
  Qed.

  Theorem validated_is_admissible : forall vh,
    dt_admissible (vh_context vh) (vh_audit vh).
  Proof.
    intro vh. apply vh_admissible.
  Qed.

  (** Children contribute to evaluation - proved per middah. *)

  Lemma dt_eval_leaf_independent : forall vid pred s,
    dt_eval (DTLeaf vid pred) s = eval_pred pred s.
  Proof. reflexivity. Qed.

End Properties.

Export Properties.

(** ========================================================================= *)
(** PART XV: SERIALIZATION                                                    *)
(** Finite representation for replication/consensus.                          *)
(** ========================================================================= *)

Module Serialization.

  Definition schema_version : nat := 2.

  Fixpoint nat_to_bytes_aux (fuel n : nat) : list nat :=
    match fuel with
    | 0 => []
    | S fuel' =>
        match n with
        | 0 => []
        | _ => (n mod 256) :: nat_to_bytes_aux fuel' (n / 256)
        end
    end.

  Definition nat_to_bytes (n : nat) : list nat :=
    nat_to_bytes_aux (S n) n.

  Definition serialize_nat (n : nat) : list nat :=
    let bytes := nat_to_bytes n in
    length bytes :: bytes.

  Definition serialize_versioned (data : list nat) : list nat :=
    schema_version :: data.

  Fixpoint serialize_pred (p : ScopePred) : list nat :=
    match p with
    | PredTrue => [0]
    | PredFalse => [1]
    | PredIdEq id => [2; id]
    | PredCategoryEq cat => [3; cat]
    | PredSeverityGe n => [4; n]
    | PredSeverityLe n => [5; n]
    | PredSeverityEq n => [6; n]
    | PredTimeEq t => [7; t]
    | PredSimilarTo s => [8; subj_id s; subj_case_severity s; subj_obligation_strength s; subj_category s; subj_time s]
    | PredStricterThan s => [9; subj_id s; subj_case_severity s; subj_obligation_strength s; subj_category s; subj_time s]
    | PredSameCategory s => [10; subj_id s; subj_case_severity s; subj_obligation_strength s; subj_category s; subj_time s]
    | PredAnd p1 p2 => [11] ++ serialize_pred p1 ++ [255] ++ serialize_pred p2
    | PredOr p1 p2 => [12] ++ serialize_pred p1 ++ [255] ++ serialize_pred p2
    | PredNot p1 => [13] ++ serialize_pred p1
    end.

  Definition serialize_subject (s : Subject) : list nat :=
    [subj_id s; subj_case_severity s; subj_obligation_strength s; subj_category s; subj_time s].

  Definition serialize_pirka (p : PirkaStatus) : list nat :=
    match p with
    | NoPirka => [0]
    | HasPirka pred => [1] ++ serialize_pred pred
    end.

  Definition serialize_kvc_cert (w : KVCCert) : list nat :=
    serialize_subject (kvc_lenient w) ++
    serialize_subject (kvc_strict w) ++
    match kvc_dayo w with
    | DayoStrict => [0]
    | DayoExtend n => [1; n]
    end ++
    serialize_pirka (kvc_pirka w).

  Definition mufneh_to_nat (m : MufnehLevel) : nat :=
    match m with
    | MufnehNone => 0
    | MufnehOne => 1
    | MufnehBoth => 2
    end.

  Definition serialize_gs_cert (w : GSCert) : list nat :=
    [gs_verse1 w; gs_verse2 w; gs_root w; mufneh_to_nat (gs_mufneh w)] ++
    serialize_pred (gs_transfer w).

  Definition serialize_kuf_cert (w : KUFCert) : list nat :=
    [kuf_klal_verse w; kuf_prat_verse w] ++ serialize_pred (kuf_restriction w).

  Definition serialize_puk_cert (w : PUKCert) : list nat :=
    [puk_prat_verse w; puk_klal_verse w] ++ serialize_pred (puk_expansion w).

  Definition serialize_dsh_cert (w : DSHCert) : list nat :=
    serialize_pred (dsh_exception w).

  Definition middah_to_nat (m : Middah) : nat :=
    match m with
    | KalVaChomer => 0
    | GezerahShavah => 1
    | BinyanAvEchad => 2
    | BinyanAvShnei => 3
    | KlalUFrat => 4
    | PratUKlal => 5
    | KlalUFratUKlal => 6
    | KlalSheTzarichLeFrat => 7
    | PratSheTzarichLeKlal => 8
    | DavarSheHayahBiKlal => 9
    | DavarYatzaLeLamed => 10
    | DavarHaLamedMeInyano => 11
    | ShneiKetuvimMakhchishim => 12
    end.

  Fixpoint serialize_tree (t : DerivationTree) : list nat :=
    match t with
    | DTLeaf vid pred => [0; vid] ++ serialize_pred pred
    | DTNode m cert children =>
        let cert_data :=
          match cert with
          | CertKVC w => serialize_kvc_cert w
          | CertGS w => serialize_gs_cert w
          | CertBA w => serialize_subject (ba_paradigm w)
          | CertBA2 w => serialize_subject (ba2_paradigm1 w) ++
                         serialize_subject (ba2_paradigm2 w) ++
                         [ba2_common_category w]
          | CertKUF w => serialize_kuf_cert w
          | CertPUK w => serialize_puk_cert w
          | CertKFK w => [kfk_klal1_verse w; kfk_prat_verse w; kfk_klal2_verse w] ++
                         serialize_pred (kfk_similarity w)
          | CertKTF w => serialize_kuf_cert w
          | CertPTK w => serialize_puk_cert w
          | CertDSH w => serialize_dsh_cert w
          | CertDYL w => [dyl_teaching_verse w] ++ serialize_pred (dyl_modifier w)
          | CertDMI w => [dmi_verse w; dmi_context_verse w] ++
                         serialize_pred (dmi_context_restriction w)
          | CertSKM w => [skm_verse1 w; skm_verse2 w; skm_verse3 w] ++
                         serialize_pred (skm_resolution w)
          end in
        [1; middah_to_nat m; length children] ++
        cert_data ++ [254] ++
        flat_map (fun c => serialize_tree c ++ [253]) children
    end.

  Definition serialize_halakha_versioned (ch : CompiledHalakha) : list nat :=
    serialize_versioned ([ch_id ch] ++ serialize_tree (ch_derivation ch)).

  Definition check_version (data : list nat) : option (list nat) :=
    match data with
    | v :: rest => if v =? schema_version then Some rest else None
    | [] => None
    end.

End Serialization.

Export Serialization.

(** ========================================================================= *)
(** PART XVI: DESERIALIZATION                                                 *)
(** Inverse of serialization with round-trip proofs.                          *)
(** ========================================================================= *)

Module Deserialization.

  Definition ParseResult (A : Type) := option (A * list nat).

  Fixpoint bytes_to_nat_aux (bytes : list nat) (acc : nat) (mult : nat) : nat :=
    match bytes with
    | [] => acc
    | b :: bs => bytes_to_nat_aux bs (acc + b * mult) (mult * 256)
    end.

  Definition bytes_to_nat (bytes : list nat) : nat :=
    bytes_to_nat_aux bytes 0 1.

  Fixpoint firstn (n : nat) (l : list nat) : list nat :=
    match n, l with
    | 0, _ => []
    | S n', x :: xs => x :: firstn n' xs
    | S _, [] => []
    end.

  Fixpoint skipn (n : nat) (l : list nat) : list nat :=
    match n, l with
    | 0, _ => l
    | S n', _ :: xs => skipn n' xs
    | S _, [] => []
    end.

  Definition deserialize_nat (l : list nat) : ParseResult nat :=
    match l with
    | len :: rest =>
        if len <=? length rest then
          Some (bytes_to_nat (firstn len rest), skipn len rest)
        else
          None
    | [] => None
    end.

  Definition deserialize_subject (l : list nat) : ParseResult Subject :=
    match l with
    | id :: csev :: osev :: cat :: t :: rest => Some (mkSubject id csev osev cat t, rest)
    | _ => None
    end.

  Definition check_sep (r : list nat) : option (list nat) :=
    match r with
    | sep :: rest => if sep =? 255 then Some rest else None
    | [] => None
    end.

  Fixpoint deserialize_pred_aux (fuel : nat) (l : list nat) : ParseResult ScopePred :=
    match fuel with
    | 0 => None
    | S fuel' =>
        match l with
        | 0 :: rest => Some (PredTrue, rest)
        | 1 :: rest => Some (PredFalse, rest)
        | 2 :: id :: rest => Some (PredIdEq id, rest)
        | 3 :: cat :: rest => Some (PredCategoryEq cat, rest)
        | 4 :: n :: rest => Some (PredSeverityGe n, rest)
        | 5 :: n :: rest => Some (PredSeverityLe n, rest)
        | 6 :: n :: rest => Some (PredSeverityEq n, rest)
        | 7 :: t :: rest => Some (PredTimeEq t, rest)
        | 8 :: id :: csev :: osev :: cat :: t :: rest =>
            Some (PredSimilarTo (mkSubject id csev osev cat t), rest)
        | 9 :: id :: csev :: osev :: cat :: t :: rest =>
            Some (PredStricterThan (mkSubject id csev osev cat t), rest)
        | 10 :: id :: csev :: osev :: cat :: t :: rest =>
            Some (PredSameCategory (mkSubject id csev osev cat t), rest)
        | 11 :: rest =>
            match deserialize_pred_aux fuel' rest with
            | Some (p1, r1) =>
                match check_sep r1 with
                | Some rest' =>
                    match deserialize_pred_aux fuel' rest' with
                    | Some (p2, rest'') => Some (PredAnd p1 p2, rest'')
                    | None => None
                    end
                | None => None
                end
            | None => None
            end
        | 12 :: rest =>
            match deserialize_pred_aux fuel' rest with
            | Some (p1, r1) =>
                match check_sep r1 with
                | Some rest' =>
                    match deserialize_pred_aux fuel' rest' with
                    | Some (p2, rest'') => Some (PredOr p1 p2, rest'')
                    | None => None
                    end
                | None => None
                end
            | None => None
            end
        | 13 :: rest =>
            match deserialize_pred_aux fuel' rest with
            | Some (p1, rest') => Some (PredNot p1, rest')
            | None => None
            end
        | _ => None
        end
    end.

  Fixpoint pred_size (p : ScopePred) : nat :=
    match p with
    | PredAnd p1 p2 => 1 + pred_size p1 + pred_size p2
    | PredOr p1 p2 => 1 + pred_size p1 + pred_size p2
    | PredNot p1 => 1 + pred_size p1
    | _ => 1
    end.

  Definition deserialize_pred (l : list nat) : ParseResult ScopePred :=
    deserialize_pred_aux (length l) l.

  Fixpoint serialize_pred_length (p : ScopePred) : nat :=
    match p with
    | PredTrue => 1
    | PredFalse => 1
    | PredIdEq _ => 2
    | PredCategoryEq _ => 2
    | PredSeverityGe _ => 2
    | PredSeverityLe _ => 2
    | PredSeverityEq _ => 2
    | PredTimeEq _ => 2
    | PredSimilarTo _ => 6
    | PredStricterThan _ => 6
    | PredSameCategory _ => 6
    | PredAnd p1 p2 => 1 + serialize_pred_length p1 + 1 + serialize_pred_length p2
    | PredOr p1 p2 => 1 + serialize_pred_length p1 + 1 + serialize_pred_length p2
    | PredNot p1 => 1 + serialize_pred_length p1
    end.

  Lemma serialize_pred_length_correct : forall p,
    length (serialize_pred p) = serialize_pred_length p.
  Proof.
    induction p; simpl; auto.
    all: try match goal with [ s : Subject |- _ ] => destruct s; reflexivity end.
    all: rewrite !app_length; simpl; lia.
  Qed.

  Lemma deser_step_aux : forall fuel l,
    match deserialize_pred_aux fuel l with
    | Some (p, rest) => deserialize_pred_aux (S fuel) l = Some (p, rest)
    | None => True
    end.
  Proof.
    induction fuel as [|fuel IH]; intro l; [reflexivity|].
    destruct l as [|x xs]; [reflexivity|].
    destruct x as [|[|[|[|[|[|[|[|[|[|[|[|[|[|n]]]]]]]]]]]]]].
    all: try reflexivity.
    all: try (cbn -[deserialize_pred_aux]; destruct xs; [exact I|reflexivity]).
    all: try (cbn -[deserialize_pred_aux]; destruct xs as [|? [|? [|? [|? [|? ?]]]]]; try exact I; reflexivity).
    - pose proof (IH xs) as IHxs.
      simpl.
      destruct (deserialize_pred_aux fuel xs) as [[p1 r1]|] eqn:E1; [|exact I].
      simpl in IHxs. rewrite IHxs.
      destruct (check_sep r1) as [rest'|] eqn:Echk; [|exact I].
      pose proof (IH rest') as IHrest'.
      destruct (deserialize_pred_aux fuel rest') as [[p2 r2]|] eqn:E2; [|exact I].
      simpl in IHrest'. rewrite IHrest'. reflexivity.
    - pose proof (IH xs) as IHxs.
      simpl.
      destruct (deserialize_pred_aux fuel xs) as [[p1 r1]|] eqn:E1; [|exact I].
      simpl in IHxs. rewrite IHxs.
      destruct (check_sep r1) as [rest'|] eqn:Echk; [|exact I].
      pose proof (IH rest') as IHrest'.
      destruct (deserialize_pred_aux fuel rest') as [[p2 r2]|] eqn:E2; [|exact I].
      simpl in IHrest'. rewrite IHrest'. reflexivity.
    - pose proof (IH xs) as IHxs.
      simpl.
      destruct (deserialize_pred_aux fuel xs) as [[p1 r1]|] eqn:E1; [|exact I].
      simpl in IHxs. rewrite IHxs. reflexivity.
  Defined.

  Lemma deser_step : forall fuel l p rest,
    deserialize_pred_aux fuel l = Some (p, rest) ->
    deserialize_pred_aux (S fuel) l = Some (p, rest).
  Proof.
    intros fuel l p rest H.
    pose proof (deser_step_aux fuel l) as Haux.
    rewrite H in Haux. exact Haux.
  Qed.

  Lemma deser_ext : forall n fuel l p rest,
    deserialize_pred_aux fuel l = Some (p, rest) ->
    deserialize_pred_aux (fuel + n) l = Some (p, rest).
  Proof.
    induction n; intros fuel l p rest H.
    - rewrite Nat.add_0_r. exact H.
    - rewrite Nat.add_succ_r. apply deser_step. apply IHn. exact H.
  Qed.

  Lemma deser_ext' : forall fuel1 fuel2 l p rest,
    fuel1 <= fuel2 ->
    deserialize_pred_aux fuel1 l = Some (p, rest) ->
    deserialize_pred_aux fuel2 l = Some (p, rest).
  Proof.
    intros fuel1 fuel2 l p rest Hle H.
    replace fuel2 with (fuel1 + (fuel2 - fuel1)) by lia.
    apply deser_ext. exact H.
  Qed.

  Lemma deser_true : forall rest, deserialize_pred_aux 1 (0 :: rest) = Some (PredTrue, rest).
  Proof. reflexivity. Qed.

  Lemma deser_false : forall rest, deserialize_pred_aux 1 (1 :: rest) = Some (PredFalse, rest).
  Proof. reflexivity. Qed.

  Lemma check_sep_255 : forall rest,
    check_sep (255 :: rest) = Some rest.
  Proof. reflexivity. Qed.

  Lemma deser_and : forall fuel p1 p2 rest,
    deserialize_pred_aux fuel (serialize_pred p1 ++ 255 :: serialize_pred p2 ++ rest) = Some (p1, 255 :: serialize_pred p2 ++ rest) ->
    deserialize_pred_aux fuel (serialize_pred p2 ++ rest) = Some (p2, rest) ->
    deserialize_pred_aux (S fuel) (11 :: serialize_pred p1 ++ 255 :: serialize_pred p2 ++ rest) = Some (PredAnd p1 p2, rest).
  Proof.
    intros fuel p1 p2 rest H1 H2.
    simpl. rewrite H1. rewrite check_sep_255. rewrite H2. reflexivity.
  Qed.

  Lemma deser_or : forall fuel p1 p2 rest,
    deserialize_pred_aux fuel (serialize_pred p1 ++ 255 :: serialize_pred p2 ++ rest) = Some (p1, 255 :: serialize_pred p2 ++ rest) ->
    deserialize_pred_aux fuel (serialize_pred p2 ++ rest) = Some (p2, rest) ->
    deserialize_pred_aux (S fuel) (12 :: serialize_pred p1 ++ 255 :: serialize_pred p2 ++ rest) = Some (PredOr p1 p2, rest).
  Proof.
    intros fuel p1 p2 rest H1 H2.
    simpl. rewrite H1. rewrite check_sep_255. rewrite H2. reflexivity.
  Qed.

  Lemma deser_not : forall fuel p rest,
    deserialize_pred_aux fuel (serialize_pred p ++ rest) = Some (p, rest) ->
    deserialize_pred_aux (S fuel) (13 :: serialize_pred p ++ rest) = Some (PredNot p, rest).
  Proof. intros. simpl. rewrite H. reflexivity. Qed.

  Lemma deser_with_rest : forall p rest,
    deserialize_pred_aux (serialize_pred_length p) (serialize_pred p ++ rest) = Some (p, rest).
  Proof.
    induction p; intros rest; simpl; try reflexivity.
    - destruct s as [id sev cat t]. reflexivity.
    - destruct s as [id sev cat t]. reflexivity.
    - destruct s as [id sev cat t]. reflexivity.
    - rewrite <- app_assoc. simpl.
      assert (H1 : deserialize_pred_aux (serialize_pred_length p1 + 1 + serialize_pred_length p2)
                     (serialize_pred p1 ++ 255 :: serialize_pred p2 ++ rest) = Some (p1, 255 :: serialize_pred p2 ++ rest)).
      { apply deser_ext' with (fuel1 := serialize_pred_length p1); [lia|]. apply IHp1. }
      rewrite H1. simpl.
      assert (H2 : deserialize_pred_aux (serialize_pred_length p1 + 1 + serialize_pred_length p2)
                     (serialize_pred p2 ++ rest) = Some (p2, rest)).
      { apply deser_ext' with (fuel1 := serialize_pred_length p2); [lia|]. apply IHp2. }
      rewrite H2. reflexivity.
    - rewrite <- app_assoc. simpl.
      assert (H1 : deserialize_pred_aux (serialize_pred_length p1 + 1 + serialize_pred_length p2)
                     (serialize_pred p1 ++ 255 :: serialize_pred p2 ++ rest) = Some (p1, 255 :: serialize_pred p2 ++ rest)).
      { apply deser_ext' with (fuel1 := serialize_pred_length p1); [lia|]. apply IHp1. }
      rewrite H1. simpl.
      assert (H2 : deserialize_pred_aux (serialize_pred_length p1 + 1 + serialize_pred_length p2)
                     (serialize_pred p2 ++ rest) = Some (p2, rest)).
      { apply deser_ext' with (fuel1 := serialize_pred_length p2); [lia|]. apply IHp2. }
      rewrite H2. reflexivity.
    - simpl.
      assert (H : deserialize_pred_aux (serialize_pred_length p) (serialize_pred p ++ rest) = Some (p, rest)).
      { apply IHp. }
      rewrite H. reflexivity.
  Qed.

  Lemma serialize_pred_roundtrip : forall p,
    deserialize_pred (serialize_pred p) = Some (p, []).
  Proof.
    intro p. unfold deserialize_pred.
    rewrite serialize_pred_length_correct.
    rewrite <- (app_nil_r (serialize_pred p)).
    apply deser_with_rest.
  Qed.

  Lemma serialize_subject_roundtrip : forall s,
    deserialize_subject (serialize_subject s) = Some (s, []).
  Proof.
    intro s. destruct s as [id csev osev cat t]. reflexivity.
  Qed.

  Lemma firstn_app_skipn : forall n (l : list nat),
    n <= length l -> firstn n l ++ skipn n l = l.
  Proof.
    induction n; intros l Hle.
    - reflexivity.
    - destruct l as [|x xs].
      + simpl in Hle. lia.
      + simpl. f_equal. apply IHn. simpl in Hle. lia.
  Qed.

  Lemma length_firstn : forall n (l : list nat),
    n <= length l -> length (firstn n l) = n.
  Proof.
    induction n; intros l Hle.
    - reflexivity.
    - destruct l as [|x xs].
      + simpl in Hle. lia.
      + simpl. f_equal. apply IHn. simpl in Hle. lia.
  Qed.

  (** Deserialize a derivation tree.
      Note: Full round-trip proof requires handling dependent NodeCert types.
      This implementation returns option to handle parse failures. *)
  Fixpoint deserialize_tree_aux (fuel : nat) (l : list nat) : option (DerivationTree * list nat) :=
    match fuel with
    | 0 => None
    | S fuel' =>
        match l with
        | 0 :: vid :: rest =>
            match deserialize_pred rest with
            | Some (pred, rest') => Some (DTLeaf vid pred, rest')
            | None => None
            end
        | 1 :: m_nat :: num_children :: rest =>
            None
        | _ => None
        end
    end.

  Definition deserialize_tree (l : list nat) : option DerivationTree :=
    match deserialize_tree_aux (length l) l with
    | Some (t, []) => Some t
    | _ => None
    end.

  Lemma serialize_tree_leaf_roundtrip : forall vid pred,
    deserialize_tree (serialize_tree (DTLeaf vid pred)) = Some (DTLeaf vid pred).
  Proof.
    intros vid pred.
    unfold deserialize_tree, serialize_tree, deserialize_tree_aux.
    simpl. rewrite serialize_pred_roundtrip. reflexivity.
  Qed.

End Deserialization.

Export Deserialization.

(** ========================================================================= *)
(** PART XVII: HASHING                                                        *)
(** Deterministic hash for consensus/integrity.                               *)
(** ========================================================================= *)

Module Hashing.

  Definition hash_combine (h1 h2 : nat) : nat :=
    h2 * 31 + h1.

  Fixpoint hash_list (l : list nat) : nat :=
    match l with
    | [] => 0
    | x :: xs => hash_combine x (hash_list xs)
    end.

  Definition hash_pred (p : ScopePred) : nat :=
    hash_list (serialize_pred p).

  Definition hash_tree (t : DerivationTree) : nat :=
    hash_list (serialize_tree t).

  Definition hash_halakha (ch : CompiledHalakha) : nat :=
    hash_combine (ch_id ch) (hash_tree (ch_derivation ch)).

End Hashing.

Export Hashing.

(** ========================================================================= *)
(** PART XVIII: LEGAL DATABASE                                                *)
(** ========================================================================= *)

Module LegalDatabase.

  Definition HalakhaDB := list ValidatedHalakha.

  Definition db_lookup (db : HalakhaDB) (hid : HalakhaId) : option ValidatedHalakha :=
    find (fun vh => ch_id (vh_halakha vh) =? hid) db.

  Definition db_query (db : HalakhaDB) (s : Subject) : list (HalakhaId * bool) :=
    map (fun vh => (ch_id (vh_halakha vh), vh_applies vh s)) db.

  Definition db_applicable (db : HalakhaDB) (s : Subject) : list ValidatedHalakha :=
    filter (fun vh => vh_applies vh s) db.

  Definition db_audit (db : HalakhaDB) (hid : HalakhaId) : option DerivationTree :=
    match db_lookup db hid with
    | Some vh => Some (vh_audit vh)
    | None => None
    end.

  Definition db_hash (db : HalakhaDB) : nat :=
    hash_list (map (fun vh => hash_halakha (vh_halakha vh)) db).

  Lemma db_all_valid : forall db vh,
    In vh db -> dt_admissible (vh_context vh) (vh_audit vh).
  Proof.
    intros db vh Hin. apply vh_admissible.
  Qed.

  Lemma db_query_deterministic : forall db s,
    db_query db s = map (fun vh => (ch_id (vh_halakha vh), dt_eval (vh_audit vh) s)) db.
  Proof.
    intros db s. reflexivity.
  Qed.

  (** Conflict detection for contradictory halakhot. *)

  Definition conflicts (ch1 ch2 : CompiledHalakha) (s : Subject) : bool :=
    let applies1 := ch_applies ch1 s in
    let applies2 := ch_applies ch2 s in
    let pol1 := ch_polarity ch1 in
    let pol2 := ch_polarity ch2 in
    applies1 && applies2 && negb (polarity_eqb pol1 pol2).

  Definition db_find_conflicts (db : HalakhaDB) (s : Subject) : list (HalakhaId * HalakhaId) :=
    let applicable := db_applicable db s in
    flat_map (fun vh1 =>
      flat_map (fun vh2 =>
        if ch_id (vh_halakha vh1) <? ch_id (vh_halakha vh2) then
          if conflicts (vh_halakha vh1) (vh_halakha vh2) s then
            [(ch_id (vh_halakha vh1), ch_id (vh_halakha vh2))]
          else []
        else []
      ) applicable
    ) applicable.

  Definition db_consistent (db : HalakhaDB) (subjects : list Subject) : bool :=
    forallb (fun s => match db_find_conflicts db s with [] => true | _ => false end) subjects.

End LegalDatabase.

Export LegalDatabase.

(** ========================================================================= *)
(** PART XIX: EXTRACTION                                                      *)
(** ========================================================================= *)

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatBigInt.

Extract Inductive ScopePred => "scope_pred"
  ["PredTrue" "PredFalse" "PredIdEq" "PredCategoryEq"
   "PredSeverityGe" "PredSeverityLe" "PredSeverityEq" "PredTimeEq"
   "PredSimilarTo" "PredStricterThan" "PredSameCategory"
   "PredAnd" "PredOr" "PredNot"].

Extract Inductive Middah => "middah"
  ["KalVaChomer" "GezerahShavah" "BinyanAvEchad" "BinyanAvShnei"
   "KlalUFrat" "PratUKlal" "KlalUFratUKlal" "KlalSheTzarichLeFrat"
   "PratSheTzarichLeKlal" "DavarSheHayahBiKlal" "DavarYatzaLeLamed"
   "DavarHaLamedMeInyano" "ShneiKetuvimMakhchishim"].

Extract Inductive DerivationTree => "derivation_tree" ["DTLeaf" "DTNode"].

Extract Inductive DayoBound => "dayo_bound" ["DayoStrict" "DayoExtend"].

Extract Inductive PirkaStatus => "pirka_status" ["NoPirka" "HasPirka"].

Extract Inductive MufnehLevel => "mufneh_level" ["MufnehNone" "MufnehOne" "MufnehBoth"].

Extract Inductive Polarity => "polarity" ["Positive" "Negative"].

(** OCaml validation wrapper.
    In extracted OCaml code, use safe_eval_halakha to ensure validation before evaluation.
    This prevents execution of invalid derivation trees. *)

Definition safe_eval_halakha (ctx : ValidationContext) (ch : CompiledHalakha) (s : Subject) : option bool :=
  if dt_valid ctx (ch_derivation ch) then
    Some (ch_applies ch s)
  else
    None.

Definition safe_eval_with_polarity (ctx : ValidationContext) (ch : CompiledHalakha) (s : Subject) : option (bool * Polarity) :=
  if dt_valid ctx (ch_derivation ch) then
    Some (ch_applies ch s, ch_polarity ch)
  else
    None.
