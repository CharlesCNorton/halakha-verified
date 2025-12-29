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

  Definition dt_requires_children (m : Middah) : nat :=
    match m with
    | ShneiKetuvimMakhchishim => 2
    | BinyanAvShnei => 2
    | KlalUFratUKlal => 3
    | GezerahShavah => 2
    | KlalUFrat => 2
    | PratUKlal => 2
    | KlalSheTzarichLeFrat => 2
    | PratSheTzarichLeKlal => 2
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

  Definition transform_restrict (base_klal base_prat : CompiledHalakha) (klal prat : VerseId) (restriction : ScopePred) (new_id : HalakhaId) : CompiledHalakha :=
    mkCompiledHalakha new_id (ch_polarity base_klal) (DTNode KlalUFrat (CertKUF (mkKUFCert klal prat restriction)) [ch_derivation base_klal; ch_derivation base_prat]).

  Definition transform_expand (base_prat base_klal : CompiledHalakha) (prat klal : VerseId) (expansion : ScopePred) (new_id : HalakhaId) : CompiledHalakha :=
    mkCompiledHalakha new_id (ch_polarity base_prat) (DTNode PratUKlal (CertPUK (mkPUKCert prat klal expansion)) [ch_derivation base_prat; ch_derivation base_klal]).

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
    (vh_klal vh_prat : ValidatedHalakha)
    (klal prat : VerseId)
    (restriction : ScopePred)
    (new_id : HalakhaId)
    (Hctx : vh_context vh_klal = vh_context vh_prat)
    (Hvalid : valid_kuf (vh_context vh_klal) (mkKUFCert klal prat restriction) = true)
    (Hanchor : dt_valid (vh_context vh_klal)
                 (DTNode KlalUFrat (CertKUF (mkKUFCert klal prat restriction))
                    [ch_derivation (vh_halakha vh_klal);
                     ch_derivation (vh_halakha vh_prat)]) = true)
    : ValidatedHalakha.
  Proof.
    exact (mkValidatedHalakha
      (transform_restrict (vh_halakha vh_klal) (vh_halakha vh_prat) klal prat restriction new_id)
      (vh_context vh_klal)
      Hanchor).
  Defined.

  Definition vtransform_expand
    (vh_prat vh_klal : ValidatedHalakha)
    (prat klal : VerseId)
    (expansion : ScopePred)
    (new_id : HalakhaId)
    (Hctx : vh_context vh_prat = vh_context vh_klal)
    (Hvalid : valid_puk (vh_context vh_prat) (mkPUKCert prat klal expansion) = true)
    (Hanchor : dt_valid (vh_context vh_prat)
                 (DTNode PratUKlal (CertPUK (mkPUKCert prat klal expansion))
                    [ch_derivation (vh_halakha vh_prat);
                     ch_derivation (vh_halakha vh_klal)]) = true)
    : ValidatedHalakha.
  Proof.
    exact (mkValidatedHalakha
      (transform_expand (vh_halakha vh_prat) (vh_halakha vh_klal) prat klal expansion new_id)
      (vh_context vh_prat)
      Hanchor).
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

  Definition nat_to_mufneh (n : nat) : option MufnehLevel :=
    match n with
    | 0 => Some MufnehNone
    | 1 => Some MufnehOne
    | 2 => Some MufnehBoth
    | _ => None
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

  Definition nat_to_middah (n : nat) : option Middah :=
    match n with
    | 0 => Some KalVaChomer
    | 1 => Some GezerahShavah
    | 2 => Some BinyanAvEchad
    | 3 => Some BinyanAvShnei
    | 4 => Some KlalUFrat
    | 5 => Some PratUKlal
    | 6 => Some KlalUFratUKlal
    | 7 => Some KlalSheTzarichLeFrat
    | 8 => Some PratSheTzarichLeKlal
    | 9 => Some DavarSheHayahBiKlal
    | 10 => Some DavarYatzaLeLamed
    | 11 => Some DavarHaLamedMeInyano
    | 12 => Some ShneiKetuvimMakhchishim
    | _ => None
    end.

  Lemma nat_to_middah_to_nat : forall m,
    nat_to_middah (middah_to_nat m) = Some m.
  Proof.
    destruct m; reflexivity.
  Qed.

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

  Definition deserialize_dayo (l : list nat) : ParseResult DayoBound :=
    match l with
    | 0 :: rest => Some (DayoStrict, rest)
    | 1 :: n :: rest => Some (DayoExtend n, rest)
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

  Definition deserialize_pirka (l : list nat) : ParseResult PirkaStatus :=
    match l with
    | 0 :: rest => Some (NoPirka, rest)
    | 1 :: rest =>
        match deserialize_pred rest with
        | Some (pred, rest') => Some (HasPirka pred, rest')
        | None => None
        end
    | _ => None
    end.

  Definition deserialize_kvc_cert (l : list nat) : ParseResult KVCCert :=
    match deserialize_subject l with
    | Some (lenient, r1) =>
        match deserialize_subject r1 with
        | Some (strict, r2) =>
            match deserialize_dayo r2 with
            | Some (dayo, r3) =>
                match deserialize_pirka r3 with
                | Some (pirka, rest) =>
                    Some (mkKVCCert lenient strict dayo pirka, rest)
                | None => None
                end
            | None => None
            end
        | None => None
        end
    | None => None
    end.

  Definition deserialize_gs_cert (l : list nat) : ParseResult GSCert :=
    match l with
    | v1 :: v2 :: root :: muf_nat :: rest =>
        match nat_to_mufneh muf_nat with
        | Some muf =>
            match deserialize_pred rest with
            | Some (transfer, rest') =>
                Some (mkGSCert v1 v2 root muf transfer, rest')
            | None => None
            end
        | None => None
        end
    | _ => None
    end.

  Definition deserialize_ba_cert (l : list nat) : ParseResult BACert :=
    match deserialize_subject l with
    | Some (paradigm, rest) => Some (mkBACert paradigm, rest)
    | None => None
    end.

  Definition deserialize_ba2_cert (l : list nat) : ParseResult BA2Cert :=
    match deserialize_subject l with
    | Some (p1, r1) =>
        match deserialize_subject r1 with
        | Some (p2, r2) =>
            match r2 with
            | cat :: rest => Some (mkBA2Cert p1 p2 cat, rest)
            | _ => None
            end
        | None => None
        end
    | None => None
    end.

  Definition deserialize_kuf_cert (l : list nat) : ParseResult KUFCert :=
    match l with
    | klal :: prat :: rest =>
        match deserialize_pred rest with
        | Some (restriction, rest') =>
            Some (mkKUFCert klal prat restriction, rest')
        | None => None
        end
    | _ => None
    end.

  Definition deserialize_puk_cert (l : list nat) : ParseResult PUKCert :=
    match l with
    | prat :: klal :: rest =>
        match deserialize_pred rest with
        | Some (expansion, rest') =>
            Some (mkPUKCert prat klal expansion, rest')
        | None => None
        end
    | _ => None
    end.

  Definition deserialize_kfk_cert (l : list nat) : ParseResult KFKCert :=
    match l with
    | k1 :: p :: k2 :: rest =>
        match deserialize_pred rest with
        | Some (similarity, rest') =>
            Some (mkKFKCert k1 p k2 similarity, rest')
        | None => None
        end
    | _ => None
    end.

  Definition deserialize_dsh_cert (l : list nat) : ParseResult DSHCert :=
    match deserialize_pred l with
    | Some (exception, rest) => Some (mkDSHCert exception, rest)
    | None => None
    end.

  Definition deserialize_dyl_cert (l : list nat) : ParseResult DYLCert :=
    match l with
    | teaching :: rest =>
        match deserialize_pred rest with
        | Some (modifier, rest') =>
            Some (mkDYLCert teaching modifier, rest')
        | None => None
        end
    | _ => None
    end.

  Definition deserialize_dmi_cert (l : list nat) : ParseResult DMICert :=
    match l with
    | v :: ctx :: rest =>
        match deserialize_pred rest with
        | Some (restriction, rest') =>
            Some (mkDMICert v ctx restriction, rest')
        | None => None
        end
    | _ => None
    end.

  Definition deserialize_skm_cert (l : list nat) : ParseResult SKMCert :=
    match l with
    | v1 :: v2 :: v3 :: rest =>
        match deserialize_pred rest with
        | Some (resolution, rest') =>
            Some (mkSKMCert v1 v2 v3 resolution, rest')
        | None => None
        end
    | _ => None
    end.

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

  Definition check_marker (marker : nat) (l : list nat) : option (list nat) :=
    match l with
    | m :: rest => if m =? marker then Some rest else None
    | [] => None
    end.

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
            match nat_to_middah m_nat with
            | None => None
            | Some m =>
                let build {M : Middah} (cert : NodeCert M) (after_cert : list nat) :=
                  match check_marker 254 after_cert with
                  | None => None
                  | Some after_marker =>
                      (fix parse_children (n : nat) (acc : list DerivationTree) (input : list nat) :=
                        match n with
                        | 0 => Some (DTNode M cert (rev acc), input)
                        | S n' =>
                            match deserialize_tree_aux fuel' input with
                            | None => None
                            | Some (child, after_child) =>
                                match check_marker 253 after_child with
                                | None => None
                                | Some r => parse_children n' (child :: acc) r
                                end
                            end
                        end) num_children [] after_marker
                  end in
                match m with
                | KalVaChomer =>
                    match deserialize_kvc_cert rest with
                    | Some (c, r) => build (CertKVC c) r
                    | None => None
                    end
                | GezerahShavah =>
                    match deserialize_gs_cert rest with
                    | Some (c, r) => build (CertGS c) r
                    | None => None
                    end
                | BinyanAvEchad =>
                    match deserialize_ba_cert rest with
                    | Some (c, r) => build (CertBA c) r
                    | None => None
                    end
                | BinyanAvShnei =>
                    match deserialize_ba2_cert rest with
                    | Some (c, r) => build (CertBA2 c) r
                    | None => None
                    end
                | KlalUFrat =>
                    match deserialize_kuf_cert rest with
                    | Some (c, r) => build (CertKUF c) r
                    | None => None
                    end
                | PratUKlal =>
                    match deserialize_puk_cert rest with
                    | Some (c, r) => build (CertPUK c) r
                    | None => None
                    end
                | KlalUFratUKlal =>
                    match deserialize_kfk_cert rest with
                    | Some (c, r) => build (CertKFK c) r
                    | None => None
                    end
                | KlalSheTzarichLeFrat =>
                    match deserialize_kuf_cert rest with
                    | Some (c, r) => build (CertKTF c) r
                    | None => None
                    end
                | PratSheTzarichLeKlal =>
                    match deserialize_puk_cert rest with
                    | Some (c, r) => build (CertPTK c) r
                    | None => None
                    end
                | DavarSheHayahBiKlal =>
                    match deserialize_dsh_cert rest with
                    | Some (c, r) => build (CertDSH c) r
                    | None => None
                    end
                | DavarYatzaLeLamed =>
                    match deserialize_dyl_cert rest with
                    | Some (c, r) => build (CertDYL c) r
                    | None => None
                    end
                | DavarHaLamedMeInyano =>
                    match deserialize_dmi_cert rest with
                    | Some (c, r) => build (CertDMI c) r
                    | None => None
                    end
                | ShneiKetuvimMakhchishim =>
                    match deserialize_skm_cert rest with
                    | Some (c, r) => build (CertSKM c) r
                    | None => None
                    end
                end
            end
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
(** FNV-1a inspired hash. For production, extract to OCaml crypto library.    *)
(** ========================================================================= *)

Module Hashing.

  Fixpoint nat_xor_aux (fuel a b : nat) : nat :=
    match fuel with
    | 0 => 0
    | S fuel' =>
        let bit_a := a mod 2 in
        let bit_b := b mod 2 in
        let xor_bit := if (bit_a =? bit_b) then 0 else 1 in
        xor_bit + 2 * nat_xor_aux fuel' (a / 2) (b / 2)
    end.

  Definition nat_xor (a b : nat) : nat :=
    nat_xor_aux 64 a b.

  Definition fnv_offset : nat := 2166136261.
  Definition fnv_prime : nat := 16777619.

  Definition hash_byte (h byte : nat) : nat :=
    (nat_xor h byte) * fnv_prime.

  Fixpoint hash_list (l : list nat) : nat :=
    match l with
    | [] => fnv_offset
    | x :: xs => hash_byte (hash_list xs) x
    end.

  Definition hash_pred (p : ScopePred) : nat :=
    hash_list (serialize_pred p).

  Definition hash_tree (t : DerivationTree) : nat :=
    hash_list (serialize_tree t).

  Definition hash_halakha (ch : CompiledHalakha) : nat :=
    hash_byte (hash_tree (ch_derivation ch)) (ch_id ch).

End Hashing.

Export Hashing.

(** ========================================================================= *)
(** PART XVIII: PRECEDENCE AND CONFLICT RESOLUTION                            *)
(** Halakhic rules for resolving contradictory sources.                       *)
(** ========================================================================= *)

Module Precedence.

  Inductive SourceType : Type :=
    | Stam : SourceType
    | Yachid : nat -> SourceType
    | Rov : SourceType
    | Minhag : SourceType.

  Inductive DerivationType : Type :=
    | Explicit : DerivationType
    | Derived : Middah -> DerivationType.

  Inductive Era : Type :=
    | Tannaitic : Era
    | Amoraic : Era
    | Gaonic : Era
    | Rishonic : Era
    | Acharonic : Era.

  Record HalakhaProvenance := mkHalakhaProvenance {
    hp_source : SourceType;
    hp_derivation : DerivationType;
    hp_era : Era;
    hp_specificity : nat;
    hp_stringency : nat
  }.

  Definition default_provenance : HalakhaProvenance :=
    mkHalakhaProvenance Stam Explicit Tannaitic 0 0.

  Definition source_weight (s : SourceType) : nat :=
    match s with
    | Rov => 4
    | Stam => 3
    | Yachid _ => 2
    | Minhag => 1
    end.

  Definition derivation_weight (d : DerivationType) : nat :=
    match d with
    | Explicit => 2
    | Derived _ => 1
    end.

  Definition era_weight (e : Era) : nat :=
    match e with
    | Tannaitic => 5
    | Amoraic => 4
    | Gaonic => 3
    | Rishonic => 2
    | Acharonic => 1
    end.

  Definition provenance_score (p : HalakhaProvenance) : nat :=
    source_weight (hp_source p) * 100 +
    derivation_weight (hp_derivation p) * 50 +
    era_weight (hp_era p) * 10 +
    hp_specificity p.

  Definition provenance_compare (p1 p2 : HalakhaProvenance) : comparison :=
    Nat.compare (provenance_score p1) (provenance_score p2).

  Definition provenance_ge (p1 p2 : HalakhaProvenance) : bool :=
    provenance_score p2 <=? provenance_score p1.

  Record ProvenancedHalakha := mkProvenancedHalakha {
    ph_halakha : CompiledHalakha;
    ph_provenance : HalakhaProvenance
  }.

  Definition ph_applies (ph : ProvenancedHalakha) (s : Subject) : bool :=
    ch_applies (ph_halakha ph) s.

  Definition ph_polarity (ph : ProvenancedHalakha) : Polarity :=
    ch_polarity (ph_halakha ph).

  Definition ph_id (ph : ProvenancedHalakha) : HalakhaId :=
    ch_id (ph_halakha ph).

  Inductive Resolution : Type :=
    | ResolveFirst : Resolution
    | ResolveSecond : Resolution
    | Unresolved : Resolution
    | NoConflict : Resolution.

  Definition resolve_by_provenance (p1 p2 : HalakhaProvenance) : Resolution :=
    match provenance_compare p1 p2 with
    | Gt => ResolveFirst
    | Lt => ResolveSecond
    | Eq => Unresolved
    end.

  Definition resolve_by_stringency (pol : Polarity) (p1 p2 : HalakhaProvenance) : Resolution :=
    match pol with
    | Negative =>
        if hp_stringency p2 <? hp_stringency p1 then ResolveFirst
        else if hp_stringency p1 <? hp_stringency p2 then ResolveSecond
        else Unresolved
    | Positive =>
        Unresolved
    end.

  Definition resolve_by_specificity (p1 p2 : HalakhaProvenance) : Resolution :=
    if hp_specificity p2 <? hp_specificity p1 then ResolveFirst
    else if hp_specificity p1 <? hp_specificity p2 then ResolveSecond
    else Unresolved.

  Definition resolve_conflict (ph1 ph2 : ProvenancedHalakha) (s : Subject) : Resolution :=
    let applies1 := ph_applies ph1 s in
    let applies2 := ph_applies ph2 s in
    let pol1 := ph_polarity ph1 in
    let pol2 := ph_polarity ph2 in
    if negb applies1 || negb applies2 then NoConflict
    else if polarity_eqb pol1 pol2 then NoConflict
    else
      let p1 := ph_provenance ph1 in
      let p2 := ph_provenance ph2 in
      match resolve_by_specificity p1 p2 with
      | Unresolved =>
          match resolve_by_provenance p1 p2 with
          | Unresolved =>
              resolve_by_stringency pol1 p1 p2
          | r => r
          end
      | r => r
      end.

  Definition resolution_winner (r : Resolution) (id1 id2 : HalakhaId) : option HalakhaId :=
    match r with
    | ResolveFirst => Some id1
    | ResolveSecond => Some id2
    | Unresolved => None
    | NoConflict => None
    end.

End Precedence.

Export Precedence.

(** ========================================================================= *)
(** PART XIX: LEGAL DATABASE                                                  *)
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

  Definition ProvenancedDB := list ProvenancedHalakha.

  Definition pdb_applicable (db : ProvenancedDB) (s : Subject) : list ProvenancedHalakha :=
    filter (fun ph => ph_applies ph s) db.

  Definition pdb_find_conflicts (db : ProvenancedDB) (s : Subject) : list (HalakhaId * HalakhaId * Resolution) :=
    let applicable := pdb_applicable db s in
    flat_map (fun ph1 =>
      flat_map (fun ph2 =>
        if ph_id ph1 <? ph_id ph2 then
          let r := resolve_conflict ph1 ph2 s in
          match r with
          | NoConflict => []
          | _ => [(ph_id ph1, ph_id ph2, r)]
          end
        else []
      ) applicable
    ) applicable.

  Definition pdb_unresolved (db : ProvenancedDB) (s : Subject) : list (HalakhaId * HalakhaId) :=
    flat_map (fun triple =>
      match triple with
      | (id1, id2, Unresolved) => [(id1, id2)]
      | _ => []
      end
    ) (pdb_find_conflicts db s).

  Definition pdb_resolved (db : ProvenancedDB) (s : Subject) : list (HalakhaId * HalakhaId * HalakhaId) :=
    flat_map (fun triple =>
      match triple with
      | (id1, id2, ResolveFirst) => [(id1, id2, id1)]
      | (id1, id2, ResolveSecond) => [(id1, id2, id2)]
      | _ => []
      end
    ) (pdb_find_conflicts db s).

  Definition pdb_effective_ruling (db : ProvenancedDB) (s : Subject) : option Polarity :=
    let applicable := pdb_applicable db s in
    match applicable with
    | [] => None
    | [ph] => Some (ph_polarity ph)
    | ph1 :: ph2 :: _ =>
        if polarity_eqb (ph_polarity ph1) (ph_polarity ph2) then
          Some (ph_polarity ph1)
        else
          match resolve_conflict ph1 ph2 s with
          | ResolveFirst => Some (ph_polarity ph1)
          | ResolveSecond => Some (ph_polarity ph2)
          | _ => None
          end
    end.

  Lemma pdb_no_unresolved_consistent : forall db subjects,
    forallb (fun s => match pdb_unresolved db s with [] => true | _ => false end) subjects = true ->
    forall s, In s subjects -> pdb_unresolved db s = [].
  Proof.
    intros db subjects Hforall s Hin.
    rewrite forallb_forall in Hforall.
    specialize (Hforall s Hin).
    destruct (pdb_unresolved db s); [reflexivity | discriminate].
  Qed.

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

Extract Inductive SourceType => "source_type" ["Stam" "Yachid" "Rov" "Minhag"].

Extract Inductive DerivationType => "derivation_type" ["Explicit" "Derived"].

Extract Inductive Era => "era" ["Tannaitic" "Amoraic" "Gaonic" "Rishonic" "Acharonic"].

Extract Inductive Resolution => "resolution" ["ResolveFirst" "ResolveSecond" "Unresolved" "NoConflict"].

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
