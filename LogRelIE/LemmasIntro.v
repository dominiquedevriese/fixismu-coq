Require StlcIso.SpecSyntax.
Require StlcEqui.SpecSyntax.
Require Import StlcEqui.SpecTyping.
Require Import StlcIso.SpecTyping.
Require Import StlcIso.LemmasTyping.
Require Import StlcIso.CanForm.
Require Import StlcIso.SpecEvaluation.
Require Import StlcIso.LemmasEvaluation.
(* Require Import StlcEqui.SpecScoping. *)
(* Require Import StlcEqui.LemmasScoping. *)
(* Require Import StlcEqui.DecideEval. *)
Require Import UValIE.UVal.
Require Import LogRelIE.PseudoType.
Require Import LogRelIE.LemmasPseudoType.
Require Import LogRelIE.LR.
Require Import LogRelIE.LemmasLR.
Require Import Coq.micromega.Lia.
Require Import Coq.Arith.Wf_nat.
Require Import Db.Lemmas.
(* Require Import StlcEqui.Fix. *)

Local Ltac crushLRMatch :=
  match goal with
    | [ |- _ ∧ _ ] => split
    | [ H : valrel _ _ ?τ ?ts ?tu   |- OfType ?τ ?ts ?tu ] => refine (valrel_implies_OfType H)
    | [ H : valrel ?d _ ?τ ?ts ?tu  |- termrel ?d _ ?τ ?ts ?tu ] => apply valrel_in_termrel
    | [ H : valrel ?d ?w ?τ ?ts ?tu |- valrel ?d ?w' ?τ ?ts ?tu ] => refine (valrel_mono _ _ H); try lia
    | [ H : valrel _ _ _ ?ts _ |- I.Value ?ts ] => refine (proj1 (valrel_implies_Value H))
    | [ H : valrel _ _ _ _ ?tu |- E.Value ?tu ] => refine (proj2 (valrel_implies_Value H))
    | [ H : OfType _ ?ts _ |- I.Value ?ts ] => refine (proj1 (OfType_implies_Value H))
    | [ H : OfType _ _ ?tu |- E.Value ?tu ] => refine (proj2 (OfType_implies_Value H))
    | [ |- valrel _ _ _ _ _] => rewrite -> valrel_fixp; unfold valrel'
    | [ |- context[ lev ]] => unfold lev
    | [ H : context[ lev ] |- _ ] => unfold lev in *
    | [ |- exists t1, ?t2 = t1 /\ _ ] => eexists; split; [reflexivity|]
  end.

Local Ltac crush :=
  repeat
    (try assumption;
     simpl;
     destruct_conjs;
     subst*;
     repeat crushLRMatch;
     crushOfType;
     repeat crushValidPTyMatch;
     I.crushTyping;
     E.crushTyping;
     trivial;
     try reflexivity
    ); try lia; eauto.

Section ValueRelation.

  (* Lambda abstraction *)
  Lemma valrel_lambda {d τ'' τ' τ ts tu w} :
    ValidPTy τ → ValidPTy τ' → ValidTy τ'' →
    OfType (ptarr τ' τ) (I.abs (repEmul τ') ts) (E.abs (isToEq τ') tu) →
    ⟪ τ'' ≗ isToEq τ' ⟫ →
    (∀ w' vs vu, w' < w → (d = dir_gt -> E.size vu <= w') -> valrel d w' τ' vs vu → termrel d w' τ (ts [beta1 vs]) (tu [beta1 vu])) →
    valrel d w (ptarr τ' τ) (I.abs (repEmul τ') ts) (E.abs τ'' tu).
  Proof.
    intros.
    rewrite valrel_fixp; unfold valrel'.
    simpl.
    split.
    crush.
    repeat eexists; crush.
    now eapply H4.
  Qed.

  (* Unit *)
  Lemma valrel_unit {d w} :
    valrel d w ptunit I.unit E.unit.
  Proof. crush. Qed.

  (* True *)
  Lemma valrel_true {d w} :
    valrel d w ptbool I.true E.true.
  Proof. crush. Qed.

  (* False *)
  Lemma valrel_false {d w} :
    valrel d w ptbool I.false E.false.
  Proof. crush. Qed.

  (* Pair *)
  Lemma valrel_pair'' {d w τ₁ τ₂ ts₁ ts₂ tu₁ tu₂} :
    ValidPTy τ₁ -> ValidPTy τ₂ ->
    OfType τ₁ ts₁ tu₁ →
    OfType τ₂ ts₂ tu₂ →
    (forall w', w' < w → valrel d w' τ₁ ts₁ tu₁) →
    (forall w', w' < w → valrel d w' τ₂ ts₂ tu₂) →
    valrel d w (ptprod τ₁ τ₂) (I.pair ts₁ ts₂) (E.pair tu₁ tu₂).
  Proof.
    crush.
  Qed.

  Lemma valrel_pair' {d w τ₁ τ₂ ts₁ ts₂ tu₁ tu₂} :
    ValidPTy τ₁ -> ValidPTy τ₂ ->
    valrel d w τ₁ ts₁ tu₁ →
    valrel d w τ₂ ts₂ tu₂ →
    valrel d (S w) (ptprod τ₁ τ₂) (I.pair ts₁ ts₂) (E.pair tu₁ tu₂).
  Proof.
    crush.
  Qed.

  Lemma valrel_0_pair {d τ₁ τ₂ vs₁ vu₁ vs₂ vu₂} :
    ValidPTy τ₁ -> ValidPTy τ₂ ->
    OfType τ₁ vs₁ vu₁ →
    OfType τ₂ vs₂ vu₂ →
    valrel d 0 (ptprod τ₁ τ₂) (I.pair vs₁ vs₂) (E.pair vu₁ vu₂).
  Proof.
    crush.
  Qed.

  Lemma valrel_pair {d w τ₁ τ₂ ts₁ ts₂ tu₁ tu₂} :
    ValidPTy τ₁ -> ValidPTy τ₂ ->
    valrel d w τ₁ ts₁ tu₁ →
    valrel d w τ₂ ts₂ tu₂ →
    valrel d w (ptprod τ₁ τ₂) (I.pair ts₁ ts₂) (E.pair tu₁ tu₂).
  Proof.
    crush.
  Qed.


  (* Inl *)
  Lemma valrel_0_inl {d τ₁ τ₂ vs vu} :
    ValidPTy τ₁ → ValidPTy τ₂ →
    OfType τ₁ vs vu →
    valrel d 0 (ptsum τ₁ τ₂) (I.inl vs) (E.inl vu).
  Proof. crush. Qed.

  Lemma valrel_inl {d w τ₁ τ₂ vs vu} :
    ValidPTy τ₁ → ValidPTy τ₂ →
    valrel d w τ₁ vs vu →
    valrel d w (ptsum τ₁ τ₂) (I.inl vs) (E.inl vu).
  Proof. crush. Qed.

  Lemma valrel_inl' {d w τ₁ τ₂ vs vu} :
    ValidPTy τ₁ → ValidPTy τ₂ →
    valrel d w τ₁ vs vu →
    valrel d (S w) (ptsum τ₁ τ₂) (I.inl vs) (E.inl vu).
  Proof. crush. Qed.

  Lemma valrel_inl'' {d w τ₁ τ₂ vs vu} :
    ValidPTy τ₁ → ValidPTy τ₂ →
    OfType τ₁ vs vu →
    (∀ w', w' < w → valrel d w' τ₁ vs vu) →
    valrel d w (ptsum τ₁ τ₂) (I.inl vs) (E.inl vu).
  Proof. crush. Qed.

  (* Inr *)
  Lemma valrel_0_inr {d τ₁ τ₂ vs vu} :
    ValidPTy τ₁ → ValidPTy τ₂ →
    OfType τ₂ vs vu →
    valrel d 0 (ptsum τ₁ τ₂) (I.inr vs) (E.inr vu).
  Proof. crush. Qed.

  Lemma valrel_inr {d w τ₁ τ₂ vs vu} :
    ValidPTy τ₁ → ValidPTy τ₂ →
    valrel d w τ₂ vs vu →
    valrel d w (ptsum τ₁ τ₂) (I.inr vs) (E.inr vu).
  Proof. crush. Qed.

  Lemma valrel_inr' {d w τ₁ τ₂ vs vu} :
    ValidPTy τ₁ → ValidPTy τ₂ →
    valrel d w τ₂ vs vu →
    valrel d (S w) (ptsum τ₁ τ₂) (I.inr vs) (E.inr vu).
  Proof. crush. Qed.

  Lemma valrel_inr'' {d w τ₁ τ₂ vs vu} :
    ValidPTy τ₁ → ValidPTy τ₂ →
    OfType τ₂ vs vu →
    (∀ w', w' < w → valrel d w' τ₂ vs vu) →
    valrel d w (ptsum τ₁ τ₂) (I.inr vs) (E.inr vu).
  Proof. crush. Qed.

  (* double check with Marco that these hypothesis are kosher *)
  Lemma valrel_unk {d w n p vu τ} :
    OfType (pEmulDV n p τ) (unkUVal n) vu → p = imprecise →
    valrel d w (pEmulDV n p τ) (unkUVal n) vu.
  Proof.
    intros eq vvu; subst.
    repeat crushLRMatch.
    - unfold OfType, OfTypeStlcIso, OfTypeStlcEqui in *; split; simpl; split; try trivial;
      eauto using unkUVal_Value, unkUValT; crush.
    - cbn.
      eexists; split; [reflexivity|]; split; [eapply unkUVal_Value|].
      destruct n; [|left]; eauto.
  Qed.

  Lemma valrel_inUnit {d w n p vs vu} :
    vs = I.unit ∧ vu = E.unit →
    valrel d w (pEmulDV (S n) p E.tunit) (I.inl vs) vu.
  Proof.
    destruct 1 as [? ?]; subst.
    repeat crushLRMatch.
    - assert (⟪ empty i⊢ I.unit : tunit ⟫) by constructor.
      unfold OfType, OfTypeStlcIso, OfTypeStlcEqui; split; simpl; crush.
    - crush. right. exists I.unit. crush.
  Qed.

  Lemma valrel_inUnit' {d w n p vs vu} :
    valrel d w ptunit vs vu →
    valrel d w (pEmulDV (S n) p E.tunit) (I.inl vs) vu.
  Proof.
    intros vr.
    rewrite valrel_fixp in vr.
    destruct vr as [_ vr].
    simpl in vr.
    apply valrel_inUnit.
    crush.
  Qed.

  Lemma valrel_inBool {d w n p vs vu} :
    (vs = I.true ∧ vu = E.true) ∨ (vs = I.false ∧ vu = E.false) →
    valrel d w (pEmulDV (S n) p E.tbool) (inBool n vs) vu.
  Proof.
    intros eqs;
    repeat crushLRMatch.
    - assert (⟪ empty i⊢ vs : tbool ⟫);
      destruct eqs as [[? ?]|[? ?]]; subst; eauto with typing;
      unfold OfType, OfTypeStlcIso, OfTypeStlcEqui; simpl;
      eauto using inBool_Value, inBoolT with typing; crush.
    - crush.
      + destruct eqs as [[-> ->]|[-> ->]]; now cbn.
      + right; exists vs; cbn; unfold is_inl; eauto.
  Qed.

  Lemma valrel_inBool' {d w n p vs vu} :
    valrel d w ptbool vs vu →
    valrel d w (pEmulDV (S n) p E.tbool) (inBool n vs) vu.
  Proof.
    intros vr.
    rewrite valrel_fixp in vr.
    destruct vr as [_ vr].
    simpl in vr.
    apply valrel_inBool.
    crush.
  Qed.

  Lemma valrel_inProd {d w n p τ₁ τ₂ vs₁ vs₂ vu₁ vu₂} :
    OfType (pEmulDV n p τ₁) vs₁ vu₁ →
    OfType (pEmulDV n p τ₂) vs₂ vu₂ →
    (forall w', w' < w → valrel d w' (pEmulDV n p τ₁) vs₁ vu₁) →
    (forall w', w' < w → valrel d w' (pEmulDV n p τ₂) vs₂ vu₂) →
    valrel d w (pEmulDV (S n) p (E.tprod τ₁ τ₂)) (inProd n (I.pair vs₁ vs₂)) (E.pair vu₁ vu₂).
  Proof.
    intros ot₁ ot₂ vr₁ vr₂.
    destruct (OfType_implies_Value ot₁).
    destruct (OfType_implies_Value ot₂).
    repeat crushLRMatch.
    - unfold OfType, OfTypeStlcIso, OfTypeStlcEqui in *; crush.
    - crush. right. cbn. exists (I.pair vs₁ vs₂). unfold is_inl; cbn.
      crush.
  Qed.

  Lemma valrel_inProd' {d w n p τ₁ τ₂ vs₁ vs₂ vu₁ vu₂} :
    ValidTy τ₁ -> ValidTy τ₂ ->
    (valrel d w (pEmulDV n p τ₁) vs₁ vu₁) →
    (valrel d w (pEmulDV n p τ₂) vs₂ vu₂) →
    valrel d (S w) (pEmulDV (S n) p (E.tprod τ₁ τ₂)) (inProd n (I.pair vs₁ vs₂)) (E.pair vu₁ vu₂).
  Proof.
    intros vτ₁ vτ₂ vr₁ vr₂.
    eapply valrel_inProd; crush.
 Qed.

  Lemma valrel_inProd'' {d w n p τ₁ τ₂ vs vu} :
    ValidTy τ₁ -> ValidTy τ₂ ->
    valrel d w (ptprod (pEmulDV n p τ₁) (pEmulDV n p τ₂)) vs vu →
    valrel d w (pEmulDV (S n) p (tprod τ₁ τ₂)) (inProd n vs) vu.
  Proof.
    intros vτ₁ vτ₂ vr.
    rewrite valrel_fixp in vr.
    destruct vr as (val & vs2 & eqfolds & vvs & vr).
    rewrite <-eqfolds in *.
    simpl in vr; unfold prod_rel in vr.
    destruct vs; try contradiction.
    destruct vu; try contradiction.
    destruct val as ((? & ?) & (? & ?)).
    destruct vr as (? & ?).
    simpl in H0.
    simpl in H2.
    I.stlcCanForm.
    E.stlcCanForm.
    destruct H as (? & ?).
    eapply valrel_inProd; crush.
  Qed.

  Lemma valrel_inSum_l {d w n p vs vs' vu vu' τl τr} :
    ValidTy τl -> ValidTy τr ->
    OfType (pEmulDV n p τl) vs vu →
    (forall w', w' < w → valrel d w' (pEmulDV n p τl) vs vu) →
    vs' = I.inl vs ∧ vu' = E.inl vu →
    valrel d w (pEmulDV (S n) p (E.tsum τl τr)) (I.inl vs') vu'.
  Proof.
    intros vτl vτr ot vr eq.
    destruct (OfType_implies_Value ot).
    assert (I.Value vs') by (crush).
    assert (E.Value vu') by (crush).
    assert ⟪ empty i⊢ vs' : UValIE n τl r⊎ UValIE n τr ⟫
      by (destruct ot as [[? ?] ?]; crush; now apply UValIE_valid).
    assert ⟪ empty e⊢ vu' : tsum τl τr ⟫
      by (destruct ot as [? [? ?]]; crush).
    repeat crushLRMatch.
    - crush; now apply UValIE_valid.
    - crush. right. exists (I.inl vs). crush.
  Qed.

  Lemma valrel_inSum_r {d w n p vs vs' vu vu' τl τr} :
    ValidTy τl -> ValidTy τr ->
    OfType (pEmulDV n p τr) vs vu →
    (forall w', w' < w → valrel d w' (pEmulDV n p τr) vs vu) →
    vs' = I.inr vs ∧ vu' = E.inr vu →
    valrel d w (pEmulDV (S n) p (E.tsum τl τr)) (I.inl vs') vu'.
  Proof.
    intros vτl vτr ot vr eq.
    destruct (OfType_implies_Value ot).
    assert (I.Value vs') by (crush).
    assert (E.Value vu') by (crush).
    assert ⟪ empty i⊢ vs' : UValIE n τl r⊎ UValIE n τr ⟫
      by (destruct ot as [[? ?] ?]; crush; now apply UValIE_valid).
    assert ⟪ empty e⊢ vu' : tsum τl τr ⟫
      by (destruct ot as [? [? ?]]; crush).
    repeat crushLRMatch.
    - crush; now apply UValIE_valid.
    - crush. right. exists (I.inr vs). crush.
  Qed.

  (* Lemma valrel_inSum {d w n p vs vs' vu vu' τ τ'} : *)
  (*   OfType (pEmulDV n p (I.tsum τ τ')) vs vu → *)
  (*   (forall w', w' < w → valrel d w' (pEmulDV n p (I.tsum τ τ')) vs vu) → *)
  (*   (vs' = F.inl vs ∧ vu' = I.inl vu) ∨ (vs' = F.inr vs ∧ vu' = I.inr vu) → *)
  (*   valrel d w (pEmulDV (S n) p (I.tsum τ τ')) (F.inl vs') vu'. *)
  (* Proof. *)
  (*   intros ot vr eqs. *)
  (*   destruct (OfType_implies_Value ot). *)
  (*   assert (F.Value vs') by (destruct eqs as [[? ?]|[? ?]]; crush). *)
  (*   assert (I.Value vu') by (destruct eqs as [[? ?]|[? ?]]; crush). *)
  (*   destruct ot as [[? ?] [? ?]]. *)
  (*   assert ⟪ F.empty ⊢ vs' : (UValFI n τ) ⊎ (UValFI n τ') ⟫. *)
  (*   destruct eqs as [[? ?]|[? ?]]; crush. *)
  (*     by (destruct eqs as [[? ?]|[? ?]]; crush). *)
  (*   assert ⟨ 0 ⊢ vu' ⟩ *)
  (*          by (destruct eqs as [[? ?]|[? ?]]; crush). *)
  (*   crush. *)
  (*   right. exists vs'. right. right. right. left. *)
  (*   destruct eqs as [[? ?]|[? ?]]; crush. *)
  (* Qed. *)

  Lemma valrel_inSum' {d w n p vs vs' vu vu' τl τr} :
    ValidTy τl -> ValidTy τr ->
    (
      valrel d w (pEmulDV n p τl) vs vu
      ∧ (vs' = I.inl vs ∧ vu' = E.inl vu)
    ) ∨ (
      valrel d w (pEmulDV n p τr) vs vu
      ∧ (vs' = I.inr vs ∧ vu' = E.inr vu)
    ) →
    valrel d (S w) (pEmulDV (S n) p (E.tsum τl τr)) (I.inl vs') vu'.
  Proof.
    intros vτl vτr.
    destruct 1;
    destruct H.
    - refine (valrel_inSum_l _ _ _ _ H0); crush.
    - refine (valrel_inSum_r _ _ _ _ H0); crush.
  Qed.

  Lemma valrel_inSum'' {d w n p vs vu τl τr} :
    ValidTy τl -> ValidTy τr ->
    valrel d w (ptsum (pEmulDV n p τl) (pEmulDV n p τr)) vs vu →
    valrel d w (pEmulDV (S n) p (E.tsum τl τr)) (I.inl vs) vu.
  Proof.
   intros vτl vτr vr.
   rewrite valrel_fixp in vr.
   destruct vr as (val & ? & <- & vval & vr).
   destruct val as ((? & ?) & ? & ?).
   simpl in H0.
   simpl in H2.
   I.stlcCanForm;
   E.stlcCanForm;
     simpl in vr;
     try contradiction.
   - eapply valrel_inSum_l; auto; crush.
   - eapply valrel_inSum_r; auto; crush.
  Qed.

  Lemma valrel_inArr {d w n p vs vu τ₁ τ₂} :
    valrel d w (ptarr (pEmulDV n p τ₁) (pEmulDV n p τ₂)) vs vu →
    valrel d w (pEmulDV (S n) p (E.tarr τ₁ τ₂)) (I.inl vs) vu.
  Proof.
    intros vr.
    crush.
    - destruct (valrel_implies_OfType vr) as [[_ ?] _].
      eauto.
    - destruct (valrel_implies_OfType vr) as (_ & _ & ?).
      crush.
    - right. exists vs. crush.
      rewrite valrel_fixp in vr.
      destruct vr as ([_ ?] & ? & <- & vrarr).
      crush.
  Qed.

  (* Lemma valrel_0_inRec {d n p vs vu τ} : *)
  (*   OfType (pEmulDV (S n) p τ[beta1 (I.trec τ)]) vs vu → *)
  (*   valrel d 0 (pEmulDV (S n) p τ[beta1 (I.trec τ)]) vs vu. *)
  (* Proof. *)
  (*   intro ot. *)
  (*   destruct ot as [[? ?] [? ?]]. *)
  (*   crush. *)
  (*   unfold UValFI in H0. *)
  (*   F.stlcCanForm. *)
  (*   right. *)
  (*   2: destruct p; [right | left; auto]. *)
  (*   revert H2 H4. *)
  (*   generalize τ[beta1 (I.trec τ)] as τ'. *)
  (*   intros τ' H2 H4. *)
  (*   dependent destruction τ'; cbn. *)
  (*   exists x. *)
  (*   crush. *)
  (*   exists unit. *)
  (*   F.stlcCanForm. *)
  (*   I.stlcCanForm. *)
  (*   crush. *)
  (*   exists x. *)
  (*   crush. *)
  (*   unfold sum_rel. *)
  (*   F.stlcCanForm. *)
  (*   dependent induction n. *)
  (*   unfold UValFI in H0. *)


  (* Lemma valrel_inRec {d w n p vs vu τ} : *)
  (*   valrel d w (pEmulDV n p τ[beta1 (I.trec τ)]) vs vu → *)
  (*   valrel d w (pEmulDV (S n) p (I.trec τ)) (F.inl vs) (I.fold_ vu). *)
  (* Proof. *)
  (*   intros vr. *)
  (*   crush. *)
  (*   - destruct (valrel_implies_OfType vr) as [[_ ?] _]. *)
  (*     eauto. *)
  (*   - destruct (valrel_implies_OfType vr) as (_ & _ & ?). *)
  (*     eauto. *)
  (*   - right. exists vs. split. *)
  (*     + crush. *)
  (*     + exists vu. split. reflexivity. *)
  (*       destruct (valrel_implies_OfType vr) as [[? ?] [? ?]]. *)
  (*       dependent induction n. *)
  (*       intro w'; *)
  (*       rewrite valrel_fixp in vr; destruct vr as [[_ ?] vrrec]; *)
  (*       crush. *)
  (*       dependent induction τ; crush. *)
  (* Qed. *)
  (* Lemma valrel_0_inRec {n dir p vs vu τ} : *)
  (*   OfType (pEmulDV (S n) p (E.trec τ)) (I.inl (fold_ vs)) vu → *)
  (*   valrel dir 0 (pEmulDV (S n) p (E.trec τ)) (I.inl (fold_ vs)) vu. *)
  (* Proof. *)
  (*   rewrite valrel_fixp; *)
  (*   unfold valrel'; *)
  (*   split; *)
  (*   destruct 0 as [[? ?] [? ?]]; *)
  (*   crush; *)
  (*   right. *)
  (*   exists vs; crush. *)
  (*   exists vu; crush. *)
  (* Qed. *)


  Lemma valrel_inRec {d w n p vs vu τ} :
    ValidTy (trec τ) →
    valrel d w (pEmulDV n p τ[beta1 (trec τ)]) vs vu →
    valrel d w (pEmulDV n p (trec τ)) vs vu.
  Proof.
    intros [clτ crτ] vr.
    rewrite valrel_fixp in vr; unfold valrel' in vr; cbn in vr.
    change (τ[beta1 (E.trec τ)]) with (unfoldOnce (trec τ)) in vr.
    rewrite (LMC_unfoldOnce (trec τ)) in vr; try assumption; [|cbn;eauto with arith].
    cbn in vr.
    rewrite valrel_fixp; unfold valrel'; cbn.
    destruct vr as [ot vr].
    split; [|assumption].
    destruct ot as ((vvs & tys) & (vvu & tyu));
    crush;
    cbn in tys, tyu.
    rewrite UValIE_trec; try assumption.
    now inversion crτ.
    refine (WtEq _ _ _ _ tyu); try assumption.
    eapply EqMuR, tyeq_refl.
    now eapply E.ValidTy_unfold_trec.
    crushValidTy.
  Qed.
End ValueRelation.

Ltac valrelIntro :=
  match goal with
    | |- valrel _ _ (ptarr ?τ _) (I.abs (repEmul ?τ) _) (E.abs (isToEq ?τ) _) => eapply valrel_lambda
    | |- valrel _ _ ptunit I.unit E.unit => apply valrel_unit
    (* | |- valrel _ _ ptbool F.true I.true => apply valrel_true *)
    (* | |- valrel _ _ ptbool F.false I.false => apply valrel_false *)
    (* | |- valrel _ ?w (ptprod _ _) (F.pair _ _) (I.pair _ _) => *)
    (*   match w with *)
    (*     | O   => apply valrel_0_pair *)
    (*     | S _ => apply valrel_pair' *)
    (*     | _   => apply valrel_pair *)
    (*   end *)
    | |- valrel _ ?w (ptsum _ _) (I.inl _) (E.inl _) =>
      match w with
        | O   => apply valrel_0_inl
        | S _ => apply valrel_inl'
        | _   => apply valrel_inl
      end
    | |- valrel _ ?w (ptsum _ _) (I.inr _) (E.inr _) =>
      match w with
        | O   => apply valrel_0_inr
        | S _ => apply valrel_inr'
        | _   => apply valrel_inr
      end
    | [ H : valrel ?d _ ?τ ?ts ?tu |- valrel ?d _ ?τ ?ts ?tu ] =>
      refine (valrel_mono _ H); try lia
  end.

Section TermRelation.

  (* Eval context *)
  (* related terms plugged in related contexts are still related (lemma 20 in TR) *)
  Lemma termrel_ectx {d w τ₁ τ₂ ts Cs tu Cu} (eCs : I.ECtx Cs) (eCu : E.ECtx Cu) :
    termrel d w τ₁ ts tu →
    (∀ w' (fw' : w' ≤ w) vs vu, valrel d w' τ₁ vs vu → termrel d w' τ₂ (I.pctx_app vs Cs) (E.pctx_app vu Cu)) →
    termrel d w τ₂ (I.pctx_app ts Cs) (E.pctx_app tu Cu).
  Proof.
    intros tr cr Cs' Cu' eCs' eCu' cr'.
    rewrite <- I.pctx_cat_app.
    rewrite <- E.pctx_cat_app.
    refine (tr (I.pctx_cat Cs Cs') (E.pctx_cat Cu Cu') _ _ _); eauto using I.ectx_cat, E.ectx_cat.
    intros w' fw' vs vu vr.
    destruct (valrel_implies_Value vr) as [vvs vvu].
    rewrite -> I.pctx_cat_app.
    rewrite -> E.pctx_cat_app.
    refine (cr w' fw' vs vu vr Cs' Cu' eCs' eCu' _).
    refine (contrel_mono fw' cr').
  Qed.

  Lemma termrel_ectx' {d w τ₁ τ₂ ts Cs tu ts' tu' Cu} :
    termrel d w τ₁ ts tu →
    (∀ w' (fw' : w' ≤ w) vs vu, valrel d w' τ₁ vs vu → termrel d w' τ₂ (I.pctx_app vs Cs) (E.pctx_app vu Cu)) →
    ts' = I.pctx_app ts Cs →
    tu' = E.pctx_app tu Cu →
    I.ECtx Cs → E.ECtx Cu →
    termrel d w τ₂ ts' tu'.
  Proof.
    intros; subst; eauto using termrel_ectx.
  Qed.

  (* Application *)
  Lemma valrel_app {d w τ₁ τ₂ vs₁ vs₂ vu₁ vu₂} :
    ValidPTy τ₁ -> ValidPTy τ₂ ->
    valrel d w (ptarr τ₁ τ₂) vs₁ vu₁ →
    valrel d w τ₁ vs₂ vu₂ →
    termrel d w τ₂ (I.app vs₁ vs₂) (E.app vu₁ vu₂).
  Proof.
    (* destruct assumptions *)
    intros vτ₁ vτ₂ vr₁ vr₂.
    rewrite -> valrel_fixp in vr₁.
    destruct vr₁ as (ot & ? & <- & vvs1 & hyp); subst; cbn in hyp.
    apply OfType_inversion_ptarr in ot.
    destruct ot as (tsb & tub & τ₁' & eqs & equ & eqτ & tytsb & tytub); subst.
    destruct (valrel_implies_Value vr₂) as [vvs₂ vvu₂].

    eapply termrel_size_right'.
    intros szvs.

    (* beta-reduce *)
    assert (es : I.eval (I.app (I.abs (repEmul τ₁) tsb) vs₂) (tsb [beta1 vs₂])) by
        (refine (I.eval_ctx₀ I.phole _ I); refine (I.eval_beta vvs₂)).
    assert (es1 : I.evaln (I.app (I.abs (repEmul τ₁) tsb) vs₂) (tsb [beta1 vs₂]) 1) by
        (unfold I.evaln; eauto with eval; lia).
    assert (eu : E.eval (E.app (E.abs τ₁' tub) vu₂) (tub [beta1 vu₂])) by
        (refine (E.eval_ctx₀ E.phole _ I); refine (E.eval_beta vvu₂)).
    assert (eu1 : E.evaln (E.app (E.abs τ₁' tub) vu₂) (tub [beta1 vu₂]) 1) by
        (unfold E.evaln; eauto with eval).
    destruct w; try apply termrel_zero.
    refine (termrel_antired w es1 eu1 _ _ _); unfold lev in *; simpl; try lia.

    (* use assumption for function body *)
    destruct hyp as (tsb' & tub' & τ₁'' & τ₂' & eq1 & eq2 & hyp).
    inversion eq1; inversion eq2; subst.
    eapply hyp; try lia; eauto using valrel_mono.
    intros ->.
    specialize (szvs eq_refl).
    cbn in szvs.
    lia.
    assumption.
    assumption.
  Qed.

  Lemma termrel_app {d w τ₁ τ₂ ts₁ ts₂ tu₁ tu₂} :
    ValidPTy τ₁ -> ValidPTy τ₂ ->
    termrel d w (ptarr τ₁ τ₂) ts₁ tu₁ →
    (∀ w', w' ≤ w → termrel d w' τ₁ ts₂ tu₂) →
    termrel d w τ₂ (I.app ts₁ ts₂) (E.app tu₁ tu₂).
  Proof.
    intros vτ₁ vτ₂ tr₁ tr₂.
    change (I.app _ _) with (I.pctx_app ts₁ (I.papp₁ I.phole ts₂)).
    change (E.app _ _) with (E.pctx_app tu₁ (E.papp₁ E.phole tu₂)).
    refine (termrel_ectx _ _ tr₁ _); crush.
    destruct (valrel_implies_Value H) as [vvs vvu].
    change (I.app _ _) with (I.pctx_app ts₂ (I.papp₂ vs I.phole)).
    change (E.app _ _) with (E.pctx_app tu₂ (E.papp₂ vu E.phole)).
    refine (termrel_ectx _ _ (tr₂ w' fw')  _); crush.
    refine (valrel_app _ _ _ H0); crush.
  Qed.

  Lemma termrel_ite {d w τ ts₁ ts₂ ts₃ tu₁ tu₂ tu₃} :
    termrel d w ptbool ts₁ tu₁ →
    (∀ w', w' ≤ w → termrel d w' τ ts₂ tu₂) →
    (∀ w', w' ≤ w → termrel d w' τ ts₃ tu₃) →
    termrel d w τ (I.ite ts₁ ts₂ ts₃) (E.ite tu₁ tu₂ tu₃).
  Proof.
    intros tr₁ tr₂ tr₃.

    (* first evaluate ts₁ and tu₁ *)
    change (I.ite _ _ _) with (I.pctx_app ts₁ (I.pite₁ I.phole ts₂ ts₃)).
    change (E.ite _ _ _) with (E.pctx_app tu₁ (E.pite₁ E.phole tu₂ tu₃)).
    refine (termrel_ectx _ _ tr₁ _); crush.

    (* then evaluate the if-statement *)
    rewrite -> valrel_fixp in H.
    destruct H as (ot & ? & <- & _ & [[? ?]|[? ?]]); subst; clear ot.
    - assert (I.eval (I.ite I.true ts₂ ts₃) ts₂) by
          (apply (I.eval_ctx₀ I.phole); try refine (I.eval_ite_true _ _); simpl; intuition).
      assert (esn : I.evaln (I.ite I.true ts₂ ts₃) ts₂ 1) by (unfold I.evaln; eauto with eval).
      assert (E.eval (E.ite E.true tu₂ tu₃) tu₂) by
          (apply (E.eval_eval₀); try refine E.eval_ite_true; simpl; intuition).
      assert (eun : E.evaln (E.ite E.true tu₂ tu₃) tu₂ 1) by (unfold E.evaln; eauto with eval).
      refine (termrel_antired w' esn eun _ _ _); crush.
    - assert (I.eval (I.ite I.false ts₂ ts₃) ts₃) by
          (apply (I.eval_ctx₀ I.phole); try refine I.eval_ite_false; simpl; intuition).
      assert (esn : I.evaln (I.ite I.false ts₂ ts₃) ts₃ 1) by (unfold I.evaln; eauto with eval).
      assert (E.eval (E.ite E.false tu₂ tu₃) tu₃) by
          (apply (E.eval_eval₀); try refine E.eval_ite_false; simpl; intuition).
      assert (eun : E.evaln (E.ite E.false tu₂ tu₃) tu₃ 1) by (unfold E.evaln; eauto with eval).
      refine (termrel_antired w' esn eun _ _ _); crush.
  Qed.

  (* Pair *)
  Lemma termrel_pair {d w τ₁ τ₂ ts₁ ts₂ tu₁ tu₂} :
    ValidPTy τ₁ -> ValidPTy τ₂ ->
    termrel d w τ₁ ts₁ tu₁ →
    (∀ w', w' ≤ w → termrel d w' τ₂ ts₂ tu₂) →
    termrel d w (ptprod τ₁ τ₂) (I.pair ts₁ ts₂) (E.pair tu₁ tu₂).
  Proof.
    intros vτ₁ vτ₂ tr₁ tr₂.
    change (I.pair _ _) with (I.pctx_app ts₁ (I.ppair₁ I.phole ts₂)).
    change (E.pair _ _) with (E.pctx_app tu₁ (E.ppair₁ E.phole tu₂)).
    refine (termrel_ectx _ _ tr₁ _); crush.
    destruct (valrel_implies_Value H) as [vvs₂ vvu₂].
    change (I.pair _ _) with (I.pctx_app ts₂ (I.ppair₂ vs I.phole)).
    change (E.pair _ _) with (E.pctx_app tu₂ (E.ppair₂ vu E.phole)).
    refine (termrel_ectx _ _ (tr₂ w' fw')  _); crush.
    eauto using valrel_in_termrel, valrel_mono, valrel_pair.
  Qed.

  (* Proj₁ *)
  Lemma termrel_proj₁ {d w τ₁ τ₂ ts tu} :
    ValidPTy τ₁ -> ValidPTy τ₂ ->
    termrel d w (ptprod τ₁ τ₂) ts tu →
    termrel d w τ₁ (I.proj₁ ts) (E.proj₁ tu).
  Proof.
    intros vτ₁ vτ₂ tr.

    (* first evaluate ts and tu *)
    change (I.proj₁ _) with (I.pctx_app ts (I.pproj₁ I.phole)).
    change (E.proj₁ _) with (E.pctx_app tu (E.pproj₁ E.phole)).
    refine (termrel_ectx _ _ tr _); crush.

    (* then evaluate the projection *)
    rewrite -> valrel_fixp in H.
    destruct H as [ot hyp]; subst; cbn in hyp.
    apply OfType_inversion_ptprod in ot; eauto.
    destruct ot as (vs₁ & vu₁ & vs₂ & vu₂ & ? & ? & ot₁ & ot₂); subst.
    destruct (OfType_implies_Value ot₁) as [vvs₁ vvs₂].
    destruct (OfType_implies_Value ot₂) as [vvu₁ vvu₂].
    destruct hyp as (? & <- & _ & vr₁ & vr₂).

    assert (I.eval (I.proj₁ (I.pair vs₁ vs₂)) vs₁) by
        (apply (I.eval_ctx₀ I.phole); try refine (I.eval_proj₁ _ _); simpl; intuition).
    assert (esn : I.evaln (I.proj₁ (I.pair vs₁ vs₂)) vs₁ 1) by (unfold I.evaln; eauto with eval).
    assert (E.eval (E.proj₁ (E.pair vu₁ vu₂)) vu₁) by
        (apply (E.eval_eval₀); try refine (E.eval_proj₁ _ _); simpl; intuition).
    assert (eun : E.evaln (E.proj₁ (E.pair vu₁ vu₂)) vu₁ 1) by (unfold E.evaln; eauto with eval).
    destruct w'; try apply termrel_zero.
    refine (termrel_antired w' esn eun _ _ _); crush.

    (* then conclude *)
    apply valrel_in_termrel.
    apply vr₁; intuition; lia.
  Qed.

  Lemma termrel₀_proj₁ {d w τ₁ τ₂ ts tu} :
    ValidPTy τ₁ -> ValidPTy τ₂ ->
    valrel d (S w) (ptprod τ₁ τ₂) ts tu →
    termrel₀ d w τ₁ (I.proj₁ ts) (E.proj₁ tu).
  Proof.
    intros vτ₁ vτ₂ vr.

    rewrite -> valrel_fixp in vr.
    destruct vr as [ot hyp]; subst; cbn in hyp.
    apply OfType_inversion_ptprod in ot; eauto.
    destruct ot as (vs₁ & vu₁ & vs₂ & vu₂ & ? & ? & ot₁ & ot₂); subst.
    destruct (OfType_implies_Value ot₁) as [vvs₁ vvs₂].
    destruct (OfType_implies_Value ot₂) as [vvu₁ vvu₂].
    destruct hyp as (? & <- & _ & vr₁ & vr₂).

    assert (I.eval (I.proj₁ (I.pair vs₁ vs₂)) vs₁) by
        (apply (I.eval_ctx₀ I.phole); try refine (I.eval_proj₁ _ _); simpl; crush).
    assert (esn : clos_refl_trans_1n I.Tm I.eval (I.proj₁ (I.pair vs₁ vs₂)) vs₁) by (eauto with eval).
    assert (E.eval (E.proj₁ (E.pair vu₁ vu₂)) vu₁) by
        (apply (E.eval_eval₀); try refine (E.eval_proj₁ _ _); simpl; intuition).
    assert (eun : E.evalStar (E.proj₁ (E.pair vu₁ vu₂)) vu₁)
      by (unfold E.evalStar; eauto with eval).
    refine (termrel₀_antired_star esn eun _); crush.

    eapply valrel_in_termrel₀.
    apply vr₁; crush.
  Qed.

  Lemma termrel₀_proj₂ {d w τ₁ τ₂ ts tu} :
    ValidPTy τ₁ -> ValidPTy τ₂ ->
    valrel d (S w) (ptprod τ₁ τ₂) ts tu →
    termrel₀ d w τ₂ (I.proj₂ ts) (E.proj₂ tu).
  Proof.
    intros vτ₁ vτ₂ vr.

    rewrite -> valrel_fixp in vr.
    destruct vr as [ot hyp]; subst; cbn in hyp.
    apply OfType_inversion_ptprod in ot; eauto.
    destruct ot as (vs₁ & vu₁ & vs₂ & vu₂ & ? & ? & ot₁ & ot₂); subst.
    destruct (OfType_implies_Value ot₁) as [vvs₁ vvs₂].
    destruct (OfType_implies_Value ot₂) as [vvu₁ vvu₂].
    destruct hyp as (? & <- & _ & vr₁ & vr₂).

    assert (I.eval (I.proj₂ (I.pair vs₁ vs₂)) vs₂) by
        (apply (I.eval_ctx₀ I.phole); try refine (I.eval_proj₂ _ _); simpl; intuition).
    assert (esn : clos_refl_trans_1n I.Tm I.eval (I.proj₂ (I.pair vs₁ vs₂)) vs₂) by (eauto with eval).
    assert (E.eval (E.proj₂ (E.pair vu₁ vu₂)) vu₂) by
        (apply (E.eval_eval₀); try refine (E.eval_proj₂ _ _); simpl; intuition).
    assert (eun : E.evalStar (E.proj₂ (E.pair vu₁ vu₂)) vu₂)
      by (unfold E.evalStar; eauto with eval).
    refine (termrel₀_antired_star esn eun _); crush.

    eapply valrel_in_termrel₀.
    apply vr₂; crush.
  Qed.

  (* Proj₂ *)
  Lemma termrel_proj₂ {d w τ₁ τ₂ ts tu} :
    ValidPTy τ₁ -> ValidPTy τ₂ ->
    termrel d w (ptprod τ₁ τ₂) ts tu →
    termrel d w τ₂ (I.proj₂ ts) (E.proj₂ tu).
  Proof.
    intros vτ₁ vτ₂ tr.

    (* first reduce ts and tu *)
    change (I.proj₂ _) with (I.pctx_app ts (I.pproj₂ I.phole)).
    change (E.proj₂ _) with (E.pctx_app tu (E.pproj₂ E.phole)).
    refine (termrel_ectx _ _ tr _); crush.

    (* then evaluate the projection *)
    rewrite -> valrel_fixp in H.
    destruct H as [ot hyp]; subst; cbn in hyp.
    apply OfType_inversion_ptprod in ot; eauto.
    destruct ot as (vs₁ & vu₁ & vs₂ & vu₂ & ? & ? & ot₁ & ot₂); subst.
    destruct (OfType_implies_Value ot₁) as [vvs₁ vvs₂].
    destruct (OfType_implies_Value ot₂) as [vvu₁ vvu₂].
    destruct hyp as (? & <- & _ & vr₁ & vr₂).

    assert (I.eval (I.proj₂ (I.pair vs₁ vs₂)) vs₂) by
        (apply (I.eval_ctx₀ I.phole); try refine (I.eval_proj₂ _ _); simpl; intuition).
    assert (esn : I.evaln (I.proj₂ (I.pair vs₁ vs₂)) vs₂ 1) by (unfold I.evaln; eauto with eval).
    assert (E.eval (E.proj₂ (E.pair vu₁ vu₂)) vu₂) by
        (apply E.eval_eval₀; try refine (E.eval_proj₂ _ _); simpl; intuition).
    assert (eun : E.evaln (E.proj₂ (E.pair vu₁ vu₂)) vu₂ 1)
      by (unfold E.evaln; eauto with eval).
    destruct w'; try apply termrel_zero.
    refine (termrel_antired w' esn eun _ _ _); crush.

    apply valrel_in_termrel.
    apply vr₂; crush.
  Qed.

  (* Inl *)
  Lemma termrel_inl {d w τ₁ τ₂ ts tu} :
    ValidPTy τ₁ -> ValidPTy τ₂ ->
    termrel d w τ₁ ts tu →
    termrel d w (ptsum τ₁ τ₂) (I.inl ts) (E.inl tu).
  Proof.
    intros vτ₁ vτ₂ tr.
    change (I.inl ts) with (I.pctx_app ts (I.pinl I.phole)).
    change (E.inl tu) with (E.pctx_app tu (E.pinl E.phole)).
    refine (termrel_ectx _ _ tr _); crush.
    apply valrel_in_termrel; crush.
  Qed.

  (* Inr *)
  Lemma termrel_inr {d w τ₁ τ₂ ts tu} :
    ValidPTy τ₁ -> ValidPTy τ₂ ->
    termrel d w τ₂ ts tu →
    termrel d w (ptsum τ₁ τ₂) (I.inr ts) (E.inr tu).
  Proof.
    intros vτ₁ vτ₂ tr.
    change (I.inr ts) with (I.pctx_app ts (I.pinr I.phole)).
    change (E.inr tu) with (E.pctx_app tu (E.pinr E.phole)).
    refine (termrel_ectx _ _ tr _); crush.
    apply valrel_in_termrel; crush.
  Qed.

  (* Caseof *)
  Lemma termrel_caseof {d w τ τ₁ τ₂ ts₁ ts₂ ts₃ tu₁ tu₂ tu₃} :
    ValidPTy τ₁ -> ValidPTy τ₂ ->
    termrel d w (ptsum τ₁ τ₂) ts₁ tu₁ →
    (∀ w' vs₁ vu₁, w' < w → valrel d w' τ₁ vs₁ vu₁ → termrel d w' τ (ts₂ [beta1 vs₁]) (tu₂ [ beta1 vu₁])) →
    (∀ w' vs₂ vu₂, w' < w → valrel d w' τ₂ vs₂ vu₂ → termrel d w' τ (ts₃ [beta1 vs₂]) (tu₃ [ beta1 vu₂])) →
    termrel d w τ (I.caseof ts₁ ts₂ ts₃) (E.caseof tu₁ tu₂ tu₃).
  Proof.
    intros vτ₁ vτ₂ tr₁ tr₂ tr₃.

    (* first evaluate ts₁ and tu₁ *)
    change (I.caseof _ _ _) with (I.pctx_app ts₁ (I.pcaseof₁ I.phole ts₂ ts₃)).
    change (E.caseof _ _ _) with (E.pctx_app tu₁ (E.pcaseof₁ E.phole tu₂ tu₃)).
    refine (termrel_ectx _ _ tr₁ _); crush.

    (* then evaluate the caseof *)
    rewrite -> valrel_fixp in H.
    destruct H as (ot & ? & <- & _ & hyp); subst; cbn in hyp.
    apply OfType_inversion_ptsum in ot; eauto.
    destruct ot as (vs' & vu' & [(? & ? & ot)|[(? & ?)|[(? & ?)|(? & ? & ot)]]]);
      subst; cbn in *; try contradiction;
      destruct (OfType_implies_Value ot) as [vvs vvu]; clear ot.
    - assert (I.eval (I.caseof (I.inl vs') ts₂ ts₃) (ts₂ [beta1 vs'])) by
          (apply (I.eval_ctx₀ I.phole); try refine (I.eval_case_inl _); simpl; intuition).
      assert (esn : I.evaln (I.caseof (I.inl vs') ts₂ ts₃) (ts₂ [beta1 vs']) 1) by (unfold I.evaln; eauto with eval).
      assert (E.eval (E.caseof (E.inl vu') tu₂ tu₃) (tu₂ [beta1 vu'])) by
          (apply (E.eval_ctx₀ E.phole); try refine (E.eval_case_inl _); simpl; intuition).
      assert (eun : E.evaln (E.caseof (E.inl vu') tu₂ tu₃) (tu₂ [beta1 vu']) 1) by (unfold E.evaln; eauto with eval).
      destruct w'; try apply termrel_zero.
      refine (termrel_antired w' esn eun _ _ _); crush.
    - assert (I.eval (I.caseof (I.inr vs') ts₂ ts₃) (ts₃ [beta1 vs'])) by
          (apply (I.eval_ctx₀ I.phole); try refine (I.eval_case_inr _); simpl; intuition).
      assert (esn : I.evaln (I.caseof (I.inr vs') ts₂ ts₃) (ts₃ [beta1 vs']) 1) by (unfold I.evaln; eauto with eval).
      assert (E.eval (E.caseof (E.inr vu') tu₂ tu₃) (tu₃ [beta1 vu'])) by
          (apply (E.eval_ctx₀ E.phole); try refine (E.eval_case_inr _); simpl; intuition).
      assert (eun : E.evaln (E.caseof (E.inr vu') tu₂ tu₃) (tu₃ [beta1 vu']) 1) by (unfold E.evaln; eauto with eval).
      destruct w'; try apply termrel_zero.
      refine (termrel_antired w' esn eun _ _ _); crush.
  Qed.

  Lemma termreli₀_caseof {d dfc w τ τ₁ τ₂ vs₁ ts₂ ts₃ vu₁ tu₂ tu₃} :
    ValidPTy τ₁ -> ValidPTy τ₂ ->
    valrel d (S w) (ptsum τ₁ τ₂) vs₁ vu₁ →
    (∀ vs₁ vu₁, valrel d w τ₁ vs₁ vu₁ → termreli₀ d dfc (S w) τ (ts₂ [beta1 vs₁]) (tu₂ [ beta1 vu₁])) →
    (∀ vs₂ vu₂, valrel d w τ₂ vs₂ vu₂ → termreli₀ d dfc (S w) τ (ts₃ [beta1 vs₂]) (tu₃ [ beta1 vu₂])) →
    termreli₀ d dfc (S w) τ (I.caseof vs₁ ts₂ ts₃) (E.caseof vu₁ tu₂ tu₃).
  Proof.
    intros vτ₁ vτ₂ vr₁ tr₂ tr₃.

    (* then evaluate the caseof *)
    rewrite -> valrel_fixp in vr₁.
    destruct vr₁ as (ot & ? & <- & _ & hyp); subst; cbn in hyp.
    apply OfType_inversion_ptsum in ot; eauto.
    destruct ot as (vs' & vu' & [(? & ? & ot)|[(? & ?)|[(? & ?)|(? & ? & ot)]]]);
      subst; cbn in *; try contradiction;
      destruct (OfType_implies_Value ot) as [vvs vvu]; clear ot.
    - assert (I.eval (I.caseof (I.inl vs') ts₂ ts₃) (ts₂ [beta1 vs'])) by
          (apply (I.eval_ctx₀ I.phole); try refine (I.eval_case_inl _); simpl; intuition).
      assert (esn : clos_refl_trans_1n I.Tm I.eval (I.caseof (I.inl vs') ts₂ ts₃) (ts₂ [beta1 vs'])) by (eauto with eval).
      assert (E.eval (E.caseof (E.inl vu') tu₂ tu₃) (tu₂ [beta1 vu'])) by
          (apply (E.eval_ctx₀ E.phole); try refine (E.eval_case_inl _); simpl; intuition).
      assert (eun : E.evalStar (E.caseof (E.inl vu') tu₂ tu₃) (tu₂ [beta1 vu'])) by (unfold E.evalStar; eauto with eval).
      refine (termreli₀_antired_star esn eun _); crush.
    - assert (I.eval (I.caseof (I.inr vs') ts₂ ts₃) (ts₃ [beta1 vs'])) by
          (apply (I.eval_ctx₀ I.phole); try refine (I.eval_case_inr _); simpl; intuition).
      assert (esn : clos_refl_trans_1n I.Tm I.eval (I.caseof (I.inr vs') ts₂ ts₃) (ts₃ [beta1 vs'])) by (eauto with eval).
      assert (E.eval (E.caseof (E.inr vu') tu₂ tu₃) (tu₃ [beta1 vu'])) by
          (apply (E.eval_ctx₀ E.phole); try refine (E.eval_case_inr _); simpl; intuition).
      assert (eun : E.evalStar (E.caseof (E.inr vu') tu₂ tu₃) (tu₃ [beta1 vu'])) by (unfold E.evalStar; eauto with eval).
      refine (termreli₀_antired_star esn eun _); crush.
  Qed.

  (* Seq *)
  Lemma termrel_seq {d w τ ts₁ ts₂ tu₁ tu₂} :
    ValidPTy τ ->
    termrel d w ptunit ts₁ tu₁ →
    (∀ w', w' ≤ w → termrel d w' τ ts₂ tu₂) →
    termrel d w τ (I.seq ts₁ ts₂) (E.seq tu₁ tu₂).
  Proof.
    intros vτ tr₁ tr₂.

    (* first evaluate ts₁ and tu₁ *)
    change (I.seq _ _) with (I.pctx_app ts₁ (I.pseq₁ I.phole ts₂)).
    change (E.seq _ _) with (E.pctx_app tu₁ (E.pseq₁ E.phole tu₂)).
    refine (termrel_ectx _ _ tr₁ _); crush.

    (* then reduce to ts₂ and tu₂ *)
    rewrite -> valrel_fixp in H.
    destruct H as (ot & ? & <- & _ & eq₁ & eq₂); subst.
    assert (I.eval (I.seq I.unit ts₂) ts₂) by
        (apply (I.eval_ctx₀ I.phole); try refine (I.eval_seq_next _); simpl; intuition).
    assert (esn : I.evaln (I.seq I.unit ts₂) ts₂ 1) by (unfold I.evaln; eauto with eval).
    assert (E.eval (E.seq E.unit tu₂) tu₂) by
        (apply (E.eval_ctx₀ E.phole); try refine (E.eval_seq_next _); simpl; intuition).
    assert (eun : E.evaln (E.seq E.unit tu₂) tu₂ 1) by (unfold E.evaln; eauto with eval).

    (* assert (∀ Cu, E.ECtx Cu → E.eval (E.pctx_app (E.seq E.unit tu₂) Cu) (E.pctx_app tu₂ Cu)) by  *)
    (*     (intros Cu eCu; apply (E.eval_ctx₀ Cu); try refine (E.eval_seq_next _); simpl; intuition). *)
    (* assert (eun : ∀ Cu, E.ECtx Cu → E.evaln (E.pctx_app (E.seq E.unit tu₂) Cu) (E.pctx_app tu₂ Cu) 1) by eauto using E.evaln. *)

    (* attempt at using evalMax instead of doing manual labor *)
    (* pose (e := evalMax 2 (E.seq E.unit (var 0)) nil (idm UTm · tu₂) I). *)

    refine (termrel_antired w' esn eun _ _ _); try lia.

    (* conclude *)
    apply tr₂; intuition.
  Qed.

  (* unfold_ *)
  Lemma termrel_unfold_ {d w τ ts tu} :
    ValidPTy (ptrec τ) ->
    termrel d w (ptrec τ) ts tu →
    termrel d w (τ [beta1 (ptrec τ)]) (unfold_ ts) tu.
  Proof.
    intros vτ tr.

    (* first evaluate the two terms *)
    change (I.unfold_ ts) with (I.pctx_app ts (I.punfold I.phole)).
    change tu with (E.pctx_app tu E.phole).
    refine (termrel_ectx _ _ tr _); crush.

    (* then evaluate the unfold_ *)
    rewrite ->valrel_fixp in H.
    destruct H as (ot & ? & (vs2 & -> & eqfolds) & vvs2 & vr); subst.
    change (pUnfoldn (LMC_pty (ptrec τ)) (ptrec τ)) with (pUnfoldn (LMC_pty τ) (τ [ beta1 (ptrec τ )])) in *.

    assert (I.eval (I.unfold_ (I.fold_ vs2)) vs2) as eval_fold.
    { apply (I.eval_ctx₀ I.phole); [|now cbn].
      eapply I.eval_fold_unfold.
      simpl; intuition.
    }
    eapply (termrel_antired_eval_left eval_fold).

    apply valrel_in_termrel.
    rewrite ->valrel_fixp.
    split.
    - crush.
    - eexists x.
      replace (LMC_pty τ[beta1 (ptrec τ)]) with (LMC_pty τ) in *.
      split; [assumption|].
      split; [now cbn in vvs2|].
      exact vr.
      symmetry.
      refine (LMC_pUnfoldOnce (ptrec τ) _ _).
      now constructor.
      cbn; now lia.
  Qed.

  (* fold_ *)
  Lemma valrel_fold_ {d w τ vs vu} :
    ValidPTy (ptrec τ) ->
    valrel d w (τ [beta1 (ptrec τ)]) vs vu →
    valrel d w (ptrec τ) (fold_ vs) vu.
  Proof.
    intros vμτ vvs.
    rewrite valrel_fixp.
    split.
    - crush.
    - rewrite valrel_fixp in vvs.
      destruct vvs as ( tvs & vs' & unfolds & vvs & rel).
      destruct vμτ as (wsμτ & cμτ).
      assert (LMC_pty τ [beta1 (ptrec τ)] = LMC_pty τ) as eq.
      { refine (LMC_pUnfoldOnce (ptrec τ) cμτ _); cbn; lia. }
      rewrite eq in unfolds.
      exists vs'.
      split; [exists vs; intuition|].
      split; crush.
      now rewrite eq in rel.
  Qed.

  Lemma termrel_fold_ {d w τ ts tu} :
    ValidPTy (ptrec τ) ->
    termrel d w (τ [beta1 (ptrec τ)]) ts tu →
    termrel d w (ptrec τ) (fold_ ts) tu.
  Proof.
    intros vτ tr.

    (* first evaluate the two terms *)
    change (I.fold_ ts) with (I.pctx_app ts (I.pfold I.phole)).
    change tu with (E.pctx_app tu E.phole).
    refine (termrel_ectx _ _ tr _); crush.

    apply valrel_in_termrel.
    eapply valrel_fold_; crush.
  Qed.

End TermRelation.
