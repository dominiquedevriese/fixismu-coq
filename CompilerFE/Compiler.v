(* Require Import StlcFix.SpecScoping. *)
(* Require Import StlcFix.LemmasScoping. *)
(* Require Import StlcFix.DecideEval. *)
Require Import LogRelFE.PseudoType.
Require Import LogRelFE.LemmasPseudoType.
Require Import LogRelFE.LR.
Require Import LogRelFE.LemmasLR.
Require Import LogRelFE.LemmasIntro.
Require Import Lia.
Require Import Db.Lemmas.

Require Import StlcFix.SpecEvaluation.
Require Import StlcFix.SpecSyntax.
Require Import StlcFix.SpecTyping.
Require Import StlcFix.SpecAnnot.
Require Import StlcFix.LemmasTyping.
Require Import StlcFix.LemmasEvaluation.
Require Import StlcFix.CanForm.
Require Import StlcFix.SpecEquivalent.
Require Import StlcFix.Size.

Require Import StlcEqui.SpecEvaluation.
Require Import StlcEqui.SpecSyntax.
Require Import StlcEqui.SpecTyping.
Require Import StlcEqui.SpecAnnot.
Require Import StlcEqui.LemmasTyping.
Require Import StlcEqui.LemmasEvaluation.
Require Import StlcEqui.CanForm.
Require Import StlcEqui.Fix.
Require Import StlcEqui.SpecEquivalent.
Require Import StlcEqui.Size.

Module F.
  Include StlcFix.SpecEvaluation.
  Include StlcFix.SpecSyntax.
  Include StlcFix.SpecTyping.
  Include StlcFix.SpecAnnot.
  Include StlcFix.LemmasTyping.
  Include StlcFix.LemmasEvaluation.
  Include StlcFix.CanForm.
  Include StlcFix.Size.
End F.

Module E.
  Include StlcEqui.SpecEvaluation.
  Include StlcEqui.SpecSyntax.
  Include StlcEqui.SpecTyping.
  Include StlcEqui.SpecAnnot.
  Include StlcEqui.LemmasTyping.
  Include StlcEqui.LemmasEvaluation.
  Include StlcEqui.CanForm.
  Include StlcEqui.Fix.
  Include StlcEqui.Size.
End E.

Fixpoint compfe_ty (τ : F.Ty) : E.Ty :=
  match τ with
    | F.tunit => E.tunit
    | F.tbool => E.tbool
    | F.tprod τ1 τ2 => E.tprod (compfe_ty τ1) (compfe_ty τ2)
    | F.tarr τ1 τ2 => E.tarr (compfe_ty τ1) (compfe_ty τ2)
    | F.tsum τ1 τ2 => E.tsum (compfe_ty τ1) (compfe_ty τ2)
  end.

Lemma validTy_compfe_ty {τ} : ValidTy (compfe_ty τ).
Proof.
  induction τ; cbn; crushValidTy.
Qed.

Fixpoint compfe_env (Γ : F.Env) : E.Env :=
  match Γ with
    | F.empty => E.empty
    | F.evar Γ τ => E.evar (compfe_env Γ) (compfe_ty τ)
  end.

Fixpoint compfe (t : F.Tm) : E.Tm :=
  match t with
    | F.var x => E.var x
    | F.abs τ t => E.abs (compfe_ty τ) (compfe t)
    | F.app t1 t2 => E.app (compfe t1) (compfe t2)
    | F.unit => E.unit
    | F.true => E.true
    | F.false => E.false
    | F.ite t1 t2 t3 => E.ite (compfe t1) (compfe t2) (compfe t3)
    | F.pair t1 t2 => E.pair (compfe t1) (compfe t2)
    | F.proj₁ t => E.proj₁ (compfe t)
    | F.proj₂ t => E.proj₂ (compfe t)
    | F.inl t => E.inl (compfe t)
    | F.inr t => E.inr (compfe t)
    | F.caseof t1 t2 t3 => E.caseof (compfe t1) (compfe t2) (compfe t3)
    | F.seq t1 t2 => E.seq (compfe t1) (compfe t2)
    | F.fixt τ1 τ2 t => E.app (E.ufix (compfe_ty τ1) (compfe_ty τ2)) (compfe t)
  end.

Fixpoint compfe_annot (t : F.TmA) : E.TmA :=
  match t with
    | F.a_var x => E.ea_var x
    | F.a_abs τ₁ τ₂ t => E.ea_abs (compfe_ty τ₁) (compfe_ty τ₂) (compfe_annot t)
    | F.a_app τ₁ τ₂ t1 t2 => E.ea_app (compfe_ty τ₁) (compfe_ty τ₂) (compfe_annot t1) (compfe_annot t2)
    | F.a_unit => E.ea_unit
    | F.a_true => E.ea_true
    | F.a_false => E.ea_false
    | F.a_ite τ t1 t2 t3 => E.ea_ite (compfe_ty τ) (compfe_annot t1) (compfe_annot t2) (compfe_annot t3)
    | F.a_pair τ₁ τ₂ t1 t2 => E.ea_pair (compfe_ty τ₁) (compfe_ty τ₂) (compfe_annot t1) (compfe_annot t2)
    | F.a_proj₁ τ₁ τ₂ t => E.ea_proj₁ (compfe_ty τ₁) (compfe_ty τ₂) (compfe_annot t)
    | F.a_proj₂ τ₁ τ₂ t => E.ea_proj₂ (compfe_ty τ₁) (compfe_ty τ₂) (compfe_annot t)
    | F.a_inl τ₁ τ₂ t => E.ea_inl (compfe_ty τ₁) (compfe_ty τ₂) (compfe_annot t)
    | F.a_inr τ₁ τ₂ t => E.ea_inr (compfe_ty τ₁) (compfe_ty τ₂) (compfe_annot t)
    | F.a_caseof τ₁ τ₂ τ t1 t2 t3 => E.ea_caseof (compfe_ty τ₁) (compfe_ty τ₂) (compfe_ty τ) (compfe_annot t1) (compfe_annot t2) (compfe_annot t3)
    | F.a_seq τ t₁ t₂ => E.ea_seq (compfe_ty τ) (compfe_annot t₁) (compfe_annot t₂)
    | F.a_fixt τ1 τ2 t => E.ea_app (tarr (tarr (compfe_ty τ1) (compfe_ty τ2)) (tarr (compfe_ty τ1) (compfe_ty τ2))) (tarr (compfe_ty τ1) (compfe_ty τ2)) (E.ufix_annot (compfe_ty τ1) (compfe_ty τ2)) (compfe_annot t)
  end.

(* The two compiler definitions are the same modulo type annotations. *)
Lemma compfe_compfe_annot {t} :
  compfe (F.eraseAnnot t) = E.eraseAnnot (compfe_annot t).
Proof.
  induction t; cbn; f_equal; try assumption; try reflexivity.
Qed.

Fixpoint compfe_pctx_annot (C : F.PCtxA) : E.PCtxA :=
  match C with
  | F.a_phole => E.ea_phole
  | F.a_pabs τ₁ τ₂ C => E.ea_pabs (compfe_ty τ₁) (compfe_ty τ₂) (compfe_pctx_annot C)
  | F.a_papp₁ τ₁ τ₂ C t => E.ea_papp₁ (compfe_ty τ₁) (compfe_ty τ₂) (compfe_pctx_annot C) (compfe_annot t)
  | F.a_papp₂ τ₁ τ₂ t C => E.ea_papp₂ (compfe_ty τ₁) (compfe_ty τ₂) (compfe_annot t) (compfe_pctx_annot C)
  | F.a_pite₁ τ C t₂ t₃ => E.ea_pite₁ (compfe_ty τ) (compfe_pctx_annot C) (compfe_annot t₂) (compfe_annot t₃)
  | F.a_pite₂ τ t₁ C t₃ => E.ea_pite₂ (compfe_ty τ) (compfe_annot t₁) (compfe_pctx_annot C) (compfe_annot t₃)
  | F.a_pite₃ τ t₁ t₂ C => E.ea_pite₃ (compfe_ty τ) (compfe_annot t₁) (compfe_annot t₂) (compfe_pctx_annot C)
  | F.a_ppair₁ τ₁ τ₂ C t => E.ea_ppair₁ (compfe_ty τ₁) (compfe_ty τ₂) (compfe_pctx_annot C) (compfe_annot t)
  | F.a_ppair₂ τ₁ τ₂ t C => E.ea_ppair₂ (compfe_ty τ₁) (compfe_ty τ₂) (compfe_annot t) (compfe_pctx_annot C)
  | F.a_pproj₁ τ₁ τ₂ C => E.ea_pproj₁ (compfe_ty τ₁) (compfe_ty τ₂) (compfe_pctx_annot C)
  | F.a_pproj₂ τ₁ τ₂ C => E.ea_pproj₂ (compfe_ty τ₁) (compfe_ty τ₂) (compfe_pctx_annot C)
  | F.a_pinl τ₁ τ₂ C => E.ea_pinl (compfe_ty τ₁) (compfe_ty τ₂) (compfe_pctx_annot C)
  | F.a_pinr τ₁ τ₂ C => E.ea_pinr (compfe_ty τ₁) (compfe_ty τ₂) (compfe_pctx_annot C)
  | F.a_pcaseof₁ τ₁ τ₂ τ C t₂ t₃ => E.ea_pcaseof₁ (compfe_ty τ₁) (compfe_ty τ₂) (compfe_ty τ) (compfe_pctx_annot C) (compfe_annot t₂) (compfe_annot t₃)
  | F.a_pcaseof₂ τ₁ τ₂ τ t₁ C t₃ => E.ea_pcaseof₂ (compfe_ty τ₁) (compfe_ty τ₂) (compfe_ty τ) (compfe_annot t₁) (compfe_pctx_annot C) (compfe_annot t₃)
  | F.a_pcaseof₃ τ₁ τ₂ τ t₁ t₂ C => E.ea_pcaseof₃ (compfe_ty τ₁) (compfe_ty τ₂) (compfe_ty τ) (compfe_annot t₁) (compfe_annot t₂) (compfe_pctx_annot C)
  | F.a_pseq₁ τ C t₂ => E.ea_pseq₁ (compfe_ty τ) (compfe_pctx_annot C) (compfe_annot t₂)
  | F.a_pseq₂ τ t₁ C => E.ea_pseq₂ (compfe_ty τ) (compfe_annot t₁) (compfe_pctx_annot C)
  | F.a_pfixt τ₁ τ₂ C => E.ea_papp₂ (tarr (tarr (compfe_ty τ₁) (compfe_ty τ₂)) (tarr (compfe_ty τ₁) (compfe_ty τ₂)))
                                   (tarr (compfe_ty τ₁) (compfe_ty τ₂))
                                   (E.ufix_annot (compfe_ty τ₁) (compfe_ty τ₂))
                                   (compfe_pctx_annot C)
  end.

Lemma smoke_test_compiler :
  (compfe_annot F.a_unit) = E.ea_unit.
Proof.
  simpl. reflexivity.
Qed.

Lemma compfe_getevar_works {i τ Γ} :
  ⟪ i : τ ∈ Γ ⟫ →
  ⟪ i : compfe_ty τ r∈ compfe_env Γ ⟫.
Proof.
  induction 1; constructor; assumption.
Qed.

Lemma compfe_typing_works {Γ t τ} :
  ⟪ Γ ⊢ t : τ ⟫ →
  ⟪ compfe_env Γ e⊢ compfe t : compfe_ty τ ⟫.
Proof.
  induction 1; F.crushTyping; E.crushTyping; eauto using E.AnnotTyping, compfe_getevar_works, E.ufix_typing, validTy_compfe_ty.
Qed.

Lemma compfe_annot_typing_works {Γ t τ} :
  ⟪ Γ a⊢ t : τ ⟫ →
  ⟪ compfe_env Γ ea⊢ compfe_annot t : compfe_ty τ ⟫.
Proof.
  induction 1; F.crushTyping; E.crushTyping; eauto using E.AnnotTyping, compfe_getevar_works, E.ufix_annot_typing, validTy_compfe_ty.
Qed.

Lemma compfe_pctx_annot_typing_works {C Γ Γ' τ τ'} :
  ⟪ a⊢ C : Γ, τ → Γ', τ' ⟫ →
  ⟪ ea⊢ compfe_pctx_annot C : compfe_env Γ, compfe_ty τ →
  compfe_env Γ', compfe_ty τ' ⟫.
Proof.
  induction 1; eauto using PCtxTypingAnnot, compfe_typing_works, validTy_compfe_ty.
  - eapply compfe_annot_typing_works in H0.
    eauto using PCtxTypingAnnot, compfe_typing_works, validTy_compfe_ty with tyvalid.
  - eapply compfe_annot_typing_works in H.
    eauto using PCtxTypingAnnot, compfe_typing_works, validTy_compfe_ty with tyvalid.
  - eapply compfe_annot_typing_works in H0, H1.
    eauto using PCtxTypingAnnot, compfe_typing_works.
  - eapply compfe_annot_typing_works in H, H1.
    eauto using PCtxTypingAnnot, compfe_typing_works.
  - eapply compfe_annot_typing_works in H, H0.
    eauto using PCtxTypingAnnot, compfe_typing_works.
  - eapply compfe_annot_typing_works in H0.
    eauto using PCtxTypingAnnot, compfe_typing_works.
  - eapply compfe_annot_typing_works in H.
    eauto using PCtxTypingAnnot, compfe_typing_works.
  - eauto using PCtxTypingAnnot, compfe_typing_works, validTy_compfe_ty with tyvalid.
  - eauto using PCtxTypingAnnot, compfe_typing_works, validTy_compfe_ty with tyvalid.
  - eapply compfe_annot_typing_works in H0, H1.
    eauto using PCtxTypingAnnot, compfe_typing_works, validTy_compfe_ty.
  - eapply compfe_annot_typing_works in H, H1.
    eauto using PCtxTypingAnnot, compfe_typing_works, validTy_compfe_ty.
  - eapply compfe_annot_typing_works in H, H0.
    eauto using PCtxTypingAnnot, compfe_typing_works, validTy_compfe_ty.
  - eapply compfe_annot_typing_works in H0.
    eauto using PCtxTypingAnnot, compfe_typing_works, E.ufix_annot_typing.
  - eapply compfe_annot_typing_works in H.
    eauto using PCtxTypingAnnot, compfe_typing_works, E.ufix_annot_typing.
  - eauto using PCtxTypingAnnot, compfe_typing_works, E.ufix_annot_typing, validTy_compfe_ty with tyvalid2.
    cbn.
    constructor; eauto using ufix_annot_typing, validTy_compfe_ty with tyvalid.
Qed.

Lemma compileCtx_works {Γ i τ} :
  F.GetEvar Γ i τ →
  ⟪ i : embed τ p∈ embedCtx Γ ⟫.
Proof.
  induction 1; eauto using GetEvarP.
Qed.

Local Ltac crush :=
  cbn in * |- ;
  repeat
    (cbn;
     repeat crushLRMatch;
     crushOfType;
     F.crushTyping;
     E.crushTyping;
     repeat crushRepEmulEmbed;
     repeat crushRecTypesMatchH;
     repeat F.crushStlcSyntaxMatchH;
     repeat E.crushStlcSyntaxMatchH;
     subst;
     trivial
    ); try lia; eauto.

Lemma compiler_is_fxToIs_embed :
  ∀ τ : F.Ty, compfe_ty τ = fxToIs (embed τ).
Proof.
  induction τ; simpl;
    try rewrite IHτ1; try rewrite IHτ2;
      reflexivity.
Qed.

Lemma compiler_is_fxToIs_embed_env :
  ∀ Γ : F.Env, compfe_env Γ = fxToIsCtx (embedCtx Γ).
Proof.
  induction Γ; crush; apply compiler_is_fxToIs_embed.
Qed.

Section CompatibilityLemmas.

  Lemma compat_lambda {Γ τ' ts d n tu τ} :
    ValidPTy τ -> ValidPTy τ' -> ValidPEnv Γ ->
    ⟪ Γ p▻ τ' ⊩ ts ⟦ d , n ⟧ tu : τ ⟫ →
    ⟪ Γ ⊩ (F.abs (repEmul τ') ts) ⟦ d , n ⟧ (E.abs (fxToIs τ') tu) : ptarr τ' τ ⟫.
  Proof.
    crush.
    - eauto using E.wtSub_up, envrel_implies_WtSub_equi, validTy_fxToIs.
    - eauto using validTy_fxToIs.
    - eauto using E.wtSub_up, envrel_implies_WtSub_equi, validTy_fxToIs.
    - eauto using validTy_fxToIs.
    - eauto using F.wtSub_up, envrel_implies_WtSub, validTy_fxToIs.
    - repeat eexists; try reflexivity.
      intros w' fw vs vu szvu vr.
      rewrite -> ?ap_comp.
      apply H4; [lia|].
      eauto using extend_envrel, envrel_mono.
  Qed.

  Lemma compat_lambda_embed {Γ τ' ts d n tu τ} :
    ValidPEnv Γ -> ValidPTy τ ->
    ⟪ Γ p▻ embed τ' ⊩ ts ⟦ d , n ⟧ tu : τ ⟫ →
    ⟪ Γ ⊩ (F.abs τ' ts) ⟦ d , n ⟧ (E.abs (fxToIs (embed τ')) tu) : ptarr (embed τ') τ ⟫.
  Proof.
    intros vΓ vτ.
    rewrite <- (repEmul_embed_leftinv τ') at 2.
    apply compat_lambda; eauto using validPTy_embed.
  Qed.

  Lemma compat_lambda_embed' {Γ τ' ts d n tu τ} :
    ValidPEnv Γ -> ValidPTy τ ->
    ⟪ Γ p▻ embed τ' ⊩ ts ⟦ d , n ⟧ tu : τ ⟫ →
    ⟪ Γ ⊩ (F.abs τ' ts) ⟦ d , n ⟧ (E.abs (compfe_ty τ') tu) : ptarr (embed τ') τ ⟫.
  Proof.
    rewrite (compiler_is_fxToIs_embed τ').
    apply compat_lambda_embed.
  Qed.

  Lemma compat_unit {Γ d n} :
    ⟪ Γ ⊩ F.unit ⟦ d , n ⟧ E.unit : ptunit ⟫.
  Proof.
    crush.
  Qed.

  Lemma compat_true {Γ d n} :
    ⟪ Γ ⊩ F.true ⟦ d , n ⟧ E.true : ptbool ⟫.
  Proof.
    crush.
  Qed.

  Lemma compat_false {Γ d n} :
    ⟪ Γ ⊩ F.false ⟦ d , n ⟧ E.false : ptbool ⟫.
  Proof.
    crush.
  Qed.

  Lemma compat_pair {Γ d n ts₁ tu₁ τ₁ ts₂ tu₂ τ₂} :
    ValidPEnv Γ -> ValidPTy τ₁ -> ValidPTy τ₂ ->
    ⟪ Γ ⊩ ts₁ ⟦ d , n ⟧ tu₁ : τ₁ ⟫ →
    ⟪ Γ ⊩ ts₂ ⟦ d , n ⟧ tu₂ : τ₂ ⟫ →
    ⟪ Γ ⊩ F.pair ts₁ ts₂ ⟦ d , n ⟧ E.pair tu₁ tu₂ : ptprod τ₁ τ₂ ⟫.
  Proof.
    crush.
    apply termrel_pair; crush.
    refine (H5 w' _ _ _ _); unfold lev in *; try lia.
    eauto using envrel_mono.
  Qed.

  Lemma compat_app {Γ d n ts₁ tu₁ τ₁ ts₂ tu₂ τ₂} :
    ValidPEnv Γ -> ValidPTy τ₁ -> ValidPTy τ₂ ->
    ⟪ Γ ⊩ ts₁ ⟦ d , n ⟧ tu₁ : ptarr τ₁ τ₂ ⟫ →
    ⟪ Γ ⊩ ts₂ ⟦ d , n ⟧ tu₂ : τ₁ ⟫ →
    ⟪ Γ ⊩ F.app ts₁ ts₂ ⟦ d , n ⟧ E.app tu₁ tu₂ : τ₂ ⟫.
  Proof.
    intros vΓ vτ₁ vτ₂.
    crush.
    refine (termrel_app vτ₁ _ _ _); crush.
    refine (H2 w' _ _ _ _); unfold lev in *; try lia.
    eauto using envrel_mono.
  Qed.

  Lemma compat_inl {Γ d n ts tu τ₁ τ₂} :
    ValidPTy τ₁ -> ValidPTy τ₂ ->
    ⟪ Γ ⊩ ts ⟦ d , n ⟧ tu : τ₁ ⟫ →
    ⟪ Γ ⊩ F.inl ts ⟦ d , n ⟧ E.inl tu : ptsum τ₁ τ₂ ⟫.
  Proof.
    crush; eauto using validTy_fxToIs.
    refine (termrel_inl _ _ _); crush.
  Qed.

  Lemma compat_inr {Γ d n ts tu τ₁ τ₂} :
    ValidPTy τ₁ -> ValidPTy τ₂ ->
    ⟪ Γ ⊩ ts ⟦ d , n ⟧ tu : τ₂ ⟫ →
    ⟪ Γ ⊩ F.inr ts ⟦ d , n ⟧ E.inr tu : ptsum τ₁ τ₂ ⟫.
  Proof.
    crush; eauto using validTy_fxToIs.
    refine (termrel_inr _ _ _); crush.
  Qed.

  Lemma compat_seq {Γ d n ts₁ tu₁ ts₂ tu₂ τ₂} :
    ValidPEnv Γ -> ValidPTy τ₂ ->
    ⟪ Γ ⊩ ts₁ ⟦ d , n ⟧ tu₁ : ptunit ⟫ →
    ⟪ Γ ⊩ ts₂ ⟦ d , n ⟧ tu₂ : τ₂ ⟫ →
    ⟪ Γ ⊩ F.seq ts₁ ts₂ ⟦ d , n ⟧ E.seq tu₁ tu₂ : τ₂ ⟫.
  Proof.
    crush.
    apply termrel_seq; crush.
    refine (H4 w' _ _ _ _); crush.
    eauto using envrel_mono.
  Qed.

  Lemma compat_proj₂ {Γ d n ts tu τ₁ τ₂} :
    ValidPEnv Γ -> ValidPTy τ₁ -> ValidPTy τ₂ ->
    ⟪ Γ ⊩ ts ⟦ d , n ⟧ tu : ptprod τ₁ τ₂ ⟫ →
    ⟪ Γ ⊩ F.proj₂ ts ⟦ d , n ⟧ E.proj₂ tu : τ₂ ⟫.
  Proof.
    intros vΓ vτ₁ vτ₂.
    crush.
    refine (termrel_proj₂ vτ₁ _ _); crush.
  Qed.

  Lemma compat_proj₁ {Γ d n ts tu τ₁ τ₂} :
    ValidPEnv Γ -> ValidPTy τ₁ -> ValidPTy τ₂ ->
    ⟪ Γ ⊩ ts ⟦ d , n ⟧ tu : ptprod τ₁ τ₂ ⟫ →
    ⟪ Γ ⊩ F.proj₁ ts ⟦ d , n ⟧ E.proj₁ tu : τ₁ ⟫.
  Proof.
    intros vΓ vτ₁ vτ₂.
    crush.
    refine (termrel_proj₁ vτ₁ vτ₂ _); crush.
  Qed.

  Lemma compat_ite {Γ d n ts₁ tu₁ ts₂ tu₂ ts₃ tu₃ τ} :
    ValidPEnv Γ -> ValidPTy τ ->
    ⟪ Γ ⊩ ts₁ ⟦ d , n ⟧ tu₁ : ptbool ⟫ →
    ⟪ Γ ⊩ ts₂ ⟦ d , n ⟧ tu₂ : τ ⟫ →
    ⟪ Γ ⊩ ts₃ ⟦ d , n ⟧ tu₃ : τ ⟫ →
    ⟪ Γ ⊩ F.ite ts₁ ts₂ ts₃ ⟦ d , n ⟧ E.ite tu₁ tu₂ tu₃ : τ ⟫.
  Proof.
    crush.
    apply termrel_ite; crush.
    - refine (H7 w' _ _ _ _); crush.
      eauto using envrel_mono.
    - refine (H5 w' _ _ _ _); crush.
      eauto using envrel_mono.
  Qed.

  Lemma compat_caseof {Γ d n ts₁ tu₁ ts₂ tu₂ ts₃ tu₃ τ₁ τ₂ τ} :
    ValidPEnv Γ -> ValidPTy τ₁ -> ValidPTy τ₂ ->
    ⟪ Γ ⊩ ts₁ ⟦ d , n ⟧ tu₁ : ptsum τ₁ τ₂ ⟫ →
    ⟪ Γ p▻ τ₁ ⊩ ts₂ ⟦ d , n ⟧ tu₂ : τ ⟫ →
    ⟪ Γ p▻ τ₂ ⊩ ts₃ ⟦ d , n ⟧ tu₃ : τ ⟫ →
    ⟪ Γ ⊩ F.caseof ts₁ ts₂ ts₃ ⟦ d , n ⟧ E.caseof tu₁ tu₂ tu₃ : τ ⟫.
  Proof.
    intros vΓ vτ₁ vτ₂.
    crush; eauto using validTy_fxToIs.
    refine (termrel_caseof vτ₁ vτ₂ _ _ _); crush;
    rewrite -> ?ap_comp.
    - refine (H5 w' _ _ _ _); [lia|].
      eauto using extend_envrel, envrel_mono.
    - refine (H3 w' _ _ _ _); [lia|].
      eauto using extend_envrel, envrel_mono.
  Qed.

  Lemma compat_fix {Γ d n ts tu τ₁ τ₂} :
    ValidPEnv Γ -> ValidPTy τ₁ -> ValidPTy τ₂ ->
    ⟪ Γ ⊩ ts ⟦ d , n ⟧ tu : ptarr (ptarr τ₁ τ₂) (ptarr τ₁ τ₂) ⟫ →
    ⟪ Γ ⊩ F.fixt (repEmul τ₁) (repEmul τ₂) ts ⟦ d , n ⟧ E.app (E.ufix (fxToIs τ₁) (fxToIs τ₂)) tu : ptarr τ₁ τ₂ ⟫.
  Proof.
    crush.
    - eauto using E.ufix_typing, validTy_fxToIs.
    - refine (termrel_fix _ _ _); crush.
  Qed.

  Lemma compat_fix' {Γ d n ts tu τ₁ τ₂} :
    ValidPEnv Γ ->
    ⟪ Γ ⊩ ts ⟦ d , n ⟧ tu : embed (F.tarr (F.tarr τ₁ τ₂) (F.tarr τ₁ τ₂)) ⟫ →
    ⟪ Γ ⊩ F.fixt τ₁ τ₂ ts ⟦ d , n ⟧ E.app (E.ufix (compfe_ty τ₁) (compfe_ty τ₂)) tu : ptarr (embed τ₁) (embed τ₂) ⟫.
  Proof.
    intros vΓ tr.
    rewrite <- (repEmul_embed_leftinv τ₁) at 1.
    rewrite <- (repEmul_embed_leftinv τ₂) at 1.
    rewrite (compiler_is_fxToIs_embed τ₁) at 1.
    rewrite (compiler_is_fxToIs_embed τ₂) at 1.
    apply compat_fix; eauto using validPTy_embed.
  Qed.

  Lemma compat_fix'' {Γ d n ts tu τ₁ τ₂} :
    ValidPEnv Γ ->
    ⟪ Γ ⊩ ts ⟦ d , n ⟧ tu : embed (F.tarr (F.tarr τ₁ τ₂) (F.tarr τ₁ τ₂)) ⟫ →
    ⟪ Γ ⊩ F.fixt τ₁ τ₂ ts ⟦ d , n ⟧ E.app (E.ufix (fxToIs (embed τ₁)) (fxToIs (embed τ₂))) tu : ptarr (embed τ₁) (embed τ₂) ⟫.
  Proof.
    rewrite <- (compiler_is_fxToIs_embed τ₁) at 1.
    rewrite <- (compiler_is_fxToIs_embed τ₂) at 1.
    exact compat_fix'.
  Qed.

  Lemma compfe_correct {Γ d n ts τ} :
    ⟪ Γ ⊢ ts : τ ⟫ →
    ⟪ embedCtx Γ ⊩ ts ⟦ d , n ⟧ compfe ts : embed τ ⟫.
  Proof.
    induction 1;
      cbn -[E.ufix_annot E.ufix₁_annot];
      rewrite ?compiler_is_fxToIs_embed, ?eraseAnnot_ufix;
      eauto using compat_inl
      , compat_inr
      , compat_pair
      , compat_lambda_embed
      , compat_app
      , compat_false, compat_true
      , compat_var
      , compat_unit
      , embedCtx_works
      , compat_seq
      , compat_ite, compat_proj₁, compat_proj₂
      , compat_caseof
      , compat_fix''
      , validPTy_embed
      , validPEnv_embedCtx.
  Qed.

  Lemma compfe_correct' {Γ d n ts τ τ'} :
    ⟪ Γ ⊢ ts : τ ⟫ →
    τ' = embed τ ->
    ⟪ embedCtx Γ ⊩ ts ⟦ d , n ⟧ compfe ts : τ' ⟫.
  Proof.
    intros; subst; now eapply compfe_correct.
  Qed.

  Lemma compfe_annot_correct {Γ d n ts τ} :
    ⟪ Γ a⊢ ts : τ ⟫ →
    ⟪ embedCtx Γ ⊩ F.eraseAnnot ts ⟦ d , n ⟧ E.eraseAnnot (compfe_annot ts) : embed τ ⟫.
  Proof.
    induction 1;
      cbn -[E.ufix_annot E.ufix₁_annot];
      rewrite ?compiler_is_fxToIs_embed, ?eraseAnnot_ufix;
      eauto using compat_inl
      , compat_inr
      , compat_pair
      , compat_lambda_embed
      , compat_app
      , compat_false, compat_true
      , compat_var
      , compat_unit
      , embedCtx_works
      , compat_seq
      , compat_ite, compat_proj₁, compat_proj₂
      , compat_caseof
      , compat_fix''
      , validPTy_embed
      , validPEnv_embedCtx.
  Qed.

  Lemma compfe_ctx_correct {Γ Γ' d n C τ τ'} :
    ⟪ a⊢ C : Γ , τ → Γ' , τ'⟫ →
    ⟪ ⊩ F.eraseAnnot_pctx C ⟦ d , n ⟧ eraseAnnot_pctx (compfe_pctx_annot C) : embedCtx Γ , embed τ → embedCtx Γ' , embed τ' ⟫.
  Proof.
    intros ty; unfold OpenLRCtxN; split; [|split];
      rewrite <-?compiler_is_fxToIs_embed in *;
      rewrite <-?compiler_is_fxToIs_embed_env in *;
      rewrite ?repEmul_embed_leftinv in *;
      rewrite ?repEmulCtx_embedCtx_leftinv in *;
      eauto using F.eraseAnnot_pctxT, E.eraseAnnot_pctxT, compfe_pctx_annot_typing_works, F.pctxtyping_app, F.eraseAnnot_pctxT, E.pctxtyping_app, E.eraseAnnot_pctxT.

    induction ty; simpl;
    intros ts tu lr;
      try assumption; (* deal with phole *)
      specialize (IHty ts tu lr);
      rewrite <-?compfe_compfe_annot;
      repeat (try match goal with
             | [ |- ⟪_⊩ F.abs _ _ ⟦d,n⟧ E.abs _ _ : _ ⟫ ] => eapply compat_lambda_embed'
             | [ |- ⟪_⊩ F.app _ _ ⟦d,n⟧ E.app _ _ : _ ⟫ ] => eapply compat_app
             | [ |- ⟪_⊩ F.ite _ _ _ ⟦d,n⟧ E.ite _ _ _ : _ ⟫ ] => eapply compat_ite
             | [ |- ⟪_⊩ F.pair _ _ ⟦d,n⟧ E.pair _ _ : _ ⟫ ] => eapply compat_pair
             | [ |- ⟪_⊩ F.inl _ ⟦d,n⟧ E.inl _ : _ ⟫ ] => eapply compat_inl
             | [ |- ⟪_⊩ F.inr _ ⟦d,n⟧ E.inr _ : _ ⟫ ] => eapply compat_inr
             | [ |- ⟪_⊩ F.proj₁ _ ⟦d,n⟧ E.proj₁ _ : _ ⟫ ] => eapply compat_proj₁
             | [ |- ⟪_⊩ F.proj₂ _ ⟦d,n⟧ E.proj₂ _ : _ ⟫ ] => eapply compat_proj₂
             | [ |- ⟪_⊩ F.fixt _ _ _ ⟦d,n⟧ _ : _ ⟫ ] => eapply compat_fix'
             | [ |- ⟪_⊩ F.caseof _ _ _ ⟦d,n⟧ E.caseof _ _ _ : _ ⟫ ] => eapply compat_caseof
             | [ |- ⟪_⊩ F.seq _ _ ⟦d,n⟧ E.seq _ _ : _ ⟫ ] => eapply compat_seq
             (* | [ |- context[ ptarr (embed ?τ1) (embed ?τ2) ]] => *)
             (*   change (ptarr (embed τ1) (embed τ2)) with (embed (F.tarr τ1 τ2)) *)
             | [ |- ⟪_⊩ _ ⟦d,n⟧ compfe _ : _ ⟫ ] => eapply compfe_correct'
             | [ |- ⟪ _ ⊢ F.eraseAnnot _ : _ ⟫ ] => eapply F.eraseAnnotT
             | [ |- ⟪ _ ⊢ E.eraseAnnot _ : _ ⟫ ] => eapply E.eraseAnnotT
              end;
              eauto using validPTy_embed, validPEnv_embedCtx;
              try eassumption;
              fold embed;
              try reflexivity;
              change (embedCtx ?Γ p▻ embed ?τ) with (embedCtx (Γ ▻ τ))).
  Qed.

End CompatibilityLemmas.

Lemma equivalenceReflection {Γ t₁ t₂ τ} :
  ⟪ Γ ⊢ t₁ : τ ⟫ →
  ⟪ Γ ⊢ t₂ : τ ⟫ →
  ⟪ compfe_env Γ e⊢ compfe t₁ ≃ compfe t₂ : compfe_ty τ ⟫ →
  ⟪ Γ ⊢ t₁ ≃ t₂ : τ ⟫.
Proof.
  revert t₁ t₂ τ.
  enough (∀ {t₁ t₂} τ,
            ⟪ Γ ⊢ t₁ : τ ⟫ →
            ⟪ Γ ⊢ t₂ : τ ⟫ →
            ⟪ compfe_env Γ e⊢ compfe t₁ ≃ compfe t₂ : compfe_ty τ ⟫ →
            ∀ C τ',
              ⟪ a⊢ C : Γ , τ → F.empty, τ' ⟫ →
                    F.Terminating (F.pctx_app t₁ (F.eraseAnnot_pctx C)) → F.Terminating (F.pctx_app t₂ (F.eraseAnnot_pctx C))) as Hltor
  by (intros t₁ t₂ τ ty1 ty2 eq C τ';
      assert (⟪ compfe_env Γ e⊢ compfe t₂ ≃ compfe t₁ : compfe_ty τ ⟫)
        by (apply E.pctx_equiv_symm; assumption);
  split;
  refine (Hltor _ _ τ _ _ _ C τ' _); assumption).

  intros t₁ t₂ τ ty1 ty2 eq C τ' tyC term.

  destruct (F.Terminating_TermHor term) as [n termN]; clear term.

  assert (⟪ embedCtx Γ ⊩ t₁ ⟦ dir_lt , S n ⟧ compfe t₁ : embed τ ⟫) as lrt₁ by exact (compfe_correct ty1).

  assert (⟪ ⊩ (F.eraseAnnot_pctx C) ⟦ dir_lt , S n ⟧ E.eraseAnnot_pctx (compfe_pctx_annot C) : embedCtx Γ , embed τ → pempty , embed τ' ⟫) as lrC_lt
      by apply (compfe_ctx_correct tyC).

  apply lrC_lt in lrt₁.

  assert (E.Terminating (E.pctx_app (compfe t₁) (E.eraseAnnot_pctx (compfe_pctx_annot C))))
    as termu₁ by (apply (adequacy_lt lrt₁ termN); lia).

  assert (E.Terminating (E.pctx_app (compfe t₂) (E.eraseAnnot_pctx (compfe_pctx_annot C)))).
  eapply eq; try assumption; eauto using compfe_pctx_annot_typing_works, validTy_compfe_ty.
  apply (compfe_pctx_annot_typing_works tyC).

  destruct (E.Terminating_TermHor H) as [n' termN']; clear H.

  assert (⟪ ⊩ F.eraseAnnot_pctx C ⟦ dir_gt , S n' ⟧ E.eraseAnnot_pctx (compfe_pctx_annot C) : embedCtx Γ , embed τ → pempty , embed τ' ⟫) as lrC_gt
    by (apply (compfe_ctx_correct tyC)).

  assert (⟪ embedCtx Γ ⊩ t₂ ⟦ dir_gt , S n' ⟧ compfe t₂ : embed τ ⟫) as lrt₂ by exact (compfe_correct ty2).

  apply lrC_gt in lrt₂.

  apply (adequacy_gt lrt₂ termN'); lia.
Qed.

Lemma equivalenceReflectionEmpty {t₁ t₂ τ} :
  ⟪ F.empty ⊢ t₁ : τ ⟫ →
  ⟪ F.empty ⊢ t₂ : τ ⟫ →
  ⟪ E.empty e⊢ compfe t₁ ≃ compfe t₂ : compfe_ty τ ⟫ →
  ⟪ F.empty ⊢ t₁ ≃ t₂ : τ ⟫.
Proof.
  apply @equivalenceReflection.
Qed.

