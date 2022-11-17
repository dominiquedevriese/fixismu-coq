Require Import StlcEqui.SpecAnnot.
Require Import CompilerFE.Compiler.

Require Import UValFE.UVal.

Require Import LogRelFE.LR.

Require Import BacktransFE.Emulate.
Require Import BacktransFE.InjectExtract.
Require Import BacktransFE.UpgradeDowngrade.

Definition backtranslateCtx n τ Cu : F.PCtx := (F.eraseAnnot_pctx (F.pctxA_cat
                      (F.a_papp₂ τ (UValFE n (compfe_ty τ)) (injectA n τ) F.a_phole)
                      (emulate_pctx n Cu))).

Lemma backtranslateCtx_works {Cu m n d p τs τu ts tu} :
  ValidTy τu →
  dir_world_prec m n d p →
  ⟪ ea⊢ Cu : E.empty, compfe_ty τs → E.empty, τu ⟫ →
  ⟪ pempty ⊩ ts ⟦ d, n ⟧ tu : embed τs ⟫ →
  ⟪ pempty ⊩ (F.pctx_app ts (backtranslateCtx m τs Cu)) ⟦ d, n ⟧ E.pctx_app tu (eraseAnnot_pctx
      Cu) : pEmulDV m p τu ⟫.
Proof.
  intros vτu dwp tCu lr; destruct p; unfold backtranslateCtx;
  rewrite F.eraseAnnot_pctx_cat, F.pctx_cat_app;
  [change pempty with (toEmulDV m precise E.empty) | change pempty with (toEmulDV m imprecise E.empty)];
  eapply emulate_pctx_works; eauto using dwp_precise, dwp_imprecise with tyvalid;
  eapply inject_works_open; eauto using dwp_precise, dwp_imprecise with tyvalid.
Qed.
