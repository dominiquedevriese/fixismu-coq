Require Import StlcEqui.SpecAnnot.
Require Import CompilerIE.Compiler.

Require Import UValIE.UVal.

Require Import LogRelIE.LR.

Require Import BacktransIE.Emulate.
Require Import BacktransIE.InjectExtract.
Require Import BacktransIE.UpgradeDowngrade.

Definition backtranslateCtx n τ Cu : I.PCtx := (I.eraseAnnot_pctx (I.pctxA_cat
                      (I.ia_papp₂ τ (UValIE n τ) (injectA n τ) I.ia_phole)
                      (emulate_pctx n Cu))).

Lemma backtranslateCtx_works {Cu m n d p τs τu ts tu} :
  ValidTy τu → ValidTy τs →
  dir_world_prec m n d p →
  ⟪ ea⊢ Cu : empty, τs → empty, τu ⟫ →
  ⟪ pempty ⊩ ts ⟦ d, n ⟧ tu : embed τs ⟫ →
  ⟪ pempty ⊩ (I.pctx_app ts (backtranslateCtx m τs Cu)) ⟦ d, n ⟧ E.pctx_app tu (eraseAnnot_pctx
      Cu) : pEmulDV m p τu ⟫.
  intros vτu vτs dwp tCu lr; destruct p; unfold backtranslateCtx;
  rewrite I.eraseAnnot_pctx_cat, I.pctx_cat_app;
  [change pempty with (toEmulDV m precise empty) | change pempty with (toEmulDV m imprecise I.empty)];
  eapply emulate_pctx_works; eauto using dwp_precise, dwp_imprecise with tyvalid;
  eapply inject_works_open; eauto using dwp_precise, dwp_imprecise with tyvalid.
Qed.
