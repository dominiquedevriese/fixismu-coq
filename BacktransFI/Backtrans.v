Require Import StlcIso.SpecAnnot.
Require Import CompilerFI.Compiler.

Require Import UValFI.UVal.

Require Import LogRelFI.LR.

Require Import BacktransFI.Emulate.
Require Import BacktransFI.InjectExtract.
Require Import BacktransFI.UpgradeDowngrade.

Definition backtranslateCtx n τ Cu : F.PCtx := (F.eraseAnnot_pctx (F.pctxA_cat
                      (F.a_papp₂ τ (UValFI n (compfi_ty τ)) (injectA n τ) F.a_phole)
                      (emulate_pctx n Cu))).

Lemma backtranslateCtx_works {Cu m n d p τs τu ts tu} :
  ValidTy τu →
  dir_world_prec m n d p →
  ⟪ ia⊢ Cu : I.empty, compfi_ty τs → I.empty, τu ⟫ →
  ⟪ pempty ⊩ ts ⟦ d, n ⟧ tu : embed τs ⟫ →
  ⟪ pempty ⊩ (F.pctx_app ts (backtranslateCtx m τs Cu)) ⟦ d, n ⟧ I.pctx_app tu (eraseAnnot_pctx
      Cu) : pEmulDV m p τu ⟫.
Proof.
  intros vτu dwp tCu lr; destruct p; unfold backtranslateCtx;
  rewrite F.eraseAnnot_pctx_cat, F.pctx_cat_app;
  [change pempty with (toEmulDV m precise I.empty) | change pempty with (toEmulDV m imprecise I.empty)];
  eapply emulate_pctx_works; eauto using dwp_precise, dwp_imprecise with tyvalid;
  eapply inject_works_open; eauto using dwp_precise, dwp_imprecise with tyvalid.
Qed.
