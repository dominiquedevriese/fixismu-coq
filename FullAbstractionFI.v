Require Import StlcFix.SpecTyping.
Require Import StlcFix.SpecEquivalent.
Require Import StlcFix.LemmasEvaluation.
Require Import StlcFix.LemmasTyping.
Require Import StlcIso.SpecEquivalent.
Require Import StlcIso.LemmasEvaluation.

Require Import CompilerFI.Compiler.

Require Import UValFI.UVal.

Require Import LogRelFI.PseudoType.
Require Import LogRelFI.LemmasPseudoType.
Require Import LogRelFI.LR.
Require Import LogRelFI.LemmasLR.

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

Lemma equivalencePreservation {t₁ t₂ τ} :
  ⟪ F.empty ⊢ t₁ : τ ⟫ →
  ⟪ F.empty ⊢ t₂ : τ ⟫ →
  ⟪ F.empty ⊢ t₁ ≃ t₂ : τ ⟫ →
  ⟪ I.empty i⊢ compfi t₁ ≃ compfi t₂ : compfi_ty τ ⟫.
Proof.
  (* sufficient to prove one direction of equi-termination *)
  revert t₁ t₂ τ.
  enough (∀ {t₁ t₂ τ τ'},
             ValidTy τ' ->
            ⟪ F.empty ⊢ t₁ : τ ⟫ →
            ⟪ F.empty ⊢ t₂ : τ ⟫ →
            ⟪ F.empty ⊢ t₁ ≃ t₂ : τ ⟫ →
            ∀ {C}, ⟪ ia⊢ C : I.empty , compfi_ty τ → I.empty , τ' ⟫ →
                 I.Terminating (I.pctx_app (compfi t₁) (eraseAnnot_pctx C)) → I.Terminating (I.pctx_app (compfi t₂) (eraseAnnot_pctx C))) as Hltor
      by (intros t₁ t₂ τ ty1 ty2 ceq;
          assert (⟪ F.empty ⊢ t₂ ≃ t₁ : τ ⟫)
            by (apply F.pctx_equiv_symm; assumption);
          split;
          refine (Hltor _ _ _ _ _ _ _ _ _ _); eassumption).

  intros t₁ t₂ τ τ' vτ' ty₁ ty₂ ceq Cu tCu term.
  destruct (I.Terminating_TermHor term) as [n termN]; clear term.

  assert (⟪ pempty ⊩ t₁ ⟦ dir_gt , S n ⟧ compfi t₁ : embed τ ⟫) as lre₁
      by (change pempty with (embedCtx (repEmulCtx pempty));
          eapply compfi_correct;
          cbn; assumption).

  unshelve epose proof (lrfull₁ := backtranslateCtx_works vτ' (dwp_precise _) tCu lre₁).
  exact (S (S n)).
  eauto.

  unfold backtranslateCtx in lrfull₁.
  rewrite F.eraseAnnot_pctx_cat, F.pctx_cat_app in lrfull₁.
  cbn in lrfull₁.

 assert (F.Terminating (F.pctx_app (F.app (inject (S (S n)) τ) t₁)
                                    (F.eraseAnnot_pctx (emulate_pctx (S (S n)) Cu)))) as termF
    by (eapply (adequacy_gt lrfull₁ termN); eauto with arith).

  change (F.app (inject (S (S n)) τ) t₁) with (F.pctx_app t₁ (F.eraseAnnot_pctx (F.a_papp₂ τ (UValFI (S (S n)) (compfi_ty τ)) (injectA (S (S n)) τ) F.a_phole))) in termF.
  rewrite <- F.pctx_cat_app in termF.
  rewrite <- F.eraseAnnot_pctx_cat in termF.

  assert (⟪ ⊢ F.eraseAnnot_pctx (emulate_pctx (S (S n)) Cu) : F.empty, UValFI (S (S n)) (compfi_ty τ) → F.empty, UValFI (S (S n)) τ' ⟫)
    by (change F.empty with (toUVals (S (S n)) I.empty);
        eapply F.eraseAnnot_pctxT, emulate_pctx_T; assumption).

  assert (vε : ValidEnv I.empty) by eauto with tyvalid.
  pose proof (tEmCu := emulate_pctx_T (n := S (S n)) tCu).
  assert (F.Terminating (F.pctx_app t₂ (backtranslateCtx (S (S n)) τ Cu))) as termS'
      by (eapply ceq;
          eauto using F.pctxtyping_cat_annot, injectAT, emulate_pctx_T, F.PCtxTypingAnnot).
  unfold backtranslateCtx in termS'.

  destruct (F.Terminating_TermHor termS') as [m termSm']; clear termS'.

  assert (⟪ pempty ⊩ t₂ ⟦ dir_lt , S m ⟧ compfi t₂ : embed τ ⟫) as lre₂
      by (change pempty with (embedCtx (repEmulCtx pempty));
          eapply compfi_correct;
          cbn; assumption).

  epose proof (lrfull₂ := backtranslateCtx_works vτ' dwp_imprecise tCu lre₂).

  eapply (adequacy_lt lrfull₂ termSm'); eauto with arith.
Qed.

Definition FullAbstraction (t₁ : F.Tm) (t₂ : F.Tm) (τ : F.Ty) : Prop :=
  ⟪ F.empty ⊢ t₁ : τ ⟫ →
  ⟪ F.empty ⊢ t₂ : τ ⟫ →
  ⟪ F.empty ⊢ t₁ ≃ t₂ : τ ⟫ ↔
  ⟪ I.empty i⊢ compfi t₁ ≃ compfi t₂ : compfi_ty τ ⟫.

Lemma fullAbstraction {t₁ t₂ τ} : FullAbstraction t₁ t₂ τ.
Proof.
  split;
  eauto using equivalenceReflection, equivalencePreservation.
Qed.
