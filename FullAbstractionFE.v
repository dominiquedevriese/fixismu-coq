Require Import StlcFix.SpecTyping.
Require Import StlcFix.SpecEquivalent.
Require Import StlcFix.LemmasEvaluation.
Require Import StlcFix.LemmasTyping.
Require Import StlcEqui.SpecEquivalent.
Require Import StlcEqui.LemmasEvaluation.

Require Import CompilerFE.Compiler.

Require Import UValFE.UVal.

Require Import LogRelFE.PseudoType.
Require Import LogRelFE.LemmasPseudoType.
Require Import LogRelFE.LR.
Require Import LogRelFE.LemmasLR.

Require Import BacktransFE.Emulate.
Require Import BacktransFE.InjectExtract.
Require Import BacktransFE.UpgradeDowngrade.

Definition backtranslateCtx n τ Cu : F.PCtx := (F.eraseAnnot_pctx (F.pctxA_cat
                      (F.a_papp₂ τ (UValFE n (compfi_ty τ)) (injectA n τ) F.a_phole)
                      (emulate_pctx n Cu))).

Lemma equivalencePreservation {t₁ t₂ τ} :
  ⟪ F.empty ⊢ t₁ : τ ⟫ →
  ⟪ F.empty ⊢ t₂ : τ ⟫ →
  ⟪ F.empty ⊢ t₁ ≃ t₂ : τ ⟫ →
  ⟪ E.empty e⊢ compfi t₁ ≃ compfi t₂ : compfi_ty τ ⟫.
Proof.
  (* sufficient to prove one direction of equi-termination *)
  revert t₁ t₂ τ.
  enough (∀ {t₁ t₂ τ τ'},
             ValidTy τ' ->
            ⟪ F.empty ⊢ t₁ : τ ⟫ →
            ⟪ F.empty ⊢ t₂ : τ ⟫ →
            ⟪ F.empty ⊢ t₁ ≃ t₂ : τ ⟫ →
            ∀ {C}, ⟪ ea⊢ C : E.empty , compfi_ty τ → E.empty , τ' ⟫ →
                 E.Terminating (E.pctx_app (compfi t₁) (eraseAnnot_pctx C)) → E.Terminating (E.pctx_app (compfi t₂) (eraseAnnot_pctx C))) as Hltor
      by (intros t₁ t₂ τ ty1 ty2 ceq;
          assert (⟪ F.empty ⊢ t₂ ≃ t₁ : τ ⟫)
            by (apply F.pctx_equiv_symm; assumption);
          split;
          refine (Hltor _ _ _ _ _ _ _ _ _ _); eassumption).

  intros t₁ t₂ τ τ' vτ' ty₁ ty₂ ceq Cu tCu term.
  destruct (E.Terminating_TermHor term) as [n termN]; clear term.

  assert (⟪ pempty ⊩ t₁ ⟦ dir_gt , S n ⟧ compfi t₁ : embed τ ⟫) as lre₁
      by (change pempty with (embedCtx (repEmulCtx pempty)); 
          eapply compfi_correct;
          cbn; assumption).
  assert (⟪ pempty ⊩ F.app (inject (S (S n)) τ) t₁ ⟦ dir_gt , S n ⟧ compfi t₁ : pEmulDV (S (S n)) precise (compfi_ty τ) ⟫) as lrpe₁
      by (eapply inject_works_open;
          eauto using dwp_precise with arith).

  assert (⟪ ⊩ F.eraseAnnot_pctx (emulate_pctx (S (S n)) Cu) ⟦ dir_gt , S n ⟧ (eraseAnnot_pctx Cu) :
              pempty , pEmulDV (S (S n)) precise (compfi_ty τ) → pempty , pEmulDV (S (S n)) precise τ' ⟫) as lrem₁ by
      (change pempty with (toEmulDV (S (S n)) precise E.empty);
       eapply emulate_pctx_works; eauto using dwp_precise with arith tyvalid).

  pose proof (proj2 (proj2 lrem₁) _ _ lrpe₁) as lrfull₁.

  assert (F.Terminating (F.pctx_app (F.app (inject (S (S n)) τ) t₁)
                                    (F.eraseAnnot_pctx (emulate_pctx (S (S n)) Cu)))) as termF
    by (eapply (adequacy_gt lrfull₁ termN); eauto with arith).

  change (F.app (inject (S (S n)) τ) t₁) with (F.pctx_app t₁ (F.eraseAnnot_pctx (F.a_papp₂ τ (UValFE (S (S n)) (compfi_ty τ)) (injectA (S (S n)) τ) F.a_phole))) in termF.
  rewrite <- F.pctx_cat_app in termF.
  rewrite <- F.eraseAnnot_pctx_cat in termF.

  assert (⟪ ⊢ F.eraseAnnot_pctx (emulate_pctx (S (S n)) Cu) : F.empty, UValFE (S (S n)) (compfi_ty τ) → F.empty, UValFE (S (S n)) τ' ⟫) by
    (change F.empty with (toUVals (S (S n)) E.empty);
        eapply F.eraseAnnot_pctxT, emulate_pctx_T; eauto with tyvalid).

  assert (vε : ValidEnv E.empty) by eauto with tyvalid.
  pose proof (tEmCu := emulate_pctx_T (n := S (S n)) vε vτ' tCu).
  assert (F.Terminating (F.pctx_app t₂ (backtranslateCtx (S (S n)) τ Cu))) as termS'
      by (eapply ceq;
          eauto using F.pctxtyping_cat_annot, injectAT, emulate_pctx_T, F.PCtxTypingAnnot).
  unfold backtranslateCtx in termS'.

  destruct (F.Terminating_TermHor termS') as [m termSm']; clear termS'.

  assert (⟪ pempty ⊩ t₂ ⟦ dir_lt , S m ⟧ compfi t₂ : embed τ ⟫) as lre₂
      by (change pempty with (embedCtx (repEmulCtx pempty)); 
          eapply compfi_correct;
          cbn; assumption).
  assert (⟪ pempty ⊩ F.app (inject (S (S n)) τ) t₂ ⟦ dir_lt , S m ⟧ compfi t₂ : pEmulDV (S (S n)) imprecise (compfi_ty τ) ⟫) as lrpe₂
      by (eapply inject_works_open;
          eauto using dwp_imprecise).

  assert (⟪ ⊩ F.eraseAnnot_pctx (emulate_pctx (S (S n)) Cu) ⟦ dir_lt , S m ⟧ (eraseAnnot_pctx Cu) : 
              pempty , pEmulDV (S (S n)) imprecise (compfi_ty τ) → pempty , pEmulDV (S (S n)) imprecise τ' ⟫) as lrem₂
      by (change pempty with (toEmulDV (S (S n)) imprecise E.empty);
          eapply emulate_pctx_works; eauto using dwp_imprecise).

  pose proof (proj2 (proj2 lrem₂) _ _ lrpe₂) as lrfull₂.
  rewrite F.eraseAnnot_pctx_cat, F.pctx_cat_app in termSm'.

  eapply (adequacy_lt lrfull₂ termSm'); eauto with arith.
Qed.

Definition FullAbstraction (t₁ : F.Tm) (t₂ : F.Tm) (τ : F.Ty) : Prop :=
  ⟪ F.empty ⊢ t₁ : τ ⟫ →
  ⟪ F.empty ⊢ t₂ : τ ⟫ →
  ⟪ F.empty ⊢ t₁ ≃ t₂ : τ ⟫ ↔
  ⟪ E.empty e⊢ compfi t₁ ≃ compfi t₂ : compfi_ty τ ⟫.

Lemma fullAbstraction {t₁ t₂ τ} : FullAbstraction t₁ t₂ τ.
Proof.
  split;
  eauto using equivalenceReflection, equivalencePreservation.
Qed.

(* Print Assumptions fullAbstraction. *)
