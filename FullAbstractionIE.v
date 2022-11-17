Require Import StlcIso.SpecTyping.
Require Import StlcIso.SpecEquivalent.
Require Import StlcIso.LemmasEvaluation.
Require Import StlcIso.LemmasTyping.
Require Import StlcEqui.SpecEquivalent.
Require Import StlcEqui.LemmasEvaluation.

Require Import CompilerIE.Compiler.

Require Import UValIE.UVal.

Require Import LogRelIE.PseudoType.
Require Import LogRelIE.LemmasPseudoType.
Require Import LogRelIE.LR.
Require Import LogRelIE.LemmasLR.

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

Lemma equivalencePreservation {t₁ t₂ τ} :
  ValidTy τ ->
  ⟪ I.empty i⊢ t₁ : τ ⟫ →
  ⟪ I.empty i⊢ t₂ : τ ⟫ →
  ⟪ I.empty i⊢ t₁ ≃ t₂ : τ ⟫ →
  ⟪ E.empty e⊢ compie t₁ ≃ compie t₂ : τ ⟫.
Proof.
  (* sufficient to prove one direction of equi-termination *)
  revert t₁ t₂ τ.
  enough (∀ {t₁ t₂ τ τ'},
             ValidTy τ ->
             ValidTy τ' ->
            ⟪ I.empty i⊢ t₁ : τ ⟫ →
            ⟪ I.empty i⊢ t₂ : τ ⟫ →
            ⟪ I.empty i⊢ t₁ ≃ t₂ : τ ⟫ →
            ∀ {C}, ⟪ ea⊢ C : E.empty , τ → E.empty , τ' ⟫ →
                 E.Terminating (E.pctx_app (compie t₁) (eraseAnnot_pctx C)) → E.Terminating (E.pctx_app (compie t₂) (eraseAnnot_pctx C))) as Hltor.
  { intros t₁ t₂ τ vτ ty1 ty2 ceq.
    assert (⟪ I.empty i⊢ t₂ ≃ t₁ : τ ⟫) as ceq'
            by (apply I.pctx_equiv_symm; assumption).
    split;
      refine (Hltor _ _ _ _ _ _ _ _ _ _ H0); crushValidTy.
  }

  intros t₁ t₂ τ τ' vτ vτ' ty₁ ty₂ ceq Cu tCu term.
  destruct (E.Terminating_TermHor term) as [n termN]; clear term.

  assert (⟪ pempty ⊩ t₁ ⟦ dir_gt , S n ⟧ compie t₁ : embed τ ⟫) as lre₁.
  { change pempty with (embedCtx (repEmulCtx pempty)).
      eapply compie_correct; crushValidTy_with_UVal.
      cbn; eauto using ValidEnv_nil. }

  unshelve epose proof (lrfull₁ := backtranslateCtx_works vτ' vτ (dwp_precise _) tCu lre₁).
  exact (S (S n)).
  eauto.

  unfold backtranslateCtx in lrfull₁.
  rewrite I.eraseAnnot_pctx_cat, I.pctx_cat_app in lrfull₁.

  assert (I.Terminating (I.pctx_app (I.app (inject (S (S n)) τ) t₁)
                                    (I.eraseAnnot_pctx (emulate_pctx (S (S n)) Cu)))) as termI
    by (eapply (adequacy_gt lrfull₁ termN); eauto with arith).

  change (I.app (inject (S (S n)) τ) t₁) with (I.pctx_app t₁ (I.eraseAnnot_pctx (I.ia_papp₂ τ (UValIE (S (S n)) τ) (injectA (S (S n)) τ) I.ia_phole))) in termI.
  rewrite <- I.pctx_cat_app in termI.
  rewrite <- I.eraseAnnot_pctx_cat in termI.

  assert (⟪ i⊢ I.eraseAnnot_pctx (emulate_pctx (S (S n)) Cu) : I.empty, UValIE (S (S n)) τ → I.empty, UValIE (S (S n)) τ' ⟫) by
    (change I.empty with (toUVals (S (S n)) E.empty);
        eapply I.eraseAnnot_pctxT, emulate_pctx_T; eauto with tyvalid).

  assert (vε : ValidEnv E.empty) by eauto with tyvalid.
  assert (vuvalτ : ValidTy (UValIE (S (S n)) τ')) by crushValidTy_with_UVal.
  pose proof (tEmCu := emulate_pctx_T (n := S (S n)) vε vτ' tCu).
  assert (I.Terminating (I.pctx_app t₂ (backtranslateCtx (S (S n)) τ Cu))) as termS'.
  { eapply ceq.
    exact vuvalτ.
    repeat (I.crushTypingMatchIAH + I.crushTypingMatchIAH2);
    crushValidTy_with_UVal; eauto using I.pctxtyping_cat_annot, injectAT, emulate_pctx_T, I.PCtxTypingAnnot.
    assumption.
  }
  unfold backtranslateCtx in termS'.

  destruct (I.Terminating_TermHor termS') as [m termSm']; clear termS'.

  assert (⟪ pempty ⊩ t₂ ⟦ dir_lt , S m ⟧ compie t₂ : embed τ ⟫) as lre₂
      by (change pempty with (embedCtx (repEmulCtx pempty)); 
          eapply compie_correct;
          cbn; assumption).

  epose proof (lrfull₂ := backtranslateCtx_works vτ' vτ dwp_imprecise tCu lre₂).

  eapply (adequacy_lt lrfull₂ termSm'); eauto with arith.
Qed.

Definition FullAbstraction (t₁ : I.Tm) (t₂ : I.Tm) (τ : Ty) : Prop :=
  ⟪ I.empty i⊢ t₁ : τ ⟫ →
  ⟪ I.empty i⊢ t₂ : τ ⟫ →
  ⟪ I.empty i⊢ t₁ ≃ t₂ : τ ⟫ ↔
  ⟪ E.empty e⊢ compie t₁ ≃ compie t₂ : τ ⟫.

Lemma fullAbstraction {t₁ t₂ τ} : FullAbstraction t₁ t₂ τ.
Proof.
  unfold FullAbstraction.
  intros.
  pose proof I.typed_terms_are_valid t₁ τ ValidEnv_nil H as vτ.
  split;
  eauto using equivalenceReflectionEmpty, equivalencePreservation.
Qed.

Print Assumptions fullAbstraction.
