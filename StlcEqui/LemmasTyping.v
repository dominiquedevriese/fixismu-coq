Require Export Db.Spec.
Require Export Db.Lemmas.

Require Export RecTypes.SpecTypes.
Require Export RecTypes.InstTy.
Require Export RecTypes.Contraction.
Require Export RecTypes.ValidTy.
Require Export RecTypes.LemmasTypes.

Require Export StlcEqui.Inst.
Require Export StlcEqui.SpecTyping.

Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.

Ltac crushTypingMatchH :=
  match goal with
    | [ H: ⟪ _ : _ r∈ empty ⟫         |- _ ] =>
      inversion H
    | [ H: ⟪ 0 : _ r∈ _ ⟫         |- _ ] =>
      apply getEvarInvHere in H; repeat subst
    | [ H: ⟪ (S _) : _ r∈ (_ r▻ _) ⟫ |- _ ] =>
      apply getEvarInvThere in H
    (* | H: ⟪ _ e⊢ var _        : _ ⟫ |- _ => inversion H; clear H *)
    (* | H: ⟪ _ e⊢ abs _ _      : _ ⟫ |- _ => destruct (invert_ty_abs H) as (? & ? & ?); clear H *)
    (* | H: ⟪ _ e⊢ app _ _      : _ ⟫ |- _ => inversion H; clear H *)
    (* | H: ⟪ _ e⊢ unit         : _ ⟫ |- _ => inversion H; clear H *)
    (* | H: ⟪ _ e⊢ true         : _ ⟫ |- _ => inversion H; clear H *)
    (* | H: ⟪ _ e⊢ false        : _ ⟫ |- _ => inversion H; clear H *)
    (* | H: ⟪ _ e⊢ ite _ _ _    : _ ⟫ |- _ => inversion H; clear H *)
    (* | H: ⟪ _ e⊢ pair _ _     : _ ⟫ |- _ => inversion H; clear H *)
    (* | H: ⟪ _ e⊢ proj₁ _      : _ ⟫ |- _ => inversion H; clear H *)
    (* | H: ⟪ _ e⊢ proj₂ _      : _ ⟫ |- _ => inversion H; clear H *)
    (* | H: ⟪ _ e⊢ inl _        : _ ⟫ |- _ => inversion H; clear H *)
    (* | H: ⟪ _ e⊢ inr _        : _ ⟫ |- _ => inversion H; clear H *)
    (* | H: ⟪ _ e⊢ caseof _ _ _ : _ ⟫ |- _ => inversion H; clear H *)

    (* | H: ⟪ _ e⊢ seq _ _      : _ ⟫ |- _ => inversion H; clear H *)
    | [ wi : ⟪ ?i : _ r∈ (_ r▻ _) ⟫
        |- context [match ?i with _ => _ end]
      ] => destruct i
    | [ wi : ⟪ ?i : _ r∈ (_ r▻ _) ⟫
        |- context [(_ · _) ?i]
      ] => destruct i
    | [ |- ⟪ _ e⊢ var _ : _ ⟫        ] => econstructor
    | [ |- ⟪ _ e⊢ abs _ _ : _ ⟫      ] => econstructor
    | [ |- ⟪ _ e⊢ app _ _ : _ ⟫      ] => econstructor
    | [ |- ⟪ _ e⊢ unit : _ ⟫         ] => econstructor
    | [ |- ⟪ _ e⊢ true : _ ⟫         ] => econstructor
    | [ |- ⟪ _ e⊢ false : _ ⟫        ] => econstructor
    | [ |- ⟪ _ e⊢ ite _ _ _ : _ ⟫    ] => econstructor
    | [ |- ⟪ _ e⊢ pair _ _ : _ ⟫     ] => econstructor
    | [ |- ⟪ _ e⊢ proj₁ _ : _ ⟫      ] => econstructor
    | [ |- ⟪ _ e⊢ proj₂ _ : _ ⟫      ] => econstructor
    | [ |- ⟪ _ e⊢ inl _ : _ ⟫        ] => econstructor
    | [ |- ⟪ _ e⊢ inr _ : _ ⟫        ] => econstructor
    | [ |- ⟪ _ e⊢ caseof _ _ _ : _ ⟫ ] => econstructor
    | [ |- ⟪ _ e⊢ seq _ _ : _ ⟫      ] => econstructor
    | H : ⟪ _ ≗ ?U ⟫ |- ⟪ _ e⊢ _ : ?U ⟫ => eapply (WtEq _ H)
    | [ |- ⟪ e⊢ phole : _ , _ → _ , _ ⟫             ] => econstructor
    | [ |- ⟪ e⊢ pabs _ _ : _ , _ → _ , _ ⟫          ] => econstructor
    | [ |- ⟪ e⊢ papp₁ _ _ : _ , _ → _ , _ ⟫         ] => econstructor
    | [ |- ⟪ e⊢ papp₂ _ _ : _ , _ → _ , _ ⟫         ] => econstructor
    | [ |- ⟪ e⊢ pite₁ _ _ _ : _ , _ → _ , _ ⟫       ] => econstructor
    | [ |- ⟪ e⊢ pite₂ _ _ _ : _ , _ → _ , _ ⟫       ] => econstructor
    | [ |- ⟪ e⊢ pite₃ _ _ _ : _ , _ → _ , _ ⟫       ] => econstructor
    | [ |- ⟪ e⊢ ppair₁ _ _ : _ , _ → _ , _ ⟫        ] => econstructor
    | [ |- ⟪ e⊢ ppair₂ _ _ : _ , _ → _ , _ ⟫        ] => econstructor
    | [ |- ⟪ e⊢ pproj₁ _ : _ , _ → _ , _ ⟫          ] => econstructor
    | [ |- ⟪ e⊢ pproj₂ _ : _ , _ → _ , _ ⟫          ] => econstructor
    | [ |- ⟪ e⊢ pinl _ : _ , _ → _ , _ ⟫            ] => econstructor
    | [ |- ⟪ e⊢ pinr _ : _ , _ → _ , _ ⟫            ] => econstructor
    | [ |- ⟪ e⊢ pcaseof₁ _ _ _ : _ , _ → _ , _ ⟫    ] => econstructor
    | [ |- ⟪ e⊢ pcaseof₂ _ _ _ : _ , _ → _ , _ ⟫    ] => econstructor
    | [ |- ⟪ e⊢ pcaseof₃ _ _ _ : _ , _ → _ , _ ⟫    ] => econstructor
    | [ |- ⟪ e⊢ pseq₁ _ _ : _ , _ → _ , _ ⟫         ] => econstructor
    | [ |- ⟪ e⊢ pseq₂ _ _ : _ , _ → _ , _ ⟫         ] => econstructor
    |  H : ⟪ _ ≗ ?U ⟫ |- ⟪ e⊢ _ : _ , _ → _ , ?U ⟫    => eapply (WtPEq H)
  end.

Local Ltac crush :=
  intros; cbn in * |-;
  repeat
    (cbn;
     repeat crushStlcSyntaxMatchH;
     repeat crushDbSyntaxMatchH;
     repeat crushTypingMatchH);
  try discriminate;
  eauto with ws.

Lemma getEvar_wsIx Γ i T :
  ⟪ i : T r∈ Γ ⟫ → dom Γ ∋ i.
Proof. induction 1; crush. Qed.
#[export]
Hint Resolve getEvar_wsIx : ws.

(* Lemma wsIx_getEvar {Γ i} (wi: dom Γ ∋ i) : *)
(*   ∀ (P: Prop), (∀ T, ⟪ i : T ∈ Γ ⟫ → P) → P. *)
(* Proof. *)
(*   depind wi; destruct Γ; crush. *)
(*   - eapply (IHwi _ x); crush. *)
(* Qed. *)

(* Lemma wtRen_wsRen Γ₁ Γ₂ ξ : *)
(*   WtRen Γ₁ Γ₂ ξ → WsRen (dom Γ₁) (dom Γ₂) ξ. *)
(* Proof. *)
(*   unfold WtRen, WsRen; intros. *)
(*   apply (wsIx_getEvar H0); crush. *)
(* Qed. *)

(* Lemma typing_wt {Γ t T} (wt: ⟪ Γ ⊢ t : T ⟫) : *)
(*   wsTm (dom Γ) t. *)
(* Proof. induction wt; crush. Qed. *)

(* Lemma wtSub_wsSub Γ₁ Γ₂ ζ : *)
(*   WtSub Γ₁ Γ₂ ζ → WsSub (dom Γ₁) (dom Γ₂) ζ. *)
(* Proof. *)
(*   unfold WtSub, WsSub; intros. *)
(*   apply (wsIx_getEvar H0); crush. *)
(*   eauto using typing_wt. *)
(* Qed. *)

(*************************************************************************)

Lemma wtRen_closed ξ Δ : WtRen empty Δ ξ.
Proof. unfold WtRen; intros. inversion H. Qed.
#[export]
Hint Resolve wtRen_closed : ws.

Lemma wtRen_idm (Γ: Env) : WtRen Γ Γ (idm Ix).
Proof. unfold WtRen, idm; auto. Qed.
#[export]
Hint Resolve wtRen_idm : ws.

Lemma wtRen_comp {Γ₁ Γ₂ Γ₃ ξ₁ ξ₂} :
  WtRen Γ₁ Γ₂ ξ₁ → WtRen Γ₂ Γ₃ ξ₂ → WtRen Γ₁ Γ₃ (ξ₁ >-> ξ₂).
Proof. unfold WtRen, comp; simpl; auto. Qed.
#[export]
Hint Resolve wtRen_comp : ws.

(*************************************************************************)

Definition WtRenNatural (Γ₁ Γ₂: Env) (ξ₁ ξ₂: Sub Ix) : Prop :=
  ∀ i T, ⟪ (ξ₁ i) : T r∈ Γ₁ ⟫ → ⟪ (ξ₂ i) : T r∈ Γ₂ ⟫.

Lemma wtRen_natural
  {f₁ f₂: Env → Env} {ξ₁ ξ₂: Sub Ix}
  (hyp: ∀ Γ, WtRenNatural (f₁ Γ) (f₂ Γ) ξ₁ ξ₂) :
  ∀ Γ₁ Γ₂ ξ,
    WtRen Γ₁ (f₁ Γ₂) (ξ >-> ξ₁) →
    WtRen Γ₁ (f₂ Γ₂) (ξ >-> ξ₂).
Proof. unfold WtRenNatural, WtRen in *; eauto. Qed.

(*************************************************************************)

Lemma wtRen_wkms (Δ: Env) :
  ∀ Γ, WtRen Γ (Γ r▻▻ Δ) (wkms (dom Δ)).
Proof. unfold WtRen. induction Δ; crush. Qed.
#[export]
Hint Resolve wtRen_wkms : ws.

Lemma wtiIx_wkms (Δ: Env) :
  ∀ (Γ: Env) (i: Ix) T,
    ⟪ (wkms (dom Δ) i) : T r∈ (Γ r▻▻ Δ) ⟫ → ⟪ i : T r∈ Γ ⟫.
Proof. induction Δ; eauto with wsi. Qed.
#[export]
Hint Resolve wtiIx_wkms : wsi.

Lemma wtRen_wkm Γ T :
  WtRen Γ (Γ r▻ T) wkm.
Proof. apply (wtRen_wkms (empty r▻ T)). Qed.
#[export]
Hint Resolve wtRen_wkm : ws.

Lemma wtiIx_wkm Γ i T :
  ⟪ (wkm i) : T r∈ (Γ r▻ T) ⟫ → ⟪ i : T r∈ Γ ⟫.
Proof. apply (wtiIx_wkms (empty r▻ T)). Qed.
#[export]
Hint Resolve wtiIx_wkm : wsi.

Lemma wtRenNatural_wkms_id Δ :
  ∀ Γ, WtRenNatural (Γ r▻▻ Δ) Γ (wkms (dom Δ)) (idm Ix).
Proof. unfold WtRenNatural; eauto using wtiIx_wkms. Qed.
#[export]
Hint Resolve wtRenNatural_wkms_id : wsi.

Lemma wtiRen_comp_wkms Δ :
  ∀ Γ₁ Γ₂ ξ,
    WtRen Γ₁ (Γ₂ r▻▻ Δ) (ξ >-> wkms (dom Δ)) →
    WtRen Γ₁ Γ₂        ξ.
Proof. apply (wtRen_natural (wtRenNatural_wkms_id Δ)). Qed.
#[export]
Hint Resolve wtiRen_comp_wkms : wsi.

Lemma wtRen_snoc Γ₁ Γ₂ ξ x T :
  WtRen Γ₁ Γ₂ ξ → ⟪ x : T r∈ Γ₂ ⟫ → WtRen (Γ₁ r▻ T) Γ₂ (ξ · x).
Proof. unfold WtRen. crush. Qed.
#[export]
Hint Resolve wtRen_snoc : ws.

Lemma wtiRen_snoc Γ₁ Γ₂ T ξ x :
  WtRen (Γ₁ r▻ T) Γ₂ (ξ · x) → WtRen Γ₁ Γ₂ ξ.
Proof.
  intros wξ i. specialize (wξ (S i)). eauto using GetEvar.
Qed.
#[export]
Hint Resolve wtiRen_snoc : wsi.

Lemma wtiIx_snoc Γ₁ Γ₂ ξ T x :
  WtRen (Γ₁ r▻ T) Γ₂ (ξ · x) → ⟪ x : T r∈ Γ₂ ⟫.
Proof.
  intros wξ. specialize (wξ 0). eauto using GetEvar.
Qed.
#[export]
Hint Resolve wtiIx_snoc : wsi.

Lemma wtRen_up {Γ₁ Γ₂ ξ} (wξ: WtRen Γ₁ Γ₂ ξ) :
  ∀ T, WtRen (Γ₁ r▻ T) (Γ₂ r▻ T) (ξ ↑).
Proof. unfold up; crush. Qed.
#[export]
Hint Resolve wtRen_up : ws.

Lemma wtiRen_up Γ₁ Γ₂ ξ T :
  WtRen (Γ₁ r▻ T) (Γ₂ r▻ T) (ξ ↑) → WtRen Γ₁ Γ₂ ξ.
Proof.
  unfold up, WtRen. crush.
  specialize (H (S i) T0). eauto with ws wsi.
Qed.
#[export]
Hint Resolve wtiRen_up : wsi.

Lemma wtRen_ups Γ₁ Γ₂ Δ ξ :
  WtRen Γ₁ Γ₂ ξ → WtRen (Γ₁ r▻▻ Δ) (Γ₂ r▻▻ Δ) (ξ ↑⋆ dom Δ).
Proof. induction Δ; crush. Qed.
#[export]
Hint Resolve wtRen_ups : ws.

Lemma wtiRen_ups Γ₁ Γ₂ Δ ξ :
  WtRen (Γ₁ r▻▻ Δ) (Γ₂ r▻▻ Δ) (ξ ↑⋆ dom Δ) → WtRen Γ₁ Γ₂ ξ.
Proof. induction Δ; eauto with wsi. Qed.
#[export]
Hint Resolve wtiRen_ups : wsi.

Lemma wtRen_beta (Γ Δ: Env) :
  ∀ ξ, WtRen Δ Γ ξ → WtRen (Γ r▻▻ Δ) Γ (beta (dom Δ) ξ).
Proof. unfold WtRen; induction Δ; crush. Qed.
#[export]
Hint Resolve wtRen_beta : ws.

Lemma typing_ren {Γ₁ t T} (wt: ⟪ Γ₁ e⊢ t : T ⟫) :
  ∀ Γ₂ ξ, WtRen Γ₁ Γ₂ ξ → ⟪ Γ₂ e⊢ t[ξ] : T ⟫.
Proof. induction wt; econstructor; crush. Qed.
#[export]
Hint Resolve typing_ren : ws.

(* Lemma typing_weakening Δ {Γ t T} (wt: ⟪ Γ ⊢ t : T ⟫) : *)
(*   ⟪ Γ ▻▻ Δ ⊢ t[@wkms Ix _ _ (dom Δ)] : T ⟫. *)
(* Proof. apply (typing_ren wt), wtRen_wkms. Qed. *)

(* Lemma typing_weakening1 T' {Γ t T} (wt: ⟪ Γ ⊢ t : T ⟫) : *)
(*   ⟪ Γ ▻ T' ⊢ t[@wkm Ix _ _] : T ⟫. *)
(* Proof. apply (typing_weakening (empty ▻ T') wt). Qed. *)

(*************************************************************************)

Lemma wtSub_closed ζ Δ : WtSub empty Δ ζ.
Proof. inversion 1. Qed.
#[export]
Hint Resolve wtSub_closed : ws.

Lemma wtSub_idm (Γ: Env) : WtSub Γ Γ (idm Tm).
Proof. unfold WtSub. crush. Qed.
#[export]
Hint Resolve wtSub_idm : ws.

Lemma wtSub_snoc Γ₁ Γ₂ ζ t T :
  WtSub Γ₁ Γ₂ ζ → ⟪ Γ₂ e⊢ t : T ⟫ → WtSub (Γ₁ r▻ T) Γ₂ (ζ · t).
Proof. unfold WtSub. crush. Qed.
#[export]
Hint Resolve wtSub_snoc : ws.

Lemma wtiSub_snoc Γ₁ Γ₂ T ζ t :
  WtSub (Γ₁ r▻ T) Γ₂ (ζ · t) → WtSub Γ₁ Γ₂ ζ.
Proof.
  intros wζ i. specialize (wζ (S i)). eauto using GetEvar.
Qed.
#[export]
Hint Resolve wtiSub_snoc : wsi.

Lemma wtSub_toSub ξ Γ₁ Γ₂ :
  WtRen Γ₁ Γ₂ ξ → WtSub Γ₁ Γ₂ ⌈ξ⌉.
Proof. unfold WtRen, WtSub; eauto using WtVar. Qed.

Lemma wtSub_wkms (Δ: Env) :
  ∀ Γ, WtSub Γ (Γ r▻▻ Δ) ⌈@wkms Ix _ _ (dom Δ)⌉.
Proof. eauto using wtRen_wkms, wtSub_toSub. Qed.

#[export]
Hint Resolve wtSub_wkms : ws.

Lemma wtSub_wkm Γ T :
  WtSub Γ (Γ r▻ T) ⌈wkm⌉.
Proof. apply (wtSub_wkms (empty r▻ T)). Qed.
#[export]
Hint Resolve wtSub_wkm : ws.

Lemma wtSub_up {Γ₁ Γ₂ ζ} (wζ: WtSub Γ₁ Γ₂ ζ) :
  ∀ T, WtSub (Γ₁ r▻ T) (Γ₂ r▻ T) (ζ ↑).
Proof. inversion 1; crush. Qed.
#[export]
Hint Resolve wtSub_up : ws.

Lemma wtSub_ups Γ₁ Γ₂ Δ ζ :
  WtSub Γ₁ Γ₂ ζ → WtSub (Γ₁ r▻▻ Δ) (Γ₂ r▻▻ Δ) (ζ ↑⋆ dom Δ).
Proof. induction Δ; crush. Qed.
#[export]
Hint Resolve wtSub_ups : ws.

Lemma typing_sub {Γ₁ t T} (wt: ⟪ Γ₁ e⊢ t : T ⟫) :
  ∀ {Γ₂ ζ}, WtSub Γ₁ Γ₂ ζ → ⟪ Γ₂ e⊢ t[ζ] : T ⟫.
Proof. induction wt; crush. Qed.
#[export]
Hint Resolve typing_sub : ws.

Lemma wtSub_comp {Γ₁ Γ₂ Γ₃ ζ₁ ζ₂} :
  WtSub Γ₁ Γ₂ ζ₁ → WtSub Γ₂ Γ₃ ζ₂ → WtSub Γ₁ Γ₃ (ζ₁ >=> ζ₂).
Proof. unfold WtSub, comp; eauto with ws. Qed.
#[export]
Hint Resolve wtSub_comp : ws.

Lemma wtTm_snoc Γ₁ Γ₂ ζ T t :
  WtSub (Γ₁ r▻ T) Γ₂ (ζ · t) → ⟪ Γ₂ e⊢ t : T ⟫.
Proof.
  intros wζ. specialize (wζ 0). eauto using GetEvar.
Qed.
#[export]
Hint Immediate wtTm_snoc : ws.

(*************************************************************************)

Lemma wtSub_beta (Γ Δ: Env) :
  ∀ ζ, WtSub Δ Γ ζ → WtSub (Γ r▻▻ Δ) Γ (beta (dom Δ) ζ).
Proof.
  unfold WtSub; induction Δ; crush.
Qed.
#[export]
Hint Resolve wtSub_beta : ws.

Lemma wtSub_beta1 Γ t T (wi: ⟪ Γ e⊢ t : T ⟫) :
  WtSub (Γ r▻ T) Γ (beta1 t).
Proof. apply (wtSub_beta Γ (empty r▻ T)); crush. Qed.
#[export]
Hint Resolve wtSub_beta1 : ws.

(*************************************************************************)

(* Lemma typing_beta {Γ Δ t T ζ} : *)
(*   WtSub Δ Γ ζ → ⟪ (Γ ▻▻ Δ) ⊢ t : T ⟫ → ⟪ Γ ⊢ t[beta (dom Δ) ζ] : T ⟫. *)
(* Proof. intros; eapply typing_sub; eauto with ws. Qed. *)

(* Lemma typing_beta1 {Γ t T t' T'} : *)
(*   ⟪ Γ ⊢ t' : T' ⟫ → ⟪ Γ ▻ T' ⊢ t : T ⟫ → ⟪ Γ ⊢ t[beta1 t'] : T ⟫. *)
(* Proof. intros; eapply typing_sub; eauto with ws. Qed. *)

(*************************************************************************)

Ltac crushTypingMatchH2 :=
  match goal with
    | [ |- ⟪ _ e⊢ @ap Tm Ix vrIx _ ?ξ ?t : _ ⟫
      ] => eapply typing_ren
    | [ |- ⟪ _ e⊢ @ap Tm Tm vrTm _ ?ζ ?t : _ ⟫
      ] => eapply typing_sub
    | [ |- WtSub (_ r▻ _) _ (beta _ _)
      ] => eapply wtSub_beta
    | [ |- WtSub (_ r▻ _) _ (beta1 _)
      ] => eapply wtSub_beta1
  end.

Ltac crushTypingTemp :=
  intros; cbn in * |-;
  repeat
    (cbn;
     repeat crushStlcSyntaxMatchH;
     repeat crushDbSyntaxMatchH;
     repeat crushDbLemmasMatchH;
     repeat crushTypingMatchH;
     repeat crushTypingMatchH2;
     eauto with ws
    ).

#[export]
Hint Resolve pctxtyping_cat : typing.
#[export]
Hint Resolve pctxtyping_app : typing.

Lemma wtvar_implies_wsvar {Γ i τ} :
  ⟪ i : τ r∈ Γ ⟫ → dom Γ ∋ i.
Proof.
  induction 1; eauto with ws.
Qed.

Lemma wt_implies_ws {Γ t τ} :
  ⟪ Γ e⊢ t : τ ⟫ → ⟨ dom Γ ⊢ t ⟩.
Proof.
  induction 1; try constructor;
  eauto using wtvar_implies_wsvar with ws.
Qed.

(* (* We want a simple way of proving that types are closed under reasonable circumstances (closed environments, etc.). *)

(*  This proof should be nasty and require us to insert various changes into the basic structures (i.e. the abs term constructor will require proof that the argument type is closed), so we admit for now as it is obviously valid (with the appropriate changes to terms and environments) and tangential to the rest of the proof. *) *)
Lemma typed_terms_are_valid {Γ} (t : Tm) (T : Ty) :
  ValidEnv Γ →
  ⟪ Γ e⊢ t : T ⟫ →
  ValidTy T.
Proof.
  intros cenv wt.
  induction wt; eauto with wt tyvalid.
  - specialize (IHwt1 cenv).
    now eapply ValidTy_invert_arr in IHwt1.
  - specialize (IHwt cenv).
    now eapply ValidTy_invert_prod in IHwt.
  - specialize (IHwt cenv).
    now eapply ValidTy_invert_prod in IHwt.
Qed.

Ltac try_typed_terms_are_valid :=
  match goal with
  | [ H: ⟪ _ e⊢ _ : ?τ ⟫ |- ValidTy ?τ ] => refine (typed_terms_are_valid _ _ _ H)
  end.

#[export]
Hint Extern 50 (ValidTy _) => try_typed_terms_are_valid : tyvalid_terms.

Lemma invert_ty_abs {Γ τ₁ t τ} :
  ValidEnv Γ ->
  ⟪ Γ e⊢ abs τ₁ t : τ ⟫ ->
  exists τ₂, ValidTy τ₁ /\ ValidTy τ /\
          ⟪ tarr τ₁ τ₂ ≗ τ ⟫ /\
          ⟪ Γ r▻ τ₁ e⊢ t : τ₂ ⟫.
Proof.
  intros vΓ wt.
  depind wt.
  - exists τ₂.
    split; [|split; [|split]]; eauto using typed_terms_are_valid with tyeq tyvalid.
  - destruct (IHwt _ _ vΓ eq_refl) as (τ₂ & vτ₁ & vT & eq₁ & wtb).
    exists τ₂; split; [|split; [|split]]; try assumption.
    unshelve eapply (eq_trans_contr _ eq₁);
      eauto with simple_contr_rec.
Qed.

Lemma invert_ty_proj₁ {Γ t τ} :
  ValidEnv Γ ->
  ⟪ Γ e⊢ proj₁ t : τ ⟫ ->
  exists τ₂, ⟪ Γ e⊢ t : τ r× τ₂ ⟫.
Proof.
  intros vΓ wt.
  depind wt.
  - now exists τ₂.
  - destruct (IHwt _ vΓ eq_refl) as (τ₂ & wtb).
    assert (vτ := typed_terms_are_valid _ _ vΓ wtb).
    destruct (ValidTy_invert_prod vτ) as (? & ?).
    exists τ₂. unshelve eapply (WtEq _ _ _ _ wtb); eauto with tyeq tyvalid.
Qed.

Lemma invert_ty_proj₂ {Γ t τ} :
  ValidEnv Γ ->
  ⟪ Γ e⊢ proj₂ t : τ ⟫ ->
  exists τ₁, ⟪ Γ e⊢ t : τ₁ r× τ ⟫.
Proof.
  intros vΓ wt.
  depind wt.
  - now exists τ₁.
  - destruct (IHwt _ vΓ eq_refl) as (τ₁ & wtb).
    assert (vτ := typed_terms_are_valid _ _ vΓ wtb).
    destruct (ValidTy_invert_prod vτ) as (? & ?).
    exists τ₁. unshelve eapply (WtEq _ _ _ _ wtb); eauto with tyeq tyvalid.
Qed.

Lemma invert_ty_pair {Γ t₁ t₂ τ} :
  ValidEnv Γ ->
  ⟪ Γ e⊢ pair t₁ t₂ : τ ⟫ ->
  exists τ₁ τ₂, ValidTy τ /\ ⟪ Γ e⊢ t₁ : τ₁ ⟫ /\ ⟪ Γ e⊢ t₂ : τ₂ ⟫ /\ ⟪ τ₁ r× τ₂ ≗ τ ⟫.
Proof.
  intros vΓ wt.
  depind wt.
  - exists τ₁. exists τ₂.
    assert (vτ₁ := typed_terms_are_valid _ _ vΓ wt1).
    assert (vτ₂ := typed_terms_are_valid _ _ vΓ wt2).
    eauto with tyeq simple_contr_rec tyvalid.
  - destruct (IHwt _ _ vΓ eq_refl) as (τ₁ & τ₂ & vτ & wt₁ & wt₂ & eq).
    exists τ₁. exists τ₂.
    split; [|split; [|split]]; try assumption.
    unshelve eapply (eq_trans_contr _ _ H); eauto with simple_contr_rec.
Qed.

Lemma invert_ty_app {Γ t₁ t₂ τ} :
  ValidEnv Γ ->
  ⟪ Γ e⊢ app t₁ t₂ : τ ⟫ ->
  exists τ₁, ⟪ Γ e⊢ t₁ : τ₁ r⇒ τ ⟫ /\ ⟪ Γ e⊢ t₂ : τ₁ ⟫.
Proof.
  intros vΓ wt.
  depind wt.
  - exists τ₁. assert (vτ₁ := typed_terms_are_valid _ _ vΓ wt1).
    now eapply ValidTy_invert_arr in vτ₁.
  - destruct (IHwt _ _ vΓ eq_refl) as (τ₁' & wt₁ & wt₂).
    assert (vτ₁ := typed_terms_are_valid _ _ vΓ wt₁).
    destruct (ValidTy_invert_arr vτ₁).
    exists τ₁'; split; [|assumption].
    unshelve eapply (WtEq _ _ _ _ wt₁); eauto with tyeq tyvalid.
Qed.

Lemma invert_ty_caseof {Γ t₁ t₂ t₃ τ} :
  ⟪ Γ e⊢ caseof t₁ t₂ t₃ : τ ⟫ ->
  exists τ₁ τ₂, ⟪ Γ e⊢ t₁ : τ₁ r⊎ τ₂ ⟫ /\ ⟪ Γ r▻ τ₁ e⊢ t₂ : τ ⟫ /\ ⟪ Γ r▻ τ₂ e⊢ t₃ : τ ⟫.
Proof.
  intros wt.
  depind wt.
  - exists τ₁. exists τ₂. eauto.
  - destruct (IHwt _ _ _ eq_refl) as (τ₁ & τ₂ & wt₁ & wt₂ & wt₃).
    exists τ₁. exists τ₂.
    split; [|split]; crushTypingTemp.
Qed.

Lemma invert_ty_inl {Γ t τ} :
  ValidEnv Γ ->
  ⟪ Γ e⊢ inl t : τ ⟫ ->
  exists τ₁ τ₂, ValidTy τ /\ ValidTy τ₂ /\ ⟪ Γ e⊢ t : τ₁ ⟫ /\ ⟪ τ₁ r⊎ τ₂ ≗ τ ⟫.
Proof.
  intros vΓ wt.
  depind wt.
  - exists τ₁. exists τ₂.
    assert (vτ₁ := typed_terms_are_valid _ _ vΓ wt).
    eauto with tyeq simple_contr_rec tyvalid.
  - destruct (IHwt _ vΓ eq_refl) as (τ₁ & τ₂ & vτ & vτ₂ & wt₁ & eq).
    exists τ₁. exists τ₂.
    split; [|split; [|split]]; try assumption.
    unshelve eapply (eq_trans_contr _ _ H); eauto with simple_contr_rec.
Qed.

Lemma invert_ty_inr {Γ t τ} :
  ValidEnv Γ ->
  ⟪ Γ e⊢ inr t : τ ⟫ ->
  exists τ₁ τ₂, ValidTy τ /\ ValidTy τ₁ /\ ⟪ Γ e⊢ t : τ₂ ⟫ /\ ⟪ τ₁ r⊎ τ₂ ≗ τ ⟫.
Proof.
  intros vΓ wt.
  depind wt.
  - exists τ₁. exists τ₂.
    assert (vτ₁ := typed_terms_are_valid _ _ vΓ wt).
    eauto with tyeq simple_contr_rec tyvalid.
  - destruct (IHwt _ vΓ eq_refl) as (τ₁ & τ₂ & vτ & vτ₂ & wt₁ & eq).
    exists τ₁. exists τ₂.
    split; [|split; [|split]]; try assumption.
    unshelve eapply (eq_trans_contr _ _ H); eauto with simple_contr_rec.
Qed.

Lemma invert_ty_ite {Γ t₁ t₂ t₃ τ} :
  ⟪ Γ e⊢ ite t₁ t₂ t₃ : τ ⟫ ->
  ⟪ Γ e⊢ t₁ : tbool ⟫ /\ ⟪ Γ e⊢ t₂ : τ ⟫ /\ ⟪ Γ e⊢ t₃ : τ ⟫.
Proof.
  intros wt.
  depind wt.
  - eauto.
  - destruct (IHwt _ _ _ eq_refl) as (wt₁ & wt₂ & wt₃).
    split; [|split]; crushTypingTemp.
Qed.

Lemma invert_ty_seq {Γ t₁ t₂ τ} :
  ⟪ Γ e⊢ seq t₁ t₂ : τ ⟫ ->
  ⟪ Γ e⊢ t₁ : tunit ⟫ /\ ⟪ Γ e⊢ t₂ : τ ⟫.
Proof.
  intros wt.
  depind wt.
  - eauto.
  - destruct (IHwt _ _ eq_refl) as (wt₁ & wt₂).
    split; crushTypingTemp.
Qed.

Ltac crushTypingMatchHInv :=
  match goal with
    (* | H: ⟪ _ e⊢ var _        : _ ⟫ |- _ => inversion H; clear H *)
    | H2: ValidEnv ?Γ, H: ⟪ _ e⊢ abs _ _      : _ ⟫ |- _ => destruct (invert_ty_abs H2 H) as (? & ? & ? & ? & ?); clear H
    | H2: ValidEnv ?Γ, H: ⟪ ?Γ e⊢ app _ _      : _ ⟫ |- _ => destruct (invert_ty_app H2 H) as (? & ? & ?); clear H
    (* | H: ⟪ _ e⊢ unit         : _ ⟫ |- _ => inversion H; clear H *)
    (* | H: ⟪ _ e⊢ true         : _ ⟫ |- _ => inversion H; clear H *)
    (* | H: ⟪ _ e⊢ false        : _ ⟫ |- _ => inversion H; clear H *)
    | H: ⟪ _ e⊢ ite _ _ _    : _ ⟫ |- _ => destruct (invert_ty_ite H) as (? & ? & ?); clear H
    | H2: ValidEnv ?Γ, H: ⟪ _ e⊢ proj₁ _      : _ ⟫ |- _ => destruct (invert_ty_proj₁ H2 H) as (? & ?); clear H
    | H2: ValidEnv ?Γ, H: ⟪ _ e⊢ proj₂ _      : _ ⟫ |- _ => destruct (invert_ty_proj₂ H2 H) as (? & ?); clear H
    | H2: ValidEnv ?Γ, H: ⟪ _ e⊢ pair _ _      : _ ⟫ |- _ => destruct (invert_ty_pair H2 H) as (? & ? & ? & ? & ?); clear H
    | H2: ValidEnv ?Γ, H: ⟪ _ e⊢ inl _        : _ ⟫ |- _ => destruct (invert_ty_inl H2 H) as (? & ? & ? & ? & ? & ?); clear H
    | H2: ValidEnv ?Γ, H: ⟪ _ e⊢ inr _        : _ ⟫ |- _ => destruct (invert_ty_inr H2 H) as (? & ? & ? & ? & ? & ?); clear H
    | H: ⟪ _ e⊢ caseof _ _ _ : _ ⟫ |- _ => destruct (invert_ty_caseof H) as (? & ? & ? & ? & ?); clear H
    | H: ⟪ _ e⊢ seq _ _      : _ ⟫ |- _ => destruct (invert_ty_seq H) as (? & ?); clear H
  end.

Ltac crushTyping :=
  intros; cbn in * |-;
  repeat
    (cbn;
     repeat crushStlcSyntaxMatchH;
     repeat crushDbSyntaxMatchH;
     repeat crushDbLemmasMatchH;
     repeat crushTypingMatchH;
     repeat crushTypingMatchHInv;
     repeat crushTypeEqualitiesMatchH;
     repeat crushTypingMatchH2
    );
  eauto with ws tyvalid tyeq.

#[export]
Hint Extern 20 (⟪ _ e⊢ _ : _ ⟫) =>
  crushTyping : typing.

#[export]
Hint Extern 20 (⟪ e⊢ _ : _ , _ → _ , _ ⟫) =>
  crushTyping : typing.

