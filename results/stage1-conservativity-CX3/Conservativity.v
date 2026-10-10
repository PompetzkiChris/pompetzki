(* CX3: conservativity for every formula in the pure membership/equality
   language. The conclusion may have free variables. *)
From Stdlib Require Import List Bool Arith.
From Cohen Require Import Syn Prov Kal Val Inv Parse Data Checks Ax Use Expand Pure Elim.
Import ListNotations.

Lemma psub_pure_fixed (f : form) (tau : nat -> option form)
    (rho : nat -> nat) :
  syms f = [] -> psub tau rho f = f.
Proof.
  intros H. apply psub_none. intros p Hp. rewrite H in Hp. contradiction.
Qed.

Theorem elim_all_pure (L : list (nat * nat * form)) (f : form) :
  okb [] L = true -> syms f = [] ->
  prov (GamL L) f -> prov ZFsym f.
Proof.
  induction L as [|d L IH] using rev_ind; intros Ok Hpure D.
  - apply (prov_mono (GamL [])); [|exact D].
    intros g [Z|[d [s [[] _]]]]. exact Z.
  - rewrite okb_app in Ok. apply andb_true_iff in Ok as [Ok1 Ok2].
    simpl in Ok2. destruct d as [[p k] B].
    apply IH; [exact Ok1|exact Hpure|].
    rewrite <- (psub_pure_fixed f (tau1 p B) sid Hpure).
    exact (elim_step L p k B Ok2 f D sid).
Qed.

Theorem gam_zfsym_pure (f : form) :
  syms f = [] -> prov Gam f -> prov ZFsym f.
Proof.
  intros Hpure D. apply (elim_all_pure Dall f okb_Dall Hpure).
  apply (prov_mono Gam); [|exact D].
  intros g [Z|[Sp|[Co|Df]]];
    [left; left; exact Z|left; right; left; exact Sp|
     left; right; right; exact Co|right; exact Df].
Qed.

Theorem zfsym_top_substitution (f : form) (rho : nat -> nat) :
  prov ZFsym f -> prov ZFpure (psub tauTop rho f).
Proof.
  intros D.
  apply (prov_psub_to ZFsym ZFpure tauTop (fun _ => True));
    [auto| |exact D|exact I].
  intros r g _ [[i [Hi ->]]|[[h ->]|[h ->]]].
  - apply p_ax. rewrite psub_none by (rewrite (axf_pure i Hi); simpl; tauto).
    split; [left; exists i; split; [exact Hi|reflexivity]|exact (axf_pure i Hi)].
  - apply p_ax. rewrite SepF_psub. split; [right; left; eexists; reflexivity|].
    unfold SepF, Qf, Kf, Xf. simpl. rewrite syms_ren, psub_top_pure. reflexivity.
  - apply p_ax. rewrite CollF_psub. split; [right; right; eexists; reflexivity|].
    unfold CollF, Kf, Xf. simpl. rewrite syms_ren, psub_top_pure. reflexivity.
Qed.

Theorem zfsym_pure_formula (f : form) :
  syms f = [] -> prov ZFsym f -> prov ZFpure f.
Proof.
  intros Hpure D. rewrite <- (psub_pure_fixed f tauTop sid Hpure).
  apply zfsym_top_substitution. exact D.
Qed.

Theorem gam_pure_conservative (f : form) :
  syms f = [] -> prov Gam f -> prov ZFpure f.
Proof.
  intros Hpure D. apply zfsym_pure_formula; [exact Hpure|].
  apply gam_zfsym_pure; assumption.
Qed.

Theorem pure_gam_inclusion (f : form) : prov ZFpure f -> prov Gam f.
Proof.
  apply prov_mono. intros g [[[Z|[Sp|Co]] Hpure]].
  - left. exact Z.
  - right; left. exact Sp.
  - right; right; left. exact Co.
Qed.

Theorem pure_provability_iff (f : form) :
  syms f = [] -> (prov Gam f <-> prov ZFpure f).
Proof.
  intros Hpure. split; [apply gam_pure_conservative; exact Hpure|apply pure_gam_inclusion].
Qed.

Theorem expanded_theorem_pure (T : list (nat * nat * form)) (f : form) :
  Good T -> syms (expD Pr T f) = [] ->
  prov Gam f -> prov ZFpure (expD Pr T f).
Proof.
  intros G Hpure D. apply gam_pure_conservative; [exact Hpure|].
  apply (p_mp Gam f); [exact D|].
  apply iff_l. apply repl. exact G.
Qed.

Theorem registered_expansion_pure
    (ds : list (nat * nat * form)) (f : form) :
  (forall d, In d ds -> In d Dall) ->
  syms (expD Pr (buildT Pr [] ds) f) = [] ->
  prov Gam f -> prov ZFpure (expD Pr (buildT Pr [] ds) f).
Proof.
  intros Hin Hpure D. apply expanded_theorem_pure; [|exact Hpure|exact D].
  apply buildT_good; [exact Hin|exact good_nil].
Qed.

Corollary all_registered_expansion_pure (f : form) :
  syms (expD Pr (buildT Pr [] Dall) f) = [] ->
  prov Gam f -> prov ZFpure (expD Pr (buildT Pr [] Dall) f).
Proof. apply registered_expansion_pure. auto. Qed.

Print Assumptions psub_pure_fixed.
Print Assumptions elim_all_pure.
Print Assumptions gam_zfsym_pure.
Print Assumptions zfsym_top_substitution.
Print Assumptions zfsym_pure_formula.
Print Assumptions gam_pure_conservative.
Print Assumptions pure_gam_inclusion.
Print Assumptions pure_provability_iff.
Print Assumptions expanded_theorem_pure.
Print Assumptions registered_expansion_pure.
Print Assumptions all_registered_expansion_pure.
