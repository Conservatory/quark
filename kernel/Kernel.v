(*
   Quark is Copyright (C) 2012-2015, Quark Team.

   You can redistribute and modify it under the terms of the GNU GPL,
   version 2 or later, but it is made available WITHOUT ANY WARRANTY.

   For more information about Quark, see our web site at:
   http://goto.ucsd.edu/quark/
*)

Require Import Ynot.
Require Import Basis.
Require Import List.
Require Import Ascii.
Require Import String.
Require Import List.
Require Import RSep.
Require Import NArith.
Require Import Arith.

Require Import VCRBase.
Require Import VCRIO.
Require Import Message.
Require Import Sumbool.

Open Local Scope stsepi_scope.
Open Local Scope hprop_scope.


(* kernel spec *)

(* returns tabs created by MKTab event *)
(* DON:Q: we will use Kill actions later *)
Fixpoint cur_tabs (trace: Trace) : list tab :=
  match trace with
  | MkTab t :: tr =>
      cur_tabs tr ++ t :: nil
  | a :: tr =>
      cur_tabs tr
  | nil =>
      nil
  end.


Fixpoint cur_cprocs (trace: Trace) : list cproc :=
  match trace with
  | MkCProc c :: tr =>
    c :: cur_cprocs tr
  | a :: tr =>
      cur_cprocs tr
  | nil =>
      nil
  end.


Fixpoint cur_cproc (domain:list ascii) (trace: Trace) : option cproc :=
  match trace with
  | MkCProc c :: tr => 
    if laeq (cproc_domain c) domain 
      then (Some c)
      else  cur_cproc domain tr
  | a :: tr =>
      cur_cproc domain tr
  | nil => None    
  end.


Lemma cur_cproc_domain : 
  forall tr domain c, 
    cur_cproc domain tr = Some c ->
    (cproc_domain c) = domain.
Proof.
  induction tr.
  intros. simpl in H. discriminate.

  intros.
  destruct a; simpl in H; auto.

  destruct (laeq (cproc_domain c0) domain).
  inv H. reflexivity.

  apply IHtr. auto.
Qed.


Lemma cur_cproc_in_cur_cprocs:
  forall domain tr ts c,
  cur_cprocs tr = ts ->
  cur_cproc domain tr = Some c ->
  In c ts.
Proof.
(*  induction tr; simpl; intros. discriminate. *)
  induction tr.
  simpl. intros. discriminate.

  intros.
  destruct a; auto.

  simpl in H0.
  destruct (laeq (cproc_domain c0) domain).
  rewrite<- H.
  inversion H0.
  rewrite<- H2.

  simpl. left. auto.

  assert (cproc_domain c = domain).
  eapply cur_cproc_domain. apply H0.

  simpl in H. rewrite<- H.
  simpl. right. 
  apply IHtr. auto.

  auto.
Qed.  


Lemma cur_cproc_in_cur_cprocs':
  forall domain tr c,
  cur_cproc domain tr = Some c ->
  In c (cur_cprocs tr).
Proof.
(*  induction tr; simpl; intros. discriminate. *)
  induction tr.
  simpl. intros. discriminate.

  intros.
  destruct a; auto.

  simpl in H.
  destruct (laeq (cproc_domain c0) domain).
  inversion H.
  rewrite<- H1.

  simpl. left. auto.

  assert (cproc_domain c = domain).
  eapply cur_cproc_domain. apply H.

  simpl. right. 
  apply IHtr. auto.
Qed.  


Fixpoint cur_tab (trace: Trace) : option tab :=
  match trace with
  | MkTab t :: tr =>
      Some t
  | ReadFile f c :: tr =>
    if file_desc_eq f stdin then
      match select_tab_idx c with
        | Some i =>
          match nth_error (cur_tabs tr) i with
            | Some t => Some t
            | None   => cur_tab tr
          end
        | None => cur_tab tr
      end
    else
      cur_tab tr
  | a :: tr =>
      cur_tab tr
  | nil =>
      None
  end.


Lemma cur_tab_in_cur_tabs:
  forall tr ts t,
  cur_tabs tr = ts ->
  cur_tab tr = Some t ->
  In t ts.
Proof.
  induction tr; simpl; intros. discriminate.
  destruct a; auto.
  destruct (file_desc_eq f stdin); auto.
  destruct (select_tab_idx a); auto. subst.
  case_eq (nth_error (cur_tabs tr) n); intros.
  rewrite H in H0. inv H0.
  eapply nth_error_some_in; eauto.
  rewrite H in H0. auto.
  inv H0. apply in_or_app. right; left; auto.
Qed.


Lemma cur_tabs_not_nil_cur_tab:
  forall tr,
  cur_tabs tr <> nil ->
  cur_tab tr <> None.
Proof.
  induction tr; simpl; intros. auto.
  destruct a; auto.
  destruct (file_desc_eq f stdin); auto.
  destruct (select_tab_idx a); auto.
  destruct (nth_error (cur_tabs tr) n); auto.
  discriminate.
  discriminate.
Qed.


Inductive user_cmd : Set :=
  | UAddTab    : user_cmd
  | UMouseClick : forall (t:tab), user_cmd
  | USwitchTab : forall (t: tab), user_cmd 
  | UEndorseYes: user_cmd
  | UEndorseNo : user_cmd
  | UKeyPress  : forall (t: tab) (k: ascii), user_cmd
  | UIgnore    : user_cmd.

Definition classify_user_cmd (k: ascii) (tr: Trace) : user_cmd :=
   if ascii_dec k "017"%char then
      UAddTab
   else if ascii_dec k "018"%char then
      match cur_tab tr with
      | Some t => UMouseClick t
      | None   => UIgnore
      end  
   else
      match select_tab_idx k with
      | Some i =>
        match nth_error (cur_tabs tr) i with
        | Some t => USwitchTab t
        | None   => UIgnore
        end
      | None =>
        match cur_tab tr with
        | Some t => UKeyPress t k
        | None   => UIgnore
        end
      end.

Fixpoint get_host (x : list ascii) : list ascii :=
match x with
| nil => nil
| ":"%char :: _ => nil
| a :: t => a :: get_host t
end.


Fixpoint lkup_tab (tabs: list tab) (ic: ichan) : option tab :=
  match tabs with
  | t::ts =>
      if iceq (t2k t) ic then
        Some t
      else
        lkup_tab ts ic
  | nil =>
      None
  end.


Lemma lkup_tab_in:
  forall ts ic t,
  lkup_tab ts ic = Some t ->
  In t ts.
Proof.
  induction ts; simpl; intros. discriminate.
  destruct (iceq (t2k a) ic).
    inv H. left; auto.
    right. eapply IHts; eauto.
Qed.


Lemma lkup_tab_nin:
  forall ts t,
  lkup_tab ts (t2k t) = None ->
  ~ In t ts.
Proof.
  induction ts; simpl; intros. auto.
  intro Hcon. inv Hcon.
  destruct (iceq (t2k t) (t2k t)); subst.
  discriminate. congruence.
  destruct (iceq (t2k a) (t2k t)); subst.
  discriminate. apply IHts in H. contradiction.
Qed.


Lemma lkup_tab_t2k:
  forall ts ic t,
  lkup_tab ts ic = Some t ->
  ic = t2k t.
Proof.
  induction ts; simpl; intros. discriminate.
  destruct (iceq (t2k a) ic); subst; auto.
  inv H; auto.
Qed.

(* 

Q: what happens if we take the domain of a cookie process instead of
the cookie string's domain property? 

A: I think it doesn't break the security of the browser much. It
allows for a tab to set a non-cross-domain third-party cookie.

*)

Fixpoint K2TSetCookieActions (c:cproc) (tabs:list tab) (cookie_str:list ascii) :=
  match tabs with
  | t :: tabs' =>  
    if (laeq (cproc_domain c) (get_topdomain_tab (tab_origin_url t))) then
      (K2TSetCookieActions c tabs' cookie_str) ++ 
      (WroteMsg t (K2TSetCookie (length_in_size cookie_str) cookie_str))
    else 
      (K2TSetCookieActions c tabs' cookie_str)
  | nil => nil
  end.

Lemma K2TSetCookieActions_not_ResultCookie : 
  forall tabs cookie c t s p,
    K2TSetCookieActions c tabs cookie <> WroteMsg t (ResultCookie s p).
Proof.
  intros.
  induction tabs.

  simpl. unfold not. intros. inversion H.
  unfold not; intros. destruct IHtabs.

  simpl in H.
  destruct (laeq (cproc_domain c) (get_topdomain_tab (tab_origin_url a))).
  
  assert (
    rev (K2TSetCookieActions c tabs cookie ++
      WroteMsg a (K2TSetCookie (length_in_size cookie) cookie)) =
    rev (WroteMsg t (ResultCookie s p))
    ).
  rewrite H. reflexivity.
  rewrite rev_app_distr in H0. simpl in H0. inv H0.
  auto.
Qed.


Lemma K2TSetCookieActions_not_WroteCMsg :
  forall tabs cookie c1 c2 m,
    K2TSetCookieActions c1 tabs cookie <> WroteCMsg c2 m.
Proof.
  intros.
  induction tabs.

  simpl. unfold not. intros. inversion H.
  unfold not; intros. destruct IHtabs.

  simpl in H.
  destruct (laeq (cproc_domain c1) (get_topdomain_tab (tab_origin_url a))).
  
  assert (
    rev (K2TSetCookieActions c1 tabs cookie ++
      WroteMsg a (K2TSetCookie (length_in_size cookie) cookie)) =
    rev (WroteCMsg c2 m)).
  rewrite H. reflexivity.
  simpl in H0.
  
  simpl. unfold not; intros.
  rewrite rev_app_distr in H0. simpl in H0. inv H0.
  destruct m; inv H3. rewrite H; auto.
Qed.

(*
   This tr is not a usual tr.
   it must be tr generated by applying KStep many times.
   Is it okay to treat tr as a random tr??

   1. Define KStep.
   2. Define TraceOK based on KStep.
   3. ???

   1. Isn't it possible to define two inductive types depending on each
   other?
   
   2. why can't we say that a cookie process always exists..
   A) we can't. -- that's what we can prove over KSteps..I mean, 
*)

Inductive KStep : Trace -> Trace -> Trace -> Prop :=
  | KStep_add_tab_wo_cproc:
      forall tr t ok c,
      classify_user_cmd ok tr = UAddTab ->
      In c (cur_cprocs tr) ->
      cur_cproc (get_topdomain_tab (tab_origin_url t)) tr = Some c -> 
      KStep tr
        (MkTab t :: ReadFile stdin ok :: nil)
        (WroteMsg t (Render (size 1%positive) ("000"%char::nil)) ++ Paint ((cur_tabs tr) ++ t::nil) t)
  | KStep_add_tab_with_cproc:
      forall tr t c ok,
      classify_user_cmd ok tr = UAddTab ->
      cur_cproc (get_topdomain_tab (tab_origin_url t)) tr = None ->
      la_eq (cproc_domain c) (get_topdomain_tab (tab_origin_url t)) ->
      KStep tr
        (MkCProc c :: MkTab t :: ReadFile stdin ok :: nil)
        (WroteMsg t (Render (size 1%positive) ("000"%char::nil))  ++ Paint ((cur_tabs tr) ++ t::nil) t)
  | KStep_switch_tab:
      forall tr t ok,
      classify_user_cmd ok tr = USwitchTab t ->
      KStep tr
        (ReadFile stdin ok :: nil)
        (WroteMsg t (Render (size 1%positive) ("000"%char :: nil))  ++ Paint (cur_tabs tr) t)
  | KStep_key_press:
      forall tr t ok k,
      classify_user_cmd ok tr = UKeyPress t k ->
      KStep tr
        (ReadFile stdin ok :: nil)
        (WroteMsg t (KeyPress (size 1%positive) (k::nil)))
  | KStep_mouseclick:
      forall tr t ok s,
      classify_user_cmd ok tr = UMouseClick t ->
      KStep tr
        (MousePos s :: ReadFile stdin ok :: nil)
        (WroteMsg t (MouseClick (length_in_size s) s))
  | KStep_ignore:
      forall tr ok,
      classify_user_cmd ok tr = UIgnore ->
      KStep tr
        (ReadFile stdin ok :: nil)
        nil
  | Kstep_fetch:
      forall tr t p url html,
      In t (cur_tabs tr) ->
      KStep tr
        (Wget url html :: ReadMsg t (ReqHtml p url))
        (WroteMsg t (RspHtml (length_in_size html) html))
  | Kstep_navigate_true_wo_cproc:
      forall tr c t t' p url,
      In t (cur_tabs tr) -> (la_eq (tab_init_url t') url) ->
      cur_cproc (get_topdomain_tab (tab_origin_url t')) tr = Some c -> 
      KStep tr
        (MkTab t' :: Endorse true :: WroteEndorseMsg url :: ReadMsg t (Navigate p url))
        (WroteMsg t' (Render (size 1%positive) ("000"%char::nil)) ++ Paint ((cur_tabs tr) ++ t'::nil) t')
  | Kstep_navigate_true_with_cproc:
      forall tr c t t' p url,
      In t (cur_tabs tr) -> (la_eq (tab_init_url t') url) ->
      cur_cproc (get_topdomain_tab (tab_origin_url t')) tr = None ->
      la_eq (cproc_domain c) (get_topdomain_tab (tab_origin_url t')) ->
      KStep tr
        (MkCProc c :: MkTab t' :: Endorse true :: WroteEndorseMsg url :: ReadMsg t (Navigate p url))
        (WroteMsg t' (Render (size 1%positive) ("000"%char::nil)) ++ Paint ((cur_tabs tr) ++ t'::nil) t')
  | Kstep_navigate_false:
      forall tr t p url,
      In t (cur_tabs tr) ->
      KStep tr
        (Endorse false :: WroteEndorseMsg url :: ReadMsg t (Navigate p url))
        nil
  | Kstep_socket_true:
      forall tr t s host sock_desc,
      In t (cur_tabs tr) -> 
      la_eq host (get_host sock_desc) ->
      is_safe_sock_dest_on host  (tab_origin_url t) = true ->
      KStep tr
        (ReadMsg t (RequestSocket s sock_desc))
        (SendSocket t host sock_desc :: WroteMsg t (ResultSocket (size 1%positive) ("000"%char :: nil)))
  | Kstep_socket_false:
      forall tr t s host sock_desc,
      In t (cur_tabs tr) -> 
      la_eq host (get_host sock_desc) ->
      is_safe_sock_dest_on host  (tab_origin_url t) <> true ->
      KStep tr
        (ReadMsg t (RequestSocket s sock_desc))
        (WroteMsg t (ResultSocket (size 1%positive) ("001"%char :: nil))) (* 001 stands for an error code *)
(* DON:Q: why do we have to make this change? Why does this help? *)
(* DON:A: so that the kernel's response to a tab only depends on the tab *)
  | Kstep_cookie_set:
      forall tr t c s cookie,
      In t (cur_tabs tr) ->
      In c (cur_cprocs tr) ->
      (* tab's toporigin = cookie's top domain  *)
      (* this prevents third-party cookies. But why? why do we have to
      disallow this?*) 
      la_eq (get_topdomain_tab (tab_origin_url t))
            (get_topdomain_cookie cookie) ->
      (* there exists such cproc *)
      cur_cproc (get_topdomain_cookie cookie) tr = (Some c) ->
      KStep tr
        (ReadMsg t (SetCookie s cookie))
        (WroteCMsg c (K2CSetCookie s (cookie)))
  | Kstep_cookie_set_error:
      forall tr t s cookie,
      In t (cur_tabs tr) ->
      ~ la_eq (get_topdomain_tab (tab_origin_url t)) (get_topdomain_cookie cookie) ->
      KStep tr
        (ReadMsg t (SetCookie s cookie))
        nil
  | Kstep_cookie_set_c2k:
      forall tr c s cookie_msg,
      In c (cur_cprocs tr) ->
      KStep tr
        (ReadCMsg c (C2KSetCookie s cookie_msg))
        (K2TSetCookieActions c (cur_tabs tr) cookie_msg)
  | Kstep_cookie_get_t2k:
      forall tr t c s url,
      In t (cur_tabs tr) ->
      In c (cur_cprocs tr) ->
      cur_cproc (get_topdomain_tab (tab_origin_url t)) tr = (Some c) -> 
      KStep tr
        (ReadMsg t (GetCookie s url))
        (WroteCMsg c (K2CGetCookie s ((tab_id_to_la (t2k t)) ++ url)))
  | Kstep_cookie_get_c2k:
      forall tr t c s cookie_msg,
      In t (cur_tabs tr) ->
      In c (cur_cprocs tr) ->
      get_tab_id cookie_msg = t2k t ->
      cur_cproc (get_topdomain_tab (tab_origin_url t)) tr = Some c -> 
      KStep tr
        (ReadCMsg c (C2KResultCookie s cookie_msg))
        (WroteMsg t (ResultCookie (length_in_size (get_cookie_content cookie_msg))
                                  (get_cookie_content cookie_msg)))
  | Kstep_cookie_get_c2k_error_wrong_dom:
      forall tr t c s cookie_msg,
      In t (cur_tabs tr) ->
      In c (cur_cprocs tr) ->
      get_tab_id cookie_msg = t2k t ->
      cur_cproc (get_topdomain_tab (tab_origin_url t)) tr <> Some c -> 
      KStep tr
        (ReadCMsg c (C2KResultCookie s cookie_msg))
        nil
  | Kstep_cookie_get_c2k_error_bad_tab_id:
      forall tr tid c s cookie_msg,
      In c (cur_cprocs tr) ->
      get_tab_id cookie_msg = tid ->
      lkup_tab (cur_tabs tr) tid = None ->
      KStep tr
        (ReadCMsg c (C2KResultCookie s cookie_msg))
        nil
  | Kstep_display:
      forall tr t s p,
      In t (cur_tabs tr) ->
      cur_tab tr = Some t ->
      KStep tr
        (ReadMsg t (Display s p))
        (WroteGMsg (K2GDisplay s p))
  | Kstep_display_ignore:
      forall tr t s p,
      In t (cur_tabs tr) ->
      cur_tab tr <> Some t ->
      KStep tr
        (ReadMsg t (Display s p))
        nil
  | Kstep_bad_msg:
      forall tr t s la,
      In t (cur_tabs tr) ->
      not_msg la ->
      KStep tr
        (ReadN (t2k t) s la :: nil)
        nil.


Theorem KStep_req_no_write :
  forall tr req rsp f s p,
    KStep tr req rsp -> ~ In (WriteN f s p) req.
Proof.
  unfold not. intros tr req rsp f s p kstep in_write.
  inv kstep;
  repeat destruct in_write as [in_write' | in_write]; try inversion in_write'; auto; fail.
Qed.


Inductive TraceOK : Trace -> Prop :=
  | TraceOK_nil:
      TraceOK nil
  | TraceOK_add:
      forall tr req rsp,
      TraceOK tr ->
      KStep tr req rsp ->
      TraceOK (rsp ++ req ++ tr).


Inductive tabs_distinct : Trace -> Prop :=
  | tabs_distinct_intro:
      forall tr,
      uniq (map k2t (cur_tabs tr)) ->
      uniq (map t2k (cur_tabs tr)) ->
      tabs_distinct tr.


Inductive cprocs_distinct : Trace -> Prop :=
  | cprocs_distinct_intro:
      forall tr,
        uniq (map c2k (cur_cprocs tr)) ->
        uniq (map k2c (cur_cprocs tr)) ->
        uniq (map cproc_domain (cur_cprocs tr)) ->
        cprocs_distinct tr.


Inductive procs_distinct : Trace -> Prop :=
  | procs_distinct_intro:
      forall tr,
      uniq (map k2t (cur_tabs tr) ++ map k2c (cur_cprocs tr)) ->
      uniq (map t2k (cur_tabs tr) ++ map c2k (cur_cprocs tr)) ->
      uniq (map cproc_domain (cur_cprocs tr)) ->
      procs_distinct tr.


Lemma procs_distinct_tabs_distinct : 
  forall tr, procs_distinct tr -> tabs_distinct tr.
Proof.
  intros tr procs_distinct.
  inversion procs_distinct.
  apply uniq_app in H. destruct H.
  apply uniq_app in H0. destruct H0.
  econstructor; eauto. 
Qed.


Lemma procs_distinct_cprocs_distinct : 
  forall tr, procs_distinct tr -> cprocs_distinct tr.
Proof.
  intros tr procs_distinct.
  inversion procs_distinct.
  apply uniq_app in H. destruct H.
  apply uniq_app in H0. destruct H0.
  econstructor; eauto. 
Qed.


Lemma cur_cprocs_same : 
  forall tr1 tr2 domain c1 c2, 
    cur_cproc domain tr1 = Some c1 ->
    cur_cproc domain tr2 = Some c2 ->
    cproc_domain c1 = cproc_domain c2.
Proof.
  intros.
  assert (cproc_domain c1 = domain).
  eapply cur_cproc_domain. apply H.

  assert (cproc_domain c2 = domain).
  eapply cur_cproc_domain. apply H0.

  rewrite H1. rewrite<- H2. auto.
Qed.


Lemma cur_cproc_inj : 
  forall tr1 tr2 domain c1 c2, 
    cprocs_distinct tr1 ->
    cprocs_distinct tr2 ->
    cur_cprocs tr2 = cur_cprocs tr1 ->
    cur_cproc domain tr1 = Some c1 ->
    cur_cproc domain tr2 = Some c2 ->
    c1 = c2.
Proof.
  intros.
  inv H.
  inv H0.

  assert (In c1 (cur_cprocs tr2)).
    rewrite H1.
    eapply cur_cproc_in_cur_cprocs in H2; eauto.
  assert (In c2 (cur_cprocs tr1)).
    rewrite <- H1.
    eapply cur_cproc_in_cur_cprocs in H3; eauto.
  assert (cproc_domain c1 = cproc_domain c2).
    eapply cur_cprocs_same; eauto.
  eapply map_in_uniq_inv.
    apply H10.
    apply H6.
    eapply cur_cproc_in_cur_cprocs in H2; eauto.
    eapply cur_cproc_in_cur_cprocs in H3; eauto.
Qed.


Definition not_sendsocket_action (act:Action): Prop :=
  match act with 
    | SendSocket _ _ _ => False
    | _ => True
  end.


Inductive socket_to_safe_origin : Trace -> Prop :=
  | socket_to_safe_origin_nil:
     socket_to_safe_origin nil
  | socket_to_safe_origin_intro:
     forall tr t host gib, 
       is_safe_sock_dest_on host  (tab_origin_url t) = true ->
       socket_to_safe_origin tr ->
       socket_to_safe_origin ((SendSocket t host gib)::tr)
  | socket_to_safe_origin_others:
    forall act tr,
      not_sendsocket_action act ->
      socket_to_safe_origin tr ->
      socket_to_safe_origin (act :: tr).


Lemma K2TSetCookieActions_dist :
  forall c t t' cookie, 
    (K2TSetCookieActions c (t ++ t') cookie) =  (K2TSetCookieActions c t' cookie) ++  (K2TSetCookieActions c t cookie).
Proof.
  intros c t t' cookie.
  induction t.
  (* base case *)
  
  simpl. rewrite app_nil_r. auto.

  (* inductive case *)
  simpl.
  destruct ( laeq (cproc_domain c) (get_topdomain_tab (tab_origin_url a)) ).
  rewrite IHt. rewrite app_assoc. auto.
  auto.
Qed.


Lemma cur_tabs_same_over_K2TSetCookieActions :
  forall c tr cookie tr' tr'', 
    cur_tabs tr = cur_tabs tr'' -> 
    cur_tabs tr = cur_tabs (K2TSetCookieActions c (cur_tabs tr') cookie ++ tr'').
Proof.
  induction tr'.
  simpl; auto.

  simpl. destruct a; simpl; auto.
  rewrite K2TSetCookieActions_dist.
  simpl. destruct (laeq (cproc_domain c) (get_topdomain_tab (tab_origin_url t))); simpl.

  intros. simpl. apply IHtr'; auto.
  intros. simpl. apply IHtr'; auto. 
Qed.


Lemma socket_to_safe_comp :
  forall tr1 tr2, 
    socket_to_safe_origin tr1 ->
    socket_to_safe_origin tr2 ->
    socket_to_safe_origin (tr1 ++ tr2).
Proof.
  intros tr1 tr2.
  induction tr1.

  intros; auto.

  intros. inversion H. rewrite <- app_comm_cons.
  econstructor. auto. auto.

  rewrite <- app_comm_cons.
  destruct a; try econstructor; eauto. 
Qed.


Lemma socket_to_safe_dist_l :
  forall tr1 tr2, 
    socket_to_safe_origin (tr1 ++ tr2) ->
    socket_to_safe_origin tr1.
Proof.
  intros tr1 tr2.
  induction tr1.

  intros. apply socket_to_safe_origin_nil.

  simpl. intros. inv H.
  apply socket_to_safe_origin_intro. auto. 
  auto. econstructor. auto. auto.
Qed.


Lemma socket_to_safe_dist_r :
  forall tr1 tr2, 
    socket_to_safe_origin (tr1 ++ tr2) ->
    socket_to_safe_origin tr2.
Proof.
  intros tr1 tr2.
  induction tr1.

  intros. auto.

  simpl. intros. inv H. auto. auto.
Qed.


Lemma K2TSetCookieActions_socket_to_safe_origin :
  forall c tr tr' cookie,
    socket_to_safe_origin tr' -> socket_to_safe_origin (K2TSetCookieActions c (cur_tabs tr) cookie ++ tr').
Proof.
  induction tr; auto.
  
  intros. simpl. destruct a; try (apply IHtr; auto; fail).
  rewrite K2TSetCookieActions_dist.
  simpl. destruct (laeq (cproc_domain c) (get_topdomain_tab (tab_origin_url t))).
  simpl.
  repeat (apply socket_to_safe_origin_others; simpl; auto).
  simpl. auto.
Qed.


Lemma SocketCreation_SOP:
  forall tr, TraceOK tr -> socket_to_safe_origin tr.
Proof.
  intros. induction H.
  econstructor; eauto; simpl; auto.
  inv H0; simpl;
  repeat match goal with
  | |- socket_to_safe_origin (SendSocket ?t ?host ?sock_desc :: ?tr) =>
      apply socket_to_safe_origin_intro; simpl; auto
  | |- socket_to_safe_origin (?tr) =>
      apply socket_to_safe_origin_others; simpl; auto
  end.
  apply K2TSetCookieActions_socket_to_safe_origin.
  repeat (apply socket_to_safe_origin_others; simpl; auto). 
Qed.


(*
Lemma K2TSetCookieActions_not_MkCProc :
  forall cproc tabs cookie_msg, (In (MkCProc cproc) (K2TSetCookieActions tabs cookie_msg)).
Proof.
  intros.
  induction tabs.
  unfold not. intros. inversion H.
  unfold not in *. intros.  destruct IHtabs.
  simpl in H. destruct (laeq (get_topdomain_tab (tab_origin_url a)) (get_topdomain_cookie cookie_msg)).
  apply in_app_or in H. destruct H. auto.
  simpl in H.
  destruct H as [H' | H]. inversion H'.
  destruct H as [H' | H]. inversion H'.
  destruct H as [H' | H]. inversion H'.
  inversion H. auto.
Qed.


Lemma K2TSetCookieActions_not_MkCProc :
  forall cproc tabs cookie_msg, ~ (In (MkCProc cproc) (K2TSetCookieActions tabs cookie_msg)).
Proof.
  intros.
  induction tabs.
  unfold not. intros. inversion H.
  unfold not in *. intros.  destruct IHtabs.
  simpl in H. destruct (laeq (get_topdomain_tab (tab_origin_url a)) (get_topdomain_cookie cookie_msg)).
  apply in_app_or in H. destruct H. auto.
  simpl in H.
  destruct H as [H' | H]. inversion H'.
  destruct H as [H' | H]. inversion H'.
  destruct H as [H' | H]. inversion H'.
  inversion H. auto.
Qed.

Lemma remove_sth_
*)

Lemma cur_proc_preserved_K2TSetCookieActions :
  forall c domain tabs cookie_msg tr,
   cur_cproc domain (K2TSetCookieActions c tabs cookie_msg ++ tr)
     = cur_cproc domain tr.
Proof.
  intros.
  generalize dependent tr.
  induction tabs.

  intros; auto.

  intros.
  simpl. destruct (laeq (cproc_domain c) (get_topdomain_tab (tab_origin_url a))).
  rewrite app_assoc.
  rewrite IHtabs. reflexivity. apply IHtabs.
Qed.


Theorem cur_cproc_some :
  forall tr t, TraceOK tr -> In t (cur_tabs tr) -> 
    cur_cproc (get_topdomain_tab (tab_origin_url t)) tr <> None.
Proof.
  intros tr t TraceOK_tr t_in_cur_tabs.
  induction TraceOK_tr.

  simpl in t_in_cur_tabs. destruct t_in_cur_tabs.
  inv H; simpl; simpl in t_in_cur_tabs; auto.
  (*
     : forall (A : Type) (l m : list A) (a : A),
       In a (l ++ m) -> In a l \/ In a m
       *)

  (* Add Tab - not creating a new cookie process *)
  assert (In t (cur_tabs tr) \/ In t (t0::nil)).
  apply in_app_or; auto.

  destruct H.
  (* when a tab in discussion existed in the past trace *)
  auto.

  (* when a tab in discussion is created in the current request *)
  simpl in H. destruct H. rewrite <- H. rewrite H2. 
  discriminate. destruct H.

  
  (* Add Tab - create a new cookie process *)
  assert (In t (cur_tabs tr) \/ In t (t0::nil)).
  apply in_app_or; auto.

  destruct H.
  destruct (laeq (cproc_domain c) (get_topdomain_tab (tab_origin_url t))).
  discriminate.

  apply IHTraceOK_tr. auto.

  (* --- when a cproc is actually created *)
  simpl in H. destruct H.
  destruct (laeq (cproc_domain c) (get_topdomain_tab (tab_origin_url t))).
  (* what's happened *) discriminate.

  destruct n.
  rewrite <- H. eapply la_eq_same; eauto. apply la_eq_refl.
  destruct H.


  (* navigation - when there already exists a cproc for the newly open tab *)
  assert (In t (cur_tabs tr) \/ In t (t'::nil)).
  apply in_app_or; auto.

  destruct H.
  apply IHTraceOK_tr; auto.

  simpl in H. destruct H. rewrite <- H. rewrite H2. 
  discriminate. destruct H.

  (* navigation - we create a new cproc *)
  assert (In t (cur_tabs tr) \/ In t (t'::nil)).
  apply in_app_or; auto.

  destruct H.
  destruct (laeq (cproc_domain c) (get_topdomain_tab (tab_origin_url t))).
  discriminate.

  apply IHTraceOK_tr. auto.

  
  simpl in H. destruct H.
  destruct (laeq (cproc_domain c) (get_topdomain_tab (tab_origin_url t))).
  (* what's happened *) discriminate.

  destruct n.
  rewrite <- H. eapply la_eq_same; eauto. apply la_eq_refl.
  destruct H.

  rewrite cur_proc_preserved_K2TSetCookieActions.
  simpl.

  rewrite <- cur_tabs_same_over_K2TSetCookieActions with (tr := ReadN (c2k c) s cookie_msg            
                                                             :: ReadN (c2k c) (size 4) (pos2la4 s)
                                                             :: ReadN (c2k c) (size 1) ("017"%char :: nil)
                                                             :: tr ) in t_in_cur_tabs.
  simpl in t_in_cur_tabs.
  apply IHTraceOK_tr. auto. auto.
Qed.

(*
Lemma KStep_det:
  forall hist req rspA rspB,
  tabs_distinct hist ->
  cprocs_distinct hist ->
  KStep hist req rspA ->
  KStep hist req rspB ->
  rspA = rspB.
Proof.
  intros.

  inv H1; inv H2; auto.

  f_equal.
  rewrite H3 in H5. inversion H5. auto.

  rewrite H3 in H5. discriminate.
  rewrite H3 in H5. discriminate.
  rewrite H3 in H5. discriminate.
  rewrite H3 in H5; inversion H5; auto.
  rewrite H3 in H5. discriminate.
  rewrite H3 in H7; inversion H7; auto.
  rewrite H3 in H5. discriminate.
  rewrite H3 in H5. discriminate.

  f_equal. inv H.
  eapply map_in_uniq_inv; eauto.

  f_equal. f_equal. inv H.
  eapply map_in_uniq_inv; eauto.

  eapply la_eq_same.
  apply H4. apply H14.

  f_equal. inv H.
  eapply map_in_uniq_inv; eauto.


  rewrite<- H5 in H15. 
  destruct H15.
  f_equal.
  eapply la_eq_same; eauto.

  assert (t0 = t).
  eapply map_in_uniq_inv; eauto.
  inv H. auto.
  rewrite H2. auto.


  rewrite<- H15 in H5.
  destruct H5.
  f_equal.
  eapply la_eq_same; eauto.

  assert (t0 = t).
  eapply map_in_uniq_inv; eauto.
  inv H. auto.
  rewrite H2. auto.
  

  f_equal.
  eapply map_in_uniq_inv. eauto.
  inversion H. eauto. auto. auto.

  f_equal. f_equal.
  eapply map_in_uniq_inv. eauto.
  inversion H. eauto. auto. auto.

  f_equal. f_equal.
  eapply cur_cproc_inj; eauto.

  assert (t = t0).  
  eapply map_in_uniq_inv. eauto.
  inversion H. eauto. auto. auto.

  destruct H15.
  rewrite<- H2 in H7.
  destruct H7; auto.

  rewrite H6 in H7.
  discriminate.

  
  destruct H4.

  assert (t = t0). 
  eapply map_in_uniq_inv. eauto.
  inversion H. eauto. auto. auto.

  destruct H2.
  rewrite<- H4 in H14.
  auto.

  rewrite H2 in H15. discriminate.

  f_equal. f_equal.

  assert (t = t0).  
  eapply map_in_uniq_inv. eauto.
  inversion H. eauto. auto. auto.
  rewrite<- H2 in H13.
  
  subst.
  rewrite H5 in H15.
  inv H15. reflexivity.

  assert (t = t0).  
  eapply map_in_uniq_inv. eauto.
  inversion H. eauto. auto. auto.
  rewrite<- H2 in H13.

  rewrite<- H2 in H14.
  rewrite H5 in H14.
  discriminate.

  assert (t = t0).  
  eapply map_in_uniq_inv. eauto.
  inversion H. eauto. auto. auto.
  rewrite<- H2 in H13.

  rewrite<- H2 in H14.
  rewrite H5 in H14.
  discriminate.

  assert (t = t0).
  eapply map_in_uniq_inv. eauto.
  inversion H. eauto. auto. auto.
  rewrite<- H2 in H14.
  rewrite H4 in H14.

  discriminate.


  f_equal. f_equal.

  rewrite H5 in H16.
  eapply map_in_uniq_inv. eauto.
  inversion H. eauto. auto. auto.

  assert (c = c0).
  eapply map_in_uniq_inv. eauto.
  inversion H0. eauto. auto. auto.
  destruct H17. rewrite<- H2.

  rewrite H5 in H16. 
  assert (t = t0).
  eapply map_in_uniq_inv. eauto.
  inversion H. eauto. auto. auto.
  rewrite<- H7. auto.

  rewrite H5 in H16.
  apply lkup_tab_nin in H16.
  contradiction.

  assert (t = t0).
  rewrite H5 in H16.
  eapply map_in_uniq_inv. eauto.
  inversion H. eauto. auto. auto.

  assert (c = c0).
  eapply map_in_uniq_inv. eauto.
  inversion H0. eauto. auto. auto.
  destruct H6. rewrite H7. rewrite H2.
  auto.

  rewrite H14 in H5.
  apply lkup_tab_nin in H5.
  contradiction.

  assert (t = t0).
  eapply map_in_uniq_inv. eauto.
  inversion H. eauto. auto. auto.

  rewrite H2 in H4. rewrite H4 in H14. discriminate.

  f_equal. f_equal.
  eapply map_in_uniq_inv. eauto.
  inversion H. eauto. auto. auto.

  rewrite H4 in H13. unfold not in H13.
  assert (t = t0).
  eapply map_in_uniq_inv. eauto.
  inversion H. eauto. auto. auto.
  rewrite H2 in H13. destruct H13. reflexivity.

  rewrite H13 in H4. unfold not in H4.
  assert (t = t0).
  eapply map_in_uniq_inv. eauto.
  inversion H. eauto. auto. auto.
  rewrite H2 in H4. destruct H4. reflexivity.

Qed.
*)


(* This says that the kernel's response to a tab's request only
depends on

1) the current tab 
2) the currently created tabs.

Since the user input uniquely decides the currently created tabs,
this theorem basically says, 

"the response of a kernel just depends on the current tab and the
previous user input" 

but this is somewhat weird. This is only about rsp can be the same,
but not should be the same. Actucally, it should be the same because
of KStep_det.  *)

Lemma cur_cproc_return_requested_domain:
  forall tr c domain, 
    cur_cproc domain tr = Some c ->
    (cproc_domain c) = domain.
Proof.
  induction tr.

  intros.
  simpl in H. discriminate.

  intros.
  destruct a; simpl in H; auto.

  destruct (laeq (cproc_domain c0) domain).
  inversion H. rewrite<- H1. apply e.

  auto.
Qed.


Lemma in_trace :
  forall a domain tr, In (MkCProc a) tr -> (cproc_domain a) = domain -> cur_cproc domain tr <> None.
Proof.
  induction tr.
  intros.
  simpl in H.
  contradiction.

  intros.
  destruct a0. 
  simpl; simpl in H; destruct H. discriminate. auto.
  simpl; simpl in H; destruct H. discriminate. auto.
  simpl; simpl in H; destruct H. discriminate. auto.
  simpl; simpl in H; destruct H. discriminate. auto.
  simpl; simpl in H; destruct H. discriminate. auto.

  simpl; simpl in H; destruct H.
  discriminate.
  auto.

  simpl.
  (*
  simpl; simpl in H; destruct H. discriminate. auto.
  simpl;
  *)
  destruct (laeq (cproc_domain c) domain).
  discriminate.

  apply IHtr.
  simpl in H. destruct H.
  inversion H.
  rewrite H2 in n. rewrite<- H0 in n.
  destruct n. reflexivity.

  auto. auto. simpl.
  apply IHtr.
  simpl in H.
  destruct H. discriminate. auto.
  auto.

  simpl. apply IHtr. simpl in H. 
  destruct H. discriminate. auto.

  auto.

  simpl. simpl in H. apply IHtr.
  destruct H. discriminate. auto.

  auto.

  simpl. simpl in H. apply IHtr.
  destruct H. discriminate. auto.

  auto.
Qed.


Lemma cur_cprocs_to_tr :
  forall a tr, In a (cur_cprocs tr) -> In (MkCProc a) tr.
Proof.
  induction tr.

  intros.
  simpl in H. contradiction.

  intros.
  destruct a0; simpl in H; simpl; auto; simpl; auto.
  
  simpl in H. destruct H.
  rewrite H. simpl. auto.

  simpl. right. auto.
Qed.


Lemma cproc_some_not_none:
  forall tr1 tr2 domain c,
    cur_cprocs tr1 = cur_cprocs tr2 ->
    cur_cproc domain tr1 = (Some c) ->
    cur_cproc domain tr2 <> None.
Proof.
  intros.
  
  assert (In c (cur_cprocs tr2)).
  eapply cur_cproc_in_cur_cprocs.
  apply H. apply H0.

  assert (In (MkCProc c) tr2).
  apply cur_cprocs_to_tr. apply H1.
  
  eapply in_trace. apply H2.

  eapply cur_cproc_return_requested_domain.
  apply H0.
Qed.


Lemma cur_cprocs_nil_cur_cproc_none:
  forall tr domain, 
    cur_cprocs tr = nil -> cur_cproc domain tr = None.
Proof.
  intros.
  induction tr; simpl; auto.
  simpl. destruct a; auto.
  destruct (laeq (cproc_domain c) domain);
  simpl in H; discriminate.
Qed.


Lemma cur_cproc_eq_on_filtered_trace:
  forall tr domain,
    cur_cproc domain (map MkCProc (cur_cprocs tr)) = cur_cproc domain tr.
Proof.
  induction tr.
  intros.
  simpl. auto.

  intros.
  simpl. destruct a; auto.

  destruct (laeq (cproc_domain c) domain). simpl.
  destruct (laeq (cproc_domain c) domain). auto.
  destruct n. auto.

  simpl.
  destruct (laeq (cproc_domain c) domain). simpl.
  destruct n. auto.

  apply IHtr.
Qed.


Lemma cur_cproc_none_eq_on_filtered_trace:
  forall tr1 c domain,
    cur_cproc domain (map MkCProc (cur_cprocs tr1)) = None ->
    cproc_domain c <> domain ->
    cur_cproc domain (MkCProc c ::map MkCProc (cur_cprocs tr1)) = None.
Proof.
  intros tr1.  

  intros.
  simpl.
  destruct (laeq (cproc_domain c) domain). simpl.
  destruct H0. auto.

  apply H.
Qed.


Lemma cproc_none_none:
  forall tr1 tr2 domain,
    cur_cprocs tr1 = cur_cprocs tr2 ->
    cur_cproc domain tr1 = None ->
    cur_cproc domain tr2 = None.
Proof.
  intros.
  induction tr1.

  simpl in *; auto.

  apply cur_cprocs_nil_cur_cproc_none. 
  rewrite H. auto.

  destruct a; auto.

  simpl in H0.
  destruct (laeq (cproc_domain c) domain).
  discriminate.

  simpl in H.
  rewrite<- cur_cproc_eq_on_filtered_trace.
  rewrite<- H.
  simpl.

  assert (cur_cproc domain (map MkCProc (cur_cprocs tr1)) = None).
  rewrite cur_cproc_eq_on_filtered_trace. auto.
  apply cur_cproc_none_eq_on_filtered_trace. auto. auto.
Qed.


Lemma cproc_distinct_cur_proc:
  forall tr1 tr2 domain,
    cprocs_distinct tr1 ->
    cprocs_distinct tr2 ->
    cur_cprocs tr1 = cur_cprocs tr2 ->
    cur_cproc domain tr1 = cur_cproc domain tr2.
Proof.
  intros.

  destruct (cur_cproc domain tr1) as []_eqn.
  destruct (cur_cproc domain tr2) as []_eqn.

  assert (c = c0).
  eapply cur_cproc_inj.
  apply H.
  apply H0.
  symmetry in H1. apply H1.
  apply Heqo.
  apply Heqo0.
  rewrite H2. auto.

  assert (cur_cproc domain tr2 <> None).
  eapply cproc_some_not_none; eauto. 
  destruct H2. auto.

  symmetry.
  eapply cproc_none_none; eauto.
Qed.


Lemma KStep_response_integrity :
  forall tr1 tr2 req rsp,
  tabs_distinct tr1 ->
  tabs_distinct tr2 ->
  cprocs_distinct tr1 ->
  cprocs_distinct tr2 ->
  KStep tr1 req rsp ->
  cur_tab tr2 = cur_tab tr1 ->
  cur_tabs tr2 = cur_tabs tr1 ->
  cur_cprocs tr2 = cur_cprocs tr1 ->
  KStep tr2 req rsp.
Proof.
  intros.
  inv H3; try (
    econstructor; eauto;
    unfold classify_user_cmd in *;
    try rewrite H4;
    try rewrite H5;
    try rewrite H6;
    try rewrite <- H8;
    try apply cproc_distinct_cur_proc;
    auto; fail
  ); try (
    try rewrite <- H4;
    try rewrite <- H5;
    try rewrite <- H6;
    try rewrite <- H8
  ).
  
  econstructor; eauto.
  unfold classify_user_cmd in *.
  rewrite H4, H5 in *; auto.
  rewrite H6; apply H8.
  rewrite<- H9.
  apply cproc_distinct_cur_proc; auto.

  (* econstructor; eauto. *)
  econstructor; eauto.
  unfold classify_user_cmd in *.
  rewrite H4, H5 in *; auto.

  eapply cproc_none_none with (tr1 := tr1) (tr2 := tr2); eauto.

  econstructor; eauto.
  unfold classify_user_cmd in *.
  rewrite H4, H5 in *; auto.
  rewrite H5; auto. 

  assert (cur_cproc (get_topdomain_tab (tab_origin_url t')) tr1 = cur_cproc (get_topdomain_tab (tab_origin_url t')) tr2).
  apply cproc_distinct_cur_proc; auto.
  rewrite <- H5.
  econstructor; eauto.
  rewrite H5. auto. rewrite H9 in H3. eauto.

  econstructor; eauto.
  rewrite H5; auto.

  eapply cproc_none_none with (tr1 := tr1) (tr2 := tr2); eauto.

  econstructor; eauto. rewrite H5; auto.

  rewrite H6; auto.

  rewrite <- H10.
  eapply cproc_distinct_cur_proc; eauto.

  econstructor; eauto. rewrite H6; eauto.

  econstructor; eauto.
  rewrite H5; eauto.
  rewrite H6; eauto.

  rewrite <- H9.
  eapply cproc_distinct_cur_proc; eauto.

  econstructor; eauto.
  rewrite H5; eauto.
  rewrite H6; eauto.

  rewrite <- H10.
  eapply cproc_distinct_cur_proc; eauto.

  econstructor; eauto.
  rewrite H5; eauto.
  rewrite H6; eauto.

  unfold not in *.
  intros. destruct H10.
  rewrite <- H3.
  eapply cproc_distinct_cur_proc; eauto.

  rewrite <- H5 in H9.

  eapply Kstep_cookie_get_c2k_error_bad_tab_id.
  rewrite H6; eauto. eauto. auto.
Qed.
     
(* BEGIN: projection *)

Inductive ctrl_key : ascii -> Prop :=
| ctrl_key_f1 : ctrl_key "001"%char
| ctrl_key_f2 : ctrl_key "002"%char
| ctrl_key_f3 : ctrl_key "003"%char
| ctrl_key_f4 : ctrl_key "004"%char
| ctrl_key_f5 : ctrl_key "005"%char
| ctrl_key_f6 : ctrl_key "006"%char
| ctrl_key_f7 : ctrl_key "007"%char
| ctrl_key_f8 : ctrl_key "014"%char
| ctrl_key_f9 : ctrl_key "015"%char
| ctrl_key_f10 : ctrl_key "016"%char
| ctrl_key_f11 : ctrl_key "017"%char
| ctrl_key_f12 : ctrl_key "018"%char.


Definition ctrl_key_dec :
  forall a, {ctrl_key a} + {~ ctrl_key a}.
Proof.
  intros. 
  destruct a.
  destruct b6; [right; unfold not; intros; inversion H; subst |].
  destruct b5; [right; unfold not; intros; inversion H; subst |].
  destruct b4; [right; unfold not; intros; inversion H; subst |].
  destruct b3; destruct b2; destruct b1; destruct b0; destruct b;
  try (right; unfold not; intros; inversion H; subst || left; econstructor); left; econstructor.
Qed.

Lemma ctrl_key_dec_true:
  forall T (A B: T) f,
  ctrl_key f -> (if ctrl_key_dec f then A else B) = A.
Proof.
  intros.
  case (ctrl_key_dec f); intros. auto.
  destruct n. auto.
Qed.

Lemma ctrl_key_dec_false:
  forall T (A B: T) f1,
  ~ ctrl_key f1  ->
  (if ctrl_key_dec f1 then A else B) = B.
Proof.
  intros. case (ctrl_key_dec f1); intros.
  subst. destruct H; auto. auto.
Qed.

Fixpoint proj_useract (trace: Trace) : Trace :=
  match trace with
  | ReadFile f p :: tr =>
      if file_desc_eq f stdin then
        if ctrl_key_dec p
          then
            ReadFile f p :: proj_useract tr
          else
            proj_useract tr
      else
        proj_useract tr
  | Endorse c :: tr => Endorse c :: proj_useract tr
  | a:: tr => proj_useract tr
  | nil =>
      nil
  end.

Lemma proj_useract_WroteMsg:
  forall t m tr,
  proj_useract (WroteMsg t m ++ tr) = proj_useract tr.
Proof.
  intros.
  unfold WroteMsg.
  rewrite<- app_comm_cons. simpl. reflexivity.
Qed.


Lemma proj_useract_Clear:
  forall tr,
  proj_useract (Clear :: tr) = proj_useract tr.
Proof.
  intros.
  unfold Clear.
  simpl. reflexivity.
Qed.


Lemma proj_useract_Paint:
  forall tr t,
  proj_useract (Paint (cur_tabs tr) t ++ tr) = proj_useract tr.
Proof.
  intros.
  unfold Paint.
  simpl. reflexivity.
Qed.


Lemma proj_useract_MkTab:
  forall t tr,
  proj_useract (MkTab t:: tr) = proj_useract tr.
Proof.
  intros.
  simpl. reflexivity.
Qed.

Lemma proj_useract_MkCProc:
  forall c tr,
  proj_useract (MkCProc c:: tr) = proj_useract tr.
Proof.
  intros.
  simpl. reflexivity.
Qed.

Lemma proj_useract_MousePos:
  forall s tr,
  proj_useract (MousePos s:: tr) = proj_useract tr.
Proof.
  intros.
  simpl. reflexivity.
Qed.

Lemma proj_useract_WroteStr:
  forall s t tr,
  proj_useract (WroteStr t s :: tr) = proj_useract tr.
Proof.
  intros.
  simpl. reflexivity.
Qed.


Lemma proj_useract_ReadFile_true:
  forall c tr,
    ctrl_key c ->
    proj_useract (ReadFile stdin c :: tr) = ReadFile stdin c :: proj_useract tr.
Proof.
  intros.
  simpl.
  rewrite file_desc_eq_true.
  rewrite ctrl_key_dec_true; auto.
Qed.  


Lemma proj_useract_ReadFile_false:
  forall c tr,
    ~ ctrl_key c ->
    proj_useract (ReadFile stdin c :: tr) = proj_useract tr.
Proof.
  intros.
  simpl.
  rewrite file_desc_eq_true.
  destruct c.
  rewrite ctrl_key_dec_false; auto.
Qed.


Lemma proj_useract_Endorse:
  forall c tr,
  proj_useract (Endorse c :: tr) = Endorse c :: proj_useract tr.
Proof.
  intros.
  simpl. reflexivity.
Qed.


Lemma proj_useract_WroteEndorseMsg:
  forall url tr,
  proj_useract (WroteEndorseMsg url :: tr) = proj_useract tr.
Proof.
  intros.
  simpl. reflexivity.
Qed.
(* END: projection *)


Lemma if_none_none_none:
  forall (b:bool) (None:option nat), (if b then None else None) = None.
Proof.
  intros.
  destruct b; auto.
Qed.


Lemma addtab_ctrl_key :
  forall a tr, 
    classify_user_cmd a tr = UAddTab -> ctrl_key a.
Proof.
  intros.
  
  unfold classify_user_cmd in H.

  destruct (ascii_dec a "017"); subst.
  econstructor.

  destruct (ascii_dec a "018"); subst.
  econstructor.

  destruct (select_tab_idx a).
  destruct (nth_error (cur_tabs tr) n1); discriminate.
  destruct (cur_tab tr); discriminate.
Qed.


Lemma mouseclick_ctrl_key :
  forall a tr t, 
    classify_user_cmd a tr = UMouseClick t -> ctrl_key a.
Proof.
  intros.
  unfold classify_user_cmd in H.

  destruct (ascii_dec a "017"); subst.
  econstructor.

  destruct (ascii_dec a "018"); subst.
  econstructor.
  
  destruct (select_tab_idx a).
  destruct (nth_error (cur_tabs tr) n1); discriminate.

  destruct (cur_tab tr); discriminate.
Qed.


Lemma switchtab_ctrl_key :
  forall a tr t, 
    classify_user_cmd a tr = USwitchTab t -> ctrl_key a.
Proof.
  intros.
  unfold classify_user_cmd in H.

  destruct (ascii_dec a "017"); subst.
  econstructor.

  destruct (ascii_dec a "018"); subst.
  econstructor.

  destruct a.
  simpl in H.

  destruct b6; destruct b5; destruct b4; destruct b3; 
  destruct b2; destruct b1; destruct b0; destruct b; 
  repeat try rewrite if_none_none_none in H ; 
  repeat try(destruct (cur_tab tr); discriminate); try econstructor.
Qed.



Lemma cur_tab_same_over_K2TSetCookieActions :
  forall c tr cookie tr' tr'', cur_tab tr = cur_tab tr'' -> 
    cur_tab tr = cur_tab (K2TSetCookieActions c (cur_tabs tr') cookie ++ tr'').
Proof.
  induction tr'.
  simpl; auto.

  simpl. destruct a; simpl; auto.
  rewrite K2TSetCookieActions_dist.
  simpl. destruct (laeq (cproc_domain c) (get_topdomain_tab (tab_origin_url t))).

  intros. simpl. apply IHtr'; auto.
  intros. simpl. apply IHtr'; auto.
Qed.


Lemma cur_cprocs_same_over_K2TSetCookieActions :
  forall c tr cookie tr' tr'', cur_cprocs tr = cur_cprocs tr'' -> 
    cur_cprocs tr = cur_cprocs (K2TSetCookieActions c (cur_tabs tr') cookie ++ tr'').
Proof.
  induction tr'.
  simpl; auto.

  simpl. destruct a; simpl; auto.
  rewrite K2TSetCookieActions_dist.
  simpl. destruct (laeq (cproc_domain c) (get_topdomain_tab (tab_origin_url t))).

  intros. simpl. apply IHtr'; auto.
  intros. simpl. apply IHtr'; auto.
Qed.

Lemma pres_useract_cur_tabs:
  forall tr req rsp,
  tabs_distinct tr ->
  KStep tr req rsp ->
  proj_useract tr = proj_useract (rsp ++ req ++ tr) ->
  cur_tabs tr = cur_tabs (rsp ++ req ++ tr).
Proof.
  destruct 2; norm_list; intros; simpl; try reflexivity.

  rewrite proj_useract_WroteMsg in H3.
  simpl in H3. rewrite file_desc_eq_true in H3.
  destruct ok. rewrite ctrl_key_dec_true in H3.
  apply f_equal with (f := @List.length _) in H3.
  simpl in H3. cut False; [contradiction | omega].

  eapply addtab_ctrl_key; eauto.

  rewrite proj_useract_WroteMsg in H3.
  simpl in H3. rewrite file_desc_eq_true in H3.
  destruct ok. rewrite ctrl_key_dec_true in H3.
  apply f_equal with (f := @List.length _) in H3.
  simpl in H3. cut False; [contradiction | omega].

  eapply addtab_ctrl_key; eauto.

  rewrite proj_useract_WroteMsg in H3.
  unfold Paint in H3. simpl in H3.
  (*
  rewrite proj_useract_Endorse in H3.
  rewrite proj_useract_WroteEndorseMsg in H3.
  Opaque proj_useract.
  simpl in H3.
  Transparent proj_useract.
  simpl in H3.
  *)
  apply f_equal with (f := @List.length _) in H3.
  simpl in H3. cut False; [contradiction | omega].

  simpl in H4.

  apply f_equal with (f := @List.length _) in H4.
  simpl in H4. cut False; [contradiction | omega].

  apply cur_tabs_same_over_K2TSetCookieActions.
  simpl; auto.
Qed.


Lemma not_ctrl_key_select_tab_idx_none:
  forall a, 
    ~ ctrl_key a ->
    select_tab_idx a = None.
Proof.
  intros.
  destruct a.
  unfold not in H.
  destruct b6; destruct b5; destruct b4; destruct b3; destruct b2; destruct b1; destruct b0; destruct b; simpl; auto;
  destruct H; econstructor.
Qed.


Lemma keypress_not_function_keys:
  forall a tr t k, classify_user_cmd a tr = UKeyPress t k -> ~ ctrl_key a.
Proof.
  intros.
  destruct a.
  unfold not. intros.
  destruct b6; destruct b5; destruct b4; destruct b3; destruct b2; destruct b1; destruct b0; destruct b; simpl; inversion H0.

  try (simpl in H; destruct (cur_tab tr); discriminate).

  unfold classify_user_cmd in H. simpl in H.
  destruct (cur_tab tr). simpl in H. discriminate.
  repeat (destruct l; simpl in H; [try discriminate|]; try discriminate).

  destruct (cur_tabs tr). simpl in H. discriminate.
  (destruct l; simpl in H; [try discriminate|]; try discriminate).

  unfold classify_user_cmd in H. simpl in H.
  destruct (cur_tabs tr). simpl in H. discriminate.
  (destruct l; simpl in H; [try discriminate|]; try discriminate).

  unfold classify_user_cmd in H. simpl in H.
  destruct (cur_tabs tr). simpl in H. discriminate.
  repeat (destruct l; simpl in H; [try discriminate|]; try discriminate).

  unfold classify_user_cmd in H. simpl in H.
  destruct (cur_tabs tr). simpl in H. discriminate.
  repeat (destruct l; simpl in H; [try discriminate|]; try discriminate).

  unfold classify_user_cmd in H. simpl in H.
  destruct (cur_tabs tr). simpl in H. discriminate.
  repeat (destruct l; simpl in H; [try discriminate|]; try discriminate).

  unfold classify_user_cmd in H. simpl in H.
  destruct (cur_tabs tr). simpl in H. discriminate.
  repeat (destruct l; simpl in H; [try discriminate|]; try discriminate).

  unfold classify_user_cmd in H. simpl in H.
  destruct (cur_tabs tr). simpl in H. discriminate.
  repeat (destruct l; simpl in H; [try discriminate|]; try discriminate).

  unfold classify_user_cmd in H. simpl in H.
  destruct (cur_tabs tr). simpl in H. discriminate.
  repeat (destruct l; simpl in H; [try discriminate|]; try discriminate).

  unfold classify_user_cmd in H. simpl in H.
  destruct (cur_tabs tr). simpl in H. discriminate.
  repeat (destruct l; simpl in H; [try discriminate|]; try discriminate).

  unfold classify_user_cmd in H. simpl in H.
  destruct (cur_tabs tr). simpl in H. discriminate.
  repeat (destruct l; simpl in H; [try discriminate|]; try discriminate).

  unfold classify_user_cmd in H. simpl in H.
  destruct (cur_tabs tr). simpl in H. discriminate.
  repeat (destruct l; simpl in H; [try discriminate|]; try discriminate).

  unfold classify_user_cmd in H. simpl in H.
  destruct (cur_tabs tr). simpl in H. discriminate.
  repeat (destruct l; simpl in H; [try discriminate|]; try discriminate).
Qed.


Lemma keypress_select_tab_idx_none :
  forall a tr t k,
    classify_user_cmd a tr = UKeyPress t k ->
    select_tab_idx a = None.
Proof.
  intros.
  assert ( ~ ctrl_key a).
  eapply keypress_not_function_keys; eauto.
  apply not_ctrl_key_select_tab_idx_none; auto.
Qed.


Lemma mouseclick_select_tab_idx_none :
  forall a tr t,
    classify_user_cmd a tr = UMouseClick t ->
    select_tab_idx a = None.
Proof.
  intros.
  destruct a.
  unfold not in H.
  destruct b6; destruct b5; destruct b4; destruct b3; destruct b2; destruct b1; destruct b0; destruct b; simpl; auto.

  unfold classify_user_cmd in H.
  destruct (cur_tabs tr). simpl in H. discriminate.
  repeat (destruct l; simpl in H; [try discriminate|]; try discriminate).
  unfold classify_user_cmd in H.
  destruct (cur_tabs tr). simpl in H. discriminate.
  repeat (destruct l; simpl in H; [try discriminate|]; try discriminate).
  unfold classify_user_cmd in H.
  destruct (cur_tabs tr). simpl in H. discriminate.
  repeat (destruct l; simpl in H; [try discriminate|]; try discriminate).
  unfold classify_user_cmd in H.
  destruct (cur_tabs tr). simpl in H. discriminate.
  repeat (destruct l; simpl in H; [try discriminate|]; try discriminate).
  unfold classify_user_cmd in H.
  destruct (cur_tabs tr). simpl in H. discriminate.
  repeat (destruct l; simpl in H; [try discriminate|]; try discriminate).
  unfold classify_user_cmd in H.
  destruct (cur_tabs tr). simpl in H. discriminate.
  repeat (destruct l; simpl in H; [try discriminate|]; try discriminate).
  unfold classify_user_cmd in H.
  destruct (cur_tabs tr). simpl in H. discriminate.
  repeat (destruct l; simpl in H; [try discriminate|]; try discriminate).
  unfold classify_user_cmd in H.
  destruct (cur_tabs tr). simpl in H. discriminate.
  repeat (destruct l; simpl in H; [try discriminate|]; try discriminate).
  unfold classify_user_cmd in H.
  destruct (cur_tabs tr). simpl in H. discriminate.
  repeat (destruct l; simpl in H; [try discriminate|]; try discriminate).
  unfold classify_user_cmd in H.
  destruct (cur_tabs tr). simpl in H. discriminate.
  repeat (destruct l; simpl in H; [try discriminate|]; try discriminate).
Qed.


Lemma pres_useract_cur_tab:
  forall tr req rsp,
  tabs_distinct tr ->
  cprocs_distinct tr ->
  KStep tr req rsp ->
  proj_useract tr = proj_useract (rsp ++ req ++ tr) ->
  cur_tab tr = cur_tab (rsp ++ req ++ tr).
Proof.
  destruct 3; norm_list; intros; simpl; auto.

  rewrite proj_useract_WroteMsg in H4.
  unfold Paint in H4.
  simpl in H4.
  rewrite file_desc_eq_true in H4.
  destruct (ctrl_key_dec ok).
  apply f_equal with (f := @List.length _) in H4.
  simpl in H4. cut False; [contradiction | omega].
  destruct n.
  eapply addtab_ctrl_key; eauto.

  rewrite proj_useract_WroteMsg in H4.
  unfold Paint in H4. simpl in H4.
  rewrite (file_desc_eq_true) in H4.
  destruct (ctrl_key_dec ok).
  apply f_equal with (f := @List.length _) in H4.
  simpl in H4. cut False; [contradiction | omega].
  destruct n.
  eapply addtab_ctrl_key; eauto.

  simpl.
  rewrite proj_useract_WroteMsg in H2.
  unfold Paint in H2. simpl in H2.
  rewrite (file_desc_eq_true) in H2.
  destruct (ctrl_key_dec ok).
  apply f_equal with (f := @List.length _) in H2.
  simpl in H2. cut False; [contradiction | omega].
  destruct n. eapply switchtab_ctrl_key; eauto.
  simpl. rewrite file_desc_eq_true.

  assert ((select_tab_idx ok) = None).
  eapply keypress_select_tab_idx_none; eauto.
  rewrite H3; auto.
  auto.

  simpl in H2. rewrite file_desc_eq_true in H2.
  destruct (ctrl_key_dec ok).
  apply f_equal with (f := @List.length _) in H2.
  simpl in H2. cut False; [contradiction | omega].

  simpl. rewrite file_desc_eq_true.
  assert ((select_tab_idx ok) = None).
  eapply mouseclick_select_tab_idx_none; eauto.
  rewrite H3; auto.
  auto.

  destruct ok.
  destruct b6; destruct b5; destruct b4; destruct b3; destruct b2; destruct b1; destruct b0; destruct b; simpl; rewrite file_desc_eq_true; auto;

  repeat (simpl in H2; rewrite file_desc_eq_true in H2; rewrite ctrl_key_dec_true in H2;
  apply f_equal with (f := @List.length _) in H2; 
    [ simpl in H2; cut False; [contradiction | omega] | econstructor ]).

  simpl in H4.
  apply f_equal with (f := @List.length _) in H4.
  simpl in H4. cut False; [contradiction | omega].

  simpl in H5.
  apply f_equal with (f := @List.length _) in H5.
  simpl in H5. cut False; [contradiction | omega].

  apply cur_tab_same_over_K2TSetCookieActions.
  simpl; auto.
Qed.


Lemma pres_useract_cur_cprocs:
  forall tr req rsp,
  tabs_distinct tr ->
  cprocs_distinct tr ->
  KStep tr req rsp ->
  proj_useract tr = proj_useract (rsp ++ req ++ tr) ->
  cur_cprocs tr = cur_cprocs (rsp ++ req ++ tr).
Proof.
  destruct 3; norm_list; intros; simpl; auto.

  rewrite proj_useract_WroteMsg in H4.

  simpl in H4. rewrite file_desc_eq_true in H4.
  rewrite ctrl_key_dec_true in H4.
  destruct ok.
  apply f_equal with (f := @List.length _) in H4.
  simpl in H4. cut False; [contradiction | omega].

  eapply addtab_ctrl_key. apply H1.
  simpl in H5.
    apply f_equal with (f := @List.length _) in H5;
  simpl in H5. cut False; [contradiction | omega].

  apply cur_cprocs_same_over_K2TSetCookieActions.
  simpl; auto.
Qed.

Theorem state_integrity :
  forall tr req rsp,
    tabs_distinct tr ->
    cprocs_distinct tr ->
    KStep tr req rsp ->
    proj_useract tr = proj_useract (rsp ++ req ++ tr) ->
    cur_tabs tr = cur_tabs (rsp ++ req ++ tr) /\
    cur_tab tr = cur_tab (rsp ++ req ++ tr) /\
    cur_cprocs tr = cur_cprocs (rsp ++ req ++ tr).
Proof.
  intros.
  split. apply pres_useract_cur_tabs; auto.
  split. apply pres_useract_cur_tab; auto.
  apply pres_useract_cur_cprocs; auto. 
Qed.

Fixpoint get_cproc (domain: list ascii) (cprocs:list cproc) : option cproc :=
  match cprocs with
    | c :: cps => if laeq (cproc_domain c) domain then (Some c) else get_cproc domain cps
    | nil => None
  end.


Lemma get_cprocs_in :
  forall domain ccps c, 
    get_cproc domain ccps = Some c -> In c ccps.
Proof.
  induction ccps.
  
  intros.
  simpl in H. discriminate.

  intros.
  destruct a.
  simpl in H.

  destruct (laeq l domain).
  simpl. inv H. left. reflexivity.
  simpl. right. apply IHccps.
  apply H.
Qed. 

Lemma cur_cproc_eq_get_cproc :
  forall domain tr,
    cur_cproc domain tr = get_cproc domain (cur_cprocs tr).
Proof.
  induction tr.
  simpl. auto.

  simpl. destruct a; auto. simpl.

  destruct (laeq (cproc_domain c) domain).
  auto.
  
  apply IHtr.
Qed.


Theorem get_cproc_some :
  forall tr t, TraceOK tr -> In t (cur_tabs tr) -> 
    get_cproc (get_topdomain_tab (tab_origin_url t))  (cur_cprocs tr) <> None.
Proof.
  intros tr t TraceOK_tr t_in_cur_tabs.
  rewrite <- cur_cproc_eq_get_cproc.
  apply cur_cproc_some. auto. auto. Qed.

Lemma get_cproc_none_not_in:
  forall domain cprocslist,
    get_cproc domain cprocslist = None -> ~ In domain (map cproc_domain cprocslist).
Proof.
  induction cprocslist.
  simpl. unfold not. intros. destruct H0.
  
  intros.
  destruct a; simpl; auto.

  unfold not. unfold not in IHcprocslist.
  simpl in H.
  destruct (laeq l domain).
  discriminate.

  unfold not in n. intros. destruct H0.
  apply n; auto.

  apply IHcprocslist; auto.
Qed.

Check length.


Inductive from_tab : tab -> Trace -> Prop :=
  | from_tab_intro :
    forall t s la, from_tab t (ReadN (t2k t) s la :: nil)
  | from_tab_more :
    forall t tr a, 
      from_tab t tr -> from_tab t (a :: tr).

Lemma in_map :
  forall (T1 T2:Type) l (g:T1->T2) (a:T1),
    In a l -> In (g a) (map g l).
Proof.
  intros.
  induction l.

  inversion H.

  simpl in H. destruct H.
  simpl. left. rewrite H. auto.

  simpl. right. apply IHl. auto.
Qed.


Lemma uniq_map_noteq :
  forall (T1 T2 T3:Type) (f:T1->T3) (g:T2->T3) l1 l2 (a:T1) (b:T2), 
    uniq (map f l1 ++ map g l2) -> 
    In a l1 ->
    In b l2 ->
    f a <> g b.
Proof.
  intros T1 T2 T3 f g l1.
  induction l1.
  
  intros. simpl in H0. inversion H0.

  intros.
  (*
  destruct l2.
  simpl in H1. inversion H1.
  *)
  assert (map f (a :: l1) = f a :: map f l1). auto.
  rewrite H2 in H.

  simpl in H0. destruct H0.
  unfold not. intros.
  inversion H. rewrite <- H0 in *.
  destruct H7. apply in_or_app. right.
  rewrite H3.

  apply in_map. auto.

  eapply IHl1; eauto.
  simpl in H. inversion H. auto.
Qed.

Lemma readn_not_from_readcmsg:
  forall tr t c s p m,
    procs_distinct tr ->
    In t (cur_tabs tr) ->
    In c (cur_cprocs tr) ->
    ~ In (ReadN (t2k t) s p) (ReadCMsg c m).
Proof.
  intros tr t c s p m procs_distinct in_t in_c.
  inversion procs_distinct.
  assert (t2k t <> c2k c).
  eapply uniq_map_noteq; eauto.
  
  unfold not. intros.
  inversion H4. inversion H5. rewrite H7 in H3. destruct H3; auto.
  inversion H5. inversion H6. rewrite H8 in H3. destruct H3; auto.
  inversion H6. inversion H7. rewrite H9 in H3. destruct H3; auto.
  inversion H7.
Qed.
  

Lemma read_msg_from_tab :
  forall t t' s p m,
    In (ReadN (t2k t) s p) (ReadMsg t' m) ->
    from_tab t  (ReadMsg t' m).
Proof.
  intros.
  apply from_tab_more.
  apply from_tab_more.

  simpl in H. destruct H.
  inversion H.
  rewrite H1. apply from_tab_intro.

  simpl in H. destruct H.
  inversion H.
  rewrite H1. apply from_tab_intro.

  simpl in H. destruct H.
  inversion H.
  rewrite H1. apply from_tab_intro.

  inversion H.
Qed.


Theorem from_tab_correct : 
  forall tr req res t s m, 
    In t (cur_tabs tr) -> 
    procs_distinct tr ->
    KStep tr req res -> 
    In (ReadN (t2k t) s m) req ->
    from_tab t req.
Proof.
  intros tr req res t s m in_t procs_distinct kstep in_read.
  inv kstep.

  (destruct in_read as [in_read' | in_read];
    [inversion in_read' | destruct in_read as [in_read' | in_read];
      [inversion in_read' | destruct in_read ]
    ]).

  (destruct in_read as [in_read' | in_read];
    [inversion in_read' | destruct in_read as [in_read' | in_read];
      [inversion in_read' | destruct in_read as [in_read' | in_read];
        [inversion in_read' | destruct in_read] 
      ]
    ]).

  (destruct in_read as [in_read' | in_read];
    [inversion in_read' | destruct in_read]).

  destruct in_read as [in_read' | in_read];
    [inversion in_read' | destruct in_read].

  (destruct in_read as [in_read' | in_read];
    [inversion in_read' | destruct in_read as [in_read' | in_read];
      [inversion in_read' | destruct in_read ]
    ]).

  destruct in_read as [in_read' | in_read];
    [inversion in_read' | destruct in_read].

  Opaque ReadMsg.
  simpl in in_read. destruct in_read.
  inversion H0.
  apply from_tab_more.
  eapply read_msg_from_tab; eauto.

  simpl in in_read. 
  destruct in_read as [ in_read' | in_read];
    [inversion in_read' | destruct in_read].
  inversion H2.
  destruct H2. inversion H2.
  apply from_tab_more. apply from_tab_more. apply from_tab_more.
  eapply read_msg_from_tab; eauto.

  apply from_tab_more. apply from_tab_more. apply from_tab_more. 
  apply from_tab_more.

  simpl in in_read. 
  destruct in_read as [ in_read' | in_read];
    [inversion in_read' | destruct in_read].
  inversion H3.
  destruct H3. inversion H3. 
  destruct H3. inversion H3. 
  eapply read_msg_from_tab; eauto.

  simpl in in_read. 
  destruct in_read. inversion H0. destruct H0.
  inversion H0.
  apply from_tab_more. apply from_tab_more.
  eapply read_msg_from_tab; eauto.

  eapply read_msg_from_tab; eauto.

  eapply read_msg_from_tab; eauto.

  eapply read_msg_from_tab; eauto.

  eapply read_msg_from_tab; eauto.
  Check readn_not_from_readcmsg.
  eapply readn_not_from_readcmsg with (t:=t) in in_read. 
  contradiction.
  eauto. auto. auto.

  eapply read_msg_from_tab; eauto.
  
  eapply readn_not_from_readcmsg with (t:=t) in in_read. 
  contradiction.
  eauto. auto. auto.

  eapply readn_not_from_readcmsg with (t:=t) in in_read. 
  contradiction.
  eauto. auto. auto.

  eapply readn_not_from_readcmsg with (t:=t) in in_read. 
  contradiction.
  eauto. auto. auto.

  eapply read_msg_from_tab; eauto.

  eapply read_msg_from_tab; eauto.

  simpl in in_read.
  destruct in_read.
  inversion H1.  rewrite H3.
  apply from_tab_intro.

  inversion H1.
Qed.

Lemma list_eq_last :
  forall (T:Type) (l1:list T) (l2:list T) (a1:T) (a2:T),
    (l1 ++ a1 :: nil = l2 ++ a2 :: nil) -> a1 = a2.
Proof.
  intros T l1.
  induction l1.
  simpl. intros.
  destruct l2. simpl in H. inversion H; auto.
  apply f_equal with (f := @List.length _) in H.
  rewrite app_length in H. simpl in H.
  cut False; [contradiction | omega].

  intros.
  destruct l2. simpl in H.
  apply f_equal with (f := @List.length _) in H.
  simpl in H. rewrite app_length in H. simpl in H.
  cut False; [contradiction | omega].

  simpl in H. inversion H. eapply IHl1; eauto.
Qed.

Lemma in_readn_readmsg_same_t:
  forall t t' s la m,
    In (ReadN (t2k t) s la) (ReadMsg t' m) -> (t2k t) = (t2k t').
Proof.
  intros.
  Transparent ReadMsg.
  unfold ReadMsg in H.
  simpl in H.
  destruct H. inversion H. auto.
  destruct H. inversion H. auto.
  destruct H. inversion H. auto.
  inversion H.
Qed.


Lemma in_readn_readmsg :
  forall tr tr' req rsp t t' s la m, 
    tabs_distinct tr ->
    In t (cur_tabs tr) ->
    In t' (cur_tabs tr) ->
    req = tr' ++ ReadMsg t' m ->
    KStep tr req rsp ->  
    In (ReadN (t2k t) s la) req ->
    t = t'.
Proof.
  intros.
  inv H3;
  try (
    unfold ReadMsg in H9;
    apply f_equal with (f := @List.rev _) in H9;
    rewrite rev_app_distr in H9; simpl in H9;
    inversion H9
  );
  try (
    unfold ReadMsg in H7;
    apply f_equal with (f := @List.rev _) in H7;
    rewrite rev_app_distr in H7; simpl in H7;
    inversion H7
  ).

  inversion H7. inversion H7.
  apply f_equal with (f := @List.rev _) in H21.
  rewrite rev_involutive in H21.
  simpl in H21.
  rewrite <- H21 in H4.
  apply in_app_or in H4.
  destruct H4. simpl in H2. destruct H2; [discriminate H2 | inversion H2].
  apply in_readn_readmsg_same_t in H2.
  eapply map_in_uniq_inv;  eauto;
  inv H; auto.

  inversion H9. inversion H9.
  apply f_equal with (f := @List.rev _) in H23.
  rewrite rev_involutive in H23.
  simpl in H23.
  rewrite <- H23 in H4.
  apply in_app_or in H4.
  destruct H4. simpl in H2.
  destruct H2; try discriminate H2.
  destruct H2; try discriminate H2.
  destruct H2; try discriminate H2.
  inversion H2.
  apply in_readn_readmsg_same_t in H2.
  eapply map_in_uniq_inv;  eauto;
  inv H; auto.

  try (
    unfold ReadMsg in H10;
    apply f_equal with (f := @List.rev _) in H10;
    rewrite rev_app_distr in H10; simpl in H10;
    inversion H10
  ).

  inversion H10. inversion H10.
  apply f_equal with (f := @List.rev _) in H24.
  rewrite rev_involutive in H24.
  simpl in H24.
  rewrite <- H24 in H4.
  apply in_app_or in H4.
  destruct H4. simpl in H2.
  destruct H2; try discriminate H2.
  destruct H2; try discriminate H2.
  destruct H2; try discriminate H2.
  destruct H2; try discriminate H2.
  inversion H2.
  apply in_readn_readmsg_same_t in H2.
  eapply map_in_uniq_inv;  eauto;
  inv H; auto.

  apply f_equal with (f := @List.rev _) in H13.
  rewrite rev_involutive in H13.
  simpl in H13.
  rewrite <- H13 in H4.
  apply in_app_or in H4.
  destruct H4. simpl in H2.
  destruct H2; try discriminate H2.
  destruct H2; try discriminate H2.
  inversion H2.
  apply in_readn_readmsg_same_t in H2.
  eapply map_in_uniq_inv;  eauto;
  inv H; auto.

  inversion H9. 
  apply f_equal with (f := @List.rev _) in H15.
  rewrite rev_involutive in H15.
  simpl in H15.
  rewrite <- H15 in H4.
  apply in_app_or in H4.
  destruct H4. simpl in H2.
  destruct H2; try discriminate H2.
  apply in_readn_readmsg_same_t in H2.
  eapply map_in_uniq_inv;  eauto;
  inv H; auto.

  inversion H9. 
  apply f_equal with (f := @List.rev _) in H15.
  rewrite rev_involutive in H15.
  simpl in H15.
  rewrite <- H15 in H4.
  apply in_app_or in H4.
  destruct H4. simpl in H2.
  destruct H2; try discriminate H2.
  apply in_readn_readmsg_same_t in H2.
  eapply map_in_uniq_inv;  eauto;
  inv H; auto.

  unfold ReadMsg in H10;
  apply f_equal with (f := @List.rev _) in H10.
  simpl in H10.
  rewrite rev_app_distr in H10; simpl in H10.
  inversion H10.
  apply f_equal with (f := @List.rev _) in H16.
  rewrite rev_involutive in H16. simpl in H16.
  rewrite <- H16 in H4.
  apply in_app_or in H4.
  destruct H4. simpl in H2.
  destruct H2; try discriminate H2.
  apply in_readn_readmsg_same_t in H2.
  eapply map_in_uniq_inv;  eauto;
  inv H; auto.

  unfold ReadMsg in H8;
  apply f_equal with (f := @List.rev _) in H8.
  simpl in H8.
  rewrite rev_app_distr in H8; simpl in H8.
  inversion H8.
  apply f_equal with (f := @List.rev _) in H14.
  rewrite rev_involutive in H14. simpl in H14.
  rewrite <- H14 in H4.
  apply in_app_or in H4.
  destruct H4. simpl in H2.
  inversion H2.
  apply in_readn_readmsg_same_t in H2.
  eapply map_in_uniq_inv;  eauto.
  inv H; auto.

  destruct m; discriminate H6.

  apply f_equal with (f := @List.rev _) in H15.
  rewrite rev_involutive in H15.
  simpl in H15.
  rewrite <- H15 in H4.
  apply in_app_or in H4.
  destruct H4. simpl in H2.
  destruct H2; try discriminate H2.
  apply in_readn_readmsg_same_t in H2.
  eapply map_in_uniq_inv;  eauto;
  inv H; auto.

  unfold ReadMsg in H10.
  apply f_equal with (f := @List.rev _) in H10.
  rewrite rev_app_distr in H10; simpl in H10.
  inversion H10.
  destruct m; discriminate H9.

  unfold ReadMsg in H10.
  apply f_equal with (f := @List.rev _) in H10.
  rewrite rev_app_distr in H10; simpl in H10.
  inversion H10.
  destruct m; discriminate H9.

  apply f_equal with (f := @List.rev _) in H14.
  rewrite rev_involutive in H14.
  simpl in H14.
  rewrite <- H14 in H4.
  apply in_app_or in H4.
  destruct H4. simpl in H2.
  destruct H2; try discriminate H2.
  apply in_readn_readmsg_same_t in H2.
  eapply map_in_uniq_inv;  eauto;
  inv H; auto.

  unfold ReadMsg in H8.
  apply f_equal with (f := @List.rev _) in H8.
  rewrite rev_app_distr in H8; simpl in H8.
  inversion H8.

  apply f_equal with (f := @List.rev _) in H14.
  rewrite rev_involutive in H14.
  simpl in H14.
  rewrite <- H14 in H4.
  apply in_app_or in H4.
  destruct H4. simpl in H2.
  destruct H2; try discriminate H2.
  apply in_readn_readmsg_same_t in H2.
  eapply map_in_uniq_inv;  eauto;
  inv H; auto.

  unfold ReadMsg in H8.
  apply f_equal with (f := @List.rev _) in H8.
  rewrite rev_app_distr in H8; simpl in H8.
  inversion H8.

  apply f_equal with (f := @List.rev _) in H14.
  rewrite rev_involutive in H14.
  simpl in H14.
  rewrite <- H14 in H4.
  apply in_app_or in H4.
  destruct H4. simpl in H2.
  destruct H2; try discriminate H2.
  apply in_readn_readmsg_same_t in H2.
  eapply map_in_uniq_inv;  eauto;
  inv H; auto.

  unfold ReadMsg in H8.
  apply f_equal with (f := @List.rev _) in H8.
  rewrite rev_app_distr in H8; simpl in H8.
  inversion H8.
Qed.


Lemma uniq_elem_swap :
  forall (T:Type) (a:T) (b:T) l1 l2,
    uniq (a :: l1 ++ b :: l2) -> uniq (a :: b :: nil ++ l1 ++ l2).
Proof. 
  intros T a b l1.
  induction l1.

  simpl. intros. auto.

  simpl. intros.
  inversion H.
  inversion H2.
  assert (uniq (a:: l1 ++ b :: l2)).
  apply uniq_cons. auto.
  simpl in H3. unfold not in H3.
  unfold not. intros. apply H3. auto.

  apply IHl1 in H8.
  constructor. constructor. constructor.
  inversion H8. inversion H11. auto.
  
  unfold not. intros.
  unfold not in H7. apply H7.
  apply in_or_app.
  apply in_app_or in H9.
  destruct H9. left; auto.
  right. apply in_cons. auto.

  simpl. unfold not. intros.
  destruct H9.
  
  rewrite H9 in H7. destruct H7.
  apply in_or_app. right. simpl. left. auto.

  inversion H8. inversion H12. auto.

  simpl. unfold not. intros.
  destruct H9.
  rewrite H9 in H8. inversion H8. destruct H13.
  simpl. left. auto.

  destruct H9.
  rewrite H9 in H3. destruct H3. simpl. left; auto.

  inversion H8. destruct H13. simpl. right. auto. 
Qed.

(*
   1) when the tab in discussion is the current tab : 1
   2) and the response is *NOT* to a cookie process : 0
*)
Lemma Tab_NI_cur_tab_not_to_cookie:
  forall tr1 tr2 req rsp1 rsp2 t,
  procs_distinct tr1 ->
  procs_distinct tr2 ->
  proj_useract req = nil ->
  from_tab t req ->
  In t (cur_tabs tr1) ->
  In t (cur_tabs tr2) ->
  cur_tab tr1 = Some t ->
  cur_tab tr2 = Some t ->
  ~ (exists c, exists m, rsp1 = WroteCMsg c m) ->
  True ->
  (* ~ (exists c, exists m, rsp2 = WroteCMsg c m) -> *)
  KStep tr1 req rsp1 ->  
  KStep tr2 req rsp2 ->
  rsp1 = rsp2.
Proof.
  intros.
  inv H9; try (
    econstructor; eauto;
    unfold classify_user_cmd in *;
    try rewrite H8;
    try rewrite H9;
    try rewrite H10;
    try rewrite <- H11;
    try apply cproc_distinct_cur_proc;
    auto; fail
  ).

  (* Mktab *)
  rewrite proj_useract_MkTab in H1.
  rewrite proj_useract_ReadFile_true in H1.
  discriminate H1.
  destruct ok. eapply addtab_ctrl_key; eauto.

  (* Mktab  + MkCProc *)
  rewrite proj_useract_MkCProc in H1.
  rewrite proj_useract_MkTab in H1.
  rewrite proj_useract_ReadFile_true in H1.
  discriminate H1.
  destruct ok. eapply addtab_ctrl_key; eauto.

  (* Switch Tab *)
  rewrite proj_useract_ReadFile_true in H1.
  discriminate H1.
  destruct ok. eapply switchtab_ctrl_key; eauto.

  (* KeyPress *)
  inversion H2. inversion H13. 
 
  (* MousePress *)
  inversion H2. inversion H13. inversion H17.

  (* ignore *)

  (* we'll have to think about two cases -- 1) ok is a control key to
     be ignored. -- not possible.  2) ok it NOT a control key, but
     ignored -- no tab must exist there. But it's not- *)
  
  (* 1 *)
  inversion H2. inversion H13.

  (* readmsg t followed by wget *)
  (* econstructor; eauto. *)
  inversion H2. inversion H13. inversion H17. inversion H21.
  assert (t0 = t).
  (* Check map_in_uniq_inv. *)
  eapply map_in_uniq_inv;  eauto.
  inv H. apply uniq_app in H28. destruct H28. auto.
  (* inv H. auto.*)
  rewrite <- H24 in *.

  inversion H10.
  assert (t0 = t5).
  Check map_in_uniq_inv.
  eapply map_in_uniq_inv with (l := cur_tabs tr2); eauto. 
  inv H0. apply uniq_app in H40. destruct H40. auto.
  rewrite <- H39 in *. auto.
  inversion H25.

  (* readmsg t : navigation action *)
  simpl in H1. inversion H1.  
  simpl in H1. inversion H1.  

  (* navigation : when the user doesn't endorse it *)
  simpl in H1. inversion H1. 
  simpl in H1. inversion H1.
  
  (* send socket - socket allowed to a same sub-domain *)
  inversion H2. inversion H15. inversion H16. inversion H19.
  assert (t0 = t).
  (* Check map_in_uniq_inv. *)
  eapply map_in_uniq_inv;  eauto.
  inv H. apply uniq_app in H27. destruct H27. auto.
  (* inv H. auto.*)
  rewrite <- H23 in *.

  inversion H10.
  assert (t0 = t4).
  eapply map_in_uniq_inv with (l := cur_tabs tr2); eauto. 
  inv H0. apply uniq_app in H39. destruct H39. auto.
  rewrite <- H38 in *. auto.
  assert (host = host0).
  eapply la_eq_same; eauto.
  rewrite <- H39 in *. auto.

  assert (t0 = t4).
  eapply map_in_uniq_inv with (l := cur_tabs tr2); eauto. 
  inv H0. apply uniq_app in H39. destruct H39. auto.
  rewrite <- H38 in *. auto.
  assert (host = host0).
  eapply la_eq_same; eauto.
  rewrite <- H39 in *. auto.
  contradiction.
  
  inversion H24.

  (* send socket - socket allowed to a same sub-domain *)
  inversion H2. inversion H15. inversion H16. inversion H19.
  assert (t0 = t).
  (* Check map_in_uniq_inv. *)
  eapply map_in_uniq_inv;  eauto.
  inv H. apply uniq_app in H27. destruct H27. auto.
  (* inv H. auto.*)
  rewrite <- H23 in *.

  inversion H10.
  assert (t0 = t4).
  eapply map_in_uniq_inv with (l := cur_tabs tr2); eauto. 
  inv H0. apply uniq_app in H39. destruct H39. auto.
  rewrite <- H38 in *. auto.
  assert (host = host0).
  eapply la_eq_same; eauto.
  rewrite <- H39 in *. auto.
  contradiction.

  assert (t0 = t4).
  eapply map_in_uniq_inv with (l := cur_tabs tr2); eauto. 
  inv H0. apply uniq_app in H39. destruct H39. auto.
  rewrite <- H38 in *. auto.
  inversion H24.

  (* t2k set cookie *)
  destruct H7.
  econstructor; eauto.

  (* t2k set cookie -- ignore *)
  (* econstructor; eauto. *)
  inversion H2. inversion H14. inversion H18.
  assert (t0 = t).
  (* Check map_in_uniq_inv. *)
  eapply map_in_uniq_inv;  eauto.
  inv H. apply uniq_app in H25. destruct H25. auto.
  (* eapply cur_tab_in_cur_tabs; eauto. *)
  rewrite <- H21 in *. eauto.

  inversion H10.
  assert (t0 = t4).
  eapply map_in_uniq_inv with (l := cur_tabs tr2); eauto. 
  inv H0. apply uniq_app in H38. destruct H38. auto.
  rewrite <- H37 in *. auto.
  contradiction.
  auto.
  inversion H22.

  (* c->k set cookie. *)
  inversion H2. inversion H13. inversion H17.
  (* attack the point that t cannot be the same as c *)
  inv H.
  assert (t2k t <> c2k c).
  eapply uniq_map_noteq; eauto.
  rewrite H21 in H. destruct H; auto.
  inversion H21.

  (* t2k get cookie *)
  destruct H7.
  econstructor; eauto.

  (* c2t get cookie *)
  inversion H2. inversion H16. inversion H20.
  (* attack the point that t cannot be the same as c *)
  inv H.
  assert (t2k t <> c2k c).
  eapply uniq_map_noteq; eauto.
  rewrite H24 in H. destruct H; auto.
  inversion H24.

  (* c2t get cookie -- ignored *)
  inversion H2. inversion H16. inversion H20.
  (* attack the point that t cannot be the same as c *)
  inv H.
  assert (t2k t <> c2k c).
  eapply uniq_map_noteq; eauto.
  rewrite H24 in H. destruct H; auto.
  inversion H24.

  (* c2t get cookie - ignored *)
  inversion H2. inversion H14. inversion H18.
  (* attack the point that t cannot be the same as c *)
  inv H.
  assert (t2k t <> c2k c).
  eapply uniq_map_noteq; eauto.
  rewrite H22 in H. destruct H; auto.
  inversion H22.

  (* display message *)
  (* econstructor; eauto. *)
  inversion H2.  inversion H14. inversion H18.
  assert (t0 = t).
  (* Check map_in_uniq_inv. *)
  eapply map_in_uniq_inv;  eauto.
  inv H. apply uniq_app in H25. destruct H25. auto.
  (* inv H. auto.*)
  rewrite <- H21 in *. eauto.

  inversion H10.
  assert (t0 = t4).
  eapply map_in_uniq_inv with (l := cur_tabs tr2); eauto. 
  inv H0. apply uniq_app in H36. destruct H36. auto.
  rewrite <- H35 in *. auto.

  assert (t0 = t4).
  eapply map_in_uniq_inv with (l := cur_tabs tr2); eauto. 
  inv H0. apply uniq_app in H36. destruct H36. auto.
  rewrite <- H35 in *. auto. contradiction.

  inversion H22.

  (* display message - ignored *)
  (* econstructor; eauto. *)
  inversion H2.  inversion H14. inversion H18.
  assert (t0 = t).
  (* Check map_in_uniq_inv. *)
  eapply map_in_uniq_inv;  eauto.
  inv H. apply uniq_app in H25. destruct H25. auto.
  (* inv H. auto.*)
  rewrite <- H21 in *. eauto.

  contradiction.

  inversion H22.

  (* wrong message id - ignored *)
  inversion H2.  
  assert (t0 = t).
  (* Check map_in_uniq_inv. *)
  eapply map_in_uniq_inv;  eauto.
  inv H. apply uniq_app in H17. destruct H17. auto.
  (* inv H. auto.*)
  rewrite <- H13 in *. eauto.
  inversion H10. auto.

  inversion H14.
Qed.


Lemma tab_eq_prop :
  forall (t1 t2:tab), t1 = t2 \/ t1 <> t2.
Proof.
  intros.
  assert ({t1 = t2} + {t1 <> t2}).
  apply tabeq.

  inversion H. left. auto.
  right. auto.
Qed.


Lemma fold_tab_agree :
  forall t0 t1 (t:tab),
  (t0 = (Some t) <-> t1 = (Some t)) ->
  (t0 = (Some t) /\ t1 = (Some t)) \/ (t0 <> (Some t) /\ t1 <> (Some t)).
Proof.
  intros.
  inversion H.
  
  destruct t0. destruct t1.
  assert (t0 = t \/ t0 <> t).
  apply tab_eq_prop.
  destruct H2.
  rewrite H2 in *.
  left.
  split.
  auto.
  apply H0. auto.

  right.
  split. unfold not in *. intros.
  destruct H2. inversion H3.  auto.

  unfold not in *. intros.
  destruct H2. 
  assert (Some t0 = Some t).
  apply H1. auto.

  inversion H2; auto.
  
  right.
  split.
  unfold not; intros.
  apply H0 in H2. inversion H2.

  unfold not; intros.
  inversion H2.

  right.
  unfold not.
  split.
  intros. inversion H2.
  intros. apply H1 in H2. inversion H2.
Qed.

(*
   1) when the tab in discussion is the current tab : 0
   2) and the response is *NOT* to a cookie process : 0
*)
Lemma Tab_NI_not_cur_tab_not_to_cookie:
  forall tr1 tr2 req rsp1 rsp2 t,
  procs_distinct tr1 ->
  procs_distinct tr2 ->
  proj_useract req = nil ->
  from_tab t req ->
  In t (cur_tabs tr1) ->
  In t (cur_tabs tr2) ->
  cur_tab tr1 <> Some t ->
  cur_tab tr2 <> Some t ->
  ~ (exists c, exists m, rsp1 = WroteCMsg c m) -> 
  True ->
  (* ~ (exists c, exists m, rsp2 = WroteCMsg c m) -> *)
  KStep tr1 req rsp1 ->  
  KStep tr2 req rsp2 ->
  rsp1 = rsp2.
Proof.
  intros.
  inv H9; try (
    econstructor; eauto;
    unfold classify_user_cmd in *;
    try rewrite H8;
    try rewrite H9;
    try rewrite H10;
    try rewrite <- H11;
    try apply cproc_distinct_cur_proc;
    auto; fail
  ).

  (* Mktab *)
  rewrite proj_useract_MkTab in H1.
  rewrite proj_useract_ReadFile_true in H1.
  discriminate H1.
  destruct ok. eapply addtab_ctrl_key; eauto.

  (* Mktab  + MkCProc *)
  rewrite proj_useract_MkCProc in H1.
  rewrite proj_useract_MkTab in H1.
  rewrite proj_useract_ReadFile_true in H1.
  discriminate H1.
  destruct ok. eapply addtab_ctrl_key; eauto.

  (* Switch Tab *)
  rewrite proj_useract_ReadFile_true in H1.
  discriminate H1.
  destruct ok. eapply switchtab_ctrl_key; eauto.

  (* KeyPress *)
  inversion H2. inversion H13. 
 
  (* MousePress *)
  inversion H2. inversion H13. inversion H17.

  (* ignore *)

  (* we'll have to think about two cases -- 1) ok is a control key to
     be ignored. -- not possible.  2) ok it NOT a control key, but
     ignored -- no tab must exist there. But it's not- *)
  
  (* 1 *)
  inversion H2. inversion H13.

  (* readmsg t followed by wget *)
  (* econstructor; eauto. *)
  inversion H2. inversion H13. inversion H17. inversion H21.
  assert (t0 = t).
  (* Check map_in_uniq_inv. *)
  eapply map_in_uniq_inv;  eauto.
  inv H. apply uniq_app in H28. destruct H28. auto.
  (* inv H. auto.*)
  rewrite <- H24 in *.

  inversion H10.
  assert (t0 = t5).
  Check map_in_uniq_inv.
  eapply map_in_uniq_inv with (l := cur_tabs tr2); eauto. 
  inv H0. apply uniq_app in H40. destruct H40. auto.
  rewrite <- H39 in *. auto.
  inversion H25.

  (* readmsg t : navigation action *)
  simpl in H1. inversion H1.  
  simpl in H1. inversion H1.  

  (* navigation : when the user doesn't endorse it *)
  simpl in H1. inversion H1. 
  simpl in H1. inversion H1.
  
  (* send socket - socket allowed to a same sub-domain *)
  inversion H2. inversion H15. inversion H16. inversion H19.
  assert (t0 = t).
  (* Check map_in_uniq_inv. *)
  eapply map_in_uniq_inv;  eauto.
  inv H. apply uniq_app in H27. destruct H27. auto.
  (* inv H. auto.*)
  rewrite <- H23 in *.

  inversion H10.
  assert (t0 = t4).
  eapply map_in_uniq_inv with (l := cur_tabs tr2); eauto. 
  inv H0. apply uniq_app in H39. destruct H39. auto.
  rewrite <- H38 in *. auto.
  assert (host = host0).
  eapply la_eq_same; eauto.
  rewrite <- H39 in *. auto.

  assert (t0 = t4).
  eapply map_in_uniq_inv with (l := cur_tabs tr2); eauto. 
  inv H0. apply uniq_app in H39. destruct H39. auto.
  rewrite <- H38 in *. auto.
  assert (host = host0).
  eapply la_eq_same; eauto.
  rewrite <- H39 in *. auto.
  contradiction.
  
  inversion H24.

  (* send socket - socket allowed to a same sub-domain *)
  inversion H2. inversion H15. inversion H16. inversion H19.
  assert (t0 = t).
  (* Check map_in_uniq_inv. *)
  eapply map_in_uniq_inv;  eauto.
  inv H. apply uniq_app in H27. destruct H27. auto.
  (* inv H. auto.*)
  rewrite <- H23 in *.

  inversion H10.
  assert (t0 = t4).
  eapply map_in_uniq_inv with (l := cur_tabs tr2); eauto. 
  inv H0. apply uniq_app in H39. destruct H39. auto.
  rewrite <- H38 in *. auto.
  assert (host = host0).
  eapply la_eq_same; eauto.
  rewrite <- H39 in *. auto.
  contradiction.

  assert (t0 = t4).
  eapply map_in_uniq_inv with (l := cur_tabs tr2); eauto. 
  inv H0. apply uniq_app in H39. destruct H39. auto.
  rewrite <- H38 in *. auto.
  inversion H24.

  (* t2k set cookie *)
  destruct H7.
  econstructor; eauto.

  (* t2k set cookie -- ignore *)
  (* econstructor; eauto. *)
  inversion H2. inversion H14. inversion H18.
  assert (t0 = t).
  (* Check map_in_uniq_inv. *)
  eapply map_in_uniq_inv;  eauto.
  inv H. apply uniq_app in H25. destruct H25. auto.
  (* eapply cur_tab_in_cur_tabs; eauto. *)
  rewrite <- H21 in *. eauto.

  inversion H10.
  assert (t0 = t4).
  eapply map_in_uniq_inv with (l := cur_tabs tr2); eauto. 
  inv H0. apply uniq_app in H38. destruct H38. auto.
  rewrite <- H37 in *. auto.
  contradiction.
  auto.
  inversion H22.

  (* c->k set cookie. *)
  inversion H2. inversion H13. inversion H17.
  (* attack the point that t cannot be the same as c *)
  inv H.
  assert (t2k t <> c2k c).
  eapply uniq_map_noteq; eauto.
  rewrite H21 in H. destruct H; auto.
  inversion H21.

  (* t2k get cookie *)
  destruct H7.
  econstructor; eauto.

  (* c2t get cookie *)
  inversion H2. inversion H16. inversion H20.
  (* attack the point that t cannot be the same as c *)
  inv H.
  assert (t2k t <> c2k c).
  eapply uniq_map_noteq; eauto.
  rewrite H24 in H. destruct H; auto.
  inversion H24.

  (* c2t get cookie -- ignored *)
  inversion H2. inversion H16. inversion H20.
  (* attack the point that t cannot be the same as c *)
  inv H.
  assert (t2k t <> c2k c).
  eapply uniq_map_noteq; eauto.
  rewrite H24 in H. destruct H; auto.
  inversion H24.

  (* c2t get cookie - ignored *)
  inversion H2. inversion H14. inversion H18.
  (* attack the point that t cannot be the same as c *)
  inv H.
  assert (t2k t <> c2k c).
  eapply uniq_map_noteq; eauto.
  rewrite H22 in H. destruct H; auto.
  inversion H22.

  (* display message *)
  (* econstructor; eauto. *)
  inversion H2.  inversion H14. inversion H18.
  assert (t0 = t).
  (* Check map_in_uniq_inv. *)
  eapply map_in_uniq_inv;  eauto.
  inv H. apply uniq_app in H25. destruct H25. auto.
  (* inv H. auto.*)
  rewrite <- H21 in *. contradiction.
  
  inversion H22.

  (* display message - ignored *)
  (* econstructor; eauto. *)
  inversion H2.  inversion H14. inversion H18.
  assert (t0 = t).
  (* Check map_in_uniq_inv. *)
  eapply map_in_uniq_inv;  eauto.
  inv H. apply uniq_app in H25. destruct H25. auto.
  (* inv H. auto.*)
  rewrite <- H21 in *. 

  inversion H10.
  assert (t0 = t4).
  eapply map_in_uniq_inv with (l := cur_tabs tr2); eauto. 
  inv H0. apply uniq_app in H36. destruct H36. auto.
  rewrite <- H35 in *. auto.
  contradiction.
  auto.
  inversion H22.

  (* wrong message id - ignored *)
  inversion H2.  
  assert (t0 = t).
  (* Check map_in_uniq_inv. *)
  eapply map_in_uniq_inv;  eauto.
  inv H. apply uniq_app in H17. destruct H17. auto.
  (* inv H. auto.*)
  rewrite <- H13 in *. eauto.
  inversion H10. auto.

  inversion H14.
Qed.


Lemma WroteCMsg_payload_inv :
  forall c1 c2 m1 m2,
    WroteCMsg c1 m1 = WroteCMsg c2 m2 -> m1 = m2.
Proof.
  intros.
  destruct m1. destruct m2.
  inversion H. auto.
  inversion H.

  destruct m2.
  inversion H.
  inversion H; auto.
Qed.


(*
   1) when the tab in discussion is the current tab : 1
   1-1) or the tab in discussion is not the current tab : 0
   2) and the response is to a cookie process : 1
*)
Lemma Tab_NI_to_cookie:
  forall tr1 tr2 req rsp1 rsp2 t c1 c2 m1 m2,
  procs_distinct tr1 ->
  procs_distinct tr2 ->
  proj_useract req = nil ->
  from_tab t req ->
  In t (cur_tabs tr1) ->
  In t (cur_tabs tr2) ->
  cur_cproc (get_topdomain_tab (tab_origin_url t)) tr1 = Some c1 ->
  cur_cproc (get_topdomain_tab (tab_origin_url t)) tr2 = Some c2 ->
  KStep tr1 req rsp1 ->  
  KStep tr2 req rsp2 ->
  rsp1 = WroteCMsg c1 m1 ->
  rsp2 = WroteCMsg c2 m2 ->
  m1 = m2.
Proof.
  intros.
  inv H7; try (
    econstructor; eauto;
    unfold classify_user_cmd in *;
    try rewrite H7;
    try rewrite H8;
    try rewrite H9;
    try rewrite <- H10;
    try apply cproc_distinct_cur_proc;
    auto; fail
  ).

  (* Mktab *)
  rewrite proj_useract_MkTab in H1.
  rewrite proj_useract_ReadFile_true in H1.
  discriminate H1.
  destruct ok. eapply addtab_ctrl_key; eauto.

  (* Mktab  + MkCProc *)
  rewrite proj_useract_MkCProc in H1.
  rewrite proj_useract_MkTab in H1.
  rewrite proj_useract_ReadFile_true in H1.
  discriminate H1.
  destruct ok. eapply addtab_ctrl_key; eauto.

  (* Switch Tab *)
  rewrite proj_useract_ReadFile_true in H1.
  discriminate H1.
  destruct ok. eapply switchtab_ctrl_key; eauto.

  (* KeyPress *)
  inversion H2. inversion H10.
 
  (* MousePress *)
  inversion H2. inversion H10. inversion H16.

  (* ignore *)
  inversion H2. inversion H10.

  (* readmsg t followed by wget *)
  inv H14. destruct m1; inversion H17.

  (* navigation : when the user doesn't endorse it *)
  simpl in H1. inversion H1.
  simpl in H1. inversion H1.
  simpl in H1. inversion H1.

  (* send socket - socket allowed to a same sub-domain *)
  inv H16. inv H16.
  destruct m1; repeat inversion H19.

  (* t2k set cookie *)
  inv H8.
  destruct m1; destruct m2; inv H17; auto.
  inversion H27.

  (* t2k set cookie -- ignore *)
  inversion H15.
  
  (* c->k set cookie. *)
  inv H2. inv H10. inv H9.
  inv H.
  assert (t2k t <> c2k c).
  eapply uniq_map_noteq; eauto.
  rewrite H10 in H. destruct H; auto.
  inversion H10.

  (* t2k get cookie *)
  inv H2. inv H10. inv H9.
  assert (t0 = t).
  (* Check map_in_uniq_inv. *)
  eapply map_in_uniq_inv;  eauto.
  inv H. apply uniq_app in H7. destruct H7. auto.
  rewrite <- H2 in *. eauto.

  inv H8.
  destruct m1; destruct m2; try inv H16.
  simpl in H27. inv H27. inv H27.
  unfold k2c_msg_payload in H23.
  rewrite <- H23.

  (* t2k get cookie *)
  assert (t1 = t).
  (* Check map_in_uniq_inv. *)
  eapply map_in_uniq_inv;  eauto.
  inv H0. apply uniq_app in H9. destruct H9. auto.
  inv H2. auto.

  inv H10.

  (* c2t get cookie *)
  inv H2.  inv H10. inv H9.   
  (* attack the point that t cannot be the same as c *)
  inv H.
  assert (t2k t <> c2k c).
  eapply uniq_map_noteq; eauto.
  rewrite H10 in H. destruct H; auto.
  inversion H10.

  (* c2t get cookie -- ignored *)
  inv H2.  inv H10. inv H9.   
  (* attack the point that t cannot be the same as c *)
  inv H.
  assert (t2k t <> c2k c).
  eapply uniq_map_noteq; eauto.
  rewrite H10 in H. destruct H; auto.
  inversion H10.

  (* c2t get cookie - ignored *)
  inv H2.  inv H10. inv H9.   
  (* attack the point that t cannot be the same as c *)
  inv H.
  assert (t2k t <> c2k c).
  eapply uniq_map_noteq; eauto.
  rewrite H10 in H. destruct H; auto.
  inversion H10.

  (* display message *)
  inv H15. inv H15.
  
  (* display message - ignored *)
  inv H15.
Qed.


Lemma KStep_rsp_WroteCMsg_or_not:
  forall req rsp tr,
    KStep tr req rsp ->
    ~ (exists c, exists m, rsp = WroteCMsg c m) \/ (exists c, exists m, rsp = WroteCMsg c m).
Proof.
  intros.
  inversion H;
  try (
    left;
    unfold not; intros;
    inversion H5;
    inversion H6;
    inversion H7;
    fail      
  );
  try (
    left;
    unfold not; intros;
    inversion H6;
    inversion H7;
    inversion H8;
    fail      
  );
  try (
    left;
    unfold not; intros;
    inversion H4;
    inversion H5;
    inversion H6;
    fail      
  );
  try (
    left;
    unfold not; intros;
    inversion H7;
    inversion H8;
    inversion H9;
    fail      
  );
  try (
    left;
    unfold not; intros;
    inversion H4;
    inversion H5;
    inversion H6;
    destruct x0; repeat inversion H14;
    fail
  );
  try (
    left;
    unfold not; intros;
    inversion H6;
    inversion H7;
    inversion H8;
    destruct x0; repeat inversion H16;
    fail
  );
  try (
    right;
    econstructor; eauto
    fail
  ).

  right.
  econstructor. eauto.

  left.
  unfold not; intros.
  inversion H4. inversion H5.
  assert (K2TSetCookieActions c (cur_tabs tr) cookie_msg <> WroteCMsg x x0).
  apply K2TSetCookieActions_not_WroteCMsg.
  contradiction.

  right.
  econstructor. eauto.

  left.
  unfold not; intros.
  inversion H7. inversion H8.
  inversion H9. destruct x0. inversion H17. inversion H17.
Qed.


Lemma exists_must_exist :
  forall req rsp1 rsp2 tr1 tr2 t, 
    procs_distinct tr1 ->
    procs_distinct tr2 ->    
    from_tab t req ->
    In t (cur_tabs tr1) ->
    In t (cur_tabs tr2) ->
    KStep tr1 req rsp1 -> 
    KStep tr2 req rsp2 -> 
    (exists c, exists m,  rsp1 = WroteCMsg c m) ->
    (exists c, exists m,  rsp2 = WroteCMsg c m).
Proof.
  intros.
  inv H4; try ( inv H6; inversion H4; inversion H6; fail).

  inv H6. inv H4. inversion H6. destruct x0; repeat inversion H14.
  inv H6. inv H4. inversion H6. destruct x0; repeat inversion H14.
  inv H6. inv H4. inversion H6. destruct x0; repeat inversion H14.
  inv H6. inv H4. inversion H6. destruct x0; repeat inversion H16.

  inv H1. inv H12. inv H11.
  assert (t0 = t).
  (* Check map_in_uniq_inv. *)
  eapply map_in_uniq_inv;  eauto.
  inv H. apply uniq_app in H4. destruct H4. auto.

  inv H5. econstructor; eauto.
  
  assert (t1 = t).
  eapply map_in_uniq_inv;  eauto.
  inv H0. apply uniq_app in H5. destruct H5. auto.
  rewrite <- H1 in *. 
  contradiction.

  inv H12.

  inv H6. inv H4.
  apply K2TSetCookieActions_not_WroteCMsg in H6. contradiction.

  inv H1. inv H11. inv H10.
  assert (t0 = t).
  (* Check map_in_uniq_inv. *)
  eapply map_in_uniq_inv;  eauto.
  inv H. apply uniq_app in H4. destruct H4. auto.
  rewrite <- H1 in *.

  inv H5. econstructor; eauto.
  inv H11.

  inv H6. inv H4. inv H6. destruct x0; repeat inversion H17.
Qed.

(*
Theorem Tab_NI_ideal:
  forall tr1 tr2 req rsp1 rsp2 t,
  TraceOK tr1 ->
  TraceOK tr2 ->
  from_tab t req ->
  (cur_tab tr1 = Some t <-> cur_tab tr2 = Some t)
  KStep tr1 req rsp1 ->  
  KStep tr2 req rsp2 ->
  rsp1 = rsp2 \/ 
  (exists m, rsp1 = WroteCMsg (get_cproc_for t tr1) m /\ 
    rsp2 = WroteCMsg (get_cproc_for t tr2) m).
Proof.
  admit.
Qed.
*)


Theorem Tab_noninteference:
  forall tr1 tr2 req rsp1 rsp2 t c1 c2 m1 m2,
  procs_distinct tr1 ->
  procs_distinct tr2 ->
  proj_useract req = nil ->
  from_tab t req ->
  In t (cur_tabs tr1) ->
  In t (cur_tabs tr2) ->
  cur_cproc (get_topdomain_tab (tab_origin_url t)) tr1 = Some c1 ->
  cur_cproc (get_topdomain_tab (tab_origin_url t)) tr2 = Some c2 ->
  (cur_tab tr1 = Some t /\ cur_tab tr2 = Some t) \/ (cur_tab tr1 <> Some t /\ cur_tab tr2 <> Some t) ->
  KStep tr1 req rsp1 ->  
  KStep tr2 req rsp2 ->
  rsp1 = rsp2 \/ ((rsp1 = WroteCMsg c1 m1 /\ rsp2 = WroteCMsg c2 m2) -> m1 = m2).
Proof.
  intros.
  destruct H7.
  destruct H7.
  
  (* when the tab is focused *)
  assert (~ (exists c, exists sm, rsp1 = WroteCMsg c sm) \/ (exists c, exists sm, rsp1 = WroteCMsg c sm)).
  eapply KStep_rsp_WroteCMsg_or_not; eauto.

  assert (~ (exists c, exists sm, rsp2 = WroteCMsg c sm) \/ (exists c, exists sm, rsp2 = WroteCMsg c sm)).
  eapply KStep_rsp_WroteCMsg_or_not; eauto.

  destruct H11. destruct H12.
  left.
  eapply Tab_NI_cur_tab_not_to_cookie with (tr1 := tr1) (tr2 := tr2); eauto.
  
  assert ((exists c : cproc, exists sm : k2c_msg, rsp1 = WroteCMsg c sm)).
  eapply exists_must_exist with (tr1 := tr2) (tr2 := tr1); eauto.
  contradiction.

  destruct H12.

  assert ((exists c : cproc, exists sm : k2c_msg, rsp2 = WroteCMsg c sm)).
  eapply exists_must_exist with (tr1 := tr1) (tr2 := tr2); eauto.
  contradiction.

  right.
  intros.
  destruct H13.

  Check Tab_NI_to_cookie.
  eapply Tab_NI_to_cookie with (tr1:=tr1)(tr2:=tr2)(m1:=m1)(m2:=m2); eauto.


  assert (~ (exists c, exists sm, rsp1 = WroteCMsg c sm) \/ (exists c, exists sm, rsp1 = WroteCMsg c sm)).
  eapply KStep_rsp_WroteCMsg_or_not; eauto.

  assert (~ (exists c, exists sm, rsp2 = WroteCMsg c sm) \/ (exists c, exists sm, rsp2 = WroteCMsg c sm)).
  eapply KStep_rsp_WroteCMsg_or_not; eauto.

  destruct H7.
  destruct H10. destruct H11.
  left.
  eapply Tab_NI_not_cur_tab_not_to_cookie with (tr1 := tr1) (tr2 := tr2); eauto.

  assert ((exists c : cproc, exists sm : k2c_msg, rsp1 = WroteCMsg c sm)).
  eapply exists_must_exist with (tr1 := tr2) (tr2 := tr1); eauto.
  contradiction.

  destruct H11.

  assert ((exists c : cproc, exists sm : k2c_msg, rsp2 = WroteCMsg c sm)).
  eapply exists_must_exist with (tr1 := tr1) (tr2 := tr2); eauto.
  contradiction.

  right.
  intros.
  destruct H13.

  Check Tab_NI_to_cookie.
  eapply Tab_NI_to_cookie with (tr1:=tr1)(tr2:=tr2)(m1:=m1)(m2:=m2); eauto.
Qed.

(*
Lemma K2TSetCookieActions_inv :
  forall t0 pts t cookie, 
    la_eq (get_topdomain_tab (tab_origin_url t)) (get_topdomain_cookie cookie) ->
    t <> t0 ->
    K2TSetCookieActions t0 (pts ++ t :: nil) cookie = 
    (WriteN (k2t t) (length_in_size cookie) cookie
      :: WriteN (k2t t) (size 4) (pos2la4 (length_in_size cookie))
      :: WriteN (k2t t) (size 1) ("016"%char :: nil)
      :: K2TSetCookieActions t0 pts cookie).
Proof.
  induction pts.
  intros. simpl.

  destruct (laeq (get_topdomain_tab (tab_origin_url t)) (get_topdomain_cookie cookie)).
  destruct (tabeq t0 t).
  rewrite e0 in H0. destruct H0; auto.
  auto.
  destruct n.
  eapply la_eq_same; eauto. eapply la_eq_refl.

  intros.
  simpl.
  destruct (laeq (get_topdomain_tab (tab_origin_url a)) (get_topdomain_cookie cookie)); simpl.
  destruct (tabeq t0 a); simpl.
  rewrite IHpts.
  simpl. auto. auto. auto.

  rewrite IHpts.
  simpl. auto. auto. auto.

  destruct (tabeq t0 a); simpl. 
  apply IHpts. auto. auto.
  apply IHpts. auto. auto.
Qed.



Lemma K2TSetCookieActions_inv2 :
  forall t0 pts t cookie, 
    ~ la_eq (get_topdomain_tab (tab_origin_url t)) (get_topdomain_cookie cookie) \/ 
    t0 = t ->
    K2TSetCookieActions t0 (pts ++ t :: nil) cookie = K2TSetCookieActions t0 pts cookie.
Proof.
  induction pts.
  intros. simpl.

  destruct (laeq (get_topdomain_tab (tab_origin_url t)) (get_topdomain_cookie cookie)); simpl.
  destruct (tabeq t0 t); simpl; auto.

  destruct H. 
  destruct H. rewrite e. apply la_eq_refl.
  
  rewrite H in n. destruct n; auto.
  auto.

  destruct (tabeq t0 t); simpl; auto.
  
  intros.
  simpl.
  destruct (laeq (get_topdomain_tab (tab_origin_url a)) (get_topdomain_cookie cookie)); simpl.
  destruct (tabeq t0 a); simpl; auto.
  rewrite IHpts.
  simpl. auto. auto.

  destruct (tabeq t0 a); simpl; auto.
Qed.  
*)

(* kernel impl *)

Record kstate : Set :=
  mkst { ctab  : option tab
       ; ctabs : list tab
       ; cprocs: list cproc
       ; ktr   : [Trace] 
       }.

(*
   kcorrect consists of the following:

   1) stdin & stdout & gout should be open.
   2) thandles (ctabs s) : the current tabs' input and ouput channels should be op.
   3) the current tab from the trace is the same as what is found in the state.
   4) the current tabs from the trace is the same as what are found in the state.
   5) TraceOK tr is true (see TraceOK)
   6) tabs_distinct tr : all the tabs are distinct from each other.
   7) SOP_OK tr : the tabs whose origins are different cannot talk to each other.
*)


(* cookie isolation *)

Lemma la_eq_eq:
  forall x y, la_eq x y -> x = y.
Proof.
  induction x; simpl; intros.
  inv H; auto.
  inv H. f_equal; auto.
Qed.


Lemma eq_la_eq:
  forall x y, x = y -> la_eq x y.
Proof.
  induction x; simpl; intros.
  inv H; constructor; auto.
  inv H; constructor; auto.
Qed.


Transparent WroteCMsg.
Transparent WroteMsg.


Lemma uniq_cproc_lkup:
  forall cs c1 c2,
  uniq (map k2c cs) ->
  In c1 cs ->
  In c2 cs ->
  k2c c1 = k2c c2 ->
  c1 = c2.
Proof.
  induction cs; simpl; intros.
  contradiction.
  destruct H0; destruct H1; subst; auto.
  inv H. destruct H5. rewrite H2. apply in_map; auto.
  inv H. destruct H5. rewrite <- H2. apply in_map; auto.
  inv H; auto.
Qed.

Lemma uniq_tab_lkup:
  forall ts t1 t2,
  uniq (map k2t ts) ->
  In t1 ts ->
  In t2 ts ->
  k2t t1 = k2t t2 ->
  t1 = t2.
Proof.
  induction ts; simpl; intros.
  contradiction.
  destruct H0; destruct H1; subst; auto.
  inv H. destruct H5. rewrite H2. apply in_map; auto.
  inv H. destruct H5. rewrite <- H2. apply in_map; auto.
  inv H; auto.
Qed.


Lemma uniq_tab_lkup2:
  forall ts t1 t2,
  uniq (map t2k ts) ->
  In t1 ts ->
  In t2 ts ->
  t2k t1 = t2k t2 ->
  t1 = t2.
Proof.
  induction ts; simpl; intros.
  contradiction.
  destruct H0; destruct H1; subst; auto.
  inv H. destruct H5. rewrite H2. apply in_map; auto.
  inv H. destruct H5. rewrite <- H2. apply in_map; auto.
  inv H; auto.
Qed.


Inductive cookie_set_ok : positive -> list ascii -> Trace -> cproc -> Prop :=
  | cookie_set_ok_intro:
      forall t c n cookie,
      la_eq (get_topdomain_tab (tab_origin_url t)) (cproc_domain c) ->
      cookie_set_ok n cookie (ReadMsg t (SetCookie n cookie)) c.


Lemma eq_rev_eq (A:Type):
  forall (ls:list A) (ls':list A), ls = ls' -> rev ls = rev ls'.
Proof.
  intros. rewrite H. auto.
Qed.


Lemma rev_app_distr (A:Type): forall x y:list A, rev (x ++ y) = rev y ++ rev x.
Proof.
  induction x as [| a l IHl].
  destruct y as [| a l].
  simpl.
  auto.

  simpl.
  rewrite app_nil_r; auto.

  intro y.
  simpl.
  rewrite (IHl y).
  rewrite app_assoc; trivial.
Qed.


Lemma no_xdom_cookie_set:
  forall tr req c s cookie,
  cprocs_distinct tr ->
  In c (cur_cprocs tr) ->
  KStep tr req (WroteCMsg c (K2CSetCookie s (cookie))) ->
  cookie_set_ok s cookie req c.
Proof.
  intros. inv H1. 
  econstructor. 
  apply cur_cproc_domain in H13.

  assert (c0 = c).
  eapply uniq_cproc_lkup; eauto.
  inv H; auto. rewrite H1 in *.
  rewrite H13. auto.
  
  assert (K2TSetCookieActions c0 (cur_tabs tr) cookie_msg <> WroteCMsg c (K2CSetCookie s cookie)).
  apply K2TSetCookieActions_not_WroteCMsg.  rewrite H2 in H1. destruct H1; auto.
Qed.

(*
Lemma no_xdom_cookie_set:
  forall tr req c n cookie,
  cprocs_distinct tr ->
  In c (cur_cprocs tr) ->
  KStep tr req (K2TSetCookieActions (cur_tabs tr) cookie) ->
  cookie_set_ok n cookie req c.
Proof.
  intros. inv H1; try Unify; 
  unfold WroteCMsg in H2;
  apply eq_rev_eq in H2;
  rewrite rev_app_distr in H2;
  simpl in H2; try discriminate.

  

  unfold WroteCMsg in H2.
  rewrite rev_app_distr in H2.
  simpl in H2. inversion H2.

  cut (c = c0); intros; subst.
  constructor; auto. 
  apply cur_cproc_domain in H8.
  rewrite H8; auto.
  eapply uniq_cproc_lkup; eauto.
  inv H; auto.
Qed.
*)

Inductive cookie_set_position_ok : Trace -> Prop :=
  | cookie_set_pos_ok_nil:
      cookie_set_position_ok nil
  | cookie_set_pos_ok_no_set:
      forall tr req rsp,
      cookie_set_position_ok tr ->
      KStep tr req rsp ->
      (forall n cookie c, req <> WroteCMsg c (K2CSetCookie n cookie)) ->
      (forall n cookie c, rsp <> WroteCMsg c (K2CSetCookie n cookie)) ->
      cookie_set_position_ok (rsp ++ req ++ tr)
  | cookie_set_pos_set:
      forall c n cookie tr req rsp,
      cookie_set_position_ok tr ->
      KStep tr req rsp ->
      cookie_set_ok n cookie req c ->
      rsp = (WroteCMsg c (K2CSetCookie n cookie)) ->
      cookie_set_position_ok (rsp ++ req ++ tr).


Lemma cookie_set_pos_ok:
  forall tr,
  TraceOK tr ->
  cookie_set_position_ok tr.
Proof.
  intros. induction H.
  constructor; auto.
  inv H0; try (
    repeat (econstructor; eauto);
    intros; try discriminate;
    fail
  ).

  eapply cookie_set_pos_set; eauto.
  econstructor; eauto. econstructor; eauto.
  apply cur_cproc_domain in H4.
  rewrite<- H4 in H3.
  eauto.

  eapply cookie_set_pos_ok_no_set; eauto.
  econstructor; eauto.

  intros; discriminate.
  intros.

  apply K2TSetCookieActions_not_WroteCMsg.

  econstructor; eauto.
  eapply Kstep_cookie_get_c2k_error_bad_tab_id; eauto.
  intros; discriminate.
  intros; discriminate.
Qed.


Inductive cookie_get_ok : list ascii -> Trace -> tab -> Prop :=
  | cookie_get_ok_intro:
      forall n t c cookie,
      la_eq (get_topdomain_tab (tab_origin_url t)) (cproc_domain c) ->
      cookie_get_ok (get_cookie_content cookie) (ReadCMsg c (C2KResultCookie n cookie)) t.


Lemma no_xdom_cookie_get:
  forall tr req t cookie,
  tabs_distinct tr ->
  In t (cur_tabs tr) ->
  KStep tr req
        (WroteMsg t (ResultCookie (length_in_size cookie) cookie)) ->
  cookie_get_ok cookie req t.
Proof.
  intros.
  inv H1.
  assert (K2TSetCookieActions c (cur_tabs tr) cookie_msg <>
       WroteMsg t (ResultCookie (length_in_size cookie) cookie)).
  apply K2TSetCookieActions_not_ResultCookie.
  rewrite H2 in H1. destruct H1; auto.

  assert (t0 = t).
  eapply map_in_uniq_inv; eauto. inv H; auto.
  rewrite H1 in *. econstructor.
  apply cur_cproc_return_requested_domain in H13.
  apply eq_la_eq; auto.
Qed.


Inductive cookie_get_position_ok : Trace -> Prop :=
  | cookie_get_pos_ok_nil:
      cookie_get_position_ok nil
  | cookie_get_pos_ok_no_set:
      forall tr req rsp,
      cookie_get_position_ok tr ->
      KStep tr req rsp ->
      (forall t cookie, req <> WroteMsg t (ResultCookie (length_in_size cookie) cookie)) ->
      (forall t cookie, rsp <> WroteMsg t (ResultCookie (length_in_size cookie) cookie)) ->
      cookie_get_position_ok (rsp ++ req ++ tr)
  | cookie_get_pos_get:
      forall t cookie tr req rsp,
      cookie_get_position_ok tr ->
      KStep tr req rsp ->
      cookie_get_ok cookie req t ->
      rsp = WroteMsg t (ResultCookie (length_in_size cookie) cookie) ->
      cookie_get_position_ok (rsp ++ req ++ tr).


Lemma cookie_get_pos_ok:
  forall tr,
  TraceOK tr ->
  cookie_get_position_ok tr.
Proof.
  intros. induction H.
  constructor; auto.
  inv H0; try (
    repeat (econstructor; eauto);
    intros; try discriminate;
    fail
  ).

  eapply cookie_get_pos_ok_no_set; eauto.
  econstructor; eauto. 
  
  intros; discriminate.
  intros. apply K2TSetCookieActions_not_ResultCookie.

  eapply cookie_get_pos_get; eauto.
  econstructor; eauto. econstructor; eauto.
  apply cur_cproc_domain in H4. rewrite H4; auto.
  apply same_la_eq.

  econstructor; eauto.
  eapply Kstep_cookie_get_c2k_error_bad_tab_id; eauto.
  intros; discriminate.
  intros; discriminate.
Qed.


Inductive hilited_string : list ascii -> Trace -> Prop :=
  | hilited_string_hilite:
      forall s tr,
      hilited_string s (WriteStrFile stdout ("@"%char :: s ++ newline :: nil) :: tr)
  | hilited_string_pres:
      forall a s tr,
      hilited_string s tr ->
      (forall s, a <> (WriteStrFile stdout ("@"%char :: s ++ newline :: nil))) ->
      hilited_string s (a :: tr).


Transparent Paint.


Lemma paint_hilites_focus:
  forall tabs t tr,
  In t tabs ->
  hilited_string (tab_origin_url t) (Paint tabs t ++ tr).
Proof.
  induction tabs; intros; simpl. inv H.
  inv H; simpl; unfold screen; simpl;
    repeat (constructor; auto);
    repeat (simpl; intros; discriminate).
Qed.


Lemma paint_hilites_curtab:
  forall t tr,
  cur_tab tr = Some t ->
  hilited_string (tab_origin_url t) (Paint (cur_tabs tr) t ++ tr).
Proof.
  intros. apply paint_hilites_focus.
  eapply cur_tab_in_cur_tabs; eauto.
Qed.


Lemma endorse_pres_hilite:
  forall tr s url,
  hilited_string s tr ->
  hilited_string s (WroteEndorseMsg url :: tr).
Proof.
  intros. apply hilited_string_pres; auto.
  unfold WroteEndorseMsg, endorsemsg; simpl.
  repeat intro. inv H0.
Qed.


Inductive stdout_cur_dom : Trace -> Prop :=
  | stdout_cur_dom_nil:
      stdout_cur_dom nil
  | stdout_cur_dom_nowrite:
      forall a tr,
      stdout_cur_dom tr ->
      (forall s, a <> WriteStrFile stdout s) ->
      stdout_cur_dom (a :: tr)
  | stdout_cur_dom_clear:
      forall tr,
      stdout_cur_dom (Clear :: tr)
  | stdout_cur_dom_paint:
      forall t tr,
      cur_tab tr = Some t ->
      stdout_cur_dom (Paint (cur_tabs tr) t ++ tr)
  | stdout_cur_dom_endorse:
      forall url tr,
      stdout_cur_dom (WroteEndorseMsg url :: tr).


Lemma K2TSetCookieActions_nowrite :
  forall t0 a tabs cookie f s,
    In a (K2TSetCookieActions t0 tabs cookie) -> a <> WriteStrFile f s.
Proof.
  induction tabs.
  intros; simpl; auto.

  simpl. destruct a; intros; try discriminate.
  destruct (laeq (cproc_domain t0) (get_topdomain_tab (tab_origin_url a0))).

  apply in_app_iff in H.
  destruct H. eapply IHtabs; eauto.
  inv H; inv H0. inv H. destruct H.
  inv H. inv H.
  eapply IHtabs; eauto.
Qed.


Lemma K2TSetCookieActions_stdout_cur_dom :
  forall c tabs tr cookie, 
    stdout_cur_dom tr -> stdout_cur_dom (K2TSetCookieActions c tabs cookie ++ tr).
Proof.
  induction tabs.
  intros; simpl; auto.

  intros. simpl.
  simpl in H.
  destruct (laeq (cproc_domain c) (get_topdomain_tab (tab_origin_url a))); simpl; auto.
  (* destruct (tabeq t0 a); simpl; auto. *)

  rewrite app_assoc.
  apply IHtabs. unfold WroteMsg. simpl.
  repeat econstructor; eauto.

  repeat intros; discriminate.
  intros; discriminate.
  intros; discriminate.
Qed.

Transparent Clear.


Lemma uniq_mod_last:
  forall A B (f: A -> B) (xs : list A) (x: A),
  uniq (map f (xs ++ x :: nil)) ->
  uniq (map f xs).
Proof.
  induction xs; simpl; intros.
  constructor; auto.
  inv H. apply IHxs in H2.
  constructor; auto. intro.
  destruct H3. rewrite map_app.
  apply in_or_app. left; auto.
Qed.


Lemma classify_switch_tab:
  forall tr x t,
  classify_user_cmd x tr = USwitchTab t ->
  In t (cur_tabs tr).
Proof with try discriminate.
  unfold classify_user_cmd; simpl; intros.
  destruct (ascii_dec x "017")...
  destruct (ascii_dec x "018")...
  destruct (cur_tab tr)...

  destruct (select_tab_idx x)...
  destruct (nth_error (cur_tabs tr) n1) as []_eqn...
  apply nth_error_some_in in Heqe. inv H; auto.
  destruct (cur_tab tr)...
Qed.


Lemma classify_keypress:
  forall tr x t k,
  classify_user_cmd x tr = UKeyPress t k ->
  In t (cur_tabs tr).
Proof with try discriminate.
  unfold classify_user_cmd; simpl; intros.
  destruct (ascii_dec x "017")...
  destruct (ascii_dec x "018")...
  destruct (cur_tab tr)...
  destruct (select_tab_idx x)...
  destruct (nth_error (cur_tabs tr) n1)...
  destruct (cur_tab tr) as []_eqn...
  inv H. eapply cur_tab_in_cur_tabs; eauto.
Qed.


Lemma classify_mouse:
  forall tr x t,
  classify_user_cmd x tr = UMouseClick t ->
  In t (cur_tabs tr).
Proof with try discriminate.
  unfold classify_user_cmd; simpl; intros.
  destruct (ascii_dec x "017")...
  destruct (ascii_dec x "018")...
  destruct (cur_tab tr) as []_eqn...
  inv H. eapply cur_tab_in_cur_tabs; eauto.
  destruct (select_tab_idx x)...
  destruct (nth_error (cur_tabs tr) n1)...
  destruct (cur_tab tr)...
Qed.


Lemma tabs_distinct_not_mktab:
  forall a x,
  (forall t, a <> MkTab t) ->
  tabs_distinct (a :: x) ->
  tabs_distinct x.
Proof.
  intros.
  destruct a; try (
    inv H0; constructor; auto; fail
  ).
  destruct (H t); auto.
Qed.


Lemma tabs_distinct_paint:
  forall ts t x,
  tabs_distinct (Paint ts t ++ x) ->
  tabs_distinct x.
Proof.
  simpl; intros.
  apply tabs_distinct_not_mktab in H.
  apply tabs_distinct_not_mktab in H.
  apply tabs_distinct_not_mktab in H; auto.
  intros; discriminate.
  intros; discriminate.
  intros; discriminate.
Qed.


Lemma tabs_distinct_not_mktab_after:
  forall t a x,
  (forall t, a <> MkTab t) ->
  tabs_distinct (MkTab t :: a :: x) ->
  tabs_distinct (MkTab t :: x).
Proof.
  intros.
  destruct a; try (
    inv H0; simpl in *;
    constructor; auto;
    fail
  ).
  destruct (H t0); auto.
Qed.


Lemma cprocs_distinct_not_mkcproc:
  forall a x,
  (forall t, a <> MkCProc t) ->
  cprocs_distinct (a :: x) ->
  cprocs_distinct x.
Proof.
  intros.
  destruct a; try (
    inv H0; constructor; auto; fail
  ).
  destruct (H c); auto.
Qed.


Lemma cprocs_distinct_paint:
  forall ts t x,
  cprocs_distinct (Paint ts t ++ x) ->
  cprocs_distinct x.
Proof.
  simpl; intros.
  apply cprocs_distinct_not_mkcproc in H.
  apply cprocs_distinct_not_mkcproc in H.
  apply cprocs_distinct_not_mkcproc in H; auto.
  intros; discriminate.
  intros; discriminate.
  intros; discriminate.
Qed.


Lemma cproc_distinct_not_mkcproc_after:
  forall t a x,
  (forall t, a <> MkCProc t) ->
  cprocs_distinct (MkCProc t :: a :: x) ->
  cprocs_distinct (MkCProc t :: x).
Proof.
  intros.
  destruct a; try (
    inv H0; simpl in *;
    constructor; auto;
    fail
  ).
  destruct (H c); auto.
Qed.


Transparent ReadCMsg.
Transparent WroteGMsg.
Transparent ReadMsg.
Opaque Paint.


Lemma cur_dom_correct:
  forall tr,
  cprocs_distinct tr ->
  tabs_distinct tr ->
  TraceOK tr ->
  stdout_cur_dom tr.
Proof.
  intros. induction H1. constructor; auto.
  inv H2; unfold ReadCMsg, WroteGMsg; simpl in *;
  repeat (apply tabs_distinct_not_mktab in H0; [| repeat intro; discriminate]);
  repeat (apply tabs_distinct_not_mktab_after in H0; [| repeat intro; discriminate]);
  repeat (apply cprocs_distinct_not_mkcproc in H; [| repeat intro; discriminate]);
  repeat (apply cprocs_distinct_not_mkcproc_after in H; [| repeat intro; discriminate]);
  repeat match goal with
  | |- stdout_cur_dom (WriteN (k2t ?t) ?n ?s :: ?tr) =>
      apply stdout_cur_dom_nowrite; auto
  | |- stdout_cur_dom (WriteN (k2c ?t) ?n ?s :: ?tr) =>
      apply stdout_cur_dom_nowrite; auto
  | |- stdout_cur_dom (WriteN gout ?n ?s :: ?tr) =>
      apply stdout_cur_dom_nowrite; auto
  | |- stdout_cur_dom (Clear :: ?tr) =>
      apply stdout_cur_dom_clear; auto
  | |- stdout_cur_dom (ReadN ?f ?n ?s :: ?tr) =>
      apply stdout_cur_dom_nowrite; auto
  | |- stdout_cur_dom (MousePos ?s :: ?tr) =>
      apply stdout_cur_dom_nowrite; auto
  | |- stdout_cur_dom (Wget ?x ?y :: ?tr) =>
      apply stdout_cur_dom_nowrite; auto
  | |- stdout_cur_dom (Endorse ?x :: ?tr) =>
      apply stdout_cur_dom_nowrite; auto
  | |- stdout_cur_dom (WroteEndorseMsg ?x :: ?tr) =>
      apply stdout_cur_dom_endorse; auto
  | |- stdout_cur_dom (SendSocket ?x ?y ?z :: ?tr) =>
      apply stdout_cur_dom_nowrite; auto
  end;
  try (
    repeat intro;
    match goal with
    | H: WriteN (k2t ?t) _ _ = WriteN stdout _ _ |- _ =>
        inv H
    end;
    eapply tab_k2t_neq_stdout; eauto; simpl;
    apply in_or_app; simpl; auto
  );
  try (
    repeat intro;
    match goal with
    | H: WriteN (k2t ?t) _ _ = WriteN stdout _ _ |- _ =>
        inv H
    end;
    eapply tab_k2t_neq_stdout with (t := t'); eauto; simpl;
    apply in_or_app; simpl; auto
  );
  try (
    repeat intro;
    match goal with
    | H: WriteN (k2t ?t) _ _ = WriteN stdout _ _ |- _ =>
        inv H
    end;
    eapply tab_k2t_neq_stdout; eauto; simpl;
    match goal with
    | H: context[classify_user_cmd ?c ?tr] |- _ =>
        try apply classify_switch_tab in H;
        try apply classify_keypress in H;
        try apply classify_mouse in H
    end; auto
  );
  try (
    repeat intro; discriminate
  ).
  
  replace (cur_tabs tr ++ t :: nil)
     with (cur_tabs (MkTab t :: ReadFile stdin ok :: tr)).
  apply stdout_cur_dom_paint. auto.
  simpl. reflexivity.

  replace (cur_tabs tr ++ t :: nil)
     with (cur_tabs (MkCProc c :: MkTab t :: ReadFile stdin ok :: tr)).
  apply stdout_cur_dom_paint. auto.
  simpl. reflexivity.

  (* rewrite app_assoc. *)
  assert (cur_tab (ReadFile stdin ok :: tr) = Some t).
  simpl. 
  destruct (file_desc_eq stdin stdin).
  unfold classify_user_cmd in H3.
  destruct (ascii_dec ok "017"); inv H3.
  destruct (ascii_dec ok "018"); inv H4.
    destruct (cur_tab tr); inv H3.
  destruct (select_tab_idx ok).
    destruct (nth_error (cur_tabs tr) n1). inv H3; auto.
    inv H3.
  destruct (cur_tab tr); inv H3.
  destruct n; auto.

  replace (cur_tabs tr)
     with (cur_tabs (ReadFile stdin ok :: tr)).
  apply stdout_cur_dom_paint. auto. auto.

  apply stdout_cur_dom_nowrite. auto.
  intros. discriminate.

  apply stdout_cur_dom_nowrite. auto.
  intros. discriminate.

  apply stdout_cur_dom_nowrite. auto.
  intros. discriminate.

  replace (cur_tabs tr ++ t' :: nil)
     with (cur_tabs (MkTab t'
       :: Endorse true
       :: WroteEndorseMsg url
       :: ReadN (t2k t) p url
       :: ReadN (t2k t) (size 4) (pos2la4 p)
       :: ReadN (t2k t) (size 1) ("009"%char :: nil) :: tr)).
  apply stdout_cur_dom_paint. auto.
  simpl. reflexivity.

  replace (cur_tabs tr ++ t' :: nil)
     with (cur_tabs (MkCProc c
       :: MkTab t'
       :: Endorse true
       :: WroteEndorseMsg url
       :: ReadN (t2k t) p url
       :: ReadN (t2k t) (size 4) (pos2la4 p)
       :: ReadN (t2k t) (size 1) ("009"%char :: nil) :: tr)).
  apply stdout_cur_dom_paint. auto.
  simpl. reflexivity.

  apply K2TSetCookieActions_stdout_cur_dom.
  repeat (apply stdout_cur_dom_nowrite; auto).
  apply IHTraceOK.

  inv H.
  assert (cur_cprocs tr = cur_cprocs (K2TSetCookieActions c (cur_tabs tr) cookie_msg ++ ReadN (c2k c) s cookie_msg
    :: ReadN (c2k c) (size 4) (pos2la4 s)
    :: ReadN (c2k c) (size 1) ("017"%char :: nil) :: tr)).
  eapply cur_cprocs_same_over_K2TSetCookieActions.
  simpl; auto.

  rewrite<- H in *.
  econstructor; eauto.

  inv H0.
  assert (cur_tabs tr = cur_tabs  (K2TSetCookieActions c (cur_tabs tr) cookie_msg ++
         ReadN (c2k c) s cookie_msg
         :: ReadN (c2k c) (size 4) (pos2la4 s)
            :: ReadN (c2k c) (size 1) ("017"%char :: nil) :: tr)).
  eapply cur_tabs_same_over_K2TSetCookieActions.
  simpl; auto.
  rewrite<- H0 in *.
  econstructor; eauto.

  intros; discriminate.
  intros; discriminate.
  intros; discriminate.
Qed.


Definition kcorrect (s: kstate) : hprop :=
  tr :~~ ktr s in
    traced tr * fhandle stdin * fhandle stdout * ohandle gout * thandles (ctabs s) * chandles (cprocs s) * [cur_tab tr = ctab s /\ cur_tabs tr = ctabs s /\ cur_cprocs tr = cprocs s /\ TraceOK tr /\ procs_distinct tr ].


Definition khandle_u:
  forall (s: kstate),
  STsep (kcorrect s)
        (fun s' => kcorrect s').
Proof.
  unfold kcorrect; intros; destruct s as [ct cts ccps tr].
  remember (tr ~~ [cur_tab tr = ct /\ cur_tabs tr = cts /\ cur_cprocs tr = ccps /\ TraceOK tr /\ procs_distinct tr]) as PRE.
  Opaque WroteMsg.
  Opaque Paint.
  refine (
    c <- readfile stdin
      tr <@> fhandle stdout * ohandle gout * thandles cts * chandles ccps * PRE;
    (* addtab command *)
    if ascii_dec c "017"%char then
      let avoid := (map t2k cts) ++ (map c2k ccps) in
      let oavoid := (map k2t cts) ++ (map k2c ccps) in
      raw_tab <- mktab nil avoid oavoid None
        (tr ~~~ ReadFile stdin c :: tr) <@>
        fhandle stdin * fhandle stdout * ohandle gout * thandles cts * chandles ccps * PRE;
      let t := (coqtab nil raw_tab None) in 
      let topdomain := (get_topdomain_tab (tab_origin_url t)) in
      let ocp := get_cproc topdomain ccps in
       match ocp as ocp' return ocp = ocp' -> _ with
      | Some cp => fun _ =>
        (* KStep_add_tab_wo_cproc *)
        paint (cts ++ t::nil) t 
          (tr ~~~ MkTab t :: ReadFile stdin c :: tr) <@>
          fhandle stdin * ohandle gout * thandles cts * thandle t * chandles ccps * PRE * [~ In (t2k t) avoid] * [~ In (k2t t) oavoid] * [ In cp ccps];;
        writemsg t (Render (size 1%positive) ("000"%char :: nil))
          (tr ~~~ Paint (cts ++ t::nil) t ++ MkTab t :: ReadFile stdin c :: tr) <@>
          fhandle stdin * fhandle stdout * ohandle gout * thandles cts * chandles ccps * PRE * [~ In (t2k t) avoid] * [~ In (k2t t) oavoid] * [ In cp ccps];;
        {{ Return (mkst (Some t) (cts ++ t :: nil) ccps 
          (tr ~~~ WroteMsg t (Render (size 1%positive) ("000"%char::nil)) ++ Paint (cts ++ t::nil) t ++ MkTab t :: ReadFile stdin c :: tr)) }}
      | None => fun _ =>
        (* KStep_add_tab_with_cproc *)
        let cavoid := (map t2k (cts ++ t :: nil)) ++ (map c2k ccps) in
        let coavoid := (map k2t (cts ++ t :: nil)) ++ (map k2c ccps) in
        raw_cproc <- mkcproc topdomain cavoid coavoid
          (tr ~~~ MkTab t :: ReadFile stdin c :: tr) <@>
          fhandle stdin * fhandle stdout * ohandle gout * thandles cts * thandle t * chandles ccps * PRE * [~ In (t2k t) avoid] * [~ In (k2t t) oavoid];
        let cp := (coqcproc topdomain raw_cproc) in 
        paint (cts ++ t::nil) t 
          (tr ~~~ MkCProc cp :: MkTab t :: ReadFile stdin c :: tr) <@>
          fhandle stdin * ohandle gout * thandles cts * thandle t * chandles ccps * chandle cp * PRE * [~ In (t2k t) avoid] * [~ In (k2t t) oavoid] * [~ In (c2k cp) cavoid] * [~ In (k2c cp) coavoid];;
        writemsg t (Render (size 1%positive) ("000"%char :: nil))
          (tr ~~~ Paint (cts ++ t :: nil) t ++ MkCProc cp :: MkTab t :: ReadFile stdin c :: tr) <@>
          fhandle stdin * fhandle stdout * ohandle gout * thandles cts * chandles ccps * chandle cp * PRE * [~ In (t2k t) avoid] * [~ In (k2t t) oavoid] * [~ In (c2k cp) cavoid] * [~ In (k2c cp) coavoid];;
        {{ Return (mkst (Some t) (cts ++ t :: nil) (cp::ccps)
          (tr ~~~ WroteMsg t (Render (size 1%positive) ("000"%char::nil)) ++ Paint (cts ++ t::nil) t ++ MkCProc cp :: MkTab t :: ReadFile stdin c :: tr)) }}
      end (refl_equal ocp)
    else if ascii_dec c "018"%char then
      (* mouse click *)
      match ct as ct' return ct = ct' -> _ with
      | Some t => fun _ =>
          mouse_str <- mousepos (tr ~~~ ReadFile stdin c :: tr) <@>
            fhandle stdin * fhandle stdout * ohandle gout * thandles cts * chandles ccps * PRE;
          writemsg t (MouseClick (length_in_size mouse_str) mouse_str)
            (tr ~~~ MousePos mouse_str :: ReadFile stdin c :: tr) <@>
            fhandle stdin * fhandle stdout * ohandle gout * thandles_drop cts t * chandles ccps * PRE;;
          {{ Return (mkst ct cts ccps (tr ~~~
            WroteMsg t (MouseClick (length_in_size mouse_str) mouse_str) ++ MousePos mouse_str :: ReadFile stdin c :: tr)) }}
      | None => fun _ =>
        (* mouse is clicked, but no tab exists. The read input is ignored *)
          {{ Return (mkst ct cts ccps
            (tr ~~~ ReadFile stdin c :: tr)) }}
      end (refl_equal ct)
    else
  
      let i := select_tab_idx c in
      match i as i' return i = i' -> _ with
      | Some i => fun _ =>
        (* switch tab *)
          let t := nth_error cts i in
          match t as t' return t = t' -> _ with
          | Some t => fun _ =>
              paint cts t 
                (tr ~~~ ReadFile stdin c :: tr) <@>
                fhandle stdin * ohandle gout * thandles cts * chandles ccps * PRE;;
              writemsg t (Render (size 1%positive) ("000"%char::nil))
                (tr ~~~ Paint cts t ++ ReadFile stdin c :: tr) <@>
                fhandle stdin * fhandle stdout * ohandle gout * thandles_drop cts t * chandles ccps * PRE;;
              {{ Return (mkst (Some t) cts ccps
                (tr ~~~ WroteMsg t (Render (size 1%positive) ("000"%char::nil)) ++ Paint cts t ++ ReadFile stdin c :: tr)) }}
          | None => fun _ =>
              {{ Return (mkst ct cts ccps
                (tr ~~~ ReadFile stdin c :: tr)) }}
          end (refl_equal t)
      | None => fun _ =>
        (* keypress *)
          match ct as ct' return ct = ct' -> _ with
          | Some t => fun _ =>
              writemsg t (KeyPress (size 1%positive) (c::nil)) 
                (tr ~~~ ReadFile stdin c :: tr) <@>
                fhandle stdin * fhandle stdout * ohandle gout * thandles_drop cts t * chandles ccps * PRE;;
              {{ Return (mkst ct cts ccps (tr ~~~
                WroteMsg t (KeyPress (size 1%positive) (c::nil)) ++ ReadFile stdin c :: tr)) }}
          | None => fun _ =>
              {{ Return (mkst ct cts ccps
                (tr ~~~ ReadFile stdin c :: tr)) }}
          end (refl_equal ct)
      end (refl_equal i)
  ); sep fail auto.

  (* create tab *)
  apply himp_inj_conc'. apply himp_refl.
  eapply get_cprocs_in; eauto.

  intuition.
  rewrite H4 in H1. simpl in H1.
  apply pack_injective in H1.
  rewrite<- H1; simpl.
  rewrite H4. simpl.

  apply himp_inj_conc. repeat split; simpl.
  (* new part *)
  Transparent WroteMsg. Transparent Paint. simpl.
  rewrite H. auto.

  (* new part *)
  simpl. rewrite H6. auto.

  (*
  Check (WroteMsg t (Render (size 1) ("000"%char :: nil)) ++ Paint (cts ++ t :: nil) t ++ Clear :: nil).
  *)
  match goal with
  |- TraceOK ?tr =>
    replace tr with
      (  
        (WroteMsg t (Render (size 1) ("000"%char :: nil)) ++ Paint (cts ++ t :: nil) t)
        ++ (MkTab t :: ReadFile stdin "017"%char :: nil)
        ++ x
      )
  end.

  econstructor. eauto.
  rewrite <- H.

  (*
  econstructor. eauto.
  *)

  rewrite<- H6 in H3.
  econstructor; eauto. 
  rewrite<- _H0.
  unfold topdomain.
  rewrite<- H6.
  apply cur_cproc_eq_get_cproc.
  
  simpl. auto.

  (* uniqness for k -> * file desc *)
  simpl. rewrite map_app. simpl.
  apply uniq_app_comm.
  rewrite <- app_assoc.
  apply uniq_end; auto.
  inversion H9. apply uniq_app_comm in H8. auto.

  unfold not; intros. destruct H2. unfold oavoid.
  rewrite <- H. rewrite <- H6. 
  apply in_app_iff. apply in_app_or in H8.
  apply or_comm in H8; auto.

  (* uniqueness for * -> k file desc *)
  simpl. rewrite map_app. simpl.
  apply uniq_app_comm.
  rewrite <- app_assoc.
  apply uniq_end; auto.
  inversion H9. apply uniq_app_comm in H10. auto.

  unfold not; intros. destruct H0. unfold avoid.
  rewrite <- H. rewrite <- H6. 
  apply in_app_iff. apply in_app_or in H8.
  apply or_comm in H8; auto.

  (* uniqueness for domain fields of cookie processes *)
  simpl. inversion H9. auto.

  Opaque WroteMsg. Opaque Paint.
  sep fail auto.
  apply himp_comm_prem.
  apply repack_thandles_last.
  

  (* when the cookie process doesn't exist *)

  intuition.
  rewrite H5 in H1. simpl in H1.
  apply pack_injective in H1.
  rewrite H5.
  rewrite<- H. rewrite<- H7.
  simpl.

  apply himp_inj_conc. 
  rewrite<- H1. simpl.
  repeat split; simpl.

  match goal with
  |- TraceOK ?tr =>
    replace tr with
      (  
        (WroteMsg t (Render (size 1) ("000"%char :: nil)) ++ (Paint (cts ++ t :: nil) t ))
        ++ (MkCProc cp :: MkTab t :: ReadFile stdin "017"%char :: nil)
        ++ x
      )
  end. 
  econstructor; eauto.
  rewrite <- H.
  
  econstructor; eauto.

  rewrite cur_cproc_eq_get_cproc.
  unfold topdomain in _H0.
  rewrite<- H7 in _H0.
  auto.

  apply same_la_eq.
  simpl. auto.

  (* uniqness for k -> * file desc *)
  Transparent WroteMsg. Transparent Paint.
  simpl. rewrite map_app. simpl.
  apply uniq_app_comm.
  rewrite <- app_assoc.
  apply uniq_end; auto.
  simpl. apply uniq_cons.
  inversion H10. apply uniq_app_comm in H9. auto.

  unfold not; intros. destruct H4. unfold coavoid.
  rewrite <- H. rewrite <- H7. 
  apply in_app_iff. apply in_app_or in H9. 
  destruct H9. right; auto. left. rewrite map_app.
  apply in_app_iff. left; auto.

  unfold not. intros. destruct H2. unfold oavoid.
  simpl in H9. destruct H9. destruct H4. unfold coavoid.
  rewrite map_app. simpl. apply in_app_iff. left.
  apply in_app_iff. right. simpl. left; auto.
  rewrite <- H. rewrite <- H7. 
  apply in_app_iff. apply in_app_or in H2.
  apply or_comm in H2; auto.

  (* uniqueness for * -> k file desc *)
  simpl. rewrite map_app. simpl.
  apply uniq_app_comm.
  rewrite <- app_assoc.
  apply uniq_end; auto.
  inversion H10. apply uniq_app_comm in H11. auto.
  
  simpl. apply uniq_cons. auto.
  unfold not; intros. destruct H3. unfold cavoid.
  rewrite <- H. rewrite <- H7.
  apply in_app_iff. apply in_app_or in H14.
  destruct H14. right; auto. left.  
  rewrite map_app. apply in_app_iff. left; auto.

  unfold not; intros. destruct H0. unfold avoid.
  simpl in H9. destruct H9. destruct H3. unfold cavoid.
  rewrite map_app. simpl. apply in_app_iff. left.
  apply in_app_iff. right. simpl. left. auto.
  
  rewrite <- H. rewrite <- H7.
  apply in_app_iff. apply in_app_or in H0.
  apply or_comm in H0; auto.

  (* uniqueness for domain fields of cookie processes *)
  simpl. apply uniq_cons. inversion H10; auto.
  apply get_cproc_none_not_in; auto.
  rewrite H7. auto.

  

  Opaque WroteMsg. Opaque Paint.
  sep fail auto.
  (* rewrite<- H1.*)
  apply himp_assoc_prem1.
  apply himp_comm_prem.
  apply himp_split.
  apply himp_comm_prem.
  apply repack_thandles_last. 
  rewrite <- H1. rewrite <- H. apply himp_refl.
  apply unpack_thandles.
  eapply cur_tab_in_cur_tabs; eauto.  

  (* mouseclick *)
  apply himp_inj_conc. repeat split. 
  Transparent WroteMsg. simpl.
  rewrite file_desc_eq_true. rewrite H0; auto.

  match goal with
  |- TraceOK ?tr =>
    replace tr with
      (  WroteMsg t (MouseClick (length_in_size mouse_str) mouse_str)
      ++ (MousePos mouse_str :: ReadFile stdin "018"%char :: nil)
      ++ x
       )
  end. auto.
  econstructor. eauto.
  econstructor. eauto.
  unfold classify_user_cmd. simpl.
  rewrite H0. reflexivity. auto.
  
  simpl. inv H5. auto.
  simpl. inv H5. auto.
  simpl. inv H5. auto.
  simpl. inv H5. auto.

  apply repack_thandles.
  eapply cur_tab_in_cur_tabs. eauto. auto.

  (* mouseclick : when there's no focused tab *)
  apply himp_inj_conc'. apply himp_refl. repeat split.
  rewrite file_desc_eq_true. auto. 
  
  match goal with
  |- TraceOK ?tr =>
    replace tr with
      (  nil
      ++ (ReadFile stdin "018"%char :: nil)
      ++ x
       )
  end; auto.
  econstructor; eauto.
  econstructor; eauto.

  unfold classify_user_cmd. simpl. rewrite H1. auto.
  simpl. inv H5. auto.
  simpl. inv H5. auto.
  simpl. inv H5. auto.
  
  (* switch tab *)
  apply unpack_thandles.
  eapply nth_error_some_in; eauto.
  apply himp_inj_conc. repeat split.  
  Transparent WroteMsg. Transparent Paint. simpl.
  rewrite file_desc_eq_true. rewrite _H1, _H2; auto.

  match goal with
  |- TraceOK ?tr =>
    replace tr with
      (  
        (WroteMsg t0 (Render (size 1%positive) ("000"%char :: nil)) ++ Paint (cur_tabs x) t0)
      ++ (ReadFile stdin c :: nil)
      ++ x
       )
  end; auto.
  econstructor; eauto.
  econstructor; eauto.

  unfold classify_user_cmd. 
  rewrite ascii_dec_false; auto.
  rewrite ascii_dec_false; auto.
  rewrite _H1. rewrite _H2. auto.

  simpl. inv H5. auto.
  simpl. inv H5. auto.
  simpl. inv H5. auto.

  apply repack_thandles.
  eapply nth_error_some_in; eauto.

  (* ignore : no tab to switch to *)
  apply himp_inj_conc'. apply himp_refl. repeat split.
  rewrite file_desc_eq_true. rewrite _H1, _H2; auto.

  match goal with
  |- TraceOK ?tr =>
    replace tr with
      (  nil
      ++ (ReadFile stdin c :: nil)
      ++ x
       )
  end; auto.
  econstructor; eauto.
  econstructor; eauto.
  unfold classify_user_cmd. 
  rewrite ascii_dec_false; auto.
  rewrite ascii_dec_false; auto.
  rewrite _H1, _H2; auto.

  simpl. inv H5; auto.
  simpl. inv H5; auto.
  simpl. inv H5; auto.
  simpl. inv H4; auto.

  apply unpack_thandles.
  eapply cur_tab_in_cur_tabs; eauto.

  (* keypress : not a tab switch char *)
  apply himp_inj_conc. repeat split.
  Transparent WroteMsg. simpl.
  rewrite file_desc_eq_true. rewrite _H1; auto.

  match goal with
  |- TraceOK ?tr =>
    replace tr with
      (  WroteMsg t (KeyPress (size 1%positive) (c::nil))
      ++ (ReadFile stdin c :: nil)
      ++ x
       )
  end; auto.
  econstructor; eauto.
  econstructor; eauto.
  unfold classify_user_cmd. simpl. rewrite ascii_dec_false; auto.
  rewrite _H1, H0; auto.
  simpl. rewrite ascii_dec_false; auto.

  simpl. inv H5; auto.
  simpl. inv H5; auto.
  simpl. inv H5; auto.

  apply repack_thandles.
  eapply cur_tab_in_cur_tabs; eauto.

  (* keypress : but no current tab *)
  apply himp_inj_conc'. apply himp_refl. repeat split.
  rewrite file_desc_eq_true. rewrite _H1; auto.

  match goal with
  |- TraceOK ?tr =>
    replace tr with
      (  nil
      ++ (ReadFile stdin c :: nil)
      ++ x
       )
  end; auto.
  econstructor; eauto.
  econstructor; eauto.
  unfold classify_user_cmd. simpl. rewrite ascii_dec_false; auto.
  rewrite _H1. 
  destruct (ascii_dec c "018"%char); auto.
  rewrite H1. auto.
  rewrite H1. auto.

  simpl. inv H5; auto.
  simpl. inv H5; auto.
  simpl. inv H5; auto.
Qed.

(*
Fixpoint K2TSetCookieActions (c:cproc) (tabs:list tab) (cookie_str:list ascii) :=
  match tabs with
  | t :: tabs' =>  
    if (laeq (cproc_domain c) (get_topdomain_tab (tab_origin_url t))) then
      (K2TSetCookieActions c tabs' cookie_str) ++ 
      (WroteMsg t (K2TSetCookie (length_in_size cookie_str) cookie_str))
    else 
      (K2TSetCookieActions c tabs' cookie_str)
  | nil => nil
  end.
*)
(*
Definition invalidatecookie : forall (c: cproc) (cts: list tab) (cookie : list ascii) (PRE:hprop) (tr : [Trace]),
  STsep (tr ~~ PRE * traced tr * thandles cts)
        (fun tr':[Trace] => tr ~~ tr' ~~ PRE * thandles cts * traced tr' * [tr' = K2TSetCookieActions t0 cts cookie ++ tr]).

  refine (
      fun (t0:tab) (cts:list tab) (cookie:list ascii) (PRE:hprop) (tr:[Trace]) =>
        {{ Fix3
              (fun pts ts tr' =>  tr ~~ tr' ~~ PRE * traced tr' * thandles cts 
                * [pts ++ ts = cts ]
                * [tr' = K2TSetCookieActions t0 pts cookie ++ tr])
              (fun pts ts tr' tr'' => tr ~~ tr' ~~ tr'' ~~ PRE  * traced tr'' * thandles cts  
                * [pts ++ ts = cts] 
                * [tr' = K2TSetCookieActions t0 pts cookie ++ tr]
                * [tr'' = K2TSetCookieActions t0 ts cookie ++ tr'])
              (fun self pts ts tr' =>
                match ts as ncts return ts = ncts -> _ with
                | nil => fun _ => {{Return tr'}}
                | t :: cts'' => fun _ =>
                if sumbool_and 
                  ((get_topdomain_tab (tab_origin_url t)) = (get_topdomain_cookie cookie))
                  ((get_topdomain_tab (tab_origin_url t)) <> (get_topdomain_cookie cookie))
                  (t0 <> t)
                  (t0 = t)
                  (laeq (get_topdomain_tab (tab_origin_url t)) (get_topdomain_cookie cookie))
                  (sumbool_not (t0 = t) (t0 <> t) (tabeq t0 t))
                  then
                  writemsg t (InvalidateCookie (length_in_size cookie) cookie) tr' <@> 
                  (tr ~~ tr' ~~ [pts ++ ts = cts ] * [tr' = K2TSetCookieActions t0 pts cookie ++ tr]
                    * thandles_drop cts t * PRE) ;;
                  {{self (pts ++ t :: nil) cts'' (tr' ~~~ WroteMsg t (InvalidateCookie (length_in_size cookie) cookie) ++ tr')}}
                else
                  {{self (pts ++ t :: nil) cts'' (tr' ~~~ tr')}}
                end (refl_equal ts)
              )
              nil cts tr}}); sep fail auto.
  
  apply unpack_thandles; auto.
  apply in_or_app.
  right. simpl. auto.
  apply himp_inj_conc; auto; intros.
  rewrite K2TSetCookieActions_inv. simpl. auto.
  rewrite H2. apply la_eq_refl.
  unfold not. intros. destruct H3. symmetry. auto.

  apply himp_inj_conc.
  rewrite app_assoc. simpl; auto.
  
  apply repack_thandles; auto.

  apply in_or_app.
  right. simpl. auto.

  
  apply himp_inj_conc.
  destruct (laeq (get_topdomain_tab (tab_origin_url t)) (get_topdomain_cookie cookie)); simpl; auto.
  destruct (tabeq t0 t); simpl; auto.

  destruct H4; auto.
  unfold WroteMsg. simpl; auto.
  rewrite app_assoc. simpl; auto.

  destruct (tabeq t0 t); simpl; auto.

  destruct H4; auto.
  destruct n; auto.

  apply himp_inj_conc.
  
  rewrite K2TSetCookieActions_inv in H. simpl in H.
  inversion H; auto.

  rewrite H3; apply la_eq_refl.
  unfold not; intros. destruct H4. symmetry; auto.

  apply himp_inj_conc'.
  apply himp_refl.

  rewrite app_assoc. simpl; auto.
  
  apply himp_inj_conc.

  rewrite K2TSetCookieActions_inv2; auto.

  unfold not. intros.
  left. intros.
  destruct H2.
  eapply la_eq_same; eauto. apply la_eq_refl.

  apply himp_inj_conc'.
  apply himp_refl.

  rewrite app_assoc. simpl; auto.

  apply himp_inj_conc.
  rewrite K2TSetCookieActions_inv2; auto.

  apply himp_inj_conc'.
  apply himp_refl.

  rewrite app_assoc. simpl; auto.

  apply himp_inj_conc.

  destruct (laeq (get_topdomain_tab (tab_origin_url t)) (get_topdomain_cookie cookie)); simpl; auto.
  destruct (tabeq t0 t); simpl; auto.

  rewrite e in H3. destruct H3; auto.

  destruct (tabeq t0 t); simpl; auto.

  apply himp_inj_conc.
  rewrite K2TSetCookieActions_inv2; auto.
  unfold not. 
  left. intros.
  destruct H3.
  eapply la_eq_same; eauto. apply la_eq_refl.

  apply himp_inj_conc'.
  apply himp_refl.

  rewrite app_assoc. simpl; auto.

  apply himp_inj_conc.

  destruct (laeq (get_topdomain_tab (tab_origin_url t)) (get_topdomain_cookie cookie)); simpl; auto.
  destruct (tabeq t t); simpl; auto.
  destruct n; auto.

  destruct (tabeq t t); simpl; auto.

  apply himp_inj_conc.
  rewrite K2TSetCookieActions_inv2; auto.

  apply himp_inj_conc'.
  apply himp_refl.

  rewrite app_assoc. simpl; auto.
Qed.
*)

Definition khandle_t:
  forall (s: kstate) (t: tab),
  STsep (kcorrect s * (tr :~~ ktr s in [In t (cur_tabs tr)]))
        (fun s' => kcorrect s').
Proof.
  unfold kcorrect; intros; destruct s as [ct cts ccps tr].
  remember (tr ~~ [cur_tab tr = ct /\ cur_tabs tr = cts /\ TraceOK tr /\ cur_cprocs tr = ccps /\ procs_distinct tr]) as PRE. 
  Opaque ReadMsg. Opaque WroteMsg. Opaque WroteCMsg. Opaque Paint.
  refine (
    mm <- readmsg t tr <@>
      fhandle stdin * fhandle stdout * ohandle gout * thandles_drop cts t * chandles ccps * PRE * [In t cts];
    match mm with
    | T2Kmsg m =>
        match m as m' return m = m' -> _ with
        | Display s_s s => fun _ =>
            match ct as ct' return ct = ct' -> _ with
            | Some x => fun _ =>
                if tabeq t x then
                  (* display message *)
                  writegmsg (K2GDisplay s_s s)
                    (tr ~~~ ReadMsg t m ++ tr) <@>
                    fhandle stdin * fhandle stdout * thandles cts * chandles ccps * PRE;;
                  {{ Return (mkst ct cts ccps 
                    (tr ~~~ WroteGMsg (K2GDisplay s_s s) ++ ReadMsg t m ++ tr)) }}
                else
                  (* display message -- ignored - case 1 *)
                  {{ Return (mkst ct cts ccps 
                    (tr ~~~ ReadMsg t m ++ tr)) }}
            | None => fun _ =>
                (* display message -- ignored - case 2 *)
                {{ Return (mkst ct cts ccps 
                  (tr ~~~ ReadMsg t m ++ tr)) }}
            end (refl_equal ct)
        | ReqHtml s_s url => fun _ =>
            (* fetch html *)
            html <- wget url 
              (tr ~~~ ReadMsg t m ++ tr) <@>
              fhandle stdin * fhandle stdout * ohandle gout * thandles cts * chandles ccps * PRE * [In t cts];
            writemsg t (RspHtml (length_in_size html) html)
              (tr ~~~ Wget url html :: ReadMsg t m ++ tr) <@>
              fhandle stdin * fhandle stdout * ohandle gout * thandles_drop cts t * chandles ccps * PRE * [In t cts];;
            {{ Return (mkst ct cts ccps 
              (tr ~~~ WroteMsg t (RspHtml (length_in_size html) html) ++ Wget url html :: ReadMsg t m ++ tr)) }}
        | RequestSocket s_s sock_desc => fun _ =>
            (* request socket *)
            let host := get_host sock_desc in
            let t_origin := (tab_origin_url t) in
            let decision := is_safe_sock_dest_on host t_origin in
            match decision as decision' return decision = decision' -> _ with
            | true => fun _ =>
              writemsg t (ResultSocket (size 1%positive) ("000"%char::nil))
              (tr ~~~ ReadMsg t m ++ tr) <@>
              fhandle stdin * fhandle stdout * ohandle gout * thandles_drop cts t * chandles ccps * PRE * [In t cts];;
              sendsocket t host sock_desc 
                (tr ~~~ WroteMsg t (ResultSocket (size 1%positive) ("000"%char::nil))  ++ ReadMsg t m ++ tr) <@>
                fhandle stdin * fhandle stdout * ohandle gout * thandles_drop cts t * chandles ccps * PRE * [In t cts];;
              {{ Return (mkst ct cts ccps 
              (tr ~~~ SendSocket t host sock_desc :: WroteMsg t (ResultSocket (size 1%positive) ("000"%char::nil))  ++ ReadMsg t m ++ tr)) }}
            | false => fun _ =>
              writemsg t (ResultSocket (size 1%positive) ("001"%char::nil))
              (tr ~~~ ReadMsg t m ++ tr) <@>
              fhandle stdin * fhandle stdout * ohandle gout * thandles_drop cts t * chandles ccps * PRE * [In t cts];;
              {{ Return (mkst ct cts ccps 
              (tr ~~~ WroteMsg t (ResultSocket (size 1%positive) ("001"%char::nil))  ++ ReadMsg t m ++ tr)) }}
            end (refl_equal decision)
        | Navigate s_s init_url => fun _ =>
            (* navigation actions *)

            writeendorsemsg init_url 
              (tr ~~~ ReadMsg t m ++ tr) <@>
              fhandle stdin * ohandle gout * thandles cts * chandles ccps * PRE * [In t cts];;
            c <- endorse  
              (tr ~~~ WroteEndorseMsg init_url :: ReadMsg t m ++ tr) <@>
              fhandle stdin * fhandle stdout * ohandle gout * thandles cts * chandles ccps * PRE * [In t cts];
            match c with 
            | true  => 
              (* the user endorses this navigation *)
              let avoid := (map t2k cts) ++ (map c2k ccps) in
              let oavoid := (map k2t cts) ++ (map k2c ccps) in
              raw_tab <- mktab init_url avoid oavoid None
                (tr ~~~ Endorse true :: WroteEndorseMsg init_url :: ReadMsg t m ++ tr ) <@>
                fhandle stdin * fhandle stdout * ohandle gout * thandles cts * chandles ccps * PRE * [In t cts];
              let nt := (coqtab init_url raw_tab None) in 
              let topdomain := (get_topdomain_tab (tab_origin_url nt)) in
              let ocp := get_cproc topdomain ccps in

              match ocp as ocp' return ocp = ocp' -> _ with
              | Some cp => fun _ =>
              (* there was a cproc for this navigation *)
              paint (cts ++ nt::nil) nt 
              (tr ~~~ MkTab nt :: Endorse true :: WroteEndorseMsg init_url :: ReadMsg t m ++ tr ) <@> fhandle stdin * ohandle gout * thandles cts * thandle nt * chandles ccps * PRE * [~ In (t2k nt) avoid] * [~ In (k2t nt) oavoid] * [In t cts];;
              writemsg nt (Render (size 1%positive) ("000"%char :: nil))
                (tr ~~~ Paint (cts ++ nt::nil) nt ++ MkTab nt ::  Endorse true :: WroteEndorseMsg init_url :: ReadMsg t m ++ tr ) <@>
                fhandle stdin * fhandle stdout * ohandle gout * thandles cts * chandles ccps * PRE * [~ In (t2k nt) avoid] * [~ In (k2t nt) oavoid] * [In t cts];;
              {{ Return (mkst (Some nt) (cts ++ nt :: nil) ccps
                (tr ~~~ WroteMsg nt (Render (size 1%positive) ("000"%char::nil)) ++ Paint (cts ++ nt::nil) nt ++ MkTab nt :: Endorse true ::  WroteEndorseMsg init_url :: ReadMsg t m ++ tr)) }}
              | None => fun _ =>
              let cavoid := (map t2k (cts ++ nt :: nil)) ++ (map c2k ccps) in
              let coavoid := (map k2t (cts ++ nt :: nil)) ++ (map k2c ccps) in
              raw_cproc <- mkcproc topdomain cavoid coavoid
                (tr ~~~ MkTab nt :: Endorse true :: WroteEndorseMsg init_url :: ReadMsg t m ++ tr ) <@>
                fhandle stdin * fhandle stdout * ohandle gout * thandles cts * thandle nt * chandles ccps * PRE * [~ In (t2k nt) avoid] * [~ In (k2t nt) oavoid] * [In t cts] ;
              let cp := (coqcproc topdomain raw_cproc) in 
              paint (cts ++ nt::nil) nt 
              (tr ~~~ MkCProc cp :: MkTab nt :: Endorse true :: WroteEndorseMsg init_url :: ReadMsg t m ++ tr ) <@>
                fhandle stdin * ohandle gout * thandles cts * thandle nt * chandles ccps * chandle cp * PRE * [~ In (t2k nt) avoid] * [~ In (k2t nt) oavoid] * [In t cts] * [~ In (c2k cp) cavoid] * [~ In (k2c cp) coavoid];;
              writemsg nt (Render (size 1%positive) ("000"%char :: nil))
                (tr ~~~ Paint (cts ++ nt::nil) nt ++ MkCProc cp :: MkTab nt ::  Endorse true :: WroteEndorseMsg init_url :: ReadMsg t m ++ tr ) <@>
                fhandle stdin * fhandle stdout * ohandle gout * thandles cts * chandles ccps * chandle cp * PRE * [~ In (t2k nt) avoid] * [~ In (k2t nt) oavoid] * [In t cts] * [~ In (c2k cp) cavoid] * [~ In (k2c cp) coavoid];;
              {{ Return (mkst (Some nt) (cts ++ nt :: nil) (cp :: ccps )
                (tr ~~~ WroteMsg nt (Render (size 1%positive) ("000"%char::nil)) ++ Paint (cts ++ nt::nil) nt ++ MkCProc cp :: MkTab nt :: Endorse true ::  WroteEndorseMsg init_url :: ReadMsg t m ++ tr)) }}
              end (refl_equal ocp)
            | false =>
              {{ Return (mkst ct cts ccps 
                (tr ~~~ Endorse false :: WroteEndorseMsg init_url :: ReadMsg t m ++ tr)) }}
            end
            (*
        | SetCookie s_s cookie => fun _ =>
          let topdomain_tab := (get_topdomain_tab (tab_origin_url t)) in
          let topdomain_cookie := (get_topdomain_cookie cookie) in
          let topdomain_same := laeq topdomain_tab topdomain_cookie in

          if topdomain_same 
          then
            let ocp := get_cproc topdomain_cookie ccps in
            match ocp as ocp' return ocp = ocp' -> _ with
            | Some cp => fun _ =>
              writecmsg cp (K2CSetCookie s_s cookie)
                (tr ~~~  ReadMsg t m ++ tr ) <@>
                fhandle stdin * fhandle stdout * ohandle gout * thandles cts * chandles_drop ccps cp * PRE * [In t cts];;
                dtr <- invalidatecookie t cts cookie (fhandle stdin * fhandle stdout * ohandle gout * chandles ccps * PRE * [In t cts]) (tr ~~~ WroteCMsg cp (K2CSetCookie s_s cookie) ++ ReadMsg t m ++ tr);
              {{ Return (mkst ct cts ccps 
                (tr ~~~ (K2TSetCookieActions t cts cookie) ++  WroteCMsg cp (K2CSetCookie s_s cookie) ++ ReadMsg t m ++ tr)) }}
            | None => fun _ =>
              {{ Return (mkst ct cts ccps 
                (tr ~~~ ReadMsg t m ++ tr)) }}
            end (refl_equal ocp)
          else
            {{ Return (mkst ct cts ccps 
              (tr ~~~ ReadMsg t m ++ tr)) }}
              *)

        | SetCookie s_s cookie => fun _ =>
          let topdomain_tab := (get_topdomain_tab (tab_origin_url t)) in
          let topdomain_cookie := (get_topdomain_cookie cookie) in
          let topdomain_same := laeq topdomain_tab topdomain_cookie in

          if topdomain_same 
          then
            let ocp := get_cproc topdomain_cookie ccps in
            match ocp as ocp' return ocp = ocp' -> _ with
            | Some cp => fun _ =>
              writecmsg cp (K2CSetCookie s_s cookie)
                (tr ~~~  ReadMsg t m ++ tr ) <@>
                fhandle stdin * fhandle stdout * ohandle gout * thandles cts * chandles_drop ccps cp * PRE * [In t cts];;
              {{ Return (mkst ct cts ccps 
                (tr ~~~ WroteCMsg cp (K2CSetCookie s_s cookie) ++ ReadMsg t m ++ tr)) }}
            | None => fun _ =>
              (* it's okay. because we know that this never happens *)
              {{ Return (mkst ct cts ccps 
                (tr ~~~ ReadMsg t m ++ tr)) }}
            end (refl_equal ocp)
          else
            (* when the domain property of the cookie doesn't agree with the tab *)
            {{ Return (mkst ct cts ccps 
              (tr ~~~ ReadMsg t m ++ tr)) }}

        | GetCookie s_s url => fun _ =>
          let topdomain_tab := (get_topdomain_tab (tab_origin_url t)) in
          let ocp := get_cproc topdomain_tab ccps in
          let tab_id_url := (tab_id_to_la (t2k t)) ++ url in
          match ocp as ocp' return ocp = ocp' -> _ with
          | Some cp => fun _ =>
            writecmsg cp (K2CGetCookie s_s tab_id_url)
              (tr ~~~  ReadMsg t m ++ tr ) <@>
              fhandle stdin * fhandle stdout * ohandle gout * thandles cts * chandles_drop ccps cp * PRE * [In t cts];;
            {{ Return (mkst ct cts ccps 
              (tr ~~~ WroteCMsg cp (K2CGetCookie s_s tab_id_url) ++ ReadMsg t m ++ tr)) }}
          | None => fun _ =>
            {{ Return (mkst ct cts ccps 
              (tr ~~~ ReadMsg t m ++ tr)) }}
          end (refl_equal ocp)
        end (refl_equal m)
    | BadTag garbage =>
        {{ Return (mkst ct cts ccps
          (tr ~~~ ReadN (t2k t) (size 1%positive) garbage :: tr)) }}
    end
  ); sep fail auto; simpl.
  simpl.
  simpl.

  (* display current tab *)
  apply unpack_thandles; auto.
  apply himp_comm_prem. apply repack_thandles. auto.
  apply himp_inj_conc'; repeat split; norm_list; simpl.
  apply himp_refl. auto.
  (* inv H3. auto. *)

  match goal with
  |- TraceOK ?tr =>
    replace tr with
      (  
        (WriteN gout s_s s
          :: WriteN gout 4 (pos2la4 s_s)
          :: WriteN gout 1 ("000"%char :: nil) :: nil) ++
        (*
        (WriteStrFile stdout (screen (cur_tabs x0) x nil)
          :: WriteStrFile stdout ("@"%char :: tab_origin_url x ++ newline :: nil)
          :: Clear :: nil)
        ++
        *)
        (ReadMsg x (Display s_s s) ++ x0)
       )
  end.
  econstructor; eauto.
  econstructor; eauto.

  eapply cur_tab_in_cur_tabs. auto. auto. auto.
  inv H5. auto. inv H5. auto. inv H5. auto.

  (* disply request from non-current tab *)
  apply himp_inj_conc. repeat split; simpl.
  inv H5. auto.

  match goal with
  |- TraceOK ?tr =>
    replace tr with
      (  nil
        ++ ReadMsg t (Display s_s s) 
        ++ x0
       )
  end; auto.
  econstructor; eauto.
  econstructor; eauto.

  unfold not; intro. destruct _H1.
  rewrite H1 in H0. inv H0; auto.
  inv H5. auto. inv H5. auto. inv H5. auto.

  apply repack_thandles; auto.

  apply himp_inj_conc. repeat split; simpl; auto.

  match goal with
  |- TraceOK ?tr =>
    replace tr with
      ( nil
      ++ ReadMsg t (Display s_s s)
      ++ x
    )
  end; auto.
  econstructor; eauto.
  econstructor; eauto.

  unfold not; intro. rewrite H1 in H0.
  discriminate.

  inv H5. auto. inv H5. auto. inv H5. auto.

  (* request html *)
  apply repack_thandles; auto.
  apply repack_thandles; auto.
  apply unpack_thandles; auto.
  apply himp_inj_conc. repeat split; norm_list; simpl.

  match goal with
  |- TraceOK ?tr =>
    replace tr with
      (
        WroteMsg t (RspHtml (length_in_size html) html)
        ++ (Wget url html ::
          ReadMsg t (ReqHtml s_s url))
        ++ x
      )
  end; auto.
  econstructor; eauto.
  econstructor; eauto.

  inv H5. auto. inv H5. auto. inv H5. auto.

  (* socket *)
  apply himp_comm_prem. 
  apply himp_comm_prem.
  apply repack_thandles; auto.
  apply himp_inj_conc. repeat split; simpl; auto.

  match goal with
  |- TraceOK ?tr =>
    replace tr with
      (
        (SendSocket t host sock_desc
          :: WroteMsg t (ResultSocket (size 1) ("000"%char :: nil)))
        ++ ReadMsg t (RequestSocket s_s sock_desc)
        ++ x
      )
  end; auto.
  econstructor; eauto.
  econstructor; eauto.

  apply la_eq_refl.

  inv H5. auto. inv H5. auto. inv H5. auto.

  apply repack_thandles; auto.
  apply himp_inj_conc. repeat split; simpl; auto.

  match goal with
  |- TraceOK ?tr =>
    replace tr with
      (
        WroteMsg t (ResultSocket (size 1) ("001"%char :: nil))
        ++ ReadMsg t (RequestSocket s_s sock_desc) 
        ++ x
      )
  end; auto.
  econstructor; eauto.
  econstructor; eauto.
  apply la_eq_refl. 

  unfold host in _H0. unfold t_origin in _H0.
  rewrite _H0. discriminate.

  inv H5. auto. inv H5. auto. inv H5. auto.

  apply repack_thandles; auto.
  apply himp_comm_prem. apply repack_thandles; auto.

  unfold size in H. simpl in H.

  (* navigation - when the user endorses this action and there exists a cookie proc for this tab *)  
  apply himp_inj_conc. repeat split; 
  intuition;
  rewrite H4 in H1; simpl in H1;
  apply pack_injective in H1;
  try rewrite H4; try rewrite H4; 
  try rewrite<- H1; 
  try rewrite<- H; try rewrite<- H10; 
  try rewrite<- H in H3; try rewrite<- H10 in _H0; 
  try unfold avoid in H0; try unfold oavoid in H2;
  try rewrite<- H in H0; try rewrite<- H in H2;
  simpl; auto.

  match goal with
  |- TraceOK ?tr =>
    replace tr with
      (
        (WroteMsg nt (Render (size 1) ("000"%char :: nil)) ++
          Paint (cur_tabs x ++ nt :: nil) nt) ++
        (MkTab nt
          :: Endorse true
          :: WroteEndorseMsg init_url
          :: ReadMsg t (Navigate s_s init_url))
        ++ x
      )
  end; auto.
  econstructor; eauto.
  econstructor; eauto.
  unfold tab_init_url. simpl. apply same_la_eq.
  rewrite <- H7 in _H0. unfold topdomain in _H0.
  rewrite cur_cproc_eq_get_cproc; eauto.
  

  (* uniqness for k -> * file desc *)
  Transparent WroteMsg. Transparent Paint. Transparent ReadMsg.
  simpl. rewrite map_app. simpl.
  apply uniq_app_comm.
  rewrite <- app_assoc.
  apply uniq_end; auto.
  inversion H9. apply uniq_app_comm in H8. auto.

  unfold not; intros. destruct H2. auto.  
  rewrite <- H7. 
  apply in_app_iff. apply in_app_or in H8. 
  destruct H8. right; auto. left. auto.
  
  (* uniqueness for * -> k file desc *)
  simpl. rewrite map_app. simpl.
  apply uniq_app_comm.
  rewrite <- app_assoc.
  apply uniq_end; auto.
  inversion H9. apply uniq_app_comm in H10. auto.
  
  unfold not; intros. destruct H0. 
  rewrite <- H7.
  apply in_app_iff. apply in_app_or in H8. destruct H8.
  right; auto. left; auto.

  (* uniqueness for domain fields of cookie processes *)
  simpl. inv H9. auto.

  Opaque ReadMsg. Opaque WroteMsg. Opaque WroteCMsg. Opaque Paint.
  intuition;
  rewrite H4 in H1; simpl in H1;
  apply pack_injective in H1;
  try rewrite H4; try rewrite H4; 
  try rewrite<- H1; 
  try rewrite<- H; try rewrite<- H10; 
  try rewrite<- H in H3; try rewrite<- H10 in _H0; 
  try unfold avoid in H0; try unfold oavoid in H2;
  try rewrite<- H in H0; try rewrite<- H in H2;
  simpl; auto; sep fail auto.

  apply himp_comm_prem.
  apply repack_thandles_last.

  (* navigation - when the user endorses this action and there isn't a cookie proc for this tab *)  
  apply himp_inj_conc. repeat split;
  intuition;
  rewrite H6 in H1; simpl in H1;
  apply pack_injective in H1;
  try rewrite H6; try rewrite<- H1;
  try rewrite<- H; try rewrite<- H7; try rewrite<- H12; 
  try rewrite<- H in H3; try rewrite<- H12 in _H0; 
  try unfold avoid in H0; try unfold oavoid in H2;
  try unfold cavoid in H4; try unfold coavoid in H5;
  try rewrite<- H in H0; try rewrite<- H in H2;
  try rewrite<- H12 in H4; try rewrite<- H12 in H5;
  simpl; auto. rewrite <- H9. auto.

  match goal with
  |- TraceOK ?tr =>
    replace tr with
      ( 
        (WroteMsg nt (Render (size 1) ("000"%char :: nil)) ++
          Paint (cur_tabs x ++ nt :: nil) nt) ++
        (MkCProc cp
          :: MkTab nt
          :: Endorse true
          :: WroteEndorseMsg init_url
          :: ReadMsg t (Navigate s_s init_url))
        ++ x
      )
  end; auto.
  econstructor; eauto.
  econstructor; eauto.
  unfold tab_init_url. simpl. apply same_la_eq.
  rewrite cur_cproc_eq_get_cproc; eauto. 
  unfold topdomain in _H0. rewrite <- H9 in _H0. auto.
  apply same_la_eq. 

  Transparent WroteMsg. Transparent Paint. Transparent ReadMsg. simpl. auto.

  (* uniqness for k -> * file desc *)
  Transparent WroteMsg. Transparent Paint.
  simpl. rewrite map_app. simpl.
  apply uniq_app_comm.
  rewrite <- app_assoc.
  apply uniq_end; auto.
  simpl. apply uniq_cons.
  inversion H11. apply uniq_app_comm in H10. auto.

  unfold not; intros. destruct H5. unfold coavoid.
  rewrite <- H. rewrite <- H9. 
  apply in_app_iff. apply in_app_or in H10. 
  destruct H10. right; auto. left. rewrite map_app.
  apply in_app_iff. left; auto.

  unfold not. intros. destruct H2. rewrite <- H9.
  simpl in H10. destruct H10. destruct H5. rewrite <- H9.
  rewrite map_app. simpl. apply in_app_iff. left.
  apply in_app_iff. right. simpl. left; auto.
  apply in_app_iff. apply in_app_or in H2.
  apply or_comm in H2; auto.
  
  (* uniqueness for * -> k file desc *)
  simpl. rewrite map_app. simpl.
  apply uniq_app_comm.
  rewrite <- app_assoc.
  apply uniq_end; auto.
  inversion H11. apply uniq_app_comm in H12. auto.
  
  simpl. apply uniq_cons. auto.
  unfold not; intros. destruct H4. 
  rewrite <- H. rewrite <- H9.
  apply in_app_iff. apply in_app_or in H15.
  destruct H15. right; auto. left.  
  rewrite map_app. apply in_app_iff. left; auto.

  unfold not; intros. destruct H0. 
  simpl in H10. destruct H10. destruct H4. 
  rewrite map_app. simpl. apply in_app_iff. left.
  apply in_app_iff. right. simpl. left. auto.
  
  rewrite <- H9.
  apply in_app_iff. apply in_app_or in H0.
  apply or_comm in H0; auto.

  (* uniqueness for domain fields of cookie processes *)
  simpl. apply uniq_cons. inversion H11; auto.
  apply get_cproc_none_not_in; auto.
  rewrite H9. auto.

  Opaque ReadMsg. Opaque WroteMsg. Opaque WroteCMsg. Opaque Paint.

  intuition;
  rewrite H6 in H1; simpl in H1;
  apply pack_injective in H1;
  try rewrite H6; try rewrite<- H1;
  try rewrite<- H; try rewrite<- H7; try rewrite<- H12; 
  try rewrite<- H in H3; try rewrite<- H12 in _H0; 
  try unfold avoid in H0; try unfold oavoid in H2;
  try unfold cavoid in H4; try unfold coavoid in H5;
  try rewrite<- H in H0; try rewrite<- H in H2;
  try rewrite<- H12 in H4; try rewrite<- H12 in H5;
  simpl; auto; sep fail auto.

  apply himp_comm_prem.
  apply repack_thandles_last.

  apply himp_inj_conc'. apply himp_refl.
  repeat split.

  match goal with
  |- TraceOK ?tr =>
    replace tr with
      (  
        nil 
        ++ (Endorse false:: WroteEndorseMsg init_url :: ReadMsg t (Navigate s_s init_url))
        ++ x
       )
  end; auto.
  econstructor; auto.
  econstructor; auto.

  inv H5. auto. inv H5. auto. inv H5. auto.
  
  apply himp_comm_prem.
  apply himp_assoc_prem1.
  apply himp_comm_prem.

  apply himp_comm_conc.
  apply himp_assoc_conc1.
  apply himp_comm_conc.

  apply himp_assoc_conc1.

  apply himp_split with (p1 := thandles_drop (cur_tabs x) t * thandle t) (p2 := chandles (cur_cprocs x)) (q1 := thandles (cur_tabs x)) (q2:= chandle cp * chandles_drop (cur_cprocs x) cp).

  apply himp_comm_prem.
  apply repack_thandles.

  auto.
  apply unpack_chandles.  
  eapply cur_cproc_in_cur_cprocs. eauto.
  rewrite<- _H0.
  apply cur_cproc_eq_get_cproc.

  (* cookie get (t2k) *)
  apply himp_inj_conc.
  repeat split; simpl.
  unfold tab_id_url.

  match goal with
  |- TraceOK ?tr =>
    replace tr with
      (  
        (WroteCMsg cp (K2CGetCookie s_s (tab_id_to_la (t2k t) ++ url)))
        ++ ReadMsg t (GetCookie s_s url)
        ++ x
      )
  end; auto.
  econstructor; eauto.
  econstructor; eauto.
  inv H5.
  eapply cur_cproc_in_cur_cprocs. auto.
  rewrite cur_cproc_eq_get_cproc; eauto.
  rewrite cur_cproc_eq_get_cproc; auto.

  inv H5. auto. inv H5. auto. inv H5. auto.
  apply himp_comm_prem.
  apply repack_chandles.

  eapply cur_cproc_in_cur_cprocs. auto.
  rewrite cur_cproc_eq_get_cproc; eauto.

  apply himp_inj_conc. repeat split; simpl.

  (* cookie get - when there's no cproc for the tab *)

  assert (get_cproc topdomain_tab (cur_cprocs x) <> None).
  unfold topdomain_tab. apply get_cproc_some. auto. auto.
  rewrite _H0 in H0. destruct H0. reflexivity.

  (*
  match goal with
  |- TraceOK ?tr =>
    replace tr with
      (  
        nil 
         ++ 
         (ReadN (t2k t) s_s url
           :: ReadN (t2k t) (size 4) (pos2la4 s_s)
           :: ReadN (t2k t) (size 1) ("010"%char :: nil) :: nil)
         ++ x
       )
  end; auto.
  econstructor; eauto.
  econstructor; eauto.
  rewrite cur_cproc_eq_get_cproc; eauto.
  *)

  inv H5. auto. inv H5. auto. inv H5. auto.

  apply repack_thandles; auto.

  (* Show Existentials.*)
 
  apply himp_comm_prem.
  apply himp_assoc_prem1.
  apply himp_comm_prem.

  apply himp_comm_conc.
  apply himp_assoc_conc1.
  apply himp_comm_conc.

  apply himp_assoc_conc1.

  apply himp_split with (p1 := thandles_drop (cur_tabs x) t * thandle t) (p2 := chandles (cur_cprocs x)) (q1 := thandles (cur_tabs x)) (q2:= chandle cp * chandles_drop (cur_cprocs x) cp).

  apply himp_comm_prem.
  apply repack_thandles. 

  auto.

  apply unpack_chandles.
  inv H4; auto.
  eapply cur_cproc_in_cur_cprocs. auto.
  rewrite cur_cproc_eq_get_cproc; eauto.

  apply himp_inj_conc. 
  Transparent WroteCMsg. Transparent ReadMsg.
  split. simpl. auto.
  split. simpl. auto.
  split. simpl. auto.
  split.

  (*
  simpl. a

  simpl.


  apply himp_comm_conc.
  

  apply himp_comm_prem.
  apply repack_chandles.
  inv H5; auto.
  eapply cur_cproc_in_cur_cprocs. auto.
  rewrite cur_cproc_eq_get_cproc; eauto.

  apply himp_inj_conc'. apply himp_refl.
  repeat split; simpl; auto.
  
  symmetry. eapply cur_tab_same_over_K2TSetCookieActions.
  simpl; auto.

  symmetry. eapply cur_tabs_same_over_K2TSetCookieActions.
  simpl; auto.

  symmetry. eapply cur_cprocs_same_over_K2TSetCookieActions.
  simpl; auto.

  *)

  match goal with
  |- TraceOK ?tr =>
    replace tr with
      (
        (WroteCMsg cp (K2CSetCookie s_s cookie)) ++
        (ReadMsg t (SetCookie s_s cookie)) ++
        x
      )
  end; auto.
  econstructor; eauto.
  econstructor; eauto.

  eapply cur_cproc_in_cur_cprocs. auto.
  rewrite cur_cproc_eq_get_cproc; eauto.
  rewrite _H0.
  apply la_eq_refl.

  rewrite cur_cproc_eq_get_cproc; eauto.

  simpl. econstructor. simpl. inv H5; auto.
  simpl; inv H5; auto. 
  simpl; inv H5; auto.

  apply himp_comm_prem.
  apply repack_chandles.

  eapply cur_cproc_in_cur_cprocs. auto.
  rewrite cur_cproc_eq_get_cproc; eauto.

  apply himp_inj_conc. 
  (* Transparent WroteCMsg. Transparent ReadMsg. *)
  split. simpl. auto.
  split. simpl. auto.
  split. simpl. auto.
  split.

  (* cookie proces always exists *)
  Check cur_cproc_some. 
  assert (cur_cproc (get_topdomain_tab (tab_origin_url t)) x <> None).
  eapply cur_cproc_some; eauto.
  rewrite cur_cproc_eq_get_cproc in H0. rewrite _H0 in H0. contradiction.
  simpl. econstructor; simpl; eauto.
  simpl; inv H5; auto.
  simpl; inv H5; auto.
  simpl; inv H5; auto.
 
  apply repack_thandles; auto.

  apply himp_inj_conc. 
  (* Transparent WroteCMsg. Transparent ReadMsg. *)
  split. simpl. auto.
  split. simpl. auto.
  split. simpl. auto.
  split.

  match goal with
  |- TraceOK ?tr =>
    replace tr with
      (
        nil ++
        (ReadMsg t (SetCookie s_s cookie)) ++
        x
      )
  end; auto.
  econstructor; eauto.
  econstructor; eauto.
  
  intros not; intros. destruct b.
  unfold topdomain_tab. unfold topdomain_cookie.
  eapply la_eq_same; eauto. apply la_eq_refl.
  econstructor; simpl; eauto. 
  simpl; inv H5; auto.
  simpl; inv H5; auto.
  simpl; inv H5; auto.

  apply repack_thandles; auto.

  apply himp_inj_conc. 
  (* Transparent WroteCMsg. Transparent ReadMsg. *)
  split. simpl. auto.
  split. simpl. auto.
  split. simpl. auto.
  split.

  match goal with
  |- TraceOK ?tr =>
    replace tr with
      (  
        nil 
         ++ (ReadN (t2k t) (size 1) garbage :: nil)
         ++ x
       )
  end; auto.
  econstructor; eauto.
  econstructor; eauto.

  econstructor; eauto.
  simpl; inv H6; auto.
  simpl; inv H6; auto.
  simpl; inv H6; auto.

  apply repack_thandles; auto.
Qed.

(*
  (*
  rewrite app_assoc. simpl. auto.
  
  rewrite<- cur_tabs_same_over_K2TSetCookieActions with (tr := WriteN (k2c cp) s_s cookie
            :: WriteN (k2c cp) (size 4) (pos2la4 s_s)
               :: WriteN (k2c cp) (size 1) ("013"%char :: nil)
                  :: ReadN (t2k t) s_s cookie
                     :: ReadN (t2k t) (size 4) (pos2la4 s_s)
                        :: ReadN (t2k t) (size 1) ("011"%char :: nil) :: x0).
  simpl. inv H3; auto. auto.

  rewrite<- cur_tabs_same_over_K2TSetCookieActions with (tr := WriteN (k2c cp) s_s cookie
            :: WriteN (k2c cp) (size 4) (pos2la4 s_s)
               :: WriteN (k2c cp) (size 1) ("013"%char :: nil)
                  :: ReadN (t2k t) s_s cookie
                     :: ReadN (t2k t) (size 4) (pos2la4 s_s)
                        :: ReadN (t2k t) (size 1) ("011"%char :: nil) :: x0).
  simpl. inv H3; auto. auto.

  rewrite<- cur_cprocs_same_over_K2TSetCookieActions with (tr := WriteN (k2c cp) s_s cookie
            :: WriteN (k2c cp) (size 4) (pos2la4 s_s)
               :: WriteN (k2c cp) (size 1) ("013"%char :: nil)
                  :: ReadN (t2k t) s_s cookie
                     :: ReadN (t2k t) (size 4) (pos2la4 s_s)
                        :: ReadN (t2k t) (size 1) ("011"%char :: nil) :: x0).
  simpl. inv H4; auto. auto.

  rewrite<- cur_cprocs_same_over_K2TSetCookieActions with (tr := WriteN (k2c cp) s_s cookie
            :: WriteN (k2c cp) (size 4) (pos2la4 s_s)
               :: WriteN (k2c cp) (size 1) ("013"%char :: nil)
                  :: ReadN (t2k t) s_s cookie
                     :: ReadN (t2k t) (size 4) (pos2la4 s_s)
                        :: ReadN (t2k t) (size 1) ("011"%char :: nil) :: x0).
  simpl. inv H4; auto. auto.

  rewrite<- cur_cprocs_same_over_K2TSetCookieActions with (tr := WriteN (k2c cp) s_s cookie
            :: WriteN (k2c cp) (size 4) (pos2la4 s_s)
               :: WriteN (k2c cp) (size 1) ("013"%char :: nil)
                  :: ReadN (t2k t) s_s cookie
                     :: ReadN (t2k t) (size 4) (pos2la4 s_s)
                        :: ReadN (t2k t) (size 1) ("011"%char :: nil) :: x0).
  simpl. inv H4; auto. auto.
  *)
  apply himp_inj_conc.

  repeat split; simpl; auto.

  match goal with
  |- TraceOK ?tr =>
    replace tr with
      (  
        nil 
        ++ (ReadN (t2k t) s_s cookie
          :: ReadN (t2k t) (size 4) (pos2la4 s_s)
          :: ReadN (t2k t) (size 1) ("011"%char :: nil) :: nil)
        ++ x
       )
  end; auto.
  econstructor; eauto.
  econstructor; eauto.
  
  right; auto.
  rewrite cur_cproc_eq_get_cproc; eauto.

  inv H3; auto. inv H3; auto. inv H3; auto.
  inv H4; auto. inv H4; auto. inv H4; auto.

  apply repack_thandles; auto.

  apply himp_inj_conc. repeat split.

  match goal with
  |- TraceOK ?tr =>
    replace tr with
      (  
        nil 
        ++ (ReadN (t2k t) s_s cookie
          :: ReadN (t2k t) (size 4) (pos2la4 s_s)
          :: ReadN (t2k t) (size 1) ("011"%char :: nil) :: nil)
         ++ x
       )
  end; auto.
  econstructor; eauto.
  econstructor; eauto.
  
  left. unfold not. intros.

  destruct _H0. unfold topdomain_tab. unfold topdomain_cookie.
  eapply la_eq_same; eauto. apply la_eq_refl.

  inv H3; auto. inv H3; auto. inv H3; auto.
  inv H4; auto. inv H4; auto. inv H4; auto.

  apply repack_thandles; auto.
  
  (* garbage *)
  apply himp_inj_conc. repeat split.

  match goal with
  |- TraceOK ?tr =>
    replace tr with
      (  
        nil 
         ++ (ReadN (t2k t) (size 1) garbage :: nil)
         ++ x
       )
  end; auto.
  econstructor; eauto.
  econstructor; eauto.

  inv H4; auto. inv H4; auto. inv H4; auto.
  inv H5; auto. inv H5; auto. inv H5; auto.

  apply repack_thandles; auto.
Qed.
*)

(* working *)
(*
Fixpoint K2TSetCookieActions (c:cproc) (tabs:list tab) (cookie_str:list ascii) :=
  match tabs with
  | t :: tabs' =>  
    if (laeq (cproc_domain c) (get_topdomain_tab (tab_origin_url t))) then
      (K2TSetCookieActions c tabs' cookie_str) ++ 
      (WroteMsg t (K2TSetCookie (length_in_size cookie_str) cookie_str))
    else 
      (K2TSetCookieActions c tabs' cookie_str)
  | nil => nil
  end.
*)

Lemma K2TSetCookieActions_inv :
  forall c pts t cookie, 
    la_eq (cproc_domain c) (get_topdomain_tab (tab_origin_url t)) ->
    K2TSetCookieActions c (pts ++ t :: nil) cookie = 
    (WroteMsg t (K2TSetCookie (length_in_size cookie) cookie) ++ 
    K2TSetCookieActions c pts cookie).
Proof.
  induction pts.
  intros. simpl.

  destruct (laeq (cproc_domain c) (get_topdomain_tab (tab_origin_url t))).
  rewrite app_nil_r. auto.

  assert (cproc_domain c = get_topdomain_tab (tab_origin_url t)).
  eapply la_eq_same. eauto. eapply la_eq_refl. rewrite H0 in n.  
  destruct n. auto.

  intros.
  simpl.
  destruct (laeq (cproc_domain c) (get_topdomain_tab (tab_origin_url a))); simpl.
  rewrite IHpts.
  simpl. auto. auto. auto.
Qed.


Lemma K2TSetCookieActions_inv2 :
  forall c pts t cookie, 
    ~ la_eq (cproc_domain c) (get_topdomain_tab (tab_origin_url t)) ->
    K2TSetCookieActions c (pts ++ t :: nil) cookie = K2TSetCookieActions c pts cookie.
Proof.
  induction pts.
  intros. simpl.

  destruct (laeq (cproc_domain c) (get_topdomain_tab (tab_origin_url t))); simpl.
  destruct H. 
  rewrite e. apply la_eq_refl.
  auto.
  
  intros.
  simpl.
  destruct (laeq (cproc_domain c) (get_topdomain_tab (tab_origin_url a))); simpl.
  rewrite IHpts.
  simpl. auto. auto.

  apply IHpts. auto.
Qed.


Definition invalidatecookie : forall (c: cproc) (cts: list tab) (cookie_msg : list ascii) (PRE:hprop) (tr : [Trace]),
  STsep (tr ~~ PRE * traced tr * thandles cts)
        (fun tr':[Trace] => tr ~~ tr' ~~ PRE * thandles cts * traced tr' * [tr' = K2TSetCookieActions c cts cookie_msg ++ tr]).

  refine (
      fun (c:cproc) (cts:list tab) (cookie:list ascii) (PRE:hprop) (tr:[Trace]) =>
        {{ Fix3
              (fun pts ts tr' =>  tr ~~ tr' ~~ PRE * traced tr' * thandles cts 
                * [pts ++ ts = cts ]
                * [tr' = K2TSetCookieActions c pts cookie ++ tr])
              (fun pts ts tr' tr'' => tr ~~ tr' ~~ tr'' ~~ PRE  * traced tr'' * thandles cts  
                * [pts ++ ts = cts] 
                * [tr' = K2TSetCookieActions c pts cookie ++ tr]
                * [tr'' = K2TSetCookieActions c ts cookie ++ tr'])
              (fun self pts ts tr' =>
                match ts as ncts return ts = ncts -> _ with
                | nil => fun _ => {{Return tr'}}
                | t :: cts'' => fun _ =>
                if (laeq (cproc_domain c) (get_topdomain_tab (tab_origin_url t))) then
                    writemsg t (K2TSetCookie (length_in_size cookie) cookie) tr' <@> 
                    (tr ~~ tr' ~~ [pts ++ ts = cts ] * [tr' = K2TSetCookieActions c pts cookie ++ tr]
                      * thandles_drop cts t * PRE) ;;
                    {{self (pts ++ t :: nil) cts'' (tr' ~~~ WroteMsg t (K2TSetCookie (length_in_size cookie) cookie) ++ tr')}}
                else
                    {{self (pts ++ t :: nil) cts'' (tr' ~~~ tr')}}

                end (refl_equal ts)
              )
              nil cts tr}}); sep fail auto.
  
  apply unpack_thandles; auto.
  apply in_or_app.
  right. simpl. auto.
  apply himp_inj_conc; auto; intros.
  rewrite K2TSetCookieActions_inv. simpl. auto.
  rewrite _H0. apply la_eq_refl.
  (*
  unfold not. intros. destruct H3. symmetry. auto.
  *)
  apply himp_inj_conc.
  rewrite app_assoc. simpl; auto.
  
  apply repack_thandles; auto.

  apply in_or_app.
  right. simpl. auto.
  
  apply himp_inj_conc.
  destruct (laeq (cproc_domain c) (get_topdomain_tab (tab_origin_url t))); simpl; auto.
  rewrite app_assoc. auto.
  rewrite _H0 in n. destruct n; auto.

  (*
  destruct H4; auto.
  unfold WroteMsg. simpl; auto.
  rewrite app_assoc. simpl; auto.

  destruct (tabeq t0 t); simpl; auto.

  destruct H4; auto.
  destruct n; auto.
  *)
  apply himp_inj_conc.
  
  rewrite K2TSetCookieActions_inv in H. simpl in H.
  inversion H; auto.

  rewrite _H0; apply la_eq_refl.
  (*
  unfold not; intros. destruct H4. symmetry; auto.
  *)
  apply himp_inj_conc'.
  apply himp_refl.

  rewrite app_assoc. simpl; auto.
  
  apply himp_inj_conc.

  rewrite K2TSetCookieActions_inv2; auto.

  unfold not. intros.
  destruct _H0.
  eapply la_eq_same; eauto. apply la_eq_refl.

  apply himp_inj_conc'.
  apply himp_refl.

  rewrite app_assoc. simpl; auto.
  
  apply himp_inj_conc.
  (*
  rewrite K2TSetCookieActions_inv2; auto.

  apply himp_inj_conc'.
  apply himp_refl.

  rewrite app_assoc. simpl; auto.

  apply himp_inj_conc.
  *)
  destruct (laeq (cproc_domain c) (get_topdomain_tab (tab_origin_url t))); simpl; auto.
  destruct _H0. auto.

  apply himp_inj_conc.
  rewrite K2TSetCookieActions_inv2; auto.
  unfold not.  intros.
  destruct _H0.
  eapply la_eq_same; eauto. apply la_eq_refl.

  apply himp_inj_conc'.
  apply himp_refl.

  rewrite app_assoc. simpl; auto.
Qed.


Fixpoint lkup_cproc (cprocs: list cproc) (ic: ichan) : option cproc :=
  match cprocs with
  | c::cs =>
      if iceq (c2k c) ic then
        Some c
      else
        lkup_cproc cs ic
  | nil =>
      None
  end.

Lemma lkup_cproc_in:
  forall ts ic t,
  lkup_cproc ts ic = Some t ->
  In t ts.
Proof.
  induction ts; simpl; intros. discriminate.
  destruct (iceq (c2k a) ic).
    inv H. left; auto.
    right. eapply IHts; eauto.
Qed.

Lemma uniq_cproc_dom:
  forall cs c,
  In c cs ->
  uniq (map cproc_domain cs) ->
  get_cproc (cproc_domain c) cs = Some c.
Proof.
  induction cs; simpl; intros. contradiction.
  destruct H. subst.
  destruct (laeq (cproc_domain c) (cproc_domain c));
    auto || congruence.
  inv H0.
  destruct (laeq (cproc_domain a) (cproc_domain c)); auto.
  destruct H4. rewrite e. apply in_map; auto.
Qed.

Fixpoint lkup_cproc_dom (cprocs: list cproc) (dom: list ascii) : option cproc :=
  match cprocs with
  | c::cs =>
      if laeq (cproc_domain c) dom then
        Some c
      else
        lkup_cproc_dom cs dom
  | nil =>
      None
  end.

Definition khandle_c:
  forall (s: kstate) (c: cproc),
  STsep (kcorrect s * (tr :~~ ktr s in [In c (cur_cprocs tr)]))
        (fun s' => kcorrect s').
Proof.
  unfold kcorrect; intros; destruct s as [ct cts ccps tr].
  Opaque ReadCMsg.
  remember (tr ~~ [cur_tab tr = ct /\ cur_tabs tr = cts /\ 
                   cur_cprocs tr = ccps /\ TraceOK tr /\ procs_distinct tr]) as PRE.
  refine (
    m <- readcmsg c tr <@>
      fhandle stdin * fhandle stdout * ohandle gout * thandles cts * chandles_drop ccps c * PRE * [In c ccps];
    match m as m' return m = m' -> _ with
    | C2KSetCookie s cookie => fun _ =>
      dtr <- invalidatecookie c cts cookie (fhandle stdin * fhandle stdout * ohandle gout * chandles ccps * PRE * [In c ccps]) (tr ~~~ ReadCMsg c m ++ tr);
      {{ Return (mkst ct cts ccps 
        (tr ~~~ (K2TSetCookieActions c cts cookie) ++  ReadCMsg c m ++ tr)) }}
    | C2KResultCookie s cookie_msg => fun _ =>
        let ot := lkup_tab cts (get_tab_id cookie_msg) in
        match ot as ot' return ot = ot' -> _ with
        | Some t => fun _ =>
            if laeq (get_topdomain_tab (tab_origin_url t)) (cproc_domain c) then
              let pay := get_cookie_content cookie_msg in
              writemsg t (ResultCookie (length_in_size pay) pay)
                (tr ~~~ ReadCMsg c (C2KResultCookie s cookie_msg) ++ tr) <@>
                fhandle stdin * fhandle stdout * ohandle gout * thandles_drop cts t * chandles ccps * PRE * [ In c ccps];;
              {{ Return (mkst ct cts ccps 
                (tr ~~~ WroteMsg t (ResultCookie (length_in_size pay) pay) ++ ReadCMsg c (C2KResultCookie s cookie_msg) ++ tr)) }}
            else
              {{ Return (mkst ct cts ccps
                (tr ~~~ ReadCMsg c (C2KResultCookie s cookie_msg) ++ tr)) }}
        | None => fun _ =>
            {{ Return (mkst ct cts ccps
              (tr ~~~  ReadCMsg c (C2KResultCookie s cookie_msg) ++ tr)) }}
        end (refl_equal ot)
    end (refl_equal m)
  );
  sep fail auto.

  apply unpack_chandles; auto.

  apply himp_comm_prem.
  apply repack_chandles; auto.

  (*
  apply himp_comm_prem.
  apply himp_assoc_prem2.
  apply himp_comm_conc.
  apply himp_assoc_conc1.
  apply himp_comm_conc.
  apply himp_split.
  apply himp_comm_conc. apply unpack_thandles; auto.
  eapply lkup_tab_in; eauto.
  apply himp_comm_prem. apply repack_chandles; auto.
  *)
  apply himp_pure'.
  repeat split.

  (* working *)
  rewrite <- cur_tab_same_over_K2TSetCookieActions with (tr := ReadCMsg c (C2KSetCookie s cookie) ++ x0).
  Transparent ReadCMsg. simpl. auto. simpl. auto.

  rewrite <- cur_tabs_same_over_K2TSetCookieActions with (tr := ReadCMsg c (C2KSetCookie s cookie) ++ x0).
  simpl. auto. simpl. auto.

  rewrite <- cur_cprocs_same_over_K2TSetCookieActions with (tr := ReadCMsg c (C2KSetCookie s cookie) ++ x0).
  Transparent ReadCMsg. simpl. auto. simpl. auto.

  econstructor. auto.
  econstructor; eauto.

  rewrite <- cur_tabs_same_over_K2TSetCookieActions with (tr := ReadCMsg c (C2KSetCookie s cookie) ++ x0).
  rewrite <- cur_cprocs_same_over_K2TSetCookieActions with (tr := ReadCMsg c (C2KSetCookie s cookie) ++ x0).
  simpl. inv H5; auto. auto. auto.

  rewrite <- cur_tabs_same_over_K2TSetCookieActions with (tr := ReadCMsg c (C2KSetCookie s cookie) ++ x0).
  rewrite <- cur_cprocs_same_over_K2TSetCookieActions with (tr := ReadCMsg c (C2KSetCookie s cookie) ++ x0).
  simpl. inv H5. auto. auto. auto.

  rewrite <- cur_cprocs_same_over_K2TSetCookieActions with (tr := ReadCMsg c (C2KSetCookie s cookie) ++ x0). simpl. inv H5; auto. auto.

  apply himp_comm_conc.
  apply himp_assoc_conc1.
  apply himp_comm_prem.
  apply himp_assoc_prem1.
  apply himp_comm_prem.
  apply himp_assoc_prem1.
  apply himp_comm_conc.

  apply himp_split.
  apply himp_comm_conc. apply unpack_thandles; auto.
  eapply lkup_tab_in; eauto.
  apply repack_chandles; auto.

  apply himp_inj_conc.
  repeat split.

  econstructor; eauto.
  econstructor; eauto.
  eapply lkup_tab_in; eauto.
  eapply lkup_tab_t2k; eauto.

  rewrite cur_cproc_eq_get_cproc.
  rewrite _H1.
  eapply uniq_cproc_dom; eauto. inv H5; auto.
  Transparent WroteMsg.
  Transparent ReadMsg.
  simpl. inv H5; auto. simpl; inv H5; auto.
  simpl; inv H5; auto.

  apply repack_thandles; auto.
  eapply lkup_tab_in; eauto.



  apply himp_inj_conc.
  repeat split.

  match goal with
  |- TraceOK ?tr =>
    replace tr with
      (  
        nil 
         ++ (ReadCMsg c (C2KResultCookie s cookie_msg))
         ++ x
       )
  end; auto.
  econstructor; eauto.
  econstructor; eauto.

  eapply lkup_tab_in; eauto.
  eapply lkup_tab_t2k; eauto.
  intro Hcon. apply _H1.
  apply cur_cproc_return_requested_domain in Hcon;
    symmetry; auto.
  simpl. inv H5; auto.
  simpl; inv H5; auto.
  simpl; inv H5; auto.

  apply himp_comm_prem.
  apply repack_chandles; auto.

  apply himp_inj_conc.
  repeat split.
 
  match goal with
  |- TraceOK ?tr =>
    replace tr with
      (  
        nil 
         ++ (ReadCMsg c (C2KResultCookie s cookie_msg))
         ++ x
       )
  end; auto.
  econstructor; eauto.

  eapply Kstep_cookie_get_c2k_error_bad_tab_id; eauto.
  simpl; inv H5; auto.
  simpl; inv H5; auto.
  simpl; inv H5; auto.
  apply himp_comm_prem.
  apply repack_chandles; auto.
Qed.

(* input selection *)

Inductive input: Set :=
  | File  : file_desc -> input
  | Tab   : tab -> input
  | CProc : cproc -> input
  | Error : input.

Definition iselect:
  forall (stdin:file_desc) (ts: list tab) (cs: list cproc) (tr: [Trace]),
  STsep (tr ~~ traced tr)
        (fun i =>
          match i with
          | File f  => tr ~~ traced tr * [f = stdin]
          | Tab t   => tr ~~ traced tr * [In t ts]
          | CProc c => tr ~~ traced tr * [In c cs]
          | Error   => tr ~~ traced tr
          end).
Proof.
  intros; refine (
    prod_f_ics <- select stdin (map t2k ts ++ map c2k cs) tr;
    let of := fst prod_f_ics in
    match of as of' return of = of' -> _ with
    | Some f => 
       fun _ => 
         if file_desc_eq f stdin then {{ Return (File f)}}
         else {{ Return Error }}
    | _  => fun _ =>
        let ics := snd prod_f_ics in
        match ics with 
        | ic :: _ =>
          let ot := lkup_tab ts ic in
          match ot as ot' return ot = ot' -> _ with
          | Some t => fun _ => {{ Return (Tab t) }}
          | None   => fun _ =>
              let oc := lkup_cproc cs ic in
              match oc as oc' return oc = oc' -> _ with
              | Some c => fun _ => {{ Return (CProc c) }}
(* this error case never happens. But why do we have to care about it
and mention it here? : How can we remove this case here? *)
              | None   => fun _ => {{ Return Error }}
              end (refl_equal oc)
          end (refl_equal ot)
        | nil => {{ Return Error }}
        end
    end (refl_equal of)
  );
  sep fail auto.
  apply himp_inj_conc'. apply himp_refl.
  eapply lkup_tab_in; eauto.
  apply himp_inj_conc'. apply himp_refl.
  eapply lkup_tab_in; eauto.
  apply himp_inj_conc'. apply himp_refl.
  eapply lkup_cproc_in; eauto.
  apply himp_inj_conc'. apply himp_refl.
  eapply lkup_cproc_in; eauto.
Qed.


Definition kbody:
  forall (s: kstate),
  STsep (kcorrect s)
        (fun s' => kcorrect s').
Proof.
  unfold kcorrect; intros; destruct s as [ct cts ccps tr].
  remember (tr ~~ [cur_tab tr = ct /\ cur_tabs tr = cts /\ cur_cprocs tr = ccps /\ TraceOK tr /\ procs_distinct tr]) as PRE.
  refine (
    i <- iselect stdin cts ccps
      tr <@>
      fhandle stdin * fhandle stdout * ohandle gout * thandles cts * chandles ccps * PRE;
    match i with
    | File f =>
        s <- khandle_u (mkst ct cts ccps tr);
        {{ Return s }}
    | Tab t =>
        s <- khandle_t (mkst ct cts ccps tr) t;
        {{ Return s }}
    | CProc c =>
        s <- khandle_c (mkst ct cts ccps tr) c;
        {{ Return s }}
    | Error =>
        {{ Return (mkst ct cts ccps tr)}}
    end
  );
  unfold kcorrect;
  sep fail auto.
Qed.

Definition kloop:
  forall (s: kstate),
  STsep (kcorrect s)
        (fun s' => kcorrect s').
Proof.
  unfold kcorrect; intros; refine (
  Fix
    (fun s => kcorrect s)
    (fun s s' => kcorrect s')
    (fun self s =>
      s <- kbody s;
      s <- self s;
      {{ Return s }}
    )
    s
  );
  sep fail auto.
Qed.


Definition main:
  STsep (traced nil * fhandle stdin * fhandle stdout * ohandle gout)
        (fun s => kcorrect s).
Proof.
  unfold kcorrect; intros; refine (
    s <- kloop (mkst None nil nil [nil]);
    {{ Return s }}
  );
  unfold kcorrect;
  sep fail auto.
  apply himp_inj_conc'.
  apply himp_refl.
  repeat split; auto; econstructor; eauto.
Qed.



