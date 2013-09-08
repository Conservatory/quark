Require Import Ynot.Extract.
Require Import Datatypes.
Require Import List.
Require Import Ascii.
Require Import NArith.
Require Import VCRIO.
Require Import Kernel.
Require Import Message.

Extract Inductive option => "option" ["Some" "None"].

(* common pair repr *)
Extract Inductive prod       => "VCRIOImpl.prod" ["VCRIOImpl.Pair"].
Extract Inlined Constant fst => "VCRIOImpl.fst".
Extract Inlined Constant snd => "VCRIOImpl.snd".

(* vcr IO *)
Extract Constant VCRIO.file_desc  => "VCRIOImpl.file_desc".
Extract Constant VCRIO.readfile  => "VCRIOImpl.readfile".
Extract Constant VCRIO.writestrfile  => "VCRIOImpl.writestrfile".

Extract Constant VCRIO.stdin  => "VCRIOImpl.stdin".
Extract Constant VCRIO.stdout => "VCRIOImpl.stdout".

Extract Constant VCRIO.file_desc_eq   => "VCRIOImpl.file_desc_eq".


Extract Constant VCRIO.ichan  => "VCRIOImpl.ichan".
Extract Constant VCRIO.ochan  => "VCRIOImpl.ochan".
Extract Constant VCRIO.iceq   => "VCRIOImpl.iceq".
Extract Constant VCRIO.oceq   => "VCRIOImpl.oceq".
Extract Constant VCRIO.mousepos => "VCRIOImpl.mousepos".
Extract Constant VCRIO.writen  => "VCRIOImpl.writen".
Extract Constant VCRIO.readn  => "VCRIOImpl.readn".
Extract Constant Message.readmsg  => "VCRIOImpl.readmsg".
Extract Constant Message.writemsg  => "VCRIOImpl.writemsg".
Extract Constant Message.writegmsg  => "VCRIOImpl.writegmsg".
Extract Constant VCRIO.sendsocket   => "VCRIOImpl.sendsocket".
Extract Constant VCRIO.mktab  => "VCRIOImpl.mktab".
Extract Constant VCRIO.wget   => "VCRIOImpl.wget".
Extract Constant VCRIO.select => "VCRIOImpl.select".
Extract Constant VCRIO.endorse => "VCRIOImpl.endorse".

Extract Constant VCRIO.gout   => "VCRIOImpl.gout".


Extract Constant VCRIO.mkcproc  => "VCRIOImpl.mkcproc".
Extract Constant Message.writecmsg  => "VCRIOImpl.writecmsg".
Extract Constant Message.readcmsg  => "VCRIOImpl.readcmsg".

(* other types *)
Extract Constant VCRIO.tab  => "VCRIOImpl.tab".
Extract Constant VCRIO.cproc  => "VCRIOImpl.cproc".
Extract Inductive positive => "VCRCommon.positive" [ "VCRCommon.XI" "VCRCommon.XO"  "VCRCommon.XH" ].
Extract Inductive Message.maybe_t2k_msg => "VCRCommon.maybe_t2k_msg" [ "VCRCommon.T2Kmsg" "VCRCommon.BadTag" ].
Extract Inductive Message.t2k_msg => "VCRCommon.t2k_msg" [ "VCRCommon.Display" "VCRCommon.ReqHtml" "VCRCommon.RequestSocket" "VCRCommon.Navigate" "VCRCommon.GetCookie" "VCRCommon.SetCookie"].
Extract Inductive Message.k2t_msg => "VCRCommon.k2t_msg" [ "VCRCommon.Render" "VCRCommon.KeyPress" "VCRCommon.MouseClick" "VCRCommon.RspHtml" "VCRCommon.ResultSocket" "VCRCommon.ResultCookie" "VCRCommon.InvalidateCookie"].
Extract Inductive Message.k2g_msg => "VCRCommon.k2g_msg" [ "VCRCommon.K2GDisplay" ].
Extract Inductive Message.c2k_msg => "VCRCommon.c2k_msg" [ "VCRCommon.C2KSetCookie" "VCRCommon.C2KResultCookie" ].
Extract Inductive Message.k2c_msg => "VCRCommon.k2c_msg" [ "VCRCommon.K2CSetCookie" "VCRCommon.K2CGetCookie" ].

(* utility functions *)
Extract Constant VCRIO.is_safe_sock_dest_on => "VCRIOImpl.is_safe_sock_dest_on".
Extract Constant VCRIO.tab_id_to_la => "VCRIOImpl.tab_id_to_la".
Extract Constant VCRIO.get_tab_id => "VCRIOImpl.get_tab_id".
Extract Constant VCRIO.get_topdomain_cookie => "VCRIOImpl.get_topdomain_cookie".
Extract Constant VCRIO.get_topdomain_tab => "VCRIOImpl.get_topdomain_tab".

Extraction ".extract/Kernel.ml" Kernel.main.
