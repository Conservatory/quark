(*
   Quark is Copyright (C) 2012-2015, Quark Team.

   You can redistribute and modify it under the terms of the GNU GPL,
   version 2 or later, but it is made available WITHOUT ANY WARRANTY.

   For more information about Quark, see our web site at:
   http://goto.ucsd.edu/quark/
*)



(*
Extract Inductive positive => "VCRCommon.positive" [ "VCRCommon.xI" "VCRCommon.xO"  "VCRCommon.xH" ].
Extract Inductive Message.maybe_t2k_msg => "VCRCommon.maybe_t2k_msg" [ "VCRCommon.T2Kmsg" "VCRCommon.BadTag" ].
Extract Inductive Message.t2k_msg => "VCRCommon.t2k_msg" [ "VCRCommon.Display" "VCRCommon.ReqHtml" "VCRCommon.RequestSocket" ].
*)

type positive =
  | XI of positive
  | XO of positive
  | XH

(* do we have to care about little/big endian here? *)
let rec pos2int pos = 
  match pos with 
  | XI p -> ( (pos2int p) lsl 1) + 1
  | XO p -> ( (pos2int p) lsl 1)
  | XH -> 1

let rec last_one_bit v idx =
  if idx <= 0 then 0
  else if ((1 lsl (idx-1)) land v) <> 0 then idx
  else last_one_bit v (idx - 1)

let rec int2pos_worker v max idx = 
  if idx >= max then XH
  else if ((1 lsl (idx-1)) land v) <> 0 then (XI (int2pos_worker v max (idx + 1)))
  else (XO (int2pos_worker v max (idx + 1)))

let int2pos v = 
  let idx = last_one_bit v 32 in
  int2pos_worker v idx 1

type t2k_msg =
  | Display of positive * MlCoq.ascii list
  | ReqHtml of positive * MlCoq.ascii list
  | RequestSocket of positive * MlCoq.ascii list
  | Navigate of positive * MlCoq.ascii list
  | GetCookie of positive * MlCoq.ascii list
  | SetCookie of positive * MlCoq.ascii list

type maybe_t2k_msg =
  | T2Kmsg of t2k_msg
  | BadTag of MlCoq.ascii list

type k2t_msg =
  | Render of positive * MlCoq.ascii list
  | KeyPress of positive * MlCoq.ascii list
  | MouseClick of positive * MlCoq.ascii list
  | RspHtml of positive * MlCoq.ascii list
  | ResultSocket of positive * MlCoq.ascii list
  | ResultCookie of positive * MlCoq.ascii list
  | InvalidateCookie of positive * MlCoq.ascii list

type k2g_msg =
  | K2GDisplay of positive * MlCoq.ascii list

type k2c_msg =
  | K2CSetCookie of positive * MlCoq.ascii list
  | K2CGetCookie of positive * MlCoq.ascii list

type c2k_msg =
  | C2KSetCookie of positive * MlCoq.ascii list
  | C2KResultCookie of positive * MlCoq.ascii list

