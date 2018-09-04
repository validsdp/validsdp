(** Heuristic algorithm for "validsdp_intro expr using * as H":
    1. Retrieve the hyps of the context that are inequalities
    2. Store them in a Map composed of pairs (hyp, false = non-selected)
    3. Retrieve the (non-polynomial) vars of expr
    4. Store them in a List
    5. For each hyp (H, false) of the Map, test if a var from List appears in H
    6. If yes, change the hyp to (H, true) and restart at step 3 with (expr:=H)
    7. If no, select the list of (H, true), call it HypList,
       and behave as "validsdp_intro expr using (HypList) as H".
 *)
