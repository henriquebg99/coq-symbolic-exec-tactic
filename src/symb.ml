(* returns true if the function is the equality proposition*)
let is_eq (f: Constr.t) : bool = 
  match Constr.kind f with
  | Constr.Ind ((mutind, _), _) -> 
      String.equal (Names.MutInd.to_string mutind) "Coq.Init.Logic.eq"
  | _ -> false
  
let extract_eq_args (ident: Names.Id.t) (gl: Proofview.Goal.t) : Constr.t * Constr.t =
  let env = Proofview.Goal.env gl in
    match EConstr.lookup_named ident env with
    | Context.Named.Declaration.LocalAssum (_, ty) ->
        let sigma = Proofview.Goal.sigma gl in
        let ty' = EConstr.to_constr sigma ty in
        begin match Constr.kind ty' with
        | Constr.App (f, args) -> 
          if is_eq f then
            (Array.get args 1, Array.get args 2) (* 0 is the type! *)
          else 
            CErrors.user_err (Pp.str (Printf.sprintf "%s is not an equality." (Names.Id.to_string ident)))
        | _ -> CErrors.user_err (Pp.str (Printf.sprintf "%s is not an equality." (Names.Id.to_string ident)))
        end
    | _ -> CErrors.user_err (Pp.str (Printf.sprintf "%s is not a local assumption." (Names.Id.to_string ident)))

let rec c2str (c: Constr.t) : string =
  match Constr.kind c with
  | Constr.Lambda (n, tn, t) -> 
    let n_str = 
      begin match (Context.binder_name n) with
      | Names.Name.Anonymous -> "_"
      | Names.Name.Name id -> Names.Id.to_string id
      end in "Lambda(" ^ n_str ^ ", " ^ c2str tn ^ ", " ^ c2str t ^ ")"
  | Constr.Prod (n, tn, t) -> 
    let n_str = 
      begin match (Context.binder_name n) with
      | Names.Name.Anonymous -> "_"
      | Names.Name.Name id -> Names.Id.to_string id
      end in "Prod(" ^ n_str ^ ", " ^ c2str tn ^ ", " ^ c2str t ^ ")" 
  | Constr.LetIn (n, v, tn, t) -> 
    let n_str = 
      begin match (Context.binder_name n) with
      | Names.Name.Anonymous -> "_"
      | Names.Name.Name id -> Names.Id.to_string id
      end in "LetIn(" ^ n_str ^ ", " ^ c2str tn ^ ", " ^ c2str v ^ ", " ^ c2str t ^ ")"

  | Constr.Var id -> Names.Id.to_string id
  | Constr.Ind ((mutind, _), univ) -> Names.MutInd.to_string mutind 
  | Constr.Const (name, univ) -> "(const)" ^Names.Constant.to_string name
  | Constr.Construct (((mutind, _), index), _) -> Names.MutInd.to_string mutind ^ "_c" ^ string_of_int index
  | Constr.Rel i -> "Rel(" ^ string_of_int i ^ ")"
  | Constr.App (f, arr) -> "(" ^ c2str f ^ " " ^ String.concat " " (List.map c2str (Array.to_list arr)) ^ ")"
  | Constr.Case (_, _, _, scr, arr, _, _) -> "match"
  | Constr.Meta _ | Constr.Evar _ | Constr.Sort _ -> "spec"
  | Constr.Fix _ -> "fix"
  | _ -> "other"


(* simplify the expression; may do destruct, to get rid of match or
   fixpoint applications *)
let simplify (c: Constr.t) (h: Names.Id.t) : unit Proofview.tactic = 
  let destruct_match_fixapp : unit Proofview.tactic =
    match Constr.kind c with
    | Constr.App (f, args) ->
      begin match Constr.kind f with
      | Constr.Fix ((skips, index), _) -> 
          (* the index of the structural argument *)
          let struct_ind : int = Array.get skips index in
          (* the structural argument *)
          let struct_arg : Constr.t = Array.get args struct_ind in 
          Tacticals.tclTHEN
            (Induction.destruct false None (EConstr.of_constr struct_arg) None None)
            Tacticals.tclIDTAC
      | Constr.Case _ -> Tacticals.tclIDTAC
      | _ -> CErrors.user_err (Pp.str ("other case, no destruct: " ^ c2str f))
      end
    | _ -> Tacticals.tclIDTAC
    in
    Tacticals.tclTHEN 
      (Tactics.simpl_in_hyp (h, Locus.InHyp))
      destruct_match_fixapp

let simplify' (c: EConstr.t) (h: Names.Id.t) : unit Proofview.tactic = 
  Proofview.Goal.enter (fun gl -> 
    let sigma = Proofview.Goal.sigma gl in
    let c' = EConstr.to_constr sigma c in
    simplify c' h)

let rec get_constructor (c: Constr.t) : (Names.MutInd.t * int) option =
  match Constr.kind c with
  | Constr.Construct (((mi, _), i), _) -> Some (mi, i)
  | Constr.App (f, args) -> 
    begin match get_constructor f with
    | None -> None
    | Some (mi, i) -> Some (mi, i)
    end
  | _ -> None

let rec tactic (idents : Names.Id.t List.t) : unit Proofview.tactic = 
  match idents with
  | [] -> Tacticals.tclIDTAC
  | h :: t -> Tacticals.tclTHEN (Tactics.simpl_in_hyp (h, Locus.InHyp))
    begin Proofview.Goal.enter 
      begin fun gl -> 
        (* we expect h to have the form `eq A arg1 arg2` *)
        let (arg1, arg2) = extract_eq_args h gl in 

        match get_constructor arg1, get_constructor arg2 with
        | Some (mi, i), Some(mi', i') -> 
            if i == i' then
              Inv.inv_tac h (* TODO should inspect the new hypothesis *)
            else
              Equality.discrHyp h
        | _, _ ->
          begin match Constr.kind arg1 with
          (* if arg1 has the form `f args_0 ... args_n` *)
          | Constr.App (f, args) ->
            begin match Constr.kind f with
            | Constr.Var id -> 
                (* unfold variable and rerun *)
                Tacticals.tclTHEN 
                  (Tactics.unfold_in_hyp [(Locus.AllOccurrences, (*Evaluable*)Tacred.EvalVarRef id)] (h, Locus.InHyp))
                  (tactic idents)

            | Constr.Const (name, _) -> 
                (* unfold constant and rerun *)
                Tacticals.tclTHEN 
                  (Tactics.unfold_in_hyp [(Locus.AllOccurrences, (*Evaluable*)Tacred.EvalConstRef name)] (h, Locus.InHyp))
                  (tactic idents)
            
            | Constr.Fix ((skips, index), _) -> 
                (* the index of the structural argument *)
                let struct_ind : int = Array.get skips index in
                (* the structural argument *)
                let struct_arg : Constr.t = Array.get args struct_ind in 
                (* destruct the struct arg of fixpoint to keep reducing *)
                (*Tacticals.tclTHEN
                  (Induction.destruct false None (EConstr.of_constr struct_arg) None None)
                  (tactic idents)*)

                Tacticals.tclTHEN
                  (Induction.destruct false None (EConstr.of_constr struct_arg) None None)
                  (tactic idents)
    

            | _ -> CErrors.user_err (Pp.str ("not supported3" ^ (c2str f)))
            end
          | _ -> CErrors.user_err (Pp.str (c2str arg1))
          end
      end
    end