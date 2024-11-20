val tactic : Names.Id.t List.t -> unit Proofview.tactic
val simplify' : EConstr.t -> Names.Id.t -> unit Proofview.tactic