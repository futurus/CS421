open Mp5common

let rec gather_exp_ty_substitution gamma exp tau =
  let judgment = ExpJudgment(gamma, exp, tau) in
  match exp
  with ConstExp c ->
       let tau' = const_signature c in
       (match unify [(tau, freshInstance tau')]
        with None       -> None
           | Some sigma -> Some(Proof([], judgment), sigma))
     | VarExp x ->
	(match lookup_env gamma x
	 with None         -> None
	    | Some gamma_x ->
	       (match unify [(tau, freshInstance gamma_x)]
		with None        -> None
		   | Some sigma  -> Some(Proof([], judgment), sigma)))
     | BinOpAppExp(binop, e1, e2) ->
	let tau' = binop_signature binop in
	let tau1 = fresh () in
	let tau2 = fresh () in
	(match gather_exp_ty_substitution gamma e1 tau1
	 with None -> None
	    | Some (proof1, sigma1) ->
	       (match gather_exp_ty_substitution (env_lift_subst sigma1 gamma) e2 tau2
		with None -> None
		   | Some (proof2, sigma2) ->
		      let map = mk_fun_ty tau1 (mk_fun_ty tau2 tau) in
		      let sigma21 = subst_compose sigma2 sigma1 in
		      (match unify [(monoTy_lift_subst sigma21 map, freshInstance tau')]
		       with None -> None
			  | Some sigma3 -> Some(Proof([proof1; proof2], judgment), subst_compose sigma3 sigma21))))
     | MonOpAppExp(monop, e) ->
	let tau' = monop_signature monop in
	let tau1 = fresh () in
	(match gather_exp_ty_substitution gamma e tau1
	 with None -> None
	    | Some (proof, sigma) ->
	       let map = mk_fun_ty tau1 tau in
	       (match unify [(monoTy_lift_subst sigma map, freshInstance tau')]
		with None -> None
		   | Some sigma1 -> Some(Proof([proof], judgment), subst_compose sigma1 sigma)))
     | IfExp (e1, e2, e3) ->
	(match gather_exp_ty_substitution gamma e1 bool_ty
	 with None -> None
	    | Some (proof1, sigma1) ->
	       (match gather_exp_ty_substitution (env_lift_subst sigma1 gamma) e2 (monoTy_lift_subst sigma1 tau)
		with None -> None
		   | Some (proof2, sigma2) ->
		      let sigma21 = subst_compose sigma2 sigma1 in
		      (match gather_exp_ty_substitution (env_lift_subst sigma21 gamma) e3 (monoTy_lift_subst sigma21 tau)
		       with None -> None
			  | Some (proof3, sigma3)
			    -> Some(Proof([proof1; proof2; proof3], judgment), subst_compose sigma3 sigma21))))
     | FnExp(x, e) ->
	let tau1 = fresh () in
	let tau2 = fresh () in
	(match gather_exp_ty_substitution (ins_env gamma x (polyTy_of_monoTy tau1)) e tau2
	 with None -> None
	    | Some (proof, sigma) ->
	       (match unify [(monoTy_lift_subst sigma tau, monoTy_lift_subst sigma (mk_fun_ty tau1 tau2))]
		with None -> None
		   | Some sigma1 -> Some(Proof([proof], judgment), subst_compose sigma1 sigma)))
     | AppExp(e1, e2) ->
	let tau1 = fresh () in
	(match gather_exp_ty_substitution gamma e1 (mk_fun_ty tau1 tau)
	 with None -> None
	    | Some (proof1, sigma1) ->
	       let tau2 = fresh () in
	       (match gather_exp_ty_substitution (env_lift_subst sigma1 gamma) e2 (monoTy_lift_subst sigma1 tau1)
		with None -> None
		   | Some (proof2, sigma2) ->
		      Some(Proof([proof1; proof2], judgment), subst_compose sigma2 sigma1)))
     | RaiseExp(e) ->
	(match gather_exp_ty_substitution gamma e int_ty
	 with None -> None
	    | Some(proof, sigma) ->
	       Some(Proof([proof], judgment), sigma))
     | LetExp(dec1, e) ->
	(match gather_dec_ty_substitution gamma dec1
	 with None -> None
	    | Some (proof1, delta, sigma1) ->
	       (match gather_exp_ty_substitution (sum_env delta (env_lift_subst sigma1 gamma)) e (monoTy_lift_subst sigma1 tau)
		with None -> None
		   | Some (proof2, sigma2) ->
		      Some(Proof([proof1; proof2], judgment), subst_compose sigma2 sigma1)))
     | HandleExp(e, intopt1, exp1, exps) ->
	(match gather_exp_ty_substitution gamma e tau
	 with None -> None
	    | Some (proof, sigma) ->
	       (match List.fold_left (fun a
				      -> fun (_, ei)
					 -> match a
					    with None -> None
					       | Some(pfs, sgs) ->
						  (match gather_exp_ty_substitution (env_lift_subst sgs gamma) ei (monoTy_lift_subst sgs tau)
						   with None -> None
						      | Some (pf, sg)
							-> Some(pf::pfs, subst_compose sg sgs))) (* f *)
				     (Some([proof], sigma)) (* a *)
				     ((intopt1, exp1) :: exps) (* x1,...,xn *)
		with None -> None
		   | Some(proofs, sigmas) ->
		      Some(Proof(List.rev proofs, judgment), sigmas)))
     | _ -> raise (Failure "Not implemented yet")

and gather_dec_ty_substitution gamma dec =
  match dec
  with Val(x, e) ->
       let tau = fresh () in
       (match gather_exp_ty_substitution gamma e tau
	with None -> None
	   | Some (proof, sigma) ->
	      let env' = make_env x (gen (env_lift_subst sigma gamma) (monoTy_lift_subst sigma tau)) in
	      Some(Proof([proof], DecJudgment(gamma, dec, env')), env', sigma))
     | Rec(f, x, e) ->
	let tau1 = fresh () in
	let tau2 = fresh () in
	let map = mk_fun_ty tau1 tau2 in
	(match gather_exp_ty_substitution (ins_env (ins_env gamma x (polyTy_of_monoTy tau1)) f (polyTy_of_monoTy map)) e tau2
	 with None -> None
	    | Some (proof, sigma) ->
	       let env' = make_env f (gen (env_lift_subst sigma gamma) (monoTy_lift_subst sigma map)) in
	       Some(Proof([proof], DecJudgment(gamma, dec, env')), env', sigma))
     | Seq(dec1, dec2) ->
	(match gather_dec_ty_substitution gamma dec1
	 with None -> None
	    | Some (proof1, delta1, sigma1) ->
	       (match gather_dec_ty_substitution (env_lift_subst sigma1 (sum_env delta1 gamma)) dec2
		with None -> None
		   | Some (proof2, delta2, sigma2) ->
		      let sigma21 = subst_compose sigma2 sigma1 in
		      let env' = env_lift_subst sigma21 (sum_env delta2 delta1) in
		      Some(Proof([proof1; proof2], DecJudgment(gamma, dec, env')), env', sigma21)))
     | Local(dec1, dec2) ->
	(match gather_dec_ty_substitution gamma dec1
	 with None -> None
	    | Some (proof1, delta1, sigma1) ->
	       (match gather_dec_ty_substitution (env_lift_subst sigma1 (sum_env delta1 gamma)) dec2
		with None -> None
		   | Some (proof2, delta2, sigma2) ->
		      let sigma21 = subst_compose sigma2 sigma1 in
		      let env' = env_lift_subst sigma21 delta2 in
		      Some(Proof([proof1; proof2], DecJudgment(gamma, dec, env')), env', sigma21)))
     | _ -> raise (Failure "Not implemented yet")
