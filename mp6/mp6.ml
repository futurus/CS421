open Mp6common

(* Problem 0*)
let asMonoTy1 () = mk_fun_ty bool_ty (mk_list_ty int_ty);;
let asMonoTy2 () = mk_fun_ty (TyVar 0) (mk_fun_ty (TyVar 1) (mk_fun_ty (TyVar 2) (TyVar 3)));;
let asMonoTy3 () = mk_fun_ty (TyVar 0) (mk_list_ty (mk_pair_ty (TyVar 1) int_ty));;
let asMonoTy4 () = mk_pair_ty (string_ty) (mk_fun_ty (mk_list_ty (TyVar 2)) (TyVar 1));;

(* Problem 1*)
let rec subst_fun subst m =
  match subst with [] -> TyVar m
		 | (n, ty) :: rest -> if n = m then ty else subst_fun rest m;;

(* Problem 2*)
let rec monoTy_lift_subst subst monoTy =
  match monoTy with TyVar x -> subst_fun subst x
		  | TyConst(c, list) -> TyConst(c, List.map (monoTy_lift_subst subst) list);;

(* Problem 3*)
let rec occurs x ty =
  match ty with TyVar a -> x = a
	      | TyConst(c, list) -> List.exists (occurs x) list;;

(* Problem 4*)
let rec unify eqlst =
  let rec union l1 l2 existing =
    match l1, l2 with [], [] -> Some existing
		    | e1::tl1, e2::tl2 -> union tl1 tl2 ((e1, e2)::existing)
		    | _ -> None
  in
  match eqlst with
    [] -> Some([])
  | (s, t)::eqns ->
     (* Delete *)
     if s = t then unify eqns
     else (match (s, t) with
     (* Orient *)
	     (TyConst(c, tl), TyVar(x)) -> unify ((TyVar(x), TyConst(c, tl))::eqns)
     (* Decompose *)
	   | (TyConst(c1, tl1), TyConst(c2, tl2)) ->
	      if c1 = c2 then (match (union tl1 tl2 eqns)
			       with None -> None
				  | Some(eqns') -> unify eqns')
	      else None
     (* Eliminate *)
	   | (TyVar(x), t) ->
	      if occurs x t then None
	      else let eqns' = List.map (fun (t1, t2) -> (monoTy_lift_subst [(x, t)] t1, monoTy_lift_subst [(x, t)] t2)) eqns
		   in (match unify eqns' with
			 None -> None
			| Some(phi) -> Some((x, monoTy_lift_subst phi t)::phi)));;

(* Problem 5: No Credit *)
let equiv_types ty1 ty2 = failwith "Not implemented"
