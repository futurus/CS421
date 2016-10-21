open Mp4common
      
(* Problem 1 *)
let rec import_list lst =
match lst with
[] -> ConExp Nil
| (x::xs) -> BinExp(Cons, ConExp(Int x), import_list xs);;


(* Problem 2 *)
let elem = 
let el = VarExp "elem" in
let e = VarExp "e" in
let xs = VarExp "xs" in
let nil = ConExp Nil in
let xseqnil = BinExp(Eq, xs, nil) in
let hdxs = MonExp(Head, xs) in
let tlxs = MonExp(Tail, xs) in
let hdxseqe = BinExp(Eq, hdxs, e) in
let elapp = AppExp(el, e) in
let recapp = AppExp(elapp, tlxs) in
let ifthenelse = IfExp(hdxseqe, ConExp(Bool true), recapp) in
let ifthenelseexp = IfExp(xseqnil, ConExp(Bool false), ifthenelse) in
let funexp = FunExp("xs", ifthenelseexp) in
RecExp("elem", "e", funexp, el);;


(* Problem 3 *)
let rec num_of_consts expression =
    match expression with
          VarExp x -> 0
	| ConExp c -> 1
	| IfExp (e1, e2, e3)    -> (num_of_consts e1) + (num_of_consts e2) + (num_of_consts e3)
	| AppExp (e1, e2)       -> (num_of_consts e1) + (num_of_consts e2)
	| BinExp (_, e1, e2)    -> (num_of_consts e1) + (num_of_consts e2)
	| MonExp (_, e)         -> (num_of_consts e)
	| FunExp (_, e)         -> (num_of_consts e)
	| LetExp (_, e1, e2)    -> (num_of_consts e1) + (num_of_consts e2)
	| RecExp (_, _, e1, e2) -> (num_of_consts e1) + (num_of_consts e2)
	| OAppExp (e1, e2)      -> (num_of_consts e1) + (num_of_consts e2)

						     
(* Problem 4 *)
let rec freeVars expression =
    match expression with
	  VarExp x              -> [x]
	| ConExp c              -> []
	| IfExp (e1, e2, e3)    -> (freeVars e1) @ (freeVars e2) @ (freeVars e3)
	| AppExp (e1, e2)       -> (freeVars e1) @ (freeVars e2)
	| BinExp (_, e1, e2)    -> (freeVars e1) @ (freeVars e2)
	| MonExp (_, e)         -> (freeVars e)
	| FunExp (f, e)         -> List.filter (fun y -> not (y = f)) (freeVars e)
	| LetExp (x, e1, e2)    -> (freeVars e1) @ (List.filter (fun y -> not (y = x)) (freeVars e2))
	| RecExp (f, x, e1, e2) -> (List.filter (fun y -> not (y = f || y = x)) (freeVars e1)) @ (List.filter (fun y -> not (y = f)) (freeVars e2))
	| OAppExp (e1, e2)      -> (freeVars e2) @ (freeVars e1)

				   
(* Problem 5 *)
let rec cps expression cont =
    match expression with
          VarExp x               -> AppExp(cont, VarExp x)
        | ConExp c               -> AppExp(cont, ConExp c)
        | IfExp (e1, e2, e3)     ->
	   let r = freshFor (freeVars cont @ freeVars e2 @ freeVars e3) in
	   let e2cps = cps e2 cont in
	   let e3cps = cps e3 cont in
	   cps e1 (FunExp(r, IfExp(VarExp r, e2cps, e3cps)))
	| AppExp (e1, e2)        ->
	   let v1 = freshFor (freeVars e2 @ freeVars cont) in
	   let v2 = freshFor (v1 :: freeVars cont) in
	   let icps = cps e2 (FunExp (v2, AppExp (AppExp (VarExp v1, VarExp v2), cont))) in
	   cps e1 (FunExp (v1, icps))
	| BinExp (binop, e1, e2) ->
	   let v1 = freshFor (freeVars e1 @ freeVars e2 @ freeVars cont) in
	   let v2 = freshFor (v1 :: freeVars e1 @ freeVars e2 @ freeVars cont) in
	   let icps = cps e2 (FunExp (v2, AppExp (cont, BinExp(binop, VarExp v1, VarExp v2)))) in
	   cps e1 (FunExp (v1, icps))
	| MonExp (monop, e)      ->
	   let v = freshFor (freeVars cont) in
	   cps e (FunExp (v, AppExp(cont, MonExp(monop, VarExp v))))
        | FunExp (x, e)          ->
	   let k = freshFor (freeVars e) in
	   let icps = (FunExp (k, (cps e (VarExp k)))) in
	   AppExp (cont, FunExp(x, icps))
	| LetExp (x, e1, e2)     ->
	   let e2cps = cps e2 cont in
	   cps e1 (FunExp (x, e2cps))
	| RecExp (f, x, e1, e2)  ->
	   let v = freshFor (f :: x :: freeVars e1) in
	   let e1cps = cps e1 (VarExp v) in
	   let e2cps = cps e2 cont in
	   RecExp(f, x, FunExp(v, e1cps), e2cps)
	| OAppExp (e1, e2)       ->
	   let v2 = freshFor (freeVars e1 @ freeVars cont) in
	   let v1 = freshFor (v2 :: freeVars cont) in
	   let icps = cps e1 (FunExp (v1, AppExp (AppExp (VarExp v1, VarExp v2), cont))) in
	   cps e2 (FunExp (v2, icps))
