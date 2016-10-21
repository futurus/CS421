open Mp3common

(* Problem 1 *)
let minmax lst = 
if lst = [] 
then (0, 0)
else List.fold_left (fun (mi, ma) -> fun elem -> ((min elem mi), (max elem ma))) (max_int, min_int) lst;;

let minmax_list lst = 
List.map minmax lst;;


(* Problem 2 *)
let cumlist_step x y = [x] :: (List.map (fun elem -> x::elem) y);; (* x: int, elem, y: list *)
let cumlist lst = List.fold_right cumlist_step lst [];;


(* Problem 3 *)
let revsplit_step f x y = 
if f y = true then match x with (l1, l2) -> ([y] @ l1, l2)
else match x with (l1, l2) -> (l1, [y] @ l2);;

let revsplit f lst = List.fold_left (revsplit_step f) ([], []) lst;;


(* Problem 4 *)
let andk a b k = k (a && b);;
let ork a b k = k (a || b);;
let landk a b k = k ((land) a b);;
let lork a b k = k ((lor) a b);;
let lxork a b k = k ((lxor) a b);;
let expk a k = k (exp a);;
let logk a k = k (log a);;
let powk a b k = k (a ** b);;


(* Problem 5 *)
let modaddk a b n k = addk a b (fun apb -> modk apb n k);;
let modsubk a b n k = subk a b (fun asb -> modk asb n k);;
let modmulk a b n k = mulk a b (fun amb -> modk amb n k);;
let modeqk a b n k = subk a b (fun asb -> modk asb n (fun c -> eqk c 0 k));;


(* Problem 6 *)
let rec power a n = if n = 0 then 1 else a * power a (n-1);;

let rec powerk a n k =
eqk n 0
(fun b -> if b then k 1
     else subk n 1
     (fun s -> powerk a s
	  (fun m -> mulk a m k)));;


(* Problem 7 *)
let rec dup_alt l =
match l with
[] -> []
| (x::[]) -> l
| (x::y::xs) -> x::y::y::(dup_alt xs);;

let rec dup_altk l k =
match l with [] -> k []
| (x::[])-> k l
| (x::y::xs) -> dup_altk xs (fun n -> consk y n (fun m -> consk y m (fun o -> consk x o k)));;


(* Problem 8 *)
let rec rev_map f l =
match l with
[] -> []
| (x::xs) -> (f x) :: rev_map f xs;;

let rec rev_mapk f l k = 
match l with
[] -> k []
| (x::xs) -> rev_mapk f xs (fun m -> f x (fun n -> consk n m k));;


(* Problem 9 *)
let rec partition l p =
match l with
[] -> ([], [])
| (x::xs) -> (match partition xs p with (t, f) -> if p x = true then (x::t, f) else (t, x::f));;

let rec partitionk l p k =  
match l with
[] -> ([], [])
| (x::xs) -> (match partitionk xs p k with
		    (t, f) -> p x
		    (fun m -> eqk m true
			 (fun n -> if n then consk x t (fun o -> pairk o f k)
			      else consk x f (fun q -> pairk t q k))));;
