(* 
 * Vu Nguyen
 * CS421 - Summer 2015
 * MP2
 *)

open Mp2common

(* Problem 1 *)
let rev_apply f (x,y) = 
	(f y, f x);;


(* Problem 2 *)
let rec s n = 
	if n <= 1 then 1
	else if n mod 2 = 0 then 3 * s (n/2)
	else 2 + s (n-1);;


(* Problem 3 *)
let rec rle lst = 
	let rec aux l c =
		match l with [] -> []
		| (x :: xs) -> 
			match xs with [] -> [(x, c + 1)]
			| (y :: ys) -> if x = y then aux xs (c + 1)
					else [(x, c + 1)] @ aux xs 0
	in aux lst 0;;


(* Problem 4 *)
let rec merge l1 l2 = 
	let rec aux lst1 lst2 result =
		match lst1, lst2 with
		[], [] -> result
		| [], (y :: ys) -> aux [] ys (result @ [y])
		| (x :: xs), [] -> aux xs [] (result @ [x])
		| (x :: xs), (y :: ys) -> if x <= y then aux xs (y :: ys) (result @ [x])
					else aux (x :: xs) ys (result @ [y])
	in aux l1 l2 [];;


(* Problem 5 *)
let rec separate l = 
	let rec aux l odds evens =
		match l with [] -> (odds, evens)
		| (x :: xs) -> if x mod 2 = 1 then aux xs (odds @ [x]) evens
				else aux xs odds (evens @ [x])
	in aux l [] [];;


(* Problem 6 *)
let rec maxsumseq l = 
	let rec aux list cmax gmax =
		match list with [] -> gmax
		| (x :: xs) -> if (cmax + x) < 0 then aux xs 0 gmax
				else if (cmax + x) > gmax then aux xs (cmax + x) (cmax + x)
					else aux xs (cmax + x) gmax
	in aux l 0 0;;


(* Problem 7 *)
let check_adj adj_list (a,b) = 
	if (a < 0 || b < 0) then false
	else
		let rec exist1 goal current list =
			match list with
				[] -> false
				| (x :: xs) -> if current = goal then 
							let rec exist2 g l =
								match l with [] -> false
								| (y :: ys) -> if y = g then true
										else exist2 g ys
							in exist2 b x
						else exist1 goal (current + 1) xs
		in exist1 a 0 adj_list;;


(* Problem 8 *)
let cumsum l = 
	let rec cs_aux l s r =
		match l with [] -> r
		| (x :: xs) -> cs_aux xs (x + s) (r @ [x + s])
	in cs_aux l 0 [];;
