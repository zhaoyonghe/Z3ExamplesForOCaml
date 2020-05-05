open Z3
open Z3.Z3Array
open Z3.Model
open Z3.Symbol
open Z3.Sort
open Z3.Expr
open Z3.Boolean
open Z3.FuncDecl
open Z3.Goal
open Z3.Tactic
open Z3.Tactic.ApplyResult
open Z3.Probe
open Z3.Solver
open Z3.Arithmetic
open Z3.Arithmetic.Integer
open Z3.Arithmetic.Real
open Z3.BitVector
open Z3.Quantifier

let print_check (solver: Solver.solver): unit =
	Printf.printf "%s\n" (string_of_status (Solver.check solver []))

let print_model (solver: Solver.solver): unit = 
	try
		match (Solver.get_model solver) with
		| Some m -> Printf.printf "%s\n" (Model.to_string m)
		| None -> Printf.printf "no model\n"		
	with
	| _ -> Printf.printf "no model\n"
	(* It should return None, but actually raises error. *)

let print_proof (solver: Solver.solver): unit = 
	try
		match (Solver.get_proof solver) with
		| Some p -> Printf.printf "%s\n" (Expr.to_string p)
		| None -> Printf.printf "no proof\n"		
	with
	| _ -> Printf.printf "no get_proof\n"
	(* It should return None, but actually raises error. *)

(*
	from z3 import *
	Tie, Shirt = Bools('Tie Shirt')
	s = Solver()
	s.add(Or(Tie, Shirt), 
	    Or(Not(Tie), Shirt), 
	    Or(Not(Tie), Not(Shirt)))
	print(s.check())
	print(s.model())
*)
let test1 (ctx: context): unit = 
	let tie: Symbol.symbol = Symbol.mk_string ctx "Tie" in
	let shirt: Symbol.symbol = Symbol.mk_string ctx "Shirt" in
	let bool_sort: Sort.sort = Boolean.mk_sort ctx in
	let tie_expr: Expr.expr = Expr.mk_const ctx tie bool_sort in 
	let shirt_expr: Expr.expr = Expr.mk_const ctx shirt bool_sort in 
	let solver = (mk_solver ctx None) in
	(Solver.add solver [
		 Boolean.mk_or ctx [tie_expr; shirt_expr]; 
		 (* Boolean.mk_or ctx [(Boolean.mk_not ctx shirt_expr); tie_expr]; unsatisfiable *)
		 Boolean.mk_or ctx [(Boolean.mk_not ctx tie_expr); shirt_expr];
		 Boolean.mk_or ctx [(Boolean.mk_not ctx tie_expr); (Boolean.mk_not ctx shirt_expr)]
		];
	print_check solver;
	print_model solver)

(*
	Z = IntSort()
	f = Function('f', Z, Z)
	x, y, z = Ints('x y z')
	A = Array('A', Z, Z)
	fml = Implies(x + 2 == y, f(Store(A, x, 3)[y - 2]) == f(y - x + 1))
	solve(Not(fml))
*)
let test2 (ctx: context): unit =
	let int_sort: Sort.sort = Arithmetic.Integer.mk_sort ctx in
	let f: FuncDecl.func_decl = FuncDecl.mk_func_decl_s ctx "f" [int_sort] int_sort in
	let x: Expr.expr = Arithmetic.Integer.mk_const_s ctx "x" in
	let y: Expr.expr = Arithmetic.Integer.mk_const_s ctx "y" in
	(* unused variable z *)
	let z: Expr.expr = Arithmetic.Integer.mk_const_s ctx "z" in
	let arr: Expr.expr = Z3Array.mk_const_s ctx "arr" int_sort int_sort in
	let one: Expr.expr = Arithmetic.Integer.mk_numeral_i ctx 1 in
	let two: Expr.expr = Arithmetic.Integer.mk_numeral_i ctx 2 in
	let three: Expr.expr = Arithmetic.Integer.mk_numeral_i ctx 3 in
	let implies_l: Expr.expr = Boolean.mk_eq ctx (Arithmetic.mk_add ctx [x; two]) y in
	(* f(Store(A, x, 3)[y - 2]) *)
	let temp1: Expr.expr = 
		FuncDecl.apply f [(Z3Array.mk_select ctx (Z3Array.mk_store ctx arr x three) (Arithmetic.mk_sub ctx [y; two]))] in
	(* f(y - x + 1) *)
	let temp2: Expr.expr = FuncDecl.apply f [Arithmetic.mk_add ctx [Arithmetic.mk_sub ctx [y; x]; one]] in
	let implies_r: Expr.expr = Boolean.mk_eq ctx temp1 temp2 in
	let fml: Expr.expr = Boolean.mk_implies ctx implies_l implies_r in
	let solver = (mk_solver ctx None) in
	Solver.add solver [Boolean.mk_not ctx fml];
	print_check solver;
	print_model solver

(*
	from z3 import *
	x, y = Ints('x y')
	s = Solver()
	s.add((x % 4) + 3 * (y / 2) > x - y)
	print(s.sexpr())
*)
let test3 (ctx: context): unit =
	let x: Expr.expr = Arithmetic.Integer.mk_const_s ctx "x" in
	let y: Expr.expr = Arithmetic.Integer.mk_const_s ctx "y" in
	let two: Expr.expr = Arithmetic.Integer.mk_numeral_i ctx 2 in
	let three: Expr.expr = Arithmetic.Integer.mk_numeral_i ctx 3 in
	let four: Expr.expr = Arithmetic.Integer.mk_numeral_i ctx 4 in
	(* x % 4 *)
	let temp1: Expr.expr = Arithmetic.Integer.mk_mod ctx x four in
	(* 3 * (y / 2) *)
	let temp2: Expr.expr = Arithmetic.mk_mul ctx [three; (Arithmetic.mk_div ctx y two)] in
	(* x - y *)
	let temp3: Expr.expr = Arithmetic.mk_sub ctx [x; y] in
	let solver = (mk_solver ctx None) in
	Solver.add solver [Arithmetic.mk_gt ctx (Arithmetic.mk_add ctx [temp1; temp2]) temp3];
	Printf.printf "%s\n" (Solver.to_string solver)

(*
	S = DeclareSort('S')
	s = Const('s', S)
	solve(ForAll(s, s != s))
*)
let test4 (ctx: context): unit =
	let s_sort: Sort.sort = Sort.mk_uninterpreted_s ctx "S" in
	let s: Expr.expr = Expr.mk_const_s ctx "s" s_sort in
	let q: Quantifier.quantifier = Quantifier.mk_forall_const ctx [s] (Boolean.mk_not ctx (Boolean.mk_eq ctx s s)) (Some 1) [] [] None None in
	let solver = (mk_solver ctx None) in
	Solver.add solver [Quantifier.expr_of_quantifier q];
	print_check solver;
	print_model solver

(*
	Z = IntSort()
	B = BoolSort()
	f = Function('f', B, Z)
	g = Function('g', Z, B)
	a = Bool('a')
	solve(g(1+f(a)))
*)
let test5 (ctx: context): unit =
	let int_sort: Sort.sort = Arithmetic.Integer.mk_sort ctx in
	let bool_sort: Sort.sort = Boolean.mk_sort ctx in
	let f: FuncDecl.func_decl = FuncDecl.mk_func_decl_s ctx "f" [bool_sort] int_sort in
	let g: FuncDecl.func_decl = FuncDecl.mk_func_decl_s ctx "g" [int_sort] bool_sort in
	let a: Expr.expr = Boolean.mk_const_s ctx "a" in
	let one: Expr.expr = Arithmetic.Integer.mk_numeral_i ctx 1 in
	let fml: Expr.expr = FuncDecl.apply g [Arithmetic.mk_add ctx [one; (FuncDecl.apply f [a])]] in
	let solver = (mk_solver ctx None) in
	Solver.add solver [fml];
	print_check solver;
	print_model solver

(*
	x = Int('x')
	y = Int('y')
	n = x + y >= 3
	print("num args: ", n.num_args())
	print("children: ", n.children())
	print("1st child:", n.arg(0))
	print("2nd child:", n.arg(1))
	print("operator: ", n.decl())
	print("op name:  ", n.decl().name())
*)
let test6 (ctx: context): unit =
	let x: Expr.expr = Arithmetic.Integer.mk_const_s ctx "x" in
	let y: Expr.expr = Arithmetic.Integer.mk_const_s ctx "y" in
	let three: Expr.expr = Arithmetic.Integer.mk_numeral_i ctx 3 in
	let n: Expr.expr = Arithmetic.mk_ge ctx (Arithmetic.mk_add ctx [x; y]) three in
	Printf.printf "num args: %s\n" (string_of_int (Expr.get_num_args n));
	let str: string = List.fold_left (fun a b -> (a ^ (Expr.to_string b) ^ "; ")) "[" (Expr.get_args n) in
	Printf.printf "children: %s\n" ((String.sub str 0 ((String.length str) - 2)) ^ "]");
	Printf.printf "1st child: %s\n" (Expr.to_string (List.nth (Expr.get_args n) 0));
	Printf.printf "2nd child: %s\n" (Expr.to_string (List.nth (Expr.get_args n) 1));
	Printf.printf "operator: %s\n" (FuncDecl.to_string (Expr.get_func_decl n));
	Printf.printf "op name: %s\n" (Symbol.to_string (FuncDecl.get_name (Expr.get_func_decl n)))


(*
	solve([y == x + 1, ForAll([y], Implies(y <= 0, x < y))])
	<==> alpha conversion
	solve([y == x + 1, ForAll([z], Implies(z <= 0, x < z))])
	unsatisfiable
*)
let test7 (ctx: context): unit =
	let x: Expr.expr = Arithmetic.Integer.mk_const_s ctx "x" in
	let y: Expr.expr = Arithmetic.Integer.mk_const_s ctx "y" in	
	let zero: Expr.expr = Arithmetic.Integer.mk_numeral_i ctx 0 in
	let one: Expr.expr = Arithmetic.Integer.mk_numeral_i ctx 1 in
	let q: Quantifier.quantifier = 
		Quantifier.mk_forall_const ctx [y] 
		(Boolean.mk_implies ctx (Arithmetic.mk_le ctx y zero) (Arithmetic.mk_lt ctx x y)) 
		(Some 1) [] [] None None in
	let solver = (mk_solver ctx None) in
	Solver.add solver [Boolean.mk_eq ctx y (Arithmetic.mk_add ctx [x; one]); Quantifier.expr_of_quantifier q];
	print_check solver;
	print_model solver

(*
	solve([y == x + 1, ForAll([y], Implies(y <= 0, x > y))])
	<==> alpha conversion
	solve([y == x + 1, ForAll([z], Implies(z <= 0, x > z))])
	unsatisfiable
*)
let test8 (ctx: context): unit =
	let x: Expr.expr = Arithmetic.Integer.mk_const_s ctx "x" in
	let y: Expr.expr = Arithmetic.Integer.mk_const_s ctx "y" in	
	let zero: Expr.expr = Arithmetic.Integer.mk_numeral_i ctx 0 in
	let one: Expr.expr = Arithmetic.Integer.mk_numeral_i ctx 1 in
	let q: Quantifier.quantifier = 
		Quantifier.mk_forall_const ctx [y] 
		(Boolean.mk_implies ctx (Arithmetic.mk_le ctx y zero) (Arithmetic.mk_gt ctx x y)) 
		(Some 1) [] [] None None in
	let solver = (mk_solver ctx None) in
	Solver.add solver [Boolean.mk_eq ctx y (Arithmetic.mk_add ctx [x; one]); Quantifier.expr_of_quantifier q];
	print_check solver;
	print_model solver

(*
	m, m1 = Array('m', Z, Z), Array('m1', Z, Z)
	def memset(lo, hi, y, m):
		return Lambda([x], If(And(lo <= x, x <= hi), y, Select(m, x)))
	solve([m1 == memset(1, 700, z, m), Select(m1, 6) != z])

let test9 (ctx: context): unit =
	let int_sort: Sort.sort = Arithmetic.Integer.mk_sort ctx in
	let x: Expr.expr = Arithmetic.Integer.mk_const_s ctx "x" in
	let z: Expr.expr = Arithmetic.Integer.mk_const_s ctx "z" in
	let one: Expr.expr = Arithmetic.Integer.mk_numeral_i ctx 1 in
	let sevenhundred: Expr.expr = Arithmetic.Integer.mk_numeral_i ctx 700 in
	let six: Expr.expr = Arithmetic.Integer.mk_numeral_i ctx 6 in
	let m: Expr.expr = Z3Array.mk_const_s ctx "m" int_sort int_sort in
	let m1: Expr.expr = Z3Array.mk_const_s ctx "m1" int_sort int_sort in
	let memset (lo: Expr.expr) (hi: Expr.expr) (y: Expr.expr) (m: Expr.expr): Expr.expr = 
		let p: Expr.expr = Boolean.mk_and ctx [Arithmetic.mk_le ctx lo x; Arithmetic.mk_le ctx x hi] in
		let q = Quantifier.mk_lambda_const ctx [x] (Boolean.mk_ite ctx p y (Z3Array.mk_select ctx m x)) in
		Quantifier.expr_of_quantifier q
	in
	let temp1: Expr.expr = Boolean.mk_eq ctx m1 (memset one sevenhundred z m) in
	let temp2: Expr.expr = Boolean.mk_not ctx (Boolean.mk_eq ctx (Z3Array.mk_select ctx m1 six) z) in
	let solver = (mk_solver ctx None) in
	Solver.add solver [temp1; temp2];
	print_check solver;
	print_model solver
*)

(*
	Q = Array('Q', Z, B)
	prove(Implies(ForAll(Q, Implies(Select(Q, x), Select(Q, y))), x == y))
*)
let test10 (ctx: context): unit =
	let int_sort: Sort.sort = Arithmetic.Integer.mk_sort ctx in
	let bool_sort: Sort.sort = Boolean.mk_sort ctx in
	let q_arr: Expr.expr = Z3Array.mk_const_s ctx "Q" int_sort bool_sort in
	let x: Expr.expr = Arithmetic.Integer.mk_const_s ctx "x" in
	let y: Expr.expr = Arithmetic.Integer.mk_const_s ctx "y" in
	let imp: Expr.expr = Boolean.mk_implies ctx (Z3Array.mk_select ctx q_arr x) (Z3Array.mk_select ctx q_arr y) in
	let q: Quantifier.quantifier = Quantifier.mk_forall_const ctx [q_arr] imp (Some 1) [] [] None None in
	let to_prove: Expr.expr = Boolean.mk_implies ctx (Quantifier.expr_of_quantifier q) (Boolean.mk_eq ctx x y) in
	let solver = (mk_solver ctx None) in
	Solver.add solver [to_prove];
	print_check solver;
	print_model solver;
	print_proof solver


let _ = 
	let cfg = [("model", "true"); ("proof", "true")] in
	let ctx = (mk_context cfg) in
	test10 ctx
;;
