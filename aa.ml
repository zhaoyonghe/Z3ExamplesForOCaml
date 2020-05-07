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
open Z3.FloatingPoint

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
	| _ -> Printf.printf "no proof\n"
	(* It should return None, but actually raises error. *)

let solve (ctx: context) (assertions: Expr.expr list): unit =
	let solver = (mk_solver ctx None) in
	Solver.add solver assertions;
	print_check solver;
	print_model solver

let prove (ctx: context) (assertions: Expr.expr list): unit =
	let solver = (mk_solver ctx None) in
	Solver.add solver assertions;
	print_check solver;
	print_model solver;
	print_proof solver

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
	solve ctx [
		Boolean.mk_or ctx [tie_expr; shirt_expr]; 
		(* Boolean.mk_or ctx [(Boolean.mk_not ctx shirt_expr); tie_expr]; unsatisfiable *)
		Boolean.mk_or ctx [(Boolean.mk_not ctx tie_expr); shirt_expr];
		Boolean.mk_or ctx [(Boolean.mk_not ctx tie_expr); (Boolean.mk_not ctx shirt_expr)]
	]

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
	solve ctx [Boolean.mk_not ctx fml]


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
	let q: Quantifier.quantifier = 
		Quantifier.mk_forall_const ctx [s] (Boolean.mk_not ctx (Boolean.mk_eq ctx s s)) 
		(Some 1) [] [] None None in
	solve ctx [Quantifier.expr_of_quantifier q]


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
	solve ctx [fml]

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
	solve ctx [
		Boolean.mk_eq ctx y (Arithmetic.mk_add ctx [x; one]); 
		Quantifier.expr_of_quantifier q
	]

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
	solve ctx [
		Boolean.mk_eq ctx y (Arithmetic.mk_add ctx [x; one]); 
		Quantifier.expr_of_quantifier q
	]


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

(*
	S = DeclareSort('S')
	f = Function('f', S, S)
	x = Const('x', S)
	solve(f(f(x)) == x, f(f(f(x))) == x)
	solve(f(f(x)) == x, f(f(f(x))) == x, f(x) != x)
*)
let test11 (ctx: context): unit =
	let s_sort: Sort.sort = Sort.mk_uninterpreted_s ctx "S" in
	let f_func: FuncDecl.func_decl = FuncDecl.mk_func_decl_s ctx "f" [s_sort] s_sort in
	let x: Expr.expr = Expr.mk_const_s ctx "x" s_sort in
	let f (x: Expr.expr): Expr.expr = (FuncDecl.apply f_func [x]) in
	solve ctx [
		Boolean.mk_eq ctx (f (f x)) x; 
		Boolean.mk_eq ctx (f (f (f x))) x
	];
	solve ctx [
		Boolean.mk_eq ctx (f (f x)) x; 
		Boolean.mk_eq ctx (f (f (f x))) x; 
		Boolean.mk_not ctx (Boolean.mk_eq ctx (f x) x)
	]


let mk_neq (ctx: context) (a: Expr.expr) (b: Expr.expr): Expr.expr = 
	Boolean.mk_not ctx (Boolean.mk_eq ctx a b)

let reals (ctx: context) (s_li: string list): Expr.expr list = 
	List.map (fun a -> Arithmetic.Real.mk_const_s ctx a) s_li

(*
	S = DeclareSort('S')
	a, b, c, d, e, s, t = Consts('a b c d e s t', S)
	f = Function('f', S, S, S)
	g = Function('g', S, S)
	solve([a == b, b == c, d == e, b == s, d == t, f(a, g(d)) != f(g(e), b)])
*)
let test12 (ctx: context): unit =
	let s_sort: Sort.sort = Sort.mk_uninterpreted_s ctx "S" in
	let a: Expr.expr = Expr.mk_const_s ctx "a" s_sort in
	let b: Expr.expr = Expr.mk_const_s ctx "b" s_sort in
	let c: Expr.expr = Expr.mk_const_s ctx "c" s_sort in
	let d: Expr.expr = Expr.mk_const_s ctx "d" s_sort in
	let e: Expr.expr = Expr.mk_const_s ctx "e" s_sort in
	let s: Expr.expr = Expr.mk_const_s ctx "s" s_sort in
	let t: Expr.expr = Expr.mk_const_s ctx "t" s_sort in
	let f_func: FuncDecl.func_decl = FuncDecl.mk_func_decl_s ctx "f" [s_sort; s_sort] s_sort in
	let g_func: FuncDecl.func_decl = FuncDecl.mk_func_decl_s ctx "g" [s_sort] s_sort in
	let f (x: Expr.expr) (y: Expr.expr): Expr.expr = (FuncDecl.apply f_func [x; y]) in
	let g (x: Expr.expr): Expr.expr = (FuncDecl.apply g_func [x]) in
	solve ctx [
		Boolean.mk_eq ctx a b; Boolean.mk_eq ctx b c;
		Boolean.mk_eq ctx d e; 
		Boolean.mk_eq ctx b s; 
		Boolean.mk_eq ctx d t;
		mk_neq ctx (f a (g d)) (f (g e) b)
	]


(*
	x, y = Reals('x y')
	solve([x >= 0, Or(x + y <= 2, x + 2*y >= 6), Or(x + y >= 2, x + 2*y > 4)])
*)
let test13 (ctx: context): unit =
	let zero: Expr.expr = Arithmetic.Integer.mk_numeral_i ctx 0 in
	let two: Expr.expr = Arithmetic.Integer.mk_numeral_i ctx 2 in
	let four: Expr.expr = Arithmetic.Integer.mk_numeral_i ctx 4 in
	let six: Expr.expr = Arithmetic.Integer.mk_numeral_i ctx 6 in
	let x: Expr.expr = Arithmetic.Real.mk_const_s ctx "x" in
	let y: Expr.expr = Arithmetic.Real.mk_const_s ctx "y" in
	let temp1: Expr.expr = Arithmetic.mk_add ctx [x; y] in
	let temp2: Expr.expr = Arithmetic.mk_add ctx [x; Arithmetic.mk_mul ctx [two; y]] in
	solve ctx [
		Arithmetic.mk_ge ctx x zero; 
		Boolean.mk_or ctx [(Arithmetic.mk_le ctx temp1 two); (Arithmetic.mk_ge ctx temp2 six)];
		Boolean.mk_or ctx [(Arithmetic.mk_ge ctx temp1 two); (Arithmetic.mk_gt ctx temp2 four)]
	]


(*
	A = Array('A', IntSort(), IntSort())
	solve(A[x] == x, Store(A, x, y) == A)
*)
let test14 (ctx: context): unit =
	let int_sort: Sort.sort = Arithmetic.Integer.mk_sort ctx in
	let x: Expr.expr = Arithmetic.Integer.mk_const_s ctx "x" in
	let y: Expr.expr = Arithmetic.Integer.mk_const_s ctx "y" in
	let a_arr: Expr.expr = Z3Array.mk_const_s ctx "A" int_sort int_sort in
	solve ctx [
		Boolean.mk_eq ctx (Z3Array.mk_select ctx a_arr x) x;
		Boolean.mk_eq ctx (Z3Array.mk_store ctx a_arr x y) a_arr
	]
	
(*
	check:

	store:
	s.add(Store(a, i, v)[j] == If(i == j, v, a[j]))
	s.add(Store(a, i, v)[i] == v)

	extensionality:
	s.add(Implies(ForAll(i, a[i] == b[i]), a == b))
	s.add(Implies(a[Ext(a, b)] == b[Ext(a, b)], a == b))
*)
let test15 (ctx: context): unit = 
	let int_sort: Sort.sort = Arithmetic.Integer.mk_sort ctx in
	let i: Expr.expr = Arithmetic.Integer.mk_const_s ctx "i" in
	let j: Expr.expr = Arithmetic.Integer.mk_const_s ctx "j" in
	let v: Expr.expr = Arithmetic.Integer.mk_const_s ctx "v" in
	let a: Expr.expr = Z3Array.mk_const_s ctx "a" int_sort int_sort in
	let b: Expr.expr = Z3Array.mk_const_s ctx "b" int_sort int_sort in
	(* Store(a, i, v)[j] *)
	let temp1: Expr.expr = Z3Array.mk_select ctx (Z3Array.mk_store ctx a i v) j in 
	(* If(i == j, v, a[j]) *)
	let temp2: Expr.expr = Boolean.mk_ite ctx (Boolean.mk_eq ctx i j) v (Z3Array.mk_select ctx a j) in
	(* Store(a, i, v)[i] *)
	let temp3: Expr.expr = Z3Array.mk_select ctx (Z3Array.mk_store ctx a i v) i in
	(* ForAll(i, a[i] == b[i]) *)
	let q: Quantifier.quantifier = 
		Quantifier.mk_forall_const ctx [i] 
		(Boolean.mk_eq ctx (Z3Array.mk_select ctx a i) (Z3Array.mk_select ctx b i)) 
		(Some 1) [] [] None None in
	(* a == b *)
	let temp4: Expr.expr = Boolean.mk_eq ctx a b in
	(* Ext(a, b) *)
	let ext: Expr.expr = Z3Array.mk_array_ext ctx a b  in
	(* a[Ext(a, b)] == b[Ext(a, b)] *)
	let temp5: Expr.expr = Boolean.mk_eq ctx (Z3Array.mk_select ctx a ext) (Z3Array.mk_select ctx b ext) in
	(* unsatisfiable, because these four axioms should all be true *)
	solve ctx [
		Boolean.mk_not ctx (Boolean.mk_and ctx [
			Boolean.mk_eq ctx temp1 temp2;
			Boolean.mk_eq ctx temp3 v;
			Boolean.mk_implies ctx (Quantifier.expr_of_quantifier q) temp4;
			Boolean.mk_implies ctx temp5 temp4
		])
	]	

(*
	def is_power_of_two(x):
		return And(x != 0, 0 == (x & (x - 1)))
	x = BitVec('x', 4)
	prove(is_power_of_two(x) == Or([x == 2**i for i in range(4)]))
*)
let test16 (ctx: context): unit =
	let zero: Expr.expr = Expr.mk_numeral_int ctx 0 (BitVector.mk_sort ctx 4) in
	let one: Expr.expr = Expr.mk_numeral_int ctx 1 (BitVector.mk_sort ctx 4) in
	let two: Expr.expr = Expr.mk_numeral_int ctx 2 (BitVector.mk_sort ctx 4) in
	let four: Expr.expr = Expr.mk_numeral_int ctx 4 (BitVector.mk_sort ctx 4) in
	let eight: Expr.expr = Expr.mk_numeral_int ctx 8 (BitVector.mk_sort ctx 4) in
	let is_power_of_two (x: Expr.expr): Expr.expr = 
		Boolean.mk_and ctx [
			mk_neq ctx x zero;
			Boolean.mk_eq ctx zero (BitVector.mk_and ctx x (BitVector.mk_sub ctx x one))
		]
	in
	let x: Expr.expr = BitVector.mk_const_s ctx "x" 4 in 
	let solver = (mk_solver ctx None) in
	Solver.add solver [
		Boolean.mk_not ctx (Boolean.mk_eq ctx (is_power_of_two x) (Boolean.mk_or ctx [
																				Boolean.mk_eq ctx x one;
																				Boolean.mk_eq ctx x two;
																				Boolean.mk_eq ctx x four;
																				Boolean.mk_eq ctx x eight
																			]))
	];
	print_check solver;
	print_model solver;
	print_proof solver

(*
	v = BitVec('v',32)
	mask = v >> 31
	prove(If(v > 0, v, -v) == (v + mask) ^ mask)
*)
let test17 (ctx: context): unit = ()

(*
	x = FP('x', FPSort(3, 4))
	print(10 + x)
*)
let test18 (ctx: context): unit = ()(*
	let fp_sort: Sort.sort = FloatingPoint.mk_sort ctx 3 4 in
	let x: Expr.expr = FloatingPoint.mk_const_s ctx "x" fp_sort in
	let ten: Expr.expr = FloatingPoint.mk_numeral_f ctx 10. fp_sort in
	let temp: Expr.expr = FloatingPoint.mk_add ctx (FloatingPoint.RoundingMode.mk_rtz ctx) x ten in
	Printf.printf "%s\n" (FloatingPoint.numeral_to_string temp)*)

let _ = 
	let cfg = [("model", "true"); ("proof", "true")] in
	let ctx = (mk_context cfg) in
	test16 ctx
;;
