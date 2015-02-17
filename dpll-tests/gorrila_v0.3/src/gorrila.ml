(*----------------------------------------------------------------------(C)-*)
(* Copyright (C) 2009-2010 K. Korovin and The University of Manchester. 
   This file is part of iProver - a theorem prover for first-order logic.

   iProver is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.
   iProver is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  
   See the GNU General Public License for more details.
   You should have received a copy of the GNU General Public License
   along with iProver.  If not, see <http://www.gnu.org/licenses/>.         *)
(*----------------------------------------------------------------------[C]-*)

(*--------------------------------------------------------------------------*)
(* Generation of completely random problems (Not based on the input formulas)*)
(*--------------------------------------------------------------------------*)

open Lib

(* later rplace by its own options *)
open Options_rnd_gen


module SR= Solver_run

let solver_params = 
  {SR.solver           = !options.solver;
   SR.solver_sat_str   = !options.solver_sat_str;
   SR.solver_unsat_str = !options.solver_unsat_str;
   SR.solver_timeout   = Some (!options.solver_timeout)
 } 

(*
type options =
      {opt_rnd_seed : int
     } 

let options = {opt_rnd_seed = 1113}
let _ = Random.init options.opt_rnd_seed
*) 

(*---------------------*)
let out_log_str log_str = 
  file_append_str !options.log_file  log_str; 
  out_str log_str

let out_res_file res_str =  
  let out_file_name = 
    Filename.concat !options.output_dir !options.rnd_output_results_file in
  file_append_str out_file_name  res_str
    
let out_summary_log_str results_list =
  out_log_str 
    ("\n\n-----------------------------------------------------------------\n"^
     (Solver_run.out_stat results_list)^
     "\n-----------------------------------------------------------------\n"
    ) 


 
(*---------------------*)

let quote_str str = "\""^str^"\""

let int_to_smt_str i =
  if i >=0 
  then string_of_int i
  else 
    "(~ "^(string_of_int (-i))^")"
 
type monomial = 
(* first is coeff, second is var id *)
  |IVar of int*int
  |IFCoeff of int

let id_to_var_name id = 
  "x_"^(string_of_int id)

let mon_to_buffer b m = 
  match m with 
  | IVar (c,id) -> 
      b.add_str "(* ";
      b.add_str (int_to_smt_str c);
      b.add_char ' ';
      b.add_str (id_to_var_name id);
      b.add_char ')'
  |IFCoeff c -> b.add_str (int_to_smt_str c);

type int_poly = monomial list 

let poly_to_buffer b p = 
  match p with 
  |[m] -> mon_to_buffer b m
  |_   -> 
      b.add_str "(+";
      List.iter (fun m -> b.add_char ' ';  mon_to_buffer b m) p;
      b.add_char ')'
 

type la_pred_symb = 
  |PEq | PGr | PGreq 

let la_pred_symb_to_buffer b p = 
  match p with 
  | PEq -> b.add_char '='
  | PGr -> b.add_char '>'
  | PGreq -> b.add_str ">="

type la_pred = la_pred_symb * int_poly

(* preds have the form (pred poly 0) *)
let la_pred_to_buffer b (la_pred_symb,poly) =
  b.add_char '(';
  la_pred_symb_to_buffer b la_pred_symb;
  b.add_char ' ';
  poly_to_buffer b poly;
  b.add_str " 0)"

type la_lit = bool * la_pred

let lit_to_buffer b (polarity,pred) = 
  if polarity
  then 
    la_pred_to_buffer b pred
  else 
    (
     b.add_char '(';
     b.add_str "not ";
     la_pred_to_buffer b pred;
     b.add_char ')';
    )

type la_system = la_lit list 


let la_system_to_buffer b s = 
  match s with 
  |[p] -> lit_to_buffer b p
  |_   -> 
      b.add_str "(and";
      b.add_char '\n';
      List.iter (fun p -> 
	lit_to_buffer  b p; 
	b.add_char '\n') s;      
      b.add_char ')'


type logic = LRA | LIA | PROP

let logic_to_string l = 
  match l with 
  |LRA  -> "lra"
  |LIA  -> "lia"
  |PROP -> "prop"

let string_to_logic s = 
  match s with 
  |"lra" -> LRA
  |"lia" -> LIA 
  |"prop" -> PROP
  |_-> failwith (s^" is an unkown logic type should be one of: lra, lia, prop")

type rnd_la_params = 
  {la_rnd_seed              : int;
   la_logic                 : logic;
   la_num_of_vars           : int;
   la_num_of_gr             : int;
   la_num_of_greq           : int;
   la_num_of_eq             : int;
   la_num_of_deq            : int;
   la_num_of_vars_in_pred   : interval;
   la_coeff_int             : interval;     
   }
      
type rnd_prop_params = 
    {prop_logic              : logic;
     prop_rnd_seed           : int;
(* we can have several algorithms for generating *)
(*     alg_id                : int;              *)
     prop_num_of_vars        : int;
     prop_num_of_clauses     : int;
     prop_num_lit_in_cl      : interval;
   }

type rnd_params = 
  |LA_param of rnd_la_params
  |PROP_param of rnd_prop_params


let is_la_rnd_param p = 
  match p with 
  |LA_param _ -> true 
  |_ -> false 
	
let is_prop_rnd_param p = 
  match p with 
  |PROP_param _ -> true 
  |_ -> false 

let rnd_param_get_seed p = 
  match p with 
  |PROP_param pp  -> pp.prop_rnd_seed   
  |LA_param lp   -> lp.la_rnd_seed  
	
(*sp -- space deliml; e.g. can be " " or "_"*)
(* also inter_to_string is as parameter for interval to string, can be either [2,3]
   or 2_3 *)

let rnd_la_params_to_string_gen sp inter_to_string p = 
  ((logic_to_string p.la_logic)^sp
   ^"rnd"^sp^(string_of_int p.la_rnd_seed)
   ^sp^"v"^sp^(string_of_int p.la_num_of_vars)
   ^sp^"gr"^sp^(string_of_int p.la_num_of_gr)
   ^sp^"greq"^sp^(string_of_int p.la_num_of_greq)
   ^sp^"eq"^sp^(string_of_int p.la_num_of_eq)
   ^sp^"deq"^sp^(string_of_int p.la_num_of_deq)
   ^sp^"vpp"^sp^(inter_to_string p.la_num_of_vars_in_pred)
   ^sp^"cf"^sp^(inter_to_string p.la_coeff_int)
  )

let rnd_prop_params_to_string_gen sp inter_to_string p = 
  ( (logic_to_string p.prop_logic)^sp
    ^"rnd"^sp^(string_of_int p.prop_rnd_seed)
    ^sp^"v"^sp^(string_of_int p.prop_num_of_vars)
    ^sp^"c"^sp^(string_of_int p.prop_num_of_clauses)
    ^sp^"vic"^sp^(inter_to_string p.prop_num_lit_in_cl)
   )

let rnd_la_params_to_string sp p = 
  rnd_la_params_to_string_gen sp interval_to_string p
    
let rnd_prop_params_to_string sp p = 
  rnd_prop_params_to_string_gen sp interval_to_string p

    
let rnd_params_to_string_gen sp inter_to_string p =
  match p with  
  |LA_param lp -> rnd_la_params_to_string_gen sp inter_to_string lp 
  |PROP_param pp -> rnd_prop_params_to_string_gen sp inter_to_string pp

let rnd_params_to_string sp  p =
  rnd_params_to_string_gen sp interval_to_string p

(*
let rnd_params_opt_to_string op = 
  match op with 
  |Some p -> quote_str (rnd_params_to_string p)
  |None -> "\""
*)

(*--------------Parsing of a problem string----------------*)



let parse_rnd_params str = 
  let str_list = (Str.split (Str.regexp "[ ]") str) in 
  match str_list with 
  |[logic;
    "rnd";rnd_str;
    "v";v_str;
    "gr";gr_str;
    "greq";greq_str;
    "eq";eq_str;
    "deq";deq_str;
    "vpp";vpp_int_str;
    "cf";cf_int_str] ->
      LA_param
	(
	 {la_logic                 = (string_to_logic logic); 
	  la_rnd_seed              = (int_of_string rnd_str);
	  la_num_of_vars           = (int_of_string v_str);
	  la_num_of_gr             = (int_of_string gr_str);
	  la_num_of_greq           = (int_of_string greq_str);
	  la_num_of_eq             = (int_of_string eq_str);
	  la_num_of_deq            = (int_of_string deq_str);
	  la_num_of_vars_in_pred   = (parse_interval vpp_int_str);
	  la_coeff_int             = (parse_interval cf_int_str)  
	 }
	 )
(* old without la_logic by default is LRA*)
  |["rnd";rnd_str;
     "v";v_str;
     "gr";gr_str;
     "greq";greq_str;
     "eq";eq_str;
     "deq";deq_str;
     "vpp";vpp_int_str;
     "cf";cf_int_str] ->
       LA_param
	 (
	  {la_logic                  = LRA;
	   la_rnd_seed              = (int_of_string rnd_str);
	   la_num_of_vars           = (int_of_string v_str);
	   la_num_of_gr             = (int_of_string gr_str);
	   la_num_of_greq           = (int_of_string greq_str);
	   la_num_of_eq             = (int_of_string eq_str);
	   la_num_of_deq            = (int_of_string deq_str);
	   la_num_of_vars_in_pred   = (parse_interval vpp_int_str);
	   la_coeff_int             = (parse_interval cf_int_str)  
	 }
	 )
  
(* to parse old params without deq and without la_logic*)
  |
   ["rnd";rnd_str;
     "v";v_str;
     "gr";gr_str;
     "greq";greq_str;
     "eq";eq_str;
     "vpp";vpp_int_str;
     "cf";cf_int_str] ->
       LA_param
	 (
	  {la_logic                 = LRA;
	   la_rnd_seed              = (int_of_string rnd_str);
	   la_num_of_vars           = (int_of_string v_str);
	   la_num_of_gr             = (int_of_string gr_str);
	   la_num_of_greq           = (int_of_string greq_str);
	   la_num_of_eq             = (int_of_string eq_str);
	   la_num_of_deq            = 0;
	   la_num_of_vars_in_pred   = (parse_interval vpp_int_str);
	   la_coeff_int             = (parse_interval cf_int_str)  
	 }
	 )

(*-------propositional params--------*)
  |[logic;
    "rnd";rnd_str;
    "v";v_str;
    "c";c_str;
    "vic";vic_int_str;     
  ] ->
    PROP_param 
      ( 
	{prop_logic            = (string_to_logic logic); 
	 prop_rnd_seed         = (int_of_string rnd_str);
	 prop_num_of_vars      = (int_of_string v_str);
	 prop_num_of_clauses   = (int_of_string c_str);
	 prop_num_lit_in_cl    = (parse_interval vic_int_str);
       }
       )
  |_-> failwith ("parse_rnd_param_str: \""^str^"\" is not a valid rnd_param")


(*
let parse_rnd_prop_param_str str = 
  let str_list = (Str.split (Str.regexp "[ ]") str) in 
  match str_list with 
    ["rnd";rnd_str;
     "v";v_str;
     "c";c_str;
     "vic";vic_int_str;     
   ] ->
	{
	 prop_rnd_seed         = (int_of_string rnd_str);
	 prop_num_of_vars      = (int_of_string v_str);
	 prop_num_of_clauses   = (int_of_string c_str);
	 prop_num_lit_in_cl     = (parse_interval vic_int_str);
       }
  |_-> failwith ("parse_rnd_prop_param_str: "^str^" is not a valid rnd_param")
*)

(*
let parse_rnd_param_str str = 
  
 if !options.rnd_prop 
  then 
    PROP_param (parse_rnd_prop_param_str str)
  else
    if (!options.rnd_lra || !options.rnd_lia)
    then 
      LRA_param (parse_rnd_lra_param_str str)
    else
      failwith "\none rnd_prop or rnd_lra should be true\n"
*)


let remove_spaces str = 
  let str_list = (Str.split (Str.regexp "[ ]") str) in
  match str_list with 
  |[s]-> s
  |_-> failwith "remove_spaces: should be one string"


(* in File_source parameter is the file name *)
type problem_source = Rnd_source of rnd_params | File_source of string

let problem_source_to_string ps = 
  match ps with
  | Rnd_source rnd_params -> " rnd \""^(rnd_params_to_string " " rnd_params)^"\" "
  | File_source file_name -> " file \""^file_name^"\" "
  
let parse_problem_source s params = 
  let str_list = (Str.split (Str.regexp "[ ]") s) in
  match str_list with 
  |["rnd"] -> Rnd_source (parse_rnd_params params)
  |["file"] -> File_source (params) (* params is the file name in this case*)
  |_-> failwith ("\""^s^"\" is not a recognised problem_source")

(*
type problem_params = 
  |Rnd_params of rnd_params
  |Empty_params  
    
*)


(*
let problem_params_to_string pp = 
  match pp with 
  |Rnd_params rnd_params -> rnd_params_to_string rnd_params
  |Empty_params -> "\""
*)

type solver_problem_res = 
    {
     res_solver             : string;
     res_problem_source     : problem_source;
     res_result             : Solver_run.result;
   }

let get_rnd_seed_from_rnd_param rnd_params = 
  match rnd_params with 
  |LA_param p   -> p.la_rnd_seed
  |PROP_param p -> p.prop_rnd_seed

let is_prop_params rnd_params =
  match rnd_params with 
  |PROP_param _-> true 
  |_ -> false
    
let solver_problem_res_to_file_name res = 
  match res.res_problem_source with 
  |File_source file_name -> file_name
  |Rnd_source rnd_params ->       
(*      let seed =  get_rnd_seed_from_rnd_param rnd_params in*)
      let ext = 
	if 
	  (!options.rnd_prop_out_format = DIMACS_Format &&
	   is_prop_params rnd_params)
	then "cnf"
	else "smt"
      in
      (rnd_params_to_string_gen "_" interval_to_string_p rnd_params)^"."^ext
 (*      "rnd_"^(string_of_int seed)^"."^ext*)
		


let solver_problem_res_to_string r =  
  (quote_str r.res_solver)
  ^(problem_source_to_string r.res_problem_source)
  ^(Solver_run.result_to_string r.res_result)




let parse_problem_str str = 
  let str_list = (Str.split (Str.regexp "\"") str) in
  match str_list with 
  |[solver_str;problem_source_str;problem_params_str; result_str] ->            
      {
       res_solver              = solver_str;

       res_problem_source     = 
       parse_problem_source problem_source_str problem_params_str; 
       
       res_result             = Solver_run.string_to_result result_str
	}

  |_-> failwith ("parse_problem_str: \""^str^"\" is not a vaild problem string")



(*-----------------------------------------------*)
    

let rnd_from_int_non_zero (l,r) = 
  assert ((r >= l) && (if r=l then (not (r=0)) else true) );
  let succ = ref false in
  let res = ref None in
  while not !succ do
   let rnd = rnd_from_inter (l,r) in
   if rnd = 0 
   then ()
   else 
     (res:= Some(rnd);
      succ := true
     )
  done;
  get_some !res

(*------------------rnd LRA----------------------------*)

let rnd_poly rnd_params = 
(* free coefficient *)
  let fcoeff = (rnd_from_inter rnd_params.la_coeff_int) in
(*  let get_rnd_coeff () =  in*)
  let poly = 
    if fcoeff = 0 
    then ref [] 
    else
      ref ([IFCoeff (fcoeff)]) 
  in
  let num_of_vmon = rnd_from_inter rnd_params.la_num_of_vars_in_pred in
(* we will remove duplicated vars, var ids start from 0 *)
  let var_list   = ref [] in
  assert 
    (let (l,r) = rnd_params.la_num_of_vars_in_pred in
    rnd_params.la_num_of_vars >= r);  
  for i = 1 to num_of_vmon 
  do
    let rnd_var =
      let var_ref = ref None in
      while (!var_ref = None) 
      do	
	let new_rnd_var = Random.int rnd_params.la_num_of_vars in
	if (not (List.exists (fun x -> x = new_rnd_var) !var_list)) 
	then
	  (var_ref:= Some new_rnd_var)
	else ()
      done;
      get_some !var_ref 
    in
    var_list:=rnd_var::(!var_list);    
    let rnd_mon = 
      IVar((rnd_from_int_non_zero rnd_params.la_coeff_int), rnd_var) in
    poly:= rnd_mon::(!poly);    
  done;
  !poly

let rnd_system rnd_params = 
  Random.init rnd_params.la_rnd_seed;
  let sys = ref [] in
  for i = 1 to rnd_params.la_num_of_gr
  do
    let new_lit = (true,(PGr,(rnd_poly rnd_params))) in
    sys:=new_lit::(!sys)
  done;
  for i = 1 to rnd_params.la_num_of_greq 
  do
    let new_lit = (true,(PGreq,(rnd_poly rnd_params))) in
    sys:=new_lit::(!sys)
  done;
  for i = 1 to rnd_params.la_num_of_eq 
  do
    let new_lit = (true,(PEq,(rnd_poly rnd_params))) in
    sys:=new_lit::(!sys)
  done;
  for i = 1 to rnd_params.la_num_of_deq 
  do
    let new_lit = (false,(PEq,(rnd_poly rnd_params))) in
    sys:=new_lit::(!sys)
  done; 
  !sys

(*--------------------------------*) 
let out_rnd_la_to_buffer rnd_params = 
  let b = Buffer.create 10000 in
  let s = {buff = b;
	   add_char = Buffer.add_char b;
	   add_str  = Buffer.add_string b} 
  in
  s.add_str "(benchmark ";
  s.add_str "rnd_";
  s.add_str (string_of_int rnd_params.la_rnd_seed);
  s.add_char '\n';
  s.add_str (":source {automatically generated by "
	     ^system_name^" with "
	     ^(rnd_la_params_to_string " " rnd_params)^"}\n");
  (match rnd_params.la_logic with 
  |LRA -> 
      s.add_str ":logic QF_LRA\n"
  |LIA -> 
      s.add_str ":logic QF_LIA\n"
  |PROP -> failwith "out_rnd_la_to_buffer should not be PROP"
   ); 
  s.add_str ":status unknown\n";  
  let type_str = 
    (match rnd_params.la_logic with 
    |LRA -> "Real"
    |LIA -> "Int"
    |PROP -> failwith "out_rnd_la_to_buffer should not be PROP"
    ) 
  in  
  for vid = 0 to (rnd_params.la_num_of_vars - 1)
  do 
    s.add_str (":extrafuns (("^(id_to_var_name vid)^" "^type_str^"))\n")
  done;
  s.add_str ":formula ";
  la_system_to_buffer s (rnd_system rnd_params);
  s.add_str "\n)\n";
  b

(*------------------End LRA---------------------------------*)


(*----------------PROP generation---------------------------*)

(* DIMACS format *)


type prop_clause = int list 

let prop_cluase_to_dimacs_buffer b cl = 
    List.iter 
    (fun i -> 
      b.add_str (string_of_int i);
      b.add_char ' '; 
    ) cl;
(*  b.add_char ' '; *)
  b.add_char '0' (* end of clause*)

let smt_var_name = "x_"
let prop_lit_to_smt_buffer b l = 
  if l>0 then 
    b.add_str (smt_var_name^(string_of_int l))
  else
    b.add_str ("(not "^smt_var_name^(string_of_int (-l))^")")

let prop_cluase_to_smt_buffer b cl = 
  b.add_str "(or";  
    List.iter 
    (fun i -> 
      b.add_char ' '; 
      (prop_lit_to_smt_buffer b i)
    ) cl;
  b.add_char ')' (* end of clause*)


(* prop_system  is just list of clauses *)    

let prop_system_to_dimacs_buffer b cl_list = 
  List.iter (fun cl -> 
    b.add_char '\n'; 
    prop_cluase_to_dimacs_buffer b cl) cl_list
(*  b.add_char '\n'*)


let prop_system_to_smt_buffer b cl_list = 
  b.add_str "(and "; 
  List.iter (fun cl -> 
    b.add_char '\n'; 
    prop_cluase_to_smt_buffer b cl) cl_list;
  b.add_char '\n';
  b.add_char ')'
    
    
let rnd_prop_clause rnd_params = 
  let num_lits = rnd_from_inter rnd_params.prop_num_lit_in_cl in
  let rnd_cl = ref [] in
 for i = 1 to num_lits 
 do
   let rnd_atom = rnd_from_inter (1, rnd_params.prop_num_of_vars) in
   let rnd_lit = 
     if (rnd_bool ()) 
     then rnd_atom else -rnd_atom
   in
   rnd_cl := rnd_lit::(!rnd_cl)
 done;
 !rnd_cl

(*
   prop_num_of_vars           : int;
     prop_num_of_clauses        : int;
     prop_num_lit_in_cl      : interval;
*)

let rnd_prop_system rnd_params = 
  Random.init rnd_params.prop_rnd_seed;
  let rnd_sys = ref [] in
  for i=1 to rnd_params.prop_num_of_clauses
  do 
    rnd_sys:= (rnd_prop_clause rnd_params)::(!rnd_sys)
  done;
  !rnd_sys 

let out_rnd_prop_to_dimacs_buffer rnd_params = 
 let b = Buffer.create 10000 in
 let s = {buff = b;
	  add_char = Buffer.add_char b;
	  add_str  = Buffer.add_string b} 
 in
 Random.init rnd_params.prop_rnd_seed; 
 s.add_str ("c automatically generated by "
	    ^system_name^" with "
	    ^(rnd_prop_params_to_string " " rnd_params)^"\n");
 s.add_str ("p cnf "^(string_of_int rnd_params.prop_num_of_vars)^" "
	    ^(string_of_int rnd_params.prop_num_of_clauses));
 prop_system_to_dimacs_buffer s 
   (rnd_prop_system rnd_params);
 b


let out_rnd_prop_to_smt_buffer rnd_params = 
  let b = Buffer.create 10000 in
  let s = {buff = b;
	   add_char = Buffer.add_char b;
	   add_str  = Buffer.add_string b} 
  in
  Random.init rnd_params.prop_rnd_seed; 
  s.add_str "(benchmark ";
  s.add_str "rnd_";
  s.add_str (string_of_int rnd_params.prop_rnd_seed);
  s.add_char '\n';
  s.add_str (":source {automatically generated by "
	     ^system_name
	     ^" with parameters \""
	     ^(rnd_prop_params_to_string " " rnd_params)^"\"}\n");
  s.add_str ":logic QF_UF\n";  
  s.add_str ":status unknown\n";  
  for vid = 1 to rnd_params.prop_num_of_vars
  do 
    s.add_str (":extrapreds (("^smt_var_name^(string_of_int vid)^"))\n");
  done;
  s.add_str ":formula ";
  prop_system_to_smt_buffer s (rnd_prop_system rnd_params);
  s.add_str "\n)\n";
  b
  


(*---------------End Prop Generation------------------------*)

let out_rnd_poblem_to_buffer rnd_params = 
  match rnd_params with 
  |LA_param la_param   -> out_rnd_la_to_buffer la_param
  |PROP_param prop_param -> 
      (match !options.rnd_prop_out_format with 
      |DIMACS_Format ->
	  out_rnd_prop_to_dimacs_buffer prop_param
      |SMT_Format ->
	  out_rnd_prop_to_smt_buffer prop_param
      )

let run_solver_rnd_params rnd_params = 
  let b = ref None in
  let fun_out out_ch = Buffer.output_buffer out_ch (get_some !b) in
  out_str ("Generating "^(rnd_params_to_string " " rnd_params)^"\n");
  b := Some(out_rnd_poblem_to_buffer rnd_params);
  out_str ("Solving"^"...");
  let result =  
    SR.run_solver_channel 
      solver_params
      fun_out 
  in   
  let solver_problem_res = 
    {
     res_solver             = !options.solver;
     res_problem_source     = Rnd_source(rnd_params);
     res_result             = result;
   } 
  in
  solver_problem_res

  

(*---------------------------*)
let rnd_run_la_solver () = 
  let problem_counter = ref 1 in
  let results_list_ref = ref [] in 
  try
    let inter_int_of_var v inter = 
      inter_float_to_int (inter_const_var_to_float 
			    (float_of_int v) inter) 
    in
    let num_of_constr_inter num_of_vars constr_inter = 
      let inter_int = inter_int_of_var num_of_vars constr_inter in
    if (inter_consistent_positive inter_int)
    then 
      rnd_from_inter inter_int
    else
      0
    in
    let vars_in_constr_inter num_of_vars = 
      let (opt_l,opt_r) =  
	inter_int_of_var num_of_vars !options.rnd_la_vars_in_constr in
      let new_l = 
	if num_of_vars <= opt_l 
	then  num_of_vars 
	else opt_l
      in
    let new_r = 
      if opt_r < opt_l 
      then 
	new_l
      else
	if num_of_vars <= opt_r
	then  num_of_vars 
	else opt_r
    in 
    (new_l,new_r)
    in
    let la_logic = 
      if !options.rnd_lra 
      then LRA
      else 
	if !options.rnd_lia
	then LIA
	else 
	  failwith "rnd_run_la_solver: one of --rnd_lra or --rnd_lia should be true "
    in
    let (v_l,v_r) = !options.rnd_num_of_vars in
    for num_of_vars = v_l to v_r 
    do
    for i = 1 to !options.rnd_num_same_var_probs 
    do
      let rnd_params = 
	LA_param (
	{la_logic                 = la_logic;
	 la_rnd_seed              = Random.int 1000000;
	 la_num_of_vars           = num_of_vars;

	 la_num_of_greq           =  
	 num_of_constr_inter num_of_vars !options.rnd_la_geqs_per_vars;
	 
	 la_num_of_gr             = 
	 num_of_constr_inter num_of_vars !options.rnd_la_grs_per_vars;
	 
	 la_num_of_eq             = 
	 num_of_constr_inter num_of_vars !options.rnd_la_eqs_per_vars;

	 la_num_of_deq             = 
	 num_of_constr_inter num_of_vars !options.rnd_la_deqs_per_vars;
	 
	 la_num_of_vars_in_pred  = vars_in_constr_inter num_of_vars;
	 la_coeff_int            = !options.rnd_la_coeff
       }
       )
      in
      let check_params p =
	match p with 
	|LA_param(params) ->
	    if (params.la_num_of_eq   = 0 && 
		params.la_num_of_deq  = 0 &&
	      params.la_num_of_greq = 0 && 
		params.la_num_of_gr   = 0)
		(*||
		  ((num_var_l > num_var_r) || (num_var_r <=0))*)
	    then 
	    (let log_str = "empty problem\n" in
	    out_log_str log_str;
	    false
	    )
	    else true
	|_-> failwith "rnd_run_lra_solver this should not happen\n"
      in
      problem_counter:=!problem_counter +1;
      (if check_params 
	  rnd_params 
      then
	let solver_problem_res = run_solver_rnd_params rnd_params in
	results_list_ref:=solver_problem_res.res_result::(!results_list_ref);
	let res_str = (solver_problem_res_to_string solver_problem_res)^"\n" in
	out_res_file res_str;
	out_log_str res_str
      else ()
      )
    done;
    done; 
    out_summary_log_str !results_list_ref;
  with 
  |Termination_Signal ->
      out_summary_log_str !results_list_ref;
      raise Termination_Signal
  
 
(*---------------------------*)
let rnd_run_prop_solver () = 
   let problem_counter = ref 1 in
   let results_list_ref = ref [] in
   try
     let (v_l,v_r) = !options.rnd_num_of_vars in
     for num_of_vars = v_l to v_r 
     do
       for i = 1 to !options.rnd_num_same_var_probs 
       do
      let rnd_params = 
	PROP_param(
	{prop_logic                 = PROP;
	 prop_rnd_seed              = Random.int 1000000;
	 prop_num_of_vars           = num_of_vars;
	 prop_num_of_clauses        = 
	 int_of_float ((!options.rnd_prop_cl_per_var)*.(float_of_int num_of_vars));
	 prop_num_lit_in_cl         = !options.rnd_prop_lit_in_cl;     
       }
       )
      in      
      let solver_problem_res = run_solver_rnd_params rnd_params in
      results_list_ref:=solver_problem_res.res_result::(!results_list_ref);
      let res_str = (solver_problem_res_to_string solver_problem_res)^"\n" in
      out_res_file res_str;
      out_log_str res_str;
      problem_counter:=!problem_counter +1;
       done;
     done; 
     out_summary_log_str !results_list_ref;
   with 
   |Termination_Signal ->
       out_summary_log_str !results_list_ref;
       raise Termination_Signal
 

let rnd_run_solver () = 
  if !options.rnd_prop 
  then 
    rnd_run_prop_solver ()
  else
    if (!options.rnd_lra || !options.rnd_lia )
    then 
      rnd_run_la_solver ()
    else 
      failwith "rnd_run_solver: one of --rnd_prop, --rnd_lra or --rnd_lia should be true\n"

(*--------------------*)

let generate_from_file file_name = 
  let b = ref None in
  let fun_out out_ch = Buffer.output_buffer out_ch (get_some !b) in
  let out_to_file file_name = 	    
    let out_channel = open_out file_name in
    fun_out out_channel;
    close_out out_channel;
  in 
  let in_channel = open_in file_name in
  try 
    while true 
    do 
      let str = input_line in_channel in
      let solver_problem_res = parse_problem_str str in
      match solver_problem_res.res_problem_source with 
      |File_source _ -> ()
      |Rnd_source rnd_params ->
	  begin
	    out_str ("Generating "
		     ^(rnd_params_to_string " " rnd_params)^"\n");
	    b := Some(out_rnd_poblem_to_buffer rnd_params);
	    let out_file_name = 
	      Filename.concat !options.output_dir 
		(solver_problem_res_to_file_name  solver_problem_res) in
	    out_to_file out_file_name
	  end
    done; 
  with 
    End_of_file ->    
      close_in in_channel


(*------------------------------------*)


(*
let out_file_channnel file_name out_channel = 
  let in_channel = open_in file_name in
  try 
    while true 
    do
      let str = (input_line in_channel) in
(*      out_str (str);*)
      output_string out_channel str;
(*      output_string out_channel "\n"*)
    done 
  with 
    End_of_file -> 
      close_in in_channel

*)

(*------------------------------------*)

let out_file_channel file_name out_channel = 
  let in_channel = open_in file_name in
  try 
    while true 
    do
      output_string out_channel (input_line in_channel);
      output_string out_channel "\n"
    done 
  with 
    End_of_file -> 
      close_in in_channel

(*--------------------*)

let run_on_results_file file_name = 
  let b = ref None in
  let fun_out out_ch = Buffer.output_buffer out_ch (get_some !b) in
  let in_channel = open_in file_name in
(* for collectiong some statistics *)
  let res_input_solver = ref [] in 
  let res_output_solver = ref [] in
  let num_better = ref 0 in
  let num_worse  = ref 0 in
  let num_same  = ref 0 in
  let num_inconsistencies = ref 0 in 
  let summary_log_str () = 
    ("\n\n-----------------------------------------------------------------\n"
     ^"input solver(s) "^(Solver_run.out_stat !res_input_solver)^"\n"
     ^(quote_str !options.solver)^" "
     ^(Solver_run.out_stat !res_output_solver)^"\n"
     ^(quote_str !options.solver)^" "
     ^"better: "^(string_of_int !num_better)^" "
     ^"worse: "^(string_of_int !num_worse)^" "
     ^"same: "^(string_of_int !num_same)^" "
     ^"inconsistencies: "^(string_of_int !num_inconsistencies)^"\n"
     ^"-----------------------------------------------------------------\n"
    )
  in
  try 
    while true 
    do 
      let str = input_line in_channel in
      let input_solver_problem_res = parse_problem_str str in


      let output_solver_problem_res = 

(* two cases: problem is a file, or randomly generated *)
	match input_solver_problem_res.res_problem_source with 
	|File_source (file_name) ->

	    begin
(*	   let full_input_file_name = file_name in*)
	      let full_input_file_name = 
		Filename.concat 
		  !options.input_dir file_name  in  
	      out_str (file_name^" Solving"^"...");
	      let result =  
		Solver_run.run_solver_channel 
		  solver_params
		  (out_file_channel full_input_file_name) in	
	      {
	       res_solver         = !options.solver;

	       res_problem_source = 
	       input_solver_problem_res.res_problem_source;

	       res_result         = result;
	     }	     
	    end
	|Rnd_source rnd_params ->
	 ( out_str 
	  ("Generating "
	   ^(rnd_params_to_string " " rnd_params)^"\n");
	   b := Some(out_rnd_poblem_to_buffer rnd_params);
	   out_str ("Solving"^"...");
	   let result =  
	     Solver_run.run_solver_channel 
	       solver_params
	       fun_out in
	   
	{
	 res_solver         = !options.solver;

	 res_problem_source = 
	 input_solver_problem_res.res_problem_source;

	 res_result         = result;
       }
	  )
      in

      (if not (Solver_run.check_consistency 
		 input_solver_problem_res.res_result 
		 output_solver_problem_res.res_result)
      then 
	(num_inconsistencies:= !num_inconsistencies +1;
	let log_str = 
	  ("inconsistency: "
	   ^(solver_problem_res_to_string input_solver_problem_res)
	   ^" "^(solver_problem_res_to_string output_solver_problem_res)
	   ^"\n") 
	in
	out_log_str log_str)
      else()
      );      
      let cmp_pref_string = 
	let cmp = 
	  Solver_run.cmp_results 
	    output_solver_problem_res.res_result input_solver_problem_res.res_result in
	if cmp > 0 
	then 
	  (num_better:=!num_better+1;
	   "better:")
	else 
	  if cmp < 0 
	  then 
	    (num_worse:=!num_worse+1;
	     "worse:")
	  else 
	    (num_same:=!num_same+1;
	     "same:")
      in
      let log_str = 
	(cmp_pref_string
	 ^" "^(solver_problem_res_to_string input_solver_problem_res)
	 ^" "^(solver_problem_res_to_string output_solver_problem_res)
	 ^"\n") 	   
      in      
      out_log_str log_str;
      let res_str = (solver_problem_res_to_string output_solver_problem_res)^"\n" in
      out_res_file res_str;
      res_input_solver  := input_solver_problem_res.res_result::!res_input_solver;
      res_output_solver := output_solver_problem_res.res_result::!res_output_solver;
    done;
  with 
    End_of_file ->    
      (close_in in_channel;
       out_log_str (summary_log_str()) 
      )
  |Termination_Signal ->
      close_in in_channel;
      out_log_str (summary_log_str());
      raise Termination_Signal
    



(*-------------------------------------------*)
let is_solver_compatible_file file_name = 
  let str_list = (Str.split (Str.regexp "[\\.]") file_name) in
  let rev_str_list = List.rev str_list in 
  let suffix = 
    match rev_str_list with 
    |(h::tl) -> h
    | _ -> ""
  in
(*  if (!options.rnd_lra && (suffix= "smt")) ||  (!options.rnd_prop && (suffix= "cnf"))*)
  if suffix=(!options.rnd_run_on_dir_ext)
  then true  
  else false
   

(*-------------------------------------------*)
let run_on_dir input_dir =
  let results_list_ref = ref [] in 
  try
    let f file_name = 
      if (not (is_solver_compatible_file file_name))
      then (out_str ("Skipping: \""^file_name^"\" is not in the solver's format \n"))
      else
	let full_input_file_name = 
	  Filename.concat !options.input_dir file_name in
	out_str ("Solving "^file_name^"...\n");
	let result =  
	  Solver_run.run_solver_channel 
	  solver_params 
	    (out_file_channel full_input_file_name) in
	results_list_ref:=result::(!results_list_ref);
	let solver_problem_res = 
	  {
	   res_solver         = !options.solver;
	 res_problem_source = File_source (file_name);
	   res_result         = result;
	 } in
	let res_str = (solver_problem_res_to_string solver_problem_res)^"\n" in
	out_res_file res_str;
	out_str ("\n"^res_str)
    in
    let dir_arr = Sys.readdir !options.input_dir in 
    Array.iter f dir_arr;
    out_summary_log_str !results_list_ref;
  with 
    Termination_Signal -> 
      out_summary_log_str !results_list_ref;
      raise Termination_Signal
    

(*-------------------------------------------*)
let _ =  
  try
    if !options.rnd_run_on_random 
    then
      rnd_run_solver ()
    else 
      if !options.rnd_generating_problems
      then
	generate_from_file !options.rnd_input_results_file
      else 
	if !options.rnd_run_on_results_file 
	then
	run_on_results_file !options.rnd_input_results_file
	else 
	  if !options.rnd_run_on_dir then 
	    run_on_dir !options.input_dir
	  else
	    failwith "random_lra: none of --rnd_run_on_random/--rnd_generating_problems/--rnd_run_on_results_file is true"
  with
    Termination_Signal ->
      out_str "\nTerminated by the user\n";
      kill_all_child_processes ()
	


(*-------------------------------------------*)


(*
let _ =   let rnd_params = 
    {
     num_of_vars           =  20;
     num_of_gr             =  30;
     num_of_greq           =  70;
     num_of_eq             =   8;
     num_of_vars_per_pred  = (5,15);
     coeff_int             = (-20,20);     
   }
  in
  let b = out_rnd_sys_to_buffer rnd_params in
  out_str (Buffer.contents b)
*)
