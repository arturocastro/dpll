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

open Lib

type prop_out_format = 
  |DIMACS_Format |SMT_Format

let parse_prop_format s = 
  match s with 
  |"smt" -> SMT_Format
  |"dimacs" -> DIMACS_Format
  |_ -> 
      failwith ("\""^s^"\" is an unrecognised rnd_prop_out_format, should be either \"smt\" or \"dimacs\"")

type options = 
    {
(*---input----*)
     mutable output_dir                  : string;
     mutable input_dir                   : string;
     mutable log_file                    : string; 
     mutable random_seed                 : int;

(*----solver -----------*)
     mutable solver                      : string;
     mutable solver_sat_str              : string;
     mutable solver_unsat_str            : string;
     mutable solver_timeout              : float;

(*---random regenrating (random_lra)----------------------*)
     mutable rnd_prop                        : bool;
     mutable rnd_lra                         : bool;
     mutable rnd_lia                         : bool;
     mutable rnd_input_results_file          : string; 
     mutable rnd_output_results_file         : string;
     mutable rnd_generating_problems         : bool;
     mutable rnd_run_on_results_file         : bool;
     mutable rnd_run_on_random               : bool;
     mutable rnd_run_on_dir                  : bool;
     mutable rnd_run_on_dir_ext              : string;
     mutable rnd_num_of_vars                 : interval;
     mutable rnd_num_same_var_probs          : int;
(*   mutable rnd_start_vars                  : int;
     mutable rnd_num_of_problems             : int;
     mutable rnd_num_same_var_probs          : int;
*)
(*---prop------*)
     mutable rnd_prop_cl_per_var             : float;
     mutable rnd_prop_lit_in_cl              : interval;
     mutable rnd_prop_out_format             : prop_out_format;

(*---lra-------*)
     mutable rnd_la_coeff                   : interval;
     mutable rnd_la_vars_in_constr          : inter_const_var;
     mutable rnd_la_eqs_per_vars            : inter_const_var;
     mutable rnd_la_deqs_per_vars           : inter_const_var;
     mutable rnd_la_geqs_per_vars           : inter_const_var;
     mutable rnd_la_grs_per_vars            : inter_const_var;
   }

let default_options () = 
  {
(*---input----*)
   output_dir             = "";
   input_dir              = "";
   log_file               = "random_generator.log";
   random_seed            = 0;

(*----solver-----------*)
   solver                    = "";
   solver_sat_str            = "sat";
   solver_unsat_str          = "unsat";        
   solver_timeout            = 20.;


(*---later move to a separate otion file------------------*)
(*---random regenrating (random_la)----------------------*)
   rnd_prop                    = false;
   rnd_lra                     = false;  
   rnd_lia                     = false;  
   rnd_input_results_file      = "";    
   rnd_output_results_file     = "random_generator.res";
   rnd_generating_problems     = false; 
   rnd_run_on_results_file     = false;
   rnd_run_on_random           = false;
   rnd_run_on_dir              = false;
   rnd_run_on_dir_ext          = "smt";
   rnd_num_of_vars             = (2,100);
   rnd_num_same_var_probs      = 100;
   rnd_prop_cl_per_var         = 4.25;
   rnd_prop_lit_in_cl          = (2,10);
   rnd_prop_out_format         = DIMACS_Format;
   rnd_la_coeff               = (-20,20);
   rnd_la_vars_in_constr      = (parse_inter_const_var "[3.,0.5v]");
   rnd_la_eqs_per_vars        = (parse_inter_const_var "[0.2v,0.5v]");
   rnd_la_deqs_per_vars       = (parse_inter_const_var "[0.,0.]");
   rnd_la_geqs_per_vars       = (parse_inter_const_var "[0.6v,1.3v]");
   rnd_la_grs_per_vars        = (parse_inter_const_var "[0.6v,1.3v]");
 }


let options = ref (default_options ())

(* random seed can be reintialised by specifing --random_seed option *)
let _ = 
  if (!options.random_seed = 0)
  then 
    Random.self_init () (* system dependent by default *)
  else
    Random.init !options.random_seed


(*--------------*)
let bool_str   = "<bool>"
let str_str = "<str>"
let int_str    = "<int>"
let float_str    = "<float>"
let interval_str    = "<interval>"
let inter_var_str   = "<interval_var>"

let inf_pref  = "\n    "
let example_str = inf_pref^"example: " 

(*--------------*)


 let usage_msg = 
   "\n random_generator <options> "
   ^inf_pref^"Generates random problems: SAT in DIMACS and linear arithmetic in SMT formats\n"

(*--------------*)

let default_arg_fun str = 
  failwith "there should be no default arguments"

(*---input----*)
(*---------*)

let opt_input_dir_str = "--input_dir"

let opt_input_dir_fun s = 
  !options.input_dir <- s

let opt_input_dir_inf = 
  (str_str^" -- the full path to smt problems from which the problems will be generated\n")


(*---------*)
let opt_output_dir_str = "--output_dir"

let opt_output_dir_fun s = 
  !options.output_dir <- s
  (*tmp_file_name:=Filename.concat s !tmp_file_name*)

let opt_output_dir_inf = 
  (str_str^" -- the full path for the output of the resulting problems\n")


(*---------*)
let opt_log_file_str = "--log_file"

let opt_log_file_fun s = 
  !options.log_file <- s

let opt_log_file_inf = 
  (str_str^" -- the log file name (put into the output_dir) for the generated problems\n")

(*---------*)

(*---------*)

let opt_rand_seed_str = "--random_seed"

let opt_rand_seed_fun i = 
  !options.random_seed <- i;  
  Random.init !options.random_seed

let opt_rand_seed_inf = 
  (int_str^" -- random seed used for the formula generation \n")

(*--solver------*)

let opt_solver_str = "--solver"

let opt_solver_fun s = 
  !options.solver <- s

let opt_solver_inf = 
  (bool_str^" -- the full solver line e.g. \"/home/cvc3/cvc3-optimized -lang smt\" or \"/home/z3/z3 -in\" \n")

(*---------*) 
let opt_solver_sat_str_str = "--solver_sat_str"

let opt_solver_sat_str_fun s = 
  !options.solver_sat_str <- s

let opt_solver_sat_str_inf =
  (str_str^" -- the solver output string matched for the satisfiable result\n")

(*---------*)

let opt_solver_unsat_str_str = "--solver_unsat_str"

let opt_solver_unsat_str_fun s = 
  !options.solver_unsat_str <- s

let opt_solver_unsat_str_inf =
  (str_str^" -- the solver output string matched for the unsatisfiable result\n")

 

(*---------*)
let opt_solver_timeout_str ="--solver_timeout"

let opt_solver_timeout_fun f = 
(*  if f > 0. 
  then*)
    !options.solver_timeout <-f
 (* else ()*)
      
let opt_solver_timeout_inf = 
  (float_str^"-- timeout for the solver in real time\n"
  ^"     use 0. or negative value for this parameter to be ignored\n")



(*---random regenrating (random_la)----------------------*)

let opt_rnd_prop_str ="--rnd_prop"

let opt_rnd_prop_fun b = 
   !options.rnd_prop <-b

let opt_rnd_prop_inf = 
 (bool_str^"-- generate random propositional set of clauses, one and only one of --rnd_prop, --rnd_lra, --rnd_lia should be true\n")

(*----------------*)
let opt_rnd_lra_str ="--rnd_lra"

let opt_rnd_lra_fun b = 
   !options.rnd_lra <-b

let opt_rnd_lra_inf =
(bool_str^"-- generate random linear arithmetic systems; see options starting with --rnd_la_  ;"^ 
 inf_pref^"only one --rnd_prop,  --rnd_lra, or --rnd_lia should be true\n")
  
(*----------------*)
let opt_rnd_lia_str ="--rnd_lia"

let opt_rnd_lia_fun b = 
   !options.rnd_lia <-b

let opt_rnd_lia_inf =
(bool_str^"-- generate random integer linear arithmetic systems; see options starting with --rnd_la_  ;"^
 inf_pref^"only one --rnd_prop,  --rnd_lra, or --rnd_lia should be true\n")
  

(*----------------*)
let opt_rnd_input_results_file_str ="--rnd_input_results_file" 

let opt_rnd_input_results_file_fun s =
 !options.rnd_input_results_file <- s

let opt_rnd_input_results_file_inf =
  (str_str^"-- read results from these file and generate problems/run solver on these problems \n")


(*----------------*)
let opt_rnd_output_results_file_str ="--rnd_output_results_file" 

let opt_rnd_output_results_file_fun s =
 !options.rnd_output_results_file <- s

let opt_rnd_output_results_file_inf =
  (str_str^"-- outputs results into this file \n")


(*----------------*)
let opt_rnd_generating_problems_str ="--rnd_generating_problems" 

let opt_rnd_generating_problems_fun b =
 !options.rnd_generating_problems <- b

let opt_rnd_generating_problems_inf =
  (bool_str^"-- generate problems from a file --rnd_input_results_file\n")


(*----------------*)

let opt_rnd_run_on_results_file_str ="--rnd_run_on_results_file"

let opt_rnd_run_on_results_file_fun b = 
   !options.rnd_run_on_results_file <-b

let opt_rnd_run_on_results_file_inf = 
  (bool_str^"-- run a solver on the --rnd_input_results_file \n")

(*----------------*)

let opt_rnd_run_on_random_str  ="--rnd_run_on_random"

let opt_rnd_run_on_random_fun b = 
   !options.rnd_run_on_random <-b

let opt_rnd_run_on_random_inf = 
  (bool_str^"--  run a solver on random problems and output results in --rnd_output_results_file\n")
 

(*----------------*)

let opt_rnd_run_on_dir_str ="--rnd_run_on_dir"

let opt_rnd_run_on_dir_fun b = 
   !options.rnd_run_on_dir <-b

let opt_rnd_run_on_dir_inf =  
(bool_str^"-- runs solver on problems with the extension specified by --rnd_run_on_dir_ext  in --input_dir"^
 inf_pref^" outputs results in --output_dir/--rnd_output_results_file\n")

(*----------------*)

let opt_rnd_run_on_dir_ext_str ="--rnd_run_on_dir_ext"

let opt_rnd_run_on_dir_ext_fun s = 
   !options.rnd_run_on_dir_ext <-s

let opt_rnd_run_on_dir_ext_inf =  
(str_str^"-- runs solver only on problems with the extension ."^str_str^
 inf_pref^"--rnd_run_on_dir should be true \n")

 

(*----------------*)

let opt_rnd_prop_cl_per_var_str ="--rnd_prop_cl_per_var"

let opt_rnd_prop_cl_per_var_fun f = 
   !options.rnd_prop_cl_per_var <-f

let opt_rnd_prop_cl_per_var_inf = 
(float_str^"-- ratio of the number of propositional clauses per the number of variables (e.g. 4.25)\n")

(*----------------*)
      
let opt_rnd_prop_lit_in_cl_str ="--rnd_prop_lit_in_cl"

let opt_rnd_prop_lit_in_cl_fun s = 
   !options.rnd_prop_lit_in_cl <- (parse_interval s)

let opt_rnd_prop_lit_in_cl_inf = 
(interval_str^"-- e.g. if \"[2,10]\" then the number of literals in a clause is selected randomly from the interval [2,10], for 3-SAT use \"[3,3]\"\n")

(*----------------*)
let opt_rnd_prop_out_format_str = "--rnd_prop_out_format"

let opt_rnd_prop_out_format_fun s = 
  !options.rnd_prop_out_format <- (parse_prop_format s)

let opt_rnd_prop_out_format_inf = 
  (str_str^"-- propositional format used in the output either \"smt\" or \"dimacs\"\n")


(*----------------*)
let opt_rnd_num_of_vars_str ="--rnd_num_of_vars"

let opt_rnd_num_of_vars_fun s = 
  !options.rnd_num_of_vars <- (parse_interval s)

let opt_rnd_num_of_vars_inf = 
  (interval_str^" -- e.g. if \"[2,100]\" then  for each 2<=i<=100,  "^
   inf_pref^"the number  of generated problems over i variables is --rnd_num_same_var_probs \n"
  )

(*
(*----------------*)
let opt_rnd_start_vars_str ="--rnd_start_vars"

let opt_rnd_start_vars_fun b = 
   !options.rnd_start_vars <-b

let opt_rnd_start_vars_inf = 
  (int_str^"-- the number of variables at the start of generation\n")
*)

(*
(*----------------*)
let opt_rnd_num_of_problems_str ="--rnd_num_of_problems"

let opt_rnd_num_of_problems_fun i = 
   !options.rnd_num_of_problems <-i

let opt_rnd_num_of_problems_inf = 
(int_str^"--  number of generated problems when --rnd_run_on_random true\n")
 
*)
(*----------------*)

let opt_rnd_num_same_var_probs_str ="--rnd_num_same_var_probs"

let opt_rnd_num_same_var_probs_fun b = 
   !options.rnd_num_same_var_probs <-b

let opt_rnd_num_same_var_probs_inf = 
  (int_str^"-- the number of generated problems with each var count, see --rnd_num_of_vars\n")

(*----------------*)
let opt_rnd_la_coeff_str ="--rnd_la_coeff"

let opt_rnd_la_coeff_fun str = 
   !options.rnd_la_coeff <- parse_interval str

let opt_rnd_la_coeff_inf = 
  (interval_str^"-- coefficients are drawn at random from this interval, ex. \"[-20,20]\"\n ")

(*----------------*)
let opt_rnd_la_vars_in_constr_str ="--rnd_la_vars_in_constr"

let opt_rnd_la_vars_in_constr_fun str = 
   !options.rnd_la_vars_in_constr <- parse_inter_const_var str

let opt_rnd_la_vars_in_constr_inf = 
  (inter_var_str^"-- the number of variables in constraints is drawn at random from this interval; "^
   inf_pref^"(see --rnd_la_eqs_per_vars for the interval syntax)"^
   inf_pref^" for [a,b] if the number of vars is less than b then the b is replaced by the number of vars,"^
   inf_pref^" if a is bigger than the number of vars then a and b are replaced by the number of vars \n"
  )
    
(*----------------*)

let opt_rnd_la_eqs_per_vars_str ="--rnd_la_eqs_per_vars"

let opt_rnd_la_eqs_per_vars_fun s = 
   !options.rnd_la_eqs_per_vars <- parse_inter_const_var s

let opt_rnd_la_eqs_per_vars_inf = 
  (inter_var_str^"-- number of equalities per number of variables, specified as"^ 
    inf_pref^"an interval optionally depending on the number of variables e.g.:"^
    inf_pref^"1) [2.,5.] or  2)[0.5v,1.5v] or 3) [5.,0.75v] or 4) [0.,0.] for no eqs \n")

(*----------------*)
let opt_rnd_la_deqs_per_vars_str ="--rnd_la_deqs_per_vars"

let opt_rnd_la_deqs_per_vars_fun s = 
   !options.rnd_la_deqs_per_vars <- parse_inter_const_var s

let opt_rnd_la_deqs_per_vars_inf = 
  (inter_var_str^"-- number of equalities per number of variables, specified as"^ 
   inf_pref^"an interval optionally depending on the number of variables (see --rnd_la_deqs_per_vars)\n"
   )
(*----------------*)

let opt_rnd_la_geqs_per_vars_str ="--rnd_la_geqs_per_vars"

let opt_rnd_la_geqs_per_vars_fun s = 
   !options.rnd_la_geqs_per_vars <- parse_inter_const_var s

let opt_rnd_la_geqs_per_vars_inf =
  (inter_var_str^"-- number of inequalities of the type >= per number of variables, specified as"^ 
   inf_pref^"an interval optionally depending on the number of variables (see --rnd_la_deqs_per_vars)\n"
  )
    

(*----------------*)
let opt_rnd_la_grs_per_vars_str ="--rnd_la_grs_per_vars"

let opt_rnd_la_grs_per_vars_fun s = 
   !options.rnd_la_grs_per_vars <- parse_inter_const_var s

let opt_rnd_la_grs_per_vars_inf = 
  (inter_var_str^"-- number of inequalities of the type > per number of variables, sepecified as"^ 
   inf_pref^"an interval optionally depending on the number of variables (see --rnd_la_deqs_per_vars)\n"
  )
   
(*----------------*)

 

(*
let opt__str ="--"

let opt__fun b = 
   !options. <-b

let opt__inf = 

*)

(*-----------------------------*)      
let speclist = 
  [
(*--input--*)   
   (opt_input_dir_str, Arg.String(opt_input_dir_fun),opt_input_dir_inf);
   (opt_output_dir_str, Arg.String(opt_output_dir_fun),opt_output_dir_inf);
   (opt_rand_seed_str, 
    Arg.Int(opt_rand_seed_fun), opt_rand_seed_inf);

(*--solver--*)
   (opt_solver_str, Arg.String(opt_solver_fun),opt_solver_inf);
   (opt_solver_sat_str_str,Arg.String(opt_solver_sat_str_fun),opt_solver_sat_str_inf);
   (opt_solver_unsat_str_str,Arg.String(opt_solver_unsat_str_fun),opt_solver_unsat_str_inf);
   (opt_log_file_str, Arg.String(opt_log_file_fun),opt_log_file_inf);
   (opt_solver_timeout_str, Arg.Float(opt_solver_timeout_fun),opt_solver_timeout_inf);

(*---random regenrating ----------------------*)

   (opt_rnd_lra_str, Arg.Bool(opt_rnd_lra_fun),opt_rnd_lra_inf);
   (opt_rnd_lia_str, Arg.Bool(opt_rnd_lia_fun),opt_rnd_lia_inf);
   (opt_rnd_prop_str, Arg.Bool(opt_rnd_prop_fun),opt_rnd_prop_inf);
   (opt_rnd_input_results_file_str, Arg.String(opt_rnd_input_results_file_fun),opt_rnd_input_results_file_inf);
   (opt_rnd_output_results_file_str, Arg.String(opt_rnd_output_results_file_fun),opt_rnd_output_results_file_inf);
   (opt_rnd_generating_problems_str, Arg.Bool(opt_rnd_generating_problems_fun),opt_rnd_generating_problems_inf);
   (opt_rnd_run_on_results_file_str, Arg.Bool(opt_rnd_run_on_results_file_fun),opt_rnd_run_on_results_file_inf); 
   (opt_rnd_run_on_random_str, Arg.Bool(opt_rnd_run_on_random_fun),opt_rnd_run_on_random_inf);
   (opt_rnd_run_on_dir_str, Arg.Bool(opt_rnd_run_on_dir_fun),opt_rnd_run_on_dir_inf);
   (opt_rnd_run_on_dir_ext_str, Arg.String(opt_rnd_run_on_dir_ext_fun),opt_rnd_run_on_dir_ext_inf);
  (* (opt_rnd_start_vars_str, Arg.Int(opt_rnd_start_vars_fun),opt_rnd_start_vars_inf); *)
   (opt_rnd_num_of_vars_str,Arg.String(opt_rnd_num_of_vars_fun),opt_rnd_num_of_vars_inf);
   (opt_rnd_num_same_var_probs_str, Arg.Int(opt_rnd_num_same_var_probs_fun),opt_rnd_num_same_var_probs_inf);
(*   (opt_rnd_num_of_problems_str, Arg.Int(opt_rnd_num_of_problems_fun),opt_rnd_num_of_problems_inf);*) 
   (opt_rnd_prop_cl_per_var_str, Arg.Float(opt_rnd_prop_cl_per_var_fun),opt_rnd_prop_cl_per_var_inf);
   (opt_rnd_prop_lit_in_cl_str, Arg.String(opt_rnd_prop_lit_in_cl_fun),opt_rnd_prop_lit_in_cl_inf);
(opt_rnd_prop_out_format_str, Arg.String(opt_rnd_prop_out_format_fun),opt_rnd_prop_out_format_inf);
   (opt_rnd_la_coeff_str, Arg.String(opt_rnd_la_coeff_fun),opt_rnd_la_coeff_inf);
   (opt_rnd_la_vars_in_constr_str, Arg.String(opt_rnd_la_vars_in_constr_fun),opt_rnd_la_vars_in_constr_inf);
   (opt_rnd_la_eqs_per_vars_str, Arg.String(opt_rnd_la_eqs_per_vars_fun),opt_rnd_la_eqs_per_vars_inf);
   (opt_rnd_la_deqs_per_vars_str, Arg.String(opt_rnd_la_deqs_per_vars_fun),opt_rnd_la_deqs_per_vars_inf);
   (opt_rnd_la_geqs_per_vars_str, Arg.String(opt_rnd_la_geqs_per_vars_fun),opt_rnd_la_geqs_per_vars_inf);
   (opt_rnd_la_grs_per_vars_str, Arg.String(opt_rnd_la_grs_per_vars_fun),opt_rnd_la_grs_per_vars_inf);
(*     (opt__str, Arg.Bool(opt__fun),opt__inf) *)
 ]



let check_options_consistency () = 
  begin
    (if !options.log_file = "" 
    then 
      failwith "log file should be specified, see --log_file\n");
    (if (not (xor_list [!options.rnd_lra;!options.rnd_lia;!options.rnd_prop;!options.rnd_run_on_dir;!options.rnd_run_on_results_file]))
    then 
      failwith "exactly one of --rnd_lra, --rnd_lia, --rnd_prop, --rnd_run_on_dir should be true or --rnd_run_on_results_file\n");
    (if not (xor_list 
	      [!options.rnd_generating_problems; 
	       !options.rnd_run_on_results_file;   
	       !options.rnd_run_on_random;         
	       !options.rnd_run_on_dir;])
    then 
      failwith " excatly one of --rnd_generating_problems, --rnd_run_on_results_file, --rnd_run_on_random, --rnd_run_on_dir should be true\n");
    (let (l,r) = !options.rnd_prop_lit_in_cl in
    if (l<=0 || l>r) 
    then 
      failwith " --rnd_prop_lit_in_cl interval should be [l,r] l>0, l<=r"
    );

    (let (l,r) = !options.rnd_la_coeff in
    if (l>r) || (l=0 & r=0)  
    then 
      failwith " --rnd_la_coeff interval should be [l,r] l<=r and not both l,r are 0\n"
    );
    let (l,r) = !options.rnd_num_of_vars in
    (if (l>r) || (l<1)
    then
      failwith "--rnd_num_of_vars should be interval [l,r] where l<=r and l>=1"  
     ); 
  (*   (let (l,r) = !options.rnd_la_vars_in_constr in
      if (l>r) || (l<= 0)   
      then 
	failwith " --rnd_la_vars_in_constr interval should be [l,r] l<=r and 0<l\n"
      );
*)
  (*  (if ((!options.rnd_lia || !options.rnd_lra)
	   &
	 (
	  ((*!options.rnd_la_eqs_per_vars < 0. || *)
	  !options.rnd_la_geqs_per_vars < 0. || 
	  !options.rnd_la_grs_per_vars  < 0. 
	  )  
	||
	  (
	   (*!options.rnd_la_eqs_per_vars   = 0. &*)
	   !options.rnd_la_geqs_per_vars  = 0. & 
	   !options.rnd_la_grs_per_vars   = 0. 
	  )
         )
	)
    then
     failwith 
	" if --rnd_la is true then at least one of  --rnd_la_eq, --rnd_la_geq  --rnd_la_gr should be strictly greater than 0. and all of them should be non-negative\n " 
    )
*)         
  end



let parse_options () =
  Arg.parse speclist default_arg_fun usage_msg;
  !options.log_file <- (Filename.concat !options.output_dir !options.log_file);
  check_options_consistency ()

let _ =  parse_options ()
