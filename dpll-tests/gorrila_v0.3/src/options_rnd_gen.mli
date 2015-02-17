type prop_out_format = DIMACS_Format | SMT_Format
val parse_prop_format : string -> prop_out_format
type options = {
  mutable output_dir : string;
  mutable input_dir : string;
  mutable log_file : string;
  mutable random_seed : int;
  mutable solver : string;
  mutable solver_sat_str : string;
  mutable solver_unsat_str : string;
  mutable solver_timeout : float;
  mutable rnd_prop : bool;
  mutable rnd_lra : bool;
  mutable rnd_lia : bool;
  mutable rnd_input_results_file : string;
  mutable rnd_output_results_file : string;
  mutable rnd_generating_problems : bool;
  mutable rnd_run_on_results_file : bool;
  mutable rnd_run_on_random : bool;
  mutable rnd_run_on_dir : bool;
  mutable rnd_run_on_dir_ext : string;
  mutable rnd_num_of_vars : Lib.interval;
  mutable rnd_num_same_var_probs : int;
  mutable rnd_prop_cl_per_var : float;
  mutable rnd_prop_lit_in_cl : Lib.interval;
  mutable rnd_prop_out_format : prop_out_format;
  mutable rnd_la_coeff : Lib.interval;
  mutable rnd_la_vars_in_constr : Lib.inter_const_var;
  mutable rnd_la_eqs_per_vars : Lib.inter_const_var;
  mutable rnd_la_deqs_per_vars : Lib.inter_const_var;
  mutable rnd_la_geqs_per_vars : Lib.inter_const_var;
  mutable rnd_la_grs_per_vars : Lib.inter_const_var;
}
val default_options : unit -> options
val options : options ref
val bool_str : string
val str_str : string
val int_str : string
val float_str : string
val interval_str : string
val inter_var_str : string
val inf_pref : string
val example_str : string
val usage_msg : string
val default_arg_fun : 'a -> 'b
val opt_input_dir_str : string
val opt_input_dir_fun : string -> unit
val opt_input_dir_inf : string
val opt_output_dir_str : string
val opt_output_dir_fun : string -> unit
val opt_output_dir_inf : string
val opt_log_file_str : string
val opt_log_file_fun : string -> unit
val opt_log_file_inf : string
val opt_rand_seed_str : string
val opt_rand_seed_fun : int -> unit
val opt_rand_seed_inf : string
val opt_solver_str : string
val opt_solver_fun : string -> unit
val opt_solver_inf : string
val opt_solver_sat_str_str : string
val opt_solver_sat_str_fun : string -> unit
val opt_solver_sat_str_inf : string
val opt_solver_unsat_str_str : string
val opt_solver_unsat_str_fun : string -> unit
val opt_solver_unsat_str_inf : string
val opt_solver_timeout_str : string
val opt_solver_timeout_fun : float -> unit
val opt_solver_timeout_inf : string
val opt_rnd_prop_str : string
val opt_rnd_prop_fun : bool -> unit
val opt_rnd_prop_inf : string
val opt_rnd_lra_str : string
val opt_rnd_lra_fun : bool -> unit
val opt_rnd_lra_inf : string
val opt_rnd_lia_str : string
val opt_rnd_lia_fun : bool -> unit
val opt_rnd_lia_inf : string
val opt_rnd_input_results_file_str : string
val opt_rnd_input_results_file_fun : string -> unit
val opt_rnd_input_results_file_inf : string
val opt_rnd_output_results_file_str : string
val opt_rnd_output_results_file_fun : string -> unit
val opt_rnd_output_results_file_inf : string
val opt_rnd_generating_problems_str : string
val opt_rnd_generating_problems_fun : bool -> unit
val opt_rnd_generating_problems_inf : string
val opt_rnd_run_on_results_file_str : string
val opt_rnd_run_on_results_file_fun : bool -> unit
val opt_rnd_run_on_results_file_inf : string
val opt_rnd_run_on_random_str : string
val opt_rnd_run_on_random_fun : bool -> unit
val opt_rnd_run_on_random_inf : string
val opt_rnd_run_on_dir_str : string
val opt_rnd_run_on_dir_fun : bool -> unit
val opt_rnd_run_on_dir_inf : string
val opt_rnd_run_on_dir_ext_str : string
val opt_rnd_run_on_dir_ext_fun : string -> unit
val opt_rnd_run_on_dir_ext_inf : string
val opt_rnd_prop_cl_per_var_str : string
val opt_rnd_prop_cl_per_var_fun : float -> unit
val opt_rnd_prop_cl_per_var_inf : string
val opt_rnd_prop_lit_in_cl_str : string
val opt_rnd_prop_lit_in_cl_fun : string -> unit
val opt_rnd_prop_lit_in_cl_inf : string
val opt_rnd_prop_out_format_str : string
val opt_rnd_prop_out_format_fun : string -> unit
val opt_rnd_prop_out_format_inf : string
val opt_rnd_num_of_vars_str : string
val opt_rnd_num_of_vars_fun : string -> unit
val opt_rnd_num_of_vars_inf : string
val opt_rnd_num_same_var_probs_str : string
val opt_rnd_num_same_var_probs_fun : int -> unit
val opt_rnd_num_same_var_probs_inf : string
val opt_rnd_la_coeff_str : string
val opt_rnd_la_coeff_fun : string -> unit
val opt_rnd_la_coeff_inf : string
val opt_rnd_la_vars_in_constr_str : string
val opt_rnd_la_vars_in_constr_fun : string -> unit
val opt_rnd_la_vars_in_constr_inf : string
val opt_rnd_la_eqs_per_vars_str : string
val opt_rnd_la_eqs_per_vars_fun : string -> unit
val opt_rnd_la_eqs_per_vars_inf : string
val opt_rnd_la_deqs_per_vars_str : string
val opt_rnd_la_deqs_per_vars_fun : string -> unit
val opt_rnd_la_deqs_per_vars_inf : string
val opt_rnd_la_geqs_per_vars_str : string
val opt_rnd_la_geqs_per_vars_fun : string -> unit
val opt_rnd_la_geqs_per_vars_inf : string
val opt_rnd_la_grs_per_vars_str : string
val opt_rnd_la_grs_per_vars_fun : string -> unit
val opt_rnd_la_grs_per_vars_inf : string
val speclist : (string * Arg.spec * string) list
val check_options_consistency : unit -> unit
val parse_options : unit -> unit
