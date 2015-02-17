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

type solver_params = 
    {
     mutable solver                      : string;
     mutable solver_sat_str              : string;
     mutable solver_unsat_str            : string;
     mutable solver_timeout              : float option;     
   }


type status = Sat | Unsat | Unknown

val status_to_string : status -> string
val string_to_status : string -> status

type time = Time of float | Timeout

val time_to_string : time -> string
val string_to_time : string -> time

val cmp_time : time -> time -> int

(* float is the time taken by the solver to produce the result *)
(*type result = (status * time)*)

(*type result = (termination_status * status *time)*)

type result

(* less time better result *)
val cmp_results : result -> result -> int
val check_consistency : result -> result -> bool
 
val result_to_string : result -> string 
val string_to_result : string -> result

(*----Some statistics---------------*)
val get_all_sat      : result list -> result list
val get_all_unsat    : result list -> result list
val get_all_unknown  : result list -> result list
val get_average_time : result list -> float
val out_stat         : result list -> string

(* run_solver_channel time_limit fun_out = (status,time)*)
(* where fun_out is a function *)
(* that outputs an smt formula into an out_channel*)
val run_solver_channel : solver_params -> (out_channel -> unit) -> result


(* run_solver_file  time_limit  file_name similar to run_solver_channel  *)
(* but reads problem from  file_name *)
val run_solver_file : solver_params -> string -> result
    
