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

val debug : bool

(* name of the system*)
val system_name : string

(*--------------------Signals Timers---------------*)
exception Termination_Signal
exception Time_out_real
exception Time_out_virtual

(* raises  Time_out_real after float seconds*)
val set_timer : float -> unit
val reset_timer : unit -> unit
(*---------------*)

type 'a param = Def of 'a | Undef 

val get_some : 'a option -> 'a

(* truncates floate to n digits after . e.g. truncate_n 2 0.123455 = 0.12 *)
val truncate_n : int -> float -> float 

(* elements and ref to elem of indexies and all others*)

  type 'a elem = Elem of 'a | Empty_Elem
  type 'a ref_elem = ('a elem) ref


(* Some regular expressions *)
val reg_expr_float : Str.regexp

val rnd_bool : unit -> bool

val xor : bool -> bool -> bool 

val xor_list : bool list -> bool 

(*---------------------------*)
type interval = int*int


val interval_to_string : interval -> string

val interval_to_string_p : interval -> string

val  parse_interval     : string -> interval

val inter_consistent          : interval -> bool

val inter_consistent_positive : interval -> bool

val rnd_from_inter : interval -> int

type inter_float = float*float 

val inter_float_to_int : inter_float -> interval

(*--inter_cont_var: itervals of types [4.,5.] or [1.5v,3.7v], or [0.5,4.v]----*)

type inter_const_var   
val parse_inter_const_var : string -> inter_const_var

val inter_const_var_to_float : float -> inter_const_var -> inter_float


(*-------String Streams--------*)
 
(* string stream can be e.g. a buffer or a channel *)

type 'a string_stream = 
    {
     buff : 'a;
     add_char : char   -> unit;
     add_str  : string -> unit;
   }


(*----------------Processes------------------------*)


val create_process_newgr : 
    string -> string array ->
      Unix.file_descr -> Unix.file_descr -> Unix.file_descr -> int

(*val check_process_status process_name process_status =*)

(* "Normally_Terminated (i)" where i is the exit code *)
(* "Ubnormally_Terminated signal_name"  signa_name is according to Sys mudle *)

type termination_status = 
    Normally_Terminated of int| Ubnormally_Terminated of string


val termination_status_to_string : termination_status -> string

val parse_termination_status     : string -> termination_status


val check_process_status : Unix.process_status -> termination_status


(*--create_process_newgr forks a process in a new process group-----*)
(*--This can be used to kill the child process and all children of the child--*)
(* Example: 
 *   let process_id = 
 *	create_process_newgr
 *	  (cmd_str) 
 *	  (Array.of_list args_list)  (* args_list[0] should be cmd_str*)
 *	  (*Unix.stdin *)
 *	  (Unix.descr_of_in_channel in_channel)
 *	  (Unix.descr_of_out_channel out_channel)
 *	(*  Unix.stderr*)
 *	  (Unix.descr_of_out_channel err_channel)
 *     let process_status =  Unix.waitpid [] process_id in 
 *     check_process_status cmd_str process_status; 
 *  
 *)
(* kills the process group associated with the child id *)
val kill_process_group : int -> unit

(* keep all children globally *)

val add_child_process : int -> unit

(* kills and removes top process *)
val remove_top_child_process  : unit -> unit
val kill_all_child_processes  : unit -> unit



(*-----------Files---------*)
(* remove_file file_name runs "rm -f file_name" *)
val remove_file : string -> unit

(*  open_file_append file_name *)
(*opens file for append if does not exists then creates it*)
val open_file_append : string -> out_channel

(* file_append_str file_name str, opens, appends then closes the file *)
val file_append_str : string -> string -> unit
 
(* fails if not a dir *)
(*val is_dir_fail : string -> unit*)


(*--------------------------------*)


   
(* outcome of compare fun.*)
val cequal   : int
val cgreater : int
val cless    : int

(* *)
val param_str_ref : string ref 
val pref_str      : string
val add_param_str : string -> unit
val add_param_str_front : string -> unit
val param_str_new_line : unit -> unit

val compose_sign  : bool -> ('a -> 'b -> int) -> ('a -> 'b -> int)
(* hash sum where the first arg is rest and second is next number*)
val hash_sum : int -> int ->int 

exception Termination_Signal

(* composes functions *)

val compose_12   : ('a->'b)->('c->'d ->'a) -> 'c->'d -> 'b

val param_to_string : ('a -> string) -> 'a param -> string


(* used for localization of vars, binding can be 
   applied for vars, terms, clauses *)
type 'a bind = int * 'a

val  propagate_binding_to_list :  ('a list) bind -> ('a bind) list

(* lexicographic comparison of pairs*)
val pair_compare_lex : ('a -> 'a -> int)-> ('b -> 'b -> int) -> 'a*'b ->'a*'b -> int

(* bool operations *)
val bool_plus : bool -> bool -> bool

(*lists*)
val list_skip : 'a -> 'a list -> 'a list

(* explicitly maps from left to right, 
   since order can matter when use imperative features *)
val list_map_left : ('a -> 'b) -> 'a list -> 'b list

val list_to_string : ('a -> string) -> 'a list -> string -> string

val list_of_str_to_str : (string list) -> string -> string

val list_findf : ('a -> 'b option) -> 'a list -> 'b option

val out_str : string -> unit
(* out if debug is on *)
(*val out_str_debug : string -> unit*)

val list_compare_lex : ('a -> 'a -> int) -> 'a list -> 'a list ->int
val lex_combination  : ('a -> 'a -> int) list -> 'a -> 'a -> int

(* in list_is_max_elem and list_get_max_elements
   we assume that compare as follows: 
   returns cequal if t greater or equal to s and 
   returns cequal+1 if t is strictly greater
   returns cequal-1 if it is not the case
  Note: it is assumed that 
   if t (gr or eq) s and s (gr or eq) t then t==s
*)    

val list_is_max_elem_v :   ('a -> 'a -> int) -> 'a -> 'a list -> bool

val list_get_max_elements_v : ('a -> 'a -> int) -> 'a list -> 'a list

(* for usual orderings *)
val list_is_max_elem :   ('a -> 'a -> int) -> 'a -> 'a list -> bool

val list_find_max_element : ('a -> 'a -> int) -> 'a list -> 'a

val list_find_max_element_p : ('a -> bool) -> ('a -> 'a -> int) -> 'a list -> 'a

(* removes duplicates  based on the fact 
  that literals are preordered i.e. the same are in sequence*)

val list_remove_duplicates : ('a list) -> ('a list)

val list_find2 : ('a -> 'b -> bool) -> ('a list) -> ('b list) -> ('a *'b) 

val list_return_g_if_f2 : 
    ('a -> 'b -> bool) -> ('a -> 'b -> 'c) -> ('a list) -> ('b list) -> 'c

(* finds first el. a' b' not equal by compare_el, 
  which suppose to return ctrue if equal,
  and returns compare_el 'a 'b 
*)

val list_find_not_equal :  
    ('a -> 'b -> int) -> ('a list) -> ('b list) -> int
	
val list_find_not_identical :
    ('a list) -> ('a list) -> 'a * 'a

(* association lists *)

type ('a, 'b) ass_list = ('a*'b) list

(* appends ass lists: if list1 and list2 have
 elem with (k,v1)  and (k,v2) resp. then new list will have (k,(f !v1 !v2))
 otherwise  appends (k1,v1) and (k2,v2)*)

val append_ass_list : 
    ('b -> 'b -> 'b) -> ('a, 'b) ass_list -> ('a, 'b) ass_list -> ('a, 'b) ass_list

type 'a num_ass_list =  ('a,int) ass_list


(* assume L is a list f : P(L) -> bool is anti-monotonic w.r.t inlcusion *)
(* (false<true) then  get_maximal_sublist f l = (max,rest)               *)
(* where max is a maximal (w.r.t inlcusion)                              *)
(* subset of L such that f(max) = true and rest is the rest of the list  *)

val get_maximal_sublist : ('a list -> bool) -> 'a list -> (('a list) * ('a list))


(*---------strings-----------*)

(*string filled with n spaces *)
val space_str        :  int -> string 

(* add spaces to str to reach distance *)
(*if the distance is less than or equal to str then just one space is added*)
(*(used for formatting output) *)
val space_padding_str :  int -> string -> string


(*--------Named modules----------------------*)

module type NameM = 
  sig
    val name : string
  end



(*--------------Global Time Limits-------------------*)
(* time limit in seconds *)
(* time_limit can be reassigned, there are number of points where it is checked*)


exception Timeout

(*---------Discount time limits can be checked in all related modules-------*)
(* After Timeout using discount can be incomplete (bit still sound) *)

val assign_discount_time_limit :float -> unit 
val assign_discount_start_time : unit -> unit
val check_disc_time_limit : unit -> unit
