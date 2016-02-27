(** Various utility functions. *)

val pp_list :
  sep:(unit, Format.formatter, unit) format ->
  (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a list -> unit

(** Returns string in option or "stdout" if None given. *)
val output_filename_string : string option -> string

(** Open an output channel on given filename, gives it to the given function and
    eventually closes the channel. stdout is used if no filename is given. *)
val with_out_ch : string option -> (out_channel -> 'b) -> 'b

(** Same as [with_out_ch] for input channels (with stdin instead of stdout). *)
val with_in_ch : string option -> (in_channel -> 'b) -> 'b

(** [profile f] executes the function [f] and returns both its result
    and the execution time in second. *)
val profile : (unit -> 'a) -> 'a * float
