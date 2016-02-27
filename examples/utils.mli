(** Various utility functions. *)

(** Returns string in option or "stdout" if None given. *)
val output_filename_string : string option -> string

(** Open an output channel on given filename, gives it to the given function and
    eventually closes the channel. stdout is used if no filename is given. *)
val with_out_ch : string option -> (out_channel -> 'b) -> 'b

(** Same as [with_out_ch] for input channels (with stdin instead of stdout). *)
val with_in_ch : string option -> (in_channel -> 'b) -> 'b
