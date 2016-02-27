exception Error

let verbosity = ref 1

let nlogf n =
  if n <= !verbosity then
    Format.kfprintf
      (fun ff ->
        Format.kfprintf
          (fun ff -> Format.fprintf ff "@]\n%!")
          ff)
      Format.err_formatter
      "%s@[" (if n >= 4 then String.make (2 * (n - 3)) ' ' else "")
  else
    Format.ifprintf
      Format.err_formatter

let kstr k str =
  Format.kfprintf
    (fun ff ->
      Format.kfprintf
        (fun ff -> Format.fprintf ff "\n%!"; k ff)
        ff)
    Format.err_formatter
    "%s" str

let kstr_loc k str loc =
  Format.kfprintf
    (fun ff ->
      Format.kfprintf
        (fun ff -> Format.fprintf ff "\n%!"; k ff)
        ff)
    Format.err_formatter
    "%a%s" Location.fprint loc str

let warning f = kstr (fun _ -> ()) "Warning: " f

let warning_loc loc f = kstr_loc (fun _ -> ()) "Warning: " loc f

let error f = kstr (fun _ -> raise Error) "Error: " f

let error_loc loc f = kstr_loc (fun _ -> raise Error) "Error: " loc f

let silent f =
  let old_verbosity = !verbosity in
  verbosity := 0;
  let res = f () in
  verbosity := old_verbosity;
  res
