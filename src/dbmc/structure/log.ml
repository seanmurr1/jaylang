open Core

let saved_oc = ref None

let filename_of_now () = Core.Time.(now () |> to_filename_string ~zone:Zone.utc)

let init ?(testname = "") ?log_level () =
  Logs.set_level log_level;
  Logs.Src.set_level Debug_log.phi_log (Some Logs.Debug);

  (* Logs.set_reporter (Logs_fmt.reporter ()); *)
  (* Logs.set_reporter (reporter (Format.err_formatter)) *)
  let suffix =
    String.Search_pattern.(replace_all (create "/") ~in_:testname ~with_:"_")
  in
  let log_file =
    Filename.of_parts [ "logs"; filename_of_now () ^ "_" ^ suffix ^ ".log" ]
  in
  let oc = Out_channel.create log_file in
  saved_oc := Some oc;
  let fmter = Format.formatter_of_out_channel oc in
  let reporter =
    Logs.format_reporter ~pp_header:Logs.pp_header ~app:Format.std_formatter
      ~dst:fmter ()
  in
  Logs.set_reporter reporter;

  ()

let dot_file_oc_of_now () =
  let filename = Core.Time.(now () |> to_filename_string ~zone:Zone.utc) in
  let dot_file = Filename.of_parts [ "dot"; filename_of_now () ^ ".dot" ] in
  Out_channel.create dot_file

let close () =
  match !saved_oc with Some oc -> Out_channel.close oc | None -> ()